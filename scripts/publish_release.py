from pathlib import Path
import hashlib
import json
import os
import subprocess
import time
import zipfile

ROOT = Path(__file__).resolve().parents[1]
os.chdir(ROOT)
REPO = os.environ['GITHUB_REPOSITORY']
assert REPO == '7654321s/zero-forcing-recovery'
inventory = json.loads((ROOT/'inventory.json').read_text(encoding='utf-8'))
TAG = inventory['tag']
TARGET = inventory['target_commit']

def gh(*args):
    result = subprocess.run(['gh', *args], check=True, text=True, capture_output=True)
    return result.stdout

def api(endpoint):
    return json.loads(gh('api', endpoint))

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

for name, expected in inventory['assets'].items():
    assert sha(ROOT/'assets'/name) == expected, name
tree = api(f'repos/{REPO}/git/trees/{TARGET}?recursive=1')
assert not tree.get('truncated')
remote = {x['path']: x['sha'] for x in tree['tree'] if x['type'] == 'blob'}
expected = {x['path']: x for x in inventory['source_files']}
assert set(remote) == set(expected) and len(remote) == 111
with zipfile.ZipFile(ROOT/'assets/zero-forcing-recovery-v1.0.1-published-source.zip') as archive:
    prefix = 'zero-forcing-recovery-v1.0.1/'
    assert {x[len(prefix):] for x in archive.namelist()} == set(expected)
    for name, row in expected.items():
        data = archive.read(prefix+name)
        assert hashlib.sha256(data).hexdigest() == row['sha256'], name
        blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert blob == remote[name] == row['git_blob_sha1'], name
print('All 111 published source files match the pinned remote commit.', flush=True)

deadline = time.monotonic()+25*60
while True:
    runs = api(f'repos/{REPO}/actions/runs?head_sha={TARGET}&per_page=30')['workflow_runs']
    candidates = [x for x in runs if x['head_sha'] == TARGET and x['path'] == '.github/workflows/verify.yml' and x['head_branch'] == 'main']
    if candidates:
        run = max(candidates, key=lambda x: (x['run_number'], x['run_attempt']))
        if run['status'] == 'completed':
            assert run['conclusion'] == 'success', 'Pinned source CI failed: '+run['html_url']
            break
    assert time.monotonic() < deadline, 'Timed out waiting for pinned source CI'
    print('Waiting for both platforms on '+TARGET, flush=True)
    time.sleep(20)
jobs = api(f"repos/{REPO}/actions/runs/{run['id']}/jobs?per_page=100")['jobs']
assert len(jobs) == 2 and all(x['conclusion'] == 'success' for x in jobs)
assert {x['name'] for x in jobs} == {'verify (ubuntu-latest)', 'verify (windows-latest)'}
gh('run', 'download', str(run['id']), '--repo', REPO, '--dir', '.ci-download')
summaries = []
for path in (ROOT/'.ci-download').rglob('summary.json'):
    row = json.loads(path.read_text(encoding='utf-8'))
    if 'project_proofs_built_from_source' not in row:
        continue
    assert row['status'] == 'passed' and row['project_proofs_built_from_source'] is True
    assert row['source_modules'] == 71 and row['checked_declarations'] == 511
    assert row['release_files_checked'] == 111
    assert row['small_trees'] == 95 and row['positive_small_trees'] == 21
    summaries.append(row)
assert len(summaries) == 2 and {x['operating_system'] for x in summaries} == {'Linux', 'Windows'}
archive = ROOT/'assets/ci-verification-v1.0.1.zip'
with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as z:
    for path in sorted((ROOT/'.ci-download').rglob('*')):
        if path.is_file():
            z.write(path, path.relative_to(ROOT/'.ci-download').as_posix())
receipt = {'status': 'passed_both_platforms', 'source_commit': TARGET,
           'workflow_run_id': run['id'], 'workflow_run_url': run['html_url'],
           'jobs': [{'id': x['id'], 'name': x['name'], 'conclusion': x['conclusion']} for x in jobs],
           'summaries': summaries, 'log_archive_sha256': sha(archive),
           'independent_human_review': False, 'novelty_confirmed': False}
(ROOT/'assets/ci-verification.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
checksums = ''.join(sha(p)+'  '+p.name+'\n' for p in sorted((ROOT/'assets').iterdir()) if p.is_file() and p.name != 'SHA256SUMS')
(ROOT/'assets/SHA256SUMS').write_text(checksums, encoding='utf-8')
files = [str(p.relative_to(ROOT)) for p in sorted((ROOT/'assets').iterdir()) if p.is_file()]
notes = (ROOT/'release-notes.md').read_text(encoding='utf-8')
notes += '\nSource commit: `'+TARGET+'`.\n\nCloud verification: '+run['html_url']+'\n'
(ROOT/'release-notes-final.md').write_text(notes, encoding='utf-8')
existing = [x for x in api(f'repos/{REPO}/releases?per_page=100') if x['tag_name'] == TAG]
assert len(existing) <= 1
if existing:
    draft = existing[0]
else:
    gh('release', 'create', TAG, *files, '--repo', REPO, '--target', TARGET, '--draft', '--title', 'v1.0.1: finite-tree classification and reproducible Lean proofs', '--notes-file', 'release-notes-final.md')
    matches = [x for x in api(f'repos/{REPO}/releases?per_page=100') if x['tag_name'] == TAG]
    assert len(matches) == 1
    draft = matches[0]
assert draft['draft'] is True and draft['target_commitish'] == TARGET
assets = {x['name']: x for x in draft['assets']}
assert set(assets) == {Path(x).name for x in files}
downloaded = ROOT/'.uploaded-assets'
downloaded.mkdir()
for name, asset in assets.items():
    assert Path(name).name == name
    destination = downloaded/name
    with destination.open('wb') as output:
        subprocess.run(['gh', 'api', f"repos/{REPO}/releases/assets/{asset['id']}", '-H', 'Accept: application/octet-stream'], stdout=output, stderr=subprocess.PIPE, check=True)
    assert asset['size'] == destination.stat().st_size
    assert asset.get('digest') == 'sha256:'+sha(destination), name
    if name in inventory['assets']:
        assert sha(destination) == inventory['assets'][name]
uploaded_receipt = json.loads((downloaded/'ci-verification.json').read_text(encoding='utf-8'))
assert uploaded_receipt['source_commit'] == TARGET and uploaded_receipt['status'] == 'passed_both_platforms'
assert uploaded_receipt['workflow_run_id'] == run['id']
assert {x['operating_system']:x for x in uploaded_receipt['summaries']} == {x['operating_system']:x for x in summaries}
assert uploaded_receipt['log_archive_sha256'] == sha(downloaded/'ci-verification-v1.0.1.zip')
with zipfile.ZipFile(downloaded/'ci-verification-v1.0.1.zip') as uploaded_zip, zipfile.ZipFile(archive) as current_zip:
    assert set(uploaded_zip.namelist()) == set(current_zip.namelist())
    assert all(uploaded_zip.read(name) == current_zip.read(name) for name in uploaded_zip.namelist())
for line in (downloaded/'SHA256SUMS').read_text(encoding='utf-8').splitlines():
    digest, name = line.split('  ', 1)
    assert name in assets and sha(downloaded/name) == digest
gh('api', '--method', 'PATCH', f"repos/{REPO}/releases/{draft['id']}", '-F', 'draft=false', '-f', 'make_latest=true')
published = api(f'repos/{REPO}/releases/tags/{TAG}')
tag = api(f'repos/{REPO}/git/ref/tags/{TAG}')
assert published['draft'] is False and tag['object']['type'] == 'commit' and tag['object']['sha'] == TARGET
print(json.dumps({'release_url': published['html_url'], 'tag_commit': TARGET, 'assets': len(published['assets'])}), flush=True)
