"""Stage the original certificate replays under the repository's build directory."""

import argparse
from hashlib import sha256
from pathlib import Path
import shutil
from zipfile import ZipFile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SIMULATOR = ROOT / "scripts" / "classification_experiment.py"
SIMULATOR_SHA256 = "c5939b16bf482bb7550e586da9c32ef530cb6867368d8eb940394ae0b3b1164b"
PINNED_LAYOUT = Path("runs/20261118T002947_523991Z-github-publication/source/scripts")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "build/unicyclic-reproduction")
    args = parser.parse_args()
    if sha256(SIMULATOR.read_bytes()).hexdigest() != SIMULATOR_SHA256:
        parser.error("scripts/classification_experiment.py differs from the pinned v1.0.1 simulator")

    workspace = args.output.resolve()
    if workspace.exists():
        parser.error(f"choose a new output directory because {workspace} already exists")
    replays = workspace / HERE.name
    with ZipFile(HERE / "evidence.zip") as evidence:
        if any(Path(entry).name != entry or not entry.endswith(".json")
               for entry in evidence.namelist()):
            raise ValueError("evidence.zip must contain only JSON files at its root")
        replays.mkdir(parents=True)
        evidence.extractall(replays)
    for source in [*HERE.glob("*.lean"), *HERE.glob("*.py")]:
        if source.name != Path(__file__).name:
            shutil.copyfile(source, replays / source.name)
    baseline = workspace / PINNED_LAYOUT
    baseline.mkdir(parents=True)
    shutil.copyfile(SIMULATOR, baseline / SIMULATOR.name)
    print(replays)


if __name__ == "__main__":
    main()
