"""Check the finite fort inequalities for the six-sheet prism chains."""

import argparse
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import runpy


CHECKS = runpy.run_path(str(Path(__file__).with_name('check_four_sheet_chain_forts.py')))
MODEL = CHECKS['MODEL']


def verify_rank_case(case):
    return CHECKS['verify_prism_rank_case'](case, 6, MODEL['six_sheet_cubic_chain_certificate'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')

    CHECKS['verify_long_ladders'](range(16, 22), 11)
    print('Ladder widths 16 through 21 verified', flush=True)
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        for extra in range(16):
            cases = [(blocks, 0, extra) for blocks in range(50, 1, -1)]
            for count, _ in enumerate(pool.map(verify_rank_case, cases), 1):
                if count % 10 == 0 or count == len(cases):
                    print(f'Rank offset {extra}: {count}/{len(cases)} graphs', flush=True)


if __name__ == '__main__':
    main()
