"""Check the finite fort inequalities for the five-sheet prism chains."""

import argparse
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import runpy


CHECKS = runpy.run_path(str(Path(__file__).with_name('check_four_sheet_chain_forts.py')))
MODEL = CHECKS['MODEL']


def verify_rank_case(case):
    return CHECKS['verify_prism_rank_case'](case, 5, MODEL['five_sheet_cubic_chain_certificate'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')

    CHECKS['verify_long_ladders'](range(13, 18), 9)
    print('Ladder widths 13 through 17 verified', flush=True)
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        for extra_values in ((0,), (1, 2, 3, 4)):
            for columns in range(13):
                cases = [(blocks, columns, extra) for blocks in range(2, 43) for extra in extra_values]
                for count, _ in enumerate(pool.map(verify_rank_case, cases), 1):
                    if count == len(cases):
                        print(f'Padding width {columns}, residues {extra_values}: {count} graphs passed', flush=True)


if __name__ == '__main__':
    main()
