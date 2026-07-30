#!/usr/bin/env python3
"""
Measure the margin in the Local Continuation Hypothesis (LCH).

At a hub (a,b) that is BLOCKED on its row (no step a -> a+2), a "rescue" is a
pair (a*, b') with
   a* in the current run window on row b   (all columns a..a* coprime to b),
   gcd(a*, s) = 1 for every s in (b, b'],  (the climb at a* is legal)
   b' odd, 3 | b' false, and gcd(a*+1,b') = gcd(a*+2,b') = 1  (travel resumes),
   every vertex on the two legs satisfies the composite condition.

LCH says a rescue always exists at every hub the construction reaches.  This
script counts rescues at random blocked hubs at several scales, so we can see
how much room the hypothesis has.
"""
from math import gcd
import sys, random, json, argparse

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from path_search import is_prime, is_composite, prime_factors, pmin  # noqa: E402


def usable_row(b):
    return b % 2 == 1 and b % 3 != 0 and b > 1 and not is_prime(b)


def blocked(a, b):
    return gcd(a + 1, b) != 1 or gcd(a + 2, b) != 1


def run_window(a, b):
    """largest W with gcd(t,b)=1 for all t in [a, a+W]"""
    W = 10 ** 9
    for p in prime_factors(b):
        nxt = (a // p + 1) * p
        W = min(W, nxt - a - 1)
    return max(W, 0)


def climb_reach(a, b, cap):
    R = cap
    for p in prime_factors(a):
        nxt = (b // p + 1) * p
        R = min(R, nxt - b - 1)
        if R <= 0:
            return 0
    return R


def climb_composite_ok(astar, b, b2):
    if is_composite(astar):
        return True
    for s in range(b + 2, b2, 2):
        if s % 3 and is_prime(s):
            return False
    return True


def count_rescues(a, b, climb_cap=200, col_cap=400):
    """number of (a*, b') rescue pairs, and the first one found"""
    n = 0
    first = None
    W = min(run_window(a, b), col_cap)
    for astar in range(a, a + W + 1):
        if astar % 2 == 0 or astar % 3 == 0:
            continue
        R = climb_reach(astar, b, climb_cap)
        for b2 in range(b + 2, b + R + 1, 2):
            if not usable_row(b2):
                continue
            if gcd(astar + 1, b2) != 1 or gcd(astar + 2, b2) != 1:
                continue
            if not climb_composite_ok(astar, b, b2):
                continue
            n += 1
            if first is None:
                first = (astar - a, b2 - b)
    return n, first, W


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--samples", type=int, default=300)
    ap.add_argument("--out", default="rescue_margin.json")
    args = ap.parse_args()
    random.seed(5)
    report = {}
    for scale in [10 ** 3, 10 ** 4, 10 ** 6, 10 ** 9, 10 ** 12]:
        counts, firsts, wins, fails = [], [], [], 0
        got = 0
        tries = 0
        while got < args.samples and tries < args.samples * 400:
            tries += 1
            b = random.randrange(scale, 2 * scale) | 1
            a = random.randrange(scale, 2 * scale) | 1
            if not usable_row(b) or gcd(a, b) != 1 or a % 3 == 0:
                continue
            if not blocked(a, b):
                continue
            got += 1
            n, first, W = count_rescues(a, b)
            counts.append(n)
            wins.append(W)
            if first:
                firsts.append(first)
            else:
                fails += 1
        report[str(scale)] = {
            "blocked_hubs_sampled": got,
            "no_rescue_found": fails,
            "rescue_count_mean": sum(counts) / max(len(counts), 1),
            "rescue_count_min": min(counts) if counts else None,
            "run_window_mean": sum(wins) / max(len(wins), 1),
            "first_rescue_dx_mean": sum(f[0] for f in firsts) / max(len(firsts), 1),
            "first_rescue_dy_mean": sum(f[1] for f in firsts) / max(len(firsts), 1),
            "first_rescue_dx_max": max((f[0] for f in firsts), default=None),
            "first_rescue_dy_max": max((f[1] for f in firsts), default=None),
        }
        print(scale, json.dumps(report[str(scale)]))
    json.dump(report, open(args.out, "w"), indent=1)


if __name__ == "__main__":
    main()
