#!/usr/bin/env python3
"""In-circuit cost of folding n revdot claims, for Ragu's weight scheme and
the two symmetric alternatives, over all 1-, 2- and 3-layer partitions.

Cost model (multiplication constraints to compute the folded value c*),
matching the book's accounting (revdot.md, "Complexity Analysis"):

  ragu(m)    = m^2 - 1           nested Horner over mu^{j-i} nu^j, plus 2
                                 per layer to precompute mu*nu and mu^{-1}
  convex(m)  = m(m-1)/2 + 2m     c* = sum_i l_i (l_i c_i + sum_{j>i} l_j g_ij)
                                 with l_i = mu^i nu^{i^2}; the 2m covers the
                                 l_i themselves (one mul each by a running
                                 power) and the outer products
  ap3(m)     = 2 * maxP(m)       Horner over rho^0 .. rho^{2 max P}, where
                                 maxP(m) is the least possible largest element
                                 of an m-element 3-AP-free set (A065825 - 1,
                                 computed by ap3_search.c)

  lagrange(m) = 5m - 2           domain {0..m-1}: Z(gamma) (m muls),
                                 1/(gamma - i) (m inversions, 1 constraint
                                 each), L_i(gamma) = Z(gamma) w_i / (gamma-i)
                                 (m muls; w_i constant), I(gamma) =
                                 sum L_i c_i (m muls), K(gamma) by Horner
                                 (m - 2 muls)

Cross terms sent per group: ragu m(m-1); convex m(m-1)/2; lagrange m-1;
ap3 |P+P| - m
(from ap3_search.c output; we use the set the search found, which minimises
the span, not necessarily |P+P|).

Run: python3 -I layer_cost.py [n]   (default: 93 and 133)
"""

import itertools
import math
import sys

# From out/ap3_search.txt: n -> (largest element, |P+P| - n).
AP3 = {
    1: (0, 0), 2: (1, 1), 3: (3, 3), 4: (4, 5), 5: (8, 9), 6: (10, 12),
    7: (12, 16), 8: (13, 19), 9: (19, 25), 10: (23, 31), 11: (25, 36),
    12: (29, 45), 13: (31, 47), 14: (35, 53), 15: (39, 61), 16: (40, 65),
    17: (50, 76), 18: (53, 83), 19: (57, 88), 20: (62, 96), 21: (70, 111),
    22: (73, 115), 23: (81, 129), 24: (83, 133), 25: (91, 145),
    26: (94, 154),
}


def layer(scheme, m):
    """(constraints, cross terms) to fold one group of m claims."""
    if m == 1:
        return 0, 0
    if scheme == "ragu":
        return m * m - 1, m * (m - 1)
    if scheme == "convex":
        return m * (m - 1) // 2 + 2 * m, m * (m - 1) // 2
    if scheme == "lagrange":
        return 5 * m - 2, m - 1
    if scheme == "ap3":
        if m not in AP3:
            return None
        mx, cross = AP3[m]
        return 2 * mx, cross
    raise ValueError(scheme)


def plan_cost(scheme, sizes, n):
    """sizes = group size per layer, innermost first; product >= n.

    Layer t folds ceil(n_t / m_t) groups; every group costs a full m_t
    (padding), which is what Ragu does with its fixed (7, 19)."""
    total, cross, cur = 0, 0, n
    for m in sizes:
        groups = math.ceil(cur / m)
        c = layer(scheme, m)
        if c is None:
            return None
        total += groups * c[0] + 2  # +2: per-layer challenge precompute
        cross += groups * c[1]
        cur = groups
    if cur != 1:
        return None
    return total, cross


def best(scheme, n, layers):
    out = None
    rng = range(2, 27) if scheme == "ap3" else range(2, 134)
    if layers == 3:
        rng = range(2, 27)
    for sizes in itertools.product(rng, repeat=layers):
        if math.prod(sizes) < n:
            continue
        r = plan_cost(scheme, sizes, n)
        if r and (out is None or r[0] < out[0]):
            out = (r[0], r[1], sizes)
    return out


def main():
    ns = [int(sys.argv[1])] if len(sys.argv) > 1 else [93, 133]
    for n in ns:
        print(f"n = {n} claims")
        r = plan_cost("ragu", (7, 19), n)
        print(f"  ragu   (7,19) as deployed       : {r[0]:5d} constraints,"
              f" {r[1]:5d} cross terms")
        for scheme in ["ragu", "convex", "ap3", "lagrange"]:
            for layers in [1, 2, 3]:
                if layers == 1 and scheme == "ap3" and n > max(AP3):
                    continue
                b = best(scheme, n, layers)
                if b:
                    print(f"  {scheme:6s} best {layers}-layer {str(b[2]):12s}:"
                          f" {b[0]:5d} constraints, {b[1]:5d} cross terms")
        print()


if __name__ == "__main__":
    main()
