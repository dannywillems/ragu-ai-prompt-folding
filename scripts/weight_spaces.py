#!/usr/bin/env python3
"""Linear algebra of fold weights: cost is a property of the weight SPACE,
soundness is a property of the weight BASIS.

For weights lambda_i (a side) and eta_j (b side), polynomials in the
challenges, put
  U = span{ lambda_i eta_j : all i, j }      (all products)
  O = span{ lambda_i eta_j : i != j }        (off-diagonal products)
  Lambda_i = lambda_i eta_i                  (diagonal products)
Theorem 5.3 of paper.md: a one-round fold with these weights is sound iff
the Lambda_i are linearly independent modulo O, and then the least number of
field elements the prover must send is dim O = dim U - k. Lemma 5.4: if each
weight family is linearly independent, dim U >= 2k - 1, for any number of
challenges, hence dim O >= k - 1.

This script computes, for each scheme and k, dim V, dim U, dim O, the rank of
the diagonal modulo O (sound iff = k), and checks dim U >= 2k - 1.

Schemes:
  ragu      lambda_i = mu^{-i}, eta_j = (mu nu)^j      (shifted to polynomials)
  convex    lambda_i = eta_i = mu^i nu^{i^2}
  ap3       lambda_i = eta_i = rho^{p_i}, P a shortest 3-AP-free set
  mono-ap   lambda_i = eta_i = rho^i (span = F[rho]_{<k}, an "AP")
  lagrange  lambda_i = eta_i = L_i(rho) on the domain {0..k-1}
mono-ap and lagrange span the SAME space; only the basis differs.

Run: python3 -I weight_spaces.py
"""

P = 0x40000000000000000000000000000000224698FC0994A8DD8C46EB2100000001

AP3_SETS = {
    3: [0, 1, 3],
    7: [0, 1, 3, 4, 9, 10, 12],
    19: [0, 1, 4, 5, 11, 13, 14, 16, 20, 30, 37, 38, 41, 42, 48, 50, 51, 53,
         57],
}


def inv(x):
    return pow(x, P - 2, P)


def pmul(f, g):
    """Multiply polynomials given as {exponent tuple: coeff}."""
    out = {}
    for e1, c1 in f.items():
        for e2, c2 in g.items():
            e = tuple(a + b for a, b in zip(e1, e2))
            out[e] = (out.get(e, 0) + c1 * c2) % P
    return {e: c for e, c in out.items() if c}


def rank(polys, reduce_by=()):
    """Rank of polys modulo span(reduce_by), over F_P."""
    keys = sorted({e for f in list(polys) + list(reduce_by) for e in f})
    idx = {e: t for t, e in enumerate(keys)}

    def vec(f):
        v = [0] * len(keys)
        for e, c in f.items():
            v[idx[e]] = c
        return v

    def reduce_rows(rows):
        basis = []  # list of (pivot, row)
        for r in rows:
            r = r[:]
            for piv, b in basis:
                if r[piv]:
                    f = r[piv]
                    r = [(x - f * y) % P for x, y in zip(r, b)]
            nz = next((t for t, x in enumerate(r) if x), None)
            if nz is not None:
                s = inv(r[nz])
                r = [x * s % P for x in r]
                # keep basis reduced at the new pivot
                basis = [(pv, [(x - b[nz] * y) % P for x, y in zip(b, r)])
                         for pv, b in basis]
                basis.append((nz, r))
        return basis

    base = reduce_rows([vec(f) for f in reduce_by])
    full = reduce_rows([vec(f) for f in reduce_by] + [vec(f) for f in polys])
    return len(full) - len(base)


def lagrange_basis(k):
    out = []
    for i in range(k):
        poly = {(0,): 1}
        den = 1
        for j in range(k):
            if j != i:
                poly = pmul(poly, {(1,): 1, (0,): (-j) % P})
                den = den * (i - j) % P
        s = inv(den)
        out.append({e: c * s % P for e, c in poly.items()})
    return out


def weights(name, k):
    if name == "ragu":  # mu^{-i} -> multiply by mu^{k-1} (a unit, same dims)
        lam = [{(k - 1 - i, 0): 1} for i in range(k)]
        eta = [{(j, j): 1} for j in range(k)]
        return lam, eta
    if name == "convex":
        w = [{(i, i * i): 1} for i in range(k)]
        return w, w
    if name == "ap3":
        w = [{(p,): 1} for p in AP3_SETS[k]]
        return w, w
    if name == "mono-ap":
        w = [{(i,): 1} for i in range(k)]
        return w, w
    if name == "lagrange":
        w = lagrange_basis(k)
        return w, w
    raise ValueError(name)


def main():
    print("scheme    k  dimV  dimU  dimO  diag_rank_mod_O  sound  "
          "min_sent=dimO  dimU>=2k-1")
    for k in [3, 7, 19]:
        for name in ["ragu", "convex", "ap3", "mono-ap", "lagrange"]:
            lam, eta = weights(name, k)
            prods = {(i, j): pmul(lam[i], eta[j])
                     for i in range(k) for j in range(k)}
            off = [prods[i, j] for (i, j) in prods if i != j]
            diag = [prods[i, i] for i in range(k)]
            dV = rank(lam)
            dU = rank(list(prods.values()))
            dO = rank(off)
            dr = rank(diag, reduce_by=off)
            sound = dr == k
            print(f"{name:8s} {k:2d}  {dV:4d}  {dU:4d}  {dO:4d}  "
                  f"{dr:15d}  {sound!s:5s}  "
                  f"{(dO if sound else '-')!s:>13s}  {dU >= 2 * k - 1}")
        print()


if __name__ == "__main__":
    main()
