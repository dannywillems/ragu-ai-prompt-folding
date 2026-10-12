#!/usr/bin/env python3
"""Check completeness and soundness of revdot folding under several weight
schemes, over the Pallas scalar field.

A revdot claim is (a, b, c) with revdot(a, b) = c, where
revdot(a, b) = sum_i a_i * b_{L-1-i}. Folding n claims uses weights
lambda_i on the a side and eta_j on the b side, both monomials in the
verifier challenges. The prover sends one value per OFF-DIAGONAL monomial
(the sum of the e_ij = revdot(a_i, b_j) that land on it), the verifier forms
c* = sum_k lambda_k eta_k c_k + sum_m m * g_m and checks
revdot(sum lambda_i a_i, sum eta_j b_j) = c*.

Schemes (exponent maps i -> exponent vector of lambda_i / eta_i):
  ragu      lambda_i = mu^{-i}, eta_j = (mu nu)^j     (book, revdot.md)
  convex    lambda_i = eta_i = mu^i nu^{i^2}          (symmetric, 2 challenges)
  ap3free   lambda_i = eta_i = rho^{p_i}, P 3-AP-free (symmetric, 1 challenge)
  ap3bad    same with P = {0, 1, 2}, which CONTAINS a 3-AP

For each scheme we report the number of cross terms the prover sends, run an
honest fold (must accept), and run the "shift" attack: corrupt one diagonal
claim c_k by delta and compensate in the off-diagonal value sharing the
diagonal's monomial, if any. The attack succeeds exactly when a diagonal
monomial coincides with an off-diagonal one.

Run: python3 -I fold_check.py
"""

import random

# Pallas scalar field = Vesta base field (order of the Pallas group).
P = 0x40000000000000000000000000000000224698FC0994A8DD8C46EB2100000001
L = 16  # vector length; irrelevant to the algebra, kept small
rng = random.Random(20261010)


def revdot(a, b):
    return sum(x * y for x, y in zip(a, reversed(b))) % P


def rand_vec():
    return [rng.randrange(P) for _ in range(L)]


def lin(ws, vs):
    out = [0] * L
    for w, v in zip(ws, vs):
        for t in range(L):
            out[t] = (out[t] + w * v[t]) % P
    return out


def scheme_exponents(name, n):
    """Return (sA, sB): lists of exponent tuples for lambda_i and eta_i."""
    if name == "ragu":  # (mu, nu) exponents
        return [(-i, 0) for i in range(n)], [(j, j) for j in range(n)]
    if name == "convex":
        e = [(i, i * i) for i in range(n)]
        return e, e
    if name == "ap3free":
        pset = [0, 1, 3, 4, 9, 10, 12, 13, 27, 28][:n]  # no base-3 digit 2
        assert len(pset) == n
        e = [(p,) for p in pset]
        return e, e
    if name == "ap3bad":
        assert n == 3
        e = [(0,), (1,), (2,)]
        return e, e
    raise ValueError(name)


def add(u, v):
    return tuple(x + y for x, y in zip(u, v))


def mono(exp, ch):
    """Evaluate the monomial with exponent tuple exp at challenges ch."""
    out = 1
    for e, c in zip(exp, ch):
        out = out * pow(c, e, P) % P  # negative e uses modular inverse
    return out


def run(name, n, attack):
    sA, sB = scheme_exponents(name, n)
    a = [rand_vec() for _ in range(n)]
    b = [rand_vec() for _ in range(n)]
    c = [revdot(a[i], b[i]) for i in range(n)]
    diag = {add(sA[k], sB[k]): k for k in range(n)}
    assert len(diag) == n, "diagonal monomials must be distinct"
    # Prover groups off-diagonal e_ij by monomial.
    g = {}
    for i in range(n):
        for j in range(n):
            if i != j:
                m = add(sA[i], sB[j])
                g[m] = (g.get(m, 0) + revdot(a[i], b[j])) % P
    clash = sorted(set(g) & set(diag))
    if attack:
        delta = rng.randrange(1, P)
        if clash:
            m = clash[0]
            k = diag[m]
            c[k] = (c[k] + delta) % P  # false claim
            g[m] = (g[m] - delta) % P  # compensate: same monomial
        else:
            c[0] = (c[0] + delta) % P  # nothing to compensate with
    # Verifier challenges (after cross terms are fixed).
    nch = len(sA[0])
    ch = [rng.randrange(1, P) for _ in range(nch)]
    lam = [mono(e, ch) for e in sA]
    eta = [mono(e, ch) for e in sB]
    cstar = sum(lam[k] * eta[k] * c[k] for k in range(n))
    cstar += sum(mono(m, ch) * v for m, v in g.items() if m not in diag)
    # A clashing off-diagonal value is merged with its diagonal monomial.
    cstar += sum(mono(m, ch) * v for m, v in g.items() if m in diag)
    cstar %= P
    ok = revdot(lin(lam, a), lin(eta, b)) == cstar
    sent = len(g)  # values the prover sends (clashing ones included)
    return ok, sent, len(clash)


def main():
    print("scheme   n  cross_terms_sent  clashes  honest  attack_accepted")
    for name, n in [("ragu", 7), ("convex", 7), ("ap3free", 7),
                    ("ragu", 3), ("ap3free", 3), ("ap3bad", 3)]:
        ok_h, sent, cl = run(name, n, attack=False)
        ok_a, _, _ = run(name, n, attack=True)
        print(f"{name:8s} {n:2d}  {sent:16d}  {cl:7d}  {ok_h!s:6s}  {ok_a}")


if __name__ == "__main__":
    main()
