#!/usr/bin/env python3
"""Lagrange (ProtoGalaxy-style) folding of k revdot claims, over the Pallas
scalar field, as a drop-in replacement for Ragu's monomial-weight fold.

Claims: (a_i, b_i, c_i), i in [k], with revdot(a_i, b_i) = c_i.
Domain: the points 0, 1, ..., k-1; L_i the Lagrange basis, Z(X) = prod (X - i).

  a(X) = sum_i L_i(X) a_i      b(X) = sum_i L_i(X) b_i      (vector-valued)
  G(X) = revdot(a(X), b(X))    degree <= 2(k-1), and G(i) = c_i on the domain
  I(X) = interpolant of the c_i (degree <= k-1, verifier-computable)
  K(X) = (G(X) - I(X)) / Z(X)  degree <= k-2, i.e. k-1 coefficients

Prover sends the k-1 coefficients of K; verifier samples gamma and outputs
the single claim (a*, b*, c*) with a* = sum L_i(gamma) a_i, likewise b*, and
c* = I(gamma) + Z(gamma) K(gamma).

Soundness (Schwartz-Zippel): if some revdot(a_i, b_i) != c_i, then the true
G differs from I + Z K at the domain point i, so the two degree-<=2(k-1)
polynomials agree at a random gamma with probability <= 2(k-1)/|F|. The
script checks: honest acceptance, cross-term count k-1 (versus k(k-1) for
Ragu's weights), and that a false claim with the prover's best guess for K
(the quotient of G - I_false, remainder dropped) is rejected.

Also runs the knowledge extractor of paper.md, Proposition 5.5: from 2k-1
accepting transcripts sharing the prover message K but with distinct gamma,
it recovers every (a_i, b_i) by inverting the k x k matrix [L_i(gamma_t)],
checks that the remaining k-1 transcripts are consistent with them (a
mismatch would be a commitment opening to two values, i.e. a binding break),
and checks revdot(a_i, b_i) = c_i for all i.

Run: python3 -I lagrange_fold.py
"""

import random

P = 0x40000000000000000000000000000000224698FC0994A8DD8C46EB2100000001
L = 8
rng = random.Random(7)


def inv(x):
    return pow(x, P - 2, P)


def revdot(a, b):
    return sum(x * y for x, y in zip(a, reversed(b))) % P


def lagrange_at(k, x):
    """[L_0(x), ..., L_{k-1}(x)] for the domain 0..k-1."""
    out = []
    for i in range(k):
        num, den = 1, 1
        for j in range(k):
            if j != i:
                num = num * (x - j) % P
                den = den * (i - j) % P
        out.append(num * inv(den) % P)
    return out


def interpolate(xs, ys):
    """Coefficients (low to high) of the interpolant through (xs, ys)."""
    n = len(xs)
    coeffs = [0] * n
    for i in range(n):
        basis = [1]
        den = 1
        for j in range(n):
            if j == i:
                continue
            basis = [(c1 - xs[j] * c0) % P for c0, c1 in
                     zip(basis + [0], [0] + basis)]
            den = den * (xs[i] - xs[j]) % P
        s = ys[i] * inv(den) % P
        for t in range(n):
            coeffs[t] = (coeffs[t] + s * basis[t]) % P
    return coeffs


def poly_eval(c, x):
    acc = 0
    for v in reversed(c):
        acc = (acc * x + v) % P
    return acc


def poly_divmod(num, den):
    num = num[:]
    q = [0] * max(1, len(num) - len(den) + 1)
    lead = inv(den[-1])
    for s in range(len(num) - len(den), -1, -1):
        f = num[s + len(den) - 1] * lead % P
        q[s] = f
        for t, d in enumerate(den):
            num[s + t] = (num[s + t] - f * d) % P
    return q, num[:len(den) - 1]


def vanishing(k):
    z = [1]
    for j in range(k):
        z = [(c1 - j * c0) % P for c0, c1 in zip(z + [0], [0] + z)]
    return z


def lin(ws, vs):
    return [sum(w * v[t] for w, v in zip(ws, vs)) % P for t in range(L)]


def prove(a, b, c):
    k = len(a)
    xs = list(range(2 * k - 1))
    gs = []
    for x in xs:
        lam = lagrange_at(k, x)
        gs.append(revdot(lin(lam, a), lin(lam, b)))
    G = interpolate(xs, gs)
    I = interpolate(list(range(k)), c)
    diff = [(g - (I[t] if t < len(I) else 0)) % P for t, g in enumerate(G)]
    K, rem = poly_divmod(diff, vanishing(k))
    return K, any(rem)


def verify(a, b, c, K):
    k = len(a)
    gamma = rng.randrange(k, P)
    lam = lagrange_at(k, gamma)
    I_g = sum(l * ci for l, ci in zip(lam, c)) % P
    cstar = (I_g + poly_eval(vanishing(k), gamma) * poly_eval(K, gamma)) % P
    return revdot(lin(lam, a), lin(lam, b)) == cstar


def mat_inv(m):
    n = len(m)
    a = [row[:] + [int(i == j) for j in range(n)] for i, row in enumerate(m)]
    for col in range(n):
        piv = next(r for r in range(col, n) if a[r][col])
        a[col], a[piv] = a[piv], a[col]
        s = inv(a[col][col])
        a[col] = [x * s % P for x in a[col]]
        for r in range(n):
            if r != col and a[r][col]:
                f = a[r][col]
                a[r] = [(x - f * y) % P for x, y in zip(a[r], a[col])]
    return [row[n:] for row in a]


def extract(k, c, K, transcripts):
    """transcripts: list of (gamma, a_star, b_star), all accepted, same K."""
    assert len(transcripts) == 2 * k - 1
    for g, ast, bst in transcripts:  # every transcript must verify
        lam = lagrange_at(k, g)
        I_g = sum(l * ci for l, ci in zip(lam, c)) % P
        cst = (I_g + poly_eval(vanishing(k), g) * poly_eval(K, g)) % P
        assert revdot(ast, bst) == cst
    head = transcripts[:k]
    V = [lagrange_at(k, g) for g, _, _ in head]
    Vi = mat_inv(V)
    a = [lin(Vi[i], [t[1] for t in head]) for i in range(k)]
    b = [lin(Vi[i], [t[2] for t in head]) for i in range(k)]
    for g, ast, bst in transcripts[k:]:  # consistency (binding)
        lam = lagrange_at(k, g)
        assert lin(lam, a) == ast and lin(lam, b) == bst
    return all(revdot(a[i], b[i]) == c[i] for i in range(k)), a, b


def main():
    print("k  cross_terms(lagrange)  cross_terms(ragu)  honest  "
          "remainder_if_false  false_accepted")
    for k in [2, 3, 7, 19]:
        a = [[rng.randrange(P) for _ in range(L)] for _ in range(k)]
        b = [[rng.randrange(P) for _ in range(L)] for _ in range(k)]
        c = [revdot(a[i], b[i]) for i in range(k)]
        K, rem = prove(a, b, c)
        assert not rem and len(K) == k - 1
        honest = verify(a, b, c, K)
        cf = c[:]
        cf[k // 2] = (cf[k // 2] + 1) % P
        Kf, remf = prove(a, b, cf)  # quotient with the remainder dropped
        cheat = verify(a, b, cf, Kf)
        print(f"{k:2d}  {len(K):21d}  {k * (k - 1):17d}  {honest!s:6s}  "
              f"{remf!s:18s}  {cheat}")
    print()
    print("k  extractor: 2k-1 transcripts -> all claims recovered and valid")
    for k in [2, 3, 7, 19]:
        a = [[rng.randrange(P) for _ in range(L)] for _ in range(k)]
        b = [[rng.randrange(P) for _ in range(L)] for _ in range(k)]
        c = [revdot(a[i], b[i]) for i in range(k)]
        K, _ = prove(a, b, c)
        gammas = rng.sample(range(k, 10**9), 2 * k - 1)
        ts = []
        for g in gammas:
            lam = lagrange_at(k, g)
            ts.append((g, lin(lam, a), lin(lam, b)))
        ok, ea, eb = extract(k, c, K, ts)
        print(f"{k:2d}  {ok and ea == a and eb == b}")


if __name__ == "__main__":
    main()
