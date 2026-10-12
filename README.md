# Specialised accumulation for Ragu's revdot claims

Status: first pass done, design-level result. Started 2026-10-10. Ragu read
at commit `526b0e3e` (main). Write-up: `paper.md` (paper format, LaTeX).
Scripts: `scripts/` (commands in `scripts/README.md`). Ragu prototype:
`prototype/` (patch against `526b0e3e`, commands in `prototype/README.md`).

Build the paper (needs pandoc >= 3 and pdflatex): `make pdf` writes
`build/paper.pdf`, `make tex` writes the LaTeX source `build/paper.tex`,
`make html` writes `build/paper.html` with MathML math (renders offline, good
on a phone). `paper.md` is the single source; `latex-paths.lua` makes long
code paths breakable in the PDF. `make help` lists the targets.

## The idea, in the user's words (paraphrased)

Folding schemes transform a relation for any NP statement into a pair: a
relation R' and an accumulator relation. Under the hood this rests on
homogenisation (see the HackMD "Behind Nova: cross-terms computation for high
degree gates", <https://hackmd.io/qq_Awc1AR3ywzkruE4Wq9Q>). Think of this
transformation as a morphism, with categories if possible. Such morphisms also
exist for specialised statements (BLS aggregation, Schnorr): every aggregation
of a cryptographic object goes through some morphism of relations. Can we find
a specialised accumulation scheme for the SNARK Ragu describes?

## Questions

1. Which NP relation does Ragu's SNARK prove, and what residue does its NARK
   verifier leave? (paper, Section 2)
2. What is the categorical shape of accumulation, and what are cross terms
   intrinsically? (Section 3)
3. Which residue admits a cheaper, specialised fold? (Sections 4-5)

## Findings

- The NP relation is Bootle16 (R1CS-equivalent, degree 2), collapsed by two
  challenges to one revdot identity, eq. (2.1). Every circuit, stage, and the
  accumulator are instances of the revdot relation R_rdp.
- Cross terms of the generic fold are the reduced coproduct of the constraint
  polynomial in the Hopf algebra O(G_a^N) (polarisation). Linear relations
  fold for free; BLS and Schnorr half-aggregation are instances of that.
- Ragu folds 93 revdot claims per fuse step (capacity 133) with weights
  mu^{-i}, (mu nu)^j: k(k-1) cross terms, two layers (7, 19).
- Monomial weights: soundness holds if and only if the diagonal sums are
  uniquely represented; in the symmetric case this is 3-AP-freeness.
  Behrend and Kelley-Meka then say the cost is k^{1+o(1)}, never O(k).
  Forgery demonstrated for P = {0,1,2}.
- Lagrange weights (ProtoGalaxy, degree 2): k-1 cross terms, matching a
  degree-counting lower bound. For Ragu: 465 constraints / 92 cross terms in
  one layer, against 1036 / 930 in two layers today (model estimates).
- Cost of any sound linear one-round fold = dim O = dim(V.W) - k, where V, W
  are the weight spaces; dim(V.W) >= 2k - 1 for any number of challenges
  (polynomial Cauchy-Davenport). Soundness = diagonal products independent
  modulo O, a property of the BASIS: rho^i and L_i(rho) span the same space,
  only Lagrange is sound. So k - 1 is optimal (Theorem 5.3, Corollary 5.6).
- The Lagrange revdot fold is (2k-1)-special sound; extractor implemented.

## Log

- 2026-10-10: read the HackMD, the Ragu book (protocol chapters), and the
  claim builder in `crates/ragu_pcd/src/internal/native/claims.rs`. Wrote
  `fold_check.py`, `ap3_search.c`, `lagrange_fold.py`, `layer_cost.py`.
  First tried 3-AP-free monomial weights; noticed while costing them that the
  monomial basis is the obstruction, and switched to Lagrange weights.
  Verified ProtoGalaxy's protocol shape through A. Cube's notes (the ePrint
  PDF was blocked). `paper.md` written.

- 2026-10-10 (second pass): closed the open items. Knowledge soundness
  (Proposition 5.5, extractor in `lagrange_fold.py`); rigorous lower bound
  for any number of challenges (Theorem 5.3, Lemma 5.4, Corollary 5.6,
  checked by `weight_spaces.py`). ProtoGalaxy PDF still unreadable here
  (Cloudflare challenge); the proofs no longer depend on it.

- 2026-10-10 (third pass): added paper Sections 1.1-1.4: Zcash and Tachyon
  context, what Ragu is, the statement a Ragu proof certifies, and why the
  recursion overhead (revdot fold) is the bottleneck. Sources: tachyon.z.cash
  site and blog (partially retrievable), book `concepts/pcd.md`,
  `guide/capacity.md`, `protocol/analysis.md`.

- 2026-10-11: prototyped the fold in Ragu (`fold_revdot.rs`, module
  `lagrange`; now `prototype/lagrange-fold.patch`). 7 tests pass;
  measured 5k-2 gates (463 at k=93, 663 at k=133) against 1276 measured for
  the deployed two-layer fold. Paper Section 5.8.

## Next

- Wire the prototype into fuse: merge `inner_collapse`/`outer_collapse`,
  drop the `outer_error` stage, update `compress/revdot`.
- Classify equality in Lemma 5.4 (optimal weight spaces).
- Check whether the registry's evaluation claims admit one Lagrange-style
  transport (paper, Section 6.1).

- 2026-10-12: moved the whole idea out of a private notes repository and
  out of the Ragu working tree into this repository (`ragu-ai-prompt-folding`).
