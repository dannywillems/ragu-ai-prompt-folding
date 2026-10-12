---
title: "Accumulation as a morphism of relations, and a specialised fold for Ragu's revdot claims"
author: Danny Willems (with Claude)
date: 2026-10-10
status: research note, draft. Ragu read at commit 526b0e3e (main).
---

# Accumulation as a morphism of relations, and a specialised fold for Ragu's revdot claims

**Abstract.** Ragu is a proof-carrying data (PCD) framework built from a
Bootle16 (R1CS-like) NARK whose verifier leaves three kinds of linear-time
residue: revdot (reversed inner product) claims, polynomial evaluation claims,
and wiring (registry) consistency claims. Each recursion step folds these
residues into an accumulator. We first state precisely which NP relation the
NARK proves and how it collapses to a single revdot identity. We then cast
accumulation as a morphism in a category of relations and reductions, recover
the generic Nova/ProtoStar transformation (homogenisation) as one such
morphism, and identify the cross terms as the reduced coproduct of the
constraint polynomial in the Hopf algebra of the additive group. This framing
says when a relation folds with no cross terms (linear relations: BLS and
Schnorr aggregation are instances) and what the cross terms cost otherwise.
Applied to Ragu, it singles out the revdot fold as the specialisation target:
the relation is bilinear, and the number of cross terms is decided entirely by
the choice of fold weights. We show (i) that with monomial weights, soundness
is equivalent to a unique-representation condition on exponents which, in the
symmetric case, is exactly 3-term-progression-freeness, so that the problem is
governed by Behrend's construction and the Kelley-Meka bound; and (ii) that
Lagrange weights (the ProtoGalaxy construction) need only $k-1$ cross terms
for $k$ claims, and are $(2k-1)$-special sound. We prove that $k-1$ is
optimal for any linear one-round fold with any number of challenges: the cost
of a fold is $\dim(V \cdot W) - k$ for the weight spaces $V, W$, bounded by a
polynomial Cauchy-Davenport inequality, while soundness depends only on the
basis. For Ragu's 93
revdot claims per fuse step, a single-layer Lagrange fold costs an estimated
465 multiplication constraints and 92 cross terms. The deployed two-layer
$(7,19)$ scheme costs 1036 constraints and 930 cross terms. The Lagrange fold
also removes one round of Fiat-Shamir challenges. All claims in this note are
backed by scripts in `scripts/`, whose outputs are in `scripts/out/`.

---

## 1. introduction

### 1.1 the setting: Zcash and Project Tachyon

Zcash's shielded pool (Orchard) attaches one zero-knowledge proof to every
transaction. The proof shows that the spent notes exist and have not been
spent before, and that values balance, without revealing which notes are
involved. Validators verify each proof, in batches. The Ragu book estimates
roughly 10-15 ms per Orchard proof on one thread (book,
`protocol/analysis.md`). Validators must also keep the nullifier set, which
grows with every spend, forever, to reject double spends.

Project Tachyon is a proposed scalability upgrade for Zcash. Its site states
that it "shrinks transactions by two orders of magnitude" and "removes
runaway state growth for validators" (<https://tachyon.z.cash/>). The
mechanism, as described on the project blog
(<https://tachyon.z.cash/blog/building-tachyons-proof-tree-with-shared-evidence/>,
2026-09-29), moves proving work from validators to wallets:

- each note has a secret master key, from which the wallet derives a
  pseudorandom nullifier *per epoch*;
- validators keep only "a rolling window of recent history", so the
  nullifier set they store stops growing without bound;
- for epochs beyond that window, the *wallet* proves that none of its note's
  earlier epoch nullifiers appeared on chain. It may delegate this to an
  oblivious syncing service, which "never learns anything about the note";
- shared historic evidence covering the pool's long history "can be built
  once per epoch, and reused by many wallets".

The result is that a spend carries a proof that is itself the composition of
many smaller proofs: about the note's creation, about each epoch's
non-membership check, and about the shared evidence. These proofs are
produced by different parties at different times and combined. That is
exactly the setting of *proof-carrying data*, and Ragu is, in the project's
words, "the fundamental platform upon which Tachyon's cryptography is
constructed" (<https://tachyon.z.cash/blog/folding-tachyon-with-ragu/>,
2026-05-07).

*Caveat.* We read only the parts of these two posts that were retrievable
from this environment. The tree structure of Tachyon's proofs is not
reconstructed here, and nothing in this note depends on it. What matters
below is the shape of the statements Ragu proves, which is given by Ragu
itself.

### 1.2 what Ragu is

Ragu is a Rust framework for proof-carrying data (PCD) [CT10]. It implements
a modified version of the recursive SNARK of Halo [BGH19] (book,
`introduction.md`). Its design is constrained by its deployment in Zcash:

- **no trusted setup**, so polynomial commitments are Pedersen vector
  commitments opened with a Bulletproofs-style inner product argument (IPA),
  as in `halo2`;
- **small proofs**, which with current techniques means an ECDLP-based
  construction;
- **the Pasta curve cycle** (Pallas, Vesta), already deployed in Orchard and
  in hardware wallets, so that each curve's group arithmetic is native in the
  other curve's scalar field.

The programming model (book, `concepts/pcd.md`) has three notions:

- a **header** is the data certified at a node of the computation graph,
  encoded as a circuit gadget (usually a commitment to the application's
  richer data);
- a **step** is a transition predicate. It takes two input headers and
  witness data and certifies an output header. Ragu is *non-uniform*:
  applications register many steps (hundreds or thousands of circuits), and
  each node pays only for the step it uses, with no verification keys, thanks
  to Halo's post-processing technique generalised to a registry of circuits;
- **fuse** is the only user-facing operation. Every node takes exactly two
  input PCD instances and applies a step, so every computation is a (possibly
  unbalanced) binary tree. The base case is a single internal step, `seed`,
  whose `Dummy` children are the only ones allowed to be invalid.

Proofs come in two modes. **Uncompressed** proofs are large but cheap to
fuse further. **Compressed** proofs are orders of magnitude smaller and
cheaper to verify, at extra proving cost, and are meant for the boundaries
where a proof leaves the application (for example, when it is posted on
chain). A proof can be rerandomised. The book states that zero knowledge and
unlinkability are not yet established and need further protocol work.

### 1.3 the proof Ragu makes

A Ragu proof for a header $h$ certifies, by induction, the following
statement:

> there exists a binary tree whose root outputs $h$, whose internal nodes
> each satisfy one registered step on the headers of their two children, and
> whose leaves are the base case.

The proof for $h$ does not contain the tree. It contains one NARK proof for
the last node, together with an *accumulator*: a short list of deferred
claims (revdot claims, polynomial evaluation claims, and a wiring claim)
that stands in for "every proof below this node was valid". Each fuse checks
the step, checks that the two children's accumulators and last proofs were
correctly merged into the new accumulator, and proves that it did so.
Verifying the final proof means checking the last NARK and *deciding* the
accumulator once. That single linear-time check, a few multi-scalar
multiplications of size $4n$, pays for the whole tree. Section 2 states
this relation precisely.

For Tachyon, $h$ is a commitment to an application-level fact, for example
that a note is valid and unspent across the epochs covered, or that a batch
of transactions is valid. Aggregation is what the analysis chapter of the
book targets. It estimates about 100 ms to verify one aggregated Ragu proof
at the default size, against about 10 ms per Orchard proof batch-verified,
and so a break-even near 50 transactions. The book marks these as rough
estimates to be benchmarked.

### 1.4 why the recursion overhead is the bottleneck

Each fuse must re-verify, inside circuits, the folding work of the previous
step. Ragu deliberately keeps circuits small: the production rank is
$2^{11} = 2048$ multiplication gates and $8192$ linear constraints per
circuit. Smaller committed vectors give smaller IPAs and faster verifiers
(book, `guide/capacity.md`, `protocol/index.md`). The budget is tight. One
Poseidon permutation costs 288 gates, so 7 fit in a step, and one endoscalar
operation costs 455 gates, so 4 fit. The recursive verifier is therefore
split across many internal circuits (`hashes_1`, `hashes_2`,
`inner_collapse`, `outer_collapse`, `compute_v`, the binding circuits, and 25
endoscaling steps per child). Each of these produces revdot claims that the
*next* step must fold. This gives a feedback loop: the cost of folding claims
determines how many circuits the recursion needs, and each circuit adds
claims to fold. The revdot fold alone costs 1036 constraints at Ragu's 93
claims per step, spread over two circuits and two rounds of challenges. It is
the most concentrated target in the recursion overhead, and the main subject
of this note.

### 1.5 this note

A folding (or accumulation) scheme turns a relation $\mathcal{R}$ into a pair
consisting of a relation $\mathcal{R}'$ and an accumulator relation
$\mathcal{R}_{\mathsf{acc}}$, together with a cheap procedure that merges a new
$\mathcal{R}'$-instance into an accumulator. PCD is obtained by proving, at
each node, "the step function was applied correctly, and the accumulator was
updated correctly". The expensive check (the *decider*) runs once, at the end.

The generic construction (Nova [KST22] for R1CS, ProtoStar [BC23] and the
companion note [Wil24] for higher degree) works for *any* NP relation written
as polynomial equations. It pays for that generality with cross terms: $d-1$
of them per fold for degree-$d$ constraints. The thesis of this note is that
specialised relations admit specialised accumulation morphisms. This is
familiar from signature aggregation (BLS, Schnorr half-aggregation), and the
same reasoning applies to the relations that a concrete SNARK leaves behind.
We carry it out for Ragu.

**Contributions.**

1. A precise statement of the NP relation behind Ragu's SNARK and of its
   reduction to one revdot identity (Section 2).
2. A categorical reading of accumulation (Section 3): relations and
   reductions of knowledge form a symmetric monoidal category, a folding
   scheme is an $n$-ary operation on an object, and homogenisation is the
   generic way to manufacture one. Cross terms are the reduced coproduct in
   $\mathcal{O}(\mathbb{G}_a^N)$; linear relations are exactly the ones that
   fold for free.
3. A decomposition of Ragu's fuse step into its three residual relations, with
   the measured claim inventory (Section 4).
4. A specialised fold for the bilinear revdot relation (Section 5), with two
   results: the monomial-weight design space reduces to additive
   combinatorics (3-AP-free sets), and Lagrange weights reach the lower bound
   of $k-1$ cross terms. We prove knowledge soundness of the Lagrange fold
   (Proposition 5.5) and the lower bound for any number of challenges
   (Theorem 5.3, Lemma 5.4, Corollary 5.6), with executable checks and a cost
   model calibrated against the Ragu book.

**Novelty disclaimer.** Lagrange-basis multi-folding is ProtoGalaxy's
construction [EG23], and homogenisation is ProtoStar's [BC23]. What we add is
the observation that Ragu's revdot fold is a degree-2 instance of the same
problem, the 3-AP characterisation of monomial weights, and the concrete cost
estimates for Ragu. We have not found the 3-AP characterisation in the
literature, but we have not searched exhaustively.

---

## 2. the NP statement behind Ragu

### 2.1 what is proved at a PCD node

Ragu proves *compliance* of a directed acyclic graph of computation in the
sense of Chiesa and Tromer [CT10]. A *compliance predicate* $\Phi$ (in Ragu,
a *step* chosen from a registry of circuits) takes the data $z_L, z_R$ on two
incoming edges and local advice $w_{\mathsf{loc}}$, and outputs data $z$. The
statement proved at a node with output $z$ is:

> there exist $z_L, z_R$, advice $w_{\mathsf{loc}}$, and proofs
> $\pi_L, \pi_R$ such that $\Phi(z_L, z_R, w_{\mathsf{loc}}) = z$, and
> $\pi_L, \pi_R$ attest to $z_L, z_R$ in the same sense.

The second conjunct is recursive. Unrolled, it states that the whole tree
below the node is compliant. A recursive SNARK makes this finite by putting
the verifier for $\pi_L, \pi_R$ inside the circuit for the node. Ragu replaces
"verify" with "accumulate": the circuit checks only that the children's
accumulators $\mathsf{acc}_L, \mathsf{acc}_R$, together with their last NARK
instances, were merged correctly into $\mathsf{acc}$ (book,
`protocol/core/accumulation/index.md`). Concretely, the relation proved at
step $i$ is

$$
\mathcal{R}_{\mathsf{step}} = \left\{
\begin{array}{l}
\mathsf{x} = (z, \mathsf{acc}.\mathsf{x}),\\
\mathsf{w} = (z_L, z_R, w_{\mathsf{loc}}, \pi_L, \pi_R, \mathsf{acc}_L, \mathsf{acc}_R, \mathsf{pf})
\end{array}
\;:\;
\begin{array}{l}
\Phi(z_L, z_R, w_{\mathsf{loc}}) = z,\\
\mathsf{Acc.V}(\{\pi_\ast.\mathsf{x}\}, \{\mathsf{acc}_\ast.\mathsf{x}\}, \mathsf{acc}.\mathsf{x}, \mathsf{pf}) = 1
\end{array}
\right\}.
$$

It is an ordinary NP relation, compiled into circuits over the Pasta cycle.
Group operations are native on one curve and field operations on the other,
so each half of $\mathsf{Acc.V}$ runs where it is native (Section 2.6).

### 2.2 the circuit relation: Bootle16

Every circuit, including the ones encoding $\mathsf{Acc.V}$, is expressed in
the constraint system of Bootle, Cerulli, Chaidos, Groth and Petit [BCCGP16],
as used in Sonic and Halo (book, `protocol/core/arithmetization.md`). Fix $n$
(the number of gates; Ragu's default rank is $n = 2^{11}$). The relation is

$$
\mathcal{R}_{\mathsf{B16}} = \Big\{ (\mathbf{k};\, \mathbf{a}, \mathbf{b}, \mathbf{c} \in \mathbb{F}^n) :\;
\mathbf{a} \circ \mathbf{b} = \mathbf{c}
\;\wedge\;
\forall j < 4n:\; \langle \mathbf{u}_j, \mathbf{a}\rangle + \langle \mathbf{v}_j, \mathbf{b}\rangle + \langle \mathbf{w}_j, \mathbf{c}\rangle = \mathbf{k}_j
\Big\},
$$

where the matrices $\mathbf{u}, \mathbf{v}, \mathbf{w} \in \mathbb{F}^{4n \times n}$
are the circuit, and $\mathbf{k} \in \mathbb{F}^{4n}$ is the instance
($\mathbf{k}_0 = 1$, then the public inputs, then zeros). There are $n$
multiplication *gates* and up to $4n$ linear *constraints* with unlimited
fan-in. This system is linear-time inter-reducible with R1CS. The only
nonlinearity is the Hadamard product, so the relation has degree 2. Ragu adds
a fourth wire vector $\mathbf{d}$ with $\mathbf{c} \circ \mathbf{d} = 0$; it
comes for free from the encoding below and is occasionally useful.

### 2.3 the idea: one inner product holds the whole circuit

The design goal is to verify $\mathcal{R}_{\mathsf{B16}}$ with univariate
polynomial commitments only, with no FFT on the folding path and no
bivariate PCS. The mechanism is a single algebraic fact:

> **Fact (middle coefficient).** For $p, q \in \mathbb{F}[X]$ of degree
> $< m$ with coefficient vectors $\mathbf{p}, \mathbf{q}$, the coefficient of
> $X^{m-1}$ in $p \cdot q$ is
> $\mathrm{revdot}(\mathbf{p}, \mathbf{q}) := \sum_i \mathbf{p}_i \mathbf{q}_{m-1-i} = \langle \mathbf{p}, \hat{\mathbf{q}} \rangle$.

So a *bilinear form* on witness vectors becomes one coefficient of a
polynomial product, which a univariate PCS can isolate. Ragu packs the
witness into a *structured vector* of length $4n$,

$$
\mathbf{r} = \mathbf{c} \,\|\, \hat{\mathbf{a}} \,\|\, \mathbf{b} \,\|\, \hat{\mathbf{d}},
\qquad
r(X) = \sum_{i<n} \big( c_i X^i + a_i X^{2n-1-i} + b_i X^{2n+i} + d_i X^{4n-1-i} \big),
$$

chosen so that reversal swaps $\mathbf{a} \leftrightarrow \mathbf{b}$ and
$\mathbf{c} \leftrightarrow \mathbf{d}$. Then
$\mathrm{revdot}(\mathbf{r}, \mathbf{r}) = 2\langle \mathbf{a}, \mathbf{b} \rangle + 2\langle \mathbf{c}, \mathbf{d}\rangle$:
the products we want to constrain appear as revdot pairings of the trace with
itself.

**Gates.** Dilating by a challenge $z$ (that is, $\mathbf{r} \circ \mathbf{z}^{4n}$,
or $r(zX)$) weights gate $i$ by distinct powers:

$$
\mathrm{revdot}(\mathbf{r}, \mathbf{r} \circ \mathbf{z}^{4n} + \mathbf{t})
= \sum_{i<n} (a_i b_i - c_i)\,(z^{2n-1-i} + z^{2n+i}) + \sum_{i<n} c_i d_i\,(z^i + z^{4n-1-i}),
$$

where the public correction vector $\mathbf{t}$ (the coefficients of
$t(X,z) = -\sum_i X^{4n-1-i}(z^{2n-1-i}+z^{2n+i})$) subtracts the $c_i$. As a
polynomial in $z$, this vanishes identically if and only if every gate holds.
By Schwartz-Zippel, a random $z$ catches a violation except with probability
at most $(4n-1)/|\mathbb{F}|$.

**Constraints.** Each constraint is a revdot of $\mathbf{r}$ against a fixed
vector $\mathbf{u}_j$ (the wire weights placed at the revdot-complementary
positions). Stacking them with powers of a challenge $y$ gives the *wiring
polynomial* $s(X, Y) = \sum_j Y^j u_j(X)$, and the check is
$\mathrm{revdot}(\mathbf{r}, s(X,y)) = k(y) := \sum_j \mathbf{k}_j y^j$.

**Consolidated identity.** Both checks add, because the gate part depends only
on $z$ and the constraint part only on $y$:

$$
\boxed{\;\mathrm{revdot}\big(r(X),\; r(zX) + s(X,y) + t(X,z)\big) = k(y)\;}
\tag{2.1}
$$

For uniform $(y,z)$, a false witness passes with probability at most
$(4n-1)/|\mathbb{F}|$ (book, `protocol/local/arithmetization.md`). So the
whole NP relation $\mathcal{R}_{\mathsf{B16}}$ reduces, with two challenges,
to one instance of the *revdot relation*

$$
\mathcal{R}_{\mathsf{rdp}} = \Big\{ (\bar A, \bar B, c;\, \mathbf{a}, \mathbf{b}, \gamma_a, \gamma_b) :\;
\bar A = \mathrm{Com}(\mathbf{a};\gamma_a) \wedge \bar B = \mathrm{Com}(\mathbf{b};\gamma_b) \wedge \mathrm{revdot}(\mathbf{a}, \mathbf{b}) = c \Big\},
\tag{2.2}
$$

with $\mathbf{a} = \mathbf{r}$ and $\mathbf{b} = r(zX) + s(X,y) + t(X,z)$.
Equation (2.2) is the NP statement that Ragu's machinery actually manipulates.
Every circuit, every *stage* (a partial trace, checked by a *masking*
polynomial in a claim $\mathrm{revdot}(\mathbf{r}, s_{\mathsf{mask}}) = 0$),
and the accumulator itself are instances of $\mathcal{R}_{\mathsf{rdp}}$.

### 2.4 from the identity to a NARK, and its three residues

The NARK (book, `protocol/core/nark.md`) commits to $r$, receives $(y, z)$,
commits to $s(X,y)$ and to $b$, and then needs three things it cannot check in
sublinear time:

| residue | relation | why it is linear-time |
|---|---|---|
| revdot | $\mathcal{R}_{\mathsf{rdp}}$ (2.2) | an inner product of length $4n$ |
| evaluation | $\mathcal{R}_{\mathsf{pcs}} = \{(\bar C, x, v; p) : \bar C = \mathrm{Com}(p),\ p(x) = v\}$ | the IPA verifier is linear |
| wiring | $S = \mathrm{Com}(s(X,y))$ for the right circuit $s$ | evaluating $s$ is $O(n)$ |

The design rationale is to *never* check these directly. The revdot claim is
not reduced to an evaluation of $a \cdot b$ (degree $8n-2$ exceeds the PCS
degree bound and would need FFTs). It is carried forward as a claim and
folded. Only at points of the tree where succinctness is needed (the
*compression* of `protocol/recursion/compression.md`) does the prover split
$a \cdot b = X^{D-1}p(1/X) + X^D q(X)$ and open.

### 2.5 the theory behind deferral

This is Halo's *nested amortisation* [BGH19], formalised as accumulation by
Bunz, Chiesa, Mishra and Spooner [BCMS20], and as *split* accumulation
(witness kept by the prover, only instances seen by the accumulation
verifier) in [BCLMS21]. Split accumulation is what allows a NARK, with
linear-size witness, to be used for PCD. Nova's folding schemes [KST22] are
the instance-only variant; the book notes that for Ragu's purposes the two are
equivalent.

The wiring residue uses Halo's *post-processing* trick, generalised to a
registry of circuits through the trivariate *registry polynomial*
$m(W, X, Y) = \sum_i \ell_i(W)\, s_i(X, Y)$. Two accumulated restrictions
$m(W, x_0, y_0)$ and $m(W, x_1, y_1)$ are bridged to a fresh $m(W, x, y)$ by
committing to intermediate restrictions $m(w, x_i, Y)$ and $m(w, X, y)$. This
turns "$S$ is the right circuit" into a chain of evaluation claims, which
land in $\mathcal{R}_{\mathsf{pcs}}$ (book, `accumulation/wiring.md`).

### 2.6 the cycle

Folding commitments needs group arithmetic. Folding scalars needs field
arithmetic in the scalar field. On the Pasta cycle,
$\mathbb{G}_{\mathsf{Pallas}}$ arithmetic is native in $\mathbb{F}_q$, and
vice versa. So each half of a step folds the scalars of its own accumulator
and the commitments of the other half's accumulator. Inputs are shared
across the two halves through *nested staged commitments*. Challenges are
shared through *endoscalars* (*transcript bridging*); see book,
`accumulation/pcs.md`.

---

## 3. accumulation as a morphism of relations

### 3.1 the category

Kothapalli and Parno [KP23] define a *reduction of knowledge* from a relation
$\mathcal{R}_1$ to a relation $\mathcal{R}_2$ as an interactive protocol that
maps an $\mathcal{R}_1$ instance-witness pair to an $\mathcal{R}_2$ pair, with
completeness and knowledge soundness (an $\mathcal{R}_1$ witness is
extractable from a prover that produces a valid $\mathcal{R}_2$ witness). They
prove sequential and parallel composition theorems. *Our framing*: these say
that relations and reductions form a symmetric monoidal category
$\mathbf{Red}$. The tensor $\mathcal{R}_1 \otimes \mathcal{R}_2$ is the
relation of pairs, with unit the trivial relation $\mathbf{1}$. Composition is
sequential composition, and the laws (associativity, unitality) hold up to
the identification of protocols that differ in bookkeeping. Soundness errors
add under composition, so the category is better seen as *graded* by the
soundness error, much as metric or quantitative equational theories are.

In this language:

- a **folding scheme** for $\mathcal{R}$ is a morphism
  $\mathsf{fold}_k : \mathcal{R}^{\otimes k} \to \mathcal{R}$. It is an
  operation of a *magma object*; associativity is not required, and Ragu's
  two-layer fold is precisely a bracketing of a $133$-ary operation into
  $7$-ary and $19$-ary ones;
- an **accumulation scheme** for $\mathcal{R}$ is an object
  $\mathcal{R}_{\mathsf{acc}}$ with a unit morphism
  $\iota : \mathcal{R} \to \mathcal{R}_{\mathsf{acc}}$ and an *action*
  $\mathcal{R}_{\mathsf{acc}} \otimes \mathcal{R} \to \mathcal{R}_{\mathsf{acc}}$.
  The decider is a (non-succinct) morphism from $\mathcal{R}_{\mathsf{acc}}$
  to the trivially decidable relation;
- the **NARK** of Section 2 is a morphism
  $\mathcal{R}_{\mathsf{B16}} \to \mathcal{R}_{\mathsf{rdp}}^{\otimes a} \otimes \mathcal{R}_{\mathsf{pcs}}^{\otimes b} \otimes \mathcal{R}_{\mathsf{wire}}$,
  and Ragu's accumulator is the object
  $\mathcal{R}_{\mathsf{rdp}} \otimes \mathcal{R}_{\mathsf{pcs}} \otimes \mathcal{R}_{\mathsf{wire}}$.

The PCD statement of Section 2.1 is then the composite: reduce the children's
NARKs to residues, act on the children's accumulators, and prove that this was
done. The point of the framing is the next observation. *An accumulation
scheme for a relation is a property of the object in $\mathbf{Red}$, not of
the circuit that produced it.* A specialised relation (BLS verification, a
revdot claim) can carry a cheaper action than the one the generic
construction provides.

### 3.2 the generic construction: homogenisation

Let a relation be given by a polynomial map $P : \mathbb{F}^N \to \mathbb{F}^M$
of degree at most $d$: $\mathcal{R}_P = \{ \mathbf{x} : P(\mathbf{x}) = 0 \}$
(public and private coordinates mixed). Homogenisation
$P^h(\mathbf{x}, u) = u^d P(\mathbf{x}/u)$ is the inverse of
dehomogenisation $Q \mapsto Q(\mathbf{x}, 1)$. It gives a linear isomorphism

$$
\mathbb{F}[X_1,\dots,X_N]_{\le d} \;\cong\; \mathbb{F}[U, X_1,\dots,X_N]_{d},
\qquad \dim = \binom{N+d}{d}.
$$

Homogenisation preserves the degree $d$ and adds one variable. A degree
$d+1$ appears only when an additional combiner (for example the challenge
$\alpha$ that batches several constraints) is itself treated as a folded
variable, as in the "shifted polynomial" section of [Wil24].

The relaxed relation is the graph of $P^h$:

$$
\mathcal{R}^{\mathsf{relax}}_P = \{ (\mathbf{x}, u, \mathbf{E}) : P^h(\mathbf{x}, u) = \mathbf{E} \},
\qquad
\iota(\mathbf{x}) = (\mathbf{x}, 1, \mathbf{0}).
$$

Here $\mathbf{E}$ is bound by a commitment in the instance. The original
relation sits inside as the fibre over $(u, \mathbf{E}) = (1, \mathbf{0})$,
and $\iota$ is the unit of the accumulation scheme. For R1CS this is exactly
Nova's relaxed R1CS. The action is "take the line through two points":

$$
P^h(\mathbf{z}_1 + r\mathbf{z}_2) = P^h(\mathbf{z}_1) + \sum_{k=1}^{d-1} r^k\, T_k(\mathbf{z}_1, \mathbf{z}_2) + r^d P^h(\mathbf{z}_2),
\qquad \mathbf{z}_i = (\mathbf{x}_i, u_i),
\tag{3.1}
$$

and the new error is $\mathbf{E}_1 + \sum_k r^k T_k + r^d \mathbf{E}_2$ with
the $T_k$ committed before $r$ is drawn. Homogeneity is what makes the two
end terms equal to the old errors, scaled by $1$ and $r^d$.

### 3.3 what the cross terms are: a coproduct

The algebra of polynomial functions on $\mathbb{F}^{N}$ is the coordinate ring
of the additive group scheme $\mathbb{G}_a^{N}$, a commutative Hopf algebra
$\mathcal{O} = \mathbb{F}[X_1, \dots, X_N]$. Its comultiplication
$\Delta : \mathcal{O} \to \mathcal{O} \otimes \mathcal{O}$ is dual to addition,
$\Delta(X_i) = X_i \otimes 1 + 1 \otimes X_i$, so that
$(\Delta f)(\mathbf{x}, \mathbf{y}) = f(\mathbf{x} + \mathbf{y})$ [Wat79, Ch. 1].
For $f$ homogeneous of degree $d$, $\Delta f$ splits by bidegree:

$$
\Delta f = \sum_{k=0}^{d} \Delta_{d-k,k} f,
\qquad \Delta_{d,0} f = f \otimes 1,\quad \Delta_{0,d} f = 1 \otimes f,
$$

and (3.1) is $\Delta P^h$ evaluated at $(\mathbf{z}_1, r\mathbf{z}_2)$.
Therefore:

> **Proposition 3.1 (cross terms are the reduced coproduct).** The cross terms
> of the generic fold are the components $T_k = \Delta_{d-k,k} P^h$,
> $1 \le k \le d-1$, of the reduced coproduct
> $\bar\Delta P^h = \Delta P^h - P^h \otimes 1 - 1 \otimes P^h$. If
> $\mathrm{char}\,\mathbb{F} > d$, they are the polarisations
> $T_k = \binom{d}{k}\, \mathcal{P}(\mathbf{z}_1^{\,d-k}, \mathbf{z}_2^{\,k})$
> of the unique symmetric $d$-linear form $\mathcal{P}$ with
> $P^h(\mathbf{z}) = \mathcal{P}(\mathbf{z}, \dots, \mathbf{z})$.

The proof is the binomial expansion of the multilinear form. It recovers the
monomial-by-monomial formulas of [Wil24].

**Consequence 1: free folding.** A relation folds with *zero* cross terms
exactly when $\bar\Delta P = 0$, that is, when $P$ is *primitive*. Over a
field of characteristic $0$, or of characteristic $p > \deg P$, the primitive
polynomials are the linear forms. So linear relations, the subobjects of
$\mathbb{F}^N$ that are themselves vector subspaces, fold for free.
Cross terms measure how far the solution set is from a subspace. (In
characteristic $p$, the endomorphisms of $\mathbb{G}_a$ are the additive
polynomials $\sum a_i X^{p^i}$ [Wat79]. Those fold freely only for challenges
in $\mathbb{F}_p$, which is useless at Pasta sizes; we mention it only for
completeness.)

**Consequence 2: specialised aggregation is linearity in the right
variables.** Folding requires a fixed linear map, and the verifier of a fold
pays for applying the challenges to the instance.

- *BLS* [BGLS03]: $e(\sigma, g_2) = e(H(m), \mathsf{pk})$ is linear in
  $\sigma$ for fixed $g_2$, so $\sigma = \sum \sigma_i$ aggregates with no
  cross terms. The right-hand side, linear in $\mathsf{pk}$ only for a fixed
  message, stays as a product of $n$ pairings unless the messages coincide.
- *Schnorr half-aggregation* [CGKN21]: $[s_i]G = R_i + [c_i]X_i$ is linear in
  $(s_i, R_i, X_i)$, so $s = \sum \rho_i s_i$ aggregates with random $\rho_i$.
  The bases $R_i, X_i$ vary, so they cannot be merged: the linear map is part
  of the instance. The authors give evidence (not a proof) that going below
  half would require statements specific to the hash function.
- *Scalar multiplication* $Q = [s]P$ with $P$ varying is bilinear in
  $(s, P)$. It folds with one group-element cross term $T = [s_1]P_2 + [s_2]P_1$,
  but the fold verifier must compute $P_1 + [r]P_2$, a scalar multiplication
  of the same cost as the claim. This is the obstruction that CycleFold-style
  delegation, and Ragu's endoscaling circuits, work around rather than
  remove.

So the question "is there a specialised accumulation for relation $\mathcal{R}$"
becomes two questions. In which variables is $\mathcal{R}$ multilinear? And
what does the fold verifier have to compute? For Ragu, the answer points at
$\mathcal{R}_{\mathsf{rdp}}$.

---

## 4. Ragu's fuse step, decomposed

Each fuse step folds the residues of two child proofs. Reading
`crates/ragu_pcd/src/internal/native/claims.rs` (function `build`), the native
revdot claims per fuse step are:

| source | per child | total |
|---|---|---|
| raw (the children's accumulators $(\bar A, \bar B, c)$) | 1 | 2 |
| application circuit | 1 | 2 |
| internal circuits: `hashes_1`, `hashes_2`, `inner_collapse`, `outer_collapse`, `compute_v` | 5 | 10 |
| `bind_challenges` ($\mathtt{NUM\_BINDERS} = 5$), `bind_beta`, `bind_endoscalar` | 7 | 14 |
| endoscaling steps ($\mathtt{NUM\_ENDOSCALING\_STEPS} = 25$) | 25 | 50 |
| stage and final-staged bonding claims (aggregated over both children) | n/a | 15 |
| **total** | | **93** |

This matches `InternalCircuitIndex::NUM = 22 + 5 + 25 = 52` (37 circuit
claims plus 15 bonding claims). The fold is configured for capacity
$M \cdot N = 7 \cdot 19 = 133$ (`NativeParameters` in
`internal/native/mod.rs`). Every claim is an $\mathcal{R}_{\mathsf{rdp}}$
instance. For a circuit claim, $b = a(zX) + s_i(X,y) + t(X,z)$ with $a$ a sum
of the circuit's stage polynomials. For a bonding claim, $b = s_{\mathsf{mask}}(X,y)$
and $c = 0$.

The current fold (book, `accumulation/revdot.md`) uses weights
$\lambda_i = \mu^{-i}$ on the $a$ side and $\eta_j = (\mu\nu)^j$ on the $b$
side:

$$
\bar A^\ast = \sum_i \mu^{-i}\bar A_i,\quad
\bar B^\ast = \sum_j (\mu\nu)^j \bar B_j,\quad
c^\ast = \sum_{i,j} \mu^{j-i}\nu^j\, e_{ij},\quad
e_{ij} = \mathrm{revdot}(\mathbf{a}_i, \mathbf{b}_j).
$$

The prover sends all $k(k-1)$ off-diagonal $e_{ij}$, and the circuit spends
about $k^2$ multiplications on $c^\ast$. Because $k^2 = 17689$ for $k = 133$
is too much for one circuit, the book introduces the two-layer reduction:
groups of $7$, then $19$ groups, for $NM^2 + N^2 - N + 3 = 1276$ constraints.
This is split across the `inner_collapse` and `outer_collapse` circuits and
costs two rounds of challenges $(\mu,\nu)$, $(\mu',\nu')$.

Commitment folding does not constrain the weights. Ragu replaces the
in-circuit MSM by a spot check of $a^\ast(\beta) = \sum_i \lambda_i a_i(\beta)$
at a fresh $\beta$, landing in $\mathcal{R}_{\mathsf{pcs}}$. So *any*
field-valued weights computable in circuit can be used. This is the freedom
exploited below.

---

## 5. a specialised fold for the revdot relation

### 5.1 the design space

Fix $k$ claims $(\mathbf{a}_i, \mathbf{b}_i, c_i)$ and weights
$\lambda_i, \eta_i \in \mathbb{F}[\boldsymbol{\chi}]$, polynomials (or Laurent
polynomials) in verifier challenges $\boldsymbol{\chi}$. Write
$\mathbf{a}(\boldsymbol\chi) = \sum_i \lambda_i \mathbf{a}_i$ and
$\mathbf{b}(\boldsymbol\chi) = \sum_j \eta_j \mathbf{b}_j$. By bilinearity,

$$
G(\boldsymbol\chi) := \mathrm{revdot}(\mathbf{a}(\boldsymbol\chi), \mathbf{b}(\boldsymbol\chi))
= \sum_{i,j} \lambda_i \eta_j\, e_{ij}.
\tag{5.1}
$$

This is Proposition 3.1 for a bilinear form folded $k$ ways at once: the
off-diagonal part of (5.1) is the reduced $k$-fold coproduct. A fold is
specified by what the prover sends about $G$ before $\boldsymbol\chi$ is
drawn, and by how the verifier computes $c^\ast = G(\boldsymbol\chi)$ from
that message and the $c_i$. Soundness needs one thing: the claimed $G$ and the
true $G$ are low-degree in $\boldsymbol\chi$, and they must differ as
polynomials whenever some $e_{ii} \ne c_i$.

### 5.2 monomial weights: an additive-combinatorics problem

Take one challenge $\rho$ and monomial weights $\lambda_i = \rho^{s_i}$,
$\eta_j = \rho^{t_j}$ (multivariate monomials reduce to this through a Freiman
isomorphism $\mathbb{Z}^m \to \mathbb{Z}$). Then
$G(\rho) = \sum_{i,j} \rho^{s_i + t_j} e_{ij}$. The prover sends, for each
off-diagonal exponent $m$, the value $g_m = \sum_{s_i + t_j = m,\ i \ne j} e_{ij}$.

> **Proposition 5.1.** The fold is sound (error at most
> $\deg G / |\mathbb{F}|$) for every choice of claims if and only if the
> diagonal sums are *uniquely represented*: $s_i + t_j = s_l + t_l$ implies
> $i = j = l$. In the symmetric case $s = t = P$, this holds if and only if
> $P$ contains no 3-term arithmetic progression.

*Proof sketch.* If the condition holds, the difference between the true and
the claimed $G$ has coefficient $e_{ll} - c_l$ at the exponent $s_l + t_l$,
and no off-diagonal value can cancel it. Conversely, if
$s_i + t_j = s_l + t_l$ with $(i,j) \ne (l,l)$, the prover adds $\delta$ to
$c_l$ and subtracts $\delta$ from $g_{s_l+t_l}$. The claimed $G$ is
unchanged, so the verifier accepts a false claim. In the symmetric case,
$p_i + p_j = 2p_l$ with $i \ne j$ is exactly a 3-AP $(p_i, p_l, p_j)$. $\square$

`scripts/fold_check.py` runs the attack: it is rejected for Ragu's weights
and for 3-AP-free $P$, and accepted (a forgery) for $P = \{0,1,2\}$.

Ragu's scheme is the corner of this design space where *all* $k^2$ sums are
distinct, so no off-diagonal values merge: $k(k-1)$ cross terms. Symmetric
weights merge $(i,j)$ with $(j,i)$, giving $k(k-1)/2$; the two-challenge
weights $\mu^i\nu^{i^2}$ already achieve this, by strict convexity. A
3-AP-free $P$ also merges every pair with the same sum. The verifier then
evaluates a polynomial of degree $2\max P$, and the prover sends
$|P+P| - k$ values. The shortest 3-AP-free sets are OEIS A065825;
`scripts/ap3_search.c` recomputes them exactly up to $k = 27$, matching the
OEIS terms:

| $k$ | $\max P$ | $\lvert P+P\rvert - k$ (sent) | Ragu $k(k-1)$ | an optimal $P$ |
|---|---|---|---|---|
| 3 | 3 | 3 | 6 | $0,1,3$ |
| 7 | 12 | 16 | 42 | $0,1,3,4,9,10,12$ |
| 8 | 13 | 19 | 56 | $0,1,3,4,9,10,12,13$ |
| 16 | 40 | 65 | 240 | $P_8 \cup (27 + P_8)$, $P_8$ the row above |
| 19 | 57 | 88 | 342 | see `out/ap3_search.txt` |
| 27 | 99 | 163 | 702 | see `out/ap3_search.txt` |

Asymptotically, Behrend's construction [Beh46] gives 3-AP-free sets of size
$N e^{-O(\sqrt{\log N})}$ in $[N]$, so $\max P \le k\, e^{O(\sqrt{\log k})}$.
The Kelley-Meka theorem [KM23] says that any subset of $[N]$ of density at
least $2^{-O((\log N)^\beta)}$, for some $\beta > 0$, contains a 3-AP; hence
$\max P \ge k\, 2^{\Omega((\log k)^\beta)}$, which is superlinear. Monomial
weights therefore cost $k^{1+o(1)}$ cross terms and verifier work, never
$O(k)$. *The obstruction is the monomial basis itself.* The diagonal claims
are forced to be coefficients of $G$, and coefficients collide.

### 5.3 Lagrange weights: the optimal fold

Change basis: let the claims be the *values* of $G$ at $k$ fixed points
rather than its coefficients. Fix distinct $\omega_0, \dots, \omega_{k-1} \in \mathbb{F}$,
let $L_i$ be the Lagrange basis, and $Z(X) = \prod_i (X - \omega_i)$. Put
$\lambda_i = \eta_i = L_i(\gamma)$. Then

$$
G(X) = \mathrm{revdot}\Big(\sum_i L_i(X)\mathbf{a}_i,\ \sum_j L_j(X)\mathbf{b}_j\Big),
\qquad \deg G \le 2(k-1),
\qquad G(\omega_i) = e_{ii}.
$$

Let $I(X)$ interpolate the claimed $c_i$ on the $\omega_i$. If every claim is
true, $Z$ divides $G - I$. The prover sends the $k-1$ coefficients of
$K = (G - I)/Z$ (degree at most $k-2$). The verifier draws $\gamma$ and
outputs the single claim

$$
\Big(\sum_i L_i(\gamma)\bar A_i,\ \sum_i L_i(\gamma)\bar B_i,\ c^\ast = I(\gamma) + Z(\gamma)K(\gamma)\Big).
\tag{5.2}
$$

This is ProtoGalaxy's fold [EG23] specialised to the degree-2 relation
$\mathcal{R}_{\mathsf{rdp}}$. Ragu's revdot claims carry no "$F(\alpha)$"
term because there is no running error vector, only the scalars $c_i$.

> **Proposition 5.2.** The fold (5.2) is complete. If some
> $\mathrm{revdot}(\mathbf{a}_l, \mathbf{b}_l) \ne c_l$, it accepts with
> probability at most $2(k-1)/|\mathbb{F}|$ over $\gamma$, for every prover
> message $K$.

*Proof.* The true $G$ satisfies $G(\omega_l) = e_{ll} \ne c_l = (I + ZK)(\omega_l)$.
So $G - I - ZK$ is a nonzero polynomial of degree at most $2(k-1)$, fixed
before $\gamma$, and Schwartz-Zippel applies. $\square$

*Remark (challenges in the domain).* If $\gamma = \omega_l$, the fold outputs
claim $l$ unchanged and drops the others. This case is already one of the at
most $2(k-1)$ roots counted in Proposition 5.2, so soundness does not require
excluding it. The verifier still rejects $\gamma \in \{\omega_i\}$, because the
barycentric formula for $L_i(\gamma)$ divides by $\gamma - \omega_i$.

**Knowledge soundness.** In the split-accumulation syntax of [BCLMS21], the
accumulation prover outputs $K$ and the folded witness, the accumulation
verifier recomputes $(\bar A^\ast, \bar B^\ast, c^\ast)$ from (5.2), and the
decider checks $\mathcal{R}_{\mathsf{rdp}}$ on the output. Knowledge soundness
of the accumulation scheme is the following special-soundness property of the
one-round public-coin protocol "prover sends $K$, verifier sends $\gamma$".

> **Proposition 5.5 ($(2k-1)$-special soundness).** Let $\mathrm{Com}$ be a
> linearly homomorphic vector commitment (Pedersen). Fix inputs
> $(\bar A_i, \bar B_i, c_i)_{i<k}$ and a prover message $K$. Given $2k-1$
> accepting transcripts with distinct challenges $\gamma_1, \dots, \gamma_{2k-1}$,
> each with a valid $\mathcal{R}_{\mathsf{rdp}}$ witness
> $(\mathbf{a}^\ast_t, \mathbf{b}^\ast_t, \rho^a_t, \rho^b_t)$ for the folded
> instance, one computes in polynomial time either valid witnesses
> $(\mathbf{a}_i, \mathbf{b}_i, \rho^a_i, \rho^b_i)$ for all $k$ inputs, or two
> distinct openings of one commitment.

*Proof.* Let $V = (L_i(\gamma_t))_{t,i<k}$ be the $k \times k$ matrix of the
first $k$ challenges. $V$ maps the values of a polynomial of degree $<k$ on
$\{\omega_i\}$ to its values on $\{\gamma_t\}_{t<k}$, so it is invertible.
Set $\mathbf{a}_i = \sum_t (V^{-1})_{it}\, \mathbf{a}^\ast_t$, and likewise for
$\rho^a_i$, $\mathbf{b}_i$, $\rho^b_i$. By homomorphism,
$\mathrm{Com}(\mathbf{a}_i; \rho^a_i) = \sum_t (V^{-1})_{it} \sum_j V_{tj} \bar A_j = \bar A_i$,
so these open the inputs. For every $t$ (including the last $k-1$),
$\mathrm{Com}(\mathbf{a}^\ast_t; \rho^a_t) = \sum_i L_i(\gamma_t) \bar A_i = \mathrm{Com}(\sum_i L_i(\gamma_t)\mathbf{a}_i; \cdot)$.
So either $\mathbf{a}^\ast_t = \mathbf{a}(\gamma_t)$ with
$\mathbf{a}(X) = \sum_i L_i(X)\mathbf{a}_i$, or we hold two openings of one
commitment; the same holds on the $b$ side. In the first case, acceptance at
$\gamma_t$ reads
$G(\gamma_t) := \mathrm{revdot}(\mathbf{a}(\gamma_t), \mathbf{b}(\gamma_t)) = (I + ZK)(\gamma_t)$
for $2k-1$ distinct points. Both sides are polynomials of degree at most
$2k-2$, so they are equal. Evaluating at $\omega_i$ gives
$\mathrm{revdot}(\mathbf{a}_i, \mathbf{b}_i) = G(\omega_i) = I(\omega_i) = c_i$. $\square$

For a one-round $m$-special-sound protocol over challenge set $\mathcal{C}$,
special soundness gives knowledge soundness with knowledge error
$(m-1)/|\mathcal{C}|$ (see [ACK21] for the general tree-special-sound
statement). The Fiat-Shamir transform of special-sound protocols loses only a
factor linear in the number $Q$ of random-oracle queries [AFK22]. Here
$m = 2k-1$, so the knowledge error is $(2k-2)/|\mathcal{C}|$; for
$k = 133$ and $|\mathcal{C}| \approx 2^{128}$ this is about $2^{-120}$.
`scripts/lagrange_fold.py` runs this extractor on $2k-1$ transcripts for
$k \in \{2, 3, 7, 19\}$ and recovers every claim.

Two composition remarks for Ragu. First, Ragu does not have the verifier
compute $\bar A^\ast$; the prover supplies it and a spot check
$a^\ast(\beta) = \sum_i L_i(\gamma) a_i(\beta)$ at a later $\beta$ ties it to
the inputs (Section 4). This adds $(4n-1)/|\mathcal{C}|$ by Schwartz-Zippel in
$\beta$, exactly as for today's weights, since that argument never used the
form of the weights. Second, the extractor needs $2k-1$ distinct field values
of $\gamma$. With endoscalar challenges this holds as long as the endoscalar
extraction map is injective on the challenge strings, which Ragu's soundness
analysis already assumes for $(\mu, \nu)$.

### 5.4 cost lives in the weight space, soundness in the basis

We now make the lower bound rigorous, and the result explains Sections 5.2 and
5.3 at once. Consider a general one-round fold:

- **(M1)** the prover sends $m \in \mathbb{F}^\ell$, then the verifier draws
  challenges $\boldsymbol\chi \in \mathcal{C}^t$ ($t \ge 1$);
- **(M2)** $\mathbf{a}^\ast = \sum_i \lambda_i(\boldsymbol\chi)\mathbf{a}_i$ and
  $\mathbf{b}^\ast = \sum_i \eta_i(\boldsymbol\chi)\mathbf{b}_i$, with
  $\lambda_i, \eta_i$ (Laurent) polynomials, and each family linearly
  independent;
- **(M3)** $c^\ast = \sum_i \alpha_i(\boldsymbol\chi) c_i + \sum_s \beta_s(\boldsymbol\chi) m_s + \delta(\boldsymbol\chi)$
  for some functions $\alpha_i, \beta_s, \delta$;
- **(M4)** $\mathcal{C}$ is larger than the degrees involved, so that
  functions on $\mathcal{C}^t$ coincide with polynomials;
- **(M5)** the vector length $L$ is at least $k$ (Ragu: $L = 4n = 8192$).

Independence in (M2) is necessary for knowledge soundness. If
$\sum_i \kappa_i \lambda_i = 0$ with $\kappa \neq 0$, replacing
$\mathbf{a}_i$ by $\mathbf{a}_i + \kappa_i \mathbf{v}$ leaves every
$\mathbf{a}^\ast$ unchanged, so no extractor can recover the inputs. Write
$U = \mathrm{span}\{\lambda_i\eta_j\}_{i,j}$,
$O = \mathrm{span}\{\lambda_i\eta_j\}_{i \neq j}$, and
$\Lambda_i = \lambda_i \eta_i$.

> **Theorem 5.3.** Under (M1)-(M5), for a perfectly complete fold:
>
> 1. if the $\Lambda_i$ are linearly dependent modulo
>    $\mathrm{span}(\beta)$, a prover makes a false claim accepted with
>    probability $1$;
> 2. hence soundness error $< 1$ forces $\ell \ge \dim \mathrm{span}(\beta) \ge \dim O$;
> 3. conversely, if the $\Lambda_i$ are independent modulo $O$, sending the
>    coordinates of the $O$-component of $G$ achieves $\ell = \dim O$, with
>    soundness error at most $\deg G / |\mathcal{C}|$.

*Proof.* By (M5), the Gram matrix $(\mathrm{revdot}(\mathbf{a}_i, \mathbf{b}_j))_{i,j}$
of honest inputs is arbitrary: take $\mathbf{a}_i$ the unit vectors and the
reversed $\mathbf{b}_j$ the columns of any matrix $E$. Completeness says that
$c^\ast = G(\boldsymbol\chi) = \sum_{i,j} \lambda_i\eta_j E_{ij}$ for every
$E$, with $c_i = E_{ii}$ and $m$ the honest message. Take $E$ with zero
diagonal: then $\sum_{i \neq j} \lambda_i \eta_j E_{ij} - \delta \in \mathrm{span}(\beta)$
for all such $E$; with $E = 0$ this gives $\delta \in \mathrm{span}(\beta)$,
hence $O \subseteq \mathrm{span}(\beta)$. Varying the diagonal alone gives
$\alpha_i - \Lambda_i \in \mathrm{span}(\beta)$.

(1) If $\sum_i \kappa_i \Lambda_i \in \mathrm{span}(\beta)$ with
$\kappa_l \neq 0$, take honest inputs, replace $c$ by $c + \kappa$, and keep
the witnesses. The change in $c^\ast$ is
$\sum_i \kappa_i \alpha_i \in \sum_i \kappa_i\Lambda_i + \mathrm{span}(\beta) = \mathrm{span}(\beta)$,
which the prover cancels by changing $m$. The output claim is the honest one,
so it is accepted, while claim $l$ is false.

(2) is $\ell \ge \dim \mathrm{span}(\beta)$ together with
$O \subseteq \mathrm{span}(\beta)$.

(3) $G = \sum_i \Lambda_i E_{ii} + o$ with $o \in O$, uniquely by
independence. The prover sends the coordinates of $o$ in a basis of $O$, and
the verifier sets $c^\ast = \sum_i \Lambda_i(\boldsymbol\chi) c_i + o(\boldsymbol\chi)$.
A false claim makes $G - c^\ast$ a nonzero polynomial, which is caught with
probability at least $1 - \deg G/|\mathcal{C}|$. $\square$

So the exact cost of a sound fold is $\dim O = \dim U - k$. The next lemma
bounds $\dim U$ from below. It is a polynomial analogue of the
Cauchy-Davenport inequality.

> **Lemma 5.4.** Let $V, W \subseteq \mathbb{F}[x_1^{\pm 1}, \dots, x_t^{\pm 1}]$
> be subspaces of dimensions $k, k'$. Then
> $\dim(V \cdot W) \ge k + k' - 1$, where $V \cdot W$ is the span of all
> products.

*Proof.* Multiplying by a monomial is injective and preserves the dimensions,
so assume polynomials. Fix a monomial order, for example lexicographic, which
is a total order on $\mathbb{Z}^t$ compatible with addition. Gaussian
elimination gives $V$ a basis with $k$ distinct leading exponents
$A = \{a_1 < \dots < a_k\}$, and likewise $B = \{b_1 < \dots < b_{k'}\}$ for
$W$. Leading exponents add under multiplication, because the polynomial ring
is a domain. The chain
$a_1 + b_1 < a_1 + b_2 < \dots < a_1 + b_{k'} < a_2 + b_{k'} < \dots < a_k + b_{k'}$
gives $k + k' - 1$ distinct leading exponents in $V \cdot W$. Polynomials with
distinct leading exponents are linearly independent. $\square$

> **Corollary 5.6 (optimality, any number of challenges).** Every fold in the
> model (M1)-(M5) with soundness error $< 1$ sends at least $k-1$ field
> elements. Lagrange weights send exactly $k-1$.

*Proof.* By Theorem 5.3, $\ell \ge \dim O \ge \dim U - k$. By (M2) and
Lemma 5.4, $\dim U \ge 2k-1$. For Lagrange weights,
$U = \mathbb{F}[\gamma]_{\le 2k-2}$ has dimension $2k-1$. $\square$

This also settles the multi-challenge question left open in the first draft:
two challenges, as Ragu uses, cannot beat $k-1$ either.

**The dichotomy, computed.** `scripts/weight_spaces.py` computes these
dimensions exactly over the Pallas field:

| scheme | $\dim U$ | $\dim O$ = min. sent | diagonal rank mod $O$ | sound |
|---|---|---|---|---|
| Ragu $\mu^{-i}, (\mu\nu)^j$ | $k^2$ | $k^2 - k$ | $k$ | yes |
| symmetric $\mu^i\nu^{i^2}$ | $k(k+1)/2$ | $k(k-1)/2$ | $k$ | yes |
| 3-AP-free monomials $\rho^{p_i}$ | $\lvert P+P\rvert$ | $\lvert P+P\rvert - k$ | $k$ | yes |
| monomials $\rho^i$, $i<k$ | $2k-1$ | $2k-3$ | $2$ | **no** |
| Lagrange $L_i(\rho)$ | $2k-1$ | $k-1$ | $k$ | yes |

(The table shows the symbolic values; the script prints them for
$k \in \{3, 7, 19\}$, e.g. $361/342$, $190/171$, $107/88$, $37/35$, $37/18$
at $k = 19$.) The last two rows span the *same* space
$\mathbb{F}[\rho]_{<k}$: the cost is a property of the space, soundness of
the basis. With monomials, $\Lambda_i = \rho^{2i}$ already lies in $O$ for
$0 < i < k-1$, because $2i = (i-1) + (i+1)$. With the Lagrange basis,
$L_i^2 \equiv L_i \pmod Z$ while $L_iL_j \equiv 0 \pmod Z$ for $i \ne j$, so
the diagonal is independent modulo $O \subseteq Z \cdot \mathbb{F}[\rho]_{\le k-2}$.

This explains Section 5.2. For monomial weights, the leading exponents
*are* the exponents, so $\dim U = |S + T|$, and Lemma 5.4 is Cauchy-Davenport
in $\mathbb{Z}^t$. Equality forces arithmetic progressions (Freiman's
$|A+B| = |A| + |B| - 1$ characterisation in $\mathbb{Z}$). For monomials,
progressions are exactly what makes the diagonal collide. Monomial schemes are
therefore caught between a small sumset and unique diagonal representation,
and 3-AP-free sets with their superlinear sumsets are the best compromise.
The Lagrange basis leaves the monomial world. It keeps the minimal space (an
"arithmetic progression" of degrees) and chooses a basis in which the
diagonal products are idempotents modulo $Z$.

### 5.5 practical properties of the Lagrange fold

- **One layer suffices.** The verifier cost is linear. With the domain
  $\{0, \dots, k-1\}$: $Z(\gamma)$ takes $k$ multiplications; the inverses
  $1/(\gamma - i)$ take one constraint each; then
  $L_i(\gamma) = Z(\gamma)\, w_i / (\gamma - i)$ with constant barycentric
  weights $w_i$; then $I(\gamma)$; then Horner for $K(\gamma)$. That is about
  $5k$ constraints, with no need for a second layer.
- **The prover gets cheaper too.** Ragu's prover computes $k^2$ revdots of
  length $4n$. The Lagrange prover extends each of the $2 \cdot 4n$
  coordinates from $k$ to $2k-1$ points (an LDE, $O(k \log k)$ each, or
  $O(k^2)$ naively on scalars) and computes $2k-1$ revdots. That is
  $O(n\,k\log k)$ field operations instead of $O(n\,k^2)$.
- **Checks.** `scripts/lagrange_fold.py` checks Proposition 5.2 over the
  Pallas scalar field for $k \in \{2, 3, 7, 19\}$. It confirms honest
  acceptance, exactly $k-1$ cross terms, and rejection of a false claim when
  the prover sends its best quotient (remainder dropped). For $k = 2$ the
  fold is Nova's single cross term, with weights $(1-\gamma, \gamma)$ in
  place of $(1, r)$.

### 5.6 cost comparison

`scripts/layer_cost.py` uses the book's own accounting (nested Horner,
$m^2 - 1$ per group of $m$, plus 2 per layer for precomputation). It
reproduces the book's figure of $1276$ for $(7, 19)$ at capacity $133$. The
symmetric schemes are costed as described in the script header.

| $k$ | scheme | layers | constraints | cross terms |
|---|---|---|---|---|
| 93 | Ragu, deployed $(7,19)$ | 2 | 1036 | 930 |
| 93 | Ragu, best $(6,16)$ | 2 | 819 | 720 |
| 93 | symmetric $\mu^i\nu^{i^2}$, $(6,16)$ | 2 | 588 | 360 |
| 93 | 3-AP-free monomials, $(4,24)$ | 2 | 362 | 253 |
| 93 | 3-AP-free monomials, $(2,4,12)$ | 3 | 254 | 152 |
| 93 | **Lagrange** | **1** | **465** | **92** |
| 133 | Ragu, deployed $(7,19)$ | 2 | 1276 | 1140 |
| 133 | 3-AP-free monomials, $(8,17)$ | 2 | 546 | 399 |
| 133 | **Lagrange** | **1** | **665** | **132** |

Three readings:

1. At equal round count, Lagrange is the clear choice: it uses one layer
   against two, with roughly half the constraints and a tenth of the cross
   terms.
2. The cross-term count is not only verifier arithmetic. The terms are witness
   wires of the `inner_error` and `outer_error` stages, they are committed and
   absorbed into the transcript, and in compression they are packed into the
   error polynomials $E_1, E_2$ that must fit in degree $D$. Going from 930 to
   92 shrinks those stages roughly tenfold.
3. 3-AP-free monomials beat Lagrange on raw constraints only with three
   layers, at the price of three challenge rounds and $1.6\times$ more cross
   terms. They need no inversions, which may matter in a setting where an
   inversion is not a single constraint.

### 5.7 what changes in Ragu

- `inner_collapse` and `outer_collapse` merge into a single fold circuit.
  The `outer_error` stage and the second challenge pair $(\mu', \nu')$
  disappear, as does the transcript split that hands sponge state through
  `outer_error` (book, `protocol/recursion/index.md`).
- The weights $L_i(\gamma)$ are general field elements. This is compatible
  with commitment folding by PCS spot check (Section 4), and with endoscalar
  challenges: $\gamma$ is an endoscalar, the $L_i(\gamma)$ are computed from
  it in-field. Soundness error is $2(k-1)/|\mathcal{C}|$ for challenge space
  $\mathcal{C}$, about $2^{-120}$ for 128-bit endoscalars and $k = 133$.
- The verifier rejects $\gamma \in \{\omega_i\}$, or uses a domain disjoint
  from the challenge space. This is for the barycentric division only;
  soundness already accounts for these values (remark after Proposition 5.2).
- The knowledge error is $(2k-2)/|\mathcal{C}|$ (Proposition 5.5), and the
  existing spot-check argument for prover-supplied $\bar A^\ast, \bar B^\ast$
  is unchanged.
- The compression path (`compress/revdot`) has the same two-layer structure,
  and the same replacement applies there: one error polynomial $K$ instead of
  $E_1, E_2$ with weight polynomials $W_1, W_2$.

These are design-level estimates. No Ragu code was changed, and the
constraint counts are a model, not a measurement of synthesised circuits.

---

### 5.8 prototype in Ragu

The fold is prototyped as the module `lagrange` in
`crates/ragu_pcd/src/internal/fold_revdot.rs` of Ragu at commit `526b0e3e`,
not wired into fuse or compress. The change ships with this note as
`prototype/lagrange-fold.patch` (the full file is `prototype/fold_revdot.rs`). It provides:

- `error_terms_with_backend`: the prover's $k-1$ coefficients of $K$. It
  evaluates $K$ at the points $k, \dots, 2k-2$ outside the domain and
  interpolates by Newton divided differences;
- `fold_claims`: the in-circuit verifier, returning $c^\ast$ and the weights
  $L_i(\gamma)$ needed to fold the $a_i, b_i$ or spot-check their
  commitments;
- `weights`, `barycentric_weights`, `fold_weighted`: native helpers, the last
  generic over `Foldable` so it also folds commitment-tracked polynomials.

Seven tests run on Ragu's own polynomial types and drivers. They check
honest acceptance for $k \in \{1,2,3,7,19\}$; rejection of a false claim;
rejection of every single-unit shift of a target into a coefficient of $K$
($k = 7$); witness-generation failure for $\gamma$ in the domain; the
Proposition 5.5 extractor; the gate count; and a head-to-head against the
deployed fold. **Measured** with Ragu's `Simulator`:

| fold | claims | gates |
|---|---|---|
| deployed two-layer `ClaimFolder`, $(7, 19)$ | 133 | 1276 |
| `lagrange::fold_claims` | 133 | 663 |
| `lagrange::fold_claims` | 93 | 463 |

`fold_claims` uses exactly $5k-2$ gates for every $k$ tested
($2, 7, 19, 93, 133$), and the deployed fold matches the book's 1276
exactly. The model of Section 5.6 is therefore exact for both schemes; its
465 for $k = 93$ included the 2 per-layer precomputation gates, which the
Lagrange verifier does not need.

## 6. further directions

1. **Evaluation claims as a fibration (our framing).** $\mathcal{R}_{\mathsf{pcs}}$
   is a family of *linear* relations indexed by the point $x$: for fixed $x$,
   $p \mapsto p(x)$ is a linear functional, and claims at the same point fold
   for free. Claims at different points live in different fibres, and the
   quotient trick (alpha batching to a fresh point $u$) is a *transport*
   between fibres. Categorically this is the Grothendieck construction of
   $x \mapsto \{\text{linear claim at } x\}$, with the quotient as cartesian
   lift. Registry consistency is the same pattern in three variables. A
   question worth asking: do the 10 registry evaluation claims per fuse step
   (Section 2.5) admit a Lagrange-style single transport?
2. **Low-rank claim families (negative result).** Many claims share stage
   polynomials ($a = \sum$ of stages), so the matrix $(e_{ij})$ factors
   through the Gram matrix of a basis. Counting distinct native rx components
   gives $2 \cdot 49 + 2 = 100$ basis polynomials against $93$ claims, so the
   factorisation does not pay at current parameters.
3. **Endoscaling claims dominate.** 50 of the 93 claims come from the 25
   endoscaling-step circuits per child. Section 3.3 explains why
   scalar-multiplication claims with varying bases do not fold for free.
   Shrinking the number of deferred group operations, for example by batching
   nested commitments before endoscaling, reduces $k$ directly, and every
   scheme above benefits.
4. **Beyond the linear model.** Corollary 5.6 settles multiple challenges
   (they cannot beat $k-1$). It leaves open folds outside (M1)-(M3): several
   rounds, weights that are not polynomial in the challenges, or a $c^\ast$
   that is nonlinear in the prover message. Whether any of these helps for a
   bilinear relation is open.
5. **Equality cases of Lemma 5.4.** In $\mathbb{Z}$, equality in
   Cauchy-Davenport forces arithmetic progressions. The analogous structure
   theorem for subspaces of $\mathbb{F}[x]$ with $\dim(V\cdot W) = 2k-1$
   (we expect $V = W = f \cdot \mathbb{F}[x]_{<k}$ up to a unit, but have not
   checked the literature) would classify all optimal weight spaces.

---

## 7. auditing the abstraction against the code

The signature: a carrier $\mathcal{R}_{\mathsf{rdp}}$, a $k$-ary operation
$\mathsf{fold}_k$, and the unit $\iota$ (a claim is its own one-element
accumulator). The laws a faithful implementation must satisfy, and their
status:

| law | statement | status |
|---|---|---|
| completeness | honest claims fold to an honest claim | tested (`fold_check.py`, `lagrange_fold.py`) |
| diagonal independence | no off-diagonal monomial equals a diagonal one | holds for Ragu's weights (all $k^2$ exponents distinct); now a stated obligation for any new weight choice |
| order independence | the folded claim's validity does not depend on claim order | holds mathematically; the code fixes a canonical interleaved order (`build`), which `inner_collapse` must reproduce for $k(y)$, an untested coupling worth a property test |
| padding | unused slots ($133 - 93$) must be trivially true claims | from reading only: padding is with zero claims; a PBT should check a padded fold equals an unpadded one |

The non-standard model to rule out, in model-theoretic terms: a weight scheme
satisfying completeness but not diagonal independence. It is precisely the
$P = \{0,1,2\}$ forgery of Section 5.2. Completeness tests alone cannot
detect it; only an adversarial test can. We recommend adding such a test to
Ragu's suite as a guard on any future change of weights.

---

## 8. limitations

- Constraint counts are a model calibrated on one book figure, not
  measurements. Real costs include stage wiring, the transcript, and padding
  to circuit boundaries.
- The lower bound (Theorem 5.3, Corollary 5.6) holds within the model
  (M1)-(M5): one prover message, polynomial weights, $c^\ast$ affine in the
  message. Section 6 lists what lies outside it.
- [EG23] could not be read in full from this environment (the ePrint PDF is
  behind a browser challenge). Its protocol shape was cross-checked against
  secondary notes. Our Propositions 5.2 and 5.5 are proved here
  independently of it, so this affects attribution only.
- The categorical statements in Section 3.1 are our framing of [KP23]'s
  composition theorems, not results from that paper.
- We did not verify the explicit exponent $\beta$ of Kelley-Meka or later
  improvements; only $\beta > 0$ is used.

---

## references

- [BC23] B. Bunz, B. Chen. *ProtoStar: Generic Efficient Accumulation/Folding
  for Special Sound Protocols.* ePrint 2023/620.
- [ACK21] T. Attema, R. Cramer, L. Kohl. *A Compressed Sigma-Protocol Theory
  for Lattices.* CRYPTO 2021, ePrint 2021/307.
- [AFK22] T. Attema, S. Fehr, M. Klooss. *Fiat-Shamir Transformation of
  Multi-Round Interactive Proofs.* TCC 2022, ePrint 2021/1377; extended in
  J. Cryptology 36(4), 2023.
- [BCCGP16] J. Bootle, A. Cerulli, P. Chaidos, J. Groth, C. Petit.
  *Efficient Zero-Knowledge Arguments for Arithmetic Circuits in the Discrete
  Log Setting.* EUROCRYPT 2016, ePrint 2016/263.
- [BCLMS21] B. Bunz, A. Chiesa, W. Lin, P. Mishra, N. Spooner.
  *Proof-Carrying Data without Succinct Arguments.* CRYPTO 2021, ePrint
  2020/1618.
- [BCMS20] B. Bunz, A. Chiesa, P. Mishra, N. Spooner. *Proof-Carrying Data
  from Accumulation Schemes.* TCC 2020, ePrint 2020/499.
- [Beh46] F. A. Behrend. *On sets of integers which contain no three terms in
  arithmetical progression.* PNAS 32 (1946), 331-332.
- [BGH19] S. Bowe, J. Grigg, D. Hopwood. *Recursive Proof Composition without
  a Trusted Setup (Halo).* ePrint 2019/1021.
- [BGLS03] D. Boneh, C. Gentry, B. Lynn, H. Shacham. *Aggregate and Verifiably
  Encrypted Signatures from Bilinear Maps.* EUROCRYPT 2003.
- [CGKN21] K. Chalkias, F. Garillot, Y. Kondi, V. Nikolaenko. *Non-interactive
  half-aggregation of EdDSA and variants of Schnorr signatures.* CT-RSA 2021,
  ePrint 2021/350.
- [CT10] A. Chiesa, E. Tromer. *Proof-Carrying Data and Hearsay Arguments
  from Signature Cards.* ICS 2010.
- [EG23] L. Eagen, A. Gabizon. *ProtoGalaxy: Efficient ProtoStar-style folding
  of multiple instances.* ePrint 2023/1106. Protocol steps cross-checked
  against A. Cube's notes, <https://arnaucube.com/blog/protogalaxy.html>
  (the ePrint PDF was not retrievable from this environment).
- [KM23] Z. Kelley, R. Meka. *Strong Bounds for 3-Progressions.*
  arXiv:2302.05537.
- [KP23] A. Kothapalli, B. Parno. *Algebraic Reductions of Knowledge.*
  CRYPTO 2023, ePrint 2022/009.
- [KST22] A. Kothapalli, S. Setty, I. Tzialla. *Nova: Recursive
  Zero-Knowledge Arguments from Folding Schemes.* CRYPTO 2022, ePrint
  2021/370.
- [Wat79] W. C. Waterhouse. *Introduction to Affine Group Schemes.* GTM 66,
  Springer, 1979.
- [Wil24] D. Willems. *Behind Nova: cross-terms computation for high degree
  gates.* HackMD, 2024, <https://hackmd.io/qq_Awc1AR3ywzkruE4Wq9Q>.
- OEIS A065825, *Smallest k such that n numbers may be picked in {1,...,k}
  with no three terms in arithmetic progression*, <https://oeis.org/A065825>.
- The Ragu book, `book/src/protocol/` at commit `526b0e3e`.

## appendix A. reproduction

See `scripts/README.md`. Every number in Sections 4 and 5 comes from one of:
`fold_check.py` (Proposition 5.1 and the attack), `ap3_search.c` (the table
in 5.2), `lagrange_fold.py` (Propositions 5.2 and 5.5, including the
extractor), `weight_spaces.py` (Theorem 5.3 and the table in 5.4),
`layer_cost.py` (the table in 5.6). Outputs are committed under `scripts/out/`.
