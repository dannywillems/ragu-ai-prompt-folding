//! Operations and utilities for reasoning about folded revdot claims.
//!
//! Folding combines many revdot claims into a single claim using verifier
//! challenges. The off-diagonal products ($i \neq j$) form the error terms
//! that must also be enforced to preserve soundness.

use core::{borrow::Borrow, iter, marker::PhantomData};

use ragu_circuits::{
    horner::Horner,
    polynomials::{Rank, sparse},
};
use ragu_core::{Result, drivers::Driver};
use ragu_primitives::{
    Element,
    io::Buffer,
    vec::{CollectFixed, ConstLen, FixedVec, Len},
};
use udon::field::Field;

/// The two operations a Horner-style fold needs: scale all components, then
/// add another element in.
pub trait Foldable<F: Field>: Default + Clone {
    fn fold_scale(&mut self, by: F);
    fn fold_add_assign(&mut self, other: &Self);
}

impl<F: Field, R: Rank> Foldable<F> for sparse::Polynomial<F, R> {
    fn fold_scale(&mut self, by: F) {
        self.scale(by);
    }
    fn fold_add_assign(&mut self, other: &Self) {
        self.add_assign(other);
    }
}

/// Generic Horner fold over any [`Foldable`] type.
pub(crate) fn fold<T: Foldable<F>, F: Field>(
    items: impl IntoIterator<Item = impl Borrow<T>>,
    scale_factor: F,
) -> T {
    items.into_iter().fold(T::default(), |mut acc, item| {
        acc.fold_scale(scale_factor);
        acc.fold_add_assign(item.borrow());
        acc
    })
}

/// The parameters $(m, n)$ that dictate the multi-layer revdot reduction.
///
/// The first layer involves $n$ instances of size-$m$ revdot reductions, and
/// the second layer reduces these into a single revdot using a single size-$n$
/// revdot reduction.
///
/// The parameters here collapse as much as $m \cdot n$ claims into a single
/// claim using roughly $f(m, n) = nm^2 + n^2 - n + 3$ gates
/// (using nested Horner evaluation).
pub trait Parameters: 'static + Send + Sync + Copy + Default {
    type NumGroups: Len;
    type GroupSize: Len;
}

/// Represents the number of "error" terms produced during a folding operation
/// of many `revdot` claims.
///
/// Given $m$ claims being folded, the error terms are defined as the
/// off-diagonal entries of an $m \times m$ matrix, which by definition has $m *
/// (m - 1)$ terms.
///
pub struct NumErrorTerms<L: Len>(PhantomData<L>);

impl<L: Len> Len for NumErrorTerms<L> {
    fn len() -> usize {
        let n = L::len();
        // n * (n - 1) = n² - n
        n * n - n
    }
}

/// Returns an iterator over off-diagonal (i, j) pairs where i != j.
fn off_diagonal_pairs(n: usize) -> impl Iterator<Item = (usize, usize)> {
    (0..n).flat_map(move |i| (0..n).filter_map(move |j| (i != j).then_some((i, j))))
}

/// Reduction step for polynomials in the first layer of revdot folding.
///
/// This takes a slice of polynomials (less than or equal to `GroupSize * NumGroups`
/// in length) and, assuming absent polynomials are zero, folds each group of
/// `GroupSize` polynomials into one polynomial using the provided scale factor.
///
/// # Panics
///
/// Panics if `source.len()` exceeds `GroupSize * NumGroups`, which would cause
/// silent truncation.
pub fn fold_inner<T: Foldable<F>, F: Field, P: Parameters>(
    source: &[impl Borrow<T>],
    scale_factor: F,
) -> FixedVec<T, P::NumGroups> {
    assert!(
        source.len() <= P::GroupSize::len() * P::NumGroups::len(),
        "source length {} exceeds GroupSize*NumGroups = {}",
        source.len(),
        P::GroupSize::len() * P::NumGroups::len()
    );

    let m = P::GroupSize::len();
    source
        .chunks(m)
        .map(|chunk| {
            fold(
                chunk
                    .iter()
                    .map(|p| p.borrow().clone())
                    .chain(iter::repeat_with(T::default).take(m - chunk.len())),
                scale_factor,
            )
        })
        .chain(iter::repeat_with(T::default))
        .take(P::NumGroups::len())
        .collect_fixed()
        .expect("iterator produces exactly NumGroups elements")
}

/// Reduction step for polynomials in the second layer of revdot folding.
///
/// This takes a length-`NumGroups` vector of polynomials and performs a simple
/// folding procedure with the scaling factor. This function exists mainly to
/// complement `fold_inner` as its behavior is trivial.
pub fn fold_outer<T: Foldable<F>, F: Field, P: Parameters>(
    source: FixedVec<T, P::NumGroups>,
    scale_factor: F,
) -> T {
    fold(source.iter(), scale_factor)
}

/// Error computation for revdot folding.
///
/// This computes off-diagonal revdot products for each group of `Inner`
/// polynomials, producing `Outer` groups of error terms.
fn compute_errors_impl<B: ragu_backend::Backend, F: Field, R: Rank, Outer: Len, Inner: Len>(
    a: &[impl Borrow<sparse::Polynomial<F, R>>],
    b: &[impl Borrow<sparse::Polynomial<F, R>>],
) -> FixedVec<FixedVec<F, NumErrorTerms<Inner>>, Outer> {
    assert_eq!(a.len(), b.len(), "a and b must have same length");
    assert!(
        a.len() <= Outer::len() * Inner::len(),
        "input length {} exceeds Outer*Inner = {}",
        a.len(),
        Outer::len() * Inner::len()
    );

    // Iterate over `Inner::len()`-sized chunks of a and b as pairs.
    a.chunks(Inner::len())
        .zip(b.chunks(Inner::len()))
        // For each chunk, compute off-diagonal revdot products.
        .map(|(a_chunk, b_chunk)| {
            // Computed using the cartesian product of indices, filtering out
            // diagonal entries.
            off_diagonal_pairs(Inner::len())
                // Missing entries are zero polynomials, producing zero revdot products.
                .map(|(i, j)| {
                    a_chunk
                        .get(i)
                        .zip(b_chunk.get(j))
                        .map_or(F::ZERO, |(l, r)| B::sparse_revdot(l.borrow(), r.borrow()))
                })
                .collect_fixed()
                .expect("lengths are correct")
        })
        // ... and missing pairs produce zeroed error term groups.
        .chain(iter::repeat_with(|| FixedVec::from_fn(|_| F::ZERO)))
        .take(Outer::len())
        .collect_fixed()
        .expect("lengths are correct")
}

/// Inner error terms: `NumGroups` groups of `GroupSize`*(`GroupSize`-1) off-diagonal revdot products.
#[cfg(test)]
pub fn inner_error_terms<F: Field, R: Rank, P: Parameters>(
    a: &[impl Borrow<sparse::Polynomial<F, R>>],
    b: &[impl Borrow<sparse::Polynomial<F, R>>],
) -> FixedVec<FixedVec<F, NumErrorTerms<P::GroupSize>>, P::NumGroups> {
    inner_error_terms_with_backend::<ragu_backend::ReferenceBackend, F, R, P>(a, b)
}

/// Computes inner error terms through the selected backend.
pub fn inner_error_terms_with_backend<
    B: ragu_backend::Backend,
    F: Field,
    R: Rank,
    P: Parameters,
>(
    a: &[impl Borrow<sparse::Polynomial<F, R>>],
    b: &[impl Borrow<sparse::Polynomial<F, R>>],
) -> FixedVec<FixedVec<F, NumErrorTerms<P::GroupSize>>, P::NumGroups> {
    compute_errors_impl::<B, F, R, P::NumGroups, P::GroupSize>(a, b)
}

/// Outer error terms: `NumGroups`*(`NumGroups`-1) off-diagonal revdot products.
#[cfg(test)]
pub fn outer_error_terms<F: Field, R: Rank, P: Parameters>(
    a: &[impl Borrow<sparse::Polynomial<F, R>>],
    b: &[impl Borrow<sparse::Polynomial<F, R>>],
) -> FixedVec<F, NumErrorTerms<P::NumGroups>> {
    outer_error_terms_with_backend::<ragu_backend::ReferenceBackend, F, R, P>(a, b)
}

/// Computes outer error terms through the selected backend.
pub fn outer_error_terms_with_backend<
    B: ragu_backend::Backend,
    F: Field,
    R: Rank,
    P: Parameters,
>(
    a: &[impl Borrow<sparse::Polynomial<F, R>>],
    b: &[impl Borrow<sparse::Polynomial<F, R>>],
) -> FixedVec<F, NumErrorTerms<P::NumGroups>> {
    compute_errors_impl::<B, F, R, ConstLen<1>, P::NumGroups>(a, b)
        .into_iter()
        .next()
        .expect("Outer produces exactly one group")
}

/// Precomputed folding context for computing revdot claim `c`.
///
/// Computing `mu_nu` and `mu_inv` once and reusing across multiple calls
/// saves 2*(N-1) multiplications in the two-layer reduction.
pub struct ClaimFolder<'dr, D: Driver<'dr>> {
    mu_nu: Element<'dr, D>,
    mu_inv: Element<'dr, D>,
}

impl<'dr, D: Driver<'dr>> ClaimFolder<'dr, D> {
    /// Create a folding context from mu and nu.
    pub fn new(dr: &mut D, mu: &Element<'dr, D>, nu: &Element<'dr, D>) -> Result<Self> {
        let mu_nu = mu.mul(dr, nu)?;
        let mu_inv = mu.invert(dr)?;
        Ok(Self { mu_nu, mu_inv })
    }

    /// Compute folded revdot claim `c` for layer 1 (`GroupSize`-element reduction).
    pub fn fold_inner<P: Parameters>(
        &self,
        dr: &mut D,
        error_terms: &FixedVec<Element<'dr, D>, NumErrorTerms<P::GroupSize>>,
        ky_values: &FixedVec<Element<'dr, D>, P::GroupSize>,
    ) -> Result<Element<'dr, D>> {
        fold_products_impl::<_, P::GroupSize>(dr, &self.mu_nu, &self.mu_inv, error_terms, ky_values)
    }

    /// Compute folded revdot claim `c` for layer 2 (`NumGroups`-element reduction).
    pub fn fold_outer<P: Parameters>(
        &self,
        dr: &mut D,
        error_terms: &FixedVec<Element<'dr, D>, NumErrorTerms<P::NumGroups>>,
        ky_values: &FixedVec<Element<'dr, D>, P::NumGroups>,
    ) -> Result<Element<'dr, D>> {
        fold_products_impl::<_, P::NumGroups>(dr, &self.mu_nu, &self.mu_inv, error_terms, ky_values)
    }
}

/// Core folding computation using precomputed mu_nu and mu_inv.
fn fold_products_impl<'dr, D: Driver<'dr>, S: Len>(
    dr: &mut D,
    mu_nu: &Element<'dr, D>,
    mu_inv: &Element<'dr, D>,
    error_terms: &FixedVec<Element<'dr, D>, NumErrorTerms<S>>,
    ky_values: &FixedVec<Element<'dr, D>, S>,
) -> Result<Element<'dr, D>> {
    let mut error_terms = error_terms.iter();
    let mut ky_values = ky_values.iter();

    let mut outer_horner = Horner::new(mu_inv);

    let n = S::len();
    for i in 0..n {
        let mut inner_horner = Horner::new(mu_nu);
        for j in 0..n {
            let term = if i == j {
                ky_values.next().expect("should exist")
            } else {
                error_terms.next().expect("should exist")
            };
            inner_horner.write(dr, term)?;
        }
        let row_result = inner_horner.finish(dr);
        outer_horner.write(dr, &row_result)?;
    }

    Ok(outer_horner.finish(dr))
}

/// Folds scalar evaluations through both layers, padding missing sources with zero.
///
/// # Panics
///
/// Panics if `sources.len()` exceeds `GroupSize * NumGroups`.
pub fn fold_two_layer<'dr, D: Driver<'dr>, P: Parameters>(
    dr: &mut D,
    sources: &[Element<'dr, D>],
    layer1_scale: &Element<'dr, D>,
    layer2_scale: &Element<'dr, D>,
) -> Result<Element<'dr, D>> {
    assert!(
        sources.len() <= P::GroupSize::len() * P::NumGroups::len(),
        "source length {} exceeds GroupSize*NumGroups = {}",
        sources.len(),
        P::GroupSize::len() * P::NumGroups::len()
    );

    let m = P::GroupSize::len();
    let mut results = alloc::vec::Vec::with_capacity(P::NumGroups::len());

    let zero = Element::zero(dr);
    for chunk in sources.chunks(m) {
        results.push(Element::fold(
            dr,
            chunk.iter().chain(iter::repeat_n(&zero, m - chunk.len())),
            layer1_scale,
        )?);
    }

    while results.len() < P::NumGroups::len() {
        results.push(zero.clone());
    }

    Element::fold(dr, results.iter(), layer2_scale)
}

/// Prototype: single-layer Lagrange folding of revdot claims.
///
/// This is an alternative to the two-layer monomial reduction above
/// ([`ClaimFolder`], [`fold_inner`], [`fold_outer`]). It is **not wired into
/// the fuse or compress pipelines**; it exists to measure cost and check
/// correctness.
///
/// # Construction
///
/// Fix the domain $\{0, 1, \ldots, k-1\}$ with Lagrange basis $L_i$ and
/// vanishing polynomial $Z(X) = \prod_i (X - i)$. For claims
/// $\mathrm{revdot}(a_i, b_i) = c_i$ put $a(X) = \sum_i L_i(X) a_i$,
/// $b(X) = \sum_i L_i(X) b_i$ and $G(X) = \mathrm{revdot}(a(X), b(X))$, a
/// polynomial of degree at most $2(k-1)$ with $G(i) = c_i$ when every claim
/// holds. Let $I(X)$ interpolate the $c_i$. The prover sends the $k-1$
/// coefficients of $K = (G - I) / Z$, and after the challenge $\gamma$ the
/// folded claim is
///
/// $$
/// \Big(\sum_i L_i(\gamma) a_i,\ \sum_i L_i(\gamma) b_i,\
///   I(\gamma) + Z(\gamma) K(\gamma)\Big).
/// $$
///
/// This is the ProtoGalaxy fold (Eagen and Gabizon, ePrint 2023/1106)
/// specialised to the bilinear revdot relation.
///
/// # Soundness
///
/// If some $\mathrm{revdot}(a_l, b_l) \neq c_l$ then $G - I - ZK$ is a
/// nonzero polynomial of degree at most $2(k-1)$ fixed before $\gamma$, so a
/// false claim survives with probability at most $2(k-1)/|\mathcal{C}|$ over
/// the challenge set $\mathcal{C}$. The fold is $(2k-1)$-special sound: from
/// $2k-1$ accepting transcripts sharing $K$, the inputs are recovered by
/// inverting the matrix $(L_i(\gamma_t))$. A $\gamma$ in the domain makes
/// $\gamma - i$ non-invertible, so the in-circuit inversion rejects it.
///
/// # Cost
///
/// $k - 1$ error terms instead of $k(k-1)$, and $5k - 2$ multiplication gates
/// in [`lagrange::fold_claims`], in one layer.
#[cfg_attr(not(test), allow(dead_code))]
pub mod lagrange {
    use alloc::vec::Vec;
    use core::borrow::Borrow;

    use ragu_circuits::{
        horner::Horner,
        polynomials::{Rank, sparse},
    };
    use ragu_core::{
        Result,
        drivers::{Coeff, Driver},
    };
    use ragu_primitives::{Element, io::Buffer};
    use udon::field::Field;

    use super::Foldable;

    fn point<F: Field>(i: usize) -> F {
        F::from(i as u64)
    }

    /// Barycentric weights $w_i = \prod_{j \neq i} (i - j)^{-1}$ of the domain
    /// $\{0, \ldots, k-1\}$, so that $L_i(x) = Z(x)\, w_i / (x - i)$.
    pub fn barycentric_weights<F: Field>(k: usize) -> Vec<F> {
        (0..k)
            .map(|i| {
                (0..k)
                    .filter(|&j| j != i)
                    .map(|j| point::<F>(i) - point::<F>(j))
                    .product::<F>()
                    .invert()
                    .expect("domain points are distinct")
            })
            .collect()
    }

    /// The Lagrange weights $L_i(x)$ for $i < k$, or `None` if $x$ is a domain
    /// point.
    pub fn weights<F: Field>(k: usize, x: F) -> Option<Vec<F>> {
        let diffs: Vec<F> = (0..k).map(|i| x - point::<F>(i)).collect();
        let z: F = diffs.iter().product();
        let w = barycentric_weights::<F>(k);
        diffs
            .iter()
            .zip(&w)
            .map(|(d, wi)| d.invert().map(|inv| z * wi * inv))
            .collect()
    }

    /// $Z(x) = \prod_{i<k} (x - i)$.
    fn vanishing<F: Field>(k: usize, x: F) -> F {
        (0..k).map(|i| x - point::<F>(i)).product()
    }

    /// Weighted sum $\sum_i w_i \cdot \mathrm{item}_i$ of [`Foldable`] values
    /// (polynomials, or polynomials tracked with their commitments).
    pub fn fold_weighted<T: Foldable<F>, F: Field>(items: &[impl Borrow<T>], weights: &[F]) -> T {
        assert_eq!(items.len(), weights.len(), "one weight per item");
        items
            .iter()
            .zip(weights)
            .fold(T::default(), |mut acc, (item, w)| {
                let mut term = item.borrow().clone();
                term.fold_scale(*w);
                acc.fold_add_assign(&term);
                acc
            })
    }

    /// Monomial coefficients (ascending) of the polynomial of degree
    /// `< xs.len()` through `(xs[t], ys[t])`, via Newton divided differences.
    fn interpolate<F: Field>(xs: &[F], ys: &[F]) -> Vec<F> {
        let n = xs.len();
        let mut dd = ys.to_vec();
        for level in 1..n {
            for t in (level..n).rev() {
                let den = (xs[t] - xs[t - level])
                    .invert()
                    .expect("interpolation points are distinct");
                dd[t] = (dd[t] - dd[t - 1]) * den;
            }
        }
        // Expand the Newton form from the innermost term outwards.
        let mut coeffs = alloc::vec![F::ZERO; n];
        for t in (0..n).rev() {
            // coeffs <- coeffs * (X - xs[t]) + dd[t]
            let mut next = alloc::vec![F::ZERO; n];
            for (deg, c) in coeffs.iter().enumerate() {
                if deg + 1 < n {
                    next[deg + 1] += *c;
                }
                next[deg] -= *c * xs[t];
            }
            next[0] += dd[t];
            coeffs = next;
        }
        coeffs
    }

    /// Prover side: the $k-1$ coefficients (ascending) of
    /// $K = (G - I) / Z$, where `ky` are the claimed targets $c_i$.
    ///
    /// $K$ is evaluated at the $k-1$ points $k, \ldots, 2k-2$ outside the
    /// domain, as $(G(t) - I(t)) / Z(t)$, and interpolated. This uses $k-1$
    /// weighted sums of the $a_i$ and $b_i$ and $k-1$ revdot products; an LDE
    /// over a two-adic domain would bring the polynomial work to
    /// $O(k \log k)$ per coefficient.
    ///
    /// If every claim holds, the result satisfies $G = I + ZK$. If not, it
    /// is still a polynomial of degree at most $k-2$, and the identity fails
    /// at the domain point of the false claim.
    pub fn error_terms_with_backend<B: ragu_backend::Backend, F: Field, R: Rank>(
        a: &[impl Borrow<sparse::Polynomial<F, R>>],
        b: &[impl Borrow<sparse::Polynomial<F, R>>],
        ky: &[F],
    ) -> Vec<F> {
        let k = ky.len();
        assert!(k >= 1, "at least one claim");
        assert_eq!(a.len(), k, "one a polynomial per claim");
        assert_eq!(b.len(), k, "one b polynomial per claim");
        let xs: Vec<F> = (k..2 * k - 1).map(point::<F>).collect();
        let ys: Vec<F> = xs
            .iter()
            .map(|&x| {
                let w = weights::<F>(k, x).expect("x is outside the domain");
                let ax: sparse::Polynomial<F, R> = fold_weighted(a, &w);
                let bx: sparse::Polynomial<F, R> = fold_weighted(b, &w);
                let g = B::sparse_revdot(&ax, &bx);
                let i: F = w.iter().zip(ky).map(|(l, c)| *l * c).sum();
                (g - i)
                    * vanishing::<F>(k, x)
                        .invert()
                        .expect("x is outside the domain")
            })
            .collect();
        interpolate(&xs, &ys)
    }

    /// [`error_terms_with_backend`] with the reference backend.
    #[cfg(test)]
    pub fn error_terms<F: Field, R: Rank>(
        a: &[impl Borrow<sparse::Polynomial<F, R>>],
        b: &[impl Borrow<sparse::Polynomial<F, R>>],
        ky: &[F],
    ) -> Vec<F> {
        error_terms_with_backend::<ragu_backend::ReferenceBackend, F, R>(a, b, ky)
    }

    /// Verifier side (in circuit): the folded target $c^\ast$ and the weights
    /// $L_i(\gamma)$, which the caller needs to fold the $a_i, b_i$ (or to
    /// spot-check their commitments).
    ///
    /// Gates: $k-1$ for $Z(\gamma)$, $k$ inversions, $k$ for the $L_i$, $k$ for
    /// $I(\gamma)$, $k-2$ for Horner on $K$, and $1$ for $Z(\gamma) K(\gamma)$:
    /// $5k - 2$ in total.
    ///
    /// # Errors
    ///
    /// Witness generation fails if $\gamma$ is a domain point, since
    /// $\gamma - i$ then has no inverse.
    ///
    /// # Panics
    ///
    /// Panics if `ky_values` is empty or `error_coeffs.len() != k - 1`.
    pub fn fold_claims<'dr, D: Driver<'dr>>(
        dr: &mut D,
        gamma: &Element<'dr, D>,
        error_coeffs: &[Element<'dr, D>],
        ky_values: &[Element<'dr, D>],
    ) -> Result<(Element<'dr, D>, Vec<Element<'dr, D>>)> {
        let k = ky_values.len();
        assert!(k >= 1, "at least one claim");
        assert_eq!(error_coeffs.len(), k - 1, "K has k - 1 coefficients");

        let diffs: Vec<Element<'dr, D>> = (0..k)
            .map(|i| {
                let c = Element::constant(dr, point::<D::F>(i));
                gamma.sub(dr, &c)
            })
            .collect();

        let mut z = diffs[0].clone();
        for d in &diffs[1..] {
            z = z.mul(dr, d)?;
        }

        let w = barycentric_weights::<D::F>(k);
        let mut lagrange = Vec::with_capacity(k);
        for (d, wi) in diffs.iter().zip(w) {
            let inv = d.invert(dr)?;
            lagrange.push(z.mul(dr, &inv)?.scale(dr, Coeff::Arbitrary(wi)));
        }

        let mut i_gamma = Element::zero(dr);
        for (l, c) in lagrange.iter().zip(ky_values) {
            let term = l.mul(dr, c)?;
            i_gamma = i_gamma.add(dr, &term);
        }

        let mut horner = Horner::new(gamma);
        for coeff in error_coeffs.iter().rev() {
            horner.write(dr, coeff)?;
        }
        let k_gamma = horner.finish(dr);
        let zk = z.mul(dr, &k_gamma)?;

        Ok((i_gamma.add(dr, &zk), lagrange))
    }

    #[cfg(test)]
    mod tests {
        use alloc::vec::Vec;

        use ragu_circuits::polynomials::{TestRank, sparse};
        use ragu_core::{drivers::emulator::Emulator, maybe::Maybe, pasta::Fp};
        use ragu_primitives::{Element, Simulator};
        use rand::{Rng, SeedableRng, rngs::StdRng};
        use udon::field::Field;

        use super::*;

        type Poly = sparse::Polynomial<Fp, TestRank>;

        fn rand_fp(rng: &mut StdRng) -> Fp {
            Fp::random(|bytes| rng.fill_bytes(bytes))
        }

        fn claims(rng: &mut StdRng, k: usize) -> (Vec<Poly>, Vec<Poly>, Vec<Fp>) {
            let a: Vec<Poly> = (0..k).map(|_| Poly::random(rng)).collect();
            let b: Vec<Poly> = (0..k).map(|_| Poly::random(rng)).collect();
            let c = a.iter().zip(&b).map(|(x, y)| x.revdot(y)).collect();
            (a, b, c)
        }

        /// Runs the verifier in the emulator; returns (c*, weights).
        fn verify(gamma: Fp, coeffs: &[Fp], ky: &[Fp]) -> Result<(Fp, Vec<Fp>)> {
            let dr = &mut Emulator::execute();
            let g = Element::constant(dr, gamma);
            let e: Vec<_> = coeffs.iter().map(|&v| Element::constant(dr, v)).collect();
            let c: Vec<_> = ky.iter().map(|&v| Element::constant(dr, v)).collect();
            let (cstar, w) = fold_claims(dr, &g, &e, &c)?;
            Ok((
                *cstar.value().take(),
                w.iter().map(|x| *x.value().take()).collect(),
            ))
        }

        #[test]
        fn honest_fold_is_accepted() -> Result<()> {
            let mut rng = StdRng::seed_from_u64(1);
            for k in [1, 2, 3, 7, 19] {
                let (a, b, c) = claims(&mut rng, k);
                let coeffs = error_terms(&a, &b, &c);
                assert_eq!(coeffs.len(), k - 1);

                let gamma = rand_fp(&mut rng);
                let (cstar, w) = verify(gamma, &coeffs, &c)?;
                assert_eq!(Some(w.clone()), weights::<Fp>(k, gamma));

                let astar: Poly = fold_weighted(&a, &w);
                let bstar: Poly = fold_weighted(&b, &w);
                assert_eq!(astar.revdot(&bstar), cstar, "k = {k}");
            }
            Ok(())
        }

        #[test]
        fn false_claim_is_rejected() -> Result<()> {
            let mut rng = StdRng::seed_from_u64(2);
            for k in [2, 3, 7, 19] {
                let (a, b, mut c) = claims(&mut rng, k);
                c[k / 2] += Fp::ONE;
                // The prover's best message: the quotient for the false
                // targets, which no longer makes G - I divisible by Z.
                let coeffs = error_terms(&a, &b, &c);
                let gamma = rand_fp(&mut rng);
                let (cstar, w) = verify(gamma, &coeffs, &c)?;
                let astar: Poly = fold_weighted(&a, &w);
                let bstar: Poly = fold_weighted(&b, &w);
                assert_ne!(astar.revdot(&bstar), cstar, "k = {k}");
            }
            Ok(())
        }

        #[test]
        fn shifting_a_claim_into_k_is_rejected() -> Result<()> {
            // The monomial-weight forgery (shift a diagonal target into a
            // colliding cross term) has no analogue here: perturbing c_l by
            // delta and K by any fixed polynomial changes c* by a nonzero
            // polynomial in gamma unless both perturbations vanish.
            let mut rng = StdRng::seed_from_u64(3);
            let k = 7;
            let (a, b, c) = claims(&mut rng, k);
            let honest = error_terms(&a, &b, &c);
            for l in 0..k {
                let mut cf = c.clone();
                cf[l] += Fp::ONE;
                for t in 0..k - 1 {
                    let mut kf = honest.clone();
                    kf[t] -= Fp::ONE;
                    let gamma = rand_fp(&mut rng);
                    let (cstar, w) = verify(gamma, &kf, &cf)?;
                    let astar: Poly = fold_weighted(&a, &w);
                    let bstar: Poly = fold_weighted(&b, &w);
                    assert_ne!(astar.revdot(&bstar), cstar);
                }
            }
            Ok(())
        }

        #[test]
        fn gamma_in_domain_fails_witness_generation() {
            let mut rng = StdRng::seed_from_u64(4);
            let k = 5;
            let (a, b, c) = claims(&mut rng, k);
            let coeffs = error_terms(&a, &b, &c);
            assert!(verify(Fp::from(3), &coeffs, &c).is_err());
            assert!(weights::<Fp>(k, Fp::from(3)).is_none());
        }

        #[test]
        fn extractor_recovers_claims() {
            // Proposition 5.5 of the accompanying note: 2k-1 transcripts
            // sharing K determine every (a_i, b_i), and the claims hold.
            let mut rng = StdRng::seed_from_u64(5);
            let k = 4;
            let (a, b, c) = claims(&mut rng, k);
            let coeffs = error_terms(&a, &b, &c);
            let gammas: Vec<Fp> = (0..2 * k - 1).map(|_| rand_fp(&mut rng)).collect();
            let transcripts: Vec<(Vec<Fp>, Poly, Poly)> = gammas
                .iter()
                .map(|&g| {
                    let w = weights::<Fp>(k, g).unwrap();
                    let astar: Poly = fold_weighted(&a, &w);
                    let bstar: Poly = fold_weighted(&b, &w);
                    let cstar: Fp = w.iter().zip(&c).map(|(l, ci)| *l * ci).sum::<Fp>()
                        + vanishing::<Fp>(k, g)
                            * coeffs.iter().rev().fold(Fp::ZERO, |acc, x| acc * g + x);
                    assert_eq!(astar.revdot(&bstar), cstar);
                    (w, astar, bstar)
                })
                .collect();

            // Invert V = (L_i(gamma_t)) for t < k by Gauss-Jordan.
            let mut m: Vec<Vec<Fp>> = transcripts[..k]
                .iter()
                .enumerate()
                .map(|(t, (w, _, _))| {
                    let mut row = w.clone();
                    row.extend((0..k).map(|j| if j == t { Fp::ONE } else { Fp::ZERO }));
                    row
                })
                .collect();
            for col in 0..k {
                let piv = (col..k).find(|&r| !m[r][col].is_zero()).unwrap();
                m.swap(col, piv);
                let s = m[col][col].invert().unwrap();
                m[col].iter_mut().for_each(|x| *x *= s);
                for r in 0..k {
                    if r != col && !m[r][col].is_zero() {
                        let f = m[r][col];
                        let pivot_row = m[col].clone();
                        m[r].iter_mut()
                            .zip(&pivot_row)
                            .for_each(|(x, y)| *x -= f * y);
                    }
                }
            }
            let vinv: Vec<Vec<Fp>> = m.into_iter().map(|row| row[k..].to_vec()).collect();
            let heads_a: Vec<&Poly> = transcripts[..k].iter().map(|t| &t.1).collect();
            let heads_b: Vec<&Poly> = transcripts[..k].iter().map(|t| &t.2).collect();
            let ea: Vec<Poly> = vinv
                .iter()
                .map(|row| fold_weighted(&heads_a, row))
                .collect();
            let eb: Vec<Poly> = vinv
                .iter()
                .map(|row| fold_weighted(&heads_b, row))
                .collect();
            // Consistency: the extracted inputs reproduce every remaining
            // transcript (a mismatch would be a binding break).
            let coeffs_of = |p: &Poly| p.iter_coeffs().collect::<Vec<Fp>>();
            for (w, astar, bstar) in &transcripts[k..] {
                let fa: Poly = fold_weighted(&ea, w);
                let fb: Poly = fold_weighted(&eb, w);
                assert_eq!(coeffs_of(&fa), coeffs_of(astar));
                assert_eq!(coeffs_of(&fb), coeffs_of(bstar));
            }
            for i in 0..k {
                assert_eq!(ea[i].revdot(&eb[i]), c[i]);
            }
        }

        /// Gates of the deployed two-layer fold at full capacity (one
        /// `ClaimFolder` per layer, every group folded).
        fn two_layer_gates<P: super::super::Parameters>() -> Result<usize> {
            use ragu_primitives::vec::{FixedVec, Len};

            use super::super::ClaimFolder;
            let sim = Simulator::simulate((), |dr, _| {
                let mut rng = StdRng::seed_from_u64(9);
                let mut el = |dr: &mut Simulator<Fp>| Element::constant(dr, rand_fp(&mut rng));
                let (mu, nu, mu2, nu2) = (el(dr), el(dr), el(dr), el(dr));
                let inner = ClaimFolder::new(dr, &mu, &nu)?;
                let mut groups = Vec::new();
                for _ in 0..P::NumGroups::len() {
                    let e = FixedVec::from_fn(|_| el(dr));
                    let ky = FixedVec::from_fn(|_| el(dr));
                    groups.push(inner.fold_inner::<P>(dr, &e, &ky)?);
                }
                let outer = ClaimFolder::new(dr, &mu2, &nu2)?;
                let e = FixedVec::from_fn(|_| el(dr));
                let ky = FixedVec::from_fn(|t| groups[t].clone());
                outer.fold_outer::<P>(dr, &e, &ky)?;
                Ok(())
            })?;
            Ok(sim.num_gates())
        }

        #[test]
        fn cheaper_than_deployed_two_layer_fold() -> Result<()> {
            use crate::internal::native::RevdotParameters;
            let two_layer = two_layer_gates::<RevdotParameters>()?;
            // The book's accounting: N M^2 + N^2 - N + 3 for (M, N) = (7, 19).
            assert_eq!(two_layer, 1276);
            // Lagrange at the same capacity (133) and at the 93 claims a fuse
            // step actually produces.
            assert_eq!(5 * 133 - 2, 663);
            assert_eq!(5 * 93 - 2, 463);
            assert!(5 * 133 - 2 < two_layer);
            Ok(())
        }

        #[test]
        fn gate_count_is_5k_minus_2() -> Result<()> {
            for k in [2usize, 7, 19, 93, 133] {
                let sim = Simulator::simulate((), |dr, _| {
                    let mut rng = StdRng::seed_from_u64(k as u64);
                    let g = Element::constant(dr, rand_fp(&mut rng));
                    let e: Vec<_> = (0..k - 1)
                        .map(|_| Element::constant(dr, rand_fp(&mut rng)))
                        .collect();
                    let c: Vec<_> = (0..k)
                        .map(|_| Element::constant(dr, rand_fp(&mut rng)))
                        .collect();
                    fold_claims(dr, &g, &e, &c)?;
                    Ok(())
                })?;
                assert_eq!(sim.num_gates(), 5 * k - 2, "k = {k}");
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::{vec, vec::Vec};

    use ragu_circuits::polynomials::{TestRank, sparse};
    use ragu_core::{drivers::emulator::Emulator, maybe::Maybe, pasta::Fp};
    use ragu_primitives::{Simulator, allocator::Standard, vec::CollectFixed};
    use rand::{Rng, SeedableRng};

    use super::*;
    use crate::internal::native::RevdotParameters;

    /// Test parameters with configurable N and M.
    #[derive(Clone, Copy, Default)]
    struct TestParams<const N: usize, const M: usize>;
    impl<const N: usize, const M: usize> Parameters for TestParams<N, M> {
        type NumGroups = ConstLen<N>;
        type GroupSize = ConstLen<M>;
    }

    #[test]
    fn test_revdot_folding() -> Result<()> {
        type P = TestParams<3, 3>;

        let n = <P as Parameters>::NumGroups::len();
        let mut rng = rand::rng();

        // Create N random polynomial pairs
        let lhs: Vec<sparse::Polynomial<Fp, TestRank>> = (0..n)
            .map(|_| sparse::Polynomial::random(&mut rng))
            .collect();
        let rhs: Vec<sparse::Polynomial<Fp, TestRank>> = (0..n)
            .map(|_| sparse::Polynomial::random(&mut rng))
            .collect();

        // Compute ky values: diagonal revdot products
        let ky: Vec<Fp> = lhs.iter().zip(&rhs).map(|(l, r)| l.revdot(r)).collect();

        // Compute error terms using outer_error_terms (single-layer N-sized reduction)
        let error_terms = outer_error_terms::<Fp, TestRank, P>(&lhs, &rhs);
        let error: Vec<Fp> = error_terms.iter().copied().collect();

        let mu = Fp::random(|bytes| rng.fill_bytes(bytes));
        let nu = Fp::random(|bytes| rng.fill_bytes(bytes));
        let mu_inv = mu.invert().unwrap();
        let munu = mu * nu;

        // Fold polynomials
        let folded_lhs = sparse::Polynomial::fold(lhs.iter(), mu_inv);
        let folded_rhs = sparse::Polynomial::fold(rhs.iter(), munu);

        // Run routine with Emulator
        let dr = &mut Emulator::execute();
        let mu_elem = Element::constant(dr, mu);
        let nu_elem = Element::constant(dr, nu);

        let error_terms = error
            .iter()
            .map(|&v| Element::constant(dr, v))
            .collect_fixed()
            .unwrap();

        let ky_values = ky
            .iter()
            .map(|&v| Element::constant(dr, v))
            .collect_fixed()
            .unwrap();

        let fold_products = ClaimFolder::new(dr, &mu_elem, &nu_elem)?;
        let result = fold_products.fold_outer::<P>(dr, &error_terms, &ky_values)?;
        let computed_c = *result.value().take();

        // Verify the folding invariant: folded polynomials produce the same c
        assert_eq!(
            folded_lhs.revdot(&folded_rhs),
            computed_c,
            "Folded polynomials should produce the same c as ClaimFolder"
        );

        Ok(())
    }

    #[test]
    fn test_fold_polys_variable_sizes() -> Result<()> {
        use alloc::vec::Vec;

        type P = TestParams<6, 5>; // M=5, N=6, so max = 30

        let m = <P as Parameters>::GroupSize::len();
        let n = <P as Parameters>::NumGroups::len();

        fn verify(count: usize, m: usize, n: usize) -> Result<()> {
            let mut rng = rand::rng();

            // Create `count` random polynomial pairs
            let lhs: Vec<sparse::Polynomial<Fp, TestRank>> = (0..count)
                .map(|_| sparse::Polynomial::random(&mut rng))
                .collect();
            let rhs: Vec<sparse::Polynomial<Fp, TestRank>> = (0..count)
                .map(|_| sparse::Polynomial::random(&mut rng))
                .collect();

            // Compute diagonal revdot products (ky values)
            let ky_values: Vec<Fp> = lhs.iter().zip(&rhs).map(|(l, r)| l.revdot(r)).collect();

            // Layer 1 challenges
            let mu = Fp::random(|bytes| rng.fill_bytes(bytes));
            let nu = Fp::random(|bytes| rng.fill_bytes(bytes));
            let mu_inv = mu.invert().unwrap();
            let munu = mu * nu;

            // Compute inner error and fold polynomials for layer 1
            let inner_error = inner_error_terms::<Fp, TestRank, P>(&lhs, &rhs);
            let folded_lhs_m = fold_inner::<_, Fp, P>(&lhs, mu_inv);
            let folded_rhs_m = fold_inner::<_, Fp, P>(&rhs, munu);

            // Verify layer 1 invariant for each group
            let dr = &mut Emulator::execute();
            let mu_elem = Element::constant(dr, mu);
            let nu_elem = Element::constant(dr, nu);
            let fold_products = ClaimFolder::new(dr, &mu_elem, &nu_elem)?;

            for g in 0..n {
                // Compute expected claim from folded polynomials
                let expected = folded_lhs_m[g].revdot(&folded_rhs_m[g]);

                // Compute claim via ClaimFolder
                let ky_start = g * m;
                let ky_end = (ky_start + m).min(count);
                let ky_group: FixedVec<Element<'_, _>, _> = FixedVec::from_fn(|i| {
                    let val = if ky_start + i < ky_end {
                        ky_values[ky_start + i]
                    } else {
                        Fp::ZERO
                    };
                    Element::constant(dr, val)
                });
                let error_group: FixedVec<Element<'_, _>, _> =
                    FixedVec::from_fn(|i| Element::constant(dr, inner_error[g][i]));

                let computed = fold_products.fold_inner::<P>(dr, &error_group, &ky_group)?;
                let computed_val = *computed.value().take();

                assert_eq!(
                    expected, computed_val,
                    "Layer 1 group {} invariant failed for count={}",
                    g, count
                );
            }

            Ok(())
        }

        // Test various sizes below or equal to M*N
        for &count in &[1, 2, 5, 7, 10, 15, 20, 25, 29, 30] {
            verify(count, m, n)?;
        }

        Ok(())
    }

    #[test]
    fn test_fold_products_constraints() -> Result<()> {
        fn measure<P: Parameters>() -> Result<usize> {
            let sim = Simulator::simulate((), |dr, _| {
                let mu = Element::constant(dr, Fp::random(|bytes| rand::rng().fill_bytes(bytes)));
                let nu = Element::constant(dr, Fp::random(|bytes| rand::rng().fill_bytes(bytes)));
                let error_terms = FixedVec::from_fn(|_| {
                    Element::constant(dr, Fp::random(|bytes| rand::rng().fill_bytes(bytes)))
                });
                let ky_values = FixedVec::from_fn(|_| {
                    Element::constant(dr, Fp::random(|bytes| rand::rng().fill_bytes(bytes)))
                });

                let fold_products = ClaimFolder::new(dr, &mu, &nu)?;
                fold_products.fold_outer::<P>(dr, &error_terms, &ky_values)?;
                Ok(())
            })?;

            Ok(sim.num_gates())
        }

        // Formula: N^2 + 1
        assert_eq!(measure::<TestParams<5, 1>>()?, 26);
        assert_eq!(measure::<TestParams<15, 1>>()?, 226);
        assert_eq!(measure::<TestParams<30, 1>>()?, 901);
        assert_eq!(measure::<TestParams<60, 1>>()?, 3601);

        Ok(())
    }

    #[test]
    fn test_multireduce() -> Result<()> {
        /// Verify two-layer folding correctness with actual polynomials.
        fn verify<P: Parameters>() -> Result<()> {
            let mut rng = rand::rng();
            let n = P::NumGroups::len();
            let m = P::GroupSize::len();
            let count = n * m;

            // Create N*M random polynomial pairs
            let lhs: Vec<sparse::Polynomial<Fp, TestRank>> = (0..count)
                .map(|_| sparse::Polynomial::random(&mut rng))
                .collect();
            let rhs: Vec<sparse::Polynomial<Fp, TestRank>> = (0..count)
                .map(|_| sparse::Polynomial::random(&mut rng))
                .collect();

            // Compute ky values: diagonal revdot products
            let ky_values: Vec<Fp> = lhs.iter().zip(&rhs).map(|(l, r)| l.revdot(r)).collect();

            // Layer 1 challenges
            let mu = Fp::random(|bytes| rng.fill_bytes(bytes));
            let nu = Fp::random(|bytes| rng.fill_bytes(bytes));
            let mu_inv = mu.invert().unwrap();
            let munu = mu * nu;

            // Compute inner error: N groups of M*(M-1) off-diagonal revdot products
            let inner_error = inner_error_terms::<Fp, TestRank, P>(&lhs, &rhs);

            // Fold polynomials for layer 1
            let folded_lhs = fold_inner::<_, Fp, P>(&lhs, mu_inv);
            let folded_rhs = fold_inner::<_, Fp, P>(&rhs, munu);

            // Compute collapsed values via ClaimFolder
            let collapsed: FixedVec<Fp, P::NumGroups> =
                Emulator::emulate_wireless((&inner_error, &ky_values, mu, nu), |dr, witness| {
                    let (inner_error, ky_values, mu, nu) = witness.cast();
                    let allocator = &mut ();
                    let mu = Element::alloc(dr, allocator, mu)?;
                    let nu = Element::alloc(dr, allocator, nu)?;
                    let fold_products = ClaimFolder::new(dr, &mu, &nu)?;

                    let mut ky_idx = 0;
                    let collapsed = FixedVec::try_from_fn(|group| {
                        let errors = FixedVec::try_from_fn(|j| {
                            Element::alloc(dr, allocator, inner_error.as_ref().map(|e| e[group][j]))
                        })?;
                        let ky = FixedVec::try_from_fn(|_| {
                            let idx = ky_idx;
                            ky_idx += 1;
                            Element::alloc(dr, allocator, ky_values.as_ref().map(|kv| kv[idx]))
                        })?;
                        let v = fold_products.fold_inner::<P>(dr, &errors, &ky)?;
                        Ok(*v.value().take())
                    })?;
                    Ok(collapsed)
                })?;

            // Verify layer 1 invariant: each collapsed[i] == folded_lhs[i].revdot(&folded_rhs[i])
            for i in 0..n {
                assert_eq!(
                    folded_lhs[i].revdot(&folded_rhs[i]),
                    collapsed[i],
                    "Layer 1 group {} invariant failed",
                    i
                );
            }

            // Layer 2 challenges
            let mu_prime = Fp::random(|bytes| rng.fill_bytes(bytes));
            let nu_prime = Fp::random(|bytes| rng.fill_bytes(bytes));
            let mu_prime_inv = mu_prime.invert().unwrap();
            let mu_prime_nu_prime = mu_prime * nu_prime;

            // Compute outer error from layer 1 folded polynomials
            let outer_error = outer_error_terms::<Fp, TestRank, P>(&folded_lhs, &folded_rhs);

            // Fold to final polynomials
            let final_lhs = fold_outer::<_, Fp, P>(folded_lhs, mu_prime_inv);
            let final_rhs = fold_outer::<_, Fp, P>(folded_rhs, mu_prime_nu_prime);

            // Compute final c via ClaimFolder
            let final_c: Fp = Emulator::emulate_wireless(
                (&outer_error, &collapsed, mu_prime, nu_prime),
                |dr, witness| {
                    let (outer_error, collapsed, mu_prime, nu_prime) = witness.cast();
                    let allocator = &mut ();
                    let mu_prime = Element::alloc(dr, allocator, mu_prime)?;
                    let nu_prime = Element::alloc(dr, allocator, nu_prime)?;
                    let fold_products = ClaimFolder::new(dr, &mu_prime, &nu_prime)?;

                    let error_terms = FixedVec::try_from_fn(|i| {
                        Element::alloc(dr, allocator, outer_error.as_ref().map(|e| e[i]))
                    })?;
                    let collapsed = FixedVec::try_from_fn(|i| {
                        Element::alloc(dr, allocator, collapsed.as_ref().map(|c| c[i]))
                    })?;

                    let c = fold_products.fold_outer::<P>(dr, &error_terms, &collapsed)?;
                    Ok(*c.value().take())
                },
            )?;

            // Verify final invariant: final_lhs.revdot(&final_rhs) == final_c
            assert_eq!(
                final_lhs.revdot(&final_rhs),
                final_c,
                "Final folding invariant failed"
            );

            Ok(())
        }

        // Test various parameter combinations
        verify::<TestParams<2, 2>>()?;
        verify::<TestParams<3, 3>>()?;
        verify::<TestParams<4, 3>>()?;
        verify::<TestParams<3, 4>>()?;

        Ok(())
    }

    #[test]
    fn test_fold_two_layer_evaluations() -> Result<()> {
        use alloc::vec::Vec;

        /// Verify fold_two_layer on evaluations matches evaluating folded polynomials
        /// for both lhs and rhs polynomial sets with their respective scale factors.
        fn verify<P: Parameters>(count: usize) -> Result<()> {
            let mut rng = rand::rng();

            // Create `count` random polynomial pairs (up to m*n)
            let lhs: Vec<sparse::Polynomial<Fp, TestRank>> = (0..count)
                .map(|_| sparse::Polynomial::random(&mut rng))
                .collect();
            let rhs: Vec<sparse::Polynomial<Fp, TestRank>> = (0..count)
                .map(|_| sparse::Polynomial::random(&mut rng))
                .collect();

            // Random evaluation point
            let x = Fp::random(|bytes| rng.fill_bytes(bytes));

            // Challenge values (matching compute_v.rs usage pattern)
            let mu = Fp::random(|bytes| rng.fill_bytes(bytes));
            let nu = Fp::random(|bytes| rng.fill_bytes(bytes));
            let mu_prime = Fp::random(|bytes| rng.fill_bytes(bytes));
            let nu_prime = Fp::random(|bytes| rng.fill_bytes(bytes));

            // Derived scale factors for lhs: mu_inv, mu_prime_inv
            let mu_inv = mu.invert().unwrap();
            let mu_prime_inv = mu_prime.invert().unwrap();

            // Derived scale factors for rhs: munu, mu_prime_nu_prime
            let munu = mu * nu;
            let mu_prime_nu_prime = mu_prime * nu_prime;

            // === LHS: fold with mu_inv (layer1), mu_prime_inv (layer2) ===
            let folded_lhs_m = fold_inner::<_, Fp, P>(&lhs, mu_inv);
            let folded_lhs_n = fold_outer::<_, Fp, P>(folded_lhs_m, mu_prime_inv);
            let expected_lhs = folded_lhs_n.eval(x);

            // === RHS: fold with munu (layer1), mu_prime_nu_prime (layer2) ===
            let folded_rhs_m = fold_inner::<_, Fp, P>(&rhs, munu);
            let folded_rhs_n = fold_outer::<_, Fp, P>(folded_rhs_m, mu_prime_nu_prime);
            let expected_rhs = folded_rhs_n.eval(x);

            // Compute evaluations at x
            let lhs_evals: Vec<Fp> = lhs.iter().map(|p| p.eval(x)).collect();
            let rhs_evals: Vec<Fp> = rhs.iter().map(|p| p.eval(x)).collect();

            // Fold evaluations using fold_two_layer with Emulator
            let dr = &mut Emulator::execute();

            let lhs_elems: Vec<Element<'_, _>> = lhs_evals
                .iter()
                .map(|&v| Element::constant(dr, v))
                .collect();
            let rhs_elems: Vec<Element<'_, _>> = rhs_evals
                .iter()
                .map(|&v| Element::constant(dr, v))
                .collect();

            let mu_inv_elem = Element::constant(dr, mu_inv);
            let mu_prime_inv_elem = Element::constant(dr, mu_prime_inv);
            let munu_elem = Element::constant(dr, munu);
            let mu_prime_nu_prime_elem = Element::constant(dr, mu_prime_nu_prime);

            let lhs_result =
                fold_two_layer::<_, P>(dr, &lhs_elems, &mu_inv_elem, &mu_prime_inv_elem)?;
            let rhs_result =
                fold_two_layer::<_, P>(dr, &rhs_elems, &munu_elem, &mu_prime_nu_prime_elem)?;

            let computed_lhs = *lhs_result.value().take();
            let computed_rhs = *rhs_result.value().take();

            assert_eq!(
                expected_lhs, computed_lhs,
                "fold_two_layer(lhs_evals) should equal fold_polys(lhs).eval(x)"
            );
            assert_eq!(
                expected_rhs, computed_rhs,
                "fold_two_layer(rhs_evals) should equal fold_polys(rhs).eval(x)"
            );

            Ok(())
        }

        // Test with various parameter combinations and various sizes
        for count in 0..=6 {
            verify::<TestParams<2, 3>>(count)?;
        }
        for &count in &[1, 2, 3, 4] {
            verify::<TestParams<2, 2>>(count)?;
        }
        for &count in &[1, 3, 5, 7, 9] {
            verify::<TestParams<3, 3>>(count)?;
        }
        for &count in &[1, 4, 7, 10, 12] {
            verify::<TestParams<4, 3>>(count)?;
        }
        for &count in &[1, 4, 7, 10, 12] {
            verify::<TestParams<3, 4>>(count)?;
        }

        // Test native parameters (6*18=108) with various sizes
        for &count in &[1, 10, 33, 50, 80, 100, 108] {
            verify::<TestParams<6, 18>>(count)?;
        }

        Ok(())
    }

    /// Computes the number of gates for given M, N.
    ///
    /// Formula: NM^2 + N^2 - N + 3
    /// - Layer 1: 2 + N(M^2 - 1) = NM^2 - N + 2
    /// - Layer 2: 2 + (N^2 - 1) = N^2 + 1
    fn muls(m: usize, n: usize) -> usize {
        n * m * m + n * n - n + 3
    }

    /// Computes the number of allocations for given M, N.
    ///
    /// Formula: NM^2 + N^2 - N + 4
    /// - 4 top-level: mu, nu, mu', nu'
    /// - Layer 1: N * (M^2 - M) error terms + N * M ky values = NM^2
    /// - Layer 2: N^2 - N error terms
    fn allocs(m: usize, n: usize) -> usize {
        n * m * m + n * n - n + 4
    }

    /// This measures the effective constraint cost that accounts
    /// for both multiplication gates and allocations for various M
    /// and N combinations. The optimal accounting here is to maximize
    /// M * N, while staying under the circuit budget.
    ///
    /// [`Standard`] pairs consecutive allocations into gates, so
    /// the total gate count is `muls + allocs / 2` (exact when `allocs`
    /// is even, which holds for the tested parameters). Each gate
    /// consumes two trace slots, giving an effective cost of
    /// `2 * total_gates`.
    #[test]
    fn test_cost_formulas() -> Result<()> {
        fn verify<const M: usize, const N: usize>() -> Result<()> {
            let rng = rand::rngs::StdRng::from_rng(&mut rand::rng());
            let sim = Simulator::simulate(rng, |dr, mut rng| {
                let allocator = &mut Standard::new();
                let mu = Element::alloc(
                    dr,
                    allocator,
                    rng.as_mut()
                        .map(|rng| Fp::random(|bytes| rng.fill_bytes(bytes))),
                )?;
                let nu = Element::alloc(
                    dr,
                    allocator,
                    rng.as_mut()
                        .map(|rng| Fp::random(|bytes| rng.fill_bytes(bytes))),
                )?;
                let mu_prime = Element::alloc(
                    dr,
                    allocator,
                    rng.as_mut()
                        .map(|rng| Fp::random(|bytes| rng.fill_bytes(bytes))),
                )?;
                let nu_prime = Element::alloc(
                    dr,
                    allocator,
                    rng.as_mut()
                        .map(|rng| Fp::random(|bytes| rng.fill_bytes(bytes))),
                )?;

                // Layer 1: N instances of M-sized reductions (uses mu, nu).
                let fold_products_layer1 = ClaimFolder::new(dr, &mu, &nu)?;
                let all_error_terms_m: FixedVec<
                    FixedVec<_, NumErrorTerms<ConstLen<M>>>,
                    ConstLen<N>,
                > = FixedVec::try_from_fn(|_| {
                    FixedVec::try_from_fn(|_| {
                        Element::alloc(
                            dr,
                            allocator,
                            rng.as_mut()
                                .map(|rng| Fp::random(|bytes| rng.fill_bytes(bytes))),
                        )
                    })
                })?;
                let all_ky_values_m: FixedVec<FixedVec<_, ConstLen<M>>, ConstLen<N>> =
                    FixedVec::try_from_fn(|_| {
                        FixedVec::try_from_fn(|_| {
                            Element::alloc(
                                dr,
                                allocator,
                                rng.as_mut()
                                    .map(|rng| Fp::random(|bytes| rng.fill_bytes(bytes))),
                            )
                        })
                    })?;

                let collapsed: FixedVec<_, ConstLen<N>> = FixedVec::try_from_fn(|i| {
                    fold_products_layer1.fold_inner::<TestParams<N, M>>(
                        dr,
                        &all_error_terms_m[i],
                        &all_ky_values_m[i],
                    )
                })?;

                // Layer 2: Single N-sized reduction (uses mu', nu' - separate ClaimFolder).
                let fold_products_layer2 = ClaimFolder::new(dr, &mu_prime, &nu_prime)?;
                let error_terms_n: FixedVec<_, NumErrorTerms<ConstLen<N>>> =
                    FixedVec::try_from_fn(|_| {
                        Element::alloc(
                            dr,
                            allocator,
                            rng.as_mut()
                                .map(|rng| Fp::random(|bytes| rng.fill_bytes(bytes))),
                        )
                    })?;

                fold_products_layer2.fold_outer::<TestParams<N, M>>(
                    dr,
                    &error_terms_n,
                    &collapsed,
                )?;
                Ok(())
            })?;

            assert_eq!(sim.num_gates(), muls(M, N) + allocs(M, N) / 2);
            Ok(())
        }

        verify::<6, 17>()?;
        verify::<7, 14>()?;

        // Verify optimal parameters fit circuit budget.
        // Each gate uses 2 trace slots, so effective cost = 2 * total_gates.
        let total_gates = muls(6, 17) + allocs(6, 17) / 2;
        assert!(
            total_gates < (1 << 11),
            "M = 6, N = 17 exceeds budget: {total_gates}",
        );

        Ok(())
    }

    #[test]
    fn test_empty_input() {
        type P = TestParams<3, 3>;

        let n = <P as Parameters>::NumGroups::len();

        // Empty input should produce all-zero folded polynomials
        let empty: Vec<sparse::Polynomial<Fp, TestRank>> = vec![];
        let folded = fold_inner::<_, Fp, P>(&empty, Fp::ONE);

        // All N groups should be zero polynomials
        for g in 0..n {
            assert!(
                folded[g].iter_coeffs().all(|c| c == Fp::ZERO),
                "Group {} should be zero polynomial for empty input",
                g
            );
        }

        // Error computation on empty input should produce zero errors
        let inner_error = inner_error_terms::<Fp, TestRank, P>(&empty, &empty);
        for g in 0..n {
            for e in inner_error[g].iter() {
                assert_eq!(*e, Fp::ZERO, "Error terms should be zero for empty input");
            }
        }
    }

    #[test]
    #[should_panic(expected = "exceeds GroupSize*NumGroups")]
    fn test_fold_inner_overflow_panics() {
        type P = TestParams<2, 2>; // max = 4

        // Create 5 polynomials, which exceeds GroupSize*NumGroups=4
        let polys: Vec<_> = (0..5)
            .map(|_| sparse::Polynomial::<Fp, TestRank>::new())
            .collect();
        let _ = fold_inner::<_, Fp, P>(&polys, Fp::ONE);
    }

    #[test]
    #[should_panic(expected = "source length 7 exceeds GroupSize*NumGroups = 6")]
    fn test_fold_two_layer_overflow_panics() {
        let dr = &mut Emulator::execute();
        let one = Element::constant(dr, Fp::ONE);
        let sources = vec![one.clone(); 7];

        fold_two_layer::<_, TestParams<2, 3>>(dr, &sources, &one, &one).unwrap();
    }

    #[test]
    fn test_error_term_ordering() {
        let mut rng = rand::rng();

        // Create 3 distinct polynomial pairs
        let a: Vec<sparse::Polynomial<Fp, TestRank>> = (0..3)
            .map(|_| sparse::Polynomial::random(&mut rng))
            .collect();
        let b: Vec<sparse::Polynomial<Fp, TestRank>> = (0..3)
            .map(|_| sparse::Polynomial::random(&mut rng))
            .collect();

        // Compute error terms (should be 3*(3-1)=6 terms)
        let errors = outer_error_terms::<Fp, TestRank, TestParams<3, 3>>(&a, &b);

        // Verify row-major ordering: (0,1), (0,2), (1,0), (1,2), (2,0), (2,1)
        let expected_pairs = [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)];
        for (idx, &(i, j)) in expected_pairs.iter().enumerate() {
            let expected = a[i].revdot(&b[j]);
            assert_eq!(
                errors[idx], expected,
                "Error term {} should be revdot(a[{}], b[{}])",
                idx, i, j
            );
        }
    }

    #[test]
    fn test_fold_inner_constraints() -> Result<()> {
        // Verify layer 1 constraint count formula: 2M^2 + 1 per group
        fn measure_m<const M: usize>() -> Result<usize> {
            let sim = Simulator::simulate((), |dr, _| {
                let mu = Element::constant(dr, Fp::random(|bytes| rand::rng().fill_bytes(bytes)));
                let nu = Element::constant(dr, Fp::random(|bytes| rand::rng().fill_bytes(bytes)));
                let error_terms: FixedVec<_, NumErrorTerms<ConstLen<M>>> =
                    FixedVec::from_fn(|_| {
                        Element::constant(dr, Fp::random(|bytes| rand::rng().fill_bytes(bytes)))
                    });
                let ky_values: FixedVec<_, ConstLen<M>> = FixedVec::from_fn(|_| {
                    Element::constant(dr, Fp::random(|bytes| rand::rng().fill_bytes(bytes)))
                });

                let fold_products = ClaimFolder::new(dr, &mu, &nu)?;
                fold_products.fold_inner::<TestParams<1, M>>(dr, &error_terms, &ky_values)?;
                Ok(())
            })?;

            Ok(sim.num_gates())
        }

        // Formula: M^2 + 1
        assert_eq!(measure_m::<3>()?, 9 + 1); // 10
        assert_eq!(measure_m::<5>()?, 25 + 1); // 26
        assert_eq!(measure_m::<6>()?, 36 + 1); // 37

        Ok(())
    }

    #[test]
    fn test_native_parameters_correctness() -> Result<()> {
        // Test with actual RevdotParameters (M=6, N=18)

        let mut rng = rand::rng();
        let m = <RevdotParameters as Parameters>::GroupSize::len();
        let _n = <RevdotParameters as Parameters>::NumGroups::len();

        // Use a subset of the full capacity to keep test fast
        let count: usize = 20; // Less than M*N=108

        let lhs: Vec<sparse::Polynomial<Fp, TestRank>> = (0..count)
            .map(|_| sparse::Polynomial::random(&mut rng))
            .collect();
        let rhs: Vec<sparse::Polynomial<Fp, TestRank>> = (0..count)
            .map(|_| sparse::Polynomial::random(&mut rng))
            .collect();

        let mu = Fp::random(|bytes| rng.fill_bytes(bytes));
        let nu = Fp::random(|bytes| rng.fill_bytes(bytes));
        let mu_inv = mu.invert().unwrap();
        let munu = mu * nu;

        // Fold with RevdotParameters
        let folded_lhs = fold_inner::<_, Fp, RevdotParameters>(&lhs, mu_inv);
        let folded_rhs = fold_inner::<_, Fp, RevdotParameters>(&rhs, munu);

        // Verify at least the first few groups
        let dr = &mut Emulator::execute();
        let mu_elem = Element::constant(dr, mu);
        let nu_elem = Element::constant(dr, nu);
        let fold_products = ClaimFolder::new(dr, &mu_elem, &nu_elem)?;

        let ky_values: Vec<Fp> = lhs.iter().zip(&rhs).map(|(l, r)| l.revdot(r)).collect();
        let inner_error = inner_error_terms::<Fp, TestRank, RevdotParameters>(&lhs, &rhs);

        // Check first 4 groups (those with actual data)
        let num_groups = count.div_ceil(m);
        for g in 0..num_groups {
            let expected = folded_lhs[g].revdot(&folded_rhs[g]);

            let ky_start = g * m;
            let ky_end = (ky_start + m).min(count);
            let ky_group: FixedVec<Element<'_, _>, _> = FixedVec::from_fn(|i| {
                let val = if ky_start + i < ky_end {
                    ky_values[ky_start + i]
                } else {
                    Fp::ZERO
                };
                Element::constant(dr, val)
            });
            let error_group: FixedVec<Element<'_, _>, _> =
                FixedVec::from_fn(|i| Element::constant(dr, inner_error[g][i]));

            let computed =
                fold_products.fold_inner::<RevdotParameters>(dr, &error_group, &ky_group)?;
            let computed_val = *computed.value().take();

            assert_eq!(
                expected, computed_val,
                "RevdotParameters: group {} invariant failed",
                g
            );
        }

        Ok(())
    }
}
