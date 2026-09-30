# Formal power series

A Lean library with two independent families: the **weighted negative logarithmic
derivative** of native single-variable power-series units over an arbitrary
commutative ring `R`, and coefficientwise **ideal-adically restricted native
multivariate power series**:

```lean
PowerSeries.negXLogDeriv (f : (PowerSeries R)ˣ) =
  -PowerSeries.X * PowerSeries.derivative (f : PowerSeries R) *
    ((f⁻¹ : (PowerSeries R)ˣ) : PowerSeries R)
```

The multivariate family works with finite exceptional *monomial indices* at
each ideal power, not a finite set of coefficient values. Its basic construction
allows arbitrary variable types and ideals; stronger hypotheses are stated
separately for internal principal division and adic completion. Neither family
imports or mathematically depends on the other.

## Headline results

### Weighted unit derivative

- **Products become sums, naturally in the coefficient ring.** Over any
  commutative ring, `PowerSeries.negXLogDeriv` takes multiplication of native
  units to addition, inverses to negatives and integer powers to integer
  multiples. It commutes with arbitrary coefficient-ring homomorphisms, also
  between different universes, and bundles as a homomorphism from the unit
  group written additively. For a supplied unit `f`, the equation
  `g * f = -X * f'` characterizes `g = negXLogDeriv f` without normalizing its
  constant coefficient. See the [definition](FormalPowerSeries/UnitLogDerivative.lean#L27),
  [laws](FormalPowerSeries/UnitLogDerivative.lean#L39),
  [naturality](FormalPowerSeries/UnitLogDerivative.lean#L81) and
  [characterization](FormalPowerSeries/UnitLogDerivative.lean#L98).
- **Integral coefficient formulas.** A finite convolution identity works for
  every native unit, including nonnormalized ones. If the constant coefficient
  is one, a **forward** recurrence determines each next coefficient of the
  weighted derivative from the coefficients of `f` and preceding derivative
  coefficients, without division by positive integers. Thus torsion and zero
  rings are allowed; this does not reconstruct `f` from its derivative. See
  [convolution](FormalPowerSeries/UnitLogDerivative.lean#L115) and
  [recurrence](FormalPowerSeries/UnitLogDerivative.lean#L124).
- **Linear factors and finite signed products.** `oneSubCXUnit a` represents
  `1 - C a * X` for every `a`; its inverse has coefficient `a^n` in degree
  `n`, and its weighted derivative has coefficient `a^(n+1)` in degree `n+1`.
  The product and integer-power laws yield a signed power-sum formula for
  finite products of these factors, including inverse factors and the empty
  family. The [signed-product example](Tests/UnitLogDerivative.lean#L127) is a
  client in the `Tests` root, not a theorem splitting arbitrary units. See the
  [factor](FormalPowerSeries/UnitLogDerivative.lean#L139) and
  [coefficient formula](FormalPowerSeries/UnitLogDerivative.lean#L160).

This is weighted by **negative `X`**, not an unweighted analytic logarithmic
derivative or a formal logarithm. Constant units lie in its kernel; under
`[CharP R p]` for any natural `p`, so do `p`-th powers. Even a normalized
nonidentity unit can lie in the kernel, as the
[characteristic-two client](Tests/UnitLogDerivative.lean#L96) shows.
For `a_n = coeff n f` and `b_n = coeff n (negXLogDeriv f)`, the unnormalized
identity is `∑ (i,j) ∈ antidiagonal (n+1), b_i * a_j = -(a_(n+1) * (n+1))`.
**Only if** `a_0 = 1`, the forward recurrence is
`b_(n+1) + ∑ i ∈ range n, a_(i+1) * b_(n-i) = -(a_(n+1) * (n+1))`.
See [API.md](API.md) for the conventions; the pin-specific `derivative_map`
helper remains private, not a separate derivative API. There is no lambda/Witt
structure, splitting extension or Adams operation here.

### Ideal-adically restricted multivariate series

- **Finite-index reduction.** For any variable type `σ`, commutative ring
  `R` and ideal `I`, `IsAdicallyRestricted I f` requires that at each `k : ℕ`,
  only finitely many monomial indices have coefficients outside `I ^ k`.
  A polynomial-range characterization yields a restricted subring and a
  **surjective** ring homomorphism
  `adicReduction I k : _ →+* MvPolynomial σ (R ⧸ I ^ k)`, including at `k = 0`.
  See the [predicate](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted.lean#L25),
  [polynomial characterization](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted.lean#L67),
  [reduction](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted.lean#L133)
  and [finite-reduction guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/README.md).
- **Regular-principal internal kernel.** When `I = Ideal.span {a}` and
  `ha : IsRegular a`, coefficientwise division by `a ^ k` constructs the
  quotient *inside the restricted subring*. The kernel of `adicReduction I k`
  is the ideal generated there by the restricted constant `a ^ k`. This is
  not arbitrary-ideal internal division. See the
  [division theorem](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/PrincipalKernel.lean#L38),
  [kernel theorem](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/PrincipalKernel.lean#L82)
  and [kernel guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/PrincipalKernel/README.md).
- **Polynomial adic-completion equivalence.** With actual coefficient
  completeness `[IsAdicComplete I R]`,
  `adicallyRestrictedEquivAdicCompletion I` is a ring equivalence between
  the restricted subring and native
  `AdicCompletion (I.map MvPolynomial.C) (MvPolynomial σ R)`. It preserves
  finite-level evaluation and polynomial inclusion. Neither finite variables
  nor finite generation of `I` is assumed; completeness of arbitrary
  non-finitely-generated polynomial completions is **not** asserted. See the
  [equivalence](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/InverseLimit.lean#L270),
  [evaluation](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/InverseLimit.lean#L280)
  and [completion guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/InverseLimit/README.md).

The latter three results concern coefficient-adic series, not norm/radius or
variable-adic restrictions, general base change, general preparation or
arbitrary-ideal division. The two mathematical families remain independent.

## Build and use

Install `elan` and Git; `lean-toolchain` pins Lean
`leanprover/lean4:v4.34.0-rc2`, and the sole direct dependency is mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. From the repository root:

```sh
lake exe cache get
lake build
```

The first command fetches the matching mathlib cache; the literal default
`lake build` includes the public library and all `Tests/` examples. Historical
**unit-derivative-only** initial module/default builds on the author's
September 2026 environment processed 1,743/1,777 Lake jobs on a matching
warm cache. These are job counts for the earlier graph, **not** measurements
of this expanded graph, time or peak memory. For the expanded graph, the
original September 2026 strict `lean-ci` run on pinned Lean/mathlib fetched
the matching mathlib cache in **39.5 seconds**, verified its cached Mathlib
build in **6.5 seconds**, then completed
`lake build FormalPowerSeries Tests` in **10.8 seconds (1,954 Lake jobs)**.
These are command wall times from that CI runner, not isolated compiler timings
or local-machine benchmarks. The complete CI run took **2 minutes 46 seconds**
including setup, build, transitive axiom checks and artifact handling; it is
not the build command's duration. No expanded-graph peak RAM or disk use was
measured.

For planning on a typical 4-core Linux machine with the matching mathlib cache
available, allow roughly **10–45 minutes** for initial toolchain/cache setup
and the full library-plus-tests build, and **1–10 minutes** for a small
library/test rebuild with dependencies already cached. Budget approximately
**16 GiB RAM and 20 GiB free disk** for the pinned toolchain, dependencies,
cache and outputs, leaving additional headroom if possible. These are
conservative **estimates**, extending earlier unbenchmarked unit-only guidance
in light of the expanded CI graph; they are not measured resource peaks,
guaranteed limits or desktop timings inferred from CI. Download bandwidth,
CPU speed, cache state and competing jobs vary. Fetch the matching cache before
building; these allowances do not cover rebuilding mathlib from source.

Import `FormalPowerSeries` from a dependent Lake project (declare and pin this
repository and its dependencies there), or selectively import
`FormalPowerSeries.UnitLogDerivative`,
`FormalPowerSeries.MvPowerSeries.IdealAdicRestricted`,
`FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.PrincipalKernel`, or
`FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.InverseLimit`. The
`Tests` root imports independent [unit](Tests/UnitLogDerivative.lean),
[finite-reduction](Tests/MvPowerSeries/IdealAdicRestricted.lean),
[kernel](Tests/MvPowerSeries/IdealAdicRestricted/PrincipalKernel.lean) and
[completion](Tests/MvPowerSeries/IdealAdicRestricted/InverseLimit.lean)
clients. The unit client contains this example:

```lean
theorem signedExample {T : Type*} [CommRing T]
    (a : T) (n : ℕ) :
    PowerSeries.coeff (n + 1)
      (PowerSeries.negXLogDeriv (PowerSeries.oneSubCXUnit a)) = a ^ (n + 1) :=
  PowerSeries.coeff_succ_negXLogDeriv_oneSubCXUnit a n
```

See [API.md](API.md) for both public families' names, hypotheses, coefficient
conventions and guide links.

## Provenance and rights

The integral formula is related to Charles A. Weibel, *The K-book: An
Introduction to Algebraic K-theory* (2013), Section II.4 and Exercise 4.6;
this small library does **not** claim to formalize the whole section or book.
Prism developed the original derivative proof expression in a checked source
experiment in
`source-weibel-k-book` at commit `6453001fbf58cbca909037650832071c594568a6`
(accepted source main `a2857276cc6bac20a65c77306e58f077d985fa93`).
Formal Frontier's `formalization-worker-a` adapted the proofs into this
source-independent module-system API and added the standalone client and
original documentation. Folio prepared the derivative headline explanations
for this combined README; that documentation work does not replace Prism's
proof authorship or `formalization-worker-a`'s adaptation credit. The derivative
module retains the originating proof structure and code expression, rather than
attributing them to mathlib. We use mathlib's
`PowerSeries.derivative`, `invOneSubPow`, `rescale`, coefficient algebra and
ordinary tactics as dependencies, not copied mathlib declarations or proofs.
The independent restricted-series base, regular-principal and inverse-limit
proofs, ordinary-import clients and guides were developed by Formal Frontier
AI contributors in the shared incubator and transferred without changing their
public mathematical declarations. Their distinct original authors and the
transfer author are recorded in the private owning provenance; the
[three guides](API.md#ideal-adically-restricted-multivariate-series) credit
the native mathlib APIs and their authors. Anchor is responsible for the
restricted-series contribution; Prism retains derivative maintenance and shared
library responsibility. Original Formal Frontier files are licensed under
Apache-2.0, **Authors: Formal Frontier Agents** (see [LICENSE](LICENSE));
mathlib is separately distributed under its own Apache-2.0 license. The
original work and these adaptations involved AI agents; historical unit-family
review does not certify the expanded destination graph or source coverage.
