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
separately for internal principal division and coefficient completeness. Under
`[IsAdicComplete I R]`, **every `R`-linear polynomial endomorphism extends
to an `R`-linear operator on restricted series**, with finite-level equations
and a uniqueness theorem requiring both polynomial agreement and preservation
of every coefficientwise reduction kernel. Independently of completeness,
**products of coefficientwise reduction kernels at levels `n` and `k` lie
in the kernel at `n + k`**, including finite-sum and level-one laws.
The multivariate family also supplies content, intrinsic actual-ring leading
terms, restricted division and **conditional** primitive ideal generation.
A separately importable generic support leaf compares cofinal ideal-adic
filtrations for arbitrary modules. The two series families are independent.

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
  See the [predicate and polynomial characterization](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted.lean),
  [reduction](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted.lean)
  and [finite-reduction guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/README.md).
- **Regular-principal internal kernel.** When `I = Ideal.span {a}` and
  `ha : IsRegular a`, coefficientwise division by `a ^ k` constructs the
  quotient *inside the restricted subring*. The kernel of `adicReduction I k`
  is the ideal generated there by the restricted constant `a ^ k`. This is
  not arbitrary-ideal internal division. See the
  [division and kernel theorems](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/PrincipalKernel.lean)
  and [kernel guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/PrincipalKernel/README.md).
- **Scalar-linear polynomial quotients.** The existing restricted subring has
  an `R`-algebra structure, and reduction to `MvPolynomial σ (R ⧸ I ^ k)` is
  surjective and `R`-linear for every ideal, variable type and level, including
  `k = 0`. For a regular principal generator `a`, its **submodule** kernel is
  `I ^ k • ⊤`, yielding an `R`-linear equivalence from the corresponding
  module quotient; it is not a ring-quotient equivalence. A separate native
  integer endpoint supports default `ℤ`-module quotient types without a
  priority override. See the [linear quotient module](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LinearQuotient.lean),
  [guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LinearQuotient/README.md)
  and [ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted/LinearQuotient.lean).
- **Polynomial adic-completion equivalence.** With actual coefficient
  completeness `[IsAdicComplete I R]`,
  `adicallyRestrictedEquivAdicCompletion I` is a ring equivalence between
  the restricted subring and native
  `AdicCompletion (I.map MvPolynomial.C) (MvPolynomial σ R)`. It preserves
  finite-level evaluation and polynomial inclusion. Neither finite variables
  nor finite generation of `I` is assumed; completeness of arbitrary
  non-finitely-generated polynomial completions is **not** asserted. See the
  [equivalence and evaluation](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/InverseLimit.lean)
  and [completion guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/InverseLimit/README.md).

- **Coefficientwise kernel filtration.** For arbitrary variables, ideals and
  commutative coefficient rings, multiplying series whose coefficients lie in `J`
  and `K` gives coefficients in `J * K`. Hence products of restricted series
  vanishing under `adicReduction I n` and `adicReduction I k` vanish at
  `n + k`; finite sums and level-one errors obey the same law. This is **not**
  an identification with intrinsic restricted-ring ideal powers and does not
  require completeness or finite generation. See the
  [producer](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/KernelFiltration.lean),
  [guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/KernelFiltration/README.md)
  and [ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted/KernelFiltration.lean).

- **Generic linear extension.** Over `[CommRing R]` and `[IsAdicComplete I R]`,
  `restrictedLinearExtension I F` extends any polynomial `R`-linear endomorphism
  `F`, for arbitrary variable type and ideal. The quotient-polynomial operator
  commutes with reductions and level transitions; the extension preserves
  each coefficientwise reduction kernel and agrees on polynomials. Its
  uniqueness assumes **both** polynomial agreement and all-level kernel
  preservation. Finite polynomial levels keep its output restricted; no
  finite-variable, Noetherian, domain, nontriviality, intrinsic arbitrary-ideal
  kernel, or intrinsic restricted-ring completeness claim is added. See the
  [producer](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LinearExtension.lean),
  [guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LinearExtension/README.md)
  and [ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted/LinearExtension.lean).

- **Content and actual-ring leading terms.** Over separated prevaluation
  rings, restricted coefficient-content ideals have a generating coefficient
  and admit selected-coefficient factorization. Over a valuation domain,
  normalizing by content gives an intrinsic leading exponent; the leading
  **term itself is a polynomial over `R`**, not merely over the residue ring.
  See the [content and division guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/RestrictedDivision/README.md)
  and [leading-term client](Tests/MvPowerSeries/IdealAdicRestricted/LeadingTerm.lean).
- **Restricted division and conditional ideal generation.** Polynomial linear
  division and monic lifting are supplied by the pinned
  `multivariate-polynomials` library; this library extends/corrects division
  for restricted series. A finite primitive family in a restricted-series
  ideal generates that ideal **if its actual-`R` leading terms generate the
  full polynomial leading-term ideal**. No standard-basis existence,
  uniqueness, preparation or finite-variable assertion follows. See the
  [conditional-generation guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/PrimitiveStandardBasis/README.md)
  and [ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted/PrimitiveStandardBasis.lean).
- **Cofinal ideal-adic modules.** Under `I ≤ J`, `1 ≤ N` and `J ^ N ≤ I`,
  separation, precompleteness and completeness are equivalent for any
  `R`-module; this public generic support leaf requires no restricted series.
  See its [standalone guide](FormalPowerSeries/AdicCompletion/README.md).

The new restricted-series theorems do not assert norm/radius or variable-adic
restrictions, general base change, standard-basis existence, or source coverage.

## Build and use

Install Git and `elan`; `lean-toolchain` pins Lean `v4.34.0-rc2`, and
`lake-manifest.json` pins mathlib to
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and
MultivariatePolynomials to `b2f525056365c513029f3b0fae6d13c000a2b633`.
From the repository root:

```sh
lake exe cache get
lake build FormalPowerSeries Tests
```

Fetch the matching precompiled mathlib cache successfully **before** any build;
`lake build` alone is not a cache-fetch step. The default `lake build` also
builds these two roots, including all ordinary-import examples under `Tests/`.
For a smaller check, use `lake build FormalPowerSeries.UnitLogDerivative` or
`lake build FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.KernelFiltration`;
its matching test module can be built separately. `LEAN_NUM_THREADS=2` can
limit Lean's threads for a selective command, but does **not** bound Lake's
global job concurrency.

On the **previous** 32-file, 16-Lean-module graph (without this restricted
division transfer or MultivariatePolynomials), a configured CI runner fetched
8,892 decompressed mathlib-cache files in **41.558 seconds**, built cached
Mathlib in **5.586 seconds**, and built both roots in **17.123 seconds**
(**1,960 Lake jobs**). These are individual command wall times, not a
small-machine benchmark. The entire workflow took about **3 minutes
53 seconds** including setup, an axiom audit and artifact handling; it is
not the build command's duration. No peak RAM or disk use was measured.
For planning on a 4-core Linux machine with a matching precompiled cache,
allow roughly **10–50 minutes** for first setup and full build,
**1–15 minutes** for a small cached rebuild, and approximately **16 GiB
RAM and 20 GiB free disk** plus headroom. These smaller-machine figures are
**unvalidated estimates**, not measured peaks or guarantees; CPU, network,
cache state and competing jobs matter. These figures have **not** been
measured or validated on the expanded dependency graph.

In a dependent Lake project, pin this library and its dependencies to
published GitHub revisions and import `FormalPowerSeries` for both families
and the generic cofinal helper,
or import a producer directly: `FormalPowerSeries.UnitLogDerivative`,
`FormalPowerSeries.MvPowerSeries.IdealAdicRestricted` and its
`PrincipalKernel`, `LinearQuotient`, `InverseLimit`, `LinearExtension`,
`KernelFiltration`, `PrimitiveStandardBasis` or other restricted-series
submodules, or `FormalPowerSeries.AdicCompletion.Cofinal`. See [API.md](API.md)
for signatures and the
[restricted-series guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/README.md)
for the navigable family of modules. The [unit](Tests/UnitLogDerivative.lean),
[finite-reduction](Tests/MvPowerSeries/IdealAdicRestricted.lean),
[principal-kernel](Tests/MvPowerSeries/IdealAdicRestricted/PrincipalKernel.lean),
[linear-quotient](Tests/MvPowerSeries/IdealAdicRestricted/LinearQuotient.lean),
[completion](Tests/MvPowerSeries/IdealAdicRestricted/InverseLimit.lean),
[linear-extension](Tests/MvPowerSeries/IdealAdicRestricted/LinearExtension.lean)
and [filtration](Tests/MvPowerSeries/IdealAdicRestricted/KernelFiltration.lean)
clients demonstrate the earlier API; the ten new leaves under the same
`Tests/MvPowerSeries/IdealAdicRestricted/` directory exercise the added APIs.
For example:

```lean
theorem signedExample {T : Type*} [CommRing T]
    (a : T) (n : ℕ) :
    PowerSeries.coeff (n + 1)
      (PowerSeries.negXLogDeriv (PowerSeries.oneSubCXUnit a)) = a ^ (n + 1) :=
  PowerSeries.coeff_succ_negXLogDeriv_oneSubCXUnit a n
```

## Sources, contributors and rights

The integral unit formulas are related to Charles A. Weibel, *The K-book:
An Introduction to Algebraic K-theory* (2013), Section II.4 and Exercise
4.6. Kazuhiro Fujiwara and Fumiharu Kato, *Foundations of Rigid Geometry I*,
provide background for coefficientwise restricted series. Neither reference
implies formal coverage of the source. Prism authored the original derivative
proof expression; Formal Frontier AI contributors adapted it into this
source-independent library, wrote the ordinary-import client and guides,
and developed the independent restricted-series constructions and proofs.
Folio contributed the derivative headlines and documentation. Distinct Formal
Frontier contributors produced and later relocated/adapted the restricted
carrier, principal kernel, completion, scalar-linear quotient, linear
extension and coefficientwise kernel-filtration proofs; further contributors
developed content, selected factorization, actual leading terms, normalized
division, cofinal comparison and conditional primitive ideal generation.
This assembly does
not erase their original authorship. The antidiagonal coefficient-product
method adapts Jz Pan's 2025 mathlib `PowerSeries.CoeffMulMem` argument,
Apache-2.0, as credited in the [producer](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/KernelFiltration.lean).
Native mathlib polynomial, power-series, ideal, quotient and completion APIs
retain their respective authors and license; using these methods is not a
claim to their original proofs.

Original project files carry **SPDX-License-Identifier: Apache-2.0** and
**Authors: Formal Frontier Agents**; see the complete [LICENSE](LICENSE).
mathlib is separately licensed under Apache-2.0. The project used AI agents
for formalization and documentation. No source-coverage or publication decision
follows from these descriptions; the appropriate reviewed release and current
published revision are determined by the repository's official release record.
