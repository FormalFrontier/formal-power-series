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
terms, restricted division, first-variable polynomial preparation and
**conditional** primitive ideal generation.
Over an adically complete coefficient ring, units inside the restricted
subring are detected by the first polynomial reduction, or equivalently by
a unit constant coefficient and radical containment of all other coefficients.
Over finitely many variables it additionally characterizes restrictedness by
degree cutoffs and identifies the **intrinsic algebraic** reduction kernel
for finitely generated coefficient ideals at every level.
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
- **Ideal change and local residue.** An inclusion `I ≤ J` induces an injective
  map between restricted subrings and a surjective polynomial reduction modulo
  `J`. For a parameter in the maximal ideal of a local ring this gives a
  polynomial-valued residue homomorphism, agreeing with the existing residue
  function over valuation domains. See the [ideal-change guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/IdealChange/README.md)
  and [residue guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/ValuationResidue/README.md).
- **First-variable regrouping.** A restricted series in `Option τ` variables
  maps injectively into a power series of restricted series in `τ`; polynomial
  expressions in the distinguished variable embed in the reverse direction.
  Bijective renaming and the `Fin (n + 1)` bridge preserve coefficients and
  bounded-degree support. No equivalence with all iterated restricted series
  is asserted. See the [regrouping guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FirstVariableRegrouping/README.md).
- **Finite-variable degree cutoffs and FG intrinsic kernels.** For finite `σ`,
  coefficients are restricted exactly when they lie in `I ^ k` above some
  degree cutoff at each `k`; the converse fails for infinite `σ`, as the
  [ordinary-import counterexample](Tests/MvPowerSeries/IdealAdicRestricted/DegreeDecay.lean)
  demonstrates. If also `I.FG`, a restricted series with coefficients in
  `I ^ k` decomposes into finitely many restricted coefficient series times
  constants from `I ^ k`. Thus the kernel of `adicReduction I k` is the
  **algebraic image ideal inside the restricted subring**, including `k = 0`;
  this needs neither completeness nor regularity and makes no ambient-ideal
  or closure assertion. See the [degree guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/DegreeDecay/README.md),
  [FG kernel guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FinitelyGeneratedKernel/README.md)
  and [FG client](Tests/MvPowerSeries/IdealAdicRestricted/FinitelyGeneratedKernel.lean).
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

- **Restricted-subring units.** For arbitrary variables and ideals with
  `[IsAdicComplete I R]`, `isUnit_adicallyRestricted_iff_adicReduction_one`
  detects units *inside* the existing restricted subring by the unit of
  `adicReduction I 1 f`. The equivalent
  `isUnit_adicallyRestricted_iff_coeff_mod_ideal` tests a unit constant
  coefficient and nilpotent nonconstant coefficients in `R ⧸ I`;
  `isUnit_iff_quotient_of_isAdicComplete` reflects scalar units from that
  quotient; and `isUnit_adicallyRestricted_iff_coeff_radical` uses an actual
  unit constant coefficient and `I.radical` for the remaining coefficients.
  This requires no finite variables, finite generation, valuation or
  intrinsic `I*T` kernel identity. See the
  [unit guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/UnitDetection/README.md)
  and [ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted/UnitDetection.lean).

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
- **Singleton and first-variable division.** The intrinsic leading exponent of
  a product of nonzero restricted series is additive over a Hausdorff principal
  valuation domain. For a nonzero singleton divisor, any two supplied division
  equations with actual-supported remainders have the same quotient and
  remainder; existence is not asserted for arbitrary divisors. A primitive
  divisor admits such a pair under a nonzero parameter, radical equality and
  adic completeness. Under those same existence hypotheses, a primitive
  first-variable divisor with nonzero scalar top residue admits a unique
  finite-polynomial remainder even in degree zero. See the [singleton](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/SingletonDivision/README.md)
  and [first-variable](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FirstVariableDivision/README.md)
  guides and their ordinary-import clients.
- **Conditional quotient units.** Over a commutative local ring, for a parameter
  in its maximal ideal, a supplied division of the distinguished first-variable
  monomial `X₀^d` by a divisor whose regrouped residue has degree `d` and
  nonzero scalar top coefficient
  `C c`, with remainder coefficients vanishing at first exponents at least
  `d`, gives quotient residue `C (c⁻¹)`. Radical equality and adic completeness
  then reflect this to a unit of the restricted subring. The theorem does not
  construct a division or preparation. See the
  [quotient-unit guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FirstVariableUnit/README.md)
  and [client](FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/FirstVariableUnit.lean).
- **First-variable restricted preparation.** For a commutative valuation domain
  complete for the principal ideal of a nonzero parameter in its maximal ideal,
  with that ideal's radical equal to the maximal ideal, suppose an adically
  restricted series in `Fin (n + 1)` variables has regrouped maximal-ideal
  residue polynomial of degree `d` and nonzero scalar coefficient `C c` at
  `d`. Then `MvPowerSeries.existsUnique_firstVariable_preparation_of_scalar_top`
  gives a restricted unit `u` and a monic polynomial `G` in the first variable
  of exact degree `d` with `polynomialRestrictedFinFirst _ n G = u * f`.
  The pair is unique even among competing multipliers not assumed units;
  actual-coefficient primitivity follows from the scalar-top condition.
  Both `d = 0` and `n = 0` are included. See the
  [theorem](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FirstVariablePreparation.lean),
  [guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FirstVariablePreparation/README.md)
  and [ordinary-import client](FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/FirstVariablePreparation.lean).
- **Cofinal ideal-adic modules.** Under `I ≤ J`, `1 ≤ N` and `J ^ N ≤ I`,
  separation, precompleteness and completeness are equivalent for any
  `R`-module; this public generic support leaf requires no restricted series.
  See its [standalone guide](FormalPowerSeries/AdicCompletion/README.md).

These restricted-series theorems do not assert norm/radius or variable-adic
restrictions, general base change, standard-basis existence, or source coverage.

## Build and use

In a dependent Lake project, add:

```toml
[[require]]
name = "formal-power-series"
git = "https://github.com/FormalFrontier/formal-power-series.git"
rev = "main"
```

Lake pins the resolved release commit in `lake-manifest.json` until you update
the dependency; replace `main` with a particular release commit to pin it
explicitly.

Install Git and `elan`; `lean-toolchain` pins Lean `v4.34.0-rc2`, and
`lake-manifest.json` pins mathlib to
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and
MultivariatePolynomials to `c8c241ff6c686368aac35f8c3b4eed502d714bbd`.
From the repository root:

```sh
lake exe cache get
lake build FormalPowerSeries Tests FormalPowerSeriesTests
```

Fetch the matching precompiled mathlib cache successfully **before** any build;
`lake build` alone is not a cache-fetch step. The default `lake build` also
builds all three roots, including the ordinary-import examples under `Tests/`
and `FormalPowerSeriesTests/`.
For a smaller check, use `lake build FormalPowerSeries.UnitLogDerivative` or
`lake build FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.KernelFiltration`;
its matching test module can be built separately. The `DegreeDecay` and
`FinitelyGeneratedKernel` producer/client leaves can likewise be built by
their full module names after cache fetch. `LEAN_NUM_THREADS=2` can
limit Lean's threads for a selective command, but does **not** bound Lake's
global job concurrency.

Fetch the matching precompiled cache to avoid building mathlib from source;
for a narrower library check, build the relevant producer and test modules
separately.

Import `FormalPowerSeries` for both families and the generic cofinal helper,
or import a producer directly: `FormalPowerSeries.UnitLogDerivative`,
`FormalPowerSeries.MvPowerSeries.IdealAdicRestricted` and its
`DegreeDecay`, `FinitelyGeneratedKernel`, `PrincipalKernel`,
`LinearQuotient`, `InverseLimit`, `LinearExtension`, `KernelFiltration`,
`UnitDetection`, `PrimitiveStandardBasis` or other restricted-series
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
clients demonstrate the API; the
[restricted-unit client](Tests/MvPowerSeries/IdealAdicRestricted/UnitDetection.lean)
exercises the four unit criteria, though its `ZMod 4` polynomial witness
uses the polynomial-unit map rather than the coefficient criterion.
The degree and FG
[clients](Tests/MvPowerSeries/IdealAdicRestricted/FinitelyGeneratedKernel.lean)
extend its finite-variable boundaries, while the other leaves under the same
`Tests/MvPowerSeries/IdealAdicRestricted/` directory exercise further APIs.
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
proof expression; Formal Frontier AI contributors adapted its mathematical
argument for this library and wrote its ordinary-import client and guides.
Folio contributed the derivative headlines and documentation. Distinct Formal
Frontier contributors developed the restricted carrier, principal kernel,
completion, scalar-linear quotient, linear extension and coefficientwise
kernel-filtration proofs; other contributors developed content, selected
factorization, actual leading terms, normalized division, cofinal comparison
and conditional primitive ideal generation. Contributors to the finite-variable
degree criterion, its infinite-variable counterexample and the finite-generation
kernel argument were distinct from those who formalized these results and wrote
their ordinary-import clients. Further contributors developed and formalized
the restricted-subring unit criteria and wrote their ordinary-import client.
Formal Frontier AI contributors also developed the intrinsic leading-product,
singleton and first-variable division, residue reflection, conditional
quotient-unit and first-variable preparation arguments and their
ordinary-import clients; these results reuse the published restricted-series
foundation and polynomial lexicographic API.
The antidiagonal coefficient-product method adapts Jz Pan's 2025 mathlib
`PowerSeries.CoeffMulMem` argument,
Apache-2.0, as credited in the [producer](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/KernelFiltration.lean).
Native mathlib polynomial, power-series, ideal, quotient and completion APIs
retain their respective authors and license; using these methods is not a
claim to their original proofs.

Original project files carry **SPDX-License-Identifier: Apache-2.0** and
**Authors: Formal Frontier Agents**; see the complete [LICENSE](LICENSE).
mathlib is separately licensed under Apache-2.0. The project used AI agents
for formalization and documentation. These credits do not assert formal
coverage of either mathematical source.
