# Formal power series

A Lean library for three independent constructions: the weighted negative
logarithmic derivative of native power-series units, the rational Artin–Hasse
exponential, and ideal-adically restricted native multivariate power series.
[Detailed results](RESULTS.md) gives detailed result descriptions, formulas,
material hypotheses, boundary cases and module links. For weighted-unit-derivative conventions, see
[API.md](API.md); for the other families, use the results and module guides.

## Headline results

### Weighted unit derivative

Over an arbitrary commutative ring `R`, for a native unit
`f : (PowerSeries R)ˣ`, `negXLogDeriv f = -X * f' * f⁻¹`, weighted by
**negative `X`**. Products become sums, inverses become negatives and integer
powers become integer multiples, naturally under coefficient-ring homomorphisms.
Integral convolution works without normalization; a division-free **forward**
recurrence for derivative coefficients requires constant coefficient one.
Linear factors `1 - C a * X` give signed power sums for finite products,
including inverse factors and the empty family.

This is neither reconstruction nor injectivity: constant units and, under
`[CharP R p]`, `p`-th powers lie in the kernel; even normalized nonidentity
units can do so. No formal logarithm, lambda/Witt structure, splitting extension
or Adams operation is asserted. See the [full formulas and limitations](RESULTS.md#weighted-unit-derivative)
and [source](FormalPowerSeries/UnitLogDerivative.lean).

### Rational Artin–Hasse exponential

The rational formal construction is defined for every natural `p` and has
constant and linear coefficients one. For `2 ≤ p` (composite `p` allowed), it is
`exp (∑ i ≥ 0, X^(p^i) / p^i)`; the coefficient recurrence together with
`a_0 = 1` determines it uniquely. The recurrence fails at `p = 1`, degree two.

For **prime `p` only**, its degree-`k` coefficient equals that of every finite
Euler product of `(1 - X^n)^(-μ(n)/n)` over positive `n ≤ N` coprime to `p`,
when `k ≤ N`. This is coefficientwise, not an infinite-product or analytic
convergence assertion. Prime `p` also gives coefficient p-integrality
(multiplicative p-adic valuation at most one), by an independent
Dieudonné–Dwork proof using p-adic divided powers, **not** the Euler identity.
The rational core does not import p-adic theory. See [details and examples](RESULTS.md#rational-artinhasse-exponential),
the [rational core](FormalPowerSeries/ArtinHasse.lean),
[Euler product](FormalPowerSeries/ArtinHasseEulerProduct.lean) and
[separate p-adic module](FormalPowerSeries/ArtinHasse/Padic.lean).

### Ideal-adically restricted multivariate series

For arbitrary variable types, commutative coefficient rings and ideals `I`,
restrictedness requires that, at each `k`, only finitely many **monomial indices**
have coefficients outside `I ^ k`. The restricted subring has surjective polynomial reductions, including
`k = 0`, ideal-change maps, and residue maps for parameters in a local ring's
maximal ideal.

- **Regrouping and kernels.** First-variable regrouping is injective, not an
  equivalence with all iterated restricted series. Finite variables give a
  degree-cutoff criterion; with `I.FG` they also identify the intrinsic
  algebraic reduction kernel at every level. Regular principal ideals admit
  internal division and scalar-linear quotient equivalences. For arbitrary
  variables and ideals, coefficientwise reduction kernels multiply from levels
  `n`, `k` into level `n + k`, without completeness or finite generation; this
  does **not** identify intrinsic ideal powers or give an arbitrary-ideal
  intrinsic kernel identity.
- **Completion and units.** Actual coefficient completeness
  `[IsAdicComplete I R]` gives a ring equivalence with the polynomial adic
  completion, for arbitrary variables and ideals; completeness of arbitrary
  polynomial completions is not asserted. Under the same hypothesis, a
  restricted series `f` is a unit exactly when `adicReduction I 1 f` is a unit,
  equivalently when its constant coefficient is a unit and every other
  coefficient lies in `I.radical`.
- **Linear extension.** Under `[IsAdicComplete I R]`, every polynomial
  `R`-linear endomorphism extends to an `R`-linear restricted-series operator
  with finite-level equations. Uniqueness needs **both** agreement on
  polynomials and preservation of **every** coefficientwise reduction kernel;
  no ring-homomorphism extension or intrinsic restricted-ring completeness is
  asserted. See the [extension guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LinearExtension/README.md).
- **Content, leading terms and division.** Separated prevaluation rings give
  selected-coefficient content factorization. Over a valuation domain separated
  for the principal ideal of a parameter in its maximal ideal, intrinsic
  leading terms are polynomials over the actual ring `R`. Any two supplied
  divisions by a nonzero singleton divisor with actual-supported remainders
  agree; arbitrary-divisor existence is not asserted. Primitive-divisor
  existence and conditional ideal generation additionally require a nonzero
  parameter, radical equal to the maximal ideal, and adic completeness.
  Under those hypotheses, a finite primitive family in a restricted-series
  ideal generates it **if** its actual-`R` leading terms generate the full
  polynomial leading-term ideal. No standard-basis existence is asserted;
  conditional quotient-unit reflection does not construct a division.
- **First-variable preparation.** Over a commutative valuation domain complete
  for the principal ideal of a nonzero parameter in its maximal ideal, with
  that ideal's radical equal to the maximal ideal, let a restricted series `f`
  in `Fin (n + 1)` variables have regrouped maximal-ideal residue polynomial
  of degree `d` with nonzero scalar top coefficient `C c`. There is a unique
  pair consisting of a restricted unit `u` and a monic first-variable polynomial
  `G` of exact degree `d` with `polynomialRestrictedFinFirst _ n G = u * f`.
  Actual-coefficient primitivity follows; uniqueness even allows competing
  multipliers not assumed units. **`n = 0` and `d = 0` are included**. See the
  [preparation guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FirstVariablePreparation/README.md).
- **Generic cofinal support.** For any `R`-module, `I ≤ J`, `1 ≤ N` and
  `J ^ N ≤ I` equate separation, precompleteness and completeness for the two
  filtrations; this separately importable result needs no restricted series.

See the [complete restricted-series results and limitations](RESULTS.md#ideal-adically-restricted-multivariate-series)
and [module guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/README.md).
These results do not assert norm/radius or variable-adic restrictions, general
base change, standard-basis existence, or source coverage.

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
lake build FormalPowerSeries FormalPowerSeriesTests
```

Fetch the matching precompiled mathlib cache successfully **before** any build;
`lake build` alone is not a cache-fetch step. The default `lake build` also
builds both roots, including the ordinary-import examples under
`FormalPowerSeriesTests/`.
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

### Client module migration

Client modules `Tests.<suffix>` moved to `FormalPowerSeriesTests.<suffix>`.
Replace `import Tests` and build target `Tests` with `FormalPowerSeriesTests`.
Build with `lake build FormalPowerSeries FormalPowerSeriesTests`.
Public declaration names and mathematical statements are unchanged; old client
imports and the old build target are not preserved.

Import `FormalPowerSeries` for these constructions and the generic cofinal
helper, or import a producer directly: `FormalPowerSeries.UnitLogDerivative`,
`FormalPowerSeries.ArtinHasse`, `FormalPowerSeries.ArtinHasseEulerProduct`,
`FormalPowerSeries.ArtinHasse.Padic`, `FormalPowerSeries.Binomial`,
`FormalPowerSeries.MvPowerSeries.IdealAdicRestricted` and its
`DegreeDecay`, `FinitelyGeneratedKernel`, `PrincipalKernel`,
`LinearQuotient`, `InverseLimit`, `LinearExtension`, `KernelFiltration`,
`UnitDetection`, `PrimitiveStandardBasis` or other restricted-series
submodules, or `FormalPowerSeries.AdicCompletion.Cofinal`. See [API.md](API.md)
for signatures and the
[restricted-series guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/README.md)
for the navigable family of modules. The [unit](FormalPowerSeriesTests/UnitLogDerivative.lean),
[finite-reduction](FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted.lean),
[principal-kernel](FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/PrincipalKernel.lean),
[linear-quotient](FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/LinearQuotient.lean),
[completion](FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/InverseLimit.lean),
[linear-extension](FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/LinearExtension.lean)
and [filtration](FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/KernelFiltration.lean)
clients demonstrate the API; the
[Artin–Hasse client](FormalPowerSeriesTests/ArtinHasse.lean) computes initial
rational coefficients from the recurrence. The
[restricted-unit client](FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/UnitDetection.lean)
exercises the four unit criteria, though its `ZMod 4` polynomial witness
uses the polynomial-unit map rather than the coefficient criterion.
The degree and FG
[clients](FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/FinitelyGeneratedKernel.lean)
extend its finite-variable boundaries, while the other leaves under the same
`FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/` directory exercise further APIs.
For example:

```lean
theorem signedExample {T : Type*} [CommRing T]
    (a : T) (n : ℕ) :
    PowerSeries.coeff (n + 1)
      (PowerSeries.negXLogDeriv (PowerSeries.oneSubCXUnit a)) = a ^ (n + 1) :=
  PowerSeries.coeff_succ_negXLogDeriv_oneSubCXUnit a n
```

## Sources, contributors and rights

Original project files carry **SPDX-License-Identifier: Apache-2.0** and
**Authors: Formal Frontier Agents**; see [LICENSE](LICENSE). See
[sources, contributors and rights](CREDITS.md) for mathematical references,
creative contributions, third-party adaptations, notices and caveats.
mathlib is separately licensed under Apache-2.0.
