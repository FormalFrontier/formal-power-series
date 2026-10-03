# Formal power series APIs

## Unit logarithmic derivative

Import `FormalPowerSeries` to obtain the `PowerSeries` namespace. All results
assume `[CommRing R]`, including characteristic-zero, finite torsion and zero
rings. The map accepts native `(PowerSeries R)ˣ`, not an ordinary series with
an unproved invertibility assumption. It is weighted by **negative `X`**:
it is not the unweighted analytic logarithmic derivative.

| Use | Declaration |
| --- | --- |
| Define `D f = -X * derivative (↑f) * ↑(f⁻¹)` | `PowerSeries.negXLogDeriv` |
| Characterize `D f` by `D f * ↑f = -X * derivative ↑f` | `negXLogDeriv_mul_value`, `eq_negXLogDeriv_iff` |
| Unit-group-to-additive laws | `negXLogDeriv_one`, `negXLogDeriv_mul`, `negXLogDeriv_inv`, `negXLogDeriv_pow`, `negXLogDeriv_zpow`, `negXLogDeriv_prod` |
| Map coefficient rings `R →+* S`, with independent universes | `negXLogDeriv_map` |
| Native additive-group homomorphism | `negXLogDerivHom : Additive ((PowerSeries R)ˣ) →+ PowerSeries R` |
| Constant and positive-characteristic power kernels | `negXLogDeriv_constant`, `negXLogDeriv_pow_char` |
| Degree zero and unnormalized finite convolution | `coeff_zero_negXLogDeriv`, `coeff_negXLogDeriv_convolution` |
| Finite recurrence **only if** `coeff 0 ↑f = 1` | `coeff_negXLogDeriv_recurrence` |
| Unit `1 - C a * X`, inverse coefficients `a^n` | `oneSubCXUnit`, `oneSubCXUnit_val`, `coeff_oneSubCXUnit_inv` |
| Weighted derivative and coefficient `a^(n+1)` | `negXLogDeriv_oneSubCXUnit`, `coeff_succ_negXLogDeriv_oneSubCXUnit` |

For `a_n = coeff n (f : PowerSeries R)` and
`b_n = coeff n (negXLogDeriv f)`, the unnormalized formula is
`∑ (i,j) ∈ Finset.antidiagonal (n+1), b_i * a_j = -(a_(n+1) * (n+1))`.
If `a_0=1`, the recurrence is
`b_(n+1) + ∑ i ∈ Finset.range n, a_(i+1) * b_(n-i) = -(a_(n+1) * (n+1))`.
This determines `b_(n+1)` with coefficient one; it **does not** divide by
`n+1` to determine `a_(n+1)`.

The default-built client `Tests/UnitLogDerivative.lean` exercises all API
families, including a nonnormalized integral unit; signed finite products
`∏ i ∈ s, (oneSubCXUnit (a i)) ^ (z i)` with coefficients
`∑ i ∈ s, (z i) • (a i) ^ (n+1)`; its empty family; independent-universe maps;
and a normalized, nonidentity characteristic-two unit in the kernel.
`derivative_map` is intentionally private: its coefficientwise proof is a
pin-specific implementation detail, not a competing public derivative API.

## Ideal-adically restricted multivariate series

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted` (or the umbrella
`FormalPowerSeries`). For any variable type `σ`, `[CommRing R]`, ideal
`I : Ideal R`, and series `f : MvPowerSeries σ R`, the predicate
`MvPowerSeries.IsAdicallyRestricted I f` means **finitely many monomial indices**
`m : σ →₀ ℕ` have `coeff m f ∉ I ^ k` at each `k : ℕ`. It does not mean finitely
many distinct coefficient values. No finite-variable, finite-generation,
completeness, norm, or proper-ideal hypothesis is imposed.

| Use | Declaration in `MvPowerSeries` |
| --- | --- |
| Characterize finite exceptions by the polynomial range of the quotient series, at one/all levels | `finite_exception_iff_map_mem_poly_range`, `isAdicallyRestricted_iff_map_mem_poly_range` |
| Restricted subring and membership | `adicallyRestrictedSubring`, `mem_adicallyRestrictedSubring` |
| Polynomial inclusion and coefficientwise compatibility | `map_polynomial_coe`, `isAdicallyRestricted_polynomial`, `polynomialToRestricted`, `polynomialToRestricted_coe` |
| Surjective ring homomorphism to `MvPolynomial σ (R ⧸ I ^ k)` | `adicReduction I k`, `adicReduction_surjective` |
| Embedded image, coefficient formula and polynomial reduction | `adicReduction_coe`, `coeff_adicReduction`, `adicReduction_polynomial` |

The result covers `k = 0`, empty or infinite variable types, and bottom or top
ideals. See the [finite-reduction guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/README.md)
and its [ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted.lean).

## Ideal change and polynomial residue

For `I ≤ J`, `restrictAlongIdeal I J` includes the `I`-restricted subring in
the `J`-restricted subring, preserving coefficients and polynomial inclusions;
its identity and composition laws allow chains of ideals. The surjective
`reductionAtLargerIdeal I J` maps to `MvPolynomial σ (R ⧸ J)` and has
coefficient, polynomial, vanishing, and quotient-factor compatibility laws.
See [ideal change](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/IdealChange.lean)
and its [client](FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/IdealChange.lean).

Over a commutative local ring, `restrictedResidueHom a ham` specializes this
map to the maximal ideal for `a` in that ideal. It is surjective without a
valuation or completeness assumption; under valuation-domain assumptions
`restrictedResidueHom_apply` identifies it with `restrictedResidue`. See
[residue compatibility](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/ValuationResidue.lean)
and its [client](FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/ValuationResidue.lean).

## First-variable coefficients and regrouping

`restrictedFirstCoeff I n` extracts a restricted coefficient series from
`Option τ` variables. `restrictedFirstRegroup I` is an injective ring map to
`PowerSeries (adicallyRestrictedSubring (σ := τ) I)`, compatible with the raw
`optionEquivLeft`. The embedding `polynomialRestrictedFirst I` has a coefficient
formula, is a left inverse to regrouping on polynomials, and gives the
bounded-degree support criterion `restrictedFirst_actual_support_iff`.
`restrictedRenameEquiv I e` transports restriction across a bijection of
variables. `restrictedFinSuccEquiv I n`, `restrictedFinFirstCoeff`, and
`polynomialRestrictedFinFirst` provide the `Fin (n + 1)` bridge, including
`n = 0`. These maps do not assert surjectivity of unrestricted iterated
power-series regrouping. See [regrouping](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FirstVariableRegrouping.lean),
[renaming](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/Rename.lean),
[Fin regrouping](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FirstVariableRegrouping/Fin.lean)
and the [client](FormalPowerSeriesTests/MvPowerSeries/IdealAdicRestricted/FirstVariableRegrouping.lean).

## Finite-variable degree cutoffs and finitely generated kernels

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.DegreeDecay` for
`MvPowerSeries.isAdicallyRestricted_iff_degree_cutoff I f`: under `[Finite σ]`,
`IsAdicallyRestricted I f` is equivalent to a cutoff **at each level** `k`
above which every coefficient of degree at least `d` belongs to `I ^ k`.
The finite-exception-to-cutoff direction needs no finite-variable assumption,
but its helper is private; the converse really needs finite variables (the
[ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted/DegreeDecay.lean)
contains an infinite-variable counterexample). See the
[degree guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/DegreeDecay/README.md).

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FinitelyGeneratedKernel`
for `[CommRing R] [Finite σ]`, `I : Ideal R`, `hI : I.FG`, any `k : ℕ`:

| Use | Public declaration in `MvPowerSeries` |
| --- | --- |
| Write a restricted series with coefficients in `I ^ k` as a finite sum of restricted series times constants from `I ^ k` | `exists_restricted_fg_decomposition` |
| Identify `RingHom.ker (adicReduction (σ := σ) I k)` with `Ideal.map ((polynomialToRestricted (σ := σ) I).comp MvPolynomial.C) (I ^ k)` inside the restricted subring | `ker_adicReduction_fg` |

These are algebraic, **intrinsic** restricted-series identities, not
closures or ambient-series assertions. No regularity, domain, completeness,
nontriviality, proper ideal, nonempty variables or positive `k` is assumed.
The [FG guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FinitelyGeneratedKernel/README.md)
and [ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted/FinitelyGeneratedKernel.lean)
give a practical kernel/quotient use and cover zero/top/zero-ring and nonregular
cases. The quotient equivalence in that client is **private**. The separate
regular-principal kernel theorem below works for arbitrary `σ`.

## Regular-principal internal kernel

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.PrincipalKernel`.
For `I = Ideal.span ({a} : Set R)` and **`ha : IsRegular a`**, the element
`principalAdicConstant (σ := σ) a k` is the image of `a ^ k` *inside*
`adicallyRestrictedSubring I`. The theorem
`exists_restricted_principal_quotient a ha k f hf` divides coefficients of
`f` by `a ^ k` and constructs the quotient within that same restricted subring;
`hf` states that every coefficient of `f` lies in `I ^ k`. The theorem
`ker_adicReduction_principal a ha k` identifies the actual kernel of
`adicReduction I k` with the ideal spanned by `principalAdicConstant a k`
in the restricted subring. No arbitrary-ideal internal division is asserted.
See the [kernel guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/PrincipalKernel/README.md)
and its [client](Tests/MvPowerSeries/IdealAdicRestricted/PrincipalKernel.lean).

## Scalar-linear reduction and principal quotients

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearQuotient`.
The existing restricted subring `S := adicallyRestrictedSubring (σ := σ) I`
acquires `adicallyRestrictedAlgebra I : Algebra R S`, whose constants and
coefficientwise scalar action are computed by
`algebraMap_adicallyRestricted_coe`, `coe_smul_adicallyRestricted`, and
`coeff_smul_adicallyRestricted`. For every `I : Ideal R`, variable type `σ`,
`[CommRing R]` and `k : ℕ`, `algebraAdicReduction I k` bundles the existing
`adicReduction I k` as an `R`-algebra map, while `linearAdicReduction I k`
bundles it as a surjective `R`-linear map. The `linearAdicReduction_apply`,
`coeff_linearAdicReduction`, and `linearAdicReduction_surjective` lemmas give
its value, coefficient law, and surjectivity at **every** level, including zero.

For the principal ideal `I := Ideal.span ({a} : Set R)`,
`principalAdicConstant_mul_eq_smul` relates multiplication by `a ^ k` to
scalar multiplication without regularity. With `ha : IsRegular a`,
`ker_linearAdicReduction_principal`
identifies the **`R`-submodule** kernel as `I ^ k • (⊤ : Submodule R S)`.
`principalLinearQuotientEquiv a ha k` is the `R`-linear equivalence
`S ⧸ (I ^ k • ⊤) ≃ₗ[R] MvPolynomial σ (R ⧸ I ^ k)`;
`principalLinearQuotientEquiv_mk` sends the class of `f` to
`adicReduction I k f`. This is not the earlier **ring-ideal** kernel theorem,
a ring quotient, or automatically an `R ⧸ I ^ k`-linear equivalence.

For `R = ℤ`, use the separately bundled native-default `intLinearAdicReduction`
and `principalIntLinearQuotientEquiv` for dependent `Submodule ℤ S` and
quotient types; their `apply`, `coeff`, `surjective`, principal-kernel and
representative lemmas match the generic laws without overriding module-instance
priority. See the [linear quotient guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LinearQuotient/README.md)
and [ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted/LinearQuotient.lean)
for both routes, including zero levels and a regular nonunit over `ℤ × ℤ`.

## Coefficientwise kernel products

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.KernelFiltration`.
For arbitrary `σ`, `[CommRing R]` and ideals `J K I : Ideal R`, no
finite-variable, finite-generation, completeness or nontriviality assumption
is required. With `ρ n := adicReduction I n` on the restricted subring:

| Use | Declaration in `MvPowerSeries` |
| --- | --- |
| Coefficients in `J` times coefficients in `K` give product coefficients in `J * K` | `coeff_mul_mem_ideal_mul_ideal` |
| `ρ n a = 0` and `ρ k b = 0` imply `ρ (n + k) (a * b) = 0` | `adicReduction_mul_eq_zero` |
| Finite sums of products at fixed levels `n` and `k` | `adicReduction_sum_mul_eq_zero` |
| Finite sums with the second factors at level one | `adicReduction_sum_mul_eq_zero_succ` |

These are statements about **coefficientwise** reduction kernels, not
intrinsic ideal powers in the restricted subring. Levels may be zero; the
[standalone guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/KernelFiltration/README.md)
and [ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted/KernelFiltration.lean)
also cover empty families and variables, bottom/top ideals and zero rings.
The producer imports the restricted-series base and pinned mathlib ideal
operations, independently of linear extension, quotients and completeness.

## Units in the restricted subring

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.UnitDetection`
(or `FormalPowerSeries`). For arbitrary `σ`, `[CommRing R]`, `I : Ideal R`
and `[IsAdicComplete I R]`, take
`f : adicallyRestrictedSubring (σ := σ) I`. These results concern **units in
that subring**, not just units of `MvPowerSeries σ R`.

| Use | Declaration in `MvPowerSeries` |
| --- | --- |
| Unit iff `adicReduction I 1 f` is a unit in `MvPolynomial σ (R ⧸ I ^ 1)` | `isUnit_adicallyRestricted_iff_adicReduction_one I f` |
| Unit iff the constant coefficient modulo `I` is a unit and nonconstant coefficients modulo `I` are nilpotent | `isUnit_adicallyRestricted_iff_coeff_mod_ideal I f` |
| Scalar unit iff its image in `R ⧸ I` is a unit | `isUnit_iff_quotient_of_isAdicComplete I r` |
| Unit iff the actual constant coefficient is a unit and all nonconstant coefficients belong to `I.radical` | `isUnit_adicallyRestricted_iff_coeff_radical I f` |

The first criterion lifts a polynomial inverse and uses coefficientwise
kernel contraction and the geometric inverse to invert inside the restricted
subring. The quotient-coefficient criterion transports `I ^ 1 = I` explicitly.
No finite-variable, finitely generated ideal, domain, valuation, nontriviality
or unproved identification with intrinsic restricted-ring ideal powers is
assumed. See the [standalone guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/UnitDetection/README.md)
and [ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted/UnitDetection.lean).
The client's `ZMod 4` witness uses the older polynomial-unit inclusion, not
the new criterion for a nonzero nilpotent nonconstant coefficient.

## Linear polynomial operators on restricted series

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearExtension`.
For any `σ`, `[CommRing R]`, ideal `I : Ideal R` and
`[IsAdicComplete I R]`, every `R`-linear endomorphism
`F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R` extends to an `R`-linear
endomorphism of `adicallyRestrictedSubring (σ := σ) I`. Completeness
is assumed for **coefficients**, not separately for the restricted subring.

| Use | Declaration in `MvPowerSeries` |
| --- | --- |
| Finite quotient-polynomial operator, reduction of an original polynomial and compatibility between levels `m ≤ n` | `polynomialLinearMapMod`, `polynomialLinearMapMod_map`, `polynomialLinearMapMod_factorPow` |
| Canonical `R`-linear restricted-series extension | `restrictedLinearExtension` |
| Defining reduction law and polynomial agreement | `adicReduction_restrictedLinearExtension`, `restrictedLinearExtension_polynomial` |
| Preserve every coefficientwise reduction kernel | `restrictedLinearExtension_preserves_ker` |
| Unique `R`-linear extension **given polynomial agreement and all-level kernel preservation** | `restrictedLinearExtension_unique` |

Each output has finite polynomial reduction at every level. Neither
finite-variable, Noetherian, domain nor nontriviality assumptions are added.
No arbitrary-ideal identity with the intrinsic submodule `I ^ n • ⊤`, or
intrinsic restricted-ring completeness, is claimed. See the
[extension guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LinearExtension/README.md)
and [ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted/LinearExtension.lean)
for the identity, level-zero, empty-variable, zero-ideal and zero-ring cases.

## Polynomial adic completion

Import `FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.InverseLimit`.
For any `σ`, `[CommRing R]`, `I : Ideal R` and **`[IsAdicComplete I R]`**,
`adicallyRestrictedEquivAdicCompletion I` identifies
`adicallyRestrictedSubring (σ := σ) I` with the native
`AdicCompletion (I.map MvPolynomial.C) (MvPolynomial σ R)` as rings. The
coefficients, not the polynomial completion at arbitrary non-finitely-generated
ideals, are assumed adically complete.

| Use | Declaration in `MvPowerSeries` |
| --- | --- |
| Quotient-power polynomial level equivalence and representative | `adicPolynomialLevelEquiv I n`, `adicPolynomialLevelEquiv_mk` |
| Quotient transition compatibility | `adicPolynomialLevelEquiv_factorPow`, `adicReduction_factorPow` |
| Forward/inverse evaluation at every level | `adicallyRestrictedEquivAdicCompletion_eval`, `adicallyRestrictedEquivAdicCompletion_symm_eval` |
| Polynomial inclusion and native completion map agree | `adicallyRestrictedEquivAdicCompletion_polynomial` |

See the [completion guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/InverseLimit/README.md)
and [client](Tests/MvPowerSeries/IdealAdicRestricted/InverseLimit.lean).
These multivariate coefficient-adic APIs are independent of the single-variable
unit logarithmic derivative. They do not provide norm/radius-weighted or
variable-adic restrictions or general base change. Restricted division under
additional hypotheses is documented below; there is no preparation theorem.

## Cofinal filtrations and coefficient content

The separately importable `FormalPowerSeries.AdicCompletion.Cofinal` has three
**global public** results for arbitrary `[CommRing R]`, `[AddCommGroup M]`,
`[Module R M]`, `I ≤ J`, `1 ≤ N` and `J ^ N ≤ I`:
`isHausdorff_iff_of_cofinal`, `isPrecomplete_iff_of_cofinal` and
`isAdicComplete_iff_of_cofinal`. The distinct
`MvPowerSeries.isAdicallyRestricted_iff_of_cofinal` compares restriction
of the *same* series to these two ideals. See the
[module guide](FormalPowerSeries/AdicCompletion/README.md).

Over `[PreValuationRing R]` and `[IsHausdorff I R]`, import the `Content`
and `SelectedFactor` restricted-series leaves for
`MvPowerSeries.IsAdicallyRestricted.exists_span_range_eq_span_coeff` and
`MvPowerSeries.IsAdicallyRestricted.exists_selected_coeff_factor`. Over a
valuation domain with a separated principal filtration, `LeadingTerm`
supplies `MvPowerSeries.restrictedContentIndex`, `restrictedResidue` and
`MonomialOrder.restrictedLeadingExponent`, `restrictedLeadingTerm`,
`restrictedLeadingTermIdeal`. The residue is a polynomial over `R ⧸ m`;
**leading terms and their ideal are over `R`**. These constructions allow
empty or infinite variable types. See the
[content and division guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/RestrictedDivision/README.md).

## Restricted division and conditional ideal generation

`MonicParameter` chooses a common normalization parameter for a finite
primitive valuation-domain family. With `[IsAdicComplete I R]`, the
`PolynomialDivision` leaf extends pinned MultivariatePolynomials fixed
polynomial quotient/remainder operators to restricted series. The
`RestrictedGeometricInverse`, `PerturbedDivision` and `MonicDivision` leaves
correct division by finite restricted divisors, using the existing
`LinearExtension` and `KernelFiltration` leaves and dependency-provided
`MultivariatePolynomials.LinearDivision`/`MonicLift`.

For a nonzero `a` in the valuation domain's maximal ideal satisfying
`(Ideal.span {a}).radical = IsLocalRing.maximalIdeal R` and
`[IsAdicComplete (Ideal.span {a}) R]`,
`MonomialOrder.exists_restricted_primitive_division` gives existential
quotients and a remainder for a finite family with actual coefficient-content
ideal `⊤`. The remainder has zero **R-valued** coefficients on componentwise
leading cones. Finally `MonomialOrder.ideal_eq_span_of_primitive_standardBasis`
assumes a finite primitive family `g i ∈ J` and the equality
`μ.restrictedLeadingTermIdeal a ham J = Ideal.span (Set.range (fun i => μ.restrictedLeadingTerm a ham (g i)))`;
it concludes `J = Ideal.span (Set.range g)`. The latter is a *conditional*
ideal-generation theorem, not existence of a standard basis, unique division,
preparation or source-specific coverage. See the
[precise theorem guide](FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/PrimitiveStandardBasis/README.md)
and [ordinary-import client](Tests/MvPowerSeries/IdealAdicRestricted/PrimitiveStandardBasis.lean).
