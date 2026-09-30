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
variable-adic restrictions, general base change, or preparation/division.
