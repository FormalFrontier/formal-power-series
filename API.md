# Unit logarithmic derivative API

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
