/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.BigOperators

public section

/-!
# Coefficientwise ideal-adic kernels and products

Multiplying series whose coefficients lie in ideals `J` and `K` puts every
coefficient of the product in `J * K`. In particular, the kernels of finite
polynomial reductions of restricted series satisfy `Kₙ * Kₖ ⊆ Kₙ₊ₖ`.
This is a statement about coefficientwise kernels, not intrinsic powers of an
ideal in the restricted subring. Neither the variables nor the ideals need be
finite or finitely generated.

The antidiagonal proof follows the one-variable argument of Jz Pan in mathlib's
`Mathlib.RingTheory.PowerSeries.CoeffMulMem` (2025, Apache-2.0).
-/

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

/-- Coefficientwise ideal membership is multiplicative for arbitrary-variable
multivariate power series. -/
theorem coeff_mul_mem_ideal_mul_ideal {J K : Ideal R}
    {f g : MvPowerSeries σ R} (hf : ∀ m, coeff m f ∈ J)
    (hg : ∀ m, coeff m g ∈ K) (m : σ →₀ ℕ) :
    coeff m (f * g) ∈ J * K := by
  classical
  rw [coeff_mul]
  exact Ideal.sum_mem _ (fun p _ => Ideal.mul_mem_mul (hf p.1) (hg p.2))

/-- Zero finite reductions multiply into the kernel at the sum of their levels,
including level zero and with no finiteness assumption on the variables. -/
theorem adicReduction_mul_eq_zero (I : Ideal R)
    (a b : adicallyRestrictedSubring (σ := σ) I) (n k : ℕ)
    (ha : adicReduction I n a = 0) (hb : adicReduction I k b = 0) :
    adicReduction I (n + k) (a * b) = 0 := by
  have ha_coeff (m : σ →₀ ℕ) : coeff m (a : MvPowerSeries σ R) ∈ I ^ n := by
    apply (Ideal.Quotient.eq_zero_iff_mem).1
    rw [← coeff_adicReduction, ha]
    simp
  have hb_coeff (m : σ →₀ ℕ) : coeff m (b : MvPowerSeries σ R) ∈ I ^ k := by
    apply (Ideal.Quotient.eq_zero_iff_mem).1
    rw [← coeff_adicReduction, hb]
    simp
  apply MvPolynomial.ext
  intro m
  simp only [coeff_adicReduction, AddMonoidAlgebra.coeff_zero]
  apply (Ideal.Quotient.eq_zero_iff_mem).2
  rw [Subring.coe_mul, pow_add]
  exact coeff_mul_mem_ideal_mul_ideal ha_coeff hb_coeff m

/-- A finite sum of products of elements in two fixed coefficientwise kernels
lies in the kernel at the sum of their levels. -/
theorem adicReduction_sum_mul_eq_zero {ι : Type*} (I : Ideal R)
    (s : Finset ι) (a b : ι → adicallyRestrictedSubring (σ := σ) I)
    (n k : ℕ) (ha : ∀ i ∈ s, adicReduction I n (a i) = 0)
    (hb : ∀ i ∈ s, adicReduction I k (b i) = 0) :
    adicReduction I (n + k) (∑ i ∈ s, a i * b i) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero (fun i hi => adicReduction_mul_eq_zero I (a i) (b i) n k
    (ha i hi) (hb i hi))

/-- The finite-sum specialization for products with level-one errors. -/
theorem adicReduction_sum_mul_eq_zero_succ {ι : Type*} (I : Ideal R)
    (s : Finset ι) (a b : ι → adicallyRestrictedSubring (σ := σ) I)
    (n : ℕ) (ha : ∀ i ∈ s, adicReduction I n (a i) = 0)
    (hb : ∀ i ∈ s, adicReduction I 1 (b i) = 0) :
    adicReduction I (n + 1) (∑ i ∈ s, a i * b i) = 0 :=
  adicReduction_sum_mul_eq_zero I s a b n 1 ha hb

end MvPowerSeries
