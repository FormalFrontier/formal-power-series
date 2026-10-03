/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FirstVariableUnit

/-!
# Clients and boundaries for first-variable quotient units

Examples compute a unit residue, apply conditional division to a monomial,
and check the zero-degree, zero-remaining-variable witness and missing-support
boundary.
-/

public section

set_option warningAsError true

open MvPowerSeries

section LocalRingExamples

variable {R : Type*} [CommRing R] [IsLocalRing R]
    (b : R) (hbm : b ∈ IsLocalRing.maximalIdeal R)
    (hbrad : (Ideal.span {b}).radical = IsLocalRing.maximalIdeal R)
    [IsAdicComplete (Ideal.span {b}) R]

include hbm hbrad
/-- An explicit restricted polynomial whose maximal-ideal residue is one is a unit. -/
theorem isUnit_polynomialToRestricted_one_add_C_mul_X {σ : Type*} (i : σ) :
    IsUnit (polynomialToRestricted (Ideal.span {b})
      (1 + MvPolynomial.C b * MvPolynomial.X i)) := by
  have hb : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) b =
      (0 : R ⧸ IsLocalRing.maximalIdeal R) :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hbm
  have hres : restrictedResidueHom b hbm
      (polynomialToRestricted (Ideal.span {b})
        (1 + MvPolynomial.C b * MvPolynomial.X i)) =
        (1 : MvPolynomial σ (R ⧸ IsLocalRing.maximalIdeal R)) := by
    have hzero : restrictedResidueHom (σ := σ) b hbm
        (polynomialToRestricted (Ideal.span {b}) (MvPolynomial.C b : MvPolynomial σ R)) =
        (0 : MvPolynomial σ (R ⧸ IsLocalRing.maximalIdeal R)) := by
      classical
      apply MvPolynomial.ext
      intro α
      rw [coeff_restrictedResidueHom, polynomialToRestricted_coe,
        MvPolynomial.coe_C, MvPowerSeries.coeff_C]
      simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      split_ifs
      · exact hb
      · exact map_zero _
    simp only [map_add, map_one, map_mul, hzero, zero_mul, add_zero]
  apply isUnit_of_isUnit_restrictedResidueHom b hbm hbrad
  rw [hres]
  exact isUnit_one

private theorem isUnit_monomial_quotient (n d : ℕ)
    (q r : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {b}))
    (heq : polynomialRestrictedFinFirst (Ideal.span {b}) n (Polynomial.X ^ d) =
      q * polynomialRestrictedFinFirst (Ideal.span {b}) n (Polynomial.X ^ d) + r)
    (hactual : ∀ (i : ℕ) (β : Fin n →₀ ℕ), d ≤ i →
      coeff (β.cons i) (r : MvPowerSeries (Fin (n + 1)) R) = 0) :
    IsUnit q := by
  have hF : MvPolynomial.finSuccEquiv _ n (restrictedResidueHom b hbm
      (polynomialRestrictedFinFirst (Ideal.span {b}) n (Polynomial.X ^ d))) =
      Polynomial.X ^ d := by
    simpa only [Polynomial.map_pow, Polynomial.map_X] using
      (finSuccEquiv_restrictedResidueHom_polynomialRestrictedFinFirst b hbm n
        (Polynomial.X ^ d))
  apply isUnit_quotient_of_restrictedFinFirst_divisionHom b hbm n d hbrad
    (polynomialRestrictedFinFirst (Ideal.span {b}) n (Polynomial.X ^ d)) q r 1 one_ne_zero
  · simp only [hF, Polynomial.natDegree_X_pow]
  · simp only [hF, Polynomial.coeff_X_pow_self, map_one]; rfl
  · exact heq
  · exact hactual

example (n d : ℕ)
    (q r : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {b}))
    (heq : polynomialRestrictedFinFirst (Ideal.span {b}) n (Polynomial.X ^ d) =
      q * polynomialRestrictedFinFirst (Ideal.span {b}) n (Polynomial.X ^ d) + r)
    (hactual : ∀ (i : ℕ) (β : Fin n →₀ ℕ), d ≤ i →
      coeff (β.cons i) (r : MvPowerSeries (Fin (n + 1)) R) = 0) :
    IsUnit q :=
  isUnit_monomial_quotient b hbm hbrad n d q r heq hactual

example (n : ℕ)
    (q r : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {b}))
    (heq : polynomialRestrictedFinFirst (Ideal.span {b}) n (Polynomial.X ^ 0) =
      q * polynomialRestrictedFinFirst (Ideal.span {b}) n (Polynomial.X ^ 0) + r)
    (hactual : ∀ (i : ℕ) (β : Fin n →₀ ℕ),
      coeff (β.cons i) (r : MvPowerSeries (Fin (n + 1)) R) = 0) :
    IsUnit q := by
  apply isUnit_monomial_quotient b hbm hbrad n 0 q r heq
  intro i β _
  exact hactual i β

example (d : ℕ)
    (q r : adicallyRestrictedSubring (σ := Fin (0 + 1)) (Ideal.span {b}))
    (heq : polynomialRestrictedFinFirst (Ideal.span {b}) 0 (Polynomial.X ^ d) =
      q * polynomialRestrictedFinFirst (Ideal.span {b}) 0 (Polynomial.X ^ d) + r)
    (hactual : ∀ (i : ℕ) (β : Fin 0 →₀ ℕ), d ≤ i →
      coeff (β.cons i) (r : MvPowerSeries (Fin (0 + 1)) R) = 0) :
    IsUnit q :=
  isUnit_monomial_quotient b hbm hbrad 0 d q r heq hactual

end LocalRingExamples

section RationalBoundaries

private theorem rational_zero_mem_maximalIdeal :
    (0 : ℚ) ∈ IsLocalRing.maximalIdeal ℚ :=
  (IsLocalRing.maximalIdeal ℚ).zero_mem

private instance : IsAdicComplete (Ideal.span {(0 : ℚ)}) ℚ := by
  rw [Ideal.span_singleton_eq_bot.mpr rfl]
  infer_instance

example :
    IsUnit (1 : adicallyRestrictedSubring (σ := Fin (0 + 1))
      (Ideal.span {(0 : ℚ)})) := by
  have hzero : Ideal.span {(0 : ℚ)} = (⊥ : Ideal ℚ) :=
    Ideal.span_singleton_eq_bot.mpr rfl
  have hrad : (Ideal.span {(0 : ℚ)}).radical = IsLocalRing.maximalIdeal ℚ := by
    rw [hzero, Ideal.radical_bot_of_isReduced, IsLocalRing.maximalIdeal_eq_bot]
  have hF : MvPolynomial.finSuccEquiv _ 0
      (restrictedResidueHom (0 : ℚ) rational_zero_mem_maximalIdeal
        (polynomialRestrictedFinFirst (Ideal.span {(0 : ℚ)}) 0 (Polynomial.X ^ 0))) =
      Polynomial.X ^ 0 := by
    simp only [pow_zero, map_one]
  apply isUnit_quotient_of_restrictedFinFirst_divisionHom
    (0 : ℚ) rational_zero_mem_maximalIdeal 0 0 hrad
    (polynomialRestrictedFinFirst (Ideal.span {(0 : ℚ)}) 0 (Polynomial.X ^ 0))
    1 0 1 one_ne_zero
  · simp only [hF, Polynomial.natDegree_X_pow]
  · simp only [hF, Polynomial.coeff_X_pow_self, map_one]; rfl
  · simp
  · intro i β _
    simp

example :
    polynomialRestrictedFinFirst (Ideal.span {(0 : ℚ)}) 0 (Polynomial.X ^ 0) =
      (0 : adicallyRestrictedSubring (σ := Fin (0 + 1)) (Ideal.span {(0 : ℚ)})) * 1 + 1 ∧
    (1 : IsLocalRing.ResidueField ℚ) ≠ 0 ∧
    (MvPolynomial.finSuccEquiv _ 0
      (restrictedResidueHom (0 : ℚ) rational_zero_mem_maximalIdeal
        (1 : adicallyRestrictedSubring (σ := Fin (0 + 1))
          (Ideal.span {(0 : ℚ)})))).natDegree = 0 ∧
    (MvPolynomial.finSuccEquiv _ 0
      (restrictedResidueHom (0 : ℚ) rational_zero_mem_maximalIdeal
        (1 : adicallyRestrictedSubring (σ := Fin (0 + 1))
          (Ideal.span {(0 : ℚ)})))).coeff 0 =
        MvPolynomial.C (1 : IsLocalRing.ResidueField ℚ) ∧
    ¬ IsUnit (0 : adicallyRestrictedSubring (σ := Fin (0 + 1))
      (Ideal.span {(0 : ℚ)})) ∧
    ¬ ∀ (i : ℕ) (β : Fin 0 →₀ ℕ), 0 ≤ i →
      coeff (β.cons i)
        ((1 : adicallyRestrictedSubring (σ := Fin (0 + 1))
          (Ideal.span {(0 : ℚ)})) : MvPowerSeries (Fin (0 + 1)) ℚ) = 0 := by
  refine ⟨by simp, one_ne_zero, by simp,
    by simp; rfl, not_isUnit_zero, ?_⟩
  intro hsupport
  have hcoeff := hsupport 0 (0 : Fin 0 →₀ ℕ) (Nat.zero_le 0)
  have hone : (1 : ℚ) = 0 := by
    simpa only [Finsupp.cons_zero_zero, Subring.coe_one,
      MvPowerSeries.coeff_zero_one] using hcoeff
  exact one_ne_zero hone

end RationalBoundaries
