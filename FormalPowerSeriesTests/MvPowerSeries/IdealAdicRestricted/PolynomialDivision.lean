/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.PolynomialDivision
public import Mathlib.Data.ZMod.Basic

public section

/-! Ordinary-import clients of the restricted polynomial division interface. -/

set_option warningAsError true

namespace Tests.RestrictedPolynomialDivision

open MvPowerSeries

variable {σ ι R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
variable (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
variable (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))

private theorem linearity (r : R) (f g : adicallyRestrictedSubring (σ := σ) I) :
    m.restrictedDivisionRemainder I b hb (f + r • g) =
      m.restrictedDivisionRemainder I b hb f + r • m.restrictedDivisionRemainder I b hb g ∧
    m.restrictedDivisionQuotient I b hb (f + r • g) =
      m.restrictedDivisionQuotient I b hb f + r • m.restrictedDivisionQuotient I b hb g := by
  exact ⟨by simp, by simp⟩

private theorem polynomial_input (p : MvPolynomial σ R) (i : ι) :
    m.restrictedDivisionRemainder I b hb (polynomialToRestricted I p) =
      polynomialToRestricted I (m.linearDivisionRemainder b hb p) ∧
    m.restrictedDivisionQuotient I b hb (polynomialToRestricted I p) i =
      polynomialToRestricted I (m.linearDivisionQuotient b hb p i) := by
  exact ⟨m.restrictedDivisionRemainder_polynomial I b hb p,
    m.restrictedDivisionQuotient_polynomial I b hb p i⟩

private theorem kernel_and_cone (n : ℕ) (f : adicallyRestrictedSubring (σ := σ) I)
    (hf : adicReduction I n f = 0) (i : ι) (α : σ →₀ ℕ)
    (hα : m.degree (b i) ≤ α) :
    adicReduction I n (m.restrictedDivisionRemainder I b hb f) = 0 ∧
    adicReduction I n (m.restrictedDivisionQuotient I b hb f i) = 0 ∧
    coeff α ((m.restrictedDivisionRemainder I b hb f :
      adicallyRestrictedSubring (σ := σ) I) : MvPowerSeries σ R) = 0 := by
  exact ⟨m.restrictedDivisionRemainder_preserves_ker I b hb n f hf,
    m.restrictedDivisionQuotient_preserves_ker I b hb n f hf i,
    m.coeff_restrictedDivisionRemainder_eq_zero I b hb f α i hα⟩

private theorem finite_family [Fintype ι]
    (f : adicallyRestrictedSubring (σ := σ) I) :
    f = (∑ i, m.restrictedDivisionQuotient I b hb f i *
      polynomialToRestricted I (b i)) + m.restrictedDivisionRemainder I b hb f :=
  m.restrictedDivision_decomposition I b hb f

private theorem empty_family (f : adicallyRestrictedSubring (σ := σ) I) :
    f = (∑ i : Fin 0,
        m.restrictedDivisionQuotient I (fun j : Fin 0 => j.elim0)
            (fun j : Fin 0 => j.elim0) f i *
          polynomialToRestricted I ((fun j : Fin 0 => j.elim0) i : MvPolynomial σ R)) +
      m.restrictedDivisionRemainder I (fun j : Fin 0 => j.elim0)
        (fun j : Fin 0 => j.elim0) f :=
  m.restrictedDivision_decomposition I _ _ f

private theorem empty_variables (m : MonomialOrder Empty)
    (b : Fin 1 → MvPolynomial Empty R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (f : adicallyRestrictedSubring (σ := Empty) I) :
    f = (∑ i, (m.restrictedDivisionQuotient I b hb f i) *
      polynomialToRestricted I (b i)) + m.restrictedDivisionRemainder I b hb f :=
  m.restrictedDivision_decomposition I b hb f

private theorem zero_ideal (m : MonomialOrder (Fin 1))
    (f : adicallyRestrictedSubring (σ := Fin 1) (⊥ : Ideal R))
    [IsAdicComplete (⊥ : Ideal R) R] :
    f = (∑ i : Fin 0,
        m.restrictedDivisionQuotient (⊥ : Ideal R)
          (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0) f i *
        polynomialToRestricted (⊥ : Ideal R)
          ((fun j : Fin 0 => j.elim0) i : MvPolynomial (Fin 1) R)) +
        m.restrictedDivisionRemainder (⊥ : Ideal R)
          (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0) f :=
  m.restrictedDivision_decomposition (⊥ : Ideal R) _ _ f

private theorem zero_ring (I : Ideal (ZMod 1)) [IsAdicComplete I (ZMod 1)]
    (m : MonomialOrder Empty)
    (f : adicallyRestrictedSubring (σ := Empty) I) :
    f = (∑ i : Fin 0,
        m.restrictedDivisionQuotient I
          (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0) f i *
        polynomialToRestricted I ((fun j : Fin 0 => j.elim0) i :
          MvPolynomial Empty (ZMod 1))) +
        m.restrictedDivisionRemainder I
          (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0) f :=
  m.restrictedDivision_decomposition I _ _ f

private theorem level_zero (f : adicallyRestrictedSubring (σ := σ) I)
    (i : ι) : adicReduction I 0 (m.restrictedDivisionQuotient I b hb f i) = 0 := by
  have hzero : Subsingleton (R ⧸ I ^ 0) :=
    Ideal.Quotient.subsingleton_iff.mpr (by simp)
  apply MvPolynomial.ext
  intro index
  exact @Subsingleton.elim _ hzero _ _

/-- Division by `X` has remainder with vanishing coefficients in the `X` cone. -/
theorem X_divisor_cone (I : Ideal R) [IsAdicComplete I R]
    (m : MonomialOrder (Fin 1))
    (f : adicallyRestrictedSubring (σ := Fin 1) I) (α : Fin 1 →₀ ℕ)
    (hα : m.degree (MvPolynomial.X 0 : MvPolynomial (Fin 1) R) ≤ α) :
    coeff α ((m.restrictedDivisionRemainder I
      (fun _ : Fin 1 => (MvPolynomial.X 0 : MvPolynomial (Fin 1) R))
      (by intro _; simpa only [m.leadingCoeff_X] using (isUnit_one : IsUnit (1 : R)))
      f : adicallyRestrictedSubring (σ := Fin 1) I) : MvPowerSeries (Fin 1) R) = 0 := by
  apply m.coeff_restrictedDivisionRemainder_eq_zero I
    (fun _ : Fin 1 => (MvPolynomial.X 0 : MvPolynomial (Fin 1) R))
    (by intro _; simpa only [m.leadingCoeff_X] using (isUnit_one : IsUnit (1 : R))) f α 0
  exact hα

end Tests.RestrictedPolynomialDivision
