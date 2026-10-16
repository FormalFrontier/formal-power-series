/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FirstVariableRegrouping.Fin
public import Mathlib.Data.ZMod.Basic

/-!
# First-variable regrouping of restricted series

Coefficient calculations and extensionality for Option and finite-variable
regrouping, including empty-variable and zero-ring cases.
-/

public section

set_option warningAsError true

-- These private mathematical examples have no exported API.
set_option linter.privateModule false

open MvPowerSeries

variable {R : Type*} [CommRing R]

private theorem restrictedRenameEquiv_finZero_refl
    (I : Ideal R) (f : adicallyRestrictedSubring (σ := Fin 0) I) :
    restrictedRenameEquiv I (Equiv.refl (Fin 0)) f = f := by
  rw [restrictedRenameEquiv_refl]
  rfl

private theorem restrictedRenameEquiv_finOne_trans
    (I : Ideal R) (f : adicallyRestrictedSubring (σ := Fin 1) I)
    (e : Fin 1 ≃ Option (Fin 0)) (g : Option (Fin 0) ≃ Fin 1) :
    restrictedRenameEquiv I g (restrictedRenameEquiv I e f) =
      restrictedRenameEquiv I (e.trans g) f := by
  rw [← restrictedRenameEquiv_trans]
  rfl

private theorem coeff_restrictedFinSuccEquiv_finOne
    (I : Ideal R) (f : adicallyRestrictedSubring (σ := Fin 1) I)
    (d : Fin 1 →₀ ℕ) :
    coeff (Finsupp.domCongr (_root_.finSuccEquiv 0) d)
        (restrictedFinSuccEquiv I 0 f : MvPowerSeries (Option (Fin 0)) R) =
      coeff d (f : MvPowerSeries (Fin 1) R) := by
  simpa only [restrictedFinSuccEquiv_coe, restrictedRenameEquiv_coe] using
    (coeff_restrictedRenameEquiv I (_root_.finSuccEquiv 0) f d)

private theorem coeff_restrictedFirstCoeff_nat (I : Ideal R)
    (f : adicallyRestrictedSubring (σ := Option ℕ) I)
    (n : ℕ) (β : ℕ →₀ ℕ) :
    coeff β (restrictedFirstCoeff I n f : MvPowerSeries ℕ R) =
      coeff (β.optionElim n) (f : MvPowerSeries (Option ℕ) R) :=
  coeff_restrictedFirstCoeff I f n β

private theorem restrictedFirstRegroup_nat_injective (I : Ideal R)
    (f g : adicallyRestrictedSubring (σ := Option ℕ) I)
    (h : restrictedFirstRegroup I f = restrictedFirstRegroup I g) : f = g :=
  restrictedFirstRegroup_injective I h

private theorem restrictedFirst_support_iff_optionEmpty (I : Ideal R)
    (f : adicallyRestrictedSubring (σ := Option Empty) I) (d : ℕ) :
    (∀ (n : ℕ) (β : Empty →₀ ℕ), d ≤ n → coeff (β.optionElim n)
        (f : MvPowerSeries (Option Empty) R) = 0) ↔
      ∃! P : Polynomial (adicallyRestrictedSubring (σ := Empty) I),
        P.degree < (d : WithBot ℕ) ∧ polynomialRestrictedFirst I P = f :=
  restrictedFirst_actual_support_iff I f d

private theorem restrictedFirst_support_iff_zmodOne (I : Ideal (ZMod 1))
    (f : adicallyRestrictedSubring (σ := Option ℕ) I) :
    (∀ (n : ℕ) (β : ℕ →₀ ℕ), 0 ≤ n → coeff (β.optionElim n)
        (f : MvPowerSeries (Option ℕ) (ZMod 1)) = 0) ↔
      ∃! P : Polynomial (adicallyRestrictedSubring (σ := ℕ) I),
        P.degree < (0 : WithBot ℕ) ∧ polynomialRestrictedFirst I P = f :=
  restrictedFirst_actual_support_iff I f 0

private theorem existsUnique_polynomialRestrictedFirst_zero (I : Ideal R) :
    ∃! P : Polynomial (adicallyRestrictedSubring (σ := ℕ) I),
      P.degree < (0 : WithBot ℕ) ∧
        polynomialRestrictedFirst I P =
          (0 : adicallyRestrictedSubring (σ := Option ℕ) I) := by
  apply (restrictedFirst_actual_support_iff I 0 0).mp
  intro n β _
  simp

private theorem existsUnique_polynomialRestrictedFirst_int_bot
    (d : ℕ) (f : adicallyRestrictedSubring (σ := Option ℕ) (⊥ : Ideal ℤ))
    (h : ∀ (n : ℕ) (β : ℕ →₀ ℕ), d ≤ n → coeff (β.optionElim n)
      (f : MvPowerSeries (Option ℕ) ℤ) = 0) :
    ∃! P : Polynomial (adicallyRestrictedSubring (σ := ℕ) (⊥ : Ideal ℤ)),
      P.degree < (d : WithBot ℕ) ∧ polynomialRestrictedFirst ⊥ P = f :=
  (restrictedFirst_actual_support_iff ⊥ f d).mp h

private theorem polynomialRestrictedFirst_int_top_support
    (d : ℕ) (f : adicallyRestrictedSubring (σ := Option Empty) (⊤ : Ideal ℤ))
    (P : Polynomial (adicallyRestrictedSubring (σ := Empty) (⊤ : Ideal ℤ)))
    (hP : P.degree < (d : WithBot ℕ) ∧ polynomialRestrictedFirst ⊤ P = f) :
    ∀ (n : ℕ) (β : Empty →₀ ℕ), d ≤ n → coeff (β.optionElim n)
      (f : MvPowerSeries (Option Empty) ℤ) = 0 := by
  exact (restrictedFirst_actual_support_iff ⊤ f d).mpr
    ⟨P, hP, fun Q hQ => polynomialRestrictedFirst_injective ⊤
      (hQ.2.trans hP.2.symm)⟩

private theorem restrictedFinFirst_support_iff (I : Ideal R) (n d : ℕ)
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) I) :
    (∀ (i : ℕ) (β : Fin n →₀ ℕ), d ≤ i → coeff (β.cons i)
        (f : MvPowerSeries (Fin (n + 1)) R) = 0) ↔
      ∃! P : Polynomial (adicallyRestrictedSubring (σ := Fin n) I),
        P.degree < (d : WithBot ℕ) ∧ polynomialRestrictedFinFirst I n P = f :=
  restrictedFinFirst_actual_support_iff I n f d

private theorem coeff_restrictedFinFirstCoeff_finZero
    (I : Ideal R) (f : adicallyRestrictedSubring (σ := Fin 1) I)
    (β : Fin 0 →₀ ℕ) (i : ℕ) :
    coeff β (restrictedFinFirstCoeff I 0 i f : MvPowerSeries (Fin 0) R) =
      coeff (β.cons i) (f : MvPowerSeries (Fin 1) R) :=
  coeff_restrictedFinFirstCoeff I 0 i f β

private theorem map_restrictedFinFirstRegroup_subtype (I : Ideal R) (n : ℕ)
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) I) :
    PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := Fin n) I))
        (restrictedFinFirstRegroup I n f) =
      finSuccEquiv R n (f : MvPowerSeries (Fin (n + 1)) R) :=
  map_restrictedFinFirstRegroup_raw I n f

private theorem coeff_restrictedFinFirstRegroup_monomial_two :
    coeff (0 : Fin 1 →₀ ℕ)
      (↑(PowerSeries.coeff 2
        (restrictedFinFirstRegroup (⊥ : Ideal ℤ) 1
          (polynomialToRestricted (⊥ : Ideal ℤ)
            (MvPolynomial.monomial ((0 : Fin 1 →₀ ℕ).cons 2) (3 : ℤ))))) :
          MvPowerSeries (Fin 1) ℤ) = 3 := by
  rw [coeff_restrictedFinFirstRegroup, coeff_restrictedFinFirstCoeff]
  simp only [polynomialToRestricted_coe, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_monomial]
  rfl

private theorem restrictedFinFirstCoeff_finTwo_ext (I : Ideal R)
    (f g : adicallyRestrictedSubring (σ := Fin 2) I)
    (h : ∀ i : ℕ, restrictedFinFirstCoeff I 1 i f = restrictedFinFirstCoeff I 1 i g) :
    f = g := by
  apply restrictedFinFirstRegroup_injective
  apply PowerSeries.ext
  intro i
  simpa only [coeff_restrictedFinFirstRegroup] using h i

private theorem coeff_polynomialRestrictedFinFirst_finZero (I : Ideal R)
    (P : Polynomial (adicallyRestrictedSubring (σ := Fin 0) I))
    (β : Fin 0 →₀ ℕ) (i : ℕ) :
    coeff (β.cons i)
        (polynomialRestrictedFinFirst I 0 P : MvPowerSeries (Fin 1) R) =
      coeff β (P.coeff i : MvPowerSeries (Fin 0) R) :=
  coeff_polynomialRestrictedFinFirst I 0 P i β
