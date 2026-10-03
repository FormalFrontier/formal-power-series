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

open MvPowerSeries

variable {R : Type*} [CommRing R]

example (I : Ideal R) (f : adicallyRestrictedSubring (σ := Fin 0) I) :
    restrictedRenameEquiv I (Equiv.refl (Fin 0)) f = f := by
  rw [restrictedRenameEquiv_refl]
  rfl

example (I : Ideal R) (f : adicallyRestrictedSubring (σ := Fin 1) I)
    (e : Fin 1 ≃ Option (Fin 0)) (g : Option (Fin 0) ≃ Fin 1) :
    restrictedRenameEquiv I g (restrictedRenameEquiv I e f) =
      restrictedRenameEquiv I (e.trans g) f := by
  rw [← restrictedRenameEquiv_trans]
  rfl

example (I : Ideal R) (f : adicallyRestrictedSubring (σ := Fin 1) I)
    (d : Fin 1 →₀ ℕ) :
    coeff (Finsupp.domCongr (_root_.finSuccEquiv 0) d)
        (restrictedFinSuccEquiv I 0 f : MvPowerSeries (Option (Fin 0)) R) =
      coeff d (f : MvPowerSeries (Fin 1) R) := by
  simpa only [restrictedFinSuccEquiv_coe, restrictedRenameEquiv_coe] using
    (coeff_restrictedRenameEquiv I (_root_.finSuccEquiv 0) f d)

example (I : Ideal R)
    (f : adicallyRestrictedSubring (σ := Option ℕ) I)
    (n : ℕ) (β : ℕ →₀ ℕ) :
    coeff β (restrictedFirstCoeff I n f : MvPowerSeries ℕ R) =
      coeff (β.optionElim n) (f : MvPowerSeries (Option ℕ) R) :=
  coeff_restrictedFirstCoeff I f n β

example (I : Ideal R)
    (f g : adicallyRestrictedSubring (σ := Option ℕ) I)
    (h : restrictedFirstRegroup I f = restrictedFirstRegroup I g) : f = g :=
  restrictedFirstRegroup_injective I h

example (I : Ideal R)
    (f : adicallyRestrictedSubring (σ := Option Empty) I) (d : ℕ) :
    (∀ (n : ℕ) (β : Empty →₀ ℕ), d ≤ n → coeff (β.optionElim n)
        (f : MvPowerSeries (Option Empty) R) = 0) ↔
      ∃! P : Polynomial (adicallyRestrictedSubring (σ := Empty) I),
        P.degree < (d : WithBot ℕ) ∧ polynomialRestrictedFirst I P = f :=
  restrictedFirst_actual_support_iff I f d

example (I : Ideal (ZMod 1))
    (f : adicallyRestrictedSubring (σ := Option ℕ) I) :
    (∀ (n : ℕ) (β : ℕ →₀ ℕ), 0 ≤ n → coeff (β.optionElim n)
        (f : MvPowerSeries (Option ℕ) (ZMod 1)) = 0) ↔
      ∃! P : Polynomial (adicallyRestrictedSubring (σ := ℕ) I),
        P.degree < (0 : WithBot ℕ) ∧ polynomialRestrictedFirst I P = f :=
  restrictedFirst_actual_support_iff I f 0

example (I : Ideal R) :
    ∃! P : Polynomial (adicallyRestrictedSubring (σ := ℕ) I),
      P.degree < (0 : WithBot ℕ) ∧
        polynomialRestrictedFirst I P =
          (0 : adicallyRestrictedSubring (σ := Option ℕ) I) := by
  apply (restrictedFirst_actual_support_iff I 0 0).mp
  intro n β _
  simp

example (d : ℕ) (f : adicallyRestrictedSubring (σ := Option ℕ) (⊥ : Ideal ℤ))
    (h : ∀ (n : ℕ) (β : ℕ →₀ ℕ), d ≤ n → coeff (β.optionElim n)
      (f : MvPowerSeries (Option ℕ) ℤ) = 0) :
    ∃! P : Polynomial (adicallyRestrictedSubring (σ := ℕ) (⊥ : Ideal ℤ)),
      P.degree < (d : WithBot ℕ) ∧ polynomialRestrictedFirst ⊥ P = f :=
  (restrictedFirst_actual_support_iff ⊥ f d).mp h

example (d : ℕ) (f : adicallyRestrictedSubring (σ := Option Empty) (⊤ : Ideal ℤ))
    (P : Polynomial (adicallyRestrictedSubring (σ := Empty) (⊤ : Ideal ℤ)))
    (hP : P.degree < (d : WithBot ℕ) ∧ polynomialRestrictedFirst ⊤ P = f) :
    ∀ (n : ℕ) (β : Empty →₀ ℕ), d ≤ n → coeff (β.optionElim n)
      (f : MvPowerSeries (Option Empty) ℤ) = 0 := by
  exact (restrictedFirst_actual_support_iff ⊤ f d).mpr
    ⟨P, hP, fun Q hQ => polynomialRestrictedFirst_injective ⊤
      (hQ.2.trans hP.2.symm)⟩

example (I : Ideal R) (n d : ℕ)
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) I) :
    (∀ (i : ℕ) (β : Fin n →₀ ℕ), d ≤ i → coeff (β.cons i)
        (f : MvPowerSeries (Fin (n + 1)) R) = 0) ↔
      ∃! P : Polynomial (adicallyRestrictedSubring (σ := Fin n) I),
        P.degree < (d : WithBot ℕ) ∧ polynomialRestrictedFinFirst I n P = f :=
  restrictedFinFirst_actual_support_iff I n f d

example (I : Ideal R) (f : adicallyRestrictedSubring (σ := Fin 1) I)
    (β : Fin 0 →₀ ℕ) (i : ℕ) :
    coeff β (restrictedFinFirstCoeff I 0 i f : MvPowerSeries (Fin 0) R) =
      coeff (β.cons i) (f : MvPowerSeries (Fin 1) R) :=
  coeff_restrictedFinFirstCoeff I 0 i f β

example (I : Ideal R) (n : ℕ)
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) I) :
    PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := Fin n) I))
        (restrictedFinFirstRegroup I n f) =
      finSuccEquiv R n (f : MvPowerSeries (Fin (n + 1)) R) :=
  map_restrictedFinFirstRegroup_raw I n f

example :
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

example (I : Ideal R)
    (f g : adicallyRestrictedSubring (σ := Fin 2) I)
    (h : ∀ i : ℕ, restrictedFinFirstCoeff I 1 i f = restrictedFinFirstCoeff I 1 i g) :
    f = g := by
  apply restrictedFinFirstRegroup_injective
  apply PowerSeries.ext
  intro i
  simpa only [coeff_restrictedFinFirstRegroup] using h i

example (I : Ideal R)
    (P : Polynomial (adicallyRestrictedSubring (σ := Fin 0) I))
    (β : Fin 0 →₀ ℕ) (i : ℕ) :
    coeff (β.cons i)
        (polynomialRestrictedFinFirst I 0 P : MvPowerSeries (Fin 1) R) =
      coeff β (P.coeff i : MvPowerSeries (Fin 0) R) :=
  coeff_polynomialRestrictedFinFirst I 0 P i β
