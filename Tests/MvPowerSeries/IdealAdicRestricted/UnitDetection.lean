/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.UnitDetection
public import Mathlib.Data.ZMod.Basic

public section

open MvPowerSeries

variable {σ R : Type*} [CommRing R]

example (I : Ideal R) [IsAdicComplete I R]
    (f : adicallyRestrictedSubring (σ := σ) I)
    (hf : adicReduction I 1 f = 0) : IsUnit (1 - f) := by
  apply (isUnit_adicallyRestricted_iff_adicReduction_one I _).2
  simpa only [map_sub, map_one, hf, sub_zero] using (isUnit_one : IsUnit (1 :
    MvPolynomial σ (R ⧸ I ^ 1)))

example (I : Ideal R) [IsAdicComplete I R]
    (f : adicallyRestrictedSubring (σ := σ) I)
    (hf : adicReduction I 1 f = 1) : IsUnit f := by
  exact (isUnit_adicallyRestricted_iff_adicReduction_one I f).2 (hf ▸ isUnit_one)

example (I : Ideal R) [IsAdicComplete I R]
    (f : adicallyRestrictedSubring (σ := σ) I)
    (hconstant : IsUnit (coeff 0 (f : MvPowerSeries σ R)))
    (hnonconstant : ∀ α : σ →₀ ℕ, α ≠ 0 →
      coeff α (f : MvPowerSeries σ R) ∈ I.radical) : IsUnit f := by
  exact (isUnit_adicallyRestricted_iff_coeff_radical I f).2
    ⟨hconstant, hnonconstant⟩

example (I : Ideal R) [IsAdicComplete I R] (r : R)
    (hr : IsUnit (Ideal.Quotient.mk I r)) : IsUnit r := by
  exact (isUnit_iff_quotient_of_isAdicComplete I r).2 hr

example (f : adicallyRestrictedSubring (σ := ℕ) (⊥ : Ideal R))
    (hf : adicReduction (⊥ : Ideal R) 1 f = 1) : IsUnit f := by
  exact (isUnit_adicallyRestricted_iff_adicReduction_one (⊥ : Ideal R) f).2
    (hf ▸ isUnit_one)

example (f : adicallyRestrictedSubring (σ := Empty) (⊥ : Ideal R))
    (hf : IsUnit (Ideal.Quotient.mk (⊥ : Ideal R) (coeff 0 (f : MvPowerSeries Empty R)))) :
    IsUnit f := by
  apply (isUnit_adicallyRestricted_iff_coeff_mod_ideal (⊥ : Ideal R) f).2
  exact ⟨hf, fun α hα => False.elim (hα (Subsingleton.elim _ _))⟩

example (σ : Type*) (I : Ideal (ZMod 1))
    (f : adicallyRestrictedSubring (σ := σ) I) : IsUnit f := by
  apply (isUnit_adicallyRestricted_iff_adicReduction_one I f).2
  have : adicReduction I 1 f = 1 := Subsingleton.elim _ _
  exact this ▸ isUnit_one

example : IsUnit (polynomialToRestricted (σ := Fin 1) (⊥ : Ideal (ZMod 4))
    (1 + MvPolynomial.C (2 : ZMod 4) * MvPolynomial.X 0)) := by
  have hn : (2 : ZMod 4) ^ 2 = 0 := by decide
  have hp : IsNilpotent (MvPolynomial.C (2 : ZMod 4) *
      MvPolynomial.X (0 : Fin 1)) := by
    refine ⟨2, ?_⟩
    rw [mul_pow, ← map_pow, hn, map_zero, zero_mul]
  exact hp.isUnit_one_add.map (polynomialToRestricted (⊥ : Ideal (ZMod 4)))
