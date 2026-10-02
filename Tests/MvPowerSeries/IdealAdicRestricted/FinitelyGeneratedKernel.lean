/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FinitelyGeneratedKernel
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Regular.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option warningAsError true

namespace Tests.MvPowerSeries.IdealAdicRestricted.FinitelyGeneratedKernel

open _root_.MvPowerSeries

private theorem generic_fg_witness {σ R : Type*} [CommRing R] [Finite σ]
    (I : Ideal R) (hI : I.FG) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I)
    (hf : adicReduction I k f = 0) :
    ∃ (n : ℕ) (v : Fin n → R)
      (g : Fin n → adicallyRestrictedSubring (σ := σ) I),
      (∀ j, v j ∈ I ^ k) ∧
        f = ∑ j, polynomialToRestricted I (MvPolynomial.C (v j)) * g j := by
  apply exists_restricted_fg_decomposition I hI k f
  intro m
  have hzero : (adicReduction I k f).coeff m = 0 := by rw [hf]; simp
  rw [coeff_adicReduction] at hzero
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

private theorem generic_fg_kernel {σ R : Type*} [CommRing R] [Finite σ]
    (I : Ideal R) (hI : I.FG) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    f ∈ RingHom.ker (adicReduction I k) ↔
      f ∈ Ideal.map ((polynomialToRestricted I).comp MvPolynomial.C) (I ^ k) := by
  rw [ker_adicReduction_fg I hI k]

private theorem generic_fg_quotient {σ R : Type*} [CommRing R] [Finite σ]
    (I : Ideal R) (hI : I.FG) (k : ℕ) :
    Nonempty
      ((adicallyRestrictedSubring (σ := σ) I ⧸
          Ideal.map ((polynomialToRestricted I).comp MvPolynomial.C) (I ^ k)) ≃+*
        MvPolynomial σ (R ⧸ I ^ k)) := by
  rw [← ker_adicReduction_fg (σ := σ) I hI k]
  exact ⟨RingHom.quotientKerEquivOfSurjective (adicReduction_surjective I k)⟩

private theorem level_zero {σ R : Type*} [CommRing R] [Finite σ]
    (I : Ideal R) (hI : I.FG) :
    RingHom.ker (adicReduction (σ := σ) I 0) = ⊤ := by
  rw [ker_adicReduction_fg I hI 0]
  simp only [pow_zero, Ideal.one_eq_top, Ideal.map_top]

private theorem zero_ideal {R : Type*} [CommRing R] (k : ℕ) :
    RingHom.ker (adicReduction (σ := Fin 2) (⊥ : Ideal R) k) =
      Ideal.map ((polynomialToRestricted (σ := Fin 2) (⊥ : Ideal R)).comp MvPolynomial.C)
        ((⊥ : Ideal R) ^ k) :=
  ker_adicReduction_fg ⊥ Submodule.fg_bot k

private theorem top_ideal {R : Type*} [CommRing R] (k : ℕ) :
    RingHom.ker (adicReduction (σ := Fin 2) (⊤ : Ideal R) k) =
      Ideal.map ((polynomialToRestricted (σ := Fin 2) (⊤ : Ideal R)).comp MvPolynomial.C)
        ((⊤ : Ideal R) ^ k) :=
  ker_adicReduction_fg ⊤ (show (⊤ : Ideal R).FG from ⟨{1}, by simp⟩) k

private theorem empty_variables (I : Ideal ℤ) (hI : I.FG) (k : ℕ) :
    RingHom.ker (adicReduction (σ := Fin 0) I k) =
      Ideal.map ((polynomialToRestricted (σ := Fin 0) I).comp MvPolynomial.C) (I ^ k) :=
  ker_adicReduction_fg I hI k

private theorem zero_ring (k : ℕ) :
    RingHom.ker (adicReduction (σ := Fin 2) (⊥ : Ideal (ZMod 1)) k) =
      Ideal.map ((polynomialToRestricted (σ := Fin 2) (⊥ : Ideal (ZMod 1))).comp
        MvPolynomial.C) ((⊥ : Ideal (ZMod 1)) ^ k) :=
  ker_adicReduction_fg ⊥ Submodule.fg_bot k

private theorem mod_four_nilpotent : (2 : ZMod 4) ^ 2 = 0 := by decide

private theorem mod_four_nonregular : ¬ IsRegular (2 : ZMod 4) := by
  intro h
  have hzero : (2 : ZMod 4) * 2 = (2 : ZMod 4) * 0 := by decide
  have hbad : (2 : ZMod 4) = 0 := h.left hzero
  exact (by decide : (2 : ZMod 4) ≠ 0) hbad

private theorem nonregular_ideal (k : ℕ) :
    RingHom.ker (adicReduction (σ := Fin 2)
      (Ideal.span ({(2 : ZMod 4)} : Set (ZMod 4))) k) =
      Ideal.map
        ((polynomialToRestricted (σ := Fin 2)
          (Ideal.span ({(2 : ZMod 4)} : Set (ZMod 4)))).comp MvPolynomial.C)
        ((Ideal.span ({(2 : ZMod 4)} : Set (ZMod 4))) ^ k) := by
  exact ker_adicReduction_fg _ (show
    (Ideal.span ({(2 : ZMod 4)} : Set (ZMod 4))).FG from
      ⟨{2}, by simp⟩) k

end Tests.MvPowerSeries.IdealAdicRestricted.FinitelyGeneratedKernel
