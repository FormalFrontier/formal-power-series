module

import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.InverseLimit
import Mathlib.Data.ZMod.Basic

set_option warningAsError true

namespace FormalPowerSeriesTests.MvPowerSeries.IdealAdicRestricted.InverseLimit

private theorem generic_forward {σ R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (n : ℕ)
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) :
    MvPowerSeries.adicPolynomialLevelEquiv (σ := σ) I n
      (AdicCompletion.evalₐ _ n
        (MvPowerSeries.adicallyRestrictedEquivAdicCompletion I f)) =
      MvPowerSeries.adicReduction I n f :=
  MvPowerSeries.adicallyRestrictedEquivAdicCompletion_eval I n f

private theorem generic_inverse {σ R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (n : ℕ)
    (x : AdicCompletion
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :
    MvPowerSeries.adicReduction I n
        ((MvPowerSeries.adicallyRestrictedEquivAdicCompletion I).symm x) =
      MvPowerSeries.adicPolynomialLevelEquiv (σ := σ) I n
        (AdicCompletion.evalₐ _ n x) :=
  MvPowerSeries.adicallyRestrictedEquivAdicCompletion_symm_eval I n x

private theorem generic_polynomial {σ R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (p : MvPolynomial σ R) :
    MvPowerSeries.adicallyRestrictedEquivAdicCompletion I
        (MvPowerSeries.polynomialToRestricted I p) =
      AdicCompletion.of (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R) p :=
  MvPowerSeries.adicallyRestrictedEquivAdicCompletion_polynomial I p

private theorem polynomial_inverse_evaluation {σ R : Type*} [CommRing R]
    (I : Ideal R) [IsAdicComplete I R] (n : ℕ) (p : MvPolynomial σ R) :
    MvPowerSeries.adicReduction I n
        ((MvPowerSeries.adicallyRestrictedEquivAdicCompletion I).symm
          (AdicCompletion.of (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R) p)) =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p := by
  rw [generic_inverse, AdicCompletion.evalₐ_of,
    MvPowerSeries.adicPolynomialLevelEquiv_mk]

private theorem transition_identity {σ R : Type*} [CommRing R] (I : Ideal R)
    (n : ℕ) (p : MvPolynomial σ (R ⧸ I ^ n)) :
    MvPolynomial.map (Ideal.Quotient.factorPow I (le_refl n)) p = p := by
  apply MvPolynomial.ext
  intro index
  obtain ⟨coefficient, hcoefficient⟩ := Ideal.Quotient.mk_surjective (p.coeff index)
  simp only [MvPolynomial.coeff_map, ← hcoefficient, Ideal.Quotient.factor_mk]

private theorem transition_composition {σ R : Type*} [CommRing R] (I : Ideal R)
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    (p : MvPolynomial σ (R ⧸ I ^ n)) :
    MvPolynomial.map (Ideal.Quotient.factorPow I hlm)
        (MvPolynomial.map (Ideal.Quotient.factorPow I hmn) p) =
      MvPolynomial.map (Ideal.Quotient.factorPow I (hlm.trans hmn)) p := by
  apply MvPolynomial.ext
  intro index
  obtain ⟨coefficient, hcoefficient⟩ := Ideal.Quotient.mk_surjective (p.coeff index)
  simp only [MvPolynomial.coeff_map, ← hcoefficient, Ideal.Quotient.factor_mk]

private theorem native_transition {σ R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n)
    (x : MvPolynomial σ R ⧸
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n) :
    MvPowerSeries.adicPolynomialLevelEquiv (σ := σ) I m
        (Ideal.Quotient.factorPow _ hmn x) =
      MvPolynomial.map (Ideal.Quotient.factorPow I hmn)
        (MvPowerSeries.adicPolynomialLevelEquiv I n x) :=
  MvPowerSeries.adicPolynomialLevelEquiv_factorPow I hmn x

private theorem restricted_reduction_transition {σ R : Type*} [CommRing R]
    (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) :
    MvPolynomial.map (Ideal.Quotient.factorPow I hmn)
        (MvPowerSeries.adicReduction I n f) =
      MvPowerSeries.adicReduction I m f :=
  MvPowerSeries.adicReduction_factorPow I hmn f

private theorem level_zero {σ R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R]
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I)
    (index : σ →₀ ℕ) :
    (MvPowerSeries.adicPolynomialLevelEquiv (σ := σ) I 0
      (AdicCompletion.evalₐ _ 0
        (MvPowerSeries.adicallyRestrictedEquivAdicCompletion I f))).coeff index = 0 := by
  rw [generic_forward, MvPowerSeries.coeff_adicReduction]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simp)

private theorem empty_variables (I : Ideal ℤ) [IsAdicComplete I ℤ]
    (p : MvPolynomial (Fin 0) ℤ) :
    MvPowerSeries.adicallyRestrictedEquivAdicCompletion I
        (MvPowerSeries.polynomialToRestricted I p) =
      AdicCompletion.of (I.map (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ))
        (MvPolynomial (Fin 0) ℤ) p :=
  generic_polynomial I p

private theorem infinitely_many_variables (I : Ideal ℤ) [IsAdicComplete I ℤ]
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := ℕ) I) (n : ℕ) :
    MvPowerSeries.adicPolynomialLevelEquiv (σ := ℕ) I n
      (AdicCompletion.evalₐ _ n
        (MvPowerSeries.adicallyRestrictedEquivAdicCompletion I f)) =
      MvPowerSeries.adicReduction I n f :=
  generic_forward I n f

private theorem zero_divisor_ring (p : MvPolynomial (Fin 2) (ZMod 6)) :
    MvPowerSeries.adicallyRestrictedEquivAdicCompletion (⊥ : Ideal (ZMod 6))
        (MvPowerSeries.polynomialToRestricted ⊥ p) =
      AdicCompletion.of
        ((⊥ : Ideal (ZMod 6)).map
          (MvPolynomial.C : ZMod 6 →+* MvPolynomial (Fin 2) (ZMod 6)))
        (MvPolynomial (Fin 2) (ZMod 6)) p :=
  generic_polynomial ⊥ p

private theorem zero_divisor_witness :
    (2 : ZMod 6) ≠ 0 ∧ (3 : ZMod 6) ≠ 0 ∧ (2 : ZMod 6) * 3 = 0 := by
  decide

private theorem zero_ring (f : MvPowerSeries.adicallyRestrictedSubring
    (σ := Fin 2) (⊤ : Ideal (ZMod 1))) :
    MvPowerSeries.adicPolynomialLevelEquiv (σ := Fin 2) (⊤ : Ideal (ZMod 1)) 0
      (AdicCompletion.evalₐ _ 0
        (MvPowerSeries.adicallyRestrictedEquivAdicCompletion ⊤ f)) =
      MvPowerSeries.adicReduction ⊤ 0 f :=
  generic_forward ⊤ 0 f

end FormalPowerSeriesTests.MvPowerSeries.IdealAdicRestricted.InverseLimit
