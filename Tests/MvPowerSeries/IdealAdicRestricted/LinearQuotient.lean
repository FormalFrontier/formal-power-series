/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearQuotient
import Mathlib.Algebra.Regular.Prod
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Int.Order.Units

set_option warningAsError true

namespace FormalPowerSeriesTests.MvPowerSeries.IdealAdicRestricted.LinearQuotient

open _root_.MvPowerSeries
open scoped Pointwise

private theorem general_scalar_coefficient {σ R : Type*} [CommRing R]
    (I : Ideal R) (r : R) (f : adicallyRestrictedSubring (σ := σ) I)
    (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m
      ((r • f : adicallyRestrictedSubring (σ := σ) I) : MvPowerSeries σ R) =
        r * MvPowerSeries.coeff m (f : MvPowerSeries σ R) :=
  coeff_smul_adicallyRestricted I r f m

private theorem general_reduction_scalar {σ R : Type*} [CommRing R]
    (I : Ideal R) (k : ℕ) (r : R)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    linearAdicReduction I k (r • f) = r • linearAdicReduction I k f := by
  exact map_smul (linearAdicReduction (σ := σ) I k) r f

private theorem general_reduction_coefficient {σ R : Type*} [CommRing R]
    (I : Ideal R) (k : ℕ) (r : R)
    (f : adicallyRestrictedSubring (σ := σ) I) (m : σ →₀ ℕ) :
    (linearAdicReduction I k (r • f)).coeff m =
      Ideal.Quotient.mk (I ^ k)
        (r * MvPowerSeries.coeff m (f : MvPowerSeries σ R)) := by
  rw [coeff_linearAdicReduction, coeff_smul_adicallyRestricted]

private theorem general_reduction_surjective {σ R : Type*} [CommRing R]
    (I : Ideal R) (k : ℕ) (p : MvPolynomial σ (R ⧸ I ^ k)) :
    ∃ f : adicallyRestrictedSubring (σ := σ) I, linearAdicReduction I k f = p :=
  linearAdicReduction_surjective I k p

private theorem one_variable_reduction (I : Ideal ℤ) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := Unit) I) (m : Unit →₀ ℕ) :
    (linearAdicReduction I k f).coeff m =
      Ideal.Quotient.mk (I ^ k) (MvPowerSeries.coeff m (f : MvPowerSeries Unit ℤ)) :=
  coeff_linearAdicReduction I k f m

private theorem four_regular : IsRegular (4 : ℤ) :=
  IsRegular.of_ne_zero (by decide)

private theorem four_nonunit : ¬ IsUnit (4 : ℤ) := by
  rw [Int.isUnit_iff_abs_eq]
  decide

private theorem pair_regular : IsRegular ((2, 1) : ℤ × ℤ) :=
  IsRegular.prodMk (IsRegular.of_ne_zero (by decide : (2 : ℤ) ≠ 0)) isRegular_one

private theorem pair_nonunit : ¬ IsUnit ((2, 1) : ℤ × ℤ) := by
  intro hu
  have htwo : IsUnit (2 : ℤ) := (Prod.isUnit_iff.mp hu).1
  have hnot : ¬ IsUnit (2 : ℤ) := by
    rw [Int.isUnit_iff_abs_eq]
    decide
  exact hnot htwo

private abbrev fourIdeal : Ideal ℤ := Ideal.span ({(4 : ℤ)} : Set ℤ)

private noncomputable abbrev fourNativeSubmodule (k : ℕ) :
    Submodule ℤ (adicallyRestrictedSubring (σ := Fin 2) fourIdeal) :=
  fourIdeal ^ k • ⊤

private abbrev fourNativeQuotient (k : ℕ) :=
  adicallyRestrictedSubring (σ := Fin 2) fourIdeal ⧸ fourNativeSubmodule k

private theorem four_module_kernel (k : ℕ) :
    LinearMap.ker (intLinearAdicReduction (σ := Fin 2) fourIdeal k) =
      fourNativeSubmodule k :=
  ker_intLinearAdicReduction_principal 4 four_regular k

private theorem four_native_scalar (k : ℕ) (r : ℤ)
    (f : adicallyRestrictedSubring (σ := Fin 2) fourIdeal) :
    intLinearAdicReduction fourIdeal k (r • f) =
      r • intLinearAdicReduction fourIdeal k f :=
  map_smul (intLinearAdicReduction (σ := Fin 2) fourIdeal k) r f

private theorem four_native_scalar_coefficient (r : ℤ)
    (f : adicallyRestrictedSubring (σ := Fin 2) fourIdeal) (m : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff m ((r • f : adicallyRestrictedSubring (σ := Fin 2) fourIdeal) :
      MvPowerSeries (Fin 2) ℤ) =
        r * MvPowerSeries.coeff m (f : MvPowerSeries (Fin 2) ℤ) := by
  have h : (r • f : adicallyRestrictedSubring (σ := Fin 2) fourIdeal) =
      (r : adicallyRestrictedSubring (σ := Fin 2) fourIdeal) * f := by
    simpa only [smul_eq_mul] using
      (Int.cast_smul_eq_zsmul (R := adicallyRestrictedSubring (σ := Fin 2)
        fourIdeal) r f).symm
  rw [h, Subring.coe_mul, Subring.coe_intCast]
  rw [← map_intCast (MvPowerSeries.C : ℤ →+* MvPowerSeries (Fin 2) ℤ) r,
    MvPowerSeries.coeff_C_mul]
  rfl

private theorem four_native_coefficient (k : ℕ)
    (f : adicallyRestrictedSubring (σ := Fin 2) fourIdeal) (m : Fin 2 →₀ ℕ) :
    (intLinearAdicReduction fourIdeal k f).coeff m =
      Ideal.Quotient.mk (fourIdeal ^ k)
        (MvPowerSeries.coeff m (f : MvPowerSeries (Fin 2) ℤ)) :=
  coeff_intLinearAdicReduction fourIdeal k f m

private theorem one_variable_int_reduction (I : Ideal ℤ) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := Unit) I) (m : Unit →₀ ℕ) :
    (intLinearAdicReduction I k f).coeff m =
      Ideal.Quotient.mk (I ^ k) (MvPowerSeries.coeff m (f : MvPowerSeries Unit ℤ)) :=
  coeff_intLinearAdicReduction I k f m

private noncomputable def four_native_quotient_equiv_at_two :
    fourNativeQuotient 2 ≃ₗ[ℤ]
      MvPolynomial (Fin 2) (ℤ ⧸ fourIdeal ^ 2) :=
  principalIntLinearQuotientEquiv (σ := Fin 2) 4 four_regular 2

private theorem four_level_zero
    (f : adicallyRestrictedSubring (σ := Fin 2)
      (Ideal.span ({(4 : ℤ)} : Set ℤ))) :
    principalIntLinearQuotientEquiv (σ := Fin 2) 4 four_regular 0
      ((Submodule.Quotient.mk f) : fourNativeQuotient 0) =
        adicReduction (Ideal.span ({(4 : ℤ)} : Set ℤ)) 0 f :=
  principalIntLinearQuotientEquiv_mk 4 four_regular 0 f

private theorem four_level_one
    (f : adicallyRestrictedSubring (σ := Fin 2)
      (Ideal.span ({(4 : ℤ)} : Set ℤ))) :
    principalIntLinearQuotientEquiv (σ := Fin 2) 4 four_regular 1
      ((Submodule.Quotient.mk f) : fourNativeQuotient 1) =
        adicReduction (Ideal.span ({(4 : ℤ)} : Set ℤ)) 1 f :=
  principalIntLinearQuotientEquiv_mk 4 four_regular 1 f

private theorem four_level_two
    (f : adicallyRestrictedSubring (σ := Fin 2)
      (Ideal.span ({(4 : ℤ)} : Set ℤ))) :
    principalIntLinearQuotientEquiv (σ := Fin 2) 4 four_regular 2
      ((Submodule.Quotient.mk f) : fourNativeQuotient 2) =
        adicReduction (Ideal.span ({(4 : ℤ)} : Set ℤ)) 2 f :=
  principalIntLinearQuotientEquiv_mk 4 four_regular 2 f

private theorem product_level_two
    (f : adicallyRestrictedSubring (σ := Fin 2)
      (Ideal.span ({((2, 1) : ℤ × ℤ)} : Set (ℤ × ℤ)))) :
    principalLinearQuotientEquiv (σ := Fin 2) (2, 1) pair_regular 2
      (Submodule.Quotient.mk f) =
        adicReduction (Ideal.span ({((2, 1) : ℤ × ℤ)} : Set (ℤ × ℤ))) 2 f :=
  principalLinearQuotientEquiv_mk (2, 1) pair_regular 2 f

end FormalPowerSeriesTests.MvPowerSeries.IdealAdicRestricted.LinearQuotient
