/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.PrincipalKernel
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Operations

public section

/-!
# Linear quotients of restricted power series

The polynomial constant map gives the existing restricted-series subring its
coefficient-ring algebra structure. Polynomial reduction is linear over this
structure. For a regular principal ideal its linear kernel is the corresponding
ideal-power submodule, giving a module quotient by the first isomorphism theorem.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

/-- The coefficient-ring algebra structure on the existing restricted subring. -/
noncomputable instance adicallyRestrictedAlgebra (I : Ideal R) :
    Algebra R (adicallyRestrictedSubring (σ := σ) I) :=
  ((polynomialToRestricted I).comp (MvPolynomial.C : R →+* MvPolynomial σ R)).toAlgebra

@[simp]
theorem algebraMap_adicallyRestricted_coe (I : Ideal R) (r : R) :
    ((algebraMap R (adicallyRestrictedSubring (σ := σ) I) r :
      adicallyRestrictedSubring (σ := σ) I) : MvPowerSeries σ R) = C r := by
  change ((polynomialToRestricted I (MvPolynomial.C r) :
    adicallyRestrictedSubring (σ := σ) I) : MvPowerSeries σ R) = C r
  rw [polynomialToRestricted_coe, MvPolynomial.coe_C]

/-- The new scalar action is the existing coefficientwise action on ambient series. -/
@[simp]
theorem coe_smul_adicallyRestricted (I : Ideal R) (r : R)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    ((r • f : adicallyRestrictedSubring (σ := σ) I) : MvPowerSeries σ R) =
      r • (f : MvPowerSeries σ R) := by
  rw [Algebra.smul_def, Subring.coe_mul, algebraMap_adicallyRestricted_coe]
  exact (smul_eq_C_mul (f : MvPowerSeries σ R) r).symm

@[simp]
theorem coeff_smul_adicallyRestricted (I : Ideal R) (r : R)
    (f : adicallyRestrictedSubring (σ := σ) I) (m : σ →₀ ℕ) :
    coeff m ((r • f : adicallyRestrictedSubring (σ := σ) I) : MvPowerSeries σ R) =
      r * coeff m (f : MvPowerSeries σ R) := by
  rw [coe_smul_adicallyRestricted, coeff_smul]

/-- The existing finite polynomial reduction, bundled over the coefficient ring. -/
noncomputable def algebraAdicReduction (I : Ideal R) (k : ℕ) :
    adicallyRestrictedSubring (σ := σ) I →ₐ[R] MvPolynomial σ (R ⧸ I ^ k) where
  __ := adicReduction I k
  commutes' r := by
    change adicReduction I k (polynomialToRestricted I (MvPolynomial.C r)) =
      MvPolynomial.C (Ideal.Quotient.mk (I ^ k) r)
    simp

/-- The linear reduction has the original polynomial reduction as its function. -/
noncomputable def linearAdicReduction (I : Ideal R) (k : ℕ) :
    adicallyRestrictedSubring (σ := σ) I →ₗ[R] MvPolynomial σ (R ⧸ I ^ k) :=
  (algebraAdicReduction (σ := σ) I k).toLinearMap

@[simp]
theorem linearAdicReduction_apply (I : Ideal R) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    linearAdicReduction I k f = adicReduction I k f := by
  simp only [linearAdicReduction, AlgHom.toLinearMap_apply]
  rfl

@[simp]
theorem coeff_linearAdicReduction (I : Ideal R) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I) (m : σ →₀ ℕ) :
    (linearAdicReduction I k f).coeff m =
      Ideal.Quotient.mk (I ^ k) (coeff m (f : MvPowerSeries σ R)) := by
  rw [linearAdicReduction_apply, coeff_adicReduction]

theorem linearAdicReduction_surjective (I : Ideal R) (k : ℕ) :
    Function.Surjective (linearAdicReduction (σ := σ) I k) :=
  adicReduction_surjective I k

/-- A restricted constant power acts by coefficient-ring scalar multiplication. -/
theorem principalAdicConstant_mul_eq_smul (a : R) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R))) :
    principalAdicConstant a k * f = (a ^ k) • f := by
  apply Subtype.ext
  rw [Subring.coe_mul, principalAdicConstant_coe,
    coe_smul_adicallyRestricted, smul_eq_C_mul]

open scoped Pointwise

/-- The linear kernel is the ideal-power submodule, not merely a ring ideal. -/
theorem ker_linearAdicReduction_principal (a : R) (ha : IsRegular a) (k : ℕ) :
    LinearMap.ker (linearAdicReduction (σ := σ)
      (Ideal.span ({a} : Set R)) k) =
        (Ideal.span ({a} : Set R)) ^ k •
          (⊤ : Submodule R
            (adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R)))) := by
  ext f
  conv_rhs => rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  rw [Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]
  constructor
  · intro hf
    rw [LinearMap.mem_ker, linearAdicReduction_apply] at hf
    have hr : f ∈ RingHom.ker (adicReduction (σ := σ)
        (Ideal.span ({a} : Set R)) k) := (RingHom.mem_ker).2 hf
    rw [ker_adicReduction_principal a ha k] at hr
    obtain ⟨g, hg⟩ := (Ideal.mem_span_singleton').1 hr
    refine ⟨g, ?_⟩
    rw [← principalAdicConstant_mul_eq_smul, mul_comm, hg]
  · rintro ⟨g, hg⟩
    rw [LinearMap.mem_ker, linearAdicReduction_apply, ← RingHom.mem_ker]
    rw [ker_adicReduction_principal a ha k]
    apply (Ideal.mem_span_singleton').2
    exact ⟨g, by
      calc
        g * principalAdicConstant a k = principalAdicConstant a k * g := mul_comm _ _
        _ = (a ^ k) • g := principalAdicConstant_mul_eq_smul a k g
        _ = f := hg⟩

/-- Native first isomorphism for the regular principal ideal-power quotient. -/
noncomputable def principalLinearQuotientEquiv (a : R) (ha : IsRegular a) (k : ℕ) :
    (adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R)) ⧸
      ((Ideal.span ({a} : Set R)) ^ k •
        (⊤ : Submodule R
          (adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R)))))) ≃ₗ[R]
      MvPolynomial σ (R ⧸ (Ideal.span ({a} : Set R)) ^ k) :=
  (Submodule.quotEquivOfEq _ _
    (ker_linearAdicReduction_principal (σ := σ) a ha k).symm).trans
      ((linearAdicReduction (σ := σ) (Ideal.span ({a} : Set R)) k).quotKerEquivOfSurjective
        (linearAdicReduction_surjective (σ := σ) (Ideal.span ({a} : Set R)) k))

@[simp]
theorem principalLinearQuotientEquiv_mk (a : R) (ha : IsRegular a) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R))) :
    principalLinearQuotientEquiv a ha k (Submodule.Quotient.mk f) =
      adicReduction (Ideal.span ({a} : Set R)) k f := by
  simp [principalLinearQuotientEquiv]

/-- The integer-linear reduction uses the native integer module on the restricted subtype. -/
noncomputable def intLinearAdicReduction (I : Ideal ℤ) (k : ℕ) :
    adicallyRestrictedSubring (σ := σ) I →ₗ[ℤ] MvPolynomial σ (ℤ ⧸ I ^ k) :=
  (adicReduction I k).toAddMonoidHom.toIntLinearMap

@[simp]
theorem intLinearAdicReduction_apply (I : Ideal ℤ) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    intLinearAdicReduction I k f = adicReduction I k f := by
  change (adicReduction I k).toAddMonoidHom f = adicReduction I k f
  rfl

@[simp]
theorem coeff_intLinearAdicReduction (I : Ideal ℤ) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I) (m : σ →₀ ℕ) :
    (intLinearAdicReduction I k f).coeff m =
      Ideal.Quotient.mk (I ^ k) (coeff m (f : MvPowerSeries σ ℤ)) := by
  rw [intLinearAdicReduction_apply, coeff_adicReduction]

theorem intLinearAdicReduction_surjective (I : Ideal ℤ) (k : ℕ) :
    Function.Surjective (intLinearAdicReduction (σ := σ) I k) :=
  adicReduction_surjective I k

/-- The scalar action in the generic principal-constant lemma is the native integer action. -/
theorem principalAdicConstant_mul_eq_int_smul (a : ℤ) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set ℤ))) :
    principalAdicConstant a k * f = (a ^ k) • f := by
  have h : principalAdicConstant (σ := σ) a k =
      (a ^ k : adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set ℤ))) := by
    apply Subtype.ext
    simp
  rw [h]
  simpa only [smul_eq_mul, Int.cast_pow] using
    (Int.cast_smul_eq_zsmul (R := adicallyRestrictedSubring (σ := σ)
      (Ideal.span ({a} : Set ℤ))) (a ^ k) f)

/-- The canonical integer-linear kernel is the native ideal-power submodule. -/
theorem ker_intLinearAdicReduction_principal (a : ℤ) (ha : IsRegular a) (k : ℕ) :
    LinearMap.ker (intLinearAdicReduction (σ := σ)
      (Ideal.span ({a} : Set ℤ)) k) =
        (Ideal.span ({a} : Set ℤ)) ^ k •
          (⊤ : Submodule ℤ
            (adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set ℤ)))) := by
  ext f
  conv_rhs => rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  rw [Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]
  constructor
  · intro hf
    rw [LinearMap.mem_ker, intLinearAdicReduction_apply] at hf
    have hr : f ∈ RingHom.ker (adicReduction (σ := σ)
        (Ideal.span ({a} : Set ℤ)) k) := (RingHom.mem_ker).2 hf
    rw [ker_adicReduction_principal a ha k] at hr
    obtain ⟨g, hg⟩ := (Ideal.mem_span_singleton').1 hr
    refine ⟨g, ?_⟩
    rw [← principalAdicConstant_mul_eq_int_smul, mul_comm, hg]
  · rintro ⟨g, hg⟩
    rw [LinearMap.mem_ker, intLinearAdicReduction_apply, ← RingHom.mem_ker]
    rw [ker_adicReduction_principal a ha k]
    apply (Ideal.mem_span_singleton').2
    exact ⟨g, by
      calc
        g * principalAdicConstant a k = principalAdicConstant a k * g := mul_comm _ _
        _ = (a ^ k) • g := principalAdicConstant_mul_eq_int_smul a k g
        _ = f := hg⟩

/-- First isomorphism with the native integer submodule and quotient types. -/
noncomputable def principalIntLinearQuotientEquiv (a : ℤ) (ha : IsRegular a) (k : ℕ) :
    (adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set ℤ)) ⧸
      ((Ideal.span ({a} : Set ℤ)) ^ k •
        (⊤ : Submodule ℤ
          (adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set ℤ)))))) ≃ₗ[ℤ]
      MvPolynomial σ (ℤ ⧸ (Ideal.span ({a} : Set ℤ)) ^ k) :=
  (Submodule.quotEquivOfEq _ _
    (ker_intLinearAdicReduction_principal (σ := σ) a ha k).symm).trans
      ((intLinearAdicReduction (σ := σ) (Ideal.span ({a} : Set ℤ)) k).quotKerEquivOfSurjective
        (intLinearAdicReduction_surjective (σ := σ) (Ideal.span ({a} : Set ℤ)) k))

@[simp]
theorem principalIntLinearQuotientEquiv_mk (a : ℤ) (ha : IsRegular a) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set ℤ))) :
    principalIntLinearQuotientEquiv a ha k (Submodule.Quotient.mk f) =
      adicReduction (Ideal.span ({a} : Set ℤ)) k f := by
  simp [principalIntLinearQuotientEquiv]

end MvPowerSeries
