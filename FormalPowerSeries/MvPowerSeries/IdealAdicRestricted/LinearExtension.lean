/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.InverseLimit
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearQuotient
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.MonoidAlgebra.Module

public section

/-!
# Linear extension to ideal-adically restricted multivariate series

Every linear endomorphism of a multivariate polynomial ring extends uniquely to the
restricted series over an adically complete coefficient ring if the extension preserves
the coefficientwise reduction kernels. The variable type and coefficient ideal are arbitrary.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

/-- The coefficientwise reduction of a polynomial linear operator. The coefficients of
the quotient polynomial are combined against the reduced images of its monomial basis. -/
noncomputable def polynomialLinearMapMod (I : Ideal R) (n : ℕ)
    (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) :
    MvPolynomial σ (R ⧸ I ^ n) →ₗ[R ⧸ I ^ n] MvPolynomial σ (R ⧸ I ^ n) :=
  (Finsupp.linearCombination (R ⧸ I ^ n)
      (fun index => MvPolynomial.map (Ideal.Quotient.mk (I ^ n))
        (F (MvPolynomial.monomial index 1)))).comp
    (AddMonoidAlgebra.coeffLinearEquiv (R ⧸ I ^ n)).toLinearMap

private theorem polynomialLinearMapMod_monomial (I : Ideal R) (n : ℕ)
    (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)
    (index : σ →₀ ℕ) (a : R ⧸ I ^ n) :
    polynomialLinearMapMod I n F (MvPolynomial.monomial index a) =
      a • MvPolynomial.map (Ideal.Quotient.mk (I ^ n))
        (F (MvPolynomial.monomial index 1)) := by
  simp [polynomialLinearMapMod, Finsupp.linearCombination_apply]

/-- Reduction of the original operator agrees with its quotient-level operator. -/
theorem polynomialLinearMapMod_map (I : Ideal R) (n : ℕ)
    (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) (p : MvPolynomial σ R) :
    polynomialLinearMapMod I n F (MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p) =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) (F p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial index a =>
    simp only [MvPolynomial.map_monomial, polynomialLinearMapMod_monomial]
    have h : MvPolynomial.monomial index a =
        a • MvPolynomial.monomial index (1 : R) := by simp [MvPolynomial.smul_monomial]
    rw [h, F.map_smul]
    ext degree
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_smul, smul_eq_mul, map_mul]

/-- Passing to a lower quotient level commutes with the polynomial operator. -/
theorem polynomialLinearMapMod_factorPow (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)
    (p : MvPolynomial σ (R ⧸ I ^ n)) :
    MvPolynomial.map (Ideal.Quotient.factorPow I hmn) (polynomialLinearMapMod I n F p) =
      polynomialLinearMapMod I m F (MvPolynomial.map (Ideal.Quotient.factorPow I hmn) p) := by
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective
    (Ideal.Quotient.mk (I ^ n)) Ideal.Quotient.mk_surjective p
  have hmap (x : MvPolynomial σ R) :
      MvPolynomial.map (Ideal.Quotient.factorPow I hmn)
          (MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) x) =
        MvPolynomial.map (Ideal.Quotient.mk (I ^ m)) x := by
    ext index
    simp only [MvPolynomial.coeff_map, Ideal.Quotient.factor_mk]
  rw [polynomialLinearMapMod_map, hmap, hmap, polynomialLinearMapMod_map]

private theorem nativeTransition_quotientEquiv (J : Ideal (MvPolynomial σ R))
    {m n : ℕ} (hmn : m ≤ n)
    (x : MvPolynomial σ R ⧸ J ^ n) :
    AdicCompletion.transitionMap J (MvPolynomial σ R) hmn
        ((Ideal.quotientEquivAlgOfEq (MvPolynomial σ R) (Ideal.mul_top (J ^ n))).symm x) =
      (Ideal.quotientEquivAlgOfEq (MvPolynomial σ R) (Ideal.mul_top (J ^ m))).symm
        (Ideal.Quotient.factorPow J hmn x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.Quotient.factor_mk]
  rfl

private noncomputable def completionOfPolynomialLevels (I : Ideal R)
    (polynomials : ∀ n, MvPolynomial σ (R ⧸ I ^ n))
    (hpolynomials : ∀ {m n : ℕ} (hmn : m ≤ n),
      MvPolynomial.map (Ideal.Quotient.factorPow I hmn) (polynomials n) =
        polynomials m) :
    AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
      (MvPolynomial σ R) :=
  ⟨fun n =>
      (Ideal.quotientEquivAlgOfEq (MvPolynomial σ R)
        (Ideal.mul_top ((I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n))).symm
        ((adicPolynomialLevelEquiv (σ := σ) I n).symm (polynomials n)), by
    intro m n hmn
    rw [nativeTransition_quotientEquiv]
    change (Ideal.quotientEquivAlgOfEq (MvPolynomial σ R)
      (Ideal.mul_top ((I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ m))).symm
        (Ideal.Quotient.factorPow _ hmn
          ((adicPolynomialLevelEquiv (σ := σ) I n).symm (polynomials n))) =
      (Ideal.quotientEquivAlgOfEq (MvPolynomial σ R)
        (Ideal.mul_top ((I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ m))).symm
          ((adicPolynomialLevelEquiv (σ := σ) I m).symm (polynomials m))
    congr 1
    apply (adicPolynomialLevelEquiv (σ := σ) I m).injective
    rw [adicPolynomialLevelEquiv_factorPow]
    simp only [RingEquiv.apply_symm_apply, hpolynomials hmn]⟩

private theorem completionOfPolynomialLevels_eval (I : Ideal R)
    (polynomials : ∀ n, MvPolynomial σ (R ⧸ I ^ n))
    (hpolynomials : ∀ {m n : ℕ} (hmn : m ≤ n),
      MvPolynomial.map (Ideal.Quotient.factorPow I hmn) (polynomials n) =
        polynomials m) (n : ℕ) :
    adicPolynomialLevelEquiv (σ := σ) I n
        (AdicCompletion.evalₐ _ n
          (completionOfPolynomialLevels I polynomials hpolynomials)) = polynomials n := by
  change adicPolynomialLevelEquiv (σ := σ) I n
    ((Ideal.quotientEquivAlgOfEq (MvPolynomial σ R)
      (Ideal.mul_top ((I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n)))
      ((Ideal.quotientEquivAlgOfEq (MvPolynomial σ R)
        (Ideal.mul_top ((I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n))).symm
        ((adicPolynomialLevelEquiv (σ := σ) I n).symm (polynomials n)))) = _
  rw [AlgEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

private theorem restricted_eq_of_reductions (I : Ideal R) [IsAdicComplete I R]
    {f g : adicallyRestrictedSubring (σ := σ) I}
    (h : ∀ n, adicReduction I n f = adicReduction I n g) : f = g := by
  apply (adicallyRestrictedEquivAdicCompletion (σ := σ) I).injective
  apply AdicCompletion.ext_evalₐ
  intro n
  apply (adicPolynomialLevelEquiv (σ := σ) I n).injective
  simpa only [adicallyRestrictedEquivAdicCompletion_eval] using h n

private theorem extendedPolynomialLevels_compat (I : Ideal R)
    (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)
    (f : adicallyRestrictedSubring (σ := σ) I) {m n : ℕ} (hmn : m ≤ n) :
    MvPolynomial.map (Ideal.Quotient.factorPow I hmn)
        (polynomialLinearMapMod I n F (adicReduction I n f)) =
      polynomialLinearMapMod I m F (adicReduction I m f) := by
  rw [polynomialLinearMapMod_factorPow, adicReduction_factorPow]

private noncomputable def restrictedLinearExtensionFun (I : Ideal R)
    [IsAdicComplete I R] (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    adicallyRestrictedSubring (σ := σ) I :=
  (adicallyRestrictedEquivAdicCompletion I).symm
    (completionOfPolynomialLevels I
      (fun n => polynomialLinearMapMod I n F (adicReduction I n f))
      (extendedPolynomialLevels_compat I F f))

private theorem adicReduction_restrictedLinearExtensionFun (I : Ideal R)
    [IsAdicComplete I R] (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)
    (n : ℕ) (f : adicallyRestrictedSubring (σ := σ) I) :
    adicReduction I n (restrictedLinearExtensionFun I F f) =
      polynomialLinearMapMod I n F (adicReduction I n f) := by
  rw [restrictedLinearExtensionFun, adicallyRestrictedEquivAdicCompletion_symm_eval,
    completionOfPolynomialLevels_eval]

/-- The canonical linear extension of any polynomial endomorphism to restricted series.
Completeness is required only for the coefficient ring, not the restricted-series ring. -/
noncomputable def restrictedLinearExtension (I : Ideal R) [IsAdicComplete I R]
    (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) :
    adicallyRestrictedSubring (σ := σ) I →ₗ[R]
      adicallyRestrictedSubring (σ := σ) I where
  toFun := restrictedLinearExtensionFun I F
  map_add' f g := by
    apply restricted_eq_of_reductions I
    intro n
    simp only [adicReduction_restrictedLinearExtensionFun, map_add]
  map_smul' r f := by
    apply restricted_eq_of_reductions I
    intro n
    rw [adicReduction_restrictedLinearExtensionFun]
    simp only [RingHom.id_apply]
    rw [← linearAdicReduction_apply I n (r • f),
      ← linearAdicReduction_apply I n (r • restrictedLinearExtensionFun I F f)]
    rw [(linearAdicReduction I n).map_smul r f,
      (linearAdicReduction I n).map_smul r (restrictedLinearExtensionFun I F f)]
    simp only [linearAdicReduction_apply, adicReduction_restrictedLinearExtensionFun]
    exact (polynomialLinearMapMod I n F).map_smul_of_tower r _

/-- At each level, the extension is exactly the finite polynomial operator. -/
@[simp]
theorem adicReduction_restrictedLinearExtension (I : Ideal R) [IsAdicComplete I R]
    (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)
    (n : ℕ) (f : adicallyRestrictedSubring (σ := σ) I) :
    adicReduction I n (restrictedLinearExtension I F f) =
      polynomialLinearMapMod I n F (adicReduction I n f) :=
  adicReduction_restrictedLinearExtensionFun I F n f

/-- On polynomial inputs, the extension is the original polynomial operator. -/
@[simp]
theorem restrictedLinearExtension_polynomial (I : Ideal R) [IsAdicComplete I R]
    (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)
    (p : MvPolynomial σ R) :
    restrictedLinearExtension I F (polynomialToRestricted I p) =
      polynomialToRestricted I (F p) := by
  apply restricted_eq_of_reductions I
  intro n
  simp only [adicReduction_restrictedLinearExtension,
    adicReduction_polynomial, polynomialLinearMapMod_map]

/-- The extension preserves each coefficientwise ideal-power kernel. No identification
of this kernel with an intrinsic ideal-power submodule is needed. -/
theorem restrictedLinearExtension_preserves_ker (I : Ideal R) [IsAdicComplete I R]
    (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)
    (n : ℕ) (f : adicallyRestrictedSubring (σ := σ) I)
    (hf : f ∈ RingHom.ker (adicReduction (σ := σ) I n)) :
    restrictedLinearExtension I F f ∈ RingHom.ker (adicReduction (σ := σ) I n) := by
  rw [RingHom.mem_ker] at hf ⊢
  rw [adicReduction_restrictedLinearExtension, hf]
  exact (polynomialLinearMapMod I n F).map_zero

/-- An `R`-linear map agreeing on polynomials and preserving all coefficientwise
reduction kernels is the canonical extension. -/
theorem restrictedLinearExtension_unique (I : Ideal R) [IsAdicComplete I R]
    (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)
    (G : adicallyRestrictedSubring (σ := σ) I →ₗ[R]
      adicallyRestrictedSubring (σ := σ) I)
    (hOnPoly : ∀ p : MvPolynomial σ R,
      G (polynomialToRestricted I p) = polynomialToRestricted I (F p))
    (hker : ∀ n f, adicReduction I n f = 0 → adicReduction I n (G f) = 0) :
    G = restrictedLinearExtension I F := by
  apply LinearMap.ext
  intro f
  apply restricted_eq_of_reductions I
  intro n
  obtain ⟨p, hp⟩ := MvPolynomial.map_surjective
    (Ideal.Quotient.mk (I ^ n)) Ideal.Quotient.mk_surjective (adicReduction I n f)
  have hlevel : adicReduction I n (polynomialToRestricted I p) = adicReduction I n f := by
    rw [adicReduction_polynomial]
    exact hp
  have hzero : adicReduction I n (f - polynomialToRestricted I p) = 0 := by
    rw [map_sub, hlevel, sub_self]
  have hGlevel : adicReduction I n (G f) =
      adicReduction I n (G (polynomialToRestricted I p)) := by
    have hsub := congrArg (adicReduction I n) (G.map_sub f (polynomialToRestricted I p))
    rw [hker n _ hzero, map_sub] at hsub
    exact sub_eq_zero.mp hsub.symm
  calc
    adicReduction I n (G f) =
        adicReduction I n (G (polynomialToRestricted I p)) := hGlevel
    _ = adicReduction I n (polynomialToRestricted I (F p)) := by rw [hOnPoly]
    _ = polynomialLinearMapMod I n F (adicReduction I n f) := by
      rw [adicReduction_polynomial, ← polynomialLinearMapMod_map, hp]
    _ = adicReduction I n (restrictedLinearExtension I F f) :=
      (adicReduction_restrictedLinearExtension I F n f).symm

end MvPowerSeries
