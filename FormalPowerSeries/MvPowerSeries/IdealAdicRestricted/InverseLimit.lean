/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import AdicModules.AdicCompletion.RestrictScalars
public import AdicModules.AdicCompletion.DFinsupp

public section

/-!
# Ideal-adically restricted series and the polynomial completion

Completion of the multivariate polynomial ring at a coefficient ideal is the
algebra of power series over the completed coefficient ring whose reductions at
every original ideal power are polynomial. The source algebra is the named
`AdicCompletion.extendedAlgebra`, induced by completing the original coefficient
map; the target has its usual coefficient algebra. Neither the variable type nor
the ideal need be finite, and the original coefficient ring need not be complete.

For complete original coefficients, coefficient transport by
`AdicCompletion.ofAlgEquiv` recovers the ideal-adically restricted series ring.
Both comparisons use the same completion-of-direct-sums equivalence.

## References

The construction reuses Mathlib's polynomial quotient equivalence, coefficient
linear equivalences, adic completion and completed scalar actions. The full linear
bijection and inverse are AdicModules' `AdicCompletion.dfinsuppEquiv`, composed
with its restriction-of-scalars comparison. The finite polynomial reductions are
the polynomial-reduction API of this library.
-/

set_option warningAsError true

universe u v

namespace MvPowerSeries

variable {σ : Type v} {R : Type u} [CommRing R]

/-- The polynomial/quotient equivalence, transported across `Ideal.map_pow`. -/
noncomputable def adicPolynomialLevelEquiv (I : Ideal R) (n : ℕ) :
    (MvPolynomial σ R ⧸
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n) ≃+*
      MvPolynomial σ (R ⧸ I ^ n) :=
  (Ideal.quotientEquivAlgOfEq (MvPolynomial σ R)
    (Ideal.map_pow (MvPolynomial.C : R →+* MvPolynomial σ R) I n).symm).toRingEquiv.trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) (I ^ n)).symm.toRingEquiv

/-- The level equivalence sends a quotient polynomial to coefficientwise reduction. -/
@[simp]
theorem adicPolynomialLevelEquiv_mk (I : Ideal R) (n : ℕ) (p : MvPolynomial σ R) :
    adicPolynomialLevelEquiv (σ := σ) I n (Ideal.Quotient.mk _ p) =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p := by
  simp only [adicPolynomialLevelEquiv, RingEquiv.trans_apply]
  change (MvPolynomial.quotientEquivQuotientMvPolynomial (I ^ n)).symm
    (Ideal.Quotient.mk ((I ^ n).map (MvPolynomial.C : R →+* MvPolynomial σ R)) p) = _
  change Ideal.Quotient.lift
    ((I ^ n).map (MvPolynomial.C : R →+* MvPolynomial σ R))
    (MvPolynomial.eval₂Hom
      (MvPolynomial.C.comp (Ideal.Quotient.mk (I ^ n))) MvPolynomial.X)
    (fun _ ha => MvPolynomial.eval₂_C_mk_eq_zero ha)
    (Ideal.Quotient.mk _ p) = _
  simp only [Ideal.Quotient.lift_mk, ← MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- The existing finite reductions commute with quotient-power transitions. -/
theorem adicReduction_factorPow (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    MvPolynomial.map (Ideal.Quotient.factorPow I hmn) (adicReduction I n f) =
      adicReduction I m f := by
  ext index
  simp only [MvPolynomial.coeff_map, coeff_adicReduction,
    Ideal.Quotient.factor_mk]

/-- The level bridge respects the quotient transitions on arbitrary elements. -/
theorem adicPolynomialLevelEquiv_factorPow (I : Ideal R) {m n : ℕ}
    (hmn : m ≤ n)
    (x : MvPolynomial σ R ⧸
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n) :
    adicPolynomialLevelEquiv (σ := σ) I m
        (Ideal.Quotient.factorPow (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
          hmn x) =
      MvPolynomial.map (Ideal.Quotient.factorPow I hmn)
        (adicPolynomialLevelEquiv (σ := σ) I n x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.Quotient.factor_mk, adicPolynomialLevelEquiv_mk,
    MvPolynomial.map_map]
  apply MvPolynomial.ext
  intro index
  simp only [MvPolynomial.coeff_map, RingHom.comp_apply, Ideal.Quotient.factor_mk]

end MvPowerSeries

section CompletedCoefficients

namespace MvPowerSeries

variable {R : Type u} [CommRing R] {σ : Type v}

private theorem evalₐ_eq_zero_iff (I : Ideal R) (n : ℕ) (a : AdicCompletion I R) :
    AdicCompletion.evalₐ I n a = 0 ↔ AdicCompletion.eval I R n a = 0 := by
  let e := Ideal.quotientEquivAlgOfEq R (Ideal.mul_top (I ^ n))
  change e (AdicCompletion.eval I R n a) = 0 ↔ _
  constructor
  · intro h
    apply e.injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- Identification of the existing restricted product with the series subalgebra;
only normalization of the equal-ideal quotient changes the support condition. -/
@[expose]
noncomputable def restrictedProductEquivPolynomialReduction (σ : Type v) (I : Ideal R) :
    AdicCompletion.restrictedProduct I (fun _ : σ →₀ ℕ => R) ≃ₗ[AdicCompletion I R]
      polynomialReductionSubalgebra σ (fun n => (AdicCompletion.evalₐ I n :
        AdicCompletion I R →+* (R ⧸ I ^ n))) where
  toFun x := ⟨x.val, by
    apply (mem_polynomialReductionSubalgebra_iff_finite_support σ _ _).2
    intro n
    change Set.Finite {d : σ →₀ ℕ | AdicCompletion.evalₐ I n (x.val d) ≠ 0}
    simpa only [ne_eq, evalₐ_eq_zero_iff] using
      (AdicCompletion.mem_restrictedProduct I (fun _ : σ →₀ ℕ => R) _).1 x.property n⟩
  invFun f := ⟨f.val, by
    apply (AdicCompletion.mem_restrictedProduct I (fun _ : σ →₀ ℕ => R) _).2
    intro n
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPowerSeries.coeff_apply,
      ne_eq, evalₐ_eq_zero_iff] using
      (mem_polynomialReductionSubalgebra_iff_finite_support σ _ _).1 f.property n⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The restricted-product comparison preserves each completed coefficient. -/
@[simp]
theorem coeff_restrictedProductEquivPolynomialReduction (σ : Type v) (I : Ideal R)
    (a : AdicCompletion.restrictedProduct I (fun _ : σ →₀ ℕ => R)) (d : σ →₀ ℕ) :
    coeff d (restrictedProductEquivPolynomialReduction σ I a).val = a.val d :=
  rfl

/-- The inverse comparison reads off the completed coefficients of the series. -/
@[simp]
theorem restrictedProductEquivPolynomialReduction_symm_apply (σ : Type v) (I : Ideal R)
    (s : polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)))
    (d : σ →₀ ℕ) :
    ((restrictedProductEquivPolynomialReduction σ I).symm s).val d = coeff d s.val :=
  rfl

end MvPowerSeries

namespace MvPolynomial

open MvPowerSeries

variable {R : Type u} [CommRing R] {σ : Type v}

-- Give instance search the normalized polynomial ideal as its class head.
-- The value is the existing named algebra, with the stock coefficient algebra.
private noncomputable abbrev completedPolynomialAlgebra (σ : Type v) (I : Ideal R) :
    Algebra (AdicCompletion I R)
      (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R)) :=
  AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I

private theorem completedPolynomialAlgebra_eq (σ : Type v) (I : Ideal R) :
    completedPolynomialAlgebra σ I =
      (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
        Algebra (AdicCompletion I R)
          (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R))) :=
  rfl

attribute [local instance] completedPolynomialAlgebra

private noncomputable def polynomialCoefficients (σ : Type v) :
    MvPolynomial σ R ≃ₗ[R] Π₀ (_ : σ →₀ ℕ), R := by
  classical
  exact (AddMonoidAlgebra.coeffLinearEquiv R).trans (finsuppLequivDFinsupp R)

private theorem polynomialCoefficients_apply (p : MvPolynomial σ R) (d : σ →₀ ℕ) :
    polynomialCoefficients σ p d = p.coeff d := by
  classical
  rfl

private noncomputable def restrictPolynomialScalars (σ : Type v) (I : Ideal R) :
    AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)
      ≃ₗ[AdicCompletion I R] AdicCompletion I (MvPolynomial σ R) where
  __ := (AdicCompletion.restrictScalarsEquiv (S := MvPolynomial σ R) I
    (MvPolynomial σ R)).toEquiv
  map_add' := (AdicCompletion.restrictScalarsEquiv
    (S := MvPolynomial σ R) I (MvPolynomial σ R)).map_add
  map_smul' a x := by
    change AdicCompletion.restrictScalarsEquiv (S := MvPolynomial σ R) I (MvPolynomial σ R)
        (AdicCompletion.mapRingHom I (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
          (MvPolynomial.C : R →+* MvPolynomial σ R) Ideal.le_comap_map a * x) = _
    exact AdicCompletion.restrictScalarsEquiv_smul (S := MvPolynomial σ R) I a x

private noncomputable def completionCoefficients (σ : Type v) (I : Ideal R) :
    AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)
      ≃ₗ[AdicCompletion I R]
        polynomialReductionSubalgebra σ (fun n => (AdicCompletion.evalₐ I n :
          AdicCompletion I R →+* (R ⧸ I ^ n))) :=
  (restrictPolynomialScalars σ I).trans
    ((AdicCompletion.congr I (polynomialCoefficients σ)).trans
      ((AdicCompletion.dfinsuppEquiv I (fun _ : σ →₀ ℕ => R)).trans
        (restrictedProductEquivPolynomialReduction σ I)))

private theorem completionCoefficients_coeff (I : Ideal R)
    (x : AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
    (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (completionCoefficients σ I x).val =
      AdicCompletion.map I (MvPolynomial.lcoeff R d)
        (AdicCompletion.restrictScalarsEquiv (S := MvPolynomial σ R) I (MvPolynomial σ R) x) := by
  have hcoord : DFinsupp.lapply (R := R) (M := fun _ : σ →₀ ℕ => R) d ∘ₗ
      (polynomialCoefficients σ).toLinearMap = MvPolynomial.lcoeff R d := by
    apply LinearMap.ext
    intro p
    exact polynomialCoefficients_apply p d
  have hprojection := AdicCompletion.dfinsuppEquiv_apply_apply I
    (fun _ : σ →₀ ℕ => R)
    (AdicCompletion.congr I (polynomialCoefficients σ)
      (AdicCompletion.restrictScalarsEquiv (S := MvPolynomial σ R) I (MvPolynomial σ R) x)) d
  have hcomposition := AdicCompletion.map_comp_apply I
    (polynomialCoefficients σ).toLinearMap
    (DFinsupp.lapply (R := R) (M := fun _ : σ →₀ ℕ => R) d)
    (AdicCompletion.restrictScalarsEquiv (S := MvPolynomial σ R) I (MvPolynomial σ R) x)
  exact hprojection.trans (hcomposition.trans
    (congrArg (fun f : MvPolynomial σ R →ₗ[R] R =>
      AdicCompletion.map I f
        (AdicCompletion.restrictScalarsEquiv (S := MvPolynomial σ R) I (MvPolynomial σ R) x))
          hcoord))

private theorem completedCoefficient_eval (I : Ideal R) (n : ℕ)
    (x : AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
    (d : σ →₀ ℕ) :
    AdicCompletion.evalₐ I n
        (AdicCompletion.map I (MvPolynomial.lcoeff R d)
          (AdicCompletion.restrictScalarsEquiv (S := MvPolynomial σ R) I (MvPolynomial σ R) x)) =
      (adicPolynomialLevelEquiv I n (AdicCompletion.evalₐ _ n x)).coeff d := by
  obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective _
    (AdicCompletion.eval (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
      (MvPolynomial σ R) n x)
  have hx : AdicCompletion.evalₐ _ n x =
      Ideal.Quotient.mk ((I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n) p := by
    rw [← AdicCompletion.factor_eval_eq_evalₐ _ x (le_of_eq (Ideal.mul_top _)), ← hp]
    rfl
  -- Compare the two quotient evaluations by typed equalities, preserving
  -- their stock additive structures.
  have hlevel : adicPolynomialLevelEquiv I n (AdicCompletion.evalₐ _ n x) =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p :=
    (congrArg (fun q : MvPolynomial σ R ⧸
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n =>
        adicPolynomialLevelEquiv I n q) hx).trans (adicPolynomialLevelEquiv_mk I n p)
  have hcoeff : AdicCompletion.evalₐ I n
      (AdicCompletion.map I (MvPolynomial.lcoeff R d)
        (AdicCompletion.restrictScalarsEquiv (S := MvPolynomial σ R) I (MvPolynomial σ R) x)) =
      Ideal.Quotient.mk (I ^ n) (p.coeff d) := by
    have heval : AdicCompletion.eval I (MvPolynomial σ R) n
        (AdicCompletion.restrictScalarsEquiv (S := MvPolynomial σ R) I (MvPolynomial σ R) x) =
        (Submodule.Quotient.mk p :
          MvPolynomial σ R ⧸ (I ^ n • (⊤ : Submodule R (MvPolynomial σ R)))) :=
      (AdicCompletion.restrictScalarsEquiv_eval (S := MvPolynomial σ R) I x n).trans
        ((congrArg (AdicCompletion.restrictScalarsLevelEquiv
          (S := MvPolynomial σ R) I (MvPolynomial σ R) n) hp.symm).trans
            (AdicCompletion.restrictScalarsLevelEquiv_mk
              (S := MvPolynomial σ R) I n p))
    exact (AdicCompletion.factor_eval_eq_evalₐ I
      (AdicCompletion.map I (MvPolynomial.lcoeff R d)
        (AdicCompletion.restrictScalarsEquiv (S := MvPolynomial σ R) I (MvPolynomial σ R) x))
      (le_of_eq (Ideal.mul_top (I ^ n)))).symm.trans
        ((congrArg (fun q :
          MvPolynomial σ R ⧸ (I ^ n • (⊤ : Submodule R (MvPolynomial σ R))) =>
            Ideal.Quotient.factor (le_of_eq (Ideal.mul_top (I ^ n)))
              ((MvPolynomial.lcoeff R d).reduceModIdeal (I ^ n) q)) heval).trans
                (by rfl))
  exact hcoeff.trans
    ((MvPolynomial.coeff_map (Ideal.Quotient.mk (I ^ n)) p d).symm.trans
      (congrArg (fun q : MvPolynomial σ (R ⧸ I ^ n) => q.coeff d) hlevel.symm))

private theorem completionCoefficients_reduction (I : Ideal R) (n : ℕ)
    (x : AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :
    polynomialReduction σ (fun n => (AdicCompletion.evalₐ I n :
      AdicCompletion I R →+* (R ⧸ I ^ n))) n
        (completionCoefficients σ I x) =
      adicPolynomialLevelEquiv I n (AdicCompletion.evalₐ _ n x) := by
  apply MvPolynomial.ext
  intro d
  rw [coeff_polynomialReduction, completionCoefficients_coeff]
  exact completedCoefficient_eval I n x d

private theorem rawReductions_injective (I : Ideal R) :
    Function.Injective (fun f : polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n :
        AdicCompletion I R →+* (R ⧸ I ^ n))) => fun n =>
        polynomialReduction σ (fun n => (AdicCompletion.evalₐ I n :
          AdicCompletion I R →+* (R ⧸ I ^ n))) n f) := by
  apply (polynomialReduction_jointly_injective_iff σ _).2
  intro a b h
  exact AdicCompletion.ext_evalₐ (fun n => congrFun h n)

private theorem completionCoefficients_mul (I : Ideal R)
    (x y : AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :
    completionCoefficients σ I (x * y) =
      completionCoefficients σ I x * completionCoefficients σ I y := by
  apply rawReductions_injective I
  funext n
  have hmul : adicPolynomialLevelEquiv I n (AdicCompletion.evalₐ _ n (x * y)) =
      adicPolynomialLevelEquiv I n (AdicCompletion.evalₐ _ n x) *
        adicPolynomialLevelEquiv I n (AdicCompletion.evalₐ _ n y) :=
    map_mul ((adicPolynomialLevelEquiv I n).toRingHom.comp
      (AdicCompletion.evalₐ (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) n).toRingHom) x y
  exact (completionCoefficients_reduction I n (x * y)).trans (hmul.trans
    ((congrArg₂ (fun p q : MvPolynomial σ (R ⧸ I ^ n) => p * q)
      (completionCoefficients_reduction I n x).symm
      (completionCoefficients_reduction I n y).symm).trans
        (map_mul (polynomialReduction σ
          (fun n => (AdicCompletion.evalₐ I n :
            AdicCompletion I R →+* (R ⧸ I ^ n))) n)
          (completionCoefficients σ I x) (completionCoefficients σ I y)).symm))

private theorem completionCoefficients_algebraMap (I : Ideal R) (a : AdicCompletion I R) :
    completionCoefficients σ I
        (algebraMap (AdicCompletion I R)
          (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) a) =
      algebraMap (AdicCompletion I R)
        (polynomialReductionSubalgebra σ (fun n => (AdicCompletion.evalₐ I n :
          AdicCompletion I R →+* (R ⧸ I ^ n)))) a := by
  apply rawReductions_injective I
  funext n
  -- This is the existing level bridge, with its domain written to match the
  -- producer's quotient evaluation square.
  let e : (MvPolynomial σ R ⧸
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n) ≃+*
        MvPolynomial σ (R ⧸ I ^ n) := adicPolynomialLevelEquiv I n
  have hconstant : e
      (Ideal.quotientMap ((I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n)
        (MvPolynomial.C : R →+* MvPolynomial σ R)
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans
          (Ideal.le_comap_pow (MvPolynomial.C : R →+* MvPolynomial σ R) n))
        (AdicCompletion.evalₐ I n a)) = MvPolynomial.C (AdicCompletion.evalₐ I n a) := by
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n a)
    rw [← hr, Ideal.quotientMap_mk]
    exact (adicPolynomialLevelEquiv_mk I n (MvPolynomial.C r)).trans
      (MvPolynomial.map_C (Ideal.Quotient.mk (I ^ n)) r)
  have hrow : adicPolynomialLevelEquiv I n
      (AdicCompletion.evalₐ _ n
        (algebraMap (AdicCompletion I R)
          (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R)) a)) = MvPolynomial.C (AdicCompletion.evalₐ I n a) :=
    (congrArg e (AdicCompletion.evalₐ_extendedAlgebra_algebraMap
      (T := MvPolynomial σ R) I n a)).trans hconstant
  exact (completionCoefficients_reduction I n _).trans (hrow.trans
    (polynomialReduction_algebraMap σ
      (fun n => (AdicCompletion.evalₐ I n :
        AdicCompletion I R →+* (R ⧸ I ^ n))) n a).symm)

/-- Completion of the polynomial ring at the extended coefficient ideal is the
coefficient algebra of series that are polynomial at every original quotient precision.
The linear bijection and inverse reuse `AdicCompletion.dfinsuppEquiv`; the source
algebra is exactly `AdicCompletion.extendedAlgebra`. -/
noncomputable def adicCompletionEquiv (σ : Type v) (I : Ideal R) :
    @AlgEquiv (AdicCompletion I R)
      (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
      (MvPowerSeries.polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n :
          AdicCompletion I R →+* (R ⧸ I ^ n))))
      (CommRing.toCommSemiring (α := AdicCompletion I R))
      (CommRing.toCommSemiring
        (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
          (MvPolynomial σ R))).toSemiring
      (Subalgebra.toSemiring
        (MvPowerSeries.polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n :
            AdicCompletion I R →+* (R ⧸ I ^ n)))))
      (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
        Algebra (AdicCompletion I R)
          (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R)))
      (Subalgebra.algebra
        (MvPowerSeries.polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n :
            AdicCompletion I R →+* (R ⧸ I ^ n))))) where
  __ := (completionCoefficients σ I).toEquiv
  map_add' := (completionCoefficients σ I).map_add
  map_mul' := completionCoefficients_mul I
  commutes' := completionCoefficients_algebraMap I

/-- Each coefficient is completion of the original polynomial coefficient map,
after the canonical restriction-of-scalars comparison. -/
@[simp]
theorem coeff_adicCompletionEquiv (I : Ideal R)
    (x : AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
    (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d
        (@DFunLike.coe _
          (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R))
          (fun _ => ↥(MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* (R ⧸ I ^ n)))))
          (@AlgEquiv.instFunLike (AdicCompletion I R)
            (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R))
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* (R ⧸ I ^ n))))
            (CommRing.toCommSemiring (α := AdicCompletion I R))
            (CommRing.toCommSemiring
              (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                (MvPolynomial σ R))).toSemiring
            (Subalgebra.toSemiring
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* (R ⧸ I ^ n)))))
            (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
              Algebra (AdicCompletion I R)
                (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                  (MvPolynomial σ R)))
            (Subalgebra.algebra
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* (R ⧸ I ^ n))))))
          (adicCompletionEquiv σ I) x).val =
      AdicCompletion.map I (MvPolynomial.lcoeff R d)
        (AdicCompletion.restrictScalarsEquiv (S := MvPolynomial σ R) I (MvPolynomial σ R) x) :=
  completionCoefficients_coeff I x d

/-- The full raw reduction square, at every natural precision including zero. -/
@[simp]
theorem polynomialReduction_adicCompletionEquiv (I : Ideal R) (n : ℕ)
    (x : AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :
    MvPowerSeries.polynomialReduction σ
        (fun n => (AdicCompletion.evalₐ I n :
          AdicCompletion I R →+* (R ⧸ I ^ n))) n
        (@DFunLike.coe _
          (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R))
          (fun _ => ↥(MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* (R ⧸ I ^ n)))))
          (@AlgEquiv.instFunLike (AdicCompletion I R)
            (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R))
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* (R ⧸ I ^ n))))
            (CommRing.toCommSemiring (α := AdicCompletion I R))
            (CommRing.toCommSemiring
              (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                (MvPolynomial σ R))).toSemiring
            (Subalgebra.toSemiring
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* (R ⧸ I ^ n)))))
            (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
              Algebra (AdicCompletion I R)
                (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                  (MvPolynomial σ R)))
            (Subalgebra.algebra
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* (R ⧸ I ^ n))))))
          (adicCompletionEquiv σ I) x) =
      MvPowerSeries.adicPolynomialLevelEquiv I n (AdicCompletion.evalₐ _ n x) :=
  completionCoefficients_reduction I n x

/-- Evaluation of the inverse is the existing polynomial level equivalence in reverse. -/
@[simp]
theorem adicCompletionEquiv_symm_eval (I : Ideal R) (n : ℕ)
    (f : MvPowerSeries.polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n :
        AdicCompletion I R →+* (R ⧸ I ^ n)))) :
    AdicCompletion.evalₐ _ n
        (@DFunLike.coe _
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* (R ⧸ I ^ n))))
          (fun _ => (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R)))
          (@AlgEquiv.instFunLike (AdicCompletion I R)
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* (R ⧸ I ^ n))))
            (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R))
            (CommRing.toCommSemiring (α := AdicCompletion I R))
            (Subalgebra.toSemiring
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* (R ⧸ I ^ n)))))
            (CommRing.toCommSemiring
              (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                (MvPolynomial σ R))).toSemiring
            (Subalgebra.algebra
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* (R ⧸ I ^ n)))))
            (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
              Algebra (AdicCompletion I R)
                (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                  (MvPolynomial σ R))))
          (@AlgEquiv.symm (AdicCompletion I R)
            (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R))
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* (R ⧸ I ^ n))))
            (CommRing.toCommSemiring (α := AdicCompletion I R))
            (CommRing.toCommSemiring
              (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                (MvPolynomial σ R))).toSemiring
            (Subalgebra.toSemiring
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* (R ⧸ I ^ n)))))
            (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
              Algebra (AdicCompletion I R)
                (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                  (MvPolynomial σ R)))
            (Subalgebra.algebra
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* (R ⧸ I ^ n)))))
            (adicCompletionEquiv σ I)) f) =
      (MvPowerSeries.adicPolynomialLevelEquiv I n).symm
        (MvPowerSeries.polynomialReduction σ
          (fun n => (AdicCompletion.evalₐ I n :
            AdicCompletion I R →+* (R ⧸ I ^ n))) n f) := by
  let _ : Algebra (AdicCompletion I R)
      (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R)) :=
    AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I
  apply (MvPowerSeries.adicPolynomialLevelEquiv I n).injective
  exact (polynomialReduction_adicCompletionEquiv I n
    ((adicCompletionEquiv σ I).symm.toEquiv f)).symm.trans
      ((congrArg (MvPowerSeries.polynomialReduction σ
        (fun n => (AdicCompletion.evalₐ I n :
          AdicCompletion I R →+* (R ⧸ I ^ n))) n)
        ((adicCompletionEquiv σ I).apply_symm_apply f)).trans
          ((MvPowerSeries.adicPolynomialLevelEquiv I n).apply_symm_apply _).symm)

/-- Completed coefficient projections of the inverse are the given series coefficients. -/
@[simp]
theorem adicCompletionEquiv_symm_coeff (I : Ideal R)
    (f : MvPowerSeries.polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n :
        AdicCompletion I R →+* (R ⧸ I ^ n)))) (d : σ →₀ ℕ) :
    AdicCompletion.map I (MvPolynomial.lcoeff R d)
        (@DFunLike.coe
          (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R) ≃ₗ[R] AdicCompletion I (MvPolynomial σ R))
          (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R))
          (fun _ => AdicCompletion I (MvPolynomial σ R))
          EquivLike.toFunLike
          (AdicCompletion.restrictScalarsEquiv (S := MvPolynomial σ R) I (MvPolynomial σ R))
          (@DFunLike.coe _
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* (R ⧸ I ^ n))))
            (fun _ => (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R)))
            (@AlgEquiv.instFunLike (AdicCompletion I R)
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* (R ⧸ I ^ n))))
              (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                (MvPolynomial σ R))
              (CommRing.toCommSemiring (α := AdicCompletion I R))
              (Subalgebra.toSemiring
                (MvPowerSeries.polynomialReductionSubalgebra σ
                  (fun n => (AdicCompletion.evalₐ I n :
                    AdicCompletion I R →+* (R ⧸ I ^ n)))))
              (CommRing.toCommSemiring
                (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                  (MvPolynomial σ R))).toSemiring
              (Subalgebra.algebra
                (MvPowerSeries.polynomialReductionSubalgebra σ
                  (fun n => (AdicCompletion.evalₐ I n :
                    AdicCompletion I R →+* (R ⧸ I ^ n)))))
              (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
                Algebra (AdicCompletion I R)
                  (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                    (MvPolynomial σ R))))
            (@AlgEquiv.symm (AdicCompletion I R)
              (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                (MvPolynomial σ R))
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* (R ⧸ I ^ n))))
              (CommRing.toCommSemiring (α := AdicCompletion I R))
              (CommRing.toCommSemiring
                (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                  (MvPolynomial σ R))).toSemiring
              (Subalgebra.toSemiring
                (MvPowerSeries.polynomialReductionSubalgebra σ
                  (fun n => (AdicCompletion.evalₐ I n :
                    AdicCompletion I R →+* (R ⧸ I ^ n)))))
              (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
                Algebra (AdicCompletion I R)
                  (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                    (MvPolynomial σ R)))
              (Subalgebra.algebra
                (MvPowerSeries.polynomialReductionSubalgebra σ
                  (fun n => (AdicCompletion.evalₐ I n :
                    AdicCompletion I R →+* (R ⧸ I ^ n)))))
              (adicCompletionEquiv σ I)) f)) = MvPowerSeries.coeff d f.val := by
  let _ : Algebra (AdicCompletion I R)
      (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R)) :=
    AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I
  exact (coeff_adicCompletionEquiv I
    ((adicCompletionEquiv σ I).symm.toEquiv f) d).symm.trans
    (congrArg (fun g : polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n :
        AdicCompletion I R →+* (R ⧸ I ^ n))) => MvPowerSeries.coeff d g.val)
          ((adicCompletionEquiv σ I).apply_symm_apply f))

/-- Original polynomial representatives give the usual coefficientwise inclusion
into power series over the completed coefficient ring. -/
@[simp]
theorem adicCompletionEquiv_of (I : Ideal R) (p : MvPolynomial σ R) :
    (@DFunLike.coe _
      (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R))
      (fun _ => ↥(MvPowerSeries.polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n :
          AdicCompletion I R →+* (R ⧸ I ^ n)))))
      (@AlgEquiv.instFunLike (AdicCompletion I R)
        (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
          (MvPolynomial σ R))
        (MvPowerSeries.polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n :
            AdicCompletion I R →+* (R ⧸ I ^ n))))
        (CommRing.toCommSemiring (α := AdicCompletion I R))
        (CommRing.toCommSemiring
          (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R))).toSemiring
        (Subalgebra.toSemiring
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* (R ⧸ I ^ n)))))
        (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
          Algebra (AdicCompletion I R)
            (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R)))
        (Subalgebra.algebra
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* (R ⧸ I ^ n))))))
      (adicCompletionEquiv σ I)
      (AdicCompletion.of (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R) p)).val =
        (MvPolynomial.map (algebraMap R (AdicCompletion I R)) p :
          MvPowerSeries σ (AdicCompletion I R)) := by
  apply MvPowerSeries.ext
  intro d
  have hrestrict : AdicCompletion.restrictScalarsEquiv (S := MvPolynomial σ R) I
      (MvPolynomial σ R) (AdicCompletion.of (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R) p) = AdicCompletion.of I (MvPolynomial σ R) p :=
    AdicCompletion.restrictScalarsEquiv_of (S := MvPolynomial σ R) I p
  have hcoeff := congrArg (fun y : AdicCompletion I (MvPolynomial σ R) =>
    AdicCompletion.map I (MvPolynomial.lcoeff R d) y) hrestrict
  have hpolynomial : AdicCompletion.of I R (p.coeff d) =
      MvPowerSeries.coeff d
        (MvPolynomial.map (algebraMap R (AdicCompletion I R)) p :
          MvPowerSeries σ (AdicCompletion I R)) := by
    rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_map]
    rfl
  exact (coeff_adicCompletionEquiv I
    (AdicCompletion.of (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
      (MvPolynomial σ R) p) d).trans
        (hcoeff.trans ((AdicCompletion.map_of I (MvPolynomial.lcoeff R d) p).trans
          hpolynomial))

/-- The inverse on polynomials over the completed coefficient ring is the stock
polynomial evaluation at the completed original variables. -/
theorem adicCompletionEquiv_symm_polynomial (I : Ideal R)
    (p : MvPolynomial σ (AdicCompletion I R)) :
    @DFunLike.coe _
      (MvPowerSeries.polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n :
          AdicCompletion I R →+* (R ⧸ I ^ n))))
      (fun _ => (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R)))
      (@AlgEquiv.instFunLike (AdicCompletion I R)
        (MvPowerSeries.polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n :
            AdicCompletion I R →+* (R ⧸ I ^ n))))
        (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
          (MvPolynomial σ R))
        (CommRing.toCommSemiring (α := AdicCompletion I R))
        (Subalgebra.toSemiring
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* (R ⧸ I ^ n)))))
        (CommRing.toCommSemiring
          (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R))).toSemiring
        (Subalgebra.algebra
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* (R ⧸ I ^ n)))))
        (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
          Algebra (AdicCompletion I R)
            (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R))))
        (@AlgEquiv.symm (AdicCompletion I R)
          (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R))
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* (R ⧸ I ^ n))))
          (CommRing.toCommSemiring (α := AdicCompletion I R))
          (CommRing.toCommSemiring
            (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R))).toSemiring
          (Subalgebra.toSemiring
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* (R ⧸ I ^ n)))))
          (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
            Algebra (AdicCompletion I R)
              (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                (MvPolynomial σ R)))
          (Subalgebra.algebra
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* (R ⧸ I ^ n)))))
          (adicCompletionEquiv σ I))
        (MvPowerSeries.polynomialToReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n :
            AdicCompletion I R →+* (R ⧸ I ^ n))) p) =
      @DFunLike.coe _
        (MvPolynomial σ (AdicCompletion I R))
        (fun _ => (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
          (MvPolynomial σ R)))
        (@AlgHom.funLike (AdicCompletion I R)
          (MvPolynomial σ (AdicCompletion I R))
          (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R))
          (CommRing.toCommSemiring (α := AdicCompletion I R))
          (AddMonoidAlgebra.semiring (R := AdicCompletion I R) (M := σ →₀ ℕ))
          (CommRing.toCommSemiring
            (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R))).toSemiring
          (AddMonoidAlgebra.algebra (R := AdicCompletion I R)
            (A := AdicCompletion I R) (M := σ →₀ ℕ))
          (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
            Algebra (AdicCompletion I R)
              (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                (MvPolynomial σ R))))
        (@MvPolynomial.aeval (R := AdicCompletion I R)
          (S₁ := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R)) (σ := σ)
          (CommRing.toCommSemiring (α := AdicCompletion I R))
          (CommRing.toCommSemiring
            (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R)))
          (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
            Algebra (AdicCompletion I R)
              (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
                (MvPolynomial σ R)))
          (fun i : σ =>
            AdicCompletion.of (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R) (MvPolynomial.X i))) p := by
  let _ : Algebra (AdicCompletion I R)
      (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R)) :=
    AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I
  let e : AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
      (MvPolynomial σ R) ≃ MvPowerSeries.polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n :
          AdicCompletion I R →+* (R ⧸ I ^ n))) :=
    (adicCompletionEquiv σ I).toEquiv
  have h : (adicCompletionEquiv σ I).toAlgHom.comp
      (MvPolynomial.aeval (fun i : σ =>
        AdicCompletion.of (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
          (MvPolynomial σ R) (MvPolynomial.X i))) =
      MvPowerSeries.polynomialToReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n :
          AdicCompletion I R →+* (R ⧸ I ^ n))) := by
    exact MvPolynomial.algHom_ext fun i => Subtype.ext
      ((congrArg (fun x : AdicCompletion
          (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R) =>
            (e x).val)
        (MvPolynomial.aeval_X (R := AdicCompletion I R) (fun j : σ =>
          AdicCompletion.of (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R) (MvPolynomial.X j)) i)).trans
        ((adicCompletionEquiv_of I (MvPolynomial.X i)).trans
          ((congrArg (fun q : MvPolynomial σ (AdicCompletion I R) =>
              (q : MvPowerSeries σ (AdicCompletion I R)))
            (MvPolynomial.map_X (algebraMap R (AdicCompletion I R)) i)).trans
              (MvPowerSeries.polynomialToReductionSubalgebra_coe σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* (R ⧸ I ^ n))) (MvPolynomial.X i)).symm)))
  exact e.symm_apply_eq.mpr (AlgHom.congr_fun h p).symm

/-- The completed original coefficient map becomes the stock power-series constant map. -/
theorem adicCompletionEquiv_algebraMap (I : Ideal R) (a : AdicCompletion I R) :
    (@DFunLike.coe _
      (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R))
      (fun _ => ↥(MvPowerSeries.polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n :
          AdicCompletion I R →+* (R ⧸ I ^ n)))))
      (@AlgEquiv.instFunLike (AdicCompletion I R)
        (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
          (MvPolynomial σ R))
        (MvPowerSeries.polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n :
            AdicCompletion I R →+* (R ⧸ I ^ n))))
        (CommRing.toCommSemiring (α := AdicCompletion I R))
        (CommRing.toCommSemiring
          (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R))).toSemiring
        (Subalgebra.toSemiring
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* (R ⧸ I ^ n)))))
        (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
          Algebra (AdicCompletion I R)
            (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R)))
        (Subalgebra.algebra
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* (R ⧸ I ^ n))))))
      (adicCompletionEquiv σ I)
      (@algebraMap (AdicCompletion I R)
        (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
          (MvPolynomial σ R))
        (CommRing.toCommSemiring (α := AdicCompletion I R))
        (CommRing.toCommSemiring
          (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R))).toSemiring
        (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
          Algebra (AdicCompletion I R)
            (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R))) a)).val =
      MvPowerSeries.C (σ := σ) a := by
  let _ : Algebra (AdicCompletion I R)
      (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R)) :=
    AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I
  exact (congrArg Subtype.val ((adicCompletionEquiv σ I).commutes a)).trans
    (MvPowerSeries.polynomialReductionSubalgebra.coe_algebraMap σ
      (fun n => (AdicCompletion.evalₐ I n :
        AdicCompletion I R →+* (R ⧸ I ^ n))) a)

end MvPolynomial

end CompletedCoefficients

namespace MvPowerSeries

section CompleteCoefficients

attribute [local instance] AdicCompletion.extendedAlgebra

variable {R : Type u} [CommRing R] {σ : Type v}

private noncomputable def completeCoefficientEquiv (I : Ideal R) [IsAdicComplete I R] :
    adicallyRestrictedSubring (σ := σ) I ≃+*
      polynomialReductionSubalgebra σ (fun n => (AdicCompletion.evalₐ I n).toRingHom) where
  toFun f := ⟨map (AdicCompletion.ofAlgEquiv I : R →+* AdicCompletion I R) f.val, by
    apply (mem_polynomialReductionSubalgebra_iff_finite_support σ _ _).2
    intro n
    simpa only [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AdicCompletion.ofAlgEquiv_apply, AdicCompletion.evalₐ_of,
      ne_eq, Ideal.Quotient.eq_zero_iff_mem] using
      (mem_adicallyRestrictedSubring I f.val).1 f.property n⟩
  invFun f := ⟨map ((AdicCompletion.ofAlgEquiv I).symm : AdicCompletion I R →+* R) f.val, by
    apply (mem_adicallyRestrictedSubring I _).2
    intro n
    simpa only [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      ← Ideal.Quotient.eq_zero_iff_mem, AdicCompletion.mk_ofAlgEquiv_symm] using
      (mem_polynomialReductionSubalgebra_iff_finite_support σ _ _).1 f.property n⟩
  left_inv f := by
    apply Subtype.ext
    apply MvPowerSeries.ext
    intro d
    change (AdicCompletion.ofAlgEquiv I).symm
      (AdicCompletion.ofAlgEquiv I (coeff d f.val)) = coeff d f.val
    exact (AdicCompletion.ofAlgEquiv I).symm_apply_apply _
  right_inv f := by
    apply Subtype.ext
    apply MvPowerSeries.ext
    intro d
    change AdicCompletion.ofAlgEquiv I
      ((AdicCompletion.ofAlgEquiv I).symm (coeff d f.val)) = coeff d f.val
    exact (AdicCompletion.ofAlgEquiv I).apply_symm_apply _
  map_add' f g := Subtype.ext (map_add _ _ _)
  map_mul' f g := Subtype.ext (map_mul _ _ _)

private theorem completeCoefficientEquiv_reduction (I : Ideal R) [IsAdicComplete I R]
    (n : ℕ) (f : adicallyRestrictedSubring (σ := σ) I) :
    polynomialReduction σ (fun n => (AdicCompletion.evalₐ I n).toRingHom) n
        (completeCoefficientEquiv I f) = adicReduction I n f := by
  apply MvPolynomial.ext
  intro d
  rw [coeff_polynomialReduction, coeff_adicReduction]
  change AdicCompletion.evalₐ I n
    (AdicCompletion.ofAlgEquiv I (coeff d f.val)) = _
  rw [AdicCompletion.ofAlgEquiv_apply, AdicCompletion.evalₐ_of]

/-- For complete original coefficients, coefficient transport followed by the inverse
of `MvPolynomial.adicCompletionEquiv` identifies restricted series with polynomial
completion. Both directions use the same completion-of-direct-sums comparison. -/
noncomputable def adicallyRestrictedEquivAdicCompletion (I : Ideal R)
    [IsAdicComplete I R] :
    adicallyRestrictedSubring (σ := σ) I ≃+*
      AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R) :=
  (completeCoefficientEquiv I).trans
    (@AlgEquiv.toRingEquiv (AdicCompletion I R)
      (MvPowerSeries.polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n :
          AdicCompletion I R →+* (R ⧸ I ^ n))))
      (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R))
      (CommRing.toCommSemiring (α := AdicCompletion I R))
      (Subalgebra.toSemiring
        (MvPowerSeries.polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n :
            AdicCompletion I R →+* (R ⧸ I ^ n)))))
      (CommRing.toCommSemiring
        (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
          (MvPolynomial σ R))).toSemiring
      (Subalgebra.algebra
        (MvPowerSeries.polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n :
            AdicCompletion I R →+* (R ⧸ I ^ n)))))
      (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
        Algebra (AdicCompletion I R)
          (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R)))
      (@AlgEquiv.symm (AdicCompletion I R)
        (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
          (MvPolynomial σ R))
        (MvPowerSeries.polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n :
            AdicCompletion I R →+* (R ⧸ I ^ n))))
        (CommRing.toCommSemiring (α := AdicCompletion I R))
        (CommRing.toCommSemiring
          (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R))).toSemiring
        (Subalgebra.toSemiring
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* (R ⧸ I ^ n)))))
        (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
          Algebra (AdicCompletion I R)
            (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R)))
        (Subalgebra.algebra
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* (R ⧸ I ^ n)))))
        (MvPolynomial.adicCompletionEquiv σ I)))

/-- The original complete-coefficient comparison agrees with the completed-coefficient
algebra equivalence after coefficientwise application of `ofAlgEquiv`. -/
theorem adicCompletionEquiv_adicallyRestrictedEquivAdicCompletion
    (I : Ideal R) [IsAdicComplete I R] (f : adicallyRestrictedSubring (σ := σ) I) :
    (@DFunLike.coe _
      (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R))
      (fun _ => ↥(MvPowerSeries.polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n :
          AdicCompletion I R →+* (R ⧸ I ^ n)))))
      (@AlgEquiv.instFunLike (AdicCompletion I R)
        (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
          (MvPolynomial σ R))
        (MvPowerSeries.polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n :
            AdicCompletion I R →+* (R ⧸ I ^ n))))
        (CommRing.toCommSemiring (α := AdicCompletion I R))
        (CommRing.toCommSemiring
          (α := AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
            (MvPolynomial σ R))).toSemiring
        (Subalgebra.toSemiring
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* (R ⧸ I ^ n)))))
        (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
          Algebra (AdicCompletion I R)
            (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R)))
        (Subalgebra.algebra
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* (R ⧸ I ^ n))))))
      (MvPolynomial.adicCompletionEquiv σ I) (adicallyRestrictedEquivAdicCompletion I f)).val =
      map (AdicCompletion.ofAlgEquiv I : R →+* AdicCompletion I R) f.val := by
  let _ : Algebra (AdicCompletion I R)
      (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R)) :=
    AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I
  exact congrArg Subtype.val
    ((MvPolynomial.adicCompletionEquiv σ I).toEquiv.apply_symm_apply
      (completeCoefficientEquiv I f))

/-- Forward evaluation is exactly the original restricted polynomial reduction. -/
@[simp]
theorem adicallyRestrictedEquivAdicCompletion_eval (I : Ideal R) [IsAdicComplete I R]
    (n : ℕ) (f : adicallyRestrictedSubring (σ := σ) I) :
    adicPolynomialLevelEquiv (σ := σ) I n
      (AdicCompletion.evalₐ _ n (adicallyRestrictedEquivAdicCompletion I f)) =
        adicReduction I n f := by
  let _ : Algebra (AdicCompletion I R)
      (AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R)) :=
    AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I
  calc
    _ = polynomialReduction σ (fun n => (AdicCompletion.evalₐ I n).toRingHom) n
        ((MvPolynomial.adicCompletionEquiv σ I).toEquiv
          (adicallyRestrictedEquivAdicCompletion I f)) :=
      (MvPolynomial.polynomialReduction_adicCompletionEquiv I n
        (adicallyRestrictedEquivAdicCompletion I f)).symm
    _ = adicReduction I n f :=
      (congrArg (polynomialReduction σ (fun n => (AdicCompletion.evalₐ I n).toRingHom) n)
        ((MvPolynomial.adicCompletionEquiv σ I).toEquiv.apply_symm_apply
          (completeCoefficientEquiv I f))).trans
            (completeCoefficientEquiv_reduction I n f)

/-- Inverse evaluation retrieves each finite reduction of a completion element. -/
@[simp]
theorem adicallyRestrictedEquivAdicCompletion_symm_eval (I : Ideal R)
    [IsAdicComplete I R] (n : ℕ)
    (x : AdicCompletion
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :
    adicReduction I n ((adicallyRestrictedEquivAdicCompletion I).symm x) =
      adicPolynomialLevelEquiv (σ := σ) I n (AdicCompletion.evalₐ _ n x) := by
  rw [← adicallyRestrictedEquivAdicCompletion_eval I n
    ((adicallyRestrictedEquivAdicCompletion I).symm x), RingEquiv.apply_symm_apply]

/-- Polynomial representatives agree with the completion map. -/
@[simp]
theorem adicallyRestrictedEquivAdicCompletion_polynomial (I : Ideal R)
    [IsAdicComplete I R] (p : MvPolynomial σ R) :
    adicallyRestrictedEquivAdicCompletion I (polynomialToRestricted I p) =
      AdicCompletion.of (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R) p := by
  apply AdicCompletion.ext_evalₐ
  intro n
  apply (adicPolynomialLevelEquiv (σ := σ) I n).injective
  rw [adicallyRestrictedEquivAdicCompletion_eval, adicReduction_polynomial,
    AdicCompletion.evalₐ_of, adicPolynomialLevelEquiv_mk]

end CompleteCoefficients

end MvPowerSeries
