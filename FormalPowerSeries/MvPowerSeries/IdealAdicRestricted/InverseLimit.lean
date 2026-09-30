module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.AdicCompletion.Algebra

public section

/-!
# Ideal-adically restricted series and the polynomial completion

For a complete coefficient ring, reduction of restricted series at every ideal power
identifies their ring with the native completion of the multivariate polynomial ring
at the coefficient ideal. The variable type and the ideal need not be finite.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

/-- The native polynomial/quotient equivalence, transported across `Ideal.map_pow`. -/
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

/-- The existing finite reductions commute with actual quotient-power transitions. -/
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

private theorem adicEval_factorPow (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  obtain ⟨representative, hrepresentative⟩ := Ideal.Quotient.mk_surjective (x.val n)
  have hm : x.val m = Ideal.Quotient.mk (I ^ m • ⊤ : Ideal R) representative := by
    rw [← x.property hmn, ← hrepresentative]
    rfl
  have hn : AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) representative := by
    rw [← AdicCompletion.factor_eval_eq_evalₐ I x (le_of_eq (Ideal.mul_top _))]
    rw [AdicCompletion.eval_apply, ← hrepresentative]
    rfl
  have hmk : AdicCompletion.evalₐ I m x = Ideal.Quotient.mk (I ^ m) representative := by
    rw [← AdicCompletion.factor_eval_eq_evalₐ I x (le_of_eq (Ideal.mul_top _))]
    rw [AdicCompletion.eval_apply, hm]
    rfl
  rw [hn, hmk, Ideal.Quotient.factor_mk]

private theorem adicCompletionLevel_factorPow (I : Ideal R) {m n : ℕ}
    (hmn : m ≤ n)
    (x : AdicCompletion
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :
    MvPolynomial.map (Ideal.Quotient.factorPow I hmn)
        (adicPolynomialLevelEquiv (σ := σ) I n
          (AdicCompletion.evalₐ _ n x)) =
      adicPolynomialLevelEquiv (σ := σ) I m
        (AdicCompletion.evalₐ _ m x) := by
  rw [← adicPolynomialLevelEquiv_factorPow I hmn,
    adicEval_factorPow]

private noncomputable def coefficientCompletion (I : Ideal R)
    (x : AdicCompletion
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
    (index : σ →₀ ℕ) : AdicCompletion I R :=
  ⟨(fun n => (Ideal.quotientEquivAlgOfEq R (Ideal.mul_top (I ^ n)).symm)
      ((adicPolynomialLevelEquiv (σ := σ) I n
        (AdicCompletion.evalₐ _ n x)).coeff index)), by
    intro m n hmn
    have hcompat : Ideal.Quotient.factorPow I hmn
        ((adicPolynomialLevelEquiv (σ := σ) I n
          (AdicCompletion.evalₐ _ n x)).coeff index) =
        (adicPolynomialLevelEquiv (σ := σ) I m
          (AdicCompletion.evalₐ _ m x)).coeff index := by
      simpa only [MvPolynomial.coeff_map] using
        congrArg (fun p : MvPolynomial σ (R ⧸ I ^ m) => p.coeff index)
          (adicCompletionLevel_factorPow I hmn x)
    obtain ⟨representative, hr⟩ := Ideal.Quotient.mk_surjective
      ((adicPolynomialLevelEquiv (σ := σ) I n
        (AdicCompletion.evalₐ _ n x)).coeff index)
    have hn := hr.symm
    have hm : (adicPolynomialLevelEquiv (σ := σ) I m
        (AdicCompletion.evalₐ _ m x)).coeff index =
        Ideal.Quotient.mk (I ^ m) representative := by
      rw [← hcompat, hn, Ideal.Quotient.factor_mk]
    simp only [hn, hm, Ideal.quotientEquivAlgOfEq_mk]
    rfl⟩

private theorem coefficientCompletion_eval (I : Ideal R)
    (x : AdicCompletion
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
    (index : σ →₀ ℕ) (n : ℕ) :
    AdicCompletion.evalₐ I n (coefficientCompletion I x index) =
      (adicPolynomialLevelEquiv (σ := σ) I n
        (AdicCompletion.evalₐ _ n x)).coeff index := by
  change (Ideal.quotientEquivAlgOfEq R (Ideal.mul_top (I ^ n)))
    ((Ideal.quotientEquivAlgOfEq R (Ideal.mul_top (I ^ n)).symm)
      ((adicPolynomialLevelEquiv (σ := σ) I n
        (AdicCompletion.evalₐ _ n x)).coeff index)) = _
  exact AlgEquiv.apply_symm_apply _ _

private noncomputable def coefficientLift (I : Ideal R) [IsAdicComplete I R]
    (x : AdicCompletion
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
    (index : σ →₀ ℕ) : R :=
  (AdicCompletion.ofAlgEquiv I).symm (coefficientCompletion I x index)

private theorem coefficientLift_mk (I : Ideal R) [IsAdicComplete I R]
    (x : AdicCompletion
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
    (index : σ →₀ ℕ) (n : ℕ) :
    Ideal.Quotient.mk (I ^ n) (coefficientLift I x index) =
      (adicPolynomialLevelEquiv (σ := σ) I n
        (AdicCompletion.evalₐ _ n x)).coeff index := by
  exact (AdicCompletion.mk_ofAlgEquiv_symm I n _).trans
    (coefficientCompletion_eval I x index n)

private noncomputable def restrictedOfCompletion (I : Ideal R) [IsAdicComplete I R]
    (x : AdicCompletion
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :
    adicallyRestrictedSubring (σ := σ) I :=
  ⟨(fun index => coefficientLift I x index), by
    apply (mem_adicallyRestrictedSubring (σ := σ) I _).2
    intro n
    have hsupport :
        {index : σ →₀ ℕ | coefficientLift I x index ∉ I ^ n} =
          ((adicPolynomialLevelEquiv (σ := σ) I n
            (AdicCompletion.evalₐ _ n x)).support : Set (σ →₀ ℕ)) := by
      ext index
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, MvPolynomial.mem_support_iff,
        ← coefficientLift_mk I x index n, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    change {index : σ →₀ ℕ | coefficientLift I x index ∉ I ^ n}.Finite
    rw [hsupport]
    exact Finset.finite_toSet _⟩

/-- Reconstruction has the prescribed finite polynomial at every level. -/
private theorem adicReduction_restrictedOfCompletion (I : Ideal R) [IsAdicComplete I R]
    (n : ℕ)
    (x : AdicCompletion
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :
    adicReduction I n (restrictedOfCompletion I x) =
      adicPolynomialLevelEquiv (σ := σ) I n (AdicCompletion.evalₐ _ n x) := by
  ext index
  rw [coeff_adicReduction]
  change Ideal.Quotient.mk (I ^ n) (coefficientLift I x index) = _
  exact coefficientLift_mk I x index n

private theorem adicRestrictedForward_compat (I : Ideal R) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow
        (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) hmn).comp
        ((adicPolynomialLevelEquiv (σ := σ) I n).symm.toRingHom.comp
          (adicReduction I n)) =
        (adicPolynomialLevelEquiv (σ := σ) I m).symm.toRingHom.comp
          (adicReduction I m) := by
  intro m n hmn
  ext f
  apply (adicPolynomialLevelEquiv (σ := σ) I m).injective
  change adicPolynomialLevelEquiv (σ := σ) I m
      (Ideal.Quotient.factorPow _ hmn
        ((adicPolynomialLevelEquiv (σ := σ) I n).symm (adicReduction I n f))) =
    adicPolynomialLevelEquiv (σ := σ) I m
      ((adicPolynomialLevelEquiv (σ := σ) I m).symm (adicReduction I m f))
  rw [RingEquiv.apply_symm_apply]
  rw [adicPolynomialLevelEquiv_factorPow, RingEquiv.apply_symm_apply,
    adicReduction_factorPow]

private noncomputable def adicRestrictedForward (I : Ideal R) :
    adicallyRestrictedSubring (σ := σ) I →+*
      AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R) :=
  AdicCompletion.liftRingHom
    (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
    (fun n => (adicPolynomialLevelEquiv (σ := σ) I n).symm.toRingHom.comp
      (adicReduction I n)) (adicRestrictedForward_compat I)

private theorem adicRestrictedForward_eval (I : Ideal R) (n : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    adicPolynomialLevelEquiv (σ := σ) I n
      (AdicCompletion.evalₐ _ n (adicRestrictedForward I f)) = adicReduction I n f := by
  unfold adicRestrictedForward
  rw [AdicCompletion.evalₐ_liftRingHom
    (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
    (fun n => (adicPolynomialLevelEquiv (σ := σ) I n).symm.toRingHom.comp
      (adicReduction I n)) (adicRestrictedForward_compat I) n f]
  change adicPolynomialLevelEquiv (σ := σ) I n
    ((adicPolynomialLevelEquiv (σ := σ) I n).symm (adicReduction I n f)) = _
  exact RingEquiv.apply_symm_apply _ _

private theorem adicReduction_jointly_injective (I : Ideal R) [IsHausdorff I R]
    {f g : adicallyRestrictedSubring (σ := σ) I}
    (h : ∀ n, adicReduction I n f = adicReduction I n g) : f = g := by
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro index
  have heq := IsHausdorff.funext' I
    (f := fun index : σ →₀ ℕ => coeff index (f : MvPowerSeries σ R))
    (g := fun index : σ →₀ ℕ => coeff index (g : MvPowerSeries σ R))
    (by
      intro n index
      simpa only [coeff_adicReduction] using
        congrArg (fun p : MvPolynomial σ (R ⧸ I ^ n) => p.coeff index) (h n))
  exact congrFun heq index

private theorem adicRestrictedForward_injective (I : Ideal R) [IsAdicComplete I R] :
    Function.Injective (adicRestrictedForward (σ := σ) I) := by
  intro f g hfg
  apply adicReduction_jointly_injective I
  intro n
  calc
    adicReduction I n f = adicPolynomialLevelEquiv (σ := σ) I n
        (AdicCompletion.evalₐ _ n (adicRestrictedForward I f)) :=
      (adicRestrictedForward_eval I n f).symm
    _ = adicPolynomialLevelEquiv (σ := σ) I n
        (AdicCompletion.evalₐ _ n (adicRestrictedForward I g)) := by rw [hfg]
    _ = adicReduction I n g := adicRestrictedForward_eval I n g

private theorem adicRestrictedForward_surjective (I : Ideal R) [IsAdicComplete I R] :
    Function.Surjective (adicRestrictedForward (σ := σ) I) := by
  intro x
  refine ⟨restrictedOfCompletion I x, ?_⟩
  apply AdicCompletion.ext_evalₐ
  intro n
  apply (adicPolynomialLevelEquiv (σ := σ) I n).injective
  rw [adicRestrictedForward_eval, adicReduction_restrictedOfCompletion]

/-- The canonical ring equivalence characterized by its finite polynomial reductions. -/
noncomputable def adicallyRestrictedEquivAdicCompletion (I : Ideal R)
    [IsAdicComplete I R] :
    adicallyRestrictedSubring (σ := σ) I ≃+*
      AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R) :=
  RingEquiv.ofBijective (adicRestrictedForward I)
    ⟨adicRestrictedForward_injective I, adicRestrictedForward_surjective I⟩

/-- Forward evaluation is exactly the original restricted polynomial reduction. -/
@[simp]
theorem adicallyRestrictedEquivAdicCompletion_eval (I : Ideal R) [IsAdicComplete I R]
    (n : ℕ) (f : adicallyRestrictedSubring (σ := σ) I) :
    adicPolynomialLevelEquiv (σ := σ) I n
      (AdicCompletion.evalₐ _ n (adicallyRestrictedEquivAdicCompletion I f)) =
        adicReduction I n f := by
  change adicPolynomialLevelEquiv (σ := σ) I n
    (AdicCompletion.evalₐ _ n (adicRestrictedForward I f)) = adicReduction I n f
  exact adicRestrictedForward_eval I n f

/-- Inverse evaluation retrieves each finite reduction of a native completion element. -/
@[simp]
theorem adicallyRestrictedEquivAdicCompletion_symm_eval (I : Ideal R)
    [IsAdicComplete I R] (n : ℕ)
    (x : AdicCompletion
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :
    adicReduction I n ((adicallyRestrictedEquivAdicCompletion I).symm x) =
      adicPolynomialLevelEquiv (σ := σ) I n (AdicCompletion.evalₐ _ n x) := by
  rw [← adicallyRestrictedEquivAdicCompletion_eval I n
    ((adicallyRestrictedEquivAdicCompletion I).symm x),
    RingEquiv.apply_symm_apply]

/-- Native polynomial representatives agree with the native completion map. -/
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

end MvPowerSeries
