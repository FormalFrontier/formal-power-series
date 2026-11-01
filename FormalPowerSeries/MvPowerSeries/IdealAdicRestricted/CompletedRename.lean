/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.InverseLimit
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Arbitrary variable maps on restricted series over completed coefficients

An arbitrary map of variables induces an algebra homomorphism on the series whose
raw reductions are polynomial. At each original ideal-power precision it is
polynomial renaming. Its coefficients are finite sums over the support of that
source reduction, even when a variable has infinitely many preimages.

The construction completes the finite direct-sum pushforward and uses the whole
`AdicCompletion.dfinsuppEquiv` in both variable types. It does not use the
polynomial-completion algebra equivalence or an ambient power-series renaming.
All coefficient algebras and completion actions are the existing ones. No finite
generation, completeness, separation or finite-fiber assumption is needed.

## References

The construction uses Mathlib's dependent direct sums, adic completion functor
and polynomial renaming, together with Adic Modules' quotient/direct-sum and
completion/restricted-product equivalences.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe uR uσ uτ uυ uS uM

namespace MvPowerSeries

variable {R : Type uR} [CommRing R]
  {σ : Type uσ} {τ : Type uτ} {υ : Type uυ}

open Classical in
/-- The finite direct-sum pushforward on monomial indices. -/
private def monomialPushforward {S : Type uS} [Semiring S]
    (M : Type uM) [AddCommMonoid M] [Module S M] (g : σ → τ) :
    (Π₀ (_ : σ →₀ ℕ), M) →ₗ[S] Π₀ (_ : τ →₀ ℕ), M :=
  DFinsupp.lsum ℕ (fun d : σ →₀ ℕ =>
    DFinsupp.lsingle (R := S) (M := fun _ : τ →₀ ℕ => M) (Finsupp.mapDomain g d))

open Classical in
private theorem monomialPushforward_single {S : Type uS} [Semiring S]
    (M : Type uM) [AddCommMonoid M] [Module S M] (g : σ → τ)
    (d : σ →₀ ℕ) (r : M) :
    monomialPushforward (S := S) M g (DFinsupp.single d r) =
      DFinsupp.single (Finsupp.mapDomain g d) r := by
  rw [monomialPushforward, DFinsupp.lsum_single, DFinsupp.lsingle_apply]

open Classical in
private theorem monomialPushforward_apply {S : Type uS} [Semiring S]
    (M : Type uM) [AddCommMonoid M] [Module S M] (g : σ → τ)
    (v : Π₀ (_ : σ →₀ ℕ), M) (b : τ →₀ ℕ) :
    monomialPushforward (S := S) M g v b =
      ∑ d ∈ v.support.filter (fun d => Finsupp.mapDomain g d = b), v d := by
  rw [monomialPushforward, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
    DFinsupp.sum_apply]
  simp only [LinearMap.toAddMonoidHom_coe, DFinsupp.lsingle_apply, DFinsupp.sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : Finsupp.mapDomain g d = b
  · subst b
    rw [DFinsupp.single_eq_same, ite_eq_left rfl]
  · rw [DFinsupp.single_eq_of_ne (Ne.symm h), ite_eq_right h]

private theorem quotientDFinsupp_monomialPushforward (I : Ideal R) (g : σ → τ) (n : ℕ)
    (z : (Π₀ (_ : σ →₀ ℕ), R) ⧸
      (I ^ n • (⊤ : Submodule R (Π₀ (_ : σ →₀ ℕ), R)))) :
    Ideal.quotientDFinsupp (I ^ n) (fun _ : τ →₀ ℕ => R)
        ((monomialPushforward (S := R) R g).reduceModIdeal (I ^ n) z) =
      monomialPushforward (S := R ⧸ I ^ n)
        (R ⧸ (I ^ n • (⊤ : Submodule R R))) g
        (Ideal.quotientDFinsupp (I ^ n) (fun _ : σ →₀ ℕ => R) z) := by
  classical
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.reduceModIdeal_apply, Ideal.quotientDFinsupp_mk,
    Ideal.quotientDFinsupp_mk]
  induction m using DFinsupp.induction with
  | h0 => simp only [map_zero]
  | ha d r m _ _ ih =>
    have hs :
        DFinsupp.mapRange.linearMap (R := R)
            (fun _ : τ →₀ ℕ => (I ^ n • (⊤ : Submodule R R)).mkQ)
            (monomialPushforward (S := R) R g (DFinsupp.single d r)) =
          monomialPushforward (S := R ⧸ I ^ n)
            (R ⧸ (I ^ n • (⊤ : Submodule R R))) g
            (DFinsupp.mapRange.linearMap (R := R)
              (fun _ : σ →₀ ℕ => (I ^ n • (⊤ : Submodule R R)).mkQ)
              (DFinsupp.single d r)) := by
      simp only [monomialPushforward_single, DFinsupp.mapRange.linearMap_apply,
        DFinsupp.mapRange_single]
    simpa only [map_add] using congrArg₂ (fun x y => x + y) hs ih

open Classical in
private theorem coeff_polynomialRename (g : σ → τ) (p : MvPolynomial σ R)
    (b : τ →₀ ℕ) :
    (MvPolynomial.rename g p).coeff b =
      ∑ d ∈ p.support.filter (fun d => Finsupp.mapDomain g d = b), p.coeff d := by
  calc
    (MvPolynomial.rename g p).coeff b =
        (MvPolynomial.rename g (∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d))).coeff b :=
      congrArg (fun q : MvPolynomial σ R => (MvPolynomial.rename g q).coeff b)
        (MvPolynomial.as_sum p)
    _ = ∑ d ∈ p.support, if Finsupp.mapDomain g d = b then p.coeff d else 0 := by
      rw [map_sum, MvPolynomial.coeff_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [MvPolynomial.rename_monomial, MvPolynomial.coeff_monomial]
    _ = _ := by rw [Finset.sum_filter]

private theorem completedReduction_ext (I : Ideal R)
    {s t : polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))}
    (h : ∀ n, polynomialReduction σ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s =
      polynomialReduction σ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n t) :
    s = t := by
  have hinj := (polynomialReduction_jointly_injective_iff σ
    (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))).2
    (fun a b hab => AdicCompletion.ext_evalₐ (fun n => congrFun hab n))
  exact hinj (funext h)

/-- The whole restricted-product composite, using the completion functor's
canonical completed-scalar linearity. -/
private def completedRenameLinear (I : Ideal R) (g : σ → τ) :
    polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
      →ₗ[AdicCompletion I R] polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) :=
  (restrictedProductEquivPolynomialReduction τ I).toLinearMap ∘ₗ
    (AdicCompletion.dfinsuppEquiv I (fun _ : τ →₀ ℕ => R)).toLinearMap ∘ₗ
    AdicCompletion.map I (monomialPushforward (S := R) R g) ∘ₗ
    (AdicCompletion.dfinsuppEquiv I (fun _ : σ →₀ ℕ => R)).symm.toLinearMap ∘ₗ
    (restrictedProductEquivPolynomialReduction σ I).symm.toLinearMap

private theorem polynomialReduction_completedRenameLinear (I : Ideal R) (g : σ → τ)
    (n : ℕ) (s : polynomialReductionSubalgebra σ
      (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m))) :
    polynomialReduction τ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n
        (completedRenameLinear I g s) =
      MvPolynomial.rename g (polynomialReduction σ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s) := by
  classical
  let a := (restrictedProductEquivPolynomialReduction σ I).symm s
  let x := (AdicCompletion.dfinsuppEquiv I (fun _ : σ →₀ ℕ => R)).symm a
  let y := AdicCompletion.map I (monomialPushforward (S := R) R g) x
  let v := Ideal.quotientDFinsupp (I ^ n) (fun _ : σ →₀ ℕ => R)
    (AdicCompletion.eval I (Π₀ (_ : σ →₀ ℕ), R) n x)
  let p := polynomialReduction σ
    (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s
  let k : (R ⧸ (I ^ n * ⊤)) →+* R ⧸ I ^ n :=
    Ideal.Quotient.factor (le_of_eq (Ideal.mul_top (I ^ n)))
  have hk : Function.Injective k :=
    (Ideal.quotientEquivAlgOfEq R (Ideal.mul_top (I ^ n))).injective
  have hv (d : σ →₀ ℕ) : v d = AdicCompletion.eval I R n (coeff d s.val) := by
    change Ideal.quotientDFinsupp (I ^ n) (fun _ : σ →₀ ℕ => R)
      (AdicCompletion.eval I (Π₀ (_ : σ →₀ ℕ), R) n
        ((AdicCompletion.dfinsuppEquiv I (fun _ : σ →₀ ℕ => R)).symm
          ((restrictedProductEquivPolynomialReduction σ I).symm s))) d = _
    rw [AdicCompletion.dfinsuppEquiv_symm_eval,
      restrictedProductEquivPolynomialReduction_symm_apply]
  have hvraw (d : σ →₀ ℕ) : k (v d) = p.coeff d := by
    rw [hv, coeff_polynomialReduction]
    exact AdicCompletion.factor_eval_eq_evalₐ I _ (le_of_eq (Ideal.mul_top (I ^ n)))
  have hsupp : v.support = p.support := by
    apply Finset.ext
    intro d
    rw [DFinsupp.mem_support_iff, MvPolynomial.mem_support_iff, ← hvraw]
    exact not_congr (⟨fun h => by rw [h, map_zero],
      fun h => hk (h.trans (map_zero k).symm)⟩ : v d = 0 ↔ k (v d) = 0)
  apply MvPolynomial.ext
  intro b
  have hout : AdicCompletion.eval I R n (coeff b (completedRenameLinear I g s).val) =
      monomialPushforward (S := R ⧸ I ^ n)
        (R ⧸ (I ^ n • (⊤ : Submodule R R))) g v b := by
    change AdicCompletion.eval I R n
      ((AdicCompletion.dfinsuppEquiv I (fun _ : τ →₀ ℕ => R) y).val b) = _
    have h := AdicCompletion.dfinsuppEquiv_symm_eval I (fun _ : τ →₀ ℕ => R)
      (AdicCompletion.dfinsuppEquiv I (fun _ : τ →₀ ℕ => R) y) n b
    rw [LinearEquiv.symm_apply_apply] at h
    rw [← h]
    change Ideal.quotientDFinsupp (I ^ n) (fun _ : τ →₀ ℕ => R)
      ((AdicCompletion.map I (monomialPushforward (S := R) R g) x).val n) b = _
    rw [AdicCompletion.map_val_apply, quotientDFinsupp_monomialPushforward,
      ← AdicCompletion.eval_apply I (Π₀ (_ : σ →₀ ℕ), R) n x]
  rw [coeff_polynomialReduction]
  calc
    AdicCompletion.evalₐ I n (coeff b (completedRenameLinear I g s).val) =
        k (AdicCompletion.eval I R n (coeff b (completedRenameLinear I g s).val)) :=
      (AdicCompletion.factor_eval_eq_evalₐ I _ (le_of_eq (Ideal.mul_top (I ^ n)))).symm
    _ = k (monomialPushforward (S := R ⧸ I ^ n)
        (R ⧸ (I ^ n • (⊤ : Submodule R R))) g v b) := congrArg k hout
    _ = ∑ d ∈ v.support.filter (fun d => Finsupp.mapDomain g d = b), k (v d) := by
      rw [monomialPushforward_apply, map_sum]
    _ = ∑ d ∈ p.support.filter (fun d => Finsupp.mapDomain g d = b), p.coeff d := by
      rw [hsupp]
      exact Finset.sum_congr rfl (fun d _ => hvraw d)
    _ = (MvPolynomial.rename g p).coeff b := (coeff_polynomialRename g p b).symm

private theorem completedRenameLinear_algebraMap (I : Ideal R) (g : σ → τ)
    (a : AdicCompletion I R) :
    completedRenameLinear I g
        (algebraMap (AdicCompletion I R) (polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) a) =
      algebraMap (AdicCompletion I R) (polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) a := by
  apply completedReduction_ext I
  intro n
  rw [polynomialReduction_completedRenameLinear, polynomialReduction_algebraMap,
    polynomialReduction_algebraMap, MvPolynomial.rename_C]

/-- Renaming by an arbitrary variable map on the series that are polynomial at
all raw ideal-power precisions, as an algebra map over the completed coefficients.
Its function is completion of the finite direct-sum monomial pushforward,
transported by the whole restricted-product comparison. -/
@[no_expose]
def completedRestrictedRename (I : Ideal R) (g : σ → τ) :
    polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
      →ₐ[AdicCompletion I R] polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) where
  toFun := completedRenameLinear I g
  map_zero' := map_zero (completedRenameLinear I g)
  map_add' := map_add (completedRenameLinear I g)
  map_one' := by
    simpa only [map_one] using completedRenameLinear_algebraMap I g 1
  map_mul' s t := by
    apply completedReduction_ext I
    intro n
    simp only [polynomialReduction_completedRenameLinear, map_mul]
  commutes' := completedRenameLinear_algebraMap I g

/-- At every raw precision, including zero, arbitrary renaming is polynomial renaming. -/
@[simp]
theorem polynomialReduction_completedRestrictedRename (I : Ideal R) (g : σ → τ)
    (n : ℕ) (s : polynomialReductionSubalgebra σ
      (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m))) :
    polynomialReduction τ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n
        (completedRestrictedRename I g s) =
      MvPolynomial.rename g (polynomialReduction σ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s) :=
  polynomialReduction_completedRenameLinear I g n s

open Classical in
/-- A renamed raw coefficient is the finite sum over the support of the source
polynomial reduction, not over the possibly infinite monomial fiber. -/
theorem coeff_completedRestrictedRename_eval (I : Ideal R) (g : σ → τ)
    (n : ℕ) (s : polynomialReductionSubalgebra σ
      (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)))
    (b : τ →₀ ℕ) :
    AdicCompletion.evalₐ I n (coeff b (completedRestrictedRename I g s).val) =
      ∑ d ∈ (polynomialReduction σ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s).support.filter
          (fun d => Finsupp.mapDomain g d = b), AdicCompletion.evalₐ I n (coeff d s.val) := by
  have h := congrArg (fun p : MvPolynomial τ (R ⧸ I ^ n) => p.coeff b)
    (polynomialReduction_completedRestrictedRename I g n s)
  rw [coeff_polynomialReduction, coeff_polynomialRename] at h
  exact h.trans (Finset.sum_congr rfl (fun d _ => coeff_polynomialReduction σ _ n s d))

/-- The identity variable map induces the identity algebra homomorphism. -/
@[simp]
theorem completedRestrictedRename_id (I : Ideal R) :
    completedRestrictedRename I (id : σ → σ) =
      AlgHom.id (AdicCompletion I R) (polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) := by
  apply AlgHom.ext
  intro s
  apply completedReduction_ext I
  intro n
  simp only [polynomialReduction_completedRestrictedRename, AlgHom.id_apply,
    MvPolynomial.rename_id_apply]

/-- Arbitrary variable maps compose in the same order as polynomial renaming. -/
theorem completedRestrictedRename_comp (I : Ideal R) (g : σ → τ) (h : τ → υ) :
    (completedRestrictedRename I h).comp (completedRestrictedRename I g) =
      completedRestrictedRename I (h ∘ g) := by
  apply AlgHom.ext
  intro s
  apply completedReduction_ext I
  intro n
  simp only [AlgHom.comp_apply, polynomialReduction_completedRestrictedRename,
    MvPolynomial.rename_rename]

/-- Renaming commutes with polynomial inclusion over the completed coefficient ring. -/
@[simp]
theorem completedRestrictedRename_polynomial (I : Ideal R) (g : σ → τ)
    (p : MvPolynomial σ (AdicCompletion I R)) :
    completedRestrictedRename I g
        (polynomialToReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) p) =
      polynomialToReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
        (MvPolynomial.rename g p) := by
  apply completedReduction_ext I
  intro n
  rw [polynomialReduction_completedRestrictedRename, polynomialReduction_polynomial,
    polynomialReduction_polynomial, MvPolynomial.map_rename]

/-- On original polynomials, renaming can be performed before completing coefficients. -/
theorem completedRestrictedRename_original_polynomial (I : Ideal R) (g : σ → τ)
    (p : MvPolynomial σ R) :
    completedRestrictedRename I g
        (polynomialToReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
          (MvPolynomial.map (algebraMap R (AdicCompletion I R)) p)) =
      polynomialToReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
        (MvPolynomial.map (algebraMap R (AdicCompletion I R)) (MvPolynomial.rename g p)) := by
  rw [completedRestrictedRename_polynomial, MvPolynomial.map_rename]

/-- Each polynomial variable is sent to the variable indexed by its image. -/
theorem completedRestrictedRename_X (I : Ideal R) (g : σ → τ) (i : σ) :
    completedRestrictedRename I g
        (polynomialToReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
          (MvPolynomial.X i)) =
      polynomialToReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
        (MvPolynomial.X (g i)) := by
  rw [completedRestrictedRename_polynomial, MvPolynomial.rename_X]

/-- Renaming fixes every constant polynomial over the completed coefficient ring. -/
theorem completedRestrictedRename_C (I : Ideal R) (g : σ → τ) (a : AdicCompletion I R) :
    completedRestrictedRename I g
        (polynomialToReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
          (MvPolynomial.C a)) =
      polynomialToReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
        (MvPolynomial.C a) := by
  rw [completedRestrictedRename_polynomial, MvPolynomial.rename_C]

/-- The stock completed coefficient algebra map is preserved by renaming. -/
theorem completedRestrictedRename_algebraMap (I : Ideal R) (g : σ → τ)
    (a : AdicCompletion I R) :
    completedRestrictedRename I g
        (algebraMap (AdicCompletion I R) (polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) a) =
      algebraMap (AdicCompletion I R) (polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) a :=
  (completedRestrictedRename I g).commutes a

/-- Renaming commutes with the completed coefficient maps as ring homomorphisms. -/
theorem completedRestrictedRename_comp_algebraMap (I : Ideal R) (g : σ → τ) :
    (completedRestrictedRename I g).toRingHom.comp
        (algebraMap (AdicCompletion I R) (polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)))) =
      algebraMap (AdicCompletion I R) (polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) := by
  apply RingHom.ext
  intro a
  exact completedRestrictedRename_algebraMap I g a

/-- Renaming fixes constants coming from the original coefficient ring. -/
theorem completedRestrictedRename_algebraMap_of (I : Ideal R) (g : σ → τ) (r : R) :
    completedRestrictedRename I g
        (algebraMap (AdicCompletion I R) (polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)))
          (AdicCompletion.of I R r)) =
      algebraMap (AdicCompletion I R) (polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)))
        (AdicCompletion.of I R r) :=
  completedRestrictedRename_algebraMap I g (AdicCompletion.of I R r)

/-- Scalar multiplication uses the same completed coefficient algebra on both sides. -/
theorem completedRestrictedRename_smul (I : Ideal R) (g : σ → τ)
    (a : AdicCompletion I R) (s : polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) :
    completedRestrictedRename I g (a • s) = a • completedRestrictedRename I g s :=
  map_smul (completedRestrictedRename I g) a s

open Classical in
/-- The support of a renamed row is contained in the image of the source support;
colliding monomials may cancel. -/
theorem support_polynomialReduction_completedRestrictedRename_subset (I : Ideal R)
    (g : σ → τ) (n : ℕ) (s : polynomialReductionSubalgebra σ
      (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m))) :
    (polynomialReduction τ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n
        (completedRestrictedRename I g s)).support ⊆
      (polynomialReduction σ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s).support.image
          (Finsupp.mapDomain g) := by
  rw [polynomialReduction_completedRestrictedRename]
  intro b hb
  obtain ⟨d, hd, hcoeff⟩ := MvPolynomial.coeff_rename_ne_zero g _ b
    (MvPolynomial.mem_support_iff.1 hb)
  exact Finset.mem_image.2 ⟨d, MvPolynomial.mem_support_iff.2 hcoeff, hd⟩

/-- Vanishing at a source raw precision implies vanishing at the same target precision. -/
theorem ker_polynomialReduction_le_comap_completedRestrictedRename (I : Ideal R)
    (g : σ → τ) (n : ℕ) :
    RingHom.ker (polynomialReduction σ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n) ≤
      (RingHom.ker (polynomialReduction τ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n)).comap
        (completedRestrictedRename I g).toRingHom := by
  intro s hs
  change polynomialReduction σ
    (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s = 0 at hs
  change polynomialReduction τ
    (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n
    (completedRestrictedRename I g s) = 0
  rw [polynomialReduction_completedRestrictedRename, hs, map_zero]

/-- The all-row polynomial-renaming squares uniquely determine the algebra homomorphism. -/
theorem eq_completedRestrictedRename (I : Ideal R) (g : σ → τ)
    (F : polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
      →ₐ[AdicCompletion I R] polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)))
    (hF : ∀ (n : ℕ) (s : polynomialReductionSubalgebra σ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m))),
      polynomialReduction τ
          (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n (F s) =
        MvPolynomial.rename g (polynomialReduction σ
          (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s)) :
    F = completedRestrictedRename I g := by
  apply AlgHom.ext
  intro s
  apply completedReduction_ext I
  intro n
  exact (hF n s).trans (polynomialReduction_completedRestrictedRename I g n s).symm

end MvPowerSeries
