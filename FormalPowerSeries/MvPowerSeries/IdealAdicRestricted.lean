/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module

public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.Ideal.Quotient.Defs

@[expose] public section

/-!
# Polynomial reductions of multivariate power series

For a family of coefficient homomorphisms `q : ∀ i, C →+* Q i` between commutative
semirings, `polynomialReductionSubalgebra σ q` consists of the series whose image
under every `q i` is polynomial. Equivalently, each reduced coefficient family has
finite support. Its algebra structure is the usual coefficient algebra; no algebra
structures on the `Q i`, compatibility between rows, or finite variable type are needed.

The ideal-adically restricted subring is the specialization to the quotient maps
`R →+* R ⧸ I ^ k`. Its original predicate, polynomial inclusion and finite reductions
are retained. No completeness or finite generation assumption is made in this module.

The finite-support argument uses Mathlib's polynomial inclusion and `truncFinset`;
the subalgebra and its reductions generalize the ideal-adic construction in this library.
-/

set_option warningAsError true

universe u v w z

namespace MvPowerSeries

/-- Coefficientwise change of semiring commutes with polynomial inclusion. -/
theorem map_polynomial_coe {σ : Type v} {R : Type u} [CommSemiring R]
    {S : Type z} [CommSemiring S] (g : R →+* S) (p : MvPolynomial σ R) :
    map g (p : MvPowerSeries σ R) =
      (MvPolynomial.map g p : MvPowerSeries σ S) := by
  ext m
  simp only [coeff_map, MvPolynomial.coeff_coe, MvPolynomial.coeff_map]

section PolynomialReduction

variable {C : Type u} [CommSemiring C] {σ : Type v}

/-- A coefficientwise image is polynomial exactly when only finitely many reduced
coefficients are nonzero. -/
theorem finite_support_iff_map_mem_polynomial_range {D : Type z} [CommSemiring D]
    (r : C →+* D) (f : MvPowerSeries σ C) :
    {m : σ →₀ ℕ | r (coeff m f) ≠ 0}.Finite ↔
      map r f ∈ Set.range (MvPolynomial.coeToMvPowerSeries.ringHom
        (σ := σ) (R := D)) := by
  classical
  constructor
  · intro h
    let s := h.toFinset
    refine ⟨truncFinset D s (map r f), ?_⟩
    apply MvPowerSeries.ext
    intro m
    by_cases hm : m ∈ s
    · simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        MvPolynomial.coeff_coe, coeff_truncFinset_of_mem _ hm]
    · have hzero : r (coeff m f) = 0 := by
        by_contra hnot
        exact hm (h.mem_toFinset.mpr hnot)
      simpa only [MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        MvPolynomial.coeff_coe, coeff_truncFinset_eq_zero _ hm, coeff_map] using
        hzero.symm
  · rintro ⟨p, hp⟩
    have hs : {m : σ →₀ ℕ | r (coeff m f) ≠ 0} = (p.support : Set (σ →₀ ℕ)) := by
      ext m
      have hc : p.coeff m = r (coeff m f) := by
        have heq := congrArg (MvPowerSeries.coeff m) hp
        simpa only [MvPolynomial.coeToMvPowerSeries.ringHom_apply,
          MvPolynomial.coeff_coe, coeff_map] using heq
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, MvPolynomial.mem_support_iff, hc]
    rw [hs]
    exact p.support.finite_toSet

variable {ι : Type w} {Q : ι → Type z} [∀ i, CommSemiring (Q i)]
variable (σ) (q : ∀ i, C →+* Q i)

/-- The coefficient subalgebra of series that become polynomials under every specified
coefficient homomorphism. Its carrier is the intersection of polynomial-range preimages. -/
noncomputable def polynomialReductionSubalgebra : Subalgebra C (MvPowerSeries σ C) where
  toSubsemiring := ⨅ i, (MvPolynomial.coeToMvPowerSeries.ringHom
    (σ := σ) (R := Q i)).rangeS.comap (map (q i))
  algebraMap_mem' c :=
    Subsemiring.mem_iInf.mpr fun i =>
      Subsemiring.mem_comap.mpr <|
        RingHom.mem_rangeS.mpr ⟨MvPolynomial.C (σ := σ) (q i c), by
          simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C,
            ← c_eq_algebraMap, map_C]⟩

/-- Membership is polynomiality of every coefficientwise image. -/
@[simp]
theorem mem_polynomialReductionSubalgebra (f : MvPowerSeries σ C) :
    f ∈ polynomialReductionSubalgebra σ q ↔
      ∀ i, map (q i) f ∈ Set.range (MvPolynomial.coeToMvPowerSeries.ringHom
        (σ := σ) (R := Q i)) := by
  change f ∈ (⨅ i, (MvPolynomial.coeToMvPowerSeries.ringHom
    (σ := σ) (R := Q i)).rangeS.comap (map (q i))) ↔ _
  simp only [Subsemiring.mem_iInf, Subsemiring.mem_comap, RingHom.mem_rangeS, Set.mem_range]

/-- Membership is finite support of each reduced coefficient family. -/
theorem mem_polynomialReductionSubalgebra_iff_finite_support (f : MvPowerSeries σ C) :
    f ∈ polynomialReductionSubalgebra σ q ↔
      ∀ i, {m : σ →₀ ℕ | q i (coeff m f) ≠ 0}.Finite := by
  simp only [mem_polynomialReductionSubalgebra,
    finite_support_iff_map_mem_polynomial_range]

/-- Restricted series are equal when all their ambient coefficients agree. -/
@[ext]
theorem polynomialReductionSubalgebra.ext {f g : polynomialReductionSubalgebra σ q}
    (h : ∀ m, coeff m (f : MvPowerSeries σ C) = coeff m (g : MvPowerSeries σ C)) :
    f = g :=
  Subtype.ext (MvPowerSeries.ext h)

/-- The subalgebra retains the stock coefficient-algebra map. -/
theorem polynomialReductionSubalgebra.coe_algebraMap (c : C) :
    ((algebraMap C (polynomialReductionSubalgebra σ q) c :
      polynomialReductionSubalgebra σ q) : MvPowerSeries σ C) = MvPowerSeries.C c := by
  rw [Subalgebra.coe_algebraMap, ← c_eq_algebraMap]

/-- Every polynomial belongs to the subalgebra, regardless of the reduction family. -/
theorem polynomial_mem_polynomialReductionSubalgebra (p : MvPolynomial σ C) :
    (p : MvPowerSeries σ C) ∈ polynomialReductionSubalgebra σ q := by
  rw [mem_polynomialReductionSubalgebra]
  intro i
  exact ⟨MvPolynomial.map (q i) p, by
    simpa only [MvPolynomial.coeToMvPowerSeries.ringHom_apply] using
      (map_polynomial_coe (q i) p).symm⟩

/-- Polynomial inclusion as a coefficient-algebra homomorphism into the subalgebra. -/
noncomputable def polynomialToReductionSubalgebra :
    MvPolynomial σ C →ₐ[C] polynomialReductionSubalgebra σ q :=
  (MvPolynomial.coeToMvPowerSeries.algHom C).codRestrict _ (fun p => by
    simpa only [MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self,
      map_id, RingHom.id_apply] using polynomial_mem_polynomialReductionSubalgebra σ q p)

/-- The restricted polynomial inclusion has the usual ambient series. -/
@[simp]
theorem polynomialToReductionSubalgebra_coe (p : MvPolynomial σ C) :
    ((polynomialToReductionSubalgebra σ q p : polynomialReductionSubalgebra σ q) :
      MvPowerSeries σ C) = p := by
  simp only [polynomialToReductionSubalgebra, AlgHom.coe_codRestrict,
    MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self,
    map_id, RingHom.id_apply]

/-- The polynomial inclusion factors the stock algebra homomorphism through the subalgebra. -/
@[simp]
theorem val_comp_polynomialToReductionSubalgebra :
    (polynomialReductionSubalgebra σ q).val.comp (polynomialToReductionSubalgebra σ q) =
      MvPolynomial.coeToMvPowerSeries.algHom C :=
  AlgHom.val_comp_codRestrict _ _ _

/-- Finite reduced coefficient supports give the usual algebra-hom codomain restriction;
composing with the subalgebra inclusion recovers the original map. -/
theorem polynomialReductionSubalgebra.val_comp_codRestrict {A : Type*} [Semiring A]
    [Algebra C A] (g : A →ₐ[C] MvPowerSeries σ C)
    (hg : ∀ x i, {m : σ →₀ ℕ | q i (coeff m (g x)) ≠ 0}.Finite) :
    (polynomialReductionSubalgebra σ q).val.comp
        (g.codRestrict (polynomialReductionSubalgebra σ q) (fun x =>
          (mem_polynomialReductionSubalgebra_iff_finite_support σ q (g x)).2 (hg x))) = g :=
  AlgHom.val_comp_codRestrict _ _ _

private noncomputable def reductionPolynomial (i : ι)
    (f : polynomialReductionSubalgebra σ q) : MvPolynomial σ (Q i) :=
  Classical.choose ((mem_polynomialReductionSubalgebra σ q
    (f : MvPowerSeries σ C)).1 f.property i)

private theorem reductionPolynomial_spec (i : ι) (f : polynomialReductionSubalgebra σ q) :
    ((reductionPolynomial σ q i f : MvPolynomial σ (Q i)) : MvPowerSeries σ (Q i)) =
      map (q i) (f : MvPowerSeries σ C) := by
  simpa only [reductionPolynomial, MvPolynomial.coeToMvPowerSeries.ringHom_apply] using
    Classical.choose_spec ((mem_polynomialReductionSubalgebra σ q
      (f : MvPowerSeries σ C)).1 f.property i)

/-- Finite polynomial reduction along one row of the coefficient homomorphism family. -/
@[no_expose]
noncomputable def polynomialReduction (i : ι) :
    polynomialReductionSubalgebra σ q →+* MvPolynomial σ (Q i) where
  toFun := reductionPolynomial σ q i
  map_zero' := by
    apply MvPolynomial.coe_injective σ (Q i)
    simp only [reductionPolynomial_spec, Subalgebra.coe_zero, map_zero,
      MvPolynomial.coe_zero]
  map_one' := by
    apply MvPolynomial.coe_injective σ (Q i)
    simp only [reductionPolynomial_spec, Subalgebra.coe_one, map_one,
      MvPolynomial.coe_one]
  map_add' f g := by
    apply MvPolynomial.coe_injective σ (Q i)
    simp only [reductionPolynomial_spec, Subalgebra.coe_add, map_add,
      MvPolynomial.coe_add]
  map_mul' f g := by
    apply MvPolynomial.coe_injective σ (Q i)
    simp only [reductionPolynomial_spec, Subalgebra.coe_mul, map_mul,
      MvPolynomial.coe_mul]

/-- Polynomial inclusion of a reduction is coefficientwise application of that row. -/
theorem polynomialReduction_coe (i : ι) (f : polynomialReductionSubalgebra σ q) :
    ((polynomialReduction σ q i f : MvPolynomial σ (Q i)) : MvPowerSeries σ (Q i)) =
      map (q i) (f : MvPowerSeries σ C) :=
  reductionPolynomial_spec σ q i f

/-- Coefficients of a polynomial reduction are the reduced original coefficients. -/
@[simp]
theorem coeff_polynomialReduction (i : ι) (f : polynomialReductionSubalgebra σ q)
    (m : σ →₀ ℕ) :
    (polynomialReduction σ q i f).coeff m = q i (coeff m (f : MvPowerSeries σ C)) := by
  have hc := congrArg (MvPowerSeries.coeff m) (polynomialReduction_coe σ q i f)
  simpa only [MvPolynomial.coeff_coe, coeff_map] using hc

/-- Reducing an included polynomial is its coefficientwise polynomial image. -/
@[simp]
theorem polynomialReduction_polynomial (i : ι) (p : MvPolynomial σ C) :
    polynomialReduction σ q i (polynomialToReductionSubalgebra σ q p) =
      MvPolynomial.map (σ := σ) (q i) p := by
  apply MvPolynomial.coe_injective σ (Q i)
  rw [polynomialReduction_coe, polynomialToReductionSubalgebra_coe, map_polynomial_coe]

/-- Reducing a coefficient scalar gives the corresponding constant polynomial. -/
@[simp]
theorem polynomialReduction_algebraMap (i : ι) (c : C) :
    polynomialReduction σ q i (algebraMap C (polynomialReductionSubalgebra σ q) c) =
      MvPolynomial.C (σ := σ) (q i c) := by
  apply MvPolynomial.coe_injective σ (Q i)
  rw [polynomialReduction_coe, polynomialReductionSubalgebra.coe_algebraMap,
    map_C, MvPolynomial.coe_C]

/-- The polynomial reductions jointly distinguish restricted series exactly when the
coefficient homomorphisms jointly distinguish coefficients. -/
theorem polynomialReduction_jointly_injective_iff :
    Function.Injective (fun f : polynomialReductionSubalgebra σ q =>
      fun i => polynomialReduction σ q i f) ↔
        Function.Injective (fun c : C => fun i => q i c) := by
  constructor
  · intro h c d hcd
    have hconst : algebraMap C (polynomialReductionSubalgebra σ q) c =
        algebraMap C (polynomialReductionSubalgebra σ q) d := by
      apply h
      funext i
      change polynomialReduction σ q i
          (algebraMap C (polynomialReductionSubalgebra σ q) c) =
        polynomialReduction σ q i (algebraMap C (polynomialReductionSubalgebra σ q) d)
      rw [polynomialReduction_algebraMap, polynomialReduction_algebraMap]
      exact congrArg (MvPolynomial.C (σ := σ)) (congrFun hcd i)
    have hcoeff := congrArg (fun f : polynomialReductionSubalgebra σ q =>
      coeff (0 : σ →₀ ℕ) (f : MvPowerSeries σ C)) hconst
    simpa only [polynomialReductionSubalgebra.coe_algebraMap, coeff_zero_C] using hcoeff
  · intro hq f g hfg
    apply polynomialReductionSubalgebra.ext σ q
    intro m
    apply hq
    funext i
    have hcoeff := congrArg (fun p : MvPolynomial σ (Q i) => p.coeff m) (congrFun hfg i)
    simpa only [coeff_polynomialReduction] using hcoeff

/-- A surjective coefficient row gives a surjective polynomial reduction. No other row
needs to be surjective: a lifted polynomial belongs to the entire subalgebra. -/
theorem polynomialReduction_surjective (i : ι) (hi : Function.Surjective (q i)) :
    Function.Surjective (polynomialReduction σ q i) := by
  intro p
  obtain ⟨r, rfl⟩ := MvPolynomial.map_surjective (σ := σ) (q i) hi p
  exact ⟨polynomialToReductionSubalgebra σ q r, polynomialReduction_polynomial σ q i r⟩

/-- A specified coefficient transition commutes with finite polynomial reduction. -/
theorem polynomialReduction_transition (i j : ι) (t : Q j →+* Q i)
    (h : t.comp (q j) = q i) (f : polynomialReductionSubalgebra σ q) :
    MvPolynomial.map (σ := σ) t (polynomialReduction σ q j f) =
      polynomialReduction σ q i f := by
  apply MvPolynomial.ext
  intro m
  simp only [MvPolynomial.coeff_map, coeff_polynomialReduction]
  exact congrArg (fun r : C →+* Q i => r (coeff m (f : MvPowerSeries σ C))) h

/-- With no reduction rows, every series belongs to the subalgebra. -/
@[simp]
theorem polynomialReductionSubalgebra_eq_top [IsEmpty ι] :
    polynomialReductionSubalgebra σ q = ⊤ := by
  apply top_unique
  intro f _
  rw [mem_polynomialReductionSubalgebra]
  exact fun i => isEmptyElim i

end PolynomialReduction

section IdentityReduction

variable {C : Type u} [CommSemiring C] (σ : Type v)

/-- One identity row cuts out precisely the polynomial-inclusion subalgebra. -/
theorem polynomialReductionSubalgebra_id :
    polynomialReductionSubalgebra σ (fun _ : Unit => RingHom.id C) =
      (MvPolynomial.coeToMvPowerSeries.algHom C (σ := σ)).range := by
  apply Subalgebra.ext
  intro f
  simp only [mem_polynomialReductionSubalgebra, map_id, RingHom.id_apply,
    AlgHom.mem_range, MvPolynomial.coeToMvPowerSeries.algHom_apply,
    Algebra.algebraMap_self, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    Set.mem_range, forall_const]

/-- For the identity row, polynomial reduction is a left inverse to inclusion. -/
theorem polynomialReduction_id_polynomial (p : MvPolynomial σ C) :
    polynomialReduction σ (fun _ : Unit => RingHom.id C) ()
      (polynomialToReductionSubalgebra σ (fun _ : Unit => RingHom.id C) p) = p := by
  rw [polynomialReduction_polynomial, MvPolynomial.map_id]

/-- For the identity row, polynomial reduction is also a right inverse to inclusion. -/
@[simp]
theorem polynomialToReductionSubalgebra_id_reduction
    (f : polynomialReductionSubalgebra σ (fun _ : Unit => RingHom.id C)) :
    polynomialToReductionSubalgebra σ (fun _ : Unit => RingHom.id C)
      (polynomialReduction σ (fun _ : Unit => RingHom.id C) () f) = f := by
  apply Subtype.ext
  rw [polynomialToReductionSubalgebra_coe, polynomialReduction_coe,
    map_id, RingHom.id_apply]

end IdentityReduction

section AdicallyRestricted

variable {σ : Type v} {R : Type u} [CommRing R]

/-- Coefficientwise ideal-adic decay, with finitely many exceptions at each level. -/
def IsAdicallyRestricted (I : Ideal R) (f : MvPowerSeries σ R) : Prop :=
  ∀ k : ℕ, {m : σ →₀ ℕ | coeff m f ∉ I ^ k}.Finite

/-- A quotient series is polynomial exactly when only finitely many coefficients
survive reduction modulo the chosen ideal power. -/
theorem finite_exception_iff_map_mem_poly_range (I : Ideal R) (k : ℕ)
    (f : MvPowerSeries σ R) :
    {m : σ →₀ ℕ | coeff m f ∉ I ^ k}.Finite ↔
      map (Ideal.Quotient.mk (I ^ k)) f ∈
        (MvPolynomial.coeToMvPowerSeries.ringHom
          (σ := σ) (R := R ⧸ I ^ k)).range := by
  simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_range, Set.mem_range] using
    finite_support_iff_map_mem_polynomial_range (Ideal.Quotient.mk (I ^ k)) f

/-- Ideal-adic decay characterized at all levels by polynomial quotient images. -/
theorem isAdicallyRestricted_iff_map_mem_poly_range (I : Ideal R)
    (f : MvPowerSeries σ R) :
    IsAdicallyRestricted I f ↔
      ∀ k : ℕ, map (Ideal.Quotient.mk (I ^ k)) f ∈
        (MvPolynomial.coeToMvPowerSeries.ringHom
          (σ := σ) (R := R ⧸ I ^ k)).range := by
  simp only [IsAdicallyRestricted, finite_exception_iff_map_mem_poly_range]

/-- The subring of series with coefficientwise ideal-adic decay, obtained from the
polynomial-reduction subalgebra for all ideal-power quotient maps. -/
noncomputable def adicallyRestrictedSubring (I : Ideal R) : Subring (MvPowerSeries σ R) :=
  (polynomialReductionSubalgebra σ (fun k : ℕ => Ideal.Quotient.mk (I ^ k))).toSubring

/-- The generic subalgebra specializes to the intrinsic ideal-adic subring. -/
theorem polynomialReductionSubalgebra_toSubring (I : Ideal R) :
    (polynomialReductionSubalgebra σ
      (fun k : ℕ => Ideal.Quotient.mk (I ^ k))).toSubring =
        adicallyRestrictedSubring (σ := σ) I :=
  rfl

@[simp]
theorem mem_adicallyRestrictedSubring (I : Ideal R) (f : MvPowerSeries σ R) :
    f ∈ adicallyRestrictedSubring I ↔ IsAdicallyRestricted I f := by
  change f ∈ (polynomialReductionSubalgebra σ
    (fun k : ℕ => Ideal.Quotient.mk (I ^ k))).toSubring ↔ _
  rw [Subalgebra.mem_toSubring, mem_polynomialReductionSubalgebra_iff_finite_support]
  simp only [IsAdicallyRestricted, ne_eq, Ideal.Quotient.eq_zero_iff_mem]

/-- Any polynomial is restricted for any ideal. -/
theorem isAdicallyRestricted_polynomial (I : Ideal R) (p : MvPolynomial σ R) :
    IsAdicallyRestricted I (p : MvPowerSeries σ R) := by
  apply (mem_adicallyRestrictedSubring I _).1
  exact polynomial_mem_polynomialReductionSubalgebra σ
    (fun k : ℕ => Ideal.Quotient.mk (I ^ k)) p

/-- Polynomial inclusion with codomain restricted to the ideal-adic decay subring. -/
noncomputable def polynomialToRestricted (I : Ideal R) :
    MvPolynomial σ R →+* adicallyRestrictedSubring (σ := σ) I :=
  (polynomialToReductionSubalgebra σ
    (fun k : ℕ => Ideal.Quotient.mk (I ^ k))).toRingHom

@[simp]
theorem polynomialToRestricted_coe (I : Ideal R) (p : MvPolynomial σ R) :
    ((polynomialToRestricted (σ := σ) I p : adicallyRestrictedSubring (σ := σ) I) :
      MvPowerSeries σ R) = p :=
  polynomialToReductionSubalgebra_coe (σ := σ)
    (q := fun k : ℕ => Ideal.Quotient.mk (I ^ k)) p

/-- Finite polynomial reduction of a restricted series modulo `I ^ k`. -/
noncomputable def adicReduction (I : Ideal R) (k : ℕ) :
    adicallyRestrictedSubring (σ := σ) I →+* MvPolynomial σ (R ⧸ I ^ k) :=
  polynomialReduction σ (fun n : ℕ => Ideal.Quotient.mk (I ^ n)) k

/-- Polynomial inclusion of reduction agrees with quotienting all coefficients. -/
theorem adicReduction_coe (I : Ideal R) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    ((adicReduction I k f : MvPolynomial σ (R ⧸ I ^ k)) :
      MvPowerSeries σ (R ⧸ I ^ k)) =
        map (Ideal.Quotient.mk (I ^ k)) (f : MvPowerSeries σ R) :=
  polynomialReduction_coe σ (fun n : ℕ => Ideal.Quotient.mk (I ^ n)) k f

/-- Each coefficient of finite reduction is the original coefficient modulo `I ^ k`. -/
@[simp]
theorem coeff_adicReduction (I : Ideal R) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I) (m : σ →₀ ℕ) :
    (adicReduction I k f).coeff m =
      Ideal.Quotient.mk (I ^ k) (coeff m (f : MvPowerSeries σ R)) :=
  coeff_polynomialReduction σ (fun n : ℕ => Ideal.Quotient.mk (I ^ n)) k f m

/-- Reducing a polynomial through the restricted subring is coefficientwise
polynomial reduction. -/
@[simp]
theorem adicReduction_polynomial (I : Ideal R) (k : ℕ) (p : MvPolynomial σ R) :
    adicReduction I k (polynomialToRestricted I p) =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ k)) p :=
  polynomialReduction_polynomial σ (fun n : ℕ => Ideal.Quotient.mk (I ^ n)) k p

/-- Every quotient polynomial has a restricted-series lift. -/
theorem adicReduction_surjective (I : Ideal R) (k : ℕ) :
    Function.Surjective (adicReduction (σ := σ) I k) :=
  polynomialReduction_surjective (σ := σ)
    (q := fun n : ℕ => Ideal.Quotient.mk (I ^ n)) k Ideal.Quotient.mk_surjective

end AdicallyRestricted

end MvPowerSeries
