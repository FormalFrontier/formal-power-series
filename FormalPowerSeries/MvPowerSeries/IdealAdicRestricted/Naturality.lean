/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.CompletionMap
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.CompletedRename

/-!
# Naturality of the completed-coefficient restricted-series dictionary

A ring homomorphism sending `I` into `J` induces `completedRestrictedCoeffMap`
between the polynomial-reduction subalgebras over the two completed coefficient
rings. This is the restriction of the usual coefficientwise power-series map.
Composing it with arbitrary variable renaming gives `completedRestrictedMap`.
Its target retains its algebra over `AdicCompletion J T`; compatibility with the
source coefficient algebra is expressed using `AdicCompletion.mapRingHom`.

The completed polynomial map and the independently constructed restricted-series
map commute with `MvPolynomial.adicCompletionEquiv` on every completed polynomial,
not just on original polynomial representatives. The proof compares their raw
polynomial reductions. Coefficients are finite sums over source row support,
even when the variable map has infinite fibers.

Every reduction is the raw row in the original quotient `R ⧸ I ^ n`, including
`n = 0`. No completeness, separation or finite-generation hypothesis on the
original rings or ideals is needed. In particular, these rows are not replaced
by quotients of the completed ring by powers of an extended ideal.

## References

The construction uses Mathlib's coefficientwise maps on multivariate power series
and polynomials, this library's polynomial-reduction subalgebras and arbitrary
completed renaming, and the completed ring maps in Adic Modules. Arbitrary
renaming uses the whole Adic Modules completion-of-direct-sums comparison.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe uR uT uU uσ uτ uυ

namespace MvPowerSeries

variable {R : Type uR} {T : Type uT} [CommRing R] [CommRing T]

private theorem map_mem_completedPolynomialReduction (σ : Type uσ)
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (s : polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) :
    map (AdicCompletion.mapRingHom I J f hf) s.val ∈
      polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n)) := by
  apply (mem_polynomialReductionSubalgebra_iff_finite_support σ
    (fun m => (AdicCompletion.evalₐ J m : AdicCompletion J T →+* T ⧸ J ^ m)) _).2
  intro n
  apply ((mem_polynomialReductionSubalgebra_iff_finite_support σ
    (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) s.val).1
    s.property n).subset
  intro d hd
  change AdicCompletion.evalₐ J n
    (coeff d (map (AdicCompletion.mapRingHom I J f hf) s.val)) ≠ 0 at hd
  change AdicCompletion.evalₐ I n (coeff d s.val) ≠ 0
  intro hz
  apply hd
  rw [coeff_map, AdicCompletion.evalₐ_mapRingHom, hz, map_zero]

/-- Coefficient change on the polynomial-reduction subalgebras over completed rings.
It is the codomain restriction of the usual coefficientwise power-series map
along the completed ring homomorphism. -/
@[no_expose]
def completedRestrictedCoeffMap (σ : Type uσ)
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) :
    polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) →+*
      polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n)) :=
  ((map (AdicCompletion.mapRingHom I J f hf)).comp
      (polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n :
          AdicCompletion I R →+* R ⧸ I ^ n))).val.toRingHom).codRestrict
    (polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n)))
    (map_mem_completedPolynomialReduction σ I J f hf)

/-- The ambient series of coefficient change is the stock coefficientwise image.
This equality is the public projection law; the membership proof remains hidden. -/
theorem completedRestrictedCoeffMap_coe (σ : Type uσ)
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (s : polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) :
    (completedRestrictedCoeffMap σ I J f hf s : MvPowerSeries σ (AdicCompletion J T)) =
      map (AdicCompletion.mapRingHom I J f hf) s.val :=
  (rfl)

/-- Every coefficient is mapped by the completed coefficient homomorphism. -/
@[simp]
theorem coeff_completedRestrictedCoeffMap (σ : Type uσ)
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (s : polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)))
    (d : σ →₀ ℕ) :
    coeff d (completedRestrictedCoeffMap σ I J f hf s :
        MvPowerSeries σ (AdicCompletion J T)) =
      AdicCompletion.mapRingHom I J f hf (coeff d s.val) := by
  rw [completedRestrictedCoeffMap_coe, coeff_map]

/-- At each raw precision, coefficient change is polynomial coefficient change
along the induced map between the original ideal-power quotients. -/
@[simp]
theorem polynomialReduction_completedRestrictedCoeffMap (σ : Type uσ)
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (n : ℕ) (s : polynomialReductionSubalgebra σ
      (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m))) :
    polynomialReduction σ
        (fun m => (AdicCompletion.evalₐ J m : AdicCompletion J T →+* T ⧸ J ^ m)) n
        (completedRestrictedCoeffMap σ I J f hf s) =
      MvPolynomial.map
        (Ideal.quotientMap (J ^ n) f
          ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow f n)))
        (polynomialReduction σ
          (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s) := by
  apply MvPolynomial.ext
  intro d
  simp only [coeff_polynomialReduction, MvPolynomial.coeff_map,
    coeff_completedRestrictedCoeffMap]
  exact AdicCompletion.evalₐ_mapRingHom I J f hf n (coeff d s.val)

/-- The identity coefficient homomorphism induces the identity on restricted series. -/
@[simp]
theorem completedRestrictedCoeffMap_id (σ : Type uσ) (I : Ideal R) :
    completedRestrictedCoeffMap σ I I (RingHom.id R) (by
      intro r hr
      exact hr) =
      RingHom.id (polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) := by
  apply RingHom.ext
  intro s
  apply polynomialReductionSubalgebra.ext σ _
  intro d
  simp only [RingHom.id_apply, coeff_completedRestrictedCoeffMap,
    AdicCompletion.mapRingHom_id]

/-- Coefficient change composes in the same order as the original ring maps. -/
theorem completedRestrictedCoeffMap_comp {U : Type uU} [CommRing U]
    (σ : Type uσ) (I : Ideal R) (J : Ideal T) (L : Ideal U)
    (f : R →+* T) (k : T →+* U) (hf : I ≤ J.comap f) (hk : J ≤ L.comap k) :
    (completedRestrictedCoeffMap σ J L k hk).comp
        (completedRestrictedCoeffMap σ I J f hf) =
      completedRestrictedCoeffMap σ I L (k.comp f) (by
        intro r hr
        exact hk (hf hr)) := by
  apply RingHom.ext
  intro s
  apply polynomialReductionSubalgebra.ext σ _
  intro d
  simp only [RingHom.comp_apply, coeff_completedRestrictedCoeffMap]
  exact congrArg (fun h : AdicCompletion I R →+* AdicCompletion L U =>
    h (coeff d s.val)) (AdicCompletion.mapRingHom_comp I J L f k hf hk)

/-- Coefficient change commutes with polynomial inclusion over the completed rings. -/
@[simp]
theorem completedRestrictedCoeffMap_polynomial (σ : Type uσ)
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (p : MvPolynomial σ (AdicCompletion I R)) :
    completedRestrictedCoeffMap σ I J f hf
        (polynomialToReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) p) =
      polynomialToReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n))
        (MvPolynomial.map (AdicCompletion.mapRingHom I J f hf) p) := by
  apply Subtype.ext
  simp only [completedRestrictedCoeffMap_coe, polynomialToReductionSubalgebra_coe,
    map_polynomial_coe]

/-- On polynomials with original coefficients, coefficient change agrees with
mapping those coefficients first and then including them in the target completion. -/
theorem completedRestrictedCoeffMap_original_polynomial (σ : Type uσ)
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (p : MvPolynomial σ R) :
    completedRestrictedCoeffMap σ I J f hf
        (polynomialToReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
          (MvPolynomial.map (algebraMap R (AdicCompletion I R)) p)) =
      polynomialToReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n))
        (MvPolynomial.map (algebraMap T (AdicCompletion J T)) (MvPolynomial.map f p)) := by
  have hcoeff : (AdicCompletion.mapRingHom I J f hf).comp
      (algebraMap R (AdicCompletion I R)) =
      (algebraMap T (AdicCompletion J T)).comp f := by
    apply RingHom.ext
    intro r
    simpa only [RingHom.comp_apply, AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply] using
      AdicCompletion.mapRingHom_of I J f hf r
  rw [completedRestrictedCoeffMap_polynomial, MvPolynomial.map_map, hcoeff,
    ← MvPolynomial.map_map]

/-- Coefficient change fixes each polynomial variable. -/
theorem completedRestrictedCoeffMap_X (σ : Type uσ)
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (i : σ) :
    completedRestrictedCoeffMap σ I J f hf
        (polynomialToReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
          (MvPolynomial.X i)) =
      polynomialToReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n))
        (MvPolynomial.X i) := by
  rw [completedRestrictedCoeffMap_polynomial, MvPolynomial.map_X]

/-- A constant series is mapped by the exact completed coefficient homomorphism. -/
@[simp]
theorem completedRestrictedCoeffMap_algebraMap (σ : Type uσ)
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (a : AdicCompletion I R) :
    completedRestrictedCoeffMap σ I J f hf
        (algebraMap (AdicCompletion I R) (polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) a) =
      algebraMap (AdicCompletion J T) (polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n)))
        (AdicCompletion.mapRingHom I J f hf a) := by
  apply Subtype.ext
  simp only [completedRestrictedCoeffMap_coe, polynomialReductionSubalgebra.coe_algebraMap,
    map_C]

/-- The constant-series square commutes as an equality of ring homomorphisms. -/
theorem completedRestrictedCoeffMap_comp_algebraMap (σ : Type uσ)
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) :
    (completedRestrictedCoeffMap σ I J f hf).comp
        (algebraMap (AdicCompletion I R) (polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)))) =
      (algebraMap (AdicCompletion J T) (polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n)))).comp
        (AdicCompletion.mapRingHom I J f hf) := by
  apply RingHom.ext
  intro a
  exact completedRestrictedCoeffMap_algebraMap σ I J f hf a

/-- On original constants, coefficient change applies the original ring map. -/
theorem completedRestrictedCoeffMap_algebraMap_of (σ : Type uσ)
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (r : R) :
    completedRestrictedCoeffMap σ I J f hf
        (algebraMap (AdicCompletion I R) (polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)))
          (AdicCompletion.of I R r)) =
      algebraMap (AdicCompletion J T) (polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n)))
        (AdicCompletion.of J T (f r)) := by
  rw [completedRestrictedCoeffMap_algebraMap, AdicCompletion.mapRingHom_of]

/-- Scalar multiplication is preserved along the completed coefficient map,
using the stock source and target coefficient algebras. -/
theorem completedRestrictedCoeffMap_smul (σ : Type uσ)
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (a : AdicCompletion I R) (s : polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) :
    completedRestrictedCoeffMap σ I J f hf (a • s) =
      AdicCompletion.mapRingHom I J f hf a • completedRestrictedCoeffMap σ I J f hf s := by
  simp only [Algebra.smul_def, map_mul, completedRestrictedCoeffMap_algebraMap]

/-- Vanishing at a raw source precision implies vanishing at the same target precision. -/
theorem ker_polynomialReduction_le_comap_completedRestrictedCoeffMap (σ : Type uσ)
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (n : ℕ) :
    RingHom.ker (polynomialReduction σ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n) ≤
      (RingHom.ker (polynomialReduction σ
        (fun m => (AdicCompletion.evalₐ J m : AdicCompletion J T →+* T ⧸ J ^ m)) n)).comap
        (completedRestrictedCoeffMap σ I J f hf) := by
  intro s hs
  change polynomialReduction σ
    (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s = 0 at hs
  change polynomialReduction σ
    (fun m => (AdicCompletion.evalₐ J m : AdicCompletion J T →+* T ⧸ J ^ m)) n
    (completedRestrictedCoeffMap σ I J f hf s) = 0
  rw [polynomialReduction_completedRestrictedCoeffMap, hs, map_zero]

/-- The raw polynomial-row squares uniquely determine coefficient change. -/
theorem eq_completedRestrictedCoeffMap (σ : Type uσ)
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (F : polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) →+*
      polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n)))
    (hF : ∀ (n : ℕ) (s : polynomialReductionSubalgebra σ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m))),
      polynomialReduction σ
          (fun m => (AdicCompletion.evalₐ J m : AdicCompletion J T →+* T ⧸ J ^ m)) n (F s) =
        MvPolynomial.map
          (Ideal.quotientMap (J ^ n) f
            ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow f n)))
          (polynomialReduction σ
            (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s)) :
    F = completedRestrictedCoeffMap σ I J f hf := by
  apply RingHom.ext
  intro s
  apply polynomialReductionSubalgebra.ext σ _
  intro d
  apply AdicCompletion.ext_evalₐ
  intro n
  have hrow := (hF n s).trans
    (polynomialReduction_completedRestrictedCoeffMap σ I J f hf n s).symm
  simpa only [coeff_polynomialReduction, AlgHom.coe_toRingHom] using
    congrArg (fun p : MvPolynomial σ (T ⧸ J ^ n) => p.coeff d) hrow

/-- Coefficient change and arbitrary variable renaming on restricted series.
The construction is coefficientwise change followed by the completed direct-sum
renaming map; it does not use the polynomial-completion dictionary. -/
def completedRestrictedMap {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ) :
    polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) →+*
      polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n)) :=
  (completedRestrictedRename J g).toRingHom.comp (completedRestrictedCoeffMap σ I J f hf)

/-- Apply coefficient change and then renaming. -/
theorem completedRestrictedMap_apply {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ)
    (s : polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) :
    completedRestrictedMap I J f hf g s =
      completedRestrictedRename J g (completedRestrictedCoeffMap σ I J f hf s) :=
  rfl

/-- At every raw precision, the joint map is polynomial coefficient change
followed by polynomial renaming. -/
@[simp]
theorem polynomialReduction_completedRestrictedMap {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ)
    (n : ℕ) (s : polynomialReductionSubalgebra σ
      (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m))) :
    polynomialReduction τ
        (fun m => (AdicCompletion.evalₐ J m : AdicCompletion J T →+* T ⧸ J ^ m)) n
        (completedRestrictedMap I J f hf g s) =
      MvPolynomial.rename g
        (MvPolynomial.map (Ideal.quotientMap (J ^ n) f
          ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow f n)))
          (polynomialReduction σ
            (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s)) := by
  rw [completedRestrictedMap_apply, polynomialReduction_completedRestrictedRename,
    polynomialReduction_completedRestrictedCoeffMap]

open Classical in
/-- A joint-map coefficient at raw precision is the finite sum over the source
row support. Terms killed by coefficient change may remain in this finite sum. -/
theorem coeff_completedRestrictedMap_eval {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ)
    (n : ℕ) (s : polynomialReductionSubalgebra σ
      (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)))
    (b : τ →₀ ℕ) :
    AdicCompletion.evalₐ J n (coeff b (completedRestrictedMap I J f hf g s).val) =
      ∑ d ∈ (polynomialReduction σ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s).support.filter
          (fun d => Finsupp.mapDomain g d = b),
        Ideal.quotientMap (J ^ n) f
          ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow f n))
          (AdicCompletion.evalₐ I n (coeff d s.val)) := by
  have hrow := congrArg (fun p : MvPolynomial τ (T ⧸ J ^ n) => p.coeff b)
    (polynomialReduction_completedRestrictedMap I J f hf g n s)
  rw [coeff_polynomialReduction, ← MvPolynomial.map_rename,
    MvPolynomial.coeff_map] at hrow
  have hrename := congrArg (fun p : MvPolynomial τ (R ⧸ I ^ n) => p.coeff b)
    (polynomialReduction_completedRestrictedRename I g n s)
  rw [coeff_polynomialReduction] at hrename
  simp only [AlgHom.coe_toRingHom] at hrow hrename
  rw [← hrename, coeff_completedRestrictedRename_eval, map_sum] at hrow
  exact hrow

/-- Coefficient change commutes with arbitrary completed renaming as ring maps.
The equality follows from the corresponding polynomial-row square. -/
theorem completedRestrictedCoeffMap_comp_completedRestrictedRename
    {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ) :
    (completedRestrictedCoeffMap τ I J f hf).comp
        (completedRestrictedRename I g).toRingHom =
      (completedRestrictedRename J g).toRingHom.comp
        (completedRestrictedCoeffMap σ I J f hf) := by
  apply RingHom.ext
  intro s
  apply (polynomialReduction_jointly_injective_iff τ
    (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n))).2
      (fun a b h => AdicCompletion.ext_evalₐ (fun n => congrFun h n))
  funext n
  change polynomialReduction τ
      (fun m => (AdicCompletion.evalₐ J m : AdicCompletion J T →+* T ⧸ J ^ m)) n
      (completedRestrictedCoeffMap τ I J f hf (completedRestrictedRename I g s)) =
    polynomialReduction τ
      (fun m => (AdicCompletion.evalₐ J m : AdicCompletion J T →+* T ⧸ J ^ m)) n
      (completedRestrictedRename J g (completedRestrictedCoeffMap σ I J f hf s))
  simp only [polynomialReduction_completedRestrictedCoeffMap,
    polynomialReduction_completedRestrictedRename, MvPolynomial.map_rename]

/-- The identity coefficient map and identity variable map induce the identity. -/
@[simp]
theorem completedRestrictedMap_id {σ : Type uσ} (I : Ideal R) :
    completedRestrictedMap I I (RingHom.id R) (by intro r hr; exact hr) (id : σ → σ) =
      RingHom.id (polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) := by
  apply RingHom.ext
  intro s
  simp only [completedRestrictedMap_apply, completedRestrictedCoeffMap_id,
    RingHom.id_apply, completedRestrictedRename_id, AlgHom.id_apply]

/-- Joint restricted-series maps compose in the order of coefficient and variable maps. -/
theorem completedRestrictedMap_comp {U : Type uU} [CommRing U]
    {σ : Type uσ} {τ : Type uτ} {υ : Type uυ}
    (I : Ideal R) (J : Ideal T) (L : Ideal U) (f : R →+* T) (k : T →+* U)
    (hf : I ≤ J.comap f) (hk : J ≤ L.comap k) (g : σ → τ) (h : τ → υ) :
    (completedRestrictedMap J L k hk h).comp (completedRestrictedMap I J f hf g) =
      completedRestrictedMap I L (k.comp f) (by intro r hr; exact hk (hf hr)) (h ∘ g) := by
  apply RingHom.ext
  intro s
  simp only [RingHom.comp_apply, completedRestrictedMap_apply]
  have hcomm := RingHom.congr_fun
    (completedRestrictedCoeffMap_comp_completedRestrictedRename J L k hk g)
    (completedRestrictedCoeffMap σ I J f hf s)
  change completedRestrictedCoeffMap τ J L k hk
      (completedRestrictedRename J g (completedRestrictedCoeffMap σ I J f hf s)) =
    completedRestrictedRename L g
      (completedRestrictedCoeffMap σ J L k hk (completedRestrictedCoeffMap σ I J f hf s)) at hcomm
  rw [hcomm]
  have hcoeff := RingHom.congr_fun (completedRestrictedCoeffMap_comp σ I J L f k hf hk) s
  change completedRestrictedCoeffMap σ J L k hk (completedRestrictedCoeffMap σ I J f hf s) =
    completedRestrictedCoeffMap σ I L (k.comp f) (by intro r hr; exact hk (hf hr)) s at hcoeff
  have hrename := AlgHom.congr_fun (completedRestrictedRename_comp L g h)
    (completedRestrictedCoeffMap σ J L k hk (completedRestrictedCoeffMap σ I J f hf s))
  change completedRestrictedRename L h
      (completedRestrictedRename L g
        (completedRestrictedCoeffMap σ J L k hk (completedRestrictedCoeffMap σ I J f hf s))) =
    completedRestrictedRename L (h ∘ g)
      (completedRestrictedCoeffMap σ J L k hk (completedRestrictedCoeffMap σ I J f hf s)) at hrename
  exact hrename.trans (congrArg (completedRestrictedRename L (h ∘ g)) hcoeff)

/-- The joint map commutes with polynomial inclusion over the completed rings. -/
@[simp]
theorem completedRestrictedMap_polynomial {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ)
    (p : MvPolynomial σ (AdicCompletion I R)) :
    completedRestrictedMap I J f hf g
        (polynomialToReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) p) =
      polynomialToReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n))
        (MvPolynomial.rename g (MvPolynomial.map (AdicCompletion.mapRingHom I J f hf) p)) := by
  rw [completedRestrictedMap_apply, completedRestrictedCoeffMap_polynomial,
    completedRestrictedRename_polynomial]

/-- For original polynomials, coefficients and variables may be mapped before
including the polynomial in the completed-coefficient restricted series. -/
theorem completedRestrictedMap_original_polynomial {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ)
    (p : MvPolynomial σ R) :
    completedRestrictedMap I J f hf g
        (polynomialToReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
          (MvPolynomial.map (algebraMap R (AdicCompletion I R)) p)) =
      polynomialToReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n))
        (MvPolynomial.map (algebraMap T (AdicCompletion J T))
          (MvPolynomial.rename g (MvPolynomial.map f p))) := by
  rw [completedRestrictedMap_apply, completedRestrictedCoeffMap_original_polynomial,
    completedRestrictedRename_original_polynomial]

/-- Each polynomial variable is sent to the variable indexed by its image. -/
theorem completedRestrictedMap_X {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ) (i : σ) :
    completedRestrictedMap I J f hf g
        (polynomialToReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
          (MvPolynomial.X i)) =
      polynomialToReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n))
        (MvPolynomial.X (g i)) := by
  rw [completedRestrictedMap_polynomial, MvPolynomial.map_X, MvPolynomial.rename_X]

/-- Included constant polynomials are changed by the completed coefficient map. -/
theorem completedRestrictedMap_C {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ)
    (a : AdicCompletion I R) :
    completedRestrictedMap I J f hf g
        (polynomialToReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))
          (MvPolynomial.C a)) =
      polynomialToReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n))
        (MvPolynomial.C (AdicCompletion.mapRingHom I J f hf a)) := by
  rw [completedRestrictedMap_polynomial, MvPolynomial.map_C, MvPolynomial.rename_C]

/-- Constants are transported through the exact completed coefficient map. -/
@[simp]
theorem completedRestrictedMap_algebraMap {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ)
    (a : AdicCompletion I R) :
    completedRestrictedMap I J f hf g
        (algebraMap (AdicCompletion I R) (polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) a) =
      algebraMap (AdicCompletion J T) (polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n)))
        (AdicCompletion.mapRingHom I J f hf a) := by
  rw [completedRestrictedMap_apply, completedRestrictedCoeffMap_algebraMap,
    completedRestrictedRename_algebraMap]

/-- The completed scalar square for the joint map, as a whole ring-map equality. -/
theorem completedRestrictedMap_comp_algebraMap {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ) :
    (completedRestrictedMap I J f hf g).comp
        (algebraMap (AdicCompletion I R) (polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)))) =
      (algebraMap (AdicCompletion J T) (polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n)))).comp
        (AdicCompletion.mapRingHom I J f hf) := by
  apply RingHom.ext
  intro a
  exact completedRestrictedMap_algebraMap I J f hf g a

/-- Original constants are mapped by the original coefficient homomorphism. -/
theorem completedRestrictedMap_algebraMap_of {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ) (r : R) :
    completedRestrictedMap I J f hf g
        (algebraMap (AdicCompletion I R) (polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)))
          (AdicCompletion.of I R r)) =
      algebraMap (AdicCompletion J T) (polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n)))
        (AdicCompletion.of J T (f r)) := by
  rw [completedRestrictedMap_algebraMap, AdicCompletion.mapRingHom_of]

/-- The joint map is compatible with scalars through the completed coefficient
homomorphism, using the stock source and target coefficient algebras. -/
theorem completedRestrictedMap_smul {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ)
    (a : AdicCompletion I R) (s : polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) :
    completedRestrictedMap I J f hf g (a • s) =
      AdicCompletion.mapRingHom I J f hf a • completedRestrictedMap I J f hf g s := by
  simp only [Algebra.smul_def, map_mul, completedRestrictedMap_algebraMap]

open Classical in
/-- A target row has support contained in the monomial image of the source
row support. Coefficient change and colliding monomials may shrink support. -/
theorem support_polynomialReduction_completedRestrictedMap_subset
    {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ)
    (n : ℕ) (s : polynomialReductionSubalgebra σ
      (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m))) :
    (polynomialReduction τ
        (fun m => (AdicCompletion.evalₐ J m : AdicCompletion J T →+* T ⧸ J ^ m)) n
        (completedRestrictedMap I J f hf g s)).support ⊆
      (polynomialReduction σ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s).support.image
          (Finsupp.mapDomain g) := by
  rw [polynomialReduction_completedRestrictedMap]
  intro b hb
  obtain ⟨d, hd, hcoeff⟩ := MvPolynomial.coeff_rename_ne_zero g _ b
    (MvPolynomial.mem_support_iff.1 hb)
  refine Finset.mem_image.2 ⟨d, MvPolynomial.mem_support_iff.2 ?_, hd⟩
  intro hz
  apply hcoeff
  rw [MvPolynomial.coeff_map, hz, map_zero]

/-- Vanishing in a source raw row implies vanishing in the corresponding target row. -/
theorem ker_polynomialReduction_le_comap_completedRestrictedMap
    {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ) (n : ℕ) :
    RingHom.ker (polynomialReduction σ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n) ≤
      (RingHom.ker (polynomialReduction τ
        (fun m => (AdicCompletion.evalₐ J m : AdicCompletion J T →+* T ⧸ J ^ m)) n)).comap
        (completedRestrictedMap I J f hf g) := by
  intro s hs
  change polynomialReduction σ
    (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s = 0 at hs
  change polynomialReduction τ
    (fun m => (AdicCompletion.evalₐ J m : AdicCompletion J T →+* T ⧸ J ^ m)) n
    (completedRestrictedMap I J f hf g s) = 0
  rw [polynomialReduction_completedRestrictedMap, hs, map_zero, map_zero]

/-- The raw-row squares uniquely determine the joint ring homomorphism. -/
theorem eq_completedRestrictedMap {σ : Type uσ} {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ)
    (F : polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)) →+*
      polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n)))
    (hF : ∀ (n : ℕ) (s : polynomialReductionSubalgebra σ
        (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m))),
      polynomialReduction τ
          (fun m => (AdicCompletion.evalₐ J m : AdicCompletion J T →+* T ⧸ J ^ m)) n (F s) =
        MvPolynomial.rename g
          (MvPolynomial.map (Ideal.quotientMap (J ^ n) f
            ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow f n)))
            (polynomialReduction σ
              (fun m => (AdicCompletion.evalₐ I m : AdicCompletion I R →+* R ⧸ I ^ m)) n s))) :
    F = completedRestrictedMap I J f hf g := by
  apply RingHom.ext
  intro s
  apply (polynomialReduction_jointly_injective_iff τ
    (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n))).2
      (fun a b h => AdicCompletion.ext_evalₐ (fun n => congrFun h n))
  funext n
  exact (hF n s).trans (polynomialReduction_completedRestrictedMap I J f hf g n s).symm

end MvPowerSeries

namespace MvPolynomial

variable {R : Type uR} {T : Type uT} [CommRing R] [CommRing T]
variable {σ : Type uσ}

private theorem adicCompletionEquiv_coeff_naturality
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) :
    (@AlgEquiv.toRingEquiv (AdicCompletion J T)
      (AdicCompletion (J.map (C : T →+* MvPolynomial σ T)) (MvPolynomial σ T))
      (MvPowerSeries.polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ J n :
          AdicCompletion J T →+* T ⧸ J ^ n)))
      (CommRing.toCommSemiring (α := AdicCompletion J T))
      (CommRing.toCommSemiring
        (α := AdicCompletion (J.map (C : T →+* MvPolynomial σ T))
          (MvPolynomial σ T))).toSemiring
      (Subalgebra.toSemiring
        (MvPowerSeries.polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ J n :
            AdicCompletion J T →+* T ⧸ J ^ n))))
      (AdicCompletion.extendedAlgebra (T := MvPolynomial σ T) J :
        Algebra (AdicCompletion J T)
          (AdicCompletion (J.map (C : T →+* MvPolynomial σ T)) (MvPolynomial σ T)))
      (Subalgebra.algebra
        (MvPowerSeries.polynomialReductionSubalgebra σ
          (fun n => (AdicCompletion.evalₐ J n :
            AdicCompletion J T →+* T ⧸ J ^ n))))
      (adicCompletionEquiv σ J)).toRingHom.comp
        (adicCompletionMap I J f hf (id : σ → σ)) =
      (MvPowerSeries.completedRestrictedCoeffMap σ I J f hf).comp
        (@AlgEquiv.toRingEquiv (AdicCompletion I R)
          (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* R ⧸ I ^ n)))
          (CommRing.toCommSemiring (α := AdicCompletion I R))
          (CommRing.toCommSemiring
            (α := AdicCompletion (I.map (C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R))).toSemiring
          (Subalgebra.toSemiring
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* R ⧸ I ^ n))))
          (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
            Algebra (AdicCompletion I R)
              (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)))
          (Subalgebra.algebra
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* R ⧸ I ^ n))))
          (adicCompletionEquiv σ I)).toRingHom := by
  let _ : Algebra (AdicCompletion I R)
      (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :=
    AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I
  let _ : Algebra (AdicCompletion J T)
      (AdicCompletion (J.map (C : T →+* MvPolynomial σ T)) (MvPolynomial σ T)) :=
    AdicCompletion.extendedAlgebra (T := MvPolynomial σ T) J
  apply RingHom.ext
  intro x
  apply (MvPowerSeries.polynomialReduction_jointly_injective_iff σ
    (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n))).2
      (fun a b h => AdicCompletion.ext_evalₐ (fun n => congrFun h n))
  funext n
  -- Instantiate the public row equations directly: the named source algebra
  -- has an `algebraMap` ideal head, while the stored equivalence uses `C`.
  exact (polynomialReduction_adicCompletionEquiv (σ := σ) J n
    (adicCompletionMap I J f hf id x)).trans
      ((adicPolynomialLevelEquiv_evalₐ_adicCompletionMap I J f hf id n x).trans
        ((rename_id_apply _).trans
          ((congrArg (map (Ideal.quotientMap (J ^ n) f
            ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow f n))))
            (polynomialReduction_adicCompletionEquiv (σ := σ) I n x).symm).trans
              (MvPowerSeries.polynomialReduction_completedRestrictedCoeffMap σ I J f hf n
                ((adicCompletionEquiv σ I).toEquiv x)).symm)))

/-- The completed-coefficient dictionary commutes with coefficient change and
arbitrary variable maps on every completed polynomial. The two maps are
constructed independently, and equality follows by comparing all raw rows. -/
theorem adicCompletionEquiv_naturality {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ) :
    (@AlgEquiv.toRingEquiv (AdicCompletion J T)
      (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T))
      (MvPowerSeries.polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ J n :
          AdicCompletion J T →+* T ⧸ J ^ n)))
      (CommRing.toCommSemiring (α := AdicCompletion J T))
      (CommRing.toCommSemiring
        (α := AdicCompletion (J.map (C : T →+* MvPolynomial τ T))
          (MvPolynomial τ T))).toSemiring
      (Subalgebra.toSemiring
        (MvPowerSeries.polynomialReductionSubalgebra τ
          (fun n => (AdicCompletion.evalₐ J n :
            AdicCompletion J T →+* T ⧸ J ^ n))))
      (AdicCompletion.extendedAlgebra (T := MvPolynomial τ T) J :
        Algebra (AdicCompletion J T)
          (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T)))
      (Subalgebra.algebra
        (MvPowerSeries.polynomialReductionSubalgebra τ
          (fun n => (AdicCompletion.evalₐ J n :
            AdicCompletion J T →+* T ⧸ J ^ n))))
      (adicCompletionEquiv τ J)).toRingHom.comp (adicCompletionMap I J f hf g) =
      (MvPowerSeries.completedRestrictedMap I J f hf g).comp
        (@AlgEquiv.toRingEquiv (AdicCompletion I R)
          (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* R ⧸ I ^ n)))
          (CommRing.toCommSemiring (α := AdicCompletion I R))
          (CommRing.toCommSemiring
            (α := AdicCompletion (I.map (C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R))).toSemiring
          (Subalgebra.toSemiring
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* R ⧸ I ^ n))))
          (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
            Algebra (AdicCompletion I R)
              (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)))
          (Subalgebra.algebra
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* R ⧸ I ^ n))))
          (adicCompletionEquiv σ I)).toRingHom := by
  let _ : Algebra (AdicCompletion I R)
      (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :=
    AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I
  let _ : Algebra (AdicCompletion J T)
      (AdicCompletion (J.map (C : T →+* MvPolynomial σ T)) (MvPolynomial σ T)) :=
    AdicCompletion.extendedAlgebra (T := MvPolynomial σ T) J
  let _ : Algebra (AdicCompletion J T)
      (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T)) :=
    AdicCompletion.extendedAlgebra (T := MvPolynomial τ T) J
  apply RingHom.ext
  intro x
  have hrename : (adicCompletionEquiv τ J).toEquiv (adicCompletionMap I J f hf g x) =
      MvPowerSeries.completedRestrictedRename J g
        ((adicCompletionEquiv σ J).toEquiv (adicCompletionMap I J f hf id x)) := by
    apply (MvPowerSeries.polynomialReduction_jointly_injective_iff τ
      (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n))).2
        (fun a b h => AdicCompletion.ext_evalₐ (fun n => congrFun h n))
    funext n
    have hrow := (polynomialReduction_adicCompletionEquiv (σ := σ) J n
      (adicCompletionMap I J f hf id x)).trans
        ((adicPolynomialLevelEquiv_evalₐ_adicCompletionMap I J f hf id n x).trans
          (rename_id_apply _))
    exact (polynomialReduction_adicCompletionEquiv (σ := τ) J n
      (adicCompletionMap I J f hf g x)).trans
        ((adicPolynomialLevelEquiv_evalₐ_adicCompletionMap I J f hf g n x).trans
          ((congrArg (rename g) hrow.symm).trans
            (MvPowerSeries.polynomialReduction_completedRestrictedRename J g n
              ((adicCompletionEquiv σ J).toEquiv (adicCompletionMap I J f hf id x))).symm))
  exact hrename.trans (congrArg (MvPowerSeries.completedRestrictedRename J g)
    (RingHom.congr_fun (adicCompletionEquiv_coeff_naturality I J f hf) x))

/-- Apply dictionary naturality to an arbitrary completed polynomial. -/
theorem adicCompletionEquiv_naturality_apply {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ)
    (x : AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :
    @DFunLike.coe _ _ _
        (@AlgEquiv.instFunLike (AdicCompletion J T)
          (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T))
          (MvPowerSeries.polynomialReductionSubalgebra τ
            (fun n => (AdicCompletion.evalₐ J n :
              AdicCompletion J T →+* T ⧸ J ^ n)))
          (CommRing.toCommSemiring (α := AdicCompletion J T))
          (CommRing.toCommSemiring
            (α := AdicCompletion (J.map (C : T →+* MvPolynomial τ T))
              (MvPolynomial τ T))).toSemiring
          (Subalgebra.toSemiring
            (MvPowerSeries.polynomialReductionSubalgebra τ
              (fun n => (AdicCompletion.evalₐ J n :
                AdicCompletion J T →+* T ⧸ J ^ n))))
          (AdicCompletion.extendedAlgebra (T := MvPolynomial τ T) J :
            Algebra (AdicCompletion J T)
              (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T)))
          (Subalgebra.algebra
            (MvPowerSeries.polynomialReductionSubalgebra τ
              (fun n => (AdicCompletion.evalₐ J n :
                AdicCompletion J T →+* T ⧸ J ^ n)))))
        (adicCompletionEquiv τ J) (adicCompletionMap I J f hf g x) =
      MvPowerSeries.completedRestrictedMap I J f hf g
        (@DFunLike.coe _ _ _
          (@AlgEquiv.instFunLike (AdicCompletion I R)
            (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* R ⧸ I ^ n)))
            (CommRing.toCommSemiring (α := AdicCompletion I R))
            (CommRing.toCommSemiring
              (α := AdicCompletion (I.map (C : R →+* MvPolynomial σ R))
                (MvPolynomial σ R))).toSemiring
            (Subalgebra.toSemiring
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* R ⧸ I ^ n))))
            (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
              Algebra (AdicCompletion I R)
                (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)))
            (Subalgebra.algebra
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* R ⧸ I ^ n)))))
          (adicCompletionEquiv σ I) x) :=
  RingHom.congr_fun (adicCompletionEquiv_naturality I J f hf g) x

/-- Inverse dictionary naturality is a consequence of the forward square and
bijectivity, not another construction of the restricted-series map. -/
theorem adicCompletionEquiv_symm_naturality {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ) :
    (@AlgEquiv.toRingEquiv (AdicCompletion J T)
      (MvPowerSeries.polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ J n :
          AdicCompletion J T →+* T ⧸ J ^ n)))
      (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T))
      (CommRing.toCommSemiring (α := AdicCompletion J T))
      (Subalgebra.toSemiring
        (MvPowerSeries.polynomialReductionSubalgebra τ
          (fun n => (AdicCompletion.evalₐ J n :
            AdicCompletion J T →+* T ⧸ J ^ n))))
      (CommRing.toCommSemiring
        (α := AdicCompletion (J.map (C : T →+* MvPolynomial τ T))
          (MvPolynomial τ T))).toSemiring
      (Subalgebra.algebra
        (MvPowerSeries.polynomialReductionSubalgebra τ
          (fun n => (AdicCompletion.evalₐ J n :
            AdicCompletion J T →+* T ⧸ J ^ n))))
      (AdicCompletion.extendedAlgebra (T := MvPolynomial τ T) J :
        Algebra (AdicCompletion J T)
          (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T)))
      (@AlgEquiv.symm (AdicCompletion J T)
        (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T))
        (MvPowerSeries.polynomialReductionSubalgebra τ
          (fun n => (AdicCompletion.evalₐ J n :
            AdicCompletion J T →+* T ⧸ J ^ n)))
        (CommRing.toCommSemiring (α := AdicCompletion J T))
        (CommRing.toCommSemiring
          (α := AdicCompletion (J.map (C : T →+* MvPolynomial τ T))
            (MvPolynomial τ T))).toSemiring
        (Subalgebra.toSemiring
          (MvPowerSeries.polynomialReductionSubalgebra τ
            (fun n => (AdicCompletion.evalₐ J n :
              AdicCompletion J T →+* T ⧸ J ^ n))))
        (AdicCompletion.extendedAlgebra (T := MvPolynomial τ T) J :
          Algebra (AdicCompletion J T)
            (AdicCompletion (J.map (C : T →+* MvPolynomial τ T))
              (MvPolynomial τ T)))
        (Subalgebra.algebra
          (MvPowerSeries.polynomialReductionSubalgebra τ
            (fun n => (AdicCompletion.evalₐ J n :
              AdicCompletion J T →+* T ⧸ J ^ n))))
        (adicCompletionEquiv τ J))).toRingHom.comp
        (MvPowerSeries.completedRestrictedMap I J f hf g) =
      (adicCompletionMap I J f hf g).comp
        (@AlgEquiv.toRingEquiv (AdicCompletion I R)
          (MvPowerSeries.polynomialReductionSubalgebra σ
            (fun n => (AdicCompletion.evalₐ I n :
              AdicCompletion I R →+* R ⧸ I ^ n)))
          (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
          (CommRing.toCommSemiring (α := AdicCompletion I R))
          (Subalgebra.toSemiring
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* R ⧸ I ^ n))))
          (CommRing.toCommSemiring
            (α := AdicCompletion (I.map (C : R →+* MvPolynomial σ R))
              (MvPolynomial σ R))).toSemiring
          (Subalgebra.algebra
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* R ⧸ I ^ n))))
          (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
            Algebra (AdicCompletion I R)
              (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)))
          (@AlgEquiv.symm (AdicCompletion I R)
            (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* R ⧸ I ^ n)))
            (CommRing.toCommSemiring (α := AdicCompletion I R))
            (CommRing.toCommSemiring
              (α := AdicCompletion (I.map (C : R →+* MvPolynomial σ R))
                (MvPolynomial σ R))).toSemiring
            (Subalgebra.toSemiring
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* R ⧸ I ^ n))))
            (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
              Algebra (AdicCompletion I R)
                (AdicCompletion (I.map (C : R →+* MvPolynomial σ R))
                  (MvPolynomial σ R)))
            (Subalgebra.algebra
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* R ⧸ I ^ n))))
            (adicCompletionEquiv σ I))).toRingHom := by
  -- Project the stored equivalences with their five fixed class values before
  -- taking inverses, so no new algebra is synthesized for either completion.
  let eI := @AlgEquiv.toEquiv (AdicCompletion I R)
    (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
    (MvPowerSeries.polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)))
    (CommRing.toCommSemiring (α := AdicCompletion I R))
    (CommRing.toCommSemiring
      (α := AdicCompletion (I.map (C : R →+* MvPolynomial σ R))
        (MvPolynomial σ R))).toSemiring
    (Subalgebra.toSemiring
      (MvPowerSeries.polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))))
    (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
      Algebra (AdicCompletion I R)
        (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)))
    (Subalgebra.algebra
      (MvPowerSeries.polynomialReductionSubalgebra σ
        (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))))
    (adicCompletionEquiv σ I)
  let eJ := @AlgEquiv.toEquiv (AdicCompletion J T)
    (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T))
    (MvPowerSeries.polynomialReductionSubalgebra τ
      (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n)))
    (CommRing.toCommSemiring (α := AdicCompletion J T))
    (CommRing.toCommSemiring
      (α := AdicCompletion (J.map (C : T →+* MvPolynomial τ T))
        (MvPolynomial τ T))).toSemiring
    (Subalgebra.toSemiring
      (MvPowerSeries.polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n))))
    (AdicCompletion.extendedAlgebra (T := MvPolynomial τ T) J :
      Algebra (AdicCompletion J T)
        (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T)))
    (Subalgebra.algebra
      (MvPowerSeries.polynomialReductionSubalgebra τ
        (fun n => (AdicCompletion.evalₐ J n : AdicCompletion J T →+* T ⧸ J ^ n))))
    (adicCompletionEquiv τ J)
  apply RingHom.ext
  intro s
  exact eJ.symm_apply_eq.mpr
    ((adicCompletionEquiv_naturality_apply I J f hf g (eI.symm s)).trans
      (congrArg (MvPowerSeries.completedRestrictedMap I J f hf g)
        (eI.apply_symm_apply s))).symm

/-- Apply inverse dictionary naturality to a restricted series. -/
theorem adicCompletionEquiv_symm_naturality_apply {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f) (g : σ → τ)
    (s : MvPowerSeries.polynomialReductionSubalgebra σ
      (fun n => (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n))) :
    @DFunLike.coe _ _ _
        (@AlgEquiv.instFunLike (AdicCompletion J T)
          (MvPowerSeries.polynomialReductionSubalgebra τ
            (fun n => (AdicCompletion.evalₐ J n :
              AdicCompletion J T →+* T ⧸ J ^ n)))
          (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T))
          (CommRing.toCommSemiring (α := AdicCompletion J T))
          (Subalgebra.toSemiring
            (MvPowerSeries.polynomialReductionSubalgebra τ
              (fun n => (AdicCompletion.evalₐ J n :
                AdicCompletion J T →+* T ⧸ J ^ n))))
          (CommRing.toCommSemiring
            (α := AdicCompletion (J.map (C : T →+* MvPolynomial τ T))
              (MvPolynomial τ T))).toSemiring
          (Subalgebra.algebra
            (MvPowerSeries.polynomialReductionSubalgebra τ
              (fun n => (AdicCompletion.evalₐ J n :
                AdicCompletion J T →+* T ⧸ J ^ n))))
          (AdicCompletion.extendedAlgebra (T := MvPolynomial τ T) J :
            Algebra (AdicCompletion J T)
              (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T))))
        (@AlgEquiv.symm (AdicCompletion J T)
          (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T))
          (MvPowerSeries.polynomialReductionSubalgebra τ
            (fun n => (AdicCompletion.evalₐ J n :
              AdicCompletion J T →+* T ⧸ J ^ n)))
          (CommRing.toCommSemiring (α := AdicCompletion J T))
          (CommRing.toCommSemiring
            (α := AdicCompletion (J.map (C : T →+* MvPolynomial τ T))
              (MvPolynomial τ T))).toSemiring
          (Subalgebra.toSemiring
            (MvPowerSeries.polynomialReductionSubalgebra τ
              (fun n => (AdicCompletion.evalₐ J n :
                AdicCompletion J T →+* T ⧸ J ^ n))))
          (AdicCompletion.extendedAlgebra (T := MvPolynomial τ T) J :
            Algebra (AdicCompletion J T)
              (AdicCompletion (J.map (C : T →+* MvPolynomial τ T))
                (MvPolynomial τ T)))
          (Subalgebra.algebra
            (MvPowerSeries.polynomialReductionSubalgebra τ
              (fun n => (AdicCompletion.evalₐ J n :
                AdicCompletion J T →+* T ⧸ J ^ n))))
          (adicCompletionEquiv τ J))
        (MvPowerSeries.completedRestrictedMap I J f hf g s) =
      adicCompletionMap I J f hf g
        (@DFunLike.coe _ _ _
          (@AlgEquiv.instFunLike (AdicCompletion I R)
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* R ⧸ I ^ n)))
            (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
            (CommRing.toCommSemiring (α := AdicCompletion I R))
            (Subalgebra.toSemiring
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* R ⧸ I ^ n))))
            (CommRing.toCommSemiring
              (α := AdicCompletion (I.map (C : R →+* MvPolynomial σ R))
                (MvPolynomial σ R))).toSemiring
            (Subalgebra.algebra
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* R ⧸ I ^ n))))
            (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
              Algebra (AdicCompletion I R)
                (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))))
          (@AlgEquiv.symm (AdicCompletion I R)
            (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
            (MvPowerSeries.polynomialReductionSubalgebra σ
              (fun n => (AdicCompletion.evalₐ I n :
                AdicCompletion I R →+* R ⧸ I ^ n)))
            (CommRing.toCommSemiring (α := AdicCompletion I R))
            (CommRing.toCommSemiring
              (α := AdicCompletion (I.map (C : R →+* MvPolynomial σ R))
                (MvPolynomial σ R))).toSemiring
            (Subalgebra.toSemiring
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* R ⧸ I ^ n))))
            (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
              Algebra (AdicCompletion I R)
                (AdicCompletion (I.map (C : R →+* MvPolynomial σ R))
                  (MvPolynomial σ R)))
            (Subalgebra.algebra
              (MvPowerSeries.polynomialReductionSubalgebra σ
                (fun n => (AdicCompletion.evalₐ I n :
                  AdicCompletion I R →+* R ⧸ I ^ n))))
            (adicCompletionEquiv σ I)) s) :=
  RingHom.congr_fun (adicCompletionEquiv_symm_naturality I J f hf g) s

section CompletedScalars

-- This is the named value, with the polynomial coefficient ideal in `C` normal form.
private abbrev polynomialCompletionExtendedAlgebra {S : Type uU} [CommRing S]
    {ι : Type uυ} (K : Ideal S) :
    Algebra (AdicCompletion K S)
      (AdicCompletion (K.map (C : S →+* MvPolynomial ι S)) (MvPolynomial ι S)) :=
  (AdicCompletion.extendedAlgebra (T := MvPolynomial ι S) K :
    Algebra (AdicCompletion K S)
      (AdicCompletion (K.map (C : S →+* MvPolynomial ι S)) (MvPolynomial ι S)))

attribute [local instance] polynomialCompletionExtendedAlgebra

/-- The polynomial completion map preserves scalar multiplication along the
completed coefficient map, for the named extended-coefficient algebra actions. -/
theorem adicCompletionMap_smul {τ : Type uτ}
    (I : Ideal R) (J : Ideal T) (f : R →+* T) (hf : I ≤ J.comap f)
    (g : σ → τ) (a : AdicCompletion I R)
    (x : AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) :
    adicCompletionMap I J f hf g
        (@SMul.smul (AdicCompletion I R)
          (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
          (@Algebra.toSMul (AdicCompletion I R)
            (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
            (CommRing.toCommSemiring (α := AdicCompletion I R))
            (CommRing.toCommSemiring
              (α := AdicCompletion (I.map (C : R →+* MvPolynomial σ R))
                (MvPolynomial σ R))).toSemiring
            (AdicCompletion.extendedAlgebra (T := MvPolynomial σ R) I :
              Algebra (AdicCompletion I R)
                (AdicCompletion (I.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))))
          a x) =
      @SMul.smul (AdicCompletion J T)
        (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T))
        (@Algebra.toSMul (AdicCompletion J T)
          (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T))
          (CommRing.toCommSemiring (α := AdicCompletion J T))
          (CommRing.toCommSemiring
            (α := AdicCompletion (J.map (C : T →+* MvPolynomial τ T))
              (MvPolynomial τ T))).toSemiring
          (AdicCompletion.extendedAlgebra (T := MvPolynomial τ T) J :
            Algebra (AdicCompletion J T)
              (AdicCompletion (J.map (C : T →+* MvPolynomial τ T)) (MvPolynomial τ T))))
        (AdicCompletion.mapRingHom I J f hf a) (adicCompletionMap I J f hf g x) := by
  change adicCompletionMap I J f hf g
      (AdicCompletion.mapRingHom I (I.map (C : R →+* MvPolynomial σ R))
        (C : R →+* MvPolynomial σ R) Ideal.le_comap_map a * x) =
    AdicCompletion.mapRingHom J (J.map (C : T →+* MvPolynomial τ T))
      (C : T →+* MvPolynomial τ T) Ideal.le_comap_map
      (AdicCompletion.mapRingHom I J f hf a) * adicCompletionMap I J f hf g x
  exact adicCompletionMap_completedCoefficient_mul I J f hf g a x

end CompletedScalars

end MvPolynomial
