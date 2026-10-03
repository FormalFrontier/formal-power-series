/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc

public section

/-!
# Coefficients in a distinguished variable

Globally restricted series regroup injectively into power series with
restricted coefficient series. Finite polynomials of restricted coefficient
series embed in the reverse direction.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {R τ : Type*} [CommRing R] (I : Ideal R)

/-- The coefficient in the distinguished `none` variable is restricted in all
the remaining variables. Extraction is additive, not multiplicative. -/
noncomputable def restrictedFirstCoeff (n : ℕ) :
    adicallyRestrictedSubring (σ := Option τ) I →+
      adicallyRestrictedSubring (σ := τ) I where
  toFun f := ⟨PowerSeries.coeff n (optionEquivLeft τ R f), by
    apply (mem_adicallyRestrictedSubring I _).2
    intro k
    have hfinite := ((mem_adicallyRestrictedSubring I
      (f : MvPowerSeries (Option τ) R)).1 f.property) k
    have hinj : Function.Injective (fun β : τ →₀ ℕ => β.optionElim n) := by
      intro β γ h
      have hs := congrArg Finsupp.some h
      simpa only [Finsupp.some_optionElim] using hs
    have hpre : ((fun β : τ →₀ ℕ => β.optionElim n) ⁻¹'
        {α : Option τ →₀ ℕ | coeff α (f : MvPowerSeries (Option τ) R) ∉ I ^ k}).Finite :=
      Set.Finite.preimage hinj.injOn hfinite
    convert hpre using 1
    ext β
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, coeff_coeff_optionEquivLeft]⟩
  map_zero' := by
    apply Subtype.ext
    simp only [map_zero, Subring.coe_zero]
  map_add' f g := by
    apply Subtype.ext
    simp only [map_add, Subring.coe_add]

theorem coeff_restrictedFirstCoeff (f : adicallyRestrictedSubring (σ := Option τ) I)
    (n : ℕ) (β : τ →₀ ℕ) :
    coeff β (restrictedFirstCoeff I n f : MvPowerSeries τ R) =
      coeff (β.optionElim n) (f : MvPowerSeries (Option τ) R) :=
  coeff_coeff_optionEquivLeft ..

/-- Forgetting the restriction on the coefficient ring recovers the raw regrouping. -/
theorem map_restrictedFirstRegroup_raw
    (f : adicallyRestrictedSubring (σ := Option τ) I) :
    PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := τ) I))
        (PowerSeries.mk (fun n => restrictedFirstCoeff I n f)) =
      optionEquivLeft τ R f := by
  apply PowerSeries.ext
  intro n
  apply MvPowerSeries.ext
  intro β
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk,
    Subring.coe_subtype, coeff_restrictedFirstCoeff, coeff_coeff_optionEquivLeft]

/-- Regroup an ideal-adically restricted series by its distinguished first variable.
This map is injective, but is generally not surjective onto iterated power series. -/
noncomputable def restrictedFirstRegroup :
    adicallyRestrictedSubring (σ := Option τ) I →+*
      PowerSeries (adicallyRestrictedSubring (σ := τ) I) where
  toFun f := PowerSeries.mk (fun n => restrictedFirstCoeff I n f)
  map_zero' := by
    apply PowerSeries.map_injective
      (Subring.subtype (adicallyRestrictedSubring (σ := τ) I)) Subtype.coe_injective
    change PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := τ) I))
        (PowerSeries.mk (fun n => restrictedFirstCoeff I n 0)) =
      PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := τ) I)) 0
    rw [map_restrictedFirstRegroup_raw]
    simp
  map_one' := by
    apply PowerSeries.map_injective
      (Subring.subtype (adicallyRestrictedSubring (σ := τ) I)) Subtype.coe_injective
    change PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := τ) I))
        (PowerSeries.mk (fun n => restrictedFirstCoeff I n 1)) =
      PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := τ) I)) 1
    rw [map_restrictedFirstRegroup_raw]
    simp
  map_add' f g := by
    apply PowerSeries.map_injective
      (Subring.subtype (adicallyRestrictedSubring (σ := τ) I)) Subtype.coe_injective
    change PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := τ) I))
        (PowerSeries.mk (fun n => restrictedFirstCoeff I n (f + g))) =
      PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := τ) I))
        (PowerSeries.mk (fun n => restrictedFirstCoeff I n f) +
         PowerSeries.mk (fun n => restrictedFirstCoeff I n g))
    rw [map_restrictedFirstRegroup_raw, map_add,
      map_restrictedFirstRegroup_raw, map_restrictedFirstRegroup_raw]
    simp
  map_mul' f g := by
    apply PowerSeries.map_injective
      (Subring.subtype (adicallyRestrictedSubring (σ := τ) I)) Subtype.coe_injective
    change PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := τ) I))
        (PowerSeries.mk (fun n => restrictedFirstCoeff I n (f * g))) =
      PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := τ) I))
        (PowerSeries.mk (fun n => restrictedFirstCoeff I n f) *
         PowerSeries.mk (fun n => restrictedFirstCoeff I n g))
    rw [map_restrictedFirstRegroup_raw, map_mul,
      map_restrictedFirstRegroup_raw, map_restrictedFirstRegroup_raw]
    simp

@[simp]
theorem coeff_restrictedFirstRegroup
    (f : adicallyRestrictedSubring (σ := Option τ) I) (n : ℕ) :
    PowerSeries.coeff n (restrictedFirstRegroup I f) = restrictedFirstCoeff I n f := by
  change PowerSeries.coeff n (PowerSeries.mk (fun m => restrictedFirstCoeff I m f)) = _
  exact PowerSeries.coeff_mk ..

theorem restrictedFirstRegroup_injective :
    Function.Injective (restrictedFirstRegroup (τ := τ) I) := by
  intro f g h
  apply Subtype.ext
  apply (optionEquivLeft τ R).injective
  have heq := congrArg
    (PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := τ) I))) h
  change PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := τ) I))
      (PowerSeries.mk (fun n => restrictedFirstCoeff I n f)) =
    PowerSeries.map (Subring.subtype (adicallyRestrictedSubring (σ := τ) I))
      (PowerSeries.mk (fun n => restrictedFirstCoeff I n g)) at heq
  simpa only [map_restrictedFirstRegroup_raw] using heq

private noncomputable def polynomialRestrictedFirstRaw :
    Polynomial (adicallyRestrictedSubring (σ := τ) I) →+*
      MvPowerSeries (Option τ) R :=
  (optionEquivLeft τ R).symm.toRingHom.comp
    ((Polynomial.coeToPowerSeries.ringHom).comp
      (Polynomial.mapRingHom (Subring.subtype (adicallyRestrictedSubring (σ := τ) I))))

private theorem coeff_polynomialRestrictedFirstRaw
    (P : Polynomial (adicallyRestrictedSubring (σ := τ) I))
    (n : ℕ) (β : τ →₀ ℕ) :
    coeff (β.optionElim n) (polynomialRestrictedFirstRaw I P) =
      coeff β (P.coeff n : MvPowerSeries τ R) := by
  have h := coeff_coeff_optionEquivLeft (polynomialRestrictedFirstRaw I P) n β
  have hraw : optionEquivLeft τ R (polynomialRestrictedFirstRaw I P) =
      ((P.map (Subring.subtype (adicallyRestrictedSubring (σ := τ) I)) :
        Polynomial (MvPowerSeries τ R)) : PowerSeries (MvPowerSeries τ R)) := by
    simp [polynomialRestrictedFirstRaw, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_mapRingHom]
  rw [hraw] at h
  simpa only [Polynomial.coeff_coe, Polynomial.coeff_map, Subring.coe_subtype] using h.symm

/-- Finite polynomial sums of restricted coefficient series are globally restricted. -/
private theorem isAdicallyRestricted_polynomialRestrictedFirstRaw
    (P : Polynomial (adicallyRestrictedSubring (σ := τ) I)) :
    IsAdicallyRestricted I (polynomialRestrictedFirstRaw I P) := by
  intro k
  let bad (n : ℕ) : Set (τ →₀ ℕ) :=
    {β | coeff β (P.coeff n : MvPowerSeries τ R) ∉ I ^ k}
  have hbad (n : ℕ) : (bad n).Finite := by
    exact ((mem_adicallyRestrictedSubring I
      (P.coeff n : MvPowerSeries τ R)).1 (P.coeff n).property) k
  have hfinite :
      (⋃ n ∈ (P.support : Set ℕ),
        (fun β : τ →₀ ℕ => β.optionElim n) '' bad n).Finite :=
    P.support.finite_toSet.biUnion (fun n _ => (hbad n).image _)
  refine hfinite.subset ?_
  intro α hα
  let n := α none
  let β := α.some
  have hcoeff : coeff α (polynomialRestrictedFirstRaw I P) =
      coeff β (P.coeff n : MvPowerSeries τ R) := by
    simpa only [n, β, Finsupp.optionElim_some] using
      coeff_polynomialRestrictedFirstRaw I P n β
  have hn : n ∈ P.support := by
    by_contra hnot
    have hz : P.coeff n = 0 := Polynomial.notMem_support_iff.mp hnot
    apply hα
    simpa only [hcoeff, hz, Subring.coe_zero, coeff_zero] using
      (I ^ k).zero_mem
  apply Set.mem_iUnion.mpr
  refine ⟨n, Set.mem_iUnion.mpr ⟨hn, ?_⟩⟩
  change ∃ γ : τ →₀ ℕ, γ ∈ bad n ∧ γ.optionElim n = α
  have hβ : β ∈ bad n := by
    change coeff β (P.coeff n : MvPowerSeries τ R) ∉ I ^ k
    rw [← hcoeff]
    exact hα
  exact ⟨β, hβ, Finsupp.optionElim_some α⟩

/-- Embed a finite polynomial in the first variable, with restricted series
coefficients in all remaining variables, into the globally restricted series. -/
noncomputable def polynomialRestrictedFirst :
    Polynomial (adicallyRestrictedSubring (σ := τ) I) →+*
      adicallyRestrictedSubring (σ := Option τ) I :=
  (polynomialRestrictedFirstRaw I).codRestrict _ (fun P =>
    (mem_adicallyRestrictedSubring I _).2
      (isAdicallyRestricted_polynomialRestrictedFirstRaw I P))

@[simp]
theorem coeff_polynomialRestrictedFirst
    (P : Polynomial (adicallyRestrictedSubring (σ := τ) I))
    (n : ℕ) (β : τ →₀ ℕ) :
    coeff (β.optionElim n)
        (polynomialRestrictedFirst I P : MvPowerSeries (Option τ) R) =
      coeff β (P.coeff n : MvPowerSeries τ R) :=
  coeff_polynomialRestrictedFirstRaw I P n β

@[simp]
theorem restrictedFirstCoeff_polynomialRestrictedFirst
    (P : Polynomial (adicallyRestrictedSubring (σ := τ) I)) (n : ℕ) :
    restrictedFirstCoeff I n (polynomialRestrictedFirst I P) = P.coeff n := by
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro β
  exact (coeff_restrictedFirstCoeff I _ n β).trans
    (coeff_polynomialRestrictedFirst I P n β)

@[simp]
theorem restrictedFirstRegroup_polynomialRestrictedFirst
    (P : Polynomial (adicallyRestrictedSubring (σ := τ) I)) :
    restrictedFirstRegroup I (polynomialRestrictedFirst I P) =
      (P : PowerSeries (adicallyRestrictedSubring (σ := τ) I)) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_restrictedFirstRegroup, restrictedFirstCoeff_polynomialRestrictedFirst,
    Polynomial.coeff_coe]

theorem polynomialRestrictedFirst_injective :
    Function.Injective (polynomialRestrictedFirst (τ := τ) I) := by
  intro P Q h
  apply Polynomial.coe_injective (adicallyRestrictedSubring (σ := τ) I)
  simpa only [restrictedFirstRegroup_polynomialRestrictedFirst] using
    congrArg (restrictedFirstRegroup I) h

/-- A restricted series is a degree-`< d` polynomial in the first variable
exactly when all its first-variable coefficients from `d` onward vanish. -/
theorem restrictedFirst_actual_support_iff
    (f : adicallyRestrictedSubring (σ := Option τ) I) (d : ℕ) :
    (∀ (n : ℕ) (β : τ →₀ ℕ), d ≤ n →
      coeff (β.optionElim n) (f : MvPowerSeries (Option τ) R) = 0) ↔
      ∃! P : Polynomial (adicallyRestrictedSubring (σ := τ) I),
        P.degree < (d : WithBot ℕ) ∧ polynomialRestrictedFirst I P = f := by
  constructor
  · intro h
    have hImage : polynomialRestrictedFirst I
        (PowerSeries.trunc d (restrictedFirstRegroup I f)) = f := by
      apply restrictedFirstRegroup_injective I
      rw [restrictedFirstRegroup_polynomialRestrictedFirst]
      apply PowerSeries.ext
      intro n
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs with hn
      · rfl
      · have hzero : restrictedFirstCoeff I n f = 0 := by
          apply Subtype.ext
          apply MvPowerSeries.ext
          intro β
          simpa only [coeff_restrictedFirstCoeff I f n β, Subring.coe_zero, coeff_zero] using
            h n β (Nat.le_of_not_gt hn)
        simp only [coeff_restrictedFirstRegroup, hzero]
    refine ⟨_, ⟨PowerSeries.degree_trunc_lt _ _, hImage⟩, ?_⟩
    intro Q hQ
    exact polynomialRestrictedFirst_injective I (hQ.2.trans hImage.symm)
  · rintro ⟨P, ⟨hdegree, hP⟩, _⟩ n β hn
    rw [← hP, coeff_polynomialRestrictedFirst]
    have hz : P.coeff n = 0 := (Polynomial.degree_lt_iff_coeff_zero P d).mp hdegree n hn
    simp only [hz, Subring.coe_zero, coeff_zero]

end MvPowerSeries
