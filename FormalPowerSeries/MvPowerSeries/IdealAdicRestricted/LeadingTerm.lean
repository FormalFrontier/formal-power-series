/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.SelectedFactor
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.IdealChange
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

public section

/-!
# Intrinsic leading terms of restricted power series

For a separated principal-adically restricted series over a valuation domain,
normalize by an actual content-generating coefficient before taking the
polynomial reduction at the maximal ideal. The resulting leading exponent is
independent of the admissible content-factor choice. Leading terms themselves
have coefficients in the original ring, not in its residue field.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

/-- Choose an actual coefficient generating the coefficient-content ideal of
a restricted series, together with a restricted factor normalized at that
coefficient. No nonzero-parameter or completeness assumption is needed. -/
theorem exists_restricted_content_factor (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    ∃ (j : σ →₀ ℕ)
      (h : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})),
      Ideal.span (Set.range (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) =
        Ideal.span {coeff j (z : MvPowerSeries σ R)} ∧
      (z : MvPowerSeries σ R) =
        C (coeff j (z : MvPowerSeries σ R)) * (h : MvPowerSeries σ R) ∧
      coeff j (h : MvPowerSeries σ R) = 1 := by
  have hz : IsAdicallyRestricted (Ideal.span {a}) (z : MvPowerSeries σ R) :=
    (mem_adicallyRestrictedSubring _ _).mp z.property
  obtain ⟨j, hj⟩ :=
    IsAdicallyRestricted.exists_span_range_eq_span_coeff
      (Ideal.span {a}) (z : MvPowerSeries σ R) hz
  obtain ⟨h, hh, hfactor, hnorm⟩ :=
    IsAdicallyRestricted.exists_selected_coeff_factor
      (Ideal.span {a}) (z : MvPowerSeries σ R) hz j hj
  exact ⟨j, ⟨h, (mem_adicallyRestrictedSubring _ _).mpr hh⟩, hj, hfactor, hnorm⟩

/-- An index whose actual coefficient generates the content of a restricted series. -/
noncomputable def restrictedContentIndex (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) : σ →₀ ℕ :=
  Classical.choose (exists_restricted_content_factor a z)

/-- The restricted factor normalized at `restrictedContentIndex`. -/
noncomputable def restrictedContentFactor (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) :=
  Classical.choose (Classical.choose_spec (exists_restricted_content_factor a z))

/-- The chosen content coefficient and normalized restricted factor satisfy
the actual coefficient-content and factorization identities. -/
theorem restrictedContentFactor_spec (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    Ideal.span (Set.range (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) =
      Ideal.span {coeff (restrictedContentIndex a z) (z : MvPowerSeries σ R)} ∧
    (z : MvPowerSeries σ R) =
      C (coeff (restrictedContentIndex a z) (z : MvPowerSeries σ R)) *
        (restrictedContentFactor a z : MvPowerSeries σ R) ∧
    coeff (restrictedContentIndex a z)
      (restrictedContentFactor a z : MvPowerSeries σ R) = 1 := by
  simpa only [restrictedContentIndex, restrictedContentFactor] using
    Classical.choose_spec (Classical.choose_spec (exists_restricted_content_factor a z))

/-- A nonzero restricted series has a nonzero selected content coefficient. -/
theorem restrictedContentCoefficient_ne_zero (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    {z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})} (hz : z ≠ 0) :
    coeff (restrictedContentIndex a z) (z : MvPowerSeries σ R) ≠ 0 := by
  intro hc
  have hfactor := (restrictedContentFactor_spec a z).2.1
  have hzraw : (z : MvPowerSeries σ R) = 0 := by
    rw [hfactor, hc]
    simp
  apply hz
  apply Subtype.ext
  simpa using hzraw

private theorem parameter_le_maximalIdeal (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R) :
    Ideal.span {a} ≤ IsLocalRing.maximalIdeal R :=
  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ham)

/-- The genuine polynomial reduction of a restricted series at the maximal
ideal. Its finite support comes from restriction at `(a) ≤ m`; no finiteness
condition on the variables is imposed. -/
noncomputable def restrictedResidue (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    MvPolynomial σ (R ⧸ IsLocalRing.maximalIdeal R) := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  have hz : IsAdicallyRestricted (Ideal.span {a}) (z : MvPowerSeries σ R) :=
    (mem_adicallyRestrictedSubring _ _).mp z.property
  have hzm : (z : MvPowerSeries σ R) ∈ adicallyRestrictedSubring m :=
    (mem_adicallyRestrictedSubring _ _).mpr
      (hz.mono (parameter_le_maximalIdeal a ham))
  exact MvPolynomial.map (Ideal.Quotient.factor (le_of_eq (Submodule.pow_one m)))
    (adicReduction m 1 ⟨z, hzm⟩)

/-- Every coefficient of the maximal-ideal polynomial reduction is the
original coefficient modulo `m`, rather than modulo a silently identified
quotient by `m ^ 1`. -/
@[simp] theorem coeff_restrictedResidue (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) (d : σ →₀ ℕ) :
    (restrictedResidue a ham z).coeff d =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
        (coeff d (z : MvPowerSeries σ R)) := by
  simp only [restrictedResidue, MvPolynomial.coeff_map, coeff_adicReduction,
    Ideal.Quotient.factor_mk]

/-- A normalized restricted factor has nonzero polynomial reduction at the
maximal ideal, even when the variable type is empty. -/
theorem restrictedResidue_ne_zero_of_coeff_one (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (h : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (j : σ →₀ ℕ) (hj : coeff j (h : MvPowerSeries σ R) = 1) :
    restrictedResidue a ham h ≠ 0 := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  have hm : m ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hone : (Ideal.Quotient.mk m (1 : R)) ≠ 0 := by
    intro hzero
    exact hm ((Ideal.eq_top_iff_one m).mpr
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero))
  intro hzero
  have hc := coeff_restrictedResidue a ham h j
  rw [hj, hzero] at hc
  exact hone (by simpa using hc.symm)

/-- The coefficient of a normalized factor at the degree of its nonzero
residue polynomial is a unit of the original valuation domain. -/
theorem isUnit_coeff_degree_restrictedResidue (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (μ : MonomialOrder σ)
    (h : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hp : restrictedResidue a ham h ≠ 0) :
    IsUnit (coeff (μ.degree (restrictedResidue a ham h)) (h : MvPowerSeries σ R)) := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  have hc : (restrictedResidue a ham h).coeff
      (μ.degree (restrictedResidue a ham h)) ≠ 0 :=
    (μ.leadingCoeff_ne_zero_iff).mpr hp
  have hnot : coeff (μ.degree (restrictedResidue a ham h))
      (h : MvPowerSeries σ R) ∉ m := by
    intro hmem
    exact hc (by rw [coeff_restrictedResidue]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  exact not_not.mp (by simpa only [m, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff] using hnot)

omit [IsDomain R] [ValuationRing R] in
/-- A coefficient that generates the content of a nonzero series is nonzero. -/
theorem coeff_ne_zero_of_generates_content (a : R)
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) (hz : z ≠ 0)
    (j : σ →₀ ℕ)
    (hj : Ideal.span (Set.range (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) =
      Ideal.span {coeff j (z : MvPowerSeries σ R)}) :
    coeff j (z : MvPowerSeries σ R) ≠ 0 := by
  intro hc
  have hall (d : σ →₀ ℕ) : coeff d (z : MvPowerSeries σ R) = 0 := by
    have hd : coeff d (z : MvPowerSeries σ R) ∈
        Ideal.span {coeff j (z : MvPowerSeries σ R)} := by
      rw [← hj]
      exact Ideal.subset_span (Set.mem_range_self d)
    have hbot : Ideal.span {coeff j (z : MvPowerSeries σ R)} = (⊥ : Ideal R) :=
      Ideal.span_singleton_eq_bot.mpr hc
    simpa only [hbot, Submodule.mem_bot] using hd
  apply hz
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro d
  simpa using hall d

omit [ValuationRing R] in
/-- Any two nonzero actual content-generating coefficients of a restricted
series differ by a unit. This does not concern arbitrary quotient choices. -/
theorem content_generators_associated (a : R)
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) (hz : z ≠ 0)
    (j j' : σ →₀ ℕ)
    (hj : Ideal.span (Set.range (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) =
      Ideal.span {coeff j (z : MvPowerSeries σ R)})
    (hj' : Ideal.span (Set.range (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) =
      Ideal.span {coeff j' (z : MvPowerSeries σ R)}) :
    ∃ u : Rˣ, coeff j' (z : MvPowerSeries σ R) =
      coeff j (z : MvPowerSeries σ R) * (u : R) := by
  let c := coeff j (z : MvPowerSeries σ R)
  let c' := coeff j' (z : MvPowerSeries σ R)
  have hc : c ≠ 0 := coeff_ne_zero_of_generates_content a z hz j hj
  have hc'div : c' ∣ c := Ideal.mem_span_singleton.mp (by
    rw [← hj']
    exact Ideal.subset_span (Set.mem_range_self j))
  have hcdiv : c ∣ c' := Ideal.mem_span_singleton.mp (by
    rw [← hj]
    exact Ideal.subset_span (Set.mem_range_self j'))
  obtain ⟨u, hu⟩ := hcdiv
  obtain ⟨v, hv⟩ := hc'div
  have huv : u * v = (1 : R) := by
    apply mul_left_cancel₀ hc
    calc
      c * (u * v) = (c * u) * v := (mul_assoc c u v).symm
      _ = c' * v := by rw [hu]
      _ = c := hv.symm
      _ = c * 1 := (mul_one c).symm
  have hunit : IsUnit u := isUnit_iff_dvd_one.mpr ⟨v, huv.symm⟩
  refine ⟨hunit.unit, ?_⟩
  calc
    c' = c * u := hu
    _ = c * (hunit.unit : R) := by rw [hunit.unit_spec]

/-- Polynomial reductions of any two admissible content factors have the
same residue support. Their normalizing coefficients need not be equal. -/
theorem restrictedResidue_support_eq_of_content_factors (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) (hz : z ≠ 0)
    (j j' : σ →₀ ℕ)
    (h h' : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hj : Ideal.span (Set.range (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) =
      Ideal.span {coeff j (z : MvPowerSeries σ R)})
    (hj' : Ideal.span (Set.range (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) =
      Ideal.span {coeff j' (z : MvPowerSeries σ R)})
    (hfactor : (z : MvPowerSeries σ R) =
      C (coeff j (z : MvPowerSeries σ R)) * (h : MvPowerSeries σ R))
    (hfactor' : (z : MvPowerSeries σ R) =
      C (coeff j' (z : MvPowerSeries σ R)) * (h' : MvPowerSeries σ R)) :
    (restrictedResidue a ham h).support = (restrictedResidue a ham h').support := by
  let c := coeff j (z : MvPowerSeries σ R)
  let c' := coeff j' (z : MvPowerSeries σ R)
  have hc : c ≠ 0 := coeff_ne_zero_of_generates_content a z hz j hj
  have hc' : c' ≠ 0 := coeff_ne_zero_of_generates_content a z hz j' hj'
  obtain ⟨u, hu⟩ := content_generators_associated a z hz j j' hj hj'
  change c' = c * (u : R) at hu
  have hdiv : c' ∣ c := Ideal.mem_span_singleton.mp (by
    rw [← hj']
    exact Ideal.subset_span (Set.mem_range_self j))
  obtain ⟨v, hv⟩ := hdiv
  have hcoeff (d : σ →₀ ℕ) :
      coeff d (h : MvPowerSeries σ R) = (u : R) * coeff d (h' : MvPowerSeries σ R) := by
    apply mul_left_cancel₀ hc
    calc
      c * coeff d (h : MvPowerSeries σ R) = coeff d (z : MvPowerSeries σ R) := by
        rw [hfactor, coeff_C_mul]
      _ = c' * coeff d (h' : MvPowerSeries σ R) := by
        rw [hfactor', coeff_C_mul]
      _ = c * ((u : R) * coeff d (h' : MvPowerSeries σ R)) := by
        rw [hu, mul_assoc]
  have hcoeff' (d : σ →₀ ℕ) :
      coeff d (h' : MvPowerSeries σ R) = v * coeff d (h : MvPowerSeries σ R) := by
    apply mul_left_cancel₀ hc'
    calc
      c' * coeff d (h' : MvPowerSeries σ R) = coeff d (z : MvPowerSeries σ R) := by
        rw [hfactor', coeff_C_mul]
      _ = c * coeff d (h : MvPowerSeries σ R) := by
        rw [hfactor, coeff_C_mul]
      _ = c' * (v * coeff d (h : MvPowerSeries σ R)) := by
        rw [hv, mul_assoc]
  have hscale (d : σ →₀ ℕ) :
      (restrictedResidue a ham h).coeff d =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (u : R) *
          (restrictedResidue a ham h').coeff d := by
    simp only [coeff_restrictedResidue, hcoeff, map_mul]
  have hscale' (d : σ →₀ ℕ) :
      (restrictedResidue a ham h').coeff d =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) v *
          (restrictedResidue a ham h).coeff d := by
    simp only [coeff_restrictedResidue, hcoeff', map_mul]
  apply Finset.ext
  intro d
  simp only [MvPolynomial.mem_support_iff]
  constructor
  · intro hd hzero
    apply hd
    rw [hscale d, hzero, mul_zero]
  · intro hd hzero
    apply hd
    rw [hscale' d, hzero, mul_zero]

/-- The monomial-order degree of a content-normalized residue polynomial is
independent of every admissible content-factor choice. -/
theorem restrictedResidue_degree_eq_of_content_factors (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R) (μ : MonomialOrder σ)
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) (hz : z ≠ 0)
    (j j' : σ →₀ ℕ)
    (h h' : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hj : Ideal.span (Set.range (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) =
      Ideal.span {coeff j (z : MvPowerSeries σ R)})
    (hj' : Ideal.span (Set.range (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) =
      Ideal.span {coeff j' (z : MvPowerSeries σ R)})
    (hfactor : (z : MvPowerSeries σ R) =
      C (coeff j (z : MvPowerSeries σ R)) * (h : MvPowerSeries σ R))
    (hfactor' : (z : MvPowerSeries σ R) =
      C (coeff j' (z : MvPowerSeries σ R)) * (h' : MvPowerSeries σ R)) :
    μ.degree (restrictedResidue a ham h) = μ.degree (restrictedResidue a ham h') := by
  have hs := restrictedResidue_support_eq_of_content_factors a ham z hz j j' h h'
    hj hj' hfactor hfactor'
  simp only [MonomialOrder.degree, hs]

end MvPowerSeries

namespace MonomialOrder

open MvPowerSeries

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

/-- The intrinsic leading exponent of a principal-adically restricted series:
first divide by a selected content-generating coefficient, then take the
degree of its nonzero polynomial reduction at the maximal ideal. Zero has
exponent zero by convention. -/
noncomputable def restrictedLeadingExponent (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) : σ →₀ ℕ := by
  classical
  exact if z = 0 then 0 else μ.degree (restrictedResidue a ham (restrictedContentFactor a z))

/-- The leading term is a polynomial monomial with the *actual* `R`-valued
coefficient of the series, not its residue coefficient. Zero has term zero. -/
noncomputable def restrictedLeadingTerm (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) : MvPolynomial σ R := by
  classical
  exact if z = 0 then 0 else
    MvPolynomial.monomial (μ.restrictedLeadingExponent a ham z)
      (coeff (μ.restrictedLeadingExponent a ham z) (z : MvPowerSeries σ R))

/-- The polynomial ideal generated by actual leading terms of members of a
restricted-series ideal; its coefficient ring is `R`, not `R ⧸ m`, and it is
distinct from the ideal of restricted series. -/
noncomputable def restrictedLeadingTermIdeal (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (J : Ideal (adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))) :
    Ideal (MvPolynomial σ R) :=
  Ideal.span ((μ.restrictedLeadingTerm a ham) '' (J : Set _))

/-- The explicit zero convention for the intrinsic exponent. -/
@[simp] theorem restrictedLeadingExponent_zero (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R) :
    μ.restrictedLeadingExponent a ham
      (0 : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) = 0 := by
  simp [restrictedLeadingExponent]

/-- The explicit zero convention for the actual-coefficient leading term. -/
@[simp] theorem restrictedLeadingTerm_zero (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R) :
    μ.restrictedLeadingTerm a ham
      (0 : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) = 0 := by
  simp [restrictedLeadingTerm]

/-- The leading term of a nonzero restricted series retains its actual
coefficient in the original ring. -/
theorem restrictedLeadingTerm_eq_monomial_of_ne_zero
    (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    {z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})} (hz : z ≠ 0) :
    μ.restrictedLeadingTerm a ham z =
      MvPolynomial.monomial (μ.restrictedLeadingExponent a ham z)
        (coeff (μ.restrictedLeadingExponent a ham z) (z : MvPowerSeries σ R)) := by
  simp only [restrictedLeadingTerm, ite_eq_right hz]

/-- The leading-term ideal of the zero restricted-series ideal is zero. -/
@[simp] theorem restrictedLeadingTermIdeal_bot
    (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R) :
    μ.restrictedLeadingTermIdeal a ham
      (⊥ : Ideal (adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))) = ⊥ := by
  apply le_antisymm
  · change Ideal.span ((μ.restrictedLeadingTerm a ham) ''
        ((⊥ : Ideal (adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))) : Set _)) ≤ ⊥
    apply Ideal.span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    have hz0 : z = 0 := (Submodule.mem_bot _).mp hz
    subst z
    simp
  · exact bot_le

/-- Any admissible actual content factor computes the chosen intrinsic
leading exponent, not just the factor picked by classical choice. -/
theorem restrictedLeadingExponent_eq_degree_of_content_factor
    (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) (hz : z ≠ 0)
    (j : σ →₀ ℕ)
    (h : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hj : Ideal.span (Set.range (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) =
      Ideal.span {coeff j (z : MvPowerSeries σ R)})
    (hfactor : (z : MvPowerSeries σ R) =
      C (coeff j (z : MvPowerSeries σ R)) * (h : MvPowerSeries σ R)) :
    μ.restrictedLeadingExponent a ham z = μ.degree (restrictedResidue a ham h) := by
  have hc := restrictedContentFactor_spec a z
  have hdegree := restrictedResidue_degree_eq_of_content_factors a ham μ z hz
    (restrictedContentIndex a z) j (restrictedContentFactor a z) h
    hc.1 hj hc.2.1 hfactor
  simpa only [restrictedLeadingExponent, ite_eq_right hz] using hdegree

/-- The chosen content factor of a nonzero series has a nonzero residue
polynomial; its leading coefficient in `R` is therefore a unit. -/
theorem isUnit_restrictedContentFactor_leading_coeff
    (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    IsUnit (coeff (μ.degree (restrictedResidue a ham (restrictedContentFactor a z)))
      (restrictedContentFactor a z : MvPowerSeries σ R)) := by
  have hnormal := (restrictedContentFactor_spec a z).2.2
  exact isUnit_coeff_degree_restrictedResidue a ham μ (restrictedContentFactor a z)
    (restrictedResidue_ne_zero_of_coeff_one a ham (restrictedContentFactor a z)
      (restrictedContentIndex a z) hnormal)

/-- For a nonzero restricted series, the actual coefficient at its intrinsic
leading exponent is nonzero, even if the series reduces to zero modulo `m`. -/
theorem restrictedLeadingCoefficient_ne_zero (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    {z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})} (hz : z ≠ 0) :
    coeff (μ.restrictedLeadingExponent a ham z) (z : MvPowerSeries σ R) ≠ 0 := by
  have hfactor := (restrictedContentFactor_spec a z).2.1
  have hunit := isUnit_restrictedContentFactor_leading_coeff μ a ham z
  have hc := restrictedContentCoefficient_ne_zero a hz
  simp only [restrictedLeadingExponent, ite_eq_right hz]
  rw [hfactor, coeff_C_mul]
  exact mul_ne_zero hc hunit.ne_zero

/-- The actual leading term of a nonzero restricted series is nonzero. -/
theorem restrictedLeadingTerm_ne_zero (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    {z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})} (hz : z ≠ 0) :
    μ.restrictedLeadingTerm a ham z ≠ 0 := by
  intro hzero
  rw [restrictedLeadingTerm, ite_eq_right hz] at hzero
  exact (μ.restrictedLeadingCoefficient_ne_zero a ham hz)
    (MvPolynomial.monomial_eq_zero.mp hzero)

/-- The leading term of every member belongs to its polynomial leading-term
ideal, including the zero series. -/
theorem restrictedLeadingTerm_mem_ideal (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (J : Ideal (adicallyRestrictedSubring (σ := σ) (Ideal.span {a})))
    {z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})} (hz : z ∈ J) :
    μ.restrictedLeadingTerm a ham z ∈ μ.restrictedLeadingTermIdeal a ham J :=
  Ideal.subset_span ⟨z, hz, rfl⟩

/-- If an actual coefficient-content ideal is the unit ideal, the selected
content-generating coefficient is a unit of the original ring. -/
theorem isUnit_restrictedContentCoefficient_of_primitive
    (a : R) [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hprim : Ideal.span (Set.range
      (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) = ⊤) :
    IsUnit (coeff (restrictedContentIndex a z) (z : MvPowerSeries σ R)) := by
  have hc := (restrictedContentFactor_spec a z).1
  have htop : Ideal.span {coeff (restrictedContentIndex a z)
      (z : MvPowerSeries σ R)} = ⊤ := hc.symm.trans hprim
  exact isUnit_iff_dvd_one.mpr
    (Ideal.mem_span_singleton.mp ((Ideal.eq_top_iff_one _).mp htop))

/-- A primitive restricted series has an actual unit leading coefficient. -/
theorem isUnit_restrictedLeadingCoefficient_of_primitive
    (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hprim : Ideal.span (Set.range
      (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) = ⊤) :
    IsUnit (coeff (μ.restrictedLeadingExponent a ham z) (z : MvPowerSeries σ R)) := by
  have hc := isUnit_restrictedContentCoefficient_of_primitive a z hprim
  have hz : z ≠ 0 := by
    intro hzero
    have hc0 : coeff (restrictedContentIndex a z) (z : MvPowerSeries σ R) = 0 := by
      simp [hzero]
    exact hc.ne_zero hc0
  have hh := isUnit_restrictedContentFactor_leading_coeff μ a ham z
  have hfactor := (restrictedContentFactor_spec a z).2.1
  simp only [restrictedLeadingExponent, ite_eq_right hz]
  rw [hfactor, coeff_C_mul]
  exact hc.mul hh

/-- Multiplication by a unit scalar preserves the support of the genuine
maximal-ideal polynomial reductions. The inverse direction is proved
coefficientwise rather than assuming quotient rings are identical. -/
theorem restrictedResidue_support_eq_of_unit_factor
    (a : R) (ham : a ∈ IsLocalRing.maximalIdeal R)
    (z h : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (c : R) (hc : IsUnit c)
    (hfactor : (z : MvPowerSeries σ R) = C c * (h : MvPowerSeries σ R)) :
    (restrictedResidue a ham z).support = (restrictedResidue a ham h).support := by
  obtain ⟨v, hv⟩ := isUnit_iff_dvd_one.mp hc
  have hcoeff (d : σ →₀ ℕ) :
      coeff d (z : MvPowerSeries σ R) = c * coeff d (h : MvPowerSeries σ R) := by
    rw [hfactor, coeff_C_mul]
  have hcoeff' (d : σ →₀ ℕ) :
      coeff d (h : MvPowerSeries σ R) = v * coeff d (z : MvPowerSeries σ R) := by
    calc
      coeff d (h : MvPowerSeries σ R) = (1 : R) * coeff d (h : MvPowerSeries σ R) :=
        (one_mul _).symm
      _ = (c * v) * coeff d (h : MvPowerSeries σ R) := by rw [← hv]
      _ = v * (c * coeff d (h : MvPowerSeries σ R)) := by
        rw [mul_comm c v, mul_assoc]
      _ = v * coeff d (z : MvPowerSeries σ R) := by rw [hcoeff]
  have hscale (d : σ →₀ ℕ) :
      (restrictedResidue a ham z).coeff d =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) c *
          (restrictedResidue a ham h).coeff d := by
    simp only [coeff_restrictedResidue, hcoeff, map_mul]
  have hscale' (d : σ →₀ ℕ) :
      (restrictedResidue a ham h).coeff d =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) v *
          (restrictedResidue a ham z).coeff d := by
    simp only [coeff_restrictedResidue, hcoeff', map_mul]
  apply Finset.ext
  intro d
  simp only [MvPolynomial.mem_support_iff]
  constructor
  · intro hd hzero
    apply hd
    rw [hscale d, hzero, mul_zero]
  · intro hd hzero
    apply hd
    rw [hscale' d, hzero, mul_zero]

/-- For any *actual* polynomial reduction of a primitive restricted series,
identified at every coefficient, its degree is the intrinsic leading
exponent. This interface does not import a division theorem. -/
theorem restrictedLeadingExponent_eq_degree_of_primitive_reduction
    (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hprim : Ideal.span (Set.range
      (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) = ⊤)
    (p : MvPolynomial σ (R ⧸ IsLocalRing.maximalIdeal R))
    (hpcoeff : ∀ d : σ →₀ ℕ, p.coeff d =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
        (coeff d (z : MvPowerSeries σ R))) :
    μ.restrictedLeadingExponent a ham z = μ.degree p := by
  have hc := isUnit_restrictedContentCoefficient_of_primitive a z hprim
  have hz : z ≠ 0 := by
    intro hzero
    have hc0 : coeff (restrictedContentIndex a z) (z : MvPowerSeries σ R) = 0 := by
      simp [hzero]
    exact hc.ne_zero hc0
  have hfactor := (restrictedContentFactor_spec a z).2.1
  have hsupport := restrictedResidue_support_eq_of_unit_factor a ham z
    (restrictedContentFactor a z) _ hc hfactor
  have heq : p = restrictedResidue a ham z := by
    ext d
    rw [hpcoeff d, coeff_restrictedResidue]
  have hdegree : μ.degree (restrictedResidue a ham (restrictedContentFactor a z)) =
      μ.degree (restrictedResidue a ham z) := by
    simp only [MonomialOrder.degree, hsupport]
  rw [restrictedLeadingExponent, ite_eq_right hz]
  calc
    μ.degree (restrictedResidue a ham (restrictedContentFactor a z)) =
        μ.degree (restrictedResidue a ham z) := hdegree
    _ = μ.degree p := by rw [heq]

end MonomialOrder
