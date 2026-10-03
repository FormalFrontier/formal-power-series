/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LeadingTerm
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.ValuationNormalizedDivision
public import Mathlib.RingTheory.MvPolynomial.Ideal

@[expose] public section

/-!
# Primitive standard bases and ideal generation

A finite family of primitive restricted series generates an ideal when its
actual-coefficient polynomial leading terms generate the polynomial leading-term
ideal. The remainder in valuation-normalized division vanishes because its
coefficients vanish on componentwise cones covering the support of its own
leading term. No finite-variable or standard-basis-existence assumption is made.

The intrinsic leading-term module provides the actual-coefficient premise.
-/

set_option warningAsError true

namespace MonomialOrder

open MvPowerSeries
open scoped MonomialOrder

variable {σ ι R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]

private theorem span_primitive_restrictedLeadingTerm_eq_monomial
    (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (g : ι → adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hprim : ∀ i, Ideal.span (Set.range
      (fun d : σ →₀ ℕ => coeff d (g i : MvPowerSeries σ R))) = ⊤) :
    Ideal.span (Set.range (fun i : ι => μ.restrictedLeadingTerm a ham (g i))) =
      Ideal.span ((fun d : σ →₀ ℕ => MvPolynomial.monomial d (1 : R)) ''
        Set.range (fun i : ι => μ.restrictedLeadingExponent a ham (g i))) := by
  classical
  have hunit (i : ι) : IsUnit
      (coeff (μ.restrictedLeadingExponent a ham (g i)) (g i : MvPowerSeries σ R)) :=
    μ.isUnit_restrictedLeadingCoefficient_of_primitive a ham (g i) (hprim i)
  have hnonzero (i : ι) : g i ≠ 0 := by
    intro hzero
    have hc : coeff (μ.restrictedLeadingExponent a ham (g i))
        (g i : MvPowerSeries σ R) = 0 := by simp [hzero]
    exact (hunit i).ne_zero hc
  have hterm (i : ι) : μ.restrictedLeadingTerm a ham (g i) =
      MvPolynomial.monomial (μ.restrictedLeadingExponent a ham (g i))
        (coeff (μ.restrictedLeadingExponent a ham (g i))
          (g i : MvPowerSeries σ R)) := by
    exact μ.restrictedLeadingTerm_eq_monomial_of_ne_zero a ham (hnonzero i)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change μ.restrictedLeadingTerm a ham (g i) ∈
      Ideal.span ((fun d : σ →₀ ℕ => MvPolynomial.monomial d (1 : R)) ''
        Set.range (fun j : ι => μ.restrictedLeadingExponent a ham (g j)))
    have hmonomial : MvPolynomial.monomial
        (μ.restrictedLeadingExponent a ham (g i)) (1 : R) ∈
        Ideal.span ((fun d : σ →₀ ℕ => MvPolynomial.monomial d (1 : R)) ''
          Set.range (fun j : ι => μ.restrictedLeadingExponent a ham (g j))) :=
      Ideal.subset_span ⟨_, ⟨i, rfl⟩, rfl⟩
    simpa only [hterm i, MvPolynomial.C_mul_monomial, mul_one] using
      (Ideal.span ((fun d : σ →₀ ℕ => MvPolynomial.monomial d (1 : R)) ''
        Set.range (fun j : ι => μ.restrictedLeadingExponent a ham (g j)))).mul_mem_left
          (MvPolynomial.C (coeff (μ.restrictedLeadingExponent a ham (g i))
            (g i : MvPowerSeries σ R))) hmonomial
  · apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    change MvPolynomial.monomial (μ.restrictedLeadingExponent a ham (g i)) (1 : R) ∈
      Ideal.span (Set.range (fun j : ι => μ.restrictedLeadingTerm a ham (g j)))
    have hmember : μ.restrictedLeadingTerm a ham (g i) ∈
        Ideal.span (Set.range (fun j : ι => μ.restrictedLeadingTerm a ham (g j))) :=
      Ideal.subset_span (Set.mem_range_self i)
    let unit := hunit i
    have hscale : (↑(unit.unit⁻¹) : R) *
        coeff (μ.restrictedLeadingExponent a ham (g i)) (g i : MvPowerSeries σ R) =
        1 := (unit.unit).inv_mul_of_eq unit.unit_spec
    simpa only [hterm i, MvPolynomial.C_mul_monomial, hscale] using
      (Ideal.span (Set.range (fun j : ι =>
        μ.restrictedLeadingTerm a ham (g j)))).mul_mem_left
          (MvPolynomial.C (↑(unit.unit⁻¹) : R)) hmember

/-- A finite primitive family in a restricted-series ideal generates that ideal
when its actual-coefficient polynomial leading terms generate the polynomial
leading-term ideal. The variable type may be empty or infinite. -/
theorem ideal_eq_span_of_primitive_standardBasis
    [Finite ι] (μ : MonomialOrder σ) (a : R)
    (ha : a ≠ 0) (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal R)
    [IsAdicComplete (Ideal.span {a}) R]
    (J : Ideal (adicallyRestrictedSubring (σ := σ) (Ideal.span {a})))
    (g : ι → adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hgJ : ∀ i, g i ∈ J)
    (hprim : ∀ i, Ideal.span (Set.range
      (fun d : σ →₀ ℕ => coeff d (g i : MvPowerSeries σ R))) = ⊤)
    (hLT : μ.restrictedLeadingTermIdeal a ham J =
      Ideal.span (Set.range (fun i : ι => μ.restrictedLeadingTerm a ham (g i)))) :
    J = Ideal.span (Set.range g) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hspan := μ.span_primitive_restrictedLeadingTerm_eq_monomial a ham g hprim
  have hcone (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
      (hz : z ∈ J) (hnonzero : z ≠ 0) :
      ∃ i : ι, μ.restrictedLeadingExponent a ham (g i) ≤
        μ.restrictedLeadingExponent a ham z := by
    have hc := μ.restrictedLeadingCoefficient_ne_zero a ham hnonzero
    have hsupport : μ.restrictedLeadingExponent a ham z ∈
        (μ.restrictedLeadingTerm a ham z).support := by
      simpa only [μ.restrictedLeadingTerm_eq_monomial_of_ne_zero a ham hnonzero,
        MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial,
        ite_eq_left rfl, ite_true] using hc
    have hmonomial : μ.restrictedLeadingTerm a ham z ∈
        Ideal.span ((fun d : σ →₀ ℕ => MvPolynomial.monomial d (1 : R)) ''
          Set.range (fun i : ι => μ.restrictedLeadingExponent a ham (g i))) := by
      rw [← hspan, ← hLT]
      exact μ.restrictedLeadingTerm_mem_ideal a ham J hz
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ :=
      (MvPolynomial.mem_ideal_span_monomial_image.mp hmonomial) _ hsupport
    exact ⟨i, hi⟩
  have hrestricted (i : ι) : IsAdicallyRestricted (Ideal.span {a})
      (g i : MvPowerSeries σ R) :=
    (mem_adicallyRestrictedSubring _ _).mp (g i).property
  obtain ⟨p, hpcoeff, _hpnonzero, hdivision⟩ :=
    μ.exists_restricted_primitive_division a ha ham hrad
      (fun i => (g i : MvPowerSeries σ R)) hrestricted hprim
  have hpdegree (i : ι) : μ.restrictedLeadingExponent a ham (g i) =
      μ.degree (p i) :=
    μ.restrictedLeadingExponent_eq_degree_of_primitive_reduction a ham
      (g i) (hprim i) (p i) (hpcoeff i)
  apply le_antisymm
  · intro f hf
    obtain ⟨q, r, hq, hr, hdecomposition, hzero⟩ :=
      hdivision (f : MvPowerSeries σ R)
        ((mem_adicallyRestrictedSubring _ _).mp f.property)
    let qs : ι → adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) :=
      fun i => ⟨q i, (mem_adicallyRestrictedSubring _ _).mpr (hq i)⟩
    let rs : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) :=
      ⟨r, (mem_adicallyRestrictedSubring _ _).mpr hr⟩
    have hdecompositionT : f = (∑ i, qs i * g i) + rs := by
      apply Subtype.ext
      change (f : MvPowerSeries σ R) =
        (Subring.subtype (adicallyRestrictedSubring (σ := σ) (Ideal.span {a})))
          ((∑ i, qs i * g i) + rs)
      simpa only [map_add, map_sum, map_mul, Subring.subtype_apply,
        qs, rs, Subtype.coe_mk] using hdecomposition
    have hsumJ : (∑ i, qs i * g i) ∈ J :=
      Ideal.sum_mem _ (fun i _ => J.mul_mem_left (qs i) (hgJ i))
    have hrs : rs ∈ J := by
      have hsub : f - ∑ i, qs i * g i ∈ J := J.sub_mem hf hsumJ
      simpa only [hdecompositionT, add_sub_cancel_left] using hsub
    have hrzero : rs = 0 := by
      by_contra hnonzero
      obtain ⟨i, hi⟩ := hcone rs hrs hnonzero
      have hcoeffzero : coeff (μ.restrictedLeadingExponent a ham rs) r = 0 :=
        hzero _ i (by rw [← hpdegree i]; exact hi)
      exact (μ.restrictedLeadingCoefficient_ne_zero a ham hnonzero) hcoeffzero
    have heq : f = ∑ i, qs i * g i := by
      simpa only [hrzero, add_zero] using hdecompositionT
    rw [heq]
    exact Ideal.sum_mem _ (fun i _ =>
      (Ideal.span (Set.range g)).mul_mem_left (qs i)
        (Ideal.subset_span (Set.mem_range_self i)))
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hgJ i

end MonomialOrder
