/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LeadingTerm

set_option warningAsError true

namespace Tests.MvPowerSeries.IdealAdicRestricted.LeadingTerm

open _root_.MvPowerSeries

private theorem zero_for_arbitrary_variables {σ R : Type*}
    [CommRing R] [IsDomain R] [ValuationRing R]
    (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R) :
    μ.restrictedLeadingExponent a ham
      (0 : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) = 0 ∧
    μ.restrictedLeadingTerm a ham
      (0 : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) = 0 := by
  simp

private theorem primitive_unit_constant {σ R : Type*}
    [CommRing R] [IsDomain R] [ValuationRing R]
    (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R) (u : Rˣ) :
    ∃ z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}),
      IsUnit (coeff (μ.restrictedLeadingExponent a ham z) (z : MvPowerSeries σ R)) := by
  let z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) :=
    polynomialToRestricted (Ideal.span {a}) (MvPolynomial.C (u : R))
  have hc : coeff (0 : σ →₀ ℕ) (z : MvPowerSeries σ R) = (u : R) := by
    simp [z, polynomialToRestricted_coe]
  have hunit : IsUnit (coeff (0 : σ →₀ ℕ) (z : MvPowerSeries σ R)) := by
    rw [hc]
    exact u.isUnit
  have hprim : Ideal.span (Set.range
      (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have hmem : (1 : R) ∈ Ideal.span
        {coeff (0 : σ →₀ ℕ) (z : MvPowerSeries σ R)} :=
      Ideal.mem_span_singleton.mpr (isUnit_iff_dvd_one.mp hunit)
    exact (Ideal.span_mono
      (Set.singleton_subset_iff.mpr (Set.mem_range_self (0 : σ →₀ ℕ)))) hmem
  exact ⟨z, μ.isUnit_restrictedLeadingCoefficient_of_primitive a ham z hprim⟩

private theorem empty_variables {R : Type*}
    [CommRing R] [IsDomain R] [ValuationRing R]
    (μ : MonomialOrder (Fin 0)) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R) (u : Rˣ) :
    ∃ z : adicallyRestrictedSubring (σ := Fin 0) (Ideal.span {a}),
      μ.restrictedLeadingTerm a ham
        (0 : adicallyRestrictedSubring (σ := Fin 0) (Ideal.span {a})) = 0 ∧
      IsUnit (coeff (μ.restrictedLeadingExponent a ham z)
        (z : MvPowerSeries (Fin 0) R)) := by
  obtain ⟨z, hz⟩ := primitive_unit_constant μ a ham u
  exact ⟨z, by simp, hz⟩

/-- The leading exponent agrees with the degree of a matching residue polynomial. -/
public theorem residue_polynomial_interface {σ R : Type*}
    [CommRing R] [IsDomain R] [ValuationRing R]
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
    μ.restrictedLeadingExponent a ham z = μ.degree p :=
  μ.restrictedLeadingExponent_eq_degree_of_primitive_reduction a ham z hprim p hpcoeff

private theorem leading_term_ideal_member {σ R : Type*}
    [CommRing R] [IsDomain R] [ValuationRing R]
    (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (J : Ideal (adicallyRestrictedSubring (σ := σ) (Ideal.span {a})))
    (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) (hz : z ∈ J) :
    μ.restrictedLeadingTerm a ham z ∈ μ.restrictedLeadingTermIdeal a ham J :=
  μ.restrictedLeadingTerm_mem_ideal a ham J hz

end Tests.MvPowerSeries.IdealAdicRestricted.LeadingTerm
