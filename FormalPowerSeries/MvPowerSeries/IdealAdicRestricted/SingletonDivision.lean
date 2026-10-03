/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LeadingTerm.Product
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.ValuationNormalizedDivision
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

public section

/-!
# Singleton restricted division

Dividing by one nonzero restricted series has at most one quotient and one
remainder with actual coefficients vanishing on its leading cone. For a
primitive divisor, the published finite-family division theorem also supplies
existence under its normalization and completeness hypotheses.
-/

set_option warningAsError true

namespace MonomialOrder

open MvPowerSeries

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)

/-- Two divisions by one nonzero restricted series have the same quotient and
remainder when the *actual* remainder coefficients vanish on its leading cone. -/
theorem restricted_singleton_division_unique
    (g : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) (hg : g ≠ 0)
    (f q r q' r' : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (h : f = q * g + r) (h' : f = q' * g + r')
    (hr : ∀ index : σ →₀ ℕ, μ.restrictedLeadingExponent a ham g ≤ index →
      coeff index (r : MvPowerSeries σ R) = 0)
    (hr' : ∀ index : σ →₀ ℕ, μ.restrictedLeadingExponent a ham g ≤ index →
      coeff index (r' : MvPowerSeries σ R) = 0) :
    q = q' ∧ r = r' := by
  have hrelation : (q - q') * g = r' - r := by
    apply sub_eq_zero.mp
    calc
      (q - q') * g - (r' - r) = (q * g + r) - (q' * g + r') := by ring
      _ = 0 := by rw [← h, ← h', sub_self]
  by_cases hq : q - q' = 0
  · have hqq : q = q' := sub_eq_zero.mp hq
    subst q'
    constructor
    · rfl
    · have hremainder : r' - r = 0 := by simpa only [sub_self, zero_mul] using hrelation.symm
      exact (sub_eq_zero.mp hremainder).symm
  · obtain ⟨hprod, hdegree⟩ :=
      μ.restrictedLeadingExponent_mul_of_ne_zero a ham (q - q') g hq hg
    have hcone : μ.restrictedLeadingExponent a ham g ≤
        μ.restrictedLeadingExponent a ham ((q - q') * g) := by
      rw [hdegree]
      exact le_add_self
    have hcoeff : coeff (μ.restrictedLeadingExponent a ham ((q - q') * g))
        (((q - q') * g : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
          MvPowerSeries σ R) = 0 := by
      rw [hrelation] at hcone ⊢
      change coeff (μ.restrictedLeadingExponent a ham (r' - r))
        ((r' : MvPowerSeries σ R) - (r : MvPowerSeries σ R)) = 0
      simp only [map_sub, hr' _ hcone, hr _ hcone, sub_self]
    exact (μ.restrictedLeadingCoefficient_ne_zero a ham hprod hcoeff).elim

end MonomialOrder

namespace MonomialOrder

open MvPowerSeries

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    (μ : MonomialOrder σ) (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    [IsAdicComplete (Ideal.span {a} : Ideal R) R]

/-- A primitive restricted divisor has exactly one quotient and remainder with
actual coefficients vanishing on its intrinsic leading cone. Existence retains
the nonzero parameter, radical equality and adic completeness hypotheses of
the published finite-family division theorem. -/
theorem existsUnique_restricted_primitive_singleton_division
    (ha : a ≠ 0)
    (hrad : (Ideal.span {a} : Ideal R).radical = IsLocalRing.maximalIdeal R)
    (g : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hprim : Ideal.span (Set.range (fun index : σ →₀ ℕ =>
      coeff index (g : MvPowerSeries σ R))) = ⊤)
    (f : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})) :
    ∃! qr : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) ×
        adicallyRestrictedSubring (σ := σ) (Ideal.span {a}),
      f = qr.1 * g + qr.2 ∧
        ∀ index : σ →₀ ℕ, μ.restrictedLeadingExponent a ham g ≤ index →
          coeff index (qr.2 : MvPowerSeries σ R) = 0 := by
  classical
  have hg : g ≠ 0 := by
    intro hzero
    have hunit := isUnit_restrictedContentCoefficient_of_primitive a g hprim
    apply hunit.ne_zero
    simp [hzero]
  have hrestricted : IsAdicallyRestricted (Ideal.span {a}) (g : MvPowerSeries σ R) :=
    (mem_adicallyRestrictedSubring _ _).mp g.property
  obtain ⟨p, hcoeff, _, hdivide⟩ :=
    μ.exists_restricted_primitive_division (ι := PUnit.{1}) a ha ham hrad
      (fun _ : PUnit.{1} => (g : MvPowerSeries σ R))
      (fun _ => hrestricted) (fun _ => hprim)
  have hdelta : μ.restrictedLeadingExponent a ham g = μ.degree (p PUnit.unit) :=
    μ.restrictedLeadingExponent_eq_degree_of_primitive_reduction a ham g hprim
      (p PUnit.unit) (hcoeff PUnit.unit)
  have hfrestricted : IsAdicallyRestricted (Ideal.span {a}) (f : MvPowerSeries σ R) :=
    (mem_adicallyRestrictedSubring _ _).mp f.property
  obtain ⟨q, r, hq, hr, hdivision, hzero⟩ := hdivide (f : MvPowerSeries σ R) hfrestricted
  let quotient : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) :=
    ⟨q PUnit.unit, (mem_adicallyRestrictedSubring _ _).mpr (hq PUnit.unit)⟩
  let remainder : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) :=
    ⟨r, (mem_adicallyRestrictedSubring _ _).mpr hr⟩
  have hdecomp : f = quotient * g + remainder := by
    apply Subtype.ext
    change (f : MvPowerSeries σ R) =
      (quotient : MvPowerSeries σ R) * (g : MvPowerSeries σ R) +
        (remainder : MvPowerSeries σ R)
    simpa [quotient, remainder] using hdivision
  have hcone : ∀ index : σ →₀ ℕ, μ.restrictedLeadingExponent a ham g ≤ index →
      coeff index (remainder : MvPowerSeries σ R) = 0 := by
    intro index hi
    exact hzero index PUnit.unit (by rw [← hdelta]; exact hi)
  refine ⟨(quotient, remainder), ⟨hdecomp, hcone⟩, ?_⟩
  intro pair hpair
  obtain ⟨hquotient, hremainder⟩ :=
    μ.restricted_singleton_division_unique a ham g hg f pair.1 pair.2
      quotient remainder hpair.1 hdecomp hpair.2 hcone
  exact Prod.ext hquotient hremainder

end MonomialOrder
