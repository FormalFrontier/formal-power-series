/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.SingletonDivision

/-!
# Singleton restricted division examples

The product law and uniqueness apply without primitivity or completeness.
Empty-variable examples instantiate uniqueness for a nonprimitive divisor and
existence for a primitive one.
-/

public section

set_option warningAsError true

open MvPowerSeries

section EmptyVariables

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    (μ : MonomialOrder Empty) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)

example (g : adicallyRestrictedSubring (σ := Empty) (Ideal.span {a})) :
    μ.restrictedLeadingExponent a ham g = 0 := Subsingleton.elim _ _

example :
    ∃ g : adicallyRestrictedSubring (σ := Empty) (Ideal.span {a}),
      g ≠ 0 ∧ IsUnit (coeff 0 (g : MvPowerSeries Empty R)) ∧
        μ.restrictedLeadingExponent a ham g = 0 := by
  let g : adicallyRestrictedSubring (σ := Empty) (Ideal.span {a}) :=
    polynomialToRestricted (Ideal.span {a}) (MvPolynomial.C (1 : R))
  have hcoeff : coeff 0 (g : MvPowerSeries Empty R) = 1 := by
    simp [g]
  refine ⟨g, ?_, ?_, Subsingleton.elim _ _⟩
  · intro hzero
    have hc0 : coeff 0 (g : MvPowerSeries Empty R) = 0 := by simp [hzero]
    exact one_ne_zero (hcoeff.symm.trans hc0)
  · rw [hcoeff]
    exact isUnit_one

example :
    (1 * 1 : adicallyRestrictedSubring (σ := Empty) (Ideal.span {a})) ≠ 0 ∧
      μ.restrictedLeadingExponent a ham
        (1 * 1 : adicallyRestrictedSubring (σ := Empty) (Ideal.span {a})) = 0 := by
  obtain ⟨hproduct, hadd⟩ := μ.restrictedLeadingExponent_mul_of_ne_zero a ham
    (1 : adicallyRestrictedSubring (σ := Empty) (Ideal.span {a})) 1 one_ne_zero one_ne_zero
  exact ⟨hproduct, by rw [hadd]; exact Subsingleton.elim _ _⟩

example (ha : a ≠ 0) :
    ∃ g : adicallyRestrictedSubring (σ := Empty) (Ideal.span {a}),
      g = polynomialToRestricted (Ideal.span {a}) (MvPolynomial.C a) ∧
        g ≠ 0 ∧
        Ideal.span (Set.range (fun index : Empty →₀ ℕ =>
          coeff index (g : MvPowerSeries Empty R))) ≠ ⊤ ∧
        (0 : adicallyRestrictedSubring (σ := Empty) (Ideal.span {a})) = 0 * g + 0 ∧
        (∀ index : Empty →₀ ℕ, μ.restrictedLeadingExponent a ham g ≤ index →
          coeff index (0 : MvPowerSeries Empty R) = 0) ∧
        ∀ q r : adicallyRestrictedSubring (σ := Empty) (Ideal.span {a}),
          (0 : adicallyRestrictedSubring (σ := Empty) (Ideal.span {a})) = q * g + r →
          (∀ index : Empty →₀ ℕ, μ.restrictedLeadingExponent a ham g ≤ index →
            coeff index (r : MvPowerSeries Empty R) = 0) →
          q = 0 ∧ r = 0 := by
  let g : adicallyRestrictedSubring (σ := Empty) (Ideal.span {a}) :=
    polynomialToRestricted (Ideal.span {a}) (MvPolynomial.C a)
  have hcoeff : coeff 0 (g : MvPowerSeries Empty R) = a := by
    simp [g, polynomialToRestricted_coe]
  have hnonunit : ¬ IsUnit (coeff 0 (g : MvPowerSeries Empty R)) := by
    rw [hcoeff]
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using ham
  have hg : g ≠ 0 := by
    intro hzero
    have hc0 : coeff 0 (g : MvPowerSeries Empty R) = 0 := by simp [hzero]
    exact ha (hcoeff.symm.trans hc0)
  have hcontent : Ideal.span (Set.range (fun index : Empty →₀ ℕ =>
      coeff index (g : MvPowerSeries Empty R))) ≠ ⊤ := by
    intro hprimitive
    have hunit := MonomialOrder.isUnit_restrictedContentCoefficient_of_primitive
      a g hprimitive
    have hindex : restrictedContentIndex a g = (0 : Empty →₀ ℕ) :=
      Subsingleton.elim _ _
    apply hnonunit
    simpa only [hindex, hcoeff] using hunit
  refine ⟨g, rfl, hg, hcontent, by simp, by simp, ?_⟩
  intro q r h hr
  exact μ.restricted_singleton_division_unique a ham g hg 0 q r 0 0 h
    (by simp) hr (by simp)

end EmptyVariables

section ZeroParameter

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    (μ : MonomialOrder σ)
    [IsHausdorff (Ideal.span {0} : Ideal R) R]

example (f g : adicallyRestrictedSubring (σ := σ) (Ideal.span {0}))
    (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 ∧
      μ.restrictedLeadingExponent (0 : R) (Ideal.zero_mem _) (f * g) =
        μ.restrictedLeadingExponent (0 : R) (Ideal.zero_mem _) f +
          μ.restrictedLeadingExponent (0 : R) (Ideal.zero_mem _) g :=
  μ.restrictedLeadingExponent_mul_of_ne_zero 0 (Ideal.zero_mem _) f g hf hg

example (g : adicallyRestrictedSubring (σ := σ) (Ideal.span {0})) (hg : g ≠ 0)
    (f q r q' r' : adicallyRestrictedSubring (σ := σ) (Ideal.span {0}))
    (h : f = q * g + r) (h' : f = q' * g + r')
    (hr : ∀ index : σ →₀ ℕ,
      μ.restrictedLeadingExponent (0 : R) (Ideal.zero_mem _) g ≤ index →
        coeff index (r : MvPowerSeries σ R) = 0)
    (hr' : ∀ index : σ →₀ ℕ,
      μ.restrictedLeadingExponent (0 : R) (Ideal.zero_mem _) g ≤ index →
        coeff index (r' : MvPowerSeries σ R) = 0) : q = q' ∧ r = r' :=
  μ.restricted_singleton_division_unique 0 (Ideal.zero_mem _) g hg f q r q' r'
    h h' hr hr'

end ZeroParameter

section PrimitiveExistence

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    (μ : MonomialOrder Empty) (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    [IsAdicComplete (Ideal.span {a} : Ideal R) R]

example (ha : a ≠ 0)
    (hrad : (Ideal.span {a} : Ideal R).radical = IsLocalRing.maximalIdeal R)
    (f : adicallyRestrictedSubring (σ := Empty) (Ideal.span {a})) :
    ∃! qr : adicallyRestrictedSubring (σ := Empty) (Ideal.span {a}) ×
        adicallyRestrictedSubring (σ := Empty) (Ideal.span {a}),
      f = qr.1 * polynomialToRestricted (Ideal.span {a}) (MvPolynomial.C (1 : R)) +
        qr.2 ∧
        ∀ index : Empty →₀ ℕ,
          μ.restrictedLeadingExponent a ham
              (polynomialToRestricted (Ideal.span {a}) (MvPolynomial.C (1 : R))) ≤ index →
            coeff index (qr.2 : MvPowerSeries Empty R) = 0 := by
  let g : adicallyRestrictedSubring (σ := Empty) (Ideal.span {a}) :=
    polynomialToRestricted (Ideal.span {a}) (MvPolynomial.C (1 : R))
  have hcoeff : coeff 0 (g : MvPowerSeries Empty R) = 1 := by
    simp [g]
  have hprimitive : Ideal.span (Set.range (fun index : Empty →₀ ℕ =>
      coeff index (g : MvPowerSeries Empty R))) = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
    apply Ideal.subset_span
    exact ⟨0, hcoeff⟩
  exact μ.existsUnique_restricted_primitive_singleton_division a ham ha hrad g hprimitive f

end PrimitiveExistence
