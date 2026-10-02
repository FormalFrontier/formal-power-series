/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.PrimitiveStandardBasis

/-!
# Private clients of primitive standard-basis ideal generation

The client imports the restricted-series leading-term and division APIs.
-/

set_option warningAsError true

namespace Tests.MvPowerSeries.IdealAdicRestricted.PrimitiveStandardBasis

open _root_.MvPowerSeries
open scoped MonomialOrder

variable {σ ι R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Fintype ι] (a : R)
  (ha : a ≠ 0) (ham : a ∈ IsLocalRing.maximalIdeal R)
  (hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal R)
  [IsAdicComplete (Ideal.span {a}) R]

include ha hrad in
private theorem arbitrary_variables (μ : MonomialOrder σ)
    (J : Ideal (adicallyRestrictedSubring (σ := σ) (Ideal.span {a})))
    (g : ι → adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hgJ : ∀ i, g i ∈ J)
    (hprim : ∀ i, Ideal.span (Set.range
      (fun d : σ →₀ ℕ => coeff d (g i : MvPowerSeries σ R))) = ⊤)
    (hLT : μ.restrictedLeadingTermIdeal a ham J =
      Ideal.span (Set.range (fun i : ι => μ.restrictedLeadingTerm a ham (g i)))) :
    J = Ideal.span (Set.range g) :=
  μ.ideal_eq_span_of_primitive_standardBasis a ha ham hrad J g hgJ hprim hLT

include ha hrad in
private theorem infinite_variables (μ : MonomialOrder ℕ)
    (J : Ideal (adicallyRestrictedSubring (σ := ℕ) (Ideal.span {a})))
    (g : ι → adicallyRestrictedSubring (σ := ℕ) (Ideal.span {a}))
    (hgJ : ∀ i, g i ∈ J)
    (hprim : ∀ i, Ideal.span (Set.range
      (fun d : ℕ →₀ ℕ => coeff d (g i : MvPowerSeries ℕ R))) = ⊤)
    (hLT : μ.restrictedLeadingTermIdeal a ham J =
      Ideal.span (Set.range (fun i : ι => μ.restrictedLeadingTerm a ham (g i)))) :
    J = Ideal.span (Set.range g) :=
  arbitrary_variables a ha ham hrad μ J g hgJ hprim hLT

include ha hrad in
private theorem empty_variables (μ : MonomialOrder Empty)
    (J : Ideal (adicallyRestrictedSubring (σ := Empty) (Ideal.span {a})))
    (g : ι → adicallyRestrictedSubring (σ := Empty) (Ideal.span {a}))
    (hgJ : ∀ i, g i ∈ J)
    (hprim : ∀ i, Ideal.span (Set.range
      (fun d : Empty →₀ ℕ => coeff d (g i : MvPowerSeries Empty R))) = ⊤)
    (hLT : μ.restrictedLeadingTermIdeal a ham J =
      Ideal.span (Set.range (fun i : ι => μ.restrictedLeadingTerm a ham (g i)))) :
    J = Ideal.span (Set.range g) :=
  arbitrary_variables a ha ham hrad μ J g hgJ hprim hLT

private theorem empty_family_zero_ideal (μ : MonomialOrder σ) (a : R)
    (ha : a ≠ 0) (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal R)
    [IsAdicComplete (Ideal.span {a}) R] :
    (⊥ : Ideal (adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))) =
      Ideal.span (Set.range (fun i : Empty =>
        (i.elim : adicallyRestrictedSubring (σ := σ) (Ideal.span {a})))) := by
  let g : Empty → adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) :=
    fun i => i.elim
  have hLT : μ.restrictedLeadingTermIdeal a ham
      (⊥ : Ideal (adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))) =
      Ideal.span (Set.range (fun i : Empty => μ.restrictedLeadingTerm a ham (g i))) := by
    simpa only [Set.range_eq_empty, Ideal.span_empty] using
      μ.restrictedLeadingTermIdeal_bot a ham
  exact μ.ideal_eq_span_of_primitive_standardBasis a ha ham hrad ⊥ g
    (fun i => i.elim) (fun i => i.elim) hLT

private theorem primitive_constant_client (μ : MonomialOrder σ) (a : R)
    (ha : a ≠ 0) (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal R)
    [IsAdicComplete (Ideal.span {a}) R]
    (hLT : μ.restrictedLeadingTermIdeal a ham
      (⊤ : Ideal (adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))) =
      Ideal.span (Set.range (fun _ : Fin 1 => μ.restrictedLeadingTerm a ham
        (polynomialToRestricted (Ideal.span {a}) (MvPolynomial.C (1 : R)))))) :
    (⊤ : Ideal (adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))) =
      Ideal.span (Set.range (fun _ : Fin 1 =>
        polynomialToRestricted (Ideal.span {a}) (MvPolynomial.C (1 : R)))) := by
  let z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) :=
    polynomialToRestricted (Ideal.span {a}) (MvPolynomial.C (1 : R))
  have hc : coeff (0 : σ →₀ ℕ) (z : MvPowerSeries σ R) = 1 := by
    simp [z]
  have hprimitive : Ideal.span (Set.range
      (fun d : σ →₀ ℕ => coeff d (z : MvPowerSeries σ R))) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have hmem : (1 : R) ∈ Ideal.span
        {coeff (0 : σ →₀ ℕ) (z : MvPowerSeries σ R)} := by
      simpa only [hc] using Ideal.mem_span_singleton_self (1 : R)
    exact (Ideal.span_mono
      (Set.singleton_subset_iff.mpr (Set.mem_range_self (0 : σ →₀ ℕ)))) hmem
  exact μ.ideal_eq_span_of_primitive_standardBasis a ha ham hrad ⊤
    (fun _ : Fin 1 => z) (fun _ => by simp) (fun _ => hprimitive) hLT

end Tests.MvPowerSeries.IdealAdicRestricted.PrimitiveStandardBasis
