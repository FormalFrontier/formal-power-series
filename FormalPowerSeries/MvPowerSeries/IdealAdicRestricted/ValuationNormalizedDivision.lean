/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.AdicCompletion.Cofinal
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.Cofinal
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.MonicParameter
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.MonicDivision

@[expose] public section

/-!
# Restricted division over a valuation domain in the original parameter

A common normalization parameter turns primitive restricted divisors into
monic ones. Cofinality transfers adic completeness and restrictedness to this
parameter and transfers the division outputs back to the original parameter.
The remainder vanishes in actual coefficients on componentwise leading cones.
-/

set_option warningAsError true

namespace MonomialOrder

open scoped MonomialOrder

variable {σ ι R : Type*} [CommRing R] [IsDomain R] [ValuationRing R] [Fintype ι]

/-- Divide by finitely many primitive restricted series using only completeness
for the original principal ideal. The residue polynomials and their leading
degrees are fixed by the divisors before the dividend is chosen. This is an
existence statement, not uniqueness or a standard-basis assertion. -/
theorem exists_restricted_primitive_division (μ : MonomialOrder σ) (a : R)
    (ha : a ≠ 0) (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal R)
    [IsAdicComplete (Ideal.span {a}) R]
    (g : ι → MvPowerSeries σ R)
    (hg : ∀ i, MvPowerSeries.IsAdicallyRestricted (Ideal.span {a}) (g i))
    (hprim : ∀ i, Ideal.span (Set.range
      (fun d : σ →₀ ℕ => MvPowerSeries.coeff d (g i))) = ⊤) :
    ∃ p : ι → MvPolynomial σ (R ⧸ IsLocalRing.maximalIdeal R),
      (∀ i d, (p i).coeff d = Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal R) (MvPowerSeries.coeff d (g i))) ∧
      (∀ i, p i ≠ 0) ∧
      ∀ f : MvPowerSeries σ R,
        MvPowerSeries.IsAdicallyRestricted (Ideal.span {a}) f →
        ∃ (q : ι → MvPowerSeries σ R) (r : MvPowerSeries σ R),
          (∀ i, MvPowerSeries.IsAdicallyRestricted (Ideal.span {a}) (q i)) ∧
          MvPowerSeries.IsAdicallyRestricted (Ideal.span {a}) r ∧
          f = (∑ i, q i * g i) + r ∧
          ∀ (α : σ →₀ ℕ) (i : ι), μ.degree (p i) ≤ α →
            MvPowerSeries.coeff α r = 0 := by
  classical
  obtain ⟨p, b, N, u, hp, hpne, _hbne, _hbm, hN, hAB, hBA, hdata⟩ :=
    MvPowerSeries.exists_common_monic_parameter μ a ha ham hrad g hg hprim
  refine ⟨p, hp, hpne, ?_⟩
  let A : Ideal R := Ideal.span {a}
  let B : Ideal R := Ideal.span {b}
  have hcompleteB : IsAdicComplete B R :=
    (isAdicComplete_iff_of_cofinal hAB N hN hBA).mp inferInstance
  let hB : ι → MvPowerSeries.adicallyRestrictedSubring (σ := σ) B :=
    fun i => Classical.choose (hdata i).2
  have hspec (i : ι) :
      (hB i : MvPowerSeries σ R) = MvPowerSeries.C (↑((u i)⁻¹) : R) * g i ∧
      μ.Monic (MvPowerSeries.adicReduction B 1 (hB i)) ∧
      μ.degree (MvPowerSeries.adicReduction B 1 (hB i)) = μ.degree (p i) :=
    Classical.choose_spec (hdata i).2
  have hmonic (i : ι) : μ.Monic (MvPowerSeries.adicReduction B 1 (hB i)) :=
    (hspec i).2.1
  intro f hf
  let fB : MvPowerSeries.adicallyRestrictedSubring (σ := σ) B :=
    ⟨f, (MvPowerSeries.mem_adicallyRestrictedSubring B f).mpr
      ((MvPowerSeries.isAdicallyRestricted_iff_of_cofinal hAB N hN hBA f).mp hf)⟩
  obtain ⟨qB, rB, hdivision, hzero⟩ :=
    @MonomialOrder.exists_restricted_monic_division σ ι R _ _ B hcompleteB μ hB hmonic fB
  let q : ι → MvPowerSeries σ R :=
    fun i => (qB i : MvPowerSeries σ R) * MvPowerSeries.C (↑((u i)⁻¹) : R)
  let r : MvPowerSeries σ R := rB
  have hqA (i : ι) : MvPowerSeries.IsAdicallyRestricted A
      (qB i : MvPowerSeries σ R) :=
    (MvPowerSeries.isAdicallyRestricted_iff_of_cofinal hAB N hN hBA _).mpr
      ((MvPowerSeries.mem_adicallyRestrictedSubring B _).mp (qB i).property)
  have hrA : MvPowerSeries.IsAdicallyRestricted A r :=
    (MvPowerSeries.isAdicallyRestricted_iff_of_cofinal hAB N hN hBA _).mpr
      ((MvPowerSeries.mem_adicallyRestrictedSubring B _).mp rB.property)
  have hcA (i : ι) : MvPowerSeries.IsAdicallyRestricted A
      (MvPowerSeries.C (↑((u i)⁻¹) : R) : MvPowerSeries σ R) := by
    simpa only [MvPolynomial.coe_C] using
      (MvPowerSeries.isAdicallyRestricted_polynomial A
        (MvPolynomial.C (↑((u i)⁻¹) : R) : MvPolynomial σ R))
  have hqrestricted (i : ι) : MvPowerSeries.IsAdicallyRestricted A (q i) := by
    apply (MvPowerSeries.mem_adicallyRestrictedSubring A _).mp
    exact (MvPowerSeries.adicallyRestrictedSubring (σ := σ) A).mul_mem
      ((MvPowerSeries.mem_adicallyRestrictedSubring A _).mpr (hqA i))
      ((MvPowerSeries.mem_adicallyRestrictedSubring A _).mpr (hcA i))
  have hcoerced : f =
      (∑ i, (qB i : MvPowerSeries σ R) * (hB i : MvPowerSeries σ R)) +
        (rB : MvPowerSeries σ R) := by
    have heq := congrArg
      (Subring.subtype (MvPowerSeries.adicallyRestrictedSubring (σ := σ) B)) hdivision
    simpa only [fB, map_add, map_sum, map_mul, Subring.subtype_apply,
      Subtype.coe_mk] using heq
  have hterm (i : ι) :
      (qB i : MvPowerSeries σ R) * (hB i : MvPowerSeries σ R) = q i * g i := by
    change (qB i : MvPowerSeries σ R) * (hB i : MvPowerSeries σ R) =
      ((qB i : MvPowerSeries σ R) * MvPowerSeries.C (↑((u i)⁻¹) : R)) * g i
    rw [(hspec i).1]
    exact (mul_assoc _ _ _).symm
  refine ⟨q, r, hqrestricted, hrA, ?_, ?_⟩
  · simpa only [← hterm] using hcoerced
  · intro α i hi
    exact hzero α i ((hspec i).2.2.symm ▸ hi)

end MonomialOrder
