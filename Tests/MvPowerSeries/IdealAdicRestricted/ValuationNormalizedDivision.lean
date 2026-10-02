/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.ValuationNormalizedDivision

@[expose] public section

/-!
# Clients of cofinal restricted division

The general comparisons work in either direction, separately for each
completeness superclass. The division clients include empty families, empty
variables, and infinitely many variables without extra finiteness hypotheses.
-/

set_option warningAsError true

section Cofinal

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {I J : Ideal R} (hIJ : I ≤ J) (N : ℕ) (hN : 1 ≤ N) (hJI : J ^ N ≤ I)

example (h : IsPrecomplete I M) : IsPrecomplete J M :=
  (isPrecomplete_iff_of_cofinal hIJ N hN hJI).mp h

example (h : IsPrecomplete J M) : IsPrecomplete I M :=
  (isPrecomplete_iff_of_cofinal hIJ N hN hJI).mpr h

example (h : IsHausdorff I M) : IsHausdorff J M :=
  (isHausdorff_iff_of_cofinal hIJ N hN hJI).mp h

example (h : IsHausdorff J M) : IsHausdorff I M :=
  (isHausdorff_iff_of_cofinal hIJ N hN hJI).mpr h

example (h : IsAdicComplete I M) : IsAdicComplete J M :=
  (isAdicComplete_iff_of_cofinal hIJ N hN hJI).mp h

example (h : IsAdicComplete J M) : IsAdicComplete I M :=
  (isAdicComplete_iff_of_cofinal hIJ N hN hJI).mpr h

variable {σ : Type*} (f : MvPowerSeries σ R)

example (h : MvPowerSeries.IsAdicallyRestricted I f) :
    MvPowerSeries.IsAdicallyRestricted J f :=
  (MvPowerSeries.isAdicallyRestricted_iff_of_cofinal hIJ N hN hJI f).mp h

example (h : MvPowerSeries.IsAdicallyRestricted J f) :
    MvPowerSeries.IsAdicallyRestricted I f :=
  (MvPowerSeries.isAdicallyRestricted_iff_of_cofinal hIJ N hN hJI f).mpr h

end Cofinal

section Division

open scoped MonomialOrder

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
variable (a : R) (ha : a ≠ 0) (ham : a ∈ IsLocalRing.maximalIdeal R)
  (hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal R)
  [IsAdicComplete (Ideal.span {a}) R]

example (μ : MonomialOrder ℕ) (f : MvPowerSeries ℕ R)
    (hf : MvPowerSeries.IsAdicallyRestricted (Ideal.span {a}) f) :
    ∃ r : MvPowerSeries ℕ R,
      MvPowerSeries.IsAdicallyRestricted (Ideal.span {a}) r ∧ f = r := by
  let g : Empty → MvPowerSeries ℕ R := fun i => i.elim
  have hg : ∀ i, MvPowerSeries.IsAdicallyRestricted (Ideal.span {a}) (g i) :=
    fun i => i.elim
  have hprim : ∀ i, Ideal.span (Set.range
      (fun d : ℕ →₀ ℕ => MvPowerSeries.coeff d (g i))) = ⊤ := fun i => i.elim
  obtain ⟨_, _, _, hdivide⟩ :=
    μ.exists_restricted_primitive_division a ha ham hrad g hg hprim
  obtain ⟨_, r, _, hr, heq, _⟩ := hdivide f hf
  exact ⟨r, hr, by simpa using heq⟩

example (μ : MonomialOrder Empty) (g : Fin 1 → MvPowerSeries Empty R)
    (hg : ∀ i, MvPowerSeries.IsAdicallyRestricted (Ideal.span {a}) (g i))
    (hprim : ∀ i, Ideal.span (Set.range
      (fun d : Empty →₀ ℕ => MvPowerSeries.coeff d (g i))) = ⊤)
    (f : MvPowerSeries Empty R)
    (hf : MvPowerSeries.IsAdicallyRestricted (Ideal.span {a}) f) :
    ∃ (q : Fin 1 → MvPowerSeries Empty R) (r : MvPowerSeries Empty R),
      (∀ i, MvPowerSeries.IsAdicallyRestricted (Ideal.span {a}) (q i)) ∧
      MvPowerSeries.IsAdicallyRestricted (Ideal.span {a}) r ∧
      f = (∑ i, q i * g i) + r := by
  obtain ⟨_, _, _, hdivide⟩ :=
    μ.exists_restricted_primitive_division a ha ham hrad g hg hprim
  obtain ⟨q, r, hq, hr, heq, _⟩ := hdivide f hf
  exact ⟨q, r, hq, hr, heq⟩

example (μ : MonomialOrder ℕ) (g : Fin 1 → MvPowerSeries ℕ R)
    (hg : ∀ i, MvPowerSeries.IsAdicallyRestricted (Ideal.span {a}) (g i))
    (hprim : ∀ i, Ideal.span (Set.range
      (fun d : ℕ →₀ ℕ => MvPowerSeries.coeff d (g i))) = ⊤) :
    ∃ p : Fin 1 → MvPolynomial ℕ (R ⧸ IsLocalRing.maximalIdeal R),
      (∀ i, p i ≠ 0) ∧
      ∀ f : MvPowerSeries ℕ R,
        MvPowerSeries.IsAdicallyRestricted (Ideal.span {a}) f →
        ∃ (q : Fin 1 → MvPowerSeries ℕ R) (r : MvPowerSeries ℕ R),
          f = (∑ i, q i * g i) + r ∧
          ∀ (α : ℕ →₀ ℕ) (i : Fin 1), μ.degree (p i) ≤ α →
            MvPowerSeries.coeff α r = 0 := by
  obtain ⟨p, _, hp, hdivide⟩ :=
    μ.exists_restricted_primitive_division a ha ham hrad g hg hprim
  refine ⟨p, hp, ?_⟩
  intro f hf
  obtain ⟨q, r, _, _, hdecomp, hcone⟩ := hdivide f hf
  exact ⟨q, r, hdecomp, hcone⟩

end Division
