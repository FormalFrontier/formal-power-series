/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.DegreeDecay
import Mathlib.RingTheory.Ideal.Operations

set_option warningAsError true

namespace Tests.MvPowerSeries.IdealAdicRestricted.DegreeDecay

private theorem restricted_to_cutoff {σ R : Type*} [CommRing R] [Finite σ]
    (I : Ideal R) (f : MvPowerSeries σ R)
    (hf : MvPowerSeries.IsAdicallyRestricted I f) :
    ∀ k : ℕ, ∃ d : ℕ, ∀ m : σ →₀ ℕ,
      d ≤ m.degree → MvPowerSeries.coeff m f ∈ I ^ k :=
  (MvPowerSeries.isAdicallyRestricted_iff_degree_cutoff I f).mp hf

private theorem cutoff_to_restricted {σ R : Type*} [CommRing R] [Finite σ]
    (I : Ideal R) (f : MvPowerSeries σ R)
    (hf : ∀ k : ℕ, ∃ d : ℕ, ∀ m : σ →₀ ℕ,
      d ≤ m.degree → MvPowerSeries.coeff m f ∈ I ^ k) :
    MvPowerSeries.IsAdicallyRestricted I f :=
  (MvPowerSeries.isAdicallyRestricted_iff_degree_cutoff I f).mpr hf

private theorem polynomial_cutoff (I : Ideal ℤ) (p : MvPolynomial (Fin 2) ℤ) :
    ∀ k : ℕ, ∃ d : ℕ, ∀ m : Fin 2 →₀ ℕ,
      d ≤ m.degree →
        MvPowerSeries.coeff m (p : MvPowerSeries (Fin 2) ℤ) ∈ I ^ k :=
  restricted_to_cutoff I (p : MvPowerSeries (Fin 2) ℤ)
    (MvPowerSeries.isAdicallyRestricted_polynomial I p)

private theorem zero_level (I : Ideal ℤ) (f : MvPowerSeries (Fin 2) ℤ) :
    ∀ m : Fin 2 →₀ ℕ,
      0 ≤ m.degree → MvPowerSeries.coeff m f ∈ I ^ 0 := by
  intro m _
  simp

private theorem top_ideal (f : MvPowerSeries (Fin 2) ℤ) :
    MvPowerSeries.IsAdicallyRestricted (⊤ : Ideal ℤ) f := by
  apply cutoff_to_restricted
  intro k
  refine ⟨0, ?_⟩
  intro m _
  simp [Ideal.top_pow]

private theorem empty_variables (I : Ideal ℤ) (f : MvPowerSeries (Fin 0) ℤ) :
    ∀ k : ℕ, ∃ d : ℕ, ∀ m : Fin 0 →₀ ℕ,
      d ≤ m.degree → MvPowerSeries.coeff m f ∈ I ^ k :=
  restricted_to_cutoff I f (by
    intro k
    exact Set.toFinite _)

/- The finite-variable hypothesis is essential in the reverse implication.
The formal sum of all variables has only degree-one coefficients, but infinitely
many coefficients remain nonzero modulo the zero ideal. -/
private noncomputable def allVariables : MvPowerSeries ℕ ℤ :=
  fun m => if m.degree = 1 then 1 else 0

private theorem allVariables_cutoff :
    ∀ k : ℕ, ∃ d : ℕ, ∀ m : ℕ →₀ ℕ,
      d ≤ m.degree →
        MvPowerSeries.coeff m allVariables ∈ (⊥ : Ideal ℤ) ^ k := by
  intro k
  refine ⟨2, ?_⟩
  intro m hm
  have hdegree : m.degree ≠ 1 := by omega
  simp [MvPowerSeries.coeff_apply, allVariables, hdegree]

private theorem allVariables_not_restricted :
    ¬ MvPowerSeries.IsAdicallyRestricted (⊥ : Ideal ℤ) allVariables := by
  intro hf
  have hinfinite : (Set.range (fun n : ℕ => Finsupp.single n (1 : ℕ))).Infinite :=
    Set.infinite_range_of_injective (Finsupp.single_left_injective (by decide))
  apply hinfinite
  apply (hf 1).subset
  rintro m ⟨n, rfl⟩
  simp [MvPowerSeries.coeff_apply, allVariables, Finsupp.degree_single]

private theorem infinite_variables_counterexample :
    ∃ f : MvPowerSeries ℕ ℤ,
      (∀ k : ℕ, ∃ d : ℕ, ∀ m : ℕ →₀ ℕ,
        d ≤ m.degree → MvPowerSeries.coeff m f ∈ (⊥ : Ideal ℤ) ^ k) ∧
      ¬ MvPowerSeries.IsAdicallyRestricted (⊥ : Ideal ℤ) f :=
  ⟨allVariables, allVariables_cutoff, allVariables_not_restricted⟩

end Tests.MvPowerSeries.IdealAdicRestricted.DegreeDecay
