/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.Content
import Mathlib.RingTheory.Finiteness.Defs

set_option warningAsError true

namespace Tests.MvPowerSeries.IdealAdicRestricted.Content

private theorem arbitrary_variables {σ R : Type*} [CommRing R] [PreValuationRing R]
    (I : Ideal R) [IsHausdorff I R] (f : MvPowerSeries σ R)
    (hf : MvPowerSeries.IsAdicallyRestricted I f) :
    ∃ m : σ →₀ ℕ,
      Ideal.span (Set.range (fun j : σ →₀ ℕ => MvPowerSeries.coeff j f)) =
        Ideal.span {MvPowerSeries.coeff m f} :=
  MvPowerSeries.IsAdicallyRestricted.exists_span_range_eq_span_coeff I f hf

private theorem zero_series {σ R : Type*} [CommRing R] [PreValuationRing R]
    (I : Ideal R) [IsHausdorff I R] :
    ∃ m : σ →₀ ℕ,
      Ideal.span (Set.range (fun j : σ →₀ ℕ =>
        MvPowerSeries.coeff j (0 : MvPowerSeries σ R))) =
        Ideal.span {MvPowerSeries.coeff m (0 : MvPowerSeries σ R)} := by
  apply arbitrary_variables I 0
  intro k
  convert (Set.finite_empty : (∅ : Set (σ →₀ ℕ)).Finite) using 1
  simp

private theorem empty_variables {R : Type*} [CommRing R] [PreValuationRing R]
    (I : Ideal R) [IsHausdorff I R] (f : MvPowerSeries (Fin 0) R) :
    ∃ m : Fin 0 →₀ ℕ,
      Ideal.span (Set.range (fun j : Fin 0 →₀ ℕ => MvPowerSeries.coeff j f)) =
        Ideal.span {MvPowerSeries.coeff m f} := by
  apply arbitrary_variables I f
  intro k
  exact Set.toFinite _

private theorem infinite_variables {R : Type*} [CommRing R] [PreValuationRing R]
    (I : Ideal R) [IsHausdorff I R] (f : MvPowerSeries ℕ R)
    (hf : MvPowerSeries.IsAdicallyRestricted I f) :
    ∃ m : ℕ →₀ ℕ,
      Ideal.span (Set.range (fun j : ℕ →₀ ℕ => MvPowerSeries.coeff j f)) =
        Ideal.span {MvPowerSeries.coeff m f} :=
  arbitrary_variables I f hf

private theorem rational_polynomial_content (p : MvPolynomial (Fin 2) ℚ) :
    ∃ m : Fin 2 →₀ ℕ,
      Ideal.span (Set.range (fun j : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff j (p : MvPowerSeries (Fin 2) ℚ))) =
        Ideal.span {MvPowerSeries.coeff m (p : MvPowerSeries (Fin 2) ℚ)} :=
  MvPowerSeries.IsAdicallyRestricted.exists_span_range_eq_span_coeff
    (σ := Fin 2) (R := ℚ) (⊥ : Ideal ℚ) (p : MvPowerSeries (Fin 2) ℚ)
    (MvPowerSeries.isAdicallyRestricted_polynomial (⊥ : Ideal ℚ) p)

private theorem rational_polynomial_content_fg (p : MvPolynomial (Fin 2) ℚ) :
    (Ideal.span (Set.range (fun j : Fin 2 →₀ ℕ =>
      MvPowerSeries.coeff j (p : MvPowerSeries (Fin 2) ℚ)))).FG := by
  obtain ⟨m, hm⟩ := rational_polynomial_content p
  rw [hm]
  exact Submodule.fg_span (Set.finite_singleton _)

end Tests.MvPowerSeries.IdealAdicRestricted.Content
