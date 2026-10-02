/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.SelectedFactor

set_option warningAsError true

namespace Tests.MvPowerSeries.IdealAdicRestricted.SelectedFactor

private theorem each_generating_index {σ R : Type*} [CommRing R] [PreValuationRing R]
    (I : Ideal R) [IsHausdorff I R] (f : MvPowerSeries σ R)
    (hf : MvPowerSeries.IsAdicallyRestricted I f) (j : σ →₀ ℕ)
    (hj : Ideal.span (Set.range (fun m : σ →₀ ℕ => MvPowerSeries.coeff m f)) =
      Ideal.span {MvPowerSeries.coeff j f}) :
    ∃ g : MvPowerSeries σ R,
      MvPowerSeries.IsAdicallyRestricted I g ∧
      f = MvPowerSeries.C (MvPowerSeries.coeff j f) * g ∧
      MvPowerSeries.coeff j g = 1 :=
  MvPowerSeries.IsAdicallyRestricted.exists_selected_coeff_factor I f hf j hj

private theorem some_generating_index {σ R : Type*} [CommRing R] [PreValuationRing R]
    (I : Ideal R) [IsHausdorff I R] (f : MvPowerSeries σ R)
    (hf : MvPowerSeries.IsAdicallyRestricted I f) :
    ∃ (j : σ →₀ ℕ) (g : MvPowerSeries σ R),
      Ideal.span (Set.range (fun m : σ →₀ ℕ => MvPowerSeries.coeff m f)) =
        Ideal.span {MvPowerSeries.coeff j f} ∧
      MvPowerSeries.IsAdicallyRestricted I g ∧
      f = MvPowerSeries.C (MvPowerSeries.coeff j f) * g ∧
      MvPowerSeries.coeff j g = 1 := by
  obtain ⟨j, hj⟩ :=
    MvPowerSeries.IsAdicallyRestricted.exists_span_range_eq_span_coeff I f hf
  obtain ⟨g, hg, hfg, hgj⟩ := each_generating_index I f hf j hj
  exact ⟨j, g, hj, hg, hfg, hgj⟩

private theorem some_factor_has_unit_content {σ R : Type*}
    [CommRing R] [PreValuationRing R] (I : Ideal R) [IsHausdorff I R]
    (f : MvPowerSeries σ R) (hf : MvPowerSeries.IsAdicallyRestricted I f) :
    ∃ (j : σ →₀ ℕ) (g : MvPowerSeries σ R),
      MvPowerSeries.IsAdicallyRestricted I g ∧
      f = MvPowerSeries.C (MvPowerSeries.coeff j f) * g ∧
      Ideal.span (Set.range (fun m : σ →₀ ℕ => MvPowerSeries.coeff m g)) = ⊤ := by
  obtain ⟨j, g, _, hg, hfg, hgj⟩ := some_generating_index I f hf
  refine ⟨j, g, hg, hfg, ?_⟩
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← hgj]
  exact Ideal.subset_span (Set.mem_range_self j)

private theorem zero_series_each_index {σ R : Type*} [CommRing R] [PreValuationRing R]
    (I : Ideal R) [IsHausdorff I R] (j : σ →₀ ℕ) :
    ∃ g : MvPowerSeries σ R,
      MvPowerSeries.IsAdicallyRestricted I g ∧
      (0 : MvPowerSeries σ R) =
        MvPowerSeries.C (MvPowerSeries.coeff j (0 : MvPowerSeries σ R)) * g ∧
      MvPowerSeries.coeff j g = 1 := by
  refine each_generating_index I 0 ?_ j ?_
  · intro n
    convert (Set.finite_empty : (∅ : Set (σ →₀ ℕ)).Finite) using 1
    simp
  · have hr : Set.range (fun m : σ →₀ ℕ =>
        MvPowerSeries.coeff m (0 : MvPowerSeries σ R)) = {0} := by
      ext x
      constructor
      · rintro ⟨m, rfl⟩
        simp
      · intro hx
        exact ⟨j, by simpa using hx.symm⟩
    rw [hr]
    simp

private theorem empty_variables_each_index {R : Type*} [CommRing R]
    [PreValuationRing R] (I : Ideal R) [IsHausdorff I R]
    (f : MvPowerSeries (Fin 0) R) (j : Fin 0 →₀ ℕ)
    (hj : Ideal.span (Set.range (fun m : Fin 0 →₀ ℕ => MvPowerSeries.coeff m f)) =
      Ideal.span {MvPowerSeries.coeff j f}) :
    ∃ g : MvPowerSeries (Fin 0) R,
      MvPowerSeries.IsAdicallyRestricted I g ∧
      f = MvPowerSeries.C (MvPowerSeries.coeff j f) * g ∧
      MvPowerSeries.coeff j g = 1 := by
  apply each_generating_index I f _ j hj
  intro n
  exact Set.toFinite _

private theorem infinite_variables_each_index {R : Type*} [CommRing R]
    [PreValuationRing R] (I : Ideal R) [IsHausdorff I R]
    (f : MvPowerSeries ℕ R) (hf : MvPowerSeries.IsAdicallyRestricted I f)
    (j : ℕ →₀ ℕ)
    (hj : Ideal.span (Set.range (fun m : ℕ →₀ ℕ => MvPowerSeries.coeff m f)) =
      Ideal.span {MvPowerSeries.coeff j f}) :
    ∃ g : MvPowerSeries ℕ R,
      MvPowerSeries.IsAdicallyRestricted I g ∧
      f = MvPowerSeries.C (MvPowerSeries.coeff j f) * g ∧
      MvPowerSeries.coeff j g = 1 :=
  each_generating_index I f hf j hj

private theorem rational_polynomial_selected_factor (p : MvPolynomial (Fin 2) ℚ) :
    ∃ (j : Fin 2 →₀ ℕ) (g : MvPowerSeries (Fin 2) ℚ),
      Ideal.span (Set.range (fun m : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff m (p : MvPowerSeries (Fin 2) ℚ))) =
        Ideal.span {MvPowerSeries.coeff j (p : MvPowerSeries (Fin 2) ℚ)} ∧
      MvPowerSeries.IsAdicallyRestricted (⊥ : Ideal ℚ) g ∧
      (p : MvPowerSeries (Fin 2) ℚ) =
        MvPowerSeries.C (MvPowerSeries.coeff j (p : MvPowerSeries (Fin 2) ℚ)) * g ∧
      MvPowerSeries.coeff j g = 1 :=
  some_generating_index (⊥ : Ideal ℚ) (p : MvPowerSeries (Fin 2) ℚ)
    (MvPowerSeries.isAdicallyRestricted_polynomial (⊥ : Ideal ℚ) p)

end Tests.MvPowerSeries.IdealAdicRestricted.SelectedFactor
