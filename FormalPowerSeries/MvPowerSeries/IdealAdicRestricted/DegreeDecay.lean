/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted
public import Mathlib.Data.Finsupp.Weight

public section

/-!
# Degree cutoffs for ideal-adically restricted power series

Over finitely many variables, coefficientwise ideal-adic restriction is equivalent
to vanishing modulo each ideal power above a sufficiently high total degree.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

private theorem finite_exception_degree_cutoff (I : Ideal R) (k : ℕ)
    (f : MvPowerSeries σ R)
    (hf : {m : σ →₀ ℕ | coeff m f ∉ I ^ k}.Finite) :
    ∃ d : ℕ, ∀ m : σ →₀ ℕ, d ≤ m.degree → coeff m f ∈ I ^ k := by
  classical
  let exceptions := hf.toFinset
  refine ⟨exceptions.sup (fun m => m.degree) + 1, ?_⟩
  intro m hm
  by_contra hnot
  have hmem : m ∈ exceptions := hf.mem_toFinset.mpr hnot
  exact (not_lt_of_ge hm) (Nat.lt_succ_of_le (Finset.le_sup hmem))

/-- For finitely many variables, restrictedness is equivalent to coefficients
lying in each ideal power above a degree cutoff. The forward implication does
not require finiteness of the variable type. -/
theorem isAdicallyRestricted_iff_degree_cutoff (I : Ideal R)
    (f : MvPowerSeries σ R) [Finite σ] :
    IsAdicallyRestricted I f ↔
      ∀ k : ℕ, ∃ d : ℕ, ∀ m : σ →₀ ℕ,
        d ≤ m.degree → coeff m f ∈ I ^ k := by
  constructor
  · intro hf k
    exact finite_exception_degree_cutoff I k f (hf k)
  · intro hf k
    obtain ⟨d, hd⟩ := hf k
    apply (Finsupp.finite_of_degree_lt (σ := σ) d).subset
    intro m hm
    exact lt_of_not_ge (fun hdeg => hm (hd m hdeg))

end MvPowerSeries
