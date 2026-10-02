/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted

@[expose] public section

/-!
# Restricted power series under cofinal ideals

For cofinal ideals the *same* series is restricted for either filtration. Both
directions compare finite exceptional coefficient sets at each ideal power;
neither requires a finite set of variables.
-/

set_option warningAsError true

namespace MvPowerSeries

/-- Cofinal ideal powers give equivalent restrictedness for the underlying
series, without identifying the two restricted subrings. -/
theorem isAdicallyRestricted_iff_of_cofinal {σ R : Type*} [CommRing R]
    {I J : Ideal R} (hIJ : I ≤ J) (N : ℕ) (_hN : 1 ≤ N)
    (hJI : J ^ N ≤ I) (f : MvPowerSeries σ R) :
    IsAdicallyRestricted I f ↔ IsAdicallyRestricted J f := by
  constructor
  · intro hf n
    exact (hf n).subset (by
      intro d hd hI
      exact hd ((Ideal.pow_right_mono hIJ n) hI))
  · intro hf n
    have hpow : J ^ (N * n) ≤ I ^ n := by
      rw [pow_mul]
      exact pow_le_pow_left' hJI n
    exact (hf (N * n)).subset (by
      intro d hd hJ
      exact hd (hpow hJ))

end MvPowerSeries
