/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted
import Mathlib.RingTheory.Ideal.Operations

set_option warningAsError true

namespace FormalPowerSeriesTests.MvPowerSeries.IdealAdicRestricted

private theorem integer_coefficient (I : Ideal ℤ) (k : ℕ)
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := Fin 2) I)
    (m : Fin 2 →₀ ℕ) :
    (MvPowerSeries.adicReduction I k f).coeff m =
      Ideal.Quotient.mk (I ^ k) (MvPowerSeries.coeff m f) :=
  MvPowerSeries.coeff_adicReduction I k f m

private theorem integer_polynomial_lift (I : Ideal ℤ) (k : ℕ)
    (p : MvPolynomial (Fin 2) (ℤ ⧸ I ^ k)) :
    ∃ f : MvPowerSeries.adicallyRestrictedSubring (σ := Fin 2) I,
      MvPowerSeries.adicReduction I k f = p :=
  MvPowerSeries.adicReduction_surjective I k p

/-- Reducing a linear polynomial in two variables commutes with coefficient reduction. -/
public theorem integer_linear_polynomial (I : Ideal ℤ) (k : ℕ) :
    MvPowerSeries.adicReduction I k
      (MvPowerSeries.polynomialToRestricted I
        (MvPolynomial.X (0 : Fin 2) + MvPolynomial.C (7 : ℤ))) =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ k))
        (MvPolynomial.X (0 : Fin 2) + MvPolynomial.C (7 : ℤ)) :=
  MvPowerSeries.adicReduction_polynomial I k _

private theorem level_zero_coefficient (I : Ideal ℤ)
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := Fin 2) I)
    (m : Fin 2 →₀ ℕ) :
    (MvPowerSeries.adicReduction I 0 f).coeff m = 0 := by
  rw [MvPowerSeries.coeff_adicReduction]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simp)

private theorem unrestricted_for_top {σ : Type*} (f : MvPowerSeries σ ℤ) :
    MvPowerSeries.IsAdicallyRestricted (⊤ : Ideal ℤ) f := by
  intro k
  convert (Set.finite_empty : (∅ : Set (σ →₀ ℕ)).Finite) using 1
  simp [Ideal.top_pow]

private theorem polynomial_for_bottom :
    MvPowerSeries.IsAdicallyRestricted (⊥ : Ideal ℤ)
      ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.C (7 : ℤ) :
          MvPolynomial (Fin 2) ℤ) :
        MvPowerSeries (Fin 2) ℤ) :=
  MvPowerSeries.isAdicallyRestricted_polynomial _ _

private theorem no_variables (I : Ideal ℤ) (f : MvPowerSeries (Fin 0) ℤ) :
    MvPowerSeries.IsAdicallyRestricted I f := by
  intro k
  exact Set.toFinite _

end FormalPowerSeriesTests.MvPowerSeries.IdealAdicRestricted
