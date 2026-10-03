/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.MonicDivision
import Mathlib.Data.ZMod.Defs

set_option warningAsError true

namespace Tests.RestrictedMonicDivision

open MvPowerSeries

variable {σ ι R : Type*} [CommRing R] [Fintype ι]
variable (I : Ideal R) [IsAdicComplete I R] (m : MonomialOrder σ)

private theorem client_cone
    (g : ι → adicallyRestrictedSubring (σ := σ) I)
    (hg : ∀ i, m.Monic (adicReduction I 1 (g i)))
    (f : adicallyRestrictedSubring (σ := σ) I) :
    ∃ (q : ι → adicallyRestrictedSubring (σ := σ) I)
      (r : adicallyRestrictedSubring (σ := σ) I),
      f = (∑ i, q i * g i) + r ∧
        ∀ (α : σ →₀ ℕ) (i : ι),
          m.degree (adicReduction I 1 (g i)) ≤ α → coeff α (r : MvPowerSeries σ R) = 0 :=
  m.exists_restricted_monic_division I g hg f

/-- Monic affine-polynomial division also applies with infinitely many variables. -/
public theorem client_polynomial_over_infinite_variables
    (m : MonomialOrder ℕ) (c : R)
    (f : adicallyRestrictedSubring (σ := ℕ) I) :
    ∃ (q : Fin 1 → adicallyRestrictedSubring (σ := ℕ) I)
      (r : adicallyRestrictedSubring (σ := ℕ) I),
      f = (∑ i, q i * polynomialToRestricted I (MvPolynomial.X 0 + MvPolynomial.C c)) + r ∧
        ∀ (α : ℕ →₀ ℕ) (_ : Fin 1),
          m.degree (adicReduction I 1 (polynomialToRestricted I
            (MvPolynomial.X 0 + MvPolynomial.C c))) ≤ α →
            coeff α (r : MvPowerSeries ℕ R) = 0 := by
  apply m.exists_restricted_monic_division I
    (fun _ : Fin 1 => polynomialToRestricted I (MvPolynomial.X 0 + MvPolynomial.C c))
  intro _
  simpa only [adicReduction_polynomial, map_add, MvPolynomial.map_X,
    MvPolynomial.map_C] using
    m.monic_X_add_C 0 (Ideal.Quotient.mk (I ^ 1) c)

private theorem client_empty_divisors
    (m : MonomialOrder σ)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    ∃ r : adicallyRestrictedSubring (σ := σ) I, f = r := by
  obtain ⟨q, r, h, _⟩ :=
    m.exists_restricted_monic_division I
      (fun i : Fin 0 => i.elim0) (fun i => i.elim0) f
  exact ⟨r, by simpa using h⟩

private theorem client_empty_variables
    (m : MonomialOrder Empty)
    (f : adicallyRestrictedSubring (σ := Empty) I) :
    ∃ (q : Fin 1 → adicallyRestrictedSubring (σ := Empty) I)
      (r : adicallyRestrictedSubring (σ := Empty) I),
      f = (∑ i, q i * (1 : adicallyRestrictedSubring (σ := Empty) I)) + r ∧
        ∀ (α : Empty →₀ ℕ) (_ : Fin 1),
          m.degree (adicReduction I 1 (1 : adicallyRestrictedSubring (σ := Empty) I)) ≤ α →
            coeff α (r : MvPowerSeries Empty R) = 0 := by
  apply m.exists_restricted_monic_division I (fun _ : Fin 1 => 1)
  intro _
  simpa only [map_one] using (m.monic_one (R := R ⧸ I ^ 1))

private theorem client_zero_ideal [IsAdicComplete (⊥ : Ideal R) R]
    (m : MonomialOrder ℕ)
    (f : adicallyRestrictedSubring (σ := ℕ) (⊥ : Ideal R)) :
    ∃ (q : Fin 1 → adicallyRestrictedSubring (σ := ℕ) (⊥ : Ideal R))
      (r : adicallyRestrictedSubring (σ := ℕ) (⊥ : Ideal R)),
      f = (∑ i, q i * (1 : adicallyRestrictedSubring (σ := ℕ) (⊥ : Ideal R))) + r ∧
        ∀ (α : ℕ →₀ ℕ) (_ : Fin 1),
          m.degree (adicReduction (⊥ : Ideal R) 1
            (1 : adicallyRestrictedSubring (σ := ℕ) (⊥ : Ideal R))) ≤ α →
            coeff α (r : MvPowerSeries ℕ R) = 0 := by
  apply m.exists_restricted_monic_division (⊥ : Ideal R) (fun _ : Fin 1 => 1)
  intro _
  simpa only [map_one] using (m.monic_one (R := R ⧸ (⊥ : Ideal R) ^ 1))

private theorem client_zero_ring (I : Ideal (ZMod 1))
    [IsAdicComplete I (ZMod 1)] (m : MonomialOrder ℕ)
    (g : Fin 1 → adicallyRestrictedSubring (σ := ℕ) I)
    (f : adicallyRestrictedSubring (σ := ℕ) I) :
    ∃ (q : Fin 1 → adicallyRestrictedSubring (σ := ℕ) I)
      (r : adicallyRestrictedSubring (σ := ℕ) I),
      f = (∑ i, q i * g i) + r ∧
        ∀ (α : ℕ →₀ ℕ) (i : Fin 1),
          m.degree (adicReduction I 1 (g i)) ≤ α →
            coeff α (r : MvPowerSeries ℕ (ZMod 1)) = 0 := by
  apply m.exists_restricted_monic_division I g
  intro i
  exact MonomialOrder.Monic.of_subsingleton

end Tests.RestrictedMonicDivision
