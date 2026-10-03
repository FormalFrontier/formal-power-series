/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FirstVariablePreparation

/-!
# Monomial clients for first-variable restricted preparation

The embedded monomial `X ^ d` has the prepared pair `(1, X ^ d)`.
The examples verify joint uniqueness without assuming that a competing
quotient is a unit, including degree zero and no remaining variables.
-/

public section

set_option warningAsError true

namespace MvPowerSeries

variable {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
    (a : V) (ham : a ∈ IsLocalRing.maximalIdeal V)
    [IsAdicComplete (Ideal.span {a}) V]
    (ha : a ≠ 0)
    (hrad : (Ideal.span {a} : Ideal V).radical = IsLocalRing.maximalIdeal V)

omit [IsAdicComplete (Ideal.span {a}) V] in
private theorem monomial_residue (n d : ℕ) :
    MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham
      (polynomialRestrictedFinFirst (Ideal.span {a}) n (Polynomial.X ^ d))) =
        Polynomial.X ^ d := by
  simpa only [restrictedResidueHom_apply, Polynomial.map_pow, Polynomial.map_X] using
    (finSuccEquiv_restrictedResidueHom_polynomialRestrictedFinFirst a ham n
      (Polynomial.X ^ d))

include ham ha hrad

private theorem monomial_preparation (n d : ℕ) :
    ∃ (u : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
      (G : Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a}))),
      IsUnit u ∧ G.Monic ∧ G.degree = (d : WithBot ℕ) ∧
        polynomialRestrictedFinFirst (Ideal.span {a}) n G =
          u * polynomialRestrictedFinFirst (Ideal.span {a}) n (Polynomial.X ^ d) ∧
        ∀ (v : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
          (H : Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a}))),
          H.Monic → H.degree = (d : WithBot ℕ) →
          polynomialRestrictedFinFirst (Ideal.span {a}) n H =
            v * polynomialRestrictedFinFirst (Ideal.span {a}) n (Polynomial.X ^ d) →
          v = u ∧ H = G := by
  apply existsUnique_firstVariable_preparation_of_scalar_top n a ham ha hrad
    (polynomialRestrictedFinFirst (Ideal.span {a}) n (Polynomial.X ^ d)) d 1
  · rw [monomial_residue]
    exact Polynomial.natDegree_X_pow d
  · rw [monomial_residue, Polynomial.coeff_X_pow_self]
    rfl
  · exact one_ne_zero

example (n d : ℕ) :
    ∃ (u : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
      (G : Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a}))),
      IsUnit u ∧ G.Monic ∧ G.degree = (d : WithBot ℕ) ∧
        polynomialRestrictedFinFirst (Ideal.span {a}) n G =
          u * polynomialRestrictedFinFirst (Ideal.span {a}) n (Polynomial.X ^ d) ∧
        u = 1 ∧ G = Polynomial.X ^ d := by
  obtain ⟨u, G, hu, hmonic, hdegree, heq, hunique⟩ :=
    monomial_preparation a ham ha hrad n d
  have hcandidate := hunique 1 (Polynomial.X ^ d) (Polynomial.monic_X_pow d)
    (Polynomial.degree_X_pow d) (by simp)
  exact ⟨u, G, hu, hmonic, hdegree, heq, hcandidate.1.symm, hcandidate.2.symm⟩

/-- Every monic preparation of the distinguished monomial has multiplier one
and polynomial `X ^ d`, without a unit assumption on the multiplier. -/
theorem monomial_preparation_unique (n d : ℕ) :
    ∀ (v : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
      (H : Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a}))),
      H.Monic → H.degree = (d : WithBot ℕ) →
      polynomialRestrictedFinFirst (Ideal.span {a}) n H =
        v * polynomialRestrictedFinFirst (Ideal.span {a}) n (Polynomial.X ^ d) →
      v = 1 ∧ H = Polynomial.X ^ d := by
  obtain ⟨u, G, _, _, _, _, hunique⟩ := monomial_preparation a ham ha hrad n d
  have hcandidate := hunique 1 (Polynomial.X ^ d) (Polynomial.monic_X_pow d)
    (Polynomial.degree_X_pow d) (by simp)
  intro v H hmonic hdegree heq
  obtain ⟨hv, hH⟩ := hunique v H hmonic hdegree heq
  exact ⟨hv.trans hcandidate.1.symm, hH.trans hcandidate.2.symm⟩

example (d : ℕ) :
    ∀ (v : adicallyRestrictedSubring (σ := Fin (0 + 1)) (Ideal.span {a}))
      (H : Polynomial (adicallyRestrictedSubring (σ := Fin 0) (Ideal.span {a}))),
      H.Monic → H.degree = (d : WithBot ℕ) →
      polynomialRestrictedFinFirst (Ideal.span {a}) 0 H =
        v * polynomialRestrictedFinFirst (Ideal.span {a}) 0 (Polynomial.X ^ d) →
      v = 1 ∧ H = Polynomial.X ^ d := by
  obtain ⟨u, G, _, _, _, _, hunique⟩ := monomial_preparation a ham ha hrad 0 d
  have hcandidate := hunique 1 (Polynomial.X ^ d) (Polynomial.monic_X_pow d)
    (Polynomial.degree_X_pow d) (by simp)
  intro v H hmonic hdegree heq
  obtain ⟨hv, hH⟩ := hunique v H hmonic hdegree heq
  exact ⟨hv.trans hcandidate.1.symm, hH.trans hcandidate.2.symm⟩

example (n : ℕ) :
    ∀ (v : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
      (H : Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a}))),
      H.Monic → H.degree = (0 : WithBot ℕ) →
      polynomialRestrictedFinFirst (Ideal.span {a}) n H =
        v * polynomialRestrictedFinFirst (Ideal.span {a}) n (Polynomial.X ^ 0) →
      v = 1 ∧ H = Polynomial.X ^ 0 := by
  obtain ⟨u, G, _, _, _, _, hunique⟩ := monomial_preparation a ham ha hrad n 0
  have hcandidate := hunique 1 (Polynomial.X ^ 0) (Polynomial.monic_X_pow 0)
    (Polynomial.degree_X_pow 0) (by simp)
  intro v H hmonic hdegree heq
  obtain ⟨hv, hH⟩ := hunique v H hmonic hdegree heq
  exact ⟨hv.trans hcandidate.1.symm, hH.trans hcandidate.2.symm⟩

end MvPowerSeries
