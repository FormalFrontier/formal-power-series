/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.MonicParameter

set_option warningAsError true

open MvPowerSeries

namespace Tests.MvPowerSeries.IdealAdicRestricted.MonicParameter

private theorem two_members {σ R : Type*} [CommRing R] [IsDomain R]
    [ValuationRing R] (μ : MonomialOrder σ) (a : R)
    (ha : a ≠ 0) (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal R)
    (g : Fin 2 → MvPowerSeries σ R)
    (hg : ∀ i, IsAdicallyRestricted (Ideal.span {a}) (g i))
    (hprim : ∀ i, Ideal.span (Set.range (fun d : σ →₀ ℕ => coeff d (g i))) = ⊤) :
    ∃ (p : Fin 2 → MvPolynomial σ (R ⧸ IsLocalRing.maximalIdeal R))
      (b : R) (N : ℕ) (u : Fin 2 → Rˣ)
      (h₀ h₁ : adicallyRestrictedSubring (σ := σ) (Ideal.span {b})),
      b ≠ 0 ∧ 1 ≤ N ∧ Ideal.span {a} ≤ Ideal.span {b} ∧
      (Ideal.span {b} : Ideal R) ^ N ≤ Ideal.span {a} ∧
      (h₀ : MvPowerSeries σ R) = C (↑((u 0)⁻¹) : R) * g 0 ∧
      (h₁ : MvPowerSeries σ R) = C (↑((u 1)⁻¹) : R) * g 1 ∧
      μ.Monic (adicReduction (Ideal.span {b}) 1 h₀) ∧
      μ.Monic (adicReduction (Ideal.span {b}) 1 h₁) ∧
      μ.degree (adicReduction (Ideal.span {b}) 1 h₀) = μ.degree (p 0) ∧
      μ.degree (adicReduction (Ideal.span {b}) 1 h₁) = μ.degree (p 1) := by
  obtain ⟨p, b, N, u, -, -, hbnz, -, hN, hAb, hpow, hnorm⟩ :=
    exists_common_monic_parameter μ a ha ham hrad g hg hprim
  obtain ⟨-, h₀, heq₀, hmon₀, hdeg₀⟩ := hnorm 0
  obtain ⟨-, h₁, heq₁, hmon₁, hdeg₁⟩ := hnorm 1
  exact ⟨p, b, N, u, h₀, h₁, hbnz, hN, hAb, hpow,
    heq₀, heq₁, hmon₀, hmon₁, hdeg₀, hdeg₁⟩

/-- A cofinal monic parameter can be chosen for an empty primitive family. -/
public theorem empty_family {σ R : Type*} [CommRing R] [IsDomain R]
    [ValuationRing R] (μ : MonomialOrder σ) (a : R)
    (ha : a ≠ 0) (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal R) :
    ∃ (b : R) (N : ℕ), b ≠ 0 ∧ b ∈ IsLocalRing.maximalIdeal R ∧ 1 ≤ N ∧
      Ideal.span {a} ≤ Ideal.span {b} ∧
      (Ideal.span {b} : Ideal R) ^ N ≤ Ideal.span {a} := by
  obtain ⟨_, b, N, _, _, _, hb, hbm, hN, hAb, hpow, _⟩ :=
    exists_common_monic_parameter μ a ha ham hrad
      (fun i : Empty => i.elim)
      (fun i : Empty => i.elim)
      (fun i : Empty => i.elim)
  exact ⟨b, N, hb, hbm, hN, hAb, hpow⟩

private theorem zero_variables {R : Type*} [CommRing R] [IsDomain R]
    [ValuationRing R] (μ : MonomialOrder (Fin 0)) (a : R)
    (ha : a ≠ 0) (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal R)
    (g : Fin 2 → MvPowerSeries (Fin 0) R)
    (hg : ∀ i, IsAdicallyRestricted (Ideal.span {a}) (g i))
    (hprim : ∀ i, Ideal.span (Set.range (fun d : Fin 0 →₀ ℕ => coeff d (g i))) = ⊤) :
    ∃ (p : Fin 2 → MvPolynomial (Fin 0) (R ⧸ IsLocalRing.maximalIdeal R))
      (b : R) (h : adicallyRestrictedSubring (σ := Fin 0) (Ideal.span {b})),
      μ.Monic (adicReduction (Ideal.span {b}) 1 h) ∧
      μ.degree (adicReduction (Ideal.span {b}) 1 h) = μ.degree (p 0) := by
  obtain ⟨p, b, _, _, _, _, _, _, _, _, _, hnorm⟩ :=
    exists_common_monic_parameter μ a ha ham hrad g hg hprim
  obtain ⟨_, h, _, hmon, hdeg⟩ := hnorm 0
  exact ⟨p, b, h, hmon, hdeg⟩

end Tests.MvPowerSeries.IdealAdicRestricted.MonicParameter
