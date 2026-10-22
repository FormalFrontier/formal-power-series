/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.KernelFiltration
import Mathlib.Data.ZMod.Defs

set_option warningAsError true

namespace Tests.MvPowerSeries.IdealAdicRestricted.KernelFiltration

open _root_.MvPowerSeries

private theorem arbitrary_variables {σ R : Type*} [CommRing R] (I : Ideal R)
    (a b : adicallyRestrictedSubring (σ := σ) I)
    (n k : ℕ) (ha : adicReduction I n a = 0) (hb : adicReduction I k b = 0) :
    adicReduction I (n + k) (a * b) = 0 :=
  adicReduction_mul_eq_zero I a b n k ha hb

/-- Kernel levels two and three multiply into kernel level five. -/
public theorem unequal_positive_levels {σ R : Type*} [CommRing R] (I : Ideal R)
    (a b : adicallyRestrictedSubring (σ := σ) I)
    (ha : adicReduction I 2 a = 0) (hb : adicReduction I 3 b = 0) :
    adicReduction I 5 (a * b) = 0 :=
  adicReduction_mul_eq_zero I a b 2 3 ha hb

private theorem left_level_zero {σ R : Type*} [CommRing R] (I : Ideal R)
    (a b : adicallyRestrictedSubring (σ := σ) I)
    (ha : adicReduction I 0 a = 0) (hb : adicReduction I 3 b = 0) :
    adicReduction I 3 (a * b) = 0 :=
  adicReduction_mul_eq_zero I a b 0 3 ha hb

private theorem right_level_zero {σ R : Type*} [CommRing R] (I : Ideal R)
    (a b : adicallyRestrictedSubring (σ := σ) I)
    (ha : adicReduction I 3 a = 0) (hb : adicReduction I 0 b = 0) :
    adicReduction I 3 (a * b) = 0 :=
  adicReduction_mul_eq_zero I a b 3 0 ha hb

private theorem finite_family {σ R ι : Type*} [CommRing R] (I : Ideal R)
    (s : Finset ι) (a b : ι → adicallyRestrictedSubring (σ := σ) I)
    (n k : ℕ) (ha : ∀ i ∈ s, adicReduction I n (a i) = 0)
    (hb : ∀ i ∈ s, adicReduction I k (b i) = 0) :
    adicReduction I (n + k) (∑ i ∈ s, a i * b i) = 0 :=
  adicReduction_sum_mul_eq_zero I s a b n k ha hb

private theorem finite_level_one {σ R ι : Type*} [CommRing R] (I : Ideal R)
    (s : Finset ι) (a b : ι → adicallyRestrictedSubring (σ := σ) I)
    (n : ℕ) (ha : ∀ i ∈ s, adicReduction I n (a i) = 0)
    (hb : ∀ i ∈ s, adicReduction I 1 (b i) = 0) :
    adicReduction I (n + 1) (∑ i ∈ s, a i * b i) = 0 :=
  adicReduction_sum_mul_eq_zero_succ I s a b n ha hb

private theorem empty_family {σ R ι : Type*} [CommRing R] (I : Ideal R)
    (a b : ι → adicallyRestrictedSubring (σ := σ) I) (n : ℕ) :
    adicReduction I (n + 1) (∑ i ∈ (∅ : Finset ι), a i * b i) = 0 := by
  apply adicReduction_sum_mul_eq_zero_succ I ∅ a b n
  · simp
  · simp

private theorem empty_variables (I : Ideal ℤ)
    (a b : adicallyRestrictedSubring (σ := Fin 0) I)
    (ha : adicReduction I 2 a = 0) (hb : adicReduction I 1 b = 0) :
    adicReduction I 3 (a * b) = 0 :=
  adicReduction_mul_eq_zero I a b 2 1 ha hb

private theorem zero_ideal {σ : Type*}
    (a b : adicallyRestrictedSubring (σ := σ) (⊥ : Ideal ℤ))
    (ha : adicReduction ⊥ 2 a = 0) (hb : adicReduction ⊥ 3 b = 0) :
    adicReduction ⊥ 5 (a * b) = 0 :=
  adicReduction_mul_eq_zero ⊥ a b 2 3 ha hb

private theorem top_ideal {σ : Type*}
    (a b : adicallyRestrictedSubring (σ := σ) (⊤ : Ideal ℤ))
    (ha : adicReduction ⊤ 2 a = 0) (hb : adicReduction ⊤ 3 b = 0) :
    adicReduction ⊤ 5 (a * b) = 0 :=
  adicReduction_mul_eq_zero ⊤ a b 2 3 ha hb

private theorem zero_ring {σ : Type*}
    (a b : adicallyRestrictedSubring (σ := σ) (⊥ : Ideal (ZMod 1)))
    (ha : adicReduction ⊥ 2 a = 0) (hb : adicReduction ⊥ 3 b = 0) :
    adicReduction ⊥ 5 (a * b) = 0 :=
  adicReduction_mul_eq_zero ⊥ a b 2 3 ha hb

end Tests.MvPowerSeries.IdealAdicRestricted.KernelFiltration
