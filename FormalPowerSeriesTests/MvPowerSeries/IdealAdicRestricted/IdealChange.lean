/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.IdealChange
public import Mathlib.Data.ZMod.Basic

public section

/-! Polynomial reductions and ideal inclusions over commutative rings. -/

set_option warningAsError true

open MvPowerSeries

section General

variable {σ R : Type*} [CommRing R] (I J K : Ideal R) (hIJ : I ≤ J) (hJK : J ≤ K)

example (f g : adicallyRestrictedSubring (σ := σ) I) :
    reductionAtLargerIdeal I J hIJ (f * g) =
      reductionAtLargerIdeal I J hIJ f * reductionAtLargerIdeal I J hIJ g :=
  map_mul _ _ _

example (f : adicallyRestrictedSubring (σ := σ) I) :
    reductionAtLargerIdeal J K hJK (restrictAlongIdeal I J hIJ f) =
      MvPolynomial.map (Ideal.Quotient.factor hJK) (reductionAtLargerIdeal I J hIJ f) := by
  rw [reductionAtLargerIdeal_restrictAlongIdeal, reductionAtLargerIdeal_map]

example : Function.Surjective (reductionAtLargerIdeal (σ := σ) I J hIJ) :=
  reductionAtLargerIdeal_surjective I J hIJ

end General

example : (⊥ : Ideal ℤ) < Ideal.span {(2 : ℤ)} := by
  exact bot_lt_iff_ne_bot.mpr (Ideal.span_singleton_eq_bot.not.mpr (by decide))

example (p : MvPolynomial (Fin 2) (ℤ ⧸ Ideal.span {(2 : ℤ)})) :
    ∃ f : adicallyRestrictedSubring (σ := Fin 2) (⊥ : Ideal ℤ),
      reductionAtLargerIdeal ⊥ (Ideal.span {(2 : ℤ)}) bot_le f = p :=
  (reductionAtLargerIdeal_surjective _ _ bot_le) p

-- Infinite variables and a noncomplete coefficient ring need no extra instances.
example (p : MvPolynomial ℕ ℤ) :
    reductionAtLargerIdeal (⊥ : Ideal ℤ) ⊤ bot_le (polynomialToRestricted ⊥ p) =
      MvPolynomial.map (Ideal.Quotient.mk ⊤) p :=
  reductionAtLargerIdeal_polynomial _ _ _ p

-- The reduction modulo the top ideal is zero, including at arbitrary support.
example (I : Ideal ℤ) (f : adicallyRestrictedSubring (σ := ℕ) I) :
    reductionAtLargerIdeal I ⊤ le_top f = 0 := by
  apply (reductionAtLargerIdeal_eq_zero_iff I ⊤ le_top f).mpr
  intro d
  exact Submodule.mem_top

-- The same API admits both the zero ring and an empty variable type.
example : Function.Surjective
    (reductionAtLargerIdeal (σ := Empty) (⊥ : Ideal (ZMod 1)) ⊤ bot_le) :=
  reductionAtLargerIdeal_surjective _ _ _

example (I : Ideal ℤ) : Function.Injective (restrictAlongIdeal (σ := Empty) I I le_rfl) :=
  restrictAlongIdeal_injective _ _ _
