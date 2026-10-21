/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FormalPowerSeries.ArtinHasse
import FormalPowerSeries.ArtinHasse.Padic
import Mathlib.Tactic.NormNum

/-!
# Low-degree coefficients of the Artin–Hasse exponential

The recurrence computes coefficients at primes two and three. The prime-two
example has a noninteger rational coefficient satisfying the prime-two
valuation bound. The boundary at `p = 1` shows why the recurrence requires `2 ≤ p`.
-/


open PowerSeries

example :
    coeff 3 (artinHasseExp 2) = (2 / 3 : ℚ) ∧
    (coeff 3 (artinHasseExp 2)).den = 3 ∧
    Rat.padicValuation 2 (2 / 3 : ℚ) ≤ 1 := by
  have artinHasseExp_two_coeff_three_and_den
      : coeff 3 (artinHasseExp 2) = (2 / 3 : ℚ) ∧
      (coeff 3 (artinHasseExp 2)).den = 3 := by
    have h₂ : coeff 2 (artinHasseExp 2) = 1 := by
      have hr := artinHasseExp_coeff_recurrence 2 (by decide) 2
      norm_num [Finset.sum_range_succ] at hr
      exact hr
    have h : coeff 3 (artinHasseExp 2) = (2 / 3 : ℚ) := by
      apply (eq_div_iff (by norm_num : (3 : ℚ) ≠ 0)).mpr
      have hr := artinHasseExp_coeff_recurrence 2 (by decide) 3
      norm_num [Finset.sum_range_succ, h₂] at hr
      simpa only [mul_comm] using hr
    refine ⟨h, ?_⟩
    rw [h]
    exact Int.ofNat_inj.mp
      (Rat.den_div_eq_of_coprime (a := 2) (b := 3) (by decide) (by decide))
  obtain ⟨hcoeff, hden⟩ := artinHasseExp_two_coeff_three_and_den
  refine ⟨hcoeff, hden, ?_⟩
  rw [← hcoeff]
  exact artinHasseExp_coeff_padicValuation_le_one 2 3

example : coeff 2 (artinHasseExp 3) = (1 / 2 : ℚ) := by
  apply (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).mpr
  simpa [Finset.sum_range_succ, mul_comm] using
    artinHasseExp_coeff_recurrence 3 (by decide) 2

example : (2 : ℚ) * coeff 2 (artinHasseExp 1) ≠
    ∑ i ∈ Finset.range 2,
      if 1 ^ i ≤ 2 then coeff (2 - 1 ^ i) (artinHasseExp 1) else 0 := by
  have hlog : artinHasseLog 1 = X := by
    classical
    ext n
    by_cases hn : n = 1 <;> simp [coeff_artinHasseLog, coeff_X, hn, eq_comm]
  have hexp : artinHasseExp 1 = exp ℚ := by
    rw [artinHasseExp_eq_subst, hlog]
    exact X_subst (exp ℚ)
  rw [hexp]
  norm_num [Finset.sum_range_succ, coeff_exp]
