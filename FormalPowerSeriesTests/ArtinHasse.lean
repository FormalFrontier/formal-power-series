/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FormalPowerSeries.ArtinHasse
import Mathlib.Tactic.NormNum

/-!
# Low-degree coefficients of the Artin–Hasse exponential

The recurrence computes coefficients at primes two and three. The prime-two
example has a noninteger rational coefficient. The boundary at `p = 1` shows
why the recurrence requires `2 ≤ p`.
-/

open PowerSeries

private theorem artinHasseExp_two_coeff_three_and_den
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

private theorem artinHasseExp_three_coeff_two : coeff 2 (artinHasseExp 3) = (1 / 2 : ℚ) := by
  apply (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).mpr
  simpa [Finset.sum_range_succ, mul_comm] using
    artinHasseExp_coeff_recurrence 3 (by decide) 2

private theorem artinHasseExp_one_recurrence_failure_two : (2 : ℚ) * coeff 2 (artinHasseExp 1) ≠
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
