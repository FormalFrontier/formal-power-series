/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FormalPowerSeries.ArtinHasseEulerProduct
import Mathlib.Tactic.NormNum

/-!
# Artin–Hasse Euler-prefix examples

At prime two, the cubic coefficient is `2/3`, both in the exponential and in
the finite Euler prefix through index three. The two computations are
independent: the exponential uses its coefficient recurrence, and the prefix
uses the stock binomial-series coefficient formulas, not the Euler theorem.

The composite parameter four shows that the coprime-index formula cannot be
extended to every parameter at least two.
-/

-- These private mathematical examples have no exported API.
set_option linter.privateModule false

open PowerSeries

private theorem artinHasseExp_two_euler_coeff_three : coeff 3 (artinHasseExp 2) = (2 / 3 : ℚ) ∧
    coeff 3
      (∏ n ∈ (Finset.Icc 1 3).filter (fun n => Nat.Coprime n 2),
        subst ((X : PowerSeries ℚ) ^ n)
          (rescale (-1 : ℚ)
            (binomialSeries ℚ (-(ArithmeticFunction.moebius n : ℚ) / (n : ℚ))))) =
      (2 / 3 : ℚ) ∧
    coeff 3 (artinHasseExp 2) =
      coeff 3
        (∏ n ∈ (Finset.Icc 1 3).filter (fun n => Nat.Coprime n 2),
          subst ((X : PowerSeries ℚ) ^ n)
            (rescale (-1 : ℚ)
              (binomialSeries ℚ (-(ArithmeticFunction.moebius n : ℚ) / (n : ℚ))))) := by
  refine ⟨?_, ?_, coeff_artinHasseExp_eq_prod 2 (by decide) 3 3 le_rfl⟩
  · have h₂ : coeff 2 (artinHasseExp 2) = 1 := by
      have hr := artinHasseExp_coeff_recurrence 2 (by decide) 2
      norm_num [Finset.sum_range_succ] at hr
      exact hr
    apply (eq_div_iff (by norm_num : (3 : ℚ) ≠ 0)).mpr
    have hr := artinHasseExp_coeff_recurrence 2 (by decide) 3
    norm_num [Finset.sum_range_succ, h₂] at hr
    simpa only [mul_comm] using hr
  · have hindices : (Finset.Icc 1 3).filter (fun n => Nat.Coprime n 2) = {1, 3} := by
      decide
    rw [hindices]
    norm_num [Finset.prod_pair, ArithmeticFunction.moebius_apply_one,
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3), coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      coeff_subst_X_pow, coeff_rescale, binomialSeries_coeff, Ring.choose_neg',
      Ring.multichoose_one, Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]

private theorem artinHasseExp_four_euler_coeff_two_ne : coeff 2 (artinHasseExp 4) ≠
    coeff 2
      (∏ n ∈ (Finset.Icc 1 2).filter (fun n => Nat.Coprime n 4),
        subst ((X : PowerSeries ℚ) ^ n)
          (rescale (-1 : ℚ)
            (binomialSeries ℚ (-(ArithmeticFunction.moebius n : ℚ) / (n : ℚ))))) := by
  have he : coeff 2 (artinHasseExp 4) = (1 / 2 : ℚ) := by
    apply (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).mpr
    simpa [Finset.sum_range_succ, mul_comm] using
      artinHasseExp_coeff_recurrence 4 (by decide) 2
  have hindices : (Finset.Icc 1 2).filter (fun n => Nat.Coprime n 4) = {1} := by
    decide
  rw [he, hindices]
  norm_num [coeff_subst_X_pow, coeff_rescale, binomialSeries_coeff,
    ArithmeticFunction.moebius_apply_one, Ring.choose_neg', Ring.multichoose_one,
    Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]
