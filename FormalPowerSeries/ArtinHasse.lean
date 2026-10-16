/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# The Artin–Hasse exponential

The rational Artin–Hasse exponential is constructed by formal substitution.
For `p ≥ 2`, it is `exp (∑ i ≥ 0, X^(p^i) / p^i)` and is uniquely characterized
by its constant coefficient one and its coefficient recurrence. The formal
exponential and substitution are those of Mathlib; no analytic convergence or
complete valued field is involved. Coefficient p-integrality is not proved here.

The auxiliary logarithm is specified coefficientwise. For `p ≥ 2`, distinct
powers of `p` give exactly the displayed formal sum. The coefficientwise
construction is also defined at the boundary values `p = 0` and `p = 1`, but
no infinite-sum interpretation is asserted there.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition (2002), Chapter I, (9.1), pp. 29–30.
* Mathlib's formal exponential, substitution, and coefficient APIs.
-/

@[expose] public section

namespace PowerSeries

/-- The rational series with coefficient `1/n` when `n` is a power of `p`,
and zero otherwise. For `p ≥ 2`, this is `∑ i ≥ 0, X^(p^i) / p^i`. -/
noncomputable def artinHasseLog (p : ℕ) : PowerSeries ℚ := by
  classical
  exact mk fun n => if ∃ i : ℕ, p ^ i = n then (n : ℚ)⁻¹ else 0

open Classical in
/-- The coefficient formula specifying the Artin–Hasse logarithm. -/
theorem coeff_artinHasseLog (p n : ℕ) :
    coeff n (artinHasseLog p) =
      if ∃ i : ℕ, p ^ i = n then (n : ℚ)⁻¹ else 0 := by
  classical
  exact coeff_mk _ _

/-- The Artin–Hasse logarithm has zero constant coefficient. -/
@[simp] theorem constantCoeff_artinHasseLog (p : ℕ) :
    constantCoeff (artinHasseLog p) = 0 := by
  classical
  rw [← coeff_zero_eq_constantCoeff, coeff_artinHasseLog]
  simp

/-- Every power of `p` has its reciprocal as logarithm coefficient. -/
@[simp] theorem coeff_artinHasseLog_pow (p i : ℕ) :
    coeff (p ^ i) (artinHasseLog p) = ((p : ℚ) ^ i)⁻¹ := by
  classical
  rw [coeff_artinHasseLog, ite_eq_left ⟨i, rfl⟩, Nat.cast_pow]

/-- The rational Artin–Hasse exponential, defined by formal substitution.
For prime `p`, this is the Artin–Hasse function of Fesenko–Vostokov I.(9.1),
not its reciprocal. -/
noncomputable def artinHasseExp (p : ℕ) : PowerSeries ℚ :=
  subst (artinHasseLog p) (exp ℚ)

/-- The defining formal-substitution equation. -/
theorem artinHasseExp_eq_subst (p : ℕ) :
    artinHasseExp p = subst (artinHasseLog p) (exp ℚ) := rfl

/-- The Artin–Hasse exponential has constant coefficient one. -/
@[simp] theorem constantCoeff_artinHasseExp (p : ℕ) :
    constantCoeff (artinHasseExp p) = 1 := by
  exact (constantCoeff_subst_of_constantCoeff_zero
    (constantCoeff_artinHasseLog p) (exp ℚ)).trans (by simp)

private theorem derivative_artinHasseExp (p : ℕ) :
    derivative (artinHasseExp p) = artinHasseExp p * derivative (artinHasseLog p) := by
  rw [artinHasseExp_eq_subst,
    derivative_subst (HasSubst.of_constantCoeff_zero' (constantCoeff_artinHasseLog p)),
    derivative_exp]

/-- The Artin–Hasse exponential has linear coefficient one. -/
@[simp] theorem coeff_one_artinHasseExp (p : ℕ) :
    coeff 1 (artinHasseExp p) = 1 := by
  have h := congrArg constantCoeff (derivative_artinHasseExp p)
  have hl : coeff 1 (artinHasseLog p) = 1 := by
    simpa using coeff_artinHasseLog_pow p 0
  have hD (f : PowerSeries ℚ) : constantCoeff (derivative f) = coeff 1 f := by
    rw [← coeff_zero_eq_constantCoeff, coeff_derivative]
    simp
  simpa only [map_mul, hD, hl, constantCoeff_artinHasseExp, one_mul] using h

/-- The rational Artin–Hasse exponential is a unit. -/
theorem isUnit_artinHasseExp (p : ℕ) : IsUnit (artinHasseExp p) := by
  exact isUnit_iff_constantCoeff.mpr (by simp)

open Classical in
private theorem coeff_X_mul_derivative_artinHasseLog (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    coeff n (X * derivative (artinHasseLog p)) =
      if ∃ i : ℕ, p ^ i = n then (1 : ℚ) else 0 := by
  classical
  cases n with
  | zero =>
    have hpow : ¬ ∃ i : ℕ, p ^ i = 0 := by
      rintro ⟨i, hi⟩
      exact (pow_ne_zero i (by omega : p ≠ 0)) hi
    rw [ite_eq_right hpow]
    simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative, coeff_artinHasseLog]
    split_ifs <;> simp [show (n + 1 : ℚ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n]

private theorem coeff_X_mul_derivative_artinHasseLog_eq_sum
    (p : ℕ) (hp : 2 ≤ p) (n k : ℕ) (hk : k ≤ n) :
    coeff k (X * derivative (artinHasseLog p)) =
      coeff k (∑ i ∈ Finset.range n, (X : PowerSeries ℚ) ^ (p ^ i)) := by
  classical
  -- Up to degree `n`, only the powers with exponent in `range n` can contribute.
  rw [coeff_X_mul_derivative_artinHasseLog p hp]
  simp only [map_sum, coeff_X_pow]
  by_cases h : ∃ i : ℕ, p ^ i = k
  · obtain ⟨i, rfl⟩ := h
    rw [ite_eq_left ⟨i, rfl⟩]
    symm
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      have hne : p ^ j ≠ p ^ i :=
        fun he => hji (Nat.pow_right_injective hp he)
      simp [Ne.symm hne]
    · intro hi
      exact (hi (Finset.mem_range.mpr ((Nat.lt_pow_self (by omega : 1 < p)).trans_le hk))).elim
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    simp [show k ≠ p ^ i from fun he => h ⟨i, he.symm⟩]

/-- The coefficient recurrence characterizing the Artin–Hasse exponential
when `p ≥ 2`. This identity holds at composite values as well as at primes. -/
theorem artinHasseExp_coeff_recurrence (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    (n : ℚ) * coeff n (artinHasseExp p) =
      ∑ i ∈ Finset.range n,
        if p ^ i ≤ n then coeff (n - p ^ i) (artinHasseExp p) else 0 := by
  classical
  have hcoeff : (n : ℚ) * coeff n (artinHasseExp p) =
      coeff n (X * derivative (artinHasseExp p)) := by
    cases n with
    | zero => simp
    | succ n => simp [coeff_derivative, mul_comm]
  rw [hcoeff, derivative_artinHasseExp, mul_left_comm]
  calc
    coeff n (artinHasseExp p * (X * derivative (artinHasseLog p))) =
        coeff n (artinHasseExp p *
          ∑ i ∈ Finset.range n, (X : PowerSeries ℚ) ^ (p ^ i)) := by
      rw [coeff_mul, coeff_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      rw [coeff_X_mul_derivative_artinHasseLog_eq_sum p hp n ij.2
        (by have := Finset.mem_antidiagonal.mp hij; omega)]
    _ = _ := by
      simp only [Finset.mul_sum, map_sum, coeff_mul_X_pow']

/-- A normalized rational series satisfying the Artin–Hasse recurrence is the
Artin–Hasse exponential. The constant coefficient condition is essential,
since scalar multiples satisfy the same recurrence. -/
theorem eq_artinHasseExp_of_coeff_recurrence (p : ℕ) (hp : 2 ≤ p)
    (f : PowerSeries ℚ) (h₀ : constantCoeff f = 1)
    (hrec : ∀ n : ℕ, (n : ℚ) * coeff n f =
      ∑ i ∈ Finset.range n, if p ^ i ≤ n then coeff (n - p ^ i) f else 0) :
    f = artinHasseExp p := by
  classical
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n.eq_zero_or_pos with rfl | hn
    · simpa using h₀
    · apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')
      rw [hrec, artinHasseExp_coeff_recurrence p hp]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs with hpi
      · exact ih _ (Nat.sub_lt hn (pow_pos (by omega : 0 < p) i))
      · rfl

end PowerSeries
