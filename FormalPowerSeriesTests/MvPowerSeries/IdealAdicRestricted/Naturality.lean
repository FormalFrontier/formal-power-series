/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.CompletedRename
import Mathlib.Algebra.GroupWithZero.Divisibility

/-!
# An infinite variable collapse over the 2-adic completion

The coefficient of `X i` in `binaryDecaySeries` is the image of `2 ^ i` in the
completion of `ℤ` at `(2)`, and every other coefficient is zero. The series has
infinite coefficient support, although every raw reduction, including precision
zero, is a finite polynomial. Renaming all variables to one variable gives
`-X ()`: at precision `n`, the colliding coefficients sum to `2 ^ n - 1 = -1`.

The construction uses the existing polynomial-reduction subalgebra and the raw
completion evaluations. Polynomial renaming and the geometric-sum identity are
from Mathlib; no completeness of the original coefficient ring is assumed.
-/

set_option warningAsError true

open scoped BigOperators

namespace FormalPowerSeriesTests.MvPowerSeries.IdealAdicRestricted.Naturality

local notation "I₂" => Ideal.span ({(2 : ℤ)} : Set ℤ)
local notation "A₂" => AdicCompletion I₂ ℤ
local notation "q₂" =>
  (fun n : ℕ => (AdicCompletion.evalₐ I₂ n : A₂ →+* ℤ ⧸ I₂ ^ n))

private noncomputable def binaryCoefficients : MvPowerSeries ℕ A₂ := by
  classical
  exact fun d => ∑ i ∈ d.support,
    if d = Finsupp.single i 1 then AdicCompletion.of I₂ ℤ (2 ^ i) else 0

private theorem coeff_binaryCoefficients_single (i : ℕ) :
    MvPowerSeries.coeff (Finsupp.single i 1) binaryCoefficients =
      AdicCompletion.of I₂ ℤ (2 ^ i) := by
  classical
  simp [MvPowerSeries.coeff_apply, binaryCoefficients]

private theorem coeff_binaryCoefficients_of_not_single (d : ℕ →₀ ℕ)
    (hd : ∀ i, d ≠ Finsupp.single i 1) :
    MvPowerSeries.coeff d binaryCoefficients = 0 := by
  classical
  change (∑ i ∈ d.support,
    if d = Finsupp.single i 1 then AdicCompletion.of I₂ ℤ (2 ^ i) else 0) = 0
  exact Finset.sum_eq_zero (fun i _ => ite_eq_right (hd i))

private theorem quotient_pow_two_eq_zero {n i : ℕ} (hni : n ≤ i) :
    Ideal.Quotient.mk (I₂ ^ n) (2 ^ i : ℤ) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.pow_le_pow_right hni
    (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (2 : ℤ)) i)

private theorem quotient_pow_two_ne_zero (i : ℕ) :
    Ideal.Quotient.mk (I₂ ^ (i + 1)) (2 ^ i : ℤ) ≠ 0 := by
  intro hzero
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  have hpow : (2 : ℤ) ^ i ≠ 0 := pow_ne_zero i (by decide)
  have hdiv : (2 : ℤ) ∣ 1 := by
    apply (mul_dvd_mul_iff_left hpow).mp
    simpa only [pow_succ, mul_one] using hmem
  exact (by decide : ¬(2 : ℤ) ∣ 1) hdiv

private theorem of_pow_two_ne_zero (i : ℕ) :
    AdicCompletion.of I₂ ℤ (2 ^ i) ≠ 0 := by
  intro hzero
  apply quotient_pow_two_ne_zero i
  have h := congrArg (AdicCompletion.evalₐ I₂ (i + 1)) hzero
  simpa only [AdicCompletion.evalₐ_of, map_zero] using h

private noncomputable def binaryRow (n : ℕ) : MvPolynomial ℕ (ℤ ⧸ I₂ ^ n) :=
  ∑ i ∈ Finset.range n,
    MvPolynomial.monomial (Finsupp.single i 1)
      (Ideal.Quotient.mk (I₂ ^ n) (2 ^ i : ℤ))

private theorem coeff_binaryRow_single (n i : ℕ) :
    (binaryRow n).coeff (Finsupp.single i 1) =
      if i < n then Ideal.Quotient.mk (I₂ ^ n) (2 ^ i : ℤ) else 0 := by
  classical
  simp only [binaryRow, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0),
    Finset.sum_ite_eq', Finset.mem_range]

private theorem coeff_binaryRow_of_not_single (n : ℕ) (d : ℕ →₀ ℕ)
    (hd : ∀ i, d ≠ Finsupp.single i 1) :
    (binaryRow n).coeff d = 0 := by
  classical
  rw [binaryRow, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [MvPolynomial.coeff_monomial, ite_eq_right (Ne.symm (hd i))]

private theorem map_binaryCoefficients (n : ℕ) :
    MvPowerSeries.map (q₂ n) binaryCoefficients =
      (binaryRow n : MvPowerSeries ℕ (ℤ ⧸ I₂ ^ n)) := by
  classical
  apply MvPowerSeries.ext
  intro d
  rw [MvPowerSeries.coeff_map, MvPolynomial.coeff_coe]
  by_cases hd : ∃ i, d = Finsupp.single i 1
  · obtain ⟨i, rfl⟩ := hd
    rw [coeff_binaryCoefficients_single, coeff_binaryRow_single]
    change AdicCompletion.evalₐ I₂ n (AdicCompletion.of I₂ ℤ (2 ^ i)) = _
    rw [AdicCompletion.evalₐ_of]
    by_cases hi : i < n
    · rw [ite_eq_left hi]
    · rw [ite_eq_right hi]
      exact quotient_pow_two_eq_zero (Nat.le_of_not_gt hi)
  · have hd' : ∀ i, d ≠ Finsupp.single i 1 := fun i h => hd ⟨i, h⟩
    rw [coeff_binaryCoefficients_of_not_single d hd',
      coeff_binaryRow_of_not_single n d hd', map_zero]

/-- The series with coefficient `of (2 ^ i)` at `X i` and zero at every other
monomial, regarded as an element of the raw polynomial-reduction subalgebra. -/
public noncomputable def binaryDecaySeries :
    MvPowerSeries.polynomialReductionSubalgebra ℕ q₂ := by
  refine ⟨binaryCoefficients, ?_⟩
  rw [MvPowerSeries.mem_polynomialReductionSubalgebra]
  intro n
  refine ⟨binaryRow n, ?_⟩
  simpa only [MvPolynomial.coeToMvPowerSeries.ringHom_apply] using
    (map_binaryCoefficients n).symm

/-- Each variable has its prescribed nonzero completed coefficient. -/
public theorem coeff_binaryDecaySeries_single (i : ℕ) :
    MvPowerSeries.coeff (Finsupp.single i 1) binaryDecaySeries.val =
      AdicCompletion.of I₂ ℤ (2 ^ i) :=
  coeff_binaryCoefficients_single i

/-- Every raw row is the finite polynomial of the first `n` decaying terms;
this includes the empty polynomial at precision zero. -/
public theorem polynomialReduction_binaryDecaySeries (n : ℕ) :
    MvPowerSeries.polynomialReduction ℕ q₂ n binaryDecaySeries =
      ∑ i ∈ Finset.range n,
        MvPolynomial.monomial (Finsupp.single i 1)
          (Ideal.Quotient.mk (I₂ ^ n) (2 ^ i : ℤ)) := by
  apply MvPolynomial.coe_injective ℕ (ℤ ⧸ I₂ ^ n)
  rw [MvPowerSeries.polynomialReduction_coe]
  exact map_binaryCoefficients n

private theorem binaryDecaySeries_support_infinite :
    {d : ℕ →₀ ℕ | MvPowerSeries.coeff d binaryDecaySeries.val ≠ 0}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun i : ℕ => Finsupp.single i 1)
    (Finsupp.single_left_injective (one_ne_zero : (1 : ℕ) ≠ 0)) ?_
  intro i
  change MvPowerSeries.coeff (Finsupp.single i 1) binaryDecaySeries.val ≠ 0
  rw [coeff_binaryDecaySeries_single]
  exact of_pow_two_ne_zero i

private theorem sum_quotient_pow_two (n : ℕ) :
    (∑ i ∈ Finset.range n, Ideal.Quotient.mk (I₂ ^ n) (2 ^ i : ℤ)) = -1 := by
  rw [← map_sum]
  have hgeom : (∑ i ∈ Finset.range n, (2 ^ i : ℤ)) = 2 ^ n - 1 := by
    simpa using geom_sum_mul (2 : ℤ) n
  rw [hgeom, map_sub, quotient_pow_two_eq_zero (le_refl n), map_one, zero_sub]

private theorem rename_binaryRow (n : ℕ) :
    MvPolynomial.rename (fun _ : ℕ => ()) (binaryRow n) =
      -(MvPolynomial.X () : MvPolynomial Unit (ℤ ⧸ I₂ ^ n)) := by
  classical
  calc
    MvPolynomial.rename (fun _ : ℕ => ()) (binaryRow n) =
        ∑ i ∈ Finset.range n,
          MvPolynomial.monomial (Finsupp.single () 1)
            (Ideal.Quotient.mk (I₂ ^ n) (2 ^ i : ℤ)) := by
      simp only [binaryRow, map_sum, MvPolynomial.rename_monomial,
        Finsupp.mapDomain_single]
    _ = MvPolynomial.monomial (Finsupp.single () 1) (-1) := by
      rw [← map_sum, sum_quotient_pow_two]
    _ = -MvPolynomial.X () := by
      exact map_neg (MvPolynomial.monomial (Finsupp.single () 1)) 1

private theorem binaryDecaySeries_collapse_rows (n : ℕ) :
    MvPolynomial.rename (fun _ : ℕ => ())
        (MvPowerSeries.polynomialReduction ℕ q₂ n binaryDecaySeries) =
      MvPowerSeries.polynomialReduction Unit q₂ n
        (MvPowerSeries.polynomialToReductionSubalgebra Unit q₂
          (-(MvPolynomial.X () : MvPolynomial Unit A₂))) := by
  rw [polynomialReduction_binaryDecaySeries,
    MvPowerSeries.polynomialReduction_polynomial]
  change MvPolynomial.rename (fun _ : ℕ => ()) (binaryRow n) =
    MvPolynomial.map (q₂ n) (-(MvPolynomial.X () : MvPolynomial Unit A₂))
  rw [map_neg, MvPolynomial.map_X]
  exact rename_binaryRow n

private theorem neg_one_eval_ne_zero :
    AdicCompletion.evalₐ I₂ 1 (-1 : A₂) ≠ 0 := by
  intro hzero
  have hneg : (-1 : ℤ ⧸ I₂ ^ 1) = 0 := by
    simpa only [map_neg, map_one] using hzero
  have hone : (1 : ℤ ⧸ I₂ ^ 1) = 0 := neg_eq_zero.mp hneg
  apply quotient_pow_two_ne_zero 0
  simpa only [pow_zero, map_one] using hone

/-- Infinitely many nonzero source coefficients collapse to the included polynomial
`-X ()` under the constant variable map. The resulting degree-one coefficient is
already nonzero modulo `2`, so this is a nonzero infinite-fiber collapse. -/
public theorem binaryDecaySeries_infinite_collapse :
    {d : ℕ →₀ ℕ | MvPowerSeries.coeff d binaryDecaySeries.val ≠ 0}.Infinite ∧
      MvPowerSeries.completedRestrictedRename I₂ (fun _ : ℕ => ()) binaryDecaySeries =
        MvPowerSeries.polynomialToReductionSubalgebra Unit q₂
          (-(MvPolynomial.X () : MvPolynomial Unit A₂)) ∧
      AdicCompletion.evalₐ I₂ 1 (-1 : A₂) ≠ 0 := by
  refine ⟨binaryDecaySeries_support_infinite, ?_, neg_one_eval_ne_zero⟩
  have hinj := (MvPowerSeries.polynomialReduction_jointly_injective_iff Unit q₂).2
    (fun a b hab => AdicCompletion.ext_evalₐ (fun n => congrFun hab n))
  apply hinj
  funext n
  exact (MvPowerSeries.polynomialReduction_completedRestrictedRename I₂
    (fun _ : ℕ => ()) n binaryDecaySeries).trans (binaryDecaySeries_collapse_rows n)

end FormalPowerSeriesTests.MvPowerSeries.IdealAdicRestricted.Naturality
