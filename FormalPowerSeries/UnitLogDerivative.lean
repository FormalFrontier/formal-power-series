/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring

/-! # Weighted negative logarithmic derivative of formal-series units

The map `negXLogDeriv` sends a native unit `f` over any commutative ring to
`-X * derivative (f : PowerSeries R) * (f⁻¹ : PowerSeries R)`. It turns products
into sums without dividing coefficients by natural numbers. Its naturality,
finite coefficient formulas and the native factor `oneSubCXUnit` are provided
below. No nontriviality, torsion-freeness or characteristic assumption is needed
except where a characteristic-kernel statement explicitly requests one.
-/

set_option warningAsError true

namespace PowerSeries

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The negative logarithmic derivative weighted by `X`, on native units. -/
public noncomputable def negXLogDeriv (f : (PowerSeries R)ˣ) : PowerSeries R :=
  -X * derivative (f : PowerSeries R) * ((f⁻¹ : (PowerSeries R)ˣ) : PowerSeries R)

/-- Multiplying by the unit recovers the weighted derivative, including in the zero ring. -/
public theorem negXLogDeriv_mul_value (f : (PowerSeries R)ˣ) :
    negXLogDeriv f * (f : PowerSeries R) = -X * derivative (f : PowerSeries R) := by
  simp [negXLogDeriv, mul_assoc]

@[simp] public theorem negXLogDeriv_one :
    negXLogDeriv (1 : (PowerSeries R)ˣ) = 0 := by
  simp [negXLogDeriv]

public theorem negXLogDeriv_mul (f g : (PowerSeries R)ˣ) :
    negXLogDeriv (f * g) = negXLogDeriv f + negXLogDeriv g := by
  apply (Units.mul_left_inj (f * g)).mp
  rw [negXLogDeriv_mul_value, Units.val_mul, derivative.leibniz]
  simp only [smul_eq_mul]
  calc
    -X * (↑f * derivative ↑g + ↑g * derivative ↑f) =
        (-X * derivative ↑f) * ↑g + (-X * derivative ↑g) * ↑f := by ring
    _ = (negXLogDeriv f * ↑f) * ↑g + (negXLogDeriv g * ↑g) * ↑f := by
      rw [negXLogDeriv_mul_value, negXLogDeriv_mul_value]
    _ = (negXLogDeriv f + negXLogDeriv g) * (↑f * ↑g) := by ring

@[simp] public theorem negXLogDeriv_inv (f : (PowerSeries R)ˣ) :
    negXLogDeriv f⁻¹ = -negXLogDeriv f := by
  have h := negXLogDeriv_mul f⁻¹ f
  simpa using (eq_neg_iff_add_eq_zero.mpr (h.symm.trans (by simp)))

public theorem negXLogDeriv_pow (f : (PowerSeries R)ˣ) (n : ℕ) :
    negXLogDeriv (f ^ n) = n • negXLogDeriv f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, negXLogDeriv_mul, ih, succ_nsmul]

public theorem negXLogDeriv_zpow (f : (PowerSeries R)ˣ) (n : ℤ) :
    negXLogDeriv (f ^ n) = n • negXLogDeriv f := by
  cases n with
  | ofNat n => simpa using negXLogDeriv_pow f n
  | negSucc n => simp [zpow_negSucc, negXLogDeriv_pow]; ring

public theorem negXLogDeriv_prod {ι : Type*} (s : Finset ι) (f : ι → (PowerSeries R)ˣ) :
    negXLogDeriv (∏ i ∈ s, f i) = ∑ i ∈ s, negXLogDeriv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, negXLogDeriv_mul, ih]

private theorem derivative_map (ρ : R →+* S) (f : PowerSeries R) :
    derivative (PowerSeries.map ρ f) = PowerSeries.map ρ (derivative f) := by
  ext n
  simp [coeff_derivative, coeff_map]

/-- Naturality holds across arbitrary (possibly distinct) coefficient universes. -/
public theorem negXLogDeriv_map (ρ : R →+* S) (f : (PowerSeries R)ˣ) :
    negXLogDeriv (Units.map (PowerSeries.map ρ).toMonoidHom f) =
      PowerSeries.map ρ (negXLogDeriv f) := by
  simp [negXLogDeriv, derivative_map]

/-- Native unit multiplication, written additively, maps to series addition. -/
public noncomputable def negXLogDerivHom :
    Additive ((PowerSeries R)ˣ) →+ PowerSeries R where
  toFun f := negXLogDeriv f.toMul
  map_zero' := negXLogDeriv_one
  map_add' f g := negXLogDeriv_mul f.toMul g.toMul

@[simp] public theorem negXLogDeriv_constant (a : Rˣ) :
    negXLogDeriv (Units.map (C : R →+* PowerSeries R).toMonoidHom a) = 0 := by
  simp [negXLogDeriv]

/-- Cancellation characterizes the image of a given unit without dividing by `n`. -/
public theorem eq_negXLogDeriv_iff (f : (PowerSeries R)ˣ) (g : PowerSeries R) :
    g = negXLogDeriv f ↔ g * (f : PowerSeries R) = -X * derivative (f : PowerSeries R) := by
  rw [← negXLogDeriv_mul_value, Units.mul_left_inj]

/-- A `p`th power is in the kernel in characteristic `p`. -/
public theorem negXLogDeriv_pow_char (p : ℕ) [CharP R p] (f : (PowerSeries R)ˣ) :
    negXLogDeriv (f ^ p) = 0 := by
  rw [negXLogDeriv_pow, nsmul_eq_mul]
  have hp : (p : PowerSeries R) = 0 := by
    rw [← map_natCast (C : R →+* PowerSeries R), CharP.cast_eq_zero R p, map_zero]
  rw [hp, zero_mul]

@[simp] public theorem coeff_zero_negXLogDeriv (f : (PowerSeries R)ˣ) :
    coeff 0 (negXLogDeriv f) = 0 := by
  simp [negXLogDeriv]

/-- The unnormalized finite convolution formula, valid even if the constant term is not one. -/
public theorem coeff_negXLogDeriv_convolution (f : (PowerSeries R)ˣ) (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal (n + 1),
      coeff p.1 (negXLogDeriv f) * coeff p.2 (f : PowerSeries R) =
        -(coeff (n + 1) (f : PowerSeries R) * (n + 1)) := by
  have h := congrArg (coeff (n + 1)) (negXLogDeriv_mul_value f)
  rw [neg_mul, map_neg, coeff_succ_X_mul, coeff_derivative, coeff_mul] at h
  exact h

/-- Integral coefficient recurrence, assuming exactly `coeff 0 f = 1`. -/
public theorem coeff_negXLogDeriv_recurrence (f : (PowerSeries R)ˣ)
    (h0 : coeff 0 (f : PowerSeries R) = 1) (n : ℕ) :
    coeff (n + 1) (negXLogDeriv f) +
      ∑ i ∈ Finset.range n,
        coeff (i + 1) (f : PowerSeries R) * coeff (n - i) (negXLogDeriv f) =
      -(coeff (n + 1) (f : PowerSeries R) * (n + 1)) := by
  have h := congrArg (coeff (n + 1)) (negXLogDeriv_mul_value f)
  rw [neg_mul, map_neg, coeff_succ_X_mul, coeff_derivative,
    mul_comm (negXLogDeriv f), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i (f : PowerSeries R) * coeff j (negXLogDeriv f)),
    Finset.sum_range_succ, Finset.sum_range_succ'] at h
  simpa [h0, add_comm] using h

/-- Native unit with underlying series `1 - C a * X`, using the geometric-series unit. -/
public noncomputable def oneSubCXUnit (a : R) : (PowerSeries R)ˣ :=
  Units.map (rescale a).toMonoidHom (invOneSubPow R 1)⁻¹

@[simp] public theorem oneSubCXUnit_val (a : R) :
    (oneSubCXUnit a : PowerSeries R) = 1 - C a * X := by
  change rescale a (invOneSubPow R 1).inv = _
  rw [invOneSubPow_inv_eq_one_sub_pow]
  simp [rescale_X]

@[simp] public theorem coeff_oneSubCXUnit_inv (a : R) (n : ℕ) :
    coeff n ((oneSubCXUnit a)⁻¹ : (PowerSeries R)ˣ) = a ^ n := by
  simp [oneSubCXUnit, invOneSubPow, coeff_rescale]

/-- The weighted derivative of a linear factor is `X * C a / (1 - C a * X)`. -/
public theorem negXLogDeriv_oneSubCXUnit (a : R) :
    negXLogDeriv (oneSubCXUnit a) =
      X * (C a * (((oneSubCXUnit a)⁻¹ : (PowerSeries R)ˣ) : PowerSeries R)) := by
  simp [negXLogDeriv, derivative.leibniz, smul_eq_mul]
  ring

/-- Positive-degree coefficients of the weighted derivative of a linear factor. -/
public theorem coeff_succ_negXLogDeriv_oneSubCXUnit (a : R) (n : ℕ) :
    coeff (n + 1) (negXLogDeriv (oneSubCXUnit a)) = a ^ (n + 1) := by
  rw [negXLogDeriv_oneSubCXUnit, coeff_succ_X_mul, coeff_C_mul,
    coeff_oneSubCXUnit_inv, pow_succ, mul_comm]

end PowerSeries
