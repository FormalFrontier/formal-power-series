/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module
public import FormalPowerSeries
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-! # Public-import examples and boundary checks

These examples intentionally import only the public library root for their
formal-power-series API; the other imports supply test coefficients and tactics.
-/

set_option warningAsError true

namespace FormalPowerSeriesTests

open PowerSeries

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

public theorem arbitrary_ring_product (f g : (PowerSeries R)ˣ) :
    negXLogDeriv (f * g) = negXLogDeriv f + negXLogDeriv g := negXLogDeriv_mul f g

public theorem torsion_ring_product (f g : (PowerSeries (ZMod 4))ˣ) :
    negXLogDeriv (f * g) = negXLogDeriv f + negXLogDeriv g := negXLogDeriv_mul f g

public theorem empty_product :
    negXLogDeriv (∏ i ∈ (∅ : Finset ℕ), oneSubCXUnit (i : R)) = 0 := by simp

public theorem degree_zero (f : (PowerSeries R)ˣ) :
    coeff 0 (negXLogDeriv f) = 0 := coeff_zero_negXLogDeriv f

public theorem normalized_degree_one (f : (PowerSeries R)ˣ)
    (h : coeff 0 (f : PowerSeries R) = 1) :
    coeff 1 (negXLogDeriv f) = -coeff 1 (f : PowerSeries R) := by
  simpa using coeff_negXLogDeriv_recurrence f h 0

public theorem line_degree_one (a : R) :
    coeff 1 (negXLogDeriv (oneSubCXUnit a)) = a := by
  simpa using coeff_succ_negXLogDeriv_oneSubCXUnit a 0

public theorem signedExample {T : Type*} [CommRing T]
    (a : T) (n : ℕ) :
    PowerSeries.coeff (n + 1)
      (PowerSeries.negXLogDeriv (PowerSeries.oneSubCXUnit a)) = a ^ (n + 1) :=
  PowerSeries.coeff_succ_negXLogDeriv_oneSubCXUnit a n

public theorem negative_power (f : (PowerSeries R)ˣ) :
    negXLogDeriv (f ^ (-3 : ℤ)) = (-3 : ℤ) • negXLogDeriv f :=
  negXLogDeriv_zpow f (-3)

public theorem cross_ring (ρ : R →+* S) (f : (PowerSeries R)ˣ) (n : ℕ) :
    coeff n (negXLogDeriv (Units.map (PowerSeries.map ρ).toMonoidHom f)) =
      ρ (coeff n (negXLogDeriv f)) := by
  rw [negXLogDeriv_map, coeff_map]

/-- Explicitly distinct coefficient universes at a public-import call site. -/
public theorem independent_universes {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (ρ : A →+* B) (f : (PowerSeries A)ˣ) :
    negXLogDeriv (Units.map (PowerSeries.map ρ).toMonoidHom f) =
      PowerSeries.map ρ (negXLogDeriv f) := negXLogDeriv_map ρ f

public theorem native_additive_tag (f g : Additive ((PowerSeries R)ˣ)) :
    negXLogDerivHom (f + g) = negXLogDerivHom f + negXLogDerivHom g :=
  map_add negXLogDerivHom f g

public theorem constant_kernel (a : Rˣ) :
    negXLogDeriv (Units.map (C : R →+* PowerSeries R).toMonoidHom a) = 0 :=
  negXLogDeriv_constant a

public theorem inverse_factor_coeff (a : R) (n : ℕ) :
    coeff n ((oneSubCXUnit a)⁻¹ : (PowerSeries R)ˣ) = a ^ n :=
  coeff_oneSubCXUnit_inv a n

public theorem zero_ring (f : (PowerSeries (ZMod 1))ˣ) : negXLogDeriv f = 0 := by
  ext n
  exact Subsingleton.elim _ _

public theorem char_two_kernel : negXLogDeriv (oneSubCXUnit (1 : ZMod 2) ^ 2) = 0 :=
  negXLogDeriv_pow_char 2 _

/-- A normalized nonidentity native unit has zero weighted derivative in characteristic two. -/
public theorem char_two_nonidentity : oneSubCXUnit (1 : ZMod 2) ^ 2 ≠ 1 := by
  intro h
  have hc := congrArg (fun f : (PowerSeries (ZMod 2))ˣ =>
    coeff 2 (f : PowerSeries (ZMod 2))) h
  norm_num [oneSubCXUnit_val, pow_two, sub_mul, mul_sub,
    coeff_succ_X_mul, coeff_succ_mul_X, coeff_X] at hc

public theorem char_two_normalized :
    coeff 0 ((oneSubCXUnit (1 : ZMod 2) ^ 2 : (PowerSeries (ZMod 2))ˣ) :
      PowerSeries (ZMod 2)) = 1 := by simp

public theorem not_injective_in_char_two :
    ¬Function.Injective (negXLogDeriv (R := ZMod 2)) := by
  intro h
  exact char_two_nonidentity (h (char_two_kernel.trans negXLogDeriv_one.symm))

/-- An integer-coefficient example with constant term `-1`, not `1`. -/
public noncomputable def nonnormalizedUnit : (PowerSeries ℤ)ˣ :=
  (-1) * oneSubCXUnit 2

public theorem nonnormalized_constant :
    coeff 0 (nonnormalizedUnit : PowerSeries ℤ) = -1 := by
  simp [nonnormalizedUnit, oneSubCXUnit_val]

public theorem nonnormalized_ne_one :
    coeff 0 (nonnormalizedUnit : PowerSeries ℤ) ≠ 1 := by
  rw [nonnormalized_constant]
  norm_num

public theorem nonnormalized_characterization :
    negXLogDeriv nonnormalizedUnit * (nonnormalizedUnit : PowerSeries ℤ) =
      -X * derivative (nonnormalizedUnit : PowerSeries ℤ) :=
  (eq_negXLogDeriv_iff nonnormalizedUnit _).mp rfl

public theorem nonnormalized_convolution (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal (n + 1),
      coeff p.1 (negXLogDeriv nonnormalizedUnit) *
        coeff p.2 (nonnormalizedUnit : PowerSeries ℤ) =
      -(coeff (n + 1) (nonnormalizedUnit : PowerSeries ℤ) * (n + 1)) :=
  coeff_negXLogDeriv_convolution nonnormalizedUnit n

/-- Signed finite products include inverse factors and the empty family. -/
public theorem signed_factors {ι : Type*} (s : Finset ι) (a : ι → R) (z : ι → ℤ)
    (n : ℕ) :
    coeff (n + 1) (negXLogDeriv (∏ i ∈ s, (oneSubCXUnit (a i)) ^ (z i))) =
      ∑ i ∈ s, (z i) • (a i) ^ (n + 1) := by
  rw [negXLogDeriv_prod]
  simp only [map_sum, negXLogDeriv_zpow, map_zsmul,
    coeff_succ_negXLogDeriv_oneSubCXUnit]

public theorem signed_factors_empty {ι : Type*} (a : ι → R) (z : ι → ℤ)
    (n : ℕ) :
    coeff (n + 1) (negXLogDeriv (∏ i ∈ (∅ : Finset ι),
      (oneSubCXUnit (a i)) ^ (z i))) = 0 := by
  simp

public theorem signed_factors_negative_singleton (a : R) (n : ℕ) :
    coeff (n + 1) (negXLogDeriv (∏ _i ∈ ({()} : Finset Unit),
      (oneSubCXUnit a) ^ (-3 : ℤ))) = (-3 : ℤ) • a ^ (n + 1) := by
  simpa only [Finset.sum_singleton] using
    signed_factors ({()} : Finset Unit) (fun _ => a) (fun _ => (-3 : ℤ)) n

end FormalPowerSeriesTests
