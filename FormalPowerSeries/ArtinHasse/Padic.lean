/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.ArtinHasse
public import Mathlib.NumberTheory.Padics.PadicNumbers

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.RingTheory.DividedPowers.Padic
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# p-integrality of the Artin–Hasse exponential

For every prime `p`, each rational coefficient of `PowerSeries.artinHasseExp p`
has multiplicative p-adic valuation at most one. This is the coefficient
integrality assertion of Fesenko–Vostokov I.(9.1).

The proof uses the standard Dieudonné–Dwork method: the logarithm shift gives
`E(X)^p = E(X^p) exp(pX)`, and Mathlib's divided powers on `(p) ⊆ ℤ_[p]`
make the positive coefficients of `exp(pX)` divisible by `p`. A coefficientwise
induction then places every coefficient of `E` in the p-adic integers. The
rational construction and recurrence remain in `FormalPowerSeries.ArtinHasse`.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition (2002), Chapter I, (9.1), pp. 29–30.
* The standard Dieudonné–Dwork integrality method.
* Mathlib's p-adic integers, divided powers, and formal power series APIs.
-/

@[expose] public section

namespace PowerSeries

-- Reduction to the prime field combines Frobenius with the divisibility of
-- the positive-degree correction coefficients; no normalization of `f` is needed.
private theorem coeff_pow_sub_expand_mul_dvd_prime (p : ℕ) [Fact p.Prime]
    (f g : PowerSeries ℤ_[p]) (hg₀ : constantCoeff g = 1)
    (hg : ∀ n : ℕ, n ≠ 0 → ∃ z : ℤ_[p], coeff n g = (p : ℤ_[p]) * z)
    (n : ℕ) :
    ∃ z : ℤ_[p],
      coeff n (f ^ p - f.expand p (Fact.out : p.Prime).ne_zero * g) = (p : ℤ_[p]) * z := by
  let φ : ℤ_[p] →+* ZMod p := PadicInt.toZMod
  have hgmap : map φ g = 1 := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp [coeff_map, coeff_zero_eq_constantCoeff, hg₀]
    · obtain ⟨z, hz⟩ := hg i hi
      simp [coeff_map, hz, hi]
  have hFrob : frobenius (ZMod p) p = RingHom.id (ZMod p) := by
    ext x
    exact ZMod.pow_card x
  have hfmap : (map φ f) ^ p = (map φ f).expand p (Fact.out : p.Prime).ne_zero := by
    simpa [hFrob, map_id] using
      (map_frobenius_expand p (Fact.out : p.Prime).ne_zero (f := map φ f)).symm
  have hmap : map φ (f ^ p - f.expand p (Fact.out : p.Prime).ne_zero * g) = 0 := by
    rw [map_sub, map_pow, map_mul, map_expand, hgmap, mul_one, hfmap, sub_self]
  have hker : coeff n (f ^ p - f.expand p (Fact.out : p.Prime).ne_zero * g) ∈
      RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
    rw [RingHom.mem_ker]
    change φ (coeff n _) = 0
    rw [← coeff_map, hmap, map_zero]
  rwa [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton] at hker

private theorem coeff_mul_of_coeff_lt_eq_zero {R : Type*} [Semiring R]
    {u v : PowerSeries R} {n : ℕ} (hu : ∀ k < n, coeff k u = 0) :
    coeff n (u * v) = coeff n u * constantCoeff v := by
  classical
  rw [coeff_mul, Finset.sum_eq_single_of_mem (n, 0) (by simp)]
  · rw [coeff_zero_eq_constantCoeff]
  · intro ij hij hne
    have hsum := Finset.mem_antidiagonal.mp hij
    have hi : ij.1 < n := by
      by_contra h
      exact hne (Prod.ext (by omega) (by omega))
    rw [hu _ hi, zero_mul]

private theorem coeff_pow_sub_pow_of_coeff_lt_eq {R : Type*} [CommRing R]
    {f g : PowerSeries R} {n : ℕ} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 1) (hlt : ∀ k < n, coeff k f = coeff k g) (m : ℕ) :
    coeff n (f ^ m - g ^ m) = (m : R) * (coeff n f - coeff n g) := by
  classical
  rw [← (Commute.all f g).mul_geom_sum₂ m,
    coeff_mul_of_coeff_lt_eq_zero (fun k hk => by simp only [map_sub, hlt k hk, sub_self])]
  simp [hf, hg, mul_comm]

private theorem coeff_exists_padicInt_of_pow_eq_expand_mul (p : ℕ) [Fact p.Prime]
    (f : PowerSeries ℚ_[p]) (g : PowerSeries ℤ_[p])
    (hf₀ : constantCoeff f = 1) (hg₀ : constantCoeff g = 1)
    (hg : ∀ n : ℕ, n ≠ 0 → ∃ z : ℤ_[p], coeff n g = (p : ℤ_[p]) * z)
    (hFE : f ^ p = f.expand p (Fact.out : p.Prime).ne_zero *
      map (algebraMap ℤ_[p] ℚ_[p]) g) (n : ℕ) :
    ∃ z : ℤ_[p], coeff n f = (z : ℚ_[p]) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n.eq_zero_or_pos with rfl | hn
    · exact ⟨1, by simpa only [coeff_zero_eq_constantCoeff, PadicInt.coe_one] using hf₀⟩
    · let φ : ℤ_[p] →+* ℚ_[p] := algebraMap ℤ_[p] ℚ_[p]
      -- Only coefficients in degrees strictly below `n` are lowered to `ℤ_[p]`.
      let P : PowerSeries ℤ_[p] :=
        mk fun i => if hi : i < n then Classical.choose (ih i hi) else 0
      have hPcoeff (i : ℕ) (hi : i < n) : coeff i (map φ P) = coeff i f := by
        simp only [coeff_map, P, coeff_mk, dite_eq_left hi]
        exact (Classical.choose_spec (ih i hi)).symm
      have hPn : coeff n (map φ P) = 0 := by simp [P, coeff_map]
      have hP₀ : constantCoeff (map φ P) = 1 := by
        rw [← coeff_zero_eq_constantCoeff, hPcoeff 0 hn, coeff_zero_eq_constantCoeff, hf₀]
      have hpow : coeff n (f ^ p - (map φ P) ^ p) = (p : ℚ_[p]) * coeff n f := by
        simpa only [hPn, sub_zero] using
          coeff_pow_sub_pow_of_coeff_lt_eq hf₀ hP₀ (fun i hi => (hPcoeff i hi).symm) p
      have hexpand (i : ℕ) (hi : i ≤ n) :
          coeff i (f.expand p (Fact.out : p.Prime).ne_zero) =
            coeff i ((map φ P).expand p (Fact.out : p.Prime).ne_zero) := by
        rw [coeff_expand, coeff_expand]
        split_ifs with hpi
        · exact (hPcoeff (i / p) ((Nat.div_le_div_right hi).trans_lt
            (Nat.div_lt_self hn (Fact.out : p.Prime).one_lt))).symm
        · rfl
      have hprod : coeff n (f.expand p (Fact.out : p.Prime).ne_zero * map φ g) =
          coeff n ((map φ P).expand p (Fact.out : p.Prime).ne_zero * map φ g) := by
        rw [coeff_mul, coeff_mul]
        apply Finset.sum_congr rfl
        intro ij hij
        rw [hexpand ij.1 (by have := Finset.mem_antidiagonal.mp hij; omega)]
      obtain ⟨z, hz⟩ := coeff_pow_sub_expand_mul_dvd_prime p P g hg₀ hg n
      have hzQ : coeff n ((map φ P) ^ p -
          (map φ P).expand p (Fact.out : p.Prime).ne_zero * map φ g) =
            (p : ℚ_[p]) * (z : ℚ_[p]) := by
        have hz' := congrArg φ hz
        rw [← coeff_map] at hz'
        simpa only [map_sub, map_pow, map_mul, map_expand, map_natCast,
          φ, PadicInt.algebraMap_apply] using hz'
      refine ⟨-z, ?_⟩
      apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
      calc
        (p : ℚ_[p]) * coeff n f = coeff n (f ^ p - (map φ P) ^ p) := hpow.symm
        _ = -coeff n ((map φ P) ^ p -
            (map φ P).expand p (Fact.out : p.Prime).ne_zero * map φ g) := by
          rw [map_sub, hFE, hprod, map_sub]
          ring
        _ = (p : ℚ_[p]) * ((-z : ℤ_[p]) : ℚ_[p]) := by rw [hzQ]; simp

private theorem coeff_rescale_exp_eq_prime_mul_padicInt
    (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    ∃ z : ℤ_[p], coeff n (rescale (p : ℚ_[p]) (exp ℚ_[p])) =
      (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp : (p : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} :=
    Ideal.mem_span_singleton_self _
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp
    ((PadicInt.dividedPowers p).dpow_mem hn hp)
  refine ⟨z, ?_⟩
  have hcoe := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hz
  rw [PadicInt.coe_dpow_eq, dite_eq_left hp, PadicInt.coe_mul, PadicInt.coe_natCast,
    Ring.inverse_eq_inv'] at hcoe
  rw [coeff_rescale, coeff_exp]
  simpa only [one_div, map_inv₀, map_natCast, mul_comm] using hcoe

-- Multiplication by `p` shifts the positive powers in the logarithm's support.
private theorem artinHasseLog_shift (p : ℕ) (hp : 2 ≤ p) :
    (p : ℚ) • artinHasseLog p =
      (p : ℚ) • X + (artinHasseLog p).expand p (by omega) := by
  classical
  have hp0 : p ≠ 0 := by omega
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  ext n
  simp only [map_add, coeff_smul]
  by_cases hn : ∃ i : ℕ, p ^ i = n
  · obtain ⟨i, rfl⟩ := hn
    cases i with
    | zero =>
      have hl1 : coeff 1 (artinHasseLog p) = 1 := by
        simpa using coeff_artinHasseLog_pow p 0
      rw [pow_zero,
        coeff_expand_of_not_dvd p hp0 _ (by simpa using (show p ≠ 1 by omega))]
      simp [hl1]
    | succ i =>
      have hne : p ^ (i + 1) ≠ 1 := by
        have := Nat.pow_lt_pow_right (by omega : 1 < p) (Nat.succ_pos i)
        simpa using ne_of_gt this
      have he : coeff (p ^ (i + 1)) ((artinHasseLog p).expand p hp0) =
          coeff (p ^ i) (artinHasseLog p) := by
        rw [pow_succ', coeff_expand_mul]
      rw [coeff_artinHasseLog_pow, he]
      rw [coeff_X, ite_eq_right hne]
      simp [coeff_artinHasseLog_pow, pow_succ, hpQ]
  · have hn1 : n ≠ 1 := fun h => hn ⟨0, by simpa using h.symm⟩
    rw [coeff_artinHasseLog, ite_eq_right hn, coeff_expand]
    simp only [smul_eq_mul, mul_zero, coeff_X, hn1, ite_false]
    split_ifs with hdiv
    · have hquot : ¬ ∃ i : ℕ, p ^ i = n / p := by
        rintro ⟨i, hi⟩
        apply hn
        exact ⟨i + 1, by rw [pow_succ', hi, Nat.mul_div_cancel' hdiv]⟩
      simp [coeff_artinHasseLog, hquot]
    · simp

-- The logarithm shift gives a common differential equation for the two sides.
-- Their quotient has derivative zero and constant coefficient one.
private theorem artinHasseExp_functional_equation (p : ℕ) (hp : 2 ≤ p) :
    artinHasseExp p ^ p = (artinHasseExp p).expand p (by omega) *
      rescale (p : ℚ) (exp ℚ) := by
  have hp0 : p ≠ 0 := by omega
  let f := artinHasseExp p ^ p
  let g := rescale (p : ℚ) (exp ℚ)
  let h := (artinHasseExp p).expand p hp0 * g
  let q := (p : ℚ) • derivative (artinHasseLog p)
  have hL := HasSubst.of_constantCoeff_zero' (constantCoeff_artinHasseLog p)
  have hLe : HasSubst ((artinHasseLog p).expand p hp0) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  have hDf : derivative f = f * q := by
    dsimp [f, q]
    rw [derivative_pow, derivative_artinHasseExp, smul_eq_C_mul, map_natCast]
    have hpow : artinHasseExp p ^ (p - 1) * artinHasseExp p = artinHasseExp p ^ p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    calc
      (p : PowerSeries ℚ) * artinHasseExp p ^ (p - 1) *
          (artinHasseExp p * derivative (artinHasseLog p)) =
          (artinHasseExp p ^ (p - 1) * artinHasseExp p) *
            ((p : PowerSeries ℚ) * derivative (artinHasseLog p)) := by ring
      _ = _ := by rw [hpow]
  have hDg : derivative g = g * C (p : ℚ) := by
    dsimp [g]
    rw [rescale_eq_subst, derivative_subst (HasSubst.smul_X' (p : ℚ)), derivative_exp]
    rw [derivative.map_smul, derivative_X]
    simp only [smul_eq_C_mul, mul_one]
  have hDe : derivative ((artinHasseExp p).expand p hp0) =
      (artinHasseExp p).expand p hp0 * derivative ((artinHasseLog p).expand p hp0) := by
    have he : (artinHasseExp p).expand p hp0 =
        subst ((artinHasseLog p).expand p hp0) (exp ℚ) := by
      rw [artinHasseExp_eq_subst]
      exact expand_subst p hp0 hL (exp ℚ)
    rw [he, derivative_subst hLe, derivative_exp]
  have hshift : q = C (p : ℚ) + derivative ((artinHasseLog p).expand p hp0) := by
    have hs := congrArg (derivative (R := ℚ)) (artinHasseLog_shift p hp)
    rw [derivative.map_smul, map_add, derivative.map_smul, derivative_X] at hs
    simpa only [q, smul_eq_C_mul, mul_one] using hs
  have hDh : derivative h = h * q := by
    dsimp only [h]
    rw [derivative.leibniz, hDe, hDg, hshift]
    simp only [smul_eq_mul]
    ring
  have hg0 : constantCoeff g = 1 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp [g, coeff_rescale]
  have hconst : constantCoeff h = 1 := by simp [h, hg0]
  have hinv : h * h⁻¹ = 1 := PowerSeries.mul_inv_cancel h (by rw [hconst]; exact one_ne_zero)
  have hquot : f * h⁻¹ = 1 := by
    apply derivative.ext
    · rw [derivative.leibniz, derivative_inv', hDf, hDh, derivative_one]
      simp only [smul_eq_mul]
      calc
        f * (-(h⁻¹ ^ 2) * (h * q)) + h⁻¹ * (f * q) =
            (f * q * h⁻¹) * (1 - h * h⁻¹) := by ring
        _ = 0 := by rw [hinv]; simp
    · simp [f, hconst]
  calc
    f = f * (h⁻¹ * h) := by rw [mul_comm h⁻¹ h, hinv, mul_one]
    _ = h := by rw [← mul_assoc, hquot, one_mul]

-- Choose integral coefficients only for the correction series `exp(pX)`.
private theorem exists_padicInt_rescale_exp (p : ℕ) [Fact p.Prime] :
    ∃ g : PowerSeries ℤ_[p], constantCoeff g = 1 ∧
      (∀ n : ℕ, n ≠ 0 → ∃ z : ℤ_[p], coeff n g = (p : ℤ_[p]) * z) ∧
      map (algebraMap ℤ_[p] ℚ_[p]) g = rescale (p : ℚ_[p]) (exp ℚ_[p]) := by
  classical
  let z (n : ℕ) (hn : n ≠ 0) : ℤ_[p] :=
    Classical.choose (coeff_rescale_exp_eq_prime_mul_padicInt p hn)
  let g : PowerSeries ℤ_[p] := mk fun n => if hn : n = 0 then 1 else (p : ℤ_[p]) * z n hn
  refine ⟨g, ?_, ?_, ?_⟩
  · simp [g]
  · intro n hn
    exact ⟨z n hn, by simp [g, hn]⟩
  · ext n
    by_cases hn : n = 0
    · subst n
      simp [g, coeff_rescale]
    · simp only [coeff_map, g, coeff_mk, dite_eq_right hn, map_mul, map_natCast]
      exact (Classical.choose_spec (coeff_rescale_exp_eq_prime_mul_padicInt p hn)).symm

private theorem coeff_artinHasseExp_exists_padicInt (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∃ z : ℤ_[p], ((coeff n (artinHasseExp p) : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
  obtain ⟨g, hg₀, hg, hgmap⟩ := exists_padicInt_rescale_exp p
  let φ : ℚ →+* ℚ_[p] := algebraMap ℚ ℚ_[p]
  have hFE : (map φ (artinHasseExp p)) ^ p =
      (map φ (artinHasseExp p)).expand p (Fact.out : p.Prime).ne_zero *
        map (algebraMap ℤ_[p] ℚ_[p]) g := by
    rw [hgmap]
    have h := congrArg (map φ)
      (artinHasseExp_functional_equation p (Fact.out : p.Prime).two_le)
    simpa only [map_pow, map_mul, map_expand, ← rescale_map, map_exp, map_natCast] using h
  have hφ (q : ℚ) : φ q = (q : ℚ_[p]) := by
    simpa only [Rat.cast_id] using map_ratCast φ q
  simpa only [coeff_map, hφ] using
    coeff_exists_padicInt_of_pow_eq_expand_mul p (map φ (artinHasseExp p)) g
      (by rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
        constantCoeff_artinHasseExp, map_one]) hg₀ hg hFE n

/-- Artin–Hasse coefficient integrality: every coefficient is a p-integral
rational number. The valuation is multiplicative, so integrality means `≤ 1`.
This is the integrality assertion of Fesenko–Vostokov I.(9.1), proved by the
standard Dieudonné–Dwork method using Mathlib's p-adic divided powers. -/
theorem artinHasseExp_coeff_padicValuation_le_one (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Rat.padicValuation p (coeff n (artinHasseExp p)) ≤ 1 := by
  obtain ⟨z, hz⟩ := coeff_artinHasseExp_exists_padicInt p n
  apply (Padic.norm_rat_le_one_iff_padicValuation_le_one p).mp
  rw [hz]
  exact (PadicInt.mem_subring_iff p).mp z.property

end PowerSeries
