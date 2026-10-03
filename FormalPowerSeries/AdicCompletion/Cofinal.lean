/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

@[expose] public section

/-!
# Cofinal ideal-adic filtrations on modules

If `I ≤ J` and a positive power of `J` is contained in `I`, their filtrations
give the same precompleteness and separation properties, even without finite
generation of either ideal. The comparison applies to arbitrary modules.
-/

set_option warningAsError true

private theorem cofinal_smul_le {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {I J : Ideal R} (hIJ : I ≤ J) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R M) ≤ J ^ n • ⊤ :=
  Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)

private theorem cofinal_smul_pow_le {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {I J : Ideal R} {N : ℕ} (hJI : J ^ N ≤ I) (n : ℕ) :
    (J ^ (N * n) • ⊤ : Submodule R M) ≤ I ^ n • ⊤ := by
  rw [pow_mul]
  exact Submodule.smul_mono_left (pow_le_pow_left' hJI n)

private theorem cofinal_le_mul (N : ℕ) (hN : 1 ≤ N) (n : ℕ) : n ≤ N * n := by
  calc
    n = 1 * n := (one_mul n).symm
    _ ≤ N * n := Nat.mul_le_mul_right n hN

/-- Hausdorff separation is invariant under cofinal ideal powers. -/
theorem isHausdorff_iff_of_cofinal {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {I J : Ideal R} (hIJ : I ≤ J) (N : ℕ) (_hN : 1 ≤ N)
    (hJI : J ^ N ≤ I) : IsHausdorff I M ↔ IsHausdorff J M := by
  constructor
  · intro h
    refine ⟨fun x hx => h.haus x (fun n => ?_)⟩
    exact SModEq.mono (cofinal_smul_pow_le (M := M) hJI n) (hx (N * n))
  · intro h
    refine ⟨fun x hx => h.haus x (fun n => ?_)⟩
    exact SModEq.mono (cofinal_smul_le (M := M) hIJ n) (hx n)

/-- A sequence Cauchy for either of two cofinal ideal filtrations has an
actual limit with the level-by-level congruences of the other filtration. -/
theorem isPrecomplete_iff_of_cofinal {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {I J : Ideal R} (hIJ : I ≤ J) (N : ℕ) (hN : 1 ≤ N)
    (hJI : J ^ N ≤ I) : IsPrecomplete I M ↔ IsPrecomplete J M := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_⟩
    let y : ℕ → M := fun n => x (N * n)
    have hy : ∀ {m n}, m ≤ n →
        y m ≡ y n [SMOD (I ^ m • ⊤ : Submodule R M)] := by
      intro m n hmn
      exact SModEq.mono (cofinal_smul_pow_le (M := M) hJI m)
        (hx (Nat.mul_le_mul_left N hmn))
    obtain ⟨L, hL⟩ := h.prec (f := y) hy
    refine ⟨L, fun n => ?_⟩
    exact (hx (cofinal_le_mul N hN n)).trans
      (SModEq.mono (cofinal_smul_le (M := M) hIJ n) (hL n))
  · intro h
    refine ⟨fun x hx => ?_⟩
    have hy : ∀ {m n}, m ≤ n →
        x m ≡ x n [SMOD (J ^ m • ⊤ : Submodule R M)] := by
      intro m n hmn
      exact SModEq.mono (cofinal_smul_le (M := M) hIJ m) (hx hmn)
    obtain ⟨L, hL⟩ := h.prec (f := x) hy
    refine ⟨L, fun n => ?_⟩
    exact (hx (cofinal_le_mul N hN n)).trans
      (SModEq.mono (cofinal_smul_pow_le (M := M) hJI n) (hL (N * n)))

/-- Both the Cauchy-limit and Hausdorff components of adic completeness
transport across cofinal ideal filtrations. -/
theorem isAdicComplete_iff_of_cofinal {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {I J : Ideal R} (hIJ : I ≤ J) (N : ℕ) (hN : 1 ≤ N)
    (hJI : J ^ N ≤ I) : IsAdicComplete I M ↔ IsAdicComplete J M := by
  constructor
  · intro h
    exact (isAdicComplete_iff (I := J) (M := M)).mpr
      ⟨(isHausdorff_iff_of_cofinal hIJ N hN hJI).mp h.toIsHausdorff,
       (isPrecomplete_iff_of_cofinal hIJ N hN hJI).mp h.toIsPrecomplete⟩
  · intro h
    exact (isAdicComplete_iff (I := I) (M := M)).mpr
      ⟨(isHausdorff_iff_of_cofinal hIJ N hN hJI).mpr h.toIsHausdorff,
       (isPrecomplete_iff_of_cofinal hIJ N hN hJI).mpr h.toIsPrecomplete⟩
