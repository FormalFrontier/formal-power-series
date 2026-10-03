/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FirstVariableDivision

/-!
# First-variable restricted division examples

Scalar-top division is exercised on explicit linear and constant divisors,
including degree zero and no remaining variables.
-/

public section

set_option warningAsError true

open MvPowerSeries

example (n d : ℕ) :
    (MonomialOrder.lex : MonomialOrder (Fin (n + 1))).degree
        ((MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) ℤ) ^ d) =
      (0 : Fin n →₀ ℕ).cons d := by
  apply MonomialOrder.lex_degree_of_finSuccEquiv_scalar_top n d _ (1 : ℤ)
  · simp only [map_pow, MvPolynomial.finSuccEquiv_X_zero, Polynomial.natDegree_X_pow]
  · simp only [map_pow, MvPolynomial.finSuccEquiv_X_zero,
      Polynomial.coeff_X_pow_self, MvPolynomial.C_1]
  · exact one_ne_zero

variable {V : Type*} [CommRing V]

private noncomputable def linearDivisor (I : Ideal V) (n : ℕ) :
    adicallyRestrictedSubring (σ := Fin (n + 1)) I :=
  polynomialToRestricted I ((MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) V) + 1)

private theorem linearDivisor_primitive (I : Ideal V) (n : ℕ) :
    Ideal.span (Set.range (fun index : Fin (n + 1) →₀ ℕ =>
      coeff index (linearDivisor I n : MvPowerSeries (Fin (n + 1)) V))) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hconstant : coeff 0 (linearDivisor I n : MvPowerSeries (Fin (n + 1)) V) = 1 := by
    simp [linearDivisor, polynomialToRestricted_coe]
  rw [← hconstant]
  exact Ideal.subset_span (Set.mem_range_self (0 : Fin (n + 1) →₀ ℕ))

/-- The constant one divisor has primitive coefficient content in every number of variables. -/
theorem unitDivisor_primitive (n : ℕ) :
    Ideal.span (Set.range (fun index : Fin (n + 1) →₀ ℕ =>
      coeff index (1 : MvPowerSeries (Fin (n + 1)) V))) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hconstant : coeff 0 (1 : MvPowerSeries (Fin (n + 1)) V) = 1 := by simp
  rw [← hconstant]
  exact Ideal.subset_span (Set.mem_range_self (0 : Fin (n + 1) →₀ ℕ))

variable [IsDomain V] [ValuationRing V]

private theorem linearDivisor_residue (n : ℕ) (a : V)
    (ham : a ∈ IsLocalRing.maximalIdeal V) :
    MvPolynomial.finSuccEquiv _ n
        (restrictedResidue a ham (linearDivisor (Ideal.span {a}) n)) =
      (Polynomial.X + 1 : Polynomial (MvPolynomial (Fin n)
        (V ⧸ IsLocalRing.maximalIdeal V))) := by
  simp [linearDivisor, restrictedResidue_polynomial,
    MvPolynomial.finSuccEquiv_X_zero]

private theorem uniqueQuotient_degreeZero (n : ℕ) (a : V)
    (ham : a ∈ IsLocalRing.maximalIdeal V)
    [IsAdicComplete (Ideal.span {a} : Ideal V) V]
    (ha : a ≠ 0)
    (hrad : (Ideal.span {a} : Ideal V).radical = IsLocalRing.maximalIdeal V)
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
    (hprim : Ideal.span (Set.range (fun index : Fin (n + 1) →₀ ℕ =>
      coeff index (f : MvPowerSeries (Fin (n + 1)) V))) = ⊤)
    (c : V ⧸ IsLocalRing.maximalIdeal V)
    (hdegree : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).natDegree = 0)
    (htop : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).coeff 0 =
      MvPolynomial.C c) (hc : c ≠ 0)
    (h : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a})) :
    ∃! q : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}),
      h = q * f := by
  obtain ⟨⟨q, P⟩, ⟨hdecomp, hPdegree⟩, hunique⟩ :=
    existsUnique_firstVariable_division_of_scalar_top n a ham ha hrad f hprim 0 c
      hdegree htop hc h
  have hPzero : P = 0 := Polynomial.degree_eq_bot.mp
    ((Nat.WithBot.lt_zero_iff).mp hPdegree)
  refine ⟨q, ?_, ?_⟩
  · simpa [hPzero] using hdecomp
  · intro q' hq'
    have hpair : (q', (0 : Polynomial
        (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a})))) = (q, P) :=
      hunique (q', 0) (by
        constructor
        · simpa using hq'
        · simp)
    exact congrArg Prod.fst hpair

section ConcreteDivisors

variable (n : ℕ) (a : V) (ham : a ∈ IsLocalRing.maximalIdeal V)
    [IsAdicComplete (Ideal.span {a} : Ideal V) V]
    (ha : a ≠ 0)
    (hrad : (Ideal.span {a} : Ideal V).radical = IsLocalRing.maximalIdeal V)

example :
    ∃! qr : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}) ×
        Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a})),
      polynomialToRestricted (Ideal.span {a})
          (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) V) =
          qr.1 * linearDivisor (Ideal.span {a}) n +
            polynomialRestrictedFinFirst (Ideal.span {a}) n qr.2 ∧
        qr.2.degree < (1 : WithBot ℕ) ∧
        qr = (1, -1) ∧ qr.2 ≠ 0 := by
  let f := linearDivisor (Ideal.span {a}) n
  let h := polynomialToRestricted (Ideal.span {a})
    (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) V)
  have hres := linearDivisor_residue n a ham
  have hdegree : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).natDegree =
      1 := by
    rw [hres, ← Polynomial.C_1, Polynomial.natDegree_X_add_C]
  have htop : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).coeff 1 =
      MvPolynomial.C (1 : V ⧸ IsLocalRing.maximalIdeal V) := by
    rw [hres]
    simp [Polynomial.coeff_one]
  obtain ⟨pair, hpair, hunique⟩ :=
    existsUnique_firstVariable_division_of_scalar_top n a ham ha hrad f
      (linearDivisor_primitive (Ideal.span {a}) n) 1 1 hdegree htop one_ne_zero h
  have hcandidate : h = (1 : adicallyRestrictedSubring (σ := Fin (n + 1))
        (Ideal.span {a})) * f +
        polynomialRestrictedFinFirst (Ideal.span {a}) n
          (-1 : Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a}))) ∧
      (-1 : Polynomial (adicallyRestrictedSubring (σ := Fin n)
        (Ideal.span {a}))).degree < (1 : WithBot ℕ) := by
    constructor
    · simp [h, f, linearDivisor, map_add]
    · simp [Polynomial.degree_neg, Polynomial.degree_one]
  refine ⟨(1, -1), ⟨hcandidate.1, hcandidate.2, rfl, ?_⟩, ?_⟩
  · exact neg_ne_zero.mpr one_ne_zero
  · intro candidate hcand
    exact (hunique candidate ⟨hcand.1, hcand.2.1⟩).trans
      (hunique (1, -1) hcandidate).symm

example (h : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a})) :
    ∃! q : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}),
      h = q * (1 : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a})) := by
  apply uniqueQuotient_degreeZero n a ham ha hrad 1
    (by simpa using unitDivisor_primitive (V := V) n) 1
  · simp
  · simp
  · exact one_ne_zero

example (h : adicallyRestrictedSubring (σ := Fin (0 + 1)) (Ideal.span {a})) :
    ∃! q : adicallyRestrictedSubring (σ := Fin (0 + 1)) (Ideal.span {a}),
      h = q * (1 : adicallyRestrictedSubring (σ := Fin (0 + 1)) (Ideal.span {a})) := by
  apply uniqueQuotient_degreeZero 0 a ham ha hrad 1
    (by simpa using unitDivisor_primitive (V := V) 0) 1
  · simp
  · simp
  · exact one_ne_zero

end ConcreteDivisors

example : ¬ ∃ c : ℤ, (MvPolynomial.finSuccEquiv ℤ 1
    (MvPolynomial.X (Fin.succ (0 : Fin 1)) : MvPolynomial (Fin 2) ℤ)).coeff 0 =
      MvPolynomial.C c := by
  rintro ⟨c, hc⟩
  have hX : (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℤ) =
      MvPolynomial.C c := by
    simpa only [MvPolynomial.finSuccEquiv_X_succ, Polynomial.coeff_C_zero] using hc
  have hcoeff := congrArg
    (fun p : MvPolynomial (Fin 1) ℤ => p.coeff (Finsupp.single (0 : Fin 1) 1)) hX
  have hnonzero : (Finsupp.single (0 : Fin 1) (1 : ℕ)) ≠ 0 := by simp
  rw [MvPolynomial.coeff_C_of_ne_zero hnonzero c] at hcoeff
  exact one_ne_zero (by simpa only [MvPolynomial.coeff_X_same] using hcoeff)
