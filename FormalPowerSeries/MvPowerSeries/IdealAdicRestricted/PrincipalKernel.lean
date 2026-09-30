module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

public section

/-!
# Principal kernels of ideal-adic restricted reduction

For a regular element, coefficientwise division by its powers preserves ideal-adic
restrictedness. Hence the kernel of polynomial reduction is generated inside the
restricted series subring by the corresponding constant polynomial.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

/-- The image of a power of a coefficient as a constant restricted series. -/
noncomputable def principalAdicConstant (a : R) (k : ℕ) :
    adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R)) :=
  polynomialToRestricted _ (MvPolynomial.C (a ^ k))

@[simp]
theorem principalAdicConstant_coe (a : R) (k : ℕ) :
    ((principalAdicConstant (σ := σ) a k :
      adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R))) :
      MvPowerSeries σ R) = C (a ^ k) := by
  rw [principalAdicConstant, polynomialToRestricted_coe, MvPolynomial.coe_C]

/-- Coefficientwise divisibility by a regular power has a quotient which is still
ideal-adically restricted. Its finite exceptional sets are sets of monomial indices. -/
theorem exists_restricted_principal_quotient (a : R) (ha : IsRegular a)
    (k : ℕ) (f : adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R)))
    (hf : ∀ m : σ →₀ ℕ,
      coeff m (f : MvPowerSeries σ R) ∈ (Ideal.span ({a} : Set R)) ^ k) :
    ∃ g : adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R)),
      f = principalAdicConstant (σ := σ) a k * g := by
  classical
  have hex (m : σ →₀ ℕ) : ∃ b : R, a ^ k * b = coeff m (f : MvPowerSeries σ R) := by
    obtain ⟨b, hb⟩ := (Ideal.mem_span_singleton').1
      (show coeff m (f : MvPowerSeries σ R) ∈
        Ideal.span ({a ^ k} : Set R) by
        simpa only [Ideal.span_singleton_pow] using hf m)
    exact ⟨b, by simpa only [mul_comm] using hb⟩
  choose quotient hquotient using hex
  let g : MvPowerSeries σ R := fun m => quotient m
  have hgcoeff (m : σ →₀ ℕ) : a ^ k * coeff m g = coeff m (f : MvPowerSeries σ R) := by
    change a ^ k * quotient m = (f : MvPowerSeries σ R) m
    exact hquotient m
  have hg : IsAdicallyRestricted (Ideal.span ({a} : Set R)) g := by
    intro l
    apply Set.Finite.subset
      (((mem_adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R))
        (f : MvPowerSeries σ R)).1 f.property) (k + l))
    intro m hm hfm
    have hmem : coeff m (f : MvPowerSeries σ R) ∈
        Ideal.span ({a ^ (k + l)} : Set R) := by
      simpa only [Ideal.span_singleton_pow] using hfm
    obtain ⟨b, hb⟩ := (Ideal.mem_span_singleton').1 hmem
    have hc : a ^ k * coeff m g = a ^ k * (a ^ l * b) := by
      rw [hgcoeff m, ← hb, pow_add]
      ring
    have hq : coeff m g = a ^ l * b := (ha.pow k).left hc
    apply hm
    rw [hq, Ideal.span_singleton_pow]
    exact (Ideal.mem_span_singleton').2 ⟨b, mul_comm b (a ^ l)⟩
  refine ⟨⟨g, (mem_adicallyRestrictedSubring _ _).2 hg⟩, ?_⟩
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro m
  simpa only [Subring.coe_mul, principalAdicConstant_coe, coeff_C_mul] using
    (hgcoeff m).symm

/-- The actual polynomial reduction kernel, computed as an ideal *inside* the
restricted series subring, for every level (including level zero). -/
theorem ker_adicReduction_principal (a : R) (ha : IsRegular a) (k : ℕ) :
    RingHom.ker (adicReduction (σ := σ) (Ideal.span ({a} : Set R)) k) =
      Ideal.span ({principalAdicConstant (σ := σ) a k} :
        Set (adicallyRestrictedSubring (σ := σ) (Ideal.span ({a} : Set R)))) := by
  apply le_antisymm
  · intro f hf
    have hfcoeff (m : σ →₀ ℕ) :
        coeff m (f : MvPowerSeries σ R) ∈ (Ideal.span ({a} : Set R)) ^ k := by
      have hzero : (adicReduction (Ideal.span ({a} : Set R)) k f).coeff m = 0 := by
        rw [(RingHom.mem_ker).1 hf]
        simp
      rw [coeff_adicReduction] at hzero
      exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
    obtain ⟨g, rfl⟩ := exists_restricted_principal_quotient a ha k f hfcoeff
    exact (Ideal.mem_span_singleton').2 ⟨g, mul_comm g _⟩
  · intro f hf
    obtain ⟨g, hg⟩ := (Ideal.mem_span_singleton').1 hf
    apply (RingHom.mem_ker).2
    rw [← hg, map_mul]
    have hc : adicReduction (Ideal.span ({a} : Set R)) k
        (principalAdicConstant (σ := σ) a k) = 0 := by
      have hmem : a ^ k ∈ (Ideal.span ({a} : Set R)) ^ k :=
        Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton a)) k
      have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [principalAdicConstant, adicReduction_polynomial,
        MvPolynomial.map_C, hzero, map_zero]
    simp [hc]

end MvPowerSeries
