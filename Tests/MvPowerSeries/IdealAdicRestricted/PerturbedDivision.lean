/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.PerturbedDivision
import Mathlib.Data.ZMod.Defs

set_option warningAsError true

namespace Tests.RestrictedPerturbedDivision

open MvPowerSeries

variable {σ ι R : Type*} [CommRing R] [Fintype ι]
variable (I : Ideal R) [IsAdicComplete I R]
variable (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
variable (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
variable (g : ι → adicallyRestrictedSubring (σ := σ) I)
variable (hg : ∀ i, adicReduction I 1 (polynomialToRestricted I (b i)) =
  adicReduction I 1 (g i))

private theorem client_decomposition
    (f : adicallyRestrictedSubring (σ := σ) I) :
    f = (∑ i, m.restrictedPerturbedDivisionQuotient I b hb g hg f i * g i) +
      m.restrictedPerturbedDivisionRemainder I b hb g hg f :=
  m.restrictedPerturbedDivision_decomposition I b hb g hg f

private theorem client_cone (f : adicallyRestrictedSubring (σ := σ) I)
    (α : σ →₀ ℕ) (i : ι) (hi : m.degree (b i) ≤ α) :
    coeff α ((m.restrictedPerturbedDivisionRemainder I b hb g hg f :
      adicallyRestrictedSubring (σ := σ) I) : MvPowerSeries σ R) = 0 :=
  m.coeff_restrictedPerturbedDivisionRemainder_eq_zero I b hb g hg f α i hi

private theorem client_kernels (n : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I)
    (hf : adicReduction I n f = 0) (i : ι) :
    adicReduction I n (m.restrictedPerturbedDivisionQuotient I b hb g hg f i) = 0 ∧
      adicReduction I n (m.restrictedPerturbedDivisionRemainder I b hb g hg f) = 0 :=
  ⟨m.restrictedPerturbedDivisionQuotient_preserves_ker I b hb g hg n f hf i,
    m.restrictedPerturbedDivisionRemainder_preserves_ker I b hb g hg n f hf⟩

private theorem client_level_zero (f : adicallyRestrictedSubring (σ := σ) I)
    (i : ι) :
    adicReduction I 0 (m.restrictedPerturbedDivisionQuotient I b hb g hg f i) = 0 := by
  have hzero : Subsingleton (R ⧸ I ^ 0) :=
    Ideal.Quotient.subsingleton_iff.mpr (by simp)
  apply MvPolynomial.ext
  intro index
  exact @Subsingleton.elim _ hzero _ _

private theorem client_empty_divisors (m : MonomialOrder σ)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    f = m.restrictedPerturbedDivisionRemainder I
      (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0)
      (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0) f := by
  simpa using m.restrictedPerturbedDivision_decomposition I
    (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0)
    (fun j : Fin 0 => j.elim0) (fun j : Fin 0 => j.elim0) f

private theorem client_unperturbed_error (f : adicallyRestrictedSubring (σ := σ) I) :
    m.restrictedDivisionError I b hb (fun i => polynomialToRestricted I (b i)) f = 0 := by
  simp [MonomialOrder.restrictedDivisionError]

private theorem client_unperturbed (f : adicallyRestrictedSubring (σ := σ) I) :
    f = (∑ i, m.restrictedPerturbedDivisionQuotient I b hb
        (fun i => polynomialToRestricted I (b i)) (by intro i; rfl) f i *
        polynomialToRestricted I (b i)) +
      m.restrictedPerturbedDivisionRemainder I b hb
        (fun i => polynomialToRestricted I (b i)) (by intro i; rfl) f :=
  m.restrictedPerturbedDivision_decomposition I b hb _ (by intro i; rfl) f

private theorem client_empty_variables (m : MonomialOrder Empty)
    (b : Fin 1 → MvPolynomial Empty R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (g : Fin 1 → adicallyRestrictedSubring (σ := Empty) I)
    (hg : ∀ i, adicReduction I 1 (polynomialToRestricted I (b i)) =
      adicReduction I 1 (g i))
    (f : adicallyRestrictedSubring (σ := Empty) I) :
    f = (∑ i, m.restrictedPerturbedDivisionQuotient I b hb g hg f i * g i) +
      m.restrictedPerturbedDivisionRemainder I b hb g hg f :=
  client_decomposition I m b hb g hg f

private theorem client_zero_ideal [IsAdicComplete (⊥ : Ideal R) R]
    (m : MonomialOrder σ) (b : Fin 1 → MvPolynomial σ R)
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (g : Fin 1 → adicallyRestrictedSubring (σ := σ) (⊥ : Ideal R))
    (hg : ∀ i, adicReduction (⊥ : Ideal R) 1
      (polynomialToRestricted (⊥ : Ideal R) (b i)) =
        adicReduction (⊥ : Ideal R) 1 (g i))
    (f : adicallyRestrictedSubring (σ := σ) (⊥ : Ideal R)) :
    f = (∑ i, m.restrictedPerturbedDivisionQuotient (⊥ : Ideal R)
      b hb g hg f i * g i) +
        m.restrictedPerturbedDivisionRemainder (⊥ : Ideal R) b hb g hg f :=
  client_decomposition (⊥ : Ideal R) m b hb g hg f

private theorem client_zero_ring (I : Ideal (ZMod 1)) [IsAdicComplete I (ZMod 1)]
    (m : MonomialOrder Empty) (b : Fin 1 → MvPolynomial Empty (ZMod 1))
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (g : Fin 1 → adicallyRestrictedSubring (σ := Empty) I)
    (hg : ∀ i, adicReduction I 1 (polynomialToRestricted I (b i)) =
      adicReduction I 1 (g i))
    (f : adicallyRestrictedSubring (σ := Empty) I) :
    f = (∑ i, m.restrictedPerturbedDivisionQuotient I b hb g hg f i * g i) +
      m.restrictedPerturbedDivisionRemainder I b hb g hg f :=
  client_decomposition I m b hb g hg f

end Tests.RestrictedPerturbedDivision
