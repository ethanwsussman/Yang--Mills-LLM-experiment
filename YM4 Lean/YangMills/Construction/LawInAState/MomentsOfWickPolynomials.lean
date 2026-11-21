import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace WickMoments
variable {ι : Type}
def IsCenteredGaussian [Fintype ι] (C : ι → ι → ℝ) (μ : Measure (ι → ℝ)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ t : ι → ℝ,
    ∫ ξ, Complex.exp (Complex.I * ((∑ i, t i * ξ i : ℝ) : ℂ)) ∂μ =
      Complex.exp ((-(1 / 2) * ∑ i, ∑ j, t i * C i j * t j : ℝ) : ℂ)
def wickPolynomial [Fintype ι] {q : ℕ} (C : ι → ι → ℝ) (A : (Fin q → ι) → ℝ) (ξ : ι → ℝ) : ℝ :=
  ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin q))).filter (fun σ => σ * σ = 1),
    (-1 : ℝ) ^ (Finset.univ.filter fun a : Fin q => a < σ a).card *
      ∑ i : Fin q → ι, A i * (∏ a ∈ Finset.univ.filter (fun a : Fin q => a < σ a), C (i a) (i (σ a))) *
        ∏ a ∈ Finset.univ.filter (fun a : Fin q => σ a = a), ξ (i a)
def WickMomentBound : Prop :=
  ∀ q r : ℕ, ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (C : ι → ι → ℝ) (lam : ℝ)
    (μ : Measure (ι → ℝ)), 0 ≤ lam → (∀ i j, C i j = C j i) →
    (∀ t : ι → ℝ, 0 ≤ ∑ i, ∑ j, t i * C i j * t j) →
    (∀ t : ι → ℝ, ∑ i, ∑ j, t i * C i j * t j ≤ lam * ∑ i, t i ^ 2) →
    IsCenteredGaussian C μ → ∀ A : (Fin q → ι) → ℝ,
      ∫ ξ, wickPolynomial C A ξ ^ (2 * r) ∂μ ≤ Cq * (lam ^ q * ∑ i, A i ^ 2) ^ r
end WickMoments
end YangMills.Construction
end
