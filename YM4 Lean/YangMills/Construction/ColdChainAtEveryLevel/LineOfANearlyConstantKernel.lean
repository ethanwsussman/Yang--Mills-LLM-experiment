import YangMills.Construction.ColdChainAtEveryLevel.BoundedDifferences
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace NearlyConstantKernel
section
variable {ι : Type}
def perturbationApply (s : Finset ι) (u : ι → ℝ) (e : ι → ι → ι → ℍ[ℝ]) (f : ι → ℍ[ℝ]) (i : ι) : ℍ[ℝ] :=
  ∑ j ∈ s, ∑ k ∈ s, (u j : ℍ[ℝ]) * ((u k : ℍ[ℝ]) * (e i j k * f k))
def perturbationMean (s : Finset ι) (u : ι → ℝ) (e : ι → ι → ι → ℍ[ℝ]) (f : ι → ℍ[ℝ]) : ℍ[ℝ] :=
  ∑ i ∈ s, (u i : ℍ[ℝ]) * perturbationApply s u e f i
def eigenStep (s : Finset ι) (u : ι → ℝ) (e : ι → ι → ι → ℍ[ℝ]) (f : ι → ℍ[ℝ]) (i : ι) : ℍ[ℝ] :=
  1 + perturbationApply s u e f i - f i * perturbationMean s u e f
end
def EigenvectorNearOne : Prop :=
  ∀ (N : ℕ) (B : ℝ), 0 ≤ B → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (A ι : Type) [AddCommGroup A] (len : A → ℝ) (D : Set A) (s : Finset ι) (w : ι → A → ℝ)
      (e : ι → ι → ι → ℍ[ℝ]) (ε : ℝ),
      (∀ a, 0 ≤ len a) → s.card ≤ N → 0 ≤ ε → ε ≤ c →
      (∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, ‖e i j k‖ ≤ ε) →
      (∀ i ∈ s, YangMills.Construction.FiniteDifferences.FiniteDiffBound len 3 D B (w i)) →
      (∀ x ∈ D, ∀ i ∈ s, 0 ≤ w i x) → (∀ x ∈ D, ∑ i ∈ s, w i x = 1) →
      ∃ f : A → ι → ℍ[ℝ],
        (∀ i ∈ s, YangMills.Construction.FiniteDifferences.FiniteDiffBound len 3 D (C * ε)
          (fun x => f x i - 1)) ∧
        (∀ x ∈ D, ∑ i ∈ s, (w i x : ℍ[ℝ]) * f x i = 1) ∧
        (∀ x ∈ D, ∀ i ∈ s,
          1 + perturbationApply s (fun i => w i x) e (f x) i =
            f x i * (1 + perturbationMean s (fun i => w i x) e (f x))) ∧
        ∀ x ∈ D, ∀ g : ι → ℍ[ℝ], (∀ i ∈ s, ‖g i - 1‖ ≤ 1) →
          ∑ i ∈ s, (w i x : ℍ[ℝ]) * g i = 1 →
          ∀ l : ℍ[ℝ], (∀ i ∈ s, 1 + perturbationApply s (fun i => w i x) e g i = g i * l) →
            ∀ i ∈ s, g i = f x i
end NearlyConstantKernel
end YangMills.Construction
end
