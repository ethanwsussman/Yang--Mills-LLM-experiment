import YangMills.Construction.Continuum.DiagonalFlatSchwartz
import Mathlib
set_option autoImplicit false
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction.ConfigSpace
def IteratedPartialRules : Prop :=
  ∀ n : ℕ,
    (∀ (α : MultiIndex n) (f : Config n → ℂ), ContDiff ℝ ∞ f →
      ContDiff ℝ ∞ (iteratedPartial α f)) ∧
    (∀ (α : MultiIndex n) (f g : Config n → ℂ), ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      iteratedPartial α (f + g) = iteratedPartial α f + iteratedPartial α g) ∧
    (∀ (ι : Type) (s : Finset ι) (F : ι → Config n → ℂ) (α : MultiIndex n),
      (∀ i ∈ s, ContDiff ℝ ∞ (F i)) →
        iteratedPartial α (∑ i ∈ s, F i) = ∑ i ∈ s, iteratedPartial α (F i)) ∧
    (∀ (α : MultiIndex n) (c : ℂ) (f : Config n → ℂ), ContDiff ℝ ∞ f →
      iteratedPartial α (c • f) = c • iteratedPartial α f) ∧
    (∀ (α : MultiIndex n) (f g : Config n → ℂ) (x : Config n), f =ᶠ[𝓝 x] g →
      iteratedPartial α f x = iteratedPartial α g x) ∧
    ∀ (l : ℕ) (A B : ℝ) (u v : Config n → ℂ) (x : Config n), ContDiff ℝ ∞ u → ContDiff ℝ ∞ v →
      (∀ γ : MultiIndex n, γ.order ≤ l → ‖iteratedPartial γ u x‖ ≤ A) →
      (∀ γ : MultiIndex n, γ.order ≤ l → ‖iteratedPartial γ v x‖ ≤ B) →
      ∀ α : MultiIndex n, α.order ≤ l →
        ‖iteratedPartial α (fun y => u y * v y) x‖ ≤ 2 ^ l * A * B
end YangMills.Construction.ConfigSpace
end
