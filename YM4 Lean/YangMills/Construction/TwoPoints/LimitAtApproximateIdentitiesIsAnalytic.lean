import YangMills.Construction.TwoPoints.LocalKernelOfAForm
import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def MollifierLimitAnalytic : Prop :=
  ∀ (σ : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ), IsDisjointForm S →
    IsAdmissibleForm σ S →
    ∃ K : AmbientSpace → ℝ, AnalyticOnNhd ℝ (fun x => (K x : ℂ)) {0}ᶜ ∧
      (∀ ξ : AmbientSpace, ξ ≠ 0 → ∀ ρ : ℕ → AmbientSpace → ℂ, IsMollifierSeq ρ →
        Tendsto (fun n : ℕ => S (ρ n) (translateFun ξ (ρ n))) atTop (𝓝 (K ξ))) ∧
      ∀ ξ : AmbientSpace, ξ ≠ 0 → IsLocalKernelNear S ξ fun x => (K x : ℂ)
end YangMills.Construction.TwoPoints
end
