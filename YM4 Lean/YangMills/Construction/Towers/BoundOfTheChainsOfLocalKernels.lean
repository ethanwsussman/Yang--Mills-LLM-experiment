import YangMills.Construction.Towers.ChainsOfLocalKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.AbelianFieldDensity YangMills.Construction.OneLoopNotation
def LoopTermsBound : Prop :=
  ∀ (c : ℝ) (m : ℕ), 0 < c → ∃ M : ℝ, 0 ≤ M ∧
    ∀ (J : Type) (place : J → YangMills.Construction.InfiniteLattice.AmbientSpace),
    IsIntegerPlacement place m →
    ∀ s : ℝ, 0 ≤ s →
      (∀ (S₀ S₁ X : J → J → ℂ) (A : ℝ), 0 ≤ A →
        IsExpDecayKernel place c s S₀ → IsExpDecayKernel place c s S₁ →
        IsCubicGrowthLocalKernel place A X →
        Summable (fun q => ‖loopTermsOne place S₀ X S₁ q‖) ∧
          ∑' q, ‖loopTermsOne place S₀ X S₁ q‖ ≤ M * A * s ^ 2) ∧
      (∀ (S₀ S₁ S₂ X Y : J → J → ℂ) (A A' : ℝ), 0 ≤ A → 0 ≤ A' →
        IsExpDecayKernel place c s S₀ → IsExpDecayKernel place c s S₁ →
        IsExpDecayKernel place c s S₂ →
        IsCubicGrowthLocalKernel place A X → IsCubicGrowthLocalKernel place A' Y →
        Summable (fun q => ‖loopTermsTwo place S₀ X S₁ Y S₂ q‖) ∧
          ∑' q, ‖loopTermsTwo place S₀ X S₁ Y S₂ q‖ ≤ M * A * A' * s ^ 3) ∧
      (∀ (S₀ S₁ S₂ S₃ X Y W : J → J → ℂ) (A A' A'' : ℝ), 0 ≤ A → 0 ≤ A' → 0 ≤ A'' →
        IsExpDecayKernel place c s S₀ → IsExpDecayKernel place c s S₁ →
        IsExpDecayKernel place c s S₂ → IsExpDecayKernel place c s S₃ →
        IsCubicGrowthLocalKernel place A X → IsCubicGrowthLocalKernel place A' Y →
        IsCubicGrowthLocalKernel place A'' W →
        Summable (fun q => ‖loopTermsThree place S₀ X S₁ Y S₂ W S₃ q‖) ∧
          ∑' q, ‖loopTermsThree place S₀ X S₁ Y S₂ W S₃ q‖ ≤ M * A * A' * A'' * s ^ 4)
end YangMills.Construction.Tower.LocalFamilies
end
