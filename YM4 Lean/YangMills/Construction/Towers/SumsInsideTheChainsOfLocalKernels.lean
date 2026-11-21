import YangMills.Construction.Towers.ChainsOfLocalKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
open OperatorCalculus UnitLatticeL2 AbelianFieldDensity OneLoopNotation
def loopSums_linear_and_tsum : Prop :=
  ∀ (c : ℝ) (m : ℕ), 0 < c → ∃ M : ℝ, 0 ≤ M ∧
    ∀ (J : Type) (pos : J → InfiniteLattice.AmbientSpace), IsIntegerPlacement pos m →
    ∀ s : ℝ, 0 ≤ s →
      (∀ (R₀ R₁ X Y : J → J → ℂ) (A A' : ℝ) (a : ℂ), 0 ≤ A → 0 ≤ A' →
        IsExpDecayKernel pos c s R₀ → IsExpDecayKernel pos c s R₁ →
        IsCubicGrowthLocalKernel pos A X → IsCubicGrowthLocalKernel pos A' Y →
        loopSumOne pos R₀ (fun i' i => X i' i + a * Y i' i) R₁ =
          loopSumOne pos R₀ X R₁ + a * loopSumOne pos R₀ Y R₁) ∧
      (∀ (R₀ R₁ R₂ X X' Y : J → J → ℂ) (A A' A'' : ℝ) (a : ℂ), 0 ≤ A → 0 ≤ A' → 0 ≤ A'' →
        IsExpDecayKernel pos c s R₀ → IsExpDecayKernel pos c s R₁ →
        IsExpDecayKernel pos c s R₂ →
        IsCubicGrowthLocalKernel pos A X → IsCubicGrowthLocalKernel pos A' X' →
        IsCubicGrowthLocalKernel pos A'' Y →
        loopSumTwo pos R₀ (fun i' i => X i' i + a * X' i' i) R₁ Y R₂ =
            loopSumTwo pos R₀ X R₁ Y R₂ + a * loopSumTwo pos R₀ X' R₁ Y R₂ ∧
          loopSumTwo pos R₀ Y R₁ (fun i' i => X i' i + a * X' i' i) R₂ =
            loopSumTwo pos R₀ Y R₁ X R₂ + a * loopSumTwo pos R₀ Y R₁ X' R₂) ∧
      (∀ (N : Type) (R₀ R₁ : J → J → ℂ) (X : N → J → J → ℂ) (A : ℝ), 0 ≤ A →
        IsExpDecayKernel pos c s R₀ → IsExpDecayKernel pos c s R₁ →
        IsCubicGrowthLocalFamily pos A X →
        Summable (fun j => ‖loopSumOne pos R₀ (X j) R₁‖) ∧
          ∑' j, ‖loopSumOne pos R₀ (X j) R₁‖ ≤ M * A * s ^ 2 ∧
          loopSumOne pos R₀ (fun i' i => ∑' j, X j i' i) R₁ =
            ∑' j, loopSumOne pos R₀ (X j) R₁) ∧
      (∀ (N N' : Type) (R₀ R₁ R₂ : J → J → ℂ) (X : N → J → J → ℂ) (Y : N' → J → J → ℂ)
        (A A' : ℝ), 0 ≤ A → 0 ≤ A' →
        IsExpDecayKernel pos c s R₀ → IsExpDecayKernel pos c s R₁ →
        IsExpDecayKernel pos c s R₂ →
        IsCubicGrowthLocalFamily pos A X → IsCubicGrowthLocalFamily pos A' Y →
        Summable (fun p : N × N' => ‖loopSumTwo pos R₀ (X p.1) R₁ (Y p.2) R₂‖) ∧
          ∑' p : N × N', ‖loopSumTwo pos R₀ (X p.1) R₁ (Y p.2) R₂‖ ≤ M * A * A' * s ^ 3 ∧
          loopSumTwo pos R₀ (fun i' i => ∑' j, X j i' i) R₁ (fun i' i => ∑' j, Y j i' i) R₂ =
            ∑' p : N × N', loopSumTwo pos R₀ (X p.1) R₁ (Y p.2) R₂)
end YangMills.Construction.Tower.LocalFamilies
end
