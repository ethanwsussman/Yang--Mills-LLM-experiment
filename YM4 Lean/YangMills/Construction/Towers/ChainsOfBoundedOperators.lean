import YangMills.Construction.Towers.ChainsOfLocalKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.AbelianFieldDensity YangMills.Construction.OneLoopNotation
def LoopSumsAsTraces : Prop :=
  ∀ (c : ℝ) (m : ℕ), 0 < c →
    ∀ (J : Type) (place : J → YangMills.Construction.InfiniteLattice.AmbientSpace),
    IsIntegerPlacement place m →
    MatrixEntryProperties J → ∀ s : ℝ, 0 ≤ s →
      (∀ (S₀ S₁ X : BddOp (IndexL2 J)) (A : ℝ), 0 ≤ A →
        IsExpDecayKernel place c s (matrixEntry S₀) → IsExpDecayKernel place c s (matrixEntry S₁) →
        IsCubicGrowthLocalKernel place A (matrixEntry X) →
        traceAt place (S₀.comp (X.comp S₁)) 0 =
          loopSumOne place (matrixEntry S₀) (matrixEntry X) (matrixEntry S₁)) ∧
      (∀ (S₀ S₁ S₂ X Y : BddOp (IndexL2 J)) (A A' : ℝ), 0 ≤ A → 0 ≤ A' →
        IsExpDecayKernel place c s (matrixEntry S₀) → IsExpDecayKernel place c s (matrixEntry S₁) →
        IsExpDecayKernel place c s (matrixEntry S₂) →
        IsCubicGrowthLocalKernel place A (matrixEntry X) →
        IsCubicGrowthLocalKernel place A' (matrixEntry Y) →
        traceAt place (S₀.comp (X.comp (S₁.comp (Y.comp S₂)))) 0 =
          loopSumTwo place (matrixEntry S₀) (matrixEntry X) (matrixEntry S₁) (matrixEntry Y)
            (matrixEntry S₂)) ∧
      (∀ (S₀ S₁ S₂ S₃ X Y W : BddOp (IndexL2 J)) (A A' A'' : ℝ),
        0 ≤ A → 0 ≤ A' → 0 ≤ A'' →
        IsExpDecayKernel place c s (matrixEntry S₀) → IsExpDecayKernel place c s (matrixEntry S₁) →
        IsExpDecayKernel place c s (matrixEntry S₂) → IsExpDecayKernel place c s (matrixEntry S₃) →
        IsCubicGrowthLocalKernel place A (matrixEntry X) →
        IsCubicGrowthLocalKernel place A' (matrixEntry Y) →
        IsCubicGrowthLocalKernel place A'' (matrixEntry W) →
        traceAt place (S₀.comp (X.comp (S₁.comp (Y.comp (S₂.comp (W.comp S₃)))))) 0 =
          loopSumThree place (matrixEntry S₀) (matrixEntry X) (matrixEntry S₁) (matrixEntry Y)
            (matrixEntry S₂) (matrixEntry W) (matrixEntry S₃))
end YangMills.Construction.Tower.LocalFamilies
end
