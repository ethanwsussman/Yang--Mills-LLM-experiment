import YangMills.Construction.ColdStepAtMirrorFrames.TopOfTheCurvedChainOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.TorusLumps
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ConstantCurvatureLevelOnTorus : Prop :=
  ∀ (F : BlockFrame) (X : imaginaryQuaternions) (μ ν : Fin 4) (n l j M : ℕ), Odd F.blockSide →
    (∀ i, F.extent i = n) → 0 < n → ‖X‖ = 1 → μ < ν →
    2 * Real.pi * l / (n : ℝ) ^ 2 ≤ 1 → j ≤ F.top → (∀ i, F.period j i = M) → 0 < M →
    IsAbelianWithCurvature X (planeUnitForm μ ν) (2 * Real.pi * l / (M : ℝ) ^ 2)
      (restrictToTorus M (constantCurvatureChain F X μ ν l j))
end YangMills.Construction.ColdStepAtMirrorFrames
end
