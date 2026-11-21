import YangMills.Construction.ClusterExpansionOfAStep.ActionAtAFieldOfOnePlane
import YangMills.Construction.ColdStepAtMirrorFrames.ChainOfConstantCurvature
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
def TopOfConstantCurvatureChainIsAbelian : Prop :=
  ∀ L : ℕ, Odd L → ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (F : BlockAverages.BlockFrame) (X : BlockAverages.imaginaryQuaternions) (μ ν : Fin 4) (n l : ℕ),
      F.blockSide = L → (∀ i, F.extent i = n) → 64 ≤ n → ‖X‖ = 1 → μ < ν →
      2 * Real.pi * l / (n : ℝ) ^ 2 ≤ γ₀ →
      IsAbelianWithCurvature X (PlaneFields.planeForm μ ν) (2 * Real.pi * l / (n : ℝ) ^ 2)
        (ColdStepAtMirrorFrames.restrictToTorus n
          (ColdStepAtMirrorFrames.constantCurvatureChain F X μ ν l F.top))
end YangMills.Construction.TorusLumps
end
