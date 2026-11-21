import YangMills.Construction.ClusterExpansionOfAStep.FamiliesAtConstantCurvature
import YangMills.Construction.ColdStepAtMirrorFrames.ChainOfConstantCurvature
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.TorusLumps
namespace YangMills.Construction.ColdStepAtMirrorFrames
def planeUnitForm (μ ν : Fin 4) : Fin 4 → Fin 4 → ℝ :=
  fun i j => if i = μ ∧ j = ν then 1 else if i = ν ∧ j = μ then -1 else 0
def ConstantCurvatureTopOnTorus : Prop :=
  ∀ (F : BlockFrame) (X : imaginaryQuaternions) (μ ν : Fin 4) (n l : ℕ), Odd F.blockSide → (∀ i, F.extent i = n) →
    0 < n → ‖X‖ = 1 → μ < ν →
    2 * Real.pi * l / (n : ℝ) ^ 2 ≤ 1 →
    IsAbelianWithCurvature X (planeUnitForm μ ν) (2 * Real.pi * l / (n : ℝ) ^ 2)
      (restrictToTorus n (constantCurvatureChain F X μ ν l F.top))
end YangMills.Construction.ColdStepAtMirrorFrames
end
