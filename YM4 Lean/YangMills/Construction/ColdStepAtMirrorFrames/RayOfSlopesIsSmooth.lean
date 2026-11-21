import YangMills.Construction.ColdStepAtMirrorFrames.SlopeAlongRaysOfADifference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def RadialSlopeIntegralContDiffOn : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Finset ι) (r : ℝ) (D : BondField ι → ℝ),
    ContDiffOn ℝ 2 D (openPolyball ι r) → ContDiffOn ℝ 1 (radialSlopeIntegral B D) (openPolyball ι r)
end YangMills.Construction.ColdStepAtMirrorFrames
end
