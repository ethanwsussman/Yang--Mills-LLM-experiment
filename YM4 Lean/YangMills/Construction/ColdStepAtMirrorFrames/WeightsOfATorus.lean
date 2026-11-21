import YangMills.Construction.ColdStepAtMirrorFrames.DistancesOfBlocks
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
def ExpWeightSumsBounded : Prop :=
  ∀ (L : ℕ) (s : ℝ), Odd L → 0 < s → ∃ S : ℝ, ∀ (F : BlockFrame) (n : ℕ), F.blockSide = L → 2 ≤ n →
    (∀ i, F.extent i = n) →
    ∀ z : F.Cell, ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(s * blockDist F (bondBlock F b) z)) ≤ S ∧
      ∑ z' ∈ finiteCells F, Real.exp (-(s * blockDist F z' z)) ≤ S
end YangMills.Construction.ColdStepAtMirrorFrames
end
