import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def decaySumOnTorusStatement : Prop :=
  ∀ (L : ℕ) (s : ℝ), Odd L → 0 < s → ∃ S : ℝ, ∀ (F : BlockFrame) (n : ℕ), F.blockSide = L → 2 ≤ n →
    (∀ i, F.extent i = n) → ∀ z : F.Cell,
      ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(s * (cellSupDist (enclosingCell b.1.1) z : ℝ))) ≤ S ∧
      ∑ z' ∈ finiteCells F, Real.exp (-(s * (cellSupDist z' z : ℝ))) ≤ S
end ColdStepAtMirrorFrames
end YangMills.Construction
end
