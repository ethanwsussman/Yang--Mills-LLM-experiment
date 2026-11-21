import YangMills.Construction.ClusterExpansionOfAStep.LumpsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
def BondsPerBlockBound : Prop :=
  ∀ (L n : ℕ) [NeZero L] [NeZero n] (Y : TorusFields.TorusSite n),
    ((Finset.univ.filter fun b : TorusFields.TorusBond (n * L) => parentBlock L b.1 = Y).card : ℝ) ≤
      4 * (2 * L) ^ 4
end YangMills.Construction.TorusLumps
end
