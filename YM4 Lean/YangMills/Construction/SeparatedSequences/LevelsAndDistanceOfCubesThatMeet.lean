import YangMills.Construction.SeparatedSequences.ClassesFramesNormsAndKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
namespace SeparatedClasses
def MeetingBlocksLevelAndDistance : Prop :=
  ∀ (C : ClassData), C.L ≤ C.blockSize → ∀ Ω ∈ C.separatedClass,
    ∀ y y' : C.Apex Ω, (y.block ∩ y'.block).Nonempty →
      |(y.level : ℝ) - (y'.level : ℝ)| ≤ 1 ∧ C.chainDist Ω y.point y'.point ≤ 4
end SeparatedClasses
end YangMills.Construction
end
