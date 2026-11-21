import YangMills.Construction.SeparatedSequences.ClassesFramesNormsAndKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
namespace SeparatedClasses
def MeetingBlocksCount : Prop :=
  ∀ (C : ClassData), C.L ≤ C.blockSize → ∀ Ω ∈ C.separatedClass,
    ∀ y : C.Apex Ω, {z : C.Apex Ω | (z.block ∩ y.block).Nonempty}.encard ≤ ((C.L + 2) ^ 4 : ℕ)
end SeparatedClasses
end YangMills.Construction
end
