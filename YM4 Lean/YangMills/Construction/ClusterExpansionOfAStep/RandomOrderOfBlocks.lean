import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockOrder
open Classical in
def precedingBlocks {I : Type} [Fintype I] [LinearOrder I] (u : I → ℝ) (Y : I) : Finset I :=
  Finset.univ.filter fun i => u i < u Y ∨ (u i = u Y ∧ i < Y)
def SumIncrementsAlongOrder : Prop :=
  ∀ (I : Type) [Fintype I] [LinearOrder I] (F : Finset I → ℝ) (u : I → ℝ),
    ∑ Y, (F (insert Y (precedingBlocks u Y)) - F (precedingBlocks u Y)) = F Finset.univ - F ∅
end YangMills.Construction.BlockOrder
end
