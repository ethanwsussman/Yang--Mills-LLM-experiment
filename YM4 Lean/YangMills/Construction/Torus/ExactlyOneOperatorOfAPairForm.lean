import YangMills.Construction.Torus.AdmissiblePairs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
def UniqueAdmissibleFormOpStatement : Prop :=
  ∀ (D : TorusData) (B : SeparatedChain D) (W : Set D.Space) (𝔟 : Set D.Bond),
    B.IsBlockUnion W → ∃! T : Module.End ℝ ↥(B.bareSpaceOn W), B.IsAdmissibleFormOp W 𝔟 T
end YangMills.Construction.Weighted
end
