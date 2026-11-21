import YangMills.Construction.Torus.MatrixOfThePairScaledSquare
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
def BlockIndicatorOnBlockUnionStatement : Prop :=
  ∀ (D : TorusData) (B : SeparatedChain D) (W : Set D.Space), B.IsBlockUnion W →
    ∀ y ∈ B.sitesIn W,
      B.block y ⊆ D.bareSites W ∧ B.block y ⊆ D.bareSites (B.stage 0) ∧
      ∃ h : B.blockIndicator y ∈ B.bareSpaceOn W,
        B.blockIndicatorIn W y = ⟨B.blockIndicator y, h⟩
end YangMills.Construction.Weighted
end
