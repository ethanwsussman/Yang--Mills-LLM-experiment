import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockAverages
def symmetryInvarianceOfShareStatement : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (S S' : Finset F.Cell) (V V' : F.GaugeField F.top) (g : CubicSymmetry), 0 ≤ a →
    Odd F.blockSide → g.IsSymmetry F → (∀ z, z ∈ S ↔ g.actSite F.top z ∈ S') → g.TransportsField V V' →
    (∀ X, IsMinimalChain a S V X → ∀ Y, cellShare a S Y X = minimalCellShare a S Y V) →
    ∀ Y, minimalCellShare a S' (g.actSite F.top Y) V' = minimalCellShare a S Y V
end BlockAverages
end YangMills.Construction
end
