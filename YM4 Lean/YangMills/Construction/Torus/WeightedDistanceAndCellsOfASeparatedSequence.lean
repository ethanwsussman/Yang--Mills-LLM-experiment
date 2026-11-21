import YangMills.Construction.Torus.PropertiesOfTheWeightedDistanceAndCells
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GeneralTorus
def ScaledDistAndCells : Prop :=
  ∀ W : GaugeSetting, W.data.L ≤ W.data.blockCount →
    W.chain.AugmentedShellsSeparated ∧
    W.ExpSumsOfScaledDist ∧
    W.chain.SupDistFunctionsLipschitzScaled ∧
    W.chain.MeetingCellsAreClose ∧
    W.CoarseSupportsAreCellUnions ∧
    W.CoarseEndpointsClose ∧
    W.chain.ScaledDistEqInfIntegral
end YangMills.Construction.GeneralTorus
end
