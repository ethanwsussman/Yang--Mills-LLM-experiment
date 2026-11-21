import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.ResponseInTheExpansion.ScoresOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepSettings StepCosts BlockOffsets
def BondScoresAgreeNearBlocks : Prop :=
  ∀ (R : StepSetup) (n n' : ℕ) [NeZero n] [NeZero n'] (s : ChartSetting R n) (s' : ChartSetting R n')
    (Y : TorusSite n) (Y' : TorusSite n') (m k : ℕ) (η : FreeCoords s.free) (η' : FreeCoords s'.free)
    (h : Fin 4 → ℤ) (i : Fin 4),
    R.params.Admissible → 11 * 2 ^ 12 * R.params.baseDepth < R.params.side → 16 ≤ n → 16 ≤ n' →
    s.free ⊆ chartBonds R.params.side n →
    SettingsAgreeNear s s' Y Y' m → 4 ≤ k → k ≤ m → CoordsAgreeNear s s' Y Y' k η η' → OffsetInBox 1 h →
    OffsetInBox 1 (h + Pi.single i 1) →
    bondScore R.params R.coupling (s.field η) s.coarse s.bases (Y + siteOfInt h, i) =
      bondScore R.params R.coupling (s'.field η') s'.coarse s'.bases (Y' + siteOfInt h, i)
end YangMills.Construction.WeightedResponses
end
