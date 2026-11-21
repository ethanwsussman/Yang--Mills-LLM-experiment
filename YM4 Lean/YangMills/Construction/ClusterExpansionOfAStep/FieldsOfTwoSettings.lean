import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps StepSettings StepCosts BlockOffsets
namespace StepSettings
def FieldsAgreeOfCoordsAgree : Prop :=
  ∀ (R : StepSetup) (n n' : ℕ) [NeZero n] [NeZero n'] (s : ChartSetting R n) (s' : ChartSetting R n')
    (Y : TorusSite n) (Y' : TorusSite n') (m k : ℕ) (η : FreeCoords s.free) (η' : FreeCoords s'.free)
    (o : Fin 4 → ℤ),
    R.params.Admissible → 2 ≤ n → 2 ≤ n' → s.free ⊆ chartBonds R.params.side n →
    s'.free ⊆ chartBonds R.params.side n' →
    SettingsAgreeNear s s' Y Y' m → 1 ≤ k → k ≤ m → CoordsAgreeNear s s' Y Y' k η η' →
    o ∈ centredCube R.params.side →
    FieldsAgreeNear (s.field η) (s'.field η') (fineSite R.params.side Y 0 o) (fineSite R.params.side Y' 0 o)
      (R.params.side * k - R.params.side)
end StepSettings
end YangMills.Construction
end
