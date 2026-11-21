import YangMills.Construction.TorusOrFourSpace.FunctionsOfClassC1SupportsAndNorms
import YangMills.Construction.TorusOrFourSpace.FunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
def SmoothIffSmoothAsTuple : Prop :=
  ∀ (P : PeriodicSpace.Params) (Y : PeriodicSpace.Kind) (u : Y.Pt P → ℝ),
    IsSmoothFn P Y u ↔
      Tuple.IsSmoothT P Y (Tuple.ofSingle P Y fun y => (u y : ℂ))
end YangMills.Construction.PeriodicSpace.Kind
