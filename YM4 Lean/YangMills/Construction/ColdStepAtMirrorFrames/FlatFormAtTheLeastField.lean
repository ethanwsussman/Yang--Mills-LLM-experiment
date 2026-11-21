import YangMills.Construction.ColdStepAtMirrorFrames.StepDensityAndItsFrame
import YangMills.Construction.ColdStepAtMirrorFrames.TransportOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def ExpansionAtFrameIsLocalDensityAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (star : Bool), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    IsLocalDensity T.L t T.n₀ (5 / 4 * T.σ) (expansionAtFrameFamily T star x f)
def flatLimitAtMinimizerStatement : Prop :=
  ∀ T : StepParameters, T.IsOrdered → 2 ^ 16 ≤ T.L → 4096 ≤ T.n₀ → expansionTransportAt T →
    ExpansionAtFrameIsLocalDensityAt T →
    ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x →
      IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
      HasBoundedFlatLimitForm T.L t (expansionAtFrameFamily T true x f) 0
end ColdStepAtMirrorFrames
end YangMills.Construction
end
