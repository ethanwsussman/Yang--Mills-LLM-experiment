import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderOnMultiplesOfASide
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import YangMills.Construction.ColdStepAtMirrorFrames.StepDensityAndItsFrame
import YangMills.Construction.ColdStepAtMirrorFrames.TransportOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusLumps
namespace ColdStepAtMirrorFrames
def torusStepParameters (T : StepParameters) [NeZero T.L] (g : LumpContours.LumpGrid T.L) :
    TorusLumps.StepParameters where
  coupling := T.a
  side := T.L
  grid := g
  baseDepth := 0
  threshold := T.σ
  κ := 1 / 8
  κ₁ := 1
  rt := T.κ
  n₁ := (T.L : ℝ) ^ (1 / 640 : ℝ)
  E := T.E
  E₃ := T.energyRatio
  derivBound := 1
  n₀ := T.n₀
  y₁ := ((2 : ℝ) ^ 16) ^ 100
  B := 1
def expansionAtFrameIsCurvatureFamily : Prop :=
  ∀ (T : StepParameters) [NeZero T.L] (g : LumpContours.LumpGrid T.L), T.IsOrdered → 2 ^ 16 ≤ T.L →
    4096 ≤ T.n₀ →
    (torusStepParameters T g).Admissible ∧
      (expansionTransportAt T → ∀ (star : Bool) (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x →
        IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
        IsLocalDensity T.L t T.n₀ (5 / 4 * T.σ) (expansionAtFrameFamily T star x f) →
        IsCurvatureFamilyOnMultiples (torusStepParameters T g) 1 T.energyRatio
          (densityOfTopFamily T.L t (expansionAtFrameFamily T star x f)))
end ColdStepAtMirrorFrames
end YangMills.Construction
end
