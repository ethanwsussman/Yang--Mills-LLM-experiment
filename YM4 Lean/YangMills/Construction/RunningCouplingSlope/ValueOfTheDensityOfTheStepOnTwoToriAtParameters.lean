import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames RenormalizationStepParameters TorusFields ReferenceDensity
def stepDensityLocalityStatement : Prop :=
  ∃ c : ChainParameters → ℝ, (∀ l, 0 < c l) ∧ ∀ T : ParameterAssignment, T.Admissible → ∃ C : ℝ, 0 < C ∧
    ∀ (t n n' : ℕ), 64 ≤ n → 64 ≤ n' →
      ∀ (Y : (torusFrame T.side t n).Cell) (Y' : (torusFrame T.side t n').Cell)
        (V : (torusFrame T.side t n).GaugeField (torusFrame T.side t n).top)
        (V' : (torusFrame T.side t n').GaugeField (torusFrame T.side t n').top) (r : ℕ),
        IsSmallCurvature (9 / 8 * T.threshold) V → IsSmallCurvature (9 / 8 * T.threshold) V' →
        AgreeOnBall (finiteCells (torusFrame T.side t n)) V (finiteCells (torusFrame T.side t n')) V' Y Y' r →
        |stepDensity T.coupling T.ρA T.lam Y V - stepDensity T.coupling T.ρA T.lam Y' V'| ≤
          C * Real.exp (-(c T.toChainParameters * r))
end YangMills.Construction.RunningCouplingSlope
end
