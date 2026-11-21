import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
namespace StepSettings
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts
variable {R : StepSetup} {n : ℕ}
def ChartSetting.kernelProduct [NeZero n] (s : ChartSetting R n) (η : FreeCoords s.free) : ℝ :=
  ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4,
    bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 (s.field η))
      (readAtLevel (stepBlockFrame R.params.side n) 1 s.coarse) s.bases c
def ChartSetting.haarJacobian (s : ChartSetting R n) (η : FreeCoords s.free) : ℝ :=
  ∏ b : s.free, haarLogDensity (toCoords (s.frame b.1) + η b)
def PotentialFactorization : Prop :=
  ∀ R : StepSetup, R.params.Admissible → R.HasExpansions → 0 < R.anchorRadius →
    R.anchorRadius + R.ballRadius < Real.pi →
    ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ s : ChartSetting R n, s.IsAdmissible →
      ∀ η : FreeCoords s.free, s.InBalls η →
        0 < R.functional (n * R.params.side) (trivialField (n * R.params.side)) ∧
        0 < s.kernelProduct η ∧ 0 < s.haarJacobian η ∧
        R.labelWeight (n * R.params.side) (s.field η) s.support s.labelling * s.kernelProduct η *
            s.haarJacobian η =
          R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
            (∏ X ∈ chainComponents R.range s.support,
              R.clusterFactor (n * R.params.side) (s.field η) s.support s.labelling X) *
            Real.exp (-s.potential η) ∧
        ((∏ X ∈ chainComponents R.range s.support,
            R.clusterFactor (n * R.params.side) (s.field η) s.support s.labelling X) ≠ 0 →
          s.potential η = -Real.log (R.labelWeight (n * R.params.side) (s.field η) s.support s.labelling /
              (R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
                ∏ X ∈ chainComponents R.range s.support,
                  R.clusterFactor (n * R.params.side) (s.field η) s.support s.labelling X) *
            s.kernelProduct η * s.haarJacobian η))
end StepSettings
end YangMills.Construction
end
