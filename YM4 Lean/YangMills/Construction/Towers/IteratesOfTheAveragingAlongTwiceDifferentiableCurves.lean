import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def SmoothingIterAlongTwiceDiffCurves : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i ≤ k →
    EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
      ∀ (I : Set ℝ) (γ : ℝ → Edge L n k 0 → Matrices.ComplexMatrix2),
        (fieldCurveData L n k 0).IsTwiceDiffCurve I γ → γ 0 = U →
        (fieldCurveData L n k 0).tangent γ ∈ edgeFormSpace L n k 0 →
        ∃ J : Set ℝ, IsOpenIntervalAroundZero J ∧ J ⊆ I ∧
          (fieldCurveData L n k i).IsTwiceDiffCurve J
            (fun t => smoothingIter L n k i (γ t)) ∧
          (fieldCurveData L n k i).tangent (fun t => smoothingIter L n k i (γ t)) =
            leftDifferential (smoothingIter L n k i) U ((fieldCurveData L n k 0).tangent γ)
end YangMills.Construction.Tower
end
