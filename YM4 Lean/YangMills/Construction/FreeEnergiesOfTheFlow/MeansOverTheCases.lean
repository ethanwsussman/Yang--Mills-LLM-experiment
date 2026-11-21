import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace YangMills.Construction.FreeEnergies
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.StepSettings
open YangMills.Construction.WeightedResponses
variable {R : StepSetup} {n : ℕ}
def truncateCases (r : ℝ) (F : CaseFunction R n) : CaseFunction R n :=
  fun W Yt ωt bad b => max (-r) (min r (F W Yt ωt bad b))
def caseMeanProperties : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n),
    (∀ W Yt ωt bad b, IsHullState R.params R.range W Yt → 0 ≤ stepWeight R C V W Yt ωt bad b) →
    (∀ F F' : CaseFunction R n,
      (∀ W Yt ωt bad b, IsHullState R.params R.range W Yt → 0 < stepWeight R C V W Yt ωt bad b →
        F W Yt ωt bad b = F' W Yt ωt bad b) →
      (CaseIntegrable R C V q F → CaseIntegrable R C V q F') ∧ caseMean R C V q F = caseMean R C V q F') ∧
    (∀ F F' : CaseFunction R n, CaseIntegrable R C V q F → CaseIntegrable R C V q F' →
      CaseIntegrable R C V q (fun W Yt ωt bad b => F W Yt ωt bad b + F' W Yt ωt bad b) ∧
      caseMean R C V q (fun W Yt ωt bad b => F W Yt ωt bad b + F' W Yt ωt bad b) =
        caseMean R C V q F + caseMean R C V q F') ∧
    (∀ (c : ℝ) (F : CaseFunction R n), CaseIntegrable R C V q F →
      CaseIntegrable R C V q (fun W Yt ωt bad b => c * F W Yt ωt bad b) ∧
      caseMean R C V q (fun W Yt ωt bad b => c * F W Yt ωt bad b) = c * caseMean R C V q F) ∧
    (∀ F F' : CaseFunction R n, CaseIntegrable R C V q F → CaseIntegrable R C V q F' →
      (∀ W Yt ωt bad b, IsHullState R.params R.range W Yt → 0 < stepWeight R C V W Yt ωt bad b →
        F W Yt ωt bad b ≤ F' W Yt ωt bad b) →
      caseMean R C V q F ≤ caseMean R C V q F') ∧
    (CaseIntegrable R C V q (fun _ _ _ _ _ => 1) → coarseStateWeight R C V q ≠ 0 →
      caseMean R C V q (fun _ _ _ _ _ => 1) = 1) ∧
    (CaseIntegrable R C V q (fun _ _ _ _ _ => 1) → ∀ F : CaseFunction R n, CaseIntegrable R C V q F →
      (∀ r : ℝ, 0 ≤ r → CaseIntegrable R C V q (truncateCases r F)) ∧
      Tendsto (fun k : ℕ => caseMean R C V q (truncateCases (k : ℝ) F)) atTop (𝓝 (caseMean R C V q F)))
end YangMills.Construction.FreeEnergies
end
