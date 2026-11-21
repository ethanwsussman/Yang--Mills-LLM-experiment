import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import YangMills.Construction.Towers.InjectiveCovariantDifference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def IdentityPrincipleNearOneStatement : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    ∀ (S : Set (Edge L n k k → Matrices.ComplexMatrix2))
      (g : (Edge L n k k → Matrices.ComplexMatrix2) → ℝ) (r : ℝ),
      IsOpenNhdOfOne S → IsAnalyticFieldFunction S g →
        EventuallyNearIdentity (fieldSpace L n k k) (fun U => CovDiffInjective U → g U = r) →
          EventuallyNearIdentity (fieldSpace L n k k) fun U => g U = r
end YangMills.Construction.Tower
end
