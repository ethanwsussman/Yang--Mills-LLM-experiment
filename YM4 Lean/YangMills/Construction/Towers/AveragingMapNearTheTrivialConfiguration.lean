import YangMills.Construction.Conventions.BlockingFactorDependence
import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfigurationDefs
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower
def polydiscRadius (L : ℕ) : ℝ := Classical.epsilon (IsAdmissiblePolydiscRadius L)
def SmoothingNearIdentity : Prop :=
  (∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ n k j : ℕ, 0 < n → j < k →
      SmoothingAnalyticCovariant L n k j ∧ SmoothingDerivAtOne L n k j ∧
        SmoothingEquivariant L n k j) ∧
    (∀ k j : ℕ, j < k →
      FullSpace.SmoothingAnalyticCovariant L k j ∧ FullSpace.SmoothingDerivAtOne L k j ∧
        FullSpace.SmoothingEquivariant L k j) ∧
    IsAdmissiblePolydiscRadius L (polydiscRadius L)) ∧
  ∀ (D : Type) (l : D → Conventions.AdmissibleBlockingFactors),
    Conventions.FactorsThroughBlockingFactor .number l fun d => polydiscRadius (l d).1
end Tower
end YangMills.Construction
end
