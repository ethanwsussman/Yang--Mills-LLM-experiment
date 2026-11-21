import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfiguration
import YangMills.Construction.Towers.ChartAtTheTrivialConfigurationDefs
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower
def stepRemainderRadius (L : ℕ) : ℝ := polydiscRadius L / 2
def stepRemainderConstant (L : ℕ) : ℝ :=
  (1 + 5 * (L : ℝ) * stepRemainderRadius L) * (stepRemainderRadius L)⁻¹ ^ 2
namespace StepRemainder
open IdentityExpChart (expForm)
def logMeanDefect {L n k j : ℕ} (A : Edge L n k j → Matrices.ComplexMatrix2) (e : Edge L n k (j + 1)) :
    Matrices.ComplexMatrix2 :=
  Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries
      (PeriodicLattice.complexBlockAverageStep j (expForm A) e) -
    linearSmoothing L n k j A e
def QuadraticBound : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j < k →
    ∀ e : Edge L n k (j + 1), e.IsPositivelyOriented →
      ∀ A ∈ complexEdgeForms L n k j, maxOperatorNorm A ≤ ENNReal.ofReal (stepRemainderRadius L / 2) →
        expForm A ∈ nearIdentityPolydisc (polydiscRadius L) e ∧
          Matrices.ComplexMatrix2.operatorNorm (logMeanDefect A e) ≤
            stepRemainderConstant L * (maxOperatorNorm A).toReal ^ 2
end StepRemainder
end YangMills.Construction.Tower
end
