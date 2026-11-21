import YangMills.Construction.RunningCouplingSlope.FamiliesThroughOne
import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import Mathlib
open Filter
open scoped Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def LevelFieldsAnalyticAlongFamily : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (X : E → ChainPoint L n k) (p₀ : E),
      IsAnalyticFamilyThroughUnit X p₀ →
      (∀ j ≤ k, ∀ b : Tower.Edge L n k j,
        AnalyticAt ℝ (fun p => RunningCouplingSlope.levelField (X p) j b) p₀ ∧ RunningCouplingSlope.levelField (X p₀) j b = 1) ∧
      (∀ (i : Fin k) (c : Tower.PositiveEdge L n k (i + 1)),
        AnalyticAt ℝ (fun p => meanRadius (RunningCouplingSlope.levelField (X p) i) c.1) p₀ ∧
          meanRadius (RunningCouplingSlope.levelField (X p₀) i) c.1 = 1) ∧
      ∀ᶠ p in 𝓝 p₀, IsCompactValued (X p)
end YangMills.Construction.RunningCouplingSlope
end
