import YangMills.Construction.Towers.FunctionalInTheBackgroundGaugeInTheExponentialChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def ExpChartFirstDerivVanishes : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    ∀ [Fintype (PositiveEdge L n k 0)] [Fintype (PositiveEdge L n k k)]
      (x : FieldTriple L n k),
      expChartFirstDeriv x = 0
end YangMills.Construction.Tower
end
