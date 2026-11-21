import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
variable {L n k j j' : ℕ}
def lineLogarithm
    (φ : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2)
    (V X : Edge L n k j → Matrices.ComplexMatrix2) (e : PositiveEdge L n k j') (t : ℝ) :
    Matrices.ComplexMatrix2 :=
  Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries
    (φ (PeriodicLattice.expTwist ((t : ℂ) • X) V) e * (φ V e)⁻¹)
def LeftChartTaylorCoefficientsAnalytic : Prop :=
  ∀ L n k j j' : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → j ≤ k → j' ≤ k →
    (∀ (U : Set (Edge L n k j → Matrices.ComplexMatrix2))
      (F : (Edge L n k j → Matrices.ComplexMatrix2) → ℝ),
      IsAnalyticFieldFunction U F → ∀ X ∈ edgeFormSpace L n k j,
        IsAnalyticFieldFunction U (fun V => leftDeriv F V X) ∧
        ∀ X' ∈ edgeFormSpace L n k j, IsAnalyticFieldFunction U fun V => leftSecondDeriv F V X X') ∧
    ∀ (U : Set (Edge L n k j → Matrices.ComplexMatrix2))
      (φ : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k j' → Matrices.ComplexMatrix2),
      IsAnalyticFieldMap U φ → ∀ X ∈ edgeFormSpace L n k j, ∀ (e : PositiveEdge L n k j')
        (ψ : Matrices.ComplexMatrix2 →ₗ[ℝ] ℝ),
        (IsAnalyticFieldFunction U fun V => ψ (deriv (lineLogarithm φ V X e) 0)) ∧
        IsAnalyticFieldFunction U fun V => ψ (iteratedDeriv 2 (lineLogarithm φ V X e) 0)
end YangMills.Construction.Tower
end
