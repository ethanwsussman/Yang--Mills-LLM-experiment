import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
variable {L n k a b : ℕ}
def logChartCoordinates
    (f : (Edge L n k a → Matrices.ComplexMatrix2) → Edge L n k b → Matrices.ComplexMatrix2)
    (U : Edge L n k a → Matrices.ComplexMatrix2)
    (Y : PositiveEdge L n k a → Matrices.ComplexMatrix2) :
    PositiveEdge L n k b → Matrices.ComplexMatrix2 :=
  fun e => Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries
    (f (PeriodicLattice.expTwist (edgeFormOfPositiveValues Y) U) e * (f U e)⁻¹)
def AnalyticMapRepresentationStatement : Prop :=
  ∀ L n k a b : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → a ≤ k → b ≤ k →
    ∀ [Fintype (PositiveEdge L n k a)] [Fintype (PositiveEdge L n k b)]
      (S : Set (Edge L n k a → Matrices.ComplexMatrix2))
      (f : (Edge L n k a → Matrices.ComplexMatrix2) → Edge L n k b → Matrices.ComplexMatrix2),
      IsAnalyticFieldMap S f → ∀ U ∈ S, ∀ δ : ℝ, 0 < δ →
      ∃ W : Set (PositiveEdge L n k a → Matrices.ComplexMatrix2),
        (0 : PositiveEdge L n k a → Matrices.ComplexMatrix2) ∈ W ∧
        logChartCoordinates f U 0 = 0 ∧
        (∀ Y ∈ W, (∀ e, Matrices.ComplexMatrix2.operatorNorm (Y e) < δ) ∧
          PeriodicLattice.expTwist (edgeFormOfPositiveValues Y) U ∈ S ∧
          (logChartCoordinates f U Y = 0 ↔
            f (PeriodicLattice.expTwist (edgeFormOfPositiveValues Y) U) = f U)) ∧
        Matrices.GroupLieProduct.Subspaces.IsAnalyticOnSubspace
          (Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k a))
          (Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k b)) W
          (logChartCoordinates f U) ∧
        ∀ Y ∈ Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k a),
          deriv (fun t : ℝ => logChartCoordinates f U (t • Y)) 0 =
            restrictToPositiveEdges (leftDifferential f U (edgeFormOfPositiveValues Y))
end YangMills.Construction.Tower
end
