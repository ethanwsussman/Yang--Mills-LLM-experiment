import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.FormsOnTowers
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace ContourLogarithms
def vertexCubePairs (L n k i : ℕ) : Set (Vertex L n k (i + 1) × Vertex L n k i) :=
  {q | q.2 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) q.1}
def expCurve {L n k i : ℕ} (V X : Edge L n k i → Matrices.ComplexMatrix2) (t : ℝ) :
    Edge L n k i → Matrices.ComplexMatrix2 :=
  PeriodicLattice.expTwist ((t : ℂ) • X) V
def ContourLogDifferentiable : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → ∀ i < k,
    (vertexCubePairs L n k i).Finite ∧
      EventuallyNearIdentity (fieldSpace L n k i) fun V =>
        ∀ q ∈ vertexCubePairs L n k i, ∀ X ∈ edgeFormSpace L n k i,
          (∀ᶠ t : ℝ in 𝓝 0,
            PeriodicLattice.HasContourMean (expCurve V X t) q.1 q.2 ∧
              Matrices.ComplexMatrix2.operatorNorm
                (PeriodicLattice.meanContourHolonomy (expCurve V X t) q.1 q.2 - 1) < 1) ∧
          DifferentiableAt ℝ
            (fun t : ℝ => Matrices.ComplexMatrix2.logSeries
              (PeriodicLattice.meanContourHolonomy (expCurve V X t) q.1 q.2)) 0
end ContourLogarithms
end Tower
end YangMills.Construction
end
