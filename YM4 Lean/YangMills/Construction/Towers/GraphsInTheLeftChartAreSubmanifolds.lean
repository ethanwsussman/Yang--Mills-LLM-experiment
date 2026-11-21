import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
variable {L n k a : ℕ}
structure IsLeftChartGraphAt [Fintype (PositiveEdge L n k a)] (N : Set (Edge L n k a → Matrices.ComplexMatrix2))
    (V : Edge L n k a → Matrices.ComplexMatrix2)
    (E E' : Submodule ℝ (PositiveEdge L n k a → Matrices.ComplexMatrix2))
    (O O' : Set (PositiveEdge L n k a → Matrices.ComplexMatrix2))
    (f : (PositiveEdge L n k a → Matrices.ComplexMatrix2) → PositiveEdge L n k a → Matrices.ComplexMatrix2) :
    Prop where
  sup_eq : E ⊔ E' = Matrices.GroupLieProduct.hermitianTracelessFunctions (PositiveEdge L n k a)
  inf_eq : E ⊓ E' = ⊥
  relOpen_left : Matrices.ComplexMatrix2.IsRelativelyOpen (E : Set (PositiveEdge L n k a → Matrices.ComplexMatrix2)) O
  relOpen_right : Matrices.ComplexMatrix2.IsRelativelyOpen (E' : Set (PositiveEdge L n k a → Matrices.ComplexMatrix2)) O'
  zero_mem_left : (0 : PositiveEdge L n k a → Matrices.ComplexMatrix2) ∈ O
  zero_mem_right : (0 : PositiveEdge L n k a → Matrices.ComplexMatrix2) ∈ O'
  norm_sum_lt : ∀ X ∈ O, ∀ X' ∈ O', ∀ c, Matrices.ComplexMatrix2.operatorNorm ((X + X') c) < 1 / 2
  mapsTo : MapsTo f O O'
  map_zero : f 0 = 0
  analytic : Matrices.GroupLieProduct.Subspaces.IsAnalyticOnSubspace E E' O f
  contDiff : ∀ (d : ℕ) (ι : (Fin d → ℝ) →L[ℝ] (PositiveEdge L n k a → Matrices.ComplexMatrix2)), (∀ u, ι u ∈ E) →
    ContDiffOn ℝ ∞ (f ∘ ι) (ι ⁻¹' O)
  hasDerivAt_zero : ∀ X ∈ E, HasDerivAt (fun t : ℝ => f (t • X)) 0 0
  mem_iff : ∀ X ∈ O, ∀ X' ∈ O',
    (PeriodicLattice.expTwist (edgeFormOfPositiveValues (X + X')) V ∈ N ↔ X' = f X)
def LeftChartGraphsAreSubmanifolds : Prop :=
  ∀ L n k a : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → a ≤ k →
    ∀ [Fintype (PositiveEdge L n k a)] (N : Set (Edge L n k a → Matrices.ComplexMatrix2)),
      N ⊆ fieldSpace L n k a →
      ((∀ V ∈ N, ∃ E E' O O' f, IsLeftChartGraphAt N V E E' O O' f) → IsAnalyticFieldSubmanifold N) ∧
      ∀ V ∈ N, ∀ E E' O O' f, IsLeftChartGraphAt N V E E' O O' f → ∀ X ∈ E,
        edgeFormOfPositiveValues X ∈ (fieldCurveData L n k a).tangentSpan N V
end YangMills.Construction.Tower
end
