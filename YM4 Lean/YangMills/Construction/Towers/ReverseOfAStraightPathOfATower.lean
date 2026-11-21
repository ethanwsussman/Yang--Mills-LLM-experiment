import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicLattice (IsBondForm complexLieAlgebra)
namespace Tower
namespace AxisPathReversal
def HoldsOnPeriodicSide (L m k : ℕ) : Prop :=
  (∀ i : ℕ, i ≤ k →
    (∀ A ∈ edgeFormSpace L m k i, IsBondForm complexLieAlgebra A) ∧
    ∀ (x y : Vertex L m k i) (μ : Fin 4) (n : ℤ),
      y - x = n • PeriodicLattice.unitStep L m (PeriodicLattice.levelDepth k i) μ →
      ((|n| : ℤ) : ℝ) * meshAt L k i < PeriodicLattice.torusSide L m / 2 →
      (∃ q : Fin 4 × ℤ, PeriodicLattice.IsAxialDisplacement x y q.1 q.2) ∧
      (∃ q : Fin 4 × ℤ, PeriodicLattice.IsAxialDisplacement y x q.1 q.2) ∧
      PeriodicLattice.axialPath y x = PeriodicLattice.reversePath (PeriodicLattice.axialPath x y) ∧
      ∀ A : Edge L m k i → Matrices.ComplexMatrix2, IsBondForm complexLieAlgebra A →
        edgeFormPathSum A (PeriodicLattice.axialPath y x) =
          -edgeFormPathSum A (PeriodicLattice.axialPath x y)) ∧
  ∀ j : ℕ, j + 1 ≤ k → ∀ (e : Edge L m k (j + 1)) (A : Edge L m k j → Matrices.ComplexMatrix2),
    IsBondForm complexLieAlgebra A →
      (∑ᶠ z ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) e.opposite.source,
          edgeFormPathSum A (PeriodicLattice.crossingPath e.opposite z)) =
        -∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) e.source,
          edgeFormPathSum A (PeriodicLattice.crossingPath e x) ∧
      linearSmoothing L m k j A e.opposite = -linearSmoothing L m k j A e
def HoldsOnFullSpace (L k : ℕ) : Prop :=
  (∀ i : ℕ, i ≤ k →
    (∀ A ∈ FullSpace.edgeFormSpace (meshAt L k i), FullSpace.IsEdgeFormIn complexLieAlgebra A) ∧
    ∀ (x y : FullSpace.Vertex L k i) (μ : Fin 4) (n : ℤ),
      y - x = n • InfiniteLattice.axisStep (meshAt L k i) μ →
      (∃ q : Fin 4 × ℤ, FullSpace.IsAxisDisplacement x y q.1 q.2) ∧
      (∃ q : Fin 4 × ℤ, FullSpace.IsAxisDisplacement y x q.1 q.2) ∧
      FullSpace.axisPath y x =
        ((FullSpace.axisPath x y).map InfiniteLattice.Link.opposite).reverse ∧
      ∀ A : FullSpace.Edge L k i → Matrices.ComplexMatrix2,
        FullSpace.IsEdgeFormIn complexLieAlgebra A →
        FullSpace.edgeFormPathSum A (FullSpace.axisPath y x) =
          -FullSpace.edgeFormPathSum A (FullSpace.axisPath x y)) ∧
  ∀ j : ℕ, j + 1 ≤ k → ∀ (e : FullSpace.Edge L k (j + 1))
    (A : FullSpace.Edge L k j → Matrices.ComplexMatrix2),
    FullSpace.IsEdgeFormIn complexLieAlgebra A →
      (∑ᶠ z ∈ FullSpace.cubeVertices L (meshAt L k j) e.opposite.initial,
          FullSpace.edgeFormPathSum A (FullSpace.crossingPath e.opposite z)) =
        -∑ᶠ x ∈ FullSpace.cubeVertices L (meshAt L k j) e.initial,
          FullSpace.edgeFormPathSum A (FullSpace.crossingPath e x) ∧
      FullSpace.linearSmoothing L A e.opposite = -FullSpace.linearSmoothing L A e
def MainStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ,
    (∀ m : ℕ, 0 < m → HoldsOnPeriodicSide L m k) ∧ HoldsOnFullSpace L k
end AxisPathReversal
end Tower
end YangMills.Construction
end
