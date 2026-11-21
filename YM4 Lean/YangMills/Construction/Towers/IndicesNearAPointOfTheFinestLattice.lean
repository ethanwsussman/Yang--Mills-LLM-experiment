import YangMills.Construction.PeriodicOperators.BoundOfTheComponentsOfAJet
import YangMills.Construction.Towers.TheScaledPicture
import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.FinestLatticeNeighbours
def FieldBoundedNear (L k : ℕ) (y : InfiniteLattice.AmbientSpace)
    (a : (Tower.remainderIndex L k).Carrier → ℂ) (M : ℝ) : Prop :=
  (∀ e : PeriodicOperators.PosEdge L k 0,
    PeriodicOperators.WithinBox (2 * Tower.finestMesh L k) e.1.initial y →
      Matrices.ComplexMatrix2.operatorNorm (Tower.ofPauliCoeffs a e) ≤ M) ∧
  ∀ P : Tower.FullSpace.Face L k 0,
    PeriodicOperators.WithinBox (2 * Tower.finestMesh L k) P.corner y →
      Matrices.ComplexMatrix2.operatorNorm
        (Tower.FullSpace.scaledEdgeCoboundary
          ((Tower.FullSpace.edgePauliCoordinates L k 0).ofCoeffs a) P) ≤ M
def CoeffsLocallyBounded {I J : PeriodicOperators.PeriodicData} (L k : ℕ)
    (T : ((Tower.remainderIndex L k).Carrier → ℂ) → J.Carrier → I.Carrier → ℂ) (c : ℝ) : Prop :=
  (∀ (ζ ζ' : (Tower.remainderIndex L k).Carrier → ℂ) (j : J.Carrier) (i : I.Carrier),
    ¬ PeriodicOperators.WithinBox (2 * Tower.finestMesh L k) (I.pos i) (J.pos j) →
      PeriodicOperators.coeffOne (Tower.remainderIndex L k) I J T ζ j i = 0 ∧
        PeriodicOperators.coeffTwo (Tower.remainderIndex L k) I J T ζ ζ' j i = 0) ∧
  ∀ (a b : (Tower.remainderIndex L k).Carrier → ℂ) (M : ℝ) (j : J.Carrier) (i : I.Carrier),
    0 ≤ M → FieldBoundedNear L k (J.pos j) a M → FieldBoundedNear L k (J.pos j) b M →
      ‖PeriodicOperators.coeffOne (Tower.remainderIndex L k) I J T
          (((Tower.finestMesh L k : ℝ) : ℂ) • a) j i‖ ≤ c * M ∧
        ‖PeriodicOperators.coeffTwo (Tower.remainderIndex L k) I J T
          (((Tower.finestMesh L k : ℝ) : ℂ) • a)
          (((Tower.finestMesh L k : ℝ) : ℂ) • b) j i‖ ≤ c * M ^ 2
def NeighbourCountBound : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ y : InfiniteLattice.AmbientSpace,
    {i : (PeriodicOperators.colourVertices L k 0).Carrier |
        PeriodicOperators.WithinBox (2 * Tower.finestMesh L k)
          ((PeriodicOperators.colourVertices L k 0).pos i) y}.encard ≤ 11250 ∧
      {i : (PeriodicOperators.colourEdges L k 0).Carrier |
        PeriodicOperators.WithinBox (2 * Tower.finestMesh L k)
          ((PeriodicOperators.colourEdges L k 0).pos i) y}.encard ≤ 11250 ∧
      {i : (PeriodicOperators.colourFaces L k 0).Carrier |
        PeriodicOperators.WithinBox (2 * Tower.finestMesh L k)
          ((PeriodicOperators.colourFaces L k 0).pos i) y}.encard ≤ 11250
end YangMills.Construction.Tower.FullSpace.FinestLatticeNeighbours
end
