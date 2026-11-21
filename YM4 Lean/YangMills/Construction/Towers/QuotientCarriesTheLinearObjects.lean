import YangMills.Construction.Towers.QuotientMapOnBonds
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def pushforwardForm (L n k i : ℕ) (S : Set (Tower.FullSpace.Edge L k i))
    (B : Tower.FullSpace.Edge L k i → Matrices.ComplexMatrix2) :
    Tower.Edge L n k i → Matrices.ComplexMatrix2 :=
  open Classical in
  fun c => if h : ∃ e ∈ S, Tower.FullSpace.projEdge L n k i e = c then B h.choose else 0
def ProjectionCommutesWithSmoothing : Prop :=
  ∀ L k j n : ℕ, Conventions.IsAdmissibleBlockingFactor L → j < k → 0 < n →
    ∀ c : Tower.FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
    ∀ B : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2,
      (∀ y : Tower.FullSpace.Vertex L k (j + 1), y = c.initial ∨ y = c.terminal →
        ∀ x ∈ Tower.FullSpace.cubeVertices L (Tower.meshAt L k j) y,
          PeriodicLattice.contourFormAverage
              (pushforwardForm L n k j
                (Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k j) c) B)
              (Tower.FullSpace.projVertex L n k (j + 1) y) (Tower.FullSpace.projVertex L n k j x) =
            Tower.FullSpace.contourAverage L B y x) ∧
      Tower.linearSmoothing L n k j
          (pushforwardForm L n k j (Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k j) c) B)
          (Tower.FullSpace.projEdge L n k (j + 1) c) =
        Tower.FullSpace.linearSmoothing L B c
end YangMills.Construction.Tower.FullSpace
end
