import YangMills.Construction.RunningCouplingSlope.EntriesWithJetsMakeALocalFamily
import YangMills.Construction.RunningCouplingSlope.FinePartsAtAnAbelianField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
variable {L n k : ℕ}
def vertexEdgeIncidence (e : Fin 3 × Tower.PositiveEdge L n k 0) (v : Fin 3 × Tower.Vertex L n k 0) : Prop :=
  v.2 = e.2.1.target
def faceEdgeIncidence (f : Fin 3 × Tower.Face L n k 0) (e : Fin 3 × Tower.PositiveEdge L n k 0) : Prop :=
  ∃ i, e.2 = facePositiveEdge f.2 i
def faceDiagonal (f' f : Fin 3 × Tower.Face L n k 0) : Prop := f = f'
def edgesShareFace (e' e : Fin 3 × Tower.PositiveEdge L n k 0) : Prop :=
  ∃ (p : Tower.Face L n k 0) (i j : Fin 4),
    facePositiveEdge p i = e'.2 ∧ facePositiveEdge p j = e.2
def FinePartRelationsSparse : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k : ℕ,
    ∀ [Fintype (Fin 3 × Tower.PositiveEdge L n k 0)] [Fintype (Fin 3 × Tower.Vertex L n k 0)]
      [Fintype (Fin 3 × Tower.Face L n k 0)],
    IsBoundedSparsityOnCells colouredVertexCell colouredEdgeCell
        (vertexEdgeIncidence (L := L) (n := n) (k := k)) 768 768 8 ∧
      IsBoundedSparsityOnCells colouredEdgeCell colouredFaceCell
        (faceEdgeIncidence (L := L) (n := n) (k := k)) 768 768 8 ∧
      IsBoundedSparsityOnCells colouredFaceCell colouredFaceCell
        (faceDiagonal (L := L) (n := n) (k := k)) 768 768 8 ∧
      IsBoundedSparsityOnCells colouredEdgeCell colouredEdgeCell
        (edgesShareFace (L := L) (n := n) (k := k)) 768 768 8 ∧
      (∀ q : Tower.PositiveEdge L n k 0,
        Nat.card {p : Tower.Face L n k 0 // ∃ i, facePositiveEdge p i = q} ≤ 64) ∧
      ∀ (p : Tower.Face L n k 0) (i : Fin 4),
        cellDist (fineVertexCell (k := k) (faceEdge p i).source) (fineVertexCell (k := k) p.origin) ≤ 4
end YangMills.Construction.RunningCouplingSlope
end
