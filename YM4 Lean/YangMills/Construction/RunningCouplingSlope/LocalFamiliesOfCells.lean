import YangMills.Construction.RunningCouplingSlope.CellsOfATower
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
variable {L n k : ℕ}
def fineVertexCell (x : Tower.Vertex L n k 0) : Tower.Vertex L n k k :=
  Classical.epsilon fun y =>
    (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k y
def colouredVertexCell (p : Fin 3 × Tower.Vertex L n k 0) : Tower.Vertex L n k k :=
  fineVertexCell p.2
def colouredEdgeCell (p : Fin 3 × Tower.PositiveEdge L n k 0) : Tower.Vertex L n k k :=
  fineVertexCell p.2.1.source
def colouredFaceCell (p : Fin 3 × Tower.Face L n k 0) : Tower.Vertex L n k k :=
  fineVertexCell p.2.origin
structure IsLocalAlongBackground {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    (c : ι → Tower.Vertex L n k k) (c' : ι' → Tower.Vertex L n k k) (T : ℝ → ℝ → Matrix ι' ι ℂ)
    (w : Fin 4 → ℤ) (M θ : ℝ) : Prop where
  contDiffAt_entry : ∀ p q, ContDiffAt ℝ 2 (fun v : ℝ × ℝ => T v.1 v.2 p q) 0
  value_local : IsLocalOnCells c c' (T 0 0) M θ fun _ => 1
  derivFirst_local : IsLocalOnCells c c' (derivFirst T) M θ
    (cellDecayWeight θ (cellOfCoords L n k 0))
  derivSecond_local : IsLocalOnCells c c' (derivSecond T) M θ
    (cellDecayWeight θ (cellOfCoords L n k w))
  derivMixed_local : IsLocalOnCells c c' (derivMixed T) M θ
    fun y => cellDecayWeight θ (cellOfCoords L n k 0) y * cellDecayWeight θ (cellOfCoords L n k w) y
def IsEdgePeriodization (L n k : ℕ)
    (T : (PeriodicOperators.colourEdges L k 0).Carrier →
      (PeriodicOperators.colourEdges L k 0).Carrier → ℂ)
    (M : Matrix (Fin 3 × Tower.PositiveEdge L n k 0) (Fin 3 × Tower.PositiveEdge L n k 0) ℂ) : Prop :=
  ∀ i' i : (PeriodicOperators.colourEdges L k 0).Carrier,
    M (i'.1, LocalKernels.projPositiveEdge L n k 0 i'.2)
        (i.1, LocalKernels.projPositiveEdge L n k 0 i.2) =
      PeriodicOperators.periodization (PeriodicOperators.colourEdges L k 0)
        (PeriodicOperators.colourEdges L k 0) T (LocalKernels.Periodisation.periodSide L n) i' i
def IsVertexPeriodization (L n k : ℕ)
    (T : (PeriodicOperators.colourVertices L k 0).Carrier →
      (PeriodicOperators.colourVertices L k 0).Carrier → ℂ)
    (M : Matrix (Fin 3 × Tower.Vertex L n k 0) (Fin 3 × Tower.Vertex L n k 0) ℂ) : Prop :=
  ∀ i' i : (PeriodicOperators.colourVertices L k 0).Carrier,
    M (i'.1, Tower.FullSpace.projVertex L n k 0 i'.2) (i.1, Tower.FullSpace.projVertex L n k 0 i.2) =
      PeriodicOperators.periodization (PeriodicOperators.colourVertices L k 0)
        (PeriodicOperators.colourVertices L k 0) T (LocalKernels.Periodisation.periodSide L n) i' i
def periodicEdgeResolventSqrt (L n k : ℕ) :
    Matrix (Fin 3 × Tower.PositiveEdge L n k 0) (Fin 3 × Tower.PositiveEdge L n k 0) ℂ :=
  Classical.epsilon (IsEdgePeriodization L n k (Tower.FreeResolvents.edgeResolventSqrt L k))
def periodicVertexResolventSqrt (L n k : ℕ) :
    Matrix (Fin 3 × Tower.Vertex L n k 0) (Fin 3 × Tower.Vertex L n k 0) ℂ :=
  Classical.epsilon (IsVertexPeriodization L n k (Tower.FreeResolvents.vertexResolventSqrt L k))
def unitNormScale (L k : ℕ) : ℂ := (((Tower.finestMesh L k ^ 2)⁻¹ : ℝ) : ℂ)
def rescaledQAlong (L n k : ℕ) (w : Fin 4 → ℤ) (s t : ℝ) :
    Matrix (Fin 3 × Tower.PositiveEdge L n k k) (Fin 3 × Tower.PositiveEdge L n k 0) ℂ :=
  unitNormScale L k • Matrix.of (Tower.rescaledOperators L n k (twoSourceBackground L n k w s t)).Q
def meanQAlong (L n k : ℕ) (w : Fin 4 → ℤ) (s t : ℝ) :
    Matrix (Fin 3 × Tower.PositiveEdge L n k k) (Fin 3 × Tower.PositiveEdge L n k 0) ℂ :=
  unitNormScale L k • Matrix.of (meanKernelQ L n k (twoSourceBackground L n k w s t))
def rescaledRAlong (L n k : ℕ) (w : Fin 4 → ℤ) (s t : ℝ) :
    Matrix (Fin 3 × Tower.Vertex L n k k) (Fin 3 × Tower.Vertex L n k 0) ℂ :=
  unitNormScale L k • Matrix.of (Tower.rescaledOperators L n k (twoSourceBackground L n k w s t)).R
def meanRAlong (L n k : ℕ) (w : Fin 4 → ℤ) (s t : ℝ) :
    Matrix (Fin 3 × Tower.Vertex L n k k) (Fin 3 × Tower.Vertex L n k 0) ℂ :=
  unitNormScale L k • Matrix.of (meanKernelR L n k (twoSourceBackground L n k w s t))
def noiseAlong (a : ℝ) (L n k : ℕ) (w : Fin 4 → ℤ) (s t : ℝ) :
    Matrix (Fin 3 × Tower.PositiveEdge L n k k) (Fin 3 × Tower.PositiveEdge L n k k) ℂ :=
  Matrix.of (noiseCovariance a L n k (twoSourceBackground L n k w s t) k)
section ResolventConjugation
variable [Fintype (Fin 3 × Tower.PositiveEdge L n k 0)] [Fintype (Fin 3 × Tower.Vertex L n k 0)]
def xiConjugated (L n k : ℕ) [Fintype (Fin 3 × Tower.PositiveEdge L n k 0)] (w : Fin 4 → ℤ) (s t : ℝ) :
    Matrix (Fin 3 × Tower.PositiveEdge L n k 0) (Fin 3 × Tower.PositiveEdge L n k 0) ℂ :=
  periodicEdgeResolventSqrt L n k *
    Matrix.of (Tower.rescaledOperators L n k (twoSourceBackground L n k w s t)).Xi *
    periodicEdgeResolventSqrt L n k
def yConjugated (L n k : ℕ) [Fintype (Fin 3 × Tower.Vertex L n k 0)] (w : Fin 4 → ℤ) (s t : ℝ) :
    Matrix (Fin 3 × Tower.Vertex L n k 0) (Fin 3 × Tower.Vertex L n k 0) ℂ :=
  periodicVertexResolventSqrt L n k *
    Matrix.of (Tower.rescaledOperators L n k (twoSourceBackground L n k w s t)).Y *
    periodicVertexResolventSqrt L n k
end ResolventConjugation
end YangMills.Construction.RunningCouplingSlope
end
