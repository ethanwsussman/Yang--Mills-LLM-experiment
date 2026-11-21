import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
variable {L n k j : ℕ}
def quietPoint (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) : ChainPoint L n k := ⟨U, fun _ _ => 1⟩
abbrev meanIterate (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) (j : ℕ) :
    Tower.Edge L n k j → Matrices.ComplexMatrix2 :=
  levelField (quietPoint U) j
def meanCovariantStep (V B : Tower.Edge L n k j → Matrices.ComplexMatrix2) :
    Tower.Edge L n k (j + 1) → Matrices.ComplexMatrix2 :=
  Tower.holLeftDifferential normalizedMean V B +
    Tower.covDiff (normalizedMean V) (Tower.contourLogDrift V B)
def meanCovariant (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :
    (j : ℕ) → (Tower.Edge L n k 0 → Matrices.ComplexMatrix2) → Tower.Edge L n k j → Matrices.ComplexMatrix2
  | 0, B => B
  | j + 1, B => meanCovariantStep (meanIterate U j) (meanCovariant U j B)
def meanCovariantFrom (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) (s : ℕ) :
    (m : ℕ) → (Tower.Edge L n k s → Matrices.ComplexMatrix2) → Tower.Edge L n k (s + m) → Matrices.ComplexMatrix2
  | 0, B => B
  | m + 1, B => meanCovariantStep (meanIterate U (s + m)) (meanCovariantFrom U s m B)
def meanKernelQ (L n k : ℕ) (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :
    PeriodicOperators.KernelMatrix (Fin 3 × Tower.PositiveEdge L n k 0) (Fin 3 × Tower.PositiveEdge L n k k) :=
  (Tower.edgePauliCoordinates L n k 0).kernel (Tower.edgePauliCoordinates L n k k)
    fun B => Tower.finestMesh L k • meanCovariant U k B
def meanKernelR (L n k : ℕ) (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :
    PeriodicOperators.KernelMatrix (Fin 3 × Tower.Vertex L n k 0) (Fin 3 × Tower.Vertex L n k k) :=
  (Tower.vertexCoordinate (Tower.Vertex L n k 0)).kernel (Tower.vertexCoordinate (Tower.Vertex L n k k))
    (composedCubeAverage (quietPoint U) k)
def meanKernelFrom (L n k : ℕ) (U : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) (s m : ℕ) :
    PeriodicOperators.KernelMatrix (Fin 3 × Tower.PositiveEdge L n k s) (Fin 3 × Tower.PositiveEdge L n k (s + m)) :=
  (Tower.edgePauliCoordinates L n k s).kernel (Tower.edgePauliCoordinates L n k (s + m))
    fun B => ((L : ℝ) ^ m)⁻¹ • meanCovariantFrom U s m B
end YangMills.Construction.RunningCouplingSlope
end
