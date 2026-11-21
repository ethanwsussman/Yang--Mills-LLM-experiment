import YangMills.Construction.RunningCouplingSlope.MatricesOfTheWholeChain
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
variable {L n k : ℕ}
def topIndexCell (p : Fin 3 × PositiveEdge L n k k) : Vertex L n k k :=
  levelVertexCell p.2.1.source
def fineIndexCell (p : Fin 3 × Vertex L n k 0) : Vertex L n k k := levelVertexCell p.2
abbrev TripleCoordIndex (L n k : ℕ) : Type :=
  LevelFormIndex L n k ⊕ LevelFormIndex L n k ⊕ Fin 3 × PositiveEdge L n k k
def tripleCoordIndexCell : TripleCoordIndex L n k → Vertex L n k k :=
  Sum.elim levelFormIndexCell (Sum.elim levelFormIndexCell topIndexCell)
def complexifyCoords {I : Type} (x : I → ℝ) : I → ℂ := fun i => (x i : ℂ)
section RealCoordinates
variable [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [Fintype (Fin 3 × Vertex L n k 0)]
  [Fintype (Fin 3 × Vertex L n k k)]
def tripleCoords (P : PauliCoordinates L n k) (τ : LevelTriple L n k) :
    TripleCoordIndex L n k → ℝ :=
  Sum.elim (P.formCoords τ.1) (Sum.elim (P.formCoords τ.2.1) (P.topFormCoords τ.2.2))
def tripleOfCoords (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ) :
    LevelTriple L n k :=
  (P.formCoords.symm fun p => x (.inl p), P.formCoords.symm (fun p => x (.inr (.inl p))),
    P.topFormCoords.symm fun p => x (.inr (.inr p)))
def pointOfCoords (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ) :
    ChainPoint L n k :=
  expMove (tripleOfCoords P x).1 (unitPoint L n k)
def fineVertexCoords (P : PauliCoordinates L n k) (l : vertexFunctionSpace L n k 0) :
    Fin 3 × Vertex L n k 0 → ℝ :=
  fun p => P.ghostCoords (l, 0) (.inl p)
end RealCoordinates
def complexFineValues (z : TripleCoordIndex L n k → ℂ) :
    Edge L n k 0 → Matrices.ComplexMatrix2 :=
  edgeFormOfPositiveValues (ofPauliCoeffs fun p => z (.inl (.inl p)))
def complexLevelValues (z : TripleCoordIndex L n k → ℂ) (i : Fin k) :
    PositiveEdge L n k (i + 1) → Matrices.ComplexMatrix2 :=
  ofPauliCoeffs fun p => z (.inl (.inr ⟨i, p⟩))
def complexChainPoint (z : TripleCoordIndex L n k → ℂ) : ChainPoint L n k :=
  ⟨PeriodicLattice.expTwist (complexFineValues z) (unitPoint L n k).fine,
    fun i c => Matrices.ComplexMatrix2.matExp (Complex.I • complexLevelValues z i c) *
      (unitPoint L n k).noise i c⟩
structure IsLocallyHolomorphicFamily {I ι ι' : Type} [Fintype I] [Fintype ι] [Fintype ι']
    [DecidableEq ι] (e : I → Vertex L n k k) (c : ι → Vertex L n k k)
    (c' : ι' → Vertex L n k k)
    (F : (I → ℂ) → Matrix ι' ι ℂ) (ρ C r : ℝ) : Prop where
  holomorphic : ∀ p q, AnalyticOnNhd ℂ (fun z => F z p q) (Metric.ball 0 ρ)
  norm_le : ∀ z ∈ Metric.ball (0 : I → ℂ) ρ, ‖F z‖ ≤ C
  depends_near : ∀ p q, ∀ z ∈ Metric.ball (0 : I → ℂ) ρ, ∀ z' ∈ Metric.ball (0 : I → ℂ) ρ,
    (∀ i, cellDist (e i) (c' p) ≤ r → z i = z' i) → F z p q = F z' p q
  eq_zero_of_far : ∀ z ∈ Metric.ball (0 : I → ℂ) ρ, ∀ p q,
    r < cellDist (c' p) (c q) → F z p q = 0
end YangMills.Construction.RunningCouplingSlope
end
