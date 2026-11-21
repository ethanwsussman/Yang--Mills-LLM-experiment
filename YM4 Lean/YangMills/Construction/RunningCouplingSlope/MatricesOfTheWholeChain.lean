import YangMills.Construction.RunningCouplingSlope.TriplesCarriedByACell
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
variable {L n k : ℕ}
abbrev LevelFormIndex (L n k : ℕ) : Type :=
  Fin 3 × Tower.PositiveEdge L n k 0 ⊕ (Σ i : Fin k, Fin 3 × Tower.PositiveEdge L n k (i + 1))
def levelFormIndexCell : LevelFormIndex L n k → Tower.Vertex L n k k
  | .inl p => levelVertexCell p.2.1.source
  | .inr p => levelVertexCell p.2.2.1.source
abbrev SaddlePointIndex (L n k : ℕ) : Type :=
  LevelFormIndex L n k ⊕ Fin 3 × Tower.PositiveEdge L n k k
def saddlePointIndexCell : SaddlePointIndex L n k → Tower.Vertex L n k k :=
  Sum.elim levelFormIndexCell fun p => levelVertexCell p.2.1.source
abbrev GhostCoordIndex (L n k : ℕ) : Type :=
  Fin 3 × Tower.Vertex L n k 0 ⊕ Fin 3 × Tower.Vertex L n k k
def ghostCoordIndexCell : GhostCoordIndex L n k → Tower.Vertex L n k k :=
  Sum.elim (fun p => levelVertexCell p.2) fun p => levelVertexCell p.2
abbrev NoiseIndex (L n k : ℕ) : Type := Σ i : Fin k, Tower.PositiveEdge L n k (i + 1)
def noiseIndexCell (p : NoiseIndex L n k) : Tower.Vertex L n k k := levelVertexCell p.2.1.source
structure PauliCoordinates (L n k : ℕ) [Fintype (LevelFormIndex L n k)]
    [Fintype (Fin 3 × Tower.PositiveEdge L n k k)] [Fintype (GhostCoordIndex L n k)]
    [Fintype (Fin 3 × Tower.Vertex L n k 0)] [Fintype (Fin 3 × Tower.Vertex L n k k)] where
  formCoords : LevelForms L n k ≃ₗ[ℝ] (LevelFormIndex L n k → ℝ)
  topFormCoords : Tower.edgeFormSpace L n k k ≃ₗ[ℝ] (Fin 3 × Tower.PositiveEdge L n k k → ℝ)
  ghostCoords : (Tower.vertexFunctionSpace L n k 0 × Tower.vertexFunctionSpace L n k k) ≃ₗ[ℝ]
    (GhostCoordIndex L n k → ℝ)
  formCoords_base : ∀ (ξ : LevelForms L n k) ι,
    Tower.toPauliCoeffs
        (Tower.restrictToPositiveEdges (ξ.1 : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)) ι =
      ((formCoords ξ (.inl ι) : ℝ) : ℂ)
  formCoords_level : ∀ (ξ : LevelForms L n k) (i : Fin k) ι,
    Tower.toPauliCoeffs
        (Tower.restrictToPositiveEdges (ξ.2 i : Tower.Edge L n k (i + 1) → Matrices.ComplexMatrix2)) ι =
      ((formCoords ξ (.inr ⟨i, ι⟩) : ℝ) : ℂ)
  topFormCoords_apply : ∀ (μ : Tower.edgeFormSpace L n k k) ι,
    Tower.toPauliCoeffs
        (Tower.restrictToPositiveEdges (μ : Tower.Edge L n k k → Matrices.ComplexMatrix2)) ι =
      ((topFormCoords μ ι : ℝ) : ℂ)
  ghostCoords_fst : ∀ (g : Tower.vertexFunctionSpace L n k 0 × Tower.vertexFunctionSpace L n k k) ι,
    Tower.toPauliCoeffs (g.1 : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2) ι =
      ((ghostCoords g (.inl ι) : ℝ) : ℂ)
  ghostCoords_snd : ∀ (g : Tower.vertexFunctionSpace L n k 0 × Tower.vertexFunctionSpace L n k k) ι,
    Tower.toPauliCoeffs (g.2 : Tower.Vertex L n k k → Matrices.ComplexMatrix2) ι =
      ((ghostCoords g (.inr ι) : ℝ) : ℂ)
  formCoords_pairing : ∀ ξ ξ' : LevelForms L n k,
    levelPairing (formValues ξ) (formValues ξ') = ∑ ι, formCoords ξ ι * formCoords ξ' ι
  topFormCoords_pairing : ∀ μ μ' : Tower.edgeFormSpace L n k k,
    (Tower.edgeFormPairing (μ : Tower.Edge L n k k → Matrices.ComplexMatrix2)
        (μ' : Tower.Edge L n k k → Matrices.ComplexMatrix2)).re =
      ∑ ι, topFormCoords μ ι * topFormCoords μ' ι
  ghostCoords_pairing : ∀ g g' : Tower.vertexFunctionSpace L n k 0 × Tower.vertexFunctionSpace L n k k,
    (Tower.traceFinsumPairing (g.1 : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2)
        (g'.1 : Tower.Vertex L n k 0 → Matrices.ComplexMatrix2)).re +
      (Tower.traceFinsumPairing (g.2 : Tower.Vertex L n k k → Matrices.ComplexMatrix2)
        (g'.2 : Tower.Vertex L n k k → Matrices.ComplexMatrix2)).re =
      ∑ ι, ghostCoords g ι * ghostCoords g' ι
def complexMatrixOfLinearMap {V V' I T : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup V']
    [Module ℝ V'] [Fintype I] [DecidableEq I] [Fintype T] (Φ : V ≃ₗ[ℝ] (I → ℝ))
    (Φ' : V' ≃ₗ[ℝ] (T → ℝ)) (f : V →ₗ[ℝ] V') : Matrix T I ℂ :=
  (LinearMap.toMatrix' (Φ'.toLinearMap ∘ₗ f ∘ₗ Φ.symm.toLinearMap)).map fun x => (x : ℂ)
section Matrices
variable [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
  [Fintype (Fin 3 × Tower.PositiveEdge L n k k)] [DecidableEq (Fin 3 × Tower.PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
  [Fintype (Fin 3 × Tower.Vertex L n k 0)] [Fintype (Fin 3 × Tower.Vertex L n k k)]
  [Fintype (NoiseIndex L n k)] [DecidableEq (NoiseIndex L n k)]
def gaugeConstraintMatrix (P : PauliCoordinates L n k) (τ : LevelTriple L n k) :
    Matrix (Fin 3 × Tower.PositiveEdge L n k k) (LevelFormIndex L n k) ℂ :=
  complexMatrixOfLinearMap P.formCoords P.topFormCoords
    (shiftedGaugeMap (expMove τ.1 (unitPoint L n k)))
def saddlePointMatrix (P : PauliCoordinates L n k) (a : ℝ) (τ : LevelTriple L n k) :
    Matrix (SaddlePointIndex L n k) (SaddlePointIndex L n k) ℂ :=
  Matrix.fromBlocks
    (complexMatrixOfLinearMap P.formCoords P.formCoords
      (gaugedOperator a (expMove τ.1 (unitPoint L n k)) τ.2.1 τ.2.2))
    (gaugeConstraintMatrix P τ).transpose (gaugeConstraintMatrix P τ) 0
def ghostOperatorMatrix (P : PauliCoordinates L n k) (τ : LevelTriple L n k) :
    Matrix (GhostCoordIndex L n k) (GhostCoordIndex L n k) ℂ :=
  complexMatrixOfLinearMap P.ghostCoords P.ghostCoords
    (ghostBlockOperator (expMove τ.1 (unitPoint L n k)))
def noiseRadiusMatrix (τ : LevelTriple L n k) : Matrix (NoiseIndex L n k) (NoiseIndex L n k) ℂ :=
  Matrix.diagonal fun p =>
    (((meanRadius (levelField (expMove τ.1 (unitPoint L n k)) p.1) p.2.1).re : ℝ) : ℂ)
end Matrices
structure IsLocalAlongCellPair {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → Tower.Vertex L n k k)
    (T : ℝ → ℝ → Matrix ι ι ℂ) (y y' : Tower.Vertex L n k k) (M θ : ℝ) : Prop where
  contDiffAt_entry : ∀ p q, ContDiffAt ℝ 2 (fun w : ℝ × ℝ => T w.1 w.2 p q) 0
  value_local : IsLocalOnCells c c (T 0 0) M θ fun _ => 1
  derivFirst_local : IsLocalOnCells c c (derivFirst T) M θ (cellDecayWeight θ y)
  derivSecond_local : IsLocalOnCells c c (derivSecond T) M θ (cellDecayWeight θ y')
  derivMixed_local : IsLocalOnCells c c (derivMixed T) M θ
    fun u => cellDecayWeight θ y u * cellDecayWeight θ y' u
end RunningCouplingSlope
end YangMills.Construction
end
