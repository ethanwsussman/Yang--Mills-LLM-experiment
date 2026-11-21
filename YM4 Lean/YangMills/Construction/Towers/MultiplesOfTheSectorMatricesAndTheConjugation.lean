import YangMills.Construction.Towers.LogarithmsSectorsAndDensityDefs
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open OperatorCalculus OneLoopNotation Tower.UnitLatticeL2
namespace Tower.AbelianFieldDensity
namespace SectorDecomposition
def conjVec {L N' : ℕ} (v : VectorL2 L N') : VectorL2 L N' :=
  Classical.epsilon fun w : VectorL2 L N' => ∀ x i, w x i = conj (v x i)
structure StarInvolutionFacts (σ : Type) : Prop where
  ofCoords_eq_fieldStar : ∀ f : L2Field σ,
    ofCoords (pointwiseStar f) = fieldStar (ofCoords f)
  isConjLinear : IsConjLinear (fun f : L2Field σ => pointwiseStar f)
  norm_eq : ∀ f : L2Field σ, ‖pointwiseStar f‖ = ‖f‖
  involutive : ∀ f : L2Field σ, pointwiseStar (pointwiseStar f) = f
  apply_eq_conj : ∀ (f : L2Field σ) (ι : Fin 3 × σ), pointwiseStar f ι = conj (f ι)
  basisVec_fixed : ∀ ι : Fin 3 × σ, pointwiseStar (basisVec ι) = basisVec ι
structure WeightMultipleFacts {L N' : ℕ} {σ : Type}
    (multiple : VectorL2 L N' → Matrices.ComplexMatrix2 → L2Field σ) : Prop where
  conjVec_apply : ∀ (v : VectorL2 L N') (x : FullSpace.Vertex L 0 0) (i : Fin N'),
    conjVec v x i = conj (v x i)
  map_add : ∀ t : Matrices.ComplexMatrix2, IsWeightMatrix t → ∀ v v' : VectorL2 L N',
    multiple (v + v') t = multiple v t + multiple v' t
  map_smul : ∀ t : Matrices.ComplexMatrix2, IsWeightMatrix t → ∀ (s : ℂ) (v : VectorL2 L N'),
    multiple (s • v) t = s • multiple v t
  inner_third : ∀ v v' : VectorL2 L N',
    inner ℂ (multiple v (Matrices.ComplexMatrix2.pauliFamily 2))
      (multiple v' (Matrices.ComplexMatrix2.pauliFamily 2)) = inner ℂ v v'
  inner_raising : ∀ v v' : VectorL2 L N',
    inner ℂ (multiple v raisingPauli) (multiple v' raisingPauli) = (1 / 2 : ℂ) * inner ℂ v v'
  inner_lowering : ∀ v v' : VectorL2 L N',
    inner ℂ (multiple v loweringPauli) (multiple v' loweringPauli) = (1 / 2 : ℂ) * inner ℂ v v'
  neutral_iff : ∀ f : L2Field σ,
    IsNeutral (ofCoords f) ↔ ∃ v, f = multiple v (Matrices.ComplexMatrix2.pauliFamily 2)
  positive_iff : ∀ f : L2Field σ,
    IsPositivelyCharged (ofCoords f) ↔ ∃ v, f = multiple v raisingPauli
  negative_iff : ∀ f : L2Field σ,
    IsNegativelyCharged (ofCoords f) ↔ ∃ v, f = multiple v loweringPauli
  star_raising : ∀ v : VectorL2 L N',
    pointwiseStar (multiple v raisingPauli) = multiple (conjVec v) loweringPauli
  star_lowering : ∀ v : VectorL2 L N',
    pointwiseStar (multiple v loweringPauli) = multiple (conjVec v) raisingPauli
end SectorDecomposition
open SectorDecomposition in
def WeightMultiplesAndStar : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ b : PeriodicOperators.PosEdge L 0 0,
      ∃! p : FullSpace.Vertex L 0 0 × Fin 4, FullSpace.forwardEdge p.1 p.2 = b) ∧
    (∀ t : Matrices.ComplexMatrix2, IsWeightMatrix t → t ∈ Matrices.ComplexMatrix2.traceless) ∧
    (∀ X ∈ Matrices.ComplexMatrix2.traceless, ∀ v : VectorL2 L 1, ∀ x : FullSpace.Vertex L 0 0,
      ofCoords (vertexTensor v X) x = v x 0 • X) ∧
    (∀ X ∈ Matrices.ComplexMatrix2.traceless, ∀ (v : VectorL2 L 4) (x : FullSpace.Vertex L 0 0)
      (μ : Fin 4), ofCoords (edgeTensor v X) (FullSpace.forwardEdge x μ) = v x μ • X) ∧
    StarInvolutionFacts (FullSpace.Vertex L 0 0) ∧
    StarInvolutionFacts (PeriodicOperators.PosEdge L 0 0) ∧
    WeightMultipleFacts (fun (v : VectorL2 L 1) (X : Matrices.ComplexMatrix2) => vertexTensor v X) ∧
    WeightMultipleFacts (fun (v : VectorL2 L 4) (X : Matrices.ComplexMatrix2) => edgeTensor v X)
end Tower.AbelianFieldDensity
end YangMills.Construction
end
