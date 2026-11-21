import YangMills.Construction.RunningCouplingSlope.LocalFamiliesOfCells
import YangMills.Construction.Towers.IteratedAveragesOfSmallRegularFields
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
open Tower.CriticalBranchResponse
open Tower.IteratedSmallFieldMeans (HolomorphicInEntries smallFormBall)
open Tower.LeftChartFields (scalarCoords)
variable {L n k : ℕ}
def edgesNearCell (r : ℝ) (y : Vertex L n k k) : Set (Edge L n k 0) :=
  {b | cellDist (fineVertexCell b.source) y ≤ r ∧ cellDist (fineVertexCell b.target) y ≤ r}
structure IsLocalNearCells {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    (c : ι → Vertex L n k k) (c' : ι' → Vertex L n k k)
    (F : (Edge L n k 0 → Matrices.ComplexMatrix2) → Matrix ι' ι ℂ) (ρ C r : ℝ) : Prop where
  holomorphic : ∀ p q, HolomorphicInEntries scalarCoords
    (complexEdgeForms L n k 0 : Set (Edge L n k 0 → Matrices.ComplexMatrix2)) ρ fun v => F v p q
  norm_le : ∀ v ∈ smallFormBall L n k ρ, ‖F v‖ ≤ C
  eq_of_eqOn : ∀ p q, ∀ v ∈ smallFormBall L n k ρ, ∀ v' ∈ smallFormBall L n k ρ,
    EqOn v v' (edgesNearCell r (c' p)) → F v p q = F v' p q
  eq_zero_of_far : ∀ v ∈ smallFormBall L n k ρ, ∀ p q, r < cellDist (c' p) (c q) → F v p q = 0
def twoCellResponseForm (L n k : ℕ) (z : Fin 4 → ℤ) (σ τ : ℂ) :
    Edge L n k 0 → Matrices.ComplexMatrix2 :=
  σ • (periodicResponse L n k (pauliUnitForm L n k 0) : Edge L n k 0 → Matrices.ComplexMatrix2) +
    τ • (periodicResponse L n k (pauliUnitForm L n k z) : Edge L n k 0 → Matrices.ComplexMatrix2)
end YangMills.Construction.RunningCouplingSlope
end
