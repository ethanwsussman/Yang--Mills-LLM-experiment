import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower PeriodicOperators Matrices
open Tower.CriticalBranchResponse
variable {L n k : ℕ}
def cellDist (y y' : Vertex L n k k) : ℝ :=
  TorusMetric.torusEuclidNorm
    ((y : PeriodicLattice.FourTorus L n) - (y' : PeriodicLattice.FourTorus L n))
def blockBetween {Y ι ι' : Type} (c : ι → Y) (c' : ι' → Y) (T : Matrix ι' ι ℂ) (y' y : Y) :
    Matrix ι' ι ℂ :=
  open Classical in
  fun p q => if c' p = y' ∧ c q = y then T p q else 0
def IsLocalOnCells {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] (c : ι → Vertex L n k k)
    (c' : ι' → Vertex L n k k) (T : Matrix ι' ι ℂ) (M θ : ℝ) (m : Vertex L n k k → ℝ) : Prop :=
  ∀ y' y, ‖blockBetween c c' T y' y‖ ≤ M * Real.exp (-(θ * cellDist y' y)) * m y'
def cellDecayWeight (θ : ℝ) (y₀ y : Vertex L n k k) : ℝ := Real.exp (-(θ * cellDist y y₀))
def edgeCell (p : Fin 3 × PositiveEdge L n k k) : Vertex L n k k := p.2.1.source
def vertexCell (p : Fin 3 × Vertex L n k k) : Vertex L n k k := p.2
def doubledEdgeCell (p : Fin 3 × PositiveEdge L n k k ⊕ Fin 3 × PositiveEdge L n k k) :
    Vertex L n k k :=
  Sum.elim edgeCell edgeCell p
def cellOfCoords (L n k : ℕ) (w : Fin 4 → ℤ) : Vertex L n k k := PeriodicLattice.offsetSite 0 w
def twoSourceBackground (L n k : ℕ) (w : Fin 4 → ℤ) (s t : ℝ) : Edge L n k 0 → ComplexMatrix2 :=
  PeriodicLattice.expTwist
    (((s : ℂ) • (meshScaledResponse L n k (pauliUnitForm L n k 0) : Edge L n k 0 → ComplexMatrix2)) +
      ((t : ℂ) • (meshScaledResponse L n k (pauliUnitForm L n k w) : Edge L n k 0 → ComplexMatrix2)))
    (fun _ => 1)
def derivFirst {ι ι' : Type} (T : ℝ → ℝ → Matrix ι' ι ℂ) : Matrix ι' ι ℂ :=
  fun p q => deriv (fun s => T s 0 p q) 0
def derivSecond {ι ι' : Type} (T : ℝ → ℝ → Matrix ι' ι ℂ) : Matrix ι' ι ℂ :=
  fun p q => deriv (fun t => T 0 t p q) 0
def derivMixed {ι ι' : Type} (T : ℝ → ℝ → Matrix ι' ι ℂ) : Matrix ι' ι ℂ :=
  fun p q => deriv (fun s => deriv (fun t => T s t p q) 0) 0
structure IsLocalFamily {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → Vertex L n k k)
    (T : ℝ → ℝ → Matrix ι ι ℂ) (w : Fin 4 → ℤ) (M θ : ℝ) : Prop where
  contDiffAt : ∀ p q, ContDiffAt ℝ 2 (fun x : ℝ × ℝ => T x.1 x.2 p q) 0
  isUnit_det : IsUnit (Matrix.det (T 0 0))
  inv_local : IsLocalOnCells c c (T 0 0)⁻¹ M θ fun _ => 1
  derivFirst_local : IsLocalOnCells c c (derivFirst T) M θ (cellDecayWeight θ (cellOfCoords L n k 0))
  derivSecond_local : IsLocalOnCells c c (derivSecond T) M θ (cellDecayWeight θ (cellOfCoords L n k w))
  derivMixed_local : IsLocalOnCells c c (derivMixed T) M θ
    fun y => cellDecayWeight θ (cellOfCoords L n k 0) y * cellDecayWeight θ (cellOfCoords L n k w) y
end RunningCouplingSlope
end YangMills.Construction
end
