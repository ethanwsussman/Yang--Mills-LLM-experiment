import YangMills.Construction.LawByMomentsOfTheFlow.TestFunctionsOnTheSpace
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace CyclicFormula
open TestFunctions
abbrev OrderedDirectionPair : Type := {p : Fin 4 × Fin 4 // p.1 < p.2}
def inversionMatrix (x : EuclideanFourSpace) : Matrix (Fin 4) (Fin 4) ℝ :=
  1 - (2 / ‖x‖ ^ 2) • Matrix.vecMulVec (fun a => x a) (fun a => x a)
def exteriorSquareMap (A : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix OrderedDirectionPair OrderedDirectionPair ℝ := fun p q =>
  A p.1.1 q.1.1 * A p.1.2 q.1.2 - A p.1.1 q.1.2 * A p.1.2 q.1.1
def exteriorSquareTrace (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  Matrix.trace (exteriorSquareMap A)
variable {n : ℕ} [NeZero n]
def cycleKernel (σ : Equiv.Perm (Fin n)) (x : Fin n → EuclideanFourSpace) : ℝ :=
  (∏ c : Fin n, (Real.pi ^ 2 * ‖x (σ c) - x (σ (c + 1))‖ ^ 4)⁻¹) *
    exteriorSquareTrace (List.ofFn fun c : Fin n => inversionMatrix (x (σ c) - x (σ (c + 1)))).prod
def unorientedCyclicOrders (n : ℕ) [NeZero n] : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ => σ 0 = 0 ∧ σ 1 ≤ σ (-1)
def cyclicMomentFormula (n : ℕ) [NeZero n] (φ : Fin n → EuclideanFourSpace → ℝ) : ℝ :=
  3 * (if n = 2 then 1 / 2 else 1) *
    ∑ σ ∈ unorientedCyclicOrders n, ∫ x : Fin n → EuclideanFourSpace, (∏ i, φ i (x i)) * cycleKernel σ x
end CyclicFormula
end YangMills.Construction
end
