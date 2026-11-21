import YangMills.Construction.Matrices.NormAndTraceOfAComplexMatrix
import YangMills.Construction.Towers.SquareSummableFunctionsOnTheUnitLattice
import Mathlib
set_option autoImplicit false
open Filter YangMills.Construction.OneLoopNotation YangMills.Construction.Tower.UnitLatticeL2
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace UnitaryCombinations
abbrev ScalarL2 (L : ℕ) : Type := VectorL2 L 1
def IsUnitaryOp {L : ℕ} (U : ScalarL2 L →ₗ[ℂ] ScalarL2 L) : Prop :=
  Function.Bijective U ∧ ∀ f, ‖U f‖ = ‖f‖
variable {L p q : ℕ}
theorem memℓp_coord (f : VectorL2 L q) (c : Fin q) :
    Memℓp (fun y => (EuclideanSpace.single 0 (f y c) : EuclideanSpace ℂ (Fin 1))) 2 := by
  have hf := lp.memℓp f
  rw [memℓp_gen_iff (by norm_num)] at hf ⊢
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun y => ?_) hf
  rw [EuclideanSpace.norm_single]
  exact Real.rpow_le_rpow (norm_nonneg _) (PiLp.norm_apply_le (f y) c) (by norm_num)
def coord (f : VectorL2 L q) (c : Fin q) : ScalarL2 L :=
  ⟨fun y => EuclideanSpace.single 0 (f y c), memℓp_coord f c⟩
def applyCoordwise (U : ScalarL2 L →ₗ[ℂ] ScalarL2 L) (f : VectorL2 L q)
    (y : FullSpace.Vertex L 0 0) : EuclideanSpace ℂ (Fin q) :=
  WithLp.toLp 2 fun c => U (coord f c) y 0
def matMulUnitary (A : Matrix (Fin p) (Fin q) ℂ)
    (U : ScalarL2 L →ₗ[ℂ] ScalarL2 L) (f : VectorL2 L q)
    (y : FullSpace.Vertex L 0 0) : EuclideanSpace ℂ (Fin p) :=
  Matrix.toEuclideanLin A (applyCoordwise U f y)
def matMulUnitaryOp (A : Matrix (Fin p) (Fin q) ℂ)
    (U : ScalarL2 L →ₗ[ℂ] ScalarL2 L) :
    BddOpBetween (VectorL2 L q) (VectorL2 L p) :=
  Classical.epsilon fun T => ∀ f y, T f y = matMulUnitary A U f y
def TendstoUnconditionally {I E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (Y : I → BddOpBetween E F)
    (S : BddOpBetween E F) : Prop :=
  ∀ σ : ℕ+ ≃ I, TendstoInOpNorm atTop (fun n : ℕ+ => ∑ k ∈ Finset.Icc 1 n, Y (σ k)) S
def tsumOp (A : (Fin 4 → ℤ) → Matrix (Fin p) (Fin q) ℂ)
    (U : (Fin 4 → ℤ) → ScalarL2 L →ₗ[ℂ] ScalarL2 L) :
    BddOpBetween (VectorL2 L q) (VectorL2 L p) :=
  Classical.epsilon fun S =>
    TendstoUnconditionally (fun n => matMulUnitaryOp (A n) (U n)) S
def MatMulUnitaryBounded (L p q : ℕ) [NeZero p] [NeZero q] : Prop :=
  ∀ (A : Matrix (Fin p) (Fin q) ℂ) (U : ScalarL2 L →ₗ[ℂ] ScalarL2 L),
    IsUnitaryOp U →
    (∀ f y, matMulUnitaryOp A U f y = matMulUnitary A U f y) ∧
      opNormOf (matMulUnitaryOp A U) ≤ Matrices.RectangularMatrix.opNormValue A
def SeriesConvergesUnconditionally (L p q : ℕ) [NeZero p] [NeZero q] : Prop :=
  ∀ (A : (Fin 4 → ℤ) → Matrix (Fin p) (Fin q) ℂ)
    (U : (Fin 4 → ℤ) → ScalarL2 L →ₗ[ℂ] ScalarL2 L),
    Summable (fun n => Matrices.RectangularMatrix.opNormValue (A n)) → (∀ n, IsUnitaryOp (U n)) →
    TendstoUnconditionally (fun n => matMulUnitaryOp (A n) (U n)) (tsumOp A U) ∧
      opNormOf (tsumOp A U) ≤ ∑' n, Matrices.RectangularMatrix.opNormValue (A n)
end UnitaryCombinations
open UnitaryCombinations in
def UnitaryOperatorSeriesClaim : Prop :=
  ∀ (L p q : ℕ) [NeZero p] [NeZero q],
    MatMulUnitaryBounded L p q ∧ SeriesConvergesUnconditionally L p q
end Tower
end YangMills.Construction
end
