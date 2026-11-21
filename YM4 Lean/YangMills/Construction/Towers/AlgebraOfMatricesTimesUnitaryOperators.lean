import YangMills.Construction.Towers.TheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tower.UnitLatticeL2 Tower.UnitaryCombinations OneLoopNotation
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (torusAverage castVec)
namespace Tower
open MagneticWeyl in
def MatMulUnitaryOpAlgebra : Prop :=
  ∀ (L N' N'' : ℕ) [NeZero N'] [NeZero N''] (V : ScalarL2 L →ₗ[ℂ] ScalarL2 L),
    IsUnitaryOp V →
    (∀ (s : ℂ) (X Y : Matrix (Fin N') (Fin N'') ℂ),
      matMulUnitaryOp (s • X + Y) V =
        s • matMulUnitaryOp X V + matMulUnitaryOp Y V) ∧
    (∀ (N''' : ℕ) [NeZero N'''] (V' : ScalarL2 L →ₗ[ℂ] ScalarL2 L),
      IsUnitaryOp V' →
      ∀ (X : Matrix (Fin N') (Fin N'') ℂ) (Y : Matrix (Fin N'') (Fin N''') ℂ),
        (matMulUnitaryOp X V).comp (matMulUnitaryOp Y V') =
          matMulUnitaryOp (X * Y) (V ∘ₗ V')) ∧
    (∀ V' : ScalarL2 L →ₗ[ℂ] ScalarL2 L, IsUnitaryOp V' →
      (∀ ψ χ : ScalarL2 L, inner ℂ (V' ψ) χ = inner ℂ ψ (V χ)) →
      ∀ X : Matrix (Fin N') (Fin N'') ℂ,
        opAdjoint (matMulUnitaryOp X V) =
          matMulUnitaryOp X.conjTranspose V') ∧
    ∀ X : Matrix (Fin N') (Fin N'') ℂ,
      matrixAtZero (matMulUnitaryOp X V) =
        (V (vectorAtZero L (EuclideanSpace.single 0 (1 : ℂ))) 0 0) • X
end Tower
end YangMills.Construction
end
