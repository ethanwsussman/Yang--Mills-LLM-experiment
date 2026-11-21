import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityOfACell
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
def TorusRatioBound (D : ChessboardSetup) (b₁ : ℝ) : Prop :=
  ∀ g : ReflectionGrid D, g.HasAdmissibleSide → ∀ j : ℕ,
    torusPartitionRatio g j ≤ Real.exp (b₁ * g.cellSide ^ 4 +
      b₁ * TorusBound.logPos (1 / g.cellSide) ^ (1 / 20 : ℝ))
def SixteenCopiesImpliesInequality : Prop :=
  ∀ (D : ChessboardSetup) (A₀ b₀ b₁ : ℝ), 0 ≤ A₀ → 0 ≤ b₀ → 0 ≤ b₁ →
    SixteenCopyBound D A₀ b₀ → TorusRatioBound D b₁ → CopyInequality D A₀ (b₀ + b₁)
end YangMills.Construction.ReflectedCopies
end
