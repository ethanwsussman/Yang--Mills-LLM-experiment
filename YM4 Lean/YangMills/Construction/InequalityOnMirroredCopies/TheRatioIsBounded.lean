import YangMills.Construction.FreeEnergiesOfTheFlow.FreeEnergyDefs
import YangMills.Construction.InequalityOnMirroredCopies.FromSixteenCopiesToTheInequality
import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityAtEveryDatum
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
def TorusRatioBoundedStatement : Prop :=
  FreeEnergies.HoldsForAdmissibleParameters fun T y => ∀ Ξ : ℝ, ∃ b₁ : ℝ, 0 ≤ b₁ ∧
    ∀ D : ChessboardTori.ChessboardSetup, IsAdmissibleSetup (T.stepParameters y) Ξ D → TorusRatioBound D b₁
end YangMills.Construction.ReflectedCopies
end
