import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import YangMills.Construction.LawInAState.DataOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
def covarianceReflectionInvariantStatement : Prop :=
  ∀ (S : ChessboardTori.ChessboardSetup) (Γ : ChessboardTori.ReflectionGrid S) (r : Γ.reflectionGroup)
    (f g : InfiniteLattice.AmbientSpace → ℝ),
    InfiniteLattice.IsBoundedBorelCompactlySupported f → InfiniteLattice.IsBoundedBorelCompactlySupported g →
    unitTorusCovariance S.L S.K S.β (fun x => f (r.1.symm x)) (fun x => g (r.1.symm x)) =
      unitTorusCovariance S.L S.K S.β f g
end YangMills.Construction.StateLaws
end
