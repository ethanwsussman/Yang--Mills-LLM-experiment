import YangMills.Construction.ChessboardTori.StandingConventions
import YangMills.Construction.LawInAState.DataOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
def unitTorusMeasureSymmetricStatement : Prop :=
  ∀ S : ChessboardTori.ChessboardSetup, IsProbabilityMeasure (unitTorusMeasure S.L S.K S.β) ∧
    ∀ g : InfiniteLattice.LatticeSymmetry S.mesh, InfiniteLattice.IsSymmetricUnder (unitTorusMeasure S.L S.K S.β) g
end YangMills.Construction.StateLaws
end
