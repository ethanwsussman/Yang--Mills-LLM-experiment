import YangMills.Construction.ChessboardTori.StandingConventions
import YangMills.Construction.LawInAState.DataOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.StateLaws
open ChessboardTori
def translationInvarianceStatement : Prop :=
  ∀ (D : ChessboardSetup) (μ : Measure D.GaugeField), IsAdmissibleState D.L D.K D.β μ →
    ∀ v : InfiniteLattice.LatticePoint D.mesh, InfiniteLattice.IsSymmetricUnder μ (InfiniteLattice.shift v)
end YangMills.Construction.StateLaws
end
