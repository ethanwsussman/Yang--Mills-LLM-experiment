import YangMills.Construction.Lattice.SignAndGaugeInvarianceOfTheAction
import YangMills.Construction.Lattice.WilsonActionGaugeInvariance
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicLattice
theorem wilsonActionGaugeInvariant_of_nonneg (hsign : ActionNonnegAndGaugeInvariant) :
    WilsonActionGaugeInvariant := by
  intro L m K hL hL13 hm hK U hU u hu
  exact ((hsign L m K hL hL13 hm hK).2 U u hU hu).2
end YangMills.Construction.PeriodicLattice
