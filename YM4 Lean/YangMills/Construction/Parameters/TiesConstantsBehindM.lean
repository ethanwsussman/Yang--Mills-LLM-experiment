import YangMills.Construction.Parameters.BoundOfThePotentialsOnARegularBox
import YangMills.Construction.Parameters.OrderOfChoice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ParameterChoice
structure PotentialConstantTie (N : ExternalConstants) : Prop where
  potentialConst_eq : N.potentialConst = PeriodicLattice.potentialBoundConstant
end YangMills.Construction.ParameterChoice
end
