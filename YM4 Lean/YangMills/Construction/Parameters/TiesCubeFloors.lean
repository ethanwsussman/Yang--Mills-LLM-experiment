import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Parameters.FloorOnTheConstantOfTheCores
import YangMills.Construction.Parameters.OrderOfChoice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ParameterChoice
structure CoreLowerBoundTie (T : DerivedConstants) (N : ExternalConstants) : Prop where
  coreGaugeLowerBound_le : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    coreGaugeLowerBound L (T.B₃ L) ≤ N.theoremBFloor L T.flowConstB
end YangMills.Construction.ParameterChoice
end
