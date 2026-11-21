import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Parameters.OrderOfChoice
import YangMills.Construction.SeparatedSequences.NumbersOfTheConditions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ParameterChoice
structure MatchesCombinedConstants (N : ExternalConstants) : Prop where
  decayBlockFloor_eq : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    N.decayBlockFloor L = SeparatedSequences.CombinedConstants.blockLower L
  decayProductFloor_eq : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    N.decayProductFloor L = SeparatedSequences.CombinedConstants.gapLower L
  decayConst_eq : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    N.decayConst L = SeparatedSequences.CombinedConstants.dirichletDecay L
end YangMills.Construction.ParameterChoice
end
