import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses
open SingleSequence
def PropagatorConstantsServeOnTori : Prop :=
  ∀ L : ℕ, Blocking.DimFourOddBlockingFactorGeThirteen 4 L →
    ∀ c : Propagator.PropagatorConstants, c.ValidFor L → (L : ℝ) ≤ c.blockLower →
      (torusGreenConstants c).Valid L
end YangMills.Construction.SeparatedClasses
end
