import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReferenceDensity
open BlockAverages ColdStepAtMirrorFrames TorusFields
def FamilyAtMinimizerInvariant : Prop :=
  EventuallyOrdered fun T => ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible →
    ∀ (t : ℕ) (f : TorusLumps.LocalDensity),
    TorusLumps.IsAdmissibleDensity ℓ f → TorusLumps.SumInvariantUnderIsometries ℓ f →
      TorusLumps.SumInvariantUnderIsometries ℓ (familyAtMinimizer T.a T.ρA T.L t f)
end YangMills.Construction.ReferenceDensity
end
