import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ReferenceDensity
def localReferenceBoundedFamily : Prop :=
  EventuallyOrdered fun T => T.AdmitsReference → ∃ e : ℕ → ℝ, ∀ t, T.IsBoundedFamilyOrderSix e t (T.localReference t)
end ReferenceDensity
end YangMills.Construction
end
