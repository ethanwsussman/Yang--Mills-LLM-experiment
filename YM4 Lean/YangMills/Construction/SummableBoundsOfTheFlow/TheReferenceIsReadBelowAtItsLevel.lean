import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepDensities
open BlockAverages ColdStepAtMirrorFrames
def ReferenceBoundsBelow : Prop :=
  ∀ (T : ColdStepAtMirrorFrames.StepParameters) (ℓ : TorusLumps.StepParameters) (Eh : ℕ → ℝ) (t : ℕ),
    T.IsOrdered → T.Compatible ℓ → ℓ.Admissible →
    ReferenceBoundsAtLevel T ℓ Eh t →
    T.IsBoundedFamilyOrderSix (fun j => if j ≤ 3 then T.energyRatio else Eh j) t (T.localReference t)
end YangMills.Construction.StepDensities
end
