import YangMills.Construction.HoleBesideASecondHole.TheInequalityOfAHoleOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusLumps HoleBounds
namespace HoleOnTori
def holeSavingOnToriStatement : Prop :=
  ∀ (ℓ : StepParameters) (cE : ℝ), Odd ℓ.side → 0 ≤ ℓ.coupling → 0 ≤ cE →
    HoleSavingWorkingBounds ℓ.grid ℓ.coupling ℓ.κ ℓ.threshold cE ℓ.baseDepth → HoleSavingBounds ℓ cE
end HoleOnTori
end YangMills.Construction
end
