import YangMills.Construction.HoleBesideASecondHole.TheInequalityOfAHoleOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusFrames
open BlockAverages TorusFields TorusLumps
def hotLumpsOfStepStatement : Prop :=
  ∀ (ℓ : StepParameters) (n : ℕ) [NeZero n],
    (∀ W : TorusField (n * ℓ.side),
      torusHotLumps ℓ W = (StepCosts.stepHotLumps ℓ W).image (fun l => l.image (toTorusSite (n * ℓ.side))) ∧
      torusHotSites ℓ W = HoleOnTori.stepLumpSites ℓ (StepCosts.stepHotLumps ℓ W) ∧
      (torusHotLumps ℓ W).card = (StepCosts.stepHotLumps ℓ W).card ∧
      StepCosts.stepHotLumps ℓ W = HoleOnTori.stepHotLumps ℓ (sitesInBlocks ℓ.side Finset.univ) W) ∧
    (ℓ.side ∣ n → ∀ V : TorusField n, torusHotLumps ℓ V = HoleOnTori.topHotLumps ℓ Finset.univ V)
end YangMills.Construction.TorusFrames
end
