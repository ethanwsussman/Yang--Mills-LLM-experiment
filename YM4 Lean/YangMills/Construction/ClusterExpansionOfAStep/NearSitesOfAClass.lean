import YangMills.Construction.ClusterExpansionOfAStep.CountsOfAClassAtAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusFields TorusLumps
def NearSitesLeLumpsAndLength : Prop :=
  ∀ (ℓ : StepParameters) (n : ℕ) [NeZero n] (r : ℕ) (X : Finset (TorusSite n)) (W : TorusField n), 1 ≤ r →
    (open Classical in
      ballCoverNumber (4 * r) X ≤ ((torusHotLumps ℓ W).filter (· ⊆ X)).card + excessLength ℓ r X W) ∧
    (open Classical in
      (nearSites r X).card ≤ (10 * r) ^ 4 * (((torusHotLumps ℓ W).filter (· ⊆ X)).card + excessLength ℓ r X W))
end YangMills.Construction.ClusterExpansionOfAStep
end
