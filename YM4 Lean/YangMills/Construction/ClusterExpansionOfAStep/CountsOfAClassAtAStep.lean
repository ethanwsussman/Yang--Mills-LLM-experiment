import YangMills.Construction.ClusterExpansionOfAStep.LengthOfAnImageUnion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.TorusFields
variable {n : ℕ}
open Classical in
def nearSites [NeZero n] (r : ℕ) (X : Finset (TorusSite n)) : Finset (TorusSite n) :=
  Finset.univ.filter fun y => ∃ z ∈ X, (supDist y z : ℝ) < (r : ℝ) / 4
section Attached
variable [NeZero n] (ℓ : StepParameters) (r : ℕ) (W : TorusField (n * ℓ.side))
  (bad : Finset (TorusBond (n * ℓ.side))) (Yt : Finset (TorusSite (n * ℓ.side))) (C X : Finset (TorusSite n))
abbrev attachedPart : Finset (TorusSite (n * ℓ.side)) := attachedInBlocks ℓ.side r bad Yt C X
open Classical in
def hotLumpsInAttached : ℕ := ((torusHotLumps ℓ W).filter (· ⊆ attachedPart ℓ r bad Yt C X)).card
def lengthInAttached : ℕ :=
  excessLength ℓ r (componentsWithin ℓ.side r Yt (attachedPart ℓ r bad Yt C X)) W
def badBlocksInAttached : ℕ := (badBlocksOff ℓ.side bad C (attachedPart ℓ r bad Yt C X)).card
end Attached
end YangMills.Construction.TorusLumps
end
