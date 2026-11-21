import YangMills.Construction.ClusterExpansionOfAStep.ActionAlongMoves
import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HotLumps
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open YangMills.Construction.LevelAction YangMills.Construction.LumpContours
def OffHotRegionIsRegular : Prop :=
  ∀ (ℓ : StepParameters) (n : ℕ) [NeZero n] (W : TorusField (n * ℓ.side)), ℓ.Admissible →
    IsRegularRegion (Finset.univ \ thickening lumpRange (torusHotSites ℓ W)) 1024
end YangMills.Construction.HotLumps
end
