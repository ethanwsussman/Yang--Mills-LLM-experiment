import YangMills.Construction.ClusterExpansionOfAStep.GeometryOfFreeBonds
import YangMills.Construction.ClusterExpansionOfAStep.RegionOffTheHotLumpsIsRegular
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HotLumps
open BlockAverages LumpContours TopLevelSites TorusFields TorusLumps StepCosts LevelAction
theorem isRegularRegion_of_torusFrame (L m : ℕ) [NeZero m] {X : Finset (TorusSite m)}
    (h : IsOrthantRegular (cellsOfSites (torusFrame L 0 m) X) 2047) : IsRegularRegion X 1024 := by apply _root_.YangMills.Construction.FreeBonds.isRegularRegion_of_torusFrame <;> assumption
theorem offHotRegionIsRegular_holds (hc : ComplementOfThickenedLumpsRegular) :
    OffHotRegionIsRegular := fun ℓ n _ W hfit =>
  isRegularRegion_of_torusFrame ℓ.side _
    (isOrthantRegular_cellsOfSites_compl_thickening hc hfit (Dvd.intro_left n rfl) (fun _ => rfl) W)
end YangMills.Construction.HotLumps
end
