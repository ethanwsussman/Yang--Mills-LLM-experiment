import YangMills.Construction.ClusterExpansionOfAStep.FrameOnASmallTorus
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TopLevelSites TorusFields TorusLumps StepMarks StepCosts
namespace TorusLumps
theorem frameCoordOnSmallTorus_holds : FrameCoordOnSmallTorus := by
  intro ℓ ρA t m n _ V b hbig
  have hn : ∀ i, (torusFrame ℓ.side t n).extent i = n := fun _ => rfl
  unfold frameCoord bondFrameCoord minimizerCoord
  rw [if_neg (fun h => hbig (h 0)), cellsOfSites_univ hn]
end TorusLumps
end YangMills.Construction
end
