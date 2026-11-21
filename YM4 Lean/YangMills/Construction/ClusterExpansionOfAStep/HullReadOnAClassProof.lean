import YangMills.Construction.ClusterExpansionOfAStep.HotLumpsOnACut
import YangMills.Construction.ClusterExpansionOfAStep.HullReadOnAClass
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
theorem hullRestrictedToComponent_holds : HullRestrictedToComponent := by
  intro R n _ V Y X z hfit hr hLn hY hX hz
  exact StepSettings.mem_hotNeighbourhoodOn_iff R hfit hLn hr hY.1 hX hz
end YangMills.Construction.ClusterExpansionOfAStep
end
