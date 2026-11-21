import YangMills.Construction.HoleBesideASecondHole.WhatAHoleSavesAtParameters
import YangMills.Construction.HoleBesideASecondHole.WhatAHoleSavesInTheBound
import YangMills.Construction.HoleBesideASecondHole.WhatAHoleSavesOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RenormalizationStepParameters
open BlockAverages HoleBounds HoleOnTori
theorem holeSaving_of_thresholdBounds (hWork : WorkingBoundsFromThresholds)
    (hTori : holeSavingOnToriStatement) : HoleSavingAtFixedParameters := by
  intro T hT
  have ha : 0 ≤ T.coupling := by linarith [hT.a_ge]
  have hσ : T.threshold ≤ T.σA := by linarith [hT.σ_le, hT.σ_pos]
  have hsav : HoleSavingWorkingBounds T.grid T.coupling T.κ T.threshold T.cE T.baseDepth := by
    refine hWork T.grid T.coupling T.κ T.threshold T.cE T.cE T.cE T.baseDepth hT.L_odd ha hT.κ_pos hT.σ_pos
      hT.cE_pos.le le_rfl le_rfl ?_ hT.hole_one hT.hole_more
    intro F S V hFL hamb hreg hcold
    obtain ⟨-, -, -, -, -, -, -, -, hc⟩ := hT.chain
    exact ⟨T.ρA, T.N 0, (hc F 2047 S hFL hamb (by norm_num) hreg T.threshold V hT.σ_pos hσ hcold).1⟩
  exact ⟨hsav, fun y => hTori (T.stepParameters y) T.cE hT.L_odd ha hT.cE_pos.le hsav⟩
end YangMills.Construction.RenormalizationStepParameters
end
