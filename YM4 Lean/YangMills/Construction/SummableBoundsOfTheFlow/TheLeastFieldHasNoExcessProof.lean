import YangMills.Construction.ColdStepAtMirrorFrames.SumOfTheShares
import YangMills.Construction.SummableBoundsOfTheFlow.TheLeastFieldHasNoExcess
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
noncomputable section
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
theorem minimizerExcessSumZero_holds (hshare : sumCellSharesEqAction) :
    minimizerExcessSumZero := by
  intro F a ρA x m V ha hodd hs hex
  have hspec : IsMinimizingChart a (finiteCells F) V ρA (minimizingCoordinates a (finiteCells F) V ρA) := by
    unfold minimizingCoordinates
    rw [dif_pos hex]
    exact hex.choose_spec
  have hmin := hspec.2.2
  set w := minimizingCoordinates a (finiteCells F) V ρA with hw
  have hE : chartedEnergy a w V = minimalAction a (finiteCells F) F.top V := by
    have hbdd : BddBelow (Set.range fun W : F.GaugeField F.depth => blockEnergy a (finiteCells F) F.depth W V) :=
      ⟨blockEnergy a (finiteCells F) F.depth (chartedField w V) V, by
        rintro _ ⟨W, rfl⟩
        exact hmin W⟩
    refine le_antisymm ?_ ?_
    · show blockEnergy a (finiteCells F) F.depth (chartedField w V) V ≤
        ⨅ W : F.GaugeField F.depth, blockEnergy a (finiteCells F) F.depth W V
      have : Nonempty (F.GaugeField F.depth) := ⟨fun _ _ => 1⟩
      exact le_ciInf hmin
    · show (⨅ W : F.GaugeField F.depth, blockEnergy a (finiteCells F) F.depth W V) ≤
        blockEnergy a (finiteCells F) F.depth (chartedField w V) V
      exact ciInf_le hbdd _
  obtain ⟨hA, hB⟩ := hshare F a (fun z i => stepFrame true a ρA m (z, i) V) V ha hodd hs
  have hfr : (fun z i => stepFrame true a ρA m (z, i) V) = w := by
    funext z i
    simp [stepFrame, minimizingBondCoordinate, hw]
  unfold frameDensity
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hA, hB, hfr, hE]
  simp
end Interpolation
end
end YangMills.Construction
