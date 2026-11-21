import YangMills.Construction.ColdStepAtMirrorFrames.SumsOverCellsAndBonds
import YangMills.Construction.ColdStepAtMirrorFrames.WeightsOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
theorem expWeightSumsBounded_of_blocksCoverLowerLevel (hcov : BlocksCoverLowerLevel) :
    ExpWeightSumsBounded := by
  classical
  intro L s hL hs
  obtain ⟨M, hM0, hM⟩ := CellSums.exists_bound_sum_exp_cellSupDist s hs
  have hc : (0 : ℝ) ≤ 4 * ((centredCube L).card : ℝ) := by positivity
  refine ⟨(4 * ((centredCube L).card : ℝ) + 1) * M, ?_⟩
  intro F n hFL hn hside z
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; exact hn
  have hLF : Odd F.blockSide := hFL ▸ hL
  have hcells := hM F z hs2
  have hle : ∀ a : ℝ, a ≤ M → a ≤ (4 * ((centredCube L).card : ℝ) + 1) * M := fun a ha => by nlinarith
  constructor
  · have hb := CellSums.sum_bonds_le_sum_cells hcov hLF hs2 (fun y => Real.exp (-(s * cellSupDist y z)))
      (fun _ => (Real.exp_pos _).le) (chordBonds (finiteCells F))
    have e : ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(s * blockDist F (bondBlock F b) z)) =
        ∑ b ∈ chordBonds (finiteCells F), Real.exp (-(s * cellSupDist (enclosingCell b.1) z)) :=
      Finset.sum_coe_sort (chordBonds (finiteCells F)) fun b => Real.exp (-(s * cellSupDist (enclosingCell b.1) z))
    rw [e]
    refine hb.trans ?_
    rw [hFL]
    have := mul_le_mul_of_nonneg_left hcells hc
    nlinarith
  · exact hle _ hcells
end ColdStepAtMirrorFrames
end YangMills.Construction
end
