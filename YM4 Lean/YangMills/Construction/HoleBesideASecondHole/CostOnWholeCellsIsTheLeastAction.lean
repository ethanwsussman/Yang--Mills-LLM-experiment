import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages
def WholeCellCostEqualsMinimalAction : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (S : Finset F.Cell), Odd F.blockSide → 0 ≤ a →
    (∀ j, j ≤ F.top → cutBelow j S = sitesOfCells S j) ∧
    (∀ j, j ≤ F.top → ∀ V : F.GaugeField j, cutEffectiveAction a j (cutBelow j S) V = minimalAction a S j V) ∧
    ∀ (W : F.GaugeField F.depth) (V : F.GaugeField F.top),
      plainBlockEnergy a S W V = blockEnergy a S F.depth W V
end YangMills.Construction.LumpContours
end
