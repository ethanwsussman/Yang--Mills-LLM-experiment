import YangMills.Construction.SeparatedSequences.ExtensionKernelAtTopsAndExpansionsProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators
noncomputable section
namespace YangMills.Construction.SeparatedClasses
namespace InverseKernelAtAnchors
open SingleSequence SingleSequence.SequenceData
section Transport
variable (s : SequenceData)
theorem levelTorusSide_ne_zero : s.levelUnitData.torusSide ≠ 0 := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeOneFormsProof.TorusComponents.gaugeSide_ne_zero <;> assumption
theorem toTorus_injective : Function.Injective (s.toTorus s.levelUnitData.torusSide) := by
  intro x y hxy
  unfold SequenceData.toTorus at hxy
  rw [dif_pos (levelTorusSide_ne_zero s), dif_pos (levelTorusSide_ne_zero s)] at hxy
  funext μ
  exact (AddCircle.equivAddCircle _ _ _ _).injective (congrFun hxy μ)
end Transport
theorem scaledDist_nonneg {D : GeneralTorus.ScaleData} (B : GeneralTorus.SeparatedChain D)
    (x x' : D.Space) : 0 ≤ B.scaledDist x x' := by apply _root_.YangMills.Construction.SeparatedClasses.ExtensionKernel.scaledDist_nonneg <;> assumption
end InverseKernelAtAnchors
end YangMills.Construction.SeparatedClasses
end
