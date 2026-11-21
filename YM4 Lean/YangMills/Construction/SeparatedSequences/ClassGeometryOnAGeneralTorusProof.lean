import YangMills.Construction.SeparatedSequences.ClassExpansionsOnAGeneralTorusProof
import YangMills.Construction.SeparatedSequences.ClassGeometryOnAGeneralTorus
import YangMills.Construction.Torus.PhysicalTorusInLevelUnitsAsATorusOfGeneralSide
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeparatedClasses.GaugeGeometryProof
open SingleSequence SingleSequence.SequenceData
def levelUnitDataOf (s : SequenceData) (e : ℕ) : GeneralTorus.LevelUnitParams :=
  ⟨s.data.L, s.blockingFactor, s.data.m, s.data.m.pos, s.data.K, s.data.K.pos, s.data.t,
    s.data.t_le_cutoff, e, s.data.gapExp⟩
theorem toTorus_eq (s : SequenceData) (e : ℕ) :
    s.toTorus s.levelUnitData.torusSide = (levelUnitDataOf s e).readPoint := by
  funext x
  have hside : s.levelUnitData.torusSide ≠ 0 := (levelUnitDataOf s e).torusSide_ne_zero
  simp only [SequenceData.toTorus]
  rw [dif_pos hside]
  rfl
end YangMills.Construction.SeparatedClasses.GaugeGeometryProof
