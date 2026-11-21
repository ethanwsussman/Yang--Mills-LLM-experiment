import YangMills.Construction.SeparatedSequences.ClassExpansionsOnAGeneralTorusProof
import YangMills.Construction.SeparatedSequences.ClassProjectionOnAGeneralTorusProof
import YangMills.Construction.SeparatedSequences.ChosenConstantsOfTheConditions
import YangMills.Construction.SeparatedSequences.OneSequenceOneSetOfObjects
import YangMills.Construction.Torus.BoundsOnTheExtensionOperator
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
noncomputable section
namespace SeparatedClasses.ExtensionKernel
open SingleSequence SingleSequence.SequenceData
section EvaluationMaps
variable (s : SequenceData)
theorem L_ne_zero : (s.data.L : ℝ) ≠ 0 := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeProjectionOfClass.blockFactor_cast_ne_zero <;> assumption
theorem levelUnitSide_eq : s.levelUnitData.torusSide =
    PeriodicLattice.torusSide s.data.L s.data.m * (s.data.L : ℝ) ^ (s.data.cutoff - s.data.t) := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeProjectionOfClass.torusSide_levelUnits_eq <;> assumption
theorem levelUnitSide_ne_zero : s.levelUnitData.torusSide ≠ 0 := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeOneFormsProof.TorusComponents.gaugeSide_ne_zero <;> assumption
theorem meshSize_mul_ratio :
    PeriodicLattice.meshSize s.data.L (PeriodicLattice.levelDepth s.data.cutoff 0) *
      ((PeriodicLattice.torusSide s.data.L s.data.m)⁻¹ * s.levelUnitData.torusSide) =
        s.levelUnitData.levelSpacing 0 := by
  have hL := L_ne_zero s
  rw [levelUnitSide_eq, ← mul_assoc (PeriodicLattice.torusSide s.data.L s.data.m)⁻¹,
    inv_mul_cancel₀ s.torusSide_ne_zero, one_mul]
  show (s.data.L : ℝ) ^ (-(((s.data.cutoff : ℕ) : ℤ) - ((0 : ℕ) : ℤ))) *
      (s.data.L : ℝ) ^ (s.data.cutoff - s.data.t) =
    (s.data.L : ℝ) ^ 0 * (s.data.L : ℝ) ^ (-(s.data.t : ℤ))
  rw [← zpow_natCast (s.data.L : ℝ) (s.data.cutoff - s.data.t), ← zpow_natCast (s.data.L : ℝ) 0,
    ← zpow_add₀ hL, ← zpow_add₀ hL]
  congr 1
  push_cast [Nat.cast_sub s.data.t_le_cutoff]
  ring
theorem levelSpacing_zero : s.levelUnitData.levelSpacing 0 = s.data.finestMesh := by apply _root_.YangMills.Construction.SeparatedClasses.GaugeOneFormsProof.TorusComponents.levelSpacing_zero <;> assumption
theorem toTorus_eq (x : s.data.Point) :
    s.toTorus s.levelUnitData.torusSide x = s.data.levelUnitTorus.levelEquiv x := by
  unfold SequenceData.toTorus
  rw [dif_pos (levelUnitSide_ne_zero s)]
  rfl
theorem bondFrom_src_posBondDir (b : s.levelUnitData.BaseBond) :
    GeneralTorus.ScaleData.bondFrom b.1.src (GeneralTorus.ScaleData.posBondDir b) = b := by
  have h : b.1.tgt - b.1.src = GeneralTorus.unitStep s.levelUnitData.torusSide
      (s.levelUnitData.levelSpacing 0) (GeneralTorus.ScaleData.posBondDir b) := b.2.choose_spec
  refine Subtype.ext (GeneralTorus.LatticeBond.ext rfl ?_)
  show b.1.src + GeneralTorus.unitStep s.levelUnitData.torusSide (s.levelUnitData.levelSpacing 0) _ =
    b.1.tgt
  rw [← h, add_sub_cancel]
end EvaluationMaps
theorem scaledDist_nonneg {D : GeneralTorus.ScaleData} (B : GeneralTorus.SeparatedChain D)
    (x x' : D.Space) : 0 ≤ B.scaledDist x x' := by
  apply Real.sInf_nonneg
  rintro r ⟨Γ, -, -, -, rfl⟩
  have hsp : ∀ n, 0 ≤ (D.levelSpacing n)⁻¹ := fun n => by
    have := D.baseSpacing_pos
    unfold GeneralTorus.ScaleData.levelSpacing
    positivity
  have hlen : ∀ A : Set D.Space, 0 ≤ TorusMetric.pathLengthIn D.torusSide Γ A := fun A => by
    unfold TorusMetric.pathLengthIn
    apply List.sum_nonneg
    intro x hx
    obtain ⟨g, -, rfl⟩ := List.mem_map.mp hx
    refine mul_nonneg ?_ ENNReal.toReal_nonneg
    unfold TorusMetric.l1NormVec
    positivity
  unfold GeneralTorus.SeparatedChain.scaledLength
  exact add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (hsp n) (hlen _))
    (mul_nonneg (hsp 0) (hlen _))
end SeparatedClasses.ExtensionKernel
end
end YangMills.Construction
