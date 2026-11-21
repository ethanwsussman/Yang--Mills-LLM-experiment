import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensities
open RenormalizationStepParameters
def AssignmentConstraints.combine (A B : AssignmentConstraints) : AssignmentConstraints where
  property S := A.property S ∧ B.property S
  sideFloor a := max (A.sideFloor a) (B.sideFloor a)
  derivBoundFloor a := max (A.derivBoundFloor a) (B.derivBoundFloor a)
  rateCeiling D := min (A.rateCeiling D) (B.rateCeiling D)
  thresholdCeiling D r := min (A.thresholdCeiling D r) (B.thresholdCeiling D r)
  n₀Floor D r s := max (A.n₀Floor D r s) (B.n₀Floor D r s)
  CsFloor D r s := max (A.CsFloor D r s) (B.CsFloor D r s)
  NFloor k := max (A.NFloor k) (B.NFloor k)
theorem HoldsAtAdmissibleParameters.and {P₁ P₂ : ParameterAssignment → ℝ → Prop}
    (h₁ : HoldsAtAdmissibleParameters P₁) (h₂ : HoldsAtAdmissibleParameters P₂) :
    HoldsAtAdmissibleParameters fun T y => P₁ T y ∧ P₂ T y := by
  obtain ⟨A, hA, g₁⟩ := h₁
  obtain ⟨B, hB, g₂⟩ := h₂
  refine ⟨A.combine B, ⟨ColdStepAtMirrorFrames.EventuallyInParameters.and hA.property_eventually
      hB.property_eventually,
    fun D => lt_min (hA.rateCeiling_pos D) (hB.rateCeiling_pos D),
    fun D r => lt_min (hA.thresholdCeiling_pos D r) (hB.thresholdCeiling_pos D r)⟩, fun T hT hM => ?_⟩
  have hon : T.HoldsFrom fun S => A.property S ∧ B.property S := hM.holds
  obtain ⟨c, nss, hc, hS⟩ := hon
  have m₁ : A.IsMetBy T :=
    ⟨le_trans (le_max_left _ _) hM.side_ge, le_trans (le_max_left _ _) hM.derivBound_ge,
      le_trans hM.rt_le (min_le_left _ _), le_trans hM.threshold_le (min_le_left _ _),
      le_trans (le_max_left _ _) hM.n₀_ge, le_trans (le_max_left _ _) hM.Cs_ge,
      fun k => le_trans (le_max_left _ _) (hM.N_ge k), ⟨c, nss, hc, fun y hy => (hS y hy).1⟩⟩
  have m₂ : B.IsMetBy T :=
    ⟨le_trans (le_max_right _ _) hM.side_ge, le_trans (le_max_right _ _) hM.derivBound_ge,
      le_trans hM.rt_le (min_le_right _ _), le_trans hM.threshold_le (min_le_right _ _),
      le_trans (le_max_right _ _) hM.n₀_ge, le_trans (le_max_right _ _) hM.Cs_ge,
      fun k => le_trans (le_max_right _ _) (hM.N_ge k), ⟨c, nss, hc, fun y hy => (hS y hy).2⟩⟩
  obtain ⟨y₁, f₁⟩ := g₁ T hT m₁
  obtain ⟨y₂, f₂⟩ := g₂ T hT m₂
  exact ⟨max y₁ y₂, fun y hy =>
    ⟨f₁ y (le_trans (le_max_left _ _) hy), f₂ y (le_trans (le_max_right _ _) hy)⟩⟩
theorem HoldsAtAdmissibleParameters.mono {P₁ P₂ : ParameterAssignment → ℝ → Prop}
    (h : HoldsAtAdmissibleParameters P₁) (himp : ∀ T y, T.Admissible → P₁ T y → P₂ T y) :
    HoldsAtAdmissibleParameters P₂ := by
  obtain ⟨A, hA, g⟩ := h
  refine ⟨A, hA, fun T hT hM => ?_⟩
  obtain ⟨y₀, f⟩ := g T hT hM
  exact ⟨y₀, fun y hy => himp T y hT (f y hy)⟩
end YangMills.Construction.TotalDensities
end
