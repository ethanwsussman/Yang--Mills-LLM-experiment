import YangMills.Construction.GrowingTori.DefinitionsForSequencesOfGrowingTori
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.FamiliesOfLimits
open ParameterChoice FlowConstants PeriodicLattice.CubesOfStep
structure LimitSetup where
  consts : DerivedConstants
  choice : FullChoice
  standingConstraints : GrowingTori.ParameterConstraints consts choice
  activityKind : PeriodicLattice.ActivityDomainKind
namespace LimitSetup
variable (D : LimitSetup)
abbrev L : ℕ := D.choice.L
abbrev upToCoupling : ChoiceUpToCoupling := D.choice.toChoiceUpToCoupling
theorem constraints : GrowingTori.ParameterConstraints D.consts D.choice := D.standingConstraints

def toGrowth : GrowingTori.GrowthParameters where
  constants := D.consts
  choice := D.choice
  admissible := D.constraints
  activityKind := D.activityKind
abbrev referenceExponent (g : ℝ) : ℕ := referenceTorusExponent D.consts D.upToCoupling g
abbrev IsReferenceCoupling (g : ℝ) : Prop := D.toGrowth.IsReferenceCoupling g
def cubeExp : ℕ := Nat.log D.L D.choice.M
theorem one_lt_L : 1 < D.L := by
  have : 13 ≤ D.choice.L := D.standingConstraints.factor_admissible.2
  show 1 < D.choice.L
  omega
theorem M_eq_pow : D.choice.M = D.L ^ D.cubeExp := by
  obtain ⟨n, h⟩ := D.standingConstraints.M_eq_pow
  have h' : D.choice.M = D.L ^ n := h
  rw [cubeExp, h', Nat.log_pow D.one_lt_L]
variable {D}
variable (D)
def SettingFloor : Prop :=
  BlockingFactorCondition D.consts D.upToCoupling.toChoiceUpToCubes
end LimitSetup
end YangMills.Construction.FamiliesOfLimits
end
