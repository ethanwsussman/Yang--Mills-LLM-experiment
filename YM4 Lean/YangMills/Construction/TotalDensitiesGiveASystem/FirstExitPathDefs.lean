import YangMills.Construction.ClusterExpansionOfAStep.StepVariablesAtParameters
import YangMills.Construction.ClusterExpansionOfAStep.TheFlowIsTheLawOfTheChain
import YangMills.Construction.WindowOfTheParameters.FirstPassageOfASequenceForm
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensities
def IsFirstPassagePoint (p : TorusLumps.StepParameters) (Bs g : ℝ) (K : ℕ) (β : ℝ) : Prop :=
  β ∈ SequencePassage.passageWindow Bs g (ClusterExpansionOfAStep.flowCoupling p) K
structure AssignmentConstraints where
  property : ColdStepAtMirrorFrames.StepParameters → Prop
  sideFloor : ℝ → ℕ
  derivBoundFloor : ℝ → ℝ
  rateCeiling : RenormalizationStepParameters.ChainParameters → ℝ
  thresholdCeiling : RenormalizationStepParameters.ChainParameters → ℝ → ℝ
  n₀Floor : RenormalizationStepParameters.ChainParameters → ℝ → ℝ → ℕ
  CsFloor : RenormalizationStepParameters.ChainParameters → ℝ → ℝ → ℝ
  NFloor : ℕ → ℝ
structure AssignmentConstraints.Satisfiable (D : AssignmentConstraints) : Prop where
  property_eventually : ColdStepAtMirrorFrames.EventuallyInParameters D.property
  rateCeiling_pos : ∀ c, 0 < D.rateCeiling c
  thresholdCeiling_pos : ∀ c r, 0 < D.thresholdCeiling c r
structure AssignmentConstraints.IsMetBy (D : AssignmentConstraints) (T : RenormalizationStepParameters.ParameterAssignment) : Prop where
  side_ge : D.sideFloor T.coupling ≤ T.side
  derivBound_ge : D.derivBoundFloor T.coupling ≤ T.derivBound
  rt_le : T.rt ≤ D.rateCeiling T.toChainParameters
  threshold_le : T.threshold ≤ D.thresholdCeiling T.toChainParameters T.rt
  n₀_ge : D.n₀Floor T.toChainParameters T.rt T.threshold ≤ T.n₀
  Cs_ge : D.CsFloor T.toChainParameters T.rt T.threshold ≤ T.Cs
  N_ge : ∀ k, D.NFloor k ≤ T.N k
  holds : T.HoldsFrom D.property
def HoldsAtAdmissibleParameters (C : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop) : Prop :=
  ∃ D : AssignmentConstraints, D.Satisfiable ∧ ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → D.IsMetBy T →
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → C T y
def ForSmallCoupling (P : ℝ → Prop) : Prop :=
  ∃ y₂ : ℝ, ∀ g : ℝ, 0 < g → y₂ ≤ g ^ (-2 : ℤ) → P g
end YangMills.Construction.TotalDensities
end
