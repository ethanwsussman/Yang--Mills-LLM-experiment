import YangMills.Construction.ClusterExpansionOfAStep.FlowOfTheExpansion
import YangMills.Construction.SummableBoundsOfTheFlow.FlowOfTheNumbers
import YangMills.Construction.SummableBoundsOfTheFlow.TheFinerExpansionReturns
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CouplingFlow
def couplingAt (P : TorusLumps.StepParameters) (β : ℝ) (t : ℕ) : ℝ := (TorusLumps.couplingFlow P β t).1
structure FlowEstimateAt (T : RenormalizationStepParameters.ParameterAssignment) (y c M R X Cr : ℝ) (mw : ℕ) (v₀ : ℝ) : Prop where
  admissible : (T.stepParameters y).Admissible
  returns : StepReturn.ExpansionReturnsAt (T.stepParameters y)
  slope_gt : 10 < slopeConst T.side
  slope : HasAverageSlope (FamilyNorms.ParameterAssignment.oneLoop T) (slopeConst T.side) c
  secondStep_le : ∀ t, |FamilyNorms.ParameterAssignment.secondStep T t| ≤ M
  floor_le : y ≤ X
  floor_ge : 8 ≤ X
  Cr_nonneg : 0 ≤ Cr
  Cr_small : 8 * Cr * X ^ (-(1 / 4) : ℝ) ≤ 1
  mw_pos : 1 ≤ mw
  v₀_ge : X + 1 ≤ v₀
  flow_above : FlowAbove (FamilyNorms.ParameterAssignment.oneLoop T) (FamilyNorms.ParameterAssignment.secondStep T) X v₀
  bounds : ∀ β : ℝ, FlowBounds (FamilyNorms.ParameterAssignment.oneLoop T) (FamilyNorms.ParameterAssignment.secondStep T)
    (slopeConst T.side) c M R X Cr mw v₀ (couplingAt (T.stepParameters y) β)
  drop_two_sided : ∀ (β : ℝ) (i j : ℕ), i ≤ j → (∀ l < j, X ≤ couplingAt (T.stepParameters y) β l) →
    3 / 4 * slopeConst T.side * ((j : ℝ) - i) - 2 * c ≤ couplingAt (T.stepParameters y) β i - couplingAt (T.stepParameters y) β j ∧
      couplingAt (T.stepParameters y) β i - couplingAt (T.stepParameters y) β j ≤ 5 / 4 * slopeConst T.side * ((j : ℝ) - i) + 2 * c
  expansion : ∀ (β : ℝ) (t : ℕ), X ≤ β → (∀ l < t, X ≤ couplingAt (T.stepParameters y) β l) →
    TorusLumps.HasExpansion (T.stepParameters y) t (couplingAt (T.stepParameters y) β t)
      (TorusLumps.couplingFlow (T.stepParameters y) β t).2
  hits_window : ∀ (K : ℕ) (g : ℝ), 0 < g → v₀ ≤ (g ^ 2)⁻¹ →
    ∃ β : ℝ, StaysAbove X (couplingAt (T.stepParameters y) β) K ∧ |couplingAt (T.stepParameters y) β K - (g ^ 2)⁻¹| ≤ 1
  no_unit_descent : ∀ (β : ℝ) (t : ℕ), StaysAbove X (couplingAt (T.stepParameters y) β) t → mw ≤ t →
    ¬ ∀ l < t, couplingAt (T.stepParameters y) β (l + 1) = couplingAt (T.stepParameters y) β l - 1
def FlowEstimateExists : Prop :=
  ∃ Q : ColdStepAtMirrorFrames.StepParameters → Prop, ColdStepAtMirrorFrames.EventuallyInParameters Q ∧
    ∃ (sideMin : ℝ → ℕ) (rtMax : RenormalizationStepParameters.ChainParameters → ℝ) (thresholdMax : RenormalizationStepParameters.ChainParameters → ℝ → ℝ)
      (nMin : RenormalizationStepParameters.ChainParameters → ℝ → ℝ → ℕ) (CsMin : RenormalizationStepParameters.ChainParameters → ℝ → ℝ → ℝ) (C₀ : ℝ),
      (∀ D, 0 < rtMax D) ∧ (∀ D r, 0 < thresholdMax D r) ∧
      ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → sideMin T.coupling ≤ T.side → T.rt ≤ rtMax T.toChainParameters →
        T.threshold ≤ thresholdMax T.toChainParameters T.rt → nMin T.toChainParameters T.rt T.threshold ≤ T.n₀ →
        CsMin T.toChainParameters T.rt T.threshold ≤ T.Cs → C₀ ≤ T.derivBound → T.HoldsFrom Q →
        ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
          ∃ (c M R X Cr v₀ : ℝ) (mw : ℕ), FlowEstimateAt T y c M R X Cr mw v₀
end YangMills.Construction.CouplingFlow
end
