import YangMills.Construction.ClusterExpansionOfAStep.AZeroFactorKillsTheState
import YangMills.Construction.ClusterExpansionOfAStep.ClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.HullStatesAreGrounds
import YangMills.Construction.FreeEnergiesOfTheFlow.ExpansionAlongTheFlow
import YangMills.Construction.FreeEnergiesOfTheFlow.StatesOfATowerStandOnGrounds
import YangMills.Construction.ResponseInTheExpansion.MassAlongTheLevelsProof
import YangMills.Construction.ResponseInTheExpansion.MeansGivenAStateAreMeansOverItsCases
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import YangMills.Construction.ResponseInTheExpansion.TwoPointFunctionByTotalCovariance
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.FreeEnergies
private theorem isWellPosed_of_onParameters {T : RenormalizationStepParameters.ParameterAssignment} (hT : T.Admissible) {y : ℝ} (hy₀ : T.floorMin ≤ y) (hy₁ : 1 ≤ y)
    {R : StepSettings.StepSetup}
    (hon : R.OnParameters T y) (hmoved : |R.nextCoupling - R.coupling| ≤ 2 * T.B) (hArr : R.IsSymmetricWeight)
    (hF : T.FloorConditions (2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17) 1 R.coupling) : R.IsWellPosed := by apply _root_.YangMills.SharedProofs.p3707 <;> assumption
theorem towerStatesAreGroundStates_holds (hG : ResponseInTheExpansion.conditionalMeanIsCaseMeanStatement)
    (hT : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement) (hSt : ResponseInTheExpansion.StageStatesMeasurableStatement)
    (hZero : ClusterExpansionOfAStep.CoarseWeightZeroOfFactorZero) (hHull : StepGas.HullStateIsHotCase) (hImg : TorusLumps.CoarseHullIsHullState)
    (hFl : StepFloors.EventuallyFloorConditions) (hRow : expansionAlongFlow) : TowerStatesAreGroundStates := by
  intro a ha
  obtain ⟨L₀, rt₀, hrt₀, H⟩ := hG a ha
  refine ⟨L₀, rt₀, 0, hrt₀, ?_⟩
  intro L hodd hL Tb hTa hTL hD hCS hOn hrt hCd K
  obtain ⟨y₁, Y₁⟩ := H L hodd hL Tb hTa hTL hD hrt
  obtain ⟨y₂, Y₂⟩ := hHull Tb hD
  have hCpos : (0 : ℝ) < 2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 17 := by positivity
  obtain ⟨y₃, Y₃⟩ := hFl Tb hD _ 1 hCpos one_pos
  refine ⟨max (max y₁ y₂) (max y₃ (max Tb.floorMin 1)), fun y hy hRS => ?_⟩
  have hy₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy₃ : y₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₀ : Tb.floorMin ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hy1 : 1 ≤ y := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  intro β T S tp hSK hOR hRR u hu
  have hst := hOR.isFlowStep u hu.le
  have hadm := hD.fits y hy₀
  have hmoved : |(T.stage u).toStepSetup.nextCoupling - (T.stage u).toStepSetup.coupling| ≤ 2 * Tb.B := by
    rw [hst.nextCoupling_eq, hst.coupling_eq]
    exact (hRow _ hRS β tp hRR).2 u hu
  have hsymm : (T.stage u).toStepSetup.IsSymmetricWeight := by
    have h := (hRow _ hRS β u (fun j hj => hRR j (by omega))).1.1
    show ∀ (n : ℕ) [NeZero n], (T.stage u).toStepSetup.params.n₀ ≤ n → _
    rw [hst.functional_eq]
    exact h
  have hposed : (T.stage u).toStepSetup.IsWellPosed :=
    isWellPosed_of_onParameters hD hy₀ hy1 hst.onFamily hmoved hsymm (Y₃ _ (hy₃.trans hst.onFamily.le_coupling))
  refine ⟨hposed, fun n _ hbs => ?_⟩
  have hsidePos : 0 < (Tb.stepParameters y).side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hbsSide : TorusLumps.IsBlockTorusSide (Tb.stepParameters y) (n * (Tb.stepParameters y).side) :=
    ⟨Dvd.intro_left _ rfl, hbs.2.trans (Nat.le_mul_of_pos_right _ hsidePos)⟩
  have hmg := Y₁ y hy₁ hRS.returns_at hRS.wilson_expansion T β u n
    ⟨hOR.startsAtWilson, fun j hj => (hOR.isFlowStep j (by omega)).coupling_eq, fun j hj => (hOR.isFlowStep j (by omega)).onFamily⟩
    hOR.isCutoff_bottom hOR.marksMeasurable hposed hbsSide hbs.1 (fun _ _ _ _ _ _ => 1) measurable_const ⟨1, fun _ => (abs_one (α := ℝ)).le⟩
  have hP : IsProbabilityMeasure (WeightedResponses.markedSampleLaw T β (u + 1) n) :=
    (hT _ hadm hadm.depth_lt T hOR.isCutoff_bottom hOR.marksMeasurable β (fun _ => 0) (u + 1) n).1
  have hField : WeightedResponses.stageSigma T (u + 1) n ≤ WeightedResponses.markedSampleMeasurableSpace (Tb.stepParameters y) (u + 1) n :=
    (hSt _ hadm T (u + 1) n).comap_le
  have hone := condExp_const (μ := WeightedResponses.markedSampleLaw T β (u + 1) n) hField (1 : ℝ)
  filter_upwards [hmg] with x hx
  have hm1 : WeightedResponses.caseMean (T.stage u).toStepSetup (StepSettings.hotCoreSites (T.stage u).toStepSetup x.2.2.1) x.2.2.1
      (WeightedResponses.stageState T (u + 1) n x).2 (fun _ _ _ _ _ => 1) = 1 := by
    refine hx.symm.trans ?_
    exact congrFun hone x
  have hne : StepSettings.coarseStateWeight (T.stage u).toStepSetup (StepSettings.hotCoreSites (T.stage u).toStepSetup x.2.2.1) x.2.2.1
      (WeightedResponses.stageState T (u + 1) n x).2 ≠ 0 := by
    intro h0
    unfold WeightedResponses.caseMean at hm1
    rw [h0, div_zero] at hm1
    exact zero_ne_one hm1
  have hhull : TorusLumps.IsHullState (Tb.stepParameters y) (T.stage u).toStepSetup.nextRange x.2.2.1 (WeightedResponses.stageState T (u + 1) n x).2.1 :=
    hImg _ hadm _ _ hposed.range_le hposed.nextRange_ge n hbs.1 x.2.2.1 _ _
  have hfac : ∀ X ∈ TorusLumps.chainComponents (T.stage u).toStepSetup.nextRange (WeightedResponses.stageState T (u + 1) n x).2.1,
      StepSettings.coarseFactor x.2.2.1 (WeightedResponses.stageState T (u + 1) n x).2 X ≠ 0 := fun X hX h0 =>
    hne (hZero _ hposed n hbs x.2.2.1 _ hhull ⟨X, hX, h0⟩)
  refine ⟨Or.inr (Y₂ y hy₂ _ hst.onFamily hposed n hbs x.2.2.1 _ hhull hfac), hhull, ?_⟩
  show 0 < StepSettings.coarseWeightExpansion (T.stage u).toStepSetup n x.2.2.1 (WeightedResponses.stageState T (u + 1) n x).2.1 (WeightedResponses.stageState T (u + 1) n x).2.2
  unfold StepSettings.coarseWeightExpansion
  rw [dif_neg (NeZero.ne n)]
  exact lt_of_le_of_ne ENNReal.toReal_nonneg hne.symm
end YangMills.Construction.FreeEnergies
end
