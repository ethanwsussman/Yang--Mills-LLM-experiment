import YangMills.Construction.ClusterExpansionOfAStep.ColdGroundIsTheColdSettingProof
import YangMills.Construction.LawByMomentsOfTheFlow.FieldOfTheColdGround
import YangMills.Construction.RunningCouplingSlope.LeastPointReadsTheChainProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdGroundField
open StepSettings StepGas TorusFields TorusLumps BlockOffsets StepCosts BlockAverages ColdStepAtMirrorFrames WeightedResponses
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem field_withFine_field (s : ChartSetting R n) (hodd : Odd R.params.side) (hn : 2 ≤ n)
    (hf : s.free ⊆ chartBonds R.params.side n) (η : FreeCoords s.free) :
    ({ s with fine := s.field 0 } : ChartSetting R n).field η = s.field η := by apply _root_.YangMills.Construction.ColdCaseGround.field_fine_field_zero <;> assumption
theorem settingWithFamily_empty (V : TorusField n) :
    (coldCaseGround R V).settingWithFamily GasFamily.empty = coldChartSetting R V := by apply _root_.YangMills.Construction.ColdCaseGround.settingWithFamily_empty_coldCaseGround <;> assumption
omit [NeZero n] in
theorem withFine_field_congr {s s' : ChartSetting R n} (h : s = s') :
    ({ s with fine := s.field 0 } : ChartSetting R n) = ({ s' with fine := s'.field 0 } : ChartSetting R n) := by apply _root_.YangMills.Construction.ColdCaseGround.fine_field_zero_congr <;> assumption
theorem pathHolonomy_one {H : BlockFrame} {j : ℕ} (x : H.Site j) (l : List PathStep) :
    BlockAverages.pathHolonomy (fun _ _ => (1 : UnitQuaternion) : H.GaugeField j) x l = 1 := by apply _root_.YangMills.SharedProofs.p3325 <;> assumption
omit [NeZero n] in
theorem gaugeAt_trivialField (x : TorusSite (n * R.params.side)) :
    gaugeAt (R := R) (trivialField (n * R.params.side)) x = 1 :=
  pathHolonomy_one _ _
open Classical in
theorem coldChartSetting_withFine_spec (V : TorusField n) (hodd : Odd R.params.side) (hn : 2 ≤ n) (s : ChartSetting R n)
    (hs : s = ({ coldChartSetting R V with fine := (coldChartSetting R V).field 0 } : ChartSetting R n)) :
    s.free = chartBonds R.params.side n ∧
    (∀ (η : FreeCoords s.free) (b : s.free),
      s.field η b.1.1 b.1.2 =
        if IsCrossingBond (F := stepBlockFrame R.params.side n)
            (torusSiteInFrame (stepBlockFrame R.params.side n) 0 b.1.1, b.1.2)
        then expUnit (frameCoord R.params R.anchorRadius R.depth R.frameReach V b.1 + toImaginary (η b)) *
          V (parentBlock R.params.side b.1.1) b.1.2
        else expUnit (frameCoord R.params R.anchorRadius R.depth R.frameReach V b.1 + toImaginary (η b))) ∧
    ∀ (η : FreeCoords s.free) (b : TorusBond (n * R.params.side)), b ∉ s.free → s.field η b.1 b.2 = 1 := by
  subst hs
  have hsub : (coldChartSetting R V).free ⊆ chartBonds R.params.side n := Finset.Subset.refl _
  refine ⟨rfl, fun η b => ?_, fun η b hb => ?_⟩
  · have hf := congrFun (congrFun (field_withFine_field (coldChartSetting R V) hodd hn hsub η) b.1.1) b.1.2
    rw [hf]
    have hb : (b.1.1, b.1.2) ∈ (coldChartSetting R V).free := b.2
    unfold ChartSetting.field
    rw [dif_pos hb]
    unfold chartLink
    have e : (coldChartSetting R V).fine = trivialField _ := rfl
    rw [e, gaugeAt_trivialField, gaugeAt_trivialField]
    simp only [inv_one, one_mul, mul_one]
    rfl
  · have hf := congrFun (congrFun (field_withFine_field (coldChartSetting R V) hodd hn hsub η) b.1) b.2
    rw [hf]
    unfold ChartSetting.field
    rw [dif_neg hb]
    rfl
theorem chartDensity_withFine (s : ChartSetting R n) (b : TorusField (n * R.params.side))
    (h : ∀ η, ({ s with fine := b } : ChartSetting R n).field η = s.field η) (η : FreeCoords s.free) :
    chartDensity ({ s with fine := b } : ChartSetting R n) η = chartDensity s η := by
  have hp : ({ s with fine := b } : ChartSetting R n).potential η = s.potential η := by
    unfold ChartSetting.potential
    rw [h η]
    rfl
  unfold chartDensity
  rw [hp]
  rfl
end ColdGroundField
namespace MomentLaw
open StepSettings StepGas StepCosts ColdGroundField
theorem coldGroundField_holds : coldGroundFieldStatement := by
  intro R n _ V hodd hn
  have hs : coldSettingOver R V =
      ({ coldChartSetting R V with fine := (coldChartSetting R V).field 0 } : ChartSetting R n) :=
    withFine_field_congr (s := (coldCaseGround R V).settingWithFamily GasFamily.empty)
      (s' := coldChartSetting R V) (settingWithFamily_empty V)
  have hsub : (coldChartSetting R V).free ⊆ chartBonds R.params.side n := Finset.Subset.refl _
  refine ⟨hs, ?_, ?_⟩
  · exact chartDensity_withFine (coldChartSetting R V) ((coldChartSetting R V).field 0)
      (fun η => field_withFine_field (coldChartSetting R V) hodd hn hsub η)
  · exact coldChartSetting_withFine_spec V hodd hn (coldSettingOver R V) hs
end MomentLaw
end YangMills.Construction
end
