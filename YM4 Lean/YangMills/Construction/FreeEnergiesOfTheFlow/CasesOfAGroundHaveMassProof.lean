import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeight
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.GasIsAWeight
import YangMills.Construction.FreeEnergiesOfTheFlow.CasesOfAGroundHaveMass
import YangMills.Construction.FreeEnergiesOfTheFlow.FunctionsOfTheLabelsAreIntegrable
import YangMills.Construction.ResponseInTheExpansion.CaseMeanIsAMeanOfTheGas
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
theorem coarseStateWeight_ne_zero_on_ground (hmean : WeightedResponses.caseMeanEqGasMeanStatement)
    (hact : ClusterExpansionOfAStep.GasIsActivityBounded) (hcond : Dobrushin.ActivityConditionalLawsStatement)
    (hint : labelFunctionsIntegrableStatement) (hfloor : StepFloors.EventuallyFloorConditions) :
    FreeEnergiesOfTheFlow.CoarseStateWeightNeZeroOnGround := by
  obtain ⟨r₁, h₁, H₁⟩ := hmean
  obtain ⟨r₂, h₂, H₂⟩ := hact
  obtain ⟨r₃, h₃, H₃⟩ := hint
  refine ⟨fun c => min (r₁ c) (min (r₂ c) (r₃ c)), fun c => lt_min (h₁ c) (lt_min (h₂ c) (h₃ c)), fun T hT hr K => ?_⟩
  obtain ⟨y₁, Y₁⟩ := H₁ T hT (hr.trans (min_le_left _ _))
  obtain ⟨y₂, Y₂⟩ := H₂ T hT (hr.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨y₃, Y₃⟩ := H₃ T hT (hr.trans ((min_le_right _ _).trans (min_le_right _ _))) K
  obtain ⟨y₄, Y₄⟩ := hfloor T hT 1 1 one_pos one_pos
  refine ⟨max (max y₁ y₂) (max y₃ y₄), fun y hy R A hK hA n _ G hG => ?_⟩
  have hy₁ : y₁ ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hy₂ : y₂ ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hy₃ : y₃ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₄ : y₄ ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hnext : R.nextCoupling ≤ 1.01 * R.coupling :=
    ((Y₄ R.coupling (hy₄.trans hA.onFamily.le_coupling)).stable_nearby.2 R.nextCoupling hA.abs_sub_le).2.1
  obtain ⟨hadm, hF⟩ := Y₁ y hy₁ R hA.onFamily hnext n G hG
  have hW := Y₂ y hy₂ R hA.onFamily hnext n G hG fun j => j.1.Touches ∅
  have hprob : IsProbabilityMeasure (G.gibbsLaw ∅) := (hcond _ _ _ _ _ _ hW).1
  have hone : WeightedResponses.CaseIntegrable R G.cut G.coarse G.state (fun _ _ _ _ _ => 1) :=
    Y₃ y hy₃ R A hK hA n G hG ∅ (fun _ _ => 1) (fun _ => measurable_const) (fun Yt ωt => by simp [scoreSumOn])
  have hm := (hF (fun _ _ _ _ _ => 1) (fun _ _ _ => measurable_const) (fun _ _ _ _ _ _ _ _ _ => rfl) hone).2
  have hg : WeightedResponses.gasExpectationOfCase G (fun _ _ _ _ _ => 1) = 1 := by
    unfold WeightedResponses.gasExpectationOfCase StepGas.GasGround.expectation
    have e : (fun σ => StepSettings.weightedMean (WeightedResponses.chartDensity (WeightedResponses.configSetting G σ)) fun η =>
        (fun (_ : TorusFields.TorusField (n * R.params.side)) (_ : Finset (TorusFields.TorusSite (n * R.params.side))) _
            (_ : Finset (TorusFields.TorusBond (n * R.params.side))) (_ : StepCosts.BaseChoice R.params.side n) => (1 : ℝ))
          ((WeightedResponses.configSetting G σ).field η) (WeightedResponses.configSetting G σ).support
          (WeightedResponses.configSetting G σ).labelling (G.badBondsOf σ) (WeightedResponses.configSetting G σ).bases)
          =ᵐ[G.gibbsLaw ∅] fun _ => (1 : ℝ) := by
      filter_upwards [hadm] with σ hσ
      unfold StepSettings.weightedMean
      simp only [one_mul]
      exact div_self hσ.2.ne'
    rw [integral_congr_ae e]
    simp
  intro h0
  unfold WeightedResponses.caseMean at hm
  rw [h0, div_zero, hg] at hm
  exact zero_ne_one hm
end YangMills.Construction.FreeEnergies
end
