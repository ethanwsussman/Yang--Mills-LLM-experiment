import Mathlib
import YangMills.ContinuumLimit.TuningAtEveryCutoff
import YangMills.Construction.TheStatementsProvedTogether.FromNumberOfAStepIsTheNumberOfItsDensityProof
import YangMills.Construction.TheStatementsProvedTogether.FromSimilarityCarriesTheInfiniteLatticeProof
import YangMills.Construction.TheStatementsProvedTogether.FromZetaOfAGroundIsBorelProof
import YangMills.Construction.TheStatementsProvedTogether.FromFarSpinsMoveAVariableProof
import YangMills.Construction.TheStatementsProvedTogether.FromThirdOrderOfTheStepProof
import YangMills.Construction.TheStatementsProvedTogether.FromConcentrationInOneBoxProof
import YangMills.Construction.TheStatementsProvedTogether.FromHeatSumOnALatticeProof
import YangMills.Construction.TheStatementsProvedTogether.FromTheFourPointLawOnTheWindowProof
import YangMills.Construction.TheStatementsProvedTogether.FromTheParametersAreDrawnParametersProof
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
set_option autoImplicit false

noncomputable section

namespace YangMills.ContinuumLimit

open YangMills.Construction
open YangMills.Construction.WeightedResponses
open YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.TheStatementsProvedTogether

theorem run_table_on_families :
    HoldsOnParameterFamilies fun T y => ∃ (Kr : ResponseParameters) (lam c₅ : ℝ), RunTable T y Kr lam c₅ := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, g₁⟩ := responseCoeff_near_one a ha
  obtain ⟨L₂, r₂, C₂, hr₂, g₂⟩ := FourPointWindowLaw.chain_response_coeff_near_one a ha
  obtain ⟨L₃, r₃, C₃, hr₃, g₃⟩ := chain_response_coeffs_unique a ha
  obtain ⟨L₄, r₄, hr₄, g₄⟩ := coupling_flow_descends_linearly a ha
  refine ⟨max (max L₁ L₂) (max L₃ L₄), fun c => min (min (r₁ c) (r₂ c)) (min (r₃ c) (r₄ c)),
    max (max C₁ C₂) C₃, fun c => lt_min (lt_min (hr₁ c) (hr₂ c)) (lt_min (hr₃ c) (hr₄ c)),
    fun L hLo hL T hTa hTL hT hCS hOn hrt hC => ?_⟩
  have hrt₁ := (hrt.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hrt₂ := (hrt.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hrt₃ := (hrt.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrt₄ := (hrt.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hL₁ : L₁ ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hL₂ : L₂ ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hL₃ : L₃ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hL₄ : L₄ ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have hC₁ : C₁ ≤ T.derivBound := ((le_max_left _ _).trans (le_max_left _ _)).trans hC
  have hC₂ : C₂ ≤ T.derivBound := ((le_max_right _ _).trans (le_max_left _ _)).trans hC
  have hC₃ : C₃ ≤ T.derivBound := (le_max_right _ _).trans hC
  obtain ⟨lam, c₅, hlam, g₄⟩ := g₄ L hLo hL₄
  obtain ⟨Kr, hKr, y₁, k₁⟩ := g₁ L hLo hL₁ T hTa hTL hT hCS hOn hrt₁ hC₁
  obtain ⟨y₂, k₂⟩ := g₂ L hLo hL₂ T hTa hTL hT hCS hOn hrt₂ hC₂
  obtain ⟨y₃, k₃⟩ := g₃ L hLo hL₃ T hTa hTL hT hCS hOn hrt₃ hC₃
  obtain ⟨y₄, k₄⟩ := g₄ T hTa hTL hT hrt₄
  refine ⟨max (max y₁ y₂) (max y₃ (max y₄ T.floorMin)), fun y hy hR hW => ⟨Kr, lam, c₅, ?_⟩⟩
  simp only [max_le_iff] at hy
  obtain ⟨⟨e₁, e₂⟩, e₃, e₄, e₅⟩ := hy
  exact
    { adm := hT
      floor := e₅
      returns := hR
      bare := hW
      response := hKr y
      lam_pos := hlam
      descent := k₄ y e₄ hR hW
      coeff := fun β k hk => by
        obtain ⟨al, hal, -⟩ := k₁ y e₁ hR hW β k hk
        exact ⟨al, hal⟩
      near := fun β k al hk hal => k₂ y e₂ hR hW Kr (hKr y) β k al hk hal
      unique := fun β k al al' hk hal hal' =>
        k₃ y e₃ hR hW Kr Kr (hKr y) (hKr y) β k al al' hk hal hal' }

theorem run_table_at_admissible_tables :
    TotalDensities.HoldsAtAdmissibleParameters fun T y =>
      ∃ (Kr : ResponseParameters) (lam c₅ : ℝ), RunTable T y Kr lam c₅ :=
  response_parameters_admissible _ run_table_on_families

variable {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ}
  {Kr : ResponseParameters} {lam c₅ : ℝ}

theorem tuned_at_runFloor_closed (h : RunTable T y Kr lam c₅) (K : ℕ) :
    (∀ β : ℝ, (y ≤ β ∧ ∀ j < K, y ≤ TotalDensityFlow.coupling (T.stepParameters y) β j) →
      TotalDensityFlow.IsDefinedUpTo (T.stepParameters y) β K ∧
        ∀ j ≤ K, TotalDensityFlow.coupling (T.stepParameters y) β j =
          flowCouplings (T.stepParameters y) β j) ∧
    (IsOpen (runDomain T y K) ∧ IsUpperSet (runDomain T y K) ∧ (runDomain T y K).Nonempty ∧
      (∀ β ∈ runDomain T y K,
        y ≤ β ∧ ∀ j < K + 1, y ≤ TotalDensityFlow.coupling (T.stepParameters y) β j) ∧
      ∀ β ∈ runDomain T y K, TotalDensityFlow.coupling (T.stepParameters y) β K =
        flowCouplings (T.stepParameters y) β K) ∧
    (ContDiffOn ℝ 1 (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K) (runDomain T y K) ∧
      StrictMonoOn (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K) (runDomain T y K) ∧
      ∀ β ∈ runDomain T y K,
        3 / 4 ≤ deriv (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K) β ∧
          deriv (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K) β ≤ 5 / 4) ∧
    (∀ P : ℝ, runFloor T y c₅ ≤ P →
      (∃! β, IsTunedAt T y P K β) ∧ ∀ β, IsTunedAt T y P K β → β ∈ runDomain T y K) ∧
    (∀ β ∈ runDomain T y K, HasDerivAt (fun β => TotalDensityFlow.coupling (T.stepParameters y) β K)
      (runSlope T y Kr β K) β) ∧
    ContinuousOn (fun β => runSlope T y Kr β K) (runDomain T y K) :=
  tuned_at_runFloor kernel_has_coupling_deriv edge_score_properties step_transition_density_bounds
    weighted_response_chain_isProbabilityMeasure response_eq_conditional_mean least_action_plane_field
    expansion_gives_total_flow total_density_flow_unique h K

theorem tuned_of_runTable_closed (h : RunTable T y Kr lam c₅) : TunedAtEveryCutoff T y :=
  tuned_of_runTable kernel_has_coupling_deriv edge_score_properties step_transition_density_bounds
    weighted_response_chain_isProbabilityMeasure response_eq_conditional_mean least_action_plane_field
    expansion_gives_total_flow total_density_flow_unique h

theorem tuning_at_admissible_tables :
    TotalDensities.HoldsAtAdmissibleParameters fun T y => TunedAtEveryCutoff T y :=
  TotalDensities.HoldsAtAdmissibleParameters.mono run_table_at_admissible_tables
    fun _ _ _ ⟨_, _, _, h⟩ => tuned_of_runTable_closed h

end YangMills.ContinuumLimit

end
