import YangMills.Construction.TheStatementsProvedTogether.FromTheParametersAreDrawnParametersProof
import YangMills.Construction.TheStatementsProvedTogether.FromHeatSumOnALatticeProof
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
set_option autoImplicit false
noncomputable section
namespace YangMills.BranchHot
open Construction Construction.RenormalizationStepParameters Construction.WeightedResponses
open Construction.FreeEnergies Construction.TheStatementsProvedTogether

def HasScoredTowers (Tb : ParameterAssignment) (Kr : ResponseParameters) (y : ℝ) : Prop :=
  ∀ (β : ℝ) (k : ℕ), CouplingsAboveFloor (Tb.stepParameters y) β k →
    ∃ (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T),
      S.params = Kr ∧ S.FollowsFlow β k

/-- Choose the expansion and response estimates on the very towers realizing the Wilson flow. -/
theorem onScoredTowers {P : ParameterAssignment → ResponseParameters → ℝ → Prop} (hP : AtResponseParameters P) :
    TotalDensities.HoldsAtAdmissibleParameters fun Tb y => ∃ Kr : ResponseParameters,
      Kr.Admissible (Tb.stepParameters y) ∧ HasScoredTowers Tb Kr y ∧ P Tb Kr y := by
  apply response_parameters_admissible
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := exists_scoredTower a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := hP a ha
  refine ⟨max L₁ L₂, fun d => min (r₁ d) (r₂ d), max C₁ C₂,
    fun d => lt_min (hr₁ d) (hr₂ d), ?_⟩
  intro L hodd hL T hTa hTL hT hcs hOn hrt hC
  obtain ⟨Kr, y₁, F₁⟩ := H₁ L hodd ((le_max_left ..).trans hL) T hTa hTL hT hcs hOn
    (hrt.trans (min_le_left ..)) ((le_max_left ..).trans hC)
  obtain ⟨y₂, F₂⟩ := H₂ L hodd ((le_max_right ..).trans hL) T hTa hTL hT hcs hOn
    (hrt.trans (min_le_right ..)) ((le_max_right ..).trans hC) Kr
  refine ⟨max y₁ y₂, fun y hy hret hwil => ?_⟩
  have hExp : ExpansionHolds (T.stepParameters y) := ⟨hret, hwil⟩
  have hTw : HasScoredTowers T Kr y := F₁ y ((le_max_left ..).trans hy) hExp
  have hb : CouplingsAboveFloor (T.stepParameters y) y 0 := by
    intro j hj
    have : j = 0 := by omega
    subst j
    exact le_rfl
  obtain ⟨_, S, hKr, hS⟩ := hTw y 0 hb
  have he := (hS.params_eq 0).trans hKr
  exact ⟨Kr, he ▸ (hS.isAdmissible 0 le_rfl).params_admissible, hTw, F₂ y ((le_max_right ..).trans hy) hExp⟩

/-- Intersect finitely many response estimates before choosing the common response parameters. -/
theorem responseAnd {P Q : ParameterAssignment → ResponseParameters → ℝ → Prop}
    (hP : AtResponseParameters P) (hQ : AtResponseParameters Q) :
    AtResponseParameters fun T Kr y => P T Kr y ∧ Q T Kr y := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hP a ha
  obtain ⟨L₂, r₂, C₂, hr₂, H₂⟩ := hQ a ha
  refine ⟨max L₁ L₂, fun d => min (r₁ d) (r₂ d), max C₁ C₂, fun d => lt_min (hr₁ d) (hr₂ d), ?_⟩
  intro L ho hL T hTa hTL hT hcs hOn hrt hC Kr
  obtain ⟨y₁, F₁⟩ := H₁ L ho ((le_max_left ..).trans hL) T hTa hTL hT hcs hOn
    (hrt.trans (min_le_left ..)) ((le_max_left ..).trans hC) Kr
  obtain ⟨y₂, F₂⟩ := H₂ L ho ((le_max_right ..).trans hL) T hTa hTL hT hcs hOn
    (hrt.trans (min_le_right ..)) ((le_max_right ..).trans hC) Kr
  exact ⟨max y₁ y₂, fun y hy he =>
    ⟨F₁ y ((le_max_left ..).trans hy) he, F₂ y ((le_max_right ..).trans hy) he⟩⟩
end YangMills.BranchHot
end
