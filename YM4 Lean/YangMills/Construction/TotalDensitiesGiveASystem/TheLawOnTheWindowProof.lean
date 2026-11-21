import YangMills.Construction.SystemOfAdmissibleConstants.TheThresholdsAlongTheTrajectory
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheCouplingsGiveTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.TheLawOnTheWindow
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TotalDensities
private theorem leadingTwoPointTerm_eq_twoPointMainTerm (d : ℝ) (f h : InfiniteLattice.AmbientSpace → ℝ) :
    AdmissibleConstants.leadingTwoPointTerm d f h = SystemsWithFiveBounds.twoPointMainTerm d f h := by
  unfold AdmissibleConstants.leadingTwoPointTerm SystemsWithFiveBounds.twoPointMainTerm
    SystemsWithFiveBounds.twoPointPrefactor
  ring
private theorem thresholdEstimates_forAllTrajectoryCouplings
    (hthr : SystemOfAdmissibleConstants.thresholdsStatement) :
    SystemOfAdmissibleConstants.ForAllTrajectoryCouplings fun T y D g =>
      ∃ Kr : WeightedResponses.ResponseParameters, Kr.Admissible (T.stepParameters y) ∧
      ∀ vt : ℝ, 0 < vt → vt ≤ 1 → ∃ XL CL : ℝ, 1 ≤ XL ∧ 0 ≤ CL ∧
        SystemOfAdmissibleConstants.couplingLawAt D Kr g vt XL CL ∧
        SystemOfAdmissibleConstants.ThresholdEstimates D Kr g vt XL CL := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hp, h⟩ := hthr a ha
  refine ⟨L₀, rt₀, C₀, hp, fun L ho hge T h1 h2 hD hC hH hr hc => ?_⟩
  obtain ⟨y₀, f⟩ := h L ho hge T h1 h2 hD hC hH hr hc
  refine ⟨y₀, fun y hy hR hW D hDh g hg hfl => ?_⟩
  obtain ⟨Kr, hKr, hk⟩ := f y hy hR hW
  exact ⟨Kr, hKr, hk D hDh g hg hfl⟩
theorem twoPointLawOnWindow_of_thresholds (hcoup : TrajectoryCouplingsGiveWindow.Statement)
    (hthr : SystemOfAdmissibleConstants.thresholdsStatement) : twoPointLawOnWindow := by
  refine HoldsAtAdmissibleParameters.mono (hcoup _ (thresholdEstimates_forAllTrajectoryCouplings hthr))
    fun T y _ h Bs hBs => ?_
  obtain ⟨y₂, f⟩ := h Bs hBs
  refine ⟨y₂, fun g hg hy ϑ hϑ => ?_⟩
  obtain ⟨D, rfl, Kr, hKr, hD⟩ := f g hg hy
  obtain ⟨XL, CL, -, -, -, th⟩ := hD ϑ hϑ.1 hϑ.2
  refine ⟨AdmissibleConstants.distanceCutoff D Kr.Cstar XL CL g, AdmissibleConstants.combinedModulus D Kr.Cstar g,
    StateLaws.minimalCutoff (T.stepParameters y) (D.threshold g),
    ⟨⟨th.pos, th.lt_one⟩, th.modulus_monotoneOn,
      fun d hd => ⟨(th.modulus_mem d hd).1, (th.modulus_mem d hd).2⟩, th.modulus_tendsto⟩, ?_⟩
  intro d hd K β hp hK ν hν u v huv
  obtain ⟨-, -, -, hlaw⟩ := th.twoPoint d hd K β ⟨hp, hK⟩
  obtain ⟨t, ht, -, heq⟩ := hlaw ν hν (u, v) huv
  refine ⟨AdmissibleConstants.leadingTwoPointTerm d u v * t, heq, t - 1, ?_, ?_, ?_⟩
  · rw [leadingTwoPointTerm_eq_twoPointMainTerm]
    ring
  · have := ht.1
    linarith
  · have := ht.2
    linarith
end YangMills.Construction.TotalDensities
end
