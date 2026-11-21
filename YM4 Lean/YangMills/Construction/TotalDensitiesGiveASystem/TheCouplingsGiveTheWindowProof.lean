import YangMills.Construction.ParameterData.ScaleSequenceData
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheCouplingsGiveTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.TheParametersAreDrawnParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open TrajectoryData
theorem trajectoryCouplingsGiveWindow_of_schedules (htables : ResponseParametersToAdmissibleParameters)
    (htrack : trajectoryDataStatement) : TotalDensities.TrajectoryCouplingsGiveWindow.Statement := by
  intro P hP
  have hparams : TotalDensities.HoldsAtAdmissibleParameters fun T y => ∃ D : TrajectoryParameters T y,
      ∀ s lam : ℝ, 2 * T.B ≤ s → 0 < lam →
      lam ≤ D.rateBound → (D.withShift s lam).Admissible ∧ HasTrajectoryData (D.withShift s lam) := by
    obtain ⟨Q, hQ, sideFloor, rateCeiling, thresholdCeiling, n₀Floor, CsFloor, C₀, h1, h2, hT'⟩ := htrack
    refine ⟨⟨Q, sideFloor, fun _ => C₀, rateCeiling, thresholdCeiling, n₀Floor, CsFloor, fun _ => 0⟩,
      ⟨hQ, h1, h2⟩, fun T hadm hmet => ?_⟩
    exact hT' T hadm hmet.side_ge hmet.rt_le hmet.threshold_le hmet.n₀_ge hmet.Cs_ge
      hmet.derivBound_ge hmet.holds
  refine TotalDensities.HoldsAtAdmissibleParameters.mono
    (TotalDensities.HoldsAtAdmissibleParameters.and (htables _ hP) hparams) fun T y hadm hboth s hs => ?_
  obtain ⟨h₁, D, hD⟩ := hboth
  have hrate : 0 < D.rateBound := by
    have hL : (1 : ℝ) < T.side := by
      have h : 1 < T.side := lt_of_lt_of_le (by norm_num) hadm.L_ge
      exact_mod_cast h
    have hlog := Real.log_pos hL
    show 0 < 3 / 4 * (11 / (3 * Real.pi ^ 2) * Real.log T.side)
    positivity
  obtain ⟨hadmissible, -⟩ := hD s D.rateBound hs hrate le_rfl
  exact ⟨SystemOfAdmissibleConstants.inverseCouplingFloor (D.withShift s D.rateBound), fun g hg hy =>
    ⟨D.withShift s D.rateBound, rfl, h₁ _ hadmissible g hg hy⟩⟩
end YangMills.Construction.TotalDensitiesGiveASystem
end
