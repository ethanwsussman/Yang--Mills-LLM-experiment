import YangMills.Construction.SystemOfAdmissibleConstants.TheFourBoundsAlongTheTrajectory
import YangMills.Construction.TotalDensitiesGiveASystem.GlueAtDrawnParameters
import YangMills.Construction.TotalDensitiesGiveASystem.TheBoundsOnTheWindow
import YangMills.Construction.TotalDensitiesGiveASystem.TheCouplingsGiveTheWindow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensities
theorem windowBoundsExist_of_familyBoundsAlongTrajectory (hcoup : TrajectoryCouplingsGiveWindow.Statement)
    (hbounds : SystemOfAdmissibleConstants.FamilyBoundsAlongFlow) : WindowBoundsExist.Statement := by
  refine HoldsAtAdmissibleParameters.mono (hcoup _ hbounds) fun T y hadm h Bs hBs => ?_
  obtain ⟨y₂, f⟩ := h Bs hBs
  refine ⟨y₂, fun g hg hy => ?_⟩
  obtain ⟨D, rfl, A, b, hA, hb, hcl, -⟩ := f g hg hy
  have hApos : 0 < A := by linarith
  refine ⟨AdmissibleConstants.cumulantConstant T.side A b, AdmissibleConstants.transferConstant T.side A b, ?_, ?_,
    fun M hM => ⟨?_, ?_⟩⟩
  · have hdisj : 0 < 10 * 2 ^ 53 * (T.side : ℝ) ^ 5 * A * Real.exp (b + b ^ ((20 : ℝ) / 19)) ∨
        0 < 24 * 2 ^ 40 * (T.side : ℝ) ^ 12 := by
      have hside : (0 : ℝ) < T.side := by
        have hle : 2 ^ 40 ≤ T.side := hadm.L_ge
        exact_mod_cast lt_of_lt_of_le (by norm_num) hle
      exact Or.inr (by positivity)
    unfold AdmissibleConstants.cumulantConstant
    have := lt_max_iff.2 hdisj
    linarith
  · unfold AdmissibleConstants.transferConstant
    exact lt_max_iff.2 (Or.inl (by positivity))
  · intro K β hp ν hν n hn R d hR hd f hf hs hsep
    exact (hcl M hM).ballInStates K β hp ν hν n hn R d hR hd f hf hs hsep
  · intro K β hp ν hν ν' hν' R hR f hf hs
    exact (hcl M hM).meanGapInStates K β hp ν hν ν' hν' R hR f hf hs
end YangMills.Construction.TotalDensities
end
