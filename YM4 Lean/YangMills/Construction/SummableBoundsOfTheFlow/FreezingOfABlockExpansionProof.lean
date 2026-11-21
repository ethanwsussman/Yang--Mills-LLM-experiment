import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionIsAdmitted
import YangMills.Construction.SummableBoundsOfTheFlow.BondsNearACellPairByOffsets
import YangMills.Construction.SummableBoundsOfTheFlow.FreezingOfABlockExpansion
import YangMills.Construction.SummableBoundsOfTheFlow.FreezingWithTwoFamilies
import YangMills.Construction.SummableBoundsOfTheFlow.ParametersMatchAtRaisedConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusComparison SummableBounds
namespace TorusFreezing
theorem exists_shortPairing_of_agreeOnBall (hP : bondsNearCellsPairStatement) {L t n₀ q : ℕ} (hL : Odd L)
    (hn : 1 ≤ n₀) {F F' : BlockFrame} (hF : IsCubicTopTorus L t n₀ F) (hF' : IsCubicTopTorus L t n₀ F')
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {Y : F.Cell} {Y' : F'.Cell}
    (hA : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (j : ι → ↥(chordBonds (finiteCells F)))
      (j' : ι → ↥(chordBonds (finiteCells F'))), IsShortPairing Y Y' q j j' := by
  obtain ⟨h1, -, m, hm, hnm⟩ := hF
  obtain ⟨h1', -, m', hm', hnm'⟩ := hF'
  refine hP F F' Y Y' q (by rw [h1]; exact hL) (by rw [h1, h1']) (fun i => ?_) (fun i => ?_)
  · rcases hA.1 i with h | h
    · have := hm i
      omega
    · exact h
  · rcases hA.2.1 i with h | h
    · have := hm' i
      omega
    · exact h
theorem blockExpansionExpectationDecouples_holds (hJ : joinAtLoweredConstantsStatement)
    (hP : bondsNearCellsPairStatement) (hF : expectationDecouples)
    (hA : interpolatedBlockExpansionAdmissibleStatement) : blockExpansionExpectationDecouples := by
  refine hJ ExpectationDecouples InterpolatedBlockExpansionAdmissibleAt BlockExpansionExpectationDecouples (fun _ => 0)
    (fun U => U.Cs * (1 + U.E / U.η₃) ^ 2 * U.Cs / U.η₃) hF hA ?_
  intro T c c' hc hc' hodd hn hE hη hη1 _ hK hFz hAd t x s ε φ h F F' V V' Y Y' q hx hs hs1 hε hφ hh hTF
    hTF' hV hV' hAg
  obtain ⟨ι, _, _, j, j', hpair⟩ := exists_shortPairing_of_agreeOnBall hP hodd hn hTF hTF' hAg
  obtain ⟨adm, hd, hd'⟩ := hAd t x s ε φ h F F' V V' Y Y' q ι j j' hx hs hs1 hε hφ hh hTF hTF' hV hV' hAg hpair
  have hα : 0 ≤ c * ε / T.η₃ := (abs_nonneg _).trans adm.expectation_sub_le
  have fz := hFz t x s (StepLaw.ofFamily φ) F F' V V' Y Y' q ι j j' (c * ε / T.η₃) _ _ hx hs hs1
    hφ hTF hTF' hV hV' hAg hpair hα hd hd' adm
  refine fz.trans ?_
  have he : 0 ≤ Real.exp (-(T.κ * q / 2 ^ 7)) := (Real.exp_pos _).le
  have e : c * StepLaw.amplitude (StepLaw.ofFamily φ) (T.E / T.η₃) ^ 2 * (c * ε / T.η₃) =
      (c * (1 + T.E / T.η₃) ^ 2 * c / T.η₃) * ε := by
    simp only [StepLaw.amplitude]
    ring
  show c * StepLaw.amplitude (StepLaw.ofFamily φ) (T.E / T.η₃) ^ 2 * (c * ε / T.η₃) *
    Real.exp (-(T.κ * q / 2 ^ 7)) ≤ T.CE * ε * Real.exp (-(T.κ * q / 2 ^ 7))
  rw [e]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hε.le) he
end TorusFreezing
end YangMills.Construction
end
