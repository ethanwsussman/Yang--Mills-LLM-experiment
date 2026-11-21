import YangMills.Construction.SummableBoundsOfTheFlow.FreezingOfABlockExpansionProof
import YangMills.Construction.SummableBoundsOfTheFlow.FreezingOfTheWeightPart
import YangMills.Construction.SummableBoundsOfTheFlow.WeightPartIsAdmitted
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusFreezing
open BlockAverages ColdStepAtMirrorFrames TorusComparison SummableBounds
namespace Remainder
theorem exists_shortPairing_of_agreeOnBall (hPair : bondsNearCellsPairStatement) {L t n₀ q : ℕ}
    (hOdd : Odd L) (hn₀ : 1 ≤ n₀) {F F' : BlockFrame} (hTor : IsCubicTopTorus L t n₀ F)
    (hTor' : IsCubicTopTorus L t n₀ F') {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
    {Y : F.Cell} {Y' : F'.Cell} (hAgree : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (j : ι → ↥(chordBonds (finiteCells F)))
      (j' : ι → ↥(chordBonds (finiteCells F'))), IsShortPairing Y Y' q j j' := by apply _root_.YangMills.Construction.TorusFreezing.exists_shortPairing_of_agreeOnBall <;> assumption
end Remainder
open Remainder in
theorem remainderExpectationDecouples_holds (hJoin : joinAtLoweredConstantsStatement)
    (hPair : bondsNearCellsPairStatement) (hDec : expectationDecouples)
    (hAdm : remainderIsAdmissible) : remainderExpectationDecouples := by
  refine hJoin ExpectationDecouples RemainderIsAdmissible RemainderExpectationDecouples (fun c => c * c)
    (fun _ => 0) hDec hAdm ?_
  intro T c c' hc hc' hOdd hn hE hη hη1 hG _ hFz hAd t x s τ F F' V V' Y Y' q hx hs hs1 hτ hτ1 hTF hTF'
    hV hV' hAg
  obtain ⟨ι, _, _, j, j', hpair⟩ := exists_shortPairing_of_agreeOnBall hPair hOdd hn hTF hTF' hAg
  obtain ⟨adm, hd, hd'⟩ := hAd t x s τ F F' V V' Y Y' q ι j j' hx hs hs1 hτ hτ1 hTF hTF' hV hV' hAg hpair
  have hα : 0 ≤ c := (abs_nonneg _).trans adm.expectation_sub_le
  have fz := hFz t x s (TorusComparison.StepLaw.ofWeight τ) F F' V V' Y Y' q ι j j' c _ _ hx hs hs1
    ⟨hτ, hτ1⟩ hTF hTF' hV hV' hAg hpair hα hd hd' adm
  refine fz.trans ?_
  have hExp : 0 ≤ Real.exp (-(T.κ * q / 2 ^ 7)) := (Real.exp_pos _).le
  have hAmp : c * TorusComparison.StepLaw.amplitude (TorusComparison.StepLaw.ofWeight τ) T.energyRatio ^ 2 * c =
      c * c := by
    simp [TorusComparison.StepLaw.amplitude]
  show c * TorusComparison.StepLaw.amplitude (TorusComparison.StepLaw.ofWeight τ) T.energyRatio ^ 2 * c *
    Real.exp (-(T.κ * q / 2 ^ 7)) ≤ T.Cs * Real.exp (-(T.κ * q / 2 ^ 7))
  rw [hAmp]
  exact mul_le_mul_of_nonneg_right hG hExp
end YangMills.Construction.TorusFreezing
end
