import YangMills.Construction.SummableBoundsOfTheFlow.FreezingOfABlockExpansionProof
import YangMills.Construction.SummableBoundsOfTheFlow.FreezingOfTheGapObservable
import YangMills.Construction.SummableBoundsOfTheFlow.GapObservableIsAdmitted
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusFreezing
open BlockAverages ColdStepAtMirrorFrames TorusComparison SummableBounds
namespace GapObservable
theorem exists_shortPairing_of_agreeOnBall (hPair : bondsNearCellsPairStatement) {L t n₀ q : ℕ}
    (hOdd : Odd L) (hn₀ : 1 ≤ n₀) {F F' : BlockFrame} (hTor : IsCubicTopTorus L t n₀ F)
    (hTor' : IsCubicTopTorus L t n₀ F') {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
    {Y : F.Cell} {Y' : F'.Cell} (hAgree : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (j : ι → ↥(chordBonds (finiteCells F)))
      (j' : ι → ↥(chordBonds (finiteCells F'))), IsShortPairing Y Y' q j j' := by apply _root_.YangMills.Construction.TorusFreezing.exists_shortPairing_of_agreeOnBall <;> assumption
end GapObservable
open GapObservable in
theorem gapObservableExpectationDecouples_holds (hJoin : joinAtLoweredConstantsStatement)
    (hPair : bondsNearCellsPairStatement) (hDec : expectationDecouples)
    (hAdm : gapObservableIsAdmissible) : gapObservableExpectationDecouples := by
  refine hJoin ExpectationDecouples GapObservableIsAdmissible GapObservableExpectationDecouples (fun _ => 0)
    (fun _ => 0) hDec hAdm ?_
  intro T c c' hc hc' hOdd hn hE hη hη1 _ _ hFz hAd N
  obtain ⟨CN, hCN⟩ := hAd N
  refine ⟨c * (1 + T.E / T.η₃) ^ 2 * CN, ?_⟩
  intro t x s φ F F' V V' Y Y' q hx hs hs1 hφ hTF hTF' hV hV' hAg hq
  obtain ⟨ι, _, _, j, j', hpair⟩ := exists_shortPairing_of_agreeOnBall hPair hOdd hn hTF hTF' hAg
  obtain ⟨adm, hd, hd'⟩ := hCN t x s φ F F' V V' Y Y' q ι j j' hx hs hs1 hφ hTF hTF' hV hV' hAg hpair hq
  have hα : 0 ≤ CN * (x ^ N)⁻¹ := (abs_nonneg _).trans adm.expectation_sub_le
  have fz := hFz t x s (TorusComparison.StepLaw.ofFamily φ) F F' V V' Y Y' q ι j j' (CN * (x ^ N)⁻¹) _ _ hx hs
    hs1 hφ hTF hTF' hV hV' hAg hpair hα hd hd' adm
  refine fz.trans (le_of_eq ?_)
  show c * TorusComparison.StepLaw.amplitude (TorusComparison.StepLaw.ofFamily φ) (T.E / T.η₃) ^ 2 *
    (CN * (x ^ N)⁻¹) * Real.exp (-(T.κ * q / 2 ^ 7)) = c * (1 + T.E / T.η₃) ^ 2 * CN * (x ^ N)⁻¹ *
      Real.exp (-(T.κ * q / 2 ^ 7))
  simp only [TorusComparison.StepLaw.amplitude]
  ring
end YangMills.Construction.TorusFreezing
end
