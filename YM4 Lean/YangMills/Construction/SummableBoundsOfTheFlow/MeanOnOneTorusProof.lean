import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.SummableBoundsOfTheFlow.BondsOfACellAreFew
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOnOneTorusAtGivenParameters
import YangMills.Construction.SummableBoundsOfTheFlow.ParametersMatchAtRaisedConstants
import YangMills.Construction.SummableBoundsOfTheFlow.SumOfTheWeightsAboutACell
import YangMills.Construction.SummableBoundsOfTheFlow.TransportOfAFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockMeans
open MeasureTheory BlockAverages ColdStepAtMirrorFrames Interpolation Cumulants CellCounting Estimates SummableBounds
set_option maxHeartbeats 400000 in
theorem singleTorusMean_holds (hAt : singleTorusMeanAtSlotsStatement)
    (hRaised : joinAtLoweredConstantsStatement) (hJ : EventuallyInParametersCombines)
    (hFr : interpolatedFramesStatement) (hTr : transportBoundsStatement) (hFam : TransportAtEveryScale)
    (hThird : thirdOrderCovarianceBound) (hCl : blockExpansionThirdOrderStatement) (hEx : CellExponentsBounded)
    (hCum : meanCumulantsAtTopStatement) (hW : ExpDecaySumBounded) (hBonds : cellBondsCardStatement) :
    singleTorusMeanStatement := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cq, Cz, Cr, hFr⟩ := hFr
  obtain ⟨Cg, Ck, hCg, -, hTr⟩ := hTr
  obtain ⟨Cth, hCth, hCl⟩ := hCl
  choose! Bf hBf using hCum
  choose! Wf hWf using hW
  have hn₂ : EventuallyInParameters fun T => 2 ≤ T.n₀ := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨2, fun _ h => ⟨0, fun _ _ => ⟨0, fun _ _ => h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hcoupling : EventuallyInParameters fun T => 1 ≤ T.coupling := fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun _ _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨1, one_pos,
      fun _ _ _ _ _ => ⟨0, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨1, fun _ h => h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hall := join _ _ hFr (join _ _ hTr (join _ _ hFam (join _ _ hThird (join _ _ hCl (join _ _ hEx
    (join _ _ hn₂ hcoupling))))))
  have hordered := weaken _ (fun T => _ ∧ T.IsOrdered) (fun T hD h => ⟨h, hD⟩) hall
  have htriv : EventuallyInParameters fun _ => True := weaken _ _ (fun _ _ _ => trivial) hn₂
  refine hRaised _ (fun _ => True) SingleTorusMeanBoundsAt (fun c => c)
    (fun T => singleTorusMeanConstant T.Cs T.E T.η₃
      (Bf (4 * T.L ^ 4) (1 + (centredCube T.L).card) T.κ T.chainParams.lam fun q => |Cz (momentParameters T) q|)
      (Wf (4 * T.L ^ 4) (2 ^ 6 * T.κ)) (Cg (rateParameters T)) |Cq (momentParameters T) 1|
      (1 + ∑ q ∈ Finset.range 7, Cth T q) ((centredCube T.L).card : ℝ)) hordered htriv ?_
  intro T c c' hc hc' hodd hn₁ hE hη hη₁ hG hK hP _
  obtain ⟨⟨hF, hT, hFm, hTh, hC, hB, hn, hy⟩, hD⟩ := hP
  generalize hT₁ : ({ T with Cs := c, CE := c' } : StepParameters) = T₁ at hF hT hFm hTh hC hB hn hy hD
  have hT0 : ({ T with Cs := c, n₀ := 0, CE := 0, coupling := 0 } : StepParameters) =
      { T₁ with n₀ := 0, CE := 0, coupling := 0 } := by
    subst hT₁
    rfl
  rw [hT0] at hK
  set T₀ : StepParameters := { T₁ with n₀ := 0, CE := 0, coupling := 0 } with hT₀
  have e1 : momentParameters T₀ = momentParameters T₁ := rfl
  have e2 : rateParameters T₀ = rateParameters T₁ := rfl
  rw [e1, e2] at hK
  have hc₁ : 1 ≤ T₁.Cs := by
    rw [← hT₁]
    exact hc
  have hκ : 0 < T₁.κ := hD.κ_pos
  have hlam : 0 < T₁.chainParams.lam := hD.chain_admissible.positivity.2.2.1
  obtain ⟨hBs0, hBs⟩ := hBf (4 * T₁.L ^ 4) (1 + (centredCube T₁.L).card) T₁.κ T₁.chainParams.lam hκ hlam
  obtain ⟨hWs0, hWs⟩ := hWf (4 * T₁.L ^ 4) (2 ^ 6 * T₁.κ) (by positivity)
  have hsmall : ∀ (F : BlockFrame) (star : Bool) (x : ℝ) (m : ℕ) (α β : ℝ) (φ h : LocalFamily)
      (V : F.GaugeField F.top),
      LawAtTop.LawAtTop star T₁.a T₁.chainParams.ρA x m (T₁.σ / 64) T₁.chainParams.lam T₁.κ α β T₁.p
        (fun q => |Cz (momentParameters T₁) q|) (4 * T₁.L ^ 4) (1 + (centredCube T₁.L).card) φ h V →
      ∀ Y : F.Cell,
      MeanCumulantBounds star T₁.a T₁.chainParams.ρA x m (T₁.σ / 64) T₁.κ T₁.p φ h V Y
        ((Bf (4 * T₁.L ^ 4) (1 + (centredCube T₁.L).card) T₁.κ T₁.chainParams.lam
          fun q => |Cz (momentParameters T₁) q|) * (α * β))
        ((Bf (4 * T₁.L ^ 4) (1 + (centredCube T₁.L).card) T₁.κ T₁.chainParams.lam
          fun q => |Cz (momentParameters T₁) q|) * (α * β ^ 2))
        ((Bf (4 * T₁.L ^ 4) (1 + (centredCube T₁.L).card) T₁.κ T₁.chainParams.lam
          fun q => |Cz (momentParameters T₁) q|) * (α * β ^ 3)) :=
    fun F star x m α β φ h V hL Y => hBs F star T₁.a T₁.chainParams.ρA x m (T₁.σ / 64) α β T₁.p _ φ h V hL Y
  have hweights : ∀ (t : ℕ) (F : BlockFrame), IsCubicTopTorus T₁.L t T₁.n₀ F → ∀ Y : F.Cell,
      ∑ b : ↥(chordBonds (finiteCells F)),
          Real.exp (-(2 ^ 6 * T₁.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) ≤
        Wf (4 * T₁.L ^ 4) (2 ^ 6 * T₁.κ) := fun t F hF' Y => by
    obtain ⟨hFL, -, n, hside, hn'⟩ := hF'
    have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
      rw [hside]
      exact hn.trans hn'
    have hoddF : Odd F.blockSide := by
      rw [hFL]
      exact hD.odd_L
    exact hWs F ↥(chordBonds (finiteCells F)) (fun b => enclosingCell b.1.1)
      (fun z => (hBonds F hoddF hs2 z).trans (by rw [hFL])) Y
  have hOnParameters : SingleTorusMeanHypotheses T₁ (Cq (momentParameters T₁)) (Cz (momentParameters T₁))
      (Cr (momentParameters T₁)) (Cg (rateParameters T₁)) (Ck (rateParameters T₁)) (Cth T₀)
      (Bf (4 * T₁.L ^ 4) (1 + (centredCube T₁.L).card) T₁.κ T₁.chainParams.lam fun q => |Cz (momentParameters T₁) q|)
      (Wf (4 * T₁.L ^ 4) (2 ^ 6 * T₁.κ)) :=
    ⟨⟨hD, hn, hy, hc₁, hF, hT, hB⟩, hCg _, hBs0 _ fun q => abs_nonneg _, hWs0, hCth T₀, hFm, hTh _ (hCth T₀), hC,
      hsmall, hweights⟩
  have res := hAt T₁ (Cq (momentParameters T₁)) (Cz (momentParameters T₁)) (Cr (momentParameters T₁))
    (Cg (rateParameters T₁)) (Ck (rateParameters T₁)) (Cth T₀)
    (Bf (4 * T₁.L ^ 4) (1 + (centredCube T₁.L).card) T₁.κ T₁.chainParams.lam fun q => |Cz (momentParameters T₁) q|)
    (Wf (4 * T₁.L ^ 4) (2 ^ 6 * T₁.κ)) T.CE hOnParameters hK
  subst hT₁
  exact res
end YangMills.Construction.BlockMeans
end
