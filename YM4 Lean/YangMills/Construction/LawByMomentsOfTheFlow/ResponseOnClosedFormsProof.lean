import YangMills.Construction.LawByMomentsOfTheFlow.ChainObeysTheFirstLevelProof
import YangMills.Construction.LawByMomentsOfTheFlow.ResponseOnClosedForms
import YangMills.Construction.ResponseInTheExpansion.TheResponseContractsCurvature
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction.ClosedFormResponse
open BlockAverages (BlockFrame expUnit imaginaryQuaternions UnitQuaternion unitStep IsBondAnalyticAt rotatedField
  IsAdmissibleAmbient IsCold HasColdMinimizer HasRegularCellShares HasRegularCoordinates IsOrthantRegular
  IsMinimizingChart chordBonds minimizingCoordinates minimizingBondCoordinate IsCrossingBond enclosingCell siteCoords
  plaquetteDefect flatTopVanishingStatement)
open FrameTransfer (torusToFrame frameToTorus torusToFrame_add torusToFrame_unitStep torusToFrame_frameToTorus
  frameToTorus_torusToFrame torusToFrame_siteOfInt intCast_cast_of_eq plaquetteHolonomy_readAtLevel)
open TorusFields (TorusBond TorusField TorusSite TorusPlaquette holonomy sq_norm_unitQuaternion_sub_one plaquetteEnergy
  trivialField siteOfInt readAtLevel plaquettesIn torusFrame)
open WeightedResponses (unitGenerator curl responseMap responseKernel)
open RenormalizationStepParameters (ParameterAssignment)
open ColdStepAtMirrorFrames (finiteCells MinimizingChartUnique MinimalActionGaugeCovariance SiteDecomposition bondDeriv
  torusCoordinate)
open TorusLumps (parentBlock)
open TorusFrame (period_torusFrame)
section Response
variable {n : ℕ} [NeZero n]
theorem responseMap_latticeGradient {Tb : ParameterAssignment} (hD : Tb.Admissible) (hFlat : flatTopVanishingStatement)
    (hOne : MinimizingChartUnique) (hGauge : MinimalActionGaugeCovariance) (hBlock : SiteDecomposition)
    (u : ℕ) (hn : 64 ≤ n) (φ : TorusSite n → ℝ) :
    responseMap Tb.coupling Tb.ρA Tb.side u (ResponseInTheExpansion.latticeGradient φ) =
      ResponseInTheExpansion.latticeGradient fun x => φ (parentBlock Tb.side x) := by apply _root_.YangMills.SharedProofs.p10520 <;> assumption
end Response
section ClosedForms
variable {m : ℕ}
private theorem curl_eq_zero_of_plaquettesIn [NeZero m] (B : TorusBond m → ℝ)
    (h : ∀ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), curl B p = 0) (p : TorusPlaquette m) :
    curl B p = 0 := by apply _root_.YangMills.SharedProofs.p30341 <;> assumption
private theorem curl_sub_form (A A' : TorusBond m → ℝ) (p : TorusPlaquette m) :
    curl (A - A') p = curl A p - curl A' p := by
  simp only [curl, Pi.sub_apply]
  ring
private theorem responseMap_sub_form (a ρ : ℝ) (L u : ℕ) [NeZero L] {n : ℕ} [NeZero n] (A A' : TorusBond n → ℝ) :
    responseMap a ρ L u (A - A') = responseMap a ρ L u A - responseMap a ρ L u A' := by
  funext b
  simp only [responseMap, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
end ClosedForms
theorem responseMapClosedForms_holds (hFlat : flatTopVanishingStatement) (hOne : MinimizingChartUnique)
    (hGauge : MinimalActionGaugeCovariance) (hBlock : SiteDecomposition)
    (hC : ResponseInTheExpansion.ResponseContractsCurvatureStatement) : MomentLaw.responseMapClosedFormsStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, h⟩ := hC a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hL hL₀ T hTa hTL hD hS hH hr hC₀ => ?_⟩
  obtain ⟨y₀, hy⟩ := h L hL hL₀ T hTa hTL hD hS hH hr hC₀
  refine ⟨y₀, fun y hy₀ hrow hW => ?_⟩
  intro u n _ hn
  have hcon := hy y hy₀ hrow hW u n hn
  have closed : ∀ A : TorusBond n → ℝ, (∀ p, curl A p = 0) → ∀ p,
      curl (responseMap T.coupling T.ρA (T.stepParameters y).side u A) p = 0 := by
    intro A hA
    refine curl_eq_zero_of_plaquettesIn _ fun p hp => ?_
    have h0 := hcon A 0 (fun p _ => by rw [hA p, abs_zero]) p hp
    rw [zero_div] at h0
    exact abs_nonpos_iff.1 h0
  refine ⟨fun φ => responseMap_latticeGradient hD hFlat hOne hGauge hBlock u hn φ, ?_, ?_⟩
  · intro v p
    refine closed _ (fun q => ?_) p
    simp only [curl, MomentLaw.constantOneForm]
    ring
  · intro A A' hA p
    have h1 := closed (A - A') (fun q => by rw [curl_sub_form, hA q, sub_self]) p
    rw [responseMap_sub_form, curl_sub_form] at h1
    linarith
end YangMills.Construction.ClosedFormResponse
end
