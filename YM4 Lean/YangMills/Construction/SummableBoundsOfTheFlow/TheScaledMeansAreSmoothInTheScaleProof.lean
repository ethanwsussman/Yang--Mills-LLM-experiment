import YangMills.Construction.SummableBoundsOfTheFlow.ACutIsSmoothThroughItsRim
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfATameObservable
import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessOfTheDensitiesIsSmallProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansAreSmoothInTheScale
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansAreTameMeans
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Estimates Set Filter
open scoped Topology
namespace ScaledVariables
namespace SmoothInScale
variable {F : BlockFrame}
theorem eventually_isSmallCurvature_bondSpread {k : ℕ} (hF : ∀ i, F.extent i ≠ 0) (s : ℝ)
    (V : F.GaugeField F.top) (hV : IsSmallCurvature s V) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), IsSmallCurvature s (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) := by apply _root_.YangMills.SharedProofs.p8866 <;> assumption
theorem IsTameOnScales.mono_bound {s ρ lo hi D D' : ℝ}
    {O : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    (h : IsTameOnScales s ρ lo hi D O) (hD : D ≤ D') : IsTameOnScales s ρ lo hi D' O :=
  ⟨h.contDiffAt, fun V' hV m i c X γ ζ hr hX a b d =>
    (h.deriv_le V' hV m i c X γ ζ hr hX a b d).trans hD⟩
end SmoothInScale
open SmoothInScale in
theorem scaledMeansSmoothInScale_proof (hM : TiltedMeanDerivSmoothInScale)
    (hT : scaledMeansTameStatement) (hC : CutoffWeightContDiff) :
    scaledMeansSmoothInScale := by
  unfold scaledMeansSmoothInScale ForallSmoothObservables
  refine EventuallyOrdered.mono hT ?_
  intro T hTd hn gT e
  obtain ⟨l₀, h0, g⟩ := gT e
  refine ⟨l₀, 1, h0, one_pos, fun l₁ h1 hle t f F V Y law K Ob k c X hf hF hV _ hK hO hX hk l hl hll => ?_⟩
  have hS := g l₁ h1 hle t f F law hf hF
  have hext : ∀ i, F.extent i ≠ 0 := by
    obtain ⟨-, -, m, hm, hm₀⟩ := hF
    intro i
    rw [hm i]
    omega
  have hρ : 0 < T.ballRadius := by
    have := hTd.σ_pos
    unfold StepParameters.ballRadius
    positivity
  have hlo : 0 < l / 2 := by positivity
  have hlol : l / 2 < l := by linarith
  have hlhi : l < 2 * l₁ := by linarith
  obtain ⟨D₁, hD₁, hA⟩ := hS.exponent_tame (l / 2) hlo
  obtain ⟨D₂, hD₂, hOb⟩ := hS.observable_tame K Y Ob hK hO (l / 2) hlo
  have hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutoffWeight T.ballRadius T.p) :=
    hC T.ballRadius T.p hρ hTd.cutoff
  have hwp : ∀ u, u < T.ballRadius → 0 < cutoffWeight T.ballRadius T.p u := by
    intro u hu
    unfold cutoffWeight cutoffFactor
    rw [if_pos (max_lt hu hρ)]
    exact Real.exp_pos _
  have hw0 : ∀ u, T.ballRadius ≤ u → cutoffWeight T.ballRadius T.p u = 0 := by
    intro u hu
    unfold cutoffWeight cutoffFactor
    rw [if_neg (not_lt.2 (hu.trans (le_max_left _ _)))]
  have hq : Continuous (gaussianPart (F := F) T.lam) := by
    unfold gaussianPart
    fun_prop
  have main := hM F (5 / 4 * T.σ) T.ballRadius (l / 2) (2 * l₁) (max D₁ D₂) l
    (cutoffWeight T.ballRadius T.p) (gaussianPart T.lam) (lawExponent T.a T.ρA T.lam f law) Ob V k c X
    hext hρ hlo hlol hlhi (le_max_of_le_left hD₁) hw hwp hw0 hq
    (IsTameOnScales.mono_bound hA (le_max_left _ _)) (IsTameOnScales.mono_bound hOb (le_max_right _ _))
    hV hX hk
  refine main.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hlol hlhi] with l' hl'
  have hl'0 : 0 < l' := hlo.trans hl'.1
  have ev : (fun τ : Fin k → ℝ => observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l'
      (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) =ᶠ[𝓝 0]
      fun τ => tiltedMean (cutoffWeight T.ballRadius T.p) (gaussianPart T.lam)
        (lawExponent T.a T.ρA T.lam f law) Ob l' (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) := by
    filter_upwards [eventually_isSmallCurvature_bondSpread hext _ V hV c X] with τ hτ
    exact hS.mean_eq _ l' Ob hτ hl'0 hl'.2.le
  unfold bondDeriv
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ ev k).self_of_nhds]
end ScaledVariables
end YangMills.Construction
end
