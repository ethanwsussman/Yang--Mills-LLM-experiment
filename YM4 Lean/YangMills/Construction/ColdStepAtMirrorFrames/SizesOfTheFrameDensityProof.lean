import YangMills.Construction.ColdStepAtMirrorFrames.CouplingFloorOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.DensityOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.SizesOfTheFrameDensityForm
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
private lemma isSmallCurvature_mono {j : ℕ} {s s' : ℝ} (h : s ≤ s') {V : F.GaugeField j}
    (hV : IsSmallCurvature s V) : IsSmallCurvature s' V :=
  fun p hp => lt_of_lt_of_le (hV p hp) h
theorem frameDensityBoundsEventually_holds (hW : frameBoundsStatement)
    (hD : frameDensityBoundsStatement) (hC : CouplingThreshold) :
    frameDensityBoundsEventually := by
  intro a ha
  refine ⟨2 ^ 40, fun L hL hLe c hc => ?_⟩
  obtain ⟨Cf, C, σ₀, hF⟩ := hW a L c ha hL hLe hc
  obtain ⟨Ct₀, σ₁, hCt₀, hσ₁, hσ₁₀, hdens⟩ := hD a L c Cf C σ₀ ha hL hLe hc hF
  have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨Ct₀, fun Ct hCt => ⟨c.δ₂ / 2 ^ 14, by positivity, fun κ hκ hκ' => ⟨1, one_pos,
    fun η₃ _ _ _ => ⟨0, fun m _ => ⟨σ₁, hσ₁, fun σ hσ hσ' p hp => ⟨0, fun Cs _ E hE =>
      ⟨64, fun n₀ hn₀ => ⟨0, fun CE _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩
  obtain ⟨y₀, hy⟩ := hC Cf C c.δ₂ κ σ 0 hδ₂ hκ hκ' hσ
  refine ⟨max y₀ 1, fun g hg t x hx => ?_⟩
  have hxg : g ≤ x := hx
  have hx0 : y₀ ≤ x := le_trans (le_trans (le_max_left _ _) hg) hxg
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) hg) hxg
  obtain ⟨-, h16, hgap, hxω, hxe, -⟩ := hy x hx0
  have H := hdens κ (κ / 2 ^ 10) σ x (frameRadius x) t n₀ hκ hκ' rfl hσ hσ' hx1 h16 hn₀ hgap hxω hxe
  have hsmall : ∀ {j : ℕ} {G : BlockFrame} {V : G.GaugeField j}, IsSmallCurvature (9 / 8 * σ) V →
      IsSmallCurvature (5 / 4 * σ) V := fun hV => isSmallCurvature_mono (by linarith) hV
  have hmul : ∀ u : ℝ, 0 ≤ u → Ct₀ * x * Real.exp (-(c.δ₂ / 8 * frameRadius x)) * u ≤
      Ct * x * Real.exp (-(c.δ₂ / 8 * frameRadius x)) * u := fun u hu => by
    have hE := Real.exp_pos (-(c.δ₂ / 8 * frameRadius x))
    have hxp : 0 ≤ x * Real.exp (-(c.δ₂ / 8 * frameRadius x)) * u := by positivity
    nlinarith
  have hdiv : ∀ w : ℝ, 0 < w → Ct₀ * x * Real.exp (-(c.δ₂ / 8 * frameRadius x)) / w ≤
      Ct * x * Real.exp (-(c.δ₂ / 8 * frameRadius x)) / w := fun w hw => by
    simpa [div_eq_mul_inv] using hmul w⁻¹ (inv_nonneg.mpr hw.le)
  have hw : ∀ u : ℝ, 0 < torusDecayFactor L (κ / 2 ^ 10) u := fun u =>
    mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
  refine ⟨⟨fun F hF Y V hV => H.localDensity.smooth F hF Y V (hsmall hV),
      fun F hF Y V γ hV => H.localDensity.gauge_invariant F hF Y V γ (hsmall hV),
      fun F hF Y h V hV => H.localDensity.translation_invariant F hF Y h V (hsmall hV)⟩,
    fun F hF Y V hV => ?_, fun F hF Y V k e X hV h1 h3 hX => ?_,
    fun F F' hF hF' Y Y' V V' r k h X hV hV' hA hk hb hX => ?_,
    fun F hF hs Y V hV => H.eq_zero F hF false (Or.inr hs) Y V (hsmall hV)⟩
  · have := H.abs_le F hF Y V (hsmall hV)
    have h2 := hmul 1 zero_le_one
    simp only [mul_one] at h2
    exact le_trans this h2
  · exact le_trans (H.derivDecay F hF Y V k e X (hsmall hV) h1 h3 hX) (hdiv _ (hw _))
  · exact le_trans (H.localOnTori F F' hF hF' Y Y' V V' r k h X (hsmall hV) (hsmall hV') hA hk hb hX)
      (hdiv _ (hw _))
end YangMills.Construction.ColdStepAtMirrorFrames
end
