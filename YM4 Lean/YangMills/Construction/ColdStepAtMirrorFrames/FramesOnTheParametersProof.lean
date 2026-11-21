import YangMills.Construction.ColdStepAtMirrorFrames.CouplingFloorOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.FramesOnTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem frameBoundsEventually_holds (hW : frameBoundsStatement) (hY : CouplingThreshold) :
    FrameBoundsEventually := by
  intro a ha
  refine ⟨2 ^ 40, fun L hL hL0 c hc => ?_⟩
  obtain ⟨Cf, C, σ₀, hCf, hC1, hσ₀, main⟩ := hW a L c ha hL hL0 hc
  have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  have hσA : 0 < c.σA := hc.positivity.2.2.2.1
  refine ⟨max Cf C, fun Ct hCt => ?_⟩
  refine ⟨min (c.δ₂ / 2 ^ 14) 1, lt_min (by positivity) one_pos, fun κ hκ hκ₀ => ?_⟩
  refine ⟨1, one_pos, fun η₃ _ _ _ => ?_⟩
  refine ⟨0, fun k _ => ?_⟩
  refine ⟨min σ₀ (min (1 / (64 * L * (C + 1))) (min (1 / (2 * (C + 5 * L))) (min (4 / 5 * c.σA) 1))),
    lt_min hσ₀ (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) one_pos))),
    fun σ hσ hσ₁ => ?_⟩
  refine fun p _ => ⟨0, fun Cs _ => ?_⟩
  refine fun E _ => ⟨64, fun n₀ hn₀ => ⟨0, fun CE _ => ?_⟩⟩
  obtain ⟨y₀, hy₀⟩ := hY Cf C c.δ₂ κ σ 0 hδ₂ hκ ((hκ₀.trans (min_le_left _ _))) hσ
  refine ⟨max y₀ (max 1 (2 / a)), fun y₁ hy₁ => ?_⟩
  have s0 : σ ≤ σ₀ := hσ₁.trans (min_le_left _ _)
  have s1 : σ ≤ 1 / (64 * L * (C + 1)) := hσ₁.trans ((min_le_right _ _).trans (min_le_left _ _))
  have s2 : σ ≤ 1 / (2 * (C + 5 * L)) :=
    hσ₁.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have s3 : σ ≤ 4 / 5 * c.σA := hσ₁.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have s4 : σ ≤ 1 := hσ₁.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hy1 : y₀ ≤ y₁ := (le_max_left _ _).trans hy₁
  have hy2 : 1 ≤ y₁ := ((le_max_left _ _).trans (le_max_right _ _)).trans hy₁
  have hy3 : 2 / a ≤ y₁ := ((le_max_right _ _).trans (le_max_right _ _)).trans hy₁
  have ha0 : 0 < a := by linarith
  refine ⟨Cf, C, hCf, hC1, (le_max_left _ _).trans hCt, (le_max_right _ _).trans hCt, hL0, hn₀,
    hκ₀.trans (min_le_right _ _), s4, ?_, ?_, ?_, hy2, ?_, ?_⟩
  · change C * σ + σ / 64 ≤ 1 / (64 * (L : ℝ))
    have h1 : σ * (64 * L * (C + 1)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at s1
      exact s1
    have h2 : (C * σ + σ / 64) * (64 * L) ≤ 1 := by
      nlinarith
    rw [le_div_iff₀ (by positivity)]
    exact h2
  · change C * σ + 5 * (L : ℝ) * (σ / 64) ≤ 1 / 2
    have h1 : σ * (2 * (C + 5 * L)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at s2
      exact s2
    nlinarith
  · change 5 / 4 * σ ≤ c.σA
    linarith
  · change 2 ≤ a * y₁
    rw [div_le_iff₀ ha0] at hy3
    linarith
  · intro t x F V hx hF hV
    have hx0 : y₀ ≤ x := hy1.trans hx
    obtain ⟨_, m16, g1, g2, g3, _⟩ := hy₀ x hx0
    exact main κ σ x (frameRadius x) t n₀ hκ (hκ₀.trans (min_le_left _ _)) hσ s0
      (hy2.trans hx) m16 hn₀ g1 g2 g3 F V hF hV
end YangMills.Construction.ColdStepAtMirrorFrames
end
