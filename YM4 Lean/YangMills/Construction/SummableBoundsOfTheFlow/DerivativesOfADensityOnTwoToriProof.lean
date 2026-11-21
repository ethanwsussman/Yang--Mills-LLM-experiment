import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfADensityOnTwoTori
import YangMills.Construction.SummableBoundsOfTheFlow.LinesOfTwoTops
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace DerivativeInterpolation
theorem densityDerivDiffLeOnTwoTori_holds (hLines : DerivDiffLeOfCloseAlongLines)
    (hAgree : SmallCurvatureAlongLineAndAgreeOn) : DensityDerivDiffLeOnTwoTori := by
  obtain ⟨C, hC, hb⟩ := hLines
  refine ⟨C, hC, ?_⟩
  intro L t n₀ σ M₀ M₃ g F F' Y Y' V V' r k h X hσ hM₀ hM₃ hk1 hk2 hF hF' hg h3 hclose hV hV' hA hbox hX
  have hτ : 0 < σ / 64 := by positivity
  have hnorm : ∀ ς : Fin k → ℝ, (∀ l, ς l = 1 ∨ ς l = -1) → ∀ l, ‖ς l • X l‖ = 1 := by
    intro ς hς l
    rw [norm_smul, hX l, mul_one]
    rcases hς l with e | e <;> simp [e]
  have hsmall : ∀ {F'' : BlockFrame} (W : F''.GaugeField F''.top) (c : Fin k → F''.Site F''.top × Fin 4)
      (ς : Fin k → ℝ), (∀ l, ς l = 1 ∨ ς l = -1) → IsSmallCurvature (9 / 8 * σ) W →
      ∀ s : ℝ, |s| ≤ σ / 64 → IsSmallCurvature (5 / 4 * σ) (alongLine c (fun l => ς l • X l) s W) := by
    intro F'' W c ς hς hW s hs
    have h1 := hAgree.1 F'' W k c (fun l => ς l • X l) s (9 / 8 * σ)
      (fun l => (hnorm ς hς l).le) hW
    intro p hp
    refine (h1 p hp).trans_le ?_
    have hk : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
    have : 4 * (k : ℝ) * |s| ≤ 4 * 2 * (σ / 64) := by
      have h0 : (0 : ℝ) ≤ |s| := abs_nonneg s
      nlinarith
    linarith
  have key := hb F F' (g F Y) (g F' Y') V V' k (bondsAt Y h) (bondsAt Y' h) X (σ / 64) M₀ M₃ hk1 hk2
    hτ hM₀ hM₃ ?_
  · exact key
  · intro ς hς
    refine ⟨⟨fun s hs => hg.smooth F hF Y _ (hsmall V _ ς hς hV s hs), fun s hs e => ?_⟩,
      ⟨fun s hs => hg.smooth F' hF' Y' _ (hsmall V' _ ς hς hV' s hs), fun s hs e => ?_⟩, fun s hs => ?_⟩
    · exact h3 F Y _ _ _ hF (hsmall V _ ς hς hV s hs) (fun l => hnorm ς hς (e l))
    · exact h3 F' Y' _ _ _ hF' (hsmall V' _ ς hς hV' s hs) (fun l => hnorm ς hς (e l))
    · exact hclose _ _ (hsmall V _ ς hς hV s hs) (hsmall V' _ ς hς hV' s hs)
        (hAgree.2 F F' V V' Y Y' r k h _ s hA hbox)
end DerivativeInterpolation
end YangMills.Construction
end
