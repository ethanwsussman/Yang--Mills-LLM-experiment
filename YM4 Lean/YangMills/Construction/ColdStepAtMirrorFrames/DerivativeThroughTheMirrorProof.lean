import YangMills.Construction.ColdStepAtMirrorFrames.AnalyticAlongFields
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeThroughTheMirror
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorImagesOfABond
import YangMills.Construction.ColdStepAtMirrorFrames.MixedDerivativeAlongFields
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace DerivThroughReflection
theorem isBondAnalyticAt_comp_reflectedField (hmv : ReflectedFieldOfTranslatedTop)
    (han : AnalyticAlongDirectionFields) (hJ : reflectedImagesOfBond) {m : ℕ} (hm : 2 ≤ m)
    (hs : ∀ i, 2 * m + 2 < F.extent i) (y : F.Cell)
    (V : F.GaugeField F.top) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : (reflectedFrame F m).GaugeField (reflectedFrame F m).top → E)
    (hG : IsBondAnalyticAt G (reflectedField m y V)) :
    IsBondAnalyticAt (fun V' => G (reflectedField m y V')) V := by
  intro k c X
  choose J hcard hzero _ _ _ using fun l => hJ F m y (c l) hm hs
  have h := han (reflectedFrame F m) (reflectedFrame F m).top k E G (reflectedField m y V) J
    (fun l => reflectedDirection m y V (c l) (X l)) (fun l z i hz => hzero l V (X l) z i hz) hG
  have e : (fun σ : Fin k → ℝ => G (reflectedField m y (rotatedField (bondSpread c X σ) V))) =
      fun τ => G (leftTranslate (fun z i => ∑ l, τ l • reflectedDirection m y V (c l) (X l) z i)
        (reflectedField m y V)) := by
    funext τ
    rw [← hmv F m y V k c X τ (by omega)]
    rfl
  change AnalyticAt ℝ (fun σ : Fin k → ℝ => G (reflectedField m y (rotatedField (bondSpread c X σ) V))) 0
  rw [e]
  exact h
theorem bondDeriv_comp_reflectedField (hmv : ReflectedFieldOfTranslatedTop)
    (hmix : MixedDerivAlongDirectionFields) {m : ℕ} (hm : 0 < m) (y : F.Cell) (V : F.GaugeField F.top)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (G : (reflectedFrame F m).GaugeField (reflectedFrame F m).top → E)
    (hG : IsBondAnalyticAt G (reflectedField m y V)) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (J : Fin k → Finset ((reflectedFrame F m).Cell × Fin 4))
    (hzero : ∀ l z i, (z, i) ∉ J l → reflectedDirection m y V (c l) (X l) z i = 0) :
    bondDeriv (fun V' => G (reflectedField m y V')) V c X =
      ∑ r ∈ Fintype.piFinset J, bondDeriv G (reflectedField m y V) r
        (fun l => reflectedDirection m y V (c l) (X l) (r l).1 (r l).2) := by
  have h := hmix (reflectedFrame F m) (reflectedFrame F m).top k E G (reflectedField m y V) J
    (fun l => reflectedDirection m y V (c l) (X l)) hzero
    (fun n c' X' => (hG n c' X').contDiffAt)
  rw [← h]
  unfold bondDeriv
  congr 2
  funext τ
  rw [← hmv F m y V k c X τ hm]
end DerivThroughReflection
open DerivThroughReflection in
theorem derivThroughReflection (hmv : ReflectedFieldOfTranslatedTop)
    (hJ : reflectedImagesOfBond) (hmix : MixedDerivAlongDirectionFields)
    (han : AnalyticAlongDirectionFields) : DerivThroughReflection := by
  intro F m y V E _ _ _ G hm hs hG
  exact ⟨isBondAnalyticAt_comp_reflectedField hmv han hJ hm hs y V G hG, fun k c X J hz =>
    bondDeriv_comp_reflectedField hmv hmix (by omega) y V G hG c X J hz⟩
end YangMills.Construction.ColdStepAtMirrorFrames
end
