import YangMills.Construction.ColdStepAtMirrorFrames.MirrorOfAMovedTopForm
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def DerivThroughReflection : Prop :=
  ∀ (F : BlockFrame) (m : ℕ) (y : F.Cell) (V : F.GaugeField F.top) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (G : (reflectedFrame F m).GaugeField (reflectedFrame F m).top → E),
    2 ≤ m → (∀ i, 2 * m + 2 < F.extent i) → IsBondAnalyticAt G (reflectedField m y V) →
    IsBondAnalyticAt (fun V' => G (reflectedField m y V')) V ∧
    ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
      (J : Fin k → Finset ((reflectedFrame F m).Cell × Fin 4)),
      (∀ l z i, (z, i) ∉ J l → reflectedDirection m y V (c l) (X l) z i = 0) →
      bondDeriv (fun V' => G (reflectedField m y V')) V c X =
        ∑ r ∈ Fintype.piFinset J, bondDeriv G (reflectedField m y V) r
          (fun l => reflectedDirection m y V (c l) (X l) (r l).1 (r l).2)
end YangMills.Construction.ColdStepAtMirrorFrames
end
