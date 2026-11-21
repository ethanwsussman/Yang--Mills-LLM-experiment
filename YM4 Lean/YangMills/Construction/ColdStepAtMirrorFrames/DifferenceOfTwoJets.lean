import YangMills.Construction.ColdStepAtMirrorFrames.JetOfAFunctionOfAField
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def JetDifferenceBound : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : BlockFrame) (j : ℕ)
    (B : Finset (F.Site j × Fin 4))
    (G G' : F.GaugeField j → E) (W W' : F.GaugeField j) (k : ℕ) (e : (Fin k → ↥B) → ℝ),
    ContDiffThreeAlongBonds G W → ContDiffThreeAlongBonds G' W' → k ≤ 3 → (∀ c, 0 ≤ e c) →
    (∀ (c : Fin k → ↥B) (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
      ‖bondDeriv G W (fun l => (c l).1) X - bondDeriv G' W' (fun l => (c l).1) X‖ ≤ e c) →
    ∀ Z : Fin k → ↥B → imaginaryQuaternions,
      ‖iteratedFDeriv ℝ k (formComposition B G W) 0 Z -
          iteratedFDeriv ℝ k (formComposition B G' W') 0 Z‖ ≤
        ∑ c : Fin k → ↥B, e c * ∏ l, ‖Z l (c l)‖
end YangMills.Construction.ColdStepAtMirrorFrames
end
