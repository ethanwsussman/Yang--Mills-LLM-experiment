import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def AnalyticAlongDirectionFields : Prop :=
  ∀ (F : BlockFrame) (j k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : F.GaugeField j → E) (W : F.GaugeField j) (J : Fin k → Finset (F.Site j × Fin 4))
    (ξ : Fin k → F.Site j → Fin 4 → imaginaryQuaternions),
    (∀ l z i, (z, i) ∉ J l → ξ l z i = 0) →
    (∀ (n : ℕ) (c : Fin n → F.Site j × Fin 4) (X : Fin n → imaginaryQuaternions),
      AnalyticAt ℝ (fun τ : Fin n → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0) →
    AnalyticAt ℝ (fun τ : Fin k → ℝ => G (leftTranslate (fun z i => ∑ l, τ l • ξ l z i) W)) 0
end YangMills.Construction.ColdStepAtMirrorFrames
end
