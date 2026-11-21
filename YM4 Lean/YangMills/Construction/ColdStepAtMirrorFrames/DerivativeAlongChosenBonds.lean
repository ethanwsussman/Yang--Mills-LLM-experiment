import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def IteratedDerivAlongSubfamily : Prop :=
  ∀ (F : BlockFrame) (j k n : ℕ) (G : F.GaugeField j → ℝ) (W : F.GaugeField j) (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (l : Fin n → Fin k),
    ContDiffAt ℝ n (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0 →
    iteratedFDeriv ℝ n (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0
        (fun i => Pi.single (l i) 1) = bondDeriv G W (c ∘ l) (X ∘ l)
end YangMills.Construction.ColdStepAtMirrorFrames
end
