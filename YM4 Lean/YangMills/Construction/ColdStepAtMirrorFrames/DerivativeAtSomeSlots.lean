import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def IteratedDerivSubsetSlots : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : BlockFrame) (j k m : ℕ) (G : F.GaugeField j → E)
    (U : F.GaugeField j) (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (σ : Fin m → Fin k),
    Function.Injective σ → ContDiffAt ℝ m (fun t : Fin k → ℝ => G (leftTranslate (bondSpread c X t) U)) 0 →
    iteratedFDeriv ℝ m (fun t : Fin k → ℝ => G (leftTranslate (bondSpread c X t) U)) 0
        (fun i => Pi.single (σ i) 1) = bondDeriv G U (c ∘ σ) (X ∘ σ)
end YangMills.Construction.ColdStepAtMirrorFrames
end
