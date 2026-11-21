import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def FirstDerivVanishesAtUniform : Prop :=
  ∀ (F : BlockFrame) (j : ℕ) (G : F.GaugeField j → ℝ) (s : ℝ) (c : Fin 1 → F.Site j × Fin 4)
    (X : Fin 1 → imaginaryQuaternions),
    0 < s → (∀ (W : F.GaugeField j) (γ : F.Site j → UnitQuaternion), IsSmallCurvature s W →
      G (gaugeTransform γ W) = G W) →
    AreUnitVectors X → bondDeriv G (uniformField F j) c X = 0
end ColdStepAtMirrorFrames
end YangMills.Construction
end
