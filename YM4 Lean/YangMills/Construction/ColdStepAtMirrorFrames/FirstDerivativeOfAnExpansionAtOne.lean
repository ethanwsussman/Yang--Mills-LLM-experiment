import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def FirstDerivAtTrivialVanishes : Prop :=
  ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame), IsRegularFamily L t n₀ σ δ E E₃ f → 0 < σ →
    IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (c : Fin 1 → F.Site F.depth × Fin 4)
      (X : Fin 1 → imaginaryQuaternions),
      bondDeriv (f F y) (uniformField F F.depth) c X = 0
end YangMills.Construction.ColdStepAtMirrorFrames
end
