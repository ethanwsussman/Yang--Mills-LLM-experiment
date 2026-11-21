import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def UniformFieldFirstDerivZero : Prop :=
  ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame) (y : F.Site F.depth)
    (c : Fin 1 → F.Site F.depth × Fin 4) (X : Fin 1 → imaginaryQuaternions),
    IsRegularFamily L t n₀ σ δ E E₃ f → IsCubicTorusAbove L t n₀ F → 0 < σ → AreUnitVectors X →
    bondDeriv (subtractTrivial f F y) (uniformField F F.depth) c X = 0
end YangMills.Construction.ColdStepAtMirrorFrames
end
