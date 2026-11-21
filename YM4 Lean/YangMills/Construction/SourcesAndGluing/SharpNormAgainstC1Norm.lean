import YangMills.Construction.SourcesAndGluing.StandingDataAndSigns
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TestFunctions
namespace SourcesAndGluing
def sharpConst (M : ℝ) : ℝ := 80 * M
def HasFiniteC1NormR4 {𝕜 : Type*} [RCLike 𝕜] (f : (Fin 4 → ℝ) → 𝕜) : Prop :=
  IsBoundedFun f ∧ ∀ μ : Fin 4, IsBoundedFun (partialDerivR4 μ f)
def GluingSetup.HasFiniteC1NormTorus (D : GluingSetup) {𝕜 : Type*} [RCLike 𝕜]
    (f : D.Torus → 𝕜) : Prop :=
  IsBoundedFun f ∧ ∀ μ : Fin 4, IsBoundedFun (D.partialDeriv μ f)
def SharpNormBound.Statement : Prop :=
  ∀ (D : GluingSetup) (𝕜 : Type) [RCLike 𝕜],
    (∀ f : D.Torus → 𝕜, D.IsC1 f → D.HasFiniteC1NormTorus f →
      IsLipschitzFor euclidDistTorus f ∧ lipConstTorus f ≤ 2 * D.c1Norm f ∧
        D.sharpNormTorus f ≤ sharpConst D.M * D.c1Norm f) ∧
    (∀ f : (Fin 4 → ℝ) → 𝕜, IsC1R4 f → HasFiniteC1NormR4 f →
      IsLipschitzFor euclidDistR4 f ∧ lipConstR4 f ≤ 2 * c1NormR4 f ∧
        D.sharpNormR4 f ≤ sharpConst D.M * c1NormR4 f)
end SourcesAndGluing
end YangMills.Construction
end
