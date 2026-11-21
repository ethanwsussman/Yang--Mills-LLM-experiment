import YangMills.Construction.SummableBoundsOfTheFlow.TheFinerExpansionReturns
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockMeans
def refinedExpansionOfTilt : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (f : ℕ → TorusLumps.LocalDensity) (b d : ℕ → ℝ) (yp C₁ : ℝ), ℓ.Admissible →
    StepReturn.ExpansionReturnsAt ℓ → 0 < C₁ →
    1 ≤ yp → 200 * ℓ.B ≤ yp → ℓ.y₁ ≤ yp → 2 * C₁ * yp ^ (-(3 / 4 : ℝ)) ≤ ℓ.E / 2 →
    (∀ t, FamilyNorms.IsNormBoundedFamily ℓ (ℓ.E / 2) (ℓ.E₃ / 2) (f t)) →
    FamilyNorms.TiltReturnsAt ℓ f b d yp C₁ →
    FamilyNorms.RefinedExpansionReturnsAt ℓ f b d yp (2 * C₁) (C₁ * (2 * C₁ + 1))
end YangMills.Construction.BlockMeans
end
