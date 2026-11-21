import YangMills.Construction.SummableBoundsOfTheFlow.TheFinerExpansionReturns
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FamilyNorms
open YangMills.Construction.TorusLumps
def wilsonHasRefinedExpansionStatement : Prop :=
  ∃ C₀ : ℝ, ∀ (ℓ : StepParameters) (f : ℕ → LocalDensity) (yp Bh : ℝ), ℓ.Admissible →
    C₀ ≤ ℓ.derivBound → f 0 = 0 → ℓ.y₁ ≤ yp → 0 < yp → 0 ≤ Bh →
    WilsonHasRefinedExpansionAt ℓ f yp Bh
end YangMills.Construction.FamilyNorms
end
