import YangMills.Construction.SummableBoundsOfTheFlow.TopFamilyHasANorm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FamilyNorms
open BlockAverages ColdStepAtMirrorFrames
def vanishingDensityPlaneBoundStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ S : ℝ, 0 < S ∧
    ∀ (L t n₀ : ℕ) (δ σ A : ℝ) (g : TopLevelFamily), Odd L → 0 < δ → 2 * δ ≤ κ → 0 < σ → 0 < A →
      IsLocalDensity L t n₀ σ g →
      (∀ (F : BlockFrame) (Y : F.Cell), IsCubicTopTorus L t n₀ F → g F Y (flatTopField (F := F)) = 0) →
      DerivDecay L t n₀ σ g (fun _ n => A * Real.exp (-(κ * n))) →
      IsLocalOnTori L t n₀ σ g (fun r => A / torusDecayFactor L δ r) →
      HasBoundedLimitForm L t g (S * A)
end YangMills.Construction.FamilyNorms
end
