import YangMills.Construction.TwoPoints.DoubleRiemannSumsTendToTheDoubleIntegral
import YangMills.Construction.TwoPoints.ThreePropertiesOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def FormOnGridSumsIsPairedSum.Statement : Prop :=
  ∀ s : FixedScale, ∀ S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ,
    IsDisjointForm S → IsAdmissibleForm s S →
    ∀ ε : ℝ, 0 < ε → ∀ φ₁ ∈ cc1NearZero ε, ∀ φ₂ ∈ cc1NearZero ε,
      ∀ k₁ ∈ ccIn (Set.univ : Set AmbientSpace),
        ∀ k₂ ∈ ccIn (Set.univ : Set AmbientSpace),
          (∀ z₁ ∈ tsupport k₁, ∀ z₂ ∈ tsupport k₂, 2 * ε < euclidNorm (z₂ - z₁)) →
            ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
              complexifyForm S (cubeRiemannSum δ k₁ φ₁) (cubeRiemannSum δ k₂ φ₂) =
                pairedGridSum δ k₁ k₂ (shiftPairing S φ₁ φ₂)
end YangMills.Construction.TwoPoints
end
