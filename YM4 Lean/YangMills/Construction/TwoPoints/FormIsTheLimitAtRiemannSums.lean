import YangMills.Construction.TwoPoints.ThreePropertiesOfAForm
import YangMills.Construction.TwoPoints.TranslationModulusAndSuperpositionsOfTranslates
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def FormIsGridSumLimit.Statement : Prop :=
  ∀ s : FixedScale, ∀ S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ,
    IsDisjointForm S → IsAdmissibleForm s S →
    ∀ ε : ℝ, 0 < ε → ∀ φ₁ ∈ cc1NearZero ε, ∀ φ₂ ∈ cc1NearZero ε,
      ∀ k₁ ∈ ccIn (univ : Set AmbientSpace),
        ∀ k₂ ∈ ccIn (univ : Set AmbientSpace),
          (∀ z₁ ∈ tsupport k₁, ∀ z₂ ∈ tsupport k₂, 2 * ε < euclidNorm (z₂ - z₁)) →
            DisjointSupports (convolve k₁ φ₁) (convolve k₂ φ₂) ∧
              Tendsto
                (fun δ : ℝ => complexifyForm S (cubeRiemannSum δ k₁ φ₁) (cubeRiemannSum δ k₂ φ₂))
                (𝓝[>] 0) (𝓝 (complexifyForm S (convolve k₁ φ₁) (convolve k₂ φ₂)))
end YangMills.Construction.TwoPoints
end
