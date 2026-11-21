import YangMills.Construction.Weighted.LengthDensity
import Mathlib
set_option autoImplicit false
open scoped ENNReal NNReal Topology
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace Weighted
variable {S : ℝ}
def distInftyToSet (A : Set (Torus4 S)) (x : Torus4 S) : ℝ := (setSupDist {x} A).toReal
def LocalLipRules : Prop :=
  ∀ D : TorusData,
    (∀ A : Set D.Space, A.Nonempty →
      LipschitzL1 (distInftyToSet A) ∧ ∀ x, localLip (distInftyToSet A) x ≤ 1) ∧
    (∀ f : D.Space → ℝ, LipschitzL1 f →
      (∀ (φ : ℝ → ℝ) (c : ℝ≥0), LipschitzWith c φ →
        LipschitzL1 (φ ∘ f) ∧
          ∀ x, localLip (φ ∘ f) x ≤ (c : ℝ≥0∞) * localLip f x) ∧
      ∀ x, (∃ U ∈ 𝓝 x, ∃ a : ℝ, ∀ y ∈ U, f y = a) → localLip f x = 0) ∧
    (∀ f₁ f₂ : D.Space → ℝ, LipschitzL1 f₁ → LipschitzL1 f₂ →
      LipschitzL1 (f₁ * f₂) ∧
        ∀ x, localLip (f₁ * f₂) x ≤
          ENNReal.ofReal |f₁ x| * localLip f₂ x +
            ENNReal.ofReal |f₂ x| * localLip f₁ x)
end Weighted
end YangMills.Construction
