import YangMills.Construction.TorusOrFourSpace.RadiusPartitionOfUnityAndTheNumberTheta
import Mathlib
set_option autoImplicit false
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction.PeriodicSpace
structure IsPeriodicPartition (θ : RadiusRatio) {B : Type} [Fintype B]
    (X : B → (Fin 4 → ℝ) → ℝ) : Prop where
  nonempty : Nonempty B
  contDiff : ∀ b, ContDiff ℝ ∞ (X b)
  mem_Icc : ∀ b x, X b x ∈ Set.Icc (0 : ℝ) 1
  periodic : ∀ b x, ∀ k : Fin 4 → ℤ, X b (x + fun μ => (k μ : ℝ)) = X b x
  sum_eq_one : ∀ x, ∑ b, X b x = 1
  supported_near_balls : ∀ b, ∃ z : Fin 4 → ℝ, ∃ θb ∈ Set.Ioo (0 : ℝ) θ.val, ∀ x, X b x ≠ 0 →
    ∃ k : Fin 4 → ℤ, TorusMetric.euclidNormVec (x - z - fun μ => (k μ : ℝ)) ≤ θb
def gradSupBound {B : Type} (X : B → (Fin 4 → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ b, ⨆ x, ENNReal.ofReal
    (TorusMetric.euclidNormVec fun μ => TestFunctions.partialDerivR4 μ (X b) x)
def partitionConstant (M : ℝ) {B : Type} [Fintype B] (X : B → (Fin 4 → ℝ) → ℝ) : ℝ≥0∞ :=
  (Fintype.card B : ℝ≥0∞) * (1 + 40 * ENNReal.ofReal M * gradSupBound X)
end YangMills.Construction.PeriodicSpace
