import YangMills.Construction.EuclideanFunctionals.PulledDownNormsTheInsertionValueAndClassesOfTensors
import YangMills.Construction.Rotation.ProductFunctionsOnFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals
variable {m : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon m S)
structure InsertionBoundHolds (p C c : ℝ) : Prop where
  nonneg_exponent : 0 ≤ p
  nonneg_constant : 0 ≤ C
  pos_fraction : 0 < c
  fraction_lt_eighth : c < 1 / 8
  le_bound : ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ x : R4, |x 3| ≤ η / 8 →
    ∀ k ∈ C1c ℝ, supp k ⊆ {z | TorusMetric.euclidNormVec (z - x) ≤ c * η} →
    ∀ F ∈ finCombIn {y | η / 4 < y 3}, ∀ A ∈ finCombIn {y | η / 4 < y 3},
      ‖insertion S F (fun y => (k y : ℂ)) A‖ ≤
        C * η ^ (-p) * m.sharpNorm k * heightNorm σ (η / 4) F * heightNorm σ (η / 4) A
def planeStrip (c η : ℝ) : Set RealPlane := {y | |y 0| < c * η}
def thinSlab (c η : ℝ) : Set R4 := {x | |x 3| < c * η}
structure ProductBoundHolds (p : ℝ) (C : (RealPlane → ℝ) → ℝ) (c : ℝ) : Prop where
  pos_exponent : 0 < p
  nonneg_constant : ∀ φ ∈ realLabels, 0 ≤ C φ
  pos_fraction : 0 < c
  fraction_lt_quarter : c < 1 / 4
  le_bound : ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ φ ∈ realLabels, ∀ α ∈ complexProfiles,
    tsupport α ⊆ planeStrip c η →
    ∀ F ∈ finCombIn {y | η / 4 < y 3}, ∀ A ∈ finCombIn {y | η / 4 < y 3},
      ‖insertion S F (productFunction α φ) A‖ ≤
        C φ * η ^ (-p) * profileL1Norm α * heightNorm σ (η / 4) F * heightNorm σ (η / 4) A
end EuclideanFunctionals
end YangMills.Construction
