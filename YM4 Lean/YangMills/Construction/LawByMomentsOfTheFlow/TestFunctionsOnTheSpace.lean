import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TestFunctions
abbrev EuclideanFourSpace : Type := EuclideanSpace ℝ (Fin 4)
structure IsSeparatedLipschitzFamily {k : ℕ} (R d : ℝ) (f : Fin k → EuclideanFourSpace → ℝ) : Prop where
  lipschitzWith_one : ∀ i, LipschitzWith 1 (f i)
  abs_le_one : ∀ i x, |f i x| ≤ 1
  tsupport_subset_closedBall : ∀ i, tsupport (f i) ⊆ Metric.closedBall 0 R
  le_dist_of_ne : ∀ i j, i ≠ j → ∀ x ∈ tsupport (f i), ∀ y ∈ tsupport (f j), d ≤ dist x y
end TestFunctions
end YangMills.Construction
end
