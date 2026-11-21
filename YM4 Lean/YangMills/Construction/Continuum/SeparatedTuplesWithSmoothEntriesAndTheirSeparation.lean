import YangMills.Construction.TestSpaces.PointsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TestSpaces
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SmoothSepR4
variable {n : ℕ}
abbrev sepR4 (n : ℕ) : Set (Fin n → (Fin 4 → ℝ) → ℝ) := disjointSupportTuples univ n
def smoothSepR4 (n : ℕ) : Set (Fin n → (Fin 4 → ℝ) → ℝ) :=
  {f | f ∈ sepR4 n ∧ HasSmoothComponents univ f}
def sepDist (f : Fin n → (Fin 4 → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨅ i, ⨅ i', ⨅ _ : i ≠ i', TestFunctions.setDistR4 (tsupport (f i)) (tsupport (f i'))
def SupportedInBalls (R : ℝ) (f : Fin n → (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ i, ∃ y, tsupport (f i) ⊆ TestFunctions.closedBallR4 y R
end YangMills.Construction.SmoothSepR4
end
