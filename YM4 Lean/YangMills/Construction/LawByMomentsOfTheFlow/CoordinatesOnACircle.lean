import YangMills.Construction.LawByMomentsOfTheFlow.TestFunctionsAcrossTheLevels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
def CircleRepProperties : Prop :=
  (∀ (c : ℝ), 0 < c → ∀ (v : ℝ) (e : ℤ), circleRep c (v + c * e) = circleRep c v) ∧
  (∀ (c : ℝ), 0 < c → ∀ v : ℝ, |circleRep c v| ≤ |v|) ∧
  (∀ (c : ℝ), 0 < c → ∀ u v : ℝ, |circleRep c (u + v)| ≤ |circleRep c u| + |circleRep c v|) ∧
  (∀ (c : ℝ), 0 < c → ∀ v : ℝ, |circleRep c (-v)| ≤ |circleRep c v|) ∧
  (∀ (c : ℝ), 0 < c → ∀ v : ℝ, |v| ≤ c / 2 → |circleRep c v| = |v|) ∧
  (∀ (c M : ℝ), 0 < c → 0 < M → ∀ v : ℝ, circleRep (c * M) (v * M) = circleRep c v * M) ∧
  (∀ (N : ℕ) [NeZero N] (y y' : ZMod N),
    |circleRep N ((y.val : ℝ) - (y'.val : ℝ))| = (((y - y').valMinAbs).natAbs : ℝ))
end YangMills.Construction.LevelTestFunctions
end
