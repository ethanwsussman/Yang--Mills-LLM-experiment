import YangMills.Construction.RotationInvariance.HarmonicsOfTheFunctionOfTheAngle
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals
def harmonicFrequencies (S : ConnFamily) (θ : openingAngles) (q : ℕ) : Set ℕ :=
  {0} ∪ {k | ∃ ν : ℤ, ν.natAbs = k ∧ ∃ y ∈ pencilSet θ (q + 1),
    ∃ φ : Fin (q + 1) → realLabels, angleHarmonic S θ y φ ν ≠ 0}
def maxFrequency (S : ConnFamily) (θ : openingAngles) : ℕ → ℕ
  | 0 => 0
  | q + 1 => if 1 ≤ q then sSup (harmonicFrequencies S θ q) else 0
end EuclideanFunctionals
end YangMills.Construction
end
