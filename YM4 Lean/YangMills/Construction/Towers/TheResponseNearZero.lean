import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ResponseAtSmallMomentum
open ResponseProperties (SmallMomentumBehaviour)
open FreeStrip (halfSupRate)
def Statement : Prop :=
  ∀ δ₀ ∈ halfSupRate, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    SmallMomentumBehaviour δ₀ L k
end YangMills.Construction.Tower.ResponseAtSmallMomentum
end
