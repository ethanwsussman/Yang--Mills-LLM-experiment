import YangMills.Construction.TwoPoints.MirrorsThePlaneAndPlates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def posHalfSpace (n : AmbientSpace) : Set AmbientSpace := {x | 0 < euclidDot n x}
def TimeReflectionInvariantPositive (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) : Prop :=
  (∀ r ∈ euclideanMotions, ∀ f ∈ compactC1Real, ∀ h ∈ compactC1Real, DisjointSupports f h →
      S (actOn r f) (actOn r h) = S f h) ∧
    ∀ f ∈ cc1In TimeAxis.upperHalfSpace,
      IsRealNonneg (complexifyForm S (timeReflected (conjFun f)) f)
def IsBallDecayBound (sc : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (C : ℝ → ℝ → ℝ) : Prop :=
  (∀ d R : ℝ, 0 < d → 0 < R → 0 ≤ C d R) ∧
    (∀ d d' R : ℝ, 0 < d → d ≤ d' → 0 < R → C d' R ≤ C d R) ∧
      ∀ d R : ℝ, 0 < d → 0 < R → ∀ x x' : AmbientSpace, ∀ f ∈ compactC1Real, ∀ h ∈ compactC1Real,
        tsupport f ⊆ euclidClosedBall x R → tsupport h ⊆ euclidClosedBall x' R →
          SeparatedBy d (tsupport f) (tsupport h) →
            |S f h| ≤ C d R * sc.sharpNorm f * sc.sharpNorm h
def HasBallDecayBound (sc : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) :
    Prop :=
  ∃ C : ℝ → ℝ → ℝ, IsBallDecayBound sc S C
def DiagonalReflectionPositive (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) : Prop :=
  ∃ n ∈ diagNormals, ∀ f ∈ cc1In (posHalfSpace n),
    IsRealNonneg (complexifyForm S (reflectFun n (conjFun f)) f)
structure IsAdmissibleForm (sc : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) :
    Prop where
  invariantPositive : TimeReflectionInvariantPositive S
  ballDecay : HasBallDecayBound sc S
  diagonalPositive : DiagonalReflectionPositive S
end TwoPoints
end YangMills.Construction
end
