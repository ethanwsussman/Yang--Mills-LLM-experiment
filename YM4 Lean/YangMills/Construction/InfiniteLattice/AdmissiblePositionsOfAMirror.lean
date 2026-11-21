import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.InfiniteLattice.LatticeMirrorsGivenWithANormal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing
open YangMills.Construction.InfiniteLattice (latticeSubgroup)
open YangMills.Construction.LatticeConventions (NormalHyperplane IsAxialNormal IsFaceDiagonalNormal
  Point euclidDot euclidNorm)
def MirrorPositionsAndReflectionRules : Prop :=
  ∀ a : ℝ, 0 < a → ∀ Q : NormalHyperplane,
    (IsAxialNormal Q.normal →
      (Q.reflect '' (latticeSubgroup a : Set Point) = (latticeSubgroup a : Set Point) ↔
        ∃ q : ℤ, Q.level = (q : ℝ) * (a / 2))) ∧
    (IsFaceDiagonalNormal Q.normal →
      (Q.reflect '' (latticeSubgroup a : Set Point) = (latticeSubgroup a : Set Point) ↔
        ∃ q : ℤ, Q.level = (q : ℝ) * a)) ∧
    (∀ x y : Point, euclidNorm (Q.reflect x - Q.reflect y) = euclidNorm (x - y)) ∧
    Q.reflect ∘ Q.reflect = id ∧
    (∀ x : Point, euclidDot Q.normal (Q.reflect x) - Q.level = -(euclidDot Q.normal x - Q.level)) ∧
    Q.reflect '' Q.upperHalfSpace = Q.lowerHalfSpace ∧
    Q.reflect '' Q.lowerHalfSpace = Q.upperHalfSpace ∧
    ∀ (x : Point) (s : ℝ), Q.reflect (x + s • Q.normal) = Q.reflect x - s • Q.normal
end YangMills.Construction.GibbsAtFixedSpacing
end
