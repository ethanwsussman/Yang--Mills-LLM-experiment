import YangMills.Construction.InfiniteLattice.LatticeMirrorsGivenWithANormal
import YangMills.Construction.InfiniteLattice.LinkSupportAndRegionObservables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeConventions
namespace LinkHalfSpaces
open YangMills.Construction.InfiniteLattice (Link LatticePoint localRegionObservables)
def LinkInBothHalvesIffInPlane (a : Spacing) (Q : NormalHyperplane) : Prop :=
  ∀ b : Link (a : ℝ),
    (b.LiesIn Q.carrier → b.LiesIn Q.upperHalfSpace ∧ b.LiesIn Q.lowerHalfSpace) ∧
      (b.LiesIn Q.upperHalfSpace ∧ b.LiesIn Q.lowerHalfSpace → b.LiesIn Q.carrier)
def CrossingLinksInNeitherHalf (a : Spacing) (μ : Direction) (c : ℝ) : Prop :=
  ∀ b : Link (a : ℝ),
    (((b.initial : Point) μ < c ∧ c < (b.terminal : Point) μ) ∨
        ((b.terminal : Point) μ < c ∧ c < (b.initial : Point) μ)) →
      ¬ b.LiesIn (NormalHyperplane.axial μ c).upperHalfSpace ∧
        ¬ b.LiesIn (NormalHyperplane.axial μ c).lowerHalfSpace
def NoPointOnPlane (a : Spacing) (μ : Direction) (c : ℝ) : Prop :=
  ∀ x : LatticePoint (a : ℝ), (x : Point) ∉ (NormalHyperplane.axial μ c).carrier
def HalfSpaceLocalObservablesEq (a : Spacing) (μ : Direction) : Prop :=
  localRegionObservables (a : ℝ) {x : Point | -((a : ℝ) / 2) ≤ x μ} =
    localRegionObservables (a : ℝ) {x : Point | 0 ≤ x μ}
def Statement : Prop :=
  ∀ a : Spacing,
    (∀ Q : NormalHyperplane, Q.IsLatticeMirror (a : ℝ) → LinkInBothHalvesIffInPlane a Q) ∧
      (∀ (μ : Direction) (c : ℝ), (NormalHyperplane.axial μ c).IsEdgeMirror (a : ℝ) →
        CrossingLinksInNeitherHalf a μ c ∧ NoPointOnPlane a μ c) ∧
      ∀ μ : Direction, HalfSpaceLocalObservablesEq a μ
end LinkHalfSpaces
end YangMills.Construction.LatticeConventions
end
