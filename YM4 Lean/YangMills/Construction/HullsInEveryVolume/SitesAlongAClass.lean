import YangMills.Construction.HullsInEveryVolume.HullDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
def sitesAlongHullClassStatement : Prop :=
  ∀ (n r : ℕ) [NeZero n] (X : Finset (TorusFields.TorusSite n)) (z : TorusFields.TorusSite n) (D : ℝ), 1 ≤ r → 0 ≤ D →
    z ∈ X → (∀ a ∈ X, ∀ b ∈ X, TorusLumps.ChainConnected r X a b) → D ≤ (supDiam X : ℝ) →
    (∃ ys : ℕ → TorusFields.TorusSite n, ys 0 = z ∧ (∀ i < max 1 ⌈D / (82 * (r : ℝ))⌉₊, ys i ∈ X) ∧
      (∀ i < max 1 ⌈D / (82 * (r : ℝ))⌉₊, ∀ i' < max 1 ⌈D / (82 * (r : ℝ))⌉₊, i ≠ i' →
        40 * r ≤ TorusFields.supDist (ys i) (ys i')) ∧
      ∀ i, i + 1 < max 1 ⌈D / (82 * (r : ℝ))⌉₊ → TorusFields.supDist (ys (i + 1)) (ys i) < 41 * r) ∧
    (open Classical in
      (Finset.univ.filter fun a : TorusFields.TorusSite n => TorusFields.supDist a z < 41 * r).card ≤ (83 * r) ^ 4)
end YangMills.Construction.HullTrees
end
