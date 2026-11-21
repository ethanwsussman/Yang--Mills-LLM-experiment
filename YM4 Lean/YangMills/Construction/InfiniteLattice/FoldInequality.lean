import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import YangMills.Construction.InfiniteLattice.UnfoldedAndFoldedArraysOfALadder
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open YangMills.Construction.InfiniteLattice
def FoldedStateBound : Prop :=
  ∀ β : ℝ, 0 < β → ∀ (L : MirrorLadder) (A : L.SlabZeroGenerator),
    ∀ ν ∈ subgroupInvariantGibbsClass one_pos β L.axialSublattice,
      ∃ ν₀ ∈ subgroupInvariantGibbsClass one_pos β L.normalSublattice,
        (∀ k : ℤ, ∃ P : NormalLevelPair 1,
          P.normal = L.normal ∧ P.level = L.offset + (k : ℝ) * (L.spacing : ℝ) ∧
          IsSymmetricUnder ν₀ P.reflectSymmetry ∧
          ∀ F, (F ∈ regionObservables 1 {x | P.level ≤ L.normal ⬝ᵥ x} ∨
              F ∈ regionObservables 1 {x | L.normal ⬝ᵥ x ≤ P.level}) →
            0 ≤ stateEval ν₀ (P.conjReflectObservable F * F)) ∧
        stateEval ν A.toFun ≤ stateEval ν₀ A.toFun
end YangMills.Construction.NormalFamilies
end
