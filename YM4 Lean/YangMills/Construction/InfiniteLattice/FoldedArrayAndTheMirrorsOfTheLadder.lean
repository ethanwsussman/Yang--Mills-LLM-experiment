import YangMills.Construction.InfiniteLattice.UnfoldedAndFoldedArraysOfALadder
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open InfiniteLattice
namespace MirrorLadder
variable (L : MirrorLadder)
def rungAt (k : ℤ) : NormalLevelPair 1 where
  normal := L.normal
  normal_mem := L.normal_mem
  level := L.offset + (k : ℝ) * (L.spacing : ℝ)
  allowed := by
    refine ⟨fun hq => ?_, fun hq => ?_⟩
    · obtain ⟨m, hm⟩ := L.offset_allowed.1 hq
      exact ⟨m + 2 * (k * L.spacing), by rw [hm]; push_cast; ring⟩
    · obtain ⟨m, hm⟩ := L.offset_allowed.2 hq
      exact ⟨m + k * L.spacing, by rw [hm]; push_cast; ring⟩
end MirrorLadder
def FoldedArrayMirrorProperties : Prop :=
  ∀ (L : MirrorLadder) (A : L.SlabZeroGenerator),
    (A.reflected ∈ continuousLocalFunctions 1 ∧ (∀ U, (A.reflected U).im = 0) ∧
      SupportLiesIn A.reflected (L.slab 1)) ∧
    (∀ (k : ℤ) (i : A.unfoldedArray.Label), MirrorLadder.UnfoldedLabelInSlab A i k →
      SupportLiesIn (A.unfoldedArray.translate i) (L.slab k)) ∧
    (∀ (a : ℤ) (v : L.normalSublattice),
      (∃ y ∈ parallelPeriodLattice L.normal,
        ((v : LatticePoint 1) : AmbientSpace) = y + (2 * (a : ℝ) * (L.spacing : ℝ)) • dualVector L.normal) →
      SupportLiesIn ((shift (v : LatticePoint 1)).actOn A.toFun) (L.slab (2 * a)) ∧
      SupportLiesIn ((shift (v : LatticePoint 1)).actOn A.reflected)
        (L.slab (2 * a + 1))) ∧
    (∀ (k : ℤ) (i : A.foldedArray.Label), MirrorLadder.FoldedLabelInSlab A i k →
      SupportLiesIn (A.foldedArray.translate i) (L.slab k)) ∧
    (∀ v w : L.normalSublattice,
      ((w : LatticePoint 1) : AmbientSpace) = linearReflect L.normal ((v : LatticePoint 1) : AmbientSpace) →
      L.upperWallOfSlabZero.reflectObservable ((shift (v : LatticePoint 1)).actOn A.toFun) =
          (shift (w : LatticePoint 1)).actOn A.reflected ∧
      L.upperWallOfSlabZero.reflectObservable ((shift (v : LatticePoint 1)).actOn A.reflected) =
          (shift (w : LatticePoint 1)).actOn A.toFun) ∧
    (∃ e : L.normalSublattice ≃ L.normalSublattice, ∀ v,
      ((e v : LatticePoint 1) : AmbientSpace) = linearReflect L.normal ((v : LatticePoint 1) : AmbientSpace)) ∧
    (∃ e : A.foldedArray.Label ≃ A.foldedArray.Label, ∀ i,
      (((e i).1 : LatticePoint 1) : AmbientSpace) = linearReflect L.normal ((i.1 : LatticePoint 1) : AmbientSpace) ∧
      (e i).2 = Fin.rev i.2 ∧
      L.upperWallOfSlabZero.reflectObservable (A.foldedArray.translate i) = A.foldedArray.translate (e i)) ∧
    ∀ k : ℤ,
      (∃ w : L.normalSublattice,
        ((w : LatticePoint 1) : AmbientSpace) = (2 * ((k : ℝ) - 1) * (L.spacing : ℝ)) • dualVector L.normal ∧
        reflectAcross L.normal (L.offset + (k : ℝ) * (L.spacing : ℝ)) =
          (shift (w : LatticePoint 1)).toFun ∘ reflectAcross L.normal (L.offset + (L.spacing : ℝ))) ∧
      (∀ (v u : A.foldedArray.sublattice) (ι : Fin A.foldedArray.size),
        ((u : LatticePoint 1) : AmbientSpace) = linearReflect L.normal ((v : LatticePoint 1) : AmbientSpace) +
          (2 * ((k : ℝ) - 1) * (L.spacing : ℝ)) • dualVector L.normal →
        (L.rungAt k).reflectObservable (A.foldedArray.translate (v, ι)) =
          A.foldedArray.translate (u, Fin.rev ι)) ∧
      (∃ e : A.foldedArray.Label ≃ A.foldedArray.Label,
        (∀ i, (((e i).1 : LatticePoint 1) : AmbientSpace) = linearReflect L.normal ((i.1 : LatticePoint 1) : AmbientSpace) +
            (2 * ((k : ℝ) - 1) * (L.spacing : ℝ)) • dualVector L.normal ∧
          (e i).2 = Fin.rev i.2 ∧
          (L.rungAt k).reflectObservable (A.foldedArray.translate i) = A.foldedArray.translate (e i)) ∧
        ∀ (i : A.foldedArray.Label) (j : ℤ),
          MirrorLadder.FoldedLabelInSlab A i j ↔
            MirrorLadder.FoldedLabelInSlab A (e i) (2 * k - 1 - j))
end YangMills.Construction.NormalFamilies
