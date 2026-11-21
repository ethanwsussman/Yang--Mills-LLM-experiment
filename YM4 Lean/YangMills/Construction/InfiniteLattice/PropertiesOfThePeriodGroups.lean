import YangMills.Construction.InfiniteLattice.LadderOfMirrorsOfOneFamily
import YangMills.Construction.InfiniteLattice.OneFamilyOfMirrors
import YangMills.Construction.InfiniteLattice.PeriodGroupsOfOneFamily
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open YangMills.Construction.InfiniteLattice
def ParallelLatticeSpansHyperplane (n : AmbientSpace) : Prop :=
  (Submodule.span ℝ (parallelPeriodLattice n : Set AmbientSpace) : Set AmbientSpace) =
      {x | n ⬝ᵥ x = 0} ∧
    Module.finrank ℝ (Submodule.span ℝ (parallelPeriodLattice n : Set AmbientSpace)) = 3 ∧
    ∀ x ∈ parallelPeriodLattice n, linearReflect n x = x
def AxialPeriodsHaveFiniteIndex (n : AmbientSpace) (h : ℤ) : Prop :=
  (h : ℝ) • firstNonzeroBasisVec n ∈ evenLattice ∧
    (2 * (h : ℝ)) • dualVector n ∈ evenLattice ∧
    axialPeriodLattice n h ≤ evenLattice ∧
    normalPeriodLattice n h ≤ evenLattice ∧
    Disjoint (parallelPeriodLattice n)
      (AddSubgroup.zmultiples ((h : ℝ) • firstNonzeroBasisVec n)) ∧
    Disjoint (parallelPeriodLattice n) (AddSubgroup.zmultiples ((2 * (h : ℝ)) • dualVector n)) ∧
    Module.finrank ℤ (axialPeriodLattice n h) = 4 ∧
    Module.finrank ℤ (normalPeriodLattice n h) = 4 ∧
    (axialPeriodLattice n h ≤ latticeSubgroup 1 ∧
      (axialPeriodLattice n h).relIndex (latticeSubgroup 1) ≠ 0) ∧
    (normalPeriodLattice n h ≤ latticeSubgroup 1 ∧
      (normalPeriodLattice n h).relIndex (latticeSubgroup 1) ≠ 0) ∧
    0 < axialPeriodDensity n h ∧
    linearReflect n '' (normalPeriodLattice n h : Set AmbientSpace) = normalPeriodLattice n h
def NormalPeriodsHaveIndexTwo (n : AmbientSpace) (h : ℤ) : Prop :=
  (2 * (h : ℝ)) • dualVector n - (2 * (h : ℝ)) • firstNonzeroBasisVec n ∈
      parallelPeriodLattice n ∧
    normalPeriodLattice n h =
      parallelPeriodLattice n ⊔ AddSubgroup.zmultiples ((2 * (h : ℝ)) • firstNonzeroBasisVec n) ∧
    Disjoint (parallelPeriodLattice n)
      (AddSubgroup.zmultiples ((2 * (h : ℝ)) • firstNonzeroBasisVec n)) ∧
    normalPeriodLattice n h ≤ axialPeriodLattice n h ∧
    (normalPeriodLattice n h).relIndex (axialPeriodLattice n h) = 2 ∧
    ((normalPeriodLattice n h).relIndex (latticeSubgroup 1) : ℝ) = 2 / axialPeriodDensity n h
def PeriodsShiftTheSlabs (L : MirrorLadder) : Prop :=
  (∀ v ∈ axialPeriodLattice L.normal L.spacing,
      ∃ m : ℤ, L.normal ⬝ᵥ v = (m : ℝ) * (L.spacing : ℝ)) ∧
    (∀ m : ℤ, ∃ v ∈ axialPeriodLattice L.normal L.spacing,
      L.normal ⬝ᵥ v = (m : ℝ) * (L.spacing : ℝ)) ∧
    (∀ (v : LatticePoint 1) (k m : ℤ), (v : AmbientSpace) ∈ axialPeriodLattice L.normal L.spacing →
      (m : ℝ) = L.normal ⬝ᵥ (v : AmbientSpace) / (L.spacing : ℝ) →
        (shift v).toFun '' L.slab k = L.slab (k + m)) ∧
    (∀ v ∈ normalPeriodLattice L.normal L.spacing,
      ∃ m : ℤ, L.normal ⬝ᵥ v = (m : ℝ) * (2 * (L.spacing : ℝ))) ∧
    (∀ m : ℤ, ∃ v ∈ normalPeriodLattice L.normal L.spacing,
      L.normal ⬝ᵥ v = (m : ℝ) * (2 * (L.spacing : ℝ))) ∧
    (∀ j : ℤ, ∀ y ∈ parallelPeriodLattice L.normal,
      L.normal ⬝ᵥ (y + ((j : ℝ) * (L.spacing : ℝ)) • firstNonzeroBasisVec L.normal) =
        (j : ℝ) * (L.spacing : ℝ)) ∧
    ∀ i : ℤ, ∀ y ∈ parallelPeriodLattice L.normal,
      L.normal ⬝ᵥ (y + (2 * (i : ℝ) * (L.spacing : ℝ)) • dualVector L.normal) =
        2 * (i : ℝ) * (L.spacing : ℝ)
def PeriodLatticeProperties : Prop :=
  (∀ n ∈ normalSet, ∀ h : ℤ, Even h → 2 ≤ h →
    ParallelLatticeSpansHyperplane n ∧ AxialPeriodsHaveFiniteIndex n h ∧
      NormalPeriodsHaveIndexTwo n h) ∧
    ∀ L : MirrorLadder, PeriodsShiftTheSlabs L
end YangMills.Construction.NormalFamilies
