import YangMills.Construction.InfiniteLattice.FrameOfAMirrorVectorAndAdaptedPeriodGroups
import YangMills.Construction.InfiniteLattice.OrientedBondsLiftsAndPreservedMeasuresOfATorus
import YangMills.Construction.InfiniteLattice.PeriodGroupsOfOneFamily
import YangMills.Construction.ReflectionPositivity.ParallelPartOfASplitPeriodLattice
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open YangMills.Construction.InfiniteLattice
def adaptedBasis (n : AmbientSpace) (hn : IsNormalVector n) (h J w : ℤ) : Fin 4 → AmbientSpace :=
  Fin.cons (longPeriod n h J) (shortPeriod n hn w)
def adaptedTransverseLattice (n : AmbientSpace) (hn : IsNormalVector n) (w : ℤ) : AddSubgroup AmbientSpace :=
  ⨆ i : Fin 3, AddSubgroup.zmultiples (shortPeriod n hn w i)
def IsPeriodSubgroup (G : AddSubgroup AmbientSpace) : Prop :=
  ∃ Γ : PeriodSublattice 1, Γ.toAmbient = G
def IsAdaptedSideTuple (n : AmbientSpace) (hn : IsNormalVector n) (h J w : ℤ) (s : Fin 4 → ℕ+) : Prop :=
  ((s 0 : ℕ) : ℝ) = 2 * (J : ℝ) * (h : ℝ) ∧
    ∀ i : Fin 3, ((s i.succ : ℕ) : ℝ) = (w : ℝ) * (normalFrame n hn).lengthSq i.succ
def adaptedSideLengths (n : AmbientSpace) (hn : IsNormalVector n) (h J w : ℤ) : Fin 4 → ℕ+ :=
  Classical.epsilon (IsAdaptedSideTuple n hn h J w)
def AdaptedTorusProperties : Prop :=
  ∀ (n : AmbientSpace) (hn : IsNormalVector n) (h J w : ℤ), AdmissibleParams h J w →
    ((Pairwise fun i j => adaptedBasis n hn h J w i ⬝ᵥ adaptedBasis n hn h J w j = 0) ∧
      (∀ i, adaptedBasis n hn h J w i ∈ latticeSubgroup 1) ∧
      iSupIndep (fun i => AddSubgroup.zmultiples (adaptedBasis n hn h J w i)) ∧
      HasFullRank (adaptedLattice n hn h J w) ∧
      (∀ γ ∈ adaptedLattice n hn h J w, γ ≠ 0 → ((min (J * h) w : ℤ) : ℝ) ≤ ‖γ‖) ∧
      (3 ≤ min (J * h) w → IsPeriodSubgroup (adaptedLattice n hn h J w)) ∧
      ∀ r : ℤ, 1 ≤ r → r + 1 < min (J * h) w →
        IsPeriodSubgroup (adaptedLattice n hn h J w) ∧
          ∀ γ ∈ adaptedLattice n hn h J w, γ ≠ 0 → (r : ℝ) + 1 < ‖γ‖) ∧
    (3 ≤ min (J * h) w → ∀ Γ : PeriodSublattice 1, Γ.toAmbient = adaptedLattice n hn h J w →
      Γ.SplitsAlongWithHalfPeriod n (J * h) ∧
        Γ.transversePart n (J * h) = adaptedTransverseLattice n hn w ∧
        IsAdaptedSideTuple n hn h J w (adaptedSideLengths n hn h J w) ∧
        Γ.IsBoxShaped (normalFrame n hn) (adaptedSideLengths n hn h J w)) ∧
    ((∀ i, shortPeriod n hn w i ∈ parallelPeriodLattice n) ∧
      longPeriod n h J ∈ normalPeriodLattice n h ∧
      adaptedLattice n hn h J w ≤ normalPeriodLattice n h ∧
      normalPeriodLattice n h ≤ axialPeriodLattice n h ∧
      (∀ (b : ℤ) (c : Fin 3 → ℤ),
        linearHeight n (b • longPeriod n h J + ∑ i, c i • shortPeriod n hn w i) =
          2 * (b : ℝ) * (J : ℝ) * (h : ℝ)) ∧
      adaptedLattice n hn h J w ⊓ parallelPeriodLattice n = adaptedTransverseLattice n hn w ∧
      (3 ≤ min (J * h) w → ∀ Γ : PeriodSublattice 1, Γ.toAmbient = adaptedLattice n hn h J w →
        adaptedLattice n hn h J w ⊓ parallelPeriodLattice n = Γ.transversePart n (J * h)))
end YangMills.Construction.NormalFamilies
