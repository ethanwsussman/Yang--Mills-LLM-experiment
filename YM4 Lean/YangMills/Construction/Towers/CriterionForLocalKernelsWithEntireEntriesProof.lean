import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.MatricesOnATorusInCoordinatesProof
import YangMills.Construction.Towers.CriterionForLocalKernelsWithEntireEntries
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
namespace Tower.FullSpace.EntireLocal
open PeriodicOperators
open EntireDependence
open TorusMetric (euclidNormVec)
theorem isHolomorphicIn_of_differentiable {l : ℕ} {h : Coordinates.ComplexCoordinates l → ℂ}
    (hd : Differentiable ℂ h) {O : Set (Coordinates.ComplexCoordinates l)} (hO : IsOpen O) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O (fun z _ => h z) := by
  refine ⟨hO, (continuous_pi fun _ => hd.continuous).continuousOn,
    fun a _ j => Filter.Eventually.of_forall fun w => ?_⟩
  refine differentiableAt_pi.2 fun _ => ?_
  exact DifferentiableAt.comp
    (f := fun t : ℂ => a + t • Coordinates.ComplexCoordinates.stdBasisVector j) w
    (hd _) (by fun_prop)
theorem isOpen_openPolydisk (l : ℕ) (r : ℝ) :
    IsOpen (Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk
      (0 : Coordinates.ComplexCoordinates l) r) := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isOpen_openPolydisk_zero <;> assumption
theorem exists_differentiable_of_isEntireOn {F : PeriodicData} {A : Set F.Carrier} {l : ℕ}
    (e : Fin l ≃ A) {S : Finset F.Carrier} (hS : ∀ k ∈ S, k ∈ A) {g : (F.Carrier → ℂ) → ℂ}
    (hg : IsEntireOn F S g) :
    ∃ h : Coordinates.ComplexCoordinates l → ℂ, Differentiable ℂ h ∧
      ∀ w, g w = h (fieldValues e w) := by
  obtain ⟨h₀, hd, hg⟩ := hg
  refine ⟨fun z => h₀ fun k => z (e.symm ⟨k, hS k k.2⟩), hd.comp (by fun_prop), fun w => ?_⟩
  rw [hg]
  simp [fieldValues]
theorem entireLocalCriterion_holds (h₁ : TowerIndexSets.Claim) (h₂ : CovariantFiniteRange.Claim) :
    EntireLocalCriterion.Criterion := by
  intro L hL k I I' T hpos hrange hread hcov
  have hF : IsPeriodic (remainderIndex L k) := (h₁ L hL k 0 (Nat.zero_le k)).2.1
  have hfin := (h₂.1 _ hF).1
  have hη : 0 ≤ 2 * finestMesh L k := by
    have : 0 ≤ finestMesh L k := zpow_nonneg (Nat.cast_nonneg L) _
    linarith
  have key : ∀ i' i, ∃ (l : ℕ)
      (e : Fin l ≃ nearIndices (remainderIndex L k) (I'.pos i') (2 * finestMesh L k))
      (h : Coordinates.ComplexCoordinates l → ℂ),
      1 ≤ l ∧ Differentiable ℂ h ∧ ∀ w, T w i' i = h (fieldValues e w) := by
    intro i' i
    have := (hfin (I'.pos i') (2 * finestMesh L k)).to_subtype
    obtain ⟨S, hS, hg⟩ := hread i' i
    let e := (Finite.equivFin
      (nearIndices (remainderIndex L k) (I'.pos i') (2 * finestMesh L k))).symm
    obtain ⟨h, hd, he⟩ := exists_differentiable_of_isEntireOn e hS hg
    obtain ⟨κ, hκ⟩ := hpos i'
    have hne : Nonempty
        (nearIndices (remainderIndex L k) (I'.pos i') (2 * finestMesh L k)) := by
      refine ⟨⟨κ, ?_⟩⟩
      change euclidNormVec ((remainderIndex L k).pos κ - I'.pos i') ≤ _
      rw [hκ, sub_self]
      simpa [euclidNormVec] using hη
    exact ⟨_, e, h, Nat.card_pos, hd, he⟩
  refine ⟨fun r hr => ⟨hr, fun w _ i' i h => hrange w i' i h, fun i' i => ?_,
    fun w _ n i' i => hcov w n i' i⟩, fun i' i => ?_⟩
  · obtain ⟨l, e, h, -, hd, he⟩ := key i' i
    exact ⟨l, e, h, isHolomorphicIn_of_differentiable hd (isOpen_openPolydisk l r),
      fun w _ => he w⟩
  · obtain ⟨l, e, h, h1, hd, he⟩ := key i' i
    exact ⟨_, l, e, h, ⟨h1, isHolomorphicIn_of_differentiable hd isOpen_univ⟩, he⟩
end Tower.FullSpace.EntireLocal
end YangMills.Construction
end
