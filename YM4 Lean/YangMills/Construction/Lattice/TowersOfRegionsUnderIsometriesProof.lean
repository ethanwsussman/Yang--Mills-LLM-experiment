import YangMills.Construction.Lattice.GluedSequencesAndSetsUnderIsometriesProof
import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegions
import YangMills.Construction.Lattice.TowersOfRegionsUnderIsometries
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric YangMills.Construction.ParameterChoice
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace IsometryTowers
variable {L m : ℕ}
def PreservesPartition (σ : FourTorus L m ≃ FourTorus L m) (c : ℤ) : Prop :=
  (fun Q => σ '' Q) '' standardCubePartition L m c = standardCubePartition L m c
theorem image_subset_image_equiv_iff (σ : FourTorus L m ≃ FourTorus L m) (A B : Set (FourTorus L m)) :
    σ '' A ⊆ σ '' B ↔ A ⊆ B :=
  Set.image_subset_image_iff σ.injective
theorem PreservesPartition.image_mem {σ : FourTorus L m ≃ FourTorus L m} {c : ℤ}
    (hσ : PreservesPartition σ c)
    {Q : Set (FourTorus L m)} (hQ : Q ∈ standardCubePartition L m c) :
    σ '' Q ∈ standardCubePartition L m c := by apply _root_.YangMills.Construction.PeriodicLattice.GluedChainIsometries.PreservesPartition.image_mem <;> assumption
theorem PreservesPartition.exists_preimage {σ : FourTorus L m ≃ FourTorus L m} {c : ℤ}
    (hσ : PreservesPartition σ c)
    {Q : Set (FourTorus L m)} (hQ : Q ∈ standardCubePartition L m c) :
    ∃ Q' ∈ standardCubePartition L m c, σ '' Q' = Q := by apply _root_.YangMills.Construction.PeriodicLattice.GluedChainIsometries.PreservesPartition.exists_preimage <;> assumption
theorem PreservesPartition.complementRegion_image {σ : FourTorus L m ≃ FourTorus L m} {c : ℤ}
    (hσ : PreservesPartition σ c) (X : Set (FourTorus L m)) :
    complementRegion c (σ '' X) = σ '' complementRegion c X := by
  ext x
  simp only [complementRegion, partitionCubesIn, mem_sUnion, mem_sdiff, mem_ofPred_eq, mem_image,
    not_and]
  constructor
  · rintro ⟨Q, ⟨hQ, hX⟩, hx⟩
    obtain ⟨Q', hQ', rfl⟩ := hσ.exists_preimage hQ
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, ⟨Q', ⟨hQ', fun _ hs => hX hQ ((image_subset_image_equiv_iff σ _ _).2 hs)⟩, hy⟩, rfl⟩
  · rintro ⟨y, ⟨Q, ⟨hQ, hX⟩, hy⟩, rfl⟩
    exact ⟨σ '' Q, ⟨hσ.image_mem hQ,
      fun _ hs => hX hQ ((image_subset_image_equiv_iff σ _ _).1 hs)⟩, mem_image_of_mem σ hy⟩
theorem selectedCubes_image {σ : FourTorus L m ≃ FourTorus L m} {a c : ℤ}
    (ha : PreservesPartition σ a) (hc : PreservesPartition σ c)
    (hdist : ∀ A B : Set (FourTorus L m), setSupDist (σ '' A) (σ '' B) = setSupDist A B)
    (K i : ℕ) (P : ℝ≥0∞ → Prop) (X : Set (FourTorus L m)) :
    ⋃₀ {Q | Q ∈ cubesOfIndex (m := m) (L := L) a ∧ Q ⊆ σ '' X ∧
        P (supDistInLevelUnits K i Q (complementRegion c (σ '' X)))} =
      σ '' ⋃₀ {Q | Q ∈ cubesOfIndex (m := m) (L := L) a ∧ Q ⊆ X ∧
        P (supDistInLevelUnits K i Q (complementRegion c X))} := by
  have hQdist : ∀ Q : Set (FourTorus L m),
      supDistInLevelUnits K i (σ '' Q) (complementRegion c (σ '' X)) =
        supDistInLevelUnits K i Q (complementRegion c X) := fun Q => by
    simp only [supDistInLevelUnits, hc.complementRegion_image, hdist]
  ext x
  simp only [mem_sUnion, mem_ofPred_eq, mem_image, cubesOfIndex]
  constructor
  · rintro ⟨Q, ⟨⟨hmem, hQ⟩, hX, hP⟩, hx⟩
    obtain ⟨Q', hQ', rfl⟩ := ha.exists_preimage hQ
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, ⟨Q', ⟨⟨hmem, hQ'⟩, (image_subset_image_equiv_iff σ _ _).1 hX,
      by rwa [hQdist] at hP⟩, hy⟩, rfl⟩
  · rintro ⟨y, ⟨Q, ⟨⟨hmem, hQ⟩, hX, hP⟩, hy⟩, rfl⟩
    exact ⟨σ '' Q, ⟨⟨hmem, ha.image_mem hQ⟩, (image_subset_image_equiv_iff σ _ _).2 hX,
      by rwa [hQdist]⟩, mem_image_of_mem σ hy⟩
theorem scaledCubeIndex_antitone (K a : ℕ) {p q : ℕ} (hpq : p ≤ q) :
    scaledCubeIndex K q a ≤ scaledCubeIndex K p a := by
  simp only [scaledCubeIndex, levelDepth]
  omega
end IsometryTowers
open IsometryTowers in
theorem isometriesPreserveTowers_of_groupAction (hG : LatticeIsometryGroupActionStatement) :
    IsometriesPreserveTowers := by
  intro L m i σ hL hm hi hσ K k n e r l d Ω _ _ _ hΩ
  obtain ⟨-, hiso, -, -, hcar⟩ := hG L m i hL hm hi
  have hdist : ∀ A B : Set (FourTorus L m), setSupDist (σ '' A) (σ '' B) = setSupDist A B :=
    (hiso σ hσ).1.2.2.2.1
  have hpres : ∀ j, i ≤ j → PreservesPartition σ j :=
    fun j hj => (hcar σ hσ j hj).1.2.2.2.2.2.2.2.2.2
  refine ⟨?_, fun hidx p hp => ?_, fun hidx p hp => ?_⟩
  · obtain ⟨c, hic, hcn, hR⟩ := hΩ
    exact ⟨c, hic, hcn, ((hcar σ hσ c hic).2.1 Ω).2 hR⟩
  · induction p with
    | zero => rfl
    | succ p ih =>
      have hnext : i ≤ scaledCubeIndex K (l + p + 1) e :=
        le_trans hidx (scaledCubeIndex_antitone K e (by omega))
      have hcur : i ≤ scaledCubeIndex K (l + p) e :=
        le_trans hidx (scaledCubeIndex_antitone K e (by omega))
      change separatedTowerStep K e r l (l + p) (separatedTower K e r l (σ '' Ω) p) =
        σ '' separatedTowerStep K e r l (l + p) (separatedTower K e r l Ω p)
      rw [ih (by omega)]
      exact selectedCubes_image (hpres _ hnext) (hpres _ hcur) hdist K l
        (fun t => separationGap L e r l (l + p) < t) _
  · induction p with
    | zero => rfl
    | succ p ih =>
      have hnext : i ≤ scaledCubeIndex K (l + p + 1) n :=
        le_trans hidx (scaledCubeIndex_antitone K n (by omega))
      have hcur : i ≤ scaledCubeIndex K (l + p) n :=
        le_trans hidx (scaledCubeIndex_antitone K n (by omega))
      change shrinkingTowerStep K n l (l + p) (shrinkingTower K n l (σ '' Ω) p) =
        σ '' shrinkingTowerStep K n l (l + p) (shrinkingTower K n l Ω p)
      rw [ih (by omega)]
      exact selectedCubes_image (hpres _ hnext) (hpres _ hcur) hdist K l
        (fun t => shrinkingGap L n l (l + p) ≤ t) _
end YangMills.Construction.PeriodicLattice
