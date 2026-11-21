import YangMills.Construction.Lattice.AveragingAtAnOrientedBondUnderAnIsometry
import YangMills.Construction.Lattice.AveragingMapIsABorelMap
import YangMills.Construction.Lattice.BlocksAndLinearSizesUnderIsometriesProof
import YangMills.Construction.Lattice.CovarianceOfTheAveragingMaps
import YangMills.Construction.Lattice.LiftingIsConsistentWithTheAverages
import YangMills.Construction.Lattice.LinearisedAverageOfAOneFormUnderIsometries
import YangMills.Construction.Lattice.ReversalOfTheAveragingAtABond
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.EquivarianceProof
open IsometryInvariance
variable {L m : ℕ}
structure PreservesFrom (σ : FourTorus L m ≃ FourTorus L m) (i : ℤ) : Prop where
  endpoints : ∀ j : ℤ, i ≤ j → ∀ b : Bond L m j,
    ((bondImage σ b).source : FourTorus L m) = σ b.source ∧
      ((bondImage σ b).target : FourTorus L m) = σ b.target
  sites : ∀ j : ℤ, i ≤ j → ∀ y : Site L m j,
    ((sitePreimage σ.symm y : Site L m j) : FourTorus L m) = σ y
  blocks : ∀ j : ℤ, i ≤ j → MapsBlocks σ j
theorem preservesFrom_of_mem (hG : LatticeIsometryGroupActionStatement)
    (hB : IsometryInvariance.InvariantUnderIsometries)
    (hs : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i) {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : σ ∈ latticeIsometries L m i) : PreservesFrom σ i := by
  have hC := fun j (hj : i ≤ j) => ((hG L m i hs hm hi).2.2.2.2 σ hσ j hj).1
  refine ⟨fun j hj => (hC j hj).2.2.2.1, fun j hj y => ?_,
    fun j hj => ((hB L m hs hm i hi σ hσ).1 j hj).1⟩
  have hex : ∃ x : Site L m j, (x : FourTorus L m) = σ.symm.symm y := by
    have hmem : σ y ∈ σ '' (sublattice L m j : Set (FourTorus L m)) := ⟨y, y.2, rfl⟩
    rw [(hC j hj).1] at hmem
    exact ⟨⟨σ y, hmem⟩, rfl⟩
  exact Classical.epsilon_spec hex
theorem symm_mem_latticeIsometries (hG : LatticeIsometryGroupActionStatement)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) :
    σ.symm ∈ latticeIsometries L m i := by
  obtain ⟨H, hH⟩ := (hG L m i hs hm hi).1.1
  have h1 : σ ∈ H := by
    have : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
    exact this
  have h2 : σ⁻¹ ∈ H := H.inv_mem h1
  have h3 : σ⁻¹ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := h2
  rw [hH] at h3
  exact h3
section Bonds
variable {σ : FourTorus L m ≃ FourTorus L m} {i j : ℤ}
theorem bondPreimage_ends (h' : PreservesFrom σ.symm i) (hj : i ≤ j) (b : Bond L m j) :
    ((bondPreimage σ b).source : FourTorus L m) = σ.symm b.source ∧
      ((bondPreimage σ b).target : FourTorus L m) = σ.symm b.target :=
  h'.endpoints j hj b
theorem bondPreimage_bondImage (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i)
    (hj : i ≤ j) (c : Bond L m j) : bondPreimage σ (bondImage σ c) = c := by
  have e := h.endpoints j hj c
  have p := bondPreimage_ends h' hj (bondImage σ c)
  apply Bond.ext <;> apply Subtype.ext
  · rw [p.1, e.1]; simp
  · rw [p.2, e.2]; simp
theorem bondImage_bondPreimage (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i)
    (hj : i ≤ j) (b : Bond L m j) : bondImage σ (bondPreimage σ b) = b :=
  bondPreimage_bondImage (σ := σ.symm) h' h hj b
theorem transportGaugeField_bondImage (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i)
    (hj : i ≤ j) (U : Bond L m j → Matrices.ComplexMatrix2) (c : Bond L m j) :
    transportGaugeField σ U (bondImage σ c) = U c :=
  congrArg U (bondPreimage_bondImage h h' hj c)
theorem bondPreimage_opposite (h' : PreservesFrom σ.symm i) (hj : i ≤ j) (b : Bond L m j) :
    bondPreimage σ b.opposite = (bondPreimage σ b).opposite := by
  have p := bondPreimage_ends h' hj b
  have q := bondPreimage_ends h' hj b.opposite
  apply Bond.ext <;> apply Subtype.ext
  · exact q.1.trans p.2.symm
  · exact q.2.trans p.1.symm
theorem bondImage_opposite (h : PreservesFrom σ i) (hj : i ≤ j) (b : Bond L m j) :
    bondImage σ b.opposite = (bondImage σ b).opposite :=
  bondPreimage_opposite (σ := σ.symm) h hj b
theorem transportGaugeField_mem (h' : PreservesFrom σ.symm i) (hj : i ≤ j)
    {U : Bond L m j → Matrices.ComplexMatrix2} (hU : U ∈ compactGaugeFields L m j) :
    transportGaugeField σ U ∈ compactGaugeFields L m j := by
  refine ⟨fun b _ => hU.1 _ (mem_univ _), fun b _ => ?_⟩
  show U (bondPreimage σ b.opposite) = (U (bondPreimage σ b))⁻¹
  rw [bondPreimage_opposite h' hj]
  exact hU.2 _ (mem_univ _)
theorem transportGaugeField_symm (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i)
    (hj : i ≤ j) (U : Bond L m j → Matrices.ComplexMatrix2) :
    transportGaugeField σ (transportGaugeField σ.symm U) = U :=
  funext fun b => congrArg U (bondImage_bondPreimage h h' hj b)
theorem mem_image_equiv_iff (X : Set (FourTorus L m)) (t : FourTorus L m) :
    t ∈ σ '' X ↔ σ.symm t ∈ X := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.mem_image_equiv_iff <;> assumption
theorem mem_bondsInside_image (h' : PreservesFrom σ.symm i) (hj : i ≤ j)
    (X : Set (FourTorus L m)) (b : Bond L m j) :
    b ∈ (bondsInside (σ '' X) : Set (Bond L m j)) ↔
      bondPreimage σ b ∈ (bondsInside X : Set (Bond L m j)) := by
  have p := bondPreimage_ends h' hj b
  show ((b.source : FourTorus L m) ∈ σ '' X ∧ (b.target : FourTorus L m) ∈ σ '' X) ↔
    (((bondPreimage σ b).source : FourTorus L m) ∈ X ∧
      ((bondPreimage σ b).target : FourTorus L m) ∈ X)
  rw [p.1, p.2, mem_image_equiv_iff, mem_image_equiv_iff]
theorem extendByOne_transport (h' : PreservesFrom σ.symm i) (hj : i ≤ j)
    (X : Set (FourTorus L m)) (U : Bond L m j → Matrices.ComplexMatrix2) :
    extendByOne (bondsInside (σ '' X)) (transportGaugeField σ U) =
      transportGaugeField σ (extendByOne (bondsInside X) U) := by
  funext b
  have hiff := mem_bondsInside_image h' hj X b
  simp only [extendByOne, transportGaugeField]
  by_cases hb : b ∈ (bondsInside (σ '' X) : Set (Bond L m j))
  · rw [if_pos hb, if_pos (hiff.1 hb)]
  · rw [if_neg hb, if_neg (mt hiff.2 hb)]
theorem bondsInside_isReversalClosed (X : Set (FourTorus L m)) :
    IsReversalClosed (bondsInside X : Set (Bond L m j)) :=
  fun _ hb => ⟨hb.2, hb.1⟩
theorem extendByOne_mem {X : Set (FourTorus L m)} {U : Bond L m j → Matrices.ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup (bondsInside X) U) :
    extendByOne (bondsInside X) U ∈ compactGaugeFields L m j :=
  extendByOne_mem_compactGaugeFields (bondsInside_isReversalClosed X) hU
theorem bondsInside_image_subset_iff (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i)
    (hj : i ≤ j) (Y Z : Set (FourTorus L m)) :
    (bondsInside (σ '' Y) : Set (Bond L m j)) ⊆ bondsInside (σ '' Z) ↔
      (bondsInside Y : Set (Bond L m j)) ⊆ bondsInside Z := by
  constructor
  · intro hs b hb
    have h1 : bondImage σ b ∈ (bondsInside (σ '' Y) : Set (Bond L m j)) := by
      rw [mem_bondsInside_image h' hj, bondPreimage_bondImage h h' hj]; exact hb
    have h2 := hs h1
    rwa [mem_bondsInside_image h' hj, bondPreimage_bondImage h h' hj] at h2
  · intro hs b hb
    rw [mem_bondsInside_image h' hj] at hb ⊢
    exact hs hb
end Bonds
section OneStep
variable {σ : FourTorus L m ≃ FourTorus L m} {i : ℤ} {K : ℕ}
theorem opposite_opposite {j : ℤ} (c : Bond L m j) : c.opposite.opposite = c := Bond.ext rfl rfl
theorem blockAverage_eq_onPositive (hR : BlockAverageAtOpposite)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {j j' : ℤ} (hj : 0 ≤ j)
    (hjj : j' = j + 1) (ω : ℝ) (c : Bond L m j) {U : Bond L m j' → Matrices.ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j') :
    blockAverage ω U c = blockAverageOnPositive ω U c := by
  by_cases hc : c.IsPositivelyOriented
  · simp only [blockAverage, if_pos hc]
  · simp only [blockAverage, if_neg hc]
    have := (hR L m hs hm j j' hj hjj ω c.opposite U hU).2
    rw [opposite_opposite] at this
    exact this.symm
theorem blockAverageCase_positivelyOriented (hR : BlockAverageAtOpposite)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {j j' : ℤ} (hj : 0 ≤ j)
    (hjj : j' = j + 1) (ω : ℝ) (c : Bond L m j) {U : Bond L m j' → Matrices.ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j') :
    blockAverageCase ω U c.positivelyOriented = blockAverageCase ω U c := by
  by_cases hc : c.IsPositivelyOriented
  · simp only [Bond.positivelyOriented, if_pos hc]
  · simp only [Bond.positivelyOriented, if_neg hc]
    exact (hR L m hs hm j j' hj hjj ω c U hU).1
theorem levelDepth_succ {K k : ℕ} (hk : k < K) :
    0 ≤ levelDepth K (k + 1) ∧ levelDepth K k = levelDepth K (k + 1) + 1 := by
  constructor <;> simp only [levelDepth] <;> push_cast <;> omega
theorem levelDepth_anti {K k k' : ℕ} (hk : k ≤ k') : levelDepth K k' ≤ levelDepth K k := by
  simp only [levelDepth]; omega
theorem stepEquivariant (hA : BlockAverageCommutesWithIsometries)
    (hR : BlockAverageAtOpposite) (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hi : -(m : ℤ) ≤ i) (hσ : σ ∈ latticeIsometries L m i) (h : PreservesFrom σ i)
    (h' : PreservesFrom σ.symm i) : BlockAverageStepEquivariant K i σ := by
  intro k hk hik
  obtain ⟨hj0, hjj⟩ := levelDepth_succ hk
  have hik' : i ≤ levelDepth K k := hik.trans (levelDepth_anti (Nat.le_succ k))
  have hA' := fun (c : BondAtLevel L m K (k + 1)) (U : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (hU : U ∈ compactGaugeFields L m (levelDepth K k)) =>
      hA L m hs hm i hi σ hσ (levelDepth K (k + 1)) (levelDepth K k) hik hj0 hjj
        (Averaging.smoothingRadius L) c U hU
  refine ⟨fun c => ?_, fun U hU => ⟨fun c => ?_, ?_⟩⟩
  · ext U'
    constructor
    · rintro ⟨U, ⟨hU, hS⟩, rfl⟩
      exact ⟨transportGaugeField_mem h' hik' hU, (hA' c U hU).1.2 hS⟩
    · rintro ⟨hU', hS⟩
      have hU : transportGaugeField σ.symm U' ∈ compactGaugeFields L m (levelDepth K k) :=
        transportGaugeField_mem (σ := σ.symm) h hik' hU'
      refine ⟨transportGaugeField σ.symm U', ⟨hU, ?_⟩, transportGaugeField_symm h h' hik' U'⟩
      have h3 := (hA' c _ hU).1
      rw [transportGaugeField_symm h h' hik'] at h3
      exact h3.1 hS
  · have hσU := transportGaugeField_mem (σ := σ) h' hik' hU
    show blockAverageCase _ U c.positivelyOriented =
      blockAverageCase _ (transportGaugeField σ U) (bondImage σ c).positivelyOriented
    rw [blockAverageCase_positivelyOriented hR hs hm hj0 hjj _ c hU,
      blockAverageCase_positivelyOriented hR hs hm hj0 hjj _ _ hσU]
    exact (hA' c U hU).2.1.symm
  · have hσU := transportGaugeField_mem (σ := σ) h' hik' hU
    funext b
    obtain ⟨c, rfl⟩ : ∃ c, b = bondImage σ c := ⟨_, (bondImage_bondPreimage h h' hik b).symm⟩
    rw [transportGaugeField_bondImage h h' hik, blockAverage_eq_onPositive hR hs hm hj0 hjj _ _ hσU,
      blockAverage_eq_onPositive hR hs hm hj0 hjj _ _ hU]
    exact (hA' c U hU).2.2
theorem blockFieldAtLevel_mem (hW : BlockAverageIsBorelMap)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    {U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2} (hU : U ∈ gaugeFieldsAtLevel L m K 0)
    (k : ℕ) (hk : k ≤ K) :
    blockFieldAtLevel (Averaging.smoothingRadius L) k U ∈ gaugeFieldsAtLevel L m K k := by
  induction k with
  | zero => exact hU
  | succ k ih =>
    have hK : 0 < K := by omega
    obtain ⟨hmaps, -⟩ := hW ⟨L, hs, ⟨K, hK⟩, ⟨m, hm⟩⟩ k hk
    exact hmaps (ih (by omega))
theorem blockFieldEquivariant (hW : BlockAverageIsBorelMap)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hstep : BlockAverageStepEquivariant K i σ) :
    BlockFieldEquivariant K i σ := by
  intro k
  induction k with
  | zero => intro _ _ _ _; rfl
  | succ k ih =>
    intro hk hik U hU
    have hik' : i ≤ levelDepth K k := hik.trans (levelDepth_anti (Nat.le_succ k))
    show blockAverage _ (blockFieldAtLevel _ k (transportGaugeField σ U)) =
      transportGaugeField σ (blockAverage _ (blockFieldAtLevel _ k U))
    rw [ih (by omega) hik' U hU]
    exact ((hstep k hk hik).2 _ (blockFieldAtLevel_mem hW hs hm hU k (by omega))).2
theorem linearAverageEquivariant (hD : LinearAverageIsometryCovariance)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hi : -(m : ℤ) ≤ i)
    (hσ : σ ∈ latticeIsometries L m i) (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i) :
    LinearBlockAverageEquivariant K i σ := by
  intro k hk hik A _
  obtain ⟨hj0, hjj⟩ := levelDepth_succ hk
  have hsum := fun c : BondAtLevel L m K (k + 1) =>
    (hD L m hs hm (levelDepth K (k + 1)) (levelDepth K k) hj0 hjj).2 i hi hik σ hσ A c
  constructor
  · funext b
    obtain ⟨c, rfl⟩ : ∃ c, b = bondImage σ c := ⟨_, (bondImage_bondPreimage h h' hik b).symm⟩
    show _ • linearBlockSum (transportForm σ A) (bondImage σ c) =
      linearBlockAverage A (bondPreimage σ (bondImage σ c))
    rw [hsum, bondPreimage_bondImage h h' hik]
    rfl
  · funext b
    obtain ⟨c, rfl⟩ : ∃ c, b = bondImage σ c := ⟨_, (bondImage_bondPreimage h h' hik b).symm⟩
    show _ • linearBlockSum (transportForm σ A) (bondImage σ c) =
      scaledLinearBlockAverage A (bondPreimage σ (bondImage σ c))
    rw [hsum, bondPreimage_bondImage h h' hik]
    rfl
theorem linearIterates_isBondForm (hD : LinearAverageIsometryCovariance)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {k : ℕ}
    {A : BondAtLevel L m K k → Matrices.ComplexMatrix2}
    (hA : IsBondForm complexLieAlgebra A) (n : ℕ) (hn : k + n ≤ K) :
    IsBondForm complexLieAlgebra (linearBlockIterateBetween (K := K) k n A) ∧
      IsBondForm complexLieAlgebra (scaledLinearBlockIterateFrom (K := K) k n A) := by
  induction n with
  | zero => exact ⟨hA, hA⟩
  | succ n ih =>
    have hk : k + n < K := by omega
    obtain ⟨hj0, hjj⟩ := levelDepth_succ hk
    obtain ⟨i1, i2⟩ := ih (by omega)
    exact ⟨((hD L m hs hm (levelDepth K (k + n + 1)) (levelDepth K (k + n)) hj0 hjj).1 _ i1).1,
      ((hD L m hs hm (levelDepth K (k + n + 1)) (levelDepth K (k + n)) hj0 hjj).1 _ i2).2⟩
theorem linearIterateEquivariant (hD : LinearAverageIsometryCovariance)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hlin : LinearBlockAverageEquivariant K i σ) :
    LinearBlockIterateEquivariant K i σ := by
  intro k n
  induction n with
  | zero => intro _ _ _ _; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro hn hik A hA
    have hik' : i ≤ levelDepth K (k + n) := hik.trans (levelDepth_anti (by omega))
    obtain ⟨e1, e2⟩ := ih (by omega) hik' A hA
    obtain ⟨f1, f2⟩ := linearIterates_isBondForm hD hs hm hA n (by omega)
    constructor
    · show linearBlockAverage (linearBlockIterateBetween (K := K) k n (transportForm σ A)) =
        transportForm σ (linearBlockAverage (linearBlockIterateBetween (K := K) k n A))
      rw [e1]
      exact (hlin (k + n) (by omega) hik _ f1).1
    · show scaledLinearBlockAverage
          (scaledLinearBlockIterateFrom (K := K) k n (transportForm σ A)) =
        transportForm σ (scaledLinearBlockAverage (scaledLinearBlockIterateFrom (K := K) k n A))
      rw [e2]
      exact (hlin (k + n) (by omega) hik _ f2).2
theorem partialAverageEquivariant (h' : PreservesFrom σ.symm i)
    (hstep : BlockAverageStepEquivariant K i σ) :
    PartialBlockAverageEquivariant K i σ := by
  intro k hk a hia haK X _ U hU b _
  have hik : i ≤ levelDepth K (k + 1) := hia.trans haK
  have hik' : i ≤ levelDepth K k := hik.trans (levelDepth_anti (Nat.le_succ k))
  show blockAverage _ (extendByOne (bondsInside (σ '' X)) (transportGaugeField σ U)) b =
    transportGaugeField σ (blockAverage _ (extendByOne (bondsInside X) U)) b
  rw [extendByOne_transport h' hik']
  exact congrFun ((hstep k hk hik).2 _ (extendByOne_mem hU)).2 b
theorem bondImage_source (h : PreservesFrom σ i) {j : ℤ} (hj : i ≤ j) (c : Bond L m j) :
    (bondImage σ c).source = sitePreimage σ.symm c.source :=
  Subtype.ext ((h.endpoints j hj c).1.trans (h.sites j hj c.source).symm)
theorem bondImage_target (h : PreservesFrom σ i) {j : ℤ} (hj : i ≤ j) (c : Bond L m j) :
    (bondImage σ c).target = sitePreimage σ.symm c.target :=
  Subtype.ext ((h.endpoints j hj c).2.trans (h.sites j hj c.target).symm)
theorem regionEquivariant (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i)
    (hfields : BlockFieldEquivariant K i σ) :
    RegionBlockFieldEquivariant K i σ := by
  intro k hk hik a hia haK Ω₀ _ U hU c
  have hi0 : i ≤ levelDepth K 0 := hia.trans haK
  constructor
  · have e : refinedBlock k (bondImage σ c).source ∪ refinedBlock k (bondImage σ c).target =
        σ '' (refinedBlock k c.source ∪ refinedBlock k c.target) := by
      rw [image_union, h.blocks _ hik, h.blocks _ hik, bondImage_source h hik,
        bondImage_target h hik]
    show (bondsInside (refinedBlock k (bondImage σ c).source ∪
        refinedBlock k (bondImage σ c).target) :
        Set (BondAtLevel L m K 0)) ⊆ bondsInside (σ '' Ω₀) ↔ _
    rw [e]
    exact bondsInside_image_subset_iff h h' hi0 _ _
  · intro _
    show blockFieldAtLevel _ k (extendByOne (bondsInside (σ '' Ω₀)) (transportGaugeField σ U))
        (bondImage σ c) = blockFieldAtLevel _ k (extendByOne (bondsInside Ω₀) U) c
    rw [extendByOne_transport h' hi0, hfields k hk hik _ (extendByOne_mem hU),
      transportGaugeField_bondImage h h' hik]
theorem averagingOnDeterminingSet_image (h' : PreservesFrom σ.symm i)
    (hfields : BlockFieldEquivariant K i σ) {j : ℕ} (hjK : j ≤ K) (hij : i ≤ levelDepth K j)
    (X : Set (FourTorus L m)) {U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2}
    (hU : IsGaugeField compactGaugeGroup (bondsInside X) U) :
    (averagingOnDeterminingSet (Averaging.smoothingRadius L) K (σ '' X)
        (transportGaugeField σ U) j : BondAtLevel L m K j → Matrices.ComplexMatrix2) =
      transportGaugeField σ (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U j) := by
  have hi0 : i ≤ levelDepth K 0 := hij.trans (levelDepth_anti (Nat.zero_le j))
  show blockFieldAtLevel _ j (extendByOne (bondsInside (σ '' X)) (transportGaugeField σ U)) = _
  rw [extendByOne_transport h' hi0]
  exact hfields j hjK hij _ (extendByOne_mem hU)
theorem determiningEquivariant (h' : PreservesFrom σ.symm i)
    (hfields : BlockFieldEquivariant K i σ) :
    DeterminingAverageEquivariant K i σ := by
  intro k Ω hΩ U hU j hj c _
  obtain ⟨hkK, -, hreg⟩ := hΩ
  obtain ⟨a, hia, haj, -⟩ := hreg j hj
  exact congrFun
    (averagingOnDeterminingSet_image h' hfields (by omega) (hia.trans haj) (Ω 0) hU) c
end OneStep
section Lifts
variable {σ : FourTorus L m ≃ FourTorus L m} {i : ℤ} {K k : ℕ}
theorem endsInOneBlock_bondImage (h : PreservesFrom σ i) (hik : i ≤ levelDepth K k) {j : ℕ}
    (hj : i ≤ levelDepth K j) {b : BondAtLevel L m K j} (hb : EndsInOneBlock k b) :
    EndsInOneBlock k (bondImage σ b) := by
  obtain ⟨y, h1, h2⟩ := hb
  refine ⟨sitePreimage σ.symm y, ?_, ?_⟩
  · show ((bondImage σ b).source : FourTorus L m) ∈ refinedBlock (k - j) (sitePreimage σ.symm y)
    rw [(h.endpoints _ hj b).1, ← h.blocks _ hik (k - j) y]
    exact ⟨_, h1, rfl⟩
  · show ((bondImage σ b).target : FourTorus L m) ∈ refinedBlock (k - j) (sitePreimage σ.symm y)
    rw [(h.endpoints _ hj b).2, ← h.blocks _ hik (k - j) y]
    exact ⟨_, h2, rfl⟩
theorem endsInOneBlock_bondImage_iff (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i)
    (hik : i ≤ levelDepth K k) {j : ℕ} (hj : i ≤ levelDepth K j) (b : BondAtLevel L m K j) :
    EndsInOneBlock k (bondImage σ b) ↔ EndsInOneBlock k b := by
  refine ⟨fun hb => ?_, endsInOneBlock_bondImage h hik hj⟩
  have := endsInOneBlock_bondImage (σ := σ.symm) h' hik hj hb
  have e : bondImage σ.symm (bondImage σ b) = b := bondPreimage_bondImage h h' hj b
  rwa [e] at this
theorem coversBond_bondImage (h : PreservesFrom σ i) (hik : i ≤ levelDepth K k) {j : ℕ}
    (hj : i ≤ levelDepth K j) {c : BondAtLevel L m K k} {b : BondAtLevel L m K j}
    (hb : CoversBond c b) : CoversBond (bondImage σ c) (bondImage σ b) := by
  obtain ⟨h1, h2⟩ := hb
  constructor
  · show ((bondImage σ b).source : FourTorus L m) ∈ refinedBlock (k - j) (bondImage σ c).source
    rw [(h.endpoints _ hj b).1, bondImage_source h hik, ← h.blocks _ hik (k - j) c.source]
    exact ⟨_, h1, rfl⟩
  · show ((bondImage σ b).target : FourTorus L m) ∈ refinedBlock (k - j) (bondImage σ c).target
    rw [(h.endpoints _ hj b).2, bondImage_target h hik, ← h.blocks _ hik (k - j) c.target]
    exact ⟨_, h2, rfl⟩
theorem coversBond_bondImage_iff (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i)
    (hik : i ≤ levelDepth K k) {j : ℕ} (hj : i ≤ levelDepth K j) (c : BondAtLevel L m K k)
    (b : BondAtLevel L m K j) :
    CoversBond (bondImage σ c) (bondImage σ b) ↔ CoversBond c b := by
  refine ⟨fun hb => ?_, coversBond_bondImage h hik hj⟩
  have := coversBond_bondImage (σ := σ.symm) h' hik hj hb
  have e : bondImage σ.symm (bondImage σ b) = b := bondPreimage_bondImage h h' hj b
  have e' : bondImage σ.symm (bondImage σ c) = c := bondPreimage_bondImage h h' hik c
  rwa [e, e'] at this
theorem endsInOneBlock_or_existsUnique_covers (hLift : LiftConsistentWithAverages)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K) (hk : k ≤ K)
    {j : ℕ} (hj : j ≤ k) (b : BondAtLevel L m K j) :
    EndsInOneBlock k b ∨ ∃! c : BondAtLevel L m K k, CoversBond c b :=
  ((hLift L m K hs hm hK k hk ∅ (fun _ hb => hb.elim) (fun _ => 1)
    (Or.inl ⟨fun _ hb => hb.elim, fun _ hb => hb.elim⟩)).1 j hj).2 b |>.1
theorem coveredBond_bondImage (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i)
    (hik : i ≤ levelDepth K k) {j : ℕ} (hij : i ≤ levelDepth K j)
    (hio : ∀ b : BondAtLevel L m K j,
      EndsInOneBlock k b ∨ ∃! c : BondAtLevel L m K k, CoversBond c b)
    {b : BondAtLevel L m K j} (hb : ¬EndsInOneBlock k b) :
    (coveredBond k (bondImage σ b) : BondAtLevel L m K k) = bondImage σ (coveredBond k b) := by
  obtain ⟨c, hc, -⟩ := (hio b).resolve_left hb
  have hb' : ¬EndsInOneBlock k (bondImage σ b) :=
    mt (endsInOneBlock_bondImage_iff h h' hik hij b).1 hb
  obtain ⟨c', hc', hu'⟩ := (hio (bondImage σ b)).resolve_left hb'
  have e1 : CoversBond (coveredBond k b : BondAtLevel L m K k) b :=
    Classical.epsilon_spec (p := fun c => CoversBond c b) ⟨c, hc⟩
  have e2 : CoversBond (coveredBond k (bondImage σ b) : BondAtLevel L m K k) (bondImage σ b) :=
    Classical.epsilon_spec (p := fun c => CoversBond c (bondImage σ b)) ⟨c', hc'⟩
  exact (hu' _ e2).trans (hu' _ (coversBond_bondImage h hik hij e1)).symm
theorem liftToFinerLevel_image (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i)
    (hik : i ≤ levelDepth K k) {j : ℕ} (hij : i ≤ levelDepth K j)
    (hio : ∀ b : BondAtLevel L m K j,
      EndsInOneBlock k b ∨ ∃! c : BondAtLevel L m K k, CoversBond c b)
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) (b : BondAtLevel L m K j) :
    liftToFinerLevel j (transportGaugeField σ V) (bondImage σ b) = liftToFinerLevel j V b := by
  have hiff := endsInOneBlock_bondImage_iff (k := k) h h' hik hij b
  simp only [liftToFinerLevel]
  by_cases hb : EndsInOneBlock k b
  · rw [if_pos hb, if_pos (hiff.2 hb)]
  · rw [if_neg hb, if_neg (mt hiff.1 hb), coveredBond_bondImage h h' hik hij hio hb,
      transportGaugeField_bondImage h h' hik]
theorem isLevelLiftData_transport (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i)
    (hik : i ≤ levelDepth K k) {𝒢 : Set Matrices.ComplexMatrix2} {j : ℕ}
    {V : PartialGaugeField L m (levelDepth K k)}
    (hV : IsLevelLiftData (K := K) 𝒢 j V) :
    IsLevelLiftData (K := K) 𝒢 j (transportPartialGaugeField σ V) := by
  obtain ⟨h1, h2, hc, hv1, hv2⟩ := hV
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact ⟨b.opposite, hc b hb, bondImage_opposite h hik b⟩
  · rintro _ ⟨b, hb, rfl⟩
    show transportGaugeField σ V.field (bondImage σ b) ∈ 𝒢
    rw [transportGaugeField_bondImage h h' hik]
    exact hv1 b hb
  · rintro _ ⟨b, hb, rfl⟩
    show transportGaugeField σ V.field (bondImage σ b).opposite =
      (transportGaugeField σ V.field (bondImage σ b))⁻¹
    rw [← bondImage_opposite h hik, transportGaugeField_bondImage h h' hik,
      transportGaugeField_bondImage h h' hik]
    exact hv2 b hb
theorem orderLiftPartial_transport (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i)
    (hik : i ≤ levelDepth K k) {j : ℕ} (hij : i ≤ levelDepth K j)
    (hio : ∀ b : BondAtLevel L m K j,
      EndsInOneBlock k b ∨ ∃! c : BondAtLevel L m K k, CoversBond c b)
    (𝒞 : Set (BondAtLevel L m K k)) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    (orderLiftPartial j (bondImage σ '' 𝒞) (transportGaugeField σ V)).EqOnSupport
      (transportPartialGaugeField σ (orderLiftPartial j 𝒞 V)) := by
  have hmem : ∀ b : BondAtLevel L m K j,
      bondImage σ b ∈ liftSupport j (bondImage σ '' 𝒞) ↔ b ∈ liftSupport j 𝒞 := by
    intro b
    constructor
    · rintro (hb | ⟨_, ⟨c, hc, rfl⟩, hb⟩)
      · exact Or.inl ((endsInOneBlock_bondImage_iff h h' hik hij b).1 hb)
      · exact Or.inr ⟨c, hc, (coversBond_bondImage_iff h h' hik hij c b).1 hb⟩
    · rintro (hb | ⟨c, hc, hb⟩)
      · exact Or.inl ((endsInOneBlock_bondImage_iff h h' hik hij b).2 hb)
      · exact Or.inr ⟨_, ⟨c, hc, rfl⟩, (coversBond_bondImage_iff h h' hik hij c b).2 hb⟩
  refine ⟨?_, ?_⟩
  · ext b'
    obtain ⟨b, rfl⟩ : ∃ b, b' = bondImage σ b := ⟨_, (bondImage_bondPreimage h h' hij b').symm⟩
    show bondImage σ b ∈ liftSupport j (bondImage σ '' 𝒞) ↔
      bondImage σ b ∈ bondImage σ '' liftSupport j 𝒞
    rw [hmem]
    constructor
    · exact fun hb => ⟨b, hb, rfl⟩
    · rintro ⟨b₁, hb₁, e⟩
      have : b₁ = b := by
        have e' := congrArg (bondPreimage σ) e
        rwa [bondPreimage_bondImage h h' hij, bondPreimage_bondImage h h' hij] at e'
      exact this ▸ hb₁
  · intro b' _
    obtain ⟨b, rfl⟩ : ∃ b, b' = bondImage σ b := ⟨_, (bondImage_bondPreimage h h' hij b').symm⟩
    show liftToFinerLevel j (transportGaugeField σ V) (bondImage σ b) =
      transportGaugeField σ (liftToFinerLevel j V) (bondImage σ b)
    rw [liftToFinerLevel_image h h' hik hij hio, transportGaugeField_bondImage h h' hij]
theorem coincides_transport_of_coincides (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i)
    {j : ℤ} (hj : i ≤ j) {W W' A B : PartialGaugeField L m j} (h1 : W.Coincides A)
    (h2 : W'.Coincides B) (h3 : A.EqOnSupport (transportPartialGaugeField σ B)) :
    W.EqOnSupport (transportPartialGaugeField σ W') := by
  have hb : W.support = bondImage σ '' W'.support := by
    rw [h1.1, h3.1, h2.1]
    rfl
  refine ⟨hb, fun b hbW => ?_⟩
  have hbA : b ∈ A.support := h1.1 ▸ hbW
  rw [h1.2 b hbW, h3.2 b hbA]
  rw [hb] at hbW
  obtain ⟨b₁, hb₁, rfl⟩ := hbW
  show transportGaugeField σ B.field (bondImage σ b₁) =
    transportGaugeField σ W'.field (bondImage σ b₁)
  rw [transportGaugeField_bondImage h h' hj, transportGaugeField_bondImage h h' hj]
  exact (h2.2 b₁ hb₁).symm
end Lifts
section Conclusion
variable {σ : FourTorus L m ≃ FourTorus L m} {i : ℤ} {K : ℕ}
theorem coincides_of_coincides {j : ℤ} {A B C : PartialGaugeField L m j} (h1 : A.Coincides B)
    (h2 : A.Coincides C) : B.Coincides C := by
  refine ⟨h1.1.symm.trans h2.1, fun b hb => ?_⟩
  have hbA : b ∈ A.support := h1.1 ▸ hb
  exact (h1.2 b hbA).symm.trans (h2.2 b hbA)
theorem levelLifts_transport_of_pos (hLift : LiftConsistentWithAverages)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K)
    (h : PreservesFrom σ i) (h' : PreservesFrom σ.symm i) {k j : ℕ} (hik : i ≤ levelDepth K k)
    {V : PartialGaugeField L m (levelDepth K k)} {𝒢 : Set Matrices.ComplexMatrix2}
    (hd : IsLevelLiftData (K := K) 𝒢 j V)
    (h𝒢 : 𝒢 = compactGaugeGroup ∨ 𝒢 = complexGaugeGroup) :
    (bareLiftPartial (K := K) (transportPartialGaugeField σ V)).EqOnSupport
        (transportPartialGaugeField σ (bareLiftPartial (K := K) V)) ∧
      (complexLevelLiftPartial (K := K) j (transportPartialGaugeField σ V)).EqOnSupport
        (transportPartialGaugeField σ (complexLevelLiftPartial (K := K) j V)) ∧
      (𝒢 = compactGaugeGroup →
        (levelLiftPartial (K := K) j (transportPartialGaugeField σ V)).EqOnSupport
          (transportPartialGaugeField σ (levelLiftPartial (K := K) j V))) := by
  have hd' := isLevelLiftData_transport h h' hik hd
  have hkK : k ≤ K := hd.2.1
  have hjk : j ≤ k := hd.1
  have hij : i ≤ levelDepth K j := hik.trans (levelDepth_anti hjk)
  have hi0 : i ≤ levelDepth K 0 := hik.trans (levelDepth_anti (Nat.zero_le k))
  have hcfg : IsGaugeField compactGaugeGroup V.support V.field ∨
      IsGaugeField complexGaugeGroup V.support V.field := by
    rcases h𝒢 with rfl | rfl
    · exact Or.inl hd.2.2.2
    · exact Or.inr hd.2.2.2
  have hcfg' : IsGaugeField compactGaugeGroup (transportPartialGaugeField σ V).support
        (transportPartialGaugeField σ V).field ∨
      IsGaugeField complexGaugeGroup (transportPartialGaugeField σ V).support
        (transportPartialGaugeField σ V).field := by
    rcases h𝒢 with rfl | rfl
    · exact Or.inl hd'.2.2.2
    · exact Or.inr hd'.2.2.2
  have LV := hLift L m K hs hm hK k hkK V.support hd.2.2.1 V.field hcfg
  have LW := hLift L m K hs hm hK k hkK _ hd'.2.2.1 _ hcfg'
  have hio := fun {n : ℕ} (hn : n ≤ k) =>
    endsInOneBlock_or_existsUnique_covers (K := K) hLift hs hm hK hkK hn
  refine ⟨?_, ?_, ?_⟩
  · have hW := LW.2.2.2.1
    have hV := LV.2.2.2.1
    exact coincides_transport_of_coincides h h' hi0
      (coincides_of_coincides hW.2.1 (hW.1 0 (Nat.zero_le k)).2.2.1)
      (coincides_of_coincides hV.2.1 (hV.1 0 (Nat.zero_le k)).2.2.1)
      (orderLiftPartial_transport h h' hik hi0 (hio (Nat.zero_le k)) V.support V.field)
  · exact coincides_transport_of_coincides h h' hij (LW.2.2.2.1.1 j hjk).2.2.1
      (LV.2.2.2.1.1 j hjk).2.2.1
      (orderLiftPartial_transport h h' hik hij (hio hjk) V.support V.field)
  · rintro rfl
    exact coincides_transport_of_coincides h h' hij ((LW.2.2.2.2.1 hd'.2.2.2).1.1 j hjk).2.2.1
      ((LV.2.2.2.2.1 hd.2.2.2).1.1 j hjk).2.2.1
      (orderLiftPartial_transport h h' hik hij (hio hjk) V.support V.field)
theorem levelLiftEquivariant (hLift : LiftConsistentWithAverages)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (h : PreservesFrom σ i)
    (h' : PreservesFrom σ.symm i) : LevelLiftEquivariant K i σ := by
  intro k j hik V
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · refine ⟨fun 𝒢 _ hd => ⟨isLevelLiftData_transport h h' hik hd, ?_, ?_⟩, fun hd => ?_⟩
    · obtain rfl : k = 0 := by have := hd.2.1; omega
      exact ⟨rfl, fun _ _ => rfl⟩
    · obtain rfl : k = 0 := by have := hd.2.1; omega
      obtain rfl : j = 0 := by have := hd.1; omega
      exact ⟨rfl, fun _ _ => rfl⟩
    · obtain rfl : k = 0 := by have := hd.2.1; omega
      obtain rfl : j = 0 := by have := hd.1; omega
      exact ⟨rfl, fun _ _ => rfl⟩
  · refine ⟨fun 𝒢 h𝒢 hd => ⟨isLevelLiftData_transport h h' hik hd, ?_⟩, fun hd => ?_⟩
    · have := levelLifts_transport_of_pos hLift hs hm hK h h' hik hd h𝒢
      exact ⟨this.1, this.2.1⟩
    · exact (levelLifts_transport_of_pos hLift hs hm hK h h' hik hd (Or.inl rfl)).2.2 rfl
theorem bareLiftFromLevel_transport (hLift : LiftConsistentWithAverages)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (h : PreservesFrom σ i)
    (h' : PreservesFrom σ.symm i) {k : ℕ} (hk : k ≤ K) (hik : i ≤ levelDepth K k)
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    bareLiftFromLevel (K := K) (transportGaugeField σ V) =
      transportGaugeField σ (bareLiftFromLevel (K := K) V) := by
  cases k with
  | zero => rfl
  | succ k =>
    have hK : 0 < K := by omega
    have hi0 : i ≤ levelDepth K 0 := hik.trans (levelDepth_anti (Nat.zero_le _))
    funext b'
    obtain ⟨b, rfl⟩ : ∃ b, b' = bondImage σ b := ⟨_, (bondImage_bondPreimage h h' hi0 b').symm⟩
    show liftToFinerLevel 0 (transportGaugeField σ V) (bondImage σ b) =
      transportGaugeField σ (liftToFinerLevel 0 V) (bondImage σ b)
    rw [liftToFinerLevel_image h h' hik hi0
        (endsInOneBlock_or_existsUnique_covers hLift hs hm hK hk (Nat.zero_le _)),
      transportGaugeField_bondImage h h' hi0]
theorem bareLiftFromLevel_mem (hLift : LiftConsistentWithAverages)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {k : ℕ} (hk : k ≤ K)
    {V : BondAtLevel L m K k → Matrices.ComplexMatrix2} (hV : V ∈ gaugeFieldsAtLevel L m K k) :
    bareLiftFromLevel (K := K) V ∈ gaugeFieldsAtLevel L m K 0 := by
  cases k with
  | zero => exact hV
  | succ k =>
    have hK : 0 < K := by omega
    exact ((hLift L m K hs hm hK (k + 1) hk univ (fun _ _ => mem_univ _) V
      (Or.inl hV)).2.2.2.2.2.1 rfl hV).1
theorem inducedDatumEquivariant (hLift : LiftConsistentWithAverages)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (h : PreservesFrom σ i)
    (h' : PreservesFrom σ.symm i) (hfields : BlockFieldEquivariant K i σ) :
    InducedDatumEquivariant K i σ := by
  intro k Ω hΩ V hV j hj c _
  obtain ⟨hkK, -, hreg⟩ := hΩ
  obtain ⟨a, hia, haj, -⟩ := hreg j hj
  obtain ⟨a', hia', hak, -⟩ := hreg k le_rfl
  have hij : i ≤ levelDepth K j := hia.trans haj
  have hik : i ≤ levelDepth K k := hia'.trans hak
  have hbare := bareLiftFromLevel_transport hLift hs hm h h' hkK hik V
  have hreal := bareLiftFromLevel_mem hLift hs hm hkK hV
  constructor
  · rw [hbare]
    exact congrFun (averagingOnDeterminingSet_image h' hfields (by omega) hij (Ω 0)
      ⟨fun b _ => hreal.1 b (mem_univ _), fun b _ => hreal.2 b (mem_univ _)⟩) c
  · show blockFieldAtLevel _ j (bareLiftFromLevel (K := K) (transportGaugeField σ V)) c =
      transportGaugeField σ (blockFieldAtLevel _ j (bareLiftFromLevel (K := K) V)) c
    rw [hbare]
    exact congrFun (hfields j (by omega) hij _ hreal) c
end Conclusion
theorem averagingMapsEquivariant (hG : LatticeIsometryGroupActionStatement)
    (hB : IsometryInvariance.InvariantUnderIsometries)
    (hW : BlockAverageIsBorelMap)
    (hLift : LiftConsistentWithAverages)
    (hA : BlockAverageCommutesWithIsometries)
    (hR : BlockAverageAtOpposite)
    (hD : LinearAverageIsometryCovariance) :
    AveragingMapsEquivariant := by
  intro L m hs hm i hi σ hσ K
  have h := preservesFrom_of_mem hG hB hs hm hi hσ
  have h' := preservesFrom_of_mem hG hB hs hm hi (symm_mem_latticeIsometries hG hs hm hi hσ)
  have hstep : BlockAverageStepEquivariant K i σ := stepEquivariant hA hR hs hm hi hσ h h'
  have hfields := blockFieldEquivariant hW hs hm hstep
  have hlin : LinearBlockAverageEquivariant K i σ := linearAverageEquivariant hD hs hm hi hσ h h'
  exact ⟨hstep, hfields, hlin, linearIterateEquivariant hD hs hm hlin,
    partialAverageEquivariant h' hstep, regionEquivariant h h' hfields,
    levelLiftEquivariant hLift hs hm h h', determiningEquivariant h' hfields,
    inducedDatumEquivariant hLift hs hm h h' hfields⟩
end YangMills.Construction.PeriodicLattice.EquivarianceProof
