import YangMills.Construction.Towers.CovariantAveragesAsDifferentialsProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.LinearMapsBetweenTwoLevelsOfATower
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnASide
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASide
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower
open PeriodicOperators (applyKernel)
open RescaledConditions
open TrivialLinearization (baseVerticesOfCube)
open TwoLevelMaps
namespace TrivialAveragesOnSide
theorem sum_pauliCoeff_smul {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • Matrices.ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem ofPauliCoeffs_toPauliCoeffs_apply {σ : Type} (f : σ → Matrices.ComplexMatrix2) (x : σ)
    (h : f x ∈ Matrices.ComplexMatrix2.traceless) :
    ofPauliCoeffs (toPauliCoeffs f) x = f x :=
  sum_pauliCoeff_smul h
theorem real_smul_eq_complex_smul (z : ℝ) (X : Matrices.ComplexMatrix2) : z • X = (z : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
theorem finsum_mem_traceless {ι : Type} (S : Set ι) (f : ι → Matrices.ComplexMatrix2)
    (h : ∀ x ∈ S, f x ∈ Matrices.ComplexMatrix2.traceless) :
    ∑ᶠ x ∈ S, f x ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.AsDifferentials.finsum_mem_traceless <;> assumption
theorem ofCoeffs_toPauliCoeffs_restrict {L n k j : ℕ} {B : Edge L n k j → Matrices.ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) :
    (edgePauliCoordinates L n k j).ofCoeffs (toPauliCoeffs (restrictToPositiveEdges B)) = B := by
  refine funext fun e : Edge L n k j => ?_
  show extendOddly (fun e : Edge L n k j => open Classical in
    if h : e.IsPositivelyOriented then
      ofPauliCoeffs (toPauliCoeffs (restrictToPositiveEdges B)) ⟨e, h⟩ else 0) e = B e
  unfold extendOddly
  by_cases he : e.IsPositivelyOriented
  · rw [if_pos he]
    beta_reduce
    rw [dif_pos he]
    exact ofPauliCoeffs_toPauliCoeffs_apply (restrictToPositiveEdges B) ⟨e, he⟩ (hB.1 e he)
  · have hr : e.opposite.IsPositivelyOriented := by
      obtain ⟨μ, h | h⟩ := e.isNeighbour
      · exact absurd ⟨μ, h⟩ he
      · refine ⟨μ, ?_⟩
        show e.source - e.target = _
        rw [← neg_sub, h, neg_neg]
    rw [if_neg he]
    beta_reduce
    rw [dif_pos hr,
      ofPauliCoeffs_toPauliCoeffs_apply (restrictToPositiveEdges B) ⟨e.opposite, hr⟩ (hB.1 _ hr)]
    show -B e.opposite = B e
    rw [hB.2 e, neg_neg]
theorem levelwiseComposition_eq_composeFromZero {F : ℕ → Type*} (f : ∀ j, F j → F (j + 1)) :
    ∀ (m : ℕ) (h : 0 ≤ m), levelwiseComposition f h = composeFromZero f m
  | 0, h => by
    rw [show h = le_refl 0 from rfl, levelwiseComposition_self]
    rfl
  | m + 1, h => by
    rw [levelwiseComposition_succ f (Nat.zero_le m) h, levelwiseComposition_eq_composeFromZero f m]
    rfl
theorem composeFromZero_eq_iterateFromBare {L n k : ℕ}
    (f : ∀ j, (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k (j + 1) → Matrices.ComplexMatrix2) :
    ∀ m : ℕ, composeFromZero (F := fun j => Edge L n k j → Matrices.ComplexMatrix2) f m =
      PeriodicLattice.iterateFromBare f m
  | 0 => rfl
  | m + 1 => by
    funext B
    show f m (composeFromZero (F := fun j => Edge L n k j → Matrices.ComplexMatrix2) f m B) =
      f m (PeriodicLattice.iterateFromBare f m B)
    rw [composeFromZero_eq_iterateFromBare f m]
section Composites
variable {L n k : ℕ}
theorem vertexSmoothingBetween_eq_mean (R : CompositeRelations L n k k k) :
    ∀ i : ℕ, k - k = i → ∀ h : i ≤ k,
      ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L n k i),
      ∀ y : Vertex L n k k, vertexSmoothingBetween L n k h f y =
        ((L : ℂ) ^ (4 * k))⁻¹ •
          ∑ᶠ x ∈ (PeriodicLattice.sitesIn (PeriodicLattice.refinedBlock k y) :
            Set (Vertex L n k i)), f x := by
  intro i e
  subst e
  intro _
  exact R.vertexSmoothing_eq
theorem crossingSmoothingBetween_eq_mean (R : CompositeRelations L n k k k) :
    ∀ i : ℕ, k - k = i → ∀ h : i ≤ k, ∀ B ∈ complexEdgeForms L n k i, ∀ c : Edge L n k k,
      crossingSmoothingBetween L n k h B c =
        ((L : ℂ) ^ (4 * k))⁻¹ •
          ∑ᶠ x ∈ (PeriodicLattice.sitesIn (PeriodicLattice.refinedBlock k c.source) :
            Set (Vertex L n k i)), edgeFormPathSum B (PeriodicLattice.crossingPath c x) := by
  intro i e
  subst e
  intro _
  exact R.crossingSmoothing_eq
theorem crossingSmoothingBetween_mem (R : CompositeRelations L n k k k) :
    ∀ i : ℕ, k - k = i → ∀ h : i ≤ k, ∀ B ∈ complexEdgeForms L n k i,
      crossingSmoothingBetween L n k h B ∈ complexEdgeForms L n k k := by
  intro i e
  subst e
  intro _ B hB
  exact R.crossingSmoothing_mapsTo_surjOn.1 hB
theorem crossingPath_eq_map_range (T : BlockTranslateAlongBond L n k k k) :
    ∀ i : ℕ, k - k = i → ∀ (c : Edge L n k k) (μ : Fin 4),
      c.target - c.source = PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) μ →
      ∀ x : Vertex L n k i, (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k c.source →
        PeriodicLattice.crossingPath c x = (List.range (L ^ k)).map fun t =>
          PeriodicLattice.Bond.forwardFrom
            (x + t • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ) μ := by
  intro i e
  subst e
  exact T.crossingPath_eq
end Composites
section Counts
variable {L n k : ℕ}
theorem image_baseVerticesOfCube (y : Vertex L n k k) :
    (fun z : Vertex L n k 0 => (z : PeriodicLattice.FourTorus L n)) '' baseVerticesOfCube L n k k y =
      PeriodicLattice.refinedBlock k y := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hp
    have hl : p ∈ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k 0) := by
      have e : PeriodicLattice.levelDepth k k + (k : ℤ) = PeriodicLattice.levelDepth k 0 := by
        simp [PeriodicLattice.levelDepth]
      rw [← e]
      exact hp.2
    exact ⟨⟨p, hl⟩, hp, rfl⟩
theorem ncard_baseVerticesOfCube (P : RefinedBlocksPartition L n k k k) (y : Vertex L n k k) :
    (baseVerticesOfCube L n k k y).ncard = L ^ (4 * k) := by
  have h := P.ncard_eq y
  rw [← image_baseVerticesOfCube, Set.ncard_image_of_injective _ Subtype.val_injective] at h
  exact h
theorem finite_baseVerticesOfCube (hL : 0 < L) (P : RefinedBlocksPartition L n k k k)
    (y : Vertex L n k k) : (baseVerticesOfCube L n k k y).Finite := by
  apply Set.finite_of_ncard_pos
  rw [ncard_baseVerticesOfCube P]
  exact pow_pos hL _
theorem finestMesh_eq_inv_pow : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := by
  simp [finestMesh, meshAt, zpow_neg]
theorem axisPath_nodup (hL : 0 < L) (hA : AxisPathUniqueness.OnPeriodicLattice L n k 0)
    (x : Vertex L n k 0) (μ : Fin 4) :
    ((List.range (L ^ k)).map fun t =>
      PeriodicLattice.Bond.forwardFrom
        (x + t • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) μ) μ).Nodup := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have bound : ∀ a : ℕ, a < L ^ k →
      ((|(a : ℤ)| : ℤ) : ℝ) * meshAt L k 0 < PeriodicLattice.torusSide L n / 2 := by
    intro a ha
    have hs : meshAt L k 0 = ((L : ℝ) ^ k)⁻¹ := finestMesh_eq_inv_pow
    have hpos : (0 : ℝ) < (L : ℝ) ^ k := by positivity
    have ha' : (a : ℝ) < (L : ℝ) ^ k := by exact_mod_cast ha
    have h1 : (a : ℝ) * ((L : ℝ) ^ k)⁻¹ < 1 := by
      rw [← div_eq_mul_inv, div_lt_one hpos]
      exact ha'
    have h2 : (1 : ℝ) ≤ (L : ℝ) ^ n := one_le_pow₀ hL1
    have h3 : PeriodicLattice.torusSide L n / 2 = (L : ℝ) ^ n := by
      simp [PeriodicLattice.torusSide]
    rw [hs, h3, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (a : ℤ))]
    push_cast
    linarith
  refine List.Nodup.map_on ?_ List.nodup_range
  intro a ha b hb hab
  have ha' : a < L ^ k := List.mem_range.1 ha
  have hb' : b < L ^ k := List.mem_range.1 hb
  have h1 : x + a • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) μ =
      x + b • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) μ :=
    congrArg PeriodicLattice.Bond.source hab
  have h2 := add_left_cancel h1
  have h3 : (a : ℤ) • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) μ =
      (b : ℤ) • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) μ := by
    simpa [natCast_zsmul] using h2
  rcases hA.1 μ μ a b (bound a ha') (bound b hb') h3 with ⟨e, e'⟩ | ⟨-, e⟩ <;> omega
theorem finsum_crossingPath_eq_and_ncard (hL : 0 < L) (P : RefinedBlocksPartition L n k k k)
    (T : BlockTranslateAlongBond L n k k k) (hA : AxisPathUniqueness.OnPeriodicLattice L n k 0)
    (c : Edge L n k k) (hc : c.IsPositivelyOriented) (w : Edge L n k 0 → Matrices.ComplexMatrix2) :
    ∑ᶠ x ∈ baseVerticesOfCube L n k k c.source, edgeFormPathSum w (PeriodicLattice.crossingPath c x) =
        ∑ᶠ q ∈ crossingIncidences L n k c, w q.2 ∧
      (crossingIncidences L n k c).ncard = L ^ (4 * k) * L ^ k := by
  classical
  obtain ⟨μ, hμ⟩ := hc
  have hfin := finite_baseVerticesOfCube hL P c.source
  have hlist : ∀ x ∈ baseVerticesOfCube L n k k c.source,
      PeriodicLattice.crossingPath c x = (List.range (L ^ k)).map fun t =>
        PeriodicLattice.Bond.forwardFrom
          (x + t • PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) μ) μ :=
    fun x hx => crossingPath_eq_map_range T 0 (Nat.sub_self k) c μ hμ x hx
  have hnd : ∀ x ∈ baseVerticesOfCube L n k k c.source, (PeriodicLattice.crossingPath c x).Nodup := by
    intro x hx
    rw [hlist x hx]
    exact axisPath_nodup hL hA x μ
  have hlen : ∀ x ∈ baseVerticesOfCube L n k k c.source,
      (PeriodicLattice.crossingPath c x).toFinset.card = L ^ k := by
    intro x hx
    rw [List.toFinset_card_of_nodup (hnd x hx), hlist x hx]
    simp
  let s : Finset (Vertex L n k 0) := hfin.toFinset
  let t : Vertex L n k 0 → Finset (Edge L n k 0) := fun x => (PeriodicLattice.crossingPath c x).toFinset
  let r : Finset (Vertex L n k 0 × Edge L n k 0) := (s.sigma t).image fun p => (p.1, p.2)
  have hr : ∀ p : Vertex L n k 0 × Edge L n k 0, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1 := by
    rintro ⟨x, e⟩
    simp only [r, Finset.mem_image, Finset.mem_sigma, Sigma.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨a, d, h, rfl, rfl⟩
      exact h
    · intro h
      exact ⟨x, e, h, rfl, rfl⟩
  have hset : crossingIncidences L n k c = (r : Set (Vertex L n k 0 × Edge L n k 0)) := by
    ext q
    rw [Finset.mem_coe, hr]
    simp only [s, t, Set.Finite.mem_toFinset, List.mem_toFinset]
    rfl
  have hs : baseVerticesOfCube L n k k c.source = (s : Set (Vertex L n k 0)) := by
    simp [s]
  constructor
  · rw [hset, finsum_mem_coe_finset, hs, finsum_mem_coe_finset,
      Finset.sum_finset_product r s t hr]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x ∈ baseVerticesOfCube L n k k c.source := by simpa [s] using hx
    exact (List.sum_toFinset _ (hnd x hx')).symm
  · rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective, Finset.card_sigma]
    · have hc' : ∀ x ∈ s, (t x).card = L ^ k := fun x hx => hlen x (by simpa [s] using hx)
      rw [Finset.sum_congr rfl hc', Finset.sum_const, smul_eq_mul]
      have : s.card = L ^ (4 * k) := by
        rw [← ncard_baseVerticesOfCube P c.source, hs, Set.ncard_coe_finset]
      rw [this]
    · rintro ⟨a, d⟩ ⟨a', d'⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
end Counts
theorem trivialAveragesOnEverySide_holds (hOne : TrivialFieldRescaledRelations.Statement)
    (hLin : TwoLevelMaps.Statement)
    (hBlocks : BlockPathContourPivotStatement)
    (hPath : AxisPathUniqueness.AxisPathsUnique) : TrivialAveragesOnEverySide := by
  intro L hL k hk n hn
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hOneAt := hOne L hL k hk n hn
  have hP : CompositeRelations L n k k k := ((hLin L hL k hk).1 n hn).2.1 k k hk le_rfl le_rfl
  obtain ⟨hPart, -, hTrans, -⟩ := (hBlocks L hL k k k hk le_rfl le_rfl).1 n hn
  have hA : AxisPathUniqueness.OnPeriodicLattice L n k 0 := (hPath L hL k 0 (Nat.zero_le k)).1 n hn
  have hη : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := finestMesh_eq_inv_pow
  have hscale : ∀ X : Matrices.ComplexMatrix2,
      ((L : ℂ) ^ (4 * k))⁻¹ • X = finestMesh L k ^ 4 • X := by
    intro X
    rw [real_smul_eq_complex_smul, hη]
    congr 1
    push_cast
    rw [inv_pow, ← pow_mul, mul_comm k 4]
  have hvertex : ∀ l ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L n k 0),
      ∀ y : Vertex L n k k,
      vertexSmoothingIter L n k k l y =
        (finestMesh L k ^ 4) • ∑ᶠ x ∈ baseVerticesOfCube L n k k y, l x := by
    intro l hl y
    have h := vertexSmoothingBetween_eq_mean hP 0 (Nat.sub_self k) (Nat.zero_le k) l hl y
    rw [show vertexSmoothingBetween L n k (Nat.zero_le k) = vertexSmoothingIter L n k k from
      levelwiseComposition_eq_composeFromZero _ k _, hscale] at h
    exact h
  have hcross : ∀ B ∈ complexEdgeForms L n k 0,
      crossingSmoothingIter L n k k B =
        crossingSmoothingBetween L n k (Nat.zero_le k) B := by
    intro B _
    show crossingSmoothingIter L n k k B = _
    rw [show crossingSmoothingBetween L n k (Nat.zero_le k) =
      composeFromZero (F := fun j => Edge L n k j → Matrices.ComplexMatrix2)
        (crossingSmoothing L n k) k from
        levelwiseComposition_eq_composeFromZero _ k _, composeFromZero_eq_iterateFromBare]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l hl y
    have hg := hOneAt.R_represents (toPauliCoeffs l)
    have e : applyKernel (rescaledOperators L n k (trivialField L n k 0)).R (toPauliCoeffs l) =
        toPauliCoeffs (vertexSmoothingIter L n k k (ofPauliCoeffs (toPauliCoeffs l))) := hg.2
    have hback : ofPauliCoeffs (toPauliCoeffs l) = l :=
      funext fun x => ofPauliCoeffs_toPauliCoeffs_apply l x (hl x (mem_univ x))
    rw [e, hback, ofPauliCoeffs_toPauliCoeffs_apply _ y, hvertex l hl y]
    rw [hvertex l hl y, real_smul_eq_complex_smul]
    exact Submodule.smul_mem _ _ (finsum_mem_traceless _ _ fun x _ => hl x (mem_univ x))
  · intro y
    rw [ncard_baseVerticesOfCube hPart y, hη]
    push_cast
    rw [inv_pow, inv_inv, ← pow_mul, mul_comm k 4]
  · intro w hw c
    have hg := hOneAt.Q_represents (toPauliCoeffs (restrictToPositiveEdges w))
    have e : applyKernel (rescaledOperators L n k (trivialField L n k 0)).Q
          (toPauliCoeffs (restrictToPositiveEdges w)) =
        toPauliCoeffs (restrictToPositiveEdges (finestMesh L k • crossingSmoothingIter L n k k
          ((edgePauliCoordinates L n k 0).ofCoeffs (toPauliCoeffs (restrictToPositiveEdges w))))) := hg.2
    have hmem : crossingSmoothingBetween L n k (Nat.zero_le k) w ∈ complexEdgeForms L n k k :=
      crossingSmoothingBetween_mem hP 0 (Nat.sub_self k) (Nat.zero_le k) w hw
    obtain ⟨hsum, -⟩ := finsum_crossingPath_eq_and_ncard hL0 hPart hTrans hA c.1 c.2 w
    have hvalue : crossingSmoothingIter L n k k w c.1 =
        (finestMesh L k ^ 4) •
          ∑ᶠ x ∈ baseVerticesOfCube L n k k c.1.source,
            edgeFormPathSum w (PeriodicLattice.crossingPath c.1 x) := by
      rw [hcross w hw,
        crossingSmoothingBetween_eq_mean hP 0 (Nat.sub_self k) (Nat.zero_le k) w hw c.1, hscale]
      rfl
    rw [e, ofCoeffs_toPauliCoeffs_restrict hw, ofPauliCoeffs_toPauliCoeffs_apply]
    · show finestMesh L k • crossingSmoothingIter L n k k w c.1 = _
      rw [hvalue, hsum, smul_smul]
      congr 1
      ring
    · show finestMesh L k • crossingSmoothingIter L n k k w c.1 ∈ Matrices.ComplexMatrix2.traceless
      rw [real_smul_eq_complex_smul, hcross w hw]
      exact Submodule.smul_mem _ _ (hmem.1 c.1 c.2)
  · intro c
    obtain ⟨-, hcount⟩ := finsum_crossingPath_eq_and_ncard hL0 hPart hTrans hA c.1 c.2 0
    rw [hcount, hη]
    push_cast
    rw [inv_pow, inv_inv, ← pow_mul, ← pow_add]
    congr 1
    ring
end TrivialAveragesOnSide
end YangMills.Construction.Tower
end
