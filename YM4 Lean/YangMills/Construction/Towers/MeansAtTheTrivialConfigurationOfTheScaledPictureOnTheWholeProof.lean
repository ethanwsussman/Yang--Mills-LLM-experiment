import YangMills.Construction.Towers.BondsOfADoubleBlockAndTheirImageInATorusProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.LinearMapsBetweenTwoLevelsOfATower
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnTheWhole
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.InfiniteLattice (AmbientSpace)
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.TrivialFieldMeans
open YangMills.Construction.Tower.FullSpace.RescaledConditions
open YangMills.Construction.Tower.FullSpace.TwoLevelMaps (CompositeRelations
  vertexSmoothingBetween crossingSmoothingBetween)
theorem sum_pauliCoeff_smul {X : Matrices.ComplexMatrix2} (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • Matrices.ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem ofPauliCoeffs_toPauliCoeffs {σ : Type} {f : σ → Matrices.ComplexMatrix2}
    (h : ∀ x, f x ∈ Matrices.ComplexMatrix2.traceless) :
    ofPauliCoeffs (toPauliCoeffs f) = f :=
  funext fun x => sum_pauliCoeff_smul (h x)
theorem reverse_isPositivelyOriented {a : ℝ} {v : InfiniteLattice.Link a} (hv : ¬v.IsPositivelyOriented) :
    v.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem ofCoeffs_coeffs {L k m : ℕ} {B : Edge L k m → Matrices.ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k m)) :
    (edgePauliCoordinates L k m).ofCoeffs ((edgePauliCoordinates L k m).coeffs B) = B := by
  classical
  have e : ofPauliCoeffs (toPauliCoeffs (restrictToPositiveEdges B)) = restrictToPositiveEdges B :=
    ofPauliCoeffs_toPauliCoeffs fun v => hB.1 v.1 v.2
  funext v
  show extendOddly (fun v => if h : v.IsPositivelyOriented then
    ofPauliCoeffs (toPauliCoeffs (restrictToPositiveEdges B)) ⟨v, h⟩ else 0) v = B v
  rw [e]
  unfold extendOddly
  by_cases hv : v.IsPositivelyOriented
  · simp [hv, restrictToPositiveEdges]
  · have hr := reverse_isPositivelyOriented hv
    simp [hv, hr, restrictToPositiveEdges, hB.2 v]
theorem real_smul_eq_complex_smul (r : ℝ) (X : Matrices.ComplexMatrix2) : r • X = (r : ℂ) • X := by apply _root_.YangMills.SharedProofs.p9878 <;> assumption
theorem composeFromZero_eq_levelwise {F : ℕ → Type*} (step : ∀ m, F m → F (m + 1)) (m : ℕ) (B : F 0) :
    composeFromZero step m B = levelwiseComposition step (Nat.zero_le m) B := by
  induction m with
  | zero =>
    have e := levelwiseComposition_self step 0
    exact (congrFun e B).symm
  | succ m ih =>
    rw [levelwiseComposition_succ step (Nat.zero_le m) (Nat.zero_le (m + 1))]
    show step m (composeFromZero step m B) = _
    rw [ih]
    rfl
theorem vertexSmoothingIter_eq (L k : ℕ) (l : Vertex L k 0 → Matrices.ComplexMatrix2) :
    vertexSmoothingIter L k k l = vertexSmoothingBetween L k (Nat.zero_le k) l :=
  composeFromZero_eq_levelwise (F := fun m => Vertex L k m → Matrices.ComplexMatrix2) (fun _ => vertexSmoothing L) k l
theorem crossingSmoothingIter_eq (L k : ℕ) (B : Edge L k 0 → Matrices.ComplexMatrix2) :
    crossingSmoothingIter L k k B = crossingSmoothingBetween L k (Nat.zero_le k) B :=
  composeFromZero_eq_levelwise (F := fun m => Edge L k m → Matrices.ComplexMatrix2) (fun _ => crossingSmoothing L) k B
section Transport
variable {L k : ℕ}
theorem vertexSmoothing_mean (P : CompositeRelations L k k k) (i : ℕ) (hi : k - k = i) (h : i ≤ k) :
    ∀ f ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L k i), ∀ y : Vertex L k k,
      vertexSmoothingBetween L k h f y = ((L : ℂ) ^ (4 * k))⁻¹ •
        ∑ᶠ x ∈ {x : Vertex L k i | (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k i) k y},
          f x := by
  subst hi
  exact P.vertexSmoothing_eq
theorem crossingSmoothing_mean (P : CompositeRelations L k k k) (i : ℕ) (hi : k - k = i) (h : i ≤ k) :
    ∀ B ∈ complexEdgeForms (meshAt L k i), ∀ c : Edge L k k,
      crossingSmoothingBetween L k h B c = ((L : ℂ) ^ (4 * k))⁻¹ •
        ∑ᶠ x ∈ {x : Vertex L k i | (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k i) k c.initial},
          edgeFormPathSum B (crossingPath c x) := by
  subst hi
  exact P.crossingSmoothing_eq
theorem crossingSmoothing_mapsTo (P : CompositeRelations L k k k) (i : ℕ) (hi : k - k = i) (h : i ≤ k) :
    MapsTo (crossingSmoothingBetween L k h) (complexEdgeForms (meshAt L k i))
      (complexEdgeForms (meshAt L k k)) := by
  subst hi
  exact P.crossingSmoothing_mapsTo_surjOn.1
theorem cubeOfOrder_ncard_and_subset (P : RefinedCubesPartition L k k k) (i : ℕ) (hi : k - k = i)
    (y : Vertex L k k) :
    (cubeOfOrder L (meshAt L k i) k y).ncard = L ^ (4 * k) ∧
      cubeOfOrder L (meshAt L k i) k y ⊆
        (InfiniteLattice.latticeSubgroup (meshAt L k i) : Set AmbientSpace) := by
  subst hi
  exact ⟨P.ncard_eq y, P.subset_sublattice y⟩
theorem crossingPath_eq_map_range (P : CubeTranslateAlongLink L k k k) (i : ℕ) (hi : k - k = i)
    (c : Edge L k k) (μ : Fin 4) (hc : c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k k) μ)
    (x : Vertex L k i) (hx : (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k i) k c.initial) :
    crossingPath c x = (List.range (L ^ k)).map fun t =>
      InfiniteLattice.Link.forwardFrom (x + t • InfiniteLattice.axisStep (meshAt L k i) μ) μ := by
  subst hi
  exact P.crossingPath_eq c μ hc x hx
end Transport
section Pairs
variable {α β M : Type*} [AddCommMonoid M]
open Classical in
def incidencePairs (S : Set α) (hS : S.Finite) (w : α → List β) : Finset (α × β) :=
  hS.toFinset.biUnion fun x => (w x).toFinset.image (Prod.mk x)
theorem coe_incidencePairs (S : Set α) (hS : S.Finite) (w : α → List β) :
    {q : α × β | q.1 ∈ S ∧ q.2 ∈ w q.1} = ↑(incidencePairs S hS w) := by
  classical
  ext ⟨x, v⟩
  simp only [incidencePairs, Set.mem_ofPred_eq, Finset.coe_biUnion, Finset.mem_coe, Finset.coe_image, mem_iUnion,
    Set.Finite.mem_toFinset, mem_image, List.mem_toFinset, Prod.mk.injEq, exists_prop]
  constructor
  · rintro ⟨hx, hv⟩
    exact ⟨x, hx, v, hv, rfl, rfl⟩
  · rintro ⟨x', hx', v', hv', rfl, rfl⟩
    exact ⟨hx', hv'⟩
open Classical in
theorem pairwiseDisjoint_incidencePairs (S : Set α) (hS : S.Finite) (w : α → List β) :
    ((hS.toFinset : Finset α) : Set α).PairwiseDisjoint
      fun x => (w x).toFinset.image (Prod.mk x) := by
  intro x _ y _ hxy
  refine Finset.disjoint_left.2 fun q hq hq' => hxy ?_
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hq
  obtain ⟨v', -, e⟩ := Finset.mem_image.1 hq'
  exact (congrArg Prod.fst e).symm
theorem finsum_incidencePairs (S : Set α) (hS : S.Finite) (w : α → List β) (hw : ∀ x ∈ S, (w x).Nodup)
    (g : β → M) :
    ∑ᶠ q ∈ {q : α × β | q.1 ∈ S ∧ q.2 ∈ w q.1}, g q.2 = ∑ᶠ x ∈ S, ((w x).map g).sum := by
  classical
  rw [coe_incidencePairs S hS w, finsum_mem_coe_finset, incidencePairs,
    Finset.sum_biUnion (pairwiseDisjoint_incidencePairs S hS w)]
  have e : ∀ x ∈ hS.toFinset, ∑ q ∈ (w x).toFinset.image (Prod.mk x), g q.2 = ((w x).map g).sum := by
    intro x hx
    rw [Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj h).2),
      List.sum_toFinset _ (hw x (hS.mem_toFinset.1 hx))]
  rw [Finset.sum_congr rfl e, ← finsum_mem_coe_finset, hS.coe_toFinset]
theorem ncard_incidencePairs (S : Set α) (hS : S.Finite) (w : α → List β) (hw : ∀ x ∈ S, (w x).Nodup) (m : ℕ)
    (hm : ∀ x ∈ S, (w x).length = m) :
    {q : α × β | q.1 ∈ S ∧ q.2 ∈ w q.1}.ncard = S.ncard * m := by
  classical
  rw [coe_incidencePairs S hS w, Set.ncard_coe_finset, incidencePairs,
    Finset.card_biUnion (pairwiseDisjoint_incidencePairs S hS w)]
  have e : ∀ x ∈ hS.toFinset, ((w x).toFinset.image (Prod.mk x)).card = m := by
    intro x hx
    have hx' := hS.mem_toFinset.1 hx
    rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
      List.toFinset_card_of_nodup (hw x hx'), hm x hx']
  rw [Finset.sum_congr rfl e, Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card S hS]
end Pairs
section Sets
variable {L k : ℕ}
theorem nodup_forwardFrom_range {a : ℝ} (ha : a ≠ 0) (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (N : ℕ) :
    ((List.range N).map fun t =>
      InfiniteLattice.Link.forwardFrom (x + t • InfiniteLattice.axisStep a μ) μ).Nodup := by
  refine List.Nodup.map ?_ List.nodup_range
  intro s t h
  have h1 : x + s • InfiniteLattice.axisStep a μ = x + t • InfiniteLattice.axisStep a μ :=
    congrArg InfiniteLattice.Link.initial h
  have h2 := add_left_cancel h1
  have h3 := congrArg (fun z : InfiniteLattice.LatticePoint a => (z : AmbientSpace) μ) h2
  simp [InfiniteLattice.axisStep, ha] at h3
  exact h3
theorem meshAt_ne_zero (hL : 0 < L) (m : ℕ) : meshAt L k m ≠ 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.DoubleCubeImage.meshAt_ne_zero <;> assumption
theorem finestMesh_eq (_hL : 0 < L) : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := by
  simp [finestMesh, meshAt, zpow_neg]
theorem finestMesh_pow_four (hL : 0 < L) :
    ((finestMesh L k ^ 4 : ℝ) : ℂ) = ((L : ℂ) ^ (4 * k))⁻¹ := by
  rw [finestMesh_eq hL]
  push_cast
  rw [inv_pow, ← pow_mul, mul_comm]
theorem baseVerticesOfCube_ncard (P : RefinedCubesPartition L k k k) (y : Vertex L k k) :
    (TrivialLinearization.baseVerticesOfCube L k k y).ncard = L ^ (4 * k) := by
  obtain ⟨h₁, h₂⟩ := cubeOfOrder_ncard_and_subset P 0 (Nat.sub_self k) y
  have e : Subtype.val '' TrivialLinearization.baseVerticesOfCube L k k y =
      cubeOfOrder L (meshAt L k 0) k y := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, h₂ hp⟩, hp, rfl⟩
  rw [← h₁, ← e, Set.ncard_image_of_injective _ Subtype.val_injective]
theorem baseVerticesOfCube_finite (hL : 0 < L) (P : RefinedCubesPartition L k k k) (y : Vertex L k k) :
    (TrivialLinearization.baseVerticesOfCube L k k y).Finite := by
  refine Set.finite_of_ncard_ne_zero ?_
  rw [baseVerticesOfCube_ncard P y]
  exact pow_ne_zero _ hL.ne'
end Sets
theorem trivialFieldMeans_holds (hZ : YangMills.Construction.Tower.BlockPathContourPivotStatement)
    (hM : YangMills.Construction.Tower.TwoLevelMaps.Statement)
    (hO : YangMills.Construction.Tower.FullSpace.RescaledTrivialRelations) :
    YangMills.Construction.Tower.FullSpace.TrivialFieldMeansCondition := by
  intro L hL k hk
  have hLpos : 0 < L := by
    have := hL.2
    omega
  obtain ⟨Bk, -, T, -⟩ := (hZ L hL k k k hk le_rfl le_rfl).2
  have P := (hM L hL k hk).2.2.1 k k hk le_rfl le_rfl
  have O := hO L hL k hk
  have hlist : ∀ c : PositiveEdge (meshAt L k k), ∀ x ∈
      TrivialLinearization.baseVerticesOfCube L k k c.1.initial,
      (crossingPath c.1 x).Nodup ∧ (crossingPath c.1 x).length = L ^ k := by
    intro c x hx
    obtain ⟨μ, hμ⟩ := c.2
    rw [crossingPath_eq_map_range T 0 (Nat.sub_self k) c.1 μ hμ x hx]
    exact ⟨nodup_forwardFrom_range (meshAt_ne_zero hLpos 0) x μ _, by simp⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l hl y
    have hl' : ofPauliCoeffs (toPauliCoeffs l) = l :=
      ofPauliCoeffs_toPauliCoeffs fun x => hl x (mem_univ x)
    have e : ∀ y : Vertex L k k, vertexSmoothingIter L k k l y = ((L : ℂ) ^ (4 * k))⁻¹ •
        ∑ᶠ x ∈ TrivialLinearization.baseVerticesOfCube L k k y, l x := by
      intro y
      exact (congrFun (vertexSmoothingIter_eq L k l) y).trans
        (vertexSmoothing_mean P 0 (Nat.sub_self k) (Nat.zero_le k) l hl y)
    have hmem : ∀ y, vertexSmoothingIter L k k l y ∈ Matrices.ComplexMatrix2.traceless := by
      intro y
      rw [e y]
      refine Submodule.smul_mem _ _ ?_
      exact finsum_mem_induction (· ∈ Matrices.ComplexMatrix2.traceless) (Submodule.zero_mem _)
        (fun _ _ => Submodule.add_mem _) fun x _ => hl x (mem_univ x)
    have g : PeriodicOperators.applyKernel (rescaledOperators L k fun _ => 1).R (toPauliCoeffs l) =
        toPauliCoeffs (vertexSmoothingIter L k k (ofPauliCoeffs (toPauliCoeffs l))) :=
      (O.R_represents (toPauliCoeffs l)).2
    rw [g, hl', ofPauliCoeffs_toPauliCoeffs hmem, e y, real_smul_eq_complex_smul, finestMesh_pow_four hLpos]
  · intro y
    rw [baseVerticesOfCube_ncard Bk y, finestMesh_eq hLpos]
    push_cast
    rw [inv_pow, inv_inv, ← pow_mul, mul_comm]
  · intro (v' : Edge L k 0 → Matrices.ComplexMatrix2) (hv : v' ∈ complexEdgeForms (meshAt L k 0)) c
    have e : crossingSmoothingIter L k k v' c.1 = ((L : ℂ) ^ (4 * k))⁻¹ •
        ∑ᶠ x ∈ TrivialLinearization.baseVerticesOfCube L k k c.1.initial,
          edgeFormPathSum v' (crossingPath c.1 x) := by
      exact (congrFun (crossingSmoothingIter_eq L k v') c.1).trans
        (crossingSmoothing_mean P 0 (Nat.sub_self k) (Nat.zero_le k) v' hv c.1)
    have hform : crossingSmoothingIter L k k v' ∈ complexEdgeForms (meshAt L k k) := by
      rw [crossingSmoothingIter_eq]
      exact crossingSmoothing_mapsTo P 0 (Nat.sub_self k) (Nat.zero_le k) hv
    have hmem : ∀ c : PositiveEdge (meshAt L k k),
        restrictToPositiveEdges (finestMesh L k • crossingSmoothingIter L k k v') c ∈
          Matrices.ComplexMatrix2.traceless := by
      intro c
      show finestMesh L k • crossingSmoothingIter L k k v' c.1 ∈ Matrices.ComplexMatrix2.traceless
      rw [real_smul_eq_complex_smul]
      exact Submodule.smul_mem _ _ (hform.1 c.1 c.2)
    have g : PeriodicOperators.applyKernel (rescaledOperators L k fun _ => 1).Q
        (toPauliCoeffs (restrictToPositiveEdges v')) =
        toPauliCoeffs (restrictToPositiveEdges (finestMesh L k •
          crossingSmoothingIter L k k ((edgePauliCoordinates L k 0).ofCoeffs
            ((edgePauliCoordinates L k 0).coeffs v')))) :=
      (O.Q_represents (toPauliCoeffs (restrictToPositiveEdges v'))).2
    rw [g, ofCoeffs_coeffs hv, ofPauliCoeffs_toPauliCoeffs hmem]
    have hs := finsum_incidencePairs (TrivialLinearization.baseVerticesOfCube L k k c.1.initial)
      (baseVerticesOfCube_finite hLpos Bk _) (fun x => crossingPath c.1 x) (fun x hx => (hlist c x hx).1) v'
    have hs' : ∑ᶠ q ∈ crossingIncidences L k c.1, v' q.2 =
        ∑ᶠ x ∈ TrivialLinearization.baseVerticesOfCube L k k c.1.initial,
          edgeFormPathSum v' (crossingPath c.1 x) := hs
    rw [hs']
    show finestMesh L k • crossingSmoothingIter L k k v' c.1 = _
    rw [e, real_smul_eq_complex_smul, real_smul_eq_complex_smul, smul_smul, ← finestMesh_pow_four hLpos]
    congr 1
    push_cast
    ring
  · intro c
    have hn := ncard_incidencePairs (TrivialLinearization.baseVerticesOfCube L k k c.1.initial)
      (baseVerticesOfCube_finite hLpos Bk _) (fun x => crossingPath c.1 x) (fun x hx => (hlist c x hx).1) (L ^ k)
      (fun x hx => (hlist c x hx).2)
    have hn' : (crossingIncidences L k c.1).ncard =
        (TrivialLinearization.baseVerticesOfCube L k k c.1.initial).ncard * L ^ k := hn
    rw [hn', baseVerticesOfCube_ncard Bk, finestMesh_eq hLpos]
    push_cast
    rw [inv_pow, inv_inv]
    ring
end YangMills.Construction.Tower.FullSpace.TrivialFieldMeans
end
