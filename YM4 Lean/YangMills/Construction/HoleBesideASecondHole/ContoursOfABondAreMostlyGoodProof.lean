import YangMills.Construction.HoleBesideASecondHole.MeansAtACoreBondProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages PathHolonomy LumpContours CornerBoxes
namespace BondContours
variable {F : BlockFrame}
theorem cellCentre_eq_refineSite (y : F.Cell) : cellCentre F.depth y = refineSite y := by apply _root_.YangMills.Construction.BondMeans.cellCentre_eq_refineSite <;> assumption
theorem siteOfCoords_minimalOffset {j : ℕ} (x x' : F.Site j) :
    siteOfCoords j (minimalOffset x x') = x' - x := by apply _root_.YangMills.Construction.BondMeans.siteOfCoords_minimalOffset <;> assumption
theorem refineSite_add_unitStep (y : F.Cell) (i : Fin 4) :
    refineSite (y + unitStep F.top i) = refineSite y + F.blockSide • unitStep F.depth i := by apply _root_.YangMills.Construction.BondMeans.refineSite_add_unitStep <;> assumption
theorem period_depth (i : Fin 4) : F.period F.depth i = F.extent i * F.blockSide := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimizingChart.period_depth <;> assumption
theorem axisPath_site_coords (j : ℕ) (x : F.Site j) (d : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (z : F.Site j)
    (hz : z ∈ pathSites x (axisPath d π)) :
    ∃ m : Fin 4, ∀ k, k ≠ m → z k = x k ∨ z k = (x + siteOfCoords j d : F.Site j) k := by
  let start : ℕ → F.Site j := fun k => x + siteOfCoords j (partialOffset d π k)
  have hval : ∀ n k, (start n) k = x k ∨ (start n) k = (x + siteOfCoords j d : F.Site j) k := by
    intro n k
    by_cases h2 : (((π.symm k : Fin 4) : ℕ)) < n
    · right
      simp [start, partialOffset, h2, siteOfCoords]
    · left
      simp [start, partialOffset, h2, siteOfCoords]
  have piece : ∀ (n : Fin 4), z ∈ pathSites (start n) (axisPathSegment d π n) →
      ∃ m : Fin 4, ∀ k, k ≠ m → z k = x k ∨ z k = (x + siteOfCoords j d : F.Site j) k := by
    intro n hz'
    obtain ⟨r, _, rfl⟩ := mem_pathSites_replicate _ _ _ _ hz'
    refine ⟨π n, fun k hk => ?_⟩
    have e0 : (stepDisplacement j (π n, decide (0 ≤ d (π n))) : F.Site j) k = 0 := by
      by_cases hc : 0 ≤ d (π n)
      · simp [stepDisplacement, hc, unitStep, siteOfCoords, Pi.single_apply, hk]
      · simp [stepDisplacement, hc, unitStep, siteOfCoords, Pi.single_apply, hk]
    have e1 : (start n + r • stepDisplacement j (π n, decide (0 ≤ d (π n))) : F.Site j) k = (start n) k := by
      simp [e0]
    rw [e1]
    exact hval _ k
  have next : ∀ n : Fin 4, start n + pathDisplacement j (axisPathSegment d π n) = start ((n : ℕ) + 1) :=
    fun n => segment_endpoint j x d π n
  have s0 : x = start 0 := by
    simp [start, partialOffset_zero, _root_.YangMills.Construction.PathHolonomy.siteOfCoords_zero]
  rw [axisPath_eq_segments, s0] at hz
  rcases mem_pathSites_append _ _ _ _ hz with h0 | hz
  · exact piece 0 h0
  have n0 : start 0 + pathDisplacement j (axisPathSegment d π 0) = start 1 := next 0
  rw [n0] at hz
  rcases mem_pathSites_append _ _ _ _ hz with h1 | hz
  · exact piece 1 h1
  have n1 : start 1 + pathDisplacement j (axisPathSegment d π 1) = start 2 := next 1
  rw [n1] at hz
  rcases mem_pathSites_append _ _ _ _ hz with h2 | hz
  · exact piece 2 h2
  have n2 : start 2 + pathDisplacement j (axisPathSegment d π 2) = start 3 := next 2
  rw [n2] at hz
  rcases mem_pathSites_append _ _ _ _ hz with h3 | hz
  · exact piece 3 h3
  have n3 : start 3 + pathDisplacement j (axisPathSegment d π 3) = start 4 := next 3
  rw [n3] at hz
  have hz4 : z = start 4 := by simpa [pathSites] using hz
  refine ⟨0, fun k _ => ?_⟩
  rw [hz4]
  exact hval 4 k
theorem mem_pathSites_of_mem_reversePath {j : ℕ} (P : List PathStep) :
    ∀ (x z : F.Site j), z ∈ pathSites (x + pathDisplacement j P) (reversePath P) → z ∈ pathSites x P := by
  induction P with
  | nil =>
    intro x z hz
    simpa [pathDisplacement, reversePath] using hz
  | cons st r ih =>
    intro x z hz
    have e : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    have e2 : x + pathDisplacement j (st :: r) = x + stepDisplacement j st + pathDisplacement j r := by
      simp [pathDisplacement, add_assoc]
    rw [e, e2] at hz
    rcases mem_pathSites_append _ _ _ _ hz with h1 | h1
    · simp only [pathSites, List.mem_cons]
      exact Or.inr (ih _ _ h1)
    · rw [pathDisplacement_reversePath] at h1
      simp only [add_neg_cancel_right, pathSites, List.mem_cons, List.not_mem_nil, or_false] at h1
      simp only [pathSites, List.mem_cons]
      rcases h1 with h1 | h1
      · right
        rw [h1]
        exact self_mem_pathSites _ _
      · left
        rw [h1]
        obtain ⟨d, b⟩ := st
        cases b <;> simp [stepDisplacement]
theorem minimalOffset_add_siteOfCoords (hL : Odd F.blockSide) (hS : ∀ i, 64 ≤ F.extent i) (x : F.Site F.depth)
    {o o' : Fin 4 → ℤ} (ho : o ∈ centredCube F.blockSide) (ho' : o' ∈ centredCube F.blockSide) :
    minimalOffset (x + siteOfCoords F.depth o) (x + siteOfCoords F.depth o') = o' - o := by apply _root_.YangMills.Construction.BondMeans.minimalOffset_add_siteOfCoords <;> assumption
open Classical in
theorem base_mem_sitesBelow (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (b : F.Cell → F.Site F.depth)
    (hL : Odd F.blockSide) (hB : IsBaseChoice J₀ h b) (u : F.Cell) : b u ∈ sitesBelow F.depth u := by apply _root_.YangMills.Construction.CoreBondMeans.base_mem_sitesBelow <;> assumption
theorem axisPath_from_base_mem_sitesBelow (hL : Odd F.blockSide) (hS : ∀ i, 64 ≤ F.extent i)
    (b : F.Cell → F.Site F.depth) (u : F.Cell)
    (hb : b u ∈ sitesBelow F.depth u) {ξ : Fin 4 → ℤ} (hξ : ξ ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) :
    ∀ x ∈ pathSites (b u) (axisPath (minimalOffset (b u) (cellCentre F.depth u + siteOfCoords F.depth ξ)) π),
      x ∈ sitesBelow F.depth u := by
  obtain ⟨ob, hob, hby⟩ := exists_offset_of_mem_sitesBelow F.depth u hb
  rw [hby, cellCentre_eq_refineSite, minimalOffset_add_siteOfCoords hL hS _ hob hξ]
  exact axisPath_sites_mem_sitesBelow F.depth u (offsetInBlock_of_mem_centredCube hob)
    (offsetInBlock_of_mem_centredCube hξ) π
open Classical in
theorem excludedBoxes_eq_empty (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (y : F.Cell)
    (hy : nearbyLumps h y = ∅) : excludedBoxes J₀ h y = ∅ := by
  unfold excludedBoxes
  by_cases hcr : IsCrowded J₀ h y
  · rw [if_pos hcr]
  · rw [if_neg hcr, hy, Finset.image_empty]
    unfold mergedBoxes
    by_cases hz : ∃ Z : Finset (Finset (F.Site F.depth)), IsLeastSeparatedCover ∅ Z
    · rw [dif_pos hz]
      have hs := hz.choose_spec
      have hc : IsSeparatedCover (F := F) (j := F.depth) ∅ (∅ : Finset (Finset (F.Site F.depth))) := by
        refine ⟨?_, ?_, ?_⟩ <;> simp
      refine Finset.eq_empty_of_forall_notMem fun B hB => ?_
      obtain ⟨B', hB', _⟩ := hs.2 ∅ hc B hB
      simp at hB'
    · rw [dif_neg hz]
open Classical in
theorem mostContoursGood : MostContoursGoodStatement := by
  intro F J₀ Λ h b c hL hS hB
  obtain ⟨y, i⟩ := c
  simp only
  set y' := y + unitStep F.top i with hy'
  have hj : F.depth < F.top := by simp [BlockFrame.top]
  have hend1 : ∀ (u : F.Cell) (ξ : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)),
      b u + pathDisplacement F.depth
        (axisPath (minimalOffset (b u) (cellCentre F.depth u + siteOfCoords F.depth ξ)) π) =
        refineSite u + siteOfCoords F.depth ξ := by
    intro u ξ π
    rw [pathDisplacement_axisPath, _root_.YangMills.Construction.BondContours.siteOfCoords_minimalOffset, cellCentre_eq_refineSite]
    abel
  have hend2 : ∀ (ξ : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)),
      b y + pathDisplacement F.depth
        (axisPath (minimalOffset (b y) (cellCentre F.depth y + siteOfCoords F.depth ξ)) π ++
        List.replicate F.blockSide (i, true)) =
      b y' + pathDisplacement F.depth
        (axisPath (minimalOffset (b y') (cellCentre F.depth y' + siteOfCoords F.depth ξ)) π) := by
    intro ξ π
    rw [pathDisplacement_append, ← add_assoc, hend1, hend1, pathDisplacement_replicate, hy',
      refineSite_add_unitStep]
    simp only [stepDisplacement, if_true]
    abel
  refine ⟨?_, ?_⟩
  · intro e he x hx
    have hξ : e.1 ∈ centredCube F.blockSide := (Finset.mem_product.1 he).1
    unfold contourPath at hx
    simp only at hx
    rcases mem_pathSites_append _ _ _ _ hx with h1 | h3
    · rcases mem_pathSites_append _ _ _ _ h1 with h1 | h2
      · exact Finset.mem_union_left _ (axisPath_from_base_mem_sitesBelow hL hS b y
          (base_mem_sitesBelow J₀ h b hL hB y) hξ e.2 x h1)
      · rw [hend1] at h2
        obtain ⟨r, hr, rfl⟩ := mem_pathSites_replicate _ _ _ _ h2
        have hmb := mem_adjacent_blocks F.depth hj hL y i (offsetInBlock_of_mem_centredCube hξ) r hr
        have es : refineSite y + siteOfCoords F.depth e.1 + r • stepDisplacement F.depth (i, true) =
            refineSite y + siteOfCoords F.depth e.1 + r • unitStep F.depth i := by
          simp only [stepDisplacement, if_true]
        rw [es]
        exact hmb
    · rw [hend2] at h3
      exact Finset.mem_union_right _ (axisPath_from_base_mem_sitesBelow hL hS b y'
        (base_mem_sitesBelow J₀ h b hL hB y') hξ e.2 x (mem_pathSites_of_mem_reversePath _ _ _ h3))
  intro hc hc' hsame hsame' hsum hsum'
  set Zs := excludedBoxes J₀ h y with hZs
  set Zs' := excludedBoxes J₀ h y' with hZs'
  let A : (k : Fin 4) → Finset (ZMod (F.period F.depth k)) := fun k => ((Zs ∪ Zs').biUnion id).image fun z => z k
  have hA : ∀ k, (A k).card ≤ 2 * Λ := by
    intro k
    have e : (A k) = (Zs ∪ Zs').biUnion fun Z => Z.image fun z => z k := by
      ext v
      simp only [A, Finset.mem_image, Finset.mem_biUnion, id]
      constructor
      · rintro ⟨z, ⟨Z, hZ, hz⟩, rfl⟩
        exact ⟨Z, hZ, z, hz, rfl⟩
      · rintro ⟨Z, hZ, z, hz, rfl⟩
        exact ⟨z, ⟨Z, hZ, hz⟩, rfl⟩
    rw [e]
    refine Finset.card_biUnion_le.trans ?_
    have hs : ∀ Z, (Z.image fun z : F.Site F.depth => z k).card ≤ largestSide Z := fun Z =>
      Finset.le_sup (f := fun i : Fin 4 => (Z.image fun x : F.Site F.depth => x i).card) (Finset.mem_univ k)
    calc ∑ Z ∈ Zs ∪ Zs', (Z.image fun z : F.Site F.depth => z k).card
        ≤ ∑ Z ∈ Zs ∪ Zs', largestSide Z := Finset.sum_le_sum fun Z _ => hs Z
      _ ≤ ∑ Z ∈ Zs, largestSide Z + ∑ Z ∈ Zs', largestSide Z := by
          rw [← Finset.sum_union_inter]
          exact Nat.le_add_right _ _
      _ ≤ 2 * Λ := by omega
  have hperL : ∀ k, F.blockSide ≤ F.period F.depth k := by
    intro k
    rw [period_depth]
    have := hS k
    nlinarith [hL.pos]
  let Bd : Fin 4 → F.Site F.depth → Finset (Fin 4 → ℤ) := fun m base =>
    (centredCube F.blockSide).filter fun ξ => ∀ k, k ≠ m → (base + siteOfCoords F.depth ξ : F.Site F.depth) k ∈ A k
  have hBd : ∀ m base, (Bd m base).card ≤ F.blockSide * (2 * Λ) ^ 3 := fun m base =>
    card_offsets_le hL F.depth hperL base m A (2 * Λ) hA
  let Bad : Finset (Fin 4 → ℤ) := Finset.univ.biUnion fun m => Bd m (refineSite y) ∪ Bd m (refineSite y')
  have hBad : Bad.card ≤ 8 * (F.blockSide * (2 * Λ) ^ 3) := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ m : Fin 4, (Bd m (refineSite y) ∪ Bd m (refineSite y')).card
        ≤ ∑ _m : Fin 4, 2 * (F.blockSide * (2 * Λ) ^ 3) := by
          refine Finset.sum_le_sum fun m _ => (Finset.card_union_le _ _).trans ?_
          have a1 := hBd m (refineSite y)
          have a2 := hBd m (refineSite y')
          omega
      _ = 8 * (F.blockSide * (2 * Λ) ^ 3) := by
          simp
          ring
  have hlegs : ∀ (u : F.Cell) (Z : Finset (Finset (F.Site F.depth))), excludedBoxes J₀ h u = Z →
      ¬ IsCrowded J₀ h u → Z ⊆ Zs ∪ Zs' → ∀ (ξ : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (x : F.Site F.depth)
      (B : Finset (F.Site F.depth)), B ∈ Z → x ∈ B →
      x ∈ pathSites (b u) (axisPath (minimalOffset (b u) (cellCentre F.depth u + siteOfCoords F.depth ξ)) π) →
      ξ ∈ centredCube F.blockSide → ∃ m, ξ ∈ Bd m (refineSite u) := by
    intro u Z hZ hcr hsub ξ π x B hBZ hxB hx hξ
    obtain ⟨m, hm⟩ := axisPath_site_coords F.depth _ _ _ _ hx
    refine ⟨m, Finset.mem_filter.2 ⟨hξ, fun k hk => ?_⟩⟩
    have hne : x k ≠ b u k := by
      have hb := hB u
      by_cases he : nearbyLumps h u = ∅ ∨ IsCrowded J₀ h u
      · exfalso
        rcases he with he | he
        · have := excludedBoxes_eq_empty J₀ h u he
          rw [hZ] at this
          rw [this] at hBZ
          simp at hBZ
        · exact hcr he
      · exact (hb.2 he).2 B (hZ ▸ hBZ) x hxB k
    rcases hm k hk with e | e
    · exact absurd e hne
    · have e2 : (b u + siteOfCoords F.depth (minimalOffset (b u) (cellCentre F.depth u + siteOfCoords F.depth ξ)) :
          F.Site F.depth) = refineSite u + siteOfCoords F.depth ξ := by
        rw [_root_.YangMills.Construction.BondContours.siteOfCoords_minimalOffset, cellCentre_eq_refineSite]
        abel
      rw [e2] at e
      rw [← e]
      refine Finset.mem_image.2 ⟨x, Finset.mem_biUnion.2 ⟨B, hsub hBZ, hxB⟩, rfl⟩
  have hbad : ∀ e ∈ allContours F, ¬ IsGoodContour J₀ h b (y, i) e.1 e.2 → e.1 ∈ Bad := by
    intro e he hng
    have hξ : e.1 ∈ centredCube F.blockSide := (Finset.mem_product.1 he).1
    unfold IsGoodContour at hng
    push_neg at hng
    obtain ⟨x, hx, B, hB', hxB⟩ := hng
    have hBu : B ∈ Zs ∪ Zs' := hB'
    unfold contourPath at hx
    simp only at hx
    rcases mem_pathSites_append _ _ _ _ hx with h1 | h3
    · rcases mem_pathSites_append _ _ _ _ h1 with h1 | h2
      · have hu := axisPath_from_base_mem_sitesBelow hL hS b y (base_mem_sitesBelow J₀ h b hL hB y) hξ e.2 x h1
        have hBZ : B ∈ Zs := by
          rcases Finset.mem_union.1 hBu with hh | hh
          · exact hh
          · exact hsame B hh ⟨x, Finset.mem_inter.2 ⟨hxB, hu⟩⟩
        obtain ⟨m, hm⟩ := hlegs y Zs rfl hc Finset.subset_union_left e.1 e.2 x B hBZ hxB h1 hξ
        exact Finset.mem_biUnion.2 ⟨m, Finset.mem_univ _, Finset.mem_union_left _ hm⟩
      · rw [hend1] at h2
        obtain ⟨r, _, rfl⟩ := mem_pathSites_replicate _ _ _ _ h2
        refine Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_union_left _ ?_⟩
        refine Finset.mem_filter.2 ⟨hξ, fun k hk => ?_⟩
        have hz0 : (stepDisplacement F.depth (i, true) : F.Site F.depth) k = 0 := by
          simp [stepDisplacement, unitStep, siteOfCoords, Pi.single_apply, hk]
        refine Finset.mem_image.2 ⟨_, Finset.mem_biUnion.2 ⟨B, hBu, hxB⟩, ?_⟩
        simp [hz0]
    · rw [hend2] at h3
      have h4 := mem_pathSites_of_mem_reversePath _ _ _ h3
      have hu := axisPath_from_base_mem_sitesBelow hL hS b y' (base_mem_sitesBelow J₀ h b hL hB y') hξ e.2 x h4
      have hBZ : B ∈ Zs' := by
        rcases Finset.mem_union.1 hBu with hh | hh
        · exact hsame' B hh ⟨x, Finset.mem_inter.2 ⟨hxB, hu⟩⟩
        · exact hh
      obtain ⟨m, hm⟩ := hlegs y' Zs' rfl hc' Finset.subset_union_right e.1 e.2 x B hBZ hxB h4 hξ
      exact Finset.mem_biUnion.2 ⟨m, Finset.mem_univ _, Finset.mem_union_right _ hm⟩
  have hsub : ((allContours F).filter fun e => ¬ IsGoodContour J₀ h b (y, i) e.1 e.2) ⊆
      Bad ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin 4))) := by
    intro e he
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 he
    exact Finset.mem_product.2 ⟨hbad e h1 h2, Finset.mem_univ _⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have h24 : Nat.factorial 4 = 24 := rfl
  rw [h24]
  omega
end BondContours
end YangMills.Construction
end
