import YangMills.Construction.HoleBesideASecondHole.BondSpreadBelowCurvature
import YangMills.Construction.HoleBesideASecondHole.CoordinatesOfAFieldNearATop
import YangMills.Construction.HoleBesideASecondHole.EnergyInTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace NearTopCoordinates
open BlockAverages GaugeFixing LumpContours SquareDescent GroupMeans BondContours HoleBounds
variable {F : BlockFrame}
abbrev blockSite (y : F.Cell) (u : Fin 4 → ℤ) : F.Site F.depth := cellCentre F.depth y + siteOfCoords F.depth u
theorem isAxialTreeBond_blockSite (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) (y : F.Cell) (u : Fin 4 → ℤ)
    (l : Fin 4) (hu : u ∈ centredCube F.blockSide) (hu' : u + Pi.single l 1 ∈ centredCube F.blockSide)
    (hz : ∀ m, l < m → u m = 0) :
    IsAxialTreeBond (blockSite y u, l) := by apply _root_.YangMills.Construction.GaugeFixing.isAxialTreeBond_cellCentre_add <;> assumption
theorem norm_sub_gaugeTransform_blockSite_eq_plaquetteDefect (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (W : F.GaugeField F.depth) (y : F.Cell) (u : Fin 4 → ℤ) (i l : Fin 4)
    (hil : i < l) (hu : u ∈ centredCube F.blockSide) (hi : u + Pi.single i 1 ∈ centredCube F.blockSide)
    (hl : u + Pi.single l 1 ∈ centredCube F.blockSide)
    (hb : u + Pi.single i 1 + Pi.single l 1 ∈ centredCube F.blockSide) (hz : ∀ m, l < m → u m = 0) :
    ‖((gaugeTransform (axialGauge 1 W) W (blockSite y u) i : UnitQuaternion) : ℍ[ℝ]) -
        (gaugeTransform (axialGauge 1 W) W (blockSite y (u + Pi.single l 1)) i : UnitQuaternion)‖ =
      plaquetteDefect W (blockSite y u, i, l) := by
  set X := gaugeTransform (axialGauge 1 W) W with hX
  have t1 : X (blockSite y u) l = 1 :=
    gaugeTransform_axialGauge_of_isAxialTreeBond hs hL W _ _ (isAxialTreeBond_blockSite hs hL y u l hu hl hz)
  have t2 : X (blockSite y (u + Pi.single i 1)) l = 1 := by
    refine gaugeTransform_axialGauge_of_isAxialTreeBond hs hL W _ _
      (isAxialTreeBond_blockSite hs hL y _ l hi hb fun m hm => ?_)
    have : m ≠ i := fun e => by subst e; exact absurd (hil.trans hm) (lt_irrefl _)
    simp [this, hz m hm]
  have e1 : blockSite y u + unitStep F.depth i = blockSite y (u + Pi.single i 1) :=
    cellCentre_add_siteOfCoords_add_unitStep y u i
  have e2 : blockSite y u + unitStep F.depth l = blockSite y (u + Pi.single l 1) :=
    cellCentre_add_siteOfCoords_add_unitStep y u l
  rw [← plaquetteDefect_gaugeTransform (axialGauge 1 W) W, ← hX]
  have hv : plaquetteHolonomy X (blockSite y u, i, l) =
      X (blockSite y u) i * (X (blockSite y (u + Pi.single l 1)) i)⁻¹ := by
    have e3 : blockSite y u + unitStep F.depth i + unitStep F.depth l - unitStep F.depth i =
        blockSite y (u + Pi.single l 1) := by
      rw [← e2]; abel
    have e4 : blockSite y u + unitStep F.depth i + unitStep F.depth l + - unitStep F.depth i -
        unitStep F.depth l = blockSite y u := by
      abel
    simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
      if_false, mul_one]
    rw [e3, e4, e1, t1, t2]
    simp
  unfold plaquetteDefect
  rw [hv, GaugeFixing.norm_mul_inv_sub_one]
def laterOffsetCount (i : Fin 4) (u : Fin 4 → ℤ) : ℕ := ∑ m, if i < m then (u m).natAbs else 0
theorem laterOffsetCount_succ (i l : Fin 4) (hil : i < l) (u v : Fin 4 → ℤ) (hv : ∀ m, m ≠ l → v m = u m)
    (hl : (v l).natAbs + 1 = (u l).natAbs) : laterOffsetCount i v + 1 = laterOffsetCount i u := by
  unfold laterOffsetCount
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l), ← Finset.add_sum_erase Finset.univ
    (fun m => if i < m then (u m).natAbs else 0) (Finset.mem_univ l)]
  have e : ∑ m ∈ Finset.univ.erase l, (if i < m then (v m).natAbs else 0) =
      ∑ m ∈ Finset.univ.erase l, (if i < m then (u m).natAbs else 0) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hv m (Finset.ne_of_mem_erase hm)]
  rw [e]
  simp only [hil, if_true]
  omega
theorem mem_centredCube_of_abs_le {M : ℕ} {w w' : Fin 4 → ℤ} (h : ∀ m, |w m| ≤ |w' m|)
    (hw : w' ∈ centredCube M) : w ∈ centredCube M := by apply _root_.YangMills.Construction.GaugeFixing.mem_centredCube_of_abs_le <;> assumption
theorem mem_cutPlaquettes_blockSite (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (S : Finset F.Cell)
    (y : F.Cell) (hy : y ∈ S) (v : Fin 4 → ℤ)
    (i l : Fin 4) (hil : i < l) (h1 : v ∈ centredCube F.blockSide) (h2 : v + Pi.single i 1 ∈ centredCube F.blockSide)
    (h3 : v + Pi.single l 1 ∈ centredCube F.blockSide)
    (h4 : v + Pi.single i 1 + Pi.single l 1 ∈ centredCube F.blockSide) :
    (blockSite y v, i, l) ∈ cutPlaquettes (cutBelow F.depth S) := by
  have in_block : ∀ w : Fin 4 → ℤ, w ∈ centredCube F.blockSide → blockSite y w ∈ cutBelow F.depth S := fun w hw => by
    rw [mem_cutBelow_depth hs hL, blockSite, enclosingCell_cellCentre_add hs hL y w hw]
    exact hy
  simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  refine ⟨in_block v h1, hil, ?_⟩
  intro x hx
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  have e1 : blockSite y v + unitStep F.depth i = blockSite y (v + Pi.single i 1) :=
    cellCentre_add_siteOfCoords_add_unitStep y v i
  have e2 : blockSite y v + unitStep F.depth l = blockSite y (v + Pi.single l 1) :=
    cellCentre_add_siteOfCoords_add_unitStep y v l
  have e3 : blockSite y v + unitStep F.depth i + unitStep F.depth l =
      blockSite y (v + Pi.single i 1 + Pi.single l 1) := by
    rw [e1]; exact cellCentre_add_siteOfCoords_add_unitStep y _ l
  rcases hx with rfl | rfl | rfl | rfl
  · exact in_block v h1
  · rw [e1]; exact in_block _ h2
  · rw [e2]; exact in_block _ h3
  · rw [e3]; exact in_block _ h4
theorem norm_gaugeTransform_sub_one_le_mul (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (W : F.GaugeField F.depth) (S : Finset F.Cell) (r : ℝ) (hr : 0 ≤ r)
    (hp : ∀ p ∈ cutPlaquettes (cutBelow F.depth S), plaquetteDefect W p ≤ r) (y : F.Cell) (hy : y ∈ S)
    (i : Fin 4) (N : ℕ) :
    ∀ u : Fin 4 → ℤ, u ∈ centredCube F.blockSide → u + Pi.single i 1 ∈ centredCube F.blockSide →
      laterOffsetCount i u ≤ N →
      ‖((gaugeTransform (axialGauge 1 W) W (blockSite y u) i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ N * r := by
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have tree : ∀ u : Fin 4 → ℤ, u ∈ centredCube F.blockSide → u + Pi.single i 1 ∈ centredCube F.blockSide →
      (∀ m, i < m → u m = 0) → gaugeTransform (axialGauge 1 W) W (blockSite y u) i = 1 := fun u hu hu' hz =>
    gaugeTransform_axialGauge_of_isAxialTreeBond hs hL W _ _ (isAxialTreeBond_blockSite hs hL y u i hu hu' hz)
  have descend : ∀ u : Fin 4 → ℤ, u ∈ centredCube F.blockSide → u + Pi.single i 1 ∈ centredCube F.blockSide →
      (¬ ∀ m, i < m → u m = 0) →
      ∃ v : Fin 4 → ℤ, v ∈ centredCube F.blockSide ∧ v + Pi.single i 1 ∈ centredCube F.blockSide ∧
        laterOffsetCount i v + 1 = laterOffsetCount i u ∧
        ‖((gaugeTransform (axialGauge 1 W) W (blockSite y u) i : UnitQuaternion) : ℍ[ℝ]) -
          (gaugeTransform (axialGauge 1 W) W (blockSite y v) i : UnitQuaternion)‖ ≤ r := by
    intro u hu hu' hall
    have hne : (Finset.univ.filter fun m => i < m ∧ u m ≠ 0).Nonempty := by
      rw [not_forall] at hall
      obtain ⟨m, hm⟩ := hall
      rw [Classical.not_imp] at hm
      exact ⟨m, by simpa using hm⟩
    set l := (Finset.univ.filter fun m => i < m ∧ u m ≠ 0).max' hne with hl
    have hlm := Finset.max'_mem _ hne
    rw [← hl] at hlm
    obtain ⟨hil, hul⟩ := (Finset.mem_filter.1 hlm).2
    have hz : ∀ m, l < m → u m = 0 := by
      intro m hm
      by_contra h0
      have : m ≤ l := Finset.le_max' _ m (by simpa using ⟨hil.trans hm, h0⟩)
      exact absurd hm (not_lt.2 this)
    have hil' : l ≠ i := hil.ne'
    rcases lt_or_gt_of_ne hul with hneg | hpos
    · set v := u + Pi.single l 1 with hv
      have vl : v l = u l + 1 := by simp [hv]
      have vo : ∀ m, m ≠ l → v m = u m := fun m hm => by simp [hv, hm]
      have hvc : v ∈ centredCube F.blockSide := mem_centredCube_of_abs_le (fun m => by
        by_cases e : m = l
        · subst e; rw [vl, abs_of_nonpos (by omega), abs_of_neg hneg]; omega
        · rw [vo m e]) hu
      have hvc' : v + Pi.single i 1 ∈ centredCube F.blockSide := mem_centredCube_of_abs_le (fun m => by
        by_cases e : m = l
        · subst e
          have h1 : (v + Pi.single i 1 : Fin 4 → ℤ) l = u l + 1 := by simp [vl, hil']
          have h2 : (u + Pi.single i 1 : Fin 4 → ℤ) l = u l := by simp [hil']
          rw [h1, h2, abs_of_nonpos (by omega), abs_of_neg hneg]; omega
        · have h1 : (v + Pi.single i 1 : Fin 4 → ℤ) m = (u + Pi.single i 1 : Fin 4 → ℤ) m := by
            simp [vo m e]
          rw [h1]) hu'
      have hsw : u + Pi.single i 1 + Pi.single l 1 = v + Pi.single i 1 := by rw [hv]; abel
      refine ⟨v, hvc, hvc', laterOffsetCount_succ i l hil u v vo (by rw [vl]; omega), ?_⟩
      rw [norm_sub_gaugeTransform_blockSite_eq_plaquetteDefect hs hL W y u i l hil hu hu' hvc (hsw ▸ hvc') hz]
      exact hp _ (mem_cutPlaquettes_blockSite hs' hL S y hy u i l hil hu hu' hvc (hsw ▸ hvc'))
    · set v := u - Pi.single l 1 with hv
      have vl : v l = u l - 1 := by simp [hv]
      have vo : ∀ m, m ≠ l → v m = u m := fun m hm => by simp [hv, hm]
      have hvc : v ∈ centredCube F.blockSide := mem_centredCube_of_abs_le (fun m => by
        by_cases e : m = l
        · subst e; rw [vl, abs_of_nonneg (by omega), abs_of_pos hpos]; omega
        · rw [vo m e]) hu
      have hvc' : v + Pi.single i 1 ∈ centredCube F.blockSide := mem_centredCube_of_abs_le (fun m => by
        by_cases e : m = l
        · subst e
          have h1 : (v + Pi.single i 1 : Fin 4 → ℤ) l = u l - 1 := by simp [vl, hil']
          have h2 : (u + Pi.single i 1 : Fin 4 → ℤ) l = u l := by simp [hil']
          rw [h1, h2, abs_of_nonneg (by omega), abs_of_pos hpos]; omega
        · have h1 : (v + Pi.single i 1 : Fin 4 → ℤ) m = (u + Pi.single i 1 : Fin 4 → ℤ) m := by
            simp [vo m e]
          rw [h1]) hu'
      have hback : v + Pi.single l 1 = u := by rw [hv]; abel
      have hsw : v + Pi.single i 1 + Pi.single l 1 = u + Pi.single i 1 := by rw [hv]; abel
      have hzv : ∀ m, l < m → v m = 0 := fun m hm => by rw [vo m hm.ne']; exact hz m hm
      refine ⟨v, hvc, hvc', laterOffsetCount_succ i l hil u v vo (by rw [vl]; omega), ?_⟩
      have h1 := norm_sub_gaugeTransform_blockSite_eq_plaquetteDefect hs hL W y v i l hil hvc hvc'
        (hback.symm ▸ hu) (hsw.symm ▸ hu') hzv
      rw [hback] at h1
      rw [norm_sub_rev, h1]
      exact hp _ (mem_cutPlaquettes_blockSite hs' hL S y hy v i l hil hvc hvc' (hback.symm ▸ hu) (hsw.symm ▸ hu'))
  induction N with
  | zero =>
    intro u hu hu' hN
    by_cases hall : ∀ m, i < m → u m = 0
    · rw [tree u hu hu' hall]; simp
    · obtain ⟨v, -, -, h, -⟩ := descend u hu hu' hall
      omega
  | succ N ih =>
    intro u hu hu' hN
    by_cases hall : ∀ m, i < m → u m = 0
    · rw [tree u hu hu' hall]
      simp only [OneMemClass.coe_one, sub_self, norm_zero]
      positivity
    · obtain ⟨v, hv, hv', h, hd⟩ := descend u hu hu' hall
      have h1 := ih v hv hv' (by omega)
      have h2 := norm_sub_le_norm_sub_add_norm_sub
        ((gaugeTransform (axialGauge 1 W) W (blockSite y u) i : UnitQuaternion) : ℍ[ℝ])
        (gaugeTransform (axialGauge 1 W) W (blockSite y v) i : UnitQuaternion) 1
      push_cast
      nlinarith
theorem laterOffsetCount_le (hL : Odd F.blockSide) (i : Fin 4) (u : Fin 4 → ℤ) (hu : u ∈ centredCube F.blockSide) :
    laterOffsetCount i u ≤ 2 * F.blockSide := by
  have hLz := blockSide_eq_two_mul_halfSide_add_one hL
  have h1 : ∀ m ∈ (Finset.univ : Finset (Fin 4)), (if i < m then (u m).natAbs else 0) ≤ F.blockSide / 2 := by
    intro m _
    have := abs_le.1 (mem_centredCube_iff_abs_le.1 hu m)
    split_ifs
    · omega
    · omega
  have := Finset.sum_le_card_nsmul _ _ _ h1
  simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  unfold laterOffsetCount
  omega
theorem norm_gaugeTransform_sub_one_le (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (W : F.GaugeField F.depth) (S : Finset F.Cell) (r : ℝ) (hr : 0 ≤ r)
    (hp : ∀ p ∈ cutPlaquettes (cutBelow F.depth S), plaquetteDefect W p ≤ r) (y : F.Cell) (hy : y ∈ S)
    (i : Fin 4) (u : Fin 4 → ℤ) (hu : u ∈ centredCube F.blockSide)
    (hu' : u + Pi.single i 1 ∈ centredCube F.blockSide) :
    ‖((gaugeTransform (axialGauge 1 W) W (blockSite y u) i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      2 * F.blockSide * r := by
  have := norm_gaugeTransform_sub_one_le_mul hs hL W S r hr hp y hy i (2 * F.blockSide) u hu hu'
    (laterOffsetCount_le hL i u hu)
  push_cast at this
  exact this
theorem norm_pathHolonomy_replicate_sub_one_le {j : ℕ} (X : F.GaugeField j) (i : Fin 4) (e : ℝ) (n : ℕ) :
    ∀ z : F.Site j, (∀ k < n, ‖((X (z + k • unitStep j i) i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e) →
      ‖((pathHolonomy X z (List.replicate n (i, true)) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ n * e := by
  induction n with
  | zero => intro z _; simp [pathHolonomy]
  | succ n ih =>
    intro z h
    have h0 := h 0 (by omega)
    simp only [zero_smul, add_zero] at h0
    have h1 := ih (z + unitStep j i) fun k hk => by
      have := h (k + 1) (by omega)
      have e1 : z + unitStep j i + k • unitStep j i = z + (k + 1) • unitStep j i := by
        rw [add_nsmul, one_nsmul]; abel
      rwa [e1]
    simp only [List.replicate_succ, pathHolonomy, linkValue, stepDisplacement, if_true]
    refine (GaugeFixing.norm_mul_sub_one_le _ _).trans ?_
    push_cast
    linarith
theorem card_centredCube (hL : Odd F.blockSide) : (centredCube F.blockSide).card = F.blockSide ^ 4 := by
  have hLz := blockSide_eq_two_mul_halfSide_add_one hL
  have h1 : (Finset.Icc (-halfSide F.blockSide) (halfSide F.blockSide)).card = F.blockSide := by
    rw [Int.card_Icc]
    have : 0 ≤ halfSide F.blockSide := by
      have := hL.pos
      omega
    omega
  simp only [centredCube, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
theorem card_sitesBelow_le (hL : Odd F.blockSide) (y : F.Cell) : (sitesBelow F.depth y).card ≤ F.blockSide ^ 4 := by
  rw [sitesBelow_depth, ← card_centredCube hL]
  exact Finset.card_image_le
theorem card_allContours_eq_mul (hL : Odd F.blockSide) :
    ((allContours F).card : ℝ) = 24 * (F.blockSide : ℝ) ^ 4 := by
  simp only [allContours, Finset.card_product, card_centredCube hL, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]
  push_cast
  norm_num [Nat.factorial]
  ring
theorem quatAverage_contourHolonomy_eq (hL : Odd F.blockSide) (W : F.GaugeField F.depth) (c : F.Cell × Fin 4) :
    quatAverage (allContours F) (fun e => ((contourHolonomy W c e : UnitQuaternion) : ℍ[ℝ])) =
      contourAverage W c := by
  unfold quatAverage contourAverage
  rw [card_allContours_eq_mul hL, allContours, Finset.sum_product]
  rfl
theorem contourVariance_le (hB : ContourVarianceCurvatureBound) (hc : IsCubicTorus F 64) (hL : Odd F.blockSide)
    (W : F.GaugeField F.depth) (S : Finset F.Cell) (r : ℝ) (hr : 0 ≤ r)
    (hp : ∀ p ∈ cutPlaquettes (cutBelow F.depth S), plaquetteDefect W p ≤ r) (c : F.Cell × Fin 4) (h1 : c.1 ∈ S)
    (h2 : c.1 + unitStep F.top c.2 ∈ S) : contourVariance W c ≤ 512 * (F.blockSide : ℝ) ^ 6 * r ^ 2 := by
  have hA : IsAdmissibleAmbient F := Or.inr fun i => by rw [hc.1 i]; exact hc.2
  refine (hB.1 F F.depth (Nat.lt_succ_self _) hL hA W c).trans ?_
  set Q := sitesBelow F.depth c.1 ∪ sitesBelow F.depth (c.1 + unitStep F.top c.2) with hQ
  have hsub : Q ⊆ cutBelow F.depth S := by
    intro x hx
    simp only [cutBelow, Finset.mem_biUnion]
    rcases Finset.mem_union.1 hx with h | h
    · exact ⟨_, h1, h⟩
    · exact ⟨_, h2, h⟩
  have hpl : ∀ p ∈ cutPlaquettes Q, plaquetteDefect W p ^ 2 ≤ r ^ 2 := by
    intro p hp'
    have hmem : p ∈ cutPlaquettes (cutBelow F.depth S) := by
      simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp' ⊢
      exact ⟨hsub hp'.1, hp'.2.1, hp'.2.2.trans hsub⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (hp p hmem) 2
  have hcard : ((cutPlaquettes Q).card : ℝ) ≤ 32 * (F.blockSide : ℝ) ^ 4 := by
    have a1 : (cutPlaquettes Q).card ≤ (Q ×ˢ (Finset.univ : Finset (Fin 4 × Fin 4))).card :=
      Finset.card_le_card (by
        intro p hp'
        simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp' ⊢
        exact hp'.1)
    have a2 : Q.card ≤ 2 * F.blockSide ^ 4 := by
      refine (Finset.card_union_le _ _).trans ?_
      have := card_sitesBelow_le hL c.1
      have := card_sitesBelow_le hL (c.1 + unitStep F.top c.2)
      omega
    rw [Finset.card_product] at a1
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at a1
    have : (cutPlaquettes Q).card ≤ 32 * F.blockSide ^ 4 := by omega
    exact_mod_cast this
  have hsum : ∑ p ∈ blockPairPlaquettes c, plaquetteDefect W p ^ 2 ≤ 32 * (F.blockSide : ℝ) ^ 4 * r ^ 2 := by
    have := Finset.sum_le_card_nsmul _ _ _ hpl
    rw [nsmul_eq_mul] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have hL2 : (0 : ℝ) ≤ 16 * (F.blockSide : ℝ) ^ 2 := by positivity
  calc _ ≤ 16 * (F.blockSide : ℝ) ^ 2 * (32 * (F.blockSide : ℝ) ^ 4 * r ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hL2
    _ = _ := by ring
set_option maxHeartbeats 1000000 in
theorem norm_axialGauge_crossing_sub_top_le (hB : ContourVarianceCurvatureBound) (hM : MeanProductEstimate)
    (hc : IsCubicTorus F 64) (hL : Odd F.blockSide) (V : F.GaugeField F.top) (W : F.GaugeField F.depth)
    (S : Finset F.Cell) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hnear : LiesNearTop r S V W) (x : F.Site F.depth) (i : Fin 4)
    (hcr : IsCrossingBond (x, i)) (h1 : enclosingCell x ∈ S) (h2 : enclosingCell (x + unitStep F.depth i) ∈ S) :
    ‖((gaugeTransform (axialGauge 1 W) W x i : UnitQuaternion) : ℍ[ℝ]) -
        (V (enclosingCell x) i : UnitQuaternion)‖ ≤ 2 ^ 11 * (F.blockSide : ℝ) ^ 6 * r := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hc.1 i]; have := hc.2; omega
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  obtain ⟨ho, hx⟩ := cellOffset_mem_and_eq hs' hL x
  set y := enclosingCell x with hy
  set o := cellOffset x with hoo
  have hLz := blockSide_eq_two_mul_halfSide_add_one hL
  have hoi : o i = halfSide F.blockSide := by
    by_contra hne
    have hlt : o i < halfSide F.blockSide := lt_of_le_of_ne (mem_centredCube.1 ho i).2 hne
    have hmem : o + Pi.single i 1 ∈ centredCube F.blockSide := by
      rw [mem_centredCube]
      intro m
      by_cases e : m = i
      · rw [e]
        have := mem_centredCube.1 ho i
        simp only [Pi.add_apply, Pi.single_eq_same]
        omega
      · simpa [e] using mem_centredCube.1 ho m
    apply hcr
    show enclosingCell (x + unitStep F.depth i) = enclosingCell x
    rw [← hy, ← hx, cellCentre_add_siteOfCoords_add_unitStep, enclosingCell_cellCentre_add hs' hL y _ hmem]
  set dN := F.blockSide / 2 with hdN
  have hd : (dN : ℤ) = halfSide F.blockSide := by omega
  have hLd : F.blockSide = dN + (dN + 1) := by omega
  set o2 := o + (1 - (F.blockSide : ℤ)) • (Pi.single i 1 : Fin 4 → ℤ) with ho2d
  have ho2 : o2 ∈ centredCube F.blockSide := by
    rw [mem_centredCube]
    intro m
    rw [ho2d, add_smul_single_apply]
    by_cases e : m = i
    · rw [e]
      simp only [if_true]
      omega
    · simp only [e, if_false, add_zero]
      exact mem_centredCube.1 ho m
  set y' := y + unitStep F.top i with hy'
  have hx2 : x + unitStep F.depth i = blockSite y' o2 := by
    rw [← hx]
    exact cellCentre_add_siteOfCoords_add_unitStep_crossing y o i
  have hcell' : enclosingCell (x + unitStep F.depth i) = y' := by
    rw [hx2]
    exact enclosingCell_cellCentre_add hs' hL y' o2 ho2
  have hy'S : y' ∈ S := hcell' ▸ h2
  set h := o + (-halfSide F.blockSide) • (Pi.single i 1 : Fin 4 → ℤ) with hhd
  have hhi : h i = 0 := by
    rw [hhd, add_smul_single_apply]
    simp [hoi]
  have hmo : ∀ m, m ≠ i → h m = o m := fun m hm => by
    rw [hhd, add_smul_single_apply]
    simp [hm]
  have hh : h ∈ centredCube F.blockSide := mem_centredCube_of_abs_le (fun m => by
    by_cases e : m = i
    · rw [e, hhi]; simp
    · rw [hmo m e]) ho
  set X := gaugeTransform (axialGauge 1 W) W with hX
  set st : PathStep := (i, true) with hst
  set c : F.Cell × Fin 4 := (y, i) with hcdef
  have hend : cellCentre F.depth y + pathDisplacement F.depth (bondContour F.blockSide h 1 i) =
      cellCentre F.depth y' := by
    have : pathDisplacement (F := F) F.depth (bondContour F.blockSide h 1 i) =
        (F.blockSide : ℤ) • unitStep F.depth i := by
      simp only [bondContour]
      rw [pathDisplacement_append, pathDisplacement_append, pathDisplacement_reversePath,
        pathDisplacement_axisPath, pathDisplacement_replicate]
      simp only [stepDisplacement, if_true]
      rw [natCast_zsmul]
      abel
    rw [this, hy', cellCentre_add_unitStep]
  have hA : contourHolonomy W c (h, 1) = pathHolonomy X (blockSite y h) (List.replicate F.blockSide st) := by
    have g1 : pathHolonomy X (cellCentre F.depth y) (bondContour F.blockSide h 1 i) = contourHolonomy W c (h, 1) := by
      rw [hX, pathHolonomy_gaugeTransform, hend, axialGauge_cellCentre hs' hL, axialGauge_cellCentre hs' hL]
      simp only [one_mul, inv_one, mul_one]
      show _ = pathHolonomy W (refineSite y) _
      rw [refineSite_eq_cellCentre]
    rw [← g1]
    simp only [bondContour]
    rw [pathHolonomy_append, pathHolonomy_append, pathHolonomy_gaugeTransform_axisPath hs' hL 1 W y h hh, one_mul]
    have g2 : cellCentre F.depth y + pathDisplacement F.depth (axisPath h 1 ++ List.replicate F.blockSide (i, true)) =
        cellCentre F.depth y' + pathDisplacement F.depth (axisPath h 1) := by
      rw [pathDisplacement_append, pathDisplacement_axisPath, pathDisplacement_replicate, hy', cellCentre_add_unitStep]
      simp only [stepDisplacement, if_true]
      rw [natCast_zsmul]
      abel
    rw [g2, pathHolonomy_reversePath, pathHolonomy_gaugeTransform_axisPath hs' hL 1 W y' h hh, inv_one, mul_one,
      pathDisplacement_axisPath]
  set A := pathHolonomy X (blockSite y h) (List.replicate dN st) with hAd
  set B := pathHolonomy X (x + unitStep F.depth i) (List.replicate dN st) with hBd
  have hzx : blockSite y h + dN • unitStep F.depth i = x := by
    rw [← hx]
    show cellCentre F.depth y + siteOfCoords F.depth h + dN • unitStep F.depth i =
      cellCentre F.depth y + siteOfCoords F.depth o
    rw [add_assoc, hhd, GaugeFixing.siteOfCoords_add, siteOfCoords_single, add_assoc, ← natCast_zsmul, hd]
    simp
  have hsplit : pathHolonomy X (blockSite y h) (List.replicate F.blockSide st) = A * X x i * B := by
    have e : List.replicate F.blockSide st = List.replicate dN st ++ (st :: List.replicate dN st) := by
      conv_lhs => rw [hLd]
      rw [List.replicate_add, List.replicate_succ]
    rw [e, pathHolonomy_append, pathDisplacement_replicate]
    have e2 : blockSite y h + dN • stepDisplacement F.depth st = x := by
      simpa [hst, stepDisplacement] using hzx
    rw [e2]
    simp only [pathHolonomy, hst, linkValue, stepDisplacement, if_true]
    rw [mul_assoc]
  have hch := norm_gaugeTransform_sub_one_le hs hL W S r hr hnear.1
  have hAle : ‖(A : ℍ[ℝ]) - 1‖ ≤ dN * (2 * F.blockSide * r) := by
    refine norm_pathHolonomy_replicate_sub_one_le X i _ dN _ fun k hk => ?_
    have e : blockSite y h + k • unitStep F.depth i = blockSite y (h + (k : ℤ) • Pi.single i 1) := by
      show cellCentre F.depth y + siteOfCoords F.depth h + k • unitStep F.depth i =
        cellCentre F.depth y + siteOfCoords F.depth (h + (k : ℤ) • Pi.single i 1)
      rw [GaugeFixing.siteOfCoords_add F.depth h, siteOfCoords_single, add_assoc, natCast_zsmul]
    rw [e]
    have hk' : (k : ℤ) + 1 ≤ halfSide F.blockSide := by omega
    refine hch y h1 i _ ?_ ?_
    · rw [mem_centredCube]
      intro m
      rw [add_smul_single_apply]
      by_cases em : m = i
      · rw [em, hhi]; simp only [if_true]; omega
      · simp only [em, if_false, add_zero]; exact mem_centredCube.1 hh m
    · rw [mem_centredCube]
      intro m
      rw [Pi.add_apply, add_smul_single_apply]
      by_cases em : m = i
      · rw [em, hhi]; simp only [if_true, Pi.single_eq_same]; omega
      · simpa [em] using mem_centredCube.1 hh m
  have hBle : ‖(B : ℍ[ℝ]) - 1‖ ≤ dN * (2 * F.blockSide * r) := by
    refine norm_pathHolonomy_replicate_sub_one_le X i _ dN _ fun k hk => ?_
    have e : x + unitStep F.depth i + k • unitStep F.depth i = blockSite y' (o2 + (k : ℤ) • Pi.single i 1) := by
      rw [hx2]
      show cellCentre F.depth y' + siteOfCoords F.depth o2 + k • unitStep F.depth i =
        cellCentre F.depth y' + siteOfCoords F.depth (o2 + (k : ℤ) • Pi.single i 1)
      rw [GaugeFixing.siteOfCoords_add F.depth o2, siteOfCoords_single, add_assoc, natCast_zsmul]
    rw [e]
    have hk' : (k : ℤ) + 1 ≤ halfSide F.blockSide := by omega
    have o2i : o2 i = - halfSide F.blockSide := by
      rw [ho2d, add_smul_single_apply]
      simp only [if_true]
      omega
    refine hch y' hy'S i _ ?_ ?_
    · rw [mem_centredCube]
      intro m
      rw [add_smul_single_apply]
      by_cases em : m = i
      · rw [em, o2i]; simp only [if_true]; omega
      · simp only [em, if_false, add_zero]; exact mem_centredCube.1 ho2 m
    · rw [mem_centredCube]
      intro m
      rw [Pi.add_apply, add_smul_single_apply]
      by_cases em : m = i
      · rw [em, o2i]; simp only [if_true, Pi.single_eq_same]; omega
      · simpa [em] using mem_centredCube.1 ho2 m
  set I := allContours F with hI
  set f := contourHolonomy W c with hf
  set dir := GroupMeans.meanDirection I f with hdir
  have hcS : c ∈ cutBonds S := Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h1, Finset.mem_univ _⟩, hy'S⟩
  have hne : I.Nonempty := by
    refine ⟨(0, 1), ?_⟩
    exact Finset.mem_product.2 ⟨zero_mem_centredCube hL, Finset.mem_univ _⟩
  have hIcard : (I.card : ℝ) = 24 * (F.blockSide : ℝ) ^ 4 := card_allContours_eq_mul hL
  have hLpos : (1 : ℝ) ≤ (F.blockSide : ℝ) := by exact_mod_cast hL.pos
  have hspread : contourVariance W c ≤ 512 * (F.blockSide : ℝ) ^ 6 * r ^ 2 :=
    contourVariance_le hB hc hL W S r hr hnear.1 c h1 hy'S
  have hspread0 : GroupMeans.variance I f = contourVariance W c := rfl
  have hmem : (h, (1 : Equiv.Perm (Fin 4))) ∈ I := Finset.mem_product.2 ⟨hh, Finset.mem_univ _⟩
  have hone : ‖((dir⁻¹ * f (h, 1) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 ≤ I.card * contourVariance W c := by
    have h3 : ‖((dir⁻¹ * f (h, 1) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 ≤
        ∑ e ∈ I, ‖((dir⁻¹ * f e : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 :=
      Finset.single_le_sum (f := fun e => ‖((dir⁻¹ * f e : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2)
        (fun _ _ => by positivity) hmem
    have hpos : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast hne.card_pos
    have h4 : contourVariance W c =
        (1 / (I.card : ℝ)) * ∑ e ∈ I, ‖((dir⁻¹ * f e : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 := rfl
    rw [h4, ← mul_assoc, mul_one_div_cancel hpos.ne', one_mul]
    exact h3
  have hg : ‖(dir : ℍ[ℝ]) - f (h, 1)‖ ≤ 128 * (F.blockSide : ℝ) ^ 5 * r := by
    rw [GaugeFixing.norm_inv_mul_sub_one] at hone
    have h5 : ‖(dir : ℍ[ℝ]) - f (h, 1)‖ ^ 2 ≤ (128 * (F.blockSide : ℝ) ^ 5 * r) ^ 2 := by
      refine hone.trans ?_
      rw [hIcard]
      have hp4 : (0 : ℝ) ≤ 24 * (F.blockSide : ℝ) ^ 4 := by positivity
      refine (mul_le_mul_of_nonneg_left hspread hp4).trans ?_
      have : 0 ≤ (F.blockSide : ℝ) ^ 10 * r ^ 2 := by positivity
      nlinarith
    exact (abs_le_of_sq_le_sq' h5 (by positivity)).2
  have hfit : blockFit W V c ≤ r ^ 2 := hnear.2 c hcS
  have hdV : ‖(V y i : ℍ[ℝ]) - dir‖ ≤ 2 * r + 2 * (512 * (F.blockSide : ℝ) ^ 6 * r ^ 2) := by
    have h6 := ((hM _ I hne).2.2.2) f (V y i)
    have e : quatAverage I (fun e => ((f e : UnitQuaternion) : ℍ[ℝ])) = contourAverage W c :=
      quatAverage_contourHolonomy_eq hL W c
    rw [e] at h6
    have h7 : Real.sqrt (‖contourAverage W c‖ -
        (contourAverage W c * (((V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) ≤ r := by
      have : ‖contourAverage W c‖ - (contourAverage W c * (((V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re ≤ r ^ 2 := hfit
      exact Real.sqrt_le_iff.2 ⟨hr, this⟩
    linarith
  have hgx : ‖((f (h, 1) : UnitQuaternion) : ℍ[ℝ]) - X x i‖ ≤ ‖(A : ℍ[ℝ]) - 1‖ + ‖(B : ℍ[ℝ]) - 1‖ := by
    have : f (h, 1) = A * X x i * B := by rw [hA, hsplit]
    rw [this]
    exact GaugeFixing.norm_mul_mul_sub_le _ _ _
  have hdNr : (dN : ℝ) ≤ (F.blockSide : ℝ) := by exact_mod_cast Nat.div_le_self _ _
  have hAB : ‖(A : ℍ[ℝ]) - 1‖ + ‖(B : ℍ[ℝ]) - 1‖ ≤ 4 * (F.blockSide : ℝ) ^ 2 * r := by
    have h9 : (dN : ℝ) * (2 * F.blockSide * r) ≤ F.blockSide * (2 * F.blockSide * r) :=
      mul_le_mul_of_nonneg_right hdNr (by positivity)
    nlinarith
  have tri : ‖((X x i : UnitQuaternion) : ℍ[ℝ]) - (V y i : UnitQuaternion)‖ ≤
      ‖((f (h, 1) : UnitQuaternion) : ℍ[ℝ]) - X x i‖ +
      ‖(dir : ℍ[ℝ]) - f (h, 1)‖ + ‖(V y i : ℍ[ℝ]) - dir‖ := by
    have e : ((X x i : UnitQuaternion) : ℍ[ℝ]) - (V y i : UnitQuaternion) =
        -(((f (h, 1) : UnitQuaternion) : ℍ[ℝ]) - X x i) -
        ((dir : ℍ[ℝ]) - f (h, 1)) - ((V y i : ℍ[ℝ]) - dir) := by abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans ?_) le_rfl
    rw [norm_neg]
  have p2 : (F.blockSide : ℝ) ^ 2 ≤ (F.blockSide : ℝ) ^ 6 := pow_le_pow_right₀ hLpos (by norm_num)
  have p5 : (F.blockSide : ℝ) ^ 5 ≤ (F.blockSide : ℝ) ^ 6 := pow_le_pow_right₀ hLpos (by norm_num)
  have p0 : (1 : ℝ) ≤ (F.blockSide : ℝ) ^ 6 := one_le_pow₀ hLpos
  have hr2 : r ^ 2 ≤ r := by nlinarith
  have q1 : (F.blockSide : ℝ) ^ 6 * r ^ 2 ≤ (F.blockSide : ℝ) ^ 6 * r := mul_le_mul_of_nonneg_left hr2 (by positivity)
  have q2 : (F.blockSide : ℝ) ^ 2 * r ≤ (F.blockSide : ℝ) ^ 6 * r := mul_le_mul_of_nonneg_right p2 hr
  have q3 : (F.blockSide : ℝ) ^ 5 * r ≤ (F.blockSide : ℝ) ^ 6 * r := mul_le_mul_of_nonneg_right p5 hr
  have q4 : r ≤ (F.blockSide : ℝ) ^ 6 * r := by nlinarith
  have hfin : ‖((X x i : UnitQuaternion) : ℍ[ℝ]) - (V y i : UnitQuaternion)‖ ≤
      2 ^ 11 * (F.blockSide : ℝ) ^ 6 * r := by
    have := hgx.trans hAB
    linarith
  exact hfin
theorem nearTopCoordinateBound (hB : ContourVarianceCurvatureBound) (hM : MeanProductEstimate) :
    NearTopCoordinateBound := by
  refine ⟨fun L => 2 ^ 12 * (L : ℝ) ^ 6 + 1, fun L => ?_, ?_⟩
  · have : (0 : ℝ) ≤ 2 ^ 12 * (L : ℝ) ^ 6 := by positivity
    linarith
  intro F hL hc S V W r hr hK hnear b hb
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hc.1 i]; have := hc.2; omega
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hLpos : (1 : ℝ) ≤ (F.blockSide : ℝ) := by exact_mod_cast hL.pos
  have p0 : (0 : ℝ) ≤ 2 ^ 12 * (F.blockSide : ℝ) ^ 6 := by positivity
  have hr1 : r ≤ 1 := by nlinarith
  obtain ⟨x, i⟩ := b
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hb
  have h1 : enclosingCell x ∈ S := (mem_sitesOfCells_depth hs' hL S x).1 hb.1
  have h2 : enclosingCell (x + unitStep F.depth i) ∈ S := (mem_sitesOfCells_depth hs' hL S _).1 hb.2
  unfold lexBondCoordinate bondCoordinate
  by_cases hcr : IsCrossingBond (x, i)
  · rw [if_pos hcr]
    have h3 := norm_axialGauge_crossing_sub_top_le hB hM hc hL V W S r hr hr1 hnear x i hcr h1 h2
    refine (norm_minimalLog_le _).trans ?_
    rw [GaugeFixing.norm_mul_inv_sub_one]
    have : 0 ≤ r := hr
    nlinarith
  · rw [if_neg hcr]
    obtain ⟨ho, hx⟩ := cellOffset_mem_and_eq hs' hL x
    have hlt := cellOffset_lt_of_not_isCrossingBond hs hL x i hcr
    have hmem : cellOffset x + Pi.single i 1 ∈ centredCube F.blockSide := by
      rw [mem_centredCube]
      intro m
      by_cases e : m = i
      · rw [e]
        have := mem_centredCube.1 ho i
        simp only [Pi.add_apply, Pi.single_eq_same]
        omega
      · simpa [e] using mem_centredCube.1 ho m
    have h3 := norm_gaugeTransform_sub_one_le hs hL W S r hr hnear.1 (enclosingCell x) h1 i _ ho hmem
    rw [blockSite, hx] at h3
    refine (norm_minimalLog_le _).trans ?_
    have p6 : (F.blockSide : ℝ) ≤ (F.blockSide : ℝ) ^ 6 := by
      calc (F.blockSide : ℝ) = (F.blockSide : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hLpos (by norm_num)
    have q : (F.blockSide : ℝ) * r ≤ (F.blockSide : ℝ) ^ 6 * r := mul_le_mul_of_nonneg_right p6 hr
    nlinarith
end NearTopCoordinates
end YangMills.Construction
end
