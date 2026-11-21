import YangMills.Construction.ColdChainAtEveryLevel.GaugeMotionsOfAChain
import YangMills.Construction.ColdChainAtEveryLevel.ShareOfTheCriticalChainProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace GaugeFixing
open BlockAverages LumpContours
variable {F : BlockFrame}
theorem wilsonAction_gaugeTransform (S : Finset F.Cell) (γ : F.Site 0 → UnitQuaternion) (U : F.GaugeField 0) :
    wilsonAction S (gaugeTransform γ U) = wilsonAction S U := by apply _root_.YangMills.Construction.GaugeMotions.wilsonAction_gaugeTransform <;> assumption
theorem gaugeTransform_gaugeTransform_inv {j : ℕ} (γ : F.Site j → UnitQuaternion) (X : F.GaugeField j) :
    gaugeTransform γ (gaugeTransform (fun x => (γ x)⁻¹) X) = X := by
  funext x i
  simp [gaugeTransform, mul_assoc]
theorem gaugeTransform_surjective {j : ℕ} (γ : F.Site j → UnitQuaternion) :
    Function.Surjective (gaugeTransform γ : F.GaugeField j → F.GaugeField j) :=
  fun X => ⟨_, gaugeTransform_gaugeTransform_inv γ X⟩
theorem minimalAction_gaugeTransform (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide) (a : ℝ)
    (S : Finset F.Cell) (j : ℕ) (hj : j ≤ F.top) : ∀ (γ : F.Site j → UnitQuaternion) (W : F.GaugeField j),
      minimalAction a S j (gaugeTransform γ W) = minimalAction a S j W := by
  induction j with
  | zero =>
    intro γ W
    exact wilsonAction_gaugeTransform S γ W
  | succ j ih =>
    intro γ V
    have hlt : j < F.top := hj
    obtain ⟨hinj, -, -, hfit⟩ := hG F j hlt hL
    classical
    set γ' : F.Site j → UnitQuaternion := fun x => if h : ∃ y, refineSite y = x then γ h.choose else 1 with hγ'
    have hdown : ∀ y, γ' (refineSite y) = γ y := by
      intro y
      have h : ∃ y', refineSite y' = refineSite (j := j) y := ⟨y, rfl⟩
      simp only [hγ', dif_pos h]
      rw [hinj h.choose_spec]
    show (⨅ W : F.GaugeField j, (minimalAction a S j W +
        a * ∑ c ∈ innerBonds S (j + 1), blockFit W (gaugeTransform γ V) c)) =
      ⨅ W : F.GaugeField j, (minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W V c)
    rw [← (gaugeTransform_surjective γ').iInf_comp]
    refine iInf_congr fun W => ?_
    rw [ih (Nat.le_of_succ_le hj) γ' W]
    congr 2
    refine Finset.sum_congr rfl fun c _ => ?_
    exact hfit γ' γ W V c (hdown _) (hdown _)
theorem pathWithin_plaquette {j : ℕ} {Q : Finset (F.Site j)} (p : F.Site j × Fin 4 × Fin 4)
    (h : plaquetteCorners p ⊆ Q) :
    PathWithin Q p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] := by
  obtain ⟨x, μ, ν⟩ := p
  have c1 : x ∈ Q := h (by simp [plaquetteCorners])
  have c2 : x + unitStep j μ ∈ Q := h (by simp [plaquetteCorners])
  have c3 : x + unitStep j ν ∈ Q := h (by simp [plaquetteCorners])
  have c4 : x + unitStep j μ + unitStep j ν ∈ Q := h (by simp [plaquetteCorners])
  refine ⟨c1, ?_, ?_, ?_, ?_⟩
  · simpa [stepDisplacement] using c2
  · simpa [stepDisplacement] using c4
  · have : x + unitStep j μ + unitStep j ν + - unitStep j μ = x + unitStep j ν := by abel
    simpa [stepDisplacement, this] using c3
  · have : x + unitStep j μ + unitStep j ν + - unitStep j μ + - unitStep j ν = x := by abel
    show x + stepDisplacement j (μ, true) + stepDisplacement j (ν, true) + stepDisplacement j (μ, false) +
      stepDisplacement j (ν, false) ∈ Q
    simpa [stepDisplacement, this] using c1
theorem minimalAction_congr (a : ℝ) (S : Finset F.Cell) (j : ℕ) (W W' : F.GaugeField j)
    (h : ∀ b ∈ innerBonds S j, W b.1 b.2 = W' b.1 b.2) : minimalAction a S j W = minimalAction a S j W' := by
  cases j with
  | zero =>
    show wilsonAction S W = wilsonAction S W'
    unfold wilsonAction
    refine Finset.sum_congr rfl fun p hp => ?_
    have hc : plaquetteCorners p ⊆ sitesOfCells S 0 := by
      simp only [innerPlaquettes, Finset.mem_filter] at hp
      exact hp.2.2
    have : plaquetteHolonomy W p = plaquetteHolonomy W' p :=
      pathHolonomy_congr (Q := sitesOfCells S 0) h _ _ (pathWithin_plaquette p hc)
    rw [this]
  | succ j =>
    show (⨅ X : F.GaugeField j, (minimalAction a S j X + a * ∑ c ∈ innerBonds S (j + 1), blockFit X W c)) =
      ⨅ X : F.GaugeField j, (minimalAction a S j X + a * ∑ c ∈ innerBonds S (j + 1), blockFit X W' c)
    refine iInf_congr fun X => ?_
    congr 2
    refine Finset.sum_congr rfl fun c hc => ?_
    unfold blockFit
    rw [h c hc]
theorem cellCentre_add_mem_sitesBelow (hL : Odd F.blockSide) (y : F.Cell) (o : Fin 4 → ℤ)
    (ho : o ∈ centredCube F.blockSide) :
    cellCentre F.depth y + siteOfCoords F.depth o ∈ sitesBelow F.depth y := by
  rw [sitesBelow_depth]
  exact Finset.mem_image.2 ⟨o, ho, rfl⟩
theorem pathWithin_bondContour (hL : Odd F.blockSide) (y : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    PathWithin (sitesBelow F.depth y ∪ sitesBelow F.depth (y + unitStep F.top i)) (cellCentre F.depth y)
      (bondContour F.blockSide h π i) := by
  set Q := sitesBelow F.depth y ∪ sitesBelow F.depth (y + unitStep F.top i) with hQ
  set y' := y + unitStep F.top i with hy'
  have hLz := blockSide_eq_two_mul_halfSide_add_one hL
  have q1 : ∀ o ∈ centredCube F.blockSide, cellCentre F.depth y + siteOfCoords F.depth o ∈ Q := fun o ho =>
    Finset.mem_union_left _ (cellCentre_add_mem_sitesBelow hL y o ho)
  have q2 : ∀ o ∈ centredCube F.blockSide, cellCentre F.depth y' + siteOfCoords F.depth o ∈ Q := fun o ho =>
    Finset.mem_union_right _ (cellCentre_add_mem_sitesBelow hL y' o ho)
  have hleg := pathWithin_axisPath (cellCentre F.depth y) q1 h hh π
  have hleg' := pathWithin_axisPath (cellCentre F.depth y') q2 h hh π
  have hcen : cellCentre F.depth y' = cellCentre F.depth y + (F.blockSide : ℤ) • unitStep F.depth i :=
    cellCentre_add_unitStep y i
  simp only [bondContour]
  have hstraight : PathWithin Q (cellCentre F.depth y + pathDisplacement F.depth (axisPath h π))
      (List.replicate F.blockSide (i, true)) := by
    refine pathWithin_replicate _ _ _ fun k hk => ?_
    rw [pathDisplacement_axisPath]
    simp only [stepDisplacement, if_true]
    have hi := mem_centredCube.1 hh i
    by_cases hc : h i + k ≤ halfSide F.blockSide
    · have hm : h + (k : ℤ) • Pi.single i 1 ∈ centredCube F.blockSide := by
        rw [mem_centredCube]
        intro m
        rw [add_smul_single_apply]
        by_cases e : m = i
        · rw [e]; simp only [if_true]; omega
        · simp only [e, if_false, add_zero]; exact mem_centredCube.1 hh m
      have := q1 _ hm
      rw [siteOfCoords_add F.depth h, siteOfCoords_single, natCast_zsmul, ← add_assoc] at this
      exact this
    · have hm : h + ((k : ℤ) - (F.blockSide : ℤ)) • Pi.single i 1 ∈ centredCube F.blockSide := by
        rw [mem_centredCube]
        intro m
        rw [add_smul_single_apply]
        by_cases e : m = i
        · rw [e]; simp only [if_true]; omega
        · simp only [e, if_false, add_zero]; exact mem_centredCube.1 hh m
      have := q2 _ hm
      rw [siteOfCoords_add F.depth h, siteOfCoords_single, sub_smul, hcen] at this
      have e2 : cellCentre F.depth y + siteOfCoords F.depth h + k • unitStep F.depth i =
          cellCentre F.depth y + (F.blockSide : ℤ) • unitStep F.depth i +
          (siteOfCoords F.depth h + ((k : ℤ) • unitStep F.depth i - (F.blockSide : ℤ) • unitStep F.depth i)) := by
        have e0 : (k • unitStep F.depth i : F.Site F.depth) = (k : ℤ) • unitStep F.depth i :=
          (natCast_zsmul _ _).symm
        rw [e0]
        abel
      rw [e2]
      exact this
  refine pathWithin_append _ _ _ (pathWithin_append _ _ _ hleg hstraight) ?_
  have e : cellCentre F.depth y + pathDisplacement F.depth (axisPath h π ++ List.replicate F.blockSide (i, true)) =
      cellCentre F.depth y' + pathDisplacement F.depth (axisPath h π) := by
    rw [pathDisplacement_append, pathDisplacement_replicate, hcen]
    simp only [stepDisplacement, if_true]
    rw [natCast_zsmul]
    abel
  rw [e]
  exact pathWithin_reversePath _ _ hleg'
theorem sitesBelow_union_subset_sitesOfCells (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (S : Finset F.Cell)
    (y y' : F.Cell) (h1 : y ∈ S) (h2 : y' ∈ S) :
    sitesBelow F.depth y ∪ sitesBelow F.depth y' ⊆ sitesOfCells S F.depth := by
  intro x hx
  rw [mem_sitesOfCells_depth hs hL]
  rcases Finset.mem_union.1 hx with h | h
  · rw [(mem_sitesBelow_depth hs hL y x).1 h]; exact h1
  · rw [(mem_sitesBelow_depth hs hL y' x).1 h]; exact h2
theorem mem_of_mem_innerBonds_top {S : Finset F.Cell} {c : F.Cell × Fin 4} (hc : c ∈ innerBonds S F.top) :
    c.1 ∈ S ∧ c.1 + unitStep F.top c.2 ∈ S := by
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hc
  exact ⟨mem_sitesOfCells_top.1 hc.1, mem_sitesOfCells_top.1 hc.2⟩
theorem contourAverage_congr (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (S : Finset F.Cell)
    (W W' : F.GaugeField F.depth) (h : ∀ b ∈ innerBonds S F.depth, W b.1 b.2 = W' b.1 b.2) (c : F.Cell × Fin 4)
    (hc : c ∈ innerBonds S F.top) : contourAverage W c = contourAverage W' c := by
  obtain ⟨h1, h2⟩ := mem_of_mem_innerBonds_top hc
  unfold contourAverage
  congr 1
  refine Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun π _ => ?_
  rw [refineSite_eq_cellCentre]
  rw [pathHolonomy_congr (Q := sitesOfCells S F.depth) h _ _
    (pathWithin_mono (sitesBelow_union_subset_sitesOfCells hs hL S _ _ h1 h2) _ _
      (pathWithin_bondContour hL c.1 e he π c.2))]
theorem blockEnergy_congr (hs : ∀ i, 0 < F.extent i) (hL : Odd F.blockSide) (a : ℝ) (S : Finset F.Cell)
    (W W' : F.GaugeField F.depth) (V : F.GaugeField F.top)
    (h : ∀ b ∈ innerBonds S F.depth, W b.1 b.2 = W' b.1 b.2) :
    blockEnergy a S F.depth W V = blockEnergy a S F.depth W' V := by
  unfold blockEnergy
  rw [minimalAction_congr a S F.depth W W' h]
  congr 2
  refine Finset.sum_congr rfl fun c hc => ?_
  unfold blockFit
  rw [contourAverage_congr hs hL S W W' h c hc]
theorem blockEnergy_gaugeTransform (hG : gaugeCovarianceStatement) (hL : 0 < F.blockSide) (a : ℝ)
    (S : Finset F.Cell) (γ : F.Site F.depth → UnitQuaternion) (hγ : ∀ z, γ (cellCentre F.depth z) = 1)
    (W : F.GaugeField F.depth) (V : F.GaugeField F.top) :
    blockEnergy a S F.depth (gaugeTransform γ W) V = blockEnergy a S F.depth W V := by
  unfold blockEnergy
  rw [minimalAction_gaugeTransform hG hL a S F.depth (Nat.le_succ _) γ W]
  congr 2
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨-, -, -, hfit⟩ := hG F F.depth (Nat.lt_succ_self _) hL
  have h1 := hfit γ (fun _ => 1) W V c (by rw [refineSite_eq_cellCentre, hγ])
    (by rw [refineSite_eq_cellCentre, hγ])
  have h2 : gaugeTransform (fun _ => (1 : UnitQuaternion)) V = V := by
    funext x i
    simp [gaugeTransform]
  rwa [h2] at h1
open Classical in
def lexicographicChart (S : Finset F.Cell) (V : F.GaugeField F.top) (W : F.GaugeField F.depth) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun x i => if (x, i) ∈ chordBonds S then bondCoordinate 1 V W (x, i) else 0
theorem chartedField_lexicographicChart_eq (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) (S : Finset F.Cell)
    (V : F.GaugeField F.top) (W : F.GaugeField F.depth) (b : F.Site F.depth × Fin 4)
    (hb : b ∈ innerBonds S F.depth) :
    chartedField (lexicographicChart S V W) V b.1 b.2 = gaugeTransform (axialGauge 1 W) W b.1 b.2 := by
  obtain ⟨x, i⟩ := b
  have hnt : IsCrossingBond (x, i) → ¬ IsAxialTreeBond (x, i) := fun h ht => ht.1 h
  have hchart : ¬ IsAxialTreeBond (x, i) → (x, i) ∈ chordBonds S := fun h => by
    simp only [chordBonds, Finset.mem_filter]
    exact ⟨hb, h⟩
  simp only [chartedField]
  by_cases hc : IsCrossingBond (x, i)
  · rw [if_pos hc]
    have : lexicographicChart S V W x i = bondCoordinate 1 V W (x, i) := by
      simp [lexicographicChart, hchart (hnt hc)]
    rw [this, bondCoordinate, if_pos hc, expUnit_minimalLog]
    simp
  · rw [if_neg hc]
    by_cases ht : IsAxialTreeBond (x, i)
    · rw [if_pos ht, gaugeTransform_axialGauge_of_isAxialTreeBond hs hL W x i ht]
    · rw [if_neg ht]
      have : lexicographicChart S V W x i = bondCoordinate 1 V W (x, i) := by
        simp [lexicographicChart, hchart ht]
      rw [this, bondCoordinate, if_neg hc, expUnit_minimalLog]
theorem blockEnergy_lexicographicChart (hG : gaugeCovarianceStatement) (hs : ∀ i, 2 ≤ F.extent i)
    (hL : Odd F.blockSide) (a : ℝ) (S : Finset F.Cell) (V : F.GaugeField F.top) (W : F.GaugeField F.depth) :
    blockEnergy a S F.depth (chartedField (lexicographicChart S V W) V) V = blockEnergy a S F.depth W V := by
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  rw [blockEnergy_congr hs' hL a S _ (gaugeTransform (axialGauge 1 W) W) V
      (chartedField_lexicographicChart_eq hs hL S V W),
    blockEnergy_gaugeTransform hG hL.pos a S _ (fun z => axialGauge_cellCentre hs' hL 1 W z) W V]
theorem isAxialTreeBond_cellCentre_add (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) (y : F.Cell)
    (u : Fin 4 → ℤ) (l : Fin 4) (hu : u ∈ centredCube F.blockSide)
    (hu' : u + Pi.single l 1 ∈ centredCube F.blockSide) (hz : ∀ m, l < m → u m = 0) :
    IsAxialTreeBond (cellCentre F.depth y + siteOfCoords F.depth u, l) := by
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  refine ⟨?_, ?_⟩
  · show ¬ (enclosingCell (cellCentre F.depth y + siteOfCoords F.depth u + unitStep F.depth l) ≠
      enclosingCell (cellCentre F.depth y + siteOfCoords F.depth u))
    rw [cellCentre_add_siteOfCoords_add_unitStep, enclosingCell_cellCentre_add hs' hL y _ hu',
      enclosingCell_cellCentre_add hs' hL y _ hu]
    simp
  · intro m hm
    show cellOffset (cellCentre F.depth y + siteOfCoords F.depth u) m = 0
    rw [cellOffset_cellCentre_add hs' hL y u hu]
    exact hz m hm
theorem chartedField_of_isAxialTreeBond (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (x : F.Site F.depth) (i : Fin 4) (h : IsAxialTreeBond (x, i)) :
    chartedField w V x i = 1 := by
  simp only [chartedField]
  rw [if_neg h.1, if_pos h]
def offsetLength (u : Fin 4 → ℤ) : ℕ := ∑ m, (u m).natAbs
theorem offsetLength_succ (l : Fin 4) (u v : Fin 4 → ℤ) (hv : ∀ m, m ≠ l → v m = u m)
    (hl : (v l).natAbs + 1 = (u l).natAbs) : offsetLength v + 1 = offsetLength u := by
  unfold offsetLength
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l), ← Finset.add_sum_erase Finset.univ
    (fun m => (u m).natAbs) (Finset.mem_univ l)]
  have e : ∑ m ∈ Finset.univ.erase l, (v m).natAbs = ∑ m ∈ Finset.univ.erase l, (u m).natAbs := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hv m (Finset.ne_of_mem_erase hm)]
  rw [e]
  omega
theorem mem_centredCube_of_abs_le {M : ℕ} {w w' : Fin 4 → ℤ} (h : ∀ m, |w m| ≤ |w' m|)
    (hw : w' ∈ centredCube M) : w ∈ centredCube M := by
  rw [mem_centredCube_iff_abs_le] at hw ⊢
  exact fun m => (h m).trans (hw m)
theorem pathHolonomy_chartedField_axisPath (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (y : F.Cell) (N : ℕ) :
    ∀ o : Fin 4 → ℤ, o ∈ centredCube F.blockSide → offsetLength o ≤ N →
      pathHolonomy (chartedField w V) (cellCentre F.depth y) (axisPath o 1) = 1 := by
  have descend : ∀ o : Fin 4 → ℤ, o ∈ centredCube F.blockSide → o ≠ 0 → ∃ v : Fin 4 → ℤ,
      v ∈ centredCube F.blockSide ∧ offsetLength v + 1 = offsetLength o ∧
      (pathHolonomy (chartedField w V) (cellCentre F.depth y) (axisPath v 1) = 1 →
        pathHolonomy (chartedField w V) (cellCentre F.depth y) (axisPath o 1) = 1) := by
    intro o ho h0
    have hne : (Finset.univ.filter fun m => o m ≠ 0).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      apply h0
      funext m
      by_contra hm
      have : m ∈ (Finset.univ.filter fun m => o m ≠ 0) := by simpa using hm
      rw [hcon] at this
      simp at this
    set i := (Finset.univ.filter fun m => o m ≠ 0).max' hne with hi
    have him := Finset.max'_mem _ hne
    rw [← hi] at him
    have hoi : o i ≠ 0 := (Finset.mem_filter.1 him).2
    have hz : ∀ m, i < m → o m = 0 := by
      intro m hm
      by_contra h1
      have : m ≤ i := Finset.le_max' _ m (by simpa using h1)
      exact absurd hm (not_lt.2 this)
    rcases lt_or_gt_of_ne hoi with hneg | hpos
    · set v := o + Pi.single i 1 with hv
      have vi : v i = o i + 1 := by simp [hv]
      have vo : ∀ m, m ≠ i → v m = o m := fun m hm => by simp [hv, hm]
      have hvc : v ∈ centredCube F.blockSide := mem_centredCube_of_abs_le (fun m => by
        by_cases e : m = i
        · rw [e, vi, abs_of_nonpos (by omega), abs_of_neg hneg]; omega
        · rw [vo m e]) ho
      refine ⟨v, hvc, offsetLength_succ i o v vo (by rw [vi]; omega), fun h1 => ?_⟩
      rw [axisPath_of_neg o i hz hneg, pathHolonomy_append, h1, pathDisplacement_axisPath, one_mul]
      have e : cellCentre F.depth y + siteOfCoords F.depth v - unitStep F.depth i =
          cellCentre F.depth y + siteOfCoords F.depth o := by
        rw [hv, ← cellCentre_add_siteOfCoords_add_unitStep]; abel
      have ht := chartedField_of_isAxialTreeBond w V _ _ (isAxialTreeBond_cellCentre_add hs hL y o i ho hvc hz)
      simp only [pathHolonomy, linkValue, Bool.false_eq_true, if_false, mul_one]
      rw [e, ht, inv_one]
    · set v := o - Pi.single i 1 with hv
      have vi : v i = o i - 1 := by simp [hv]
      have vo : ∀ m, m ≠ i → v m = o m := fun m hm => by simp [hv, hm]
      have hvc : v ∈ centredCube F.blockSide := mem_centredCube_of_abs_le (fun m => by
        by_cases e : m = i
        · rw [e, vi, abs_of_nonneg (by omega), abs_of_pos hpos]; omega
        · rw [vo m e]) ho
      have hback : v + Pi.single i 1 = o := by rw [hv]; abel
      have hzv : ∀ m, i < m → v m = 0 := fun m hm => by rw [vo m hm.ne']; exact hz m hm
      refine ⟨v, hvc, offsetLength_succ i o v vo (by rw [vi]; omega), fun h1 => ?_⟩
      have e1 := axisPath_add_single_of_nonneg v i hzv (by omega)
      rw [hback] at e1
      rw [e1, pathHolonomy_append, h1, pathDisplacement_axisPath, one_mul]
      have ht := chartedField_of_isAxialTreeBond w V _ _
        (isAxialTreeBond_cellCentre_add hs hL y v i hvc (hback.symm ▸ ho) hzv)
      simp only [pathHolonomy, linkValue, if_true, mul_one]
      exact ht
  induction N with
  | zero =>
    intro o ho hN
    by_cases h0 : o = 0
    · rw [h0, axisPath_zero]; rfl
    · obtain ⟨v, -, h, -⟩ := descend o ho h0
      omega
  | succ N ih =>
    intro o ho hN
    by_cases h0 : o = 0
    · rw [h0, axisPath_zero]; rfl
    · obtain ⟨v, hv, h, h2⟩ := descend o ho h0
      exact h2 (ih v hv (by omega))
theorem axialGauge_chartedField (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (x : F.Site F.depth) :
    axialGauge 1 (chartedField w V) x = 1 := by
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  exact pathHolonomy_chartedField_axisPath hs hL w V _ _ _ (cellOffset_mem_and_eq hs' hL x).1 le_rfl
theorem gaugeTransform_axialGauge_of_agreeOnBonds (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (S : Finset F.Cell) (V : F.GaugeField F.top) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (γ : F.Site F.depth → UnitQuaternion) (Wl : F.GaugeField F.depth) (hγ : ∀ z, γ (cellCentre F.depth z) = 1)
    (hsame : AgreeOnBonds S F.depth Wl (gaugeTransform γ (chartedField w V))) (b : F.Site F.depth × Fin 4)
    (hb : b ∈ innerBonds S F.depth) :
    gaugeTransform (axialGauge 1 Wl) Wl b.1 b.2 = chartedField w V b.1 b.2 := by
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hG : ∀ x ∈ sitesOfCells S F.depth, axialGauge 1 Wl x = (γ x)⁻¹ := by
    intro x hx
    obtain ⟨ho, hxe⟩ := cellOffset_mem_and_eq hs' hL x
    have hy := (mem_sitesOfCells_depth hs' hL S x).1 hx
    have hQ : ∀ o ∈ centredCube F.blockSide,
        cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth o ∈ sitesOfCells S F.depth := fun o ho' => by
      rw [mem_sitesOfCells_depth hs' hL, enclosingCell_cellCentre_add hs' hL _ o ho']
      exact hy
    have h1 := pathHolonomy_congr (Q := sitesOfCells S F.depth) hsame _ _ (pathWithin_axisPath _ hQ _ ho 1)
    have h2 : axialGauge 1 Wl x =
        pathHolonomy Wl (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) 1) := rfl
    rw [h2, h1, pathHolonomy_gaugeTransform, hγ, pathDisplacement_axisPath, hxe]
    have h3 := axialGauge_chartedField hs hL w V x
    have h4 : pathHolonomy (chartedField w V) (cellCentre F.depth (enclosingCell x))
        (axisPath (cellOffset x) 1) = 1 := h3
    rw [h4]
    simp
  obtain ⟨x, i⟩ := b
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hb
  have hW : Wl x i = gaugeTransform γ (chartedField w V) x i := hsame (x, i) (by
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact hb)
  simp only [gaugeTransform] at hW ⊢
  rw [hG x hb.1, hG _ hb.2, hW]
  group
theorem bondCoordinate_of_agreeOnBonds (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) (S : Finset F.Cell)
    (V : F.GaugeField F.top) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (γ : F.Site F.depth → UnitQuaternion) (Wl : F.GaugeField F.depth) (hγ : ∀ z, γ (cellCentre F.depth z) = 1)
    (hsame : AgreeOnBonds S F.depth Wl (gaugeTransform γ (chartedField w V))) (b : F.Site F.depth × Fin 4)
    (hb : b ∈ chordBonds S) (hw : ‖(w b.1 b.2 : ℍ[ℝ])‖ < Real.pi) : bondCoordinate 1 V Wl b = w b.1 b.2 := by
  have hb' : b ∈ innerBonds S F.depth ∧ ¬ IsAxialTreeBond b := by
    simpa only [chordBonds, Finset.mem_filter] using hb
  have h1 := gaugeTransform_axialGauge_of_agreeOnBonds hs hL S V w γ Wl hγ hsame b hb'.1
  unfold bondCoordinate
  by_cases hc : IsCrossingBond b
  · rw [if_pos hc, h1]
    simp only [chartedField]
    rw [if_pos (show IsCrossingBond (b.1, b.2) from hc)]
    simp only [mul_inv_cancel_right]
    exact minimalLog_expUnit _ hw
  · rw [if_neg hc, h1]
    simp only [chartedField]
    rw [if_neg (show ¬ IsCrossingBond (b.1, b.2) from hc),
      if_neg (show ¬ IsAxialTreeBond (b.1, b.2) from hb'.2)]
    exact minimalLog_expUnit _ hw
theorem isCrossingBond_iff (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) (x : F.Site F.depth) (i : Fin 4) :
    IsCrossingBond (x, i) ↔ cellOffset x i = halfSide F.blockSide := by
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  obtain ⟨ho, hx⟩ := cellOffset_mem_and_eq hs' hL x
  constructor
  · intro hcr
    by_contra hne
    have hlt : cellOffset x i < halfSide F.blockSide := lt_of_le_of_ne (mem_centredCube.1 ho i).2 hne
    have hmem : cellOffset x + Pi.single i 1 ∈ centredCube F.blockSide := by
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
    conv_lhs => rw [← hx]
    rw [cellCentre_add_siteOfCoords_add_unitStep, enclosingCell_cellCentre_add hs' hL _ _ hmem]
  · intro h
    by_contra hcr
    have := cellOffset_lt_of_not_isCrossingBond hs hL x i hcr
    omega
theorem enclosingCell_add_unitStep_of_isCrossingBond (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (x : F.Site F.depth) (i : Fin 4) (h : IsCrossingBond (x, i)) :
    enclosingCell (x + unitStep F.depth i) = enclosingCell x + unitStep F.top i ∧
      cellOffset (x + unitStep F.depth i) = cellOffset x + (1 - (F.blockSide : ℤ)) • Pi.single i 1 := by
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  obtain ⟨ho, hx⟩ := cellOffset_mem_and_eq hs' hL x
  have hoi := (isCrossingBond_iff hs hL x i).1 h
  have hLz := blockSide_eq_two_mul_halfSide_add_one hL
  have hmem : cellOffset x + (1 - (F.blockSide : ℤ)) • (Pi.single i 1 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
    rw [mem_centredCube]
    intro m
    rw [add_smul_single_apply]
    by_cases e : m = i
    · rw [e, hoi]; simp only [if_true]; omega
    · simp only [e, if_false, add_zero]; exact mem_centredCube.1 ho m
  have e1 : x + unitStep F.depth i = cellCentre F.depth (enclosingCell x + unitStep F.top i) +
      siteOfCoords F.depth (cellOffset x + (1 - (F.blockSide : ℤ)) • Pi.single i 1) := by
    conv_lhs => rw [← hx]
    exact cellCentre_add_siteOfCoords_add_unitStep_crossing _ _ i
  rw [e1]
  exact ⟨enclosingCell_cellCentre_add hs' hL _ _ hmem, cellOffset_cellCentre_add hs' hL _ _ hmem⟩
theorem enclosingCell_add_unitStep_of_not_isCrossingBond (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (x : F.Site F.depth) (i : Fin 4) (h : ¬ IsCrossingBond (x, i)) :
    enclosingCell (x + unitStep F.depth i) = enclosingCell x ∧
      cellOffset (x + unitStep F.depth i) = cellOffset x + Pi.single i 1 := by
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  obtain ⟨ho, hx⟩ := cellOffset_mem_and_eq hs' hL x
  have hlt := cellOffset_lt_of_not_isCrossingBond hs hL x i h
  have hmem : cellOffset x + Pi.single i 1 ∈ centredCube F.blockSide := by
    rw [mem_centredCube]
    intro m
    by_cases e : m = i
    · rw [e]
      have := mem_centredCube.1 ho i
      simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    · simpa [e] using mem_centredCube.1 ho m
  have e1 : x + unitStep F.depth i =
      cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth (cellOffset x + Pi.single i 1) := by
    conv_lhs => rw [← hx]
    exact cellCentre_add_siteOfCoords_add_unitStep _ _ i
  rw [e1]
  exact ⟨enclosingCell_cellCentre_add hs' hL _ _ hmem, cellOffset_cellCentre_add hs' hL _ _ hmem⟩
theorem isCrossingBond_add_unitStep (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) (x : F.Site F.depth)
    (μ ν : Fin 4) (hne : μ ≠ ν) : IsCrossingBond (x + unitStep F.depth ν, μ) ↔ IsCrossingBond (x, μ) := by
  rw [isCrossingBond_iff hs hL, isCrossingBond_iff hs hL]
  have : cellOffset (x + unitStep F.depth ν) μ = cellOffset x μ := by
    by_cases hc : IsCrossingBond (x, ν)
    · rw [(enclosingCell_add_unitStep_of_isCrossingBond hs hL x ν hc).2, add_smul_single_apply]
      simp [hne]
    · rw [(enclosingCell_add_unitStep_of_not_isCrossingBond hs hL x ν hc).2]
      simp [hne]
  rw [this]
theorem norm_coe_mul_sub_coe_mul_le (a b a' b' : UnitQuaternion) :
    ‖((a * b : UnitQuaternion) : ℍ[ℝ]) - ((a' * b' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖(a : ℍ[ℝ]) - a'‖ + ‖(b : ℍ[ℝ]) - b'‖ := by apply _root_.YangMills.Construction.BlockAverages.CriticalShare.norm_coe_mul_sub_coe_mul_le <;> assumption
theorem norm_coe_inv_sub_coe_inv (g g' : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = ‖(g : ℍ[ℝ]) - g'‖ := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.norm_sub_inv_inv <;> assumption
theorem norm_linkValue_sub_le {j : ℕ} {Q : Finset (F.Site j)} {X X' : F.GaugeField j} (e : ℝ)
    (h : ∀ b ∈ cutBonds Q, ‖((X b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - (X' b.1 b.2 : UnitQuaternion)‖ ≤ e)
    {x : F.Site j} {st : PathStep} (hx : x ∈ Q) (hx' : x + stepDisplacement j st ∈ Q) :
    ‖((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) - (linkValue X' x st : UnitQuaternion)‖ ≤ e := by
  obtain ⟨i, b⟩ := st
  cases b
  · have hm : (x - unitStep j i, i) ∈ cutBonds Q := by
      simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      refine ⟨?_, ?_⟩
      · simpa [stepDisplacement, sub_eq_add_neg] using hx'
      · simpa using hx
    simp only [linkValue, Bool.false_eq_true, if_false]
    rw [norm_coe_inv_sub_coe_inv]
    exact h (x - unitStep j i, i) hm
  · have hm : (x, i) ∈ cutBonds Q := by
      simp only [cutBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨hx, by simpa [stepDisplacement] using hx'⟩
    simp only [linkValue, if_true]
    exact h (x, i) hm
theorem norm_pathHolonomy_sub_le {j : ℕ} {Q : Finset (F.Site j)} {X X' : F.GaugeField j} (e : ℝ)
    (h : ∀ b ∈ cutBonds Q, ‖((X b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - (X' b.1 b.2 : UnitQuaternion)‖ ≤ e)
    (l : List PathStep) : ∀ x, PathWithin Q x l →
      ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) - (pathHolonomy X' x l : UnitQuaternion)‖ ≤ l.length * e := by
  induction l with
  | nil => intro x _; simp [pathHolonomy]
  | cons st r ih =>
    intro x hp
    simp only [pathHolonomy, List.length_cons]
    refine (norm_coe_mul_sub_coe_mul_le _ _ _ _).trans ?_
    have h1 := norm_linkValue_sub_le e h hp.1 hp.2.head_mem
    have h2 := ih _ hp.2
    push_cast
    linarith
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem norm_chartedField_sub_le (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (x : F.Site F.depth) (i : Fin 4) (hw : ‖(w x i : ℍ[ℝ])‖ ≤ 1 / 4) :
    ‖((chartedField w V x i : UnitQuaternion) : ℍ[ℝ]) - (chartedField (fun _ _ => 0) V x i : UnitQuaternion)‖ ≤
      2 * ‖(w x i : ℍ[ℝ])‖ := by
  have h1 := norm_coe_expUnit_sub_one_le (w x i) hw
  simp only [chartedField]
  by_cases hc : IsCrossingBond (x, i)
  · rw [if_pos hc, if_pos hc, expUnit_zero, one_mul, coe_mul_unitQuaternion]
    have e : ((expUnit (w x i) : UnitQuaternion) : ℍ[ℝ]) * (V (enclosingCell x) i : UnitQuaternion) -
        (V (enclosingCell x) i : UnitQuaternion) =
        (((expUnit (w x i) : UnitQuaternion) : ℍ[ℝ]) - 1) * (V (enclosingCell x) i : UnitQuaternion) := by
      noncomm_ring
    rw [e, norm_mul_coe]
    exact h1
  · rw [if_neg hc, if_neg hc]
    by_cases ht : IsAxialTreeBond (x, i)
    · rw [if_pos ht, if_pos ht]
      simp
    · rw [if_neg ht, if_neg ht, expUnit_zero]
      simpa using h1
open Classical in
theorem chartedField_zero_apply (V : F.GaugeField F.top) (x : F.Site F.depth) (i : Fin 4) :
    chartedField (fun _ _ => 0) V x i = if IsCrossingBond (x, i) then V (enclosingCell x) i else 1 := by
  simp only [chartedField, expUnit_zero, one_mul]
  split_ifs <;> rfl
theorem plaquetteDefect_chartedField_zero_le (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    (S : Finset F.Cell) (V : F.GaugeField F.top) (r : ℝ) (hr : 0 ≤ r) (hV : IsCold S F.top r V)
    (p : F.Site F.depth × Fin 4 × Fin 4) (hp : p ∈ innerPlaquettes S F.depth) :
    plaquetteDefect (chartedField (fun _ _ => 0) V) p ≤ r := by
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  obtain ⟨x, μ, ν⟩ := p
  simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp
  obtain ⟨hx, hμν, hcor⟩ := hp
  have hne : μ ≠ ν := hμν.ne
  have hP := isCrossingBond_add_unitStep hs hL x μ ν hne
  have hQ := isCrossingBond_add_unitStep hs hL x ν μ hne.symm
  set C := chartedField (fun _ _ => 0) V with hC
  have hval : plaquetteHolonomy C (x, μ, ν) =
      C x μ * (C (x + unitStep F.depth μ) ν * ((C (x + unitStep F.depth ν) μ)⁻¹ * (C x ν)⁻¹)) := by
    have e3 : x + unitStep F.depth μ + unitStep F.depth ν - unitStep F.depth μ = x + unitStep F.depth ν := by abel
    have e4 : x + unitStep F.depth μ + unitStep F.depth ν + - unitStep F.depth μ - unitStep F.depth ν = x := by
      abel
    simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
      if_false, mul_one]
    rw [e3, e4]
  have cx : enclosingCell x ∈ S := (mem_sitesOfCells_depth hs' hL S x).1 hx
  have c2 : enclosingCell (x + unitStep F.depth μ) ∈ S :=
    (mem_sitesOfCells_depth hs' hL S _).1 (hcor (by simp [plaquetteCorners]))
  have c3 : enclosingCell (x + unitStep F.depth ν) ∈ S :=
    (mem_sitesOfCells_depth hs' hL S _).1 (hcor (by simp [plaquetteCorners]))
  have c4 : enclosingCell (x + unitStep F.depth μ + unitStep F.depth ν) ∈ S :=
    (mem_sitesOfCells_depth hs' hL S _).1 (hcor (by simp [plaquetteCorners]))
  unfold plaquetteDefect
  rw [hval, hC, chartedField_zero_apply V x μ, chartedField_zero_apply V (x + unitStep F.depth μ) ν,
    chartedField_zero_apply V (x + unitStep F.depth ν) μ, chartedField_zero_apply V x ν]
  by_cases h1 : IsCrossingBond (x, μ)
  · by_cases h2 : IsCrossingBond (x, ν)
    · rw [if_pos h1, if_pos (hQ.2 h2), if_pos (hP.2 h1), if_pos h2,
        (enclosingCell_add_unitStep_of_isCrossingBond hs hL x μ h1).1,
        (enclosingCell_add_unitStep_of_isCrossingBond hs hL x ν h2).1]
      have e1 := (enclosingCell_add_unitStep_of_isCrossingBond hs hL x μ h1).1
      have e2 := (enclosingCell_add_unitStep_of_isCrossingBond hs hL x ν h2).1
      have e3 := (enclosingCell_add_unitStep_of_isCrossingBond hs hL (x + unitStep F.depth μ) ν (hQ.2 h2)).1
      rw [e1] at c2 e3
      rw [e2] at c3
      rw [e3] at c4
      have hmem : (enclosingCell x, μ, ν) ∈ innerPlaquettes S F.top := by
        simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
        refine ⟨mem_sitesOfCells_top.2 cx, hμν, ?_⟩
        intro z hz
        simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact mem_sitesOfCells_top.2 cx
        · exact mem_sitesOfCells_top.2 c2
        · exact mem_sitesOfCells_top.2 c3
        · exact mem_sitesOfCells_top.2 c4
      have h3 := hV _ hmem
      have h4 : plaquetteHolonomy V (enclosingCell x, μ, ν) = V (enclosingCell x) μ *
          (V (enclosingCell x + unitStep F.top μ) ν *
          ((V (enclosingCell x + unitStep F.top ν) μ)⁻¹ * (V (enclosingCell x) ν)⁻¹)) := by
        have e5 : enclosingCell x + unitStep F.top μ + unitStep F.top ν - unitStep F.top μ =
            enclosingCell x + unitStep F.top ν := by abel
        have e6 : enclosingCell x + unitStep F.top μ + unitStep F.top ν + - unitStep F.top μ -
            unitStep F.top ν = enclosingCell x := by abel
        simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
          if_false, mul_one]
        rw [e5, e6]
      unfold plaquetteDefect at h3
      rw [h4] at h3
      exact h3.le
    · rw [if_pos h1, if_neg (fun h => h2 (hQ.1 h)), if_pos (hP.2 h1), if_neg h2,
        (enclosingCell_add_unitStep_of_not_isCrossingBond hs hL x ν h2).1]
      simpa using hr
  · by_cases h2 : IsCrossingBond (x, ν)
    · rw [if_neg h1, if_pos (hQ.2 h2), if_neg (fun h => h1 (hP.1 h)), if_pos h2,
        (enclosingCell_add_unitStep_of_not_isCrossingBond hs hL x μ h1).1]
      simpa using hr
    · rw [if_neg h1, if_neg (fun h => h2 (hQ.1 h)), if_neg (fun h => h1 (hP.1 h)), if_neg h2]
      simpa using hr
theorem plaquetteDefect_chartedField_le (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide) (S : Finset F.Cell)
    (V : F.GaugeField F.top) (r e : ℝ) (hr : 0 ≤ r) (hV : IsCold S F.top r V)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (he : e ≤ 1 / 4)
    (hw : ∀ b ∈ innerBonds S F.depth, ‖(w b.1 b.2 : ℍ[ℝ])‖ ≤ e) (p : F.Site F.depth × Fin 4 × Fin 4)
    (hp : p ∈ innerPlaquettes S F.depth) : plaquetteDefect (chartedField w V) p ≤ r + 8 * e := by
  have hc := plaquetteDefect_chartedField_zero_le hs hL S V r hr hV p hp
  have hcor : plaquetteCorners p ⊆ sitesOfCells S F.depth := by
    simp only [innerPlaquettes, Finset.mem_filter] at hp
    exact hp.2.2
  have hb : ∀ b ∈ cutBonds (sitesOfCells S F.depth), ‖((chartedField w V b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) -
      (chartedField (fun _ _ => 0) V b.1 b.2 : UnitQuaternion)‖ ≤ 2 * e := by
    intro b hb
    have h1 := hw b hb
    have := norm_chartedField_sub_le w V b.1 b.2 (h1.trans he)
    linarith
  have h2 := norm_pathHolonomy_sub_le (2 * e) hb _ _ (pathWithin_plaquette p hcor)
  simp only [List.length_cons, List.length_nil] at h2
  unfold plaquetteDefect at hc ⊢
  have h3 := norm_sub_le_norm_sub_add_norm_sub (((plaquetteHolonomy (chartedField w V) p : UnitQuaternion)) : ℍ[ℝ])
    (plaquetteHolonomy (chartedField (fun _ _ => 0) V) p : UnitQuaternion) 1
  have h4 : ‖((plaquetteHolonomy (chartedField w V) p : UnitQuaternion) : ℍ[ℝ]) -
      (plaquetteHolonomy (chartedField (fun _ _ => 0) V) p : UnitQuaternion)‖ ≤ 4 * (2 * e) := by
    have : (((0 + 1 + 1 + 1 + 1 : ℕ) : ℝ)) = 4 := by norm_num
    rw [this] at h2
    exact h2
  linarith
end GaugeFixing
end YangMills.Construction
end
