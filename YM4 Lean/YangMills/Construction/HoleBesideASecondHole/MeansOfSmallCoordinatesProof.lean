import YangMills.Construction.HoleBesideASecondHole.ChartOfSmallCoordinatesProof
import YangMills.Construction.HoleBesideASecondHole.MeansOfSmallCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.CellTerms
open BlockAverages LumpContours LumpContours.BlockLevels LocalNorms LatticePaths
variable {F : BlockFrame}
theorem norm_sub_pathHolonomy_le {j : ℕ} (Z : Finset (F.Site j)) (X Y : F.GaugeField j) (δ : ℝ) (_hδ : 0 ≤ δ)
    (h : ∀ x i, x ∈ Z → x + unitStep j i ∈ Z →
      ‖((X x i : UnitQuaternion) : ℍ[ℝ]) - (Y x i : UnitQuaternion)‖ ≤ δ) (l : List PathStep) :
    ∀ x, PathWithin Z x l →
      ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) - (pathHolonomy Y x l : UnitQuaternion)‖ ≤ l.length * δ := by
  induction l with
  | nil =>
    intro x _
    simp [pathHolonomy]
  | cons st r ih =>
    intro x hp
    have hs : ‖((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) - (linkValue Y x st : UnitQuaternion)‖ ≤ δ := by
      obtain ⟨d, b⟩ := st
      cases b
      · simp only [linkValue, Bool.false_eq_true, if_false]
        rw [norm_sub_inv_inv]
        have h1 := hp.1
        have h2 := hp.2.1
        simp only [stepDisplacement, Bool.false_eq_true, if_false] at h2
        have e1 : x + -unitStep j d = x - unitStep j d := by abel
        have e2 : x - unitStep j d + unitStep j d = x := by abel
        rw [e1] at h2
        exact h (x - unitStep j d) d h2 (by rw [e2]; exact h1)
      · simp only [linkValue, if_true]
        have h2 := hp.2.1
        simp only [stepDisplacement, if_true] at h2
        exact h x d hp.1 h2
    have h3 := ih _ hp.2.2
    simp only [pathHolonomy, List.length_cons, unitQuaternion_coe_mul]
    set a := ((linkValue X x st : UnitQuaternion) : ℍ[ℝ])
    set c := ((linkValue Y x st : UnitQuaternion) : ℍ[ℝ])
    set b := ((pathHolonomy X (x + stepDisplacement j st) r : UnitQuaternion) : ℍ[ℝ])
    set d := ((pathHolonomy Y (x + stepDisplacement j st) r : UnitQuaternion) : ℍ[ℝ])
    have e : a * b - c * d = (a - c) * b + c * (b - d) := by noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have n1 : ‖b‖ = 1 := unitQuaternion_norm _
    have n2 : ‖c‖ = 1 := unitQuaternion_norm _
    rw [n1, n2, mul_one, one_mul]
    push_cast
    linarith
theorem norm_sub_contourAverage_le (hL : Odd F.blockSide) {j : ℕ} (X Y : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) (e : ℝ)
    (h : ∀ a ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy X (refineSite c.1) (bondContour F.blockSide a π c.2) : UnitQuaternion) : ℍ[ℝ]) -
        (pathHolonomy Y (refineSite c.1) (bondContour F.blockSide a π c.2) : UnitQuaternion)‖ ≤ e) :
    ‖contourAverage X c - contourAverage Y c‖ ≤ e := by
  classical
  have hL0 : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  unfold contourAverage
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← Finset.sum_sub_distrib]
  have h1 : ‖∑ a ∈ centredCube F.blockSide,
      (∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide a π c.2) : UnitQuaternion) : ℍ[ℝ]) -
      ∑ π : Equiv.Perm (Fin 4),
        ((pathHolonomy Y (refineSite c.1) (bondContour F.blockSide a π c.2) : UnitQuaternion) : ℍ[ℝ]))‖ ≤
      24 * (F.blockSide : ℝ) ^ 4 * e := by
    refine (norm_sum_le _ _).trans ?_
    have h2 : ∀ a ∈ centredCube F.blockSide,
        ‖∑ π : Equiv.Perm (Fin 4),
          ((pathHolonomy X (refineSite c.1) (bondContour F.blockSide a π c.2) : UnitQuaternion) : ℍ[ℝ]) -
        ∑ π : Equiv.Perm (Fin 4),
          ((pathHolonomy Y (refineSite c.1) (bondContour F.blockSide a π c.2) : UnitQuaternion) : ℍ[ℝ])‖ ≤
          24 * e := by
      intro a ha
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun π _ => h a ha π).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      norm_num [Nat.factorial]
    refine (Finset.sum_le_sum h2).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, card_centredCube hL]
    push_cast
    linarith
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _
        ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) * (24 * (F.blockSide : ℝ) ^ 4 * e) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = e := by field_simp
theorem length_bondContour_le (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (i : Fin 4)
    (hh : WithinBlock F.blockSide h) :
    (bondContour F.blockSide h π i).length ≤ 5 * F.blockSide := by
  have e : List.finRange 4 = [0, 1, 2, 3] := by decide
  have hb : ∀ k, ((h k).natAbs : ℤ) ≤ ((F.blockSide : ℤ) - 1) / 2 := fun k => by
    rw [Int.natCast_natAbs]
    exact hh k
  have h0 := hb (π 0)
  have h1 := hb (π 1)
  have h2 := hb (π 2)
  have h3 := hb (π 3)
  simp only [bondContour, reversePath, axisPath, e, List.flatMap_cons, List.flatMap_nil, List.length_append,
    List.length_replicate, List.append_nil, List.length_map, List.length_reverse]
  omega
theorem levelScale_le_one (hL : 1 ≤ F.blockSide) (j : ℕ) : levelScale F j ≤ 1 := by apply _root_.YangMills.Construction.SmallChart.levelScale_le_one <;> assumption
theorem le_of_sum_pow_four_le {ι : Type} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (B : ℝ) (hB : 0 ≤ B)
    (h : ∑ i ∈ s, f i ^ 4 ≤ B ^ 4) {i : ι} (hi : i ∈ s) : f i ≤ B := by apply _root_.YangMills.Construction.SmallChart.le_of_sum_pow_four_le <;> assumption
theorem nonzeroAverages (hB : referenceBoundsStatement) (hG : levelGapNearCellStatement) :
    nonzeroAveragesStatement := by
  obtain ⟨C0, c0, L1, hC0, hc0, hB⟩ := hB
  obtain ⟨C2, hC2, L2, hG⟩ := hG
  refine ⟨max L1 L2, ?_⟩
  intro L hLo hLL del hdel
  have hL1 : L1 ≤ L := (le_max_left _ _).trans hLL
  have hL2 : L2 ≤ L := (le_max_right _ _).trans hLL
  obtain ⟨c2, hc2, hG2⟩ := hG L hLo hL2
  have hexp : 1 ≤ Real.exp (3 * del) := Real.one_le_exp (by positivity)
  set e3 := Real.exp (3 * del) with he3
  have he30 : 0 < e3 := by linarith
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLo.pos
  set ε : ℝ := 1 / (20 * L * C2) with hε
  have hε0 : 0 < ε := by positivity
  set ε' : ℝ := 1 / (2 * C0 + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hε'1 : ε' ≤ 1 := by
    rw [hε', div_le_one (by positivity)]
    linarith
  set cm := min (min (min c0 c2) ε) ε' with hcm
  have hcm0 : 0 < cm := lt_min (lt_min (lt_min hc0 hc2) hε0) hε'0
  refine ⟨cm / e3, by positivity, ?_⟩
  intro F m S hF hamb hm hreg r V hr hrc hcold U hU C hCS
  subst hF
  have hcmle : cm / e3 ≤ cm := div_le_self hcm0.le hexp
  have hrcm : r ≤ cm := hrc.trans hcmle
  have hrc0 : r ≤ c0 := hrcm.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hrc2 : r ≤ c2 := hrcm.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hrε' : r ≤ ε' := hrcm.trans (min_le_right _ _)
  have hcm2 : cm ≤ c2 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hcmε : cm ≤ ε := (min_le_left _ _).trans (min_le_right _ _)
  set R := referenceFieldChain S V with hR
  obtain ⟨-, -, -, -, -, b6⟩ := hB F m S hLo hL1 hamb hm hreg r V hr hrc0 hcold
  have hnorm : ∀ y ∈ S, unweightedLocalNorm S R U y ≤ cm := by
    intro y hy
    have h1 := unweightedLocalNorm_le_exp_mul_supWeightedNorm del hdel S R U y hy
    have h2 : e3 * supWeightedNorm S del R U ≤ e3 * (cm / e3) := mul_le_mul_of_nonneg_left hU he30.le
    have h3 : e3 * (cm / e3) = cm := by field_simp
    linarith
  intro j hj c hc
  have hj' : j < F.top := by omega
  have hj1 : j + 1 ≤ F.top := hj'
  have hcS : c ∈ innerBonds S (j + 1) := by
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨(mem_sitesOfCells_iff hj1 hLo).2 (hCS hc.1), (mem_sitesOfCells_iff hj1 hLo).2 (hCS hc.2)⟩
  obtain ⟨h60, h61⟩ := b6 j hj' c hcS
  have hlev : levelScale F (j + 1) ^ 4 ≤ 1 := pow_le_one₀ (by unfold levelScale; positivity)
    (levelScale_le_one hLo.pos _)
  have hmeanR : 1 / 2 ≤ ‖contourAverage (R j) c‖ := by
    have h1 : C0 * r ^ 2 * levelScale F (j + 1) ^ 4 ≤ C0 * r ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hlev (by positivity)
    have h2 : r ^ 2 ≤ r * ε' := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left hrε' hr.le
    have h3 : r * ε' ≤ ε' * ε' := mul_le_mul_of_nonneg_right hrε' hε'0.le
    have h4 : ε' * ε' ≤ ε' * 1 := mul_le_mul_of_nonneg_left hε'1 hε'0.le
    have h5 : C0 * ε' ≤ 1 / 2 := by
      rw [hε', mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    have h6 : C0 * r ^ 2 ≤ C0 * ε' := mul_le_mul_of_nonneg_left (by linarith) hC0.le
    linarith
  have hR0 : contourAverage (R j) c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hmeanR
    norm_num at hmeanR
  refine ⟨hR0, ?_⟩
  set δ := C2 * cm with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hclose : ∀ x i, x ∈ sitesBelow j c.1 ∪ sitesBelow j (c.1 + unitStep (j + 1) c.2) →
      x + unitStep j i ∈ sitesBelow j c.1 ∪ sitesBelow j (c.1 + unitStep (j + 1) c.2) →
      ‖((chartField R U j x i : UnitQuaternion) : ℍ[ℝ]) - (R j x i : UnitQuaternion)‖ ≤ δ := by
    intro x i h1 h2
    have hin : ∀ w : F.Site j, w ∈ sitesBelow j c.1 ∪ sitesBelow j (c.1 + unitStep (j + 1) c.2) →
        enclosingCell w ∈ S := by
      intro w hw
      rcases Finset.mem_union.1 hw with h | h
      · rw [enclosingCell_of_mem_sitesBelow (Nat.le_succ j) hj1 hLo h]
        exact hCS hc.1
      · rw [enclosingCell_of_mem_sitesBelow (Nat.le_succ j) hj1 hLo h]
        exact hCS hc.2
    have hxb : (x, i) ∈ bondsOver S {enclosingCell x} j := by
      refine Finset.mem_filter.2 ⟨?_, Finset.mem_singleton.2 rfl⟩
      simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      exact ⟨(mem_sitesOfCells_iff hj'.le hLo).2 (hin x h1), (mem_sitesOfCells_iff hj'.le hLo).2 (hin _ h2)⟩
    have hs := hG2 F m S rfl hamb hm hreg r V hr hrc2 hcold U (enclosingCell x) cm (hin x h1) hcm0.le hcm2
      (hnorm _ (hin x h1)) j hj'
    have hg : normSubOne (chartGap R U j x i) ≤ δ :=
      le_of_sum_pow_four_le _ (fun b : F.Site j × Fin 4 => normSubOne (chartGap R U j b.1 b.2))
        (fun _ => norm_nonneg _) δ hδ0 hs.2 (i := (x, i)) hxb
    have e : ((chartField R U j x i : UnitQuaternion) : ℍ[ℝ]) - (R j x i : UnitQuaternion) =
        (((chartGap R U j x i : UnitQuaternion) : ℍ[ℝ]) - 1) * (R j x i : UnitQuaternion) := by
      simp only [chartGap, Submonoid.coe_mul, sub_mul, one_mul, mul_assoc, unitQuaternion_inv_mul, mul_one]
    rw [e, norm_mul, unitQuaternion_norm, mul_one]
    exact hg
  have hcl : ‖contourAverage (chartField R U j) c - contourAverage (R j) c‖ ≤ 5 * F.blockSide * δ :=
    norm_sub_contourAverage_le hLo _ _ c _ fun a ha π => by
      have hp := bondContour_within_blocks j hj' hLo c a (withinBlock_of_mem_centredCube ha) π
      have h1 := norm_sub_pathHolonomy_le _ _ _ δ hδ0 hclose _ _ hp
      refine h1.trans ?_
      have hl : ((bondContour F.blockSide a π c.2).length : ℝ) ≤ 5 * F.blockSide := by
        exact_mod_cast length_bondContour_le a π c.2 (withinBlock_of_mem_centredCube ha)
      exact mul_le_mul_of_nonneg_right hl hδ0
  have hsm : 5 * (F.blockSide : ℝ) * δ ≤ 1 / 4 := by
    have h1 : δ ≤ C2 * ε := mul_le_mul_of_nonneg_left hcmε hC2.le
    have h2 : 5 * (F.blockSide : ℝ) * (C2 * ε) = 1 / 4 := by
      rw [hε]
      field_simp
      ring
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 5 * (F.blockSide : ℝ))
    linarith
  have hX0 : contourAverage (chartField R U j) c ≠ 0 := by
    intro h0
    rw [h0, zero_sub, norm_neg] at hcl
    linarith
  unfold gaugedContourAverage
  exact mul_ne_zero (mul_ne_zero (BlockAverages.coe_unitQuaternion_ne_zero _) hX0)
    (BlockAverages.coe_unitQuaternion_ne_zero _)
end YangMills.Construction.CellTerms
end
