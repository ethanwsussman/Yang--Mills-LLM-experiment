import YangMills.Construction.HoleBesideASecondHole.CellsPutBackProof
import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.TermsAgainstTheirFirstOrderProof
import YangMills.Construction.HoleBesideASecondHole.ChartOfSmallCoordinates
import YangMills.Construction.HoleBesideASecondHole.NormsNearACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.SmallChart
open BlockAverages
variable {F : BlockFrame}
theorem pathHolonomy_gaugeTransform {j : ℕ} (g : F.Site j → UnitQuaternion) (X : F.GaugeField j) (l : List PathStep) :
    ∀ x, pathHolonomy (gaugeTransform g X) x l =
      g x * pathHolonomy X x l * (g (x + LumpContours.BlockLevels.pathDisplacement j l))⁻¹ := by apply _root_.YangMills.Construction.GaugeFixing.pathHolonomy_gaugeTransform <;> assumption
theorem norm_pathHolonomy_sub_one_le {j : ℕ} (Z : Finset (F.Site j)) (X : F.GaugeField j) (δ : ℝ) (hδ : 0 ≤ δ)
    (hX : ∀ x i, x ∈ Z → x + unitStep j i ∈ Z → ‖((X x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ δ) (l : List PathStep) :
    ∀ x, LumpContours.BlockLevels.PathWithin Z x l →
      ‖((pathHolonomy X x l : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ l.length * δ := by
  induction l with
  | nil =>
    intro x _
    simp [pathHolonomy]
  | cons st r ih =>
    intro x h
    have hs : ‖((linkValue X x st : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ δ := by
      obtain ⟨d, b⟩ := st
      cases b
      · simp only [linkValue, Bool.false_eq_true, if_false]
        rw [norm_coe_inv_sub_one]
        have h1 := h.1
        have h2 := h.2.1
        simp only [stepDisplacement, Bool.false_eq_true, if_false] at h2
        have e1 : x + -unitStep j d = x - unitStep j d := by abel
        have e2 : x - unitStep j d + unitStep j d = x := by abel
        rw [e1] at h2
        exact hX (x - unitStep j d) d h2 (by rw [e2]; exact h1)
      · simp only [linkValue, if_true]
        have h2 := h.2.1
        simp only [stepDisplacement, if_true] at h2
        exact hX x d h.1 h2
    have h3 := ih _ h.2.2
    simp only [pathHolonomy, List.length_cons]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    push_cast
    linarith
theorem length_axisPath_le (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4))
    (hh : LumpContours.BlockLevels.WithinBlock F.blockSide h) :
    (axisPath h π).length ≤ 2 * F.blockSide := by
  have e : List.finRange 4 = [0, 1, 2, 3] := by decide
  have hb : ∀ k, ((h k).natAbs : ℤ) ≤ ((F.blockSide : ℤ) - 1) / 2 := fun k => by
    rw [Int.natCast_natAbs]
    exact hh k
  have h0 := hb (π 0)
  have h1 := hb (π 1)
  have h2 := hb (π 2)
  have h3 := hb (π 3)
  simp only [axisPath, e, List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_replicate,
    List.length_nil, List.append_nil]
  omega
theorem norm_average_sub_one_le {ι : Type} (s : Finset ι) (a : ι → ℍ[ℝ]) (c e : ℝ) (hc0 : 0 ≤ c)
    (hc : c * s.card = 1) (h : ∀ i ∈ s, ‖a i - 1‖ ≤ e) : ‖c • ∑ i ∈ s, a i - 1‖ ≤ e := by
  have e1 : c • ∑ i ∈ s, a i - 1 = c • ∑ i ∈ s, (a i - 1) := by
    rw [Finset.sum_sub_distrib, smul_sub]
    congr 1
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have : c • ((s.card : ℍ[ℝ])) = ((c * s.card : ℝ) : ℍ[ℝ]) := by
      rw [← Quaternion.coe_natCast, ← Quaternion.coe_mul_eq_smul, Quaternion.coe_mul]
    rw [this, hc]
    rfl
  rw [e1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  calc c * ‖∑ i ∈ s, (a i - 1)‖ ≤ c * ∑ i ∈ s, ‖a i - 1‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hc0
    _ ≤ c * (s.card * e) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        have := Finset.sum_le_card_nsmul s (fun i => ‖a i - 1‖) e h
        simpa using this
    _ = e := by rw [← mul_assoc, hc, one_mul]
theorem norm_polarUnit_sub_one_le_four_mul {q : ℍ[ℝ]} {e : ℝ} (hq : ‖q - 1‖ ≤ e) (he : e ≤ 1 / 2) :
    ‖((polarUnit q : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 4 * e := by
  have hre : |(q - 1).re| ≤ ‖q - 1‖ := by
    have h := quaternion_re_le_norm (q - 1)
    have h' := quaternion_re_le_norm (-(q - 1))
    rw [norm_neg] at h'
    simp only [Quaternion.re_neg] at h'
    rw [abs_le]
    constructor <;> linarith
  have hr : 1 / 2 ≤ q.re := by
    have := (abs_le.1 (hre.trans hq)).1
    simp only [Quaternion.re_sub, Quaternion.re_one] at this
    linarith
  have hn : 1 / 2 ≤ ‖q‖ := hr.trans (quaternion_re_le_norm q)
  have h0 : q ≠ 0 := by
    intro h
    rw [h] at hn
    norm_num at hn
  have h1 := norm_polarUnit_sub_one_le (by linarith : 0 ≤ q.re) h0
  have hp : ‖pureComponent q‖ ≤ e := by
    have e1 : pureComponent q = pureComponent (q - 1) := by
      rw [pureComponent_sub, pureComponent_one, sub_zero]
    rw [e1]
    exact (norm_pureComponent_le _).trans hq
  refine h1.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (pureComponent q), norm_nonneg q]
theorem polarUnit_conj (g : UnitQuaternion) (q : ℍ[ℝ]) :
    polarUnit ((g : ℍ[ℝ]) * q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) = g * polarUnit q * g⁻¹ := by
  by_cases hq : q = 0
  · subst hq
    have h0 : polarUnit (0 : ℍ[ℝ]) = 1 := dif_pos rfl
    simp [h0]
  · have h0 : (g : ℍ[ℝ]) * q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (coe_unitQuaternion_ne_zero g) hq) (coe_unitQuaternion_ne_zero _)
    apply Subtype.ext
    rw [coe_polarUnit h0]
    simp only [Submonoid.coe_mul]
    rw [coe_polarUnit hq, norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
    simp only [mul_smul_comm, smul_mul_assoc]
theorem inv_count_mul_card_contours (hL : Odd F.blockSide) :
    (1 / (24 * (F.blockSide : ℝ) ^ 4)) *
      ((centredCube F.blockSide ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin 4)))).card : ℝ) = 1 := by apply _root_.YangMills.Construction.BlockAverages.TermwiseBounds.contour_weight_mul_card <;> assumption
theorem norm_conj_balancingGauge_sub_one_le (hL : Odd F.blockSide) {j : ℕ} (X R : F.GaugeField j)
    (y : F.Site (j + 1)) (g : UnitQuaternion) (e : ℝ) (he : e ≤ 1 / 2)
    (hterm : ∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((g⁻¹ * (pathHolonomy X (refineSite y) (axisPath h π) *
        (pathHolonomy R (refineSite y) (axisPath h π))⁻¹) * g : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e) :
    ‖((g⁻¹ * balancingGauge X R y * g : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 4 * e := by
  classical
  have hL0 : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  set q := relativePathAverage X R y with hq
  set q' : ℍ[ℝ] := ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * q * (g : ℍ[ℝ]) with hq'
  have hmean : ‖q' - 1‖ ≤ e := by
    have h1 : q' = (1 / (24 * (F.blockSide : ℝ) ^ 4)) •
        ∑ i ∈ centredCube F.blockSide ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin 4))),
        ((g⁻¹ * (pathHolonomy X (refineSite y) (axisPath i.1 i.2) *
          (pathHolonomy R (refineSite y) (axisPath i.1 i.2))⁻¹) * g : UnitQuaternion) : ℍ[ℝ]) := by
      rw [hq', hq]
      unfold relativePathAverage
      rw [mul_smul_comm, smul_mul_assoc, Finset.sum_product]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun π _ => ?_
      simp only [Submonoid.coe_mul]
    rw [h1]
    exact norm_average_sub_one_le _ _ _ e (by positivity) (inv_count_mul_card_contours hL) fun i hi =>
      hterm i.1 (Finset.mem_product.1 hi).1 i.2
  have h2 := norm_polarUnit_sub_one_le_four_mul hmean he
  have e1 : g⁻¹ * balancingGauge X R y * g = (polarUnit q')⁻¹ := by
    have h3 : polarUnit q' = g⁻¹ * polarUnit q * g := by
      have := polarUnit_conj g⁻¹ q
      rw [inv_inv] at this
      exact this
    rw [h3]
    show g⁻¹ * (polarUnit q)⁻¹ * g = (g⁻¹ * polarUnit q * g)⁻¹
    group
  rw [e1, norm_coe_inv_sub_one]
  exact h2
theorem refineSite_injective (hL : Odd F.blockSide) {y y' : F.Cell} (h : refineSite y = refineSite y') :
    y = y' := by
  have hmem : ∀ w : F.Cell, refineSite w ∈ LumpContours.sitesBelow F.depth w := fun w => by
    have := LumpContours.BlockLevels.refineSite_add_mem_sitesBelow F.depth w (o := 0) (fun m => by
      have : (0 : ℤ) ≤ ((F.blockSide : ℤ) - 1) / 2 := by
        obtain ⟨q, hq⟩ := hL
        rw [hq]
        push_cast
        omega
      simpa using this)
    simpa [LumpContours.BlockLevels.siteOfCoords_zero] using this
  have e1 := LumpContours.BlockLevels.enclosingCell_of_mem_sitesBelow (Nat.le_succ _) le_rfl hL (hmem y)
  have e2 := LumpContours.BlockLevels.enclosingCell_of_mem_sitesBelow (Nat.le_succ _) le_rfl hL (hmem y')
  rw [LumpContours.BlockLevels.enclosingCell_cell hL.pos] at e1 e2
  rw [← e1, ← e2, h]
theorem centreGauge_refineSite (hL : Odd F.blockSide) (k : F.Cell → UnitQuaternion) (y : F.Cell) :
    CellTerms.centreGauge k (refineSite y) = k y := by
  unfold CellTerms.centreGauge
  have hex : ∃ y' : F.Cell, refineSite y' = refineSite y := ⟨y, rfl⟩
  rw [dif_pos hex, refineSite_injective hL hex.choose_spec]
theorem cellOffset_spec (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide) (x : F.Site F.depth) :
    LumpContours.BlockLevels.WithinBlock F.blockSide (cellOffset x) ∧
      cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth (cellOffset x) = x := by apply _root_.YangMills.Construction.Reinsertion.cellOffset_spec <;> assumption
theorem refineSite_eq_cellCentre (y : F.Cell) : refineSite y = cellCentre F.depth y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
theorem axialGauge_transform_eq (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide) (X : F.GaugeField F.depth)
    (k : F.Cell → UnitQuaternion) (π : Equiv.Perm (Fin 4)) (x : F.Site F.depth) (i : Fin 4) :
    gaugeTransform (LumpContours.axialGauge π (gaugeTransform (CellTerms.centreGauge k) X))
        (gaugeTransform (CellTerms.centreGauge k) X) x i =
      k (enclosingCell x) * (pathHolonomy X (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) π) *
        X x i * (pathHolonomy X (cellCentre F.depth (enclosingCell (x + unitStep F.depth i)))
          (axisPath (cellOffset (x + unitStep F.depth i)) π))⁻¹) *
        (k (enclosingCell (x + unitStep F.depth i)))⁻¹ := by
  have hT : ∀ w : F.Site F.depth, LumpContours.axialGauge π (gaugeTransform (CellTerms.centreGauge k) X) w =
      k (enclosingCell w) * pathHolonomy X (cellCentre F.depth (enclosingCell w)) (axisPath (cellOffset w) π) *
        (CellTerms.centreGauge k w)⁻¹ := by
    intro w
    unfold LumpContours.axialGauge
    rw [pathHolonomy_gaugeTransform, LumpContours.BlockLevels.pathDisplacement_axisPath,
      (cellOffset_spec hamb hL w).2, ← refineSite_eq_cellCentre, centreGauge_refineSite hL]
  simp only [gaugeTransform]
  rw [hT, hT]
  group
def patchFrame (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (x : F.Site F.depth) : UnitQuaternion :=
  GaugeMap.frameChange S V z (baseSite x)
structure FrameNearOne (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (X Rt : F.GaugeField F.depth)
    (δ : ℝ) : Prop where
  field : ∀ (x : F.Site F.depth) (d : Fin 4), (x, d) ∈ innerBonds S F.depth → enclosingCell x ∈ cellBall S z 1 →
    ‖(((patchFrame S V z x)⁻¹ * X x d * patchFrame S V z (x + unitStep F.depth d) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ δ
  reference : ∀ (x : F.Site F.depth) (d : Fin 4), (x, d) ∈ innerBonds S F.depth → enclosingCell x ∈ cellBall S z 1 →
    ‖(((patchFrame S V z x)⁻¹ * Rt x d * patchFrame S V z (x + unitStep F.depth d) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ δ
section Near
variable {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell} {X Rt : F.GaugeField F.depth} {δ : ℝ}
theorem gaugeTransform_inv_apply (g : F.Site F.depth → UnitQuaternion) (Y : F.GaugeField F.depth)
    (x : F.Site F.depth) (d : Fin 4) :
    gaugeTransform (fun w => (g w)⁻¹) Y x d = (g x)⁻¹ * Y x d * g (x + unitStep F.depth d) := by
  simp [gaugeTransform]
theorem innerBond_of_mem_sitesBelow (hL : Odd F.blockSide) {y : F.Cell} (hy : y ∈ cellBall S z 1)
    {x : F.Site F.depth} {d : Fin 4} (h1 : x ∈ LumpContours.sitesBelow F.depth y)
    (h2 : x + unitStep F.depth d ∈ LumpContours.sitesBelow F.depth y) :
    (x, d) ∈ innerBonds S F.depth ∧ enclosingCell x ∈ cellBall S z 1 := by
  have hyS : y ∈ S := (Finset.mem_filter.1 hy).1
  have hm : ∀ w : F.Site F.depth, w ∈ LumpContours.sitesBelow F.depth y → w ∈ sitesOfCells S F.depth :=
    fun w hw => by
      rw [← LumpContours.BlockLevels.cutBelow_eq_sitesOfCells]
      exact Finset.mem_biUnion.2 ⟨y, hyS, hw⟩
  constructor
  · simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hm x h1, hm _ h2⟩
  · rw [LumpContours.BlockLevels.enclosingCell_of_mem_sitesBelow (Nat.le_succ _) le_rfl hL h1,
      LumpContours.BlockLevels.enclosingCell_cell hL.pos]
    exact hy
theorem norm_framed_axisPath_sub_one_le (hL : Odd F.blockSide) (hδ : 0 ≤ δ) (Y : F.GaugeField F.depth)
    (hY : ∀ (x : F.Site F.depth) (d : Fin 4), (x, d) ∈ innerBonds S F.depth → enclosingCell x ∈ cellBall S z 1 →
      ‖(((patchFrame S V z x)⁻¹ * Y x d * patchFrame S V z (x + unitStep F.depth d) : UnitQuaternion) : ℍ[ℝ]) - 1‖
        ≤ δ)
    {y : F.Cell} (hy : y ∈ cellBall S z 1) (h : Fin 4 → ℤ)
    (hh : LumpContours.BlockLevels.WithinBlock F.blockSide h) (π : Equiv.Perm (Fin 4)) :
    ‖(((patchFrame S V z (refineSite y))⁻¹ * pathHolonomy Y (refineSite y) (axisPath h π) *
        patchFrame S V z (refineSite y + LumpContours.BlockLevels.pathDisplacement F.depth (axisPath h π)) :
          UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * F.blockSide * δ := by
  have hp := LumpContours.BlockLevels.axisPath_within_block F.depth hL y h hh π
  have hn := norm_pathHolonomy_sub_one_le (LumpContours.sitesBelow F.depth y)
    (gaugeTransform (fun w => (patchFrame S V z w)⁻¹) Y) δ hδ
    (fun x i h1 h2 => by
      obtain ⟨b1, b2⟩ := innerBond_of_mem_sitesBelow hL hy h1 h2
      rw [gaugeTransform_inv_apply]
      exact hY x i b1 b2) _ _ hp
  rw [pathHolonomy_gaugeTransform, inv_inv] at hn
  refine hn.trans ?_
  have hl : ((axisPath h π).length : ℝ) ≤ 2 * F.blockSide := by exact_mod_cast length_axisPath_le h π hh
  exact mul_le_mul_of_nonneg_right hl hδ
theorem norm_framed_balancingGauge_sub_one_le (hL : Odd F.blockSide) (hN : FrameNearOne S V z X Rt δ)
    (hδ : 0 ≤ δ) (hsmall : 4 * F.blockSide * δ ≤ 1 / 2) {y : F.Cell} (hy : y ∈ cellBall S z 1) :
    ‖(((patchFrame S V z (refineSite y))⁻¹ * balancingGauge X Rt y * patchFrame S V z (refineSite y) :
      UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 16 * F.blockSide * δ := by
  have := norm_conj_balancingGauge_sub_one_le hL X Rt y (patchFrame S V z (refineSite y))
    (4 * F.blockSide * δ) hsmall (fun h hh π => by
    have h1 := norm_framed_axisPath_sub_one_le hL hδ X hN.field hy h
      (LumpContours.BlockLevels.withinBlock_of_mem_centredCube hh) π
    have h2 := norm_framed_axisPath_sub_one_le hL hδ Rt hN.reference hy h
      (LumpContours.BlockLevels.withinBlock_of_mem_centredCube hh) π
    set g := patchFrame S V z (refineSite y)
    set g' := patchFrame S V z (refineSite y + LumpContours.BlockLevels.pathDisplacement F.depth (axisPath h π))
    have e : g⁻¹ * (pathHolonomy X (refineSite y) (axisPath h π) *
        (pathHolonomy Rt (refineSite y) (axisPath h π))⁻¹) * g =
        (g⁻¹ * pathHolonomy X (refineSite y) (axisPath h π) * g') *
          (g⁻¹ * pathHolonomy Rt (refineSite y) (axisPath h π) * g')⁻¹ := by
      group
    rw [e]
    refine (norm_coe_mul_sub_one_le _ _).trans ?_
    rw [norm_coe_inv_sub_one]
    linarith)
  calc _ ≤ _ := this
    _ = _ := by ring
def blockLoop (X : F.GaugeField F.depth) (π : Equiv.Perm (Fin 4)) (x : F.Site F.depth) (i : Fin 4) :
    UnitQuaternion :=
  pathHolonomy X (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) π) * X x i *
    (pathHolonomy X (cellCentre F.depth (enclosingCell (x + unitStep F.depth i)))
      (axisPath (cellOffset (x + unitStep F.depth i)) π))⁻¹
theorem norm_framed_blockLoop_sub_one_le (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    (hN : FrameNearOne S V z X Rt δ) (hδ : 0 ≤ δ)
    (π : Equiv.Perm (Fin 4)) {x : F.Site F.depth} {i : Fin 4} (hb : (x, i) ∈ innerBonds S F.depth)
    (h1 : enclosingCell x ∈ cellBall S z 1) (h2 : enclosingCell (x + unitStep F.depth i) ∈ cellBall S z 1) :
    ‖(((patchFrame S V z (cellCentre F.depth (enclosingCell x)))⁻¹ * blockLoop X π x i *
        patchFrame S V z (cellCentre F.depth (enclosingCell (x + unitStep F.depth i))) : UnitQuaternion) :
          ℍ[ℝ]) - 1‖ ≤ (4 * F.blockSide + 1) * δ := by
  obtain ⟨o1, e1⟩ := cellOffset_spec hamb hL x
  obtain ⟨o2, e2⟩ := cellOffset_spec hamb hL (x + unitStep F.depth i)
  have l1 := norm_framed_axisPath_sub_one_le hL hδ X hN.field h1 (cellOffset x) o1 π
  have l2 := norm_framed_axisPath_sub_one_le hL hδ X hN.field h2 (cellOffset (x + unitStep F.depth i)) o2 π
  rw [LumpContours.BlockLevels.pathDisplacement_axisPath, refineSite_eq_cellCentre, e1] at l1
  rw [LumpContours.BlockLevels.pathDisplacement_axisPath, refineSite_eq_cellCentre, e2] at l2
  have hb' := hN.field x i hb h1
  set g := patchFrame S V z (cellCentre F.depth (enclosingCell x))
  set g' := patchFrame S V z (cellCentre F.depth (enclosingCell (x + unitStep F.depth i)))
  set A := pathHolonomy X (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) π)
  set B := pathHolonomy X (cellCentre F.depth (enclosingCell (x + unitStep F.depth i)))
    (axisPath (cellOffset (x + unitStep F.depth i)) π)
  set fx := patchFrame S V z x
  set fx' := patchFrame S V z (x + unitStep F.depth i)
  have e : g⁻¹ * blockLoop X π x i * g' = (g⁻¹ * A * fx) * (fx⁻¹ * X x i * fx') * (g'⁻¹ * B * fx')⁻¹ := by
    show g⁻¹ * (A * X x i * B⁻¹) * g' = _
    group
  rw [e]
  refine (norm_coe_mul_sub_one_le _ _).trans ?_
  rw [norm_coe_inv_sub_one]
  have := norm_coe_mul_sub_one_le (g⁻¹ * A * fx) (fx⁻¹ * X x i * fx')
  nlinarith
theorem norm_chord_sub_one_le (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    (hN : FrameNearOne S V z X Rt δ) (hδ : 0 ≤ δ)
    (k : F.Cell → UnitQuaternion) (π : Equiv.Perm (Fin 4)) {x : F.Site F.depth} {i : Fin 4}
    (hb : (x, i) ∈ innerBonds S F.depth)
    (h1 : enclosingCell x ∈ cellBall S z 1) (hc : enclosingCell (x + unitStep F.depth i) = enclosingCell x) :
    ‖((gaugeTransform (LumpContours.axialGauge π (gaugeTransform (CellTerms.centreGauge k) X))
        (gaugeTransform (CellTerms.centreGauge k) X) x i : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      (4 * F.blockSide + 1) * δ := by
  have hl := norm_framed_blockLoop_sub_one_le hamb hL hN hδ π hb h1 (by rw [hc]; exact h1)
  rw [axialGauge_transform_eq hamb hL]
  rw [hc] at hl ⊢
  have hfold : pathHolonomy X (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) π) * X x i *
      (pathHolonomy X (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset (x + unitStep F.depth i)) π))⁻¹ =
        blockLoop X π x i := by
    unfold blockLoop
    rw [hc]
  rw [hfold, norm_coe_conj_sub_one]
  set g := patchFrame S V z (cellCentre F.depth (enclosingCell x))
  have := norm_coe_conj_sub_one g⁻¹ (blockLoop X π x i)
  rw [inv_inv] at this
  rw [← this]
  exact hl
theorem norm_crossing_sub_one_le (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    (hN : FrameNearOne S V z X Rt δ) (hδ : 0 ≤ δ)
    (hsmall : 4 * F.blockSide * δ ≤ 1 / 2) (π : Equiv.Perm (Fin 4)) {x : F.Site F.depth} {i : Fin 4}
    (hb : (x, i) ∈ innerBonds S F.depth) (h1 : enclosingCell x ∈ cellBall S z 1)
    (h2 : enclosingCell (x + unitStep F.depth i) ∈ cellBall S z 1)
    (T : UnitQuaternion) (τ : ℝ)
    (hT : ‖(((patchFrame S V z (cellCentre F.depth (enclosingCell x)))⁻¹ * T *
        patchFrame S V z (cellCentre F.depth (enclosingCell (x + unitStep F.depth i))) : UnitQuaternion) :
          ℍ[ℝ]) - 1‖ ≤ τ) :
    ‖((gaugeTransform (LumpContours.axialGauge π (gaugeTransform (CellTerms.centreGauge (balancingGauge X Rt)) X))
        (gaugeTransform (CellTerms.centreGauge (balancingGauge X Rt)) X) x i * T⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖
      ≤ (36 * F.blockSide + 1) * δ + τ := by
  have hl := norm_framed_blockLoop_sub_one_le hamb hL hN hδ π hb h1 h2
  have k1 := norm_framed_balancingGauge_sub_one_le hL hN hδ hsmall h1
  have k2 := norm_framed_balancingGauge_sub_one_le hL hN hδ hsmall h2
  rw [refineSite_eq_cellCentre] at k1 k2
  rw [axialGauge_transform_eq hamb hL]
  set g := patchFrame S V z (cellCentre F.depth (enclosingCell x))
  set g' := patchFrame S V z (cellCentre F.depth (enclosingCell (x + unitStep F.depth i)))
  set k := balancingGauge X Rt (enclosingCell x)
  set k' := balancingGauge X Rt (enclosingCell (x + unitStep F.depth i))
  have hfold : pathHolonomy X (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) π) * X x i *
      (pathHolonomy X (cellCentre F.depth (enclosingCell (x + unitStep F.depth i)))
        (axisPath (cellOffset (x + unitStep F.depth i)) π))⁻¹ =
      blockLoop X π x i := rfl
  rw [hfold]
  set A := blockLoop X π x i
  have hconj := norm_coe_conj_sub_one g⁻¹ (k * A * k'⁻¹ * T⁻¹)
  rw [inv_inv] at hconj
  rw [← hconj]
  have e : g⁻¹ * (k * A * k'⁻¹ * T⁻¹) * g =
      (g⁻¹ * k * g) * (g⁻¹ * A * g') * (g'⁻¹ * k' * g')⁻¹ * (g⁻¹ * T * g')⁻¹ := by
    group
  rw [e]
  have n1 := norm_coe_mul_sub_one_le ((g⁻¹ * k * g) * (g⁻¹ * A * g') * (g'⁻¹ * k' * g')⁻¹) ((g⁻¹ * T * g')⁻¹)
  have n2 := norm_coe_mul_sub_one_le ((g⁻¹ * k * g) * (g⁻¹ * A * g')) ((g'⁻¹ * k' * g')⁻¹)
  have n3 := norm_coe_mul_sub_one_le (g⁻¹ * k * g) (g⁻¹ * A * g')
  rw [norm_coe_inv_sub_one] at n1 n2
  nlinarith
theorem plaquetteDefect_le (hL : Odd F.blockSide) (hN : FrameNearOne S V z X Rt δ)
    (k : F.Site F.depth → UnitQuaternion)
    {p : F.Site F.depth × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S F.depth)
    (h1 : ∀ x ∈ plaquetteCorners p, enclosingCell x ∈ cellBall S z 1) :
    plaquetteDefect (gaugeTransform k X) p ≤ 4 * δ := by
  have c1 : p.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have c2 : p.1 + unitStep F.depth p.2.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have c3 : p.1 + unitStep F.depth p.2.2 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have c4 : p.1 + unitStep F.depth p.2.1 + unitStep F.depth p.2.2 ∈ plaquetteCorners p := by
    simp [plaquetteCorners]
  have hsub : plaquetteCorners p ⊆ sitesOfCells S F.depth := by
    simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp
    exact hp.2.2
  have hbond : ∀ x d, x ∈ plaquetteCorners p → x + unitStep F.depth d ∈ plaquetteCorners p →
      (x, d) ∈ innerBonds S F.depth := fun x d a b => by
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hsub a, hsub b⟩
  have hpv : ∀ (Y : F.GaugeField F.depth) (g : F.Site F.depth → UnitQuaternion),
      plaquetteHolonomy (gaugeTransform g Y) p = g p.1 * plaquetteHolonomy Y p * (g p.1)⁻¹ := by
    intro Y g
    unfold plaquetteHolonomy
    rw [pathHolonomy_gaugeTransform]
    have he : p.1 + LumpContours.BlockLevels.pathDisplacement F.depth
        [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] = p.1 := by
      simp only [LumpContours.BlockLevels.pathDisplacement, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, stepDisplacement, if_true, Bool.false_eq_true, if_false]
      abel
    rw [he]
  unfold plaquetteDefect
  rw [hpv, norm_coe_conj_sub_one]
  set f := patchFrame S V z with hf
  have hv := hpv X (fun w => (f w)⁻¹)
  have hn := norm_coe_conj_sub_one (f p.1)⁻¹ (plaquetteHolonomy X p)
  rw [inv_inv] at hn
  have hv' : ((f p.1)⁻¹ * plaquetteHolonomy X p * (f p.1) : UnitQuaternion) =
      plaquetteHolonomy (gaugeTransform (fun w => (f w)⁻¹) X) p := by
    rw [hv]
    simp
  rw [hv'] at hn
  rw [← hn]
  have hclosed : ‖((plaquetteHolonomy (gaugeTransform (fun w => (f w)⁻¹) X) p : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      ((4 : ℕ) : ℝ) * δ := by
    have hδ : 0 ≤ δ := (norm_nonneg _).trans (hN.field p.1 p.2.1 (hbond _ _ c1 c2) (h1 _ c1))
    have := norm_pathHolonomy_sub_one_le (plaquetteCorners p) (gaugeTransform (fun w => (f w)⁻¹) X) δ hδ
      (fun x i a b => by
        rw [gaugeTransform_inv_apply]
        exact hN.field x i (hbond x i a b) (h1 x a))
      [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] p.1 (by
      simp only [LumpContours.BlockLevels.PathWithin, stepDisplacement, if_true, Bool.false_eq_true, if_false]
      have e1 : p.1 + unitStep F.depth p.2.1 + unitStep F.depth p.2.2 + -unitStep F.depth p.2.1 =
          p.1 + unitStep F.depth p.2.2 := by abel
      have e2 : p.1 + unitStep F.depth p.2.2 + -unitStep F.depth p.2.2 = p.1 := by abel
      rw [e1, e2]
      exact ⟨c1, c2, c2, c4, c4, c3, c3, c1, trivial⟩)
    unfold plaquetteHolonomy
    simpa using this
  simpa using hclosed
end Near
section Patch
variable {S : Finset F.Cell} {z y : F.Cell}
theorem exists_patchSite_eq (hL : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (hy : y ∈ cellBall S z 10)
    {x : F.Site 0} (hx : x ∈ LumpContours.sitesBelow 0 y) :
    ∃ a ∈ GaugeMap.patchDomain S z, GaugeMap.patchSite S z a = x := by
  classical
  set N := GaugeMap.cellSideLength F with hN
  have hN0 : 0 < N := cellSideLength_pos hL.pos
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hL
  rw [LumpContours.BlockLevels.sitesBelow_cell_eq] at hx
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
  have hcs : ((F.blockSide ^ (F.top - 0) : ℕ) : ℤ) = N := by simp [hN, GaugeMap.cellSideLength]
  have hb : ∀ i, |h i| ≤ (N - 1) / 2 := fun i => by
    have := LumpContours.BlockLevels.mem_centredCube_iff.1 hh i
    rwa [hcs] at this
  set o := cellDisplacement z y with ho
  have hy' : y = z + siteOfCoords F.top o := @YangMills.Construction.PatchPoints.eq_add_siteOfCoords_cellDisplacement F z y
  have hd : ∀ i, |o i| ≤ 10 := fun i => by
    have h1 : cellSupDist y z ≤ 10 := by
      rw [BlockLines.cellSupDist_comm]
      exact (Finset.mem_filter.1 hy).2
    have h2 : ((y i - z i).valMinAbs).natAbs ≤ cellSupDist y z :=
      Finset.le_sup (f := fun i => ((y i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h3 : |o i| = (((y i - z i).valMinAbs).natAbs : ℤ) := by
      simp only [ho, cellDisplacement, Pi.sub_apply]
      rw [Int.natCast_natAbs]
    rw [h3]
    omega
  refine ⟨fun i => closedOrthant S z i * (N * o i + h i) + (N - 1) / 2, ?_, ?_⟩
  · refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, ?_⟩
    · have b1 := abs_le.1 (hb i)
      have b2 := abs_le.1 (hd i)
      have hNo1 : N * o i ≤ 10 * N := by nlinarith
      have hNo2 : -(10 * N) ≤ N * o i := by nlinarith
      rw [Finset.mem_Icc]
      rcases he i with h1 | h1 <;> rw [h1] <;> constructor <;> omega
    · refine ⟨fun i => closedOrthant S z i * cellDisplacement z y i * N, ?_, fun i => ?_⟩
      · exact Finset.mem_image.2 ⟨y, hy, rfl⟩
      · have b1 := abs_le.1 (hb i)
        have e : closedOrthant S z i * (N * o i + h i) + (N - 1) / 2 -
            closedOrthant S z i * cellDisplacement z y i * N =
            closedOrthant S z i * h i + (N - 1) / 2 := by
          rw [← ho]
          ring
        have e3 : 0 ≤ closedOrthant S z i * h i + (N - 1) / 2 := by
          rcases he i with h1 | h1 <;> rw [h1] <;> omega
        show closedOrthant S z i * cellDisplacement z y i * N ≤ closedOrthant S z i * (N * o i + h i) + (N - 1) / 2
        linarith
  · unfold GaugeMap.patchSite
    rw [hy']
    have e1 : cellCentre 0 (z + siteOfCoords F.top o) =
        cellCentre 0 z + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ (F.top - 0) * o i) :=
      cellCentre_add 0 (Nat.zero_le _) z o
    rw [e1, add_assoc, ← siteOfCoords_add]
    congr 2
    funext i
    have hs := closedOrthant_mul_self he i
    have e2 : (F.blockSide : ℤ) ^ (F.top - 0) = N := by simp [hN, GaugeMap.cellSideLength]
    simp only [Pi.add_apply, e2]
    rw [← hN, add_sub_cancel_right, ← mul_assoc, hs, one_mul]
end Patch
theorem norm_conj_sub_one_le_add (X R g g' : UnitQuaternion) :
    ‖((g⁻¹ * X * g' : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      ‖((X * R⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ + ‖((g⁻¹ * R * g' : UnitQuaternion) : ℍ[ℝ]) - 1‖ := by
  have e : g⁻¹ * X * g' = (g⁻¹ * (X * R⁻¹) * g) * (g⁻¹ * R * g') := by group
  rw [e]
  refine (norm_coe_mul_sub_one_le _ _).trans ?_
  have := norm_coe_conj_sub_one g⁻¹ (X * R⁻¹)
  rw [inv_inv] at this
  rw [this]
theorem le_of_sum_pow_four_le {ι : Type} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (B : ℝ) (hB : 0 ≤ B)
    (h : ∑ i ∈ s, f i ^ 4 ≤ B ^ 4) {i : ι} (hi : i ∈ s) : f i ≤ B := by
  have h1 : f i ^ 4 ≤ ∑ i ∈ s, f i ^ 4 :=
    Finset.single_le_sum (f := fun i => f i ^ 4) (fun _ _ => by positivity) hi
  exact (pow_le_pow_iff_left₀ (hf i) hB (by norm_num)).1 (h1.trans h)
theorem levelScale_le_one (hL : 1 ≤ F.blockSide) (j : ℕ) : levelScale F j ≤ 1 := by
  unfold levelScale
  refine pow_le_one₀ (by positivity) ?_
  rw [div_le_one (by exact_mod_cast hL)]
  exact_mod_cast hL
theorem cellSupDist_triangle (x y w : F.Cell) : cellSupDist x w ≤ cellSupDist x y + cellSupDist y w := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem cellSupDist_enclosingCell_step_le (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    {x : F.Site F.depth} (d : Fin 4) :
    cellSupDist (enclosingCell x) (enclosingCell (x + unitStep F.depth d)) ≤ 1 := by
  have hb := LumpContours.BlockLevels.enclosingCell_add_unitStep_mem_cellBall (Nat.le_succ _) hL.pos x d
  obtain ⟨h, hh, e⟩ := Finset.mem_image.1 hb
  rw [← e, BlockLines.cellSupDist_comm]
  exact cellSupDist_add_le hamb _ (a := h) (r := 1) (by norm_num) (fun i => by
    have := LumpContours.BlockLevels.mem_centredCube_iff.1 hh i
    simpa using this)
theorem crossing_bound_arith (L C3 K r β δ E : ℝ) (hL : 0 ≤ L) (hC3 : 0 ≤ C3) (hr : 0 ≤ r) (hβ : 0 ≤ β)
    (hδ : δ ≤ K * (r + β)) (hE : E ≤ (36 * L + 1) * δ + C3 * r) :
    2 * E ≤ 2 * ((36 * L + 1) * K + C3) * (r + β) := by
  have h1 := mul_le_mul_of_nonneg_left hδ (by positivity : (0 : ℝ) ≤ 36 * L + 1)
  have h2 : C3 * r ≤ C3 * (r + β) := mul_le_mul_of_nonneg_left (by linarith) hC3
  have e : 2 * ((36 * L + 1) * K + C3) * (r + β) = 2 * ((36 * L + 1) * (K * (r + β)) + C3 * (r + β)) := by ring
  rw [e]
  linarith
theorem chord_bound_arith (L C3 K r β δ E : ℝ) (hL : 0 ≤ L) (hC3 : 0 ≤ C3) (hr : 0 ≤ r) (hβ : 0 ≤ β)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ K * (r + β)) (hE : E ≤ (4 * L + 1) * δ) :
    2 * E ≤ 2 * ((36 * L + 1) * K + C3) * (r + β) := by
  refine crossing_bound_arith L C3 K r β δ E hL hC3 hr hβ hδ ?_
  have h1 : (4 * L + 1) * δ ≤ (36 * L + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ0
  have h2 : 0 ≤ C3 * r := by positivity
  linarith
theorem defect_bound_arith (L C3 K r β δ E : ℝ) (hL : 1 ≤ L) (hC3 : 0 ≤ C3) (hr : 0 ≤ r) (hβ : 0 ≤ β)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ K * (r + β)) (hE : E ≤ 4 * δ) :
    E ≤ 2 * ((36 * L + 1) * K + C3) * (r + β) := by
  have h := crossing_bound_arith L C3 K r β δ (2 * δ) (by linarith) hC3 hr hβ hδ (by
    have h2 : 0 ≤ C3 * r := by positivity
    have h3 : 2 * δ ≤ (36 * L + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ0
    linarith)
  linarith
theorem smallChartBound (hB : referenceBoundsStatement) (hLoc : patchPairingLocalFormStatement)
    (hTr : patchTransportStatement) (hG : levelGapNearCellStatement) :
    CellTerms.smallChartBoundStatement := by
  obtain ⟨C0, c0, L1, hC0, hc0, hB⟩ := hB
  obtain ⟨Bl, Cl, cl, -, -, hcl, hLoc⟩ := hLoc
  obtain ⟨C3, hC3, hTr⟩ := hTr
  obtain ⟨C2, hC2, L2, hG⟩ := hG
  refine ⟨max (max L1 L2) 3, ?_⟩
  intro L hLo hLL del hdel
  have hL1 : L1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hLL)
  have hL2 : L2 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hLL)
  have hL3 : 3 ≤ L := (le_max_right _ _).trans hLL
  obtain ⟨c2, hc2, hG2⟩ := hG L hLo hL2
  have hexp : 1 ≤ Real.exp (3 * del) := Real.one_le_exp (by positivity)
  set e3 := Real.exp (3 * del) with he3
  have he30 : 0 < e3 := by linarith
  have hLr : (0 : ℝ) < L := by
    have : (0 : ℕ) < L := by omega
    exact_mod_cast this
  set ε : ℝ := 1 / (8 * L * (C2 + C0)) with hε
  have hε0 : 0 < ε := by positivity
  set cm := min (min (min c0 cl) c2) ε with hcm
  have hcm0 : 0 < cm := lt_min (lt_min (lt_min hc0 hcl) hc2) hε0
  refine ⟨cm / e3, 2 * ((36 * L + 1) * (C2 + C0) + C3), by positivity, by positivity, ?_⟩
  intro F m S hF hamb hm hreg r V hr hrc hcold U hU β hβ
  subst hF
  have hcmle : cm / e3 ≤ cm := div_le_self hcm0.le hexp
  have hrcm : r ≤ cm := hrc.trans hcmle
  have hrc0 : r ≤ c0 := hrcm.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hrcl : r ≤ cl := hrcm.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hrc2 : r ≤ c2 := hrcm.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrε : r ≤ ε := hrcm.trans (min_le_right _ _)
  set R := referenceFieldChain S V with hR
  set X := chartField R U F.depth with hX
  have hes : ∀ (z : F.Cell) (i : Fin 4), closedOrthant S z i = 1 ∨ closedOrthant S z i = -1 := fun z =>
    (closedOrthant_spec hreg (by omega) z).1
  have hcm' : ∀ y ∈ S, CellTerms.unweightedLocalNorm S R U y ≤ cm := by
    intro y hy
    have h1 := LocalNorms.unweightedLocalNorm_le_exp_mul_supWeightedNorm del hdel S R U y hy
    have h2 : e3 * supWeightedNorm S del R U ≤ e3 * (cm / e3) := mul_le_mul_of_nonneg_left hU he30.le
    have h3 : e3 * (cm / e3) = cm := by field_simp
    linarith
  obtain ⟨b1, -⟩ := hB F m S hLo hL1 hamb hm hreg r V hr hrc0 hcold
  set b' := min β cm with hb'
  have hb'0 : 0 ≤ b' := le_min hβ hcm0.le
  have hb'β : b' ≤ β := min_le_left _ _
  have hb'cm : b' ≤ cm := min_le_right _ _
  have hb'c2 : b' ≤ c2 := hb'cm.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hb'ε : b' ≤ ε := hb'cm.trans (min_le_right _ _)
  set δ := C2 * b' + C0 * r with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδε : δ ≤ (C2 + C0) * ε := by
    have h1 := mul_le_mul_of_nonneg_left hb'ε hC2.le
    have h2 := mul_le_mul_of_nonneg_left hrε hC0.le
    rw [add_mul]
    exact add_le_add h1 h2
  have hsmall : 4 * (F.blockSide : ℝ) * δ ≤ 1 / 2 := by
    have e1 : 4 * (F.blockSide : ℝ) * ((C2 + C0) * ε) = 1 / 2 := by
      rw [hε]
      field_simp
      ring
    have := mul_le_mul_of_nonneg_left hδε (by positivity : (0 : ℝ) ≤ 4 * (F.blockSide : ℝ))
    linarith
  have hδrβ : δ ≤ (C2 + C0) * (r + β) := by
    have h1 : C2 * b' ≤ C2 * (r + β) := mul_le_mul_of_nonneg_left (by linarith) hC2.le
    have h2 : C0 * r ≤ C0 * (r + β) := mul_le_mul_of_nonneg_left (by linarith) hC0.le
    rw [add_mul]
    exact add_le_add h1 h2
  have hlev : levelScale F F.depth ≤ 1 := levelScale_le_one (by omega) _
  have near : ∀ z ∈ S, (∀ y ∈ cellBall S z 5, CellTerms.unweightedLocalNorm S R U y ≤ β) →
      FrameNearOne S V z X (R F.depth) δ := by
    intro z hz hbox
    have hRef : ∀ (x : F.Site F.depth) (d : Fin 4), (x, d) ∈ innerBonds S F.depth →
        enclosingCell x ∈ cellBall S z 1 →
        ‖(((patchFrame S V z x)⁻¹ * R F.depth x d * patchFrame S V z (x + unitStep F.depth d) :
          UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ C0 * r := by
      intro x d hbd hcell
      have hends := Finset.mem_filter.1 hbd
      have hmem : ∀ w : F.Site F.depth, w ∈ sitesOfCells S F.depth → enclosingCell w ∈ cellBall S z 10 →
          baseSite w ∈ (GaugeMap.patchDomain S z).image (GaugeMap.patchSite S z) := by
        intro w _ hc
        have hw : baseSite w ∈ LumpContours.sitesBelow 0 (enclosingCell w) := by
          have h1 : baseSite w ∈ LumpContours.sitesBelow 0 w :=
            Finset.mem_image.2 ⟨0, LumpContours.BlockLevels.mem_centredCube_iff.2 fun m => by
            have : (0 : ℤ) ≤ (((F.blockSide ^ (F.depth - 0) : ℕ) : ℤ) - 1) / 2 := by
              obtain ⟨q, hq⟩ := (hLo.pow : Odd (F.blockSide ^ (F.depth - 0)))
              rw [hq]
              push_cast
              omega
            simpa using this, by
              funext k
              simp [baseSite, siteOfCoords]⟩
          exact LumpContours.BlockLevels.sitesBelow_trans (Nat.zero_le _) (Nat.le_succ _) le_rfl hLo
            (enclosingCell w) (LumpContours.BlockLevels.mem_sitesBelow_enclosingCell (Nat.le_succ _) hLo w) h1
        obtain ⟨a, ha, e⟩ := exists_patchSite_eq hLo (hes z) hc hw
        exact Finset.mem_image.2 ⟨a, ha, e⟩
      have hc1 : enclosingCell x ∈ cellBall S z 10 := BlockLines.cellBall_mono S z (by norm_num) hcell
      have hc2 : enclosingCell (x + unitStep F.depth d) ∈ cellBall S z 10 := by
        refine Finset.mem_filter.2
          ⟨LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells (Nat.le_succ _) hLo hends.2, ?_⟩
        have h1 : cellSupDist z (enclosingCell x) ≤ 1 := (Finset.mem_filter.1 hcell).2
        have h2 := cellSupDist_enclosingCell_step_le hamb hLo (x := x) d
        have h3 := cellSupDist_triangle z (enclosingCell x) (enclosingCell (x + unitStep F.depth d))
        omega
      have h1 := b1 F.depth (Nat.lt_succ_self _) z hz (x, d) hbd
        (hmem x (Finset.mem_product.1 hends.1).1 hc1) (hmem _ hends.2 hc2)
      have h2 : unitDeviation (referenceInPatchFrame S V z F.depth x d) ≤ C0 * r := by
        refine h1.trans ?_
        have : C0 * r * levelScale F F.depth ≤ C0 * r * 1 := mul_le_mul_of_nonneg_left hlev (by positivity)
        linarith
      have e : referenceInPatchFrame S V z F.depth x d =
          (patchFrame S V z x)⁻¹ * R F.depth x d * patchFrame S V z (x + unitStep F.depth d) := by
        simp [referenceInPatchFrame, gaugeTransform, patchFrame, hR]
      unfold unitDeviation at h2
      rw [e] at h2
      exact h2
    refine ⟨fun x d hbd hcell => ?_, fun x d hbd hcell => (hRef x d hbd hcell).trans ?_⟩
    rotate_left
    · have hb0 : 0 ≤ C2 * b' := by positivity
      linarith
    have hyS : enclosingCell x ∈ S := (Finset.mem_filter.1 hcell).1
    have hnorm : CellTerms.unweightedLocalNorm S R U (enclosingCell x) ≤ b' :=
      le_min (hbox _ (BlockLines.cellBall_mono S z (by norm_num) hcell)) (hcm' _ hyS)
    have hsum := hG2 F m S rfl hamb hm hreg r V hr hrc2 hcold U (enclosingCell x) b' hyS hb'0 hb'c2 hnorm F.depth
      (Nat.lt_succ_self _)
    have hgap : normSubOne (chartGap R U F.depth x d) ≤ C2 * b' :=
      le_of_sum_pow_four_le _ (fun b : F.Site F.depth × Fin 4 => normSubOne (chartGap R U F.depth b.1 b.2))
        (fun _ => norm_nonneg _) (C2 * b') (by positivity) hsum.2
        (i := (x, d)) (Finset.mem_filter.2 ⟨hbd, Finset.mem_singleton.2 rfl⟩)
    have hsplit := norm_conj_sub_one_le_add (X x d) (R F.depth x d) (patchFrame S V z x)
      (patchFrame S V z (x + unitStep F.depth d))
    have hr1 := hRef x d hbd hcell
    have hg : ‖((X x d * (R F.depth x d)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ C2 * b' := hgap
    linarith
  have hball : ∀ (z y : F.Cell), y ∈ S → y ∈ LumpContours.cellBall z 1 → y ∈ cellBall S z 1 := by
    intro z y hy hb
    obtain ⟨h, hh, e⟩ := Finset.mem_image.1 hb
    refine Finset.mem_filter.2 ⟨hy, ?_⟩
    rw [← e, BlockLines.cellSupDist_comm]
    exact cellSupDist_add_le hamb z (a := h) (r := 1) (by norm_num) (fun i => by
      have := LumpContours.BlockLevels.mem_centredCube_iff.1 hh i
      simpa using this)
  have hself : ∀ z ∈ S, z ∈ cellBall S z 1 := fun z hz =>
    Finset.mem_filter.2 ⟨hz, by rw [BlockLines.cellSupDist_self]; omega⟩
  have hFL : (0 : ℝ) ≤ F.blockSide := by positivity
  have hCr : 0 ≤ C3 * r := by positivity
  refine ⟨fun π b hb hbox => ?_, fun p hp hbox => ?_⟩
  · have hbS := Finset.mem_filter.1 hb
    have hzS : enclosingCell b.1 ∈ S :=
      LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells (Nat.le_succ _) hLo
        (Finset.mem_product.1 hbS.1).1
    have hyS : enclosingCell (b.1 + unitStep F.depth b.2) ∈ S :=
      LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells (Nat.le_succ _) hLo hbS.2
    have hN := near _ hzS hbox
    have h1 := hself _ hzS
    have h2 : enclosingCell (b.1 + unitStep F.depth b.2) ∈ cellBall S (enclosingCell b.1) 1 :=
      hball _ _ hyS (LumpContours.BlockLevels.enclosingCell_add_unitStep_mem_cellBall (Nat.le_succ _) hLo.pos b.1 b.2)
    unfold LumpContours.bondCoordinate
    by_cases hcr : IsCrossingBond b
    · rw [if_pos hcr]
      have hy' : enclosingCell (b.1 + unitStep F.depth b.2) = enclosingCell b.1 + unitStep F.top b.2 := by
        rcases LumpContours.BlockLevels.enclosingCell_add_unitStep (Nat.le_succ _) hLo.pos b.1 b.2 with h | h
        · exact absurd h hcr
        · exact h
      set z := enclosingCell b.1 with hz
      have hfr : ∀ y ∈ S, cellSupDist z y ≤ 1 →
          patchFrame S V z (cellCentre F.depth y) = GaugeMap.cellTransport S V z y := by
        intro y hy hd
        obtain ⟨P0, P1, -, -, -, -, -, hc⟩ := hLoc F m S hLo hamb hm hreg r V hr hrcl hcold z hzS
        have hw : cellCentre 0 y ∈ LumpContours.sitesBelow 0 y := by
          rw [LumpContours.BlockLevels.sitesBelow_cell_eq]
          refine Finset.mem_image.2 ⟨0, LumpContours.BlockLevels.mem_centredCube_iff.2 fun k => ?_,
            by simp [LumpContours.BlockLevels.siteOfCoords_zero]⟩
          have : (0 : ℤ) ≤ (((F.blockSide ^ (F.top - 0) : ℕ) : ℤ) - 1) / 2 := by
            obtain ⟨q, hq⟩ := (hLo.pow : Odd (F.blockSide ^ (F.top - 0)))
            rw [hq]
            push_cast
            omega
          simpa using this
        obtain ⟨a, ha, e⟩ := exists_patchSite_eq hLo (hes z)
          (Finset.mem_filter.2 ⟨hy, by omega⟩ : y ∈ cellBall S z 10) hw
        have hdom : a ∈ patchLocalSites S z := by
          refine ⟨fun i => ?_, ?_⟩
          · have h3 := (Fintype.mem_piFinset.1 (Finset.mem_filter.1 ha).1) i
            rw [Finset.mem_Icc] at h3
            constructor <;> omega
          · rw [e]
            rw [← LumpContours.BlockLevels.cutBelow_eq_sitesOfCells]
            exact Finset.mem_biUnion.2 ⟨y, hy, hw⟩
        have := hc y hy a hdom e
        rw [e] at this
        unfold patchFrame
        rw [baseSite_cellCentre F.depth (Nat.le_succ _) y]
        exact this
      have hT : ‖(((patchFrame S V z (cellCentre F.depth z))⁻¹ * V z b.2 *
          patchFrame S V z (cellCentre F.depth (enclosingCell (b.1 + unitStep F.depth b.2))) : UnitQuaternion) :
            ℍ[ℝ]) - 1‖ ≤ C3 * r := by
        rw [hy', hfr z hzS (by rw [BlockLines.cellSupDist_self]; omega),
          hfr _ (hy' ▸ hyS) (by have := (Finset.mem_filter.1 h2).2; rw [hy'] at this; exact this)]
        exact (hTr F m S hLo hamb hm hreg r V hr.le hcold z hzS).2 b.2 (hy' ▸ hyS)
      have hcb := norm_crossing_sub_one_le hamb hLo hN hδ0 hsmall π (x := b.1) (i := b.2) hb h1 h2 (V z b.2)
        (C3 * r) hT
      refine (GaugeFixing.norm_minimalLog_le _).trans ?_
      exact crossing_bound_arith _ _ _ _ _ _ _ hFL hC3.le hr.le hβ hδrβ hcb
    · rw [if_neg hcr]
      have hc : enclosingCell (b.1 + unitStep F.depth b.2) = enclosingCell b.1 := by
        by_contra h
        exact hcr h
      have hcb := norm_chord_sub_one_le hamb hLo hN hδ0 (chartGauge R U F.top) π (x := b.1) (i := b.2) hb h1 hc
      refine (GaugeFixing.norm_minimalLog_le _).trans ?_
      exact chord_bound_arith _ _ _ _ _ _ _ hFL hC3.le hr.le hβ hδ0 hδrβ hcb
  · have hpS := Finset.mem_filter.1 hp
    have hzS : enclosingCell p.1 ∈ S :=
      LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells (Nat.le_succ _) hLo
        (Finset.mem_product.1 hpS.1).1
    have hN := near _ hzS hbox
    have hcb := plaquetteDefect_le hLo hN (CellTerms.centreGauge (chartGauge R U F.top)) hp (fun x hx => by
      refine hball _ _
        (LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells (Nat.le_succ _) hLo (hpS.2.2 hx)) ?_
      exact LumpContours.BlockLevels.enclosingCell_corner_mem_cellBall (Nat.le_succ _) hLo.pos p hpS.2.1 hx)
    have hFL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hLo.pos
    exact defect_bound_arith _ _ _ _ _ _ _ hFL1 hC3.le hr.le hβ hδ0 hδrβ hcb
end YangMills.Construction.SmallChart
end
