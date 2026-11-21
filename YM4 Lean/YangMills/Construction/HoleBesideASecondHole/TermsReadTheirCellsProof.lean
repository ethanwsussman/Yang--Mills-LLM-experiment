import YangMills.Construction.ColdChainAtEveryLevel.DensityUnderAChangeOfFramingProof
import YangMills.Construction.HoleBesideASecondHole.ChartOfSmallCoordinatesProof
import YangMills.Construction.HoleBesideASecondHole.TermsReadTheirCells
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.CellTerms
open BlockAverages LumpContours LumpContours.BlockLevels
namespace Locality
variable {F : BlockFrame}
theorem unitQuaternion_inv_mul_mul_cancel (g : UnitQuaternion) (x : ℍ[ℝ]) :
    ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * ((g : ℍ[ℝ]) * x) = x := by apply _root_.YangMills.Construction.GaugedCriticality.coe_inv_mul_coe_mul <;> assumption
theorem unitQuaternion_mul_inv_mul_cancel (g : UnitQuaternion) (x : ℍ[ℝ]) :
    (g : ℍ[ℝ]) * (((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * x) = x := by
  rw [← mul_assoc, unitQuaternion_mul_inv, one_mul]
theorem polarUnit_mul_mul (g h : UnitQuaternion) {q : ℍ[ℝ]} (hq : q ≠ 0) :
    polarUnit ((g : ℍ[ℝ]) * q * (h : ℍ[ℝ])) = g * polarUnit q * h := by apply _root_.YangMills.Construction.BlockAverages.GaugeChangeDensity.polarUnit_mul_mul <;> assumption
theorem polarUnit_conj (g : UnitQuaternion) (q : ℍ[ℝ]) :
    polarUnit ((g : ℍ[ℝ]) * q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) = g * polarUnit q * g⁻¹ := by apply _root_.YangMills.Construction.SmallChart.polarUnit_conj <;> assumption
theorem re_conj (g : UnitQuaternion) (q : ℍ[ℝ]) :
    ((g : ℍ[ℝ]) * q * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = q.re := by apply _root_.YangMills.Construction.GaugedCriticality.re_conj_unit <;> assumption
theorem norm_mul_mul_unitQuaternion (g h : UnitQuaternion) (q : ℍ[ℝ]) :
    ‖(g : ℍ[ℝ]) * q * (h : ℍ[ℝ])‖ = ‖q‖ := by
  rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
theorem expUnit_conj (g : UnitQuaternion) (w w' : imaginaryQuaternions)
    (h : (w' : ℍ[ℝ]) = adjointAction g w) :
    expUnit w' = g * expUnit w * g⁻¹ := by
  apply Subtype.ext
  simp only [expUnit, Submonoid.coe_mul]
  have hre : (w' : ℍ[ℝ]).re = 0 := w'.2
  have hn : ‖(w' : ℍ[ℝ])‖ = ‖(w : ℍ[ℝ])‖ := by
    rw [h]
    exact norm_mul_mul_unitQuaternion g g⁻¹ _
  rw [Quaternion.exp_of_re_eq_zero _ hre, Quaternion.exp_of_re_eq_zero _ w.2, hn, h]
  unfold adjointAction
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, ← Quaternion.coe_commutes]
  simp only [mul_assoc, unitQuaternion_mul_inv, mul_one]
theorem pathHolonomy_gaugeTransform {j : ℕ} (Z : Finset (F.Site j)) (X X' : F.GaugeField j)
    (g : F.Site j → UnitQuaternion)
    (hX : ∀ x i, x ∈ Z → x + unitStep j i ∈ Z → X' x i = gaugeTransform g X x i) (l : List PathStep) :
    ∀ x, PathWithin Z x l →
      pathHolonomy X' x l = g x * pathHolonomy X x l * (g (x + pathDisplacement j l))⁻¹ := by
  induction l with
  | nil =>
    intro x _
    simp [pathHolonomy, pathDisplacement]
  | cons st r ih =>
    intro x h
    have hp : x + pathDisplacement j (st :: r) = x + stepDisplacement j st + pathDisplacement j r := by
      simp [pathDisplacement, add_assoc]
    have hs : linkValue X' x st = g x * linkValue X x st * (g (x + stepDisplacement j st))⁻¹ := by
      obtain ⟨d, b⟩ := st
      cases b
      · simp only [linkValue, Bool.false_eq_true, if_false, stepDisplacement]
        have h1 := h.1
        have h2 := h.2.1
        simp only [stepDisplacement, Bool.false_eq_true, if_false] at h2
        have e1 : x + -unitStep j d = x - unitStep j d := by abel
        rw [e1] at h2 ⊢
        have e2 : x - unitStep j d + unitStep j d = x := by abel
        rw [hX (x - unitStep j d) d h2 (by rw [e2]; exact h1)]
        simp only [gaugeTransform, e2, mul_inv_rev, inv_inv, mul_assoc]
      · simp only [linkValue, if_true, stepDisplacement]
        have h2 := h.2.1
        simp only [stepDisplacement, if_true] at h2
        rw [hX x d h.1 h2]
        rfl
    simp only [pathHolonomy]
    rw [ih _ h.2.2, hs, hp]
    group
theorem refineSite_add_pathDisplacement_bondContour (j : ℕ) (hj : j < F.top)
    (c : F.Site (j + 1) × Fin 4) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) :
    refineSite c.1 + pathDisplacement j (bondContour F.blockSide h π c.2) =
      refineSite (c.1 + unitStep (j + 1) c.2) := by
  unfold bondContour
  rw [pathDisplacement_append, pathDisplacement_append, pathDisplacement_reversePath,
    pathDisplacement_replicate]
  have := refineSite_add_step j hj c.1 (c.2, true)
  simp only [stepDisplacement, if_true] at this ⊢
  rw [this]
  abel
theorem contourAverage_gaugeTransform {j : ℕ} (hj : j < F.top) (hL : Odd F.blockSide)
    (X X' : F.GaugeField j) (g : F.Site j → UnitQuaternion) (c : F.Site (j + 1) × Fin 4)
    (hX : ∀ x i, x ∈ sitesBelow j c.1 ∪ sitesBelow j (c.1 + unitStep (j + 1) c.2) →
      x + unitStep j i ∈ sitesBelow j c.1 ∪ sitesBelow j (c.1 + unitStep (j + 1) c.2) →
        X' x i = gaugeTransform g X x i) :
    contourAverage X' c = (g (refineSite c.1) : ℍ[ℝ]) * contourAverage X c *
      (((g (refineSite (c.1 + unitStep (j + 1) c.2)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  unfold contourAverage
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [pathHolonomy_gaugeTransform _ X X' g hX _ _
      (bondContour_within_blocks j hj hL c h (withinBlock_of_mem_centredCube hh) π),
    refineSite_add_pathDisplacement_bondContour j hj c h π]
  simp only [Submonoid.coe_mul]
theorem relativePathAverage_gaugeTransform {j : ℕ} (hL : Odd F.blockSide) (X X' R R' : F.GaugeField j)
    (g : F.Site j → UnitQuaternion) (y : F.Site (j + 1))
    (hX : ∀ x i, x ∈ sitesBelow j y → x + unitStep j i ∈ sitesBelow j y → X' x i = gaugeTransform g X x i)
    (hR : ∀ x i, x ∈ sitesBelow j y → x + unitStep j i ∈ sitesBelow j y → R' x i = gaugeTransform g R x i) :
    relativePathAverage X' R' y = (g (refineSite y) : ℍ[ℝ]) * relativePathAverage X R y *
      (((g (refineSite y))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  unfold relativePathAverage
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun π _ => ?_
  have hp := axisPath_within_block j hL y h (withinBlock_of_mem_centredCube hh) π
  rw [pathHolonomy_gaugeTransform _ X X' g hX _ _ hp, pathHolonomy_gaugeTransform _ R R' g hR _ _ hp]
  have e : g (refineSite y) * pathHolonomy X (refineSite y) (axisPath h π) *
      (g (refineSite y + pathDisplacement j (axisPath h π)))⁻¹ *
      (g (refineSite y) * pathHolonomy R (refineSite y) (axisPath h π) *
        (g (refineSite y + pathDisplacement j (axisPath h π)))⁻¹)⁻¹ =
      g (refineSite y) * (pathHolonomy X (refineSite y) (axisPath h π) *
        (pathHolonomy R (refineSite y) (axisPath h π))⁻¹) * (g (refineSite y))⁻¹ := by group
  rw [e]
  simp only [Submonoid.coe_mul]
theorem balancingGauge_gaugeTransform {j : ℕ} (hL : Odd F.blockSide) (X X' R R' : F.GaugeField j)
    (g : F.Site j → UnitQuaternion) (y : F.Site (j + 1))
    (hX : ∀ x i, x ∈ sitesBelow j y → x + unitStep j i ∈ sitesBelow j y → X' x i = gaugeTransform g X x i)
    (hR : ∀ x i, x ∈ sitesBelow j y → x + unitStep j i ∈ sitesBelow j y → R' x i = gaugeTransform g R x i) :
    balancingGauge X' R' y = g (refineSite y) * balancingGauge X R y * (g (refineSite y))⁻¹ := by
  unfold balancingGauge
  rw [relativePathAverage_gaugeTransform hL X X' R R' g y hX hR, polarUnit_conj]
  group
theorem fitDefect_conj (g g' : UnitQuaternion) (q : ℍ[ℝ]) (x : UnitQuaternion) :
    ‖(g : ℍ[ℝ]) * q * ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ -
        ((g : ℍ[ℝ]) * q * ((g'⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
          (((g * x * g'⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re =
      ‖q‖ - (q * ((x⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by apply _root_.YangMills.Construction.GaugeMotions.norm_sub_re_conj <;> assumption
section Levels
variable {C : Finset F.Cell} {γ : F.Site 0 → UnitQuaternion} {R R' : F.FieldChain}
  {U U' : ChainChart F}
theorem bondWithin_of_mem_sitesBelow_union {j : ℕ} (hj : j < F.top) (hL : Odd F.blockSide)
    (c : F.Site (j + 1) × Fin 4) (hc : BondWithin C c) {x : F.Site j} {i : Fin 4}
    (h1 : x ∈ sitesBelow j c.1 ∪ sitesBelow j (c.1 + unitStep (j + 1) c.2))
    (h2 : x + unitStep j i ∈ sitesBelow j c.1 ∪ sitesBelow j (c.1 + unitStep (j + 1) c.2)) :
    BondWithin C (x, i) := by
  have key : ∀ w : F.Site j, w ∈ sitesBelow j c.1 ∪ sitesBelow j (c.1 + unitStep (j + 1) c.2) →
      enclosingCell w ∈ C := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · rw [enclosingCell_of_mem_sitesBelow (Nat.le_succ j) hj hL h]
      exact hc.1
    · rw [enclosingCell_of_mem_sitesBelow (Nat.le_succ j) hj hL h]
      exact hc.2
  exact ⟨key x h1, key _ h2⟩
theorem bondWithin_of_mem_sitesBelow {j : ℕ} (hj : j < F.top) (hL : Odd F.blockSide) (y : F.Site (j + 1))
    (hy : enclosingCell y ∈ C) {x : F.Site j} {i : Fin 4} (h1 : x ∈ sitesBelow j y)
    (h2 : x + unitStep j i ∈ sitesBelow j y) :
    BondWithin C (x, i) := by
  constructor
  · show enclosingCell x ∈ C
    rw [enclosingCell_of_mem_sitesBelow (Nat.le_succ j) hj hL h1]
    exact hy
  · show enclosingCell (x + unitStep j i) ∈ C
    rw [enclosingCell_of_mem_sitesBelow (Nat.le_succ j) hj hL h2]
    exact hy
theorem balancingGauge_rotated (hL : Odd F.blockSide) (hT : IsGaugeRotatedOn C γ R R' U U') {j : ℕ}
    (hj : j < F.top)
    (hf : ∀ b : F.Site j × Fin 4, BondWithin C b →
      chartField R' U' j b.1 b.2 = gaugeTransform (fun x => γ (baseSite x)) (chartField R U j) b.1 b.2)
    (y : F.Site (j + 1)) (hy : enclosingCell y ∈ C) :
    balancingGauge (chartField R' U' j) (R' j) y =
      γ (baseSite y) * balancingGauge (chartField R U j) (R j) y * (γ (baseSite y))⁻¹ := by
  rw [balancingGauge_gaugeTransform hL _ _ _ _ (fun x => γ (baseSite x)) y
    (fun x i h1 h2 => hf (x, i) (bondWithin_of_mem_sitesBelow hj hL y hy h1 h2))
    (fun x i h1 h2 => hT.reference_eq j hj (x, i) (bondWithin_of_mem_sitesBelow hj hL y hy h1 h2))]
  simp only [baseSite_refineSite j hj]
theorem chartField_rotated (hL : Odd F.blockSide) (hT : IsGaugeRotatedOn C γ R R' U U')
    (hM : HasNonzeroAveragesOn C R U) :
    ∀ j, j < F.top → ∀ b : F.Site j × Fin 4, BondWithin C b →
      chartField R' U' j b.1 b.2 = gaugeTransform (fun x => γ (baseSite x)) (chartField R U j) b.1 b.2 := by
  intro j
  induction j with
  | zero =>
    intro _ b hb
    have h1 := hT.reference_eq 0 (Nat.succ_pos _) b hb
    have h2 := expUnit_conj (γ (baseSite b.1)) _ _ (hT.fine_eq b hb)
    show expUnit (U'.fine b.1 b.2) * R' 0 b.1 b.2 = _
    rw [h1, h2]
    show _ = γ (baseSite b.1) * (expUnit (U.fine b.1 b.2) * R 0 b.1 b.2) *
      (γ (baseSite (b.1 + unitStep 0 b.2)))⁻¹
    simp only [gaugeTransform]
    group
  | succ j ih =>
    intro hj c hc
    have hj' : j < F.top := by omega
    have hf := ih hj'
    set g1 : F.Site (j + 1) → UnitQuaternion := fun x => γ (baseSite x) with hg1
    set g0 : F.Site j → UnitQuaternion := fun x => γ (baseSite x) with hg0
    have hd : ∀ y : F.Site (j + 1), g0 (refineSite y) = g1 y := fun y => by
      simp only [hg0, hg1, baseSite_refineSite j hj']
    have hk1 : balancingGauge (chartField R' U' j) (R' j) c.1 =
        g1 c.1 * balancingGauge (chartField R U j) (R j) c.1 * (g1 c.1)⁻¹ :=
      balancingGauge_rotated hL hT hj' hf c.1 hc.1
    have hk2 : balancingGauge (chartField R' U' j) (R' j) (c.1 + unitStep (j + 1) c.2) =
        g1 (c.1 + unitStep (j + 1) c.2) *
          balancingGauge (chartField R U j) (R j) (c.1 + unitStep (j + 1) c.2) *
          (g1 (c.1 + unitStep (j + 1) c.2))⁻¹ :=
      balancingGauge_rotated hL hT hj' hf (c.1 + unitStep (j + 1) c.2) hc.2
    have hmean := contourAverage_gaugeTransform hj' hL (chartField R U j) (chartField R' U' j) g0 c
      (fun x i h1 h2 => hf (x, i) (bondWithin_of_mem_sitesBelow_union hj' hL c hc h1 h2))
    have hmeanR := contourAverage_gaugeTransform hj' hL (R j) (R' j) g0 c
      (fun x i h1 h2 => hT.reference_eq j hj' (x, i) (bondWithin_of_mem_sitesBelow_union hj' hL c hc h1 h2))
    rw [hd, hd] at hmean hmeanR
    have hne := hM j hj c hc
    have hframed : gaugedContourAverage (chartField R' U' j)
        (balancingGauge (chartField R' U' j) (R' j)) c =
        (g1 c.1 : ℍ[ℝ]) * gaugedContourAverage (chartField R U j)
          (balancingGauge (chartField R U j) (R j)) c *
          (((g1 (c.1 + unitStep (j + 1) c.2))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
      unfold gaugedContourAverage
      rw [hmean, hk1, hk2]
      simp only [mul_inv_rev, inv_inv, Submonoid.coe_mul, mul_assoc, unitQuaternion_inv_mul_mul_cancel,
        unitQuaternion_mul_inv_mul_cancel]
    have hmis : referenceDefect R' j c = g1 c.1 * referenceDefect R j c * (g1 c.1)⁻¹ := by
      have hR1 : R' (j + 1) c.1 c.2 = g1 c.1 * R (j + 1) c.1 c.2 * (g1 (c.1 + unitStep (j + 1) c.2))⁻¹ :=
        hT.reference_eq (j + 1) hj c hc
      unfold referenceDefect
      rw [hmeanR, polarUnit_mul_mul _ _ hne.1, hR1]
      group
    have hmu := expUnit_conj (g1 c.1) _ _ (hT.coarse_eq j hj c hc)
    show expUnit (U'.coarse j c.1 c.2) * referenceDefect R' j (c.1, c.2) *
        polarUnit (gaugedContourAverage (chartField R' U' j)
          (balancingGauge (chartField R' U' j) (R' j)) (c.1, c.2)) = _
    have hc' : ((c.1, c.2) : F.Site (j + 1) × Fin 4) = c := rfl
    rw [hc', hmis, hframed, polarUnit_mul_mul _ _ hne.2, hmu]
    show _ = g1 c.1 * (expUnit (U.coarse j c.1 c.2) * referenceDefect R j (c.1, c.2) *
        polarUnit (gaugedContourAverage (chartField R U j)
          (balancingGauge (chartField R U j) (R j)) (c.1, c.2))) *
        (g1 (c.1 + unitStep (j + 1) c.2))⁻¹
    rw [hc']
    group
theorem gaugedContourAverage_rotated (hL : Odd F.blockSide) (hT : IsGaugeRotatedOn C γ R R' U U') {j : ℕ}
    (hj : j < F.top)
    (hf : ∀ b : F.Site j × Fin 4, BondWithin C b →
      chartField R' U' j b.1 b.2 = gaugeTransform (fun x => γ (baseSite x)) (chartField R U j) b.1 b.2)
    (c : F.Site (j + 1) × Fin 4) (hc : BondWithin C c) :
    gaugedContourAverage (chartField R' U' j) (balancingGauge (chartField R' U' j) (R' j)) c =
      (γ (baseSite c.1) : ℍ[ℝ]) * gaugedContourAverage (chartField R U j)
        (balancingGauge (chartField R U j) (R j)) c *
        (((γ (baseSite (c.1 + unitStep (j + 1) c.2)))⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
  have hk1 := balancingGauge_rotated hL hT hj hf c.1 hc.1
  have hk2 := balancingGauge_rotated hL hT hj hf (c.1 + unitStep (j + 1) c.2) hc.2
  have hmean := contourAverage_gaugeTransform hj hL (chartField R U j) (chartField R' U' j)
    (fun x => γ (baseSite x)) c
    (fun x i h1 h2 => hf (x, i) (bondWithin_of_mem_sitesBelow_union hj hL c hc h1 h2))
  simp only [baseSite_refineSite j hj] at hmean
  unfold gaugedContourAverage
  rw [hmean, hk1, hk2]
  simp only [mul_inv_rev, inv_inv, Submonoid.coe_mul, mul_assoc, unitQuaternion_inv_mul_mul_cancel,
    unitQuaternion_mul_inv_mul_cancel]
theorem chartChain_of_lt (V : F.GaugeField F.top) {j : ℕ} (hj : j < F.top) :
    chartChain R U V j = chartField R U j := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.chartChain_of_lt <;> assumption
theorem chartChain_top (V : F.GaugeField F.top) : chartChain R U V F.top = V := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.chartChain_top <;> assumption
theorem baseSite_eq_cellCentre (y : F.Cell) : baseSite y = cellCentre 0 y := by apply _root_.YangMills.Construction.ReferenceBounds.baseSite_cell <;> assumption
theorem plaquetteEnergy_rotated (hL : Odd F.blockSide) (hT : IsGaugeRotatedOn C γ R R' U U')
    (hM : HasNonzeroAveragesOn C R U) (p : F.Site 0 × Fin 4 × Fin 4)
    (hc : ∀ x ∈ plaquetteCorners p, enclosingCell x ∈ C) :
    plaquetteEnergy (chartField R' U' 0) p = plaquetteEnergy (chartField R U 0) p := by
  have hf := chartField_rotated hL hT hM 0 (Nat.succ_pos _)
  have c1 : p.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have c2 : p.1 + unitStep 0 p.2.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have c3 : p.1 + unitStep 0 p.2.2 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have c4 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have hpath : PathWithin (plaquetteCorners p) p.1
      [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] := by
    simp only [PathWithin, stepDisplacement, if_true, Bool.false_eq_true, if_false]
    have e1 : p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 + -unitStep 0 p.2.1 = p.1 + unitStep 0 p.2.2 := by
      abel
    have e2 : p.1 + unitStep 0 p.2.2 + -unitStep 0 p.2.2 = p.1 := by abel
    rw [e1, e2]
    exact ⟨c1, c2, c2, c4, c4, c3, c3, c1, trivial⟩
  have hv := pathHolonomy_gaugeTransform (plaquetteCorners p) (chartField R U 0) (chartField R' U' 0)
    (fun x => γ (baseSite x)) (fun x i h1 h2 => hf (x, i) ⟨hc x h1, hc _ h2⟩) _ p.1 hpath
  have he : p.1 + pathDisplacement 0 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] =
      p.1 := by
    simp only [pathDisplacement, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      stepDisplacement, if_true, Bool.false_eq_true, if_false]
    abel
  rw [he] at hv
  unfold plaquetteEnergy plaquetteHolonomy
  rw [hv]
  congr 1
  simp only [Submonoid.coe_mul]
  exact re_conj _ _
end Levels
section Chart
variable {C : Finset F.Cell}
theorem cellOffset_spec (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide) (x : F.Site F.depth) :
    WithinBlock F.blockSide (cellOffset x) ∧
      cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth (cellOffset x) = x := by apply _root_.YangMills.Construction.SmallChart.cellOffset_spec <;> assumption
theorem axialGauge_gaugeTransform (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    (π : Equiv.Perm (Fin 4)) (W W' : F.GaugeField F.depth) (σ : F.Site F.depth → UnitQuaternion)
    (hσ : ∀ y ∈ C, σ (cellCentre F.depth y) = 1)
    (hW : ∀ b : F.Site F.depth × Fin 4, BondWithin C b → W' b.1 b.2 = gaugeTransform σ W b.1 b.2)
    (x : F.Site F.depth) (hx : enclosingCell x ∈ C) :
    axialGauge π W' x = axialGauge π W x * (σ x)⁻¹ := by
  obtain ⟨hb, he⟩ := cellOffset_spec hamb hL x
  have hd : refineSite (enclosingCell x) = cellCentre F.depth (enclosingCell x) := by
    funext k
    have ht : F.top - F.depth = 1 := by simp [BlockFrame.top]
    simp [refineSite, cellCentre, siteOfCoords, ht]
  have hp := axisPath_within_block F.depth hL (enclosingCell x) (cellOffset x) hb π
  rw [hd] at hp
  have hv := pathHolonomy_gaugeTransform _ W W' σ (fun w i h1 h2 => hW (w, i)
    (bondWithin_of_mem_sitesBelow (Nat.lt_succ_self _) hL (enclosingCell x)
      (by rwa [enclosingCell_cell hL.pos]) h1 h2)) _ _ hp
  unfold axialGauge
  rw [hv, pathDisplacement_axisPath, he, hσ _ hx, one_mul]
theorem gaugeTransform_axialGauge_invariant (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    (π : Equiv.Perm (Fin 4)) (W W' : F.GaugeField F.depth) (σ : F.Site F.depth → UnitQuaternion)
    (hσ : ∀ y ∈ C, σ (cellCentre F.depth y) = 1)
    (hW : ∀ b : F.Site F.depth × Fin 4, BondWithin C b → W' b.1 b.2 = gaugeTransform σ W b.1 b.2)
    (b : F.Site F.depth × Fin 4) (hb : BondWithin C b) :
    gaugeTransform (axialGauge π W') W' b.1 b.2 = gaugeTransform (axialGauge π W) W b.1 b.2 := by
  simp only [gaugeTransform]
  rw [axialGauge_gaugeTransform hamb hL π W W' σ hσ hW _ hb.1,
    axialGauge_gaugeTransform hamb hL π W W' σ hσ hW _ hb.2, hW b hb]
  simp only [gaugeTransform]
  group
end Chart
theorem cellTermsLocality : cellTermsLocalityStatement := by
  intro F C γ R R' U U' hL hamb hT hM
  have hf := chartField_rotated hL hT hM
  have hk : ∀ j, j < F.top → ∀ y : F.Site (j + 1), enclosingCell y ∈ C →
      chartGauge R' U' (j + 1) y = γ (baseSite y) * chartGauge R U (j + 1) y * (γ (baseSite y))⁻¹ :=
    fun j hj y hy => balancingGauge_rotated hL hT hj (hf j hj) y hy
  refine ⟨hf, hk, fun hγ => ⟨?_, ?_⟩⟩
  · intro a S S' V V' z hball hV
    have hzS : ∀ y ∈ cellBall z 1, y ∈ S ↔ y ∈ S' := fun y hy => (hball y hy).1
    have hP : plaquettesOver S {z} 0 = plaquettesOver S' {z} 0 := by
      ext p
      simp only [plaquettesOver, innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        and_true, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, h4⟩
        have key : ∀ x ∈ plaquetteCorners p, x ∈ sitesOfCells S' 0 := fun x hx => by
          have hb := enclosingCell_corner_mem_cellBall (Nat.zero_le _) hL.pos p h2 hx
          rw [h4] at hb
          exact (mem_sitesOfCells_iff (Nat.zero_le _) hL).2
            ((hzS _ hb).1 ((mem_sitesOfCells_iff (Nat.zero_le _) hL).1 (h3 hx)))
        exact ⟨⟨key _ (by simp [plaquetteCorners]), h2, fun x hx => key x hx⟩, h4⟩
      · rintro ⟨⟨h1, h2, h3⟩, h4⟩
        have key : ∀ x ∈ plaquetteCorners p, x ∈ sitesOfCells S 0 := fun x hx => by
          have hb := enclosingCell_corner_mem_cellBall (Nat.zero_le _) hL.pos p h2 hx
          rw [h4] at hb
          exact (mem_sitesOfCells_iff (Nat.zero_le _) hL).2
            ((hzS _ hb).2 ((mem_sitesOfCells_iff (Nat.zero_le _) hL).1 (h3 hx)))
        exact ⟨⟨key _ (by simp [plaquetteCorners]), h2, fun x hx => key x hx⟩, h4⟩
    have hB : ∀ j, j < F.top → bondsOver S {z} (j + 1) = bondsOver S' {z} (j + 1) := by
      intro j hj
      ext c
      simp only [bondsOver, innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
        Finset.mem_singleton]
      have hj1 : j + 1 ≤ F.top := hj
      constructor
      · rintro ⟨⟨h1, h2⟩, h4⟩
        have hb := enclosingCell_add_unitStep_mem_cellBall hj1 hL.pos c.1 c.2
        rw [h4] at hb
        have ha : z ∈ cellBall z 1 := by
          have := add_mem_cellBall_one z 0 (by simp)
          simpa [BlockLevels.siteOfCoords_zero] using this
        refine ⟨⟨?_, ?_⟩, h4⟩
        · refine (mem_sitesOfCells_iff hj1 hL).2 ?_
          rw [h4]
          exact (hzS _ ha).1 (h4 ▸ (mem_sitesOfCells_iff hj1 hL).1 h1)
        · exact (mem_sitesOfCells_iff hj1 hL).2 ((hzS _ hb).1 ((mem_sitesOfCells_iff hj1 hL).1 h2))
      · rintro ⟨⟨h1, h2⟩, h4⟩
        have hb := enclosingCell_add_unitStep_mem_cellBall hj1 hL.pos c.1 c.2
        rw [h4] at hb
        have ha : z ∈ cellBall z 1 := by
          have := add_mem_cellBall_one z 0 (by simp)
          simpa [BlockLevels.siteOfCoords_zero] using this
        refine ⟨⟨?_, ?_⟩, h4⟩
        · refine (mem_sitesOfCells_iff hj1 hL).2 ?_
          rw [h4]
          exact (hzS _ ha).2 (h4 ▸ (mem_sitesOfCells_iff hj1 hL).1 h1)
        · exact (mem_sitesOfCells_iff hj1 hL).2 ((hzS _ hb).2 ((mem_sitesOfCells_iff hj1 hL).1 h2))
    unfold chartCellTerms cellTerms
    rw [hP]
    refine congrArg₂ (· + ·) ?_ (congrArg (a * ·) ?_)
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [chartChain_of_lt V (Nat.succ_pos _), chartChain_of_lt V' (Nat.succ_pos _)]
      symm
      refine plaquetteEnergy_rotated hL hT hM p fun x hx => ?_
      simp only [plaquettesOver, innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        and_true, Finset.mem_singleton] at hp
      obtain ⟨⟨-, h2, h3⟩, h4⟩ := hp
      have hb := enclosingCell_corner_mem_cellBall (Nat.zero_le _) hL.pos p h2 hx
      rw [h4] at hb
      exact ((hball _ hb).2) ((hzS _ hb).2 ((mem_sitesOfCells_iff (Nat.zero_le _) hL).1 (h3 hx)))
    · refine Finset.sum_congr rfl fun j hjr => ?_
      have hj : j < F.top := Finset.mem_range.1 hjr
      rw [hB j hj]
      refine Finset.sum_congr rfl fun c hc => ?_
      simp only [bondsOver, innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
        Finset.mem_singleton] at hc
      obtain ⟨⟨h1, h2⟩, h4⟩ := hc
      have hj1 : j + 1 ≤ F.top := hj
      have hb := enclosingCell_add_unitStep_mem_cellBall hj1 hL.pos c.1 c.2
      rw [h4] at hb
      have ha : z ∈ cellBall z 1 := by
        have := add_mem_cellBall_one z 0 (by simp)
        simpa [BlockLevels.siteOfCoords_zero] using this
      have hcC : BondWithin C c := by
        constructor
        · rw [h4]
          exact (hball _ ha).2 ((hzS _ ha).2 (h4 ▸ (mem_sitesOfCells_iff hj1 hL).1 h1))
        · exact (hball _ hb).2 ((hzS _ hb).2 ((mem_sitesOfCells_iff hj1 hL).1 h2))
      have hfr := gaugedContourAverage_rotated hL hT hj (hf j hj) c hcC
      rw [chartChain_of_lt V hj, chartChain_of_lt V' hj]
      show gaugedBlockFit (chartField R U j) (balancingGauge (chartField R U j) (R j)) _ c =
        gaugedBlockFit (chartField R' U' j) (balancingGauge (chartField R' U' j) (R' j)) _ c
      by_cases hjt : j + 1 < F.top
      · rw [chartChain_of_lt V hjt, chartChain_of_lt V' hjt]
        unfold gaugedBlockFit
        rw [hfr]
        have hX : chartField R' U' (j + 1) c.1 c.2 = γ (baseSite c.1) * chartField R U (j + 1) c.1 c.2 *
            (γ (baseSite (c.1 + unitStep (j + 1) c.2)))⁻¹ := hf (j + 1) hjt c hcC
        rw [hX]
        exact (fitDefect_conj _ _ _ _).symm
      · have hn : F.top = F.depth + 1 := rfl
        have hjt' : j = F.depth := by omega
        subst hjt'
        have hC1 : c.1 ∈ C := by
          have := hcC.1
          rwa [enclosingCell_cell hL.pos] at this
        have hC2 : c.1 + unitStep (F.depth + 1) c.2 ∈ C := by
          have := hcC.2
          rwa [enclosingCell_cell hL.pos] at this
        have e1 : γ (baseSite c.1) = 1 := by
          rw [baseSite_eq_cellCentre]
          exact hγ _ hC1
        have e2 : γ (baseSite (c.1 + unitStep (F.depth + 1) c.2)) = 1 := by
          rw [baseSite_eq_cellCentre]
          exact hγ _ hC2
        have h1 : (((1 : UnitQuaternion)) : ℍ[ℝ]) = 1 := rfl
        rw [e1, e2, inv_one, h1, one_mul, mul_one] at hfr
        have hVc : V c.1 c.2 = V' c.1 c.2 := hV c.1 c.2 hC1 hC2
        unfold gaugedBlockFit
        rw [hfr, chartChain_top V, chartChain_top V', hVc]
  · intro π V V' b hb hcross
    have hγb : ∀ y : F.Cell, y ∈ C → γ (baseSite y) = 1 := fun y hy => by
      rw [baseSite_eq_cellCentre]
      exact hγ y hy
    have hκ : ∀ x : F.Site F.depth, enclosingCell x ∈ C →
        centreGauge (chartGauge R' U' F.top) x = centreGauge (chartGauge R U F.top) x := by
      intro x hx
      unfold centreGauge
      by_cases h : ∃ y : F.Cell, refineSite y = x
      · rw [dif_pos h, dif_pos h]
        have hy := h.choose_spec
        have hmem : refineSite h.choose ∈ sitesBelow F.depth h.choose := by
          have := refineSite_add_mem_sitesBelow F.depth h.choose (o := 0) (fun m => by
            have : (0 : ℤ) ≤ ((F.blockSide : ℤ) - 1) / 2 := by
              obtain ⟨q, hq⟩ := hL
              rw [hq]
              push_cast
              omega
            simpa using this)
          simpa [BlockLevels.siteOfCoords_zero] using this
        have hc : h.choose ∈ C := by
          have e := enclosingCell_of_mem_sitesBelow (Nat.le_succ _) le_rfl hL hmem
          rw [hy, enclosingCell_cell hL.pos] at e
          rwa [← e]
        have hcc : enclosingCell (h.choose : F.Site (F.depth + 1)) ∈ C := by
          rwa [enclosingCell_cell hL.pos]
        have := hk F.depth (Nat.lt_succ_self _) h.choose hcc
        rw [hγb _ hc] at this
        simpa using this
      · rw [dif_neg h, dif_neg h]
    set κ := centreGauge (chartGauge R U F.top) with hκd
    set σ : F.Site F.depth → UnitQuaternion := fun x => κ x * γ (baseSite x) * (κ x)⁻¹ with hσd
    have hσ : ∀ y ∈ C, σ (cellCentre F.depth y) = 1 := fun y hy => by
      simp only [hσd]
      rw [baseSite_cellCentre F.depth (Nat.le_succ _) y, hγ y hy]
      simp
    have hW : ∀ b' : F.Site F.depth × Fin 4, BondWithin C b' →
        chartFieldTopFixed R' U' b'.1 b'.2 = gaugeTransform σ (chartFieldTopFixed R U) b'.1 b'.2 := by
      intro b' hb'
      have hX : chartField R' U' F.depth b'.1 b'.2 = γ (baseSite b'.1) * chartField R U F.depth b'.1 b'.2 *
          (γ (baseSite (b'.1 + unitStep F.depth b'.2)))⁻¹ := hf F.depth (Nat.lt_succ_self _) b' hb'
      show centreGauge (chartGauge R' U' F.top) b'.1 * chartField R' U' F.depth b'.1 b'.2 *
          (centreGauge (chartGauge R' U' F.top) (b'.1 + unitStep F.depth b'.2))⁻¹ =
        σ b'.1 * (κ b'.1 * chartField R U F.depth b'.1 b'.2 * (κ (b'.1 + unitStep F.depth b'.2))⁻¹) *
          (σ (b'.1 + unitStep F.depth b'.2))⁻¹
      rw [hκ _ hb'.1, hκ _ hb'.2, hX]
      simp only [hσd]
      group
    have hcoord := gaugeTransform_axialGauge_invariant hamb hL π (chartFieldTopFixed R U)
      (chartFieldTopFixed R' U') σ hσ hW b hb
    unfold bondCoordinate
    by_cases hcr : IsCrossingBond b
    · simp only [if_pos hcr]
      rw [hcoord, hcross hcr]
    · simp only [if_neg hcr]
      rw [hcoord]
end Locality
end YangMills.Construction.CellTerms
end
