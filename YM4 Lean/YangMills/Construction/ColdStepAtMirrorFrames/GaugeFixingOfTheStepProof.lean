import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.ColdStepAtMirrorFrames.GaugeFixingOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.HaarMeasureInLogarithmicCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps MeasureTheory
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace GaugeFixing
section Paths
variable {F : BlockFrame} {j : ℕ}
def pathEnd (x : F.Site j) : List PathStep → F.Site j
  | [] => x
  | st :: r => pathEnd (x + stepDisplacement j st) r
theorem pathHolonomy_append (X : F.GaugeField j) (l l' : List PathStep) (x : F.Site j) :
    pathHolonomy X x (l ++ l') = pathHolonomy X x l * pathHolonomy X (pathEnd x l) l' := by
  induction l generalizing x with
  | nil => simp [pathHolonomy, pathEnd]
  | cons st r ih =>
    simp only [List.cons_append, pathHolonomy, pathEnd, ih, mul_assoc]
theorem pathEnd_append (l l' : List PathStep) (x : F.Site j) :
    pathEnd x (l ++ l') = pathEnd (pathEnd x l) l' := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih => simp only [List.cons_append, pathEnd, ih]
theorem pathEnd_replicate (a : ℕ) (st : PathStep) (x : F.Site j) :
    pathEnd x (List.replicate a st) = x + a • stepDisplacement j st := by
  induction a generalizing x with
  | zero => simp [pathEnd]
  | succ a ih =>
    simp only [List.replicate_succ, pathEnd, ih, succ_nsmul]
    abel
def axisLeg (h : Fin 4 → ℤ) (k : Fin 4) : List PathStep :=
  List.replicate (h k).natAbs (k, decide (0 ≤ h k))
theorem axisPath_eq_legs (h : Fin 4 → ℤ) :
    axisPath h 1 = axisLeg h 0 ++ (axisLeg h 1 ++ (axisLeg h 2 ++ axisLeg h 3)) := by apply _root_.YangMills.Construction.GaugeFixing.axisPath_one_eq <;> assumption
theorem pathEnd_axisLeg (h : Fin 4 → ℤ) (k : Fin 4) (x : F.Site j) :
    pathEnd x (axisLeg h k) = x + (h k) • BlockAverages.unitStep j k := by
  rw [axisLeg, pathEnd_replicate]
  congr 1
  by_cases hk : 0 ≤ h k
  · have : ((h k).natAbs : ℤ) = h k := Int.natAbs_of_nonneg hk
    simp only [stepDisplacement, decide_eq_true hk, if_true]
    rw [← natCast_zsmul, this]
  · have h1 : ((h k).natAbs : ℤ) = -h k := by
      have := not_le.mp hk
      omega
    have h2 : decide (0 ≤ h k) = false := decide_eq_false hk
    simp only [stepDisplacement, h2, Bool.false_eq_true, if_false]
    rw [← natCast_zsmul, h1]
    simp
theorem siteOfCoords_eq_sum (h : Fin 4 → ℤ) :
    siteOfCoords (F := F) j h = ∑ k, (h k) • BlockAverages.unitStep (F := F) j k := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_eq_sum <;> assumption
theorem pathEnd_axisPath (h : Fin 4 → ℤ) (x : F.Site j) :
    pathEnd x (axisPath h 1) = x + siteOfCoords j h := by
  rw [axisPath_eq_legs, pathEnd_append, pathEnd_append, pathEnd_append, pathEnd_axisLeg,
    pathEnd_axisLeg, pathEnd_axisLeg, pathEnd_axisLeg, siteOfCoords_eq_sum, Fin.sum_univ_four]
  abel
theorem axisPath_add_single_of_nonneg (h : Fin 4 → ℤ) (i : Fin 4) (hz : ∀ l, i < l → h l = 0)
    (hs : 0 ≤ h i) :
    axisPath (h + Pi.single i 1) 1 = axisPath h 1 ++ [(i, true)] := by apply _root_.YangMills.Construction.GaugeFixing.axisPath_add_single_of_nonneg <;> assumption
theorem axisPath_eq_add_single_of_neg (h : Fin 4 → ℤ) (i : Fin 4) (hz : ∀ l, i < l → h l = 0)
    (hs : h i < 0) :
    axisPath h 1 = axisPath (h + Pi.single i 1) 1 ++ [(i, false)] := by apply _root_.YangMills.Construction.GaugeFixing.axisPath_of_neg <;> assumption
end Paths
section Geometry
variable {F : BlockFrame} {n : ℕ}
structure IsCubicOdd (F : BlockFrame) (n : ℕ) : Prop where
  extent_eq : ∀ i, F.extent i = n
  two_le : 2 ≤ n
  odd_blockSide : Odd F.blockSide
theorem top_sub_depth (F : BlockFrame) : F.top - F.depth = 1 := by simp [BlockFrame.top]
theorem period_depth (h : IsCubicOdd F n) (i : Fin 4) : F.period F.depth i = n * F.blockSide := by
  simp [BlockFrame.period, BlockFrame.top, h.extent_eq]
theorem period_top (h : IsCubicOdd F n) (i : Fin 4) : F.period F.top i = n := by
  simp [BlockFrame.period, BlockFrame.top, h.extent_eq]
def halfSide (F : BlockFrame) : ℤ := ((F.blockSide : ℤ) - 1) / 2
theorem blockSide_eq_two_mul_halfSide_add_one (h : IsCubicOdd F n) :
    (F.blockSide : ℤ) = 2 * halfSide F + 1 := by
  obtain ⟨k, hk⟩ := h.odd_blockSide
  unfold halfSide
  rw [hk]
  push_cast
  omega
theorem halfSide_nonneg (h : IsCubicOdd F n) : 0 ≤ halfSide F := by
  obtain ⟨k, hk⟩ := h.odd_blockSide
  unfold halfSide
  rw [hk]
  push_cast
  omega
theorem blockSide_pos (h : IsCubicOdd F n) : 0 < F.blockSide := h.odd_blockSide.pos
theorem neZero_period_depth (h : IsCubicOdd F n) (i : Fin 4) : NeZero (F.period F.depth i) :=
  ⟨by rw [period_depth h]; exact (Nat.mul_pos (by have := h.two_le; omega) (blockSide_pos h)).ne'⟩
theorem neZero_period_top (h : IsCubicOdd F n) (i : Fin 4) : NeZero (F.period F.top i) :=
  ⟨by rw [period_top h]; have := h.two_le; omega⟩
theorem cellCentre_enclosingCell_apply (h : IsCubicOdd F n) (x : F.Site F.depth) (i : Fin 4) :
    (cellCentre F.depth (enclosingCell x)) i =
      (((F.blockSide : ℤ) * ((siteCoords x i + halfSide F) / (F.blockSide : ℤ)) : ℤ) :
        ZMod (F.period F.depth i)) := by
  have := neZero_period_top h i
  have := neZero_period_depth h i
  simp only [cellCentre, enclosingCell, siteOfCoords, siteCoords, top_sub_depth, pow_one]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.coe_intCast]
  set q : ℤ := (ZMod.cast (x i) + ((F.blockSide : ℤ) - 1) / 2) / (F.blockSide : ℤ) with hq
  have e2 := Int.emod_add_mul_ediv q (F.period F.top i : ℤ)
  refine ⟨q / (F.period F.top i : ℤ), ?_⟩
  have hkk : ((ZMod.cast (x i) : ℤ) + halfSide F) / (F.blockSide : ℤ) = q := rfl
  rw [hkk, period_depth h, ← period_top h i]
  push_cast
  linear_combination (-(F.blockSide : ℤ)) * e2
theorem cellOffset_apply (h : IsCubicOdd F n) (x : F.Site F.depth) (i : Fin 4) :
    cellOffset x i =
      siteCoords x i - (F.blockSide : ℤ) * ((siteCoords x i + halfSide F) / (F.blockSide : ℤ)) := by
  have := neZero_period_depth h i
  have hL := blockSide_eq_two_mul_halfSide_add_one h
  have hk := halfSide_nonneg h
  have hLz : (0 : ℤ) < (F.blockSide : ℤ) := by omega
  set c := siteCoords x i with hc
  set q := (c + halfSide F) / (F.blockSide : ℤ) with hq
  have e1 := Int.emod_add_mul_ediv (c + halfSide F) (F.blockSide : ℤ)
  have e2 := Int.emod_nonneg (c + halfSide F) hLz.ne'
  have e3 := Int.emod_lt_of_pos (c + halfSide F) hLz
  have hN : ((F.period F.depth i : ℕ) : ℤ) = (n : ℤ) * (F.blockSide : ℤ) := by
    rw [period_depth h]
    push_cast
    ring
  have hn2 : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast h.two_le
  unfold cellOffset
  rw [ZMod.valMinAbs_spec]
  constructor
  · rw [Pi.sub_apply, cellCentre_enclosingCell_apply h x i, Int.cast_sub, ← hc, ← hq]
    congr 1
    exact (ZMod.intCast_zmod_cast (x i)).symm
  · rw [Set.mem_Ioc, hN]
    have hr : c - (F.blockSide : ℤ) * q = (c + halfSide F) % (F.blockSide : ℤ) - halfSide F := by
      rw [← hq] at e1
      linarith
    rw [hr]
    constructor <;> nlinarith
theorem abs_cellOffset_le (h : IsCubicOdd F n) (x : F.Site F.depth) (i : Fin 4) :
    |cellOffset x i| ≤ halfSide F := by
  have hL := blockSide_eq_two_mul_halfSide_add_one h
  have hLz : (0 : ℤ) < (F.blockSide : ℤ) := by omega
  rw [cellOffset_apply h]
  set c := siteCoords x i with hc
  have e1 := Int.emod_add_mul_ediv (c + halfSide F) (F.blockSide : ℤ)
  have e2 := Int.emod_nonneg (c + halfSide F) hLz.ne'
  have e3 := Int.emod_lt_of_pos (c + halfSide F) hLz
  rw [abs_le]
  constructor <;> linarith
theorem cellOffset_cast (x : F.Site F.depth) (i : Fin 4) [NeZero (F.period F.depth i)] :
    ((cellOffset x i : ℤ) : ZMod (F.period F.depth i)) =
      (x - cellCentre F.depth (enclosingCell x)) i :=
  ZMod.coe_valMinAbs _
theorem cellCentre_add_cellOffset (h : IsCubicOdd F n) (x : F.Site F.depth) :
    cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth (cellOffset x) = x := by
  funext i
  have := neZero_period_depth h i
  simp only [Pi.add_apply, siteOfCoords]
  rw [cellOffset_cast]
  simp
theorem cellOffset_add_unitStep (h : IsCubicOdd F n) (x : F.Site F.depth) (i : Fin 4)
    (hc : enclosingCell (x + BlockAverages.unitStep F.depth i) = enclosingCell x) :
    cellOffset (x + BlockAverages.unitStep F.depth i) = cellOffset x + Pi.single i 1 := by
  funext l
  have := neZero_period_depth h l
  have hcast : ((cellOffset (x + BlockAverages.unitStep F.depth i) l : ℤ) : ZMod (F.period F.depth l)) =
      (((cellOffset x + Pi.single i 1 : Fin 4 → ℤ) l : ℤ) : ZMod (F.period F.depth l)) := by
    rw [cellOffset_cast, hc, Pi.add_apply, Int.cast_add, cellOffset_cast]
    simp only [Pi.sub_apply, Pi.add_apply, BlockAverages.unitStep, siteOfCoords]
    abel
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
  have hb1 := abs_le.mp (abs_cellOffset_le h x l)
  have hb2 := abs_le.mp (abs_cellOffset_le h (x + BlockAverages.unitStep F.depth i) l)
  have hL := blockSide_eq_two_mul_halfSide_add_one h
  have hN : ((F.period F.depth l : ℕ) : ℤ) = (n : ℤ) * (F.blockSide : ℤ) := by
    rw [period_depth h]
    push_cast
    ring
  have hn2 : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast h.two_le
  have hs : |(Pi.single i 1 : Fin 4 → ℤ) l| ≤ 1 := by
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have hs' := abs_le.mp hs
  have hlt : |((cellOffset x + Pi.single i 1 : Fin 4 → ℤ) l -
      cellOffset (x + BlockAverages.unitStep F.depth i) l)| < ((F.period F.depth l : ℕ) : ℤ) := by
    rw [hN, Pi.add_apply, abs_lt]
    constructor <;> nlinarith
  have h0 := Int.eq_zero_of_abs_lt_dvd hcast hlt
  linarith
theorem enclosingCell_cellCentre (h : IsCubicOdd F n) (z : F.Cell) :
    enclosingCell (cellCentre F.depth z) = z := by
  funext i
  have := neZero_period_depth h i
  have := neZero_period_top h i
  have hL := blockSide_eq_two_mul_halfSide_add_one h
  have hk := halfSide_nonneg h
  have hLz : (0 : ℤ) < (F.blockSide : ℤ) := by omega
  set a : ℤ := siteCoords z i with ha
  have ha0 : 0 ≤ a := by
    rw [ha, siteCoords, ← ZMod.natCast_val]
    positivity
  have han : a < (n : ℤ) := by
    have h1 : (z i).val < n := lt_of_lt_of_eq (ZMod.val_lt _) (period_top h i)
    rw [ha, siteCoords, ← ZMod.natCast_val]
    exact_mod_cast h1
  have hN : ((F.period F.depth i : ℕ) : ℤ) = (n : ℤ) * (F.blockSide : ℤ) := by
    rw [period_depth h]
    push_cast
    ring
  have hcoord : siteCoords (cellCentre F.depth z) i = (F.blockSide : ℤ) * a := by
    have ha' : (ZMod.cast (z i) : ℤ) = a := rfl
    simp only [siteCoords, cellCentre, siteOfCoords, top_sub_depth, pow_one]
    rw [ZMod.coe_intCast, hN, ha']
    refine Int.emod_eq_of_lt (mul_nonneg hLz.le ha0) ?_
    rw [mul_comm (n : ℤ)]
    exact mul_lt_mul_of_pos_left han hLz
  simp only [enclosingCell, siteOfCoords, top_sub_depth, pow_one]
  have hkk : ((F.blockSide : ℤ) - 1) / 2 = halfSide F := rfl
  rw [hcoord, hkk]
  have hq : ((F.blockSide : ℤ) * a + halfSide F) / (F.blockSide : ℤ) = a := by
    rw [add_comm, Int.add_mul_ediv_left _ _ hLz.ne', Int.ediv_eq_zero_of_lt hk (by omega), zero_add]
  rw [hq, ha]
  exact ZMod.intCast_zmod_cast (z i)
theorem cellOffset_cellCentre (h : IsCubicOdd F n) (z : F.Cell) :
    cellOffset (cellCentre F.depth z) = 0 := by
  funext i
  have := neZero_period_depth h i
  unfold cellOffset
  rw [enclosingCell_cellCentre h]
  simp
def treeTransport (X : F.GaugeField F.depth) (x : F.Site F.depth) : UnitQuaternion :=
  pathHolonomy X (cellCentre F.depth (enclosingCell x)) (axisPath (cellOffset x) 1)
theorem treeTransport_cellCentre (h : IsCubicOdd F n) (X : F.GaugeField F.depth) (z : F.Cell) :
    treeTransport X (cellCentre F.depth z) = 1 := by
  unfold treeTransport
  rw [cellOffset_cellCentre h, axisPath_eq_legs]
  simp [axisLeg, pathHolonomy]
theorem treeTransport_add_unitStep (h : IsCubicOdd F n) (X : F.GaugeField F.depth) (x : F.Site F.depth)
    (i : Fin 4) (ht : IsAxialTreeBond (x, i)) :
    treeTransport X (x + BlockAverages.unitStep F.depth i) = treeTransport X x * X x i := by
  have hc : enclosingCell (x + BlockAverages.unitStep F.depth i) = enclosingCell x := not_not.mp ht.1
  have hz : ∀ l, i < l → cellOffset x l = 0 := ht.2
  have hoff := cellOffset_add_unitStep h x i hc
  unfold treeTransport
  rw [hc, hoff]
  by_cases hs : 0 ≤ cellOffset x i
  · rw [axisPath_add_single_of_nonneg _ i hz hs, pathHolonomy_append, pathEnd_axisPath,
      cellCentre_add_cellOffset h]
    simp [pathHolonomy, linkValue]
  · have hs' := not_le.mp hs
    have hy : cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth (cellOffset x + Pi.single i 1) =
        x + BlockAverages.unitStep F.depth i := by
      rw [← hoff, ← hc]
      exact cellCentre_add_cellOffset h _
    rw [axisPath_eq_add_single_of_neg _ i hz hs', pathHolonomy_append, pathEnd_axisPath, hy]
    simp [pathHolonomy, linkValue]
end Geometry
section Group
abbrev ImagSpace : Type := EuclideanSpace ℝ (Fin 3)
theorem eq_haarUnit_of_isMulLeftInvariant (μ : Measure UnitQuaternion) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] : μ = haarUnit := by apply _root_.YangMills.Construction.WeightedResponses.eq_haarUnit_of_isMulLeftInvariant <;> assumption
instance haarUnit_isMulRightInvariant : haarUnit.IsMulRightInvariant := by
  constructor
  intro g
  have : (Measure.map (· * g) haarUnit).IsMulLeftInvariant := isMulLeftInvariant_map_mul_right g
  have : IsProbabilityMeasure (Measure.map (· * g) haarUnit) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  exact eq_haarUnit_of_isMulLeftInvariant _
theorem measurePreserving_mul_left_mul_right (g h : UnitQuaternion) :
    MeasurePreserving (fun u : UnitQuaternion => g * u * h) haarUnit haarUnit :=
  (measurePreserving_mul_right haarUnit h).comp (measurePreserving_mul_left haarUnit g)
def expLog (v : ImagSpace) : UnitQuaternion := expUnit (toImaginary v)
theorem continuous_expLog : Continuous expLog := by
  have hl : Continuous fun v : ImagSpace => ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]) := by
    have h : (fun v : ImagSpace => ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])) = fun v =>
        Quaternion.linearIsometryEquivTuple.symm (!₂[0, v 0, v 1, v 2] : EuclideanSpace ℝ (Fin 4)) := rfl
    rw [h]
    refine Quaternion.linearIsometryEquivTuple.symm.continuous.comp ?_
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  refine Continuous.subtype_mk ?_ _
  refine continuous_iff_continuousAt.mpr fun a => ?_
  exact ContinuousAt.comp (g := NormedSpace.exp)
    (f := fun v : ImagSpace => ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]))
    (NormedSpace.exp_analytic (𝕂 := ℝ) _).continuousAt hl.continuousAt
theorem measurable_expLog : Measurable expLog := continuous_expLog.measurable
theorem measurable_haarLogDensity : Measurable haarLogDensity := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.measurable_haarLogDensity <;> assumption
theorem haarLogDensity_nonneg (v : ImagSpace) : 0 ≤ haarLogDensity v := by
  unfold haarLogDensity
  split_ifs
  · positivity
  · exact le_rfl
theorem integrable_haarLogDensity (hH : HaarIntegralInLogCoords) :
    Integrable haarLogDensity ∧ ∫ v, haarLogDensity v = 1 := by
  have h1 := hH (fun _ => 1) continuous_const
  simp only [mul_one] at h1
  have h2 : ∫ _ : UnitQuaternion, (1 : ℝ) ∂haarUnit = 1 := by simp
  rw [h2] at h1
  refine ⟨?_, h1.symm⟩
  by_contra hnot
  rw [integral_undef hnot] at h1
  exact one_ne_zero h1
theorem haarUnit_eq_map_expLog (hH : HaarIntegralInLogCoords) :
    haarUnit = ((volume : Measure ImagSpace).withDensity fun v =>
      ENNReal.ofReal (haarLogDensity v)).map expLog := by
  obtain ⟨hi, h1⟩ := integrable_haarLogDensity hH
  have hmass : ∫⁻ v : ImagSpace, ENNReal.ofReal (haarLogDensity v) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall haarLogDensity_nonneg), h1, ENNReal.ofReal_one]
  have hfin : IsFiniteMeasure ((volume : Measure ImagSpace).withDensity fun v =>
      ENNReal.ofReal (haarLogDensity v)) := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hmass]
    exact ENNReal.one_lt_top⟩
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map measurable_expLog.aemeasurable f.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul measurable_haarLogDensity.ennreal_ofReal
      (Filter.Eventually.of_forall fun v => ENNReal.ofReal_lt_top), hH f f.continuous]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (haarLogDensity_nonneg v)]
  rfl
theorem lintegral_haarUnit (hH : HaarIntegralInLogCoords) {ψ : UnitQuaternion → ℝ≥0∞}
    (hψ : Measurable ψ) :
    ∫⁻ g, ψ g ∂haarUnit = ∫⁻ v : ImagSpace, ENNReal.ofReal (haarLogDensity v) * ψ (expLog v) := by
  rw [haarUnit_eq_map_expLog hH, lintegral_map hψ measurable_expLog]
  exact lintegral_withDensity_eq_lintegral_mul _ measurable_haarLogDensity.ennreal_ofReal
    (hψ.comp measurable_expLog)
theorem lintegral_prod_ofReal_pi {ι : Type} [Fintype ι] (f : ι → ImagSpace → ℝ)
    (hf : ∀ c, Integrable (f c)) (h0 : ∀ c v, 0 ≤ f c v) :
    ∫⁻ w : ι → ImagSpace, ∏ c, ENNReal.ofReal (f c (w c)) = ∏ c, ∫⁻ v, ENNReal.ofReal (f c v) := by
  have hp : ∀ w : ι → ImagSpace, ∏ c, ENNReal.ofReal (f c (w c)) = ENNReal.ofReal (∏ c, f c (w c)) :=
    fun w => (ENNReal.ofReal_prod_of_nonneg fun c _ => h0 c _).symm
  simp only [hp]
  rw [volume_pi, ← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod hf)
    (Filter.Eventually.of_forall fun w => Finset.prod_nonneg fun c _ => h0 c _),
    integral_fintype_prod_eq_prod (𝕜 := ℝ) f, ENNReal.ofReal_prod_of_nonneg fun c _ =>
      integral_nonneg (h0 c)]
  refine Finset.prod_congr rfl fun c _ => ?_
  exact ofReal_integral_eq_lintegral_ofReal (hf c) (Filter.Eventually.of_forall (h0 c))
theorem pi_haarUnit_eq_map (hH : HaarIntegralInLogCoords) {ι κ : Type} [Fintype ι]
    [Fintype κ] [DecidableEq κ] (ε : ι ≃ κ) (r : ι → UnitQuaternion) :
    Measure.pi (fun _ : ι => haarUnit) =
      ((volume : Measure (κ → ImagSpace)).withDensity fun w =>
        ∏ c, ENNReal.ofReal (haarLogDensity (w c))).map
        fun w b => expLog (w (ε b)) * r b := by
  obtain ⟨hi, _⟩ := integrable_haarLogDensity hH
  have hK : Measurable fun (w : κ → ImagSpace) (b : ι) => expLog (w (ε b)) * r b :=
    measurable_pi_lambda _ fun b =>
      (measurable_expLog.comp (measurable_pi_apply (ε b))).mul_const (r b)
  refine Measure.pi_eq fun s hs => ?_
  have hbox : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  rw [Measure.map_apply hK hbox, withDensity_apply _ (hK hbox)]
  set f : κ → ImagSpace → ℝ := fun c v =>
    (s (ε.symm c)).indicator (fun _ => (1 : ℝ)) (expLog v * r (ε.symm c)) * haarLogDensity v with hf
  have hmeasind : ∀ c, Measurable fun v : ImagSpace =>
      (s (ε.symm c)).indicator (fun _ => (1 : ℝ)) (expLog v * r (ε.symm c)) := fun c =>
    (measurable_const.indicator (hs _)).comp (measurable_expLog.mul_const _)
  have hfi : ∀ c, Integrable (f c) := by
    intro c
    refine Integrable.bdd_mul (c := 1) hi (hmeasind c).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun v => ?_
    simp only [Set.indicator]
    split_ifs <;> simp
  have hf0 : ∀ c v, 0 ≤ f c v := fun c v =>
    mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (haarLogDensity_nonneg v)
  have hprod : ∫⁻ w in (fun (w : κ → ImagSpace) (b : ι) => expLog (w (ε b)) * r b) ⁻¹'
      Set.pi Set.univ s, ∏ c, ENNReal.ofReal (haarLogDensity (w c)) =
      ∫⁻ w : κ → ImagSpace, ∏ c, ENNReal.ofReal (f c (w c)) := by
    rw [← lintegral_indicator (hK hbox)]
    refine lintegral_congr fun w => ?_
    by_cases hw : w ∈ (fun (w : κ → ImagSpace) (b : ι) => expLog (w (ε b)) * r b) ⁻¹' Set.pi Set.univ s
    · rw [Set.indicator_of_mem hw]
      refine Finset.prod_congr rfl fun c _ => ?_
      have hm := hw (ε.symm c) (Set.mem_univ _)
      simp only [Equiv.apply_symm_apply] at hm
      simp only [hf]
      rw [Set.indicator_of_mem hm, one_mul]
    · rw [Set.indicator_of_notMem hw]
      have : ∃ b, expLog (w (ε b)) * r b ∉ s b := by
        by_contra hcon
        push Not at hcon
        exact hw fun b _ => hcon b
      obtain ⟨b, hb⟩ := this
      refine (Finset.prod_eq_zero (Finset.mem_univ (ε b)) ?_).symm
      simp only [hf, Equiv.symm_apply_apply]
      rw [Set.indicator_of_notMem hb, zero_mul, ENNReal.ofReal_zero]
  rw [hprod, lintegral_prod_ofReal_pi f hfi hf0]
  rw [← Equiv.prod_comp ε]
  refine Finset.prod_congr rfl fun b _ => ?_
  have hψ : Measurable fun g : UnitQuaternion =>
      ENNReal.ofReal ((s b).indicator (fun _ => (1 : ℝ)) (g * r b)) :=
    ((measurable_const.indicator (hs b)).comp (measurable_mul_const (r b))).ennreal_ofReal
  have h1 := lintegral_haarUnit hH hψ
  have h2 : ∫⁻ v, ENNReal.ofReal (f (ε b) v) =
      ∫⁻ v : ImagSpace, ENNReal.ofReal (haarLogDensity v) *
        ENNReal.ofReal ((s b).indicator (fun _ => (1 : ℝ)) (expLog v * r b)) := by
    refine lintegral_congr fun v => ?_
    simp only [hf, Equiv.symm_apply_apply]
    rw [ENNReal.ofReal_mul (Set.indicator_nonneg (fun _ _ => zero_le_one) _), mul_comm]
  rw [h2, ← h1]
  have h3 : (fun g : UnitQuaternion => ENNReal.ofReal ((s b).indicator (fun _ => (1 : ℝ)) (g * r b))) =
      ((· * r b) ⁻¹' s b).indicator 1 := by
    funext g
    by_cases hg : g * r b ∈ s b
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (show g ∈ (· * r b) ⁻¹' s b from hg)]
      simp
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (show g ∉ (· * r b) ⁻¹' s b from hg)]
      simp
  rw [h3, lintegral_indicator_one (measurable_mul_const (r b) (hs b)),
    (measurePreserving_mul_right haarUnit (r b)).measure_preimage (hs b).nullMeasurableSet]
end Group
section Main
open Classical
variable {F : BlockFrame} {n m : ℕ}
theorem zmod_cast_cast_of_eq {a b : ℕ} (h : a = b) (u : ZMod b) :
    (((((u.cast : ℤ) : ZMod a)).cast : ℤ) : ZMod b) = u := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_roundTrip <;> assumption
theorem zmod_cast_add_of_eq {a b : ℕ} (h : a = b) (u v : ZMod a) :
    (((u + v).cast : ℤ) : ZMod b) = ((u.cast : ℤ) : ZMod b) + ((v.cast : ℤ) : ZMod b) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_add <;> assumption
theorem zmod_cast_intCast_of_eq {a b : ℕ} (h : a = b) (z : ℤ) :
    (((z : ZMod a).cast : ℤ) : ZMod b) = (z : ZMod b) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_intCast <;> assumption
def frameSite (F : BlockFrame) (x : TorusSite m) : F.Site F.depth :=
  siteOfCoords F.depth fun k => ((x k).cast : ℤ)
theorem toTorusSite_frameSite (hp : ∀ i, F.period F.depth i = m) (x : TorusSite m) :
    toTorusSite m (frameSite F x) = x :=
  funext fun k => zmod_cast_cast_of_eq (hp k) (x k)
theorem frameSite_toTorusSite (hp : ∀ i, F.period F.depth i = m) (y : F.Site F.depth) :
    frameSite F (toTorusSite m y) = y :=
  funext fun k => zmod_cast_cast_of_eq (hp k).symm (y k)
theorem toTorusSite_add (hp : ∀ i, F.period F.depth i = m) (x y : F.Site F.depth) :
    toTorusSite m (x + y) = toTorusSite m x + toTorusSite m y :=
  funext fun k => zmod_cast_add_of_eq (hp k) (x k) (y k)
theorem siteOfInt_single (i : Fin 4) :
    (siteOfInt (Pi.single i 1) : TorusSite m) = TorusFields.unitStep m i := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfInt_single <;> assumption
theorem toTorusSite_unitStep (hp : ∀ i, F.period F.depth i = m) (i : Fin 4) :
    toTorusSite m (BlockAverages.unitStep (F := F) F.depth i) = TorusFields.unitStep m i := by
  have h : toTorusSite m (siteOfCoords (F := F) F.depth (Pi.single i 1)) = siteOfInt (Pi.single i 1) :=
    funext fun k => zmod_cast_intCast_of_eq (hp k) _
  rw [BlockAverages.unitStep, h, siteOfInt_single]
theorem frameSite_add_unitStep (hp : ∀ i, F.period F.depth i = m) (x : TorusSite m) (i : Fin 4) :
    frameSite F (x + TorusFields.unitStep m i) = frameSite F x + BlockAverages.unitStep F.depth i := by
  have h1 := frameSite_toTorusSite hp (frameSite F x + BlockAverages.unitStep F.depth i)
  rw [toTorusSite_add hp, toTorusSite_frameSite hp, toTorusSite_unitStep hp] at h1
  exact h1
def IsOnTree (F : BlockFrame) (b : TorusBond m) : Prop :=
  IsAxialTreeBond (F := F) (frameSite F b.1, b.2)
def glueBonds (F : BlockFrame) (A : {b : TorusBond m // IsOnTree F b} → UnitQuaternion)
    (u : {b : TorusBond m // ¬IsOnTree F b} → UnitQuaternion) : TorusBond m → UnitQuaternion :=
  fun b => if h : IsOnTree F b then A ⟨b, h⟩ else u ⟨b, h⟩
def treeOnlyField (F : BlockFrame) (A : {b : TorusBond m // IsOnTree F b} → UnitQuaternion) :
    F.GaugeField F.depth :=
  fun x i => glueBonds F A (fun _ => 1) (toTorusSite m x, i)
def treeGauge (F : BlockFrame) (A : {b : TorusBond m // IsOnTree F b} → UnitQuaternion)
    (z : TorusSite m) : UnitQuaternion :=
  treeTransport (treeOnlyField F A) (frameSite F z)
def gaugedOffTree (F : BlockFrame) (A : {b : TorusBond m // IsOnTree F b} → UnitQuaternion)
    (u : {b : TorusBond m // ¬IsOnTree F b} → UnitQuaternion) :
    {b : TorusBond m // ¬IsOnTree F b} → UnitQuaternion := fun b =>
  treeGauge F A b.1.1 * u b * (treeGauge F A (b.1.1 + TorusFields.unitStep m b.1.2))⁻¹
theorem restrictToTorus_glue (hp : ∀ i, F.period F.depth i = m)
    (A : {b : TorusBond m // IsOnTree F b} → UnitQuaternion)
    (u : {b : TorusBond m // ¬IsOnTree F b} → UnitQuaternion) :
    restrictToTorus m (fun (x : F.Site F.depth) i => glueBonds F A u (toTorusSite m x, i)) =
      Function.curry (glueBonds F A u) := by
  funext x i
  show glueBonds F A u (toTorusSite m (frameSite F x), i) = _
  rw [toTorusSite_frameSite hp]
  rfl
theorem restrictToTorus_gauge_glue (h : IsCubicOdd F n) (hp : ∀ i, F.period F.depth i = m)
    (A : {b : TorusBond m // IsOnTree F b} → UnitQuaternion)
    (u : {b : TorusBond m // ¬IsOnTree F b} → UnitQuaternion) :
    restrictToTorus m (gaugeTransform (treeTransport (treeOnlyField F A))
      (fun (x : F.Site F.depth) i => glueBonds F A u (toTorusSite m x, i))) =
      Function.curry (glueBonds F (fun _ => 1) (gaugedOffTree F A u)) := by
  funext x i
  show treeTransport (treeOnlyField F A) (frameSite F x) *
    glueBonds F A u (toTorusSite m (frameSite F x), i) *
    (treeTransport (treeOnlyField F A) (frameSite F x + BlockAverages.unitStep F.depth i))⁻¹ =
      glueBonds F (fun _ => 1) (gaugedOffTree F A u) (x, i)
  rw [toTorusSite_frameSite hp]
  by_cases ht : IsOnTree F (x, i)
  · have h1 := treeTransport_add_unitStep h (treeOnlyField F A) (frameSite F x) i ht
    have h2 : treeOnlyField F A (frameSite F x) i = glueBonds F A u (x, i) := by
      simp only [treeOnlyField, toTorusSite_frameSite hp, glueBonds, dif_pos ht]
    rw [h1, h2]
    simp [glueBonds, dif_pos ht]
  · have h1 : glueBonds F A u (x, i) = u ⟨(x, i), ht⟩ := dif_neg ht
    have h2 : glueBonds F (fun _ => 1) (gaugedOffTree F A u) (x, i) =
        gaugedOffTree F A u ⟨(x, i), ht⟩ := dif_neg ht
    rw [h1, h2]
    simp only [gaugedOffTree, treeGauge, frameSite_add_unitStep hp]
theorem measurePreserving_uncurry_fieldHaar [NeZero m] :
    MeasurePreserving (fun (W : TorusField m) (b : TorusBond m) => W b.1 b.2) (fieldHaar m)
      (Measure.pi fun _ : TorusBond m => haarUnit) := by
  have hm : Measurable fun (W : TorusField m) (b : TorusBond m) => W b.1 b.2 :=
    measurable_pi_lambda _ fun b => (measurable_pi_apply b.2).comp (measurable_pi_apply b.1)
  refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hset : (fun (W : TorusField m) (b : TorusBond m) => W b.1 b.2) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun x => Set.pi Set.univ fun i => s (x, i) := by
    ext W
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Prod.forall]
  rw [hset, fieldHaar, Measure.pi_pi]
  simp only [Measure.pi_pi]
  rw [Fintype.prod_prod_type]
theorem measurePreserving_gaugedOffTree [NeZero m]
    (A : {b : TorusBond m // IsOnTree F b} → UnitQuaternion) :
    MeasurePreserving (gaugedOffTree F A)
      (Measure.pi fun _ : {b : TorusBond m // ¬IsOnTree F b} => haarUnit)
      (Measure.pi fun _ : {b : TorusBond m // ¬IsOnTree F b} => haarUnit) := measurePreserving_pi _ _ fun b => measurePreserving_mul_left_mul_right _ _
theorem measurable_glueBonds [NeZero m] :
    Measurable fun q : ({b : TorusBond m // IsOnTree F b} → UnitQuaternion) ×
      ({b : TorusBond m // ¬IsOnTree F b} → UnitQuaternion) => glueBonds F q.1 q.2 :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : TorusBond m => UnitQuaternion) (IsOnTree F)).symm.measurable
theorem lintegral_fieldHaar_eq_offTree [NeZero m] (h : IsCubicOdd F n) (hp : ∀ i, F.period F.depth i = m)
    {Gf : TorusField m → ℝ≥0∞} (hG : Measurable Gf)
    (hinv : ∀ γ : F.Site F.depth → UnitQuaternion, (∀ z, γ (cellCentre F.depth z) = 1) →
      ∀ X : F.GaugeField F.depth,
        Gf (restrictToTorus m (gaugeTransform γ X)) = Gf (restrictToTorus m X)) :
    ∫⁻ W, Gf W ∂(fieldHaar m) = ∫⁻ u : {b : TorusBond m // ¬IsOnTree F b} → UnitQuaternion,
      Gf (Function.curry (glueBonds F (fun _ => 1) u)) ∂(Measure.pi fun _ => haarUnit) := by
  have hcur : Measurable (Function.curry : (TorusBond m → UnitQuaternion) → TorusField m) :=
    (MeasurableEquiv.curry (TorusSite m) (Fin 4) UnitQuaternion).measurable
  have hm1 : Measurable fun f : TorusBond m → UnitQuaternion => Gf (Function.curry f) := hG.comp hcur
  have hm2 : Measurable fun q : ({b : TorusBond m // IsOnTree F b} → UnitQuaternion) ×
      ({b : TorusBond m // ¬IsOnTree F b} → UnitQuaternion) =>
        Gf (Function.curry (glueBonds F q.1 q.2)) :=
    hm1.comp measurable_glueBonds
  have hs := MeasurePreserving.symm _ (measurePreserving_piEquivPiSubtypeProd
    (fun _ : TorusBond m => (haarUnit : Measure UnitQuaternion)) (IsOnTree F))
  calc ∫⁻ W, Gf W ∂(fieldHaar m)
      = ∫⁻ f, Gf (Function.curry f) ∂(Measure.pi fun _ : TorusBond m => haarUnit) := by
        rw [← measurePreserving_uncurry_fieldHaar.lintegral_comp hm1]
        rfl
    _ = ∫⁻ q, Gf (Function.curry (glueBonds F q.1 q.2))
          ∂((Measure.pi fun _ : {b : TorusBond m // IsOnTree F b} => haarUnit).prod
          (Measure.pi fun _ : {b : TorusBond m // ¬IsOnTree F b} => haarUnit)) := by
        rw [← hs.lintegral_comp hm1]
        rfl
    _ = ∫⁻ A, ∫⁻ u, Gf (Function.curry (glueBonds F A u)) ∂(Measure.pi fun _ => haarUnit)
          ∂(Measure.pi fun _ => haarUnit) := lintegral_prod _ hm2.aemeasurable
    _ = ∫⁻ _ : {b : TorusBond m // IsOnTree F b} → UnitQuaternion,
          (∫⁻ u : {b : TorusBond m // ¬IsOnTree F b} → UnitQuaternion,
          Gf (Function.curry (glueBonds F (fun _ => 1) u)) ∂(Measure.pi fun _ => haarUnit))
          ∂(Measure.pi fun _ => haarUnit) := by
        refine lintegral_congr fun A => ?_
        have hm3 : Measurable fun u : {b : TorusBond m // ¬IsOnTree F b} → UnitQuaternion =>
            Gf (Function.curry (glueBonds F (fun _ => 1) u)) :=
          hm2.comp (measurable_const.prodMk measurable_id)
        rw [← (measurePreserving_gaugedOffTree A).lintegral_comp hm3]
        refine lintegral_congr fun u => ?_
        have h1 := hinv (treeTransport (treeOnlyField F A)) (fun z => treeTransport_cellCentre h _ z)
          (fun (x : F.Site F.depth) i => glueBonds F A u (toTorusSite m x, i))
        rw [restrictToTorus_gauge_glue h hp, restrictToTorus_glue hp] at h1
        exact h1.symm
    _ = _ := by
        rw [lintegral_const]
        simp
end Main
section Chart
open Classical
variable {F : BlockFrame} {n m : ℕ}
def offTreeValue (F : BlockFrame) (V : F.GaugeField F.top) (b : {b : TorusBond m // ¬IsOnTree F b}) :
    UnitQuaternion :=
  if IsCrossingBond (frameSite F b.1.1, b.1.2) then V (enclosingCell (frameSite F b.1.1)) b.1.2 else 1
theorem mem_chordBonds_iff (hcov : BlocksCoverLowerLevel) (h : IsCubicOdd F n)
    (c : F.Site F.depth × Fin 4) :
    c ∈ chordBonds (finiteCells F) ↔ ¬IsAxialTreeBond c := by
  have hs : ∀ i, 0 < F.extent i := fun i => by
    rw [h.extent_eq]
    have := h.two_le
    omega
  have hall : ∀ x : F.Site F.depth, x ∈ sitesOfCells (finiteCells F) F.depth :=
    hcov F h.odd_blockSide hs
  unfold chordBonds innerBonds
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  constructor
  · exact fun hc => hc.2
  · exact fun hc => ⟨⟨hall _, hall _⟩, hc⟩
def offTreeEquivChord (hcov : BlocksCoverLowerLevel) (h : IsCubicOdd F n)
    (hp : ∀ i, F.period F.depth i = m) :
    {b : TorusBond m // ¬IsOnTree F b} ≃ ↥(chordBonds (finiteCells F)) where
  toFun b := ⟨(frameSite F b.1.1, b.1.2), (mem_chordBonds_iff hcov h _).mpr b.2⟩
  invFun c := ⟨(toTorusSite m c.1.1, c.1.2), by
    have h1 := (mem_chordBonds_iff hcov h _).mp c.2
    show ¬IsAxialTreeBond (F := F) (frameSite F (toTorusSite m c.1.1), c.1.2)
    rw [frameSite_toTorusSite hp]
    exact h1⟩
  left_inv b := by
    apply Subtype.ext
    exact Prod.ext (toTorusSite_frameSite hp b.1.1) rfl
  right_inv c := by
    apply Subtype.ext
    exact Prod.ext (frameSite_toTorusSite hp c.1.1) rfl
theorem glue_chart_eq (hcov : BlocksCoverLowerLevel) (h : IsCubicOdd F n)
    (hp : ∀ i, F.period F.depth i = m) (V : F.GaugeField F.top)
    (w : ↥(chordBonds (finiteCells F)) → ImagSpace) :
    Function.curry (glueBonds F (fun _ => 1)
      (fun b => expLog (w (offTreeEquivChord hcov h hp b)) * offTreeValue F V b)) =
      restrictToTorus m (chartedField (stepCoordinates w) V) := by
  funext x i
  show glueBonds F (fun _ => 1) _ (x, i) = chartedField (stepCoordinates w) V (frameSite F x) i
  by_cases ht : IsOnTree F (x, i)
  · have hc : ¬IsCrossingBond (F := F) (frameSite F x, i) := ht.1
    have ht' : IsAxialTreeBond (F := F) (frameSite F x, i) := ht
    simp only [glueBonds, dif_pos ht, chartedField, if_neg hc, if_pos ht']
  · have hmem : (frameSite F x, i) ∈ chordBonds (finiteCells F) := (mem_chordBonds_iff hcov h _).mpr ht
    have hco : stepCoordinates w (frameSite F x) i = toImaginary (w ⟨(frameSite F x, i), hmem⟩) := by
      simp only [stepCoordinates, dif_pos hmem]
    have h1 : glueBonds F (fun _ => 1)
        (fun b => expLog (w (offTreeEquivChord hcov h hp b)) * offTreeValue F V b) (x, i) =
        expLog (w ⟨(frameSite F x, i), hmem⟩) * offTreeValue F V ⟨(x, i), ht⟩ := dif_neg ht
    rw [h1]
    by_cases hc : IsCrossingBond (F := F) (frameSite F x, i)
    · simp only [chartedField, if_pos hc, hco, offTreeValue, expLog]
    · have ht' : ¬IsAxialTreeBond (F := F) (frameSite F x, i) := ht
      simp only [chartedField, if_neg hc, if_neg ht', hco, offTreeValue, expLog, mul_one]
theorem integral_fieldHaar_eq_step [NeZero m] (hH : HaarIntegralInLogCoords)
    (hcov : BlocksCoverLowerLevel) (h : IsCubicOdd F n) (hp : ∀ i, F.period F.depth i = m)
    (V : F.GaugeField F.top) {G : TorusField m → ℝ} (hG : Measurable G) (h0 : ∀ W, 0 ≤ G W)
    (hinv : ∀ γ : F.Site F.depth → UnitQuaternion, (∀ z, γ (cellCentre F.depth z) = 1) →
      ∀ X : F.GaugeField F.depth,
        G (restrictToTorus m (gaugeTransform γ X)) = G (restrictToTorus m X)) :
    ∫ W, G W ∂(fieldHaar m) = ∫ w : StepVariable (finiteCells F),
      G (restrictToTorus m (chartedField (stepCoordinates w) V)) * ∏ b, haarLogDensity (w b) := by
  set ε := offTreeEquivChord hcov h hp with hε
  have hlaw := pi_haarUnit_eq_map hH ε (offTreeValue F V)
  have hK : Measurable fun (w : ↥(chordBonds (finiteCells F)) → ImagSpace)
      (b : {b : TorusBond m // ¬IsOnTree F b}) => expLog (w (ε b)) * offTreeValue F V b :=
    measurable_pi_lambda _ fun b =>
      (measurable_expLog.comp (measurable_pi_apply (ε b))).mul_const _
  have hD : Measurable fun w : ↥(chordBonds (finiteCells F)) → ImagSpace =>
      ∏ c, ENNReal.ofReal (haarLogDensity (w c)) :=
    Finset.measurable_prod _ fun c _ =>
      (measurable_haarLogDensity.comp (measurable_pi_apply c)).ennreal_ofReal
  have hDr : Measurable fun w : ↥(chordBonds (finiteCells F)) → ImagSpace =>
      ∏ c, haarLogDensity (w c) :=
    Finset.measurable_prod _ fun c _ => measurable_haarLogDensity.comp (measurable_pi_apply c)
  have hcur : Measurable (Function.curry : (TorusBond m → UnitQuaternion) → TorusField m) :=
    (MeasurableEquiv.curry (TorusSite m) (Fin 4) UnitQuaternion).measurable
  have hH1 : Measurable fun u : {b : TorusBond m // ¬IsOnTree F b} → UnitQuaternion =>
      G (Function.curry (glueBonds F (fun _ => 1) u)) := by
    have hc : Measurable fun u : {b : TorusBond m // ¬IsOnTree F b} → UnitQuaternion =>
        (((fun _ => 1) : {b : TorusBond m // IsOnTree F b} → UnitQuaternion), u) :=
      measurable_const.prodMk measurable_id
    exact hG.comp (hcur.comp ((measurable_glueBonds (F := F) (m := m)).comp hc))
  have hchart : Measurable fun w : ↥(chordBonds (finiteCells F)) → ImagSpace =>
      G (restrictToTorus m (chartedField (stepCoordinates w) V)) := by
    have : (fun w : ↥(chordBonds (finiteCells F)) → ImagSpace =>
        G (restrictToTorus m (chartedField (stepCoordinates w) V))) =
        (fun u => G (Function.curry (glueBonds F (fun _ => 1) u))) ∘
          fun w b => expLog (w (ε b)) * offTreeValue F V b := by
      funext w
      simp only [Function.comp]
      rw [glue_chart_eq hcov h hp V w]
    rw [this]
    exact hH1.comp hK
  have hrhs0 : ∀ w : ↥(chordBonds (finiteCells F)) → ImagSpace,
      0 ≤ G (restrictToTorus m (chartedField (stepCoordinates w) V)) * ∏ b, haarLogDensity (w b) :=
    fun w => mul_nonneg (h0 _) (Finset.prod_nonneg fun _ _ => haarLogDensity_nonneg _)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) hG.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hrhs0)
      (hchart.mul hDr).aestronglyMeasurable]
  congr 1
  rw [lintegral_fieldHaar_eq_offTree h hp hG.ennreal_ofReal fun γ hγ X => by rw [hinv γ hγ X], hlaw,
    lintegral_map hH1.ennreal_ofReal hK]
  refine (lintegral_withDensity_eq_lintegral_mul _ hD (hH1.ennreal_ofReal.comp hK)).trans ?_
  refine lintegral_congr fun w => ?_
  simp only [Pi.mul_apply, Function.comp]
  rw [glue_chart_eq hcov h hp V w, ENNReal.ofReal_mul (h0 _),
    ENNReal.ofReal_prod_of_nonneg fun c _ => haarLogDensity_nonneg _, mul_comm]
end Chart
end GaugeFixing
open GaugeFixing in
theorem haarIntegralEqStepIntegral (hH : HaarIntegralInLogCoords)
    (hcov : BlocksCoverLowerLevel) : HaarIntegralEqStepIntegral := by
  intro L t n inst hodd h2 V G hG h0 hinv
  have hC : IsCubicOdd (torusFrame L t n) n := ⟨fun _ => rfl, h2, hodd⟩
  haveI : NeZero (n * (torusFrame L t n).blockSide) := inst
  exact integral_fieldHaar_eq_step hH hcov hC (fun i => period_depth hC i) V hG h0 hinv
end YangMills.Construction.ColdStepAtMirrorFrames
end
