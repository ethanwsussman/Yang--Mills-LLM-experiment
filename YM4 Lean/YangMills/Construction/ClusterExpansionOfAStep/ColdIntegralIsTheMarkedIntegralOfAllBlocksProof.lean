import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheMarkedIntegralOfAllBlocks
import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingIsASetting
import YangMills.Construction.ClusterExpansionOfAStep.FreeBondsInCoordinates
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import YangMills.Construction.SummableBoundsOfTheFlow.TwoLevelsOnOneTorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings StepCosts StepMarks
  GaugeFixing
namespace MarkedIntegrals
namespace ChartRepresentation
theorem cast_add_of_eq (P m : ℕ) (h : P = m) (a b : ZMod m) :
    (((a + b).cast : ℤ) : ZMod P) = ((a.cast : ℤ) : ZMod P) + ((b.cast : ℤ) : ZMod P) := by
  subst h; simp
theorem cast_intCast_of_eq (P m : ℕ) (h : P = m) (z : ℤ) :
    ((((z : ZMod m)).cast : ℤ) : ZMod P) = (z : ZMod P) := by
  subst h; simp
variable {H : BlockFrame} {m : ℕ}
theorem toTorusSite_torusSiteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusSite m) :
    toTorusSite m (torusSiteInFrame H j x) = x := by apply _root_.YangMills.Construction.TorusLevels.toTorusSite_torusSiteInFrame <;> assumption
theorem torusSiteInFrame_toTorusSite (j : ℕ) (hm : ∀ i, H.period j i = m) (y : H.Site j) :
    torusSiteInFrame H j (toTorusSite m y) = y := by apply _root_.YangMills.Construction.TorusLevels.torusSiteInFrame_toTorusSite <;> assumption
theorem torusSiteInFrame_add (j : ℕ) (hm : ∀ i, H.period j i = m) (x y : TorusSite m) :
    torusSiteInFrame H j (x + y) = torusSiteInFrame H j x + torusSiteInFrame H j y := by
  funext k
  exact cast_add_of_eq _ _ (hm k) (x k) (y k)
theorem torusSiteInFrame_unitStep (j : ℕ) (hm : ∀ i, H.period j i = m) (i : Fin 4) :
    torusSiteInFrame H j (TorusFields.unitStep m i) = BlockAverages.unitStep j i := by
  funext k
  have h := cast_intCast_of_eq _ _ (hm k) ((Pi.single i 1 : Fin 4 → ℤ) k)
  have h2 : (TorusFields.unitStep m i) k = (((Pi.single i 1 : Fin 4 → ℤ) k : ℤ) : ZMod m) := by
    by_cases hk : k = i
    · subst hk; simp [TorusFields.unitStep]
    · simp [TorusFields.unitStep, hk]
  show ((((TorusFields.unitStep m i) k).cast : ℤ) : ZMod (H.period j k)) = _
  rw [h2, h]
  rfl
theorem torusSiteInFrame_neg (j : ℕ) (hm : ∀ i, H.period j i = m) (x : TorusSite m) :
    torusSiteInFrame H j (-x) = - torusSiteInFrame H j x := by
  have h := torusSiteInFrame_add (H := H) j hm x (-x)
  have h0 : torusSiteInFrame H j (0 : TorusSite m) = 0 := by
    have := torusSiteInFrame_add (H := H) j hm (0 : TorusSite m) 0
    simpa using this
  rw [add_neg_cancel, h0] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm
theorem torusSiteInFrame_sub (j : ℕ) (hm : ∀ i, H.period j i = m) (x y : TorusSite m) :
    torusSiteInFrame H j (x - y) = torusSiteInFrame H j x - torusSiteInFrame H j y := by
  rw [sub_eq_add_neg, torusSiteInFrame_add j hm, torusSiteInFrame_neg j hm, sub_eq_add_neg]
def torusPathHolonomy (W : TorusField m) : TorusSite m → List PathStep → UnitQuaternion
  | _, [] => 1
  | x, st :: r =>
    (if st.2 then W x st.1 else (W (x - TorusFields.unitStep m st.1) st.1)⁻¹) *
      torusPathHolonomy W (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) r
theorem readAtLevel_torusSiteInFrame (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusField m)
    (x : TorusSite m) (i : Fin 4) :
    readAtLevel H j W (torusSiteInFrame H j x) i = W x i := by
  show W (toTorusSite m (torusSiteInFrame H j x)) i = W x i
  rw [toTorusSite_torusSiteInFrame j hm]
theorem pathHolonomy_readAtLevel (j : ℕ) (hm : ∀ i, H.period j i = m) (W : TorusField m) (x : TorusSite m)
    (l : List PathStep) :
    pathHolonomy (readAtLevel H j W) (torusSiteInFrame H j x) l = torusPathHolonomy W x l := by
  induction l generalizing x with
  | nil => rfl
  | cons st r ih =>
    have hv : stepDisplacement j st + torusSiteInFrame H j x = torusSiteInFrame H j
        (x + (if st.2 then TorusFields.unitStep m st.1 else - TorusFields.unitStep m st.1)) := by
      rw [torusSiteInFrame_add j hm]
      rcases st with ⟨i, b⟩
      cases b
      · simp [stepDisplacement, torusSiteInFrame_neg j hm, torusSiteInFrame_unitStep j hm, add_comm]
      · simp [stepDisplacement, torusSiteInFrame_unitStep j hm, add_comm]
    simp only [pathHolonomy, torusPathHolonomy]
    rw [add_comm (torusSiteInFrame H j x), hv, ih]
    congr 1
    rcases st with ⟨i, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      rw [← torusSiteInFrame_unitStep j hm, ← torusSiteInFrame_sub j hm, readAtLevel_torusSiteInFrame j hm]
    · simp only [linkValue, if_true]
      rw [readAtLevel_torusSiteInFrame j hm]
section Blocks
variable {H : BlockFrame} {n : ℕ}
theorem period_depth_eq (hs : ∀ i, H.extent i = n) (i : Fin 4) : H.period H.depth i = n * H.blockSide := by
  simp [BlockFrame.period, hs]
end Blocks
section Plain
variable {H : BlockFrame} {n : ℕ}
theorem mergedBoxes_empty {j : ℕ} : mergedBoxes (∅ : Finset (Finset (H.Site j))) = ∅ := by apply _root_.YangMills.Construction.SettingFits.mergedBoxes_empty <;> assumption
theorem excludedBoxes_empty (J₀ : ℕ) (y : H.Cell) :
    excludedBoxes J₀ (∅ : Finset (Finset (H.Site H.depth))) y = ∅ := by
  unfold excludedBoxes
  split_ifs
  · rfl
  · simp [nearbyLumps, mergedBoxes_empty]
theorem usedContours_empty (J₀ : ℕ) (b : H.Cell → H.Site H.depth) (c : H.Cell × Fin 4) :
    usedContours J₀ (∅ : Finset (Finset (H.Site H.depth))) b c = allContours H := by
  unfold usedContours
  split_ifs with h
  · rfl
  · ext e
    simp only [Finset.mem_filter]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    intro x _ B hB
    simp [excludedBoxes_empty] at hB
theorem card_centredCube (M : ℕ) (hM : Odd M) : (centredCube M).card = M ^ 4 := by apply _root_.YangMills.Construction.LatticePaths.card_centredCube <;> assumption
theorem card_allContours (hL : Odd H.blockSide) : (allContours H).card = H.blockSide ^ 4 * 24 := by
  unfold allContours
  rw [Finset.card_product, card_centredCube _ hL]
  simp [Fintype.card_perm]
  exact Or.inl rfl
theorem valMinAbs_intCast_of_small (P : ℕ) (hP : 0 < P) (z : ℤ) (h : |z| * 2 < P) :
    ((z : ZMod P)).valMinAbs = z := by
  have : NeZero P := ⟨hP.ne'⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩ <;> cases abs_cases z <;> omega
theorem cellCentre_eq_refineSite (z : H.Cell) : cellCentre H.depth z = refineSite (j := H.depth) z := by apply _root_.YangMills.Construction.BondMeans.cellCentre_eq_refineSite <;> assumption
theorem minimalOffset_cellCentre_add (hs : ∀ i, H.extent i = n) (hn : 0 < n) (hL : Odd H.blockSide)
    (z : H.Cell) (ξ : Fin 4 → ℤ) (hξ : ξ ∈ centredCube H.blockSide) :
    minimalOffset (cellCentre H.depth z) (cellCentre H.depth z + siteOfCoords H.depth ξ) = ξ := by
  funext k
  unfold minimalOffset
  have h1 : (cellCentre H.depth z + siteOfCoords H.depth ξ - cellCentre H.depth z : H.Site H.depth) k =
      ((ξ k : ℤ) : ZMod (H.period H.depth k)) := by
    rw [add_sub_cancel_left]; rfl
  rw [h1]
  have hm := Fintype.mem_piFinset.1 hξ k
  rw [Finset.mem_Icc] at hm
  obtain ⟨q, hq⟩ := hL
  have hq' : (((H.blockSide : ℕ) : ℤ) - 1) / 2 = q := by rw [hq]; push_cast; omega
  rw [hq'] at hm
  have hP : H.period H.depth k = n * H.blockSide := period_depth_eq hs k
  have h2 : H.blockSide ≤ n * H.blockSide := Nat.le_mul_of_pos_left _ hn
  apply valMinAbs_intCast_of_small
  · rw [hP]; have : 0 < H.blockSide := by omega
    positivity
  · have h3 : |ξ k| ≤ q := abs_le.2 ⟨by omega, by omega⟩
    rw [hP]
    have h5 : ((H.blockSide : ℕ) : ℤ) = 2 * q + 1 := by rw [hq]; push_cast; ring
    omega
theorem contourMean_empty (hs : ∀ i, H.extent i = n) (hn : 0 < n) (hL : Odd H.blockSide) (J₀ : ℕ)
    (W : H.GaugeField H.depth) (c : H.Cell × Fin 4) :
    contourMean J₀ (∅ : Finset (Finset (H.Site H.depth))) (fun y => cellCentre H.depth y) W c =
      _root_.YangMills.Construction.BlockAverages.contourAverage (j := H.depth) W c := by
  unfold contourMean _root_.YangMills.Construction.BlockAverages.contourAverage
  rw [usedContours_empty, card_allContours hL]
  have h1 : (1 / (((H.blockSide ^ 4 * 24 : ℕ) : ℝ))) = 1 / (24 * (H.blockSide : ℝ) ^ 4) := by
    push_cast; ring_nf
  rw [h1]
  congr 1
  unfold allContours
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun ξ hξ => Finset.sum_congr rfl fun π _ => ?_
  unfold contourPath bondContour
  simp only [minimalOffset_cellCentre_add hs hn hL _ ξ hξ]
  rw [cellCentre_eq_refineSite]
theorem torusPathHolonomy_plaquette {m : ℕ} (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    torusPathHolonomy W x [(μ, true), (ν, true), (μ, false), (ν, false)] = holonomy W x μ ν := by
  simp only [torusPathHolonomy, holonomy]
  simp [mul_assoc, add_assoc, sub_eq_add_neg]
end Plain
section Hot
variable {n : ℕ}
theorem plaquetteDefect_readAtLevel_torus {H : BlockFrame} {j m : ℕ} (hm : ∀ i, H.period j i = m)
    (W : TorusField m) (p : H.Site j × Fin 4 × Fin 4) :
    plaquetteDefect (readAtLevel H j W) p = curvature W (toTorusSite m p.1) p.2.1 p.2.2 := by
  obtain ⟨y, μ, ν⟩ := p
  obtain ⟨x, rfl⟩ : ∃ x : TorusSite m, torusSiteInFrame H j x = y :=
    ⟨_, torusSiteInFrame_toTorusSite _ hm y⟩
  unfold plaquetteDefect curvature plaquetteHolonomy
  simp only [toTorusSite_torusSiteInFrame j hm]
  rw [pathHolonomy_readAtLevel j hm, torusPathHolonomy_plaquette]
theorem hotLumps_eq_empty_of_isCold {H : BlockFrame} {j m : ℕ} {L : ℕ} (g : LumpGrid L)
    (hm : ∀ i, H.period j i = m) (s : ℝ) (X : Finset (H.Site j)) (W : TorusField m) (hW : IsCold s W) :
    hotLumps g s X (readAtLevel H j W) = ∅ := by
  unfold hotLumps
  have hf : ((cutPlaquettes X).filter fun p => s ≤ plaquetteDefect (readAtLevel H j W) p) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    rw [Finset.mem_filter] at hp
    have h1 : p.2.1 < p.2.2 := by
      have := hp.1
      unfold cutPlaquettes at this
      rw [Finset.mem_filter] at this
      exact this.2.1
    have h2 := hW (toTorusSite m p.1) p.2.1 p.2.2 h1
    rw [plaquetteDefect_readAtLevel_torus hm] at hp
    exact absurd hp.2 (not_le.2 h2)
  rw [hf]
  rfl
theorem stepHotLumps_eq_empty (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (W : TorusField (n * ℓ.side)) (hW : IsCold ℓ.threshold W) :
    stepHotLumps ℓ W = ∅ :=
  hotLumps_eq_empty_of_isCold _ (period_depth_eq (H := stepBlockFrame ℓ.side n) (n := n) fun _ => rfl) _ _ W hW
theorem torusHotSites_eq_empty (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (W : TorusField (n * ℓ.side)) (hW : IsCold ℓ.threshold W) :
    torusHotSites ℓ W = ∅ := by
  have hL : 0 < ℓ.side := Nat.pos_of_ne_zero (NeZero.ne ℓ.side)
  have hq : n * ℓ.side / ℓ.side = n := Nat.mul_div_cancel _ hL
  have hm : ∀ i, (stepBlockFrame ℓ.side (n * ℓ.side / ℓ.side)).period 0 i = n * ℓ.side := by
    intro i
    show n * ℓ.side / ℓ.side * ℓ.side ^ (0 + 1 - 0) = n * ℓ.side
    rw [hq]
    simp
  unfold torusHotSites torusHotLumps
  rw [hotLumps_eq_empty_of_isCold _ hm _ _ W hW]
  rfl
end Hot
end ChartRepresentation
namespace MarkedIntegralIdentity
open TopLevelSites
def logFormula (g : UnitQuaternion) : ℍ[ℝ] :=
  (Real.arccos ((g : ℍ[ℝ])).re / ‖((g : ℍ[ℝ])).im‖) • ((g : ℍ[ℝ])).im
theorem measurable_logFormula [MeasurableSpace ℍ[ℝ]] [BorelSpace ℍ[ℝ]] : Measurable logFormula := by
  have h1 : Continuous fun g : UnitQuaternion => ((g : ℍ[ℝ])) := continuous_subtype_val
  have h2 : Continuous fun g : UnitQuaternion => ((g : ℍ[ℝ])).re := Quaternion.continuous_re.comp h1
  have h3 : Continuous fun g : UnitQuaternion => ((g : ℍ[ℝ])).im := Quaternion.continuous_im.comp h1
  have h4 : Continuous fun g : UnitQuaternion => Real.arccos ((g : ℍ[ℝ])).re := Real.continuous_arccos.comp h2
  have h5 : Continuous fun g : UnitQuaternion => ‖((g : ℍ[ℝ])).im‖ := h3.norm
  exact (h4.measurable.div h5.measurable).smul h3.measurable
theorem coe_minimalLog_eq_logFormula (g : UnitQuaternion) (hg : g ≠ -1) :
    ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]) = logFormula g := by
  set q : ℍ[ℝ] := (g : ℍ[ℝ]) with hq
  have hnorm : ‖q‖ = 1 := norm_unitQuaternion g
  have hparts := norm_sq_eq_re_sq_add_norm_im_sq q
  rw [hnorm] at hparts
  have hre1 : q.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖q.im‖]
  have hle : -1 ≤ q.re ∧ q.re ≤ 1 := abs_le.mp ((sq_le_one_iff_abs_le_one _).mp hre1)
  set θ := Real.arccos q.re with hθ
  have hcos : Real.cos θ = q.re := Real.cos_arccos hle.1 hle.2
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hθπ : θ ≤ Real.pi := Real.arccos_le_pi _
  have hsin : Real.sin θ = ‖q.im‖ := by
    have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ
    have h2 := Real.sin_sq_add_cos_sq θ
    rw [hcos] at h2
    have h3 : Real.sin θ ^ 2 = ‖q.im‖ ^ 2 := by linarith
    exact (pow_left_inj₀ h1 (norm_nonneg _) two_ne_zero).mp h3
  by_cases hv : q.im = 0
  · have hr : 0 < q.re := by
      by_contra hr
      have hre : q.re = -1 := by
        rw [hv] at hparts
        simp at hparts
        nlinarith
      apply hg
      apply Subtype.ext
      have := Quaternion.re_add_im q
      rw [hv, hre] at this
      have h1 : q = -1 := by simpa using this.symm
      exact h1.trans rfl
    have hre : q.re = 1 := by
      rw [hv] at hparts
      simp at hparts
      nlinarith
    have hq1 : q = 1 := by
      have := Quaternion.re_add_im q
      rw [hv, hre] at this
      simpa using this.symm
    have hg1 : g = expUnit 0 := by
      apply Subtype.ext
      rw [GaugeFixing.coe_expUnit]
      simp [← hq, hq1]
    have hl : minimalLog g = 0 := by
      rw [hg1]
      exact minimalLog_expUnit 0 (by simpa using Real.pi_pos)
    unfold logFormula
    rw [hl, ← hq, hv]
    simp
  · have hvn : ‖q.im‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hθne : θ ≠ 0 := by
      intro h0
      rw [h0, Real.sin_zero] at hsin
      exact hvn hsin.symm
    have hθlt : θ < Real.pi := by
      refine lt_of_le_of_ne hθπ fun h0 => hvn ?_
      rw [← hsin, h0, Real.sin_pi]
    let w : imaginaryQuaternions := ⟨(θ / ‖q.im‖) • q.im, by
      show ((θ / ‖q.im‖) • q.im).re = 0
      simp⟩
    have hwn : ‖(w : ℍ[ℝ])‖ = θ := by
      change ‖(θ / ‖q.im‖) • q.im‖ = θ
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hθ0 (norm_nonneg _))]
      field_simp
    have hexp : expUnit w = g := by
      apply Subtype.ext
      rw [GaugeFixing.coe_expUnit, exp_imaginary, hwn, hcos, hsin]
      change _ + _ • ((θ / ‖q.im‖) • q.im) = q
      rw [smul_smul]
      have e : ‖q.im‖ / θ * (θ / ‖q.im‖) = 1 := by field_simp
      rw [e, one_smul]
      exact Quaternion.re_add_im q
    have hl : minimalLog g = w := by
      rw [← hexp]
      exact minimalLog_expUnit w (by rw [hwn]; exact hθlt)
    rw [hl]
    rfl
theorem measurable_coe_minimalLog [MeasurableSpace ℍ[ℝ]] [BorelSpace ℍ[ℝ]] :
    Measurable fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]) := by
  classical
  have hs : MeasurableSet ({-1} : Set UnitQuaternion) := measurableSet_singleton _
  have e : (fun g : UnitQuaternion => ((minimalLog g : imaginaryQuaternions) : ℍ[ℝ])) =
      Set.piecewise {-1} (fun _ => ((minimalLog (-1) : imaginaryQuaternions) : ℍ[ℝ])) logFormula := by
    funext g
    by_cases hg : g = -1
    · subst hg
      simp
    · rw [Set.piecewise_eq_of_notMem _ _ _ (by simpa using hg)]
      exact coe_minimalLog_eq_logFormula g hg
  rw [e]
  exact Measurable.piecewise hs measurable_const measurable_logFormula
theorem measurable_norm_minimalLog_sub (c : ℍ[ℝ]) :
    Measurable fun g : UnitQuaternion => ‖((minimalLog g : imaginaryQuaternions) : ℍ[ℝ]) - c‖ := by
  letI : MeasurableSpace ℍ[ℝ] := borel ℍ[ℝ]
  haveI : BorelSpace ℍ[ℝ] := ⟨rfl⟩
  have hc : Continuous fun q : ℍ[ℝ] => ‖q - c‖ := by fun_prop
  exact hc.measurable.comp measurable_coe_minimalLog
section Borel
variable {n : ℕ} [NeZero n]
theorem continuous_pathHolonomy {F : BlockFrame} {j : ℕ} (x : F.Site j) (l : List PathStep) :
    Continuous fun W : F.GaugeField j => pathHolonomy W x l := by
  induction l generalizing x with
  | nil => exact continuous_const
  | cons st r ih =>
    simp only [pathHolonomy]
    refine Continuous.mul ?_ (ih _)
    rcases st with ⟨k, b⟩
    cases b
    · simp only [linkValue, Bool.false_eq_true, if_false]
      exact (continuous_apply_apply (x - BlockAverages.unitStep j k) k).inv
    · simp only [linkValue, if_true]
      exact continuous_apply_apply x k
theorem continuous_readAtLevel {F : BlockFrame} {j m : ℕ} :
    Continuous fun W : TorusField m => readAtLevel F j W := by
  refine continuous_pi fun x => continuous_pi fun i => ?_
  exact continuous_apply_apply _ i
theorem continuous_gaugeTransform_axialGauge {F : BlockFrame} (x : F.Site F.depth) (i : Fin 4) :
    Continuous fun W : F.GaugeField F.depth => BlockAverages.gaugeTransform (axialGauge 1 W) W x i := by
  unfold BlockAverages.gaugeTransform axialGauge
  exact ((continuous_pathHolonomy _ _).mul (continuous_apply_apply x i)).mul (continuous_pathHolonomy _ _).inv
theorem measurable_norm_bondCoordinate_sub {m : ℕ} [NeZero m] {F : BlockFrame} (V : F.GaugeField F.top)
    (b : F.Site F.depth × Fin 4) (c : ℍ[ℝ]) :
    Measurable fun W : TorusField m =>
      ‖((bondCoordinate 1 V (readAtLevel F F.depth W) b : imaginaryQuaternions) : ℍ[ℝ]) - c‖ := by
  unfold bondCoordinate
  by_cases hb : IsCrossingBond b
  · simp only [if_pos hb]
    exact (measurable_norm_minimalLog_sub c).comp
      ((((continuous_gaugeTransform_axialGauge b.1 b.2).comp continuous_readAtLevel).mul
        continuous_const).measurable)
  · simp only [if_neg hb]
    exact (measurable_norm_minimalLog_sub c).comp
      (((continuous_gaugeTransform_axialGauge b.1 b.2).comp continuous_readAtLevel).measurable)
theorem measurable_bondMark (R : StepSetup) [NeZero (n * R.params.side)] (hcut : IsCutoff R.ballRadius R.barrierFn)
    (V : TorusField n) (b : TorusBond (n * R.params.side)) :
    Measurable fun W : TorusField (n * R.params.side) => R.bondMark V W b := by
  classical
  have hd : Measurable fun W : TorusField (n * R.params.side) =>
      ‖((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]) -
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])‖ :=
    measurable_norm_bondCoordinate_sub (F := stepBlockFrame R.params.side n) _ _ _
  have h1 : ContinuousOn (fun u : ℝ => Real.exp (- R.barrierFn u)) (Set.Ico 0 R.ballRadius) :=
    Real.continuous_exp.comp_continuousOn hcut.smooth.continuousOn.neg
  have hm : MeasurableSet (Set.Ico 0 R.ballRadius) := measurableSet_Ico
  have h2 : Measurable ((Set.Ico 0 R.ballRadius).piecewise (fun u => Real.exp (- R.barrierFn u))
      fun _ => (0 : ℝ)) :=
    h1.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) hm
  have e : (fun W : TorusField (n * R.params.side) => R.bondMark V W b) =
      ((Set.Ico 0 R.ballRadius).piecewise (fun u => Real.exp (- R.barrierFn u)) fun _ => (0 : ℝ)) ∘
        fun W : TorusField (n * R.params.side) => ‖((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]) -
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])‖ := by
    funext W
    show cutoffFactor R.ballRadius R.barrierFn _ = _
    simp only [Function.comp]
    unfold cutoffFactor frameDeviation
    by_cases hlt : ‖((chartCoord R.params V W b : imaginaryQuaternions) : ℍ[ℝ]) -
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach V b : imaginaryQuaternions) : ℍ[ℝ])‖ <
          R.ballRadius
    · have e1 := Set.piecewise_eq_of_mem (Set.Ico 0 R.ballRadius) (fun u => Real.exp (- R.barrierFn u))
        (fun _ => (0 : ℝ)) (⟨norm_nonneg _, hlt⟩ : _ ∈ Set.Ico 0 R.ballRadius)
      exact (if_pos hlt).trans e1.symm
    · have e1 := Set.piecewise_eq_of_notMem (Set.Ico 0 R.ballRadius) (fun u => Real.exp (- R.barrierFn u))
        (fun _ => (0 : ℝ)) (fun h => hlt h.2)
      exact (if_neg hlt).trans e1.symm
  rw [e]
  exact h2.comp hd
end Borel
section Lower
variable {n : ℕ} [NeZero n]
def emptyLabelling (R : StepSetup) : (↥(∅ : Finset (TorusSite (n * R.params.side)))) → R.labels.Ω :=
  fun z => absurd z.2 (Finset.notMem_empty _)
theorem sitesInBlocks_univ (L : ℕ) [NeZero L] :
    sitesInBlocks L (Finset.univ : Finset (TorusSite n)) = Finset.univ := by
  ext x
  simp [sitesInBlocks]
open Classical in
theorem avoidingPart_univ (R : StepSetup) [NeZero R.params.side] (hrow : R.HasExpansions)
    (hb : IsBlockTorusSide R.params (n * R.params.side)) (W : TorusField (n * R.params.side)) :
    R.avoidingPart Finset.univ W =
      if IsHullState R.params R.range W ∅ then R.labelWeight (n * R.params.side) W ∅ (emptyLabelling R) else 0 := by
  unfold StepSetup.avoidingPart
  have hset : ((Finset.univ : Finset (Finset (TorusSite (n * R.params.side)))).filter fun Y =>
      IsHullState R.params R.range W Y ∧
        Disjoint Y (sitesInBlocks R.params.side (Finset.univ : Finset (TorusSite n)))) =
      if IsHullState R.params R.range W ∅ then {∅} else ∅ := by
    ext Y
    rw [sitesInBlocks_univ, ← Finset.top_eq_univ]
    simp only [Finset.mem_filter, Finset.top_eq_univ, Finset.mem_univ, true_and]
    rw [← Finset.top_eq_univ, disjoint_top, Finset.bot_eq_empty]
    split_ifs with h
    · simp only [Finset.mem_singleton]
      exact ⟨fun q => q.2, fun q => by rw [q]; exact ⟨h, rfl⟩⟩
    · simp only [Finset.notMem_empty, iff_false]
      rintro ⟨q1, rfl⟩
      exact h q1
  rw [hset]
  split_ifs with h
  · rw [Finset.sum_singleton]
    have hempty : (Measure.pi fun _ : ↥(∅ : Finset (TorusSite (n * R.params.side))) => R.labels.μ) =
        Measure.dirac (emptyLabelling R) := Measure.pi_of_empty _ _
    rw [hempty, lintegral_dirac' _ ?_, ENNReal.toReal_ofReal (hrow.2.nonneg _ hb W ∅ _ h)]
    exact measurable_const' fun a b => by rw [Subsingleton.elim a b]
  · simp
end Lower
section Gauge
open ChartRepresentation
variable {n : ℕ} [NeZero n]
theorem isCold_of_isHullState (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (hfit : ℓ.Admissible) {m : ℕ} [NeZero m]
    (hLn : ℓ.side ∣ m) (r : ℕ) (W : TorusField m) (h : IsHullState ℓ r W ∅) : IsCold ℓ.threshold W := by
  intro x μ ν hμ
  by_contra hc
  have hl : torusLumpOf ℓ x ∈ torusHotLumps ℓ W := (mem_torusHotLumps_iff ℓ hfit hLn W _).2
    ⟨x, μ, ν, hμ, not_lt.1 hc, x, by simp [plaquetteVertices], rfl⟩
  have hx : x ∈ torusHotSites ℓ W := mem_torusHotSites_iff.2 ⟨_, hl, mem_torusLumpOf_self x⟩
  have hw : x ∈ thickening (2 * r) (torusHotSites ℓ W) :=
    (mem_thickening _ _ _).2 ⟨x, hx, by rw [supDist_self]; omega⟩
  exact Finset.notMem_empty _ (h.1 hw)
theorem isHullState_of_isCold (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (r : ℕ) (W : TorusField (n * ℓ.side))
    (hW : IsCold ℓ.threshold W) : IsHullState ℓ r W ∅ := by
  refine ⟨?_, ?_⟩
  · rw [torusHotSites_eq_empty ℓ W hW]
    simp [thickening]
  · intro X hX
    simp [chainComponents] at hX
theorem baseChoices_eq_singleton (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (W : TorusField (n * ℓ.side)) (hW : IsCold ℓ.threshold W) :
    baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) = {fun y => cellCentre 0 y} := by
  classical
  have h0 : hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0)
      (readAtLevel (stepBlockFrame ℓ.side n) 0 W) = ∅ :=
    stepHotLumps_eq_empty ℓ W hW
  ext b
  simp only [baseChoices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  have key : ∀ Hs : Finset (Finset ((stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth)), Hs = ∅ →
      (IsBaseChoice ℓ.baseDepth Hs b ↔ b = fun y => cellCentre 0 y) := by
    rintro _ rfl
    constructor
    · intro hb
      funext y
      exact (hb y).1 (Or.inl (by unfold nearbyLumps; exact Finset.filter_empty _))
    · rintro rfl y
      exact ⟨fun _ => rfl,
        fun h => absurd (Or.inl (by unfold nearbyLumps; exact Finset.filter_empty _)) h⟩
  exact key _ h0
theorem averagedKernel_eq_prod (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (x : ℝ) (W : TorusField (n * ℓ.side))
    (hW : IsCold ℓ.threshold W) (V : (stepBlockFrame ℓ.side n).GaugeField 1) :
    averagedKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W) V =
      ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
        bondKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W) V (fun y => cellCentre 0 y) c := by
  unfold averagedKernel
  rw [baseChoices_eq_singleton ℓ W hW]
  simp
theorem bondKernel_eq (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (hodd : Odd ℓ.side) (x : ℝ) (W : TorusField (n * ℓ.side))
    (hW : IsCold ℓ.threshold W) (V : (stepBlockFrame ℓ.side n).GaugeField 1)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) :
    bondKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W) V (fun y => cellCentre 0 y) c =
      Real.exp (ℓ.coupling * x * (_root_.YangMills.Construction.BlockAverages.contourAverage (j := (stepBlockFrame ℓ.side n).depth)
        (readAtLevel (stepBlockFrame ℓ.side n) 0 W) c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).re) /
        partitionFn (ℓ.coupling * x * ‖_root_.YangMills.Construction.BlockAverages.contourAverage (j := (stepBlockFrame ℓ.side n).depth)
          (readAtLevel (stepBlockFrame ℓ.side n) 0 W) c‖) := by
  have h0 : hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0)
      (readAtLevel (stepBlockFrame ℓ.side n) 0 W) = ∅ :=
    stepHotLumps_eq_empty ℓ W hW
  have h := contourMean_empty (H := stepBlockFrame ℓ.side n) (n := n) (fun _ => rfl)
    (Nat.pos_of_ne_zero (NeZero.ne n)) hodd ℓ.baseDepth (readAtLevel (stepBlockFrame ℓ.side n) 0 W) c
  have key : ∀ Hs : Finset (Finset ((stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth)), Hs = ∅ →
      Real.exp (ℓ.coupling * x * (contourMean ℓ.baseDepth Hs (fun y => cellCentre 0 y)
        (readAtLevel (stepBlockFrame ℓ.side n) 0 W) c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).re) /
        partitionFn (ℓ.coupling * x * ‖contourMean ℓ.baseDepth Hs (fun y => cellCentre 0 y)
          (readAtLevel (stepBlockFrame ℓ.side n) 0 W) c‖) =
      Real.exp (ℓ.coupling * x * (_root_.YangMills.Construction.BlockAverages.contourAverage (j := (stepBlockFrame ℓ.side n).depth)
        (readAtLevel (stepBlockFrame ℓ.side n) 0 W) c * ((V c.1 c.2)⁻¹ : UnitQuaternion)).re) /
        partitionFn (ℓ.coupling * x * ‖_root_.YangMills.Construction.BlockAverages.contourAverage (j := (stepBlockFrame ℓ.side n).depth)
          (readAtLevel (stepBlockFrame ℓ.side n) 0 W) c‖) := by
    rintro _ rfl
    exact congrArg₂ (fun a b : ℍ[ℝ] =>
      Real.exp (ℓ.coupling * x * (a * (((V c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) /
        partitionFn (ℓ.coupling * x * ‖b‖)) h h
  exact key _ h0
theorem readAtLevel_gaugeTransform (L : ℕ) (g : TorusSite (n * L) → UnitQuaternion) (W : TorusField (n * L)) :
    readAtLevel (stepBlockFrame L n) 0 (TorusFields.gaugeTransform g W) =
      BlockAverages.gaugeTransform (fun z => g (toTorusSite (n * L) z))
        (readAtLevel (stepBlockFrame L n) 0 W) := by
  have hm : ∀ i, (stepBlockFrame L n).period 0 i = n * L := fun i => by
    show n * L ^ (0 + 1 - 0) = n * L
    simp
  funext z i
  show g (toTorusSite (n * L) z) * W (toTorusSite (n * L) z) i *
      (g (toTorusSite (n * L) z + TorusFields.unitStep _ i))⁻¹ =
    g (toTorusSite (n * L) z) * W (toTorusSite (n * L) z) i *
      (g (toTorusSite (n * L) (z + BlockAverages.unitStep 0 i)))⁻¹
  obtain ⟨x, rfl⟩ : ∃ x : TorusSite (n * L), torusSiteInFrame (stepBlockFrame L n) 0 x = z :=
    ⟨_, torusSiteInFrame_toTorusSite _ hm z⟩
  rw [← torusSiteInFrame_unitStep _ hm, ← torusSiteInFrame_add _ hm, toTorusSite_torusSiteInFrame _ hm,
    toTorusSite_torusSiteInFrame _ hm]
end Gauge
section Weight
open ChartRepresentation
variable {n : ℕ} [NeZero n]
theorem cellOffset_refineSite (R : StepSetup) (hodd : Odd R.params.side) (hn : 2 ≤ n)
    (z : (stepBlockFrame R.params.side n).Cell) :
    cellOffset (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0
        (toTorusSite (n * R.params.side) (refineSite (j := (stepBlockFrame R.params.side n).depth) z))) = 0 := by
  have hm : ∀ i, (stepBlockFrame R.params.side n).period (stepBlockFrame R.params.side n).depth i =
      n * R.params.side :=
    period_depth_eq (H := stepBlockFrame R.params.side n) (n := n) fun _ => rfl
  have h0 : (0 : Fin 4 → ℤ) ∈ centredCube (stepBlockFrame R.params.side n).blockSide := by
    rw [TopLevelSites.mem_centredCube_iff]
    intro i
    obtain ⟨q, hq⟩ := hodd
    have : TopLevelSites.halfWidth (stepBlockFrame R.params.side n).blockSide = q := by
      show TopLevelSites.halfWidth R.params.side = q
      unfold TopLevelSites.halfWidth
      rw [hq]
      push_cast
      omega
    rw [this]
    refine ⟨?_, ?_⟩ <;> simp only [Pi.zero_apply] <;> omega
  have h1 := TopLevelSites.cellOffset_centre_add (F := stepBlockFrame R.params.side n) hodd (fun _ => hn) z 0 h0
  have h2 : torusSiteInFrame (stepBlockFrame R.params.side n) 0
      (toTorusSite (n * R.params.side) (refineSite (j := (stepBlockFrame R.params.side n).depth) z)) =
      cellCentre (stepBlockFrame R.params.side n).depth z +
        siteOfCoords (stepBlockFrame R.params.side n).depth 0 := by
    rw [show torusSiteInFrame (stepBlockFrame R.params.side n) 0
        (toTorusSite (n * R.params.side) (refineSite (j := (stepBlockFrame R.params.side n).depth) z))
      = refineSite (j := (stepBlockFrame R.params.side n).depth) z from torusSiteInFrame_toTorusSite _ hm _,
      cellCentre_eq_refineSite]
    have h0' : (siteOfCoords (stepBlockFrame R.params.side n).depth (0 : Fin 4 → ℤ) :
        (stepBlockFrame R.params.side n).Site _) = 0 := by
      funext l
      simp [siteOfCoords]
    rw [h0']
    exact (add_zero _).symm
  rw [h2]
  exact h1
theorem averagedKernel_gaugeTransform (R : StepSetup) (hodd : Odd R.params.side) (hn : 2 ≤ n)
    (hgc : gaugeCovarianceStatement) (g : TorusSite (n * R.params.side) → UnitQuaternion)
    (hg : ∀ x, cellOffset (F := stepBlockFrame R.params.side n)
      (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x) = 0 → g x = 1)
    (W : TorusField (n * R.params.side)) (hW : IsCold R.params.threshold W)
    (hW' : IsCold R.params.threshold (TorusFields.gaugeTransform g W))
    (V : (stepBlockFrame R.params.side n).GaugeField 1) :
    averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0
      (TorusFields.gaugeTransform g W)) V =
      averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W) V := by
  rw [averagedKernel_eq_prod R.params R.coupling _ hW', averagedKernel_eq_prod R.params R.coupling _ hW]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [bondKernel_eq R.params hodd R.coupling _ hW', bondKernel_eq R.params hodd R.coupling _ hW]
  have hpos : 0 < R.params.side := hodd.pos
  have hcov := (hgc (stepBlockFrame R.params.side n) 0 (by simp [BlockFrame.top, stepBlockFrame]) hpos).2.1
    (fun z => g (toTorusSite (n * R.params.side) z)) (readAtLevel (stepBlockFrame R.params.side n) 0 W) c
  have h1 : g (toTorusSite (n * R.params.side) (refineSite (j := 0) c.1)) = 1 :=
    hg _ (cellOffset_refineSite R hodd hn c.1)
  have h2 : g (toTorusSite (n * R.params.side) (refineSite (j := 0) (c.1 + BlockAverages.unitStep 1 c.2))) = 1 :=
    hg _ (cellOffset_refineSite R hodd hn _)
  have hmean : _root_.YangMills.Construction.BlockAverages.contourAverage (j := (stepBlockFrame R.params.side n).depth)
      (readAtLevel (stepBlockFrame R.params.side n) 0 (TorusFields.gaugeTransform g W)) c =
      _root_.YangMills.Construction.BlockAverages.contourAverage (j := (stepBlockFrame R.params.side n).depth)
        (readAtLevel (stepBlockFrame R.params.side n) 0 W) c := by
    rw [readAtLevel_gaugeTransform]
    have hone : ∀ (a b : UnitQuaternion) (X : ℍ[ℝ]), a = 1 → b = 1 →
        (a : ℍ[ℝ]) * X * ((b⁻¹ : UnitQuaternion) : ℍ[ℝ]) = X := by
      rintro _ _ X rfl rfl
      simp
    exact hcov.trans (hone _ _ _ h1 h2)
  rw [hmean]
end Weight
theorem coordNorm_eq_norm (v : EuclideanSpace ℝ (Fin 3)) : coordNorm v = ‖v‖ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coordNorm_eq_norm <;> assumption
section Close
open ChartRepresentation
variable {n : ℕ} [NeZero n]
theorem measurable_cutoffFactor {ρ : ℝ} {p : ℝ → ℝ} (hcut : IsCutoff ρ p) {α : Type} [MeasurableSpace α]
    {f : α → ℝ} (hf : Measurable f) (h0 : ∀ a, 0 ≤ f a) :
    Measurable fun a => cutoffFactor ρ p (f a) := by apply _root_.YangMills.Construction.CoarseMeasurability.measurable_cutoffFactor <;> assumption
theorem cutoffFactor_nonneg (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
theorem measurable_haarLogDensity : Measurable haarLogDensity := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.measurable_haarLogDensity <;> assumption
theorem measurable_cutoffProduct (R : StepSetup) (hcut : IsCutoff R.ballRadius R.barrierFn) (V : TorusField n) :
    Measurable (coldChartSetting R V).cutoffProduct := by
  unfold ChartSetting.cutoffProduct
  refine Finset.measurable_prod _ fun b _ => ?_
  have hc : Continuous fun η : FreeCoords (coldChartSetting R V).free => coordNorm (η b) := by
    have e : (fun η : FreeCoords (coldChartSetting R V).free => coordNorm (η b)) =
        fun η => ‖η b‖ := by
      funext η
      exact coordNorm_eq_norm (η b)
    rw [e]
    exact (continuous_apply b).norm
  exact measurable_cutoffFactor hcut hc.measurable fun η => norm_nonneg _
theorem measurable_haarJacobian (R : StepSetup) (V : TorusField n) :
    Measurable (coldChartSetting R V).haarJacobian := by
  unfold ChartSetting.haarJacobian
  refine Finset.measurable_prod _ fun b _ => ?_
  have hc : Continuous fun η : FreeCoords (coldChartSetting R V).free =>
      toCoords ((coldChartSetting R V).frame b.1) + η b := continuous_const.add (continuous_apply b)
  exact measurable_haarLogDensity.comp hc.measurable
theorem cutoffProduct_nonneg (R : StepSetup) (V : TorusField n) (η : FreeCoords (coldChartSetting R V).free) :
    0 ≤ (coldChartSetting R V).cutoffProduct η :=
  Finset.prod_nonneg fun _ _ => cutoffFactor_nonneg _ _ _
theorem norm_lt_of_cutoffProduct_ne_zero (R : StepSetup) (V : TorusField n)
    (η : FreeCoords (coldChartSetting R V).free)
    (h : (coldChartSetting R V).cutoffProduct η ≠ 0) : ∀ b, ‖η b‖ < R.ballRadius := by
  intro b
  by_contra hb
  apply h
  unfold ChartSetting.cutoffProduct
  refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
  unfold cutoffFactor
  rw [if_neg]
  rwa [coordNorm_eq_norm]
theorem averagedKernel_nonneg (ℓ : _root_.YangMills.Construction.TorusLumps.StepParameters) (x : ℝ) (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (V : (stepBlockFrame ℓ.side n).GaugeField 1) : 0 ≤ averagedKernel ℓ x W V := by
  unfold averagedKernel
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun b _ => Finset.prod_nonneg fun c _ => ?_)
  unfold bondKernel
  exact div_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)
end Close
section Parts
open ChartRepresentation
variable {n : ℕ} [NeZero n]
structure Hypotheses (R : StepSetup) (n : ℕ) [NeZero n] (V : TorusField n) : Prop where
  odd_side : Odd R.params.side
  two_le : 2 ≤ n
  n₀_le : R.params.n₀ ≤ n
  admissible : R.params.Admissible
  expansions : R.HasExpansions
  cutoff : IsCutoff R.ballRadius R.barrierFn
  blockSide : IsBlockTorusSide R.params (n * R.params.side)
  anchor_pos : 0 < R.anchorRadius
  radii_lt_pi : R.anchorRadius + R.ballRadius < Real.pi
  ball_pos : 0 < R.ballRadius
  setting : (coldChartSetting R V).IsAdmissible
  kernelBorel : BondKernelBorel
  covariance : gaugeCovarianceStatement
  potential : PotentialFactorization
  haarCoords : ClusterExpansionOfAStep.HaarInChartCoordinates
variable {R : StepSetup} {V : TorusField n}
def kernelAt (R : StepSetup) (V : TorusField n) (W : TorusField (n * R.params.side)) : ℝ :=
  averagedKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 W)
    (readAtLevel (stepBlockFrame R.params.side n) 1 V)
def weightedKernel (R : StepSetup) (V : TorusField n) (W : TorusField (n * R.params.side)) : ℝ :=
  R.avoidingPart Finset.univ W * kernelAt R V W
theorem measurable_avoidingPart (c : Hypotheses R n V) :
    Measurable fun W : TorusField (n * R.params.side) => R.avoidingPart Finset.univ W := by
  have h := (c.expansions.2.borel (n * R.params.side) c.blockSide ∅).1
  have h2 := h.comp (measurable_id.prodMk (measurable_const (a := emptyLabelling (n := n) R)))
  have e : (fun W : TorusField (n * R.params.side) => R.avoidingPart Finset.univ W) = _ :=
    funext (avoidingPart_univ (n := n) R c.expansions c.blockSide)
  rw [e]
  exact h2
theorem measurable_kernelAt (c : Hypotheses R n V) : Measurable (kernelAt R V) := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := c.kernelBorel R.params R.coupling n
  have h2 : Measurable fun W : TorusField (n * R.params.side) => (W, V) := measurable_id.prodMk measurable_const
  have key : ∀ Fn : TorusField (n * R.params.side) → TorusField n → ℝ,
      Measurable (fun p : TorusField (n * R.params.side) × TorusField n => Fn p.1 p.2) →
      Measurable fun W : TorusField (n * R.params.side) => Fn W V := fun Fn hF => hF.comp h2
  exact key (fun W V' => averagedKernel R.params R.coupling (fineLevelField R.params n W)
    (coarseLevelField R.params n V')) h
theorem weightedKernel_nonneg (W : TorusField (n * R.params.side)) : 0 ≤ weightedKernel R V W :=
  mul_nonneg ENNReal.toReal_nonneg (averagedKernel_nonneg _ _ _ _)
theorem measurable_weightedKernel (c : Hypotheses R n V) : Measurable (weightedKernel R V) :=
  (measurable_avoidingPart c).mul (measurable_kernelAt c)
theorem isCold_gaugeTransform_iff (g : TorusSite (n * R.params.side) → UnitQuaternion)
    (W : TorusField (n * R.params.side)) :
    IsCold R.params.threshold (TorusFields.gaugeTransform g W) ↔ IsCold R.params.threshold W := by
  constructor
  · intro h x μ ν hμ
    have := h x μ ν hμ
    rwa [curvature_gaugeTransform] at this
  · intro h x μ ν hμ
    rw [curvature_gaugeTransform]
    exact h x μ ν hμ
theorem isHullState_empty_iff (c : Hypotheses R n V) (W : TorusField (n * R.params.side)) :
    IsHullState R.params R.range W ∅ ↔ IsCold R.params.threshold W :=
  ⟨isCold_of_isHullState R.params c.admissible c.blockSide.1 R.range W,
    isHullState_of_isCold R.params R.range W⟩
theorem weightedKernel_gaugeTransform (c : Hypotheses R n V) (g : TorusSite (n * R.params.side) → UnitQuaternion)
    (hg : ClusterExpansionOfAStep.IsBlockGauge R.params.side (Finset.univ : Finset (TorusSite n)) g)
    (W : TorusField (n * R.params.side)) :
    weightedKernel R V (TorusFields.gaugeTransform g W) = weightedKernel R V W := by
  unfold weightedKernel
  rw [avoidingPart_univ R c.expansions c.blockSide, avoidingPart_univ R c.expansions c.blockSide]
  by_cases hW : IsCold R.params.threshold W
  · have hW' := (isCold_gaugeTransform_iff g W).2 hW
    rw [if_pos ((isHullState_empty_iff c _).2 hW'), if_pos ((isHullState_empty_iff c _).2 hW)]
    have hd := c.expansions.2.gauge (n * R.params.side) c.blockSide W ∅ (emptyLabelling R) g
      ((isHullState_empty_iff c W).2 hW)
    have hl : R.labels.act ∅ g (emptyLabelling (n := n) R) = emptyLabelling R := Subsingleton.elim _ _
    rw [hl] at hd
    have hk : kernelAt R V (TorusFields.gaugeTransform g W) = kernelAt R V W :=
      averagedKernel_gaugeTransform R c.odd_side c.two_le c.covariance g hg.2 W hW hW' _
    rw [hd, hk]
  · rw [if_neg (fun h => hW ((isCold_gaugeTransform_iff g W).1 ((isHullState_empty_iff c _).1 h))),
      if_neg (fun h => hW ((isHullState_empty_iff c _).1 h)), zero_mul, zero_mul]
theorem glueOver_univ (W : TorusField (n * R.params.side)) : (coldChartSetting R V).glueOver Finset.univ W = W := by
  funext x i
  unfold ChartSetting.glueOver
  by_cases hb1 : (x, i) ∈ (coldChartSetting R V).free
  · rw [if_pos (Or.inl hb1)]
  · refine if_pos (Or.inr ?_)
    have h1 : (x, i) ∉ chartBonds R.params.side n := hb1
    unfold chartBonds at h1
    unfold ClusterExpansionOfAStep.axialTreeBonds
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at h1 ⊢
    exact h1
theorem bondMark_nonneg (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side)) :
    0 ≤ R.bondMark V W b :=
  cutoffFactor_nonneg _ _ _
def markedIntegrand (R : StepSetup) (V : TorusField n) (W : TorusField (n * R.params.side)) : ℝ :=
  weightedKernel R V W * ∏ b ∈ chartBondsInBlocks R.params.side (Finset.univ : Finset (TorusSite n)),
    R.bondMark V W b
theorem markedIntegrand_nonneg (W : TorusField (n * R.params.side)) : 0 ≤ markedIntegrand R V W :=
  mul_nonneg (weightedKernel_nonneg W) (Finset.prod_nonneg fun b _ => bondMark_nonneg W b)
theorem measurable_markedIntegrand (c : Hypotheses R n V) : Measurable (markedIntegrand R V) := by
  have h1 : NeZero (n * R.params.side) := inferInstance
  exact (measurable_weightedKernel c).mul
    (Finset.measurable_prod _ fun b _ => measurable_bondMark R c.cutoff V b)
theorem markedIntegral_eq_toReal (c : Hypotheses R n V) : R.markedIntegral Finset.univ V =
    (∫⁻ W, ENNReal.ofReal (markedIntegrand R V W) ∂(fieldHaar (n * R.params.side))).toReal :=
  integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall markedIntegrand_nonneg)
    (measurable_markedIntegrand c).aestronglyMeasurable
theorem chartBondsInBlocks_univ : chartBondsInBlocks R.params.side (Finset.univ : Finset (TorusSite n)) =
    chartBonds R.params.side n := by
  unfold chartBondsInBlocks
  simp
theorem ofReal_markedIntegrand (W : TorusField (n * R.params.side)) : ENNReal.ofReal (markedIntegrand R V W) =
    ENNReal.ofReal (weightedKernel R V ((coldChartSetting R V).glueOver Finset.univ W)) *
      ∏ b : (coldChartSetting R V).free, ENNReal.ofReal
        ((coldChartSetting R V).bondCutoff ((coldChartSetting R V).glueOver Finset.univ W) b) := by
  rw [glueOver_univ]
  unfold markedIntegrand
  rw [ENNReal.ofReal_mul (weightedKernel_nonneg W),
    ENNReal.ofReal_prod_of_nonneg fun b _ => bondMark_nonneg W b, chartBondsInBlocks_univ]
  congr 1
  exact (Finset.prod_coe_sort (chartBonds R.params.side n)
    fun b => ENNReal.ofReal (R.bondMark V W b)).symm
end Parts
section Right
open ChartRepresentation
variable {n : ℕ} [NeZero n] {R : StepSetup} {V : TorusField n}
theorem inBalls_of_norm_lt (η : FreeCoords (coldChartSetting R V).free) (hη : ∀ b, ‖η b‖ < R.ballRadius) :
    (coldChartSetting R V).InBalls η := fun b => by
  rw [coordNorm_eq_norm]
  exact (hη b).le
theorem functional_trivialField_pos (c : Hypotheses R n V) :
    0 < R.functional (n * R.params.side) (trivialField (n * R.params.side)) := by
  have h0 : (coldChartSetting R V).InBalls (0 : FreeCoords (coldChartSetting R V).free) :=
    inBalls_of_norm_lt 0 fun b => by simpa using c.ball_pos
  exact (c.potential R c.admissible c.expansions c.anchor_pos c.radii_lt_pi n c.n₀_le
    (coldChartSetting R V) c.setting 0 h0).1
def coldIntegrand (R : StepSetup) (V : TorusField n) (η : FreeCoords (coldChartSetting R V).free) : ℝ :=
  (coldChartSetting R V).cutoffProduct η * Real.exp (-(coldChartSetting R V).potential η)
theorem coldIntegrand_nonneg (η : FreeCoords (coldChartSetting R V).free) : 0 ≤ coldIntegrand R V η :=
  mul_nonneg (cutoffProduct_nonneg R V η) (Real.exp_pos _).le
theorem ofReal_weightedKernel_mul (c : Hypotheses R n V) (η : FreeCoords (coldChartSetting R V).free) :
    ENNReal.ofReal (weightedKernel R V ((coldChartSetting R V).field η)) *
        ENNReal.ofReal ((coldChartSetting R V).cutoffProduct η * (coldChartSetting R V).haarJacobian η) =
      ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
        coldIntegrand R V η) := by
  by_cases hc : (coldChartSetting R V).cutoffProduct η = 0
  · simp [hc, coldIntegrand]
  · have hη := inBalls_of_norm_lt η (norm_lt_of_cutoffProduct_ne_zero R V η hc)
    obtain ⟨_, _, _, hid, _⟩ := c.potential R c.admissible c.expansions c.anchor_pos c.radii_lt_pi n c.n₀_le
      (coldChartSetting R V) c.setting η hη
    have hhull : IsHullState R.params R.range ((coldChartSetting R V).field η) ∅ := c.setting.isHull η hη
    have hcold := (isHullState_empty_iff c _).1 hhull
    have hk : kernelAt R V ((coldChartSetting R V).field η) = (coldChartSetting R V).kernelProduct η :=
      averagedKernel_eq_prod R.params R.coupling _ hcold _
    have hlab : (coldChartSetting R V).labelling = emptyLabelling R := by
      funext z
      exact absurd z.2 (Finset.notMem_empty _)
    have hcl : ∏ X ∈ chainComponents R.range (coldChartSetting R V).support,
        R.clusterFactor (n * R.params.side) ((coldChartSetting R V).field η) (coldChartSetting R V).support
          (coldChartSetting R V).labelling X = 1 := by
      have e : chainComponents R.range (coldChartSetting R V).support = ∅ := by
        show chainComponents R.range (∅ : Finset (TorusSite (n * R.params.side))) = ∅
        simp [chainComponents]
      rw [e]
      simp
    rw [hcl, mul_one] at hid
    have hHv : weightedKernel R V ((coldChartSetting R V).field η) =
        R.labelWeight (n * R.params.side) ((coldChartSetting R V).field η) ∅ (emptyLabelling R) *
          (coldChartSetting R V).kernelProduct η := by
      unfold weightedKernel
      rw [avoidingPart_univ R c.expansions c.blockSide, if_pos hhull, hk]
    have hid' : R.labelWeight (n * R.params.side) ((coldChartSetting R V).field η) ∅ (emptyLabelling R) *
        (coldChartSetting R V).kernelProduct η * (coldChartSetting R V).haarJacobian η =
          R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
            Real.exp (-(coldChartSetting R V).potential η) := by
      rw [← hlab]
      exact hid
    rw [← ENNReal.ofReal_mul (weightedKernel_nonneg _), hHv]
    congr 1
    unfold coldIntegrand
    calc _ = (coldChartSetting R V).cutoffProduct η *
          (R.labelWeight (n * R.params.side) ((coldChartSetting R V).field η) ∅ (emptyLabelling R) *
            (coldChartSetting R V).kernelProduct η * (coldChartSetting R V).haarJacobian η) := by ring
      _ = _ := by rw [hid']; ring
theorem measurable_coldIntegrand (c : Hypotheses R n V) : Measurable (coldIntegrand R V) := by
  have hD := functional_trivialField_pos c
  have hMm : Measurable fun η : FreeCoords (coldChartSetting R V).free =>
      ENNReal.ofReal (weightedKernel R V ((coldChartSetting R V).field η)) *
        ENNReal.ofReal ((coldChartSetting R V).cutoffProduct η * (coldChartSetting R V).haarJacobian η) :=
    (ENNReal.measurable_ofReal.comp ((measurable_weightedKernel c).comp
      (ClusterExpansionOfAStep.ChartSetting.measurable_field _))).mul
      (ENNReal.measurable_ofReal.comp ((measurable_cutoffProduct R c.cutoff V).mul (measurable_haarJacobian R V)))
  have e : coldIntegrand R V = fun η => (ENNReal.ofReal (weightedKernel R V ((coldChartSetting R V).field η)) *
      ENNReal.ofReal ((coldChartSetting R V).cutoffProduct η * (coldChartSetting R V).haarJacobian η)).toReal /
      R.functional (n * R.params.side) (trivialField (n * R.params.side)) := by
    funext η
    rw [ofReal_weightedKernel_mul c, ENNReal.toReal_ofReal (mul_nonneg hD.le (coldIntegrand_nonneg η)),
      mul_div_cancel_left₀ _ hD.ne']
  rw [e]
  exact hMm.ennreal_toReal.div_const _
theorem markedIntegral_univ_eq (c : Hypotheses R n V) :
    R.markedIntegral Finset.univ V = coldImageIntegral R V := by
  have hD := functional_trivialField_pos c
  have hchart : (coldChartSetting R V).IsChartCover Finset.univ :=
    ⟨Finset.Subset.refl _, fun b hb1 _ => hb1, fun b _ => rfl⟩
  have hfb := c.haarCoords R c.odd_side c.cutoff n c.two_le (coldChartSetting R V) Finset.univ hchart
    (fun W => ENNReal.ofReal (weightedKernel R V W)) (ENNReal.measurable_ofReal.comp (measurable_weightedKernel c))
    (fun g hg W => by simp only [weightedKernel_gaugeTransform c g hg W])
  have hfin : (∫⁻ η, ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
      coldIntegrand R V η)).toReal =
      ∫ η, R.functional (n * R.params.side) (trivialField (n * R.params.side)) * coldIntegrand R V η :=
    (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun η => mul_nonneg hD.le (coldIntegrand_nonneg η))
      ((measurable_coldIntegrand c).const_mul _).aestronglyMeasurable).symm
  rw [markedIntegral_eq_toReal c, lintegral_congr ofReal_markedIntegrand, hfb,
    lintegral_congr (ofReal_weightedKernel_mul c), hfin, integral_const_mul]
  rfl
end Right
end MarkedIntegralIdentity
open MarkedIntegralIdentity in
theorem fullMarkedIntegralIsColdImage (hfree : ClusterExpansionOfAStep.HaarInChartCoordinates)
    (hker : BondKernelBorel) (hpot : PotentialFactorization)
    (hset : ColdChartSettingIsAdmissible) (hgc : gaugeCovarianceStatement) :
    FullMarkedIntegralIsColdImage := by
  intro T hT
  obtain ⟨y₁, h₁⟩ := hset T hT
  refine ⟨max y₁ T.floorMin, fun y hy R hR _ n _ hn V hV => ?_⟩
  have hy1 : y₁ ≤ y := le_trans (le_max_left _ _) hy
  have hy0 : T.floorMin ≤ y := le_trans (le_max_right _ _) hy
  have hs := h₁ y hy1 R hR n hn V hV
  have hσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hLe : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have hodd : Odd R.params.side := by rw [hLe]; exact hT.L_odd
  have hn₀ : R.params.n₀ ≤ n := by
    have : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
    omega
  have h4096 : 4096 ≤ T.n₀ := hT.n₀_ge
  have hfits : R.params.Admissible := by rw [hR.params_eq]; exact hT.fits y hy0
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have e : R.ballRadius = T.ballRadius := by
      show R.params.threshold / 64 = _
      rw [hσ]
      rfl
    rw [e, hR.barrierFn_eq]
    exact hT.cut
  have hρA : 0 < R.anchorRadius := by rw [hR.anchorRadius_eq]; exact hT.chain.2.2.2.1
  have hρ1 : R.anchorRadius ≤ 1 := by rw [hR.anchorRadius_eq]; exact hT.chain.2.2.2.2.1
  have hρπ : R.anchorRadius + R.ballRadius < Real.pi := by
    have h1 : R.ballRadius = R.params.threshold / 64 := rfl
    have h2 : R.params.threshold ≤ 1 := by rw [hσ]; exact hT.σ_one
    have h3 := Real.pi_gt_three
    linarith
  have hσ0 : 0 < R.ballRadius := by
    show 0 < R.params.threshold / 64
    rw [hσ]
    have := hT.σ_pos
    positivity
  exact markedIntegral_univ_eq
    { odd_side := hodd
      two_le := by omega
      n₀_le := hn₀
      admissible := hfits
      expansions := hR.isStep.1
      cutoff := hcut
      blockSide := ⟨Nat.dvd_mul_left _ _, by rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left _ hn₀⟩
      anchor_pos := hρA
      radii_lt_pi := hρπ
      ball_pos := hσ0
      setting := hs
      kernelBorel := hker
      covariance := hgc
      potential := hpot
      haarCoords := hfree }
end MarkedIntegrals
end YangMills.Construction
end
