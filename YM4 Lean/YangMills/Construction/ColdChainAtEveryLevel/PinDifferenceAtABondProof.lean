import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import YangMills.Construction.ColdChainAtEveryLevel.CurlOfAGapOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.FactsOfTheLogarithm
import YangMills.Construction.ColdChainAtEveryLevel.PinDifferenceAtABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.PinnedBondDifference
variable {F : BlockFrame}
theorem distFromOne_nonneg (a : UnitQuaternion) : 0 ≤ _root_.YangMills.Construction.BlockAverages.distFromOne a := norm_nonneg _
theorem norm_pureComponent_le_distFromOne (g : UnitQuaternion) :
    ‖pureComponent (g : ℍ[ℝ])‖ ≤ _root_.YangMills.Construction.BlockAverages.distFromOne g := by apply _root_.YangMills.Construction.BlockLines.norm_pureComponent_coe_le <;> assumption
theorem norm_pureComponent_mul_sub_le (x y : UnitQuaternion) :
    ‖pureComponent ((x * y : UnitQuaternion) : ℍ[ℝ]) - pureComponent (x : ℍ[ℝ]) - pureComponent (y : ℍ[ℝ])‖ ≤
      _root_.YangMills.Construction.BlockAverages.distFromOne x * _root_.YangMills.Construction.BlockAverages.distFromOne y := by apply _root_.YangMills.Construction.BlockLines.norm_pureComponent_mul_sub_le <;> assumption
theorem pureComponent_coe_inv (g : UnitQuaternion) :
    pureComponent ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = - pureComponent (g : ℍ[ℝ]) := by
  rw [coe_unitQuaternion_inv, pureComponent_star]
theorem pureComponent_coe_conj (a b : UnitQuaternion) :
    pureComponent ((a * b * a⁻¹ : UnitQuaternion) : ℍ[ℝ]) = adjointAction a (pureComponent (b : ℍ[ℝ])) := by
  rw [coe_conj_eq_adjointAction, pureComponent_adjointAction]
theorem norm_pureComponent_mul_conj_sub_le (K1 K2 Vh : UnitQuaternion) (v : ℝ) (hv : _root_.YangMills.Construction.BlockAverages.distFromOne Vh ≤ v) :
    ‖pureComponent ((K1 * (Vh * K2⁻¹ * Vh⁻¹) : UnitQuaternion) : ℍ[ℝ]) -
        (pureComponent (K1 : ℍ[ℝ]) - pureComponent (K2 : ℍ[ℝ]))‖ ≤
      (_root_.YangMills.Construction.BlockAverages.distFromOne K1 + 2 * v) * _root_.YangMills.Construction.BlockAverages.distFromOne K2 := by
  have h1 := norm_pureComponent_mul_sub_le K1 (Vh * K2⁻¹ * Vh⁻¹)
  have s1 : _root_.YangMills.Construction.BlockAverages.distFromOne (Vh * K2⁻¹ * Vh⁻¹) = _root_.YangMills.Construction.BlockAverages.distFromOne K2 := by
    unfold _root_.YangMills.Construction.BlockAverages.distFromOne
    rw [norm_coe_conj_sub_one, norm_coe_inv_sub_one]
  rw [s1] at h1
  have h2 : ‖pureComponent ((Vh * K2⁻¹ * Vh⁻¹ : UnitQuaternion) : ℍ[ℝ]) + pureComponent (K2 : ℍ[ℝ])‖ ≤
      2 * v * _root_.YangMills.Construction.BlockAverages.distFromOne K2 := by
    have e : pureComponent ((Vh * K2⁻¹ * Vh⁻¹ : UnitQuaternion) : ℍ[ℝ]) + pureComponent (K2 : ℍ[ℝ]) =
        -(adjointAction Vh (pureComponent (K2 : ℍ[ℝ])) - pureComponent (K2 : ℍ[ℝ])) := by
      rw [pureComponent_coe_conj, pureComponent_coe_inv, PatchForms.adjointAction_apply_neg]
      abel
    rw [e, norm_neg]
    refine (PatchForms.norm_adjointAction_apply_sub_le _ _).trans ?_
    have hv0 : 0 ≤ v := (_root_.YangMills.Construction.BlockAverages.PinnedBondDifference.distFromOne_nonneg _).trans hv
    exact mul_le_mul (mul_le_mul_of_nonneg_left hv (by norm_num)) (norm_pureComponent_le_distFromOne K2)
      (norm_nonneg _) (by positivity)
  have e : pureComponent ((K1 * (Vh * K2⁻¹ * Vh⁻¹) : UnitQuaternion) : ℍ[ℝ]) -
      (pureComponent (K1 : ℍ[ℝ]) - pureComponent (K2 : ℍ[ℝ])) =
      (pureComponent ((K1 * (Vh * K2⁻¹ * Vh⁻¹) : UnitQuaternion) : ℍ[ℝ]) - pureComponent (K1 : ℍ[ℝ]) -
          pureComponent ((Vh * K2⁻¹ * Vh⁻¹ : UnitQuaternion) : ℍ[ℝ])) +
        (pureComponent ((Vh * K2⁻¹ * Vh⁻¹ : UnitQuaternion) : ℍ[ℝ]) + pureComponent (K2 : ℍ[ℝ])) := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have e2 : (_root_.YangMills.Construction.BlockAverages.distFromOne K1 + 2 * v) * _root_.YangMills.Construction.BlockAverages.distFromOne K2 = _root_.YangMills.Construction.BlockAverages.distFromOne K1 * _root_.YangMills.Construction.BlockAverages.distFromOne K2 + 2 * v * _root_.YangMills.Construction.BlockAverages.distFromOne K2 := by
    ring
  rw [e2]
  exact add_le_add h1 h2
variable {S : Finset F.Cell} {z : F.Cell} {V : F.GaugeField F.top}
theorem norm_pureComponent_gaugedGap_sub_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (W : F.FieldChain) (X : F.FieldChain) (Γ : F.SiteGauge) (γ : LatticeFractionalIntegration.Lattice4 → UnitQuaternion)
    (h0 : Γ 0 = PatchLatticeChart.siteGaugeOfLatticeGauge S V z γ) {a : LatticeFractionalIntegration.Lattice4}
    {i : Fin 4} (ha : a ∈ GaugeMap.patchDomain S z)
    (ha' : a + LatticeFractionalIntegration.basisVector i ∈ GaugeMap.patchDomain S z) :
    ‖pureComponent ((PatchCurls.gaugedGap S V z (X 0) (W 0) γ a i : UnitQuaternion) : ℍ[ℝ]) -
        PatchForms.signedChartForm S z (framedPureDefect S V z W X Γ 0) a i‖ ≤
      2 * _root_.YangMills.Construction.BlockAverages.distFromOne (PatchLatticeChart.framedLatticeField S V z (W 0) a i) *
        _root_.YangMills.Construction.BlockAverages.distFromOne (PatchCurls.gaugedGap S V z (X 0) (W 0) γ a i) := by
  have hg : PatchCurls.gaugedGap S V z (X 0) (W 0) γ a i = _ :=
    PatchLatticeChart.Framing.latticeGaugeTransform_mul_inv_framed (V := V) hamb hodd he γ (X 0) (W 0) ha ha'
  obtain ⟨k1, k2⟩ := PatchForms.patchSite_add_basisVector_cases he a i
  set T := gaugeTransform (PatchLatticeChart.siteGaugeOfLatticeGauge S V z γ) (X 0) with hT
  have hrel : ∀ s k, relativeDefect W X Γ 0 s k = T s k * (W 0 s k)⁻¹ := by
    intro s k
    unfold relativeDefect gaugedChainFields
    rw [h0]
  rcases he i with h | h
  · have e1 : PatchForms.signedChartForm S z (framedPureDefect S V z W X Γ 0) a i =
        framedPureDefect S V z W X Γ 0 (GaugeMap.patchSite S z a) i := by
      simp [PatchForms.signedChartForm, h]
    have e2 : pureComponent ((PatchCurls.gaugedGap S V z (X 0) (W 0) γ a i : UnitQuaternion) : ℍ[ℝ]) =
        framedPureDefect S V z W X Γ 0 (GaugeMap.patchSite S z a) i := by
      unfold framedPureDefect
      rw [PatchLatticeChart.Framing.baseSite_eq_self, hrel, hg]
      have e3 : PatchLatticeChart.latticeField S z T a i * (PatchLatticeChart.latticeField S z (W 0) a i)⁻¹ =
          T (GaugeMap.patchSite S z a) i * (W 0 (GaugeMap.patchSite S z a) i)⁻¹ := by
        simp [PatchLatticeChart.latticeField, h]
      rw [e3]
      have e4 : (GaugeMap.frameChange S V z (GaugeMap.patchSite S z a))⁻¹ *
          (T (GaugeMap.patchSite S z a) i * (W 0 (GaugeMap.patchSite S z a) i)⁻¹) *
          GaugeMap.frameChange S V z (GaugeMap.patchSite S z a) =
          (GaugeMap.frameChange S V z (GaugeMap.patchSite S z a))⁻¹ *
          (T (GaugeMap.patchSite S z a) i * (W 0 (GaugeMap.patchSite S z a) i)⁻¹) *
          ((GaugeMap.frameChange S V z (GaugeMap.patchSite S z a))⁻¹)⁻¹ := by group
      rw [e4, pureComponent_coe_conj]
    rw [e1, e2, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (_root_.YangMills.Construction.BlockAverages.PinnedBondDifference.distFromOne_nonneg _)) (_root_.YangMills.Construction.BlockAverages.PinnedBondDifference.distFromOne_nonneg _)
  · have hne : closedOrthant S z i ≠ 1 := by rw [h]; norm_num
    set s' := GaugeMap.patchSite S z (a + LatticeFractionalIntegration.basisVector i) with hs'
    set f' := GaugeMap.frameChange S V z s' with hf'
    set fa := GaugeMap.frameChange S V z (GaugeMap.patchSite S z a) with hfa
    set w := W 0 s' i with hw
    set t := T s' i with ht
    have e1 : PatchForms.signedChartForm S z (framedPureDefect S V z W X Γ 0) a i =
        - framedPureDefect S V z W X Γ 0 s' i := by
      simp [PatchForms.signedChartForm, hne, hs']
    set p := f'⁻¹ * (t * w⁻¹)⁻¹ * (f'⁻¹)⁻¹ with hp
    have ew : PatchLatticeChart.framedLatticeField S V z (W 0) a i = fa⁻¹ * w⁻¹ * f' := by
      simp [PatchLatticeChart.framedLatticeField, PatchLatticeChart.latticeField, hne, hfa, hf', hs', hw]
    have eg : PatchCurls.gaugedGap S V z (X 0) (W 0) γ a i = (fa⁻¹ * w⁻¹ * f') * p * (fa⁻¹ * w⁻¹ * f')⁻¹ := by
      rw [hg]
      have e3 : PatchLatticeChart.latticeField S z T a i * (PatchLatticeChart.latticeField S z (W 0) a i)⁻¹ =
          t⁻¹ * (w⁻¹)⁻¹ := by
        simp [PatchLatticeChart.latticeField, hne, ht, hw, hs']
      rw [e3, hp]
      group
    have epp : pureComponent (p : ℍ[ℝ]) = - framedPureDefect S V z W X Γ 0 s' i := by
      unfold framedPureDefect
      rw [PatchLatticeChart.Framing.baseSite_eq_self, hrel, hp, pureComponent_coe_conj, pureComponent_coe_inv,
        PatchForms.adjointAction_apply_neg]
    rw [e1, ← epp]
    rw [← ew] at eg
    have hsz : _root_.YangMills.Construction.BlockAverages.distFromOne (PatchCurls.gaugedGap S V z (X 0) (W 0) γ a i) = _root_.YangMills.Construction.BlockAverages.distFromOne p := by
      rw [eg]
      exact norm_coe_conj_sub_one _ _
    rw [hsz, eg, pureComponent_coe_conj]
    refine (PatchForms.norm_adjointAction_apply_sub_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_pureComponent_le_distFromOne p)
      (mul_nonneg (by norm_num) (_root_.YangMills.Construction.BlockAverages.PinnedBondDifference.distFromOne_nonneg _))
theorem latticeFormAtSites_signedChartForm (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (t : F.Site 0) (i : Fin 4) :
    latticeFormAtSites S z (PatchForms.signedChartForm S z f) t i = f t i := by
  unfold latticeFormAtSites PatchForms.signedChartForm
  rcases he i with h | h
  · simp only [h, if_true, PatchPoints.patchSite_patchChart he]
  · have hne : closedOrthant S z i ≠ 1 := by rw [h]; norm_num
    simp only [if_neg hne]
    have e := (PatchForms.patchSite_add_basisVector_cases he (GaugeMap.patchChart S z (t + unitStep 0 i)) i).2 h
    rw [PatchPoints.patchSite_patchChart he] at e
    have e2 : GaugeMap.patchSite S z (GaugeMap.patchChart S z (t + unitStep 0 i) +
        LatticeFractionalIntegration.basisVector i) = t := (add_right_cancel e).symm
    rw [e2, neg_neg]
theorem sum_mul_le_sum_mul_sum {ι : Type} (s : Finset ι) (u v : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    ∑ i ∈ s, u i * v i ≤ (∑ i ∈ s, u i) * ∑ i ∈ s, v i := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hu i)
  exact Finset.single_le_sum (fun j _ => hv j) hi
set_option maxHeartbeats 2000000 in
theorem pinnedBondDifference : pinnedBondDifferenceStatement := by
  classical
  intro C₃ n₀ F m S V W kW X k γ z y y' B v hC₃ hodd hamb hm hreg hz hy hy' hadj hXW hcells hlev hB hv
  obtain ⟨hs, -⟩ := closedOrthant_spec hreg (by omega : 32 ≤ m) z
  set D := pinnedGaugeDataOfPatch S V z W kW X k with hD
  set Γ := pinnedGaugeOfBase W kW X k (PatchLatticeChart.siteGaugeOfLatticeGauge S V z γ) with hΓ
  set i := hadj.choose with hi
  have hyi : y' = y + unitStep F.top i := hadj.choose_spec
  have hbond : (y, i) ∈ innerBonds (patchCells S z) F.top := Finset.mem_filter.2
    ⟨Finset.mem_product.2 ⟨mem_sitesOfCells_top.2 hy, Finset.mem_univ _⟩, by
      show y + unitStep F.top i ∈ _
      rw [← hyi]
      exact mem_sitesOfCells_top.2 hy'⟩
  have hbond' : (y, i) ∈ patchInnerBonds S z F.top := by
    rw [← innerBonds_patchCells hamb hodd hs le_rfl]
    exact hbond
  set f := framedPureDefect S V z W X Γ 0 with hf
  set ν := PatchForms.signedChartForm S z f with hν
  set u := D.defectForm γ with hu
  have hAv : ∀ g, D.bondAverage y y' g = iteratedBlockAverage (latticeFormAtSites S z g) F.top y i := by
    intro g
    show lineAverage S z y y' g = _
    unfold lineAverage
    rw [dif_pos hadj]
  have hadj' : D.Adj y y' := hadj
  have h1 : iteratedBlockAverage f F.top y i = D.bondAverage y y' ν := by
    rw [hAv]
    exact hlev f (latticeFormAtSites S z ν) (fun b _ => (latticeFormAtSites_signedChartForm hs f b.1 b.2).symm)
      (y, i) hbond'
  have h2 : D.bondAverage y y' u = D.bondAverage y y' ν + D.bondAverage y y' (u - ν) := by
    rw [← hcells.average_add y hy y' hy' hadj', add_sub_cancel]
  refine ⟨‖D.bondAverage y y' (u - ν)‖, norm_nonneg _, ?_, ?_⟩
  · refine (hcells.average_pow_le y hy y' hy' hadj' (u - ν)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₃
    have hterm : ∀ b ∈ LatticeFractionalIntegration.bondsOf (GaugeMap.patchDomain S z), ‖(u - ν) b.1 b.2‖ ^ 4 ≤
        16 * (‖((PatchLatticeChart.framedLatticeField S V z (W 0) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 *
          ‖((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4) := by
      intro b hb
      have hb' := Finset.mem_filter.1 hb
      have hg := norm_pureComponent_gaugedGap_sub_le (V := V) hamb hodd hs W X Γ γ rfl
        (Finset.mem_product.1 hb'.1).1 hb'.2
      have h3 := pow_le_pow_left₀ (norm_nonneg _) hg 4
      refine h3.trans (le_of_eq ?_)
      show (2 * ‖((PatchLatticeChart.framedLatticeField S V z (W 0) b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ *
        ‖((D.defect γ b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖) ^ 4 = _
      ring
    have h4 := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at h4
    refine h4.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact sum_mul_le_sum_mul_sum _ _ _ (fun _ => by positivity) (fun _ => by positivity)
  · set K := topCorrection W kW X k Γ with hK
    set fy := patchFrame S V z y with hfy
    set fy' := patchFrame S V z y' with hfy'
    set K1 := pinnedTopCorrection S V z W kW X k γ y with hK1
    set K2 := pinnedTopCorrection S V z W kW X k γ y' with hK2
    set Vh := fy⁻¹ * W F.top y i * fy' with hVh
    have hVv : _root_.YangMills.Construction.BlockAverages.distFromOne Vh ≤ v := by
      have h5 := hv (y, i) hbond
      have e5 : patchFrame S V z (y + unitStep F.top i) = fy' := by rw [hfy', hyi]
      simp only [] at h5
      rw [e5] at h5
      exact h5
    have htop : topDefect W kW X k Γ y i = K y * W F.top y i * (K y')⁻¹ * (W F.top y i)⁻¹ := by
      unfold topDefect framedUpperField
      rw [dif_pos rfl]
      simp only [gaugeTransform, hXW, hyi]
      rfl
    have hframe : adjointAction (GaugeMap.frameChange S V z (baseSite y))⁻¹
        (pureComponent ((topDefect W kW X k Γ y i : UnitQuaternion) : ℍ[ℝ])) =
        pureComponent ((K1 * (Vh * K2⁻¹ * Vh⁻¹) : UnitQuaternion) : ℍ[ℝ]) := by
      rw [← pureComponent_coe_conj, htop]
      congr 2
      simp only [hK1, hK2, hVh, pinnedTopCorrection, hfy, hfy', ← hΓ, ← hK]
      show _ = (patchFrame S V z y)⁻¹ * K y * _ * _
      unfold patchFrame
      group
    have hc := norm_pureComponent_mul_conj_sub_le K1 K2 Vh v hVv
    have hb := hB (y, i) hbond'
    simp only [] at hb
    rw [hframe] at hb
    have e : pureComponent (K1 : ℍ[ℝ]) - pureComponent (K2 : ℍ[ℝ]) - D.bondAverage y y' u =
        -(pureComponent ((K1 * (Vh * K2⁻¹ * Vh⁻¹) : UnitQuaternion) : ℍ[ℝ]) -
            (pureComponent (K1 : ℍ[ℝ]) - pureComponent (K2 : ℍ[ℝ]))) +
          (pureComponent ((K1 * (Vh * K2⁻¹ * Vh⁻¹) : UnitQuaternion) : ℍ[ℝ]) - iteratedBlockAverage f F.top y i) -
          D.bondAverage y y' (u - ν) := by
      rw [h2, h1]
      abel
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
    rw [norm_neg, add_comm]
    exact add_le_add hb hc
end YangMills.Construction.BlockAverages.PinnedBondDifference
end
