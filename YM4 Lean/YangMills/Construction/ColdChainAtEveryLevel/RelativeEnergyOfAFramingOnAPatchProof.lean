import YangMills.Construction.ColdChainAtEveryLevel.MisfitsOfAFraming
import YangMills.Construction.ColdChainAtEveryLevel.OneStepOfAFraming
import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheCriticalChainOnAPatchProof
import YangMills.Construction.ColdChainAtEveryLevel.RelativeEnergyOfAFramingOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.SizesAtAGoodCell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace PinnedGaugeRelativeEnergy
open BlockLines PatchLocality BondHull
variable {F : BlockFrame}
theorem sum_biUnion_le_sum_sum {ι α : Type} (s : Finset ι) (t : ι → Finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    [DecidableEq α] : ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by apply _root_.YangMills.Construction.BlockAverages.PatchRates.sum_biUnion_le_sum_sum <;> assumption
theorem baseSite_of_level_zero (x : F.Site 0) : baseSite x = x := by apply _root_.YangMills.Construction.CellBumps.baseSite_zero <;> assumption
theorem norm_im_sq_and_distFromOne_sq (g : UnitQuaternion) : ‖((g : ℍ[ℝ])).im‖ ^ 2 ≤ _root_.YangMills.Construction.BlockAverages.distFromOne g ^ 2 ∧
    (0 ≤ ((g : ℍ[ℝ])).re → _root_.YangMills.Construction.BlockAverages.distFromOne g ^ 2 ≤ 2 * ‖((g : ℍ[ℝ])).im‖ ^ 2) := by
  have h1 : _root_.YangMills.Construction.BlockAverages.distFromOne g ^ 2 = 2 - 2 * ((g : ℍ[ℝ])).re := _root_.YangMills.Construction.BlockAverages.distFromOne_sq g
  have h2 : ‖(g : ℍ[ℝ])‖ = 1 := _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion g
  have h3 : Quaternion.normSq (g : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, h2]
    norm_num
  have h4 : ‖((g : ℍ[ℝ])).im‖ ^ 2 = 1 - ((g : ℍ[ℝ])).re ^ 2 := by
    have e : ‖((g : ℍ[ℝ])).im‖ ^ 2 = Quaternion.normSq ((g : ℍ[ℝ])).im := by
      rw [Quaternion.normSq_eq_norm_mul_self]
      ring
    rw [e]
    rw [Quaternion.normSq_def'] at h3 ⊢
    simp only [Quaternion.re_im, Quaternion.imI_im, Quaternion.imJ_im, Quaternion.imK_im]
    nlinarith
  rw [h1, h4]
  constructor
  · nlinarith
  · intro h
    nlinarith
theorem exists_patchCell_baseDistance_le {S : Finset F.Cell} {z : F.Cell} (hodd : Odd F.blockSide) {j : ℕ}
    (hj : j ≤ F.top) {x : F.Site j} (hx : x ∈ sitesOfCells (patchCells S z) j) :
    ∃ y ∈ patchCells S z, baseDistance x (cellCentre 0 y) ≤ F.blockSide ^ F.top := by
  obtain ⟨y, hy, h', hh', e⟩ := exists_cell_of_mem_sitesOfCells hodd hj hx (zero_mem_centredCube hodd.pow)
  rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_zero, add_zero] at e
  refine ⟨y, hy, ?_⟩
  unfold baseDistance
  refine Finset.sup_le fun i _ => ?_
  rw [e, add_sub_cancel_left]
  refine (PatchPoints.natAbs_valMinAbs_intCast_le _ (h' i)).trans ?_
  have h3 := abs_le_of_mem_centredCube (pow_pos hodd.pos _) hh' i
  rw [Int.abs_eq_natAbs] at h3
  exact_mod_cast h3
section Sums
variable {a θ del Ca C₁ s : ℝ} {S : Finset F.Cell} {V V' : F.GaugeField F.top} {U : ChainChart F} {z : F.Cell}
open Classical in
def plaquettesNear (S : Finset F.Cell) (p : F.Site 0) (r : ℝ) : Finset (F.Site 0 × Fin 4 × Fin 4) :=
  (innerPlaquettes S 0).filter (fun q => (baseDistance q.1 p : ℝ) ≤ r)
open Classical in
def bondsNear (S : Finset F.Cell) (j : ℕ) (p : F.Site 0) (r : ℝ) : Finset (F.Site (j + 1) × Fin 4) :=
  (innerBonds S (j + 1)).filter (fun c => (baseDistance c.1 p : ℝ) ≤ r)
theorem sum_patchPlaquettes_norm_im_sq_le (hcrit : IsCriticalChainOverTop a θ del Ca C₁ s S V V' U)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) :
    ∑ q ∈ patchPlaquettes S z,
        ‖((plaquetteHolonomy (chartField (referenceFieldChain S V) U 0) q : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 ≤
      47 ^ 4 * (C₁ * s) ^ 2 := by
  classical
  have hL1 : 1 ≤ F.blockSide := hodd.pos
  have hLR : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL1
  set r : ℝ := (F.blockSide : ℝ) ^ F.top with hr
  have hr1 : 1 ≤ r := one_le_pow₀ hLR
  set g : F.Site 0 × Fin 4 × Fin 4 → ℝ := fun q =>
    ‖((plaquetteHolonomy (chartField (referenceFieldChain S V) U 0) q : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 with hg
  have hg0 : ∀ q, 0 ≤ g q := fun q => by positivity
  have hsub : patchPlaquettes S z ⊆ (patchCells S z).biUnion fun y => plaquettesNear S (cellCentre 0 y) r := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
    have hc : q.1 ∈ plaquetteCorners q := by simp [plaquetteCorners]
    have h1 : q.1 ∈ sitesOfCells S 0 := (Finset.mem_filter.1 hq1).2.2 hc
    have h2 : q.1 ∈ patchBaseSites S z := hq2 hc
    have h3 : q.1 ∈ sitesOfCells (patchCells S z) 0 :=
      (mem_sitesOfCells_patchCells_iff hamb hodd he (Nat.zero_le _)).2 ⟨h1, by rwa [baseSite_of_level_zero]⟩
    obtain ⟨y, hy, hd⟩ := exists_patchCell_baseDistance_le hodd (Nat.zero_le _) h3
    refine Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_filter.2 ⟨hq1, ?_⟩⟩
    rw [hr]
    exact_mod_cast hd
  calc ∑ q ∈ patchPlaquettes S z, g q
      ≤ ∑ q ∈ (patchCells S z).biUnion fun y => plaquettesNear S (cellCentre 0 y) r, g q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hg0 b
    _ ≤ ∑ y ∈ patchCells S z, ∑ q ∈ plaquettesNear S (cellCentre 0 y) r, g q :=
        sum_biUnion_le_sum_sum _ _ _ hg0
    _ ≤ ∑ _y ∈ patchCells S z, (C₁ * s) ^ 2 := by
        refine Finset.sum_le_sum fun y _ => ?_
        have h1 := (hcrit.curvature_and_misfits (cellCentre 0 y) r hr1 le_rfl).1
        have e3 : r / (F.blockSide : ℝ) ^ F.top = 1 := by
          rw [hr]
          exact div_self (by positivity)
        rw [e3, Real.one_rpow, mul_one] at h1
        exact h1
    _ = ((patchCells S z).card : ℝ) * (C₁ * s) ^ 2 := by simp
    _ ≤ 47 ^ 4 * (C₁ * s) ^ 2 := by
        have h2 : ((patchCells S z).card : ℝ) ≤ 47 ^ 4 := by
          exact_mod_cast card_patchCells_le hamb hodd he
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
theorem mem_innerBonds_of_mem_patchFitBonds (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ}
    (hj : j + 1 ≤ F.top) {c : F.Site (j + 1) × Fin 4} (hc : c ∈ patchFitBonds S z j) :
    c ∈ innerBonds (patchCells S z) (j + 1) := by
  classical
  obtain ⟨hb, hf⟩ := Finset.mem_filter.1 hc
  obtain ⟨h1, h2⟩ := hf 0 (zero_mem_centredCube hodd.pow)
  rw [_root_.YangMills.Construction.BlockAverages.siteOfCoords_zero, add_zero] at h1 h2
  rw [innerBonds_patchCells hamb hodd he hj]
  exact Finset.mem_filter.2 ⟨hb, h1, h2⟩
theorem sum_patchFitBonds_misfit_sq_le (hcrit : IsCriticalChainOverTop a θ del Ca C₁ s S V V' U)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) :
    ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j,
        _root_.YangMills.Construction.BlockAverages.distFromOne (chartBondMisfit (referenceFieldChain S V) U V' j c) ^ 2 ≤ 47 ^ 4 * (C₁ * s) ^ 2 := by
  classical
  have hL1 : 1 ≤ F.blockSide := hodd.pos
  have hLR : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL1
  set r : ℝ := (F.blockSide : ℝ) ^ F.top with hr
  have hr1 : 1 ≤ r := one_le_pow₀ hLR
  set g : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℝ := fun j c =>
    _root_.YangMills.Construction.BlockAverages.distFromOne (chartBondMisfit (referenceFieldChain S V) U V' j c) ^ 2 with hg
  have hg0 : ∀ j c, 0 ≤ g j c := fun j c => by positivity
  have hone : ∀ j, j < F.top → ∑ c ∈ patchFitBonds S z j, g j c ≤
      ∑ y ∈ patchCells S z, ∑ c ∈ bondsNear S j (cellCentre 0 y) r, g j c := by
    intro j hj
    have hsub : patchFitBonds S z j ⊆ (patchCells S z).biUnion fun y => bondsNear S j (cellCentre 0 y) r := by
      intro c hc
      have h1 := mem_innerBonds_of_mem_patchFitBonds hamb hodd he hj hc
      have h2 : c.1 ∈ sitesOfCells (patchCells S z) (j + 1) :=
        (Finset.mem_product.1 (Finset.mem_filter.1 h1).1).1
      obtain ⟨y, hy, hd⟩ := exists_patchCell_baseDistance_le hodd hj h2
      refine Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hc).1, ?_⟩⟩
      rw [hr]
      exact_mod_cast hd
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hg0 j b).trans
      (sum_biUnion_le_sum_sum _ _ _ (hg0 j))
  calc ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j, g j c
      ≤ ∑ j ∈ Finset.range F.top, ∑ y ∈ patchCells S z, ∑ c ∈ bondsNear S j (cellCentre 0 y) r, g j c :=
        Finset.sum_le_sum fun j hj => hone j (Finset.mem_range.1 hj)
    _ = ∑ y ∈ patchCells S z, ∑ j ∈ Finset.range F.top, ∑ c ∈ bondsNear S j (cellCentre 0 y) r, g j c :=
        Finset.sum_comm
    _ ≤ ∑ _y ∈ patchCells S z, (C₁ * s) ^ 2 := by
        refine Finset.sum_le_sum fun y _ => ?_
        have h1 := (hcrit.curvature_and_misfits (cellCentre 0 y) r hr1 le_rfl).2
        have e3 : r / (F.blockSide : ℝ) ^ F.top = 1 := by
          rw [hr]
          exact div_self (by positivity)
        rw [e3, Real.one_rpow, mul_one] at h1
        have hfil : (Finset.range F.top).filter (fun j => (F.blockSide : ℝ) ^ (j + 1) ≤ r) =
            Finset.range F.top := by
          refine Finset.filter_true_of_mem fun j hj => ?_
          exact pow_le_pow_right₀ hLR (Finset.mem_range.1 hj)
        unfold localMisfitSum at h1
        rw [hfil] at h1
        exact h1
    _ = ((patchCells S z).card : ℝ) * (C₁ * s) ^ 2 := by simp
    _ ≤ 47 ^ 4 * (C₁ * s) ^ 2 := by
        have h2 : ((patchCells S z).card : ℝ) ≤ 47 ^ 4 := by
          exact_mod_cast card_patchCells_le hamb hodd he
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
end Sums
theorem distFromOne_plaquetteHolonomy_le (Y : F.GaugeField 0) (q : F.Site 0 × Fin 4 × Fin 4) (t : ℝ)
    (h1 : _root_.YangMills.Construction.BlockAverages.distFromOne (Y q.1 q.2.1) ≤ t) (h2 : _root_.YangMills.Construction.BlockAverages.distFromOne (Y (q.1 + unitStep 0 q.2.1) q.2.2) ≤ t)
    (h3 : _root_.YangMills.Construction.BlockAverages.distFromOne (Y (q.1 + unitStep 0 q.2.2) q.2.1) ≤ t) (h4 : _root_.YangMills.Construction.BlockAverages.distFromOne (Y q.1 q.2.2) ≤ t) :
    _root_.YangMills.Construction.BlockAverages.distFromOne (plaquetteHolonomy Y q) ≤ 4 * t := by
  have e : plaquetteHolonomy Y q = Y q.1 q.2.1 * (Y (q.1 + unitStep 0 q.2.1) q.2.2 *
      ((Y (q.1 + unitStep 0 q.2.2) q.2.1)⁻¹ * (Y q.1 q.2.2)⁻¹)) := by
    have a1 : q.1 + unitStep 0 q.2.1 + unitStep 0 q.2.2 + -unitStep 0 q.2.1 - unitStep 0 q.2.1 +
        unitStep 0 q.2.1 = q.1 + unitStep 0 q.2.2 := by abel
    have a2 : q.1 + unitStep 0 q.2.1 + unitStep 0 q.2.2 - unitStep 0 q.2.1 = q.1 + unitStep 0 q.2.2 := by abel
    have a3 : q.1 + unitStep 0 q.2.1 + unitStep 0 q.2.2 + -unitStep 0 q.2.1 - unitStep 0 q.2.2 = q.1 := by abel
    simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
      if_false, mul_one]
    rw [a2, a3]
  rw [e]
  have b1 := _root_.YangMills.Construction.BondHull.distFromOne_mul_le (Y q.1 q.2.1) (Y (q.1 + unitStep 0 q.2.1) q.2.2 *
      ((Y (q.1 + unitStep 0 q.2.2) q.2.1)⁻¹ * (Y q.1 q.2.2)⁻¹))
  have b2 := _root_.YangMills.Construction.BondHull.distFromOne_mul_le (Y (q.1 + unitStep 0 q.2.1) q.2.2)
      ((Y (q.1 + unitStep 0 q.2.2) q.2.1)⁻¹ * (Y q.1 q.2.2)⁻¹)
  have b3 := _root_.YangMills.Construction.BondHull.distFromOne_mul_le (Y (q.1 + unitStep 0 q.2.2) q.2.1)⁻¹ (Y q.1 q.2.2)⁻¹
  rw [_root_.YangMills.Construction.BondHull.distFromOne_inv, _root_.YangMills.Construction.BondHull.distFromOne_inv] at b3
  linarith
end PinnedGaugeRelativeEnergy
set_option maxHeartbeats 1600000 in
open PinnedGaugeRelativeEnergy BlockLines PatchLocality BondHull in
theorem pinnedGaugeRelativeEnergyStatement_proof (hS : lowCostPatchBoundsStatement)
    (hR : criticalChainPatchRatesStatement) (hM : gaugedMisfitNormStatement)
    (hG : gaugeCovarianceStatement) : pinnedGaugeRelativeEnergyStatement := by
  intro a θ del Ca ha hθ hθ' hd hd' hCa
  obtain ⟨LS, hSz⟩ := hS a ha
  obtain ⟨LR, hRt⟩ := hR a θ del Ca ha hθ hθ' hd hd' hCa
  refine ⟨max LS LR, fun L hLodd hLL C₁ hC₁ => ?_⟩
  have hLS : LS ≤ L := le_trans (le_max_left _ _) hLL
  have hLRl : LR ≤ L := le_trans (le_max_right _ _) hLL
  obtain ⟨cS, hcS, hSz'⟩ := hSz L hLodd hLS
  obtain ⟨Cr, cr, hCr, hcr, hRt'⟩ := hRt L hLodd hLRl C₁ hC₁
  refine ⟨cS, hcS, fun e0 he0 he0c => ?_⟩
  set Z : ℝ := (2 + a) * (47 ^ 2 * C₁) with hZ
  have hZp : 0 < Z := by positivity
  refine ⟨min cr (min (1 / (4 * Cr)) (e0 / Z)), lt_min hcr (lt_min (by positivity) (by positivity)), ?_⟩
  intro F m S hFL hamb hm hreg s V v hs hsσ hcold U hcrit X k z hz hterms γ
  subst hFL
  have hodd : Odd F.blockSide := hLodd
  have hscr : s ≤ cr := hsσ.trans (min_le_left _ _)
  have hs4 : 4 * (Cr * s) ≤ 1 := by
    have h1 : s ≤ 1 / (4 * Cr) := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hsZ : Z * s ≤ e0 := by
    have h1 : s ≤ e0 / Z := hsσ.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ hZp] at h1
    linarith
  obtain ⟨he, -⟩ := closedOrthant_spec hreg (by omega) z
  obtain ⟨-, -, hframe⟩ := hRt' F m S rfl hamb hm hreg s V v hs hscr hcold U hcrit z hz
  obtain ⟨sz1, sz2, sz3⟩ := hSz' e0 he0 he0c F m S rfl hamb hm hreg X k z hz hterms
  have h0n : 0 < F.top := Nat.succ_pos _
  have hWj : criticalFieldChain S V v U 0 = chartField (referenceFieldChain S V) U 0 := by
    unfold criticalFieldChain chartChain
    exact Function.update_of_ne h0n.ne _ _
  have hcurv := sum_patchPlaquettes_norm_im_sq_le (z := z) hcrit hamb hodd he
  have hmtot := sum_patchFitBonds_misfit_sq_le (z := z) (V' := rotatedField v V) hcrit hamb hodd he
  set W := criticalFieldChain S V v U with hW
  set kW := criticalGauge S V U with hkW
  set Γ := pinnedGaugeOfBase W kW X k γ with hΓ
  have htop : ∀ y, Γ F.top y = 1 := pinnedGaugeOfBase_top W kW X k γ
  have hbal : ∀ j', j' + 1 < F.top → ∀ y,
      gaugedLink k Γ j' y = balancedLinkAgainst W kW (gaugedChainFields X Γ) j' y :=
    fun j' hj' y => gaugedLink_pinnedGaugeOfBase W kW X k γ hj' y
  obtain ⟨-, -, hcovp, -⟩ := hG F 0 h0n hodd.pos
  rw [← hWj] at hcurv
  set φ : F.Site 0 → UnitQuaternion := fun x => (patchFrame S V z x)⁻¹ with hφ
  have hbond : ∀ b ∈ patchInnerBonds S z 0, _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform φ (W 0) b.1 b.2) ≤ Cr * s := by
    intro b hb
    have h1 := hframe 0 h0n
    rw [innerBonds_patchCells hamb hodd he (Nat.zero_le _)] at h1
    have h2 := Finset.single_le_sum
      (f := fun b : F.Site 0 × Fin 4 => _root_.YangMills.Construction.BlockAverages.distFromOne (gaugeTransform φ (W 0) b.1 b.2) ^ 4)
      (fun b _ => pow_nonneg (_root_.YangMills.Construction.BondHull.distFromOne_nonneg _) 4) hb
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) (h2.trans h1)
  have hplW : ∀ q ∈ patchPlaquettes S z, _root_.YangMills.Construction.BlockAverages.distFromOne (plaquetteHolonomy (W 0) q) ^ 2 ≤
      2 * ‖((plaquetteHolonomy (W 0) q : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
    have hcS := (Finset.mem_filter.1 hq1).2.2
    have mem_of : ∀ x i, x ∈ plaquetteCorners q → x + unitStep 0 i ∈ plaquetteCorners q →
        (x, i) ∈ patchInnerBonds S z 0 := by
      intro x i h1 h2
      refine Finset.mem_filter.2
        ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hcS h1, Finset.mem_univ _⟩, hcS h2⟩, ?_, ?_⟩
      · rw [baseSite_of_level_zero]
        exact hq2 h1
      · rw [baseSite_of_level_zero]
        exact hq2 h2
    have c1 : q.1 ∈ plaquetteCorners q := by simp [plaquetteCorners]
    have c2 : q.1 + unitStep 0 q.2.1 ∈ plaquetteCorners q := by simp [plaquetteCorners]
    have c3 : q.1 + unitStep 0 q.2.2 ∈ plaquetteCorners q := by simp [plaquetteCorners]
    have c4 : q.1 + unitStep 0 q.2.1 + unitStep 0 q.2.2 ∈ plaquetteCorners q := by simp [plaquetteCorners]
    have c5 : q.1 + unitStep 0 q.2.2 + unitStep 0 q.2.1 ∈ plaquetteCorners q := by
      have : q.1 + unitStep 0 q.2.2 + unitStep 0 q.2.1 = q.1 + unitStep 0 q.2.1 + unitStep 0 q.2.2 := by abel
      rw [this]
      exact c4
    have hs1 := _root_.YangMills.Construction.BlockAverages.PinnedGaugeRelativeEnergy.distFromOne_plaquetteHolonomy_le (gaugeTransform φ (W 0)) q (Cr * s)
      (hbond (q.1, q.2.1) (mem_of _ _ c1 c2))
      (hbond (q.1 + unitStep 0 q.2.1, q.2.2) (mem_of _ _ c2 c4))
      (hbond (q.1 + unitStep 0 q.2.2, q.2.1) (mem_of _ _ c3 c5)) (hbond (q.1, q.2.2) (mem_of _ _ c1 c3))
    rw [hcovp φ (W 0) q, _root_.YangMills.Construction.BondHull.distFromOne_conj] at hs1
    exact (norm_im_sq_and_distFromOne_sq _).2 (re_nonneg_of_norm_sub_one_le _ (hs1.trans hs4))
  set pm : (j : ℕ) → F.Site (j + 1) × Fin 4 → UnitQuaternion := fun j c =>
    bondMisfit (gaugedChainFields X Γ j) (balancedLinkAgainst W kW (gaugedChainFields X Γ) j)
        (framedUpperField W kW X k Γ j) c *
      (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)⁻¹ with hpm
  set own : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℝ := fun j c =>
    _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (X j) (k (j + 1)) (X (j + 1)) c) with hown
  set ms : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℝ := fun j c =>
    _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) with hms
  have hmtot' : ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j, ms j c ^ 2 ≤
      47 ^ 4 * (C₁ * s) ^ 2 := hmtot
  have hpt : ∀ j, j < F.top → ∀ c ∈ patchFitBonds S z j,
      ‖((pm j c : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 ≤ 2 * (own j c ^ 2 + ms j c ^ 2) := by
    intro j hj c hc
    have h1 : gaugedContourAverage (X j) (k (j + 1)) c ≠ 0 := by
      intro h0
      have := sz1 j hj c hc
      rw [h0, norm_zero] at this
      linarith
    have h2 := hM F W kW X k Γ j c hodd.pos hj htop hbal h1
    have h3 : _root_.YangMills.Construction.BlockAverages.distFromOne (pm j c) ≤ own j c + ms j c := by
      refine (_root_.YangMills.Construction.BondHull.distFromOne_mul_le _ _).trans ?_
      rw [_root_.YangMills.Construction.BondHull.distFromOne_inv, h2]
    have h4 := pow_le_pow_left₀ (_root_.YangMills.Construction.BondHull.distFromOne_nonneg _) h3 2
    have h5 := (norm_im_sq_and_distFromOne_sq (pm j c)).1
    nlinarith [sq_nonneg (own j c - ms j c)]
  have hfit : a * ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j,
      ‖((pm j c : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 ≤ 8 * e0 ^ 2 + 2 * a * (47 ^ 4 * (C₁ * s) ^ 2) := by
    have h1 : ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j, ‖((pm j c : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 ≤
        2 * (∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j, own j c ^ 2 +
          ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j, ms j c ^ 2) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum fun c hc => hpt j (Finset.mem_range.1 hj) c hc
    have h2 : ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j, own j c ^ 2 ≤ 4 / a * e0 ^ 2 := sz2
    have h3 := mul_le_mul_of_nonneg_left h1 ha.le
    have e1 : a * (4 / a * e0 ^ 2) = 4 * e0 ^ 2 := by field_simp
    have h4 := mul_le_mul_of_nonneg_left h2 ha.le
    have h5 := mul_le_mul_of_nonneg_left hmtot' ha.le
    nlinarith
  have hplaq : ∑ p ∈ patchPlaquettes S z,
      ‖((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) -
        ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ])‖ ^ 2 ≤
      4 * e0 ^ 2 + 4 * (47 ^ 4 * (C₁ * s) ^ 2) := by
    have hp : ∀ p ∈ patchPlaquettes S z,
        ‖((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) -
          ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ])‖ ^ 2 ≤
        2 * (_root_.YangMills.Construction.BlockAverages.distFromOne (plaquetteHolonomy (X 0) p) ^ 2 +
          2 * ‖((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2) := by
      intro p hp
      have h1 : _root_.YangMills.Construction.BlockAverages.distFromOne (plaquetteHolonomy (gaugedChainFields X Γ 0) p) =
          _root_.YangMills.Construction.BlockAverages.distFromOne (plaquetteHolonomy (X 0) p) := by
        have : gaugedChainFields X Γ 0 = gaugeTransform (Γ 0) (X 0) := rfl
        rw [this, hcovp, _root_.YangMills.Construction.BondHull.distFromOne_conj]
      have h2 : ‖((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) -
            ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ])‖ ≤
          _root_.YangMills.Construction.BlockAverages.distFromOne (plaquetteHolonomy (X 0) p) + _root_.YangMills.Construction.BlockAverages.distFromOne (plaquetteHolonomy (W 0) p) := by
        rw [← h1]
        unfold _root_.YangMills.Construction.BlockAverages.distFromOne
        have e : ((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) -
              ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]) =
            (((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) - 1) -
              (((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ]) - 1) := by
          abel
        rw [e]
        exact norm_sub_le _ _
      have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      have h4 := hplW p hp
      nlinarith [sq_nonneg (_root_.YangMills.Construction.BlockAverages.distFromOne (plaquetteHolonomy (X 0) p) - _root_.YangMills.Construction.BlockAverages.distFromOne (plaquetteHolonomy (W 0) p))]
    refine (Finset.sum_le_sum hp).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : ∑ p ∈ patchPlaquettes S z, _root_.YangMills.Construction.BlockAverages.distFromOne (plaquetteHolonomy (X 0) p) ^ 2 ≤ 2 * e0 ^ 2 := sz3
    linarith
  have hsmall : (4 + 2 * a) * (47 ^ 4 * (C₁ * s) ^ 2) ≤ 4 * e0 ^ 2 := by
    have h1 : (Z * s) ^ 2 ≤ e0 ^ 2 := pow_le_pow_left₀ (by positivity) hsZ 2
    have e1 : (Z * s) ^ 2 = (2 + a) ^ 2 * (47 ^ 4 * (C₁ * s) ^ 2) := by
      rw [hZ]
      ring
    have h2 : 0 ≤ 47 ^ 4 * (C₁ * s) ^ 2 := by positivity
    rw [e1] at h1
    nlinarith
  show relativeEnergy a S z W kW X k Γ ≤ _
  unfold relativeEnergy
  have e : (∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j,
      ‖((bondMisfit (gaugedChainFields X Γ j) (balancedLinkAgainst W kW (gaugedChainFields X Γ) j)
          (framedUpperField W kW X k Γ j) c * (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)⁻¹ :
            UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2) =
      ∑ j ∈ Finset.range F.top, ∑ c ∈ patchFitBonds S z j, ‖((pm j c : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 := rfl
  rw [e]
  linarith
end YangMills.Construction.BlockAverages
end
