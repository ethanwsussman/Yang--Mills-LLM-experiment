import YangMills.Construction.ColdChainAtEveryLevel.GapsOfAFramingOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.HolonomiesOnTheHullOfABond
import YangMills.Construction.ColdChainAtEveryLevel.LevelRecursionWithARate
import YangMills.Construction.ColdChainAtEveryLevel.MisfitsOfAFraming
import YangMills.Construction.ColdChainAtEveryLevel.OneStepOfAFraming
import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheCriticalChainOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.SizesAtAGoodCell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
namespace FramingDefects
theorem sqrt_sqrt_pow_four {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) ^ 4 = x := by apply _root_.YangMills.Construction.BlockAverages.LocalQuarticNorms.sqrt_sqrt_pow_four <;> assumption
theorem sqrt_sqrt_le_of_le_pow_four {a x : ℝ} (ha : 0 ≤ a) (h : x ≤ a ^ 4) : Real.sqrt (Real.sqrt x) ≤ a := by
  have e : Real.sqrt (Real.sqrt (a ^ 4)) = a := by
    have e1 : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [e1, Real.sqrt_sq (by positivity), Real.sqrt_sq ha]
  calc Real.sqrt (Real.sqrt x) ≤ Real.sqrt (Real.sqrt (a ^ 4)) := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)
    _ = a := e
theorem distFromOne_sq_le_two_mul_norm_im_sq (g : UnitQuaternion) (h : 0 ≤ ((g : ℍ[ℝ])).re) :
    _root_.YangMills.Construction.BlockAverages.distFromOne g ^ 2 ≤ 2 * ‖((g : ℍ[ℝ])).im‖ ^ 2 := by
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
  nlinarith
theorem secondOrder_le {CO Lr t ε m : ℝ} (hCO : 0 ≤ CO) (hL : 1 ≤ Lr) (ht : 0 ≤ t) (hε : 0 ≤ ε) (hm : 0 ≤ m) :
    CO * (Lr * t) * (Lr * t + ε) ≤ CO * Lr ^ 2 * (t ^ 2 + (ε + m) * t) := by
  have h1 : Lr ≤ Lr ^ 2 := by nlinarith
  have h2 : 0 ≤ CO * t * ε := by positivity
  have h3 : 0 ≤ CO * Lr ^ 2 * (m * t) := by positivity
  have h4 : CO * t * ε * Lr ≤ CO * t * ε * Lr ^ 2 := mul_le_mul_of_nonneg_left h1 h2
  nlinarith
end FramingDefects
set_option maxHeartbeats 3200000 in
open FramingDefects in
theorem framingDefectsOnPatchStatement_holds (hS : lowCostPatchBoundsStatement)
    (hR : criticalChainPatchRatesStatement) (hRec : QuarticBoundAcrossLevelsWithRate)
    (hO : gaugedOneStepComparisonStatement) (hM : gaugedMisfitNormStatement)
    (hA : averagesAndLocalSizesStatement) : framingDefectsOnPatchStatement := by
  intro a θ del Ca ha hθ hθ' hd hd' hCa
  obtain ⟨LS, hSz⟩ := hS a ha
  obtain ⟨LR, hRt⟩ := hR a θ del Ca ha hθ hθ' hd hd' hCa
  obtain ⟨CO, cO, hCO, hcO, hOne⟩ := hO
  refine ⟨max (max LS LR) 5, fun L hLodd hLL C₁ hC₁ => ?_⟩
  have hLS : LS ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL
  have hLRl : LR ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL
  have hL5 : 5 ≤ L := le_trans (le_max_right _ _) hLL
  obtain ⟨cS, hcS, hSz'⟩ := hSz L hLodd hLS
  obtain ⟨Cr, cr, hCr, hcr, hRt'⟩ := hRt L hLodd hLRl C₁ hC₁
  have hLr5 : (5 : ℝ) ≤ L := by exact_mod_cast hL5
  have hLp : (0 : ℝ) < L := by linarith
  set K : ℝ := CO * (L : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set c0 : ℝ := cO / L with hc0
  have hc0p : 0 < c0 := by positivity
  obtain ⟨c1, hc1, hRc⟩ := hRec L (47 ^ 4) K c0 hLodd hL5 hK0 hc0p
  set bB : ℝ := min c1 (min (1 / (16 * L)) (min (cO / (24 * (L : ℝ) ^ 2)) (1 / (48 * (L : ℝ) ^ 2)))) with hbB
  have hbBp : 0 < bB := by
    refine lt_min hc1 (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hb1 : bB ≤ c1 := min_le_left _ _
  have hb2 : bB ≤ 1 / (16 * L) := (min_le_right _ _).trans (min_le_left _ _)
  have hb3 : bB ≤ cO / (24 * (L : ℝ) ^ 2) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb4 : bB ≤ 1 / (48 * (L : ℝ) ^ 2) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set u : ℝ := Real.sqrt (8 / a) with hu
  have hup : 0 < u := Real.sqrt_pos.2 (by positivity)
  have hu2 : u ^ 2 = 8 / a := Real.sq_sqrt (by positivity)
  set A₀ : ℝ := 1 + u + 2 * Cr with hA₀
  have hA₀p : 0 < A₀ := by positivity
  set CC : ℝ := 4 * A₀ * (1 + (1 + CO) * 24 * (L : ℝ) ^ 2) with hCC
  refine ⟨CC, min (bB / 3) (min (bB / (3 * u)) (min cS (min (1 / (2 * u)) 1))), by positivity,
    lt_min (by positivity) (lt_min (by positivity) (lt_min hcS (lt_min (by positivity) one_pos))), ?_⟩
  intro e0 he0 he0c
  set cc := min (bB / 3) (min (bB / (3 * u)) (min cS (min (1 / (2 * u)) 1))) with hcc
  have hcc1 : cc ≤ bB / 3 := min_le_left _ _
  have he01 : e0 ≤ bB / (3 * u) := he0c.trans ((min_le_right _ _).trans (min_le_left _ _))
  have he02 : e0 ≤ cS := he0c.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he03 : e0 ≤ 1 / (2 * u) :=
    he0c.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  refine ⟨min cr (min (bB / (6 * Cr)) (min (1 / (2 * Cr)) (cO / Cr))),
    lt_min hcr (lt_min (by positivity) (lt_min (by positivity) (by positivity))), ?_⟩
  intro F m S hFL hamb hm hreg s V v hs hsσ hcold hv U hcrit X k z hXn hz hterms γ hγ
  subst hFL
  have hodd : Odd F.blockSide := hLodd
  have hLR1 : (1 : ℝ) ≤ F.blockSide := by linarith
  have hscr : s ≤ cr := hsσ.trans (min_le_left _ _)
  have hsb : 6 * Cr * s ≤ bB := by
    have h1 : s ≤ bB / (6 * Cr) := hsσ.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hs2 : 2 * Cr * s ≤ 1 := by
    have h1 : s ≤ 1 / (2 * Cr) := hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hso : Cr * s ≤ cO := by
    have h1 : s ≤ cO / Cr := hsσ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    rw [le_div_iff₀ hCr] at h1
    linarith
  obtain ⟨he, -⟩ := closedOrthant_spec hreg (by omega) z
  obtain ⟨hlev, -⟩ := hRt' F m S rfl hamb hm hreg s V v hs hscr hcold U hcrit z hz
  choose! Er er hEr0 her0 hEr4 her4 hm2 hrt using hlev
  obtain ⟨sz1, sz2, -⟩ := hSz' e0 he0 he02 F m S rfl hamb hm hreg X k z hz hterms
  set W := criticalFieldChain S V v U with hW
  set kW := criticalGauge S V U with hkW
  set Γ := pinnedGaugeOfBase W kW X k γ with hΓ
  set P := patchCells S z with hP
  have hbp : ∀ j, j ≤ F.top → innerBonds P j = patchInnerBonds S z j := fun j hj =>
    innerBonds_patchCells hamb hodd he hj
  have htop : ∀ y, Γ F.top y = 1 := pinnedGaugeOfBase_top W kW X k γ
  have hbal : ∀ j', j' + 1 < F.top → ∀ y, gaugedLink k Γ j' y = balancedLinkAgainst W kW (gaugedChainFields X Γ) j' y :=
    fun j' hj' y => gaugedLink_pinnedGaugeOfBase W kW X k γ hj' y
  set gp : (j : ℕ) → F.Site j → Fin 4 → ℝ := fun j x i => _root_.YangMills.Construction.BlockAverages.distFromOne (relativeDefect W X Γ j x i) with hgp
  set pm : (j : ℕ) → F.Site (j + 1) × Fin 4 → UnitQuaternion := fun j c =>
    bondMisfit (gaugedChainFields X Γ j) (balancedLinkAgainst W kW (gaugedChainFields X Γ) j)
        (framedUpperField W kW X k Γ j) c *
      (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)⁻¹ with hpm
  set own : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℝ := fun j c =>
    _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (X j) (k (j + 1)) (X (j + 1)) c) with hown
  set ms : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℝ := fun j c =>
    _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c) with hms
  set D := relativeEnergy a S z W kW X k Γ with hD
  have hfit : ∀ j, j < F.top → ∀ c ∈ innerBonds P (j + 1), c ∈ patchFitBonds S z j := fun j hj c hc =>
    mem_patchFitBonds_of_mem_innerBonds hamb hodd he hj hc
  have hpm_le : ∀ j, j < F.top → ∀ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (pm j c) ≤ own j c + ms j c := by
    intro j hj c hc
    have h1 : gaugedContourAverage (X j) (k (j + 1)) c ≠ 0 := by
      intro h0
      have := sz1 j hj c (hfit j hj c hc)
      rw [h0, norm_zero] at this
      linarith
    have h2 := hM F W kW X k Γ j c hodd.pos hj htop hbal h1
    refine (BondHull.distFromOne_mul_le _ _).trans ?_
    rw [BondHull.distFromOne_inv, h2]
  have hownsum : ∀ j, j < F.top → ∑ c ∈ innerBonds P (j + 1), own j c ^ 2 ≤ 4 / a * e0 ^ 2 := by
    intro j hj
    have h1 : ∑ c ∈ innerBonds P (j + 1), own j c ^ 2 ≤ ∑ c ∈ patchFitBonds S z j, own j c ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => hfit j hj c hc) fun c _ _ => by positivity
    have h2 := Finset.single_le_sum (f := fun j' => ∑ b ∈ patchFitBonds S z j', own j' b ^ 2)
      (fun j' _ => Finset.sum_nonneg fun c _ => by positivity) (Finset.mem_range.2 hj)
    exact h1.trans (h2.trans sz2)
  have hms2 : ∀ j, j < F.top → ∑ c ∈ innerBonds P (j + 1), ms j c ^ 2 ≤ (Cr * s) ^ 2 := hm2
  have hpoint : ∀ j, j < F.top → ∀ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (pm j c) ≤ 1 := by
    intro j hj c hc
    have h1 := Finset.single_le_sum (f := fun c => own j c ^ 2) (fun c _ => by positivity) hc
    have h2 := Finset.single_le_sum (f := fun c => ms j c ^ 2) (fun c _ => by positivity) hc
    have h3 : own j c ^ 2 ≤ 4 / a * e0 ^ 2 := h1.trans (hownsum j hj)
    have h4 : ms j c ^ 2 ≤ (Cr * s) ^ 2 := h2.trans (hms2 j hj)
    have h5 : ms j c ≤ Cr * s := abs_le_of_sq_le_sq' h4 (by positivity) |>.2
    have h6 : own j c ≤ 1 / 2 := by
      have e1 : 4 / a * e0 ^ 2 ≤ (1 / 2) ^ 2 := by
        have e2 : (2 * u * e0) ^ 2 ≤ 1 := by
          have : 2 * u * e0 ≤ 1 := by
            rw [le_div_iff₀ (by positivity)] at he03
            linarith
          exact pow_le_one₀ (by positivity) this
        have e3 : (2 * u * e0) ^ 2 = 32 / a * e0 ^ 2 := by
          rw [mul_pow, mul_pow, hu2]
          ring
        rw [e3] at e2
        have e4 : 4 / a * e0 ^ 2 = (32 / a * e0 ^ 2) / 8 := by ring
        rw [e4]
        linarith
      exact (abs_le_of_sq_le_sq' (h3.trans e1) (by norm_num)).2
    have := hpm_le j hj c hc
    linarith
  have him : ∀ j, j < F.top → ∑ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (pm j c) ^ 2 ≤ 2 / a * D := by
    intro j hj
    have h1 : ∀ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (pm j c) ^ 2 ≤ 2 * ‖((pm j c : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 :=
      fun c hc => _root_.YangMills.Construction.BlockAverages.FramingDefects.distFromOne_sq_le_two_mul_norm_im_sq _ (BlockLines.re_nonneg_of_norm_sub_one_le _ (hpoint j hj c hc))
    have h2 : ∑ c ∈ innerBonds P (j + 1), ‖((pm j c : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 ≤ ∑ c ∈ patchFitBonds S z j,
        ‖((pm j c : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => hfit j hj c hc) fun c _ _ => by positivity
    have h3 := Finset.single_le_sum
      (f := fun j' => ∑ b ∈ patchFitBonds S z j', ‖((pm j' b : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2)
      (fun j' _ => Finset.sum_nonneg fun c _ => by positivity) (Finset.mem_range.2 hj)
    have h4 : a * ∑ j' ∈ Finset.range F.top, ∑ b ∈ patchFitBonds S z j',
        ‖((pm j' b : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 ≤ D := by
      have h5 : 0 ≤ ∑ p ∈ patchPlaquettes S z,
          ‖((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) -
          ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ])‖ ^ 2 := Finset.sum_nonneg fun p _ => by positivity
      simp only [hD, relativeEnergy]
      linarith
    have h6 : ∑ j' ∈ Finset.range F.top, ∑ b ∈ patchFitBonds S z j',
        ‖((pm j' b : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 ≤ D / a := by
      rw [le_div_iff₀ ha]
      linarith
    calc ∑ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (pm j c) ^ 2
        ≤ ∑ c ∈ innerBonds P (j + 1), 2 * ‖((pm j c : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 := Finset.sum_le_sum h1
      _ = 2 * ∑ c ∈ innerBonds P (j + 1), ‖((pm j c : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 2 * (D / a) := by
          have := h2.trans (h3.trans h6)
          linarith
      _ = 2 / a * D := by ring
  have hD0 : 0 ≤ D := by
    have h5 : 0 ≤ ∑ p ∈ patchPlaquettes S z,
        ‖((plaquetteHolonomy (gaugedChainFields X Γ 0) p : UnitQuaternion) : ℍ[ℝ]) -
        ((plaquetteHolonomy (W 0) p : UnitQuaternion) : ℍ[ℝ])‖ ^ 2 := Finset.sum_nonneg fun p _ => by positivity
    have h6 : 0 ≤ ∑ j' ∈ Finset.range F.top, ∑ b ∈ patchFitBonds S z j',
        ‖((pm j' b : UnitQuaternion) : ℍ[ℝ]).im‖ ^ 2 :=
      Finset.sum_nonneg fun j' _ => Finset.sum_nonneg fun c _ => by positivity
    have h7 := mul_nonneg ha.le h6
    simp only [hD, relativeEnergy]
    linarith
  set M₂ : ℝ := u * e0 + 2 * Cr * s with hM₂
  have hM₂p : 0 ≤ M₂ := by positivity
  have hsmall2 : ∀ j, j < F.top → Real.sqrt (∑ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (pm j c) ^ 2) ≤ M₂ := by
    intro j hj
    have h1 : ∑ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (pm j c) ^ 2 ≤ M₂ ^ 2 := by
      have h2 : ∀ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (pm j c) ^ 2 ≤ 2 * (own j c ^ 2 + ms j c ^ 2) := by
        intro c hc
        have h3 := hpm_le j hj c hc
        have h4 := pow_le_pow_left₀ (BondHull.distFromOne_nonneg _) h3 2
        nlinarith [sq_nonneg (own j c - ms j c)]
      calc ∑ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (pm j c) ^ 2
          ≤ ∑ c ∈ innerBonds P (j + 1), 2 * (own j c ^ 2 + ms j c ^ 2) := Finset.sum_le_sum h2
        _ = 2 * (∑ c ∈ innerBonds P (j + 1), own j c ^ 2 + ∑ c ∈ innerBonds P (j + 1), ms j c ^ 2) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ 2 * (4 / a * e0 ^ 2 + (Cr * s) ^ 2) := by
            have := add_le_add (hownsum j hj) (hms2 j hj)
            linarith
        _ ≤ M₂ ^ 2 := by
            have e3 : M₂ ^ 2 = 8 / a * e0 ^ 2 + 4 * u * e0 * (Cr * s) + 4 * (Cr * s) ^ 2 := by
              rw [hM₂, ← hu2]
              ring
            rw [e3]
            have : 0 ≤ 4 * u * e0 * (Cr * s) := by positivity
            have e4 : 2 * (4 / a * e0 ^ 2) = 8 / a * e0 ^ 2 := by ring
            nlinarith [sq_nonneg (Cr * s)]
    rw [← Real.sqrt_sq hM₂p]
    exact Real.sqrt_le_sqrt h1
  have henergy2 : ∀ j, j < F.top → Real.sqrt (∑ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (pm j c) ^ 2) ≤
      Real.sqrt (2 / a * D) := fun j hj => Real.sqrt_le_sqrt (him j hj)
  set e := quarticDefectNorm S z W X Γ 0 with hedef
  have he0' : 0 ≤ e := Real.sqrt_nonneg _
  have hec : e ≤ cc := hγ
  set N : ℝ := min (Real.sqrt (2 / a * D)) M₂ with hN
  have hN0 : 0 ≤ N := le_min (Real.sqrt_nonneg _) hM₂p
  set B : ℝ := e + N with hB
  have hB0 : 0 ≤ B := by positivity
  have hBb : B ≤ bB := by
    have h1 : N ≤ M₂ := min_le_right _ _
    have h2 : u * e0 ≤ bB / 3 := by
      rw [le_div_iff₀ (by positivity)] at he01
      linarith
    have h3 : e ≤ bB / 3 := hec.trans hcc1
    have h4 : 2 * Cr * s ≤ bB / 3 := by linarith
    simp only [hB, hM₂] at *
    linarith
  have hδ : Cr * s ≤ c1 := by
    have : 6 * Cr * s ≤ c1 := hsb.trans hb1
    have h0 : 0 ≤ Cr * s := by positivity
    linarith
  have hLc : ∀ t, t ≤ c0 → (F.blockSide : ℝ) * t ≤ cO := by
    intro t ht
    have := mul_le_mul_of_nonneg_left ht hLp.le
    have e2 : (F.blockSide : ℝ) * c0 = cO := by
      rw [hc0]
      field_simp
    linarith
  have hcard : P.card ≤ 47 ^ 4 := card_patchCells_le hamb hodd he
  have hrc := hRc F P gp (fun j y i => _root_.YangMills.Construction.BlockAverages.distFromOne (pm j (y, i))) (fun j y i => |er j (y, i)|) (Cr * s) B rfl hcard
    (by positivity) hδ hB0 (hBb.trans hb1) (fun j x i => BondHull.distFromOne_nonneg _)
    (fun j y i => BondHull.distFromOne_nonneg _)
    (fun j y i => abs_nonneg _)
    (by
      have : Real.sqrt (Real.sqrt (∑ b ∈ innerBonds P 0, gp 0 b.1 b.2 ^ 4)) = e := by
        rw [hbp 0 (Nat.zero_le _)]
        rfl
      rw [this]
      have : 0 ≤ N := hN0
      simp only [hB]
      linarith)
    (fun j hj => by
      have hj' : j < F.top := by omega
      have h1 := hsmall2 j hj'
      have h2 := henergy2 j hj'
      have h3 : Real.sqrt (∑ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (pm j c) ^ 2) ≤ N := le_min h2 h1
      have : e ≥ 0 := he0'
      simp only [hB]
      show Real.sqrt (∑ c ∈ innerBonds P (j + 1), _root_.YangMills.Construction.BlockAverages.distFromOne (pm j c) ^ 2) ≤ _
      linarith)
    (fun j hj => by
      have hj' : j < F.top := by omega
      refine sqrt_sqrt_le_of_le_pow_four (by positivity) ?_
      have e1 : ∑ c ∈ innerBonds P (j + 1), |er j (c.1, c.2)| ^ 4 = ∑ c ∈ innerBonds P (j + 1), er j c ^ 4 := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Prod.mk.eta, abs_of_nonneg (her0 j hj' c)]
      rw [e1]
      exact her4 j hj')
    (fun j hj c hc t ht0 htc hmc hBl => by
      have hj' : j < F.top := by omega
      have hj1 : j + 1 ≤ F.top := hj'
      have hec' : er j c ≤ Cr * s := by
        have h1 := Finset.single_le_sum (f := fun c => er j c ^ 4)
          (fun c _ => by have := her0 j hj' c; positivity) hc
        exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) (h1.trans (her4 j hj'))
      have h1 := (hOne F j (gaugedChainFields X Γ j) (W j) (kW (j + 1)) (framedUpperField W kW X k Γ j) (W (j + 1)) c t
        (er j c) hodd hj1 ht0 (her0 j hj' c) (hLc t htc) (hec'.trans hso) hBl ((hrt j hj').contour_le c hc)).2
      have hne : j ≠ F.depth := by
        have : F.top = F.depth + 1 := rfl
        omega
      have hup : framedUpperField W kW X k Γ j = gaugedChainFields X Γ (j + 1) := by
        simp only [framedUpperField, dif_neg hne]
      rw [hup] at h1
      have h2 := secondOrder_le (Lr := (F.blockSide : ℝ)) (t := t) (ε := er j c) (m := _root_.YangMills.Construction.BlockAverages.distFromOne (pm j (c.1, c.2)))
        hCO.le hLR1 ht0 (her0 j hj' c) (BondHull.distFromOne_nonneg _)
      have e1 : |er j (c.1, c.2)| = er j c := by
        rw [Prod.mk.eta, abs_of_nonneg (her0 j hj' c)]
      rw [e1]
      have e2 : _root_.YangMills.Construction.BlockAverages.distFromOne (pm j (c.1, c.2)) = _root_.YangMills.Construction.BlockAverages.distFromOne (bondMisfit (gaugedChainFields X Γ j)
          (balancedLinks (gaugedChainFields X Γ j) (W j) (kW (j + 1))) (gaugedChainFields X Γ (j + 1)) c *
            (bondMisfit (W j) (kW (j + 1)) (W (j + 1)) c)⁻¹) := by
        simp only [hpm, Prod.mk.eta, hup]
        rfl
      have h3 : gp (j + 1) c.1 c.2 ≤ _root_.YangMills.Construction.BlockAverages.distFromOne (pm j (c.1, c.2)) + lineBlockAverage (gp j) c +
          CO * ((F.blockSide : ℝ) * t) * ((F.blockSide : ℝ) * t + er j c) := by
        rw [e2]
        exact h1
      show gp (j + 1) c.1 c.2 ≤ _root_.YangMills.Construction.BlockAverages.distFromOne (pm j (c.1, c.2)) + lineBlockAverage (gp j) c +
        K * (t ^ 2 + (er j c + _root_.YangMills.Construction.BlockAverages.distFromOne (pm j (c.1, c.2))) * t)
      linarith)
  have hS0 : ∀ j, 0 ≤ ∑ b ∈ innerBonds P j, gp j b.1 b.2 ^ 4 := fun j =>
    Finset.sum_nonneg fun b _ => pow_nonneg (BondHull.distFromOne_nonneg _) 4
  have hsum4 : ∀ j, j < F.top → ∑ b ∈ innerBonds P j, gp j b.1 b.2 ^ 4 ≤ (4 * B) ^ 4 := by
    intro j hj
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hrc j hj) 4
    rwa [sqrt_sqrt_pow_four (hS0 j)] at this
  have hterm : ∀ j, j < F.top → ∀ b ∈ innerBonds P j, gp j b.1 b.2 ≤ 4 * B := by
    intro j hj b hb
    have h1 := Finset.single_le_sum (f := fun b : F.Site j × Fin 4 => gp j b.1 b.2 ^ 4)
      (fun b _ => pow_nonneg (BondHull.distFromOne_nonneg _) 4) hb
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) (h1.trans (hsum4 j hj))
  have hq : ∀ j, j < F.top → quarticDefectNorm S z W X Γ j ≤ 4 * B := by
    intro j hj
    have h1 := hrc j hj
    rw [hbp j hj.le] at h1
    exact h1
  have hBe : B ≤ e + Real.sqrt (2 / a * D) := by
    have : N ≤ Real.sqrt (2 / a * D) := min_le_left _ _
    simp only [hB]
    linarith
  have hG0 : 0 ≤ e + e0 + s := by positivity
  have hBG : B ≤ A₀ * (e + e0 + s) := by
    have h1 : N ≤ M₂ := min_le_right _ _
    have h2 : e + u * e0 + 2 * Cr * s ≤ A₀ * (e + e0 + s) := by
      have p1 : 0 ≤ u * e := by positivity
      have p2 : 0 ≤ 2 * Cr * e := by positivity
      have p3 : 0 ≤ 2 * Cr * e0 := by positivity
      have p4 : 0 ≤ u * s := by positivity
      simp only [hA₀]
      nlinarith
    simp only [hB, hM₂] at *
    linarith
  have hC4 : 4 * A₀ ≤ CC := by
    have h1 : 0 ≤ (1 + CO) * 24 * (F.blockSide : ℝ) ^ 2 := by positivity
    simp only [hCC]
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj y hy hb
    have hyP : y ∈ sitesOfCells P (j + 1) := (mem_sitesOfCells_patchCells_iff hamb hodd he hj).2 ⟨hy, hb⟩
    have hcl : ∀ g ∈ centredCube F.blockSide, ∀ k', g + LatticeFractionalIntegration.basisVector k' ∈ centredCube F.blockSide →
        _root_.YangMills.Construction.BlockAverages.distFromOne (gaugedChainFields X Γ j (refineSite y + siteOfCoords j g) k' *
          (W j (refineSite y + siteOfCoords j g) k')⁻¹) ≤ 4 * B := by
      intro g hg k' hk'
      have hb1 := BlockLines.refineSite_add_mem_sitesOfCells hj hodd y hyP g hg
      have hb2 := BlockLines.refineSite_add_mem_sitesOfCells hj hodd y hyP _ hk'
      have e1 : refineSite y + siteOfCoords j g + unitStep j k' =
          refineSite y + siteOfCoords j (g + LatticeFractionalIntegration.basisVector k') := by
        rw [unitStep_eq, add_assoc, ← siteOfCoords_add]
      refine hterm j hj (refineSite y + siteOfCoords j g, k') ?_
      refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hb1, Finset.mem_univ _⟩, ?_⟩
      show refineSite y + siteOfCoords j g + unitStep j k' ∈ sitesOfCells P j
      rw [e1]
      exact hb2
    refine (BondHull.norm_relativePathAverage_sub_one_le hodd _ _ y (4 * B) (by positivity) hcl).trans ?_
    have h1 : (F.blockSide : ℝ) * B ≤ 1 / 16 := by
      have h2 := mul_le_mul_of_nonneg_left (hBb.trans hb2) hLp.le
      have e2 : (F.blockSide : ℝ) * (1 / (16 * F.blockSide)) = 1 / 16 := by field_simp
      linarith
    nlinarith
  · intro j hj
    have h1 := hq j hj
    have h2 : 4 * B ≤ 4 * A₀ * (e + e0 + s) := by linarith
    have h3 := mul_le_mul_of_nonneg_right hC4 hG0
    linarith
  · intro b hb
    have hb' : b ∈ innerBonds P (F.depth + 1) := by
      rw [hbp _ (le_refl _)]
      exact hb
    have hjt : F.depth < F.top := Nat.lt_succ_self _
    obtain ⟨-, -, -, T, hT0, hTb, -, hT1, -, -⟩ :=
      hA F P F.depth (gp F.depth) hodd (le_refl _) (fun x i => BondHull.distFromOne_nonneg _)
    have hT24 : T b.1 ≤ 24 * F.blockSide * B := by
      have h1 : T b.1 ^ 4 ≤ (24 * (F.blockSide : ℝ) * B) ^ 4 := by
        have h2 := mul_le_mul_of_nonneg_left (hsum4 F.depth hjt)
          (by positivity : 0 ≤ 4 * (3 * (F.blockSide : ℝ)) ^ 4)
        refine (hT1 b.1).trans (h2.trans ?_)
        have h3 : 0 ≤ ((F.blockSide : ℝ) * B) ^ 4 := by positivity
        have e1 : 4 * (3 * (F.blockSide : ℝ)) ^ 4 * (4 * B) ^ 4 = 82944 * ((F.blockSide : ℝ) * B) ^ 4 := by ring
        have e2 : (24 * (F.blockSide : ℝ) * B) ^ 4 = 331776 * ((F.blockSide : ℝ) * B) ^ 4 := by ring
        rw [e1, e2]
        linarith
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h1
    have hLt : (F.blockSide : ℝ) * T b.1 ≤ 24 * (F.blockSide : ℝ) ^ 2 * B := by
      have := mul_le_mul_of_nonneg_left hT24 hLp.le
      nlinarith
    have hBL : 24 * (F.blockSide : ℝ) ^ 2 * B ≤ 1 / 2 := by
      have h2 := mul_le_mul_of_nonneg_left (hBb.trans hb4) (by positivity : 0 ≤ 24 * (F.blockSide : ℝ) ^ 2)
      have e2 : 24 * (F.blockSide : ℝ) ^ 2 * (1 / (48 * (F.blockSide : ℝ) ^ 2)) = 1 / 2 := by field_simp; norm_num
      linarith
    have hBO : 24 * (F.blockSide : ℝ) ^ 2 * B ≤ cO := by
      have h2 := mul_le_mul_of_nonneg_left (hBb.trans hb3) (by positivity : 0 ≤ 24 * (F.blockSide : ℝ) ^ 2)
      have e2 : 24 * (F.blockSide : ℝ) ^ 2 * (cO / (24 * (F.blockSide : ℝ) ^ 2)) = cO := by field_simp
      linarith
    have hec' : er F.depth b ≤ Cr * s := by
      have h1 := Finset.single_le_sum (f := fun c => er F.depth c ^ 4)
        (fun c _ => by have := her0 F.depth hjt c; positivity) hb'
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) (h1.trans (her4 F.depth hjt))
    have hε0 := her0 F.depth hjt b
    have h1 := (hOne F F.depth (gaugedChainFields X Γ F.depth) (W F.depth) (kW (F.depth + 1))
      (framedUpperField W kW X k Γ F.depth) (W (F.depth + 1)) b
      (T b.1) (er F.depth b) hodd (le_refl _) (hT0 _) hε0 (hLt.trans hBO) (hec'.trans hso) (hTb b hb')
      ((hrt F.depth hjt).contour_le b hb')).2
    have h2 : _root_.YangMills.Construction.BlockAverages.distFromOne (pm F.depth b) ≤ M₂ := by
      have h3 := Finset.single_le_sum (f := fun c => _root_.YangMills.Construction.BlockAverages.distFromOne (pm F.depth c) ^ 2) (fun c _ => by positivity) hb'
      have h4 := Real.le_sqrt_of_sq_le h3
      exact h4.trans (hsmall2 F.depth hjt)
    have h3 : lineBlockAverage (gp F.depth) b ≤ (F.blockSide : ℝ) * T b.1 := by
      have hc : ((centredCube F.blockSide).card : ℝ) = (F.blockSide : ℝ) ^ 4 := by
        rw [LatticePaths.card_centredCube hodd]
        push_cast
        rfl
      unfold lineBlockAverage
      have h4 : ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
          gp F.depth (refineSite b.1 + siteOfCoords F.depth h + (r : ℤ) • unitStep F.depth b.2) b.2 ≤
          ∑ _h ∈ centredCube F.blockSide, ∑ _r ∈ Finset.range F.blockSide, T b.1 :=
        Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun r hr => (hTb b hb').2 h hh r hr
      have h5 : ∑ _h ∈ centredCube F.blockSide, ∑ _r ∈ Finset.range F.blockSide, T b.1 =
          (F.blockSide : ℝ) ^ 4 * ((F.blockSide : ℝ) * T b.1) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [hc]
      rw [h5] at h4
      calc 1 / (F.blockSide : ℝ) ^ 4 * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
            gp F.depth (refineSite b.1 + siteOfCoords F.depth h + (r : ℤ) • unitStep F.depth b.2) b.2
          ≤ 1 / (F.blockSide : ℝ) ^ 4 * ((F.blockSide : ℝ) ^ 4 * ((F.blockSide : ℝ) * T b.1)) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = (F.blockSide : ℝ) * T b.1 := by field_simp
    have h4 : CO * ((F.blockSide : ℝ) * T b.1) * ((F.blockSide : ℝ) * T b.1 + er F.depth b) ≤
        CO * ((F.blockSide : ℝ) * T b.1) := by
      have p1 : 0 ≤ CO * ((F.blockSide : ℝ) * T b.1) := mul_nonneg hCO.le (mul_nonneg hLp.le (hT0 _))
      have p2 : (F.blockSide : ℝ) * T b.1 + er F.depth b ≤ 1 := by
        have : Cr * s ≤ 1 / 2 := by linarith
        linarith
      calc _ ≤ CO * ((F.blockSide : ℝ) * T b.1) * 1 := mul_le_mul_of_nonneg_left p2 p1
        _ = _ := by ring
    have h5 : _root_.YangMills.Construction.BlockAverages.distFromOne (topDefect W kW X k Γ b.1 b.2) ≤ _root_.YangMills.Construction.BlockAverages.distFromOne (pm F.depth b) +
        lineBlockAverage (gp F.depth) b +
        CO * ((F.blockSide : ℝ) * T b.1) * ((F.blockSide : ℝ) * T b.1 + er F.depth b) := h1
    have h6 : M₂ ≤ A₀ * (e + e0 + s) := by
      have p1 : 0 ≤ u * e := by positivity
      have p2 : 0 ≤ 2 * Cr * e := by positivity
      have p3 : 0 ≤ 2 * Cr * e0 := by positivity
      have p4 : 0 ≤ u * s := by positivity
      simp only [hA₀, hM₂]
      nlinarith
    have h7 : (F.blockSide : ℝ) * T b.1 ≤ 24 * (F.blockSide : ℝ) ^ 2 * (A₀ * (e + e0 + s)) :=
      hLt.trans (mul_le_mul_of_nonneg_left hBG (by positivity))
    have h8 : (1 + CO) * ((F.blockSide : ℝ) * T b.1) ≤
        (1 + CO) * (24 * (F.blockSide : ℝ) ^ 2 * (A₀ * (e + e0 + s))) :=
      mul_le_mul_of_nonneg_left h7 (by positivity)
    have h9 : A₀ * (e + e0 + s) + (1 + CO) * (24 * (F.blockSide : ℝ) ^ 2 * (A₀ * (e + e0 + s))) ≤
        CC * (e + e0 + s) := by
      have hx : 0 ≤ A₀ * (e + e0 + s) := by positivity
      have hy : 0 ≤ (1 + CO) * 24 * (F.blockSide : ℝ) ^ 2 := by positivity
      have e1 : CC * (e + e0 + s) = 4 * (A₀ * (e + e0 + s)) * (1 + (1 + CO) * 24 * (F.blockSide : ℝ) ^ 2) := by
        simp only [hCC]
        ring
      have e2 : A₀ * (e + e0 + s) + (1 + CO) * (24 * (F.blockSide : ℝ) ^ 2 * (A₀ * (e + e0 + s))) =
          (A₀ * (e + e0 + s)) * (1 + (1 + CO) * 24 * (F.blockSide : ℝ) ^ 2) := by ring
      rw [e1, e2]
      have h10 : 0 ≤ (A₀ * (e + e0 + s)) * (1 + (1 + CO) * 24 * (F.blockSide : ℝ) ^ 2) := by positivity
      nlinarith
    have h10 : normSubOne (topDefect W kW X k Γ b.1 b.2) = _root_.YangMills.Construction.BlockAverages.distFromOne (topDefect W kW X k Γ b.1 b.2) := rfl
    linarith
  · intro j hj
    rw [← hbp (j + 1) hj]
    exact him j hj
  · intro j hj
    have h1 := hq j hj
    linarith
end YangMills.Construction.BlockAverages
end
