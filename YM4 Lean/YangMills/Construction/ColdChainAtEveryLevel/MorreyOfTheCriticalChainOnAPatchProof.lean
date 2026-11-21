import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfASplitCriticalPointProof
import YangMills.Construction.ColdChainAtEveryLevel.HolonomiesOnTheHullOfABond
import YangMills.Construction.ColdChainAtEveryLevel.MorreyOfTheCriticalChainOnAPatch
import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheCriticalChainOnAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace PatchMorrey
open BlockAverages GaugeMap PatchLatticeChart PatchLatticeChart.Framing LatticeFractionalIntegration LatticePaths BondHull PatchForms PatchPoints
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem pow_four_add_pow_four_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) : A ^ 4 + B ^ 4 ≤ (A + B) ^ 4 := by
  have e : (A + B) ^ 4 = A ^ 4 + 4 * A ^ 3 * B + 6 * A ^ 2 * B ^ 2 + 4 * A * B ^ 3 + B ^ 4 := by ring
  have h1 : 0 ≤ 4 * A ^ 3 * B + 6 * A ^ 2 * B ^ 2 + 4 * A * B ^ 3 := by positivity
  rw [e]
  linarith
theorem add_pow_four_le_eight_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by apply _root_.YangMills.Construction.BlockAverages.SplitCriticalPointBounds.add_pow_four_le <;> assumption
theorem norm_framedLatticeField_sub_one (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (V : F.GaugeField F.top) (W : F.GaugeField 0) (b : Lattice4 × Fin 4) :
    ‖((framedLatticeField S V z W b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ =
      distFromOne (gaugeTransform (fun x => (patchFrame S V z x)⁻¹) W (siteBond S z b).1 (siteBond S z b).2) := by
  obtain ⟨k1, k2⟩ := patchSite_add_basisVector_cases he b.1 b.2
  have hfa : ∀ x : F.Site 0, patchFrame S V z x = frameChange S V z x := by
    intro x
    unfold patchFrame
    rw [baseSite_eq_self]
  unfold framedLatticeField latticeField siteBond distFromOne
  rcases he b.2 with h | h
  · simp only [h, if_true, gaugeTransform, hfa, inv_inv]
    rw [← k1 h]
  · have hne : closedOrthant S z b.2 ≠ 1 := by rw [h]; norm_num
    simp only [if_neg hne, gaugeTransform, hfa, inv_inv]
    rw [← k2 h]
    have e : (frameChange S V z (patchSite S z b.1))⁻¹ * (W (patchSite S z (b.1 + basisVector b.2)) b.2)⁻¹ *
        frameChange S V z (patchSite S z (b.1 + basisVector b.2)) =
        ((frameChange S V z (patchSite S z (b.1 + basisVector b.2)))⁻¹ * W (patchSite S z (b.1 + basisVector b.2)) b.2 *
          frameChange S V z (patchSite S z b.1))⁻¹ := by group
    rw [e, norm_coe_inv_sub_one]
theorem distFromOne_gaugeTransform_le {j : ℕ} (Y R : F.GaugeField j) (φ : F.Site j → UnitQuaternion) (x : F.Site j) (k : Fin 4) :
    distFromOne (gaugeTransform φ Y x k) ≤ distFromOne (Y x k * (R x k)⁻¹) + distFromOne (gaugeTransform φ R x k) := by
  have e : gaugeTransform φ Y x k = (φ x * (Y x k * (R x k)⁻¹) * (φ x)⁻¹) * gaugeTransform φ R x k := by
    simp only [gaugeTransform]
    group
  rw [e]
  refine (distFromOne_mul_le _ _).trans ?_
  rw [distFromOne_conj]
theorem baseDistance_patchSite_le (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (w x : Lattice4) :
    baseDistance (patchSite S z w) (patchSite S z x) ≤ supNorm (w - x) := by
  unfold baseDistance
  refine Finset.sup_le fun i _ => ?_
  rw [baseSite_eq_self]
  have e : patchSite S z w - patchSite S z x = siteOfCoords 0 (fun k => closedOrthant S z k * (w k - x k)) := by
    unfold patchSite
    have : siteOfCoords (F := F) 0 (fun k => closedOrthant S z k * (w k - (cellSideLength F - 1) / 2)) =
        siteOfCoords 0 (fun k => closedOrthant S z k * (x k - (cellSideLength F - 1) / 2)) +
          siteOfCoords 0 (fun k => closedOrthant S z k * (w k - x k)) := by
      rw [← siteOfCoords_add]
      congr 1
      funext k
      simp only [Pi.add_apply]
      ring
    rw [this]
    abel
  rw [e]
  refine (natAbs_valMinAbs_intCast_le _ _).trans ?_
  have h1 : (closedOrthant S z i * (w i - x i)).natAbs = (w i - x i).natAbs := by
    rcases he i with h | h <;> rw [h]
    · simp
    · simp only [neg_mul, one_mul, Int.natAbs_neg]
  rw [h1]
  exact natAbs_le_supNorm (w - x) i
open Classical in
def baseBondsNear (S : Finset F.Cell) (p : F.Site 0) (r : ℝ) : Finset (F.Site 0 × Fin 4) :=
  (innerBonds S 0).filter (fun b => (baseDistance b.1 p : ℝ) ≤ r * (F.blockSide : ℝ) ^ 0)
theorem card_filter_supNorm_le (x : Lattice4) (r : ℕ) (P : Finset Lattice4) :
    ((P.filter (fun u => supNorm (u - x) ≤ r)).card : ℝ) ≤ (2 * (r : ℝ) + 1) ^ 4 := by
  classical
  have hsub : P.filter (fun u => supNorm (u - x) ≤ r) ⊆
      Fintype.piFinset fun i : Fin 4 => Finset.Icc (x i - r) (x i + r) := by
    intro u hu
    have h1 := (Finset.mem_filter.1 hu).2
    refine Fintype.mem_piFinset.2 fun i => ?_
    have h2 := (natAbs_le_supNorm (u - x) i).trans h1
    rw [Finset.mem_Icc]
    simp only [Pi.sub_apply] at h2
    omega
  have h1 := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at h1
  have h2 : ∀ i : Fin 4, (Finset.Icc (x i - r) (x i + r)).card = 2 * r + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have h3 : ((P.filter (fun u => supNorm (u - x) ≤ r)).card : ℝ) ≤ ((2 * r + 1) ^ 4 : ℕ) := by exact_mod_cast h1
  refine h3.trans (le_of_eq ?_)
  push_cast
  ring
theorem sum_frameDefectWeight_eq (W : F.GaugeField 0) (V : F.GaugeField F.top) (Fil : Finset Lattice4) :
    ∑ u ∈ Fil, frameDefectWeight S V z W u =
      ∑ p ∈ (Fil ×ˢ (Finset.univ : Finset (Fin 4))).filter (fun p => (p.1 - basisVector p.2, p.2) ∈ bondsOf (patchDomain S z)),
        ‖((framedLatticeField S V z W (p.1 - basisVector p.2) p.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 := by
  rw [Finset.sum_filter, Finset.sum_product]
  rfl
end PatchMorrey
set_option maxHeartbeats 1600000 in
open PatchMorrey BlockAverages GaugeMap PatchLatticeChart PatchLatticeChart.Framing LatticeFractionalIntegration LatticePaths BondHull PatchForms PatchPoints in
theorem PatchMorrey.criticalChainMorreyStatement_holds (hR : criticalChainPatchRatesStatement)
    (hB : referenceBoundsStatement) : criticalChainMorreyStatement := by
  intro a θ del Ca ha hθ hθ' hd hd' hCa
  obtain ⟨LR, hRt⟩ := hR a θ del Ca ha hθ hθ' hd hd' hCa
  obtain ⟨CR, cR, L1, hCR, hcR, hRef⟩ := hB
  refine ⟨max LR L1, fun L hLodd hLL C₁ hC₁ => ?_⟩
  have hLRl : LR ≤ L := le_trans (le_max_left _ _) hLL
  have hL1 : L1 ≤ L := le_trans (le_max_right _ _) hLL
  obtain ⟨Cr, cr, hCr, hcr, hRt'⟩ := hRt L hLodd hLRl C₁ hC₁
  refine ⟨11 * C₁ + 5200 * CR + 7 * Cr, min cr cR, by positivity, lt_min hcr hcR, ?_⟩
  intro F m S hFL hamb hm hreg s V v hs hsc hcold U hcrit z hz x r hr1 hr2
  subst hFL
  have hodd : Odd F.blockSide := hLodd
  have hL1' : 1 ≤ F.blockSide := hodd.pos
  have hLR : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL1'
  have hscr : s ≤ cr := hsc.trans (min_le_left _ _)
  have hsR : s ≤ cR := hsc.trans (min_le_right _ _)
  obtain ⟨he, -⟩ := closedOrthant_spec hreg (by omega) z
  obtain ⟨-, -, hframe⟩ := hRt' F m S rfl hamb hm hreg s V v hs hscr hcold U hcrit z hz
  obtain ⟨hr1', -⟩ := hRef F m S hodd hL1 hamb hm hreg s V hs hsR hcold
  have h0n : 0 < F.top := Nat.succ_pos _
  have hWj : criticalFieldChain S V v U 0 = chartField (referenceFieldChain S V) U 0 := by
    unfold criticalFieldChain chartChain
    exact Function.update_of_ne h0n.ne _ _
  set W0 := criticalFieldChain S V v U 0 with hW0
  set R0 := referenceFieldChain S V 0 with hR0
  set N : ℝ := (F.blockSide : ℝ) ^ F.top with hN
  have hN1 : 1 ≤ N := one_le_pow₀ hLR
  have hNp : 0 < N := by linarith
  have hNc : (((cellSideLength F).toNat : ℕ) : ℝ) = N := by
    have h1 : 0 < cellSideLength F := cellSideLength_pos hodd.pos
    have h2 : (((cellSideLength F).toNat : ℕ) : ℤ) = cellSideLength F := Int.toNat_of_nonneg h1.le
    have h3 : ((((cellSideLength F).toNat : ℕ) : ℤ) : ℝ) = ((cellSideLength F : ℤ) : ℝ) := by rw [h2]
    rw [Int.cast_natCast] at h3
    rw [h3, hN]
    simp [cellSideLength]
  set Rl : ℝ := ((80 * (9 * (cellSideLength F).toNat) : ℕ) : ℝ) with hRl
  have hRlN : Rl = 720 * N := by
    rw [hRl]
    push_cast
    rw [hNc]
    ring
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrRl : (r : ℝ) ≤ Rl := by
    rw [hRl]
    exact_mod_cast hr2
  set ρ : ℝ := (r : ℝ) / Rl with hρ
  have hRlp : 0 < Rl := by rw [hRlN]; positivity
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, div_le_one hRlp]
    exact hrRl
  have h4θ : 4 * θ ≤ 1 := by linarith
  have h4θ0 : 0 < 4 * θ := by positivity
  have hρp : 0 < ρ ^ (4 * θ) := Real.rpow_pos_of_pos hρ0 _
  set Fil := (patchDomain S z).filter (fun u => supNorm (u - x) ≤ r) with hFil
  rw [sum_frameDefectWeight_eq]
  set T := (Fil ×ˢ (Finset.univ : Finset (Fin 4))).filter (fun p => (p.1 - basisVector p.2, p.2) ∈ bondsOf (patchDomain S z)) with hT
  set Φ : Lattice4 × Fin 4 → F.Site 0 × Fin 4 := fun p => siteBond S z (p.1 - basisVector p.2, p.2) with hΦ
  set G : F.Site 0 × Fin 4 → ℝ := fun c =>
    distFromOne (gaugeTransform (fun x => (patchFrame S V z x)⁻¹) W0 c.1 c.2) ^ 4 with hG
  have hG0 : ∀ c, 0 ≤ G c := fun c => pow_nonneg (distFromOne_nonneg _) 4
  have e1 : ∀ p ∈ T, ‖((framedLatticeField S V z W0 (p.1 - basisVector p.2) p.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 4 = G (Φ p) := by
    intro p _
    have := norm_framedLatticeField_sub_one he V W0 (p.1 - basisVector p.2, p.2)
    simp only [hG, hΦ]
    rw [← this]
  rw [Finset.sum_congr rfl e1]
  have hmemT : ∀ p ∈ T, (p.1 - basisVector p.2, p.2) ∈ bondsOf (patchDomain S z) := fun p hp => (Finset.mem_filter.1 hp).2
  have hΦmem : ∀ p ∈ T, Φ p ∈ patchInnerBonds S z 0 := fun p hp => siteBond_mem_patchInnerBonds hamb hodd (by omega) hreg he (hmemT p hp)
  have hΦinj : Set.InjOn Φ (T : Set (Lattice4 × Fin 4)) := by
    intro p hp q hq e
    have h1 := siteBond_injOn hamb hodd he (Finset.mem_coe.2 (hmemT p hp)) (Finset.mem_coe.2 (hmemT q hq)) e
    obtain ⟨h3, h2⟩ := Prod.mk.inj h1
    rw [h2] at h3
    exact Prod.ext (sub_left_injective h3) h2
  have hsumΦ : ∀ {B : Finset (F.Site 0 × Fin 4)} {g : F.Site 0 × Fin 4 → ℝ}, (∀ c, 0 ≤ g c) → (∀ p ∈ T, Φ p ∈ B) →
      ∑ p ∈ T, g (Φ p) ≤ ∑ c ∈ B, g c := by
    intro B g hg hB
    classical
    rw [← Finset.sum_image (f := g) hΦinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hg _
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
    exact hB p hp
  have hCs : 0 ≤ (11 * C₁ + 5200 * CR + 7 * Cr) * s := by positivity
  by_cases hsm : 2 * (r : ℝ) ≤ N
  · set u₀ : F.Site 0 × Fin 4 → ℝ := fun c => distFromOne (W0 c.1 c.2 * (R0 c.1 c.2)⁻¹) with hu₀
    have hu0 : ∀ c, 0 ≤ u₀ c := fun c => distFromOne_nonneg _
    set ρ₀ : ℝ := CR * s / N with hρ₀
    have hρ₀0 : 0 ≤ ρ₀ := by positivity
    have hpt : ∀ p ∈ T, G (Φ p) ≤ 8 * (u₀ (Φ p) ^ 4 + ρ₀ ^ 4) := by
      intro p hp
      have h1 := distFromOne_gaugeTransform_le W0 R0 (fun x => (patchFrame S V z x)⁻¹) (Φ p).1 (Φ p).2
      have h2 : distFromOne (gaugeTransform (fun x => (patchFrame S V z x)⁻¹) R0 (Φ p).1 (Φ p).2) ≤ ρ₀ := by
        obtain ⟨hb, hb1, hb2⟩ := Finset.mem_filter.1 (hΦmem p hp)
        have h3 := hr1' 0 h0n z hz (Φ p) hb hb1 hb2
        have e2 : levelScale F 0 = 1 / N := by
          unfold levelScale
          rw [hN, one_div_pow]
          rfl
        rw [e2] at h3
        have e3 : CR * s * (1 / N) = ρ₀ := by
          rw [hρ₀]
          ring
        rw [e3] at h3
        exact h3
      have h4 : distFromOne (gaugeTransform (fun x => (patchFrame S V z x)⁻¹) W0 (Φ p).1 (Φ p).2) ≤ u₀ (Φ p) + ρ₀ := by linarith
      exact (pow_le_pow_left₀ (distFromOne_nonneg _) h4 4).trans (add_pow_four_le_eight_mul (hu0 _) hρ₀0)
    have hr2p : (1 : ℝ) ≤ 2 * r := by linarith
    have hnear : ∑ p ∈ T, u₀ (Φ p) ^ 4 ≤ (C₁ * s) ^ 4 * (2 * (r : ℝ) / N) ^ (4 * θ) := by
      have hq : ∑ c ∈ baseBondsNear S (patchSite S z x) (2 * r), u₀ c ^ 4 ≤
          (C₁ * s) ^ 4 * (2 * (r : ℝ) / N) ^ (4 * θ) := by
        have h1 := hcrit.quartic 0 (patchSite S z x) (2 * r) h0n hr2p (by simpa [hN] using hsm)
        simp only [hu₀]
        rw [hWj]
        exact h1
      refine le_trans (hsumΦ (g := fun c => u₀ c ^ 4) (fun c => pow_nonneg (hu0 c) 4) ?_) hq
      intro p hp
      refine Finset.mem_filter.2 ⟨(Finset.mem_filter.1 (hΦmem p hp)).1, ?_⟩
      have hp1 : supNorm (p.1 - x) ≤ r := (Finset.mem_filter.1 (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1).2
      have hd : baseDistance (Φ p).1 (patchSite S z x) ≤ r + 1 := by
        simp only [hΦ, siteBond]
        split_ifs with hs1
        · refine (baseDistance_patchSite_le he _ _).trans ?_
          have e : p.1 - basisVector p.2 - x = (p.1 - x) + -basisVector p.2 := by abel
          rw [e]
          refine (supNorm_add_le _ _).trans ?_
          rw [supNorm_neg, supNorm_basisVector]
          omega
        · refine (baseDistance_patchSite_le he _ _).trans ?_
          have e : p.1 - basisVector p.2 + basisVector p.2 - x = p.1 - x := by abel
          rw [e]
          omega
      have hd' : ((baseDistance (Φ p).1 (patchSite S z x) : ℕ) : ℝ) ≤ (r : ℝ) + 1 := by exact_mod_cast hd
      have e0 : 2 * (r : ℝ) * (F.blockSide : ℝ) ^ 0 = 2 * r := by simp
      rw [e0]
      linarith
    have hcardT : (T.card : ℝ) ≤ 4 * (3 * (r : ℝ)) ^ 4 := by
      have h1 : T.card ≤ Fil.card * 4 := by
        refine (Finset.card_filter_le _ _).trans ?_
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      have h2 := card_filter_supNorm_le x r (patchDomain S z)
      have h3 : (T.card : ℝ) ≤ (Fil.card : ℝ) * 4 := by exact_mod_cast h1
      have h4 : (2 * (r : ℝ) + 1) ^ 4 ≤ (3 * (r : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
      linarith
    have hsumT : ∑ p ∈ T, G (Φ p) ≤ 8 * ((C₁ * s) ^ 4 * (2 * (r : ℝ) / N) ^ (4 * θ)) +
        8 * (4 * (3 * (r : ℝ)) ^ 4 * ρ₀ ^ 4) := by
      calc ∑ p ∈ T, G (Φ p) ≤ ∑ p ∈ T, 8 * (u₀ (Φ p) ^ 4 + ρ₀ ^ 4) := Finset.sum_le_sum hpt
        _ = 8 * ∑ p ∈ T, u₀ (Φ p) ^ 4 + 8 * ((T.card : ℝ) * ρ₀ ^ 4) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
            ring
        _ ≤ _ := by
            have h1 := mul_le_mul_of_nonneg_right hcardT (by positivity : 0 ≤ ρ₀ ^ 4)
            linarith
    have e2 : 2 * (r : ℝ) / N = 1440 * ρ := by
      rw [hρ, hRlN]
      field_simp
      ring
    have hpow1 : (2 * (r : ℝ) / N) ^ (4 * θ) ≤ 1440 * ρ ^ (4 * θ) := by
      rw [e2, Real.mul_rpow (by norm_num) hρ0.le]
      have h1 : (1440 : ℝ) ^ (4 * θ) ≤ 1440 := by
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 1440) h4θ
        rwa [Real.rpow_one] at this
      exact mul_le_mul_of_nonneg_right h1 hρp.le
    have hpow2 : ρ ^ 4 ≤ ρ ^ (4 * θ) := by
      have h1 := Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 (by linarith : 4 * θ ≤ (4 : ℝ))
      have e3 : ρ ^ (4 : ℝ) = ρ ^ 4 := by
        rw [← Real.rpow_natCast]
        norm_num
      rwa [e3] at h1
    have e4 : 4 * (3 * (r : ℝ)) ^ 4 * ρ₀ ^ 4 = 324 * 720 ^ 4 * (CR * s) ^ 4 * ρ ^ 4 := by
      rw [hρ₀, hρ, hRlN]
      field_simp
      ring
    have hA4 : 0 ≤ (C₁ * s) ^ 4 := by positivity
    have hB4 : 0 ≤ (CR * s) ^ 4 := by positivity
    have b1 : 8 * ((C₁ * s) ^ 4 * (2 * (r : ℝ) / N) ^ (4 * θ)) ≤ 11520 * (C₁ * s) ^ 4 * ρ ^ (4 * θ) := by
      have := mul_le_mul_of_nonneg_left hpow1 hA4
      nlinarith
    have b2 : 8 * (4 * (3 * (r : ℝ)) ^ 4 * ρ₀ ^ 4) ≤ 2592 * 720 ^ 4 * (CR * s) ^ 4 * ρ ^ (4 * θ) := by
      rw [e4]
      have := mul_le_mul_of_nonneg_left hpow2 (by positivity : 0 ≤ 2592 * 720 ^ 4 * (CR * s) ^ 4)
      nlinarith
    have hC4 : 11520 * (C₁ * s) ^ 4 + 2592 * 720 ^ 4 * (CR * s) ^ 4 ≤ ((11 * C₁ + 5200 * CR + 7 * Cr) * s) ^ 4 := by
      have x1 : 0 ≤ 11 * C₁ * s := by positivity
      have x2 : 0 ≤ 5200 * CR * s := by positivity
      have x3 : 0 ≤ 7 * Cr * s := by positivity
      have y1 := pow_four_add_pow_four_le x1 x2
      have y2 := pow_le_pow_left₀ (add_nonneg x1 x2) (by linarith : 11 * C₁ * s + 5200 * CR * s ≤ 11 * C₁ * s + 5200 * CR * s + 7 * Cr * s) 4
      have e5 : (11 * C₁ + 5200 * CR + 7 * Cr) * s = 11 * C₁ * s + 5200 * CR * s + 7 * Cr * s := by ring
      have e6 : (11 * C₁ * s) ^ 4 = 14641 * (C₁ * s) ^ 4 := by ring
      have e7 : (5200 * CR * s) ^ 4 = 731161600000000 * (CR * s) ^ 4 := by ring
      rw [e5]
      norm_num at *
      nlinarith
    calc ∑ p ∈ T, G (Φ p) ≤ 11520 * (C₁ * s) ^ 4 * ρ ^ (4 * θ) + 2592 * 720 ^ 4 * (CR * s) ^ 4 * ρ ^ (4 * θ) := by
          linarith
      _ = (11520 * (C₁ * s) ^ 4 + 2592 * 720 ^ 4 * (CR * s) ^ 4) * ρ ^ (4 * θ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC4 hρp.le
  · have hsmall : (1 : ℝ) / 1440 ≤ ρ := by
      have h1 : N < 2 * r := not_le.1 hsm
      rw [hρ, hRlN, le_div_iff₀ (by positivity)]
      nlinarith
    have hw4 : ∑ c ∈ patchInnerBonds S z 0, G c ≤ (Cr * s) ^ 4 := by
      have h2 := hframe 0 h0n
      rw [innerBonds_patchCells hamb hodd he (Nat.zero_le _)] at h2
      exact h2
    have h1 : ∑ p ∈ T, G (Φ p) ≤ (Cr * s) ^ 4 := (hsumΦ (g := G) hG0 hΦmem).trans hw4
    have hp : (1 : ℝ) / 1440 ≤ ρ ^ (4 * θ) := by
      have h2 := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 1440) hsmall h4θ0.le
      have h3 := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 1440) (by norm_num : (1 : ℝ) / 1440 ≤ 1) h4θ
      rw [Real.rpow_one] at h3
      linarith
    have hC7 : (7 * Cr * s) ^ 4 ≤ ((11 * C₁ + 5200 * CR + 7 * Cr) * s) ^ 4 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 4
      have e5 : (11 * C₁ + 5200 * CR + 7 * Cr) * s = 11 * C₁ * s + 5200 * CR * s + 7 * Cr * s := by ring
      have x1 : 0 ≤ 11 * C₁ * s := by positivity
      have x2 : 0 ≤ 5200 * CR * s := by positivity
      rw [e5]
      linarith
    have hB4 : 0 ≤ (Cr * s) ^ 4 := by positivity
    have e6 : (7 * Cr * s) ^ 4 = 2401 * (Cr * s) ^ 4 := by ring
    have h5 : (Cr * s) ^ 4 ≤ 2401 * (Cr * s) ^ 4 * ρ ^ (4 * θ) := by
      have h6 : 2401 * (Cr * s) ^ 4 * (1 / 1440) ≤ 2401 * (Cr * s) ^ 4 * ρ ^ (4 * θ) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      linarith
    rw [e6] at hC7
    exact h1.trans (h5.trans (mul_le_mul_of_nonneg_right hC7 hρp.le))
end YangMills.Construction
end
