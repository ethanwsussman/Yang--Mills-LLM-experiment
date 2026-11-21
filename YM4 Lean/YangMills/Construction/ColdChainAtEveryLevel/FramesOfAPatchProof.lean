import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdChainAtEveryLevel.FramesOfAPatch
import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheTerms
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages FlatPairing LatticeFractionalIntegration PatchPoints
namespace PatchFrames
section Units
theorem polarUnit_smul_of_pos {c : ℝ} (hc : 0 < c) {q : ℍ[ℝ]} (hq : q ≠ 0) :
    polarUnit (c • q) = polarUnit q := by
  have hcq : c • q ≠ 0 := smul_ne_zero hc.ne' hq
  apply Subtype.ext
  rw [coe_polarUnit hcq, coe_polarUnit hq, norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
  congr 1
  have := norm_ne_zero_iff.2 hq
  field_simp
theorem norm_inv_smul_sub_inv_smul_le {q q' : ℍ[ℝ]} (hq : 1 ≤ ‖q‖) (hq' : 1 ≤ ‖q'‖) :
    ‖‖q‖⁻¹ • q - ‖q'‖⁻¹ • q'‖ ≤ 2 * ‖q - q'‖ := by
  have hpos : 0 < ‖q‖ := by linarith
  have hpos' : 0 < ‖q'‖ := by linarith
  have hsplit : ‖q‖⁻¹ • q - ‖q'‖⁻¹ • q' = ‖q‖⁻¹ • (q - q') + (‖q‖⁻¹ - ‖q'‖⁻¹) • q' := by
    rw [smul_sub, sub_smul]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_inv, norm_norm, Real.norm_eq_abs]
  have hinv : ‖q‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  have hdiff : |‖q‖⁻¹ - ‖q'‖⁻¹| * ‖q'‖ = |‖q'‖ - ‖q‖| * ‖q‖⁻¹ := by
    have : ‖q‖⁻¹ - ‖q'‖⁻¹ = (‖q'‖ - ‖q‖) * ‖q‖⁻¹ * ‖q'‖⁻¹ := by field_simp
    rw [this, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hpos), abs_of_pos (inv_pos.2 hpos')]
    field_simp
  rw [hdiff]
  have hrev : |‖q'‖ - ‖q‖| ≤ ‖q - q'‖ := by
    have := abs_norm_sub_norm_le q' q
    rwa [norm_sub_rev] at this
  have hnn : 0 ≤ ‖q - q'‖ := norm_nonneg _
  calc ‖q‖⁻¹ * ‖q - q'‖ + |‖q'‖ - ‖q‖| * ‖q‖⁻¹ ≤ 1 * ‖q - q'‖ + ‖q - q'‖ * 1 :=
        add_le_add (mul_le_mul_of_nonneg_right hinv hnn)
          (mul_le_mul hrev hinv (inv_pos.2 hpos).le hnn)
    _ = _ := by ring
theorem norm_polarUnit_sub_le {p p' : ℍ[ℝ]} (hp : 1 / 2 ≤ p.re) (hp' : 1 / 2 ≤ p'.re) :
    ‖((polarUnit p : UnitQuaternion) : ℍ[ℝ]) - ((polarUnit p' : UnitQuaternion) : ℍ[ℝ])‖ ≤
      4 * ‖pureComponent p - pureComponent p'‖ + 8 * ‖pureComponent p'‖ * |p.re - p'.re| := by
  have ha : 0 < p.re := by linarith
  have ha' : 0 < p'.re := by linarith
  set t : ℍ[ℝ] := 1 + p.re⁻¹ • pureComponent p with ht
  set t' : ℍ[ℝ] := 1 + p'.re⁻¹ • pureComponent p' with ht'
  have hpure_re : ∀ q : ℍ[ℝ], (pureComponent q).re = 0 := by
    intro q
    simp [pureComponent]
  have ht1 : t.re = 1 := by simp [ht, hpure_re]
  have ht1' : t'.re = 1 := by simp [ht', hpure_re]
  have hn : 1 ≤ ‖t‖ := by simpa [ht1] using quaternion_re_le_norm t
  have hn' : 1 ≤ ‖t'‖ := by simpa [ht1'] using quaternion_re_le_norm t'
  have hne : ∀ q : ℍ[ℝ], 1 ≤ ‖q‖ → q ≠ 0 := fun q hq h0 => by
    rw [h0, norm_zero] at hq
    linarith
  have hreal : ∀ c : ℝ, c • (1 : ℍ[ℝ]) = (c : ℍ[ℝ]) := fun c => by
    ext <;> simp
  have ep : p = p.re • t := by
    rw [ht, smul_add, smul_smul, mul_inv_cancel₀ ha.ne', one_smul, hreal]
    exact (re_add_pureComponent p).symm
  have ep' : p' = p'.re • t' := by
    rw [ht', smul_add, smul_smul, mul_inv_cancel₀ ha'.ne', one_smul, hreal]
    exact (re_add_pureComponent p').symm
  have hU : polarUnit p = polarUnit t := by
    conv_lhs => rw [ep]
    exact polarUnit_smul_of_pos ha (hne t hn)
  have hU' : polarUnit p' = polarUnit t' := by
    conv_lhs => rw [ep']
    exact polarUnit_smul_of_pos ha' (hne t' hn')
  rw [hU, hU', coe_polarUnit (hne t hn), coe_polarUnit (hne t' hn')]
  refine (norm_inv_smul_sub_inv_smul_le hn hn').trans ?_
  have e : t - t' = p.re⁻¹ • (pureComponent p - pureComponent p') +
      (p.re⁻¹ - p'.re⁻¹) • pureComponent p' := by
    rw [ht, ht', smul_sub, sub_smul]
    abel
  have h1 : p.re⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ ha (by norm_num)]
    linarith
  have h2 : p'.re⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ ha' (by norm_num)]
    linarith
  have h3 : |p.re⁻¹ - p'.re⁻¹| ≤ 4 * |p.re - p'.re| := by
    have : p.re⁻¹ - p'.re⁻¹ = (p'.re - p.re) * p.re⁻¹ * p'.re⁻¹ := by field_simp
    rw [this, abs_mul, abs_mul, abs_of_pos (inv_pos.2 ha), abs_of_pos (inv_pos.2 ha'), abs_sub_comm]
    have h4 : p.re⁻¹ * p'.re⁻¹ ≤ 2 * 2 := mul_le_mul h1 h2 (inv_pos.2 ha').le (by norm_num)
    calc |p.re - p'.re| * p.re⁻¹ * p'.re⁻¹ = |p.re - p'.re| * (p.re⁻¹ * p'.re⁻¹) := by ring
      _ ≤ |p.re - p'.re| * (2 * 2) := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
      _ = _ := by ring
  have h5 : ‖t - t'‖ ≤ 2 * ‖pureComponent p - pureComponent p'‖ +
      4 * |p.re - p'.re| * ‖pureComponent p'‖ := by
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ha)]
    exact add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
      (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
  nlinarith [norm_nonneg (pureComponent p'), abs_nonneg (p.re - p'.re)]
end Units
section Proof
theorem abs_re_le_norm (q : ℍ[ℝ]) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
theorem supNorm_zero : supNorm (0 : Lattice4) = 0 := by apply _root_.YangMills.Construction.LatticePaths.supNorm_zero <;> assumption
end Proof
end PatchFrames
open PatchFrames in
theorem PatchFrames.patchFrameExistence (hLoc : patchPairingLocalFormStatement)
    (hNF : nearlyFlatPairingStatement) : patchFrameExistenceStatement := by
  obtain ⟨B, C, c, hB, hC, hc, hLf⟩ := hLoc
  obtain ⟨C1, r, hC1, hr, hNF'⟩ := hNF B hB
  have hB0 : 0 < B := by linarith
  set r0 : ℝ := min r (1 / (8 * (B + 1))) with hr0
  have hr0p : 0 < r0 := lt_min hr (by positivity)
  have hr0r : r0 ≤ r := min_le_left _ _
  have hr0b : r0 ≤ 1 / (8 * (B + 1)) := min_le_right _ _
  have hr0B : (B + 1) * r0 ≤ 1 / 8 := by
    have h1 := mul_le_mul_of_nonneg_left hr0b (by linarith : 0 ≤ B + 1)
    refine h1.trans (le_of_eq ?_)
    field_simp
  set Ct : ℝ := (C1 + 8 + 16 * (B + 1)) * C with hCt
  refine ⟨Ct, r0, min c (1 / C), by positivity, hr0p, lt_min hc (by positivity), ?_⟩
  intro F m S hodd hamb hm hreg s V hs hsc hcold z hz
  have hL := hodd.pos
  have hsc1 : s ≤ c := hsc.trans (min_le_left _ _)
  have hsc2 : s ≤ 1 / C := hsc.trans (min_le_right _ _)
  have hρ0 : 0 ≤ C * s := by positivity
  have hρ1 : C * s ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hsc2 hC.le
    rwa [mul_one_div_cancel hC.ne'] at this
  obtain ⟨P0, P1, h0, h1, hsym, hlow, hpair, -⟩ := hLf F m S hodd hamb hm hreg s V hs hsc1 hcold z hz
  have hNz : (0 : ℝ) < GaugeMap.cellSideLength F := by exact_mod_cast cellSideLength_pos (F := F) hL
  obtain ⟨κ, hκd⟩ : ∃ κ : ℝ, κ = 1 / (GaugeMap.cellSideLength F : ℝ) := ⟨_, rfl⟩
  rw [← hκd] at h0 h1
  have hκ0 : 0 < κ := by rw [hκd]; positivity
  have hκN : κ * GaugeMap.cellSideLength F = 1 := by rw [hκd]; field_simp
  obtain ⟨n1, -, -⟩ := hNF' κ (C * s) (patchLocalSites S z) P0 P1 hκ0.le hρ0 hρ1 h0 h1 hsym hlow
  have hD : ∀ a ∈ GaugeMap.patchDomain S z, a ∈ patchLocalSites S z := fun a ha =>
    ⟨patchDomain_coord_bounds ha, patchSite_mem_sitesOfCells hamb hodd hreg (by omega) ha⟩
  have hlen0 : ∀ v : Lattice4, scaledPairNorm κ ((0 : Lattice4), v) = κ * supNorm v := by
    intro v
    simp [scaledPairNorm, supNorm_zero]
  have hclose : ∀ a ∈ patchLocalSites S z, ∀ b ∈ patchLocalSites S z, κ * supNorm (b - a) ≤ r0 →
      1 / 2 ≤ (pairingValue P0 P1 a b).re := by
    intro a ha b hb hd
    have e : ((a, a) : Lattice4 × Lattice4) + ((0 : Lattice4), b - a) = (a, b) := by simp
    have f0 := h0.norm_sub_le (x := (a, a)) (a := ((0 : Lattice4), b - a)) ⟨ha, ha⟩ (by rw [e]; exact ⟨ha, hb⟩)
    have f1 := h1.norm_sub_le (x := (a, a)) (a := ((0 : Lattice4), b - a)) ⟨ha, ha⟩ (by rw [e]; exact ⟨ha, hb⟩)
    rw [e, hlen0] at f0 f1
    have hlo := hlow a ha
    have hd0 : 0 ≤ κ * supNorm (b - a) := by positivity
    have e2 : (pairingValue P0 P1 a b).re = (pairingValue P0 P1 a a).re + (P0 (a, b) - P0 (a, a)) +
        (P1 (a, b) - P1 (a, a)).re := by
      simp [pairingValue]
      ring
    have g0 : |P0 (a, b) - P0 (a, a)| ≤ B * (κ * supNorm (b - a)) := f0
    have g1 : |(P1 (a, b) - P1 (a, a)).re| ≤ 1 * (κ * supNorm (b - a)) :=
      (abs_re_le_norm _).trans (f1.trans (mul_le_mul_of_nonneg_right hρ1 hd0))
    have g2 : (B + 1) * (κ * supNorm (b - a)) ≤ 1 / 8 :=
      (mul_le_mul_of_nonneg_left hd (by linarith)).trans hr0B
    have g3 := (abs_le.1 g0).1
    have g4 := (abs_le.1 g1).1
    rw [e2]
    nlinarith
  have hne : ∀ a ∈ patchLocalSites S z, ∀ b ∈ patchLocalSites S z, κ * supNorm (b - a) ≤ r0 →
      pairingValue P0 P1 a b ≠ 0 := by
    intro a ha b hb hd h
    have := hclose a ha b hb hd
    rw [h] at this
    simp at this
    linarith
  have hdist : ∀ v : Lattice4, (supNorm v : ℝ) ≤ r0 * GaugeMap.cellSideLength F → κ * supNorm v ≤ r0 := by
    intro v hv
    have h2 := mul_le_mul_of_nonneg_left hv hκ0.le
    calc κ * supNorm v ≤ κ * (r0 * GaugeMap.cellSideLength F) := h2
      _ = r0 * (κ * GaugeMap.cellSideLength F) := by ring
      _ = r0 := by rw [hκN, mul_one]
  have hCtC : (C1 + 8 + 16 * (B + 1)) * (C * s) = Ct * s := by
    rw [hCt]
    ring
  refine ⟨fun a b => polarUnit (pairingValue P0 P1 a b), ⟨fun a b => ?_, fun a ha b hb hd => ?_,
    fun a ha b hb hd => ?_, fun hN1 a e e' he he' ha hae hae' haee => ?_⟩⟩
  · show polarUnit (pairingValue P0 P1 b a) = _
    rw [hsym a b, polarUnit_star]
  · have h2 := n1 a (hD a ha) b (hD b hb) ((hdist _ hd).trans hr0r)
    refine h2.trans ?_
    have h3 : 0 ≤ κ * supNorm (b - a) := by positivity
    have h4 : C1 * (C * s) ≤ Ct * s := by
      rw [← hCtC]
      refine mul_le_mul_of_nonneg_right ?_ hρ0
      nlinarith
    have e5 : (supNorm (b - a) : ℝ) / GaugeMap.cellSideLength F = κ * supNorm (b - a) := by
      rw [hκd]
      ring
    rw [e5]
    exact mul_le_mul_of_nonneg_right h4 h3
  · exact hpair a (hD a ha) b (hD b hb) (hne a (hD a ha) b (hD b hb) (hdist _ hd))
  · have ha' := hD a ha
    have hae1 := hD _ hae
    have hae2 := hD _ hae'
    have hae3 := hD _ haee
    have hκr : κ ≤ r0 := by
      have := mul_le_mul_of_nonneg_left hN1 hκ0.le
      calc κ = κ * 1 := (mul_one _).symm
        _ ≤ κ * (r0 * GaugeMap.cellSideLength F) := this
        _ = r0 * (κ * GaugeMap.cellSideLength F) := by ring
        _ = r0 := by rw [hκN, mul_one]
    have hlen1 : ∀ v : Lattice4, supNorm v = 1 → κ * supNorm v ≤ r0 := fun v hv => by
      rw [hv]
      simpa using hκr
    have c1 := hclose a ha' (a + e) hae1 (by rw [add_sub_cancel_left]; exact hlen1 e he)
    have c2 := hclose (a + e') hae2 (a + e' + e) hae3 (by rw [add_sub_cancel_left]; exact hlen1 e he)
    have hun := norm_polarUnit_sub_le c1 c2
    refine hun.trans ?_
    have lenA : scaledPairNorm κ ((0 : Lattice4), e) = κ := by rw [hlen0, he]; simp
    have lenB : scaledPairNorm κ (e', e') = 2 * κ := by
      simp only [scaledPairNorm, he']
      push_cast
      ring
    have eA : ((a, a) : Lattice4 × Lattice4) + ((0 : Lattice4), e) = (a, a + e) := by simp
    have eB : ((a, a) : Lattice4 × Lattice4) + (e', e') = (a + e', a + e') := by simp
    have eBA : ((a + e', a + e') : Lattice4 × Lattice4) + ((0 : Lattice4), e) = (a + e', a + e' + e) := by simp
    have eC : ((a, a + e) : Lattice4 × Lattice4) + (e', e') = (a + e', a + e' + e) := by
      simp only [Prod.mk_add_mk]
      congr 1
      abel
    have s1 := h1.norm_second_diff_le (x := (a, a)) (a := ((0 : Lattice4), e)) (b := (e', e')) ⟨ha', ha'⟩
      (by rw [eA]; exact ⟨ha', hae1⟩) (by rw [eB]; exact ⟨hae2, hae2⟩) (by rw [eB, eBA]; exact ⟨hae2, hae3⟩)
    rw [eB, eBA, eA, lenA, lenB] at s1
    have f1 := h1.norm_sub_le (x := (a + e', a + e')) (a := ((0 : Lattice4), e)) ⟨hae2, hae2⟩
      (by rw [eBA]; exact ⟨hae2, hae3⟩)
    rw [eBA, lenA] at f1
    have f2 := h0.norm_sub_le (x := (a, a + e)) (a := (e', e')) ⟨ha', hae1⟩ (by rw [eC]; exact ⟨hae2, hae3⟩)
    have f3 := h1.norm_sub_le (x := (a, a + e)) (a := (e', e')) ⟨ha', hae1⟩ (by rw [eC]; exact ⟨hae2, hae3⟩)
    rw [eC, lenB] at f2 f3
    have hpd : ∀ u v : Lattice4, pureComponent (pairingValue P0 P1 u v) = pureComponent (P1 (u, v)) := by
      intro u v
      simp only [pairingValue, pureComponent_add, pureComponent_coe, zero_add]
    have hdiag : ∀ u : Lattice4, pureComponent (P1 (u, u)) = 0 := by
      intro u
      rw [← hpd]
      exact pureComponent_eq_zero (hsym u u).symm
    set A := pureComponent (P1 (a, a + e)) with hA
    set A' := pureComponent (P1 (a + e', a + e' + e)) with hA'
    have hAA : ‖A - A'‖ ≤ C * s * κ * (2 * κ) := by
      have e6 : A - A' = - pureComponent ((P1 (a + e', a + e' + e) - P1 (a + e', a + e')) -
          (P1 (a, a + e) - P1 (a, a))) := by
        rw [pureComponent_sub, pureComponent_sub, pureComponent_sub, hdiag, hdiag]
        simp only [sub_zero, neg_sub]
        rfl
      rw [e6, norm_neg]
      exact (norm_pureComponent_le _).trans s1
    have hA'n : ‖A'‖ ≤ C * s * κ := by
      have e6 : A' = pureComponent (P1 (a + e', a + e' + e) - P1 (a + e', a + e')) := by
        rw [pureComponent_sub, hdiag, sub_zero]
      rw [e6]
      exact (norm_pureComponent_le _).trans f1
    have hre : |(pairingValue P0 P1 a (a + e)).re - (pairingValue P0 P1 (a + e') (a + e' + e)).re| ≤
        (B + 1) * (2 * κ) := by
      have e7 : (pairingValue P0 P1 a (a + e)).re - (pairingValue P0 P1 (a + e') (a + e' + e)).re =
          -((P0 (a + e', a + e' + e) - P0 (a, a + e)) + (P1 (a + e', a + e' + e) - P1 (a, a + e)).re) := by
        simp [pairingValue]
        ring
      rw [e7, abs_neg]
      refine (abs_add_le _ _).trans ?_
      have g0 : |P0 (a + e', a + e' + e) - P0 (a, a + e)| ≤ B * (2 * κ) := f2
      have g1 : |(P1 (a + e', a + e' + e) - P1 (a, a + e)).re| ≤ 1 * (2 * κ) :=
        (abs_re_le_norm _).trans (f3.trans (mul_le_mul_of_nonneg_right hρ1 (by positivity)))
      nlinarith
    rw [hpd, hpd, ← hA, ← hA']
    have hκsq : 1 / (GaugeMap.cellSideLength F : ℝ) ^ 2 = κ ^ 2 := by
      rw [hκd]
      field_simp
    have hgoal : Ct * s / (GaugeMap.cellSideLength F : ℝ) ^ 2 = (C1 + 8 + 16 * (B + 1)) * (C * s) * κ ^ 2 := by
      rw [hCtC, div_eq_mul_one_div, hκsq]
    rw [hgoal]
    have t1 : 4 * ‖A - A'‖ ≤ 8 * (C * s) * κ ^ 2 := by
      have e8 : C * s * κ * (2 * κ) = 2 * (C * s) * κ ^ 2 := by ring
      rw [e8] at hAA
      linarith
    have t2 : 8 * ‖A'‖ * |(pairingValue P0 P1 a (a + e)).re - (pairingValue P0 P1 (a + e') (a + e' + e)).re| ≤
        16 * (B + 1) * (C * s) * κ ^ 2 := by
      have hp : ‖A'‖ * |(pairingValue P0 P1 a (a + e)).re - (pairingValue P0 P1 (a + e') (a + e' + e)).re| ≤
          (C * s * κ) * ((B + 1) * (2 * κ)) :=
        mul_le_mul hA'n hre (abs_nonneg _) (by positivity)
      have e9 : C * s * κ * ((B + 1) * (2 * κ)) = 2 * (B + 1) * (C * s) * κ ^ 2 := by ring
      rw [e9] at hp
      calc _ = 8 * (‖A'‖ * |(pairingValue P0 P1 a (a + e)).re -
              (pairingValue P0 P1 (a + e') (a + e' + e)).re|) := by ring
        _ ≤ 8 * (2 * (B + 1) * (C * s) * κ ^ 2) := by linarith
        _ = _ := by ring
    have t3 : 0 ≤ C1 * (C * s) * κ ^ 2 := by positivity
    have e10 : (C1 + 8 + 16 * (B + 1)) * (C * s) * κ ^ 2 =
        C1 * (C * s) * κ ^ 2 + 8 * (C * s) * κ ^ 2 + 16 * (B + 1) * (C * s) * κ ^ 2 := by ring
    rw [e10]
    linarith
end YangMills.Construction
end
