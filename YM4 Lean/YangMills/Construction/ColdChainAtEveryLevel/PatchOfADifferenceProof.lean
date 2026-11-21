import YangMills.Construction.ColdChainAtEveryLevel.PatchOfADifference
import YangMills.Construction.ColdChainAtEveryLevel.PotentialsInAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.PatchDifferences
open BlockAverages GaugeMap PatchPoints LatticeFractionalIntegration BondShares PatchFrames FiniteDifferences
section
variable {F : BlockFrame} {S : Finset F.Cell} {V : F.GaugeField F.top} {z : F.Cell} {R : Lattice4 → Lattice4 → UnitQuaternion} {Cs r : ℝ}
theorem patchCubicKernel_nonneg {f : F.Site 0 → ℝ} (hf : ∀ t, 0 ≤ f t) (t : F.Site 0) : 0 ≤ patchCubicKernel S z f t := by apply _root_.YangMills.Construction.PatchPotentials.patchCubicKernel_nonneg <;> assumption
def remainderCurl (R : Lattice4 → Lattice4 → UnitQuaternion) (S : Finset F.Cell) (V : F.GaugeField F.top) (z : F.Cell) (ξ : F.Site 0 → ℍ[ℝ]) :
    F.Site 0 → ℝ :=
  restrictToPatch S z fun t => curlNormAt S z (remainderForm R S V z ξ) (patchChart S z t)
theorem remainderCurl_nonneg (ξ : F.Site 0 → ℍ[ℝ]) (t : F.Site 0) : 0 ≤ remainderCurl R S V z ξ t :=
  restrictToPatch_nonneg (fun _ => curlNormAt_nonneg _ _) t
theorem coeff_div_nonneg {a Cs N : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ Cs) (hN : 0 < N) : 0 ≤ a * Cs / N :=
  div_nonneg (mul_nonneg ha hC) hN.le
theorem coeff_div_sq_nonneg {a Cs N : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ Cs) (hN : 0 < N) : 0 ≤ a * Cs / N ^ 2 :=
  div_nonneg (mul_nonneg ha hC) (pow_pos hN 2).le
theorem stepNorms_patchSite_le {H Gk Ch} (hk : PatchPathKernels S z H Gk Ch) (hCh : 0 ≤ Ch) (hF : IsPatchFrame S V z R Cs r)
    (hr1 : 1 ≤ r * cellSideLength F) (hC : 0 ≤ Cs) (hN1 : (1 : ℝ) ≤ cellSideLength F) (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (hP : patchSiteSet S z ⊆ sitesOfCells S 0)
    (ξ : F.Site 0 → ℍ[ℝ]) {a : Lattice4} (ha : a ∈ patchDomain S z) :
    stepNorms S z (remainderMean R S V z ξ) (patchSite S z a) ≤
      8 * Cs / (cellSideLength F : ℝ) * neighbourSum S z (restrictToPatch S z (sectionNormOn S ξ)) (patchSite S z a) +
        4 * Ch * patchCubicKernel S z (remainderCurl R S V z ξ) (patchSite S z a) := by
  classical
  obtain ⟨N, hNd⟩ : ∃ N : ℝ, N = (cellSideLength F : ℝ) := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hNd]; linarith
  obtain ⟨A, hAd⟩ : ∃ A, A = neighbourSum S z (restrictToPatch S z (sectionNormOn S ξ)) (patchSite S z a) := ⟨_, rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T, T = patchCubicKernel S z (remainderCurl R S V z ξ) (patchSite S z a) := ⟨_, rfl⟩
  have hnξ0 : ∀ t, 0 ≤ restrictToPatch S z (sectionNormOn S ξ) t := restrictToPatch_nonneg (sectionNormOn_nonneg ξ)
  have hA0 : 0 ≤ A := hAd ▸ neighbourSum_nonneg hnξ0 _
  have hT0 : 0 ≤ T := hTd ▸ patchCubicKernel_nonneg (remainderCurl_nonneg ξ) _
  rw [stepNorms_patchSite hamb hodd he _ ha, ← hAd, ← hTd, ← hNd]
  have hone : ∀ i : Fin 4, (if a + basisVector i ∈ patchDomain S z then
      ‖remainderMean R S V z ξ (a + basisVector i) - remainderMean R S V z ξ a‖ else 0) ≤ 2 * Cs / N * A + Ch * T := by
    intro i
    have hb0 : 0 ≤ 2 * Cs / N * A + Ch * T :=
      add_nonneg (mul_nonneg (coeff_div_nonneg (by norm_num) hC hN0) hA0) (mul_nonneg hCh hT0)
    split_ifs with h
    · have h1 := norm_randomPathMean_step_le hk hCh hamb hodd he (remainderForm R S V z ξ) ha h
      have h2 := norm_remainderForm_le hF hr1 ξ ha h hC
      rw [← hNd] at h2
      have h3 : ‖ξ (patchSite S z (a + basisVector i))‖ ≤ A := by
        rw [norm_eq_restrictToPatch_sectionNormOn hP ξ (Finset.mem_image_of_mem _ h), hAd]
        exact (le_neighbourSum_of_bond hnξ0 he ha h).1
      have h4 : 2 * Cs / N * ‖ξ (patchSite S z (a + basisVector i))‖ ≤ 2 * Cs / N * A :=
        mul_le_mul_of_nonneg_left h3 (coeff_div_nonneg (by norm_num) hC hN0)
      have e : remainderMean R S V z ξ (a + basisVector i) - remainderMean R S V z ξ a =
          randomPathMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (remainderForm R S V z ξ) (a + basisVector i) -
            randomPathMean (9 * (cellSideLength F).toNat) (fun _ => 12 * cellSideLength F) (remainderForm R S V z ξ) a := rfl
      rw [e]
      have h5 : Ch * patchCubicKernel S z (restrictToPatch S z fun t => curlNormAt S z (remainderForm R S V z ξ) (patchChart S z t))
          (patchSite S z a) = Ch * T := by rw [hTd]; rfl
      rw [h5] at h1
      linarith
    · exact hb0
  calc _ ≤ ∑ _i : Fin 4, (2 * Cs / N * A + Ch * T) := Finset.sum_le_sum fun i _ => hone i
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
theorem remainder_total_arith {K3 Ch Bc K Cs N Tx Td G Tot W : ℝ} (hK3 : 0 ≤ K3) (hCh : 0 ≤ Ch) (hBc : 0 ≤ Bc) (hK : 0 ≤ K) (hC : 0 ≤ Cs)
    (hN : 0 < N) (hTx : 0 ≤ Tx) (hTd : 0 ≤ Td)
    (h1 : Tot ≤ 8 * Cs / N * (K3 * Tx) + 4 * Ch * W) (h2 : W ≤ Bc * (K * (K * N * G)))
    (h3 : G ≤ 192 * Cs / N ^ 2 * (K3 * (K3 * Tx)) + 128 * Cs / N * (K3 * (K3 * Td))) :
    Tot ≤ (8 * K3 + 4 * Ch * Bc * K ^ 2 * 192 * K3 ^ 2) * Cs * (Tx / N + Td) := by
  have h4 : Bc * (K * (K * N * G)) ≤
      Bc * (K * (K * N * (192 * Cs / N ^ 2 * (K3 * (K3 * Tx)) + 128 * Cs / N * (K3 * (K3 * Td))))) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 ?_) hK) hBc
    positivity
  have e1 : Bc * (K * (K * N * (192 * Cs / N ^ 2 * (K3 * (K3 * Tx)) + 128 * Cs / N * (K3 * (K3 * Td))))) =
      Bc * K ^ 2 * K3 ^ 2 * Cs * (192 * (Tx / N) + 128 * Td) := by
    field_simp
  have e2 : 8 * Cs / N * (K3 * Tx) = 8 * K3 * Cs * (Tx / N) := by
    field_simp
  have hW : 4 * Ch * W ≤ 4 * Ch * (Bc * K ^ 2 * K3 ^ 2 * Cs * (192 * (Tx / N) + 128 * Td)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hpos : 0 ≤ 4 * Ch * (Bc * K ^ 2 * K3 ^ 2 * Cs) := by positivity
  have e3 : (8 * K3 + 4 * Ch * Bc * K ^ 2 * 192 * K3 ^ 2) * Cs * (Tx / N + Td) =
      8 * K3 * Cs * (Tx / N) + 8 * K3 * Cs * Td + 4 * Ch * (Bc * K ^ 2 * K3 ^ 2 * Cs) * (192 * (Tx / N) + 192 * Td) := by
    ring
  have e4 : 4 * Ch * (Bc * K ^ 2 * K3 ^ 2 * Cs * (192 * (Tx / N) + 128 * Td)) =
      4 * Ch * (Bc * K ^ 2 * K3 ^ 2 * Cs) * (192 * (Tx / N) + 128 * Td) := by ring
  have h5 : 4 * Ch * (Bc * K ^ 2 * K3 ^ 2 * Cs) * (192 * (Tx / N) + 128 * Td) ≤
      4 * Ch * (Bc * K ^ 2 * K3 ^ 2 * Cs) * (192 * (Tx / N) + 192 * Td) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos
  have h6 : 0 ≤ 8 * K3 * Cs * Td := by positivity
  rw [e3]
  rw [e2] at h1
  rw [e4] at hW
  linarith
theorem sum_cellBall_stepNorms_le {H Gk Ch} (hk : PatchPathKernels S z H Gk Ch) (hCh : 0 ≤ Ch) (hF : IsPatchFrame S V z R Cs r)
    (hr1 : 1 ≤ r * cellSideLength F) (hC : 0 ≤ Cs) (hC1 : Cs ≤ 1) (hN1 : (1 : ℝ) ≤ cellSideLength F) (hamb : IsAdmissibleAmbient F)
    (hodd : Odd F.blockSide) {m : ℕ} (hreg : IsOrthantRegular S m) (hm : 32 ≤ m) (hz : z ∈ S)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (ξ : F.Site 0 → ℍ[ℝ]) {Md Lf Sr : (F.Site 0 → ℝ) → F.Cell → ℝ} {σ : F.Cell → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hN : CellNormFamily S Md Lf Sr σ K) :
    ∑ y ∈ cellBall S z 20, Md (stepNorms S z (remainderMean R S V z ξ)) y ≤
      (8 * (1 + 8 * K * 81) + 4 * Ch * 41 ^ 4 * K ^ 2 * 192 * (1 + 8 * K * 81) ^ 2) * Cs *
        ∑ y ∈ cellBall S z 20, (Md (restrictToPatch S z (sectionNormOn S ξ)) y / (cellSideLength F : ℝ) +
          Md (restrictToPatch S z (formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ))) y) := by
  classical
  have hP : patchSiteSet S z ⊆ sitesOfCells S 0 := fun t ht => by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ht
    exact patchSite_mem_sitesOfCells hamb hodd hreg hm hb
  have hcell : ∀ y ∈ S, y ∉ cellBall S z 20 → ∀ x ∈ cellSites S y, x ∉ patchSiteSet S z := by
    intro y hy hn x hx hxp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hxp
    have h1 := (enclosingCell_patchSite hamb hodd hreg hm hb).2
    rw [(Finset.mem_filter.1 hx).2] at h1
    exact hn (Finset.mem_filter.2 ⟨hy, by rw [cellSupDist_symm]; exact h1⟩)
  have hN0 : (0 : ℝ) < cellSideLength F := by linarith
  set nξ := restrictToPatch S z (sectionNormOn S ξ) with hnξ
  set nd := restrictToPatch S z (formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ)) with hnd
  set Dl := stepNorms S z (remainderMean R S V z ξ) with hDl
  have hnξ0 : ∀ t, 0 ≤ nξ t := restrictToPatch_nonneg (sectionNormOn_nonneg ξ)
  have hnd0 : ∀ t, 0 ≤ nd t := restrictToPatch_nonneg (formNormOn_nonneg _)
  have hoffξ : ∀ t, t ∉ patchSiteSet S z → nξ t = 0 := fun t ht => restrictToPatch_of_not_mem ht
  have hoffd : ∀ t, t ∉ patchSiteSet S z → nd t = 0 := fun t ht => restrictToPatch_of_not_mem ht
  have hoffnb : ∀ (f : F.Site 0 → ℝ) t, t ∉ patchSiteSet S z → neighbourSum S z f t = 0 := fun f t ht => restrictToPatch_of_not_mem ht
  set K3 : ℝ := 1 + 8 * K * 81 with hK3
  have hK30 : 0 ≤ K3 := by
    rw [hK3]
    have : 0 ≤ 8 * K * 81 := mul_nonneg (mul_nonneg (by norm_num) hK) (by norm_num)
    linarith
  have tot1 : ∀ {f : F.Site 0 → ℝ}, (∀ t, t ∉ patchSiteSet S z → f t = 0) →
      ∑ y ∈ cellBall S z 20, Md (neighbourSum S z f) y ≤ K3 * ∑ y ∈ cellBall S z 20, Md f y :=
    fun hf => sum_cellBall_neighbourSum_le hK hN hamb hP hcell hf
  have tot2 : ∀ {f : F.Site 0 → ℝ}, (∀ t, t ∉ patchSiteSet S z → f t = 0) →
      ∑ y ∈ cellBall S z 20, Md (neighbourSum S z (neighbourSum S z f)) y ≤ K3 * (K3 * ∑ y ∈ cellBall S z 20, Md f y) := fun hf =>
    (tot1 (hoffnb _)).trans (mul_le_mul_of_nonneg_left (tot1 hf) hK30)
  set Tx := ∑ y ∈ cellBall S z 20, Md nξ y with hTx
  set Td := ∑ y ∈ cellBall S z 20, Md nd y with hTd
  have hTx0 : 0 ≤ Tx := Finset.sum_nonneg fun _ _ => hN.isSeminorm_base.nonneg _ _
  have hTd0 : 0 ≤ Td := Finset.sum_nonneg fun _ _ => hN.isSeminorm_base.nonneg _ _
  set Gc := remainderCurl R S V z ξ with hGc
  have hGc0 : ∀ t, 0 ≤ Gc t := remainderCurl_nonneg ξ
  set G := ∑ x ∈ cellBall S z 20, Md (restrictToPatch S z Gc) x with hG
  have hstep : ∀ y, Md Dl y ≤ 8 * Cs / (cellSideLength F : ℝ) * Md (neighbourSum S z nξ) y + 4 * Ch * Md (patchCubicKernel S z Gc) y := by
    intro y
    have hc1 : 0 ≤ 8 * Cs / (cellSideLength F : ℝ) := coeff_div_nonneg (by norm_num) hC hN0
    have hc2 : 0 ≤ 4 * Ch := mul_nonneg (by norm_num) hCh
    have h1 : Md Dl y ≤ Md (fun x => 8 * Cs / (cellSideLength F : ℝ) * neighbourSum S z nξ x + 4 * Ch * patchCubicKernel S z Gc x) y := by
      refine hN.isSeminorm_base.mono_abs _ _ _ fun x _ => ?_
      have hr0 : 0 ≤ 8 * Cs / (cellSideLength F : ℝ) * neighbourSum S z nξ x + 4 * Ch * patchCubicKernel S z Gc x :=
        add_nonneg (mul_nonneg hc1 (neighbourSum_nonneg hnξ0 x)) (mul_nonneg hc2 (patchCubicKernel_nonneg hGc0 x))
      rw [abs_of_nonneg hr0, abs_of_nonneg (stepNorms_nonneg _ _)]
      by_cases hx' : x ∈ patchSiteSet S z
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx'
        exact stepNorms_patchSite_le hk hCh hF hr1 hC hN1 hamb hodd he hP ξ ha
      · have hz0 : stepNorms S z (remainderMean R S V z ξ) x = 0 := by simp [stepNorms, hx']
        rw [hz0]
        exact hr0
    refine h1.trans ((hN.isSeminorm_base.add_le _ _ y).trans ?_)
    rw [hN.isSeminorm_base.smul, hN.isSeminorm_base.smul, abs_of_nonneg hc1, abs_of_nonneg hc2]
  have hthrough : ∀ y, Md (patchCubicKernel S z Gc) y ≤ K * ((K * (cellSideLength F : ℝ)) * G) := by
    intro y
    refine (hN.base_le_target _ y).trans ((hN.kernel_le z hz Gc y).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ hK
    rw [hG, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hN.source_le _ x
  have hcard : ((cellBall S z 20).card : ℝ) ≤ 41 ^ 4 := by
    have := card_le_of_cellSupDist_le hamb z 20 (cellBall S z 20) fun y hy => (Finset.mem_filter.1 hy).2
    have h2 : ((cellBall S z 20).card : ℝ) ≤ (((2 * 20 + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast this
    norm_num at h2 ⊢
    exact h2
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun _ _ => hN.isSeminorm_base.nonneg _ _
  have hW : ∑ y ∈ cellBall S z 20, Md (patchCubicKernel S z Gc) y ≤ 41 ^ 4 * (K * ((K * (cellSideLength F : ℝ)) * G)) := by
    calc _ ≤ ∑ _y ∈ cellBall S z 20, K * ((K * (cellSideLength F : ℝ)) * G) := Finset.sum_le_sum fun y _ => hthrough y
      _ = ((cellBall S z 20).card : ℝ) * (K * ((K * (cellSideLength F : ℝ)) * G)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (mul_nonneg hK (mul_nonneg (mul_nonneg hK hN0.le) hG0))
  have hGb : G ≤ 192 * Cs / (cellSideLength F : ℝ) ^ 2 * (K3 * (K3 * Tx)) + 128 * Cs / (cellSideLength F : ℝ) * (K3 * (K3 * Td)) := by
    have hc1 : 0 ≤ 192 * Cs / (cellSideLength F : ℝ) ^ 2 := coeff_div_sq_nonneg (by norm_num) hC hN0
    have hc2 : 0 ≤ 128 * Cs / (cellSideLength F : ℝ) := coeff_div_nonneg (by norm_num) hC hN0
    have hpt : ∀ x, Md (restrictToPatch S z Gc) x ≤ 192 * Cs / (cellSideLength F : ℝ) ^ 2 * Md (neighbourSum S z (neighbourSum S z nξ)) x +
        128 * Cs / (cellSideLength F : ℝ) * Md (neighbourSum S z (neighbourSum S z nd)) x := by
      intro x
      have h1 : Md (restrictToPatch S z Gc) x ≤ Md (fun t => 192 * Cs / (cellSideLength F : ℝ) ^ 2 * neighbourSum S z (neighbourSum S z nξ) t +
          128 * Cs / (cellSideLength F : ℝ) * neighbourSum S z (neighbourSum S z nd) t) x := by
        refine hN.isSeminorm_base.mono_abs _ _ _ fun t _ => ?_
        have hr0 : 0 ≤ 192 * Cs / (cellSideLength F : ℝ) ^ 2 * neighbourSum S z (neighbourSum S z nξ) t +
            128 * Cs / (cellSideLength F : ℝ) * neighbourSum S z (neighbourSum S z nd) t :=
          add_nonneg (mul_nonneg hc1 (neighbourSum_nonneg (neighbourSum_nonneg hnξ0) t)) (mul_nonneg hc2 (neighbourSum_nonneg (neighbourSum_nonneg hnd0) t))
        rw [abs_of_nonneg hr0, abs_of_nonneg (restrictToPatch_nonneg hGc0 t)]
        by_cases ht : t ∈ patchSiteSet S z
        · rw [restrictToPatch_of_mem ht, hGc, remainderCurl, restrictToPatch_of_mem ht]
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ht
          rw [patchChart_patchSite hamb hodd he (patchDomain_coord_bounds ha)]
          exact curlNormAt_remainderForm_le hF hr1 hC hC1 hN1 he hP ξ ha
        · rw [restrictToPatch_of_not_mem ht]
          exact hr0
      refine h1.trans ((hN.isSeminorm_base.add_le _ _ x).trans ?_)
      rw [hN.isSeminorm_base.smul, hN.isSeminorm_base.smul, abs_of_nonneg hc1, abs_of_nonneg hc2]
    calc G ≤ ∑ x ∈ cellBall S z 20, (192 * Cs / (cellSideLength F : ℝ) ^ 2 * Md (neighbourSum S z (neighbourSum S z nξ)) x +
          128 * Cs / (cellSideLength F : ℝ) * Md (neighbourSum S z (neighbourSum S z nd)) x) := Finset.sum_le_sum fun x _ => hpt x
      _ = 192 * Cs / (cellSideLength F : ℝ) ^ 2 * ∑ x ∈ cellBall S z 20, Md (neighbourSum S z (neighbourSum S z nξ)) x +
          128 * Cs / (cellSideLength F : ℝ) * ∑ x ∈ cellBall S z 20, Md (neighbourSum S z (neighbourSum S z nd)) x := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (tot2 hoffξ) hc1) (mul_le_mul_of_nonneg_left (tot2 hoffd) hc2)
  have h1 : ∑ y ∈ cellBall S z 20, Md Dl y ≤ 8 * Cs / (cellSideLength F : ℝ) * (K3 * Tx) +
      4 * Ch * ∑ y ∈ cellBall S z 20, Md (patchCubicKernel S z Gc) y := by
    calc _ ≤ ∑ y ∈ cellBall S z 20, (8 * Cs / (cellSideLength F : ℝ) * Md (neighbourSum S z nξ) y + 4 * Ch * Md (patchCubicKernel S z Gc) y) :=
          Finset.sum_le_sum fun y _ => hstep y
      _ = 8 * Cs / (cellSideLength F : ℝ) * ∑ y ∈ cellBall S z 20, Md (neighbourSum S z nξ) y +
          4 * Ch * ∑ y ∈ cellBall S z 20, Md (patchCubicKernel S z Gc) y := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (tot1 hoffξ) (coeff_div_nonneg (by norm_num) hC hN0)) le_rfl
  have hfin := remainder_total_arith (Bc := 41 ^ 4) hK30 hCh (by norm_num) hK hC hN0 hTx0 hTd0 h1 hW hGb
  refine hfin.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.sum_div]
end
theorem covariantDiffPatchRemainderStatement_holds (hHF : randomStaircaseHomotopyStatement) (hFr : patchFrameExistenceStatement) :
    covariantDiffPatchRemainderStatement := by
  classical
  obtain ⟨Ch, hCh, hHom⟩ := hHF
  obtain ⟨Cf, r, cf, hCf, hr, hcf, hFrames⟩ := hFr
  intro K hK
  obtain ⟨Ct, hCtd⟩ : ∃ Ct, Ct = 8 * (1 + 8 * K * 81) + 4 * Ch * 41 ^ 4 * K ^ 2 * 192 * (1 + 8 * K * 81) ^ 2 := ⟨_, rfl⟩
  have hCt0 : 0 ≤ Ct := by rw [hCtd]; positivity
  refine ⟨Ch + Ct * Cf, min cf (1 / Cf), ⌈1 / r⌉₊ + 1, by positivity, lt_min hcf (by positivity), ?_⟩
  intro F m S hodd hL1 hamb hm hreg s V hs hsc hcold ξ hξ z hz
  have hL := hodd.pos
  have he := (closedOrthant_spec (S := S) hreg (by omega) z).1
  have hNz := cellSideLength_pos (F := F) hL
  have hN1 : (1 : ℝ) ≤ cellSideLength F := by exact_mod_cast hNz
  have hLN : (F.blockSide : ℝ) ≤ cellSideLength F := by
    have h1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hL
    have h2 : (F.blockSide : ℝ) ≤ (F.blockSide : ℝ) ^ F.top := le_self_pow₀ h1 (by simp [BlockFrame.top])
    simpa [cellSideLength] using h2
  have hr1 : 1 ≤ r * cellSideLength F := by
    have h1 : 1 / r ≤ (F.blockSide : ℝ) := by
      have h2 : (⌈1 / r⌉₊ : ℝ) ≤ F.blockSide := by
        have : ⌈1 / r⌉₊ ≤ F.blockSide := by omega
        exact_mod_cast this
      exact (Nat.le_ceil _).trans h2
    have h3 : 1 / r ≤ cellSideLength F := h1.trans hLN
    rw [div_le_iff₀ hr] at h3
    linarith
  obtain ⟨R, hF⟩ := hFrames F m S hodd hamb hm hreg s V hs (hsc.trans (min_le_left _ _)) hcold z hz
  have hC0 : 0 ≤ Cf * s := by positivity
  have hC1 : Cf * s ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (hsc.trans (min_le_right _ _)) hCf.le
    rwa [mul_one_div_cancel hCf.ne'] at this
  have hfill := patchDomain_isFilledToward hz he hL
  have hl1 : 1 ≤ 9 * (cellSideLength F).toNat := by omega
  obtain ⟨H, Gk, hH, hG, hall⟩ := hHom _ _ _ hl1 hfill
  obtain ⟨c1, c2, c3⟩ := hall ℍ[ℝ]
  have hk : PatchPathKernels S z H Gk Ch := ⟨hH, hG, c1, c2, c3⟩
  refine ⟨fun a => remainderMean R S V z ξ a - cellMean F (remainderMean R S V z ξ), stepNorms S z (remainderMean R S V z ξ),
    ⟨stepNorms_nonneg _, fun t ht => by simp [stepNorms, ht], fun a ha => ?_, fun a ha i hi => ?_, fun a ha => ?_⟩, ?_⟩
  · rw [localPotential_eq hk hF hr1 he ξ ha, localPotentialMean_eq hk hF hr1 he hL hz ξ hξ]
    abel
  · rw [stepNorms_patchSite hamb hodd he _ ha, sub_sub_sub_cancel_right]
    have := Finset.single_le_sum (f := fun i => if a + basisVector i ∈ patchDomain S z then
      ‖remainderMean R S V z ξ (a + basisVector i) - remainderMean R S V z ξ a‖ else 0)
      (fun _ _ => by split_ifs <;> simp) (Finset.mem_univ i)
    simpa [hi] using this
  · refine (norm_sub_cellMean_le hk hCh.le hamb hodd he hz _ ha).trans ?_
    have hT0 : 0 ≤ patchCubicKernel S z (stepNorms S z (remainderMean R S V z ξ)) (patchSite S z a) :=
      patchCubicKernel_nonneg (stepNorms_nonneg _) _
    have hM0 : 0 ≤ (1 / (cellSideLength F : ℝ) ^ 4) * ∑ x ∈ cellOffsets F,
        patchCubicKernel S z (stepNorms S z (remainderMean R S V z ξ)) (patchSite S z x) :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => patchCubicKernel_nonneg (stepNorms_nonneg _) _)
    have hle : Ch ≤ Ch + Ct * Cf := by
      have : 0 ≤ Ct * Cf := by positivity
      linarith
    exact add_le_add (mul_le_mul_of_nonneg_right hle hT0) (mul_le_mul_of_nonneg_right hle hM0)
  · intro Md Lf Sr σ hN
    have h := sum_cellBall_stepNorms_le hk hCh.le hF hr1 hC0 hC1 hN1 hamb hodd hreg (by omega) hz he ξ hK.le hN
    rw [← hCtd] at h
    refine h.trans ?_
    have hT : 0 ≤ ∑ y ∈ cellBall S z 20, (Md (restrictToPatch S z (sectionNormOn S ξ)) y / (cellSideLength F : ℝ) +
        Md (restrictToPatch S z (formNormOn S (covariantDiff (referenceFieldChain S V 0) ξ))) y) :=
      Finset.sum_nonneg fun y _ => add_nonneg (div_nonneg (hN.isSeminorm_base.nonneg _ _) (by linarith)) (hN.isSeminorm_base.nonneg _ _)
    refine mul_le_mul_of_nonneg_right ?_ hT
    have : Ct * (Cf * s) = Ct * Cf * s := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) hs.le
end YangMills.Construction.PatchDifferences
end
