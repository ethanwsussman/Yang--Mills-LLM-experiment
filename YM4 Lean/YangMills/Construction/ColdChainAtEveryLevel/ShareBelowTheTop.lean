import YangMills.Construction.ColdChainAtEveryLevel.TermsNearACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator Topology
open Metric Filter
namespace YangMills.Construction.LowerShare
open BlockAverages
variable {F : BlockFrame} {k : ℕ}
section Abstract
def weightedSize {m : ℕ} (n₀ : ℝ) (near : Fin m → ℝ) (t : Fin m → ℂ) : ℝ := n₀ + ∑ l, ‖t l‖ * near l
theorem weightedSize_add_single_le {m : ℕ} (n₀ : ℝ) {near : Fin m → ℝ} (hn : ∀ l, 0 ≤ near l) (t : Fin m → ℂ) (τ : ℂ)
    (l₀ : Fin m) :
    weightedSize n₀ near (t + τ • (Pi.single l₀ 1 : Fin m → ℂ)) ≤ weightedSize n₀ near t + ‖τ‖ * near l₀ := by
  classical
  unfold weightedSize
  have h1 : ∀ l, ‖(t + τ • (Pi.single l₀ 1 : Fin m → ℂ)) l‖ * near l ≤
      ‖t l‖ * near l + (if l = l₀ then ‖τ‖ * near l else 0) := by
    intro l
    by_cases h : l = l₀
    · subst h
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, if_true]
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (hn _)
    · simp [Pi.single_eq_of_ne h, h]
  have h2 := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => h1 l
  rw [Finset.sum_add_distrib] at h2
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  linarith
theorem continuous_weightedSize {m : ℕ} (n₀ : ℝ) (near : Fin m → ℝ) : Continuous (weightedSize n₀ near) := by
  unfold weightedSize
  fun_prop
set_option maxHeartbeats 2000000 in
theorem norm_iteratedFDeriv_le_of_secondDiff_of_pos (hmix : Analytic.mixedDerivativeOfSecondDifferencesStatement)
    {k' : ℕ} {G : (Fin (k' + 2) → ℂ) → ℂ}
    {n₀ y Mc : ℝ} (near : Fin (k' + 2) → ℝ) (hnear0 : ∀ l, 0 ≤ near l) (hy0 : 0 < y) (hU : n₀ ≤ y / 2) (hMc0 : 0 ≤ Mc)
    (hGan : ∀ t, weightedSize n₀ near t < y → AnalyticAt ℂ G t)
    (hsec : ∀ (t : Fin (k' + 2) → ℂ) (τ₁ τ₂ : ℂ) (l₁ l₂ : Fin (k' + 2)), weightedSize n₀ near t ≤ y →
      weightedSize n₀ near (t + τ₁ • (Pi.single l₁ 1 : Fin (k' + 2) → ℂ)) ≤ y →
      weightedSize n₀ near (t + τ₂ • (Pi.single l₂ 1 : Fin (k' + 2) → ℂ)) ≤ y →
      weightedSize n₀ near (t + τ₁ • (Pi.single l₁ 1 : Fin (k' + 2) → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin (k' + 2) → ℂ)) ≤ y →
      ‖G (t + τ₁ • (Pi.single l₁ 1 : Fin (k' + 2) → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin (k' + 2) → ℂ)) -
        G (t + τ₁ • (Pi.single l₁ 1 : Fin (k' + 2) → ℂ)) - G (t + τ₂ • (Pi.single l₂ 1 : Fin (k' + 2) → ℂ)) + G t‖ ≤
        Mc * ((3 * (‖τ₁‖ * near l₁)) * (3 * (‖τ₂‖ * near l₂))))
    {l1 l2 : Fin (k' + 2)} (hne : l1 ≠ l2) {ε : ℝ} (hε : 0 < ε) :
    ‖iteratedFDeriv ℂ (k' + 2) G 0 (fun l => Pi.single l 1)‖ ≤
      Analytic.cauchyHalvingConstant k' * (Mc * 9 * near l1 * near l2) / 1 ^ k' *
        ∏ l ∈ (Finset.univ.erase l1).erase l2, ((near l + ε) / (y / (4 * ((k' : ℝ) + 2)))) := by
  set ρ := y / (4 * ((k' : ℝ) + 2)) with hρ
  have hρ0 : 0 < ρ := by positivity
  set r : Fin (k' + 2) → ℝ := fun l => ρ / (near l + ε) with hr
  have hd : ∀ l, 0 < near l + ε := fun l => by
    have := hnear0 l
    linarith
  have hr0 : ∀ l, 0 < r l := fun l => div_pos hρ0 (hd l)
  set Ω : Set (Fin (k' + 2) → ℂ) := {t | weightedSize n₀ near t < y} with hΩ
  have hΩo : IsOpen Ω := isOpen_lt (continuous_weightedSize n₀ near) continuous_const
  have hGan' : ∀ t ∈ Ω, AnalyticAt ℂ G t := fun t ht => hGan t ht
  set T : (Fin (k' + 2) → ℂ) →L[ℂ] (Fin (k' + 2) → ℂ) :=
    ContinuousLinearMap.pi fun l => (r l : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (k' + 2) => ℂ) l with hT
  have hTa : ∀ t l, T t l = (r l : ℂ) * t l := fun t l => by
    simp [hT]
  have hnear_T : ∀ t ∈ ball (0 : Fin (k' + 2) → ℂ) 1, weightedSize n₀ near (T t) ≤ 3 * y / 4 := by
    intro t ht
    have ht1 : ‖t‖ < 1 := by simpa using ht
    have h1 : ∀ l ∈ (Finset.univ : Finset (Fin (k' + 2))), ‖T t l‖ * near l ≤ ρ := by
      intro l _
      rw [hTa, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr0 l)]
      have h3 : ‖t l‖ ≤ 1 := (norm_le_pi_norm t l).trans ht1.le
      have h4 : r l * near l ≤ ρ := by
        simp only [hr]
        rw [div_mul_eq_mul_div, div_le_iff₀ (hd l)]
        have := hnear0 l
        nlinarith
      calc r l * ‖t l‖ * near l = (r l * near l) * ‖t l‖ := by ring
        _ ≤ ρ * 1 := mul_le_mul h4 h3 (norm_nonneg _) hρ0.le
        _ = ρ := mul_one _
    have h5 := Finset.sum_le_card_nsmul _ _ _ h1
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h5
    have e : (((k' + 2 : ℕ)) : ℝ) * ρ = y / 4 := by
      rw [hρ]
      push_cast
      field_simp
    rw [e] at h5
    unfold weightedSize
    linarith
  have hball : ∀ t ∈ ball (0 : Fin (k' + 2) → ℂ) 1, T t ∈ Ω := fun t ht => by
    have := hnear_T t ht
    show weightedSize n₀ near (T t) < y
    linarith
  set Gt : (Fin (k' + 2) → ℂ) → ℂ := G ∘ T with hGt
  have hGtan : AnalyticOnNhd ℂ Gt (ball 0 1) := fun t ht =>
    (hGan' (T t) (hball t ht)).comp (T.analyticAt t)
  set v : Fin (k' + 2) → Fin (k' + 2) → ℂ := fun l => Pi.single l ((r l : ℂ)⁻¹) with hv
  have hTv : ∀ l, T (v l) = Pi.single l 1 := by
    intro l
    funext m
    rw [hTa]
    by_cases h : m = l
    · subst h
      have : (r m : ℂ) ≠ 0 := by exact_mod_cast (hr0 m).ne'
      simp [hv, this]
    · simp [hv, Pi.single_eq_of_ne h]
  set M := Mc * 9 * near l1 * near l2 with hM
  have hM0 : 0 ≤ M := mul_nonneg (mul_nonneg (by positivity) (hnear0 _)) (hnear0 _)
  have hsd : ∀ t ∈ ball (0 : Fin (k' + 2) → ℂ) 1, ∃ δ : ℝ, 0 < δ ∧ ∀ τ₁ τ₂ : ℂ, ‖τ₁‖ < δ → ‖τ₂‖ < δ →
      ‖Gt (t + τ₁ • v l1 + τ₂ • v l2) - Gt (t + τ₁ • v l1) - Gt (t + τ₂ • v l2) + Gt t‖ ≤ M * ‖τ₁‖ * ‖τ₂‖ := by
    intro t ht
    have hT3 := hnear_T t ht
    have hnn : 0 < near l1 + near l2 + 1 := by
      have := hnear0 l1
      have := hnear0 l2
      linarith
    refine ⟨y / (8 * (near l1 + near l2 + 1)), by positivity, fun τ₁ τ₂ h₁ h₂ => ?_⟩
    have hδ₁ : ‖τ₁‖ * near l1 ≤ y / 8 := by
      have h3 : near l1 ≤ near l1 + near l2 + 1 := by
        have := hnear0 l2
        linarith
      calc ‖τ₁‖ * near l1 ≤ y / (8 * (near l1 + near l2 + 1)) * (near l1 + near l2 + 1) :=
            mul_le_mul h₁.le h3 (hnear0 _) (by positivity)
        _ = y / 8 := by field_simp
    have hδ₂ : ‖τ₂‖ * near l2 ≤ y / 8 := by
      have h3 : near l2 ≤ near l1 + near l2 + 1 := by
        have := hnear0 l1
        linarith
      calc ‖τ₂‖ * near l2 ≤ y / (8 * (near l1 + near l2 + 1)) * (near l1 + near l2 + 1) :=
            mul_le_mul h₂.le h3 (hnear0 _) (by positivity)
        _ = y / 8 := by field_simp
    set t' := T t with ht'
    have m₁ := weightedSize_add_single_le n₀ hnear0 t' τ₁ l1
    have m₂ := weightedSize_add_single_le n₀ hnear0 t' τ₂ l2
    have m₃ := weightedSize_add_single_le n₀ hnear0 (t' + τ₁ • (Pi.single l1 1 : Fin (k' + 2) → ℂ)) τ₂ l2
    have hb := hsec t' τ₁ τ₂ l1 l2 (by linarith) (by linarith) (by linarith) (by linarith)
    have e₁ : T (t + τ₁ • v l1 + τ₂ • v l2) =
        t' + τ₁ • (Pi.single l1 1 : Fin (k' + 2) → ℂ) + τ₂ • (Pi.single l2 1 : Fin (k' + 2) → ℂ) := by
      rw [map_add, map_add, map_smul, map_smul, hTv, hTv]
    have e₂ : T (t + τ₁ • v l1) = t' + τ₁ • (Pi.single l1 1 : Fin (k' + 2) → ℂ) := by
      rw [map_add, map_smul, hTv]
    have e₃ : T (t + τ₂ • v l2) = t' + τ₂ • (Pi.single l2 1 : Fin (k' + 2) → ℂ) := by
      rw [map_add, map_smul, hTv]
    simp only [hGt, Function.comp_apply, e₁, e₂, e₃]
    refine hb.trans (le_of_eq ?_)
    rw [hM]
    ring
  have hm := hmix (k' + 2) k' Gt 1 M v l1 l2 hne one_pos hM0 hGtan hsd
  have h0Ω : (0 : Fin (k' + 2) → ℂ) ∈ Ω := by
    show weightedSize n₀ near 0 < y
    have : weightedSize n₀ near 0 = n₀ := by
      simp [weightedSize]
    rw [this]
    linarith
  have hcd : ContDiffOn ℂ (k' + 2 : ℕ) G Ω := fun x hx => (hGan' x hx).contDiffAt.contDiffWithinAt
  have hs' : IsOpen (T ⁻¹' Ω) := hΩo.preimage T.continuous
  have hmem : (0 : Fin (k' + 2) → ℂ) ∈ T ⁻¹' Ω := by
    simpa using h0Ω
  have h3 := T.iteratedFDerivWithin_comp_right hcd hΩo.uniqueDiffOn hs'.uniqueDiffOn hmem (i := k' + 2) le_rfl
  rw [iteratedFDerivWithin_of_isOpen (k' + 2) hs' hmem, map_zero, iteratedFDerivWithin_of_isOpen (k' + 2) hΩo h0Ω] at h3
  have e4 : iteratedFDeriv ℂ (k' + 2) Gt 0 v = iteratedFDeriv ℂ (k' + 2) G 0 (fun l => Pi.single l 1) := by
    rw [show Gt = G ∘ T from rfl, h3]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext l
    exact hTv l
  rw [← e4]
  refine hm.trans (le_of_eq ?_)
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  have e5 : ‖v l‖ = (r l)⁻¹ := by
    simp only [hv]
    rw [Pi.norm_single, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr0 l)]
  rw [e5]
  simp only [hr]
  rw [inv_div]
theorem norm_iteratedFDeriv_le_of_secondDiff (hmix : Analytic.mixedDerivativeOfSecondDifferencesStatement) {k' : ℕ}
    {G : (Fin (k' + 2) → ℂ) → ℂ}
    {n₀ y Mc : ℝ} (near : Fin (k' + 2) → ℝ) (hnear0 : ∀ l, 0 ≤ near l) (hy0 : 0 < y) (hU : n₀ ≤ y / 2) (hMc0 : 0 ≤ Mc)
    (hGan : ∀ t, weightedSize n₀ near t < y → AnalyticAt ℂ G t)
    (hsec : ∀ (t : Fin (k' + 2) → ℂ) (τ₁ τ₂ : ℂ) (l₁ l₂ : Fin (k' + 2)), weightedSize n₀ near t ≤ y →
      weightedSize n₀ near (t + τ₁ • (Pi.single l₁ 1 : Fin (k' + 2) → ℂ)) ≤ y →
      weightedSize n₀ near (t + τ₂ • (Pi.single l₂ 1 : Fin (k' + 2) → ℂ)) ≤ y →
      weightedSize n₀ near (t + τ₁ • (Pi.single l₁ 1 : Fin (k' + 2) → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin (k' + 2) → ℂ)) ≤ y →
      ‖G (t + τ₁ • (Pi.single l₁ 1 : Fin (k' + 2) → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin (k' + 2) → ℂ)) -
        G (t + τ₁ • (Pi.single l₁ 1 : Fin (k' + 2) → ℂ)) - G (t + τ₂ • (Pi.single l₂ 1 : Fin (k' + 2) → ℂ)) + G t‖ ≤
        Mc * ((3 * (‖τ₁‖ * near l₁)) * (3 * (‖τ₂‖ * near l₂))))
    {l1 l2 : Fin (k' + 2)} (hne : l1 ≠ l2) :
    ‖iteratedFDeriv ℂ (k' + 2) G 0 (fun l => Pi.single l 1)‖ ≤
      Analytic.cauchyHalvingConstant k' * (Mc * 9 * near l1 * near l2) / 1 ^ k' *
        ∏ l ∈ (Finset.univ.erase l1).erase l2, ((near l + 0) / (y / (4 * ((k' : ℝ) + 2)))) := by
  set B := Analytic.cauchyHalvingConstant k' * (Mc * 9 * near l1 * near l2) / 1 ^ k' with hB
  have hcont : Continuous fun ε : ℝ => B * ∏ l ∈ (Finset.univ.erase l1).erase l2,
      ((near l + ε) / (y / (4 * ((k' : ℝ) + 2)))) := by
    refine continuous_const.mul (continuous_finset_prod _ fun l _ => ?_)
    exact (continuous_const.add continuous_id).div_const _
  have ht : Tendsto (fun ε : ℝ => B * ∏ l ∈ (Finset.univ.erase l1).erase l2,
      ((near l + ε) / (y / (4 * ((k' : ℝ) + 2))))) (𝓝[>] 0)
      (𝓝 (B * ∏ l ∈ (Finset.univ.erase l1).erase l2, ((near l + 0) / (y / (4 * ((k' : ℝ) + 2)))))) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact norm_iteratedFDeriv_le_of_secondDiff_of_pos hmix near hnear0 hy0 hU hMc0 hGan hsec hne hε
def higherDerivConst (Mc y : ℝ) (k' : ℕ) : ℝ :=
  Analytic.cauchyHalvingConstant k' * (Mc * 9) * (4 * ((k' : ℝ) + 2) / y) ^ k'
theorem norm_iteratedFDeriv_le_higherDerivConst_mul_prod (hmix : Analytic.mixedDerivativeOfSecondDifferencesStatement)
    {k' : ℕ} {G : (Fin (k' + 2) → ℂ) → ℂ}
    {n₀ y Mc : ℝ} (near : Fin (k' + 2) → ℝ) (hnear0 : ∀ l, 0 ≤ near l) (hy0 : 0 < y) (hU : n₀ ≤ y / 2) (hMc0 : 0 ≤ Mc)
    (hGan : ∀ t, weightedSize n₀ near t < y → AnalyticAt ℂ G t)
    (hsec : ∀ (t : Fin (k' + 2) → ℂ) (τ₁ τ₂ : ℂ) (l₁ l₂ : Fin (k' + 2)), weightedSize n₀ near t ≤ y →
      weightedSize n₀ near (t + τ₁ • (Pi.single l₁ 1 : Fin (k' + 2) → ℂ)) ≤ y →
      weightedSize n₀ near (t + τ₂ • (Pi.single l₂ 1 : Fin (k' + 2) → ℂ)) ≤ y →
      weightedSize n₀ near (t + τ₁ • (Pi.single l₁ 1 : Fin (k' + 2) → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin (k' + 2) → ℂ)) ≤ y →
      ‖G (t + τ₁ • (Pi.single l₁ 1 : Fin (k' + 2) → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin (k' + 2) → ℂ)) -
        G (t + τ₁ • (Pi.single l₁ 1 : Fin (k' + 2) → ℂ)) - G (t + τ₂ • (Pi.single l₂ 1 : Fin (k' + 2) → ℂ)) + G t‖ ≤
        Mc * ((3 * (‖τ₁‖ * near l₁)) * (3 * (‖τ₂‖ * near l₂)))) :
    ‖iteratedFDeriv ℂ (k' + 2) G 0 (fun l => Pi.single l 1)‖ ≤ higherDerivConst Mc y k' * ∏ l, near l := by
  classical
  have hne : (0 : Fin (k' + 2)) ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  refine (norm_iteratedFDeriv_le_of_secondDiff hmix near hnear0 hy0 hU hMc0 hGan hsec hne).trans (le_of_eq ?_)
  have hcard : ((Finset.univ.erase (0 : Fin (k' + 2))).erase 1).card = k' := by
    rw [Finset.card_erase_of_mem (by simp [hne.symm]), Finset.card_erase_of_mem (by simp)]
    simp
  have e1 : ∏ l ∈ (Finset.univ.erase (0 : Fin (k' + 2))).erase 1, ((near l + 0) / (y / (4 * ((k' : ℝ) + 2)))) =
      (∏ l ∈ (Finset.univ.erase (0 : Fin (k' + 2))).erase 1, near l) * (4 * ((k' : ℝ) + 2) / y) ^ k' := by
    have : ∀ l, (near l + 0) / (y / (4 * ((k' : ℝ) + 2))) = near l * (4 * ((k' : ℝ) + 2) / y) := by
      intro l
      have hk : (4 * ((k' : ℝ) + 2)) ≠ 0 := by positivity
      field_simp
      ring
    simp only [this]
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  have e2 : ∏ l, near l = near 0 * (near 1 * ∏ l ∈ (Finset.univ.erase (0 : Fin (k' + 2))).erase 1, near l) := by
    rw [Finset.mul_prod_erase (Finset.univ.erase 0) near (by simp [hne.symm]),
      Finset.mul_prod_erase Finset.univ near (Finset.mem_univ _)]
  rw [e1, e2]
  unfold higherDerivConst
  simp only [one_pow, div_one]
  ring
end Abstract
section Weights
open Classical in
def plaquetteWeight (Y : F.Cell) (p : F.Site 0 × Fin 4 × Fin 4) : ℝ :=
  ∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0
open Classical in
def bondWeight (Y : F.Cell) {j : ℕ} (c : F.Site j × Fin 4) : ℝ :=
  (if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
    (if enclosingCell (c.1 + unitStep j c.2) = Y then (1 / 2 : ℝ) else 0)
theorem plaquetteWeight_nonneg (Y : F.Cell) (p : F.Site 0 × Fin 4 × Fin 4) : 0 ≤ plaquetteWeight Y p := by
  classical
  unfold plaquetteWeight
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> norm_num
theorem plaquetteWeight_le_one (Y : F.Cell) (p : F.Site 0 × Fin 4 × Fin 4) : plaquetteWeight Y p ≤ 1 := by
  classical
  unfold plaquetteWeight
  have h1 : ∀ x ∈ plaquetteCorners p, (if enclosingCell x = Y then (1 / 4 : ℝ) else 0) ≤ 1 / 4 := fun x _ => by
    split_ifs <;> norm_num
  refine (Finset.sum_le_card_nsmul _ _ _ h1).trans ?_
  have hc : (plaquetteCorners p).card ≤ 4 := Finset.card_le_four
  have hc' : ((plaquetteCorners p).card : ℝ) ≤ 4 := by exact_mod_cast hc
  rw [nsmul_eq_mul]
  linarith
theorem bondWeight_nonneg (Y : F.Cell) {j : ℕ} (c : F.Site j × Fin 4) : 0 ≤ bondWeight Y c := by
  classical
  unfold bondWeight
  split_ifs <;> norm_num
theorem bondWeight_le_one (Y : F.Cell) {j : ℕ} (c : F.Site j × Fin 4) : bondWeight Y c ≤ 1 := by
  classical
  unfold bondWeight
  split_ifs <;> norm_num
theorem enclosingCell_mem_cellBall_of_plaquetteWeight_ne_zero (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S : Finset F.Cell} {Y : F.Cell}
    {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ innerPlaquettes S 0) (hn : plaquetteWeight Y p ≠ 0) :
    enclosingCell p.1 ∈ cellBall S Y 1 := by
  classical
  obtain ⟨x, hx, hxY⟩ : ∃ x ∈ plaquetteCorners p, enclosingCell x = Y := by
    by_contra hcon
    push Not at hcon
    apply hn
    unfold plaquetteWeight
    exact Finset.sum_eq_zero fun x hx => if_neg (hcon x hx)
  set z := enclosingCell p.1 with hz
  have hq : p ∈ plaquettesOver S {z} 0 := Finset.mem_filter.2 ⟨hp, Finset.mem_singleton.2 rfl⟩
  obtain ⟨b1, b2, b3, b4⟩ := PlaquettesNearCell.plaquette_bonds_mem_innerBonds hamb hodd hq
  have hend : ∀ {b : F.Site 0 × Fin 4}, b ∈ innerBonds (cellBall S z 1) 0 → b.1 ∈ sitesOfCells (cellBall S z 1) 0 ∧
      b.1 + unitStep 0 b.2 ∈ sitesOfCells (cellBall S z 1) 0 := fun hb => ChartCoordinates.innerBonds_ends hb
  have hx' : x ∈ sitesOfCells (cellBall S z 1) 0 := by
    simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (hend b1).1
    · exact (hend b1).2
    · exact (hend b4).2
    · exact (hend b2).2
  have hc := BlockLines.enclosingCell_mem hodd hx'
  rw [hxY] at hc
  obtain ⟨hYS, hd⟩ := Finset.mem_filter.1 hc
  have hzS : z ∈ S := BlockLines.enclosingCell_mem hodd (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1
  refine Finset.mem_filter.2 ⟨hzS, ?_⟩
  rw [PatchLocality.cellSupDist_comm]
  exact hd
theorem enclosingCell_mem_cellBall_of_bondWeight_ne_zero (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    {S : Finset F.Cell} {Y : F.Cell} {j : ℕ} (hj : j ≤ F.top)
    {c : F.Site j × Fin 4} (hc : c ∈ innerBonds S j) (hn : bondWeight Y c ≠ 0) : enclosingCell c.1 ∈ cellBall S Y 1 := by
  classical
  set z := enclosingCell c.1 with hz
  have hq : c ∈ bondsOver S {z} j := Finset.mem_filter.2 ⟨hc, Finset.mem_singleton.2 rfl⟩
  have hb := BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hamb hodd S z hj hq
  have he := ChartCoordinates.innerBonds_ends hb
  have hzS : z ∈ S := BlockLines.enclosingCell_mem hodd (ChartCoordinates.innerBonds_ends hc).1
  have hY : enclosingCell c.1 = Y ∨ enclosingCell (c.1 + unitStep j c.2) = Y := by
    by_contra hcon
    push Not at hcon
    apply hn
    unfold bondWeight
    rw [if_neg hcon.1, if_neg hcon.2]
    simp
  have h2 : Y ∈ cellBall S z 1 := by
    rcases hY with h | h
    · rw [← h]
      exact BlockLines.enclosingCell_mem hodd he.1
    · rw [← h]
      exact BlockLines.enclosingCell_mem hodd he.2
  obtain ⟨-, hd⟩ := Finset.mem_filter.1 h2
  refine Finset.mem_filter.2 ⟨hzS, ?_⟩
  rw [PatchLocality.cellSupDist_comm]
  exact hd
end Weights
section Real
def lowerEvaluation (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (Y : F.Cell) (U : ChainChart F) : ℝ :=
  ∑ p ∈ innerPlaquettes S 0, plaquetteWeight Y p *
      (1 - ((plaquetteHolonomy (chartField R U 0) p : UnitQuaternion) : ℍ[ℝ]).re) +
    a * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ innerBonds S (j + 1), bondWeight Y c *
      gaugedBlockFit (chartField R U j) (chartGauge R U (j + 1)) (chartField R U (j + 1)) c
def topRestriction (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain) (V : F.GaugeField F.top) (Y : F.Cell) (U : ChainChart F)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : ℝ :=
  a * ∑ c ∈ innerBonds S (F.depth + 1), bondWeight Y c *
    gaugedBlockFit (chartField R U F.depth) (chartGauge R U (F.depth + 1)) (rotatedField v V) c
theorem cellShareInChart_eq_lowerShareInChart_add_topShareInChart (a : ℝ) (S : Finset F.Cell) (R : F.FieldChain)
    (V : F.GaugeField F.top) (Y : F.Cell) (U : ChainChart F) (v : F.Site F.top → Fin 4 → imaginaryQuaternions) :
    localCellShare a S R V Y U v = lowerEvaluation a S R Y U + topRestriction a S R V Y U v := by
  classical
  have h0 : 0 < F.top := Nat.succ_pos _
  have e1 : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1),
      gaugedBlockFit (chartChain R U (rotatedField v V) j) (chartGauge R U (j + 1))
        (chartChain R U (rotatedField v V) (j + 1)) c =
      gaugedBlockFit (chartField R U j) (chartGauge R U (j + 1)) (chartField R U (j + 1)) c := by
    intro j hj c _
    rw [ChartCoordinates.chartChain_of_lt R U _ (by omega : j < F.top), ChartCoordinates.chartChain_of_lt R U _ hj]
  have et : ∀ c ∈ innerBonds S (F.depth + 1),
      gaugedBlockFit (chartChain R U (rotatedField v V) F.depth) (chartGauge R U (F.depth + 1))
        (chartChain R U (rotatedField v V) (F.depth + 1)) c =
      gaugedBlockFit (chartField R U F.depth) (chartGauge R U (F.depth + 1)) (rotatedField v V) c := by
    intro c _
    rw [ChartCoordinates.chartChain_of_lt R U _ (Nat.lt_succ_self _)]
    have : chartChain R U (rotatedField v V) (F.depth + 1) = rotatedField v V := ChartCoordinates.chartChain_top R U _
    rw [this]
  have hn : F.top - 1 = F.depth := rfl
  unfold localCellShare gaugedCellShare lowerEvaluation topRestriction
  rw [ChartCoordinates.chartChain_of_lt R U (rotatedField v V) h0]
  have hr : Finset.range F.top = Finset.range (F.depth + 1) := rfl
  rw [hr, Finset.sum_range_succ, hn]
  have l1 : ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1),
      ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
        (if enclosingCell (c.1 + unitStep (j + 1) c.2) = Y then (1 / 2 : ℝ) else 0)) *
      gaugedBlockFit (chartChain R U (rotatedField v V) j) (chartGauge R U (j + 1))
        (chartChain R U (rotatedField v V) (j + 1)) c =
      ∑ j ∈ Finset.range F.depth, ∑ c ∈ innerBonds S (j + 1), bondWeight Y c *
        gaugedBlockFit (chartField R U j) (chartGauge R U (j + 1)) (chartField R U (j + 1)) c := by
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c hc => ?_
    have hj' := Finset.mem_range.1 hj
    rw [e1 j (by simp only [BlockFrame.top]; omega) c hc]
    rfl
  have l2 : ∑ c ∈ innerBonds S (F.depth + 1),
      ((if enclosingCell c.1 = Y then (1 / 2 : ℝ) else 0) +
        (if enclosingCell (c.1 + unitStep (F.depth + 1) c.2) = Y then (1 / 2 : ℝ) else 0)) *
      gaugedBlockFit (chartChain R U (rotatedField v V) F.depth) (chartGauge R U (F.depth + 1))
        (chartChain R U (rotatedField v V) (F.depth + 1)) c =
      ∑ c ∈ innerBonds S (F.depth + 1), bondWeight Y c *
        gaugedBlockFit (chartField R U F.depth) (chartGauge R U (F.depth + 1)) (rotatedField v V) c := by
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [et c hc]
    rfl
  rw [l1, l2]
  have l3 : ∑ p ∈ innerPlaquettes S 0, (∑ x ∈ plaquetteCorners p, if enclosingCell x = Y then (1 / 4 : ℝ) else 0) *
      (1 - ((plaquetteHolonomy (chartField R U 0) p : UnitQuaternion) : ℍ[ℝ]).re) =
      ∑ p ∈ innerPlaquettes S 0, plaquetteWeight Y p *
        (1 - ((plaquetteHolonomy (chartField R U 0) p : UnitQuaternion) : ℍ[ℝ]).re) :=
    Finset.sum_congr rfl fun p _ => rfl
  rw [l3]
  ring
end Real
section Complex
def lowerCellTerms (a : ℝ) (S : Finset F.Cell) (Y : F.Cell) (R : F.FieldChain) (W : ComplexChainChart F)
    (V : F.GaugeField F.top) (z : F.Cell) : ℂ :=
  ∑ q ∈ plaquettesOver S {z} 0, (plaquetteWeight Y q : ℂ) * complexPlaquetteTerm (complexChartField R W 0) q +
    (a : ℂ) * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S {z} (j + 1),
      (bondWeight Y c : ℂ) * complexBondTerm R W V j c
def lowerExtension (a : ℝ) (S : Finset F.Cell) (Y : F.Cell) (R : F.FieldChain) (W : ComplexChainChart F)
    (V : F.GaugeField F.top) : ℂ :=
  ∑ z ∈ cellBall S Y 1, lowerCellTerms a S Y R W V z
theorem norm_lowerCellTerms_secondDiff_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (a : ℝ)
    (S : Finset F.Cell) (Y z : F.Cell) (R : F.FieldChain)
    (V : F.GaugeField F.top) (W₀ W₁ W₂ W₃ : ComplexChainChart F) :
    ‖lowerCellTerms a S Y R W₃ V z - lowerCellTerms a S Y R W₁ V z - lowerCellTerms a S Y R W₂ V z +
        lowerCellTerms a S Y R W₀ V z‖ ≤
      CellSecondDifferences.cellSecondDiffSum a S z R V W₀ W₁ W₂ W₃ := by
  classical
  set dq : F.Site 0 × Fin 4 × Fin 4 → ℂ := fun q => complexPlaquetteTerm (complexChartField R W₃ 0) q -
    complexPlaquetteTerm (complexChartField R W₁ 0) q - complexPlaquetteTerm (complexChartField R W₂ 0) q +
    complexPlaquetteTerm (complexChartField R W₀ 0) q with hdq
  set dc : (j : ℕ) → F.Site (j + 1) × Fin 4 → ℂ := fun j c => complexBondTerm R W₃ V j c -
    complexBondTerm R W₁ V j c - complexBondTerm R W₂ V j c + complexBondTerm R W₀ V j c with hdc
  have e : lowerCellTerms a S Y R W₃ V z - lowerCellTerms a S Y R W₁ V z - lowerCellTerms a S Y R W₂ V z +
      lowerCellTerms a S Y R W₀ V z =
      ∑ q ∈ plaquettesOver S {z} 0, (plaquetteWeight Y q : ℂ) * dq q +
        (a : ℂ) * ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S {z} (j + 1), (bondWeight Y c : ℂ) * dc j c := by
    simp only [lowerCellTerms, hdq, hdc, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [e]
  unfold CellSecondDifferences.cellSecondDiffSum
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (plaquetteWeight_nonneg Y q)]
    exact mul_le_of_le_one_left (norm_nonneg _) (plaquetteWeight_le_one Y q)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
    rw [ComplexCells.lowerBonds, Finset.sum_sigma]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    refine (norm_sum_le _ _).trans ?_
    have hj' : j + 1 ≤ F.top := by
      have := Finset.mem_range.1 hj
      omega
    refine le_trans (Finset.sum_le_sum fun c _ => ?_) (Finset.sum_le_sum_of_subset_of_nonneg
      (fun c hc => BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hamb hodd S z hj' hc)
      fun _ _ _ => norm_nonneg _)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bondWeight_nonneg Y c)]
    exact mul_le_of_le_one_left (norm_nonneg _) (bondWeight_le_one Y c)
end Complex
section Hypotheses
variable {S : Finset F.Cell} {Y : F.Cell} {R : F.FieldChain} {C₀ s y : ℝ}
theorem cellSupDist_le_of_mem_cellBall {z : F.Cell} (hz : z ∈ cellBall S Y 1) : cellSupDist Y z ≤ 1 := by
  classical
  exact (Finset.mem_filter.1 hz).2
theorem analyticAt_lowerExtension_spanChart (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (a : ℝ)
    (V : F.GaugeField F.top) (ctx : ∀ z, CellSpans.CellHypotheses S z R C₀ s y) (U : ChainChart F)
    (A : Fin k → ChainChart F) {t₀ : Fin k → ℂ}
    (h0 : CellSpans.spanLocalNorm S R U A t₀ Y ≤ y) :
    AnalyticAt ℂ (fun t => lowerExtension a S Y R (CellSpans.spanChart U A t) V) t₀ := by
  unfold lowerExtension
  refine Finset.analyticAt_fun_sum _ fun z hz => ?_
  obtain ⟨hp, hb⟩ := NearbyCellTerms.analyticAt_cellTerms_spanChart hamb hodd (cellSupDist_le_of_mem_cellBall hz) V
    (ctx z) U A h0
  unfold lowerCellTerms
  refine (Finset.analyticAt_fun_sum _ fun q hq => analyticAt_const.mul (hp q hq)).add (analyticAt_const.mul ?_)
  refine Finset.analyticAt_fun_sum _ fun j hj => Finset.analyticAt_fun_sum _ fun c hc => ?_
  have hj' : j + 1 < F.top := by
    have := Finset.mem_range.1 hj
    simp only [BlockFrame.top] at this ⊢
    omega
  exact analyticAt_const.mul (hb j hj' c hc).1
theorem sum_secondDiff {ι : Type} (T : Finset ι) (f₀ f₁ f₂ f₃ : ι → ℂ) :
    ∑ z ∈ T, f₃ z - ∑ z ∈ T, f₁ z - ∑ z ∈ T, f₂ z + ∑ z ∈ T, f₀ z = ∑ z ∈ T, (f₃ z - f₁ z - f₂ z + f₀ z) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
def lowerSecondDiffConst (L : ℕ) (a : ℝ) : ℝ :=
  81 * CellBounds.cellSecondDiffConst (HullBounds.hullFactor L) (200000 * (L : ℝ) ^ 2)
    (1 / (2 * (200000 * (L : ℝ) ^ 2))) a
theorem lowerSecondDiffConst_nonneg (L : ℕ) (a : ℝ) : 0 ≤ lowerSecondDiffConst L a := by
  have hF := ComplexCells.hullFactor_nonneg L
  unfold lowerSecondDiffConst CellBounds.cellSecondDiffConst CellBounds.secondDiffConst
  positivity
theorem norm_lowerExtension_secondDiff_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (a : ℝ) (V : F.GaugeField F.top)
    (ctx : ∀ z, CellSpans.CellHypotheses S z R C₀ s y) (U : ChainChart F) (A : Fin k → ChainChart F) (t : Fin k → ℂ)
    (τ₁ τ₂ : ℂ) (l₁ l₂ : Fin k)
    (n₀ : CellSpans.spanLocalNorm S R U A t Y ≤ y)
    (n₁ : CellSpans.spanLocalNorm S R U A (t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ)) Y ≤ y)
    (n₂ : CellSpans.spanLocalNorm S R U A (t + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ)) Y ≤ y)
    (n₃ : CellSpans.spanLocalNorm S R U A
      (t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ)) Y ≤ y) :
    ‖lowerExtension a S Y R
          (CellSpans.spanChart U A (t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ))) V -
        lowerExtension a S Y R (CellSpans.spanChart U A (t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ))) V -
        lowerExtension a S Y R (CellSpans.spanChart U A (t + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ))) V +
        lowerExtension a S Y R (CellSpans.spanChart U A t) V‖ ≤
      lowerSecondDiffConst F.blockSide a * ((3 * (‖τ₁‖ * localNorm S R (A l₁) (constOneWeights F) Y)) *
        (3 * (‖τ₂‖ * localNorm S R (A l₂) (constOneWeights F) Y))) := by
  classical
  unfold lowerExtension
  rw [sum_secondDiff]
  refine (norm_sum_le _ _).trans ?_
  set B := CellBounds.cellSecondDiffConst (HullBounds.hullFactor F.blockSide) (200000 * (F.blockSide : ℝ) ^ 2)
      (1 / (2 * (200000 * (F.blockSide : ℝ) ^ 2))) a *
    ((3 * (‖τ₁‖ * localNorm S R (A l₁) (constOneWeights F) Y)) *
      (3 * (‖τ₂‖ * localNorm S R (A l₂) (constOneWeights F) Y))) with hB
  have hz : ∀ z ∈ cellBall S Y 1, ‖lowerCellTerms a S Y R (CellSpans.spanChart U A
        (t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ) + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ))) V z -
      lowerCellTerms a S Y R (CellSpans.spanChart U A (t + τ₁ • (Pi.single l₁ 1 : Fin k → ℂ))) V z -
      lowerCellTerms a S Y R (CellSpans.spanChart U A (t + τ₂ • (Pi.single l₂ 1 : Fin k → ℂ))) V z +
      lowerCellTerms a S Y R (CellSpans.spanChart U A t) V z‖ ≤ B := fun z hz =>
    (norm_lowerCellTerms_secondDiff_le hamb hodd a S Y z R V _ _ _ _).trans
      (NearbyCellTerms.cellSecondDiffSum_spanChart_le hamb hodd h2 a (cellSupDist_le_of_mem_cellBall hz) V (ctx z)
        U A t τ₁ τ₂ l₁ l₂ n₀ n₁ n₂ n₃)
  refine (Finset.sum_le_card_nsmul _ _ _ hz).trans ?_
  have hB0 : 0 ≤ B := by
    have hF := ComplexCells.hullFactor_nonneg F.blockSide
    have h1 : 0 ≤ localNorm S R (A l₁) (constOneWeights F) Y := Real.sqrt_nonneg _
    have h2 : 0 ≤ localNorm S R (A l₂) (constOneWeights F) Y := Real.sqrt_nonneg _
    rw [hB]
    unfold CellBounds.cellSecondDiffConst CellBounds.secondDiffConst
    positivity
  have hc : ((cellBall S Y 1).card : ℝ) ≤ 81 := by exact_mod_cast BlockLines.card_cellBall_one_le S Y
  rw [nsmul_eq_mul]
  unfold lowerSecondDiffConst
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right hc hB0
theorem spanChart_complexify (U : ChainChart F) (A : Fin k → ChainChart F) (t : Fin k → ℝ) :
    CellSpans.spanChart U A (Analytic.complexifyCLM t) = realChart (chartShiftAlong U A t) := by
  have e1 : chartShiftMulti U A (fun l => (Analytic.complexifyCLM t l).re) = chartShiftAlong U A t := by
    simp only [Analytic.complexifyCLM_apply, Complex.ofReal_re]
    rfl
  have e2 : chartShiftMulti (zeroChart F) A (fun l => (Analytic.complexifyCLM t l).im) =
      ⟨fun _ _ => 0, fun _ _ _ => 0⟩ := by
    simp only [chartShiftMulti, Analytic.complexifyCLM_apply, Complex.ofReal_im, zero_smul, Finset.sum_const_zero,
      add_zero]
    rfl
  unfold CellSpans.spanChart realChart
  rw [e1, e2]
theorem complexBondTerm_realChart (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) {j : ℕ}
    (hj : j + 1 < F.top) (c : F.Site (j + 1) × Fin 4)
    (hpos : 0 < (complexGaugedContourAverage (complexChartField R (realChart U) j)
      (complexBalancingGauge (complexChartField R (realChart U) j) (R j)) c).det.re) :
    complexBondTerm R (realChart U) V j c =
      ((gaugedBlockFit (chartField R U j) (chartGauge R U (j + 1)) (chartField R U (j + 1)) c : ℝ) : ℂ) := by
  have hm : complexGaugedContourAverage (complexChartField R (realChart U) j) (complexBalancingGauges R (realChart U) (j + 1)) c =
      ComplexifiedQuaternions.ofQuat (gaugedContourAverage (chartField R U j) (chartGauge R U (j + 1)) c) := by
    rw [complexChartField_realChart, ComplexChartCoordinates.complexBalancingGauges_realChart,
      complexGaugedContourAverage_complexify]
  have hne : gaugedContourAverage (chartField R U j) (chartGauge R U (j + 1)) c ≠ 0 := by
    intro h0
    have e : complexGaugedContourAverage (complexChartField R (realChart U) j)
        (complexBalancingGauge (complexChartField R (realChart U) j) (R j)) c = 0 := by
      have : complexGaugedContourAverage (complexChartField R (realChart U) j)
          (complexBalancingGauge (complexChartField R (realChart U) j) (R j)) c =
          complexGaugedContourAverage (complexChartField R (realChart U) j)
            (complexBalancingGauges R (realChart U) (j + 1)) c := by
        simp only [complexBalancingGauges]
      rw [this, hm, h0, ComplexifiedQuaternions.ofQuat_zero]
    rw [e] at hpos
    simp at hpos
  unfold complexBondTerm gaugedBlockFit
  rw [ComplexBondTerms.complexFieldChain_of_ne R _ V (k := j) (by omega),
    ComplexBondTerms.complexFieldChain_of_ne R _ V (k := j + 1) (by omega), hm, complexChartField_realChart]
  exact ComplexChartCoordinates.complexBlockFit_ofQuat_ofUnit hne _
theorem complexPlaquetteTerm_realChart (R : F.FieldChain) (U : ChainChart F) (q : F.Site 0 × Fin 4 × Fin 4) :
    complexPlaquetteTerm (complexChartField R (realChart U) 0) q =
      ((1 - ((plaquetteHolonomy (chartField R U 0) q : UnitQuaternion) : ℍ[ℝ]).re : ℝ) : ℂ) := by
  rw [complexChartField_realChart, ComplexChartCoordinates.complexPlaquetteTerm_complexify]
theorem sum_eq_sum_fiberwise_cell {β : Type} [DecidableEq β] {M : Type} [AddCommMonoid M] (P : Finset β)
    (g : β → F.Cell) (B : Finset F.Cell)
    (f : β → M) (hf : ∀ p ∈ P, f p ≠ 0 → g p ∈ B) :
    ∑ p ∈ P, f p = ∑ z ∈ B, ∑ p ∈ P.filter (fun p => g p = z), f p := by
  classical
  have h1 : ∑ p ∈ P, f p = ∑ p ∈ P.filter (fun p => g p ∈ B), f p := by
    refine (Finset.sum_filter_of_ne fun p hp hn => hf p hp hn).symm
  rw [h1, ← Finset.sum_fiberwise_of_maps_to (s := P.filter fun p => g p ∈ B) (t := B) (g := g)
    (fun p hp => (Finset.mem_filter.1 hp).2)]
  refine Finset.sum_congr rfl fun z hz => Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨⟨h1, h3 ▸ hz⟩, h3⟩
theorem ofReal_lowerSlice_eq_lowerExtension (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (a : ℝ)
    (V : F.GaugeField F.top) (U' : ChainChart F)
    (hpos : ∀ z ∈ cellBall S Y 1, ∀ j, j + 1 < F.top → ∀ c ∈ bondsOver S {z} (j + 1),
      0 < (complexGaugedContourAverage (complexChartField R (realChart U') j)
        (complexBalancingGauge (complexChartField R (realChart U') j) (R j)) c).det.re) :
    ((lowerEvaluation a S R Y U' : ℝ) : ℂ) = lowerExtension a S Y R (realChart U') V := by
  classical
  unfold lowerEvaluation lowerExtension lowerCellTerms
  push_cast
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  · have e1 := sum_eq_sum_fiberwise_cell (innerPlaquettes S 0) (fun p => enclosingCell p.1) (cellBall S Y 1)
      (fun p => (plaquetteWeight Y p : ℂ) *
        (1 - (((plaquetteHolonomy (chartField R U' 0) p : UnitQuaternion) : ℍ[ℝ]).re : ℂ)))
      (fun p hp hn => enclosingCell_mem_cellBall_of_plaquetteWeight_ne_zero hamb hodd hp
        (fun h0 => hn (by simp [h0])))
    rw [e1]
    refine Finset.sum_congr rfl fun z _ => ?_
    have e2 : (innerPlaquettes S 0).filter (fun p => enclosingCell p.1 = z) = plaquettesOver S {z} 0 := by
      ext p
      simp [plaquettesOver, Finset.mem_filter]
    rw [e2]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [complexPlaquetteTerm_realChart]
    push_cast
    rfl
  · congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j + 1 < F.top := by
      have := Finset.mem_range.1 hj
      simp only [BlockFrame.top] at this ⊢
      omega
    have e1 := sum_eq_sum_fiberwise_cell (innerBonds S (j + 1)) (fun c => enclosingCell c.1) (cellBall S Y 1)
      (fun c => (bondWeight Y c : ℂ) * ((gaugedBlockFit (chartField R U' j) (chartGauge R U' (j + 1))
        (chartField R U' (j + 1)) c : ℝ) : ℂ))
      (fun c hc hn => enclosingCell_mem_cellBall_of_bondWeight_ne_zero hamb hodd hj'.le hc
        (fun h0 => hn (by simp [h0])))
    rw [e1]
    refine Finset.sum_congr rfl fun z hz => ?_
    have e2 : (innerBonds S (j + 1)).filter (fun c => enclosingCell c.1 = z) = bondsOver S {z} (j + 1) := by
      ext p
      simp [bondsOver, Finset.mem_filter]
    rw [e2]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [complexBondTerm_realChart R U' V hj' c (hpos z hz j hj' c hc)]
end Hypotheses
section RealDerivatives
variable {m : ℕ}
theorem exists_isBoundedHolomorphicExtension {f : (Fin m → ℝ) → ℝ} {g : (Fin m → ℂ) → ℂ} (hg : AnalyticAt ℂ g 0)
    (he : ∀ᶠ t in 𝓝 (0 : Fin m → ℝ), (f t : ℂ) = g (Analytic.complexifyCLM t)) :
    ∃ ρ M : ℝ, Analytic.IsBoundedHolomorphicExtension Complex.ofRealCLM f g ρ M := by apply _root_.YangMills.Construction.ChartActionDerivatives.exists_isBoundedHolomorphicExtension <;> assumption
theorem ofReal_iteratedFDeriv_eq {f : (Fin m → ℝ) → ℝ} {g : (Fin m → ℂ) → ℂ} {ρ M : ℝ}
    (h : Analytic.IsBoundedHolomorphicExtension Complex.ofRealCLM f g ρ M) :
    ((iteratedFDeriv ℝ m f 0 (fun l => Pi.single l 1) : ℝ) : ℂ) =
      iteratedFDeriv ℂ m g 0 (fun l => Pi.single l 1) := by apply _root_.YangMills.Construction.ChartActionDerivatives.ofReal_iteratedFDeriv_eq <;> assumption
end RealDerivatives
section Derivatives
variable {S : Finset F.Cell} {Y : F.Cell} {R : F.FieldChain} {C₀ s y : ℝ}
theorem lowerEvaluation_eventuallyEq_lowerExtension (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (a : ℝ)
    (V : F.GaugeField F.top)
    (ctx : ∀ z, CellSpans.CellHypotheses S z R C₀ s y) (U : ChainChart F) (A : Fin k → ChainChart F)
    (hU : localNorm S R U (constOneWeights F) Y < y) :
    ∀ᶠ t in 𝓝 (0 : Fin k → ℝ), ((lowerEvaluation a S R Y (chartShiftAlong U A t) : ℝ) : ℂ) =
      lowerExtension a S Y R (CellSpans.spanChart U A (Analytic.complexifyCLM t)) V := by
  have hc : Continuous fun t : Fin k → ℝ => CellSpans.spanLocalNorm S R U A (Analytic.complexifyCLM t) Y :=
    (continuous_weightedSize (localNorm S R U (constOneWeights F) Y)
      (fun l => localNorm S R (A l) (constOneWeights F) Y)).comp Analytic.complexifyCLM.continuous
  have h0 : CellSpans.spanLocalNorm S R U A (Analytic.complexifyCLM (0 : Fin k → ℝ)) Y < y := by
    have : CellSpans.spanLocalNorm S R U A (Analytic.complexifyCLM (0 : Fin k → ℝ)) Y =
        localNorm S R U (constOneWeights F) Y := by
      simp [CellSpans.spanLocalNorm]
    rw [this]
    exact hU
  filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h0] with t ht
  rw [spanChart_complexify]
  refine ofReal_lowerSlice_eq_lowerExtension hamb hodd a V _ fun z hz j hj c hc => ?_
  have := ((NearbyCellTerms.analyticAt_cellTerms_spanChart hamb hodd (cellSupDist_le_of_mem_cellBall hz) V (ctx z)
    U A ht.le).2 j hj c hc).2
  rwa [spanChart_complexify] at this
theorem analyticAt_lowerObservable (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) (a : ℝ)
    (V : F.GaugeField F.top)
    (ctx : ∀ z, CellSpans.CellHypotheses S z R C₀ s y) (U : ChainChart F) (A : Fin k → ChainChart F)
    (hU : localNorm S R U (constOneWeights F) Y < y) :
    AnalyticAt ℝ (fun t : Fin k → ℝ => lowerEvaluation a S R Y (chartShiftAlong U A t)) 0 := by
  have h0 : CellSpans.spanLocalNorm S R U A 0 Y ≤ y := by
    have : CellSpans.spanLocalNorm S R U A 0 Y = localNorm S R U (constOneWeights F) Y := by
      simp [CellSpans.spanLocalNorm]
    rw [this]
    exact hU.le
  obtain ⟨ρ, M, h⟩ := exists_isBoundedHolomorphicExtension
    (analyticAt_lowerExtension_spanChart hamb hodd a V ctx U A h0)
    (lowerEvaluation_eventuallyEq_lowerExtension hamb hodd a V ctx U A hU)
  exact h.analyticAt_of_leftInverse Complex.reCLM fun a => by simp
theorem norm_iteratedFDeriv_lowerShare_le (hmix : Analytic.mixedDerivativeOfSecondDifferencesStatement)
    (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (h2 : 2 ≤ F.blockSide) (a : ℝ) (V : F.GaugeField F.top) (ctx : ∀ z, CellSpans.CellHypotheses S z R C₀ s y)
    (hy0 : 0 < y) (U : ChainChart F) {k' : ℕ} (A : Fin (k' + 2) → ChainChart F)
    (hU : localNorm S R U (constOneWeights F) Y ≤ y / 2) :
    ‖iteratedFDeriv ℝ (k' + 2) (fun t : Fin (k' + 2) → ℝ => lowerEvaluation a S R Y (chartShiftAlong U A t)) 0
        (fun l => Pi.single l 1)‖ ≤
      higherDerivConst (lowerSecondDiffConst F.blockSide a) y k' * ∏ l, localNorm S R (A l) (constOneWeights F) Y := by
  have hU' : localNorm S R U (constOneWeights F) Y < y := by linarith
  have h0 : CellSpans.spanLocalNorm S R U A 0 Y ≤ y := by
    have : CellSpans.spanLocalNorm S R U A 0 Y = localNorm S R U (constOneWeights F) Y := by
      simp [CellSpans.spanLocalNorm]
    rw [this]
    exact hU'.le
  obtain ⟨ρ, M, h⟩ := exists_isBoundedHolomorphicExtension
    (analyticAt_lowerExtension_spanChart hamb hodd a V ctx U A h0)
    (lowerEvaluation_eventuallyEq_lowerExtension hamb hodd a V ctx U A hU')
  have e := ofReal_iteratedFDeriv_eq h
  have e2 : ‖iteratedFDeriv ℝ (k' + 2) (fun t : Fin (k' + 2) → ℝ => lowerEvaluation a S R Y (chartShiftAlong U A t)) 0
      (fun l => Pi.single l 1)‖ =
      ‖iteratedFDeriv ℂ (k' + 2) (fun t => lowerExtension a S Y R (CellSpans.spanChart U A t) V) 0
        (fun l => Pi.single l 1)‖ := by
    rw [← e, Complex.norm_real]
  rw [e2]
  exact norm_iteratedFDeriv_le_higherDerivConst_mul_prod hmix (fun l => localNorm S R (A l) (constOneWeights F) Y)
    (fun l => Real.sqrt_nonneg _) hy0 hU
    (lowerSecondDiffConst_nonneg F.blockSide a)
    (fun t ht => analyticAt_lowerExtension_spanChart hamb hodd a V ctx U A ht.le)
    (fun t τ₁ τ₂ l₁ l₂ n₀ n₁ n₂ n₃ =>
      norm_lowerExtension_secondDiff_le hamb hodd h2 a V ctx U A t τ₁ τ₂ l₁ l₂ n₀ n₁ n₂ n₃)
end Derivatives
end YangMills.Construction.LowerShare
end
