import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem hasDerivAt_comp_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : E → F} (p u : E) (t : ℝ)
    (h : DifferentiableAt ℝ G (p + t • u)) :
    HasDerivAt (fun t : ℝ => G (p + t • u)) (fderiv ℝ G (p + t • u) u) t := by
  have h1 : HasDerivAt (fun t : ℝ => p + t • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add p
  exact h.hasFDerivAt.comp_hasDerivAt t h1
theorem iteratedFDeriv_three_apply_eq_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : E → F)
    (z : E) (m : Fin 3 → E) :
    iteratedFDeriv ℝ 3 G z m = fderiv ℝ (fderiv ℝ (fderiv ℝ G)) z (m 0) (m 1) (m 2) := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  rfl
theorem abs_mixed_fderiv_le_of_mixed_difference {G : E → ℝ} {u v : E} {h M e : ℝ} (hh : 0 < h)
    (hC : ∀ s t : ℝ, 0 ≤ s → s ≤ h → 0 ≤ t → t ≤ h → ContDiffAt ℝ 3 G (s • u + t • v))
    (h3u : ∀ s t : ℝ, 0 ≤ s → s ≤ h → 0 ≤ t → t ≤ h →
      |fderiv ℝ (fderiv ℝ (fderiv ℝ G)) (s • u + t • v) u v u| ≤ M)
    (h3v : ∀ s t : ℝ, 0 ≤ s → s ≤ h → 0 ≤ t → t ≤ h →
      |fderiv ℝ (fderiv ℝ (fderiv ℝ G)) (s • u + t • v) v v u| ≤ M)
    (hd : |G (h • u + h • v) - G (h • u) - G (h • v) + G 0| ≤ e) :
    |fderiv ℝ (fderiv ℝ G) 0 v u| ≤ e / h ^ 2 + 2 * M * h := by
  have hd1 : ∀ s t : ℝ, 0 ≤ s → s ≤ h → 0 ≤ t → t ≤ h → DifferentiableAt ℝ G (s • u + t • v) :=
    fun s t a b c d => (hC s t a b c d).differentiableAt (by norm_num)
  have hd2 : ∀ s t : ℝ, 0 ≤ s → s ≤ h → 0 ≤ t → t ≤ h →
      DifferentiableAt ℝ (fderiv ℝ G) (s • u + t • v) := fun s t a b c d =>
    ((hC s t a b c d).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hd3 : ∀ s t : ℝ, 0 ≤ s → s ≤ h → 0 ≤ t → t ≤ h →
      DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ G)) (s • u + t • v) := fun s t a b c d =>
    (((hC s t a b c d).fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  set A : ℝ → ℝ := fun s => G (s • u + h • v) - G (s • u + (0 : ℝ) • v) with hA
  have hAd : ∀ s ∈ Set.Icc (0 : ℝ) h, HasDerivAt A
      (fderiv ℝ G (s • u + h • v) u - fderiv ℝ G (s • u + (0 : ℝ) • v) u) s := by
    intro s hs
    have e1 : ∀ c : ℝ, (fun s : ℝ => G (s • u + c • v)) = fun s : ℝ => G (c • v + s • u) := by
      intro c
      funext s
      rw [add_comm]
    have l1 : ∀ c : ℝ, 0 ≤ c → c ≤ h → HasDerivAt (fun s : ℝ => G (s • u + c • v))
        (fderiv ℝ G (s • u + c • v) u) s := by
      intro c c0 c1
      rw [e1]
      have := hasDerivAt_comp_line (G := G) (c • v) u s (by
        rw [add_comm]; exact hd1 s c hs.1 hs.2 c0 c1)
      rwa [add_comm (c • v)] at this
    exact (l1 h hh.le le_rfl).sub (l1 0 le_rfl hh.le)
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope A (fun s => fderiv ℝ G (s • u + h • v) u -
      fderiv ℝ G (s • u + (0 : ℝ) • v) u) hh
    (fun s hs => (hAd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hAd s ⟨hs.1.le, hs.2.le⟩)
  have hξ0 : 0 ≤ ξ := hξ.1.le
  have hξh : ξ ≤ h := hξ.2.le
  set B : ℝ → ℝ := fun t => fderiv ℝ G (ξ • u + t • v) u with hB
  have hBd : ∀ t ∈ Set.Icc (0 : ℝ) h, HasDerivAt B
      (fderiv ℝ (fderiv ℝ G) (ξ • u + t • v) v u) t := by
    intro t ht
    have := hasDerivAt_comp_line (G := fderiv ℝ G) (ξ • u) v t (hd2 ξ t hξ0 hξh ht.1 ht.2)
    exact ((ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp_hasDerivAt t this)
  obtain ⟨ζ, hζ, hζe⟩ := exists_hasDerivAt_eq_slope B
    (fun t => fderiv ℝ (fderiv ℝ G) (ξ • u + t • v) v u) hh
    (fun t ht => (hBd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hBd t ⟨ht.1.le, ht.2.le⟩)
  have hζ0 : 0 ≤ ζ := hζ.1.le
  have hζh : ζ ≤ h := hζ.2.le
  set d : E := ξ • u + ζ • v with hdd
  have ep : ∀ w : ℝ, (0 : E) + w • d = (w * ξ) • u + (w * ζ) • v := by
    intro w
    simp only [hdd, zero_add, smul_add, smul_smul]
  set T : ℝ → ℝ := fun w => fderiv ℝ (fderiv ℝ G) ((0 : E) + w • d) v u with hT
  have hmem : ∀ w ∈ Set.Icc (0 : ℝ) 1, 0 ≤ w * ξ ∧ w * ξ ≤ h ∧ 0 ≤ w * ζ ∧ w * ζ ≤ h := by
    intro w hw
    refine ⟨mul_nonneg hw.1 hξ0, ?_, mul_nonneg hw.1 hζ0, ?_⟩
    · nlinarith [hw.1, hw.2]
    · nlinarith [hw.1, hw.2]
  have hTd : ∀ w ∈ Set.Icc (0 : ℝ) 1, HasDerivAt T
      (ξ * fderiv ℝ (fderiv ℝ (fderiv ℝ G)) ((0 : E) + w • d) u v u +
        ζ * fderiv ℝ (fderiv ℝ (fderiv ℝ G)) ((0 : E) + w • d) v v u) w := by
    intro w hw
    obtain ⟨m1, m2, m3, m4⟩ := hmem w hw
    have h1 := hasDerivAt_comp_line (G := fderiv ℝ (fderiv ℝ G)) (0 : E) d w (by
      rw [ep]; exact hd3 _ _ m1 m2 m3 m4)
    have h3 := (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).hasFDerivAt.comp_hasDerivAt w h1
    have h4 := (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp_hasDerivAt w h3
    have e2 : (fderiv ℝ (fderiv ℝ (fderiv ℝ G)) ((0 : E) + w • d) d v) u =
        ξ * fderiv ℝ (fderiv ℝ (fderiv ℝ G)) ((0 : E) + w • d) u v u +
        ζ * fderiv ℝ (fderiv ℝ (fderiv ℝ G)) ((0 : E) + w • d) v v u := by
      simp [hdd]
    simp only [ContinuousLinearMap.apply_apply] at h4
    rw [e2] at h4
    exact h4
  have hTb : ∀ w ∈ Set.Ico (0 : ℝ) 1, ‖ξ * fderiv ℝ (fderiv ℝ (fderiv ℝ G)) ((0 : E) + w • d) u v u +
        ζ * fderiv ℝ (fderiv ℝ (fderiv ℝ G)) ((0 : E) + w • d) v v u‖ ≤ 2 * M * h := by
    intro w hw
    obtain ⟨m1, m2, m3, m4⟩ := hmem w ⟨hw.1, hw.2.le⟩
    have b1 := h3u _ _ m1 m2 m3 m4
    have b2 := h3v _ _ m1 m2 m3 m4
    rw [← ep] at b1 b2
    have hM : 0 ≤ M := (abs_nonneg _).trans b1
    rw [Real.norm_eq_abs]
    calc _ ≤ |ξ * fderiv ℝ (fderiv ℝ (fderiv ℝ G)) ((0 : E) + w • d) u v u| +
          |ζ * fderiv ℝ (fderiv ℝ (fderiv ℝ G)) ((0 : E) + w • d) v v u| := abs_add_le _ _
      _ ≤ h * M + h * M := by
        rw [abs_mul, abs_mul, abs_of_nonneg hξ0, abs_of_nonneg hζ0]
        exact add_le_add (mul_le_mul hξh b1 (abs_nonneg _) hh.le)
          (mul_le_mul hζh b2 (abs_nonneg _) hh.le)
      _ = 2 * M * h := by ring
  have hTdiff := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := T) (a := 0) (b := 1) (C := 2 * M * h)
    (f' := fun w => ξ * fderiv ℝ (fderiv ℝ (fderiv ℝ G)) ((0 : E) + w • d) u v u +
        ζ * fderiv ℝ (fderiv ℝ (fderiv ℝ G)) ((0 : E) + w • d) v v u)
    (fun w hw => (hTd w hw).hasDerivWithinAt) hTb 1 (by simp)
  have eT0 : T 0 = fderiv ℝ (fderiv ℝ G) 0 v u := by simp [hT]
  have eT1 : T 1 = fderiv ℝ (fderiv ℝ G) (ξ • u + ζ • v) v u := by simp [hT, hdd]
  rw [eT0, eT1, Real.norm_eq_abs] at hTdiff
  have hmix : |fderiv ℝ (fderiv ℝ G) (ξ • u + ζ • v) v u| ≤ e / h ^ 2 := by
    have a1 : A h - A 0 = G (h • u + h • v) - G (h • u) - G (h • v) + G 0 := by
      simp only [hA, zero_smul, add_zero, zero_add]
      ring
    have a2 : B h - B 0 = (A h - A 0) / (h - 0) := by
      rw [← hξe]
    have a3 : fderiv ℝ (fderiv ℝ G) (ξ • u + ζ • v) v u = (A h - A 0) / h ^ 2 := by
      rw [hζe, a2, sub_zero, div_div, sq]
    rw [a3, a1, abs_div, abs_of_pos (by positivity : (0 : ℝ) < h ^ 2)]
    exact div_le_div_of_nonneg_right hd (by positivity)
  have := abs_sub_abs_le_abs_sub (fderiv ℝ (fderiv ℝ G) 0 v u) (fderiv ℝ (fderiv ℝ G) (ξ • u + ζ • v) v u)
  have h5 : |fderiv ℝ (fderiv ℝ G) 0 v u - fderiv ℝ (fderiv ℝ G) (ξ • u + ζ • v) v u| ≤ 2 * M * h * (1 - 0) := by
    rw [abs_sub_comm]
    exact hTdiff
  linarith
theorem abs_fderiv_le_of_difference {G : E → ℝ} {u : E} {h M e : ℝ} (hh : 0 < h)
    (hC : ∀ s : ℝ, 0 ≤ s → s ≤ h → ContDiffAt ℝ 2 G (s • u))
    (h2 : ∀ s : ℝ, 0 ≤ s → s ≤ h → |fderiv ℝ (fderiv ℝ G) (s • u) u u| ≤ M)
    (hd : |G (h • u) - G 0| ≤ e) :
    |fderiv ℝ G 0 u| ≤ e / h + M * h := by
  have hd1 : ∀ s : ℝ, 0 ≤ s → s ≤ h → DifferentiableAt ℝ G (s • u) :=
    fun s a b => (hC s a b).differentiableAt (by norm_num)
  have hd2 : ∀ s : ℝ, 0 ≤ s → s ≤ h → DifferentiableAt ℝ (fderiv ℝ G) (s • u) := fun s a b =>
    ((hC s a b).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hAd : ∀ s ∈ Set.Icc (0 : ℝ) h, HasDerivAt (fun s : ℝ => G (s • u)) (fderiv ℝ G (s • u) u) s := by
    intro s hs
    simpa using hasDerivAt_comp_line (G := G) 0 u s (by simpa using hd1 s hs.1 hs.2)
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => G (s • u))
    (fun s => fderiv ℝ G (s • u) u) hh
    (fun s hs => (hAd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hAd s ⟨hs.1.le, hs.2.le⟩)
  have hBd : ∀ s ∈ Set.Icc (0 : ℝ) ξ, HasDerivAt (fun s : ℝ => fderiv ℝ G (s • u) u)
      (fderiv ℝ (fderiv ℝ G) (s • u) u u) s := by
    intro s hs
    have h1 := hasDerivAt_comp_line (G := fderiv ℝ G) 0 u s (by
      simpa using hd2 s hs.1 (hs.2.trans hξ.2.le))
    simp only [zero_add] at h1
    exact (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp_hasDerivAt s h1
  have hdiff := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s : ℝ => fderiv ℝ G (s • u) u) (a := 0) (b := ξ) (C := M)
    (f' := fun s => fderiv ℝ (fderiv ℝ G) (s • u) u u)
    (fun s hs => (hBd s hs).hasDerivWithinAt)
    (fun s hs => by
      rw [Real.norm_eq_abs]
      exact h2 s hs.1 (hs.2.le.trans hξ.2.le)) ξ (by simp [hξ.1.le])
  have hM : 0 ≤ M := (abs_nonneg _).trans (h2 0 le_rfl hh.le)
  simp only [zero_smul, sub_zero, Real.norm_eq_abs] at hdiff
  have e1 : |fderiv ℝ G (ξ • u) u| ≤ e / h := by
    rw [hξe]
    simp only [zero_smul, sub_zero]
    rw [abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right hd hh.le
  have e2 : M * ξ ≤ M * h := mul_le_mul_of_nonneg_left hξ.2.le hM
  have := abs_sub_abs_le_abs_sub (fderiv ℝ G 0 u) (fderiv ℝ G (ξ • u) u)
  rw [abs_sub_comm] at this
  linarith
end Calculus
end YangMills.Construction
end
