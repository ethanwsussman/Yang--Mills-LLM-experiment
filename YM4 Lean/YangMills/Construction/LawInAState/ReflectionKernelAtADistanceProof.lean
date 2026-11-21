import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.LawInAState.ReflectionKernelAtADistance
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionKernel
theorem normSq_pos {u : Fin 4 → ℝ} (hu : u ≠ 0) : 0 < normSq u := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  have hi' : u i ≠ 0 := by simpa using hi
  have h1 : 0 < u i ^ 2 := by positivity
  have h2 : u i ^ 2 ≤ normSq u :=
    Finset.single_le_sum (f := fun l => u l ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ i)
  linarith
theorem normSq_nonneg (u : Fin 4 → ℝ) : 0 ≤ normSq u := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.sumSq_nonneg <;> assumption
theorem abs_apply_le_sqrt_normSq (u : Fin 4 → ℝ) (i : Fin 4) : |u i| ≤ Real.sqrt (normSq u) := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem abs_mul_apply_le_normSq (u : Fin 4 → ℝ) (m r : Fin 4) : |u m * u r| ≤ normSq u := by
  have h1 := abs_apply_le_sqrt_normSq u m
  have h2 := abs_apply_le_sqrt_normSq u r
  rw [abs_mul]
  calc |u m| * |u r| ≤ Real.sqrt (normSq u) * Real.sqrt (normSq u) :=
        mul_le_mul h1 h2 (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = normSq u := Real.mul_self_sqrt (normSq_nonneg u)
theorem abs_reflectionEntry_le {u : Fin 4 → ℝ} (hu : u ≠ 0) (m r : Fin 4) : |reflectionEntry u m r| ≤ 3 := by
  have hs := normSq_pos hu
  have h1 : |2 * u m * u r / normSq u| ≤ 2 := by
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs, mul_assoc, abs_mul]
    have := abs_mul_apply_le_normSq u m r
    simp only [abs_two]
    linarith
  have h2 : |(if m = r then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  unfold reflectionEntry
  calc _ ≤ |(if m = r then (1 : ℝ) else 0)| + |2 * u m * u r / normSq u| := abs_sub _ _
    _ ≤ 3 := by linarith
theorem abs_mul_sub_mul_le_eighteen {a b c d : ℝ} (ha : |a| ≤ 3) (hb : |b| ≤ 3) (hc : |c| ≤ 3) (hd : |d| ≤ 3) :
    |a * b - c * d| ≤ 18 := by
  have h1 : |a * b| ≤ 9 := by
    rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg b]
  have h2 : |c * d| ≤ 9 := by
    rw [abs_mul]; nlinarith [abs_nonneg c, abs_nonneg d]
  calc _ ≤ |a * b| + |c * d| := abs_sub _ _
    _ ≤ 18 := by linarith
theorem one_le_pi_sq : (1 : ℝ) ≤ Real.pi ^ 2 := by
  have := Real.pi_gt_three
  nlinarith
theorem abs_kernel_le {u : Fin 4 → ℝ} (m n r s : Fin 4) (hu : u ≠ 0) :
    |kernel u m n r s| ≤ 18 / normSq u ^ 2 := by
  have hs := normSq_pos hu
  unfold kernel
  rw [abs_div, abs_of_pos (by positivity : 0 < Real.pi ^ 2 * normSq u ^ 2)]
  have h1 := abs_mul_sub_mul_le_eighteen (abs_reflectionEntry_le hu m r) (abs_reflectionEntry_le hu n s)
    (abs_reflectionEntry_le hu m s) (abs_reflectionEntry_le hu n r)
  have h2 : normSq u ^ 2 ≤ Real.pi ^ 2 * normSq u ^ 2 := by
    nlinarith [one_le_pi_sq, (by positivity : 0 < normSq u ^ 2)]
  exact div_le_div₀ (by norm_num) h1 (by positivity) h2
theorem sqrt_normSq_add_le (a b : Fin 4 → ℝ) :
    Real.sqrt (normSq (a + b)) ≤ Real.sqrt (normSq a) + Real.sqrt (normSq b) := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem abs_sub_normalized_product_le {u w : Fin 4 → ℝ} {s t δ : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hT : normSq w = t ^ 2) (hsr : Real.sqrt (normSq u) = s) (htr : Real.sqrt (normSq w) = t)
    (hδ : Real.sqrt (normSq (u - w)) = δ) (hts : |t - s| ≤ δ) (ht3 : t ≤ 3 / 2 * s) (m r : Fin 4) :
    |u m * u r / s ^ 2 - w m * w r / t ^ 2| ≤ 5 * δ / s := by
  have hum := abs_apply_le_sqrt_normSq u r
  have hwm := abs_apply_le_sqrt_normSq w m
  have hd1 := abs_apply_le_sqrt_normSq (u - w) m
  have hd2 := abs_apply_le_sqrt_normSq (u - w) r
  rw [hsr] at hum
  rw [htr] at hwm
  rw [hδ] at hd1 hd2
  simp only [Pi.sub_apply] at hd1 hd2
  have hδ0 : 0 ≤ δ := hδ ▸ Real.sqrt_nonneg _
  have e1 : u m * u r / s ^ 2 - w m * w r / t ^ 2 =
      (((u m - w m) * u r + w m * (u r - w r)) + (w m * w r / t ^ 2) * (t ^ 2 - s ^ 2)) / s ^ 2 := by
    field_simp
    ring
  have h1 : |(u m - w m) * u r| ≤ δ * s := by
    rw [abs_mul]; exact mul_le_mul hd1 hum (abs_nonneg _) hδ0
  have h2 : |w m * (u r - w r)| ≤ t * δ := by
    rw [abs_mul]; exact mul_le_mul hwm hd2 (abs_nonneg _) ht.le
  have h3 : |w m * w r / t ^ 2| ≤ 1 := by
    have := abs_mul_apply_le_normSq w m r
    rw [hT] at this
    rw [abs_div, abs_of_pos (by positivity : 0 < t ^ 2)]
    exact (div_le_one (by positivity)).mpr this
  have h4 : |t ^ 2 - s ^ 2| ≤ δ * (5 / 2 * s) := by
    have e : t ^ 2 - s ^ 2 = (t - s) * (t + s) := by ring
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < t + s)]
    exact mul_le_mul hts (by linarith) (by positivity) hδ0
  have h5 : |(w m * w r / t ^ 2) * (t ^ 2 - s ^ 2)| ≤ δ * (5 / 2 * s) := by
    rw [abs_mul]
    calc _ ≤ 1 * |t ^ 2 - s ^ 2| := mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
      _ ≤ _ := by linarith
  have h6 : |((u m - w m) * u r + w m * (u r - w r)) + (w m * w r / t ^ 2) * (t ^ 2 - s ^ 2)| ≤ 5 * δ * s := by
    refine (abs_add_le _ _).trans ?_
    have := abs_add_le ((u m - w m) * u r) (w m * (u r - w r))
    nlinarith
  rw [e1, abs_div, abs_of_pos (by positivity : 0 < s ^ 2)]
  calc _ ≤ 5 * δ * s / s ^ 2 := div_le_div_of_nonneg_right h6 (by positivity)
    _ = 5 * δ / s := by field_simp
theorem abs_sub_mul_sub_mul_le {a b c d a' b' c' d' D : ℝ} (ha : |a| ≤ 3) (hc : |c| ≤ 3)
    (hb' : |b'| ≤ 3) (hd' : |d'| ≤ 3)
    (h1 : |a - a'| ≤ D) (h2 : |b - b'| ≤ D) (h3 : |c - c'| ≤ D) (h4 : |d - d'| ≤ D) :
    |(a * b - c * d) - (a' * b' - c' * d')| ≤ 12 * D := by
  have e : (a * b - c * d) - (a' * b' - c' * d') =
      a * (b - b') + (a - a') * b' - (c * (d - d') + (c - c') * d') := by ring
  have k1 : |a * (b - b')| ≤ 3 * D := by
    rw [abs_mul]; exact mul_le_mul ha h2 (abs_nonneg _) (by norm_num)
  have k2 : |(a - a') * b'| ≤ D * 3 := by
    rw [abs_mul]; exact mul_le_mul h1 hb' (abs_nonneg _) ((abs_nonneg _).trans h1)
  have k3 : |c * (d - d')| ≤ 3 * D := by
    rw [abs_mul]; exact mul_le_mul hc h4 (abs_nonneg _) (by norm_num)
  have k4 : |(c - c') * d'| ≤ D * 3 := by
    rw [abs_mul]; exact mul_le_mul h3 hd' (abs_nonneg _) ((abs_nonneg _).trans h3)
  rw [e]
  have q1 := abs_add_le (a * (b - b')) ((a - a') * b')
  have q2 := abs_add_le (c * (d - d')) ((c - c') * d')
  have q3 := abs_sub (a * (b - b') + (a - a') * b') (c * (d - d') + (c - c') * d')
  linarith
theorem abs_kernel_sub_le {u w : Fin 4 → ℝ} (m n r s' : Fin 4) (hu : u ≠ 0) (hc : 4 * normSq (u - w) ≤ normSq u) :
    |kernel u m n r s' - kernel w m n r s'| ≤
      3000 * Real.sqrt (normSq (u - w)) / Real.sqrt (normSq u) ^ 5 := by
  have hS0 := normSq_pos hu
  set s := Real.sqrt (normSq u) with hs_def
  set t := Real.sqrt (normSq w) with ht_def
  set δ := Real.sqrt (normSq (u - w)) with hδ_def
  have hs : 0 < s := Real.sqrt_pos.mpr hS0
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hS : normSq u = s ^ 2 := (Real.sq_sqrt hS0.le).symm
  have hT : normSq w = t ^ 2 := (Real.sq_sqrt (normSq_nonneg w)).symm
  have hD : normSq (u - w) = δ ^ 2 := (Real.sq_sqrt (normSq_nonneg _)).symm
  have hδs : 2 * δ ≤ s := by
    rw [hS, hD] at hc
    nlinarith
  have hneg : normSq (w - u) = normSq (u - w) := by
    simp only [normSq, Pi.sub_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  have t1 : s ≤ t + δ := by
    have := sqrt_normSq_add_le w (u - w)
    rwa [add_sub_cancel] at this
  have t2 : t ≤ s + δ := by
    have := sqrt_normSq_add_le u (w - u)
    rw [add_sub_cancel, hneg] at this
    exact this
  have ht : 0 < t := by linarith
  have hts : |t - s| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
  have ht3 : t ≤ 3 / 2 * s := by linarith
  have hth : s / 2 ≤ t := by linarith
  have hw : w ≠ 0 := by
    rintro rfl
    simp [ht_def, normSq] at ht
  have pm := fun a b => abs_sub_normalized_product_le hs ht hT rfl rfl rfl hts ht3 a b
  have refl_moves : ∀ a b, |reflectionEntry u a b - reflectionEntry w a b| ≤ 10 * δ / s := by
    intro a b
    have e : reflectionEntry u a b - reflectionEntry w a b = -2 * (u a * u b / s ^ 2 - w a * w b / t ^ 2) := by
      simp only [reflectionEntry, hS, hT]
      ring
    rw [e, abs_mul]
    have := pm a b
    have e2 : |(-2 : ℝ)| = 2 := by norm_num
    rw [e2]
    calc _ ≤ 2 * (5 * δ / s) := by linarith
      _ = _ := by ring
  set P := reflectionEntry u m r * reflectionEntry u n s' - reflectionEntry u m s' * reflectionEntry u n r with hP
  set P' := reflectionEntry w m r * reflectionEntry w n s' - reflectionEntry w m s' * reflectionEntry w n r with hP'
  have hPP : |P - P'| ≤ 12 * (10 * δ / s) :=
    abs_sub_mul_sub_mul_le (abs_reflectionEntry_le hu _ _) (abs_reflectionEntry_le hu _ _)
      (abs_reflectionEntry_le hw _ _) (abs_reflectionEntry_le hw _ _)
      (refl_moves _ _) (refl_moves _ _) (refl_moves _ _) (refl_moves _ _)
  have hP'18 : |P'| ≤ 18 :=
    abs_mul_sub_mul_le_eighteen (abs_reflectionEntry_le hw _ _) (abs_reflectionEntry_le hw _ _)
      (abs_reflectionEntry_le hw _ _) (abs_reflectionEntry_le hw _ _)
  have hq : |1 / s ^ 4 - 1 / t ^ 4| ≤ 130 * δ / s ^ 5 := by
    have e : 1 / s ^ 4 - 1 / t ^ 4 = (t - s) * (t + s) * (t ^ 2 + s ^ 2) / (s ^ 4 * t ^ 4) := by
      field_simp
      ring
    have k1 : |t + s| ≤ 5 / 2 * s := by rw [abs_of_pos (by positivity)]; linarith
    have k2 : |t ^ 2 + s ^ 2| ≤ 13 / 4 * s ^ 2 := by
      rw [abs_of_pos (by positivity)]; nlinarith
    have k3 : s ^ 8 / 16 ≤ s ^ 4 * t ^ 4 := by
      have : (s / 2) ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ (by positivity) hth 4
      have h5 : 0 < s ^ 4 := by positivity
      nlinarith
    rw [e, abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < s ^ 4 * t ^ 4)]
    calc _ ≤ (δ * (5 / 2 * s) * (13 / 4 * s ^ 2)) / (s ^ 8 / 16) := by
          refine div_le_div₀ (by positivity) ?_ (by positivity) k3
          exact mul_le_mul (mul_le_mul hts k1 (abs_nonneg _) hδ0) k2 (abs_nonneg _) (by positivity)
      _ = 130 * δ / s ^ 5 := by
          field_simp
          ring
  have hpi := one_le_pi_sq
  have hpi0 : 0 < Real.pi ^ 2 := by positivity
  have hinv : (Real.pi ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpi
  have e : kernel u m n r s' - kernel w m n r s' =
      (Real.pi ^ 2)⁻¹ * ((P - P') * (1 / s ^ 4) + P' * (1 / s ^ 4 - 1 / t ^ 4)) := by
    simp only [kernel, hS, hT]
    rw [← hP, ← hP']
    field_simp
    ring
  have k5 : |(P - P') * (1 / s ^ 4)| ≤ 120 * δ / s ^ 5 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / s ^ 4)]
    calc _ ≤ 12 * (10 * δ / s) * (1 / s ^ 4) := mul_le_mul_of_nonneg_right hPP (by positivity)
      _ = _ := by field_simp; ring
  have k6 : |P' * (1 / s ^ 4 - 1 / t ^ 4)| ≤ 18 * (130 * δ / s ^ 5) := by
    rw [abs_mul]
    exact mul_le_mul hP'18 hq (abs_nonneg _) (by norm_num)
  have k7 : 0 ≤ δ / s ^ 5 := by positivity
  rw [e, abs_mul, abs_of_pos (inv_pos.mpr hpi0)]
  have k8 := abs_add_le ((P - P') * (1 / s ^ 4)) (P' * (1 / s ^ 4 - 1 / t ^ 4))
  have e3 : 120 * δ / s ^ 5 = 120 * (δ / s ^ 5) := by ring
  have e4 : 130 * δ / s ^ 5 = 130 * (δ / s ^ 5) := by ring
  have e5 : 3000 * δ / s ^ 5 = 3000 * (δ / s ^ 5) := by ring
  rw [e3] at k5
  rw [e4] at k6
  rw [e5]
  calc _ ≤ 1 * |(P - P') * (1 / s ^ 4) + P' * (1 / s ^ 4 - 1 / t ^ 4)| :=
        mul_le_mul_of_nonneg_right hinv (abs_nonneg _)
    _ ≤ _ := by nlinarith
private def shiftedMatrix (u : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  normSq u * (if i = j then 1 else 0) - 2 * u i * u j
private def planeMinor (u : Fin 4 → ℝ) (m n r s : Fin 4) : ℝ :=
  shiftedMatrix u m r * shiftedMatrix u n s - shiftedMatrix u m s * shiftedMatrix u n r
private theorem kernel_eq_planeMinor_div {u : Fin 4 → ℝ} (hu : u ≠ 0) (m n r s : Fin 4) :
    kernel u m n r s = planeMinor u m n r s / (Real.pi ^ 2 * normSq u ^ 4) := by
  have hS := (normSq_pos hu).ne'
  have h : ∀ a b, reflectionEntry u a b = shiftedMatrix u a b / normSq u := by
    intro a b
    simp only [reflectionEntry, shiftedMatrix]
    field_simp
  simp only [kernel, planeMinor, h]
  field_simp
private theorem orientedPlanes_eq : orientedPlanes = {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide
private theorem sum_orientedPlanes (g : Fin 4 × Fin 4 → ℝ) :
    ∑ A ∈ orientedPlanes, g A = g (0, 1) + g (0, 2) + g (0, 3) + g (1, 2) + g (1, 3) + g (2, 3) := by
  rw [orientedPlanes_eq]
  simp [Finset.sum_insert, Finset.sum_singleton]
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p501473 := @sum_orientedPlanes
set_option maxRecDepth 100000 in
private theorem sum_planeMinor_mul_planeMinor (u : Fin 4 → ℝ) :
    ∑ A ∈ orientedPlanes, ∑ B ∈ orientedPlanes, planeMinor u A.1 A.2 B.1 B.2 * planeMinor u B.1 B.2 A.1 A.2 =
      6 * normSq u ^ 4 := by
  simp only [sum_orientedPlanes, planeMinor, shiftedMatrix, normSq, Fin.sum_univ_four]
  generalize u 0 = a
  generalize u 1 = b
  generalize u 2 = c
  generalize u 3 = d
  simp only [Fin.reduceEq, if_true, if_false, Fin.isValue, ↓reduceIte]
  ring
theorem sum_kernel_mul_kernel {u : Fin 4 → ℝ} (hu : u ≠ 0) :
    ∑ A ∈ orientedPlanes, ∑ B ∈ orientedPlanes,
      kernel u A.1 A.2 B.1 B.2 * kernel u B.1 B.2 A.1 A.2 =
        6 / (Real.pi ^ 4 * normSq u ^ 4) := by
  have hS := (normSq_pos hu).ne'
  have e : ∀ A B : Fin 4 × Fin 4, kernel u A.1 A.2 B.1 B.2 * kernel u B.1 B.2 A.1 A.2 =
      (planeMinor u A.1 A.2 B.1 B.2 * planeMinor u B.1 B.2 A.1 A.2) / (Real.pi ^ 4 * normSq u ^ 8) := by
    intro A B
    rw [kernel_eq_planeMinor_div hu, kernel_eq_planeMinor_div hu]
    field_simp
  simp only [e, ← Finset.sum_div, sum_planeMinor_mul_planeMinor]
  field_simp
theorem kernelEstimates_holds : KernelEstimates :=
  ⟨fun _ m n r s hu => abs_kernel_le m n r s hu,
    fun _ _ m n r s hu hc => abs_kernel_sub_le m n r s hu hc,
    fun _ hu => sum_kernel_mul_kernel hu⟩
end YangMills.Construction.ReflectionKernel
end
