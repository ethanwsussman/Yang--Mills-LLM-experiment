import YangMills.Construction.ClusterExpansionOfAStep.ContoursOnTheTorus
import YangMills.Construction.LawOnABoxOfTheFlow.SizesOfTheBackground
import YangMills.Construction.LawOnABoxOfTheFlow.ToolsOfAChart
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfAStepFallsByHalfProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusContours ResponseInTheExpansion BlockAverages
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
variable {n : ℕ} [NeZero n]
private theorem curlNormSq_mono_radius {center : TorusSite n} {r r' : ℝ} (hle : r ≤ r')
    (A : TorusBond n → imaginaryQuaternions) :
    curlNormSq (supBall center r) A ≤ curlNormSq (supBall center r') A := by
  unfold curlNormSq
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => by positivity
  intro q hq
  simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  refine ⟨hq.1, fun z hz => ?_⟩
  have := hq.2 z hz
  simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and] at this ⊢
  linarith
private theorem translate_mem_plaquettesIn {center : TorusSite n} {r : ℝ} {q : TorusPlaquette n}
    (hq : q ∈ plaquettesIn (supBall center r)) (i : Fin 4) :
    (q.1 + TorusFields.unitStep n i, q.2) ∈ plaquettesIn (supBall center (r + 1)) := by
  simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  refine ⟨hq.1, fun z hz => ?_⟩
  have hw : ∃ w ∈ plaquetteVertices q.1 q.2.1 q.2.2, z = w + TorusFields.unitStep n i := by
    simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨q.1, by simp [plaquetteVertices], rfl⟩
    · exact ⟨q.1 + TorusFields.unitStep n q.2.1, by simp [plaquetteVertices], by abel⟩
    · exact ⟨q.1 + TorusFields.unitStep n q.2.2, by simp [plaquetteVertices], by abel⟩
    · exact ⟨q.1 + TorusFields.unitStep n q.2.1 + TorusFields.unitStep n q.2.2, by simp [plaquetteVertices], by abel⟩
  obtain ⟨w, hw, rfl⟩ := hw
  have h1 := hq.2 w hw
  simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and] at h1 ⊢
  have h2 : supDist (w + TorusFields.unitStep n i) w ≤ 1 := by
    have := supDist_sub_unitStep_le (w + TorusFields.unitStep n i) i
    rwa [add_sub_cancel_right] at this
  have h3 := supDist_triangle (w + TorusFields.unitStep n i) w center
  have h4 : (supDist (w + TorusFields.unitStep n i) center : ℝ) ≤
      (supDist (w + TorusFields.unitStep n i) w : ℝ) + supDist w center := by exact_mod_cast h3
  have h5 : (supDist (w + TorusFields.unitStep n i) w : ℝ) ≤ 1 := by exact_mod_cast h2
  linarith
private theorem plaquettesIn_supBall_mono {center : TorusSite n} {r r' : ℝ} (hle : r ≤ r') :
    plaquettesIn (supBall center r) ⊆ plaquettesIn (supBall center r') := by apply _root_.YangMills.SharedProofs.p58549 <;> assumption
private theorem iteratedDiff_congr_on_ball {center : TorusSite n} {r' : ℝ}
    {F G : TorusPlaquette n → imaginaryQuaternions}
    (hFG : ∀ q ∈ plaquettesIn (supBall center r'), F q = G q) :
    ∀ (dirs : List (Fin 4)) (r : ℝ), r + dirs.length ≤ r' → ∀ q ∈ plaquettesIn (supBall center r),
      iteratedDiff dirs F q = iteratedDiff dirs G q := by
  intro dirs
  induction dirs with
  | nil =>
    intro r hr q hq
    exact hFG q (plaquettesIn_supBall_mono (by simpa using hr) hq)
  | cons i dirs ih =>
    intro r hr q hq
    have hr1 : r + 1 + dirs.length ≤ r' := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hr
      linarith
    have hr2 : r + dirs.length ≤ r' := by linarith
    show forwardDiff i (iteratedDiff dirs F) q = forwardDiff i (iteratedDiff dirs G) q
    unfold forwardDiff
    rw [ih (r + 1) hr1 _ (translate_mem_plaquettesIn hq i), ih r hr2 q hq]
private theorem norm_iteratedDiff_le {F : TorusPlaquette n → imaginaryQuaternions} {M : ℝ}
    (hF : ∀ q, ‖F q‖ ≤ M) :
    ∀ (dirs : List (Fin 4)) (q : TorusPlaquette n), ‖iteratedDiff dirs F q‖ ≤ 2 ^ dirs.length * M := by
  intro dirs
  induction dirs with
  | nil =>
    intro q
    simpa [iteratedDiff] using hF q
  | cons i dirs ih =>
    intro q
    show ‖forwardDiff i (iteratedDiff dirs F) q‖ ≤ _
    unfold forwardDiff
    refine (norm_sub_le _ _).trans ?_
    have h1 := ih (q.1 + TorusFields.unitStep n i, q.2)
    have h2 := ih q
    simp only [List.length_cons, pow_succ]
    linarith
private theorem boxScale_bounds {κ x : ℝ} (hκ : 1 / 27 ≤ κ) (hx : 3 ≤ x) :
    boxScale x ≤ 4 ∧ ((boxRadius κ x : ℝ) ^ 14)⁻¹ ≤ boxScale x := by
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    exact le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hx
  have hs : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hinv : x ^ (-(1 / 2 : ℝ)) = (x ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hx0.le _
  have hlog2 : Real.log x ≤ 2 * x ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    calc Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2) := this
      _ = 2 * x ^ (1 / 2 : ℝ) := by ring
  constructor
  · simp only [boxScale, hinv]
    calc 2 * (x ^ (1 / 2 : ℝ))⁻¹ * Real.log x ≤ 2 * (x ^ (1 / 2 : ℝ))⁻¹ * (2 * x ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ = 4 := by field_simp; norm_num
  · set R := boxRadius κ x with hR
    have hRx : x ^ κ ≤ (R : ℝ) := Nat.le_ceil _
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have h27 : x ^ (1 / 27 : ℝ) ≤ (R : ℝ) := le_trans (Real.rpow_le_rpow_of_exponent_le hx1 hκ) hRx
    have hxp : 1 ≤ x ^ (1 / 27 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    have h14 : x ^ (1 / 2 : ℝ) ≤ (R : ℝ) ^ 14 := by
      calc x ^ (1 / 2 : ℝ) ≤ x ^ ((14 : ℝ) * (1 / 27)) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        _ = (x ^ (1 / 27 : ℝ)) ^ (14 : ℕ) := by
            rw [mul_comm, Real.rpow_mul hx0.le]
            norm_cast
        _ ≤ (R : ℝ) ^ 14 := pow_le_pow_left₀ (by linarith) h27 14
    have h2 : ((R : ℝ) ^ 14)⁻¹ ≤ (x ^ (1 / 2 : ℝ))⁻¹ := inv_anti₀ hs h14
    simp only [boxScale, hinv]
    have h3 : 0 < (x ^ (1 / 2 : ℝ))⁻¹ := by positivity
    nlinarith
theorem backgroundCurlBounds (hReg : interiorRegularityStatement) : backgroundCurlBoundsStatement := by
  refine holdsAtAdmissibleParameters_mono ?_ hReg
  intro Tb y hTb hi κ h1 h2 C₃ hC₃
  choose Cj' c' R₀ hc' hint using hi 4 1 one_pos
  set D₃ := Real.sqrt C₃ with hD₃
  have hD₃0 : 0 ≤ D₃ := Real.sqrt_nonneg _
  have hD₃s : D₃ ^ 2 = C₃ := Real.sq_sqrt hC₃
  set rr : ℕ := max 1 ⌈4 * C₃⌉₊ with hrr
  let R₁ : ℕ → ℕ := fun j => max (R₀ j) (4 * j + 8)
  let Cl : ℕ → ℝ := fun j => max (Cj' j) 0 * D₃ + ((j + 14).factorial : ℝ) / c' j ^ (j + 14)
  refine ⟨D₃, max 3 (((rr : ℝ) + 1) ^ 27),
    fun j => max (Cl j) (2 ^ j * (D₃ * (R₁ j : ℝ) ^ (j + 2))), ?_⟩
  intro x R k n _ o B hx hR hn hcs hbd horth
  have hx3 : 3 ≤ x := le_trans (le_max_left _ _) hx
  have hRr : rr ≤ R := by
    rw [hR]
    exact le_boxRadius κ x h1 rr (le_trans (le_max_right _ _) hx)
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hRr
  have hRpos : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hRC : 4 * C₃ ≤ R := by
    have : ((⌈4 * C₃⌉₊ : ℕ) : ℝ) ≤ R := by exact_mod_cast le_trans (le_max_right _ _) hRr
    exact le_trans (Nat.le_ceil _) this
  obtain ⟨hδ4, hδR⟩ := boxScale_bounds (κ := κ) h1 hx3
  rw [← hR] at hδR
  set δ := boxScale x with hδ
  have hδ0 : 0 ≤ δ := le_trans (by positivity) hδR
  have hbound : ∀ b ∈ bondsWithin (supBall o (2 * R)), ‖B b‖ ≤ (R : ℝ) ^ (4 : ℝ) := by
    intro b hb
    refine le_trans (hbd b hb) ?_
    have e4 : (R : ℝ) ^ (4 : ℝ) = (R : ℝ) ^ (4 : ℕ) := by norm_cast
    rw [e4]
    have h3 : C₃ * δ ≤ R := by nlinarith
    calc C₃ * (R : ℝ) ^ 3 * δ = (C₃ * δ) * (R : ℝ) ^ 3 := by ring
      _ ≤ R * (R : ℝ) ^ 3 := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (R : ℝ) ^ 4 := by ring
  have hzero : ∀ η : TorusBond n → imaginaryQuaternions, (∀ b, b ∉ bondsTouching o R → η b = 0) →
      |hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) B η| ≤ Real.exp (-(1 * R)) * ∑ b : TorusBond n, ‖η b‖ := by
    intro η hη
    rw [horth η hη, abs_zero]
    exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun b _ => norm_nonneg _)
  have hsq : Real.sqrt (((R : ℝ) ^ 4)⁻¹ * curlNormSq (supBall o R) B) ≤ D₃ * δ := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have h3 : curlNormSq (supBall o (R : ℝ)) B ≤ C₃ * (R : ℝ) ^ 4 * δ ^ 2 :=
      le_trans (curlNormSq_mono_radius (by linarith) B) hcs
    calc ((R : ℝ) ^ 4)⁻¹ * curlNormSq (supBall o R) B ≤ ((R : ℝ) ^ 4)⁻¹ * (C₃ * (R : ℝ) ^ 4 * δ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (D₃ * δ) ^ 2 := by
          rw [mul_pow, hD₃s]
          field_simp
  have hsize : ∀ q ∈ plaquettesIn (supBall o (2 * R)), ‖lieFormCurl B q‖ ≤ D₃ * (R : ℝ) ^ 2 * δ := by
    intro q hq
    have h3 : ‖lieFormCurl B q‖ ^ 2 ≤ curlNormSq (supBall o (2 * R)) B :=
      Finset.single_le_sum (f := fun q => ‖lieFormCurl B q‖ ^ 2) (fun q _ => by positivity) hq
    have h4 : ‖lieFormCurl B q‖ ^ 2 ≤ (D₃ * (R : ℝ) ^ 2 * δ) ^ 2 := by
      calc _ ≤ C₃ * (R : ℝ) ^ 4 * δ ^ 2 := le_trans h3 hcs
        _ = (D₃ * (R : ℝ) ^ 2 * δ) ^ 2 := by
            rw [mul_pow, mul_pow, hD₃s]
            ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h4
  refine ⟨hsize, fun l q hq => ?_⟩
  set m := l.length with hm
  set a := ((R : ℝ) ^ m)⁻¹ with ha
  have ha0 : 0 ≤ a := by positivity
  have hcut : ∀ q, ‖restrictedCurl (supBall o (2 * R)) B q‖ ≤ D₃ * (R : ℝ) ^ 2 * δ := by
    intro q
    by_cases h : q ∈ plaquettesIn (supBall o (2 * (R : ℝ)))
    · simp only [restrictedCurl, if_pos h]
      exact hsize q h
    · simp only [restrictedCurl, if_neg h, norm_zero]
      positivity
  by_cases hbig : R₁ m ≤ R
  · have hR0 : R₀ m ≤ R := le_trans (le_max_left _ _) hbig
    have hm4 : 4 * m + 8 ≤ R := le_trans (le_max_right _ _) hbig
    have hmR : (m : ℝ) ≤ (R : ℝ) := by
      have : m ≤ R := by omega
      exact_mod_cast this
    have heq : iteratedDiff l (restrictedCurl (supBall o (2 * R)) B) q = iteratedDiff l (lieFormCurl B) q := by
      refine iteratedDiff_congr_on_ball (r' := 2 * (R : ℝ)) (fun q hq => ?_) l ((R : ℝ) / 4) (by linarith) q hq
      simp only [restrictedCurl, if_pos hq]
    rw [heq]
    have h3 := hint m k n o R B hR0 hn hbound hzero l rfl q hq
    have h4 : Cj' m * a * Real.sqrt (((R : ℝ) ^ 4)⁻¹ * curlNormSq (supBall o R) B) ≤ max (Cj' m) 0 * D₃ * a * δ := by
      have h5 : Cj' m * a ≤ max (Cj' m) 0 * a := mul_le_mul_of_nonneg_right (le_max_left _ _) ha0
      calc Cj' m * a * Real.sqrt (((R : ℝ) ^ 4)⁻¹ * curlNormSq (supBall o R) B)
          ≤ max (Cj' m) 0 * a * Real.sqrt (((R : ℝ) ^ 4)⁻¹ * curlNormSq (supBall o R) B) :=
            mul_le_mul_of_nonneg_right h5 (Real.sqrt_nonneg _)
        _ ≤ max (Cj' m) 0 * a * (D₃ * δ) :=
            mul_le_mul_of_nonneg_left hsq (mul_nonneg (le_max_right _ _) ha0)
        _ = max (Cj' m) 0 * D₃ * a * δ := by ring
    have h6 : Real.exp (-(c' m * R)) ≤ ((m + 14).factorial : ℝ) / c' m ^ (m + 14) * a * δ := by
      have hc := hc' m
      have hy : 0 ≤ c' m * (R : ℝ) := by positivity
      have hp := Real.pow_div_factorial_le_exp (c' m * R) hy (m + 14)
      have h7 : Real.exp (-(c' m * R)) ≤ ((m + 14).factorial : ℝ) / (c' m * (R : ℝ)) ^ (m + 14) := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
        exact hp
      refine le_trans h7 (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left hδR (by positivity)))
      rw [ha, mul_pow, pow_add]
      field_simp
      ring
    have h8 : Cl m * a * δ ≤ max (Cl m) (2 ^ m * (D₃ * (R₁ m : ℝ) ^ (m + 2))) * a * δ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) ha0) hδ0
    refine le_trans h3 (le_trans (add_le_add h4 h6) (le_trans (le_of_eq ?_) h8))
    simp only [Cl]
    ring
  · have hlt : (R : ℝ) ≤ (R₁ m : ℝ) := by
      have : R ≤ R₁ m := by omega
      exact_mod_cast this
    have h3 := norm_iteratedDiff_le hcut l q
    refine le_trans h3 ?_
    have hpow : (R : ℝ) ^ (m + 2) ≤ (R₁ m : ℝ) ^ (m + 2) := pow_le_pow_left₀ (by linarith) hlt _
    have h4 : (2 : ℝ) ^ m * (D₃ * (R : ℝ) ^ 2 * δ) ≤ 2 ^ m * (D₃ * (R₁ m : ℝ) ^ (m + 2)) * a * δ := by
      have e1 : (R : ℝ) ^ 2 = (R : ℝ) ^ (m + 2) * a := by
        rw [ha, pow_add]
        field_simp
      rw [e1]
      calc (2 : ℝ) ^ m * (D₃ * ((R : ℝ) ^ (m + 2) * a) * δ) = 2 ^ m * (D₃ * (R : ℝ) ^ (m + 2)) * a * δ := by ring
        _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ ha0) hδ0
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hD₃0) (by positivity)
    refine le_trans h4 ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) ha0) hδ0
end YangMills.Construction.BoxGaussian
end
