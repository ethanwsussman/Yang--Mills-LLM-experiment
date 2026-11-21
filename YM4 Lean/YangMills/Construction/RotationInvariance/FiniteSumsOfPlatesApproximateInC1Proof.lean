import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPiecesProof
import YangMills.Construction.EuclideanFunctionals.ElementAboveAHeightAndItsPulledDownElementProof
import YangMills.Construction.PassageToTheLimit.SpacesOfFunctionsOfClassC1AreBanachSpacesProof
import YangMills.Construction.RotationInvariance.FiniteSumsOfPlatesApproximateInC1
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane Filter Topology
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ProductSumApprox
def bump (t : ℝ) : ℝ := Real.smoothTransition (t + 1) - Real.smoothTransition t
theorem bump_contDiff : ContDiff ℝ 1 bump := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.bump_contDiff <;> assumption
theorem bump_eq_zero_of_one_le_abs {t : ℝ} (h : 1 ≤ |t|) : bump t = 0 := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.bump_eq_zero <;> assumption
theorem deriv_bump_eq_zero_of_one_lt_abs {t : ℝ} (h : 1 < |t|) : deriv bump t = 0 := by
  have hev : bump =ᶠ[𝓝 t] fun _ => 0 := by
    have ho : IsOpen {u : ℝ | 1 < |u|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [ho.mem_nhds h] with u hu
    exact bump_eq_zero_of_one_le_abs (le_of_lt hu)
  rw [hev.deriv_eq]
  simp
def IsUnitWeight (C : ℝ) (w : ℝ → ℝ) : Prop := (∀ t, |w t| ≤ C) ∧ ∀ t, w t ≠ 0 → |t| ≤ 1
theorem exists_unitWeight_bound :
    ∃ C : ℝ, 1 ≤ C ∧ IsUnitWeight C bump ∧ IsUnitWeight C (deriv bump) := by
  have hc : Continuous (deriv bump) := bump_contDiff.continuous_deriv le_rfl
  have hs : HasCompactSupport (deriv bump) :=
    HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun t ht =>
      deriv_bump_eq_zero_of_one_lt_abs (by
        by_contra hle
        exact ht (abs_le.1 (not_lt.1 hle)))
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  refine ⟨max 1 C, le_max_left _ _, ⟨fun t => ?_, fun t ht => ?_⟩, ⟨fun t => ?_, fun t ht => ?_⟩⟩
  · refine le_trans ?_ (le_max_left _ _)
    have h1 := Real.smoothTransition.nonneg (t + 1)
    have h2 := Real.smoothTransition.le_one (t + 1)
    have h3 := Real.smoothTransition.nonneg t
    have h4 := Real.smoothTransition.le_one t
    unfold bump
    rw [abs_le]
    constructor <;> linarith
  · by_contra hle
    exact ht (bump_eq_zero_of_one_le_abs (le_of_lt (not_le.1 hle)))
  · exact le_trans (hC t) (le_max_right _ _)
  · by_contra hle
    exact ht (deriv_bump_eq_zero_of_one_lt_abs (not_le.1 hle))
theorem sum_abs_translate_le {C : ℝ} {w : ℝ → ℝ} (hw : IsUnitWeight C w) (hC : 0 ≤ C) (t : ℝ)
    (n : ℕ) : ∑ j ∈ Finset.range n, |w (t - j)| ≤ 3 * C := by
  set a := ⌊t⌋₊ with ha
  have hsub : ∀ j ∈ Finset.range n, j ∉ Finset.Icc (a - 1) (a + 1) → |w (t - j)| = 0 := by
    intro j _ hj
    by_contra hne
    have hne' : w (t - j) ≠ 0 := fun h0 => hne (by simp [h0])
    have hb := abs_le.1 (hw.2 _ hne')
    apply hj
    have hlt : t < a + 1 := Nat.lt_floor_add_one t
    have hup : (j : ℝ) < (a + 2 : ℕ) := by push_cast; linarith [hb.1]
    have hup' : j < a + 2 := by exact_mod_cast hup
    have hlow : a - 1 ≤ j := by
      rcases lt_or_ge t 0 with h0 | h0
      · have : a = 0 := Nat.floor_of_nonpos h0.le
        omega
      · have hle : (a : ℝ) ≤ t := Nat.floor_le h0
        have h1 : (a : ℝ) < (j + 2 : ℕ) := by push_cast; linarith [hb.2]
        have h2 : a < j + 2 := by exact_mod_cast h1
        omega
    exact Finset.mem_Icc.2 ⟨hlow, by omega⟩
  calc ∑ j ∈ Finset.range n, |w (t - j)|
      = ∑ j ∈ (Finset.range n).filter (· ∈ Finset.Icc (a - 1) (a + 1)), |w (t - j)| := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j hj => ?_
        split_ifs with h
        · rfl
        · exact hsub j hj h
    _ ≤ ∑ j ∈ Finset.Icc (a - 1) (a + 1), |w (t - j)| := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => abs_nonneg _
        intro j hj
        exact (Finset.mem_filter.1 hj).2
    _ ≤ (Finset.Icc (a - 1) (a + 1)).card • C :=
        Finset.sum_le_card_nsmul _ _ _ fun j _ => hw.1 _
    _ ≤ 3 * C := by
        rw [nsmul_eq_mul]
        have hcard : (Finset.Icc (a - 1) (a + 1)).card ≤ 3 := by
          rw [Nat.card_Icc]
          omega
        have : ((Finset.Icc (a - 1) (a + 1)).card : ℝ) ≤ 3 := by exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right this hC
theorem sum_bump_translates_eq_one {M : ℕ} {t : ℝ} (h : |t| ≤ M) :
    ∑ j ∈ Finset.range (2 * M + 1), bump (t + M - j) = 1 := by
  have hb := abs_le.1 h
  have key := Finset.sum_range_sub' (fun j : ℕ => Real.smoothTransition (t + M + 1 - j))
    (2 * M + 1)
  have hterm : ∀ j : ℕ, bump (t + M - j) =
      Real.smoothTransition (t + M + 1 - j) - Real.smoothTransition (t + M + 1 - (j + 1 : ℕ)) := by
    intro j
    unfold bump
    push_cast
    congr 2 <;> ring
  simp only [hterm]
  rw [key]
  rw [Real.smoothTransition.one_of_one_le (by push_cast; linarith [hb.1]),
    Real.smoothTransition.zero_of_nonpos (by push_cast; linarith [hb.2])]
  simp
def scaledCoord (ε : ℝ) (M : ℕ) (j : Fin 4 → ℕ) (μ : Fin 4) (x : R4) : ℝ :=
  ε⁻¹ * x μ + M - j μ
def nodePoint (ε : ℝ) (M : ℕ) (j : Fin 4 → ℕ) : R4 := fun μ => ε * ((j μ : ℝ) - M)
def nodeIndices (M : ℕ) : Finset (Fin 4 → ℕ) :=
  Fintype.piFinset fun _ => Finset.range (2 * M + 1)
theorem abs_sub_nodePoint_le {ε : ℝ} (hε : 0 < ε) {M : ℕ} {j : Fin 4 → ℕ} {μ : Fin 4} {x : R4}
    (h : |scaledCoord ε M j μ x| ≤ 1) : |x μ - nodePoint ε M j μ| ≤ ε := by
  have he : x μ - nodePoint ε M j μ = ε * scaledCoord ε M j μ x := by
    unfold nodePoint scaledCoord
    field_simp
    ring
  rw [he, abs_mul, abs_of_pos hε]
  nlinarith
theorem sum_abs_prod_mul_le {ε C H : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) (hH : 0 ≤ H) (M : ℕ)
    {w : Fin 4 → ℝ → ℝ} (hw : ∀ μ, IsUnitWeight C (w μ)) (x : R4) {e : (Fin 4 → ℕ) → ℝ}
    (he : ∀ j, ‖x - nodePoint ε M j‖ ≤ ε → e j ≤ H) :
    ∑ j ∈ nodeIndices M, |∏ μ, w μ (scaledCoord ε M j μ x)| * e j ≤ (3 * C) ^ 4 * H := by
  have hterm : ∀ j ∈ nodeIndices M, |∏ μ, w μ (scaledCoord ε M j μ x)| * e j ≤
      (∏ μ, |w μ (ε⁻¹ * x μ + M - j μ)|) * H := by
    intro j _
    rw [Finset.abs_prod]
    by_cases hz : ∃ μ, w μ (scaledCoord ε M j μ x) = 0
    · obtain ⟨μ, hμ⟩ := hz
      have h0 : ∏ ν, |w ν (scaledCoord ε M j ν x)| = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ μ) (by simp [hμ])
      have h0' : ∏ ν, |w ν (ε⁻¹ * x ν + M - j ν)| = 0 := h0
      rw [h0, h0']
      simp
    · push Not at hz
      have hnear : ‖x - nodePoint ε M j‖ ≤ ε := by
        refine (pi_norm_le_iff_of_nonneg hε.le).2 fun μ => ?_
        rw [Real.norm_eq_abs]
        exact abs_sub_nodePoint_le hε ((hw μ).2 _ (hz μ))
      exact mul_le_mul_of_nonneg_left (he j hnear)
        (Finset.prod_nonneg fun _ _ => abs_nonneg _)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hH
  have hprod := Finset.prod_univ_sum (fun _ : Fin 4 => Finset.range (2 * M + 1))
    (fun μ j => |w μ (ε⁻¹ * x μ + M - j)|)
  unfold nodeIndices
  rw [← hprod]
  calc ∏ μ : Fin 4, ∑ j ∈ Finset.range (2 * M + 1), |w μ (ε⁻¹ * x μ + M - j)|
      ≤ ∏ _μ : Fin 4, 3 * C := by
        refine Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          fun μ _ => sum_abs_translate_le (hw μ) hC _ _
    _ = (3 * C) ^ 4 := by simp
def tile (ε : ℝ) (M : ℕ) (j : Fin 4 → ℕ) (x : R4) : ℝ :=
  ∏ μ, bump (scaledCoord ε M j μ x)
theorem sum_tile_eq_one {ε : ℝ} (hε : 0 < ε) {M : ℕ} {x : R4}
    (hx : ∀ μ, |x μ| ≤ ε * M) : ∑ j ∈ nodeIndices M, tile ε M j x = 1 := by
  have hprod := Finset.prod_univ_sum (fun _ : Fin 4 => Finset.range (2 * M + 1))
    (fun μ j => bump (ε⁻¹ * x μ + M - j))
  unfold nodeIndices tile scaledCoord
  rw [← hprod]
  refine Finset.prod_eq_one fun μ _ => sum_bump_translates_eq_one ?_
  rw [abs_mul, abs_of_pos (inv_pos.2 hε), inv_mul_le_iff₀ hε]
  exact hx μ
theorem hasFDerivAt_scaledCoord (ε : ℝ) (M : ℕ) (j : Fin 4 → ℕ) (μ : Fin 4) (x : R4) :
    HasFDerivAt (scaledCoord ε M j μ)
      (ε⁻¹ • (ContinuousLinearMap.proj μ : R4 →L[ℝ] ℝ)) x := by
  have h := ((ContinuousLinearMap.proj μ : R4 →L[ℝ] ℝ).hasFDerivAt (x := x)).const_mul ε⁻¹
  exact (h.add_const (M : ℝ)).sub_const (j μ : ℝ)
def tileDeriv (ε : ℝ) (M : ℕ) (j : Fin 4 → ℕ) (x : R4) : R4 →L[ℝ] ℝ :=
  ∑ i, (∏ k ∈ Finset.univ.erase i, bump (scaledCoord ε M j k x)) •
    (deriv bump (scaledCoord ε M j i x) •
      (ε⁻¹ • (ContinuousLinearMap.proj i : R4 →L[ℝ] ℝ)))
theorem hasFDerivAt_tile (ε : ℝ) (M : ℕ) (j : Fin 4 → ℕ) (x : R4) :
    HasFDerivAt (tile ε M j) (tileDeriv ε M j x) x := by
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      HasFDerivAt (fun x => bump (scaledCoord ε M j i x))
        (deriv bump (scaledCoord ε M j i x) •
          (ε⁻¹ • (ContinuousLinearMap.proj i : R4 →L[ℝ] ℝ))) x := fun i _ =>
    ((bump_contDiff.differentiable (by norm_num)) _).hasDerivAt.comp_hasFDerivAt x
      (hasFDerivAt_scaledCoord ε M j i x)
  exact HasFDerivAt.finsetProd hd
def partialFactor (μ ν : Fin 4) : ℝ → ℝ := if ν = μ then deriv bump else bump
theorem tileDeriv_apply_single (ε : ℝ) (M : ℕ) (j : Fin 4 → ℕ) (x : R4) (μ : Fin 4) :
    tileDeriv ε M j x (Pi.single μ 1) =
      ε⁻¹ * ∏ ν, partialFactor μ ν (scaledCoord ε M j ν x) := by
  unfold tileDeriv
  rw [sum_apply, Finset.sum_eq_single μ]
  · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ)]
    have h1 : ∏ ν ∈ Finset.univ.erase μ, partialFactor μ ν (scaledCoord ε M j ν x) =
        ∏ k ∈ Finset.univ.erase μ, bump (scaledCoord ε M j k x) := by
      refine Finset.prod_congr rfl fun ν hν => ?_
      simp [partialFactor, Finset.ne_of_mem_erase hν]
    rw [h1]
    simp [partialFactor]
    ring
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ μ) h
def firstTaylor (f : R4 → ℂ) (c x : R4) : ℂ := f c + fderiv ℝ f c (x - c)
def tileApprox (f : R4 → ℂ) (ε : ℝ) (M : ℕ) (x : R4) : ℂ :=
  ∑ j ∈ nodeIndices M, (tile ε M j x : ℂ) * firstTaylor f (nodePoint ε M j) x
theorem norm_firstTaylor_sub_le {f : R4 → ℂ} (hf : ContDiff ℝ 1 f) {ε δ η : ℝ} (hεδ : ε < δ)
    (hη : 0 ≤ η) (hD : ∀ u v : R4, ‖u - v‖ < δ → ‖fderiv ℝ f u - fderiv ℝ f v‖ ≤ η)
    {c x : R4} (h : ‖x - c‖ ≤ ε) : ‖firstTaylor f c x - f x‖ ≤ η * ε := by
  have hdiff : ∀ u ∈ Metric.ball c δ, HasFDerivWithinAt f (fderiv ℝ f u) (Metric.ball c δ) u :=
    fun u _ => ((hf.differentiable (by norm_num)) u).hasFDerivAt.hasFDerivWithinAt
  have hb : ∀ u ∈ Metric.ball c δ, ‖fderiv ℝ f u - fderiv ℝ f c‖ ≤ η := fun u hu =>
    hD u c (by rwa [Metric.mem_ball, dist_eq_norm] at hu)
  have hδ : 0 < δ := lt_of_le_of_lt ((norm_nonneg _).trans h) hεδ
  have hx : x ∈ Metric.ball c δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt h hεδ
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' hdiff hb (convex_ball c δ)
    (Metric.mem_ball_self hδ) hx
  have he : firstTaylor f c x - f x = -(f x - f c - fderiv ℝ f c (x - c)) := by
    unfold firstTaylor
    ring
  rw [he, norm_neg]
  exact key.trans (mul_le_mul_of_nonneg_left h hη)
theorem hasFDerivAt_firstTaylor (f : R4 → ℂ) (c x : R4) :
    HasFDerivAt (firstTaylor f c) (fderiv ℝ f c) x := by
  have h1 := (fderiv ℝ f c).hasFDerivAt (x := x - c)
  have h2 : HasFDerivAt (fun y : R4 => y - c) (ContinuousLinearMap.id ℝ R4) x :=
    (hasFDerivAt_id x).sub_const c
  have h3 : HasFDerivAt (fun y : R4 => fderiv ℝ f c (y - c)) (fderiv ℝ f c) x := by
    have h := h1.comp x h2
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  exact h3.const_add (f c)
theorem tileApprox_sub_eq {f : R4 → ℂ} {ε : ℝ} (hε : 0 < ε) {M : ℕ}
    (hsupp : ∀ x, f x ≠ 0 → ∀ μ, |x μ| ≤ ε * M) (x : R4) :
    tileApprox f ε M x - f x =
      ∑ j ∈ nodeIndices M, (tile ε M j x : ℂ) * (firstTaylor f (nodePoint ε M j) x - f x) := by
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  by_cases h : f x = 0
  · simp [h, tileApprox]
  · have h1 : (∑ j ∈ nodeIndices M, (tile ε M j x : ℂ)) = 1 := by
      have := sum_tile_eq_one hε (hsupp x h)
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) this
    rw [h1, one_mul]
    rfl
theorem norm_tileApprox_sub_le {f : R4 → ℂ} {ε C H : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hH : 0 ≤ H) {M : ℕ} (hw : IsUnitWeight C bump)
    (hsupp : ∀ x, f x ≠ 0 → ∀ μ, |x μ| ≤ ε * M)
    (hnear : ∀ c x : R4, ‖x - c‖ ≤ ε → ‖firstTaylor f c x - f x‖ ≤ H) (x : R4) :
    ‖tileApprox f ε M x - f x‖ ≤ (3 * C) ^ 4 * H := by
  rw [tileApprox_sub_eq hε hsupp]
  refine (norm_sum_le _ _).trans ?_
  have := sum_abs_prod_mul_le (w := fun _ => bump)
    (e := fun j => ‖firstTaylor f (nodePoint ε M j) x - f x‖) hε hC hH M (fun _ => hw) x
    (fun j hj => hnear _ _ hj)
  refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) this
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rfl
theorem partialFactor_isUnitWeight {C : ℝ} (h₁ : IsUnitWeight C bump)
    (h₂ : IsUnitWeight C (deriv bump)) (μ ν : Fin 4) : IsUnitWeight C (partialFactor μ ν) := by
  unfold partialFactor
  split_ifs
  · exact h₂
  · exact h₁
theorem norm_pi_single_one_le (μ : Fin 4) : ‖(Pi.single μ 1 : R4)‖ ≤ 1 := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.C1Banach.norm_single_one_le <;> assumption
def errorDeriv (f : R4 → ℂ) (ε : ℝ) (M : ℕ) (x : R4) : R4 →L[ℝ] ℂ :=
  ∑ j ∈ nodeIndices M,
    ((tile ε M j x : ℂ) • (fderiv ℝ f (nodePoint ε M j) - fderiv ℝ f x) +
      (firstTaylor f (nodePoint ε M j) x - f x) •
        Complex.ofRealCLM.comp (tileDeriv ε M j x))
theorem hasFDerivAt_tileApprox {f : R4 → ℂ} (hf : ContDiff ℝ 1 f) {ε : ℝ} (hε : 0 < ε) {M : ℕ}
    (hsupp : ∀ x, f x ≠ 0 → ∀ μ, |x μ| ≤ ε * M) (x : R4) :
    HasFDerivAt (tileApprox f ε M) (errorDeriv f ε M x + fderiv ℝ f x) x := by
  have hfx : HasFDerivAt f (fderiv ℝ f x) x := ((hf.differentiable (by norm_num)) x).hasFDerivAt
  have hterm : ∀ j ∈ nodeIndices M,
      HasFDerivAt (fun x => (tile ε M j x : ℂ) * (firstTaylor f (nodePoint ε M j) x - f x))
        ((tile ε M j x : ℂ) • (fderiv ℝ f (nodePoint ε M j) - fderiv ℝ f x) +
          (firstTaylor f (nodePoint ε M j) x - f x) •
            Complex.ofRealCLM.comp (tileDeriv ε M j x)) x := by
    intro j _
    have h1 : HasFDerivAt (fun x => (tile ε M j x : ℂ))
        (Complex.ofRealCLM.comp (tileDeriv ε M j x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_tile ε M j x)
    exact h1.mul ((hasFDerivAt_firstTaylor f _ x).sub hfx)
  have hsum := (HasFDerivAt.fun_sum hterm).add hfx
  have heq : tileApprox f ε M = fun x =>
      (∑ j ∈ nodeIndices M, (tile ε M j x : ℂ) * (firstTaylor f (nodePoint ε M j) x - f x)) +
        f x := by
    funext y
    rw [← tileApprox_sub_eq hε hsupp]
    ring
  rw [heq]
  exact hsum
theorem norm_fderiv_tileApprox_sub_le {f : R4 → ℂ} (hf : ContDiff ℝ 1 f) {ε C η : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hη : 0 ≤ η) {M : ℕ} (h₁ : IsUnitWeight C bump)
    (h₂ : IsUnitWeight C (deriv bump)) (hsupp : ∀ x, f x ≠ 0 → ∀ μ, |x μ| ≤ ε * M)
    (hnear : ∀ c x : R4, ‖x - c‖ ≤ ε → ‖firstTaylor f c x - f x‖ ≤ η * ε)
    (hnear' : ∀ c x : R4, ‖x - c‖ ≤ ε → ‖fderiv ℝ f c - fderiv ℝ f x‖ ≤ η)
    (x : R4) (μ : Fin 4) :
    ‖fderiv ℝ (tileApprox f ε M) x (Pi.single μ 1) - fderiv ℝ f x (Pi.single μ 1)‖ ≤
      2 * (3 * C) ^ 4 * η := by
  rw [(hasFDerivAt_tileApprox hf hε hsupp x).fderiv]
  have hval : (errorDeriv f ε M x + fderiv ℝ f x) (Pi.single μ 1) -
      fderiv ℝ f x (Pi.single μ 1) = errorDeriv f ε M x (Pi.single μ 1) := by
    rw [add_apply]
    ring
  rw [hval]
  unfold errorDeriv
  rw [sum_apply]
  refine (norm_sum_le _ _).trans ?_
  have hA := sum_abs_prod_mul_le (w := fun _ => bump)
    (e := fun j => ‖(fderiv ℝ f (nodePoint ε M j) - fderiv ℝ f x) (Pi.single μ 1)‖)
    hε hC hη M (fun _ => h₁) x (fun j hj => by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have h3 := hnear' (nodePoint ε M j) x hj
      have h4 := norm_pi_single_one_le μ
      calc _ ≤ η * 1 := mul_le_mul h3 h4 (norm_nonneg _) hη
        _ = η := mul_one η)
  have hB := sum_abs_prod_mul_le (w := partialFactor μ)
    (e := fun j => ε⁻¹ * ‖firstTaylor f (nodePoint ε M j) x - f x‖)
    hε hC hη M (partialFactor_isUnitWeight h₁ h₂ μ) x (fun j hj => by
      have h3 := hnear (nodePoint ε M j) x hj
      calc ε⁻¹ * ‖firstTaylor f (nodePoint ε M j) x - f x‖ ≤ ε⁻¹ * (η * ε) :=
            mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hε.le)
        _ = η := by field_simp)
  have hterm : ∀ j ∈ nodeIndices M,
      ‖((tile ε M j x : ℂ) • (fderiv ℝ f (nodePoint ε M j) - fderiv ℝ f x) +
        (firstTaylor f (nodePoint ε M j) x - f x) •
          Complex.ofRealCLM.comp (tileDeriv ε M j x)) (Pi.single μ 1)‖ ≤
      |∏ ν, bump (scaledCoord ε M j ν x)| *
          ‖(fderiv ℝ f (nodePoint ε M j) - fderiv ℝ f x) (Pi.single μ 1)‖ +
        |∏ ν, partialFactor μ ν (scaledCoord ε M j ν x)| *
          (ε⁻¹ * ‖firstTaylor f (nodePoint ε M j) x - f x‖) := by
    intro j _
    rw [add_apply, smul_apply,
      smul_apply, ContinuousLinearMap.comp_apply, tileDeriv_apply_single]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h5 : ‖Complex.ofRealCLM (ε⁻¹ * ∏ ν, partialFactor μ ν (scaledCoord ε M j ν x))‖ =
        ε⁻¹ * |∏ ν, partialFactor μ ν (scaledCoord ε M j ν x)| := by
      rw [Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (inv_pos.2 hε)]
    rw [h5]
    unfold tile
    ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib]
  linarith [hA, hB]
theorem scaledCoord_contDiff (ε : ℝ) (M : ℕ) (j : Fin 4 → ℕ) (μ : Fin 4) :
    ContDiff ℝ 1 (scaledCoord ε M j μ) :=
  ((contDiff_const.mul (contDiff_apply ℝ ℝ μ)).add contDiff_const).sub contDiff_const
theorem tile_contDiff (ε : ℝ) (M : ℕ) (j : Fin 4 → ℕ) : ContDiff ℝ 1 (tile ε M j) :=
  contDiff_prod fun μ _ => bump_contDiff.comp (scaledCoord_contDiff ε M j μ)
theorem firstTaylor_contDiff (f : R4 → ℂ) (c : R4) : ContDiff ℝ 1 (firstTaylor f c) :=
  contDiff_const.add ((fderiv ℝ f c).contDiff.comp (contDiff_id.sub contDiff_const))
theorem tileApprox_contDiff (f : R4 → ℂ) (ε : ℝ) (M : ℕ) :
    ContDiff ℝ 1 (tileApprox f ε M) := by
  unfold tileApprox
  exact ContDiff.sum fun j _ =>
    (Complex.ofRealCLM.contDiff.comp (tile_contDiff ε M j)).mul (firstTaylor_contDiff f _)
theorem norm_sub_nodePoint_le_of_tile_ne_zero {ε : ℝ} (hε : 0 < ε) {M : ℕ} {j : Fin 4 → ℕ}
    {x : R4} (h : tile ε M j x ≠ 0) : ‖x - nodePoint ε M j‖ ≤ ε := by
  refine (pi_norm_le_iff_of_nonneg hε.le).2 fun μ => ?_
  rw [Real.norm_eq_abs]
  refine abs_sub_nodePoint_le hε ?_
  by_contra hle
  exact Finset.prod_ne_zero_iff.1 h μ (Finset.mem_univ μ)
    (bump_eq_zero_of_one_le_abs (le_of_lt (not_le.1 hle)))
theorem tile_hasCompactSupport {ε : ℝ} (hε : 0 < ε) (M : ℕ) (j : Fin 4 → ℕ) :
    HasCompactSupport (tile ε M j) :=
  HasCompactSupport.intro (isCompact_closedBall (nodePoint ε M j) ε) fun x hx => by
    by_contra hne
    exact hx (by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact norm_sub_nodePoint_le_of_tile_ne_zero hε hne)
theorem tileApprox_hasCompactSupport (f : R4 → ℂ) {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    HasCompactSupport (tileApprox f ε M) := by
  classical
  have hterm : ∀ j, HasCompactSupport fun x =>
      (tile ε M j x : ℂ) * firstTaylor f (nodePoint ε M j) x := fun j =>
    HasCompactSupport.mul_right
      ((tile_hasCompactSupport hε M j).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))
  unfold tileApprox
  induction nodeIndices M using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hterm j).add ih
section ProductSums
variable {y z : RealPlane} {ρ : ℝ}
theorem isProductSumIn_zero : IsProductSumIn y z ρ 0 := by
  refine ⟨1, le_rfl, fun _ => 0, fun _ => 0, fun _ => ⟨⟨contDiff_const, HasCompactSupport.zero⟩,
    ⟨contDiff_const, HasCompactSupport.zero⟩, ?_, ?_⟩, ?_⟩
  · simp [tsupport]
  · simp [tsupport]
  · funext x
    simp [productFunction]
theorem IsProductSumIn.add {g h : R4 → ℂ} (hg : IsProductSumIn y z ρ g)
    (hh : IsProductSumIn y z ρ h) : IsProductSumIn y z ρ (g + h) := by
  obtain ⟨p, hp, α, φ, hm, rfl⟩ := hg
  obtain ⟨q, _, α', φ', hm', rfl⟩ := hh
  refine ⟨p + q, by omega, Fin.append α α', Fin.append φ φ', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left, Fin.append_left]
      exact hm i
    · rw [Fin.append_right, Fin.append_right]
      exact hm' i
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
theorem isProductSumIn_finsetSum {ι : Type*} (s : Finset ι) (G : ι → R4 → ℂ)
    (h : ∀ i ∈ s, IsProductSumIn y z ρ (G i)) :
    IsProductSumIn y z ρ fun x => ∑ i ∈ s, G i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isProductSumIn_zero
  | insert i s hi ih =>
    have he : (fun x => ∑ k ∈ insert i s, G k x) = G i + fun x => ∑ k ∈ s, G k x := by
      funext x
      simp [Finset.sum_insert hi]
    rw [he]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
theorem isProductSumIn_mul_mul {A Φ L L' : RealPlane → ℝ} (hA : A ∈ realLabels)
    (hΦ : Φ ∈ realLabels) (hsA : tsupport A ⊆ openDiscAt y ρ)
    (hsΦ : tsupport Φ ⊆ openDiscAt z ρ) (hL : ContDiff ℝ 1 L) (hL' : ContDiff ℝ 1 L') (b : ℂ) :
    IsProductSumIn y z ρ fun x =>
      b * ((L (planeComponent x) * A (planeComponent x) : ℝ) : ℂ) *
        ((L' (orthogonalComponent x) * Φ (orthogonalComponent x) : ℝ) : ℂ) := by
  have h1 : HasCompactSupport fun y => L y * A y := hA.2.mul_left (f := L)
  have h2 := h1.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨1, le_rfl, fun _ y => b * ((L y * A y : ℝ) : ℂ), fun _ z => L' z * Φ z,
    fun _ => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hL.mul hA.1))
  · exact h2.mul_left (f := fun _ => b)
  · exact hL'.mul hΦ.1
  · exact hΦ.2.mul_left (f := L')
  · refine (closure_mono fun v hv => ?_).trans hsA
    rw [Function.mem_support] at hv ⊢
    intro h0
    simp [h0] at hv
  · refine (closure_mono fun v hv => ?_).trans hsΦ
    rw [Function.mem_support] at hv ⊢
    intro h0
    simp [h0] at hv
  · funext x
    simp [productFunction]
end ProductSums
def planeTile (ε : ℝ) (M a b : ℕ) (v : RealPlane) : ℝ :=
  bump (ε⁻¹ * v 0 + M - a) * bump (ε⁻¹ * v 1 + M - b)
theorem planeCoord_contDiff (i : Fin 2) : ContDiff ℝ 1 fun v : RealPlane => v i :=
  (EuclideanSpace.proj i : RealPlane →L[ℝ] ℝ).contDiff
theorem planeTile_contDiff (ε : ℝ) (M a b : ℕ) : ContDiff ℝ 1 (planeTile ε M a b) :=
  (bump_contDiff.comp (((contDiff_const.mul (planeCoord_contDiff 0)).add
    contDiff_const).sub contDiff_const)).mul
  (bump_contDiff.comp (((contDiff_const.mul (planeCoord_contDiff 1)).add
    contDiff_const).sub contDiff_const))
theorem norm_plane_le_two_mul {v : RealPlane} {r : ℝ} (hr : 0 ≤ r) (h0 : |v 0| ≤ r)
    (h1 : |v 1| ≤ r) : ‖v‖ ≤ 2 * r := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [Fin.sum_univ_two]
  simp only [Real.norm_eq_abs]
  nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)]
theorem abs_sub_le_of_bump_ne_zero {ε s t : ℝ} (hε : 0 < ε) {m : ℝ}
    (h : bump (ε⁻¹ * t + s - m) ≠ 0) : |t - ε * (m - s)| ≤ ε := by
  have hb : |ε⁻¹ * t + s - m| ≤ 1 := by
    by_contra hle
    exact h (bump_eq_zero_of_one_le_abs (le_of_lt (not_le.1 hle)))
  have he : t - ε * (m - s) = ε * (ε⁻¹ * t + s - m) := by
    field_simp
    ring
  rw [he, abs_mul, abs_of_pos hε]
  nlinarith
theorem norm_sub_le_of_planeTile_ne_zero {ε : ℝ} (hε : 0 < ε) {M a b : ℕ} {u v : RealPlane}
    (h0 : u 0 = ε * ((a : ℝ) - M)) (h1 : u 1 = ε * ((b : ℝ) - M)) (h : planeTile ε M a b v ≠ 0) :
    ‖v - u‖ ≤ 2 * ε := by
  have hn := mul_ne_zero_iff.1 h
  refine norm_plane_le_two_mul hε.le ?_ ?_
  · have := abs_sub_le_of_bump_ne_zero hε hn.1
    simpa [h0] using this
  · have := abs_sub_le_of_bump_ne_zero hε hn.2
    simpa [h1] using this
theorem planeTile_mem_realLabels {ε : ℝ} (hε : 0 < ε) {M a b : ℕ} {u : RealPlane}
    (h0 : u 0 = ε * ((a : ℝ) - M)) (h1 : u 1 = ε * ((b : ℝ) - M)) :
    planeTile ε M a b ∈ realLabels ∧
      tsupport (planeTile ε M a b) ⊆ Metric.closedBall u (2 * ε) := by
  have hsub : tsupport (planeTile ε M a b) ⊆ Metric.closedBall u (2 * ε) :=
    closure_minimal (fun v hv => by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact norm_sub_le_of_planeTile_ne_zero hε h0 h1 hv) Metric.isClosed_closedBall
  exact ⟨⟨planeTile_contDiff ε M a b,
    (isCompact_closedBall u (2 * ε)).of_isClosed_subset (isClosed_tsupport _) hsub⟩, hsub⟩
theorem planeComponent_at_zero (x : R4) : planeComponent x 0 = x 3 := by
  simp [planeComponent]
theorem planeComponent_at_one (x : R4) : planeComponent x 1 = x 0 := by
  simp [planeComponent]
theorem orthogonalComponent_at_zero (x : R4) : orthogonalComponent x 0 = x 1 := by
  simp [orthogonalComponent]
theorem orthogonalComponent_at_one (x : R4) : orthogonalComponent x 1 = x 2 := by
  simp [orthogonalComponent]
theorem tile_eq_mul (ε : ℝ) (M : ℕ) (j : Fin 4 → ℕ) (x : R4) :
    tile ε M j x = planeTile ε M (j 3) (j 0) (planeComponent x) *
      planeTile ε M (j 1) (j 2) (orthogonalComponent x) := by
  unfold tile planeTile scaledCoord
  rw [Fin.prod_univ_four, planeComponent_at_zero, planeComponent_at_one,
    orthogonalComponent_at_zero, orthogonalComponent_at_one]
  ring
theorem firstTaylor_eq_coords (f : R4 → ℂ) (c x : R4) :
    firstTaylor f c x = f c + ((x 3 - c 3 : ℝ) : ℂ) * fderiv ℝ f c (Pi.single 3 1) +
      ((x 0 - c 0 : ℝ) : ℂ) * fderiv ℝ f c (Pi.single 0 1) +
      ((x 1 - c 1 : ℝ) : ℂ) * fderiv ℝ f c (Pi.single 1 1) +
      ((x 2 - c 2 : ℝ) : ℂ) * fderiv ℝ f c (Pi.single 2 1) := by
  have hv : x - c = ∑ μ, (x μ - c μ) • (Pi.single μ 1 : R4) := by
    funext ν
    simp [Finset.sum_apply, Pi.single_apply]
  unfold firstTaylor
  rw [hv, map_sum, Fin.sum_univ_four]
  simp only [map_smul, Complex.real_smul]
  ring
theorem isProductSumIn_tile_mul {y z : RealPlane} {ρ ε : ℝ} (hε : 0 < ε) {M : ℕ}
    {j : Fin 4 → ℕ} (f : R4 → ℂ)
    (hy : Metric.closedBall (planeComponent (nodePoint ε M j)) (2 * ε) ⊆ openDiscAt y ρ)
    (hz : Metric.closedBall (orthogonalComponent (nodePoint ε M j)) (2 * ε) ⊆ openDiscAt z ρ) :
    IsProductSumIn y z ρ fun x =>
      (tile ε M j x : ℂ) * firstTaylor f (nodePoint ε M j) x := by
  set c := nodePoint ε M j with hc
  obtain ⟨hA, hsA⟩ := planeTile_mem_realLabels (a := j 3) (b := j 0) (u := planeComponent c) hε
    (by rw [planeComponent_at_zero]; rfl) (by rw [planeComponent_at_one]; rfl)
  obtain ⟨hΦ, hsΦ⟩ := planeTile_mem_realLabels (a := j 1) (b := j 2)
    (u := orthogonalComponent c) hε
    (by rw [orthogonalComponent_at_zero]; rfl) (by rw [orthogonalComponent_at_one]; rfl)
  have term := fun (L L' : RealPlane → ℝ) (hL : ContDiff ℝ 1 L) (hL' : ContDiff ℝ 1 L')
      (b : ℂ) =>
    isProductSumIn_mul_mul (y := y) (z := z) (ρ := ρ) hA hΦ (hsA.trans hy) (hsΦ.trans hz)
      hL hL' b
  have hone : ContDiff ℝ 1 fun _ : RealPlane => (1 : ℝ) := contDiff_const
  have hcoord : ∀ (i : Fin 2) (r : ℝ), ContDiff ℝ 1 fun v : RealPlane => v i - r :=
    fun i r => (planeCoord_contDiff i).sub contDiff_const
  have hsum := ((((term _ _ hone hone (f c)).add
    (term _ _ (hcoord 0 (c 3)) hone (fderiv ℝ f c (Pi.single 3 1)))).add
    (term _ _ (hcoord 1 (c 0)) hone (fderiv ℝ f c (Pi.single 0 1)))).add
    (term _ _ hone (hcoord 0 (c 1)) (fderiv ℝ f c (Pi.single 1 1)))).add
    (term _ _ hone (hcoord 1 (c 2)) (fderiv ℝ f c (Pi.single 2 1)))
  convert hsum using 1
  funext x
  simp only [Pi.add_apply]
  rw [tile_eq_mul, firstTaylor_eq_coords, planeComponent_at_zero, planeComponent_at_one,
    orthogonalComponent_at_zero, orthogonalComponent_at_one]
  push_cast
  ring
theorem closedBall_subset_openDiscAt {u y : RealPlane} {ε ρ : ℝ} (hu : ‖u - y‖ < ρ)
    (h : 2 * ε ≤ ρ) : Metric.closedBall u (2 * ε) ⊆ openDiscAt y (2 * ρ) := by
  intro v hv
  rw [Metric.mem_closedBall, dist_eq_norm] at hv
  have ht : ‖v - y‖ ≤ ‖v - u‖ + ‖u - y‖ := by
    simpa [dist_eq_norm] using dist_triangle v u y
  change ‖v - y‖ < 2 * ρ
  linarith
theorem norm_components_sub_lt {c x₀ : R4} {ρ : ℝ} (h : c ∈ EuclideanBalls.euclidBall x₀ ρ) :
    ‖planeComponent c - planeComponent x₀‖ < ρ ∧
      ‖orthogonalComponent c - orthogonalComponent x₀‖ < ρ := by
  have h' : Real.sqrt (∑ μ, (c - x₀) μ ^ 2) < ρ := h
  rw [Fin.sum_univ_four] at h'
  constructor
  · rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    refine lt_of_le_of_lt (Real.sqrt_le_sqrt ?_) h'
    simp only [PiLp.sub_apply, planeComponent_at_zero, planeComponent_at_one, Real.norm_eq_abs,
      sq_abs, Pi.sub_apply]
    nlinarith [sq_nonneg (c 1 - x₀ 1), sq_nonneg (c 2 - x₀ 2)]
  · rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    refine lt_of_le_of_lt (Real.sqrt_le_sqrt ?_) h'
    simp only [PiLp.sub_apply, orthogonalComponent_at_zero, orthogonalComponent_at_one,
      Real.norm_eq_abs, sq_abs, Pi.sub_apply]
    nlinarith [sq_nonneg (c 0 - x₀ 0), sq_nonneg (c 3 - x₀ 3)]
theorem firstTaylor_eq_zero {f : R4 → ℂ} {c : R4} (h : c ∉ tsupport f) (x : R4) :
    firstTaylor f c x = 0 := by
  simp [firstTaylor, image_eq_zero_of_notMem_tsupport h, fderiv_of_notMem_tsupport (𝕜 := ℝ) h]
theorem exists_productSum_approx {x₀ : R4} {ρ₀ : ℝ} {f : R4 → ℂ} (hf : ContDiff ℝ 1 f)
    (hcs : HasCompactSupport f) (hsub : tsupport f ⊆ EuclideanBalls.euclidBall x₀ ρ₀)
    (hρ : 0 < ρ₀) {η : ℝ} (hη : 0 < η) :
    ∃ g : R4 → ℂ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧
      IsProductSumIn (planeComponent x₀) (orthogonalComponent x₀) (2 * ρ₀) g ∧
      (∀ x, ‖g x - f x‖ ≤ η) ∧
      ∀ (μ : Fin 4) (x : R4),
        ‖fderiv ℝ g x (Pi.single μ 1) - fderiv ℝ f x (Pi.single μ 1)‖ ≤ η := by
  obtain ⟨C, hC1, hw₁, hw₂⟩ := exists_unitWeight_bound
  have hC : 0 ≤ C := by linarith
  have hK : 0 < (3 * C) ^ 4 := by positivity
  obtain ⟨η', hη'def⟩ : ∃ η', η' = η / (2 * (3 * C) ^ 4) := ⟨_, rfl⟩
  have hη' : 0 < η' := by rw [hη'def]; positivity
  have hKη : 2 * (3 * C) ^ 4 * η' = η := by
    rw [hη'def]
    field_simp
  have hDu : UniformContinuous (fderiv ℝ f) :=
    (hcs.fderiv (𝕜 := ℝ)).uniformContinuous_of_continuous (hf.continuous_fderiv one_ne_zero)
  obtain ⟨δ, hδ, hD⟩ := Metric.uniformContinuous_iff.1 hDu η' hη'
  have hD' : ∀ u v : R4, ‖u - v‖ < δ → ‖fderiv ℝ f u - fderiv ℝ f v‖ ≤ η' := fun u v h => by
    have h2 := hD (a := u) (b := v) (by rwa [dist_eq_norm])
    rw [dist_eq_norm] at h2
    exact h2.le
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = min (min (δ / 2) (ρ₀ / 2)) 1 := ⟨_, rfl⟩
  have hε : 0 < ε := by
    rw [hεdef]
    exact lt_min (lt_min (by positivity) (by positivity)) one_pos
  have hεδ : ε < δ := by
    have : ε ≤ δ / 2 := by rw [hεdef]; exact (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have h2ε : 2 * ε ≤ ρ₀ := by
    have : ε ≤ ρ₀ / 2 := by rw [hεdef]; exact (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hε1 : ε ≤ 1 := by rw [hεdef]; exact min_le_right _ _
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.exists_norm_le
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ⌈R / ε⌉₊ := ⟨_, rfl⟩
  have hsupp : ∀ x, f x ≠ 0 → ∀ μ, |x μ| ≤ ε * M := by
    intro x hx μ
    have h1 : |x μ| ≤ ‖x‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm x μ
    have h2 := hR x (subset_tsupport f hx)
    have h3 : R / ε ≤ M := by rw [hMdef]; exact Nat.le_ceil _
    have h4 : R ≤ ε * M := by
      rw [div_le_iff₀ hε] at h3
      linarith
    linarith
  have hnear : ∀ c x : R4, ‖x - c‖ ≤ ε → ‖firstTaylor f c x - f x‖ ≤ η' * ε :=
    fun c x h => norm_firstTaylor_sub_le hf hεδ hη'.le hD' h
  have hnear' : ∀ c x : R4, ‖x - c‖ ≤ ε → ‖fderiv ℝ f c - fderiv ℝ f x‖ ≤ η' :=
    fun c x h => hD' c x (by rw [norm_sub_rev]; exact lt_of_le_of_lt h hεδ)
  refine ⟨tileApprox f ε M, tileApprox_contDiff f ε M, tileApprox_hasCompactSupport f hε M,
    ?_, fun x => ?_, fun μ x => ?_⟩
  · classical
    have he : tileApprox f ε M = fun x =>
        ∑ j ∈ (nodeIndices M).filter (fun j => nodePoint ε M j ∈ tsupport f),
          (tile ε M j x : ℂ) * firstTaylor f (nodePoint ε M j) x := by
      funext x
      unfold tileApprox
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h
      · rfl
      · rw [firstTaylor_eq_zero h, mul_zero]
    rw [he]
    refine isProductSumIn_finsetSum _ _ fun j hj => ?_
    obtain ⟨hp, ht⟩ := norm_components_sub_lt (hsub (Finset.mem_filter.1 hj).2)
    exact isProductSumIn_tile_mul hε f (closedBall_subset_openDiscAt hp h2ε)
      (closedBall_subset_openDiscAt ht h2ε)
  · refine (norm_tileApprox_sub_le hε hC (by positivity) hw₁ hsupp hnear x).trans ?_
    have h1 : (3 * C) ^ 4 * (η' * ε) ≤ (3 * C) ^ 4 * (η' * 1) := by
      refine mul_le_mul_of_nonneg_left ?_ hK.le
      exact mul_le_mul_of_nonneg_left hε1 hη'.le
    nlinarith
  · exact (norm_fderiv_tileApprox_sub_le hf hε hC hη'.le hw₁ hw₂ hsupp hnear hnear' x μ).trans
      hKη.le
theorem mem_C1c_iff (f : R4 → ℂ) :
    f ∈ C1c ℂ ↔ ContDiff ℝ 1 f ∧ HasCompactSupport f := by apply _root_.YangMills.Construction.EuclideanFunctionals.AboveHeight.mem_C1c_iff <;> assumption
theorem tendstoUniformly_of_norm_le_inv_succ {F : ℕ → R4 → ℂ} {G : R4 → ℂ}
    (h : ∀ k x, ‖F k x - G x‖ ≤ 1 / ((k : ℝ) + 1)) : TendstoUniformly F G atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro e he
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt he
  filter_upwards [eventually_ge_atTop N] with k hk x
  rw [dist_comm, dist_eq_norm]
  have h1 : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith)
  linarith [h k x]
theorem productSumsDenseC1_holds : ProductSumsDenseC1 := by
  intro x₀ ρ₀ hρ f hf hsub
  obtain ⟨hC, hcs⟩ := (mem_C1c_iff f).1 hf
  choose g hgC hgc hgS hg0 hg1 using fun n : ℕ+ =>
    exists_productSum_approx hC hcs hsub hρ (η := 1 / ((n : ℕ) : ℝ)) (by positivity)
  refine ⟨g, fun j => (mem_C1c_iff _).2 ⟨hgC j, hgc j⟩, ⟨?_, fun μ => ?_⟩, hgS⟩
  · refine tendstoUniformly_of_norm_le_inv_succ fun k x => ?_
    have := hg0 k.succPNat x
    simpa using this
  · refine tendstoUniformly_of_norm_le_inv_succ fun k x => ?_
    have := hg1 k.succPNat μ x
    simpa using this
end YangMills.Construction.EuclideanFunctionals.ProductSumApprox
end
