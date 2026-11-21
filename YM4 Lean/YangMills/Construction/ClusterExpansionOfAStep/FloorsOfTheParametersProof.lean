import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Filter Topology
namespace YangMills.Construction
open TorusLumps RenormalizationStepParameters
namespace StepFloors
theorem tendsto_rpow_mul_exp_neg_rpow (A b α : ℝ) (hb : 0 < b) (hα : 0 < α) :
    Tendsto (fun x : ℝ => x ^ A * Real.exp (-(b * x ^ α))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / α) b hb).comp (tendsto_rpow_atTop hα)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp]
  have hαA : α * (A / α) = A := by
    field_simp
  rw [← Real.rpow_mul hx.le, hαA, neg_mul]
theorem eventually_mul_rpow_mul_exp_le (K A b α ε : ℝ) (hb : 0 < b) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, K * (x ^ A * Real.exp (-(b * x ^ α))) ≤ ε := by
  have h : Tendsto (fun x : ℝ => K * (x ^ A * Real.exp (-(b * x ^ α)))) atTop (𝓝 (K * 0)) :=
    (tendsto_rpow_mul_exp_neg_rpow A b α hb hα).const_mul K
  rw [mul_zero] at h
  exact (h.eventually (gt_mem_nhds hε)).mono fun _ h => h.le
theorem rpow_le_clusterRange {x : ℝ} : x ^ (1 / 100 : ℝ) ≤ clusterRange x := by
  simpa [clusterRange] using Nat.le_ceil (x ^ ((1 : ℝ) / 100))
theorem clusterRange_le_rpow_add_one {x : ℝ} (hx : 0 ≤ x) :
    (clusterRange x : ℝ) ≤ x ^ (1 / 100 : ℝ) + 1 := by
  have h : 0 ≤ x ^ ((1 : ℝ) / 100) := Real.rpow_nonneg hx _
  simpa [clusterRange] using (Nat.ceil_lt_add_one h).le
theorem boxRadius_eq (x : ℝ) : boxRadius x = clusterRange x / 2 ^ 11 := rfl
theorem clusterRange_le_boxRadius (x : ℝ) :
    (clusterRange x : ℝ) ≤ 2 ^ 11 * boxRadius x + 2 ^ 11 := by
  have h : clusterRange x ≤ 2 ^ 11 * boxRadius x + 2 ^ 11 := by
    rw [boxRadius_eq]
    omega
  exact_mod_cast h
theorem boxRadius_le_clusterRange (x : ℝ) : (boxRadius x : ℝ) ≤ clusterRange x := by
  have h : boxRadius x ≤ clusterRange x := by
    rw [boxRadius_eq]
    omega
  exact_mod_cast h
theorem rpow_le_boxRadius (x : ℝ) : x ^ (1 / 100 : ℝ) / 2 ^ 11 - 1 ≤ boxRadius x := by
  have h1 := rpow_le_clusterRange (x := x)
  have h2 := clusterRange_le_boxRadius x
  have : x ^ (1 / 100 : ℝ) ≤ 2 ^ 11 * boxRadius x + 2 ^ 11 := h1.trans h2
  linarith
theorem eventually_exp_boxRadius_le (K A b ε : ℝ) (hK : 0 ≤ K) (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, K * x ^ A * Real.exp (-(b * boxRadius x)) ≤ ε := by
  have h := eventually_mul_rpow_mul_exp_le (K * Real.exp b) A (b / 2 ^ 11) (1 / 100) ε
    (by positivity) (by norm_num) hε
  filter_upwards [h, eventually_gt_atTop 0] with x hx hx0
  refine le_trans ?_ hx
  have hm := rpow_le_boxRadius x
  have hexp : Real.exp (-(b * boxRadius x)) ≤
      Real.exp b * Real.exp (-(b / 2 ^ 11 * x ^ (1 / 100 : ℝ))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : b * (x ^ (1 / 100 : ℝ) / 2 ^ 11 - 1) ≤ b * boxRadius x :=
      mul_le_mul_of_nonneg_left hm hb.le
    linarith
  calc K * x ^ A * Real.exp (-(b * boxRadius x))
      ≤ K * x ^ A * (Real.exp b * Real.exp (-(b / 2 ^ 11 * x ^ (1 / 100 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = K * Real.exp b * (x ^ A * Real.exp (-(b / 2 ^ 11 * x ^ (1 / 100 : ℝ)))) := by ring
theorem eventually_exp_clusterRange_le (K A b ε : ℝ) (hK : 0 ≤ K) (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, K * x ^ A * Real.exp (-(b * clusterRange x)) ≤ ε := by
  have h := eventually_mul_rpow_mul_exp_le K A b (1 / 100) ε hb (by norm_num) hε
  filter_upwards [h, eventually_gt_atTop 0] with x hx hx0
  refine le_trans ?_ hx
  have hexp : Real.exp (-(b * clusterRange x)) ≤ Real.exp (-(b * x ^ (1 / 100 : ℝ))) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left (rpow_le_clusterRange (x := x)) hb.le
    linarith
  calc K * x ^ A * Real.exp (-(b * clusterRange x))
      ≤ K * x ^ A * Real.exp (-(b * x ^ (1 / 100 : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = K * (x ^ A * Real.exp (-(b * x ^ (1 / 100 : ℝ)))) := by ring
theorem eventually_le_rpow (K α : ℝ) (hα : 0 < α) : ∀ᶠ x : ℝ in atTop, K ≤ x ^ α :=
  (tendsto_rpow_atTop hα).eventually_ge_atTop K
theorem eventually_le_clusterRange (K : ℝ) : ∀ᶠ x : ℝ in atTop, K ≤ clusterRange x := by
  filter_upwards [eventually_le_rpow K (1 / 100) (by norm_num)] with x hx
  exact hx.trans rpow_le_clusterRange
theorem eventually_le_boxRadius (K : ℝ) : ∀ᶠ x : ℝ in atTop, K ≤ boxRadius x := by
  filter_upwards [eventually_le_rpow (2 ^ 11 * (K + 1)) (1 / 100) (by norm_num)] with x hx
  have := rpow_le_boxRadius x
  linarith
theorem eventually_mul_rpow_neg_le (K α ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, K * x ^ (-α) ≤ ε := by
  have h : Tendsto (fun x : ℝ => K * x ^ (-α)) atTop (𝓝 (K * 0)) :=
    (tendsto_rpow_neg_atTop hα).const_mul K
  rw [mul_zero] at h
  exact (h.eventually (gt_mem_nhds hε)).mono fun _ h => h.le
theorem eventually_clusterRange_pow_mul_log_le (C : ℝ) (hC : 0 < C) (k : ℕ) (e : ℝ)
    (he : ((k : ℝ) + 1) / 100 < e) :
    ∀ᶠ x : ℝ in atTop, C * (clusterRange x : ℝ) ^ k * Real.log x ≤ x ^ e := by
  have hβ : 0 < e - ((k : ℝ) + 1) / 100 := by linarith
  have hlog : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ 1 * ‖x ^ (1 / 100 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (r := 1 / 100) (by norm_num)).bound one_pos
  filter_upwards [hlog, eventually_le_rpow (C * 2 ^ k) _ hβ,
    eventually_le_rpow 1 (1 / 100) (by norm_num), eventually_ge_atTop 1] with x hl hp hu hx
  have hx0 : 0 < x := by linarith
  have hu0 : 0 ≤ x ^ (1 / 100 : ℝ) := Real.rpow_nonneg hx0.le _
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hl' : Real.log x ≤ x ^ (1 / 100 : ℝ) := by
    rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hu0, one_mul] at hl
    exact hl
  have hr : (clusterRange x : ℝ) ≤ 2 * x ^ (1 / 100 : ℝ) := by
    have := clusterRange_le_rpow_add_one hx0.le
    linarith
  have hrk : (clusterRange x : ℝ) ^ k ≤ 2 ^ k * x ^ ((k : ℝ) / 100) := by
    calc (clusterRange x : ℝ) ^ k ≤ (2 * x ^ (1 / 100 : ℝ)) ^ k :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hr k
      _ = 2 ^ k * x ^ ((k : ℝ) / 100) := by
          rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / 100 : ℝ)), ← Real.rpow_mul hx0.le]
          congr 2
          ring
  have hsplit : x ^ e = x ^ (e - ((k : ℝ) + 1) / 100) * (x ^ ((k : ℝ) / 100) * x ^ (1 / 100 : ℝ)) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    ring
  calc C * (clusterRange x : ℝ) ^ k * Real.log x
      ≤ C * (2 ^ k * x ^ ((k : ℝ) / 100)) * x ^ (1 / 100 : ℝ) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hrk hC.le) hl' hlog0 (by positivity)
    _ = (C * 2 ^ k) * (x ^ ((k : ℝ) / 100) * x ^ (1 / 100 : ℝ)) := by ring
    _ ≤ x ^ (e - ((k : ℝ) + 1) / 100) * (x ^ ((k : ℝ) / 100) * x ^ (1 / 100 : ℝ)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
    _ = x ^ e := hsplit.symm
theorem eventually_rpow_le_mul (α b : ℝ) (hα : α < 1) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, x ^ α ≤ b * x := by
  filter_upwards [eventually_le_rpow (1 / b) (1 - α) (by linarith), eventually_gt_atTop 0]
    with x hp hx
  have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx _
  have hsplit : x = x ^ α * x ^ (1 - α) := by
    rw [← Real.rpow_add hx]
    simp
  have hb1 : 1 ≤ b * x ^ (1 - α) := by
    rw [div_le_iff₀ hb] at hp
    linarith
  calc x ^ α = x ^ α * 1 := (mul_one _).symm
    _ ≤ x ^ α * (b * x ^ (1 - α)) := mul_le_mul_of_nonneg_left hb1 hxα.le
    _ = b * (x ^ α * x ^ (1 - α)) := by ring
    _ = b * x := by rw [← hsplit]
theorem rpow_hundredth_le_add_one {p q h : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq : q ≤ p + h)
    (hh : h ≤ p ^ (99 / 100 : ℝ)) : q ^ (1 / 100 : ℝ) ≤ p ^ (1 / 100 : ℝ) + 1 := by
  have hh0 : 0 ≤ h := by linarith
  have hu : 0 < p ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos hp _
  have hv : 0 < p ^ (99 / 100 : ℝ) := Real.rpow_pos_of_pos hp _
  have hone : 1 ≤ 1 + h / p := by
    have : 0 ≤ h / p := div_nonneg hh0 hp.le
    linarith
  have hpp : p = p ^ (1 / 100 : ℝ) * p ^ (99 / 100 : ℝ) := by
    rw [← Real.rpow_add hp]
    norm_num
  have h1 : (p + h) ^ (1 / 100 : ℝ) = p ^ (1 / 100 : ℝ) * (1 + h / p) ^ (1 / 100 : ℝ) := by
    rw [← Real.mul_rpow hp.le (by linarith)]
    congr 1
    field_simp
  have h2 : (1 + h / p) ^ (1 / 100 : ℝ) ≤ 1 + h / p := by
    calc (1 + h / p) ^ (1 / 100 : ℝ) ≤ (1 + h / p) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hone (by norm_num)
      _ = 1 + h / p := Real.rpow_one _
  have h3 : p ^ (1 / 100 : ℝ) * (h / p) ≤ 1 := by
    have key : ∀ u v : ℝ, 0 < u → 0 < v → u * (h / (u * v)) = h / v := by
      intro u v hu hv
      field_simp
    have : p ^ (1 / 100 : ℝ) * (h / p) = h / p ^ (99 / 100 : ℝ) := by
      calc p ^ (1 / 100 : ℝ) * (h / p)
          = p ^ (1 / 100 : ℝ) * (h / (p ^ (1 / 100 : ℝ) * p ^ (99 / 100 : ℝ))) := by rw [← hpp]
        _ = h / p ^ (99 / 100 : ℝ) := key _ _ hu hv
    rw [this]
    exact (div_le_one hv).2 hh
  calc q ^ (1 / 100 : ℝ) ≤ (p + h) ^ (1 / 100 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hq (by norm_num)
    _ = p ^ (1 / 100 : ℝ) * (1 + h / p) ^ (1 / 100 : ℝ) := h1
    _ ≤ p ^ (1 / 100 : ℝ) * (1 + h / p) := mul_le_mul_of_nonneg_left h2 hu.le
    _ = p ^ (1 / 100 : ℝ) + p ^ (1 / 100 : ℝ) * (h / p) := by ring
    _ ≤ p ^ (1 / 100 : ℝ) + 1 := by linarith
theorem clusterRange_le_add_one {p q : ℝ} (hp : 0 ≤ p)
    (h : q ^ (1 / 100 : ℝ) ≤ p ^ (1 / 100 : ℝ) + 1) :
    clusterRange q ≤ clusterRange p + 1 := by
  have hp' : 0 ≤ p ^ ((1 : ℝ) / 100) := Real.rpow_nonneg hp _
  have h1 : ⌈q ^ ((1 : ℝ) / 100)⌉₊ ≤ ⌈p ^ ((1 : ℝ) / 100) + 1⌉₊ := Nat.ceil_mono h
  rw [Nat.ceil_add_one hp'] at h1
  exact h1
theorem eventually_clusterRange_close (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ x : ℝ in atTop, ∀ x' : ℝ, |x' - x| ≤ D →
      clusterRange x ≤ clusterRange x' + 1 ∧ clusterRange x' ≤ clusterRange x + 1 := by
  have hhalf : ∀ᶠ x : ℝ in atTop, D ≤ (x / 2) ^ (99 / 100 : ℝ) :=
    ((tendsto_rpow_atTop (y := 99 / 100) (by norm_num)).comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).eventually_ge_atTop D
  filter_upwards [hhalf, eventually_ge_atTop (2 * D + 2)] with x hh hx x' hx'
  have hx0 : 0 < x := by linarith
  have hab := abs_le.1 hx'
  have hlow : x / 2 ≤ x' := by linarith
  have hlow0 : 0 < x' := by linarith
  have hmono : (x / 2) ^ (99 / 100 : ℝ) ≤ x' ^ (99 / 100 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hlow (by norm_num)
  have hmono2 : (x / 2) ^ (99 / 100 : ℝ) ≤ x ^ (99 / 100 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  rcases le_total x x' with hle | hle
  · have h1 : x' ^ (1 / 100 : ℝ) ≤ x ^ (1 / 100 : ℝ) + 1 :=
      rpow_hundredth_le_add_one hx0 hle (by linarith) (hh.trans hmono2)
    have h2 : x ^ (1 / 100 : ℝ) ≤ x' ^ (1 / 100 : ℝ) + 1 := by
      have := Real.rpow_le_rpow hx0.le hle (by norm_num : (0 : ℝ) ≤ 1 / 100)
      linarith
    exact ⟨clusterRange_le_add_one hlow0.le h2, clusterRange_le_add_one hx0.le h1⟩
  · have h1 : x ^ (1 / 100 : ℝ) ≤ x' ^ (1 / 100 : ℝ) + 1 :=
      rpow_hundredth_le_add_one hlow0 hle (by linarith) (hh.trans hmono)
    have h2 : x' ^ (1 / 100 : ℝ) ≤ x ^ (1 / 100 : ℝ) + 1 := by
      have := Real.rpow_le_rpow hlow0.le hle (by norm_num : (0 : ℝ) ≤ 1 / 100)
      linarith
    exact ⟨clusterRange_le_add_one hlow0.le h1, clusterRange_le_add_one hx0.le h2⟩
theorem exists_pow_mul_exp_le (d : ℕ) (hd : 0 < d) (n₁ b : ℝ) (hn : 0 < n₁) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, (1 + (m : ℝ) / n₁) ^ d * Real.exp (-(b * m)) ≤ K := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = min 1 (b * n₁ / d) := ⟨_, rfl⟩
  have hβ : 0 < β := by
    rw [hβdef]
    exact lt_min one_pos (by positivity)
  have hβ1 : β ≤ 1 := by
    rw [hβdef]
    exact min_le_left _ _
  have hβ2 : β ≤ b * n₁ / d := by
    rw [hβdef]
    exact min_le_right _ _
  have hinv : 0 < β⁻¹ := inv_pos.2 hβ
  refine ⟨(β⁻¹) ^ d, pow_pos hinv d, fun m => ?_⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = (m : ℝ) / n₁ := ⟨_, rfl⟩
  rw [← hz]
  have hz0 : 0 ≤ z := by
    rw [hz]
    positivity
  have h1 : 1 + z ≤ β⁻¹ * Real.exp (β * z) := by
    have hinv1 : 1 ≤ β⁻¹ := (one_le_inv₀ hβ).2 hβ1
    have h2 : 1 + β * z ≤ Real.exp (β * z) := by
      have := Real.add_one_le_exp (β * z)
      linarith
    have h3 : β⁻¹ * (1 + β * z) ≤ β⁻¹ * Real.exp (β * z) :=
      mul_le_mul_of_nonneg_left h2 hinv.le
    have h4 : β⁻¹ * (1 + β * z) = β⁻¹ + z := by
      field_simp
    linarith
  have hexp : Real.exp (β * z) ^ d = Real.exp (d * (β * z)) := (Real.exp_nat_mul _ _).symm
  have h5 : (1 + z) ^ d ≤ (β⁻¹) ^ d * Real.exp (d * (β * z)) := by
    rw [← hexp, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) h1 _
  have h6 : d * (β * z) ≤ b * m := by
    have h7 : β * z ≤ b * n₁ / d * z := mul_le_mul_of_nonneg_right hβ2 hz0
    have h8 : (d : ℝ) * (b * n₁ / d * z) = b * m := by
      rw [hz]
      field_simp
    have h9 := mul_le_mul_of_nonneg_left h7 hd'.le
    linarith
  have h10 : Real.exp (d * (β * z)) * Real.exp (-(b * m)) ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hpd : 0 ≤ (β⁻¹) ^ d := (pow_pos hinv d).le
  calc (1 + z) ^ d * Real.exp (-(b * m))
      ≤ (β⁻¹) ^ d * Real.exp (d * (β * z)) * Real.exp (-(b * m)) :=
        mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
    _ = (β⁻¹) ^ d * (Real.exp (d * (β * z)) * Real.exp (-(b * m))) := mul_assoc _ _ _
    _ ≤ (β⁻¹) ^ d * 1 := mul_le_mul_of_nonneg_left h10 hpd
    _ = (β⁻¹) ^ d := mul_one _
variable {T : ParameterAssignment}
theorem lam_pos (h : T.Admissible) : 0 < T.lam := h.chain.2.2.1
theorem N_pos (h : T.Admissible) (k : ℕ) : 0 < T.N k := h.chain.2.2.2.2.2.2.2.1 k
theorem E_pos (h : T.Admissible) : 0 < T.E := by
  have := h.B_ge
  unfold ParameterAssignment.E
  linarith
theorem E₃_pos (h : T.Admissible) : 0 < T.E₃ := div_pos (E_pos h) h.η₃_pos
theorem κ₁_pos (h : T.Admissible) : 0 < T.κ₁ := by
  have h1 := h.κ_pos
  have h2 := h.cE_pos
  have h3 := h.σ_pos
  exact lt_min (by positivity) (by positivity)
theorem gasRate_pos (h : T.Admissible) : 0 < T.gasRate := by
  have h1 := h.κ_pos
  have h2 := h.cE_pos
  have h3 := h.σ_pos
  have h4 := κ₁_pos h
  unfold ParameterAssignment.gasRate
  exact mul_pos (by norm_num) (lt_min h2 (lt_min (by positivity) (by positivity)))
theorem n₁_pos (h : T.Admissible) : 0 < T.n₁ := by
  have : 0 < (T.side : ℝ) := by
    have := h.L_ge
    have h2 : (2 : ℕ) ^ 40 ≤ T.side := this
    have h3 : 0 < T.side := lt_of_lt_of_le (by norm_num) h2
    exact_mod_cast h3
  exact Real.rpow_pos_of_pos this _
theorem weight_pos (T : ParameterAssignment) (n : ℕ) : 0 < T.weight n :=
  mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
theorem rt_le_δ₁ (h : T.Admissible) : T.rt ≤ T.δ₁ / 2 ^ 20 := by
  have h1 := h.rt_le
  have h2 := h.δc_le
  linarith
section Conditions
variable (h : T.Admissible) {C c : ℝ} (hC : 0 < C)
include h hC
theorem eventually_drift_le (hc : 0 < c) : ∀ᶠ x : ℝ in atTop,
    C * (1 + T.E₃) + x ^ C * Real.exp (-(c * clusterRange x)) ≤ x * T.lam / 16 := by
  have hl := lam_pos h
  filter_upwards [eventually_exp_clusterRange_le 1 C c 1 zero_le_one hc one_pos,
    eventually_ge_atTop (16 * (C * (1 + T.E₃) + 1) / T.lam)] with x h1 h2
  rw [div_le_iff₀ hl] at h2
  rw [one_mul] at h1
  linarith
theorem eventually_le_sqrt : ∀ᶠ x : ℝ in atTop, C * (1 + T.E) + 1 ≤ Real.sqrt (x * T.lam / 4) ∧
    1 + T.E₃ ≤ Real.sqrt x := by
  have hl := lam_pos h
  filter_upwards [eventually_ge_atTop (4 * (C * (1 + T.E) + 1) ^ 2 / T.lam),
    eventually_ge_atTop ((1 + T.E₃) ^ 2)] with x h1 h2
  rw [div_le_iff₀ hl] at h1
  refine ⟨?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    linarith
  · exact Real.le_sqrt_of_sq_le h2
theorem eventually_boxRadius_ge : ∀ᶠ x : ℝ in atTop, 16 ≤ boxRadius x ∧ C ≤ boxRadius x := by
  filter_upwards [eventually_le_boxRadius 16, eventually_le_boxRadius C] with x h1 h2
  exact ⟨by exact_mod_cast h1, h2⟩
theorem eventually_exp_boxRadius_le_threshold : ∀ᶠ x : ℝ in atTop,
    C * Real.exp (-(T.δc / 4 * boxRadius x)) ≤ 2⁻¹ ^ 10 * T.threshold := by
  have h1 := h.δc_pos
  have h2 := h.σ_pos
  filter_upwards [eventually_exp_boxRadius_le C 0 (T.δc / 4) (2⁻¹ ^ 10 * T.threshold) hC.le
    (by positivity) (by positivity)] with x hx
  simpa using hx
theorem eventually_sq_mul_exp_boxRadius_le : ∀ᶠ x : ℝ in atTop,
    C * x ^ 2 * Real.exp (-(T.δc / 4 * boxRadius x)) ≤
      Real.exp (-(2 ^ 10 * T.rt * boxRadius x)) := by
  have h1 := h.δc_pos
  have h2 := h.rt_le
  have hβ : 0 < T.δc / 4 - 2 ^ 10 * T.rt := by linarith
  filter_upwards [eventually_exp_boxRadius_le C 2 _ 1 hC.le hβ one_pos] with x hx
  rw [Real.rpow_two] at hx
  have hsplit : Real.exp (-(T.δc / 4 * boxRadius x)) =
      Real.exp (-((T.δc / 4 - 2 ^ 10 * T.rt) * boxRadius x)) *
        Real.exp (-(2 ^ 10 * T.rt * boxRadius x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit, ← mul_assoc]
  calc _ ≤ 1 * Real.exp (-(2 ^ 10 * T.rt * boxRadius x)) :=
        mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    _ = _ := one_mul _
theorem eventually_sq_mul_exp_two_boxRadius_le :
    ∀ᶠ x : ℝ in atTop, C * x ^ 2 * Real.exp (-(2 * T.δc * boxRadius x)) ≤ 1 := by
  have h1 := h.δc_pos
  filter_upwards [eventually_exp_boxRadius_le C 2 (2 * T.δc) 1 hC.le (by positivity) one_pos]
    with x hx
  rwa [Real.rpow_two] at hx
theorem eventually_exp_boxRadius_le_rpow_neg : ∀ᶠ x : ℝ in atTop,
    C * Real.exp (-(T.δc / 4 * boxRadius x)) ≤ x ^ (-(1 / 2 : ℝ)) := by
  have h1 := h.δc_pos
  filter_upwards [eventually_exp_boxRadius_le C (1 / 2) (T.δc / 4) 1 hC.le (by positivity) one_pos,
    eventually_gt_atTop 0] with x hx hx0
  have hp : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  rw [Real.rpow_neg hx0.le, ← one_div, le_div_iff₀ hp]
  calc _ = C * x ^ (1 / 2 : ℝ) * Real.exp (-(T.δc / 4 * boxRadius x)) := by ring
    _ ≤ 1 := hx
theorem eventually_rpow_neg_le_weight : ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, (n : ℝ) ≤ C →
    C * x ^ (-(1 / 2 : ℝ)) ≤ 2⁻¹ ^ 5 * T.E / T.weight n := by
  have hE := E_pos h
  have hall : ∀ᶠ x : ℝ in atTop, ∀ n ∈ Finset.range (⌊C⌋₊ + 1),
      C * x ^ (-(1 / 2 : ℝ)) ≤ 2⁻¹ ^ 5 * T.E / T.weight n := by
    rw [Filter.eventually_all_finset]
    intro n _
    have hw := weight_pos T n
    exact eventually_mul_rpow_neg_le C (1 / 2) _ (by norm_num) (by positivity)
  filter_upwards [hall] with x hx n hn
  exact hx n (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hn)))
theorem eventually_exp_clusterRange_le_exp_rpow (hc : 0 < c) : ∀ᶠ x : ℝ in atTop,
    C * x ^ C * Real.exp (-(c * clusterRange x)) ≤ Real.exp (-(x ^ (1 / 200 : ℝ))) ∧
      C * Real.exp (-(x ^ (1 / 200 : ℝ))) ≤ 1 / C := by
  filter_upwards [eventually_exp_clusterRange_le C C (c / 2) 1 hC.le (by positivity) one_pos,
    eventually_le_rpow (2 / c) (1 / 200) (by norm_num),
    eventually_mul_rpow_mul_exp_le (C * C) 0 1 (1 / 200) 1 one_pos (by norm_num) one_pos,
    eventually_gt_atTop 0] with x h1 h2 h3 hx0
  have hv : 0 < x ^ (1 / 200 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have huv : x ^ (1 / 100 : ℝ) = x ^ (1 / 200 : ℝ) * x ^ (1 / 200 : ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  refine ⟨?_, ?_⟩
  · have hr := rpow_le_clusterRange (x := x)
    have hkey : x ^ (1 / 200 : ℝ) ≤ c / 2 * clusterRange x := by
      rw [div_le_iff₀ hc] at h2
      have hcv : 1 ≤ c / 2 * x ^ (1 / 200 : ℝ) := by linarith
      have h5 : c / 2 * x ^ (1 / 100 : ℝ) ≤ c / 2 * clusterRange x :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      rw [huv] at h5
      calc x ^ (1 / 200 : ℝ) = 1 * x ^ (1 / 200 : ℝ) := (one_mul _).symm
        _ ≤ c / 2 * x ^ (1 / 200 : ℝ) * x ^ (1 / 200 : ℝ) :=
            mul_le_mul_of_nonneg_right hcv hv.le
        _ = c / 2 * (x ^ (1 / 200 : ℝ) * x ^ (1 / 200 : ℝ)) := by ring
        _ ≤ c / 2 * clusterRange x := h5
    have hsplit : Real.exp (-(c * clusterRange x)) =
        Real.exp (-(c / 2 * clusterRange x)) * Real.exp (-(c / 2 * clusterRange x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit, ← mul_assoc]
    calc _ ≤ 1 * Real.exp (-(c / 2 * clusterRange x)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ Real.exp (-(x ^ (1 / 200 : ℝ))) := by
          rw [one_mul]
          exact Real.exp_le_exp.2 (by linarith)
  · rw [le_div_iff₀ hC]
    simp only [Real.rpow_zero, one_mul] at h3
    calc _ = C * C * Real.exp (-(x ^ (1 / 200 : ℝ))) := by ring
      _ ≤ 1 := h3
theorem eventually_log_bounds : ∀ᶠ x : ℝ in atTop,
    C * (clusterRange x : ℝ) ^ 8 * Real.log x ≤ x ^ (1 / 10 : ℝ) ∧
    C * (clusterRange x : ℝ) ^ 12 * Real.log x ≤ x ^ (1 / 6 : ℝ) ∧
    x ^ (1 / 6 : ℝ) ≤ T.gasRate * x := by
  filter_upwards [eventually_clusterRange_pow_mul_log_le C hC 8 (1 / 10) (by norm_num),
    eventually_clusterRange_pow_mul_log_le C hC 12 (1 / 6) (by norm_num),
    eventually_rpow_le_mul (1 / 6) T.gasRate (by norm_num) (gasRate_pos h)] with x h1 h2 h3
  exact ⟨h1, h2, h3⟩
theorem eventually_shift_bounds : ∀ᶠ x : ℝ in atTop, 200 * T.B ≤ x ∧ ∀ x' : ℝ, |x' - x| ≤ 2 * T.B →
    x ≤ 1.01 * x' ∧ x' ≤ 1.01 * x ∧ clusterRange x ≤ clusterRange x' + 1 ∧
      clusterRange x' ≤ clusterRange x + 1 := by
  have hB := h.B_ge
  filter_upwards [eventually_clusterRange_close (2 * T.B) (by linarith),
    eventually_ge_atTop (400 * T.B)] with x h1 h2
  refine ⟨by linarith, fun x' hx' => ?_⟩
  have hab := abs_le.1 hx'
  have := h1 x' hx'
  exact ⟨by linarith [hab.1], by linarith [hab.2], this.1, this.2⟩
theorem eventually_error_sum_le (hc : 0 < c) : ∀ᶠ x : ℝ in atTop, C * x ^ (-(1 / 2 : ℝ)) +
      (C * x * Real.exp (-(T.δc / 8 * boxRadius x)) + Real.exp (-(T.gasRate * x / 2))) * C +
      x ^ C * Real.exp (-(c * clusterRange x)) ≤ min 1 (T.E / 64) := by
  have hE := E_pos h
  have hδ := h.δc_pos
  have hch := gasRate_pos h
  set ε : ℝ := min 1 (T.E / 64) / 4 with hε
  have hε0 : 0 < ε := by
    have : 0 < min 1 (T.E / 64) := lt_min one_pos (by positivity)
    positivity
  filter_upwards [eventually_mul_rpow_neg_le C (1 / 2) ε (by norm_num) hε0,
    eventually_exp_boxRadius_le (C * C) 1 (T.δc / 8) ε (by positivity) (by positivity) hε0,
    eventually_mul_rpow_mul_exp_le C 0 (T.gasRate / 2) 1 ε (by positivity) one_pos hε0,
    eventually_exp_clusterRange_le 1 C c ε zero_le_one hc hε0] with x h1 h2 h3 h4
  simp only [Real.rpow_zero, one_mul, Real.rpow_one] at h2 h3 h4
  have e3 : Real.exp (-(T.gasRate * x / 2)) = Real.exp (-(T.gasRate / 2 * x)) := by
    congr 1
    ring
  rw [e3]
  have e4 : (C * x * Real.exp (-(T.δc / 8 * boxRadius x)) + Real.exp (-(T.gasRate / 2 * x))) * C =
      C * C * x * Real.exp (-(T.δc / 8 * boxRadius x)) + C * Real.exp (-(T.gasRate / 2 * x)) := by
    ring
  rw [e4]
  have : min 1 (T.E / 64) = 4 * ε := by
    rw [hε]
    ring
  rw [this]
  linarith
theorem eventually_decay_bounds : ∀ᶠ x : ℝ in atTop,
    16 * T.rt * boxRadius x + 16 * T.rt ≤ x ^ (1 / 90 : ℝ) ∧ x ^ (1 / 90 : ℝ) ≤ T.gasRate * x ∧
    ∀ n : ℕ, x ^ C * (1 + (n : ℝ) / T.n₁) ^ 16000 *
      Real.exp (-(1 / 4 * (T.gasRate * x + T.rt * n / 2 ^ 8))) ≤ 1 := by
  have hrt := h.rt_pos
  have hch := gasRate_pos h
  obtain ⟨K, hK, hbound⟩ :=
    exists_pow_mul_exp_le 16000 (by norm_num) T.n₁ (T.rt / 2 ^ 10) (n₁_pos h) (by positivity)
  filter_upwards [eventually_le_rpow (48 * T.rt) (1 / 90 - 1 / 100) (by norm_num),
    eventually_le_rpow 1 (1 / 100) (by norm_num),
    eventually_rpow_le_mul (1 / 90) T.gasRate (by norm_num) hch,
    eventually_mul_rpow_mul_exp_le K C (T.gasRate / 4) 1 1 (by positivity) one_pos one_pos,
    eventually_gt_atTop 0] with x h1 h2 h3 h4 hx0
  refine ⟨?_, h3, fun n => ?_⟩
  · have hr := clusterRange_le_rpow_add_one hx0.le
    have hm := boxRadius_le_clusterRange x
    have hsplit : x ^ (1 / 90 : ℝ) = x ^ (1 / 90 - 1 / 100 : ℝ) * x ^ (1 / 100 : ℝ) := by
      rw [← Real.rpow_add hx0]
      norm_num
    have h5 : 16 * T.rt * boxRadius x ≤ 16 * T.rt * (x ^ (1 / 100 : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (hm.trans hr) (by positivity)
    have h6 : 48 * T.rt * x ^ (1 / 100 : ℝ) ≤ x ^ (1 / 90 - 1 / 100 : ℝ) * x ^ (1 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have h7 : 16 * T.rt * 1 ≤ 16 * T.rt * x ^ (1 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [hsplit]
    linarith
  · have hxC : 0 < x ^ C := Real.rpow_pos_of_pos hx0 _
    simp only [Real.rpow_one] at h4
    have hsplit : Real.exp (-(1 / 4 * (T.gasRate * x + T.rt * n / 2 ^ 8))) =
        Real.exp (-(T.gasRate / 4 * x)) * Real.exp (-(T.rt / 2 ^ 10 * n)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    have hb := hbound n
    generalize (1 + (n : ℝ) / T.n₁) ^ 16000 = P at hb ⊢
    calc _ = x ^ C * Real.exp (-(T.gasRate / 4 * x)) *
          (P * Real.exp (-(T.rt / 2 ^ 10 * n))) := by ring
      _ ≤ x ^ C * Real.exp (-(T.gasRate / 4 * x)) * K :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = K * (x ^ C * Real.exp (-(T.gasRate / 4 * x))) := by ring
      _ ≤ 1 := h4
theorem eventually_tail_sum_le : ∀ᶠ x : ℝ in atTop, ∀ m : ℕ, (clusterRange x : ℝ) - 1 ≤ 64 * m →
    4 * Real.exp (-(15 / 16 * T.rt * m / 2 ^ 5)) +
        3 * Real.exp (-(T.gasRate * x) - T.rt * m / 2 ^ 8) +
        2 * x * T.N 0 * Real.exp (-(T.δ₁ * m / 2)) ≤ Real.exp (-(T.rt / 2 ^ 12 * m)) := by
  have hrt := h.rt_pos
  have hch := gasRate_pos h
  have hδ := h.chain.1
  have hN := N_pos h 0
  have hrtδ := rt_le_δ₁ h
  filter_upwards [eventually_le_clusterRange (1 + 64 * 4096 / (119 * T.rt) * Real.log 12),
    eventually_ge_atTop (Real.log 9 / T.gasRate),
    eventually_exp_clusterRange_le (2 * T.N 0 * Real.exp (T.δ₁ / 256)) 1 (T.δ₁ / 256) (1 / 3)
      (by positivity) (by positivity) (by norm_num), eventually_gt_atTop 0]
    with x h1 h2 h3 hx0 m hm
  simp only [Real.rpow_one] at h3
  rw [div_le_iff₀ hch] at h2
  set e : ℝ := Real.exp (-(T.rt / 2 ^ 12 * m)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hA : 4 * Real.exp (-(15 / 16 * T.rt * m / 2 ^ 5)) ≤ e / 3 := by
    have hsplit : Real.exp (-(15 / 16 * T.rt * m / 2 ^ 5)) =
        Real.exp (-(119 / 4096 * T.rt * m)) * e := by
      rw [he, ← Real.exp_add]
      congr 1
      ring
    have hbig : Real.log 12 ≤ 119 / 4096 * T.rt * m := by
      have h5 : 64 * 4096 / (119 * T.rt) * Real.log 12 ≤ 64 * m := by linarith
      have hpos : 0 < 119 * T.rt := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos] at h5
      linarith
    have hsmall : Real.exp (-(119 / 4096 * T.rt * m)) ≤ 1 / 12 := by
      have e12 : Real.exp (-(Real.log 12)) = 1 / 12 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
      rw [← e12]
      exact Real.exp_le_exp.2 (by linarith)
    rw [hsplit]
    have := mul_le_mul_of_nonneg_right hsmall he0.le
    linarith
  have hB : 3 * Real.exp (-(T.gasRate * x) - T.rt * m / 2 ^ 8) ≤ e / 3 := by
    have hsmall : Real.exp (-(T.gasRate * x)) ≤ 1 / 9 := by
      have e9 : Real.exp (-(Real.log 9)) = 1 / 9 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
      rw [← e9]
      exact Real.exp_le_exp.2 (by linarith)
    have hle : Real.exp (-(T.gasRate * x) - T.rt * m / 2 ^ 8) ≤
        Real.exp (-(T.gasRate * x)) * e := by
      rw [he, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have : 0 ≤ T.rt * m := by positivity
      linarith
    have := mul_le_mul_of_nonneg_right hsmall he0.le
    linarith
  have hD : 2 * x * T.N 0 * Real.exp (-(T.δ₁ * m / 2)) ≤ e / 3 := by
    have hle : Real.exp (-(T.δ₁ * m / 2)) ≤ Real.exp (-(T.δ₁ / 4 * m)) * e := by
      rw [he, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have h5 : T.rt / 2 ^ 12 * m ≤ T.δ₁ / 4 * m := by
        apply mul_le_mul_of_nonneg_right _ hm0
        linarith
      linarith
    have hle2 : Real.exp (-(T.δ₁ / 4 * m)) ≤
        Real.exp (T.δ₁ / 256) * Real.exp (-(T.δ₁ / 256 * clusterRange x)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h5 : T.δ₁ / 256 * ((clusterRange x : ℝ) - 1) ≤ T.δ₁ / 256 * (64 * m) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      linarith
    have hc0 : 0 ≤ 2 * x * T.N 0 := by positivity
    calc 2 * x * T.N 0 * Real.exp (-(T.δ₁ * m / 2))
        ≤ 2 * x * T.N 0 * (Real.exp (T.δ₁ / 256) * Real.exp (-(T.δ₁ / 256 * clusterRange x)) * e) :=
          mul_le_mul_of_nonneg_left
            (hle.trans (mul_le_mul_of_nonneg_right hle2 he0.le)) hc0
      _ = (2 * T.N 0 * Real.exp (T.δ₁ / 256) * x *
            Real.exp (-(T.δ₁ / 256 * clusterRange x))) * e := by
          ring
      _ ≤ (1 / 3) * e := mul_le_mul_of_nonneg_right h3 he0.le
      _ = e / 3 := by ring
  linarith
end Conditions
theorem eventuallyFloorConditions_holds : EventuallyFloorConditions := by
  intro T h C c hC hc
  have key : ∀ᶠ x : ℝ in atTop, T.FloorConditions C c x := by
    filter_upwards [eventually_ge_atTop (2 / T.coupling), eventually_drift_le h hC hc,
      eventually_le_sqrt h hC, eventually_boxRadius_ge h hC,
      eventually_exp_boxRadius_le_threshold h hC, eventually_sq_mul_exp_boxRadius_le h hC,
      eventually_sq_mul_exp_two_boxRadius_le h hC, eventually_exp_boxRadius_le_rpow_neg h hC,
      eventually_rpow_neg_le_weight h hC, eventually_le_clusterRange C,
      eventually_exp_clusterRange_le_exp_rpow h hC hc, eventually_log_bounds h hC,
      eventually_shift_bounds h hC, eventually_error_sum_le h hC hc,
      eventually_decay_bounds h hC, eventually_tail_sum_le h hC] with x h1 h2 h3 h4 h5 h6 h7 h8
      h9 h10 h11 h12 h13 h14 h15 h16
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
  obtain ⟨y, hy⟩ := eventually_atTop.1 key
  exact ⟨y, hy⟩
end StepFloors
end YangMills.Construction
end
