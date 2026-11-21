import YangMills.Construction.ResponseInTheExpansion.ProductOfSumsOverALattice
import YangMills.Construction.ResponseInTheExpansion.RapidSymbolOverALattice
import Mathlib
set_option autoImplicit false
open scoped SchwartzMap LineDeriv
noncomputable section
namespace YangMills.Construction.LatticeFourier
namespace DecayAux
private abbrev E := Fin 4 → ℝ
private def weight (p : E) : ℝ := ∏ j, (1 + p j ^ 2)⁻¹
private lemma weight_pos (p : E) : 0 < weight p := Finset.prod_pos fun j _ => by positivity
private lemma norm_le_mul_weight (g : 𝓢(E, ℂ)) : ∃ A : ℝ, 0 ≤ A ∧ ∀ p, ‖g p‖ ≤ A * weight p := by
  set C := 2 ^ 8 * ((Finset.Iic ((8 : ℕ), (0 : ℕ))).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
    with hC
  have hb : ∀ p : E, (1 + ‖p‖) ^ 8 * ‖g p‖ ≤ C := by
    intro p
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (8, 0)) (k := 8) (n := 0)
      le_rfl le_rfl g p
    simpa using this
  refine ⟨C, ?_, fun p => ?_⟩
  · exact le_trans (by positivity) (hb 0)
  · have h1 : ∏ j, (1 + p j ^ 2) ≤ (1 + ‖p‖) ^ 8 := by
      have h2 : ∏ j : Fin 4, (1 + p j ^ 2) ≤ ∏ _j : Fin 4, (1 + ‖p‖) ^ 2 := by
        refine Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => ?_)
        have h3 : |p j| ≤ ‖p‖ := by simpa using norm_le_pi_norm p j
        have h4 : p j ^ 2 ≤ ‖p‖ ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h3 2
        nlinarith [norm_nonneg p]
      calc _ ≤ _ := h2
        _ = (1 + ‖p‖) ^ 8 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    have hP : 0 < ∏ j, (1 + p j ^ 2) := Finset.prod_pos fun j _ => by positivity
    have h5 : ‖g p‖ * ∏ j, (1 + p j ^ 2) ≤ C := by
      refine le_trans ?_ (hb p)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h6 : weight p = (∏ j, (1 + p j ^ 2))⁻¹ := by
      simp [weight, Finset.prod_inv_distrib]
    rw [h6, ← div_eq_mul_inv, le_div_iff₀ hP]
    exact h5
private lemma weight_shift_le (p : E) (i : Fin 4) (θ : ℝ) (hθ : |θ| ≤ 1) :
    weight (p + θ • Pi.single i (1 : ℝ)) ≤ 4 * weight p := by
  have hθ2 : θ ^ 2 ≤ 1 := by nlinarith [abs_nonneg θ, sq_abs θ]
  have h1 : ∏ j, (1 + (p + θ • Pi.single i (1 : ℝ) : E) j ^ 2)⁻¹ ≤
      ∏ j, ((if j = i then (4 : ℝ) else 1) * (1 + p j ^ 2)⁻¹) := by
    refine Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => ?_)
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, if_true]
      rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (p j + θ + θ), sq_nonneg (p j + θ)]
    · simp [hj]
  rw [Finset.prod_mul_distrib] at h1
  simpa [Finset.prod_ite_eq', weight] using h1
private def fwdDiff (v : E) (w : E → ℂ) : E → ℂ := fun p => w (p + v) - w p
private lemma hasDerivAt_iterate_fwdDiff (e v : E) (g g' : E → ℂ)
    (H : ∀ (p : E) (θ : ℝ), HasDerivAt (fun θ : ℝ => g (p + θ • e)) (g' (p + θ • e)) θ) (n : ℕ) :
    ∀ (p : E) (θ : ℝ),
      HasDerivAt (fun θ : ℝ => ((fwdDiff v)^[n] g) (p + θ • e))
        (((fwdDiff v)^[n] g') (p + θ • e)) θ := by
  induction n with
  | zero => simpa using H
  | succ n ih =>
    intro p θ
    simp only [Function.iterate_succ_apply']
    have e1 : ∀ θ : ℝ, p + θ • e + v = p + v + θ • e := fun θ => by abel
    simp only [fwdDiff, e1]
    exact (ih (p + v) θ).sub (ih p θ)
private lemma norm_iterate_fwdDiff_le (i : Fin 4) (n : ℕ) : ∀ g : 𝓢(E, ℂ), ∃ A : ℝ, 0 ≤ A ∧
    ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ p,
      ‖((fwdDiff (h • Pi.single i (1 : ℝ)))^[n] (g : E → ℂ)) p‖ ≤ A * h ^ n * weight p := by
  induction n with
  | zero =>
    intro g
    obtain ⟨A, hA, hb⟩ := norm_le_mul_weight g
    exact ⟨A, hA, fun h _ _ p => by simpa using hb p⟩
  | succ n ih =>
    intro g
    set e : E := Pi.single i (1 : ℝ) with he
    set g' : 𝓢(E, ℂ) := ∂_{e} g with hg'
    obtain ⟨A, hA, hb⟩ := ih g'
    refine ⟨4 * A, by positivity, fun h h0 h1 p => ?_⟩
    have H : ∀ (p : E) (θ : ℝ),
        HasDerivAt (fun θ : ℝ => g (p + θ • e)) (g' (p + θ • e)) θ := by
      intro p θ
      have hl : HasDerivAt (fun θ : ℝ => p + θ • e) e θ := by
        simpa using ((hasDerivAt_id θ).smul_const e).const_add p
      have := (g.differentiableAt (x := p + θ • e)).hasFDerivAt.comp_hasDerivAt θ hl
      rw [hg', SchwartzMap.lineDerivOp_apply_eq_fderiv]
      exact this
    have hD := hasDerivAt_iterate_fwdDiff e (h • e) g g' H n p
    have key := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun θ : ℝ => ((fwdDiff (h • e))^[n] (g : E → ℂ)) (p + θ • e))
      (f' := fun θ : ℝ => ((fwdDiff (h • e))^[n] (g' : E → ℂ)) (p + θ • e))
      (a := 0) (b := h) (C := A * h ^ n * (4 * weight p))
      (fun θ _ => (hD θ).hasDerivWithinAt)
      (fun θ hθ => ?_) h ⟨h0.le, le_rfl⟩
    · have e2 : ((fwdDiff (h • e))^[n + 1] (g : E → ℂ)) p =
          ((fwdDiff (h • e))^[n] (g : E → ℂ)) (p + h • e) -
            ((fwdDiff (h • e))^[n] (g : E → ℂ)) (p + (0 : ℝ) • e) := by
        rw [Function.iterate_succ_apply']
        simp [fwdDiff]
      rw [e2]
      refine le_trans key ?_
      have := weight_pos p
      have h3 : A * h ^ n * (4 * weight p) * (h - 0) = 4 * A * h ^ (n + 1) * weight p := by ring
      exact h3.le
    · refine le_trans (hb h h0 h1 _) ?_
      have hθ' : |θ| ≤ 1 := by
        rw [abs_of_nonneg hθ.1]
        exact hθ.2.le.trans h1
      exact mul_le_mul_of_nonneg_left (weight_shift_le p i θ hθ') (by positivity)
private def latticePoint (h : ℝ) (k : Fin 4 → ℤ) : E := fun j => h * k j
private def character (h : ℝ) (z : E) (k : Fin 4 → ℤ) : ℂ :=
  Complex.exp (Complex.I * ((∑ j, h * k j * z j : ℝ) : ℂ))
private lemma latticePoint_add_single (h : ℝ) (k : Fin 4 → ℤ) (i : Fin 4) :
    latticePoint h (k + Pi.single i 1) = latticePoint h k + h • Pi.single i (1 : ℝ) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [latticePoint]
    ring
  · simp [latticePoint, hj]
private lemma character_add_single (h : ℝ) (z : E) (k : Fin 4 → ℤ) (i : Fin 4) :
    character h z (k + Pi.single i 1) =
      character h z k * Complex.exp (Complex.I * ((h * z i : ℝ) : ℂ)) := by
  have e1 : (∑ j, h * (((k + Pi.single i 1 : Fin 4 → ℤ) j : ℤ) : ℝ) * z j : ℝ) =
      (∑ j, h * k j * z j) + h * z i := by
    have : ∀ j, h * (((k + Pi.single i 1 : Fin 4 → ℤ) j : ℤ) : ℝ) * z j =
        h * k j * z j + (if j = i then h * z i else 0) := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp
        ring
      · simp [hj]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold character
  rw [e1, ← Complex.exp_add]
  congr 1
  push_cast
  ring
private lemma tsum_fwdDiff_mul_character (h : ℝ) (z : E) (i : Fin 4) (w : E → ℂ)
    (hs : Summable fun k => w (latticePoint h k) * character h z k) :
    ∑' k, (fwdDiff (h • Pi.single i (1 : ℝ)) w) (latticePoint h k) * character h z k =
      ((Complex.exp (Complex.I * ((h * z i : ℝ) : ℂ)))⁻¹ - 1) *
        ∑' k, w (latticePoint h k) * character h z k := by
  set c := Complex.exp (Complex.I * ((h * z i : ℝ) : ℂ)) with hc
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  set F : (Fin 4 → ℤ) → ℂ := fun k => w (latticePoint h k) * character h z k with hF
  let s : (Fin 4 → ℤ) ≃ (Fin 4 → ℤ) := Equiv.addRight (Pi.single i 1)
  have hs' : Summable fun k => F (s k) := s.summable_iff.2 hs
  have e1 : ∀ k, (fwdDiff (h • Pi.single i (1 : ℝ)) w) (latticePoint h k) * character h z k =
      c⁻¹ * F (s k) - F k := by
    intro k
    have : F (s k) = w (latticePoint h k + h • Pi.single i (1 : ℝ)) * (character h z k * c) := by
      simp only [hF, s, Equiv.coe_addRight, latticePoint_add_single, character_add_single, hc]
    rw [this]
    simp only [fwdDiff, hF]
    field_simp
  simp only [e1]
  rw [(hs'.mul_left _).tsum_sub hs, tsum_mul_left, s.tsum_eq F]
  ring
private lemma summable_and_tsum_line_le (h : ℝ) (h0 : 0 < h) (h1 : h ≤ 1) :
    Summable (fun m : ℤ => (1 + (h * m) ^ 2)⁻¹) ∧ ∑' m : ℤ, (1 + (h * (m : ℝ)) ^ 2)⁻¹ ≤ 8 / h := by
  set b : ℕ → ℝ := fun n => (1 + h * n)⁻¹ with hb
  have hterm : ∀ n : ℕ, (1 + (h * (n : ℝ)) ^ 2)⁻¹ ≤ 4 / h * (b n - b (n + 1)) := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hx : 0 ≤ h * n := by positivity
    have e1 : b n - b (n + 1) = h / ((1 + h * n) * (1 + h * (n + 1))) := by
      simp only [hb]
      push_cast
      field_simp
      ring
    rw [e1]
    have e2 : 4 / h * (h / ((1 + h * n) * (1 + h * (n + 1)))) =
        4 / ((1 + h * n) * (1 + h * (n + 1))) := by
      field_simp
    rw [e2, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (h * n - 1), mul_nonneg hx h0.le]
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 + (h * (i : ℝ)) ^ 2)⁻¹ ≤ 4 / h := by
    intro n
    have e1 : ∑ i ∈ Finset.range n, (1 + (h * (i : ℝ)) ^ 2)⁻¹ ≤
        ∑ i ∈ Finset.range n, 4 / h * (b i - b (i + 1)) := Finset.sum_le_sum fun i _ => hterm i
    rw [← Finset.mul_sum, Finset.sum_range_sub'] at e1
    refine e1.trans ?_
    have hb0 : b 0 = 1 := by simp [hb]
    have hbn : 0 ≤ b n := by
      simp only [hb]
      positivity
    have : 0 < 4 / h := by positivity
    nlinarith
  have hnn : ∀ n : ℕ, 0 ≤ (1 + (h * (n : ℝ)) ^ 2)⁻¹ := fun n => by positivity
  have hS : Summable (fun n : ℕ => (1 + (h * (n : ℝ)) ^ 2)⁻¹) := summable_of_sum_range_le hnn hsum
  have hT : ∑' n : ℕ, (1 + (h * (n : ℝ)) ^ 2)⁻¹ ≤ 4 / h := Real.tsum_le_of_sum_range_le hnn hsum
  have hneg : ∀ n : ℕ,
      (1 + (h * ((-((n : ℤ) + 1) : ℤ) : ℝ)) ^ 2)⁻¹ ≤ (1 + (h * (n : ℝ)) ^ 2)⁻¹ := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    refine inv_anti₀ (by positivity) ?_
    push_cast
    nlinarith [mul_nonneg h0.le hn, mul_pos h0 h0, mul_nonneg (mul_nonneg h0.le h0.le) hn]
  have hS2 : Summable (fun n : ℕ => (1 + (h * ((-((n : ℤ) + 1) : ℤ) : ℝ)) ^ 2)⁻¹) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hneg hS
  have hH : HasSum (fun m : ℤ => (1 + (h * (m : ℝ)) ^ 2)⁻¹) _ :=
    HasSum.of_nat_of_neg_add_one (f := fun m : ℤ => (1 + (h * (m : ℝ)) ^ 2)⁻¹)
      (by simpa using hS.hasSum) hS2.hasSum
  refine ⟨hH.summable, ?_⟩
  rw [hH.tsum_eq]
  have h2 := hS2.tsum_le_tsum hneg hS
  have h3 : (4 / h) + 4 / h = 8 / h := by ring
  linarith
private lemma summable_and_tsum_weight_le (hP : tsum_pi_prod_statement) (h : ℝ) (h0 : 0 < h)
    (h1 : h ≤ 1) :
    Summable (fun k => weight (latticePoint h k)) ∧
      ∑' k, weight (latticePoint h k) ≤ (8 / h) ^ 4 := by
  obtain ⟨hs, hb⟩ := summable_and_tsum_line_le h h0 h1
  have hnorm : Summable fun m : ℤ => ‖(1 + (h * (m : ℝ)) ^ 2)⁻¹‖ := by
    refine hs.congr fun m => ?_
    rw [Real.norm_of_nonneg (by positivity)]
  obtain ⟨_, hH⟩ := hP ℝ 4 (fun _ m => (1 + (h * (m : ℝ)) ^ 2)⁻¹) (fun _ => hnorm)
  have e1 : (fun k : Fin 4 → ℤ => ∏ i, (1 + (h * (k i : ℝ)) ^ 2)⁻¹) =
      fun k => weight (latticePoint h k) := rfl
  rw [e1] at hH
  refine ⟨hH.summable, ?_⟩
  rw [hH.tsum_eq, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine pow_le_pow_left₀ ?_ hb 4
  exact tsum_nonneg fun m => by positivity
end DecayAux
open DecayAux in
theorem schwartzLatticeSumDecay_holds (hP : tsum_pi_prod_statement) :
    schwartzLatticeSumDecayStatement := by
  intro f
  have hA5 : ∀ i : Fin 4, ∃ A : ℝ, 0 ≤ A ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ p,
      ‖((fwdDiff (h • Pi.single i (1 : ℝ)))^[5] (f : E → ℂ)) p‖ ≤ A * h ^ 5 * weight p :=
    fun i => norm_iterate_fwdDiff_le i 5 f
  choose A hA0 hA using hA5
  refine ⟨8 ^ 4 * (Real.pi / 2) ^ 5 * ∑ i, A i, fun h z i h0 h1 hz hzh => ?_⟩
  obtain ⟨hwS, hwT⟩ := summable_and_tsum_weight_le hP h h0 h1
  set v : E := h • Pi.single i (1 : ℝ) with hv
  have hchar : ∀ k, ‖character h z k‖ = 1 := by
    intro k
    unfold character
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hsum : ∀ n : ℕ,
      Summable fun k => ((fwdDiff v)^[n] (f : E → ℂ)) (latticePoint h k) * character h z k := by
    intro n
    obtain ⟨B, _, hB⟩ := norm_iterate_fwdDiff_le i n f
    refine Summable.of_norm_bounded (g := fun k => B * h ^ n * weight (latticePoint h k))
      (hwS.mul_left _) ?_
    intro k
    rw [norm_mul, hchar, mul_one]
    exact hB h h0 h1 _
  set c := Complex.exp (Complex.I * ((h * z i : ℝ) : ℂ)) with hc
  have hiter : ∀ n : ℕ,
      ∑' k, ((fwdDiff v)^[n] (f : E → ℂ)) (latticePoint h k) * character h z k =
        (c⁻¹ - 1) ^ n * ∑' k, (f : E → ℂ) (latticePoint h k) * character h z k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [tsum_fwdDiff_mul_character h z i _ (hsum n), ih]
      ring
  set W := ∑' k, (f : E → ℂ) (latticePoint h k) * character h z k with hW
  have h5 : ‖(c⁻¹ - 1) ^ 5 * W‖ ≤ A i * h ^ 5 * (8 / h) ^ 4 := by
    rw [← hiter 5]
    have hn : Summable fun k =>
        ‖((fwdDiff v)^[5] (f : E → ℂ)) (latticePoint h k) * character h z k‖ := (hsum 5).norm
    calc ‖∑' k, ((fwdDiff v)^[5] (f : E → ℂ)) (latticePoint h k) * character h z k‖
        ≤ ∑' k, ‖((fwdDiff v)^[5] (f : E → ℂ)) (latticePoint h k) * character h z k‖ :=
          norm_tsum_le_tsum_norm hn
      _ ≤ ∑' k, A i * h ^ 5 * weight (latticePoint h k) := by
          refine hn.tsum_le_tsum (fun k => ?_) (hwS.mul_left _)
          rw [norm_mul, hchar, mul_one]
          exact hA i h h0 h1 _
      _ = A i * h ^ 5 * ∑' k, weight (latticePoint h k) := tsum_mul_left
      _ ≤ A i * h ^ 5 * (8 / h) ^ 4 :=
          mul_le_mul_of_nonneg_left hwT (mul_nonneg (hA0 i) (by positivity))
  set y := |z i| with hy
  have hy0 : 0 < y := abs_pos.2 hz
  have hlow : 2 / Real.pi * (h * y) ≤ ‖c⁻¹ - 1‖ := by
    have e1 : c⁻¹ = Complex.exp (Complex.I * ((-(h * z i) : ℝ) : ℂ)) := by
      rw [hc, ← Complex.exp_neg]
      congr 1
      push_cast
      ring
    rw [e1, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
    have hx0 : 0 ≤ h * y / 2 := by positivity
    have hx1 : h * y / 2 ≤ Real.pi / 2 := by linarith
    have hs := Real.mul_le_sin hx0 hx1
    have e2 : |Real.sin (-(h * z i) / 2)| = Real.sin (h * y / 2) := by
      have hs0 : 0 ≤ Real.sin (h * y / 2) := le_trans (by positivity) hs
      rcases le_total 0 (z i) with hz0 | hz0
      · have : -(h * z i) / 2 = -(h * y / 2) := by
          rw [hy, abs_of_nonneg hz0]
          ring
        rw [this, Real.sin_neg, abs_neg, abs_of_nonneg hs0]
      · have : -(h * z i) / 2 = h * y / 2 := by
          rw [hy, abs_of_nonpos hz0]
          ring
        rw [this, abs_of_nonneg hs0]
    rw [e2]
    have : 2 / Real.pi * (h * y) = 2 * (2 / Real.pi * (h * y / 2)) := by ring
    rw [this]
    linarith
  have hAs : A i ≤ ∑ i, A i := Finset.single_le_sum (fun i _ => hA0 i) (Finset.mem_univ i)
  have hWn : 0 ≤ ‖W‖ := norm_nonneg _
  have step : (2 / Real.pi * (h * y)) ^ 5 * ‖W‖ ≤ A i * h * 8 ^ 4 := by
    have e3 : A i * h ^ 5 * (8 / h) ^ 4 = A i * h * 8 ^ 4 := by
      field_simp
    rw [← e3]
    refine le_trans ?_ h5
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hlow 5) hWn
  have hX : (2 / Real.pi) ^ 5 * (h ^ 4 * ‖W‖ * y ^ 5) ≤ A i * 8 ^ 4 := by
    have e4 : (2 / Real.pi * (h * y)) ^ 5 * ‖W‖ =
        h * ((2 / Real.pi) ^ 5 * (h ^ 4 * ‖W‖ * y ^ 5)) := by
      ring
    rw [e4] at step
    have e5 : A i * h * 8 ^ 4 = h * (A i * 8 ^ 4) := by ring
    rw [e5] at step
    exact le_of_mul_le_mul_left step h0
  refine ⟨hsum 0, ?_⟩
  have hgoal : h ^ 4 * ‖W‖ * y ^ 5 ≤ 8 ^ 4 * (Real.pi / 2) ^ 5 * ∑ i, A i := by
    have e6 : h ^ 4 * ‖W‖ * y ^ 5 =
        (Real.pi / 2) ^ 5 * ((2 / Real.pi) ^ 5 * (h ^ 4 * ‖W‖ * y ^ 5)) := by
      field_simp
    rw [e6]
    have hp : 0 ≤ (Real.pi / 2) ^ 5 := by positivity
    calc (Real.pi / 2) ^ 5 * ((2 / Real.pi) ^ 5 * (h ^ 4 * ‖W‖ * y ^ 5))
        ≤ (Real.pi / 2) ^ 5 * (A i * 8 ^ 4) := mul_le_mul_of_nonneg_left hX hp
      _ ≤ (Real.pi / 2) ^ 5 * ((∑ i, A i) * 8 ^ 4) := by gcongr
      _ = 8 ^ 4 * (Real.pi / 2) ^ 5 * ∑ i, A i := by ring
  have hfin : ‖(h : ℂ) ^ 4 * W‖ = h ^ 4 * ‖W‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg h0.le]
  show ‖(h : ℂ) ^ 4 * W‖ ≤ _
  rw [hfin, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact hgoal
end YangMills.Construction.LatticeFourier
