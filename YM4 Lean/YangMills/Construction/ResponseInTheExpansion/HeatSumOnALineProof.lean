import YangMills.Construction.ResponseInTheExpansion.HeatSumOnALine
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFourier
private lemma circleMomentum_eq_mul (N : ℕ) (n : ℤ) : circleMomentum N n = (2 * Real.pi / N) * n := by
  unfold circleMomentum
  ring
private lemma summable_abs_pow_mul_exp_momentum (N : ℕ) (hN : N ≠ 0) (t : ℝ) (ht : 0 < t) (k : ℕ) :
    Summable (fun n : ℤ => |circleMomentum N n| ^ k * Real.exp (-(t * circleMomentum N n ^ 2))) := by
  set h : ℝ := 2 * Real.pi / N with hh
  have hh0 : 0 < h := by positivity
  have hT : 0 < t * h ^ 2 / Real.pi := by positivity
  have := (summable_pow_mul_jacobiTheta₂_term_bound 0 hT k).mul_left (h ^ k)
  refine this.congr fun n => ?_
  rw [circleMomentum_eq_mul, ← hh, abs_mul, abs_of_pos hh0]
  have e1 : -Real.pi * (t * h ^ 2 / Real.pi * (n : ℝ) ^ 2 - 2 * 0 * ((|n| : ℤ) : ℝ)) =
      -(t * (h * n) ^ 2) := by
    field_simp
    ring
  rw [e1, Int.cast_abs, mul_pow h |(n : ℝ)| k, mul_assoc]
private lemma norm_thetaTerm_eq (N : ℕ) (t x : ℝ) (k : ℕ) (n : ℤ) :
    ‖thetaTerm N t x k n‖ = |circleMomentum N n| ^ k * Real.exp (-(t * circleMomentum N n ^ 2)) := by
  unfold thetaTerm
  rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
private lemma summable_thetaTerm (N : ℕ) (hN : N ≠ 0) (t : ℝ) (ht : 0 < t) (x : ℝ) (k : ℕ) :
    Summable (thetaTerm N t x k) :=
  Summable.of_norm ((summable_abs_pow_mul_exp_momentum N hN t ht k).congr fun n => (norm_thetaTerm_eq N t x k n).symm)
private lemma hasDerivAt_thetaTerm (N : ℕ) (t : ℝ) (k : ℕ) (n : ℤ) (x : ℝ) :
    HasDerivAt (fun x => thetaTerm N t x k n) (Complex.I * thetaTerm N t x (k + 1) n) x := by
  set p := circleMomentum N n with hp
  have h1 : HasDerivAt (fun x : ℝ => ((p * x : ℝ) : ℂ)) (p : ℂ) x := by
    have := ((hasDerivAt_id x).const_mul p).ofReal_comp
    simpa using this
  have h2 := (h1.const_mul Complex.I).cexp
  have h3 := h2.const_mul (((p ^ k * Real.exp (-(t * p ^ 2)) : ℝ)) : ℂ)
  unfold thetaTerm
  rw [← hp]
  refine h3.congr_deriv ?_
  push_cast
  ring
private lemma hasDerivAt_tsum_thetaTerm (N : ℕ) (hN : N ≠ 0) (t : ℝ) (ht : 0 < t) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x => ∑' n, thetaTerm N t x k n) (Complex.I * ∑' n, thetaTerm N t x (k + 1) n) x := by
  have := hasDerivAt_tsum (𝕜 := ℝ) (F := ℂ)
    (u := fun n : ℤ => |circleMomentum N n| ^ (k + 1) * Real.exp (-(t * circleMomentum N n ^ 2)))
    (g := fun (n : ℤ) (x : ℝ) => thetaTerm N t x k n)
    (g' := fun (n : ℤ) (y : ℝ) => Complex.I * thetaTerm N t y (k + 1) n) (y₀ := x)
    (summable_abs_pow_mul_exp_momentum N hN t ht (k + 1)) (fun n y => hasDerivAt_thetaTerm N t k n y)
    (fun n y => by rw [norm_mul, Complex.norm_I, one_mul, norm_thetaTerm_eq])
    (summable_thetaTerm N hN t ht x k) x
  rwa [tsum_mul_left] at this
private lemma hasDerivAt_exp_neg_sq_div (t : ℝ) (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / (4 * t))))
      (-(y / (2 * t)) * Real.exp (-(y ^ 2 / (4 * t)))) y := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / (4 * t))) (-(y / (2 * t))) y := by
    have := (((hasDerivAt_id y).pow 2).div_const (4 * t)).neg
    refine this.congr_deriv ?_
    simp
    field_simp
    ring
  have := h1.exp
  refine this.congr_deriv ?_
  ring
private lemma hasDerivAt_gaussianProfile (t : ℝ) (ht : 0 < t) (k : ℕ) (hk : k ≤ 1) (y : ℝ) :
    HasDerivAt (gaussianProfile t k) (gaussianProfile t (k + 1) y) y := by
  have h0 := hasDerivAt_exp_neg_sq_div t ht y
  interval_cases k
  · exact h0
  · have h1 : HasDerivAt (fun y : ℝ => -(y / (2 * t))) (-(1 / (2 * t))) y := ((hasDerivAt_id y).div_const (2 * t)).neg
    have := h1.mul h0
    refine this.congr_deriv ?_
    simp only [gaussianProfile]
    field_simp
    ring
private lemma one_add_mul_exp_neg_le (w : ℝ) (hw : 0 ≤ w) :
    (1 + w) * Real.exp (-(w / 4)) ≤ 8 * Real.exp (-(w / 8)) := by
  have h1 : w / 8 + 1 ≤ Real.exp (w / 8) := Real.add_one_le_exp _
  have h2 : Real.exp (-(w / 4)) = Real.exp (-(w / 8)) * Real.exp (-(w / 8)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (w / 8) * Real.exp (-(w / 8)) = 1 := by
    rw [← Real.exp_add]
    simp
  have h4 : 0 < Real.exp (-(w / 8)) := Real.exp_pos _
  rw [h2, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ h4.le
  have h5 : (1 + w) ≤ 8 * Real.exp (w / 8) := by linarith
  calc (1 + w) * Real.exp (-(w / 8)) ≤ 8 * Real.exp (w / 8) * Real.exp (-(w / 8)) :=
        mul_le_mul_of_nonneg_right h5 h4.le
    _ = 8 := by rw [mul_assoc, h3, mul_one]
private lemma abs_gaussianProfile_le (t : ℝ) (ht : 0 < t) (k : ℕ) (hk : k ≤ 2) (y : ℝ) :
    |gaussianProfile t k y| ≤ 8 * (Real.sqrt t)⁻¹ ^ k * Real.exp (-(y ^ 2 / (8 * t))) := by
  set τ := Real.sqrt t with hτ
  have hτ0 : 0 < τ := Real.sqrt_pos.2 ht
  have hτ2 : τ ^ 2 = t := Real.sq_sqrt ht.le
  set w := y ^ 2 / t with hw
  have hw0 : 0 ≤ w := by positivity
  have e4 : y ^ 2 / (4 * t) = w / 4 := by rw [hw]; field_simp
  have e8 : y ^ 2 / (8 * t) = w / 8 := by rw [hw]; field_simp
  have hb := one_add_mul_exp_neg_le w hw0
  have hE : 0 < Real.exp (-(w / 4)) := Real.exp_pos _
  have key : ∀ c : ℝ, |c| ≤ τ⁻¹ ^ k * (1 + w) →
      |c * Real.exp (-(w / 4))| ≤ 8 * τ⁻¹ ^ k * Real.exp (-(w / 8)) := by
    intro c hc
    rw [abs_mul, abs_of_pos hE]
    have hk0 : 0 ≤ τ⁻¹ ^ k := by positivity
    calc |c| * Real.exp (-(w / 4)) ≤ τ⁻¹ ^ k * (1 + w) * Real.exp (-(w / 4)) :=
          mul_le_mul_of_nonneg_right hc hE.le
      _ = τ⁻¹ ^ k * ((1 + w) * Real.exp (-(w / 4))) := by ring
      _ ≤ τ⁻¹ ^ k * (8 * Real.exp (-(w / 8))) := mul_le_mul_of_nonneg_left hb hk0
      _ = _ := by ring
  rw [e8]
  interval_cases k
  · have := key 1 (by simp; linarith)
    simpa [gaussianProfile, e4] using this
  · have := key (-(y / (2 * t))) (by
      rw [abs_neg, abs_div, abs_of_pos (show 0 < 2 * t by positivity), pow_one]
      set v := |y| * τ⁻¹ with hv
      have hv2 : w = v ^ 2 := by
        rw [hw, hv, mul_pow, sq_abs, ← hτ2]
        field_simp
      have e : |y| / (2 * t) = τ⁻¹ * (v / 2) := by
        rw [hv, ← hτ2]
        field_simp
      rw [e, hv2]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith [sq_nonneg (v - 1)])
    simpa [gaussianProfile, e4] using this
  · have := key (y ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) (by
      have e : y ^ 2 / (4 * t ^ 2) - 1 / (2 * t) = τ⁻¹ ^ 2 * (w / 4 - 1 / 2) := by
        rw [hw, ← hτ2]
        field_simp
      rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ τ⁻¹ ^ 2)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [abs_le]
      constructor <;> linarith)
    simpa [gaussianProfile, e4] using this
private lemma exp_neg_sq_sub_le (t : ℝ) (ht : 0 < t) (y m : ℝ) :
    Real.exp (-((y - m) ^ 2 / (8 * t))) ≤ Real.exp (y ^ 2 / (8 * t)) * Real.exp (-(m ^ 2 / (16 * t))) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : y ^ 2 / (8 * t) + -(m ^ 2 / (16 * t)) + (y - m) ^ 2 / (8 * t) = 2 * (y - m / 2) ^ 2 / (8 * t) := by
    field_simp
    ring
  have h2 : 0 ≤ 2 * (y - m / 2) ^ 2 / (8 * t) := by positivity
  linarith
private lemma summable_exp_neg_sq_lattice (N : ℕ) (hN : N ≠ 0) (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-(((N : ℝ) * n) ^ 2 / (16 * t)))) := by
  have hT : 0 < (N : ℝ) ^ 2 / (16 * Real.pi * t) := by positivity
  refine (summable_pow_mul_jacobiTheta₂_term_bound 0 hT 0).congr fun n => ?_
  simp only [pow_zero, one_mul]
  congr 1
  field_simp
  ring
private lemma summable_gaussianProfile_translate (N : ℕ) (hN : N ≠ 0) (t : ℝ) (ht : 0 < t) (k : ℕ) (hk : k ≤ 2) (x : ℝ) :
    Summable (fun n : ℤ => gaussianProfile t k (x - N * n)) := by
  refine Summable.of_norm_bounded
    (g := fun n : ℤ => 8 * (Real.sqrt t)⁻¹ ^ k * (Real.exp (x ^ 2 / (8 * t)) *
      Real.exp (-(((N : ℝ) * n) ^ 2 / (16 * t)))))
    (((summable_exp_neg_sq_lattice N hN t ht).mul_left _).mul_left _) fun n => ?_
  rw [Real.norm_eq_abs]
  refine (abs_gaussianProfile_le t ht k hk _).trans ?_
  exact mul_le_mul_of_nonneg_left (exp_neg_sq_sub_le t ht x _) (by positivity)
private lemma hasDerivAt_periodized_gaussianProfile (N : ℕ) (hN : N ≠ 0) (t : ℝ) (ht : 0 < t) (k : ℕ) (hk : k ≤ 1) (x : ℝ) :
    HasDerivAt (fun x => ∑' n : ℤ, gaussianProfile t k (x - N * n))
      (∑' n : ℤ, gaussianProfile t (k + 1) (x - N * n)) x := by
  set R := |x| + 1 with hR
  have hxR : x ∈ Metric.ball (0 : ℝ) R := by
    simp [hR]
  refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
    (u := fun n : ℤ => 8 * (Real.sqrt t)⁻¹ ^ (k + 1) * (Real.exp (R ^ 2 / (8 * t)) *
      Real.exp (-(((N : ℝ) * n) ^ 2 / (16 * t)))))
    (g := fun (n : ℤ) (x : ℝ) => gaussianProfile t k (x - N * n))
    (g' := fun (n : ℤ) (y : ℝ) => gaussianProfile t (k + 1) (y - N * n))
    (t := Metric.ball (0 : ℝ) R) (y₀ := x) (y := x)
    (((summable_exp_neg_sq_lattice N hN t ht).mul_left _).mul_left _) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected ?_ ?_ hxR (summable_gaussianProfile_translate N hN t ht k (by omega) x) hxR
  · intro n y _
    have := hasDerivAt_gaussianProfile t ht k hk (y - N * n)
    exact this.comp_sub_const y _
  · intro n y hy
    rw [Real.norm_eq_abs]
    refine (abs_gaussianProfile_le t ht (k + 1) (by omega) _).trans ?_
    refine mul_le_mul_of_nonneg_left ((exp_neg_sq_sub_le t ht y _).trans ?_) (by positivity)
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    have hy' : |y| < R := by simpa using hy
    have : y ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs y]
      exact pow_le_pow_left₀ (abs_nonneg _) hy'.le 2
    gcongr
private lemma hasSum_geometric_int_punctured (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) :
    HasSum (fun n : ℤ => if n = 0 then (0 : ℝ) else q ^ n.natAbs) (q / (1 - q) + q / (1 - q)) := by
  have hg : HasSum (fun n : ℕ => q ^ (n + 1)) (q / (1 - q)) := by
    have := (hasSum_geometric_of_lt_one h0 h1).mul_left q
    simpa [pow_succ', div_eq_mul_inv] using this
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · have : HasSum (fun n : ℕ => if ((n : ℤ)) = 0 then (0 : ℝ) else q ^ ((n : ℤ)).natAbs)
        (q / (1 - q)) := by
      have e : ∀ n : ℕ, (if ((n : ℤ) + 1) = 0 then (0 : ℝ) else q ^ ((n : ℤ) + 1).natAbs) =
          q ^ (n + 1) := by
        intro n
        rw [if_neg (by omega)]
        congr 1
      rw [← hasSum_nat_add_iff' 1]
      simpa [e] using hg
    exact this
  · have e : ∀ n : ℕ, (if (-((n : ℤ) + 1)) = 0 then (0 : ℝ) else q ^ (-((n : ℤ) + 1)).natAbs) =
        q ^ (n + 1) := by
      intro n
      rw [if_neg (by omega)]
      congr 1
    simp only [e]
    exact hg
private lemma abs_periodized_sub_gaussianProfile_le (N : ℕ) (t x : ℝ) (hN : 8 ≤ N) (ht : 1 ≤ t) (htN : t ≤ (N : ℝ) ^ 2)
    (hx : |x| ≤ (N : ℝ) / 8) (k : ℕ) (hk : k ≤ 2) :
    |∑' n : ℤ, gaussianProfile t k (x - N * n) - gaussianProfile t k x| ≤
      192 * (Real.sqrt t)⁻¹ ^ k * Real.exp (-((N : ℝ) ^ 2 / (11 * t))) := by
  have ht0 : 0 < t := by linarith
  have hN0 : N ≠ 0 := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set q := Real.exp (-((N : ℝ) ^ 2 / (11 * t))) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hwq : 1 ≤ (N : ℝ) ^ 2 / t := by
    rw [le_div_iff₀ ht0]
    linarith
  have hq1 : q ≤ 11 / 12 := by
    have h1 : (1 / 11 : ℝ) ≤ (N : ℝ) ^ 2 / (11 * t) := by
      have : (N : ℝ) ^ 2 / (11 * t) = ((N : ℝ) ^ 2 / t) / 11 := by
        field_simp
      rw [this]
      linarith
    have h2 : q ≤ Real.exp (-(1 / 11)) := Real.exp_le_exp.2 (by linarith)
    have h3 : (1 / 11 : ℝ) + 1 ≤ Real.exp (1 / 11) := Real.add_one_le_exp _
    have h4 : Real.exp (-(1 / 11)) ≤ 11 / 12 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      norm_num
      linarith
    linarith
  set c := 8 * (Real.sqrt t)⁻¹ ^ k with hc
  have hc0 : 0 ≤ c := by positivity
  have hS := summable_gaussianProfile_translate N hN0 t ht0 k hk x
  have e1 := hS.tsum_eq_add_tsum_ite (0 : ℤ)
  have e0 : gaussianProfile t k (x - N * ((0 : ℤ) : ℝ)) = gaussianProfile t k x := by simp
  rw [e1, e0, add_sub_cancel_left]
  have hb : ∀ n : ℤ, ‖(if n = 0 then (0 : ℝ) else gaussianProfile t k (x - N * n))‖ ≤
      c * (if n = 0 then (0 : ℝ) else q ^ n.natAbs) := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn, if_neg hn, Real.norm_eq_abs]
      refine (abs_gaussianProfile_le t ht0 k hk _).trans (mul_le_mul_of_nonneg_left ?_ hc0)
      have ha : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have hqn : q ^ n.natAbs = Real.exp (((n.natAbs : ℕ) : ℝ) * (-((N : ℝ) ^ 2 / (11 * t)))) := by
        rw [hq, ← Real.exp_nat_mul]
      rw [hqn]
      refine Real.exp_le_exp.2 ?_
      have hnat : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [hnat]
      set a := |(n : ℝ)| with ha'
      have hy : (7 / 8) * N * a ≤ |x - N * n| := by
        have h1 : |(N : ℝ) * n| - |x| ≤ |x - N * n| := by
          have := abs_sub_abs_le_abs_sub ((N : ℝ) * n) x
          rwa [abs_sub_comm] at this
        rw [abs_mul, abs_of_pos hN'] at h1
        nlinarith
      have hy2 : ((7 / 8) * N * a) ^ 2 ≤ (x - N * n) ^ 2 := by
        rw [← sq_abs (x - N * n)]
        exact pow_le_pow_left₀ (by positivity) hy 2
      have h5 : a * ((N : ℝ) ^ 2 / (11 * t)) ≤ (x - N * n) ^ 2 / (8 * t) := by
        have e5 : a * ((N : ℝ) ^ 2 / (11 * t)) = (8 * a * (N : ℝ) ^ 2 / 11) / (8 * t) := by
          field_simp
        rw [e5]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have h6 : 0 ≤ (49 / 64 * a ^ 2 - 8 / 11 * a) * (N : ℝ) ^ 2 :=
          mul_nonneg (by nlinarith) (sq_nonneg _)
        nlinarith
      linarith
  have hsum := tsum_of_norm_bounded ((hasSum_geometric_int_punctured q hq0.le (by linarith)).mul_left c) hb
  rw [← Real.norm_eq_abs]
  refine hsum.trans ?_
  have h7 : q / (1 - q) ≤ 12 * q := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  calc c * (q / (1 - q) + q / (1 - q)) ≤ c * (12 * q + 12 * q) := by gcongr
    _ = _ := by rw [hc]; ring
private lemma tsum_thetaTerm_zero_eq (N : ℕ) (hN : N ≠ 0) (t : ℝ) (ht : 0 < t) (x : ℝ) :
    ∑' n, thetaTerm N t x 0 n = ((N / Real.sqrt (4 * Real.pi * t) : ℝ) : ℂ) *
      ((∑' n : ℤ, gaussianProfile t 0 (x - N * n) : ℝ) : ℂ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hpi := Real.pi_pos
  have hpic : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  set A : ℝ := 4 * Real.pi * t / (N : ℝ) ^ 2 with hA
  have hA0 : 0 < A := by positivity
  have hre : 0 < ((A : ℝ) : ℂ).re := by simpa using hA0
  have key := Complex.tsum_exp_neg_quadratic hre (Complex.I * x / N)
  have e1 : ∀ n : ℤ, thetaTerm N t x 0 n = Complex.exp (-Real.pi * (A : ℂ) * (n : ℂ) ^ 2 +
      2 * Real.pi * (Complex.I * x / N) * n) := by
    intro n
    unfold thetaTerm circleMomentum
    simp only [pow_zero, one_mul]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [hA]
    push_cast
    field_simp
    ring
  have eI : Complex.I * (Complex.I * (x : ℂ) / N) = -(x : ℂ) / N := by
    rw [← mul_div_assoc, ← mul_assoc, Complex.I_mul_I]
    ring
  have e2 : ∀ n : ℤ, Complex.exp (-Real.pi / (A : ℂ) * ((n : ℂ) + Complex.I * (Complex.I * x / N)) ^ 2) =
      ((gaussianProfile t 0 (x - N * n) : ℝ) : ℂ) := by
    intro n
    simp only [gaussianProfile]
    rw [Complex.ofReal_exp, eI]
    congr 1
    rw [hA]
    push_cast
    field_simp
    ring
  have e3 : ((A : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt A : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hA0.le]
    norm_num
  have e4 : Real.sqrt A = Real.sqrt (4 * Real.pi * t) / N := by
    rw [hA, Real.sqrt_div (by positivity), Real.sqrt_sq hN'.le]
  rw [tsum_congr e1, key, tsum_congr e2, Complex.ofReal_tsum, e3, e4]
  congr 1
  push_cast
  simp [one_div, inv_div]
theorem poissonSummationHeat : poissonSummationHeatStatement := by
  refine ⟨192, fun N t x hN ht htN hx k hk => ?_⟩
  have ht0 : 0 < t := by linarith
  have hN0 : N ≠ 0 := by omega
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hpi := Real.pi_pos
  set S := Real.sqrt (4 * Real.pi * t) with hS
  have hS0 : 0 < S := Real.sqrt_pos.2 (by positivity)
  have hSc : (S : ℂ) ≠ 0 := by exact_mod_cast hS0.ne'
  set κ : ℂ := ((N / S : ℝ) : ℂ) with hκ
  let L : ℕ → ℝ → ℂ := fun k x => ∑' n, thetaTerm N t x k n
  let G : ℕ → ℝ → ℝ := fun k x => ∑' n : ℤ, gaussianProfile t k (x - N * n)
  have hL0 : ∀ x, L 0 x = κ * ((G 0 x : ℝ) : ℂ) := fun x => tsum_thetaTerm_zero_eq N hN0 t ht0 x
  have d1 : ∀ x, Complex.I * L 1 x = κ * ((G 1 x : ℝ) : ℂ) := by
    intro x
    have a := hasDerivAt_tsum_thetaTerm N hN0 t ht0 0 x
    have b := ((hasDerivAt_periodized_gaussianProfile N hN0 t ht0 0 (by omega) x).ofReal_comp).const_mul κ
    have hfun : (fun x => ∑' n, thetaTerm N t x 0 n) = fun x => κ * ((G 0 x : ℝ) : ℂ) := funext hL0
    rw [hfun] at a
    exact a.unique b
  have hL1 : ∀ x, L 1 x = -Complex.I * κ * ((G 1 x : ℝ) : ℂ) := by
    intro x
    have := d1 x
    calc L 1 x = -Complex.I * (Complex.I * L 1 x) := by
          rw [← mul_assoc]
          simp
      _ = _ := by rw [this, mul_assoc]
  have d2 : ∀ x, Complex.I * L 2 x = -Complex.I * κ * ((G 2 x : ℝ) : ℂ) := by
    intro x
    have a := hasDerivAt_tsum_thetaTerm N hN0 t ht0 1 x
    have b := ((hasDerivAt_periodized_gaussianProfile N hN0 t ht0 1 le_rfl x).ofReal_comp).const_mul (-Complex.I * κ)
    have hfun : (fun x => ∑' n, thetaTerm N t x 1 n) =
        fun x => -Complex.I * κ * ((G 1 x : ℝ) : ℂ) := funext hL1
    rw [hfun] at a
    exact a.unique b
  have hL2 : ∀ x, L 2 x = -κ * ((G 2 x : ℝ) : ℂ) := by
    intro x
    have := d2 x
    calc L 2 x = -Complex.I * (Complex.I * L 2 x) := by
          rw [← mul_assoc]
          simp
      _ = _ := by
          rw [this, ← mul_assoc, ← mul_assoc]
          simp
  have hcast : (N : ℂ)⁻¹ * κ = ((S⁻¹ : ℝ) : ℂ) := by
    rw [hκ]
    push_cast
    field_simp
  have hmain : (N : ℂ)⁻¹ * L k x = (-Complex.I) ^ k * ((S⁻¹ * G k x : ℝ) : ℂ) := by
    interval_cases k
    · rw [hL0, ← mul_assoc, hcast]
      push_cast
      ring
    · rw [hL1]
      have : (N : ℂ)⁻¹ * (-Complex.I * κ * ((G 1 x : ℝ) : ℂ)) =
          -Complex.I * (((N : ℂ)⁻¹ * κ) * ((G 1 x : ℝ) : ℂ)) := by ring
      rw [this, hcast]
      push_cast
      ring
    · rw [hL2]
      have : (N : ℂ)⁻¹ * (-κ * ((G 2 x : ℝ) : ℂ)) = -(((N : ℂ)⁻¹ * κ) * ((G 2 x : ℝ) : ℂ)) := by ring
      rw [this, hcast]
      push_cast
      have hII : (-Complex.I) ^ 2 = -1 := by
        rw [neg_sq, Complex.I_sq]
      rw [hII]
      ring
  have hnI : ‖(-Complex.I) ^ k‖ = 1 := by simp
  have hτ0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hSτ : S⁻¹ ≤ (Real.sqrt t)⁻¹ := by
    refine inv_anti₀ hτ0 (Real.sqrt_le_sqrt ?_)
    have : (1 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith
  refine ⟨summable_thetaTerm N hN0 t ht0 x k, ?_, ?_⟩
  · show ‖(N : ℂ)⁻¹ * L k x - heatKernelDeriv t x k‖ ≤ _
    rw [hmain]
    unfold heatKernelDeriv
    rw [← mul_sub, norm_mul, hnI, one_mul, ← Complex.ofReal_sub, Complex.norm_real, ← mul_sub,
      norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hS0)]
    have hT := abs_periodized_sub_gaussianProfile_le N t x hN ht htN hx k hk
    calc S⁻¹ * |G k x - gaussianProfile t k x|
        ≤ (Real.sqrt t)⁻¹ * (192 * (Real.sqrt t)⁻¹ ^ k * Real.exp (-((N : ℝ) ^ 2 / (11 * t)))) :=
          mul_le_mul hSτ hT (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · unfold heatKernelDeriv
    rw [norm_mul, hnI, one_mul, Complex.norm_real, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hS0)]
    have hB := abs_gaussianProfile_le t ht0 k hk x
    have hE : Real.exp (-(x ^ 2 / (8 * t))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ x ^ 2 / (8 * t) := by positivity
      linarith
    have hp0 : 0 ≤ (Real.sqrt t)⁻¹ ^ k := by positivity
    have hB2 : |gaussianProfile t k x| ≤ 192 * (Real.sqrt t)⁻¹ ^ k := by
      refine hB.trans ?_
      nlinarith
    calc S⁻¹ * |gaussianProfile t k x| ≤ (Real.sqrt t)⁻¹ * (192 * (Real.sqrt t)⁻¹ ^ k) :=
          mul_le_mul hSτ hB2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
end YangMills.Construction.LatticeFourier
