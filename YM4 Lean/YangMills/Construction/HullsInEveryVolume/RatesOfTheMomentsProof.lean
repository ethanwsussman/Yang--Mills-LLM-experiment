import YangMills.Construction.HullsInEveryVolume.MeansOfTheLocalHull
import YangMills.Construction.HullsInEveryVolume.RatesOfTheMoments
import YangMills.Construction.LawByMomentsOfTheFlow.HullsClearOfThePointInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open RenormalizationStepParameters TorusLumps HullMeans HullsInEveryVolume
section FactorialBounds
private theorem factorial_add_le_two_pow (a b : ℕ) :
    (a + b).factorial ≤ 2 ^ (a + b) * (a.factorial * b.factorial) := by
  have hc := Nat.add_choose_mul_factorial_mul_factorial a b
  rw [← hc, mul_assoc]
  exact Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
private theorem factorial_four_mul_succ_le (k : ℕ) (hk : 1 ≤ k) :
    ((4 * k + 1).factorial : ℝ) ≤ (1280 : ℝ) ^ k * (k.factorial : ℝ) ^ 4 := by
  have h5 : 4 * k + 1 ≤ 5 ^ k := by
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      rw [pow_succ]
      omega
  have h2 : (2 * k).factorial ≤ 2 ^ (2 * k) * (k.factorial * k.factorial) := by
    have := factorial_add_le_two_pow k k
    rwa [← two_mul] at this
  have h4 : (4 * k).factorial ≤ 2 ^ (4 * k) * ((2 * k).factorial * (2 * k).factorial) := by
    have := factorial_add_le_two_pow (2 * k) (2 * k)
    rwa [show 2 * k + 2 * k = 4 * k by ring] at this
  have hN : (4 * k + 1).factorial ≤ 1280 ^ k * k.factorial ^ 4 := by
    calc (4 * k + 1).factorial = (4 * k + 1) * (4 * k).factorial := Nat.factorial_succ _
      _ ≤ 5 ^ k * (2 ^ (4 * k) * ((2 ^ (2 * k) * (k.factorial * k.factorial)) *
            (2 ^ (2 * k) * (k.factorial * k.factorial)))) :=
          Nat.mul_le_mul h5 (h4.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 h2)))
      _ = 1280 ^ k * k.factorial ^ 4 := by
          rw [show (1280 : ℕ) = 5 * 2 ^ 8 by norm_num, mul_pow, ← pow_mul]
          ring
  exact_mod_cast hN
private theorem pow_mul_exp_neg_le {b t : ℝ} (hb : 0 < b) (ht : 0 < t) (m : ℕ) :
    t ^ m * Real.exp (-(b * t)) ≤ ((m + 1).factorial : ℝ) * (b ^ (m + 1))⁻¹ * t⁻¹ := by
  have h := Real.pow_div_factorial_le_exp (b * t) (by positivity) (m + 1)
  have hf : (0 : ℝ) < ((m + 1).factorial : ℝ) := by positivity
  rw [div_le_iff₀ hf] at h
  have e1 : t ^ m = (b * t) ^ (m + 1) * (b ^ (m + 1))⁻¹ * t⁻¹ := by
    rw [mul_pow, pow_succ t]
    field_simp
  rw [e1, Real.exp_neg]
  calc (b * t) ^ (m + 1) * (b ^ (m + 1))⁻¹ * t⁻¹ * (Real.exp (b * t))⁻¹
      = (b * t) ^ (m + 1) * (Real.exp (b * t))⁻¹ * ((b ^ (m + 1))⁻¹ * t⁻¹) := by ring
    _ ≤ (Real.exp (b * t) * ((m + 1).factorial : ℝ)) * (Real.exp (b * t))⁻¹ * ((b ^ (m + 1))⁻¹ * t⁻¹) := by
        gcongr
    _ = ((m + 1).factorial : ℝ) * (b ^ (m + 1))⁻¹ * t⁻¹ := by
        field_simp
private theorem dyadic_band_sum_le (c E Lr : ℝ) (hc : 0 < c) (hE : 0 ≤ E) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x r : ℝ) (k N : ℕ), 1 ≤ x → 1 ≤ r → r ≤ 2 * x → 1 ≤ k →
      ∑ i ∈ Finset.range N, (16 * (k : ℝ) * (4 * 56 ^ 4 * Lr ^ 4 * r ^ 4 * ((2 : ℝ) ^ i) ^ 4)) ^ k *
          Real.exp (E * Real.log x) * Real.exp (-(3 / 8 * (c * x)) - c * x / 8 * 2 ^ i) ≤
        C ^ k * (k.factorial : ℝ) ^ 6 * Real.exp (-(c * x / 4)) := by
  set E₁ : ℝ := E + 1 with hE₁
  have hE₁0 : 0 < E₁ := by positivity
  set a : ℝ := c / (8 * E₁) with ha
  have ha0 : 0 < a := by positivity
  set M : ℝ := Real.exp (E₁ * (-1 - Real.log a)) with hM
  have hM0 : 0 < M := Real.exp_pos _
  set A : ℝ := 4 * 56 ^ 4 * Lr ^ 4 with hA
  have hA0 : 0 ≤ A := by positivity
  set Q : ℝ := max 1 (M * (16 / c)) with hQ
  have hQ1 : 1 ≤ Q := le_max_left _ _
  set W : ℝ := 16 * A * Real.exp 1 * (16 / c) ^ 4 * 1280 with hW
  have hW0 : 0 ≤ W := by positivity
  have hQM : M * (16 / c) ≤ Q := le_max_right _ _
  have hWk : ∀ k : ℕ, W ^ k = (16 * A) ^ k * Real.exp 1 ^ k * (1280 : ℝ) ^ k * (16 / c) ^ (4 * k) := by
    intro k
    clear_value A
    rw [hW, show 16 * A * Real.exp 1 * (16 / c) ^ 4 * 1280 = (16 * A) * Real.exp 1 * 1280 * (16 / c) ^ 4 by ring,
      mul_pow, mul_pow, mul_pow, ← pow_mul, mul_comm 4 k]
  clear_value E₁ a M A Q W
  refine ⟨max 1 (Q * W), le_max_left _ _, fun x r k N hx hr hrx hk => ?_⟩
  have hx0 : 0 < x := by linarith
  set b : ℝ := c * x / 8 with hb
  have hb0 : 0 < b := by positivity
  clear_value b
  set G : ℝ := (16 * A) ^ k * (k : ℝ) ^ k * r ^ (4 * k) * Real.exp (E * Real.log x) *
    Real.exp (-(3 / 8 * (c * x))) * (((4 * k + 1).factorial : ℝ) * (b ^ (4 * k + 1))⁻¹) with hG
  have hG0 : 0 ≤ G := by positivity
  clear_value G
  have hterm : ∀ i ∈ Finset.range N, (16 * (k : ℝ) * (A * r ^ 4 * ((2 : ℝ) ^ i) ^ 4)) ^ k *
      Real.exp (E * Real.log x) * Real.exp (-(3 / 8 * (c * x)) - b * 2 ^ i) ≤ G * (1 / 2) ^ i := by
    intro i _
    have ht : (0 : ℝ) < 2 ^ i := by positivity
    have h1 := pow_mul_exp_neg_le hb0 ht (4 * k)
    have e1 : (16 * (k : ℝ) * (A * r ^ 4 * ((2 : ℝ) ^ i) ^ 4)) ^ k =
        (16 * A) ^ k * (k : ℝ) ^ k * r ^ (4 * k) * ((2 : ℝ) ^ i) ^ (4 * k) := by
      rw [show 16 * (k : ℝ) * (A * r ^ 4 * ((2 : ℝ) ^ i) ^ 4) =
        (16 * A) * (k : ℝ) * r ^ 4 * ((2 : ℝ) ^ i) ^ 4 by ring, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    have e2 : Real.exp (-(3 / 8 * (c * x)) - b * 2 ^ i) =
        Real.exp (-(3 / 8 * (c * x))) * Real.exp (-(b * 2 ^ i)) := by
      rw [← Real.exp_add]
      ring_nf
    have e3 : ((1 : ℝ) / 2) ^ i = ((2 : ℝ) ^ i)⁻¹ := by
      rw [one_div, inv_pow]
    rw [e1, e2, e3, hG]
    calc (16 * A) ^ k * (k : ℝ) ^ k * r ^ (4 * k) * ((2 : ℝ) ^ i) ^ (4 * k) * Real.exp (E * Real.log x) *
          (Real.exp (-(3 / 8 * (c * x))) * Real.exp (-(b * 2 ^ i)))
        = (16 * A) ^ k * (k : ℝ) ^ k * r ^ (4 * k) * Real.exp (E * Real.log x) *
            Real.exp (-(3 / 8 * (c * x))) * (((2 : ℝ) ^ i) ^ (4 * k) * Real.exp (-(b * 2 ^ i))) := by ring
      _ ≤ (16 * A) ^ k * (k : ℝ) ^ k * r ^ (4 * k) * Real.exp (E * Real.log x) *
            Real.exp (-(3 / 8 * (c * x))) * (((4 * k + 1).factorial : ℝ) * (b ^ (4 * k + 1))⁻¹ * ((2 : ℝ) ^ i)⁻¹) := by
          gcongr
      _ = _ := by ring
  have hsum : ∑ i ∈ Finset.range N, (16 * (k : ℝ) * (A * r ^ 4 * ((2 : ℝ) ^ i) ^ 4)) ^ k *
      Real.exp (E * Real.log x) * Real.exp (-(3 / 8 * (c * x)) - b * 2 ^ i) ≤ G * 2 := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_geometric_two_le N) hG0
  refine hsum.trans ?_
  have hlog : E₁ * Real.log x ≤ c * x / 8 + E₁ * (-1 - Real.log a) := by
    have h1 := Real.log_le_sub_one_of_pos (mul_pos ha0 hx0)
    rw [Real.log_mul ha0.ne' hx0.ne'] at h1
    have h2 : E₁ * (a * x) = c * x / 8 := by
      rw [ha]
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 hE₁0.le]
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hx1 : Real.exp (E * Real.log x) * Real.exp (-(3 / 8 * (c * x))) ≤ M * Real.exp (-(c * x / 4)) := by
    rw [← Real.exp_add, hM, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : E * Real.log x ≤ E₁ * Real.log x := by
      rw [hE₁]
      nlinarith
    nlinarith
  have hkk : (k : ℝ) ^ k ≤ Real.exp 1 ^ k * (k.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (k : ℝ) (by positivity) k
    have hf : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    rw [div_le_iff₀ hf, ← Real.exp_one_pow] at h
    exact h
  have h4 := factorial_four_mul_succ_le k hk
  have hbinv : b⁻¹ ≤ 8 / c := by
    rw [hb, inv_div]
    apply div_le_div_of_nonneg_left (by norm_num) hc
    nlinarith
  have hrb : r * b⁻¹ ≤ 16 / c := by
    have : r * b⁻¹ = 8 * r / (c * x) := by
      rw [hb]
      field_simp
    rw [this, div_le_div_iff₀ (by positivity) hc]
    nlinarith
  have hpow : r ^ (4 * k) * (b ^ (4 * k + 1))⁻¹ ≤ (16 / c) ^ (4 * k) * (8 / c) := by
    have e : r ^ (4 * k) * (b ^ (4 * k + 1))⁻¹ = (r * b⁻¹) ^ (4 * k) * b⁻¹ := by
      rw [mul_pow, pow_succ, mul_inv, inv_pow]
      ring
    rw [e]
    gcongr
  have hfin : G * 2 ≤ (M * (16 / c)) * W ^ k * (k.factorial : ℝ) ^ 5 * Real.exp (-(c * x / 4)) := by
    have e1 : G * 2 = 2 * (16 * A) ^ k * (k : ℝ) ^ k * ((4 * k + 1).factorial : ℝ) *
        (Real.exp (E * Real.log x) * Real.exp (-(3 / 8 * (c * x)))) *
        (r ^ (4 * k) * (b ^ (4 * k + 1))⁻¹) := by
      rw [hG]
      ring
    rw [e1]
    calc 2 * (16 * A) ^ k * (k : ℝ) ^ k * ((4 * k + 1).factorial : ℝ) *
          (Real.exp (E * Real.log x) * Real.exp (-(3 / 8 * (c * x)))) * (r ^ (4 * k) * (b ^ (4 * k + 1))⁻¹)
        ≤ 2 * (16 * A) ^ k * (Real.exp 1 ^ k * (k.factorial : ℝ)) * ((1280 : ℝ) ^ k * (k.factorial : ℝ) ^ 4) *
          (M * Real.exp (-(c * x / 4))) * ((16 / c) ^ (4 * k) * (8 / c)) := by
          gcongr
      _ = (M * (16 / c)) * W ^ k * (k.factorial : ℝ) ^ 5 * Real.exp (-(c * x / 4)) := by
          rw [hWk k]
          ring
  refine hfin.trans ?_
  have hk1 : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hQW : Q * W ^ k ≤ (max 1 (Q * W)) ^ k := by
    have h1 : Q ≤ Q ^ k := le_self_pow₀ hQ1 (by omega)
    calc Q * W ^ k ≤ Q ^ k * W ^ k := by gcongr
      _ = (Q * W) ^ k := (mul_pow _ _ _).symm
      _ ≤ _ := by
        gcongr
        exact le_max_right _ _
  have hf5 : (k.factorial : ℝ) ^ 5 ≤ (k.factorial : ℝ) ^ 6 := pow_le_pow_right₀ hk1 (by norm_num)
  calc (M * (16 / c)) * W ^ k * (k.factorial : ℝ) ^ 5 * Real.exp (-(c * x / 4))
      ≤ Q * W ^ k * (k.factorial : ℝ) ^ 6 * Real.exp (-(c * x / 4)) := by
        gcongr
    _ ≤ _ := by gcongr
abbrev _root_.YangMills.SharedProofs.p100659 := @dyadic_band_sum_le
end FactorialBounds
private theorem hullDecayRate_pos (Tb : ParameterAssignment) (hD : Tb.Admissible) : 0 < hullDecayRate Tb := by apply _root_.YangMills.SharedProofs.p22298 <;> assumption
private theorem band_term_le {k p : ℕ} (hp : 2 ≤ p) {E lx Λ t : ℝ} (hE : 0 ≤ E) (hlx : 0 ≤ lx) (hq : Λ ≤ p) (ht : 0 ≤ t) :
    (16 ^ (k * p) * ((k * p).factorial : ℝ) * Real.exp (E * lx * Λ)) ^ (1 / (p : ℝ)) *
        (Real.exp (-t)) ^ (1 - 1 / (p : ℝ)) ≤ (16 * (k : ℝ) * p) ^ k * Real.exp (E * lx) * Real.exp (-(t / 2)) := by
  set A₁ : ℝ := (16 * (k : ℝ) * p) ^ k * Real.exp (E * lx) with hA₁
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hmom : 16 ^ (k * p) * ((k * p).factorial : ℝ) * Real.exp (E * lx * Λ) ≤ A₁ ^ p := by
    have hf : ((k * p).factorial : ℝ) ≤ ((k : ℝ) * p) ^ (k * p) := by
      have := Nat.factorial_le_pow (k * p)
      exact_mod_cast this
    have he : Real.exp (E * lx * Λ) ≤ Real.exp (E * lx) ^ p := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have : E * lx * Λ ≤ E * lx * p := mul_le_mul_of_nonneg_left hq (mul_nonneg hE hlx)
      linarith
    calc (16 : ℝ) ^ (k * p) * ((k * p).factorial : ℝ) * Real.exp (E * lx * Λ)
        ≤ (16 : ℝ) ^ (k * p) * ((k : ℝ) * p) ^ (k * p) * Real.exp (E * lx) ^ p := by gcongr
      _ = A₁ ^ p := by
        rw [hA₁, mul_pow _ (Real.exp (E * lx)) p, ← pow_mul, mul_assoc (16 : ℝ) (k : ℝ) (p : ℝ),
          mul_pow (16 : ℝ) ((k : ℝ) * p) (k * p)]
  have hbase : 0 ≤ 16 ^ (k * p) * ((k * p).factorial : ℝ) * Real.exp (E * lx * Λ) := by positivity
  have hfirst : (16 ^ (k * p) * ((k * p).factorial : ℝ) * Real.exp (E * lx * Λ)) ^ (1 / (p : ℝ)) ≤ A₁ := by
    calc _ ≤ (A₁ ^ p) ^ (1 / (p : ℝ)) := Real.rpow_le_rpow hbase hmom (by positivity)
      _ = A₁ := by
        rw [one_div]
        exact Real.pow_rpow_inv_natCast hA₁0 (by omega)
  have hhalf : (1 : ℝ) / 2 ≤ 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      exact_mod_cast hp
    linarith
  have hsecond : (Real.exp (-t)) ^ (1 - 1 / (p : ℝ)) ≤ Real.exp (-(t / 2)) := by
    rw [← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul hfirst hsecond (Real.rpow_nonneg (Real.exp_pos _).le _) hA₁0
theorem bandMomentSumStatement_holds : bandMomentSumStatement := by
  intro CE hCE
  refine EventuallyInParameters.mono_of_imp ?_ (fun a _ => ⟨0, fun _ => 1, 0, fun _ => one_pos, fun _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨0, fun _ _ _ _ _ _ => ⟨0, fun _ _ _ _ => trivial⟩⟩⟩ : EventuallyInParameters fun _ _ _ => True)
  rintro Tb Kr y hodd hDr hy hAdm hRet hExp _ g
  have hfit : (Tb.stepParameters y).Admissible := hDr.fits y hy
  have hc : 0 < hullDecayRate Tb := hullDecayRate_pos Tb hDr
  have hL1 : (1 : ℝ) ≤ (Tb.side : ℝ) := by
    have h2 : 1 ≤ Tb.side := le_trans (by norm_num) hDr.L_ge
    exact_mod_cast h2
  obtain ⟨C, hC1, hCs⟩ := dyadic_band_sum_le (hullDecayRate Tb) (CE Tb) (Tb.side : ℝ) hc (hCE Tb)
  refine ⟨C, hC1, fun β K m T u n _ hlev => ?_⟩
  have hchain := hlev.chain
  have hxy : y ≤ stageCoupling T u := by
    have e : stageCoupling T u = (couplingFlow (Tb.stepParameters y) β u).1 := hchain.follows u (by have := hlev.le; omega)
    rw [e]
    exact y₁_le_couplingFlow_of_le_crossing hRet hExp (by show 0 ≤ Tb.B; linarith [hDr.B_ge]) hchain.le_inv_sq hchain.upper_le hchain.isFirst u hlev.le
  have hx : 1 ≤ stageCoupling T u := hfit.y₁_ge.trans hxy
  have hpos : 0 < stageCoupling T u ^ ((1 : ℝ) / 100) := Real.rpow_pos_of_pos (by linarith) _
  have hpow : stageCoupling T u ^ ((1 : ℝ) / 100) ≤ stageCoupling T u := by
    calc stageCoupling T u ^ ((1 : ℝ) / 100) ≤ stageCoupling T u ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = stageCoupling T u := Real.rpow_one _
  have hr : (1 : ℝ) ≤ (stageRange T u : ℝ) := by
    have : 1 ≤ stageRange T u := Nat.ceil_pos.mpr hpos
    exact_mod_cast this
  have hrx : (stageRange T u : ℝ) ≤ 2 * stageCoupling T u := by
    have h1 : (stageRange T u : ℝ) < stageCoupling T u ^ ((1 : ℝ) / 100) + 1 := Nat.ceil_lt_add_one hpos.le
    linarith
  have hlx : 0 ≤ Real.log (stageCoupling T u) := Real.log_nonneg hx
  obtain ⟨r, hrd⟩ : ∃ r : ℝ, r = (stageRange T u : ℝ) := ⟨_, rfl⟩
  rw [← hrd] at hr hrx
  have hΛ : ∀ i : ℕ, 1 ≤ ((Tb.side : ℝ) * (16 * (2 ^ i * r) + 40 * r)) ^ 4 := fun i => by
    have h2i : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    have hin : 1 ≤ 16 * (2 ^ i * r) + 40 * r := by nlinarith
    exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le hL1 hin)
  have hbp : ∀ i, (holderExponentAtBand Tb.side (stageRange T u) i : ℝ) = ⌈((Tb.side : ℝ) * (16 * (2 ^ i * r) + 40 * r)) ^ 4⌉₊ := fun i => by
    rw [hrd]
    rfl
  have hp2 : ∀ i, 2 ≤ holderExponentAtBand Tb.side (stageRange T u) i := by
    intro i
    have h2i : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    have h1 : (2 : ℝ) ≤ ((Tb.side : ℝ) * (16 * (2 ^ i * r) + 40 * r)) ^ 4 := by
      have hin : 2 ≤ 16 * (2 ^ i * r) + 40 * r := by nlinarith
      have h3 : 2 ≤ (Tb.side : ℝ) * (16 * (2 ^ i * r) + 40 * r) := by nlinarith
      calc (2 : ℝ) ≤ 2 ^ 4 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) h3 4
    have h4 := Nat.le_ceil (((Tb.side : ℝ) * (16 * (2 ^ i * r) + 40 * r)) ^ 4)
    have h5 : (2 : ℝ) ≤ (holderExponentAtBand Tb.side (stageRange T u) i : ℝ) := by
      rw [hbp]
      linarith
    exact_mod_cast h5
  refine ⟨hp2, fun k I q hk hq => ?_⟩
  have hterm : ∀ i ∈ Finset.range I,
      (16 ^ (k * holderExponentAtBand Tb.side (stageRange T u) i) * ((k * holderExponentAtBand Tb.side (stageRange T u) i).factorial : ℝ) *
          Real.exp (CE Tb * Real.log (stageCoupling T u) * q i)) ^ (1 / (holderExponentAtBand Tb.side (stageRange T u) i : ℝ)) *
        (Real.exp (-(hullDecayRate Tb * stageCoupling T u * (1 + dyadicDiameterFloor (stageRange T u) i / (stageRange T u : ℝ))))) ^
          (1 - 1 / (holderExponentAtBand Tb.side (stageRange T u) i : ℝ)) ≤
      (16 * (k : ℝ) * (4 * 56 ^ 4 * (Tb.side : ℝ) ^ 4 * r ^ 4 * ((2 : ℝ) ^ i) ^ 4)) ^ k *
        Real.exp (CE Tb * Real.log (stageCoupling T u)) *
        Real.exp (-(3 / 8 * (hullDecayRate Tb * stageCoupling T u)) - hullDecayRate Tb * stageCoupling T u / 8 * 2 ^ i) := by
    intro i _
    have h2i : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    have hfl0 : 0 ≤ dyadicDiameterFloor (stageRange T u) i / (stageRange T u : ℝ) := by
      refine div_nonneg ?_ (by positivity)
      unfold dyadicDiameterFloor
      split_ifs
      · exact le_rfl
      · positivity
    have hcx : 0 < hullDecayRate Tb * stageCoupling T u := mul_pos hc (by linarith)
    have ht : 0 ≤ hullDecayRate Tb * stageCoupling T u * (1 + dyadicDiameterFloor (stageRange T u) i / (stageRange T u : ℝ)) := by positivity
    have hqp : q i ≤ (holderExponentAtBand Tb.side (stageRange T u) i : ℝ) := by
      rw [hbp]
      refine (hq i).trans ?_
      rw [← hrd]
      exact Nat.le_ceil _
    have h1 := band_term_le (k := k) (hp2 i) (hCE Tb) hlx hqp ht
    refine h1.trans ?_
    have hpA : (holderExponentAtBand Tb.side (stageRange T u) i : ℝ) ≤ 4 * 56 ^ 4 * (Tb.side : ℝ) ^ 4 * r ^ 4 * ((2 : ℝ) ^ i) ^ 4 := by
      rw [hbp]
      have h0 : 0 ≤ ((Tb.side : ℝ) * (16 * (2 ^ i * r) + 40 * r)) ^ 4 := by positivity
      have h2 := Nat.ceil_lt_add_one h0
      have h3 : ((Tb.side : ℝ) * (16 * (2 ^ i * r) + 40 * r)) ^ 4 ≤ ((Tb.side : ℝ) * (56 * 2 ^ i * r)) ^ 4 := by
        have : 16 * (2 ^ i * r) + 40 * r ≤ 56 * 2 ^ i * r := by nlinarith
        gcongr
      have h4 : ((Tb.side : ℝ) * (56 * 2 ^ i * r)) ^ 4 = 56 ^ 4 * (Tb.side : ℝ) ^ 4 * r ^ 4 * ((2 : ℝ) ^ i) ^ 4 := by ring
      rw [h4] at h3
      have h5 := hΛ i
      nlinarith
    have hex : -(hullDecayRate Tb * stageCoupling T u * (1 + dyadicDiameterFloor (stageRange T u) i / (stageRange T u : ℝ)) / 2) ≤
        -(3 / 8 * (hullDecayRate Tb * stageCoupling T u)) - hullDecayRate Tb * stageCoupling T u / 8 * 2 ^ i := by
      cases i with
      | zero =>
        simp only [dyadicDiameterFloor, if_true, zero_div, add_zero, pow_zero]
        linarith
      | succ j =>
        have hrne : (stageRange T u : ℝ) ≠ 0 := by
          rw [← hrd]
          linarith
        have e : dyadicDiameterFloor (stageRange T u) (j + 1) / (stageRange T u : ℝ) = 2 ^ j := by
          simp only [dyadicDiameterFloor, Nat.add_sub_cancel]
          rw [if_neg (by omega)]
          field_simp
        rw [e, pow_succ]
        have h2 : (0 : ℝ) < 2 ^ j := by positivity
        nlinarith [mul_pos hcx h2]
    have hk0 : 0 ≤ 16 * (k : ℝ) * (holderExponentAtBand Tb.side (stageRange T u) i : ℝ) := by positivity
    have hpow' : (16 * (k : ℝ) * (holderExponentAtBand Tb.side (stageRange T u) i : ℝ)) ^ k ≤
        (16 * (k : ℝ) * (4 * 56 ^ 4 * (Tb.side : ℝ) ^ 4 * r ^ 4 * ((2 : ℝ) ^ i) ^ 4)) ^ k :=
      pow_le_pow_left₀ hk0 (mul_le_mul_of_nonneg_left hpA (by positivity)) k
    have hexp := Real.exp_le_exp.2 hex
    calc _ ≤ (16 * (k : ℝ) * (4 * 56 ^ 4 * (Tb.side : ℝ) ^ 4 * r ^ 4 * ((2 : ℝ) ^ i) ^ 4)) ^ k *
          Real.exp (CE Tb * Real.log (stageCoupling T u)) *
          Real.exp (-(hullDecayRate Tb * stageCoupling T u * (1 + dyadicDiameterFloor (stageRange T u) i / (stageRange T u : ℝ)) / 2)) := by gcongr
      _ ≤ _ := by gcongr
  exact (Finset.sum_le_sum hterm).trans (hCs (stageCoupling T u) r k I hx hr hrx hk)
end YangMills.Construction.HullTrees
end
