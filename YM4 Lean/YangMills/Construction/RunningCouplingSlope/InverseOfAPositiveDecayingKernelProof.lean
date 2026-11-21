import YangMills.Construction.RunningCouplingSlope.InverseOfAPositiveDecayingKernel
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.DecayingKernels
open Matrix
section PowerBounds
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem dotProduct_mulVec_symm (A : Matrix ι ι ℝ) (hA : A.IsSymm) (u v : ι → ℝ) :
    u ⬝ᵥ (A *ᵥ v) = (A *ᵥ u) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq]
private theorem quadForm_contract_sq (A : Matrix ι ι ℝ) (hA : A.IsSymm) (q : ℝ) (hq : 0 < q)
    (hnn : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v))
    (hle : ∀ v : ι → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ q * (v ⬝ᵥ v)) (v : ι → ℝ) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ q ^ 2 * (v ⬝ᵥ v) := by
  obtain ⟨w, hw⟩ : ∃ w, w = A *ᵥ v := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = A *ᵥ w := ⟨_, rfl⟩
  have hvu : v ⬝ᵥ u = w ⬝ᵥ w := by
    rw [hu, dotProduct_mulVec_symm A hA v w, ← hw]
  have i1 : w ⬝ᵥ u ≤ q * (w ⬝ᵥ w) := by
    rw [hu]
    exact hle w
  have i2 := hnn (q • v - w)
  have e : (q • v - w) ⬝ᵥ (A *ᵥ (q • v - w)) =
      q ^ 2 * (v ⬝ᵥ w) - 2 * q * (w ⬝ᵥ w) + w ⬝ᵥ u := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ← hw, ← hu]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hvu]
    ring
  rw [e] at i2
  have hb : v ⬝ᵥ w ≤ q * (v ⬝ᵥ v) := by
    rw [hw]
    exact hle v
  have h3 : q * (w ⬝ᵥ w) ≤ q * (q * (v ⬝ᵥ w)) := by nlinarith
  have h4 : w ⬝ᵥ w ≤ q * (v ⬝ᵥ w) := le_of_mul_le_mul_left h3 hq
  rw [← hw]
  calc w ⬝ᵥ w ≤ q * (v ⬝ᵥ w) := h4
    _ ≤ q * (q * (v ⬝ᵥ v)) := mul_le_mul_of_nonneg_left hb hq.le
    _ = q ^ 2 * (v ⬝ᵥ v) := by ring
private theorem pow_quadForm_contract_sq (A : Matrix ι ι ℝ) (hA : A.IsSymm) (q : ℝ) (hq : 0 < q)
    (hnn : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v))
    (hle : ∀ v : ι → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ q * (v ⬝ᵥ v)) (k : ℕ) (v : ι → ℝ) :
    ((A ^ k) *ᵥ v) ⬝ᵥ ((A ^ k) *ᵥ v) ≤ (q ^ k) ^ 2 * (v ⬝ᵥ v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' A, ← Matrix.mulVec_mulVec]
    calc (A *ᵥ ((A ^ k) *ᵥ v)) ⬝ᵥ (A *ᵥ ((A ^ k) *ᵥ v))
        ≤ q ^ 2 * (((A ^ k) *ᵥ v) ⬝ᵥ ((A ^ k) *ᵥ v)) := quadForm_contract_sq A hA q hq hnn hle _
      _ ≤ q ^ 2 * ((q ^ k) ^ 2 * (v ⬝ᵥ v)) := mul_le_mul_of_nonneg_left ih (sq_nonneg q)
      _ = (q ^ (k + 1)) ^ 2 * (v ⬝ᵥ v) := by ring
private theorem abs_pow_entry_le (A : Matrix ι ι ℝ) (hA : A.IsSymm) (q : ℝ) (hq : 0 < q)
    (hnn : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v))
    (hle : ∀ v : ι → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ q * (v ⬝ᵥ v)) (k : ℕ) (x y : ι) :
    |(A ^ k) x y| ≤ q ^ k := by
  have h := pow_quadForm_contract_sq A hA q hq hnn hle k (Pi.single y 1)
  have hone : (Pi.single y (1 : ℝ) : ι → ℝ) ⬝ᵥ Pi.single y 1 = 1 := by simp
  rw [hone, mul_one] at h
  have hcol : ((A ^ k) *ᵥ (Pi.single y (1 : ℝ) : ι → ℝ)) x = (A ^ k) x y := by simp
  have h2 : ((A ^ k) x y) ^ 2 ≤
      ((A ^ k) *ᵥ (Pi.single y (1 : ℝ) : ι → ℝ)) ⬝ᵥ ((A ^ k) *ᵥ Pi.single y 1) := by
    rw [← hcol, sq]
    exact Finset.single_le_sum
      (f := fun i => ((A ^ k) *ᵥ (Pi.single y (1 : ℝ) : ι → ℝ)) i *
        ((A ^ k) *ᵥ (Pi.single y (1 : ℝ) : ι → ℝ)) i)
      (fun i _ => mul_self_nonneg _) (Finset.mem_univ x)
  have h3 := sq_le_sq.mp (h2.trans h)
  rwa [abs_of_nonneg (pow_nonneg hq.le k)] at h3
private theorem weighted_row_sum_one (w : ι → ι → ℝ) (hw1 : ∀ x, w x x = 1) (x : ι) :
    ∑ y, |(1 : Matrix ι ι ℝ) x y| * w x y = 1 := by
  rw [Finset.sum_eq_single x]
  · simp [hw1]
  · intro y _ hy
    simp [Matrix.one_apply_ne (Ne.symm hy)]
  · simp
private theorem weighted_row_sum_pow_le (w : ι → ι → ℝ) (hw0 : ∀ x y, 0 ≤ w x y)
    (hw1 : ∀ x, w x x = 1)
    (hw : ∀ x y z, w x z ≤ w x y * w y z) (A : Matrix ι ι ℝ) (s : ℝ) (hs : 0 ≤ s)
    (hA : ∀ x, ∑ y, |A x y| * w x y ≤ s) (k : ℕ) (x : ι) :
    ∑ y, |(A ^ k) x y| * w x y ≤ s ^ k := by
  induction k generalizing x with
  | zero =>
    simp only [pow_zero]
    exact (weighted_row_sum_one w hw1 x).le
  | succ k ih =>
    calc ∑ y, |(A ^ (k + 1)) x y| * w x y
        ≤ ∑ y, ∑ z, (|A x z| * w x z) * (|(A ^ k) z y| * w z y) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [pow_succ' A, Matrix.mul_apply]
          calc |∑ z, A x z * (A ^ k) z y| * w x y
              ≤ (∑ z, |A x z * (A ^ k) z y|) * w x y :=
                mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (hw0 _ _)
            _ = ∑ z, |A x z * (A ^ k) z y| * w x y := Finset.sum_mul _ _ _
            _ ≤ ∑ z, (|A x z| * w x z) * (|(A ^ k) z y| * w z y) := by
              refine Finset.sum_le_sum fun z _ => ?_
              rw [abs_mul]
              calc |A x z| * |(A ^ k) z y| * w x y
                  ≤ |A x z| * |(A ^ k) z y| * (w x z * w z y) :=
                    mul_le_mul_of_nonneg_left (hw x z y)
                      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
                _ = (|A x z| * w x z) * (|(A ^ k) z y| * w z y) := by ring
      _ = ∑ z, (|A x z| * w x z) * ∑ y, |(A ^ k) z y| * w z y := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ ≤ ∑ z, (|A x z| * w x z) * s ^ k :=
          Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_left (ih z) (mul_nonneg (abs_nonneg _) (hw0 _ _))
      _ = (∑ z, |A x z| * w x z) * s ^ k := (Finset.sum_mul _ _ _).symm
      _ ≤ s * s ^ k := mul_le_mul_of_nonneg_right (hA x) (pow_nonneg hs k)
      _ = s ^ (k + 1) := by rw [pow_succ']
private theorem schur_quadForm_le (T : Matrix ι ι ℝ) (E : ι → ι → ℝ) (c : ℝ)
    (hE : ∀ x y, E x y = E y x) (hT : ∀ x y, |T x y| ≤ E x y) (hrow : ∀ x, ∑ y, E x y ≤ c)
    (v : ι → ℝ) : ∑ x, ∑ y, T x y * v x * v y ≤ c * ∑ x, v x ^ 2 := by
  have h1 : ∀ x y, T x y * v x * v y ≤ E x y * (v x ^ 2 / 2) + E y x * (v y ^ 2 / 2) := by
    intro x y
    have hE0 : 0 ≤ E x y := (abs_nonneg _).trans (hT x y)
    have h2 : |v x * v y| ≤ (v x ^ 2 + v y ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|v x| - |v y|), sq_abs (v x), sq_abs (v y)]
    have h3 : T x y * (v x * v y) ≤ |T x y| * |v x * v y| := by
      rw [← abs_mul]
      exact le_abs_self _
    rw [hE y x]
    calc T x y * v x * v y = T x y * (v x * v y) := by ring
      _ ≤ |T x y| * |v x * v y| := h3
      _ ≤ E x y * ((v x ^ 2 + v y ^ 2) / 2) :=
          mul_le_mul (hT x y) h2 (abs_nonneg _) hE0
      _ = E x y * (v x ^ 2 / 2) + E x y * (v y ^ 2 / 2) := by ring
  calc ∑ x, ∑ y, T x y * v x * v y
      ≤ ∑ x, ∑ y, (E x y * (v x ^ 2 / 2) + E y x * (v y ^ 2 / 2)) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => h1 x y
    _ = ∑ x, ∑ y, E x y * (v x ^ 2 / 2) + ∑ x, ∑ y, E y x * (v y ^ 2 / 2) := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ x, ∑ y, E x y * (v x ^ 2 / 2) := by
        rw [Finset.sum_comm (f := fun x y => E y x * (v y ^ 2 / 2))]
        ring
    _ = ∑ x, (∑ y, E x y) * v x ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
    _ ≤ ∑ x, c * v x ^ 2 :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hrow x) (sq_nonneg _)
    _ = c * ∑ x, v x ^ 2 := (Finset.mul_sum _ _ _).symm
private theorem dotProduct_mulVec_eq_double_sum (T : Matrix ι ι ℝ) (v : ι → ℝ) :
    v ⬝ᵥ (T *ᵥ v) = ∑ x, ∑ y, T x y * v x * v y := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
private theorem dotProduct_self_eq_sum_sq (v : ι → ℝ) : v ⬝ᵥ v = ∑ x, v x ^ 2 := by
  simp only [dotProduct, sq]
private theorem neumann_series_inverse (T A : Matrix ι ι ℝ) (τ q : ℝ) (hTA : τ⁻¹ • T = 1 - A)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hb : ∀ (k : ℕ) (x y : ι), |(A ^ k) x y| ≤ q ^ k) :
    ∃ G : Matrix ι ι ℝ, G * T = 1 ∧ T * G = 1 ∧
      ∀ x y, HasSum (fun k : ℕ => τ⁻¹ * (A ^ k) x y) (G x y) := by
  have hsum : ∀ x y, Summable fun k : ℕ => τ⁻¹ * (A ^ k) x y := by
    intro x y
    refine Summable.mul_left _ ?_
    refine Summable.of_norm_bounded (g := fun k : ℕ => q ^ k)
      (summable_geometric_of_lt_one hq0 hq1) fun k => ?_
    simpa using hb k x y
  obtain ⟨G, hG⟩ : ∃ G : Matrix ι ι ℝ, G = fun x y => ∑' k : ℕ, τ⁻¹ * (A ^ k) x y := ⟨_, rfl⟩
  have hH : ∀ x y, HasSum (fun k : ℕ => τ⁻¹ * (A ^ k) x y) (G x y) := by
    intro x y
    rw [hG]
    exact (hsum x y).hasSum
  have hGT : G * T = 1 := by
    ext x y
    have hs : HasSum (fun k : ℕ => ∑ z, τ⁻¹ * (A ^ k) x z * T z y) ((G * T) x y) := by
      rw [Matrix.mul_apply]
      exact hasSum_sum fun z _ => (hH x z).mul_right (T z y)
    have hterm : ∀ k : ℕ, ∑ z, τ⁻¹ * (A ^ k) x z * T z y = (A ^ k) x y - (A ^ (k + 1)) x y := by
      intro k
      have h1 : A ^ k * (τ⁻¹ • T) = A ^ k - A ^ (k + 1) := by
        rw [hTA, mul_sub, mul_one, pow_succ]
      have h2 := congrFun (congrFun h1 x) y
      rw [Matrix.mul_apply] at h2
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply] at h2
      rw [← h2]
      exact Finset.sum_congr rfl fun z _ => by ring
    have ht := hs.tendsto_sum_nat
    simp only [hterm] at ht
    simp only [Finset.sum_range_sub' (fun k : ℕ => (A ^ k) x y)] at ht
    have hz : Filter.Tendsto (fun n : ℕ => (A ^ n) x y) Filter.atTop (nhds 0) :=
      squeeze_zero_norm (fun n => by simpa using hb n x y)
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
    have hl : Filter.Tendsto (fun n : ℕ => (A ^ 0) x y - (A ^ n) x y) Filter.atTop
        (nhds ((A ^ 0) x y - 0)) := tendsto_const_nhds.sub hz
    have := tendsto_nhds_unique ht hl
    simpa using this
  exact ⟨G, hGT, mul_eq_one_comm.mp hGT, hH⟩
private theorem le_exp_convex_comb (E u v s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (h1 : E ≤ Real.exp u)
    (h2 : E ≤ Real.exp v) : E ≤ Real.exp ((1 - s) * u + s * v) := by
  rcases le_total u v with h | h
  · exact h1.trans (Real.exp_le_exp.2 (by nlinarith))
  · exact h2.trans (Real.exp_le_exp.2 (by nlinarith))
private theorem geometric_decay_of_two_bounds (E q s₁ D : ℝ) (k : ℕ) (hq : 0 < q) (hq1 : q < 1)
    (hs : 1 < s₁)
    (h1 : E ≤ q ^ k) (h2 : E * Real.exp D ≤ s₁ ^ k) :
    E ≤ Real.exp (Real.log q / 2) ^ k *
      Real.exp (-(Real.log q / (2 * (Real.log q - Real.log s₁)) * D)) := by
  have ha : Real.log q < 0 := Real.log_neg hq hq1
  have hb : 0 < Real.log s₁ := Real.log_pos hs
  have hden : Real.log q - Real.log s₁ < 0 := by linarith
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.log q / (2 * (Real.log q - Real.log s₁)) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by
    rw [hsdef]
    exact (div_pos_of_neg_of_neg ha (by linarith)).le
  have hs1 : s ≤ 1 := by
    rw [hsdef, div_le_one_of_neg (by linarith)]
    linarith
  have hsm : s * (Real.log q - Real.log s₁) = Real.log q / 2 := by
    have hne : Real.log q - Real.log s₁ ≠ 0 := hden.ne
    rw [hsdef]
    field_simp
  have u1 : E ≤ Real.exp (k * Real.log q) := by
    rw [Real.exp_nat_mul, Real.exp_log hq]
    exact h1
  have u2 : E ≤ Real.exp (k * Real.log s₁ - D) := by
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by linarith), le_div_iff₀ (Real.exp_pos _)]
    exact h2
  have h := le_exp_convex_comb E _ _ s hs0 hs1 u1 u2
  rw [← hsdef, ← Real.exp_nat_mul, ← Real.exp_add]
  convert h using 2
  have : (k : ℝ) * (Real.log q / 2) = k * Real.log q - k * (s * (Real.log q - Real.log s₁)) := by
    rw [hsm]
    ring
  rw [this]
  ring
end PowerBounds
theorem decayingInverseBound_holds : DecayingInverseBound := by
  intro M θ κ S hM hθ hκ hS
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = M * S + κ := ⟨_, rfl⟩
  have hτ : 0 < τ := by rw [hτdef]; positivity
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  obtain ⟨q, hqdef⟩ : ∃ q, q = τ⁻¹ * (M * S) := ⟨_, rfl⟩
  have hsplit : q + τ⁻¹ * κ = 1 := by
    rw [hqdef, ← mul_add, ← hτdef]
    exact inv_mul_cancel₀ hτ.ne'
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hτκ : 0 < τ⁻¹ * κ := by positivity
  have hq1 : q < 1 := by linarith
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, s₁ = 1 + q := ⟨_, rfl⟩
  have hs1 : 1 < s₁ := by linarith
  obtain ⟨r, hr⟩ : ∃ r, r = Real.exp (Real.log q / 2) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = Real.log q / (2 * (Real.log q - Real.log s₁)) := ⟨_, rfl⟩
  have hlq : Real.log q < 0 := Real.log_neg hq0 hq1
  have hls : 0 < Real.log s₁ := Real.log_pos hs1
  have hspos : 0 < s := by
    rw [hs]
    exact div_pos_of_neg_of_neg hlq (by linarith)
  have hr0 : 0 < r := by rw [hr]; exact Real.exp_pos _
  have hr1 : r < 1 := by
    have h := Real.exp_lt_exp.2 (show Real.log q / 2 < 0 by linarith)
    rwa [Real.exp_zero, ← hr] at h
  refine ⟨τ⁻¹ * (1 - r)⁻¹, s * (θ / 2), τ, q, ?_, by positivity, hτ, hq0.le, hq1, ?_⟩
  · have : 0 < 1 - r := by linarith
    positivity
  intro ι _ _ d T hd0 hdn hds hdt hrow hT hdec hfloor
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix ι ι ℝ, A = 1 - τ⁻¹ • T := ⟨_, rfl⟩
  have hAs : A.IsSymm := by
    rw [hAdef]
    exact Matrix.isSymm_one.sub (hT.smul _)
  have hTA : τ⁻¹ • T = 1 - A := by rw [hAdef]; abel
  have hform : ∀ v : ι → ℝ, v ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ v - τ⁻¹ * (v ⬝ᵥ (T *ᵥ v)) := by
    intro v
    rw [hAdef, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul]
  have hE : ∀ x y, |T x y| ≤ M * Real.exp (-(θ / 2 * d x y)) := by
    intro x y
    refine (hdec x y).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM.le)
    nlinarith [hdn x y]
  have hErow : ∀ x, ∑ y, M * Real.exp (-(θ / 2 * d x y)) ≤ M * S := by
    intro x
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hrow x) hM.le
  have hup : ∀ v : ι → ℝ, v ⬝ᵥ (T *ᵥ v) ≤ M * S * (v ⬝ᵥ v) := by
    intro v
    rw [dotProduct_mulVec_eq_double_sum, dotProduct_self_eq_sum_sq]
    exact schur_quadForm_le T _ _ (fun x y => by rw [hds x y]) hE hErow v
  have hlow : ∀ v : ι → ℝ, κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (T *ᵥ v) := by
    intro v
    rw [dotProduct_mulVec_eq_double_sum, dotProduct_self_eq_sum_sq]
    exact hfloor v
  have h0 : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
    intro v
    rw [hform]
    have hvv : 0 ≤ v ⬝ᵥ v := by
      rw [dotProduct_self_eq_sum_sq]
      exact Finset.sum_nonneg fun x _ => sq_nonneg _
    have h1 : τ⁻¹ * (v ⬝ᵥ (T *ᵥ v)) ≤ q * (v ⬝ᵥ v) := by
      rw [hqdef, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hup v) hτi.le
    nlinarith
  have h1 : ∀ v : ι → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ q * (v ⬝ᵥ v) := by
    intro v
    rw [hform]
    have h2 : τ⁻¹ * (κ * (v ⬝ᵥ v)) ≤ τ⁻¹ * (v ⬝ᵥ (T *ᵥ v)) :=
      mul_le_mul_of_nonneg_left (hlow v) hτi.le
    have h3 : q * (v ⬝ᵥ v) = v ⬝ᵥ v - τ⁻¹ * (κ * (v ⬝ᵥ v)) := by
      have : q = 1 - τ⁻¹ * κ := by linarith
      rw [this]
      ring
    rw [h3]
    linarith
  have hsmall := abs_pow_entry_le A hAs q hq0 h0 h1
  have hwt : ∀ (k : ℕ) (x : ι),
      ∑ y, |(A ^ k) x y| * Real.exp (θ / 2 * d x y) ≤ s₁ ^ k := by
    refine weighted_row_sum_pow_le (fun x y => Real.exp (θ / 2 * d x y))
      (fun _ _ => (Real.exp_pos _).le)
      (fun x => by simp [hd0 x]) (fun x y z => ?_) A s₁ (by linarith) (fun x => ?_)
    · rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith [hdt x y z]
    · have hterm : ∀ y, |A x y| * Real.exp (θ / 2 * d x y) ≤
          |(1 : Matrix ι ι ℝ) x y| * Real.exp (θ / 2 * d x y) +
            τ⁻¹ * (M * Real.exp (-(θ / 2 * d x y))) := by
        intro y
        have hAxy : |A x y| ≤ |(1 : Matrix ι ι ℝ) x y| + τ⁻¹ * |T x y| := by
          rw [hAdef, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_of_pos hτi]
        have hw : 0 ≤ Real.exp (θ / 2 * d x y) := (Real.exp_pos _).le
        have hmul : |T x y| * Real.exp (θ / 2 * d x y) ≤ M * Real.exp (-(θ / 2 * d x y)) := by
          calc |T x y| * Real.exp (θ / 2 * d x y)
              ≤ M * Real.exp (-(θ * d x y)) * Real.exp (θ / 2 * d x y) :=
                mul_le_mul_of_nonneg_right (hdec x y) hw
            _ = M * Real.exp (-(θ / 2 * d x y)) := by
                rw [mul_assoc, ← Real.exp_add]
                congr 2
                ring
        calc |A x y| * Real.exp (θ / 2 * d x y)
            ≤ (|(1 : Matrix ι ι ℝ) x y| + τ⁻¹ * |T x y|) * Real.exp (θ / 2 * d x y) :=
              mul_le_mul_of_nonneg_right hAxy hw
          _ = |(1 : Matrix ι ι ℝ) x y| * Real.exp (θ / 2 * d x y) +
                τ⁻¹ * (|T x y| * Real.exp (θ / 2 * d x y)) := by ring
          _ ≤ _ := by
              have := mul_le_mul_of_nonneg_left hmul hτi.le
              linarith
      calc ∑ y, |A x y| * Real.exp (θ / 2 * d x y)
          ≤ ∑ y, (|(1 : Matrix ι ι ℝ) x y| * Real.exp (θ / 2 * d x y) +
              τ⁻¹ * (M * Real.exp (-(θ / 2 * d x y)))) := Finset.sum_le_sum fun y _ => hterm y
        _ = 1 + τ⁻¹ * ∑ y, M * Real.exp (-(θ / 2 * d x y)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum,
              weighted_row_sum_one (fun x y => Real.exp (θ / 2 * d x y))
                (fun x => by simp [hd0 x]) x]
        _ ≤ 1 + τ⁻¹ * (M * S) := by
            have := mul_le_mul_of_nonneg_left (hErow x) hτi.le
            linarith
        _ = s₁ := by rw [hs₁, hqdef]
  have hdecay : ∀ (k : ℕ) (x y : ι),
      |(A ^ k) x y| ≤ r ^ k * Real.exp (-(s * (θ / 2) * d x y)) := by
    intro k x y
    have hone : |(A ^ k) x y| * Real.exp (θ / 2 * d x y) ≤ s₁ ^ k :=
      (Finset.single_le_sum (f := fun y => |(A ^ k) x y| * Real.exp (θ / 2 * d x y))
        (fun _ _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (Finset.mem_univ y)).trans
        (hwt k x)
    have := geometric_decay_of_two_bounds _ q s₁ _ k hq0 hq1 hs1 (hsmall k x y) hone
    rw [← hr, ← hs] at this
    rw [mul_assoc s]
    exact this
  obtain ⟨G, hGT, hTG, hH⟩ := neumann_series_inverse T A τ q hTA hq0.le hq1 hsmall
  have hAback : 1 - τ⁻¹ • T = A := hAdef.symm
  rw [hAback]
  refine ⟨G, hGT, hTG, fun x y => ?_, hsmall, hH⟩
  have hgeo : HasSum (fun k : ℕ => τ⁻¹ * (r ^ k * Real.exp (-(s * (θ / 2) * d x y))))
      (τ⁻¹ * ((1 - r)⁻¹ * Real.exp (-(s * (θ / 2) * d x y)))) :=
    ((hasSum_geometric_of_lt_one hr0.le hr1).mul_right _).mul_left _
  have hn := (hH x y).norm_le_of_bounded hgeo (fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hτi]
    exact mul_le_mul_of_nonneg_left (hdecay k x y) hτi.le)
  rw [Real.norm_eq_abs] at hn
  calc |G x y| ≤ τ⁻¹ * ((1 - r)⁻¹ * Real.exp (-(s * (θ / 2) * d x y))) := hn
    _ = τ⁻¹ * (1 - r)⁻¹ * Real.exp (-(s * (θ / 2) * d x y)) := by ring
end YangMills.Construction.DecayingKernels
end
