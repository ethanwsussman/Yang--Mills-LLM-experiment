import YangMills.Construction.ResponseInTheExpansion.HeatSumOnALattice
import YangMills.Construction.ResponseInTheExpansion.ProductOfSumsOverALattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFourier
private def derivOrder (a b i : Fin 4) : ℕ := (if i = a then 1 else 0) + (if i = b then 1 else 0)
private lemma derivOrder_le_two (a b i : Fin 4) : derivOrder a b i ≤ 2 := by
  unfold derivOrder
  split_ifs <;> omega
private lemma sum_derivOrder_succ (a b : Fin 4) : ∑ i, (derivOrder a b i + 1) = 6 := by
  fin_cases a <;> fin_cases b <;> simp [derivOrder, Fin.sum_univ_four]
private lemma prod_pow_derivOrder {R : Type} [CommMonoid R] (p : Fin 4 → R) (a b : Fin 4) :
    ∏ i, p i ^ derivOrder a b i = p a * p b := by
  have h : ∀ c : Fin 4, ∏ i, p i ^ (if i = c then 1 else 0) = p c := by
    intro c
    rw [Finset.prod_eq_single c]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  unfold derivOrder
  simp only [pow_add]
  rw [Finset.prod_mul_distrib, h, h]
private def hermiteCoeff (t : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  match k with
  | 0 => 1
  | 1 => -(y / (2 * t))
  | _ => y ^ 2 / (4 * t ^ 2) - 1 / (2 * t)
private lemma gaussianProfile_eq_coeff_mul_exp (t : ℝ) (k : ℕ) (y : ℝ) :
    gaussianProfile t k y = hermiteCoeff t k y * Real.exp (-(y ^ 2 / (4 * t))) := by
  match k with
  | 0 => simp [gaussianProfile, hermiteCoeff]
  | 1 => simp [gaussianProfile, hermiteCoeff]
  | (n + 2) => simp [gaussianProfile, hermiteCoeff]
private lemma prod_hermiteCoeff (t : ℝ) (z : Fin 4 → ℝ) (a b : Fin 4) :
    ∏ i, hermiteCoeff t (derivOrder a b i) (z i) =
      z a * z b / (4 * t ^ 2) - (if a = b then 1 / (2 * t) else 0) := by
  fin_cases a <;> fin_cases b <;> simp [derivOrder, Fin.prod_univ_four, hermiteCoeff] <;> ring
private lemma heatLatticeTerm_eq_prod (N : ℕ) (t : ℝ) (z : Fin 4 → ℝ) (a b : Fin 4) (k : Fin 4 → ℤ) :
    heatLatticeTerm N t z a b k = ∏ i, thetaTerm N t (z i) (derivOrder a b i) (k i) := by
  unfold heatLatticeTerm thetaTerm
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, Finset.prod_mul_distrib,
    prod_pow_derivOrder (fun i => circleMomentum N (k i)) a b, ← Real.exp_sum, ← Complex.exp_sum]
  congr 2
  · congr 2
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  · rw [← Finset.mul_sum]
    push_cast
    rfl
private lemma prod_heatKernelDeriv (t : ℝ) (ht : 0 < t) (z : Fin 4 → ℝ) (a b : Fin 4) :
    ∏ i, heatKernelDeriv t (z i) (derivOrder a b i) = (heatKernelHessian t z a b : ℂ) := by
  unfold heatKernelDeriv
  have hsqrt : (Real.sqrt (4 * Real.pi * t))⁻¹ ^ 4 = (16 * Real.pi ^ 2 * t ^ 2)⁻¹ := by
    rw [inv_pow]
    congr 1
    have : Real.sqrt (4 * Real.pi * t) ^ 2 = 4 * Real.pi * t := Real.sq_sqrt (by positivity)
    calc Real.sqrt (4 * Real.pi * t) ^ 4 = (Real.sqrt (4 * Real.pi * t) ^ 2) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  have hI : ∏ i, (-Complex.I) ^ derivOrder a b i = -1 := by
    rw [prod_pow_derivOrder (fun _ => -Complex.I) a b]
    simp
  have hexp : ∏ i, Real.exp (-(z i ^ 2 / (4 * t))) = Real.exp (-((∑ i, z i ^ 2) / (4 * t))) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib, Finset.sum_div]
  have hreal : ∏ i, ((Real.sqrt (4 * Real.pi * t))⁻¹ * gaussianProfile t (derivOrder a b i) (z i)) =
      -heatKernelHessian t z a b := by
    simp only [gaussianProfile_eq_coeff_mul_exp]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hsqrt, prod_hermiteCoeff, hexp]
    unfold heatKernelHessian
    field_simp
    ring
  rw [Finset.prod_mul_distrib, hI, ← Complex.ofReal_prod, hreal]
  push_cast
  ring
private lemma norm_prod_four_sub_le (u m : Fin 4 → ℂ) (w : Fin 4 → ℝ) (c q : ℝ) (hc : 0 ≤ c) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hw : ∀ i, 0 ≤ w i) (hd : ∀ i, ‖u i - m i‖ ≤ c * w i * q)
    (hm : ∀ i, ‖m i‖ ≤ c * w i) :
    ‖∏ i, u i - ∏ i, m i‖ ≤ 32 * c ^ 4 * (∏ i, w i) * q := by
  have hu : ∀ i, ‖u i‖ ≤ 2 * c * w i := by
    intro i
    have h1 : ‖u i‖ ≤ ‖u i - m i‖ + ‖m i‖ := by
      simpa using norm_add_le (u i - m i) (m i)
    have h2 : c * w i * q ≤ c * w i := by
      have : 0 ≤ c * w i := mul_nonneg hc (hw i)
      nlinarith
    have := hd i
    have := hm i
    linarith
  have hid : ∏ i, u i - ∏ i, m i = (u 0 - m 0) * u 1 * u 2 * u 3 + m 0 * (u 1 - m 1) * u 2 * u 3 +
      m 0 * m 1 * (u 2 - m 2) * u 3 + m 0 * m 1 * m 2 * (u 3 - m 3) := by
    simp only [Fin.prod_univ_four]
    ring
  have hw0 := hw 0
  have hw1 := hw 1
  have hw2 := hw 2
  have hw3 := hw 3
  have t1 : ‖(u 0 - m 0) * u 1 * u 2 * u 3‖ ≤ (c * w 0 * q) * (2 * c * w 1) * (2 * c * w 2) * (2 * c * w 3) := by
    simp only [norm_mul]
    gcongr
    · exact hd 0
    · exact hu 1
    · exact hu 2
    · exact hu 3
  have t2 : ‖m 0 * (u 1 - m 1) * u 2 * u 3‖ ≤ (c * w 0) * (c * w 1 * q) * (2 * c * w 2) * (2 * c * w 3) := by
    simp only [norm_mul]
    gcongr
    · exact hm 0
    · exact hd 1
    · exact hu 2
    · exact hu 3
  have t3 : ‖m 0 * m 1 * (u 2 - m 2) * u 3‖ ≤ (c * w 0) * (c * w 1) * (c * w 2 * q) * (2 * c * w 3) := by
    simp only [norm_mul]
    gcongr
    · exact hm 0
    · exact hm 1
    · exact hd 2
    · exact hu 3
  have t4 : ‖m 0 * m 1 * m 2 * (u 3 - m 3)‖ ≤ (c * w 0) * (c * w 1) * (c * w 2) * (c * w 3 * q) := by
    simp only [norm_mul]
    gcongr
    · exact hm 0
    · exact hm 1
    · exact hm 2
    · exact hd 3
  rw [hid, Fin.prod_univ_four]
  have hW : 0 ≤ c ^ 4 * (w 0 * w 1 * w 2 * w 3) * q := by positivity
  have n1 := norm_add_le ((u 0 - m 0) * u 1 * u 2 * u 3 + m 0 * (u 1 - m 1) * u 2 * u 3 +
      m 0 * m 1 * (u 2 - m 2) * u 3) (m 0 * m 1 * m 2 * (u 3 - m 3))
  have n2 := norm_add_le ((u 0 - m 0) * u 1 * u 2 * u 3 + m 0 * (u 1 - m 1) * u 2 * u 3)
      (m 0 * m 1 * (u 2 - m 2) * u 3)
  have n3 := norm_add_le ((u 0 - m 0) * u 1 * u 2 * u 3) (m 0 * (u 1 - m 1) * u 2 * u 3)
  have e1 : (c * w 0 * q) * (2 * c * w 1) * (2 * c * w 2) * (2 * c * w 3) =
      8 * (c ^ 4 * (w 0 * w 1 * w 2 * w 3) * q) := by ring
  have e2 : (c * w 0) * (c * w 1 * q) * (2 * c * w 2) * (2 * c * w 3) =
      4 * (c ^ 4 * (w 0 * w 1 * w 2 * w 3) * q) := by ring
  have e3 : (c * w 0) * (c * w 1) * (c * w 2 * q) * (2 * c * w 3) =
      2 * (c ^ 4 * (w 0 * w 1 * w 2 * w 3) * q) := by ring
  have e4 : (c * w 0) * (c * w 1) * (c * w 2) * (c * w 3 * q) =
      c ^ 4 * (w 0 * w 1 * w 2 * w 3) * q := by ring
  rw [e1] at t1
  rw [e2] at t2
  rw [e3] at t3
  rw [e4] at t4
  have e5 : 32 * c ^ 4 * (w 0 * w 1 * w 2 * w 3) * q =
      32 * (c ^ 4 * (w 0 * w 1 * w 2 * w 3) * q) := by ring
  rw [e5]
  linarith
theorem poissonSummationHeatLattice_of_line (hprod : tsum_pi_prod_statement)
    (hline : poissonSummationHeatStatement) : poissonSummationHeatLatticeStatement := by
  obtain ⟨C₀, hC₀⟩ := hline
  refine ⟨32 * |C₀| ^ 4, fun N t z a b hN ht htN hz => ?_⟩
  have ht0 : 0 < t := by linarith
  have hzi : ∀ i, |z i| ≤ (N : ℝ) / 8 := by
    intro i
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    exact (Finset.single_le_sum (f := fun j => z j ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)).trans hz
  have hl := fun i => hC₀ N t (z i) hN ht htN (hzi i) (derivOrder a b i) (derivOrder_le_two a b i)
  set f : Fin 4 → ℤ → ℂ := fun i => thetaTerm N t (z i) (derivOrder a b i) with hf
  have hn : ∀ i, Summable fun m => ‖f i m‖ := fun i => (hl i).1.norm
  obtain ⟨_, hH⟩ := hprod ℂ 4 f hn
  have hfun : heatLatticeTerm N t z a b = fun k => ∏ i, f i (k i) :=
    funext (heatLatticeTerm_eq_prod N t z a b)
  refine ⟨by rw [hfun]; exact hH.summable, ?_⟩
  rw [hfun, hH.tsum_eq, ← prod_heatKernelDeriv t ht0 z a b]
  set u : Fin 4 → ℂ := fun i => (N : ℂ)⁻¹ * ∑' n, f i n with hu
  set m : Fin 4 → ℂ := fun i => heatKernelDeriv t (z i) (derivOrder a b i) with hm
  have e : ((N : ℂ) ^ 4)⁻¹ * ∏ i, ∑' n, f i n = ∏ i, u i := by
    simp only [hu]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  rw [e]
  set τ := Real.sqrt t with hτ
  have hτ2 : τ ^ 2 = t := Real.sq_sqrt ht0.le
  set q := Real.exp (-((N : ℝ) ^ 2 / (11 * t))) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q ≤ 1 := by
    rw [hq, Real.exp_le_one_iff]
    have : 0 ≤ (N : ℝ) ^ 2 / (11 * t) := by positivity
    linarith
  have hb := norm_prod_four_sub_le u m (fun i => τ⁻¹ ^ (derivOrder a b i + 1)) |C₀| q
    (abs_nonneg _) hq0 hq1
    (fun i => by positivity)
    (fun i => by
      refine (hl i).2.1.trans ?_
      have : 0 ≤ τ⁻¹ ^ (derivOrder a b i + 1) := by positivity
      have h2 := le_abs_self C₀
      gcongr)
    (fun i => by
      refine (hl i).2.2.trans ?_
      have : 0 ≤ τ⁻¹ ^ (derivOrder a b i + 1) := by positivity
      have h2 := le_abs_self C₀
      gcongr)
  refine hb.trans (le_of_eq ?_)
  rw [Finset.prod_pow_eq_pow_sum, sum_derivOrder_succ]
  have e6 : τ⁻¹ ^ 6 = (t ^ 3)⁻¹ := by
    rw [← hτ2, inv_pow]
    congr 1
    ring
  rw [e6]
end YangMills.Construction.LatticeFourier
