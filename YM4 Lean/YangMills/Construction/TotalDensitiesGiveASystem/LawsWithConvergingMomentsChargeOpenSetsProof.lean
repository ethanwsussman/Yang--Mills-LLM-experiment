import YangMills.Construction.TotalDensitiesGiveASystem.LawsWithConvergingMomentsChargeOpenSets
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory MvPolynomial
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem.MomentConvergence
private theorem integrable_and_tendsto_integral_eval {k : ℕ} (μs : ℕ+ → Measure (Fin k → ℝ))
    (μ : Measure (Fin k → ℝ))
    (hμ : ∀ e : Fin k → ℕ, Integrable (fun x => ∏ i, x i ^ e i) μ)
    (hconv : ∀ e : Fin k → ℕ, (∀ j, Integrable (fun x => ∏ i, x i ^ e i) (μs j)) ∧
      Tendsto (fun j => ∫ x, ∏ i, x i ^ e i ∂μs j) atTop (𝓝 (∫ x, ∏ i, x i ^ e i ∂μ)))
    (P : MvPolynomial (Fin k) ℝ) :
    Integrable (fun x : Fin k → ℝ => eval x P) μ ∧
      Tendsto (fun j => ∫ x : Fin k → ℝ, eval x P ∂μs j) atTop (𝓝 (∫ x : Fin k → ℝ, eval x P ∂μ)) := by
  have heval : (fun x : Fin k → ℝ => eval x P) =
      fun x => ∑ d ∈ P.support, P.coeff d * ∏ i, x i ^ d i := funext fun x => eval_eq' x P
  have hintegral : ∀ ν : Measure (Fin k → ℝ), (∀ e : Fin k → ℕ, Integrable (fun x => ∏ i, x i ^ e i) ν) →
      ∫ x : Fin k → ℝ, eval x P ∂ν = ∑ d ∈ P.support, P.coeff d * ∫ x, ∏ i, x i ^ d i ∂ν := by
    intro ν hν
    rw [heval]
    refine (integral_finsetSum P.support
      (f := fun (d : Fin k →₀ ℕ) (x : Fin k → ℝ) => P.coeff d * ∏ i, x i ^ d i)
      fun d _ => (hν d).const_mul _).trans ?_
    exact Finset.sum_congr rfl fun d _ => integral_const_mul _ _
  refine ⟨?_, ?_⟩
  · rw [heval]
    exact integrable_finsetSum _ fun d _ => (hμ d).const_mul _
  · rw [hintegral μ hμ]
    simp_rw [hintegral _ (fun e => (hconv e).1 _)]
    exact tendsto_finsetSum _ fun d _ => (hconv d).2.const_mul _
theorem chargesOpenSets : MomentConvergenceChargesOpenSets := by
  intro k μs μ hμs hμ ⟨K, hK, hKμ⟩ hconv U hU hUpos
  have hae : ∀ᵐ y ∂μ, y ∈ K := mem_ae_iff.2 hKμ
  have hmonomial : ∀ e : Fin k → ℕ, Integrable (fun x : Fin k → ℝ => ∏ i, x i ^ e i) μ := by
    intro e
    have hcont : Continuous fun x : Fin k → ℝ => ∏ i, x i ^ e i := by fun_prop
    have : IntegrableOn (fun x : Fin k → ℝ => ∏ i, x i ^ e i) K μ := hcont.continuousOn.integrableOn_compact hK
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at this
  obtain ⟨x₀, hx₀U, hx₀⟩ := exists_mem_forall_mem_nhdsWithin_pos_measure hUpos.ne'
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀U
  let Q : MvPolynomial (Fin k) ℝ := ∑ i, (X i - C (x₀ i)) ^ 2
  let q : (Fin k → ℝ) → ℝ := fun y => ∑ i, (y i - x₀ i) ^ 2
  have hQ : ∀ y, eval y Q = q y := by
    intro y
    simp [Q, q]
  have hq_nonneg : ∀ y, 0 ≤ q y := fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hq_cont : Continuous q := by fun_prop
  have hq_outside : ∀ y, y ∉ U → ε ^ 2 ≤ q y := by
    intro y hy
    by_contra hlt
    rw [not_le] at hlt
    apply hy
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq]
    have hi : (y i - x₀ i) ^ 2 ≤ q y :=
      Finset.single_le_sum (f := fun i => (y i - x₀ i) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
    exact abs_lt_of_sq_lt_sq (hi.trans_lt hlt) hε.le
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ε ^ 2 := ⟨_, rfl⟩
  have hr_pos : 0 < r := hr ▸ pow_pos hε 2
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = r / 2 := ⟨_, rfl⟩
  have hρ_pos : 0 < ρ := by linarith
  have hρr : ρ < r := by linarith
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hq_cont.continuousOn
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = |R| + r + 1 := ⟨_, rfl⟩
  have hrτ : r < τ := by
    have := abs_nonneg R
    linarith
  have hτ_pos : 0 < τ := by linarith
  have hq_le : ∀ y ∈ K, q y ≤ τ := by
    intro y hy
    have h1 := hR y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (hq_nonneg y)] at h1
    have := le_abs_self R
    linarith
  let W : Set (Fin k → ℝ) := {y | q y < ρ}
  have hW_open : IsOpen W := isOpen_lt hq_cont continuous_const
  have hx₀W : x₀ ∈ W := by
    simp [W, q, hρ_pos]
  have hW_pos : 0 < μ.real W :=
    ENNReal.toReal_pos (hx₀ W (mem_nhdsWithin_of_mem_nhds (hW_open.mem_nhds hx₀W))).ne' (measure_ne_top _ _)
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (τ - ρ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = (τ - r) ^ 2 := ⟨_, rfl⟩
  have hv_nonneg : 0 ≤ v := hv ▸ sq_nonneg _
  have hvu : v < u := by
    rw [hu, hv]
    exact pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
  have hu_pos : 0 < u := hv_nonneg.trans_lt hvu
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < (r - ρ) * μ.real W / τ by
    have : 0 < r - ρ := by linarith
    positivity) ((div_lt_one hu_pos).2 hvu)
  have hnτ : τ * v ^ n < (r - ρ) * u ^ n * μ.real W := by
    rw [div_pow, div_lt_div_iff₀ (pow_pos hu_pos n) hτ_pos] at hn
    nlinarith [hn]
  let P : MvPolynomial (Fin k) ℝ := (C r - Q) * ((C τ - Q) ^ 2) ^ n
  have hP : ∀ y, eval y P = (r - q y) * ((τ - q y) ^ 2) ^ n := by
    intro y
    simp [P, hQ]
  obtain ⟨hPint, hPlim⟩ := integrable_and_tendsto_integral_eval μs μ hmonomial hconv P
  have hW_meas : MeasurableSet W := hW_open.measurableSet
  have hP_pos : 0 < ∫ y : Fin k → ℝ, eval y P ∂μ := by
    have hbelow : ∀ᵐ y ∂μ, W.indicator (fun _ => (r - ρ) * u ^ n) y - τ * v ^ n ≤ eval y P := by
      filter_upwards [hae] with y hy
      rw [hP]
      have hqy := hq_le y hy
      have hpow_nonneg : 0 ≤ ((τ - q y) ^ 2) ^ n := pow_nonneg (sq_nonneg _) n
      have hτv : 0 ≤ τ * v ^ n := mul_nonneg hτ_pos.le (pow_nonneg hv_nonneg n)
      by_cases hyW : y ∈ W
      · rw [Set.indicator_of_mem hyW]
        have hyρ : q y < ρ := hyW
        have hupow : u ^ n ≤ ((τ - q y) ^ 2) ^ n := by
          refine pow_le_pow_left₀ hu_pos.le ?_ n
          rw [hu]
          exact pow_le_pow_left₀ (by linarith) (by linarith) 2
        have hdiff : r - ρ ≤ r - q y := by linarith
        have hun : 0 ≤ u ^ n := pow_nonneg hu_pos.le n
        have : (r - ρ) * u ^ n ≤ (r - q y) * ((τ - q y) ^ 2) ^ n :=
          mul_le_mul hdiff hupow hun (by linarith)
        linarith
      · rw [Set.indicator_of_notMem hyW]
        by_cases hqr : q y ≤ r
        · have : 0 ≤ (r - q y) * ((τ - q y) ^ 2) ^ n := mul_nonneg (by linarith) hpow_nonneg
          linarith
        · rw [not_le] at hqr
          have hpow_le : ((τ - q y) ^ 2) ^ n ≤ v ^ n := by
            refine pow_le_pow_left₀ (sq_nonneg _) ?_ n
            rw [hv]
            exact pow_le_pow_left₀ (by linarith) (by linarith) 2
          have : (q y - r) * ((τ - q y) ^ 2) ^ n ≤ τ * v ^ n :=
            mul_le_mul (by linarith [hq_nonneg y]) hpow_le hpow_nonneg hτ_pos.le
          nlinarith [this]
    have hlower_int : Integrable (fun y => W.indicator (fun _ => (r - ρ) * u ^ n) y - τ * v ^ n) μ :=
      ((integrable_const _).indicator hW_meas).sub (integrable_const _)
    have hmono := integral_mono_ae hlower_int hPint hbelow
    rw [integral_sub ((integrable_const _).indicator hW_meas) (integrable_const _),
      integral_indicator_const _ hW_meas] at hmono
    simp only [integral_const, probReal_univ, smul_eq_mul] at hmono
    nlinarith [hmono, hnτ]
  filter_upwards [hPlim.eventually (lt_mem_nhds hP_pos)] with j hj
  by_contra hzero
  have hUj : μs j U = 0 := by simpa using hzero
  have hcompl : ∀ᵐ y ∂μs j, y ∈ Uᶜ := compl_mem_ae_iff.2 hUj
  have hnonpos : ∫ y : Fin k → ℝ, eval y P ∂μs j ≤ 0 := by
    refine integral_nonpos_of_ae ?_
    filter_upwards [hcompl] with y hy
    rw [hP]
    have h1 : r ≤ q y := hr ▸ hq_outside y hy
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (pow_nonneg (sq_nonneg _) n)
  linarith
end YangMills.Construction.TotalDensitiesGiveASystem.MomentConvergence
end
