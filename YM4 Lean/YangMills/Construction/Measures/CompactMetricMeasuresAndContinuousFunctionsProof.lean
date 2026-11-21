import YangMills.Construction.Measures.CompactMetricMeasuresAndContinuousFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace YangMills.Construction.Measures.CompactMetric
theorem measuresAndContinuousFunctions_holds : measuresAndContinuousFunctions := by
  intro X _ _ _ _ _
  refine ⟨?_, ?_, ?_⟩
  · intro σ σ' hσ hσ' h
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
    exact h f.toContinuousMap
  · intro ν hν
    let P : ℕ → ProbabilityMeasure X := fun i => ⟨ν i, hν i⟩
    obtain ⟨μ, -, φ, hφ, hlim⟩ :=
      (isCompact_univ (X := ProbabilityMeasure X)).tendsto_subseq (x := P)
        (fun _ => Set.mem_univ _)
    refine ⟨φ, (μ : Measure X), hφ, inferInstance, fun F => ?_⟩
    have hreal : ∀ f : C(X, ℝ), Tendsto (fun j => ∫ y, f y ∂(ν (φ j))) atTop
        (𝓝 (∫ y, f y ∂(μ : Measure X))) := fun f =>
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim)
        (BoundedContinuousFunction.mkOfCompact f)
    let reF : C(X, ℝ) := ⟨fun y => (F y).re, Complex.continuous_re.comp F.continuous⟩
    let imF : C(X, ℝ) := ⟨fun y => (F y).im, Complex.continuous_im.comp F.continuous⟩
    have hsplit : ∀ (m : Measure X) [IsProbabilityMeasure m], ∫ y, F y ∂m =
        ((∫ y, reF y ∂m : ℝ) : ℂ) + ((∫ y, imF y ∂m : ℝ) : ℂ) * Complex.I := by
      intro m _
      have hint : Integrable (fun y => F y) m :=
        F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      exact (integral_re_add_im hint).symm
    have hν' : ∀ j, IsProbabilityMeasure (ν (φ j)) := fun j => hν _
    simp only [hsplit]
    exact ((Complex.continuous_ofReal.tendsto _).comp (hreal reF)).add
      (((Complex.continuous_ofReal.tendsto _).comp (hreal imF)).mul_const Complex.I)
  · let e : ℕ → C(X, ℝ) := TopologicalSpace.denseSeq C(X, ℝ)
    have he : DenseRange e := TopologicalSpace.denseRange_denseSeq _
    let scale : C(X, ℝ) → C(X, ℝ) := fun f =>
      ⟨fun y => (f y + ‖f‖) / (2 * ‖f‖ + 1), by have := f.continuous; fun_prop⟩
    obtain ⟨ψ, h0, hs⟩ : ∃ ψ : ℕ → C(X, ℝ), ψ 0 = 1 ∧ ∀ n, ψ (n + 1) = scale (e n) :=
      ⟨fun t => Nat.casesOn t 1 (fun n => scale (e n)), rfl, fun _ => rfl⟩
    refine ⟨ψ, ?_, ?_⟩
    · intro t y
      cases t with
      | zero => simp [h0]
      | succ n =>
        have hb := abs_le.mp ((Real.norm_eq_abs _).symm.trans_le ((e n).norm_coe_le_norm y))
        have hN := norm_nonneg (e n)
        rw [hs]
        change (e n y + ‖e n‖) / (2 * ‖e n‖ + 1) ∈ Set.Icc (0 : ℝ) 1
        constructor
        · exact div_nonneg (by linarith [hb.1]) (by linarith)
        · rw [div_le_one (by linarith)]
          linarith [hb.2]
    · intro F ε hε
      let reF : C(X, ℝ) := ⟨fun y => (F y).re, Complex.continuous_re.comp F.continuous⟩
      let imF : C(X, ℝ) := ⟨fun y => (F y).im, Complex.continuous_im.comp F.continuous⟩
      obtain ⟨n, hn⟩ := he.exists_dist_lt reF (half_pos hε)
      obtain ⟨m, hm⟩ := he.exists_dist_lt imF (half_pos hε)
      set N₁ : ℝ := ‖e n‖ with hN₁
      set N₂ : ℝ := ‖e m‖ with hN₂
      have hN₁0 : (2 * (N₁ : ℂ) + 1) ≠ 0 := by
        have : 2 * N₁ + 1 ≠ 0 := by have := norm_nonneg (e n); positivity
        exact_mod_cast this
      have hN₂0 : (2 * (N₂ : ℂ) + 1) ≠ 0 := by
        have : 2 * N₂ + 1 ≠ 0 := by have := norm_nonneg (e m); positivity
        exact_mod_cast this
      refine ⟨Finset.range (max n m + 2),
        fun t => (if t = 0 then -(N₁ : ℂ) - (N₂ : ℂ) * Complex.I else 0) +
          (if t = n + 1 then 2 * (N₁ : ℂ) + 1 else 0) +
          (if t = m + 1 then (2 * (N₂ : ℂ) + 1) * Complex.I else 0), fun y => ?_⟩
      have hsum : ∑ t ∈ Finset.range (max n m + 2),
          ((if t = 0 then -(N₁ : ℂ) - (N₂ : ℂ) * Complex.I else 0) +
            (if t = n + 1 then 2 * (N₁ : ℂ) + 1 else 0) +
            (if t = m + 1 then (2 * (N₂ : ℂ) + 1) * Complex.I else 0)) * (ψ t y : ℂ) =
          (e n y : ℂ) + (e m y : ℂ) * Complex.I := by
        have h1 : n + 1 < max n m + 2 := by omega
        have h2 : m + 1 < max n m + 2 := by omega
        simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_range, h1, h2, if_true, Nat.zero_lt_succ, h0, hs]
        have hv₁ : scale (e n) y = (e n y + N₁) / (2 * N₁ + 1) := rfl
        have hv₂ : scale (e m) y = (e m y + N₂) / (2 * N₂ + 1) := rfl
        rw [hv₁, hv₂, ContinuousMap.one_apply]
        have k₁ : (2 * (N₁ : ℂ) + 1) * (((e n y : ℂ) + N₁) / (2 * N₁ + 1)) = (e n y : ℂ) + N₁ :=
          mul_div_cancel₀ _ hN₁0
        have k₂ : (2 * (N₂ : ℂ) + 1) * (((e m y : ℂ) + N₂) / (2 * N₂ + 1)) = (e m y : ℂ) + N₂ :=
          mul_div_cancel₀ _ hN₂0
        push_cast
        linear_combination k₁ + Complex.I * k₂
      rw [hsum]
      have hn' : |(F y).re - e n y| ≤ ε / 2 := by
        have h := (ContinuousMap.dist_apply_le_dist (f := reF) (g := e n) y)
        have h' : dist (reF y) (e n y) < ε / 2 := lt_of_le_of_lt h hn
        exact (Real.dist_eq _ _ ▸ h').le
      have hm' : |(F y).im - e m y| ≤ ε / 2 := by
        have h := (ContinuousMap.dist_apply_le_dist (f := imF) (g := e m) y)
        have h' : dist (imF y) (e m y) < ε / 2 := lt_of_le_of_lt h hm
        exact (Real.dist_eq _ _ ▸ h').le
      have hdec : F y - ((e n y : ℂ) + (e m y : ℂ) * Complex.I) =
          (((F y).re - e n y : ℝ) : ℂ) + (((F y).im - e m y : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [hdec]
      calc ‖(((F y).re - e n y : ℝ) : ℂ) + (((F y).im - e m y : ℝ) : ℂ) * Complex.I‖
          ≤ ‖(((F y).re - e n y : ℝ) : ℂ)‖ + ‖(((F y).im - e m y : ℝ) : ℂ) * Complex.I‖ :=
            norm_add_le _ _
        _ = |(F y).re - e n y| + |(F y).im - e m y| := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ ε := by linarith
end YangMills.Construction.Measures.CompactMetric
