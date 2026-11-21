import YangMills.Construction.Matrices.ExpLogSeriesConvergence
import YangMills.Construction.Matrices.OperatorNormAbsoluteSeries
import Mathlib
open Filter
open scoped Matrix.Norms.L2Operator Topology
namespace YangMills.Construction.Matrices.ComplexMatrix2
namespace ExpLogSeriesBounds
theorem tsum_Ioi_eq_tsum_shift (f : ℕ → ℝ) (l : ℕ) :
    ∑' n : Set.Ioi l, f n = ∑' k : ℕ, f (k + (l + 1)) := by
  let e : ℕ ≃ Set.Ioi l :=
    { toFun := fun k => ⟨k + (l + 1), by simp only [Set.mem_Ioi]; omega⟩
      invFun := fun n => (n : ℕ) - (l + 1)
      left_inv := fun k => by simp
      right_inv := fun n => by
        have hn : l < (n : ℕ) := n.2
        apply Subtype.ext
        show (n : ℕ) - (l + 1) + (l + 1) = n
        omega }
  exact (e.tsum_eq (fun n : Set.Ioi l => f n)).symm
theorem norm_tsum_sub_partialSum_le {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (T : ℕ → E) (b : ℕ → ℝ) (hb : Summable b) (hT : ∀ n, ‖T n‖ ≤ b n) (l : ℕ) :
    ‖(∑' n, T n) - ∑ n ∈ Finset.range (l + 1), T n‖ ≤ ∑' n : Set.Ioi l, b n := by
  have hs : Summable (fun n => ‖T n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hT hb
  have hsT : Summable T := hs.of_norm
  have hsplit := hsT.sum_add_tsum_nat_add (l + 1)
  have he : (∑' n, T n) - ∑ n ∈ Finset.range (l + 1), T n = ∑' k, T (k + (l + 1)) := by
    rw [← hsplit]
    abel
  have hshift : Summable (fun k => ‖T (k + (l + 1))‖) :=
    (summable_nat_add_iff (f := fun n => ‖T n‖) (l + 1)).2 hs
  rw [he, tsum_Ioi_eq_tsum_shift]
  calc ‖∑' k, T (k + (l + 1))‖ ≤ ∑' k, ‖T (k + (l + 1))‖ :=
        norm_tsum_le_tsum_norm hshift
    _ ≤ ∑' k, b (k + (l + 1)) :=
        Summable.tsum_le_tsum (fun k => hT _) hshift
          ((summable_nat_add_iff (f := b) (l + 1)).2 hb)
theorem norm_entry_le_operatorNorm (hN : OperatorNormSeriesProperties) (M : ComplexMatrix2)
    (i j : Fin 2) : ‖M i j‖ ≤ operatorNorm M :=
  le_trans (Finset.le_sup' (fun p : Fin 2 × Fin 2 => ‖M p.1 p.2‖) (Finset.mem_univ (i, j)))
    (hN.1 M).1
theorem dominated_series_properties (hN : OperatorNormSeriesProperties)
    (T : ℕ → ComplexMatrix2) (b : ℕ → ℝ) (hb : Summable b)
    (hT : ∀ n, operatorNorm (T n) ≤ b n) :
    SeriesAbsolutelyConvergent T ∧
    ∑' n, operatorNorm (T n) ≤ ∑' n, b n ∧
    operatorNorm (∑' n, T n) ≤ ∑' n, operatorNorm (T n) ∧
    (∃! S : ComplexMatrix2,
      Tendsto (fun l => operatorNorm (S - seriesPartialSum T l)) atTop (𝓝 0)) ∧
    Tendsto (fun l => operatorNorm ((∑' n, T n) - seriesPartialSum T l)) atTop (𝓝 0) ∧
    (∀ i j : Fin 2, Summable (fun n => ‖T n i j‖) ∧
      HasSum (fun n => T n i j) ((∑' n, T n) i j)) ∧
    ∀ l : ℕ, operatorNorm ((∑' n, T n) - seriesPartialSum T l) ≤ ∑' n : Set.Ioi l, b n := by
  have hs : Summable (fun n => ‖T n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hT hb
  have hsT : Summable T := hs.of_norm
  have hlim : Tendsto (fun l => seriesPartialSum T l) atTop (𝓝 (∑' n, T n)) :=
    (hsT.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hz : Tendsto (fun l => operatorNorm ((∑' n, T n) - seriesPartialSum T l)) atTop (𝓝 0) := by
    have := tendsto_iff_norm_sub_tendsto_zero.1 hlim
    simpa only [norm_sub_rev] using this
  refine ⟨?_, ?_, norm_tsum_le_tsum_norm hs, ⟨∑' n, T n, hz, ?_⟩, hz, ?_, ?_⟩
  · exact ⟨∑' n, ‖T n‖, (hs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)⟩
  · exact Summable.tsum_le_tsum hT hs hb
  · intro S hS
    exact hN.2.2.2.2.2.2.2.2.2.2.2.2.1 (seriesPartialSum T) S (∑' n, T n) hS hz
  · intro i j
    refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_entry_le_operatorNorm hN (T n) i j) hs, ?_⟩
    exact hsT.hasSum.map (Matrix.entryAddMonoidHom ℂ i j) (continuous_id.matrix_elem i j)
  · intro l
    exact norm_tsum_sub_partialSum_le T b hb hT l
theorem operatorNorm_expSeriesTerm_le (hN : OperatorNormSeriesProperties) (Z : ComplexMatrix2)
    (n : ℕ) : operatorNorm (expSeriesTerm Z n) ≤ operatorNorm Z ^ n / (n.factorial : ℝ) := by
  have hp : operatorNorm (Z ^ n) ≤ operatorNorm Z ^ n := hN.2.2.2.2.2.2.2.2.2.1 Z n
  have hc : ‖((n.factorial : ℂ)⁻¹)‖ = ((n.factorial : ℝ))⁻¹ := by simp
  show ‖((n.factorial : ℂ)⁻¹) • Z ^ n‖ ≤ _
  rw [norm_smul, hc, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hp (by positivity)
theorem matExp_series_properties (hN : OperatorNormSeriesProperties) (Z : ComplexMatrix2) :
    SeriesAbsolutelyConvergent (expSeriesTerm Z) ∧
    ∑' n : ℕ, operatorNorm (expSeriesTerm Z n) ≤ Real.exp (operatorNorm Z) ∧
    (∃! S : ComplexMatrix2,
      Tendsto (fun l => operatorNorm (S - expSeriesPartialSum Z l)) atTop (𝓝 0)) ∧
    Tendsto (fun l => operatorNorm (matExp Z - expSeriesPartialSum Z l)) atTop (𝓝 0) ∧
    (∀ i j : Fin 2,
      Summable (fun n : ℕ => ‖(Z ^ n) i j / (n.factorial : ℂ)‖) ∧
      HasSum (fun n : ℕ => (Z ^ n) i j / (n.factorial : ℂ)) (matExp Z i j)) ∧
    (∀ l : ℕ, operatorNorm (matExp Z - expSeriesPartialSum Z l) ≤
      ∑' n : Set.Ioi l, operatorNorm Z ^ (n : ℕ) / ((n : ℕ).factorial : ℝ)) ∧
    operatorNorm (matExp Z - 1) ≤ Real.exp (operatorNorm Z) - 1 ∧
    operatorNorm (matExp Z - 1 - Z) ≤ Real.exp (operatorNorm Z) - 1 - operatorNorm Z ∧
    operatorNorm (matExp Z) ≤ Real.exp (operatorNorm Z) := by
  have hb : HasSum (fun n : ℕ => operatorNorm Z ^ n / (n.factorial : ℝ))
      (Real.exp (operatorNorm Z)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (operatorNorm Z)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ :=
    dominated_series_properties hN (expSeriesTerm Z) _ hb.summable
      (operatorNorm_expSeriesTerm_le hN Z)
  rw [← matExp_eq_tsum_expSeriesTerm] at f3 f5 f6 f7
  rw [hb.tsum_eq] at f2
  simp only [seriesPartialSum_expSeriesTerm] at f4 f5 f7
  have e0 : ∑' n : Set.Ioi 0, operatorNorm Z ^ (n : ℕ) / ((n : ℕ).factorial : ℝ) =
      Real.exp (operatorNorm Z) - 1 := by
    have hsplit := hb.summable.sum_add_tsum_nat_add 1
    rw [hb.tsum_eq] at hsplit
    rw [tsum_Ioi_eq_tsum_shift (fun n => operatorNorm Z ^ n / (n.factorial : ℝ)) 0, ← hsplit]
    simp
  have e1 : ∑' n : Set.Ioi 1, operatorNorm Z ^ (n : ℕ) / ((n : ℕ).factorial : ℝ) =
      Real.exp (operatorNorm Z) - 1 - operatorNorm Z := by
    have hsplit := hb.summable.sum_add_tsum_nat_add 2
    rw [hb.tsum_eq] at hsplit
    rw [tsum_Ioi_eq_tsum_shift (fun n => operatorNorm Z ^ n / (n.factorial : ℝ)) 1, ← hsplit]
    simp [Finset.sum_range_succ]
    ring
  have p0 : expSeriesPartialSum Z 0 = 1 := by simp [expSeriesPartialSum]
  have p1 : expSeriesPartialSum Z 1 = 1 + Z := by
    simp [expSeriesPartialSum, Finset.sum_range_succ]
  refine ⟨f1, f2, f4, f5, ?_, f7, ?_, ?_, f3.trans f2⟩
  · intro i j
    have he : ∀ n : ℕ, expSeriesTerm Z n i j = (Z ^ n) i j / (n.factorial : ℂ) := by
      intro n
      simp [expSeriesTerm, Matrix.smul_apply, div_eq_inv_mul]
    have := f6 i j
    simp only [he] at this
    exact this
  · have := f7 0
    rwa [p0, e0] at this
  · have := f7 1
    rwa [p1, e1, ← sub_sub] at this
theorem operatorNorm_logSeriesTerm_le (hN : OperatorNormSeriesProperties) (X : ComplexMatrix2)
    (n : ℕ) : operatorNorm (logSeriesTerm X n) ≤ operatorNorm (X - 1) ^ n / (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [logSeriesTerm]
  have hp : operatorNorm ((1 - X) ^ n) ≤ operatorNorm (X - 1) ^ n := by
    have := hN.2.2.2.2.2.2.2.2.2.1 (1 - X) n
    rwa [show operatorNorm (1 - X) = operatorNorm (X - 1) from norm_sub_rev _ _] at this
  have hc : ‖((n : ℂ)⁻¹)‖ = ((n : ℝ))⁻¹ := by simp
  rw [logSeriesTerm, if_neg hn.ne']
  show ‖-(((n : ℂ)⁻¹) • (1 - X) ^ n)‖ ≤ _
  rw [norm_neg, norm_smul, hc, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hp (by positivity)
theorem tsum_Ioi_pow_div_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (l : ℕ) :
    ∑' n : Set.Ioi l, t ^ (n : ℕ) / ((n : ℕ) : ℝ) ≤ t ^ (l + 1) / (((l : ℝ) + 1) * (1 - t)) := by
  have hg : Summable (fun k : ℕ => t ^ (l + 1) / ((l : ℝ) + 1) * t ^ k) :=
    (summable_geometric_of_lt_one ht0 ht1).mul_left _
  have hle : ∀ k : ℕ, t ^ (k + (l + 1)) / ((k + (l + 1) : ℕ) : ℝ) ≤
      t ^ (l + 1) / ((l : ℝ) + 1) * t ^ k := by
    intro k
    have h1 : (0 : ℝ) < (l : ℝ) + 1 := by positivity
    have h2 : (l : ℝ) + 1 ≤ ((k + (l + 1) : ℕ) : ℝ) := by
      push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    calc t ^ (k + (l + 1)) / ((k + (l + 1) : ℕ) : ℝ) ≤ t ^ (k + (l + 1)) / ((l : ℝ) + 1) :=
          div_le_div_of_nonneg_left (by positivity) h1 h2
      _ = t ^ (l + 1) / ((l : ℝ) + 1) * t ^ k := by rw [pow_add]; ring
  have hs : Summable (fun k : ℕ => t ^ (k + (l + 1)) / ((k + (l + 1) : ℕ) : ℝ)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hle hg
  rw [tsum_Ioi_eq_tsum_shift (fun n => t ^ n / (n : ℝ)) l]
  calc ∑' k : ℕ, t ^ (k + (l + 1)) / ((k + (l + 1) : ℕ) : ℝ)
      ≤ ∑' k : ℕ, t ^ (l + 1) / ((l : ℝ) + 1) * t ^ k := Summable.tsum_le_tsum hle hs hg
    _ = t ^ (l + 1) / (((l : ℝ) + 1) * (1 - t)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one ht0 ht1, div_mul_eq_div_div,
          div_eq_mul_inv _ (1 - t)]
theorem logSeries_series_properties (hN : OperatorNormSeriesProperties) (X : ComplexMatrix2)
    (t : ℝ) (ht : t = operatorNorm (X - 1)) (ht1 : t < 1) :
    SeriesAbsolutelyConvergent (logSeriesTerm X) ∧
    ∑' n : Set.Ici (1 : ℕ), operatorNorm ((((n : ℕ) : ℂ)⁻¹) • (1 - X) ^ (n : ℕ)) ≤
      -realLog (1 - t) ∧
    (∃! S : ComplexMatrix2,
      Tendsto (fun l => operatorNorm (S - logSeriesPartialSum X l)) atTop (𝓝 0)) ∧
    Tendsto (fun l => operatorNorm (logSeries X - logSeriesPartialSum X l)) atTop (𝓝 0) ∧
    (∀ i j : Fin 2,
      Summable (fun n : Set.Ici (1 : ℕ) => ‖-((((n : ℕ) : ℂ)⁻¹) * ((1 - X) ^ (n : ℕ)) i j)‖) ∧
      HasSum (fun n : Set.Ici (1 : ℕ) => -((((n : ℕ) : ℂ)⁻¹) * ((1 - X) ^ (n : ℕ)) i j))
        (logSeries X i j)) ∧
    (∀ l : ℕ, operatorNorm (logSeries X - logSeriesPartialSum X l) ≤
        ∑' n : Set.Ioi l, t ^ (n : ℕ) / ((n : ℕ) : ℝ) ∧
      ∑' n : Set.Ioi l, t ^ (n : ℕ) / ((n : ℕ) : ℝ) ≤
        t ^ (l + 1) / (((l : ℝ) + 1) * (1 - t))) ∧
    operatorNorm (logSeries X - (X - 1)) ≤ t ^ 2 / (2 * (1 - t)) ∧
    operatorNorm (logSeries X) ≤ -realLog (1 - t) := by
  have ht0 : 0 ≤ t := ht ▸ norm_nonneg _
  have hb : Summable (fun n : ℕ => t ^ n / (n : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (summable_geometric_of_lt_one ht0 ht1)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact div_le_self (by positivity) (by exact_mod_cast hn)
  have hln : ∑' n : ℕ, t ^ n / (n : ℝ) = -realLog (1 - t) := by
    have hsum : HasSum (fun n : ℕ => t ^ (n + 1) / ((n : ℝ) + 1)) (-Real.log (1 - t)) :=
      Real.hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_of_nonneg ht0])
    rw [hb.tsum_eq_zero_add]
    simp only [Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]
    exact hsum.tsum_eq
  have hbound : ∀ n, operatorNorm (logSeriesTerm X n) ≤ t ^ n / (n : ℝ) := fun n => by
    rw [ht]
    exact operatorNorm_logSeriesTerm_le hN X n
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ :=
    dominated_series_properties hN (logSeriesTerm X) _ hb hbound
  rw [← logSeries_eq_tsum_logSeriesTerm] at f3 f5 f6 f7
  rw [hln] at f2
  simp only [seriesPartialSum_logSeriesTerm] at f4 f5 f7
  have hne : ∀ n : Set.Ici (1 : ℕ), (n : ℕ) ≠ 0 := fun n => by
    have : 1 ≤ (n : ℕ) := n.2
    omega
  have hsupp : Function.support (fun n : ℕ => operatorNorm (logSeriesTerm X n)) ⊆ Set.Ici 1 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · exact absurd (by simp [logSeriesTerm]) hn
    · exact hn'
  have e2 : ∑' n : Set.Ici (1 : ℕ), operatorNorm ((((n : ℕ) : ℂ)⁻¹) • (1 - X) ^ (n : ℕ)) =
      ∑' n : ℕ, operatorNorm (logSeriesTerm X n) := by
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    refine tsum_congr fun n => ?_
    rw [logSeriesTerm, if_neg (hne n)]
    exact (norm_neg _).symm
  have p1 : logSeriesPartialSum X 1 = X - 1 := by simp [logSeriesPartialSum]
  refine ⟨f1, e2 ▸ f2, f4, f5, ?_, fun l => ⟨f7 l, tsum_Ioi_pow_div_le ht0 ht1 l⟩, ?_,
    f3.trans f2⟩
  · intro i j
    obtain ⟨s1, s2⟩ := f6 i j
    have he : ∀ n : Set.Ici (1 : ℕ), -((((n : ℕ) : ℂ)⁻¹) * ((1 - X) ^ (n : ℕ)) i j) =
        logSeriesTerm X n i j := by
      intro n
      rw [logSeriesTerm, if_neg (hne n)]
      simp [Matrix.smul_apply]
    have hs' : Function.support (fun n : ℕ => logSeriesTerm X n i j) ⊆ Set.Ici 1 := by
      intro n hn
      rcases Nat.eq_zero_or_pos n with rfl | hn'
      · exact absurd (by simp [logSeriesTerm]) hn
      · exact hn'
    simp only [he]
    exact ⟨s1.subtype _, (hasSum_subtype_iff_of_support_subset hs').2 s2⟩
  · have h1 := (f7 1).trans (tsum_Ioi_pow_div_le ht0 ht1 1)
    rw [p1] at h1
    have e : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
    rwa [e] at h1
end ExpLogSeriesBounds
open ExpLogSeriesBounds in
theorem expLogSeriesConvergence_holds (hN : OperatorNormSeriesProperties) :
    ExpLogSeriesConvergence :=
  ⟨matExp_series_properties hN, logSeries_series_properties hN, by simp [logSeries]⟩
end YangMills.Construction.Matrices.ComplexMatrix2
