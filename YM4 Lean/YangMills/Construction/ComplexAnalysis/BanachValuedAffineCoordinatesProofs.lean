import YangMills.Construction.ComplexAnalysis.BanachValuedAffineCoordinates
import Mathlib
noncomputable section
namespace YangMills.Construction.BanachValued.AffineCoordinates
open YangMills.Construction.PowerSeries
open YangMills.Construction.Coordinates
variable {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
theorem norm_monomial_le_pow_order {w : ComplexCoordinates n} {r : ℝ} (hw : ‖w‖ ≤ r)
    (γ : MultiIndex n) :
    ‖MultiIndex.monomial w γ‖ ≤ r ^ MultiIndex.order γ := by
  unfold MultiIndex.monomial MultiIndex.order
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm w i).trans hw) _
theorem continuousAt_of_powerSeriesData [CompleteSpace Y] {O : Set (ComplexCoordinates n)}
    {f : ComplexCoordinates n → Y} {c : ComplexCoordinates n} {ρ : ℝ} {a : MultiIndex n → Y}
    (h : IsPowerSeriesDataAt O f c ρ a) : ContinuousAt f c := by
  have hcont : ContinuousOn
      (fun w : ComplexCoordinates n => ∑' γ : MultiIndex n, MultiIndex.monomial w γ • a γ)
      (Metric.closedBall 0 ρ) := by
    refine continuousOn_tsum (u := fun γ => ‖a γ‖ * ρ ^ MultiIndex.order γ) (fun γ => ?_)
      h.summable (fun γ w hw => ?_)
    · refine Continuous.continuousOn ?_
      unfold MultiIndex.monomial
      exact (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _).smul continuous_const
    · rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_monomial_le_pow_order (by simpa using hw) γ)
        (norm_nonneg _)
  have heq : Set.EqOn (fun w => f (c + w))
      (fun w : ComplexCoordinates n => ∑' γ : MultiIndex n, MultiIndex.monomial w γ • a γ)
      (Metric.closedBall 0 ρ) :=
    fun w hw => ((h.hasSum w (by simpa using hw)).tsum_eq).symm
  have h1 : ContinuousAt (fun w => f (c + w)) 0 :=
    (hcont.congr heq).continuousAt (Metric.closedBall_mem_nhds _ h.pos)
  have h2 : ContinuousAt (fun z : ComplexCoordinates n => z - c) c :=
    (continuous_id.sub continuous_const).continuousAt
  have h3 : ContinuousAt ((fun w => f (c + w)) ∘ fun z : ComplexCoordinates n => z - c) c :=
    ContinuousAt.comp (by simpa using h1) h2
  simpa [Function.comp_def] using h3
theorem powerSeriesData_clm_comp [CompleteSpace Y] {O : Set (ComplexCoordinates n)}
    {f : ComplexCoordinates n → Y} {c : ComplexCoordinates n} {ρ : ℝ} {a : MultiIndex n → Y}
    (h : IsPowerSeriesDataAt O f c ρ a) (l : Y →L[ℂ] ℂ) :
    IsPowerSeriesDataAt O (fun z => l (f z)) c ρ (fun γ => l (a γ)) where
  pos := h.pos
  subset := h.subset
  summable := by
    refine Summable.of_nonneg_of_le (fun γ => ?_) (fun γ => ?_)
      (h.summable.mul_left ‖l‖)
    · exact mul_nonneg (norm_nonneg _) (pow_nonneg h.pos.le _)
    · rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (l.le_opNorm _) (pow_nonneg h.pos.le _)
  hasSum := fun w hw => by
    have := l.hasSum (h.hasSum w hw)
    simpa only [map_smul] using this
theorem rowAbsSum_le_maxAbsRowSum (J : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    ∑ j, ‖J i j‖ ≤ maxAbsRowSum J :=
  le_ciSup (f := fun i => ∑ j, ‖J i j‖) (Set.finite_range _).bddAbove i
theorem weightedRowAbsSum_le {J : Matrix (Fin n) (Fin n) ℂ} {w : ComplexCoordinates n} {ρ : ℝ}
    (hw : ‖w‖ * maxAbsRowSum J ≤ ρ) (i : Fin n) : ∑ j, ‖J i j‖ * ‖w j‖ ≤ ρ := by
  calc ∑ j, ‖J i j‖ * ‖w j‖ ≤ ∑ j, ‖J i j‖ * ‖w‖ :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (norm_le_pi_norm w j) (norm_nonneg _)
    _ = (∑ j, ‖J i j‖) * ‖w‖ := Finset.sum_mul _ _ _ |>.symm
    _ ≤ maxAbsRowSum J * ‖w‖ :=
        mul_le_mul_of_nonneg_right (rowAbsSum_le_maxAbsRowSum J i) (norm_nonneg _)
    _ ≤ ρ := by rw [mul_comm]; exact hw
theorem norm_mulVec_le_of_mul_maxAbsRowSum_le {J : Matrix (Fin n) (Fin n) ℂ}
    {w : ComplexCoordinates n} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hw : ‖w‖ * maxAbsRowSum J ≤ ρ) : ‖J.mulVec w‖ ≤ ρ := by
  refine (pi_norm_le_iff_of_nonneg hρ).2 fun i => ?_
  refine le_trans ?_ (weightedRowAbsSum_le hw i)
  change ‖∑ j, J i j * w j‖ ≤ _
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun j _ => norm_mul _ _
theorem monomial_collectedExponent {M : Type*} [CommMonoid M] (w : Fin n → M)
    (t : ExpandedIndex n) :
    MultiIndex.monomial w (collectedExponent t) = ∏ i, ∏ k, w (t.2 i k) := by
  unfold MultiIndex.monomial collectedExponent
  calc ∏ j, w j ^ (∑ i, (Finset.univ.filter fun k => t.2 i k = j).card)
      = ∏ j, ∏ i, w j ^ (Finset.univ.filter fun k => t.2 i k = j).card :=
        Finset.prod_congr rfl fun j _ => (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ = ∏ i, ∏ j, w j ^ (Finset.univ.filter fun k => t.2 i k = j).card := Finset.prod_comm
    _ = ∏ i, ∏ k, w (t.2 i k) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_fiberwise Finset.univ (t.2 i) (fun k => w (t.2 i k))]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Finset.prod_congr rfl (g := fun _ => w j), Finset.prod_const]
        intro k hk
        rw [(Finset.mem_filter.1 hk).2]
theorem sum_prod_choices_eq_prod_sum_pow {R : Type*} [CommSemiring R] (γ : MultiIndex n)
    (g : Fin n → Fin n → R) :
    ∑ y : (∀ i, Fin (γ i) → Fin n), ∏ i, ∏ k, g i (y i k) = ∏ i, (∑ j, g i j) ^ γ i := by
  simp_rw [Fintype.sum_pow]
  rw [Finset.prod_univ_sum]
  simp
theorem expandedSeriesTerm_eq_smul (J : Matrix (Fin n) (Fin n) ℂ) (a : MultiIndex n → Y)
    (w : ComplexCoordinates n) (t : ExpandedIndex n) :
    expandedSeriesTerm J a w t = (∏ i, ∏ k, (J i (t.2 i k) * w (t.2 i k))) • a t.1 := by
  unfold expandedSeriesTerm chosenEntryProd
  rw [monomial_collectedExponent]
  simp only [Finset.prod_mul_distrib]
theorem sum_expandedSeriesTerm_fibre (J : Matrix (Fin n) (Fin n) ℂ) (a : MultiIndex n → Y)
    (w : ComplexCoordinates n) (γ : MultiIndex n) :
    ∑ y : (∀ i, Fin (γ i) → Fin n), expandedSeriesTerm J a w ⟨γ, y⟩ =
      MultiIndex.monomial (J.mulVec w) γ • a γ := by
  simp only [expandedSeriesTerm_eq_smul]
  rw [← Finset.sum_smul, sum_prod_choices_eq_prod_sum_pow γ (fun i j => J i j * w j)]
  rfl
theorem sum_norm_expandedSeriesTerm_fibre (J : Matrix (Fin n) (Fin n) ℂ) (a : MultiIndex n → Y)
    (w : ComplexCoordinates n) (γ : MultiIndex n) :
    ∑ y : (∀ i, Fin (γ i) → Fin n), ‖expandedSeriesTerm J a w ⟨γ, y⟩‖ =
      majorantSeriesTerm J a w γ := by
  unfold majorantSeriesTerm
  rw [← sum_prod_choices_eq_prod_sum_pow γ (fun i j => ‖J i j‖ * ‖w j‖), Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [expandedSeriesTerm_eq_smul, norm_smul, mul_comm, norm_prod]
  simp only [norm_prod, norm_mul]
theorem hasSum_collect_of_hasSum [CompleteSpace Y] {J : Matrix (Fin n) (Fin n) ℂ}
    {a : MultiIndex n → Y} {w : ComplexCoordinates n} {s : Y}
    (hnorm : Summable fun t : ExpandedIndex n => ‖expandedSeriesTerm J a w t‖)
    (hs : HasSum (expandedSeriesTerm J a w) s) :
    HasSum (fun β : MultiIndex n =>
      ∑' t : {t : ExpandedIndex n // collectedExponent t = β}, expandedSeriesTerm J a w t.1) s := by
  let e := Equiv.sigmaFiberEquiv (collectedExponent (n := n))
  have h1 : HasSum (expandedSeriesTerm J a w ∘ e) s := e.hasSum_iff.2 hs
  have hn2 : Summable fun x => ‖(expandedSeriesTerm J a w ∘ e) x‖ := e.summable_iff.2 hnorm
  refine HasSum.sigma h1 fun β => ?_
  exact (Summable.hasSum (hn2.of_norm.comp_injective sigma_mk_injective))
theorem seriesAtIncrement_of_powerSeriesData [CompleteSpace Y] {O : Set (ComplexCoordinates n)}
    {f : ComplexCoordinates n → Y} {J : Matrix (Fin n) (Fin n) ℂ} {b z w : ComplexCoordinates n}
    {ρ : ℝ} {a : MultiIndex n → Y} (h : IsPowerSeriesDataAt O f (J.mulVec z + b) ρ a)
    (hw : ‖w‖ * maxAbsRowSum J ≤ ρ) : SeriesAtIncrement J b f z w ρ a := by
  have hρ : 0 ≤ ρ := h.pos.le
  have hpoint : J.mulVec (z + w) + b = (J.mulVec z + b) + J.mulVec w := by
    rw [Matrix.mulVec_add]; abel
  have hsum : HasSum (fun γ : MultiIndex n => MultiIndex.monomial (J.mulVec w) γ • a γ)
      (f (J.mulVec (z + w) + b)) := by
    rw [hpoint]
    exact h.hasSum _ (norm_mulVec_le_of_mul_maxAbsRowSum_le hρ hw)
  have hmaj : ∀ γ, majorantSeriesTerm J a w γ ≤ ‖a γ‖ * ρ ^ MultiIndex.order γ := by
    intro γ
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    unfold MultiIndex.order
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun i _ => ?_) fun i _ => ?_
    · exact pow_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
    · exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (weightedRowAbsSum_le hw i) _
  have hmaj0 : ∀ γ, 0 ≤ majorantSeriesTerm J a w γ := fun γ =>
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ =>
      pow_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) _)
  have hsm : Summable (majorantSeriesTerm J a w) :=
    Summable.of_nonneg_of_le hmaj0 hmaj h.summable
  have hnorm : Summable fun t : ExpandedIndex n => ‖expandedSeriesTerm J a w t‖ := by
    refine (summable_sigma_of_nonneg fun _ => norm_nonneg _).2
      ⟨fun γ => (hasSum_fintype _).summable, ?_⟩
    simpa only [tsum_fintype, sum_norm_expandedSeriesTerm_fibre] using hsm
  have hS : Summable (expandedSeriesTerm J a w) := hnorm.of_norm
  have htotal : HasSum (expandedSeriesTerm J a w) (f (J.mulVec (z + w) + b)) := by
    have h1 := hS.hasSum.sigma (fun γ => hasSum_fintype _)
    simp only [sum_expandedSeriesTerm_fibre] at h1
    rw [← h1.unique hsum]
    exact hS.hasSum
  have htsum : ∑' t : ExpandedIndex n, ‖expandedSeriesTerm J a w t‖ =
      ∑' γ, majorantSeriesTerm J a w γ := by
    rw [hnorm.tsum_sigma' fun γ => (hasSum_fintype _).summable]
    simp only [tsum_fintype, sum_norm_expandedSeriesTerm_fibre]
  exact
    { hasSum := hsum
      summable_norm_expanded := hnorm
      summable_majorant := hsm
      summable_norm_mul_pow := h.summable
      tsum_norm_expanded_le := htsum.le
      tsum_majorant_le := hsm.tsum_le_tsum hmaj h.summable
      hasSum_collected := by
        exact hasSum_collect_of_hasSum hnorm htotal }
def collectedCoeff (J : Matrix (Fin n) (Fin n) ℂ) (a : MultiIndex n → Y)
    (β : MultiIndex n) : Y :=
  ∑' t : {t : ExpandedIndex n // collectedExponent t = β}, chosenEntryProd J t.1 • a t.1.1
theorem tsum_collectedExponent_fibre (J : Matrix (Fin n) (Fin n) ℂ) (a : MultiIndex n → Y)
    (w : ComplexCoordinates n) (β : MultiIndex n) :
    ∑' t : {t : ExpandedIndex n // collectedExponent t = β}, expandedSeriesTerm J a w t.1 =
      MultiIndex.monomial w β • collectedCoeff J a β := by
  unfold collectedCoeff
  rw [← tsum_const_smul'']
  refine tsum_congr fun t => ?_
  unfold expandedSeriesTerm
  rw [t.2, smul_smul, mul_comm]
theorem maxAbsRowSum_pos (hn : 1 ≤ n) {J : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J) :
    0 < maxAbsRowSum J := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hne : J ≠ 0 := hJ.ne_zero
  obtain ⟨i, j, hij⟩ : ∃ i j, J i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (Matrix.ext hcon)
  calc 0 < ‖J i j‖ := norm_pos_iff.2 hij
    _ ≤ ∑ j, ‖J i j‖ :=
        Finset.single_le_sum (f := fun j => ‖J i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ maxAbsRowSum J := rowAbsSum_le_maxAbsRowSum J i
theorem powerSeriesData_comp_affine [CompleteSpace Y] (hn : 1 ≤ n)
    {O : Set (ComplexCoordinates n)}
    {f : ComplexCoordinates n → Y} {J : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J)
    {b z : ComplexCoordinates n} {ρ : ℝ} {a : MultiIndex n → Y}
    (h : IsPowerSeriesDataAt O f (J.mulVec z + b) ρ a) :
    IsPowerSeriesDataAt {z | J.mulVec z + b ∈ O} (fun z => f (J.mulVec z + b)) z
      (ρ / maxAbsRowSum J) (collectedCoeff J a) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hj := maxAbsRowSum_pos hn hJ
  have hr : 0 < ρ / maxAbsRowSum J := div_pos h.pos hj
  have hsmall : ∀ w : ComplexCoordinates n, ‖w‖ ≤ ρ / maxAbsRowSum J →
      ‖w‖ * maxAbsRowSum J ≤ ρ :=
    fun w hw => (le_div_iff₀ hj).1 hw
  set r : ℝ := ρ / maxAbsRowSum J with hrdef
  refine ⟨hr, ?_, ?_, ?_⟩
  · intro z' hz'
    have hw : ‖z' - z‖ ≤ r := hz'
    have hpoint : J.mulVec z' + b = (J.mulVec z + b) + J.mulVec (z' - z) := by
      rw [Matrix.mulVec_sub]; abel
    refine h.subset ?_
    change ‖J.mulVec z' + b - (J.mulVec z + b)‖ ≤ ρ
    rw [hpoint, add_sub_cancel_left]
    exact norm_mulVec_le_of_mul_maxAbsRowSum_le h.pos.le (hsmall _ hw)
  · let w₀ : ComplexCoordinates n := fun _ => (r : ℂ)
    have hw₀ : ‖w₀‖ ≤ r := (pi_norm_le_iff_of_nonneg hr.le).2 fun _ => by
      simp [w₀, abs_of_pos hr]
    have hnorm :=
      (seriesAtIncrement_of_powerSeriesData (w := w₀) h (hsmall _ hw₀)).summable_norm_expanded
    have hfib := (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).1
      ((Equiv.sigmaFiberEquiv (collectedExponent (n := n))).summable_iff.2 hnorm)
    refine Summable.of_nonneg_of_le (fun β => mul_nonneg (norm_nonneg _) (pow_nonneg hr.le _))
      (fun β => ?_) hfib.2
    have hpow : ‖MultiIndex.monomial w₀ β‖ = r ^ MultiIndex.order β := by
      unfold MultiIndex.monomial MultiIndex.order
      rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [w₀, abs_of_pos hr]
    calc ‖collectedCoeff J a β‖ * r ^ MultiIndex.order β
        = ‖MultiIndex.monomial w₀ β • collectedCoeff J a β‖ := by
          rw [norm_smul, hpow, mul_comm]
      _ = ‖∑' t : {t : ExpandedIndex n // collectedExponent t = β},
            expandedSeriesTerm J a w₀ t.1‖ := by rw [tsum_collectedExponent_fibre]
      _ ≤ ∑' t : {t : ExpandedIndex n // collectedExponent t = β},
            ‖expandedSeriesTerm J a w₀ t.1‖ := norm_tsum_le_tsum_norm (hfib.1 β)
      _ = _ := rfl
  · intro w hw
    have h1 := (seriesAtIncrement_of_powerSeriesData (w := w) h (hsmall _ hw)).hasSum_collected
    simpa only [tsum_collectedExponent_fibre] using h1
theorem isHolomorphicOnOpen_comp_affine [CompleteSpace Y] (hn : 1 ≤ n)
    {O : Set (ComplexCoordinates n)}
    {f : ComplexCoordinates n → Y} (hf : IsHolomorphicOnOpen O f) {J : Matrix (Fin n) (Fin n) ℂ}
    (hJ : IsUnit J) (b : ComplexCoordinates n) :
    IsHolomorphicOnOpen {z | J.mulVec z + b ∈ O} (fun z => f (J.mulVec z + b)) := by
  obtain ⟨hO, hdata⟩ := hf
  rcases hdata with ⟨-, hdata⟩ | ⟨h0, -⟩
  · refine ⟨hO.preimage ?_, Or.inl ⟨hn, fun z hz => ?_⟩⟩
    · exact (continuous_const.matrix_mulVec continuous_id).add continuous_const
    · obtain ⟨ρ, a, h⟩ := hdata _ hz
      exact ⟨_, _, powerSeriesData_comp_affine hn hJ h⟩
  · omega
theorem holomorphicCompositionProperties_holds : HolomorphicCompositionProperties := by
  intro Y _ _ _ n hn O f hf
  refine ⟨fun c hc => ?_, fun l => ?_,
    fun J b hJ => ⟨isHolomorphicOnOpen_comp_affine hn hf hJ b, ?_⟩⟩
  · obtain ⟨hO, hdata⟩ := hf
    rcases hdata with ⟨-, hdata⟩ | ⟨h0, -⟩
    · obtain ⟨ρ, a, h⟩ := hdata c hc
      exact (continuousAt_of_powerSeriesData h).continuousWithinAt
    · omega
  · obtain ⟨hO, hdata⟩ := hf
    rcases hdata with ⟨-, hdata⟩ | ⟨h0, -⟩
    · refine ⟨hO, Or.inl ⟨hn, fun c hc => ?_⟩⟩
      obtain ⟨ρ, a, h⟩ := hdata c hc
      exact ⟨ρ, _, powerSeriesData_clm_comp h l⟩
    · omega
  · intro z ρ a h w hw
    exact seriesAtIncrement_of_powerSeriesData h hw
end YangMills.Construction.BanachValued.AffineCoordinates
