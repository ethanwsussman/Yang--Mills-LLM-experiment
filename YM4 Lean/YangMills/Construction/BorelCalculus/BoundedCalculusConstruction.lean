import YangMills.Construction.SpectralTheory.BoundedBorelCalculus
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.BorelCalculus.OfSpectralMeasure
open YangMills.Construction.BorelSpectral YangMills.Construction.BorelCalculus
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
omit [CompleteSpace H] in
theorem ext_of_inner_self {A B : H →L[ℂ] H} (hAB : ∀ v, ⟪v, A v⟫_ℂ = ⟪v, B v⟫_ℂ) : A = B := by
  refine ContinuousLinearMap.coe_injective ((ext_inner_map (A : H →ₗ[ℂ] H) B).mp fun v => ?_)
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, hAB v, inner_conj_symm]
theorem integrable_of_isBoundedFn (P : SpectralMeasure Y H) {σ : Y → ℂ} (hσ : Measurable σ)
    (hσb : IsBoundedFn σ) (v : H) : Integrable σ (P.diagMeasure v) := by
  rcases hσb with ⟨M, hM⟩
  exact Integrable.of_bound hσ.aestronglyMeasurable M (Eventually.of_forall hM)
theorem commute_apply (P : SpectralMeasure Y H) (D D' : BorelSubsets Y) :
    Commute (P D) (P D') := by
  have hswap : (⟨D.1 ∩ D'.1, D.2.inter D'.2⟩ : BorelSubsets Y) = ⟨D'.1 ∩ D.1, D'.2.inter D.2⟩ :=
    Subtype.ext (inter_comm _ _)
  show P D * P D' = P D' * P D
  rw [← P.map_inter D D', ← P.map_inter D' D, hswap]
theorem diagMeasure_apply_vec (P : SpectralMeasure Y H) (D : BorelSubsets Y) (v : H) :
    P.diagMeasure (P D v) = (P.diagMeasure v).restrict D.1 := by
  ext S hS
  rw [Measure.restrict_apply hS, P.diagMeasure_apply _ ⟨S, hS⟩,
    P.diagMeasure_apply v ⟨S ∩ D.1, hS.inter D.2⟩, P.map_inter ⟨S, hS⟩ D]
  rfl
theorem diagMeasure_real_univ (P : SpectralMeasure Y H) (v : H) :
    (P.diagMeasure v).real univ = ‖v‖ ^ 2 := by
  rw [Measure.real, P.diagMeasure_univ]
  exact ENNReal.toReal_ofReal (sq_nonneg _)
theorem integral_norm_sq_le_of_bound (P : SpectralMeasure Y H) {σ : Y → ℂ} (hσ : Measurable σ)
    {M : ℝ} (hM : ∀ x, ‖σ x‖ ≤ M) (v : H) :
    ∫ x, ‖σ x‖ ^ 2 ∂P.diagMeasure v ≤ M ^ 2 * ‖v‖ ^ 2 := by
  have hsq : ∀ x, ‖σ x‖ ^ 2 ≤ M ^ 2 := fun x => pow_le_pow_left₀ (norm_nonneg _) (hM x) 2
  have hint : Integrable (fun x => ‖σ x‖ ^ 2) (P.diagMeasure v) :=
    Integrable.of_bound (hσ.norm.pow_const 2).aestronglyMeasurable (M ^ 2)
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hsq x)
  refine (integral_mono hint (integrable_const _) hsq).trans_eq ?_
  rw [integral_const, smul_eq_mul, diagMeasure_real_univ, mul_comm]
structure Realizes (P : SpectralMeasure Y H) (σ : Y → ℂ) (A : H →L[ℂ] H) : Prop where
  measurable : Measurable σ
  bounded : IsBoundedFn σ
  diag : P.IsDiagonalIntegral σ A
  commute : ∀ D, Commute A (P D)
variable {P : SpectralMeasure Y H} {σ τ : Y → ℂ} {A B : H →L[ℂ] H}
theorem Realizes.eq (h₁ : Realizes P σ A) (h₂ : Realizes P σ B) : A = B :=
  ext_of_inner_self fun v => by rw [h₁.diag v, h₂.diag v]
theorem realizes_apply (P : SpectralMeasure Y H) (D : BorelSubsets Y) :
    Realizes P (D.1.indicator 1) (P D) where
  measurable := measurable_one.indicator D.2
  bounded := by
    refine ⟨1, fun x => ?_⟩
    by_cases hx : x ∈ D.1 <;> simp [hx]
  diag v := by
    have hone : D.1.indicator (1 : Y → ℂ) = D.1.indicator fun _ => (1 : ℂ) := rfl
    rw [P.inner_apply_self_eq_diagMeasure, hone, integral_indicator_const _ D.2]
    simp
  commute D' := commute_apply P D D'
theorem Realizes.add (hA : Realizes P σ A) (hB : Realizes P τ B) :
    Realizes P (σ + τ) (A + B) where
  measurable := hA.measurable.add hB.measurable
  bounded := by
    rcases hA.bounded with ⟨M, hM⟩
    rcases hB.bounded with ⟨K, hK⟩
    exact ⟨M + K, fun x => (norm_add_le (σ x) (τ x)).trans (add_le_add (hM x) (hK x))⟩
  diag v := by
    have iσ := integrable_of_isBoundedFn P hA.measurable hA.bounded v
    have iτ := integrable_of_isBoundedFn P hB.measurable hB.bounded v
    simp only [add_apply, inner_add_right, Pi.add_apply]
    rw [integral_add iσ iτ, hA.diag v, hB.diag v]
  commute D := (hA.commute D).add_left (hB.commute D)
theorem Realizes.smul (a : ℂ) (hA : Realizes P σ A) : Realizes P (a • σ) (a • A) where
  measurable := hA.measurable.const_smul a
  bounded := by
    rcases hA.bounded with ⟨M, hM⟩
    refine ⟨‖a‖ * M, fun x => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg a)
  diag v := by
    simp only [smul_apply, inner_smul_right, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, hA.diag v]
  commute D := (hA.commute D).smul_left a
theorem Realizes.congr (hA : Realizes P σ A) (he : σ = τ) : Realizes P τ A := by
  subst he
  exact hA
theorem Realizes.star (hA : Realizes P σ A) :
    Realizes P (conjFn σ) (Star.star A) where
  measurable := Complex.continuous_conj.measurable.comp hA.measurable
  bounded := by
    rcases hA.bounded with ⟨M, hM⟩
    refine ⟨M, fun x => ?_⟩
    simpa [conjFn] using hM x
  diag v := by
    have hadj : ⟪v, Star.star A v⟫_ℂ = conj ⟪v, A v⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
        inner_conj_symm]
    rw [hadj, hA.diag v]
    exact integral_conj.symm
  commute D := by
    have hproj : Star.star (P D) = P D := (P.isStarProjection D).isSelfAdjoint
    have hc := (hA.commute D).star_star
    rwa [hproj] at hc
theorem Realizes.mul_apply (hA : Realizes P σ A) (D : BorelSubsets Y) :
    Realizes P (D.1.indicator σ) (A * P D) where
  measurable := hA.measurable.indicator D.2
  bounded := by
    rcases hA.bounded with ⟨M, hM⟩
    exact ⟨M, fun x => (norm_indicator_le_norm_self σ x).trans (hM x)⟩
  diag v := by
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (P.isStarProjection D).isSelfAdjoint
    have hidem : P D (P D v) = P D v :=
      congrArg (fun R : H →L[ℂ] H => R v) (P.isStarProjection D).isIdempotentElem.eq
    have hcomm : A (P D (P D v)) = P D (A (P D v)) :=
      congrArg (fun R : H →L[ℂ] H => R (P D v)) (hA.commute D).eq
    have hmove : ⟪v, P D (A (P D v))⟫_ℂ = ⟪P D v, A (P D v)⟫_ℂ := by
      simpa only [ContinuousLinearMap.coe_coe] using (hsym v (A (P D v))).symm
    calc ⟪v, (A * P D) v⟫_ℂ = ⟪v, A (P D v)⟫_ℂ := rfl
      _ = ⟪v, P D (A (P D v))⟫_ℂ := by rw [← hcomm, hidem]
      _ = ⟪P D v, A (P D v)⟫_ℂ := hmove
      _ = ∫ x, D.1.indicator σ x ∂P.diagMeasure v := by
          rw [hA.diag, diagMeasure_apply_vec, integral_indicator D.2]
  commute D' := (hA.commute D').mul_left (commute_apply P D D')
theorem Realizes.of_tendsto {G : ℕ → Y → ℂ} {U : ℕ → H →L[ℂ] H} {C : H →L[ℂ] H}
    (hGU : ∀ k, Realizes P (G k) (U k)) (hU : Tendsto U atTop (𝓝 C)) (hτ : Measurable τ)
    (hτb : IsBoundedFn τ) {M : ℝ} (hM : ∀ k x, ‖G k x‖ ≤ M)
    (hG : ∀ x, Tendsto (fun k => G k x) atTop (𝓝 (τ x))) : Realizes P τ C where
  measurable := hτ
  bounded := hτb
  diag v := by
    have hcont : Continuous fun B : H →L[ℂ] H => ⟪v, B v⟫_ℂ := by fun_prop
    have hlhs : Tendsto (fun k => ∫ x, G k x ∂P.diagMeasure v) atTop (𝓝 ⟪v, C v⟫_ℂ) := by
      refine ((hcont.tendsto C).comp hU).congr fun k => ?_
      exact (hGU k).diag v
    have hrhs : Tendsto (fun k => ∫ x, G k x ∂P.diagMeasure v) atTop
        (𝓝 (∫ x, τ x ∂P.diagMeasure v)) :=
      tendsto_integral_of_dominated_convergence (fun _ => M)
        (fun k => (hGU k).measurable.aestronglyMeasurable) (integrable_const M)
        (fun k => Eventually.of_forall (hM k)) (Eventually.of_forall hG)
    exact tendsto_nhds_unique hlhs hrhs
  commute D := by
    have hr : Tendsto (fun k => U k * P D) atTop (𝓝 (C * P D)) := hU.mul_const _
    have hl : Tendsto (fun k => P D * U k) atTop (𝓝 (P D * C)) := hU.const_mul _
    show C * P D = P D * C
    refine tendsto_nhds_unique (hr.congr fun k => ?_) hl
    exact ((hGU k).commute D).eq
theorem exists_realizes_simpleFunc (P : SpectralMeasure Y H) (e : SimpleFunc Y ℂ) :
    ∃ A, Realizes P e A ∧ ∀ (τ : Y → ℂ) (B : H →L[ℂ] H), Realizes P τ B →
      Realizes P (τ * e) (B * A) := by
  induction e using SimpleFunc.induction with
  | const a hS =>
    rename_i S
    have hpw : ⇑(SimpleFunc.piecewise S hS (SimpleFunc.const Y a) (SimpleFunc.const Y 0)) =
        a • S.indicator (1 : Y → ℂ) := by
      funext x
      by_cases hx : x ∈ S <;> simp [hx]
    refine ⟨a • P ⟨S, hS⟩, ?_, fun τ B hB => ?_⟩
    · rw [hpw]
      exact (realizes_apply P ⟨S, hS⟩).smul a
    · have hprod : τ * ⇑(SimpleFunc.piecewise S hS (SimpleFunc.const Y a)
          (SimpleFunc.const Y 0)) = a • S.indicator τ := by
        funext x
        by_cases hx : x ∈ S <;> simp [hx, mul_comm]
      rw [hprod, mul_smul_comm]
      exact (hB.mul_apply ⟨S, hS⟩).smul a
  | add _ ih₁ ih₂ =>
    obtain ⟨A₁, hA₁, hm₁⟩ := ih₁
    obtain ⟨A₂, hA₂, hm₂⟩ := ih₂
    refine ⟨A₁ + A₂, ?_, fun τ B hB => ?_⟩
    · rw [SimpleFunc.coe_add]
      exact hA₁.add hA₂
    · rw [SimpleFunc.coe_add, mul_add, mul_add]
      exact (hm₁ τ B hB).add (hm₂ τ B hB)
theorem norm_sq_of_realizes_star_mul
    (hA : Realizes P (conjFn σ * σ) (star A * A)) (v : H) :
    ‖A v‖ ^ 2 = ∫ x, ‖σ x‖ ^ 2 ∂P.diagMeasure v := by
  have hl : ⟪v, (star A * A) v⟫_ℂ = ((‖A v‖ ^ 2 : ℝ) : ℂ) := by
    show ⟪v, star A (A v)⟫_ℂ = _
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hr : conjFn σ * σ = fun x => ((‖σ x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    simp [conjFn, Complex.conj_mul']
  have hd := hA.diag v
  rw [hl, hr, integral_complex_ofReal] at hd
  exact_mod_cast hd
theorem opNorm_le_of_simpleFunc (e : SimpleFunc Y ℂ) (hA : Realizes P e A) {M : ℝ} (hM₀ : 0 ≤ M)
    (hM : ∀ x, ‖e x‖ ≤ M) : ‖A‖ ≤ M := by
  obtain ⟨A', hA', hmul⟩ := exists_realizes_simpleFunc P e
  obtain rfl := hA'.eq hA
  refine ContinuousLinearMap.opNorm_le_bound _ hM₀ fun v => ?_
  have hsq := integral_norm_sq_le_of_bound P hA'.measurable hM v
  rw [← norm_sq_of_realizes_star_mul (hmul _ _ hA'.star) v, ← mul_pow] at hsq
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
theorem exists_simpleFunc_dist_le (hτ : Measurable τ) (hτb : IsBoundedFn τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : SimpleFunc Y ℂ, ∀ x, ‖e x - τ x‖ ≤ ε := by
  rcases hτb with ⟨M, hM⟩
  have hcover : Metric.closedBall (0 : ℂ) M ⊆
      ⋃ j, Metric.ball (TopologicalSpace.denseSeq ℂ j) ε := by
    intro w _
    rcases (TopologicalSpace.denseRange_denseSeq ℂ).exists_dist_lt w hε with ⟨j, hj⟩
    exact mem_iUnion.2 ⟨j, Metric.mem_ball.2 hj⟩
  rcases (isCompact_closedBall (0 : ℂ) M).elim_finite_subcover _
    (fun _ => Metric.isOpen_ball) hcover with ⟨J, hJ⟩
  refine ⟨(SimpleFunc.nearestPt (TopologicalSpace.denseSeq ℂ) (J.sup id)).comp τ hτ,
    fun x => ?_⟩
  have hx : τ x ∈ Metric.closedBall (0 : ℂ) M := by simpa using hM x
  rcases mem_iUnion₂.1 (hJ hx) with ⟨j, hjJ, hxj⟩
  have hnear := SimpleFunc.edist_nearestPt_le (TopologicalSpace.denseSeq ℂ) (τ x)
    (Finset.le_sup (f := id) hjJ)
  rw [edist_dist, edist_dist] at hnear
  have hle := (ENNReal.ofReal_le_ofReal_iff dist_nonneg).1 hnear
  rw [← dist_eq_norm]
  exact hle.trans ((dist_comm _ _).le.trans (Metric.mem_ball.1 hxj).le)
theorem exists_simpleFunc_approx (P : SpectralMeasure Y H) (hτ : Measurable τ)
    (hτb : IsBoundedFn τ) :
    ∃ (e : ℕ → SimpleFunc Y ℂ) (U : ℕ → H →L[ℂ] H) (C : H →L[ℂ] H),
      (∀ k, Realizes P (e k) (U k)) ∧ (∀ k x, ‖e k x - τ x‖ ≤ 1 / ((k : ℝ) + 1)) ∧
      Tendsto U atTop (𝓝 C) ∧ Realizes P τ C := by
  have hδ : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun _ => Nat.one_div_pos_of_nat
  have hanti : ∀ {j k : ℕ}, j ≤ k → 1 / ((k : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := fun hjk =>
    Nat.one_div_le_one_div hjk
  have hsmall : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  choose e he using fun k : ℕ => exists_simpleFunc_dist_le hτ hτb (hδ k)
  choose U hU _ using fun k => exists_realizes_simpleFunc P (e k)
  have hdist : ∀ j k N : ℕ, N ≤ j → N ≤ k → dist (U j) (U k) ≤ 2 * (1 / ((N : ℝ) + 1)) := by
    intro j k N hj hk
    have hdiff : Realizes P ⇑(e j - e k) (U j - U k) := by
      have hsum := (hU j).add ((hU k).smul (-1))
      rw [SimpleFunc.coe_sub]
      convert hsum using 1
      · funext x
        simp [sub_eq_add_neg]
      · simp [sub_eq_add_neg]
    rw [dist_eq_norm]
    refine opNorm_le_of_simpleFunc (e j - e k) hdiff (by positivity) fun x => ?_
    rw [SimpleFunc.coe_sub, Pi.sub_apply,
      show e j x - e k x = (e j x - τ x) - (e k x - τ x) by ring]
    linarith [norm_sub_le (e j x - τ x) (e k x - τ x), (he j x).trans (hanti hj),
      (he k x).trans (hanti hk)]
  have hcauchy : CauchySeq U :=
    cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 * (1 / ((N : ℝ) + 1))) hdist
      (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2)
  obtain ⟨C, hC⟩ := cauchySeq_tendsto_of_complete hcauchy
  rcases hτb with ⟨M, hM⟩
  have hpt : ∀ x, Tendsto (fun k => e k x) atTop (𝓝 (τ x)) := fun x => by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => he k x)
      tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨e, U, C, hU, he, hC,
    Realizes.of_tendsto hU hC hτ ⟨M, hM⟩ (M := M + 1) (fun k x => ?_) hpt⟩
  show ‖e k x‖ ≤ M + 1
  have htri : ‖e k x‖ ≤ ‖e k x - τ x‖ + ‖τ x‖ := by
    simpa using norm_add_le (e k x - τ x) (τ x)
  linarith [he k x, hsmall k, hM x]
theorem Realizes.mul (hA : Realizes P σ A) (hB : Realizes P τ B) :
    Realizes P (σ * τ) (A * B) := by
  obtain ⟨e, U, C, hU, he, hC, hτC⟩ := exists_simpleFunc_approx P hB.measurable hB.bounded
  obtain rfl := hτC.eq hB
  rcases hA.bounded with ⟨M, hM⟩
  rcases hB.bounded with ⟨K, hK⟩
  have hstep : ∀ k, Realizes P (σ * e k) (A * U k) := fun k => by
    obtain ⟨A', hA', hmul⟩ := exists_realizes_simpleFunc P (e k)
    obtain rfl := hA'.eq (hU k)
    exact hmul σ A hA
  have hM₀ : ∀ x, 0 ≤ M := fun x => (norm_nonneg _).trans (hM x)
  have hek : ∀ k x, ‖e k x‖ ≤ K + 1 := fun k x => by
    have htri : ‖e k x‖ ≤ ‖e k x - τ x‖ + ‖τ x‖ := by
      simpa using norm_add_le (e k x - τ x) (τ x)
    have hsmall : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    linarith [hK x, he k x]
  refine Realizes.of_tendsto hstep (hC.const_mul A) (hA.measurable.mul hB.measurable)
    ⟨M * K, fun x => ?_⟩ (M := M * (K + 1)) (fun k x => ?_) (fun x => ?_)
  · rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hM x) (hK x) (norm_nonneg _) (hM₀ x)
  · show ‖σ x * e k x‖ ≤ M * (K + 1)
    rw [norm_mul]
    exact mul_le_mul (hM x) (hek k x) (norm_nonneg _) (hM₀ x)
  · have hlim : Tendsto (fun k => e k x) atTop (𝓝 (τ x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _) (fun k => he k x)
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact hlim.const_mul (σ x)
theorem realizes_integralOp (P : SpectralMeasure Y H) (hτ : Measurable τ)
    (hτb : IsBoundedFn τ) : Realizes P τ (P.integralOp τ) := by
  obtain ⟨-, -, C, -, -, -, hC⟩ := exists_simpleFunc_approx P hτ hτb
  have hspec : P.IsDiagonalIntegral τ (P.integralOp τ) :=
    Classical.epsilon_spec (p := P.IsDiagonalIntegral τ) ⟨C, hC.diag⟩
  have hop : P.integralOp τ = C := ext_of_inner_self fun v => by rw [hspec v, hC.diag v]
  rw [hop]
  exact hC
theorem Realizes.integralOp_eq (hA : Realizes P τ A) : P.integralOp τ = A :=
  (realizes_integralOp P hA.measurable hA.bounded).eq hA
theorem Realizes.norm_sq (hA : Realizes P τ A) (v : H) :
    ‖A v‖ ^ 2 = ∫ x, ‖τ x‖ ^ 2 ∂P.diagMeasure v :=
  norm_sq_of_realizes_star_mul (hA.star.mul hA) v
theorem inner_eq_polarizedIntegral (P : SpectralMeasure Y H)
    (hA : P.IsDiagonalIntegral τ A) (w v : H) : ⟪w, A v⟫_ℂ = P.polarizedIntegral τ w v := by
  have hexp : ∀ a : ℂ, ⟪w + a • v, A (w + a • v)⟫_ℂ = ⟪w, A w⟫_ℂ + a * ⟪w, A v⟫_ℂ +
      conj a * ⟪v, A w⟫_ℂ + conj a * a * ⟪v, A v⟫_ℂ := fun a => by
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right]
    ring
  have i2 := Complex.I_sq
  have i3 : Complex.I ^ 3 = -Complex.I := Complex.I_pow_three
  have j2 : (-Complex.I) ^ 2 = -1 := by rw [neg_sq, i2]
  have j3 : (-Complex.I) ^ 3 = Complex.I := by rw [Odd.neg_pow (by decide), i3, neg_neg]
  simp only [SpectralMeasure.polarizedIntegral, ← hA _, Finset.sum_range_succ,
    Finset.sum_range_zero, pow_zero, pow_one, i2, i3, j2, j3, zero_add, hexp, map_one, map_neg,
    Complex.conj_I, neg_neg]
  linear_combination ((⟪w, A v⟫_ℂ - ⟪v, A w⟫_ℂ) / 2) * i2
theorem boundedFunctionalCalculus (P : SpectralMeasure Y H) : BoundedFunctionalCalculus P where
  existsUnique_op σ hσ hσb := by
    have hr := realizes_integralOp P hσ hσb
    refine ⟨P.integralOp σ, hr.diag, fun B hB => ext_of_inner_self fun v => ?_⟩
    rw [hB v, hr.diag v]
  indicator D := (realizes_apply P D).integralOp_eq
  add σ τ hσ hσb hτ hτb :=
    ((realizes_integralOp P hσ hσb).add (realizes_integralOp P hτ hτb)).integralOp_eq
  smul a σ hσ hσb := ((realizes_integralOp P hσ hσb).smul a).integralOp_eq
  mul σ τ hσ hσb hτ hτb :=
    ((realizes_integralOp P hσ hσb).mul (realizes_integralOp P hτ hτb)).integralOp_eq
  star_eq σ hσ hσb := (realizes_integralOp P hσ hσb).star.integralOp_eq
  inner_eq σ hσ hσb w v := inner_eq_polarizedIntegral P (realizes_integralOp P hσ hσb).diag w v
  diagMeasure_eq σ hσ hσb v D := by
    have hr := realizes_integralOp P hσ hσb
    have hswap : P D (P.integralOp σ v) = P.integralOp σ (P D v) :=
      congrArg (fun R : H →L[ℂ] H => R v) (hr.commute D).eq.symm
    rw [P.diagMeasure_apply _ D, hswap, hr.norm_sq, diagMeasure_apply_vec]
    rcases hσb with ⟨M, hM⟩
    have hint : Integrable (fun x => ‖σ x‖ ^ 2) ((P.diagMeasure v).restrict D.1) :=
      Integrable.of_bound (hσ.norm.pow_const 2).aestronglyMeasurable (M ^ 2)
        (Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hM x) 2)
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  norm_sq σ hσ hσb v := (realizes_integralOp P hσ hσb).norm_sq v
  integral_le σ hσ hσb v := by
    rcases hσb with ⟨M, hM⟩
    have hbdd : BddAbove (range fun x => ‖σ x‖) := by
      refine ⟨M, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hM x
    exact integral_norm_sq_le_of_bound P hσ (fun x => le_ciSup hbdd x) v
  isSelfAdjoint σ hσ hσb hre := by
    have hr := realizes_integralOp P hσ hσb
    have hfix : conjFn σ = σ := funext fun x => Complex.conj_eq_iff_im.2 (hre x)
    exact (hr.star.congr hfix).eq hr
  isPositive σ hσ hσb hpos := by
    have hr := realizes_integralOp P hσ hσb
    have hfix : conjFn σ = σ :=
      funext fun x => Complex.conj_eq_iff_im.2 (Complex.le_def.1 (hpos x)).2.symm
    refine ⟨(hr.star.congr hfix).eq hr, fun v => ?_⟩
    have hreal : σ = fun x => (((σ x).re : ℝ) : ℂ) :=
      funext fun x => Complex.ext rfl (by simpa using (Complex.le_def.1 (hpos x)).2.symm)
    rw [hr.diag v, hreal, integral_complex_ofReal]
    exact Complex.zero_le_real.2 (integral_nonneg fun x => (Complex.le_def.1 (hpos x)).1)
  isUnitary σ hσ hunit := by
    have hσb : IsBoundedFn σ := ⟨1, fun x => (hunit x).le⟩
    have hr := realizes_integralOp P hσ hσb
    have hid : Realizes P (1 : Y → ℂ) 1 := by
      have hu := realizes_apply P ⟨univ, MeasurableSet.univ⟩
      rw [P.map_univ] at hu
      exact hu.congr (by simp)
    refine ⟨((hr.star.mul hr).congr ?_).eq hid, ((hr.mul hr.star).congr ?_).eq hid⟩
    · funext x
      simp [conjFn, Complex.conj_mul', hunit x]
    · funext x
      simp [conjFn, Complex.mul_conj', hunit x]
  diagMeasure_compl D v hv := by
    obtain ⟨w, rfl⟩ := hv
    have hDc : (⟨D.1ᶜ ∩ D.1, D.2.compl.inter D.2⟩ : BorelSubsets Y) =
        ⟨∅, MeasurableSet.empty⟩ := Subtype.ext (compl_inter_self _)
    have hzero : P ⟨D.1ᶜ, D.2.compl⟩ (P D w) = 0 := by
      have hm := P.map_inter ⟨D.1ᶜ, D.2.compl⟩ D
      rw [hDc, P.apply_empty] at hm
      exact (congrArg (fun R : H →L[ℂ] H => R w) hm).symm
    have hval := P.diagMeasure_apply (P D w) ⟨D.1ᶜ, D.2.compl⟩
    simpa [hzero] using hval
  apply_empty := P.apply_empty
  apply_subset D D' hD hsub := by
    have hm := P.map_inter D' D
    have hsame : (⟨D'.1 ∩ D.1, D'.2.inter D.2⟩ : BorelSubsets Y) = D' :=
      Subtype.ext (inter_eq_left.2 hsub)
    rw [hsame] at hm
    show P.toFun D' = 0
    rw [hm]
    show P D' * P D = 0
    rw [hD, mul_zero]
  apply_iUnion ι _ D hD := by
    ext v
    have hnull : ∀ i, P.diagMeasure v (D i).1 = 0 := fun i => by
      rw [P.diagMeasure_apply v (D i), hD i]
      simp
    have hU := measure_iUnion_null hnull
    rw [P.diagMeasure_apply v ⟨⋃ i, (D i).1, MeasurableSet.iUnion fun i => (D i).2⟩] at hU
    have hsq := ENNReal.ofReal_eq_zero.1 hU
    have hnorm : ‖P ⟨⋃ i, (D i).1, MeasurableSet.iUnion fun i => (D i).2⟩ v‖ = 0 := by
      nlinarith [norm_nonneg (P ⟨⋃ i, (D i).1, MeasurableSet.iUnion fun i => (D i).2⟩ v)]
    simpa using hnorm
theorem boundedBorelCalculusHolds :
    SpectralTheory.BoundedBorelCalculus.BoundedBorelCalculusHolds :=
  fun _ _ _ _ _ _ P => boundedFunctionalCalculus P
end YangMills.Construction.BorelCalculus.OfSpectralMeasure
