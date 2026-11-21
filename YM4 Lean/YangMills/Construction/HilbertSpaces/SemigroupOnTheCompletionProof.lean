import YangMills.Construction.HilbertSpaces.BoundedFunctionalsBoundedFormsAdjointsAndOrthogonalVectors
import YangMills.Construction.HilbertSpaces.SemigroupOnTheCompletion
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ComplexOrder InnerProductSpace
open YangMills.Construction.FormsOperators
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction.SemigroupOnCompletion
theorem le_of_sq_le_mul_succ (N σ : ℝ) (a : ℕ → ℝ) (hN : 0 ≤ N) (ha : ∀ k, 0 ≤ a k)
    (h : ∀ k, a k ^ 2 ≤ N * a (k + 1)) (hb : ∀ k, a k ^ 2 ≤ σ) : a 0 ≤ N := by
  by_contra hlt
  rw [not_le] at hlt
  have hN0 : 0 < N := by
    rcases hN.eq_or_lt with h0 | h0
    · exfalso
      have h1 := h 0
      rw [← h0, zero_mul] at h1
      have h2 : a 0 = 0 := by
        have : a 0 ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      linarith
    · exact h0
  have ha0 : 0 < a 0 := lt_of_le_of_lt hN hlt
  have hr1 : 1 < a 0 / N := by rwa [one_lt_div hN0]
  have key : ∀ k, a 0 * (a 0 / N) ^ k ≤ a k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : a 0 ≤ a k :=
        le_trans (le_mul_of_one_le_right ha0.le (one_le_pow₀ hr1.le)) ih
      have h2 : a k * a 0 ≤ N * a (k + 1) := by nlinarith [h k, ha k]
      have h3 : a k * (a 0 / N) ≤ a (k + 1) := by
        rw [mul_div_assoc', div_le_iff₀ hN0]
        linarith
      calc a 0 * (a 0 / N) ^ (k + 1) = a 0 * (a 0 / N) ^ k * (a 0 / N) := by ring
        _ ≤ a k * (a 0 / N) := mul_le_mul_of_nonneg_right ih (by positivity)
        _ ≤ a (k + 1) := h3
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((σ + 1) / a 0) hr1
  have h1 : σ + 1 < a 0 * (a 0 / N) ^ n := by
    rwa [div_lt_iff₀' ha0] at hn
  have h2 := key n
  nlinarith [hb n, sq_nonneg (a n - 1), sq_nonneg (a n)]
section Forms
variable {V : Type} [AddCommGroup V] [Module ℂ V] (S : PreHilbertData V)
theorem qNorm_sq (h : S.IsAdmissible) (F : V) :
    qNorm S.form F ^ 2 = (S.form F F).re :=
  Real.sq_sqrt (Complex.nonneg_iff.mp (h.posSemidef.nonneg F)).1
theorem form_semigroupMap_semigroupMap (h : S.IsAdmissible) (s : ℝ≥0) (F : V) :
    S.form (S.semigroupMap s F) (S.semigroupMap s F) = S.form F (S.semigroupMap (s + s) F) := by
  rw [← h.form_semigroupMap, ← h.semigroupMap_comp]
  rfl
theorem qNorm_semigroupMap_le (hQ : PosFormQuotient) (h : S.IsAdmissible) (t : ℝ≥0)
    (F : V) : qNorm S.form (S.semigroupMap t F) ≤ qNorm S.form F := by
  obtain ⟨σ, hσ⟩ := h.bddAbove_semigroup F
  have hσ' : ∀ s, ‖S.form F (S.semigroupMap s F)‖ ≤ σ := fun s => hσ (mem_range_self s)
  have hcs := (hQ V S.form h.hermitian h.posSemidef).1
  have hre : ∀ s : ℝ≥0, qNorm S.form (S.semigroupMap s F) ^ 2 ≤
      ‖S.form F (S.semigroupMap (s + s) F)‖ := fun s => by
    rw [qNorm_sq S h, form_semigroupMap_semigroupMap S h]
    exact Complex.re_le_norm _
  refine le_of_sq_le_mul_succ (qNorm S.form F) σ
    (fun k => qNorm S.form (S.semigroupMap (2 ^ k * t) F)) (Real.sqrt_nonneg _)
    (fun k => Real.sqrt_nonneg _) (fun k => ?_) (fun k => (hre _).trans (hσ' _)) |>.trans' ?_
  · refine (hre _).trans ((hcs _ _).trans (le_of_eq ?_))
    rw [pow_succ, mul_two, add_mul]
  · simp
end Forms
section Classes
variable {V : Type} [AddCommGroup V] [Module ℂ V] (S : PreHilbertData V) (hq : IsSesquilinear S.form)
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (j : (V ⧸ formRadical S.form hq) →ₗ[ℂ] H)
def embedLinear : V →ₗ[ℂ] H := j ∘ₗ (formRadical S.form hq).mkQ
omit [CompleteSpace H] in
theorem embedLinear_apply (F : V) : embedLinear S hq j F = embed S hq j F := rfl
theorem denseRange_embed (hc : IsHilbertCompletion (formOnQuotient S.form hq) j) :
    DenseRange (embed S hq j) := by
  have h1 : range (embed S hq j) = range j := by
    have : embed S hq j = j ∘ (Submodule.Quotient.mk : V → V ⧸ formRadical S.form hq) := rfl
    rw [this, Function.Surjective.range_comp (Submodule.Quotient.mk_surjective _)]
  have h2 : Dense (range j) := (isDenseSet_iff_dense _).mp hc.dense_range
  rw [DenseRange, h1]
  exact h2
theorem inner_embed (hc : IsHilbertCompletion (formOnQuotient S.form hq) j)
    (hm : ∀ F F' : V, formOnQuotient S.form hq (Submodule.Quotient.mk F) (Submodule.Quotient.mk F') =
      S.form F F') (F F' : V) :
    ⟪embed S hq j F, embed S hq j F'⟫_ℂ = S.form F F' := by
  rw [← hm]
  exact hc.inner_map _ _
theorem exists_clm_extends (hE : DenseExtension) (hc : IsHilbertCompletion (formOnQuotient S.form hq) j)
    (R : V →ₗ[ℂ] V) (hR : ∀ F, ‖embed S hq j (R F)‖ ≤ ‖embed S hq j F‖) :
    ∃ B : H →L[ℂ] H, CLMExtends S hq j R B := by
  have hker : LinearMap.ker (embedLinear S hq j) ≤ LinearMap.ker (embedLinear S hq j ∘ₗ R) := by
    intro F hF
    rw [LinearMap.mem_ker] at hF ⊢
    have h1 := hR F
    rw [← embedLinear_apply, ← embedLinear_apply, hF, norm_zero] at h1
    simpa using h1
  let L := (LinearMap.ker (embedLinear S hq j)).liftQ (embedLinear S hq j ∘ₗ R) hker
  let B₀ : LinearMap.range (embedLinear S hq j) →ₗ[ℂ] H :=
    L ∘ₗ (embedLinear S hq j).quotKerEquivRange.symm.toLinearMap
  have hB₀ : ∀ (F : V) (hF : embedLinear S hq j F ∈ LinearMap.range (embedLinear S hq j)),
      B₀ ⟨embedLinear S hq j F, hF⟩ = embed S hq j (R F) := by
    intro F hF
    simp only [B₀, L, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image (embedLinear S hq j) F hF]
    rfl
  have hdense : IsDenseSet ((LinearMap.range (embedLinear S hq j) : Submodule ℂ H) : Set H) := by
    rw [isDenseSet_iff_dense]
    have h1 := denseRange_embed S hq j hc
    rw [DenseRange] at h1
    have h2 : ((LinearMap.range (embedLinear S hq j) : Submodule ℂ H) : Set H) =
        range (embed S hq j) := LinearMap.coe_range _
    rw [h2]
    exact h1
  obtain ⟨B, hB, -⟩ := hE H H (LinearMap.range (embedLinear S hq j)) 1 B₀ hdense zero_le_one (by
    rintro ⟨x, hx⟩
    obtain ⟨F, rfl⟩ := LinearMap.mem_range.mp hx
    rw [hB₀ F hx, one_mul]
    exact hR F)
  refine ⟨B, fun F => ?_⟩
  have h1 := hB ⟨embedLinear S hq j F, LinearMap.mem_range_self _ F⟩
  rw [hB₀ F (LinearMap.mem_range_self _ F)] at h1
  exact h1
end Classes
section Semigroup
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
omit [CompleteSpace H] in
theorem continuous_of_tendsto_at_zero (T : ℝ≥0 → H →L[ℂ] H) (hadd : ∀ t t', T t * T t' = T (t + t'))
    (hcontr : ∀ t ψ, ‖T t ψ‖ ≤ ‖ψ‖) (ψ : H) (h0 : Tendsto (fun t => T t ψ) (𝓝 0) (𝓝 ψ)) :
    Continuous fun t => T t ψ := by
  have hstep : ∀ s d, ‖T (s + d) ψ - T s ψ‖ ≤ ‖T d ψ - ψ‖ := fun s d => by
    have h1 : T (s + d) ψ - T s ψ = T s (T d ψ - ψ) := by
      rw [← hadd, map_sub]
      rfl
    rw [h1]
    exact hcontr _ _
  have hbound : ∀ t t₀, ‖T t ψ - T t₀ ψ‖ ≤ ‖T (nndist t t₀) ψ - ψ‖ := fun t t₀ => by
    rcases le_total t₀ t with hle | hle
    · obtain ⟨d, rfl⟩ := exists_add_of_le hle
      have : nndist (t₀ + d) t₀ = d := by
        rw [NNReal.nndist_eq, add_tsub_cancel_left, tsub_eq_zero_of_le le_self_add,
          max_eq_left zero_le]
      rw [this]
      exact hstep _ _
    · obtain ⟨d, rfl⟩ := exists_add_of_le hle
      have : nndist t (t + d) = d := by
        rw [NNReal.nndist_eq, add_tsub_cancel_left, tsub_eq_zero_of_le le_self_add,
          max_eq_right zero_le]
      rw [this, norm_sub_rev]
      exact hstep _ _
  rw [continuous_iff_continuousAt]
  intro t₀
  have hd : Tendsto (fun t => nndist t t₀) (𝓝 t₀) (𝓝 0) := by
    have h1 : Continuous fun t : ℝ≥0 => nndist t t₀ := continuous_id.nndist continuous_const
    have h2 := h1.tendsto t₀
    simpa using h2
  have h1 : Tendsto (fun t => ‖T (nndist t t₀) ψ - ψ‖) (𝓝 t₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (h0.comp hd)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) (fun t => hbound t t₀) h1)
theorem tendsto_nhds_zero_of_nhdsGT {X : Type*} [TopologicalSpace X] (f : ℝ≥0 → X) (x : X)
    (h0 : f 0 = x) (h : Tendsto f (𝓝[>] 0) (𝓝 x)) : Tendsto f (𝓝 0) (𝓝 x) := by
  have h1 : (univ : Set ℝ≥0) = {0} ∪ Ioi 0 := by
    ext t
    simp
  rw [← nhdsWithin_univ, h1, nhdsWithin_union, nhdsWithin_singleton]
  refine Tendsto.sup ?_ h
  rw [tendsto_pure_left]
  intro s hs
  rw [h0]
  exact mem_of_mem_nhds hs
end Semigroup
theorem transfer_semigroup_properties {V : Type} [AddCommGroup V] [Module ℂ V] (S : PreHilbertData V)
    (h : S.IsAdmissible) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (c : V → H) (hd : DenseRange c)
    (hin : ∀ F F', ⟪c F, c F'⟫_ℂ = S.form F F') (hnorm : ∀ F, ‖c F‖ = qNorm S.form F)
    (hle : ∀ t F, qNorm S.form (S.semigroupMap t F) ≤ qNorm S.form F)
    (T : ℝ≥0 → H →L[ℂ] H) (hext : ∀ t F, T t (c F) = c (S.semigroupMap t F))
    (hB : ∀ B : H →L[ℂ] H,
      IsSelfAdj (ofCLM B) ↔ ∀ φ ψ, ⟪φ, B ψ⟫_ℂ = ⟪B φ, ψ⟫_ℂ) :
    IsC0Semigroup T ∧
      (∀ t, IsPositiveBounded (T t) ∧ IsSelfAdj (ofCLM (T t)) ∧
        IsContractive (T t)) ∧
      ∀ t, T t (c S.unitVec) = c S.unitVec := by
  have hcontr : ∀ t ψ, ‖T t ψ‖ ≤ ‖ψ‖ := fun t ψ => by
    refine hd.induction_on (p := fun ψ => ‖T t ψ‖ ≤ ‖ψ‖) ψ
      (isClosed_le (T t).continuous.norm continuous_norm) fun F => ?_
    rw [hext, hnorm, hnorm]
    exact hle t F
  have hzero : T 0 = 1 := ContinuousLinearMap.ext fun ψ =>
    hd.induction_on (p := fun ψ => T 0 ψ = (1 : H →L[ℂ] H) ψ) ψ
      (isClosed_eq (T 0).continuous (1 : H →L[ℂ] H).continuous) fun F => by
        rw [hext, h.semigroupMap_zero]
        rfl
  have hadd : ∀ t t', T t * T t' = T (t + t') := fun t t' => ContinuousLinearMap.ext fun ψ =>
    hd.induction_on (p := fun ψ => (T t * T t') ψ = T (t + t') ψ) ψ
      (isClosed_eq (T t * T t').continuous (T (t + t')).continuous) fun F => by
        rw [ContinuousLinearMap.mul_apply, hext, hext, hext, ← h.semigroupMap_comp]
        rfl
  have hsym : ∀ t φ ψ, ⟪φ, T t ψ⟫_ℂ = ⟪T t φ, ψ⟫_ℂ := fun t φ ψ =>
    hd.induction_on₂ (p := fun φ ψ => ⟪φ, T t ψ⟫_ℂ = ⟪T t φ, ψ⟫_ℂ)
      (isClosed_eq (continuous_fst.inner ((T t).continuous.comp continuous_snd))
        (((T t).continuous.comp continuous_fst).inner continuous_snd))
      (fun F F' => by
        rw [hext, hext, hin, hin]
        exact h.form_semigroupMap t F F') φ ψ
  have hpos : ∀ t ψ, 0 ≤ ⟪ψ, T t ψ⟫_ℂ := fun t ψ => by
    have h1 : T t ψ = T (t / 2) (T (t / 2) ψ) := by
      rw [← ContinuousLinearMap.mul_apply, hadd, add_halves]
    rw [h1, hsym]
    exact Complex.nonneg_iff.mpr ⟨inner_self_nonneg (𝕜 := ℂ), (inner_self_im (𝕜 := ℂ) _).symm⟩
  have hclass : ∀ F, Tendsto (fun t => T t (c F)) (𝓝[>] 0) (𝓝 (c F)) := fun F => by
    have hg := h.tendsto_semigroup F
    have hdbl : Tendsto (fun t : ℝ≥0 => t + t) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h1 : Continuous fun t : ℝ≥0 => t + t := continuous_id.add continuous_id
        have h2 := h1.tendsto 0
        simp only [add_zero] at h2
        exact h2.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mem_Ioi.mpr (add_pos (mem_Ioi.mp ht) (mem_Ioi.mp ht))
    have hre : Tendsto (fun t => (S.form F (S.semigroupMap (t + t) F)).re -
        2 * (S.form F (S.semigroupMap t F)).re + (S.form F F).re) (𝓝[>] 0) (𝓝 0) := by
      have h1 := (Complex.continuous_re.tendsto _).comp (hg.comp hdbl)
      have h2 := (Complex.continuous_re.tendsto _).comp hg
      have h3 := (h1.sub (h2.const_mul 2)).add_const (S.form F F).re
      have h4 : (S.form F F).re - 2 * (S.form F F).re + (S.form F F).re = 0 := by ring
      rw [h4] at h3
      exact h3
    have hsq : ∀ t, ‖T t (c F) - c F‖ ^ 2 = (S.form F (S.semigroupMap (t + t) F)).re -
        2 * (S.form F (S.semigroupMap t F)).re + (S.form F F).re := fun t => by
      rw [norm_sub_sq (𝕜 := ℂ), hext, hnorm, hnorm, qNorm_sq S h, qNorm_sq S h,
        form_semigroupMap_semigroupMap S h, hin, ← h.form_semigroupMap]
      rfl
    have hn : Tendsto (fun t => ‖T t (c F) - c F‖) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun t => ‖T t (c F) - c F‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
        simp only [hsq]
        exact hre
      have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
      simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h2
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hn
  have hright : ∀ ψ, Tendsto (fun t => T t ψ) (𝓝[>] 0) (𝓝 ψ) := fun ψ => by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨F, hF⟩ := hd.exists_dist_lt ψ (show 0 < ε / 3 by positivity)
    have h1 := (Metric.tendsto_nhds.mp (hclass F)) (ε / 3) (by positivity)
    filter_upwards [h1] with t ht
    rw [dist_eq_norm] at hF ht ⊢
    have h2 : T t ψ - ψ = T t (ψ - c F) + (T t (c F) - c F) + (c F - ψ) := by
      rw [map_sub]
      abel
    have h3 := hcontr t (ψ - c F)
    have h4 : ‖c F - ψ‖ = ‖ψ - c F‖ := norm_sub_rev _ _
    rw [h2]
    calc _ ≤ ‖T t (ψ - c F)‖ + ‖T t (c F) - c F‖ + ‖c F - ψ‖ := norm_add₃_le
      _ < ε := by linarith
  refine ⟨⟨hzero, hadd, fun ψ => continuous_of_tendsto_at_zero T hadd hcontr ψ
      (tendsto_nhds_zero_of_nhdsGT _ _ (by rw [hzero]; rfl) (hright ψ))⟩,
    fun t => ⟨hpos t, (hB (T t)).mpr (hsym t), hcontr t⟩, fun t => ?_⟩
  rw [hext, h.semigroupMap_unitVec]
theorem transferSemigroupSpec_holds (h₁ : FormsAndCompletions)
    (h₂ : BoundedRepresentation.Claim) : TransferSemigroupSpec := by
  intro V _ _ S h H _ _ _ j hc
  obtain ⟨-, hQ, hE, -⟩ := h₁
  have hm := (hQ V S.form h.hermitian h.posSemidef).2.2.2.2.1
  have hq : IsSesquilinear S.form := h.hermitian.toIsSesquilinear
  have hin := inner_embed S hq j hc hm
  have hnorm : ∀ F, ‖embed S hq j F‖ = qNorm S.form F := fun F => by
    have h1 : ‖embed S hq j F‖ ^ 2 = (S.form F F).re := by
      rw [← hin F F]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    rw [qNorm, ← h1, Real.sqrt_sq (norm_nonneg _)]
  have hle := qNorm_semigroupMap_le S hQ h
  have hext : ∀ t, CLMExtends S hq j (S.semigroupMap t) (transferOp S hq j t) := fun t =>
    Classical.epsilon_spec (exists_clm_extends S hq j hE hc (S.semigroupMap t) fun F => by
      rw [hnorm, hnorm]
      exact hle t F)
  exact ⟨hext, transfer_semigroup_properties S h (embed S hq j) (denseRange_embed S hq j hc) hin
    hnorm hle (transferOp S hq j) (fun t F => hext t F) (fun B => ((h₂ H 0 le_rfl).2.2.2.1 B).2)⟩
end YangMills.Construction.PositiveFormReconstruction.SemigroupOnCompletion
