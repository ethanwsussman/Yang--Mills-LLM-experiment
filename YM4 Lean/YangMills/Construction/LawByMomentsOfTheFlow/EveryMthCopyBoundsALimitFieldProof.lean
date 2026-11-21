import YangMills.Construction.LawByMomentsOfTheFlow.EveryMthCopyBoundsALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.MeansOfALimitField
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace YangMills.Construction.MomentMethod
private theorem sum_range_mul_split (m : ℕ) (h : ℕ → ℝ) (M : ℕ) :
    ∑ t ∈ Finset.range (m * M), h t = ∑ r ∈ Finset.range m, ∑ k ∈ Finset.range M, h (m * k + r) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_range_succ]
private theorem translateShift_iterate_apply {J : Type} (r : ℕ) (v : TranslateValues J) (a : J × ℕ) :
    ((translateShift (J := J))^[r] v) a = v (a.1, a.2 + r) := by
  induction r generalizing v a with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply, ih]
    show v ((a.1, a.2 + r).1, (a.1, a.2 + r).2 + 1) = _
    simp only [Nat.add_assoc]
theorem multipleTranslatesBound (hM : jointLimitPropertiesStatement) : multipleTranslatesBoundStatement := by
  intro T J _ X P hT hX hP j b C₀ Cb m hm hb hbd hq
  haveI := hP.isProbability
  let T' : TranslatedLaws := { Ω := T.Ω, μ := T.μ, τ := fun i => (T.τ i)^[m] }
  have hT' : T'.IsPreserving := ⟨hT.isProbability, fun i => (hT.measurePreserving i).iterate m⟩
  let φ : TranslateValues J → TranslateValues J := fun v a => v (a.1, m * a.2)
  have hφ : Measurable φ := measurable_pi_lambda _ fun a => measurable_pi_apply _
  obtain ⟨hS, -, -, h4, -, -⟩ := hM T J X P hT hX hP
  let P' : Measure (TranslateValues J) := P.map φ
  let X' : J → T'.Family := X
  have hX' : ∀ j, TranslatedLaws.HasBoundedMoments (X' j) := fun j => ⟨(hX j).aemeasurable, (hX j).moment_bound⟩
  have htr : ∀ (Y : T.Family) (k i : ℕ) (ω : T.Ω i), TranslatedLaws.translate (T := T') Y k i ω = TranslatedLaws.translate (T := T) Y (m * k) i ω := by
    intro Y k i ω
    show Y i (((T.τ i)^[m])^[k] ω) = Y i ((T.τ i)^[m * k] ω)
    rw [Function.iterate_mul]
  have hP' : IsJointLimitLaw T' X' P' := by
    refine ⟨Measure.isProbabilityMeasure_map hφ.aemeasurable, fun l a G hG hb' => ?_⟩
    have h1 := hP.tendsto l (fun c => ((a c).1, m * (a c).2)) G hG hb'
    have e1 : ∫ v, G (fun c => v (a c)) ∂P' = ∫ v, G (fun c => v ((a c).1, m * (a c).2)) ∂P := by
      refine integral_map hφ.aemeasurable ?_
      exact (hG.measurable.comp (measurable_pi_lambda _ fun c => measurable_pi_apply _)).aestronglyMeasurable
    rw [e1]
    refine h1.congr fun i => integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show G _ = G _
    congr 1
    funext c
    exact (htr (X' (a c).1) (a c).2 i ω).symm
  obtain ⟨-, -, -, h4', -, h6'⟩ := hM T' J X' P' hT' hX' hP'
  have hbd' : ∀ᵐ v ∂P', 0 ≤ v (j, 0) ∧ v (j, 0) ≤ Cb := by
    refine (ae_map_iff hφ.aemeasurable ?_).2 ?_
    · exact (measurableSet_le measurable_const (measurable_pi_apply _)).inter
        (measurableSet_le (measurable_pi_apply _) measurable_const)
    · filter_upwards [hbd] with v hv
      simpa [φ] using hv
  have hZ' : ∀ᵐ v ∂P', invariantCondExp P' (evalAtZero j) v ≤ b := by
    refine h6' j b C₀ Cb hb hbd' fun q hq1 => ?_
    obtain ⟨gap, hgap⟩ := hq q hq1
    refine ⟨gap, fun k hk => ?_⟩
    have e : ∫ v, ∏ c, v (j, k c) ∂P' = ∫ v, ∏ c, v (j, m * k c) ∂P := by
      refine integral_map hφ.aemeasurable ?_
      have hmp : Measurable fun v : TranslateValues J => ∏ c, v (j, k c) :=
        Finset.measurable_prod _ fun c _ => measurable_pi_apply (j, k c)
      exact hmp.aestronglyMeasurable
    rw [e]
    exact hgap k hk
  set Z : TranslateValues J → ℝ := invariantCondExp P (evalAtZero j) with hZ
  set Z' : TranslateValues J → ℝ := invariantCondExp P' (evalAtZero j) with hZd
  have hZm : AEStronglyMeasurable Z P := integrable_condExp.aestronglyMeasurable
  have hZm' : AEStronglyMeasurable Z' P' := integrable_condExp.aestronglyMeasurable
  let f : ℕ → TranslateValues J → ℝ := fun M v => (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (j, k)
  have hf : ∀ M, Measurable (f M) := fun M => by
    have hs : Measurable fun v : TranslateValues J => ∑ k ∈ Finset.range M, v (j, k) :=
      Finset.measurable_sum _ fun k _ => measurable_pi_apply (j, k)
    exact hs.const_mul _
  let sh : ℕ → TranslateValues J → TranslateValues J := fun r => (translateShift (J := J))^[r]
  have hpres : ∀ r, MeasurePreserving (φ ∘ sh r) P P' := fun r =>
    (⟨hφ, rfl⟩ : MeasurePreserving φ P P').comp (hS.iterate r)
  let g : ℕ → TranslateValues J → ℝ := fun M v => f M v - Z' v
  have hg : ∀ M, AEStronglyMeasurable (g M) P' := fun M => (hf M).aestronglyMeasurable.sub hZm'
  have he : ∀ M r, eLpNorm (g M ∘ (φ ∘ sh r)) 2 P = eLpNorm (g M) 2 P' := fun M r =>
    eLpNorm_comp_measurePreserving (hg M) (hpres r)
  have hgm : ∀ M r, AEStronglyMeasurable (g M ∘ (φ ∘ sh r)) P := fun M r =>
    (hg M).comp_measurePreserving (hpres r)
  let W : TranslateValues J → ℝ := fun v => (m : ℝ)⁻¹ * ∑ r ∈ Finset.range m, Z' (φ (sh r v))
  have hWb : ∀ᵐ v ∂P, W v ≤ b := by
    have hall : ∀ r, ∀ᵐ v ∂P, Z' (φ (sh r v)) ≤ b := fun r => (hpres r).quasiMeasurePreserving.ae hZ'
    filter_upwards [ae_all_iff.2 hall] with v hv
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 : ∑ r ∈ Finset.range m, Z' (φ (sh r v)) ≤ ∑ _r ∈ Finset.range m, b :=
      Finset.sum_le_sum fun r _ => hv r
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    show (m : ℝ)⁻¹ * _ ≤ b
    rw [inv_mul_le_iff₀ hm0]
    exact h1
  have hWm : AEStronglyMeasurable W P := by
    refine AEStronglyMeasurable.const_mul ?_ _
    have : (fun v => ∑ r ∈ Finset.range m, Z' (φ (sh r v))) = ∑ r ∈ Finset.range m, (Z' ∘ (φ ∘ sh r)) := by
      funext v
      simp [Finset.sum_apply]
    rw [this]
    exact Finset.aestronglyMeasurable_sum _ fun r _ => hZm'.comp_measurePreserving (hpres r)
  have hid : ∀ M v, 1 ≤ M → f (m * M) v - W v = ∑ r ∈ Finset.range m, (m : ℝ)⁻¹ * (g M ∘ (φ ∘ sh r)) v := by
    intro M v hM1
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
    have hfr : ∀ r, f M (φ (sh r v)) = (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (j, m * k + r) := by
      intro r
      show (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, (sh r v) (j, m * k) = _
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      exact translateShift_iterate_apply r v (j, m * k)
    show ((m * M : ℕ) : ℝ)⁻¹ * ∑ t ∈ Finset.range (m * M), v (j, t) - (m : ℝ)⁻¹ * ∑ r ∈ Finset.range m, Z' (φ (sh r v)) = _
    rw [sum_range_mul_split m (fun t => v (j, t)) M]
    simp only [Function.comp_apply, g, hfr, ← Finset.mul_sum, Finset.sum_sub_distrib]
    push_cast
    rw [mul_inv]
    ring
  have hbound : ∀ M, 1 ≤ M → eLpNorm (fun v => f (m * M) v - W v) 2 P ≤ (m : ℝ≥0∞) * eLpNorm (g M) 2 P' := by
    intro M hM1
    have hc : ‖(m : ℝ)⁻¹‖ₑ ≤ 1 := by
      have h1 : ‖(m : ℝ)⁻¹‖ ≤ 1 := by
        rw [norm_inv, Real.norm_natCast]
        exact inv_le_one_of_one_le₀ (by exact_mod_cast hm)
      rw [← ofReal_norm]
      simpa using ENNReal.ofReal_le_ofReal h1
    have e1 : (fun v => f (m * M) v - W v) = ∑ r ∈ Finset.range m, ((m : ℝ)⁻¹ • (g M ∘ (φ ∘ sh r))) := by
      funext v
      rw [hid M v hM1, Finset.sum_apply]
      rfl
    rw [e1]
    refine (eLpNorm_sum_le (fun r _ => (hgm M r).const_smul _) (by norm_num)).trans ?_
    have e2 : ∀ r ∈ Finset.range m, eLpNorm ((m : ℝ)⁻¹ • (g M ∘ (φ ∘ sh r))) 2 P ≤ eLpNorm (g M) 2 P' := by
      intro r _
      rw [eLpNorm_const_smul, he]
      calc ‖(m : ℝ)⁻¹‖ₑ * eLpNorm (g M) 2 P' ≤ 1 * eLpNorm (g M) 2 P' := by gcongr
        _ = _ := one_mul _
    refine (Finset.sum_le_sum e2).trans ?_
    simp
  have hzero : eLpNorm (fun v => Z v - W v) 2 P = 0 := by
    have hm0 : 0 < m := by omega
    have hsub : Tendsto (fun M : ℕ => eLpNorm (fun v => f (m * M) v - Z v) 2 P) atTop (𝓝 0) :=
      (h4 j).comp (tendsto_id.const_mul_atTop' hm0)
    have hsecond : Tendsto (fun M : ℕ => (m : ℝ≥0∞) * eLpNorm (g M) 2 P') atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := (m : ℝ≥0∞)) (h4' j) (Or.inr (ENNReal.natCast_ne_top m))
      simpa using h
    have hsum := hsub.add hsecond
    rw [add_zero] at hsum
    refine le_antisymm (ge_of_tendsto hsum ?_) zero_le
    filter_upwards [eventually_ge_atTop 1] with M hM1
    have e : (fun v => Z v - W v) = (fun v => -(f (m * M) v - Z v)) + (fun v => f (m * M) v - W v) := by
      funext v
      simp only [Pi.add_apply]
      ring
    rw [e]
    refine (eLpNorm_add_le ((hf _).aestronglyMeasurable.sub hZm).neg
      ((hf _).aestronglyMeasurable.sub hWm) (by norm_num)).trans ?_
    refine add_le_add (le_of_eq ?_) (hbound M hM1)
    exact eLpNorm_neg _ _ _
  have hae := (eLpNorm_eq_zero_iff (hZm.sub hWm) (by norm_num)).1 hzero
  filter_upwards [hae, hWb] with v h1 h2
  have : Z v - W v = 0 := h1
  linarith
end YangMills.Construction.MomentMethod
end
