import YangMills.Construction.EnergyMomentum.LaplaceFourierDenseDeterminingProof
import YangMills.Construction.EnergyMomentum.SemigroupGeneratorsProof
import YangMills.Construction.HilbertSpace.BoundedOperatorFacts
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.EnergyMomentum.JointSpectral.Existence
open YangMills.Construction.EuclideanSpectral
section SquareMean
variable {Y : Type*} [MeasurableSpace Y]
theorem eLpNorm_two_eq_lintegral_sq (M : Measure Y) (f : Y → ℂ) :
    eLpNorm f 2 M = (∫⁻ y, ‖f y‖ₑ ^ 2 ∂M) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp
theorem tendsto_eLpNorm_of_tendstoSqMean {M : Measure Y} {f : ℕ → Y → ℂ} {φ : Y → ℂ}
    (h : TendstoSqMean M f φ) :
    Tendsto (fun n => eLpNorm (f n - φ) 2 M) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun n => (∫⁻ y, ‖f n y - φ y‖ₑ ^ 2 ∂M) ^ (1 / 2 : ℝ)) atTop
      (𝓝 ((0 : ℝ≥0∞) ^ (1 / 2 : ℝ))) :=
    ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h₁
  simpa only [eLpNorm_two_eq_lintegral_sq, Pi.sub_apply] using h₁
theorem tendstoSqMean_of_le {M M' : Measure Y} (hM : M' ≤ M) {f : ℕ → Y → ℂ} {φ : Y → ℂ}
    (h : TendstoSqMean M f φ) : TendstoSqMean M' f φ :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    fun _ => lintegral_mono' hM le_rfl
theorem tendsto_integral_conj_mul_of_tendstoSqMean {M : Measure Y} {f g : ℕ → Y → ℂ}
    {f₀ g₀ : Y → ℂ}
    (hf : ∀ n, MemLp (f n) 2 M) (hg : ∀ n, MemLp (g n) 2 M) (hf₀ : MemLp f₀ 2 M)
    (hg₀ : MemLp g₀ 2 M) (tf : TendstoSqMean M f f₀) (tg : TendstoSqMean M g g₀) :
    Tendsto (fun n => ∫ y, conj (f n y) * g n y ∂M) atTop (𝓝 (∫ y, conj (f₀ y) * g₀ y ∂M)) := by
  have key : ∀ {a b : Y → ℂ} (ha : MemLp a 2 M) (hb : MemLp b 2 M),
      ⟪ha.toLp a, hb.toLp b⟫_ℂ = ∫ y, conj (a y) * b y ∂M := by
    intro a b ha hb
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h₁ h₂
    rw [h₁, h₂, RCLike.inner_apply, mul_comm]
  have uf := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf f₀ hf₀).2
    (tendsto_eLpNorm_of_tendstoSqMean tf)
  have ug := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg g₀ hg₀).2
    (tendsto_eLpNorm_of_tendstoSqMean tg)
  have h := Filter.Tendsto.inner (𝕜 := ℂ) uf ug
  simpa only [key] using h
end SquareMean
section Exponentials
theorem laplaceFourierExp_mul (t t' : ℝ≥0) (y y' : Momentum3) (p : EnergyMomentumSpace) :
    laplaceFourierExp t y p * laplaceFourierExp t' y' p =
      laplaceFourierExp (t + t') (y + y') p := by apply _root_.YangMills.Construction.EnergyMomentum.DenseDetermining.laplaceFourierExp_mul <;> assumption
theorem conj_laplaceFourierExp (t : ℝ≥0) (y : Momentum3) (p : EnergyMomentumSpace) :
    conj (laplaceFourierExp t y p) = laplaceFourierExp t (-y) p := by apply _root_.YangMills.Construction.EnergyMomentum.DenseDetermining.conj_laplaceFourierExp <;> assumption
theorem laplaceFourierExp_zero_zero (p : EnergyMomentumSpace) : laplaceFourierExp 0 0 p = 1 := by
  simp [laplaceFourierExp, spatialDot]
end Exponentials
section Pairs
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {S : ℝ≥0 → H →L[ℂ] H} {V : Momentum3 → H →L[ℂ] H}
theorem unitaryGroup_zero (hS : IsContractionSemigroupWithUnitaryGroup S V) : V 0 = 1 := by apply _root_.YangMills.Construction.EnergyMomentum.GeneratorsProof.unitaryGroup_zero <;> assumption
theorem star_unitaryGroup (hS : IsContractionSemigroupWithUnitaryGroup S V) (y : Momentum3) :
    star (V y) = V (-y) := by
  have hu := (isUnitaryOperator_iff_mem_unitary (V y)).1 (hS.isUnitary y)
  have h₁ : star (V y) * V y = 1 := (Unitary.mem_iff.1 hu).1
  have h₂ : V y * V (-y) = 1 := by rw [hS.group_add, add_neg_cancel, unitaryGroup_zero hS]
  calc star (V y) = star (V y) * (V y * V (-y)) := by rw [h₂, mul_one]
    _ = V (-y) := by rw [← mul_assoc, h₁, one_mul]
theorem star_semigroup_mul_unitaryGroup (hS : IsContractionSemigroupWithUnitaryGroup S V)
    (t : ℝ≥0) (y : Momentum3) : star (S t * V y) = S t * V (-y) := by
  rw [star_mul, star_unitaryGroup hS, (hS.isSelfAdjoint t).star_eq, hS.semigroup_mul_group t (-y)]
theorem semigroup_unitaryGroup_mul_mul (hS : IsContractionSemigroupWithUnitaryGroup S V)
    (t t' : ℝ≥0) (y y' : Momentum3) : S t * V y * (S t' * V y') = S (t + t') * V (y + y') := by
  calc S t * V y * (S t' * V y') = S t * (V y * S t') * V y' := by simp only [mul_assoc]
    _ = S t * (S t' * V y) * V y' := by rw [hS.semigroup_mul_group t' y]
    _ = S t * S t' * (V y * V y') := by simp only [mul_assoc]
    _ = S (t + t') * V (y + y') := by rw [hS.semigroup_add, hS.group_add]
def operatorPairs (S : ℝ≥0 → H →L[ℂ] H) (V : Momentum3 → H →L[ℂ] H) :
    Submodule ℂ ((EnergyMomentumSpace → ℂ) × (H →L[ℂ] H)) :=
  Submodule.span ℂ
    (range fun i : ℝ≥0 × Momentum3 => (laplaceFourierExp i.1 i.2, S i.1 * V i.2))
theorem operatorPairs_mul_mem (hS : IsContractionSemigroupWithUnitaryGroup S V)
    {x y : (EnergyMomentumSpace → ℂ) × (H →L[ℂ] H)} (hx : x ∈ operatorPairs S V)
    (hy : y ∈ operatorPairs S V) : x * y ∈ operatorPairs S V := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      refine Submodule.subset_span ⟨(i.1 + j.1, i.2 + j.2), ?_⟩
      exact Prod.ext (funext fun p => (laplaceFourierExp_mul _ _ _ _ p).symm)
        (semigroup_unitaryGroup_mul_mul hS _ _ _ _).symm
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha
theorem operatorPairs_star_mem (hS : IsContractionSemigroupWithUnitaryGroup S V)
    {x : (EnergyMomentumSpace → ℂ) × (H →L[ℂ] H)} (hx : x ∈ operatorPairs S V) :
    star x ∈ operatorPairs S V := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine Submodule.subset_span ⟨(i.1, -i.2), ?_⟩
    exact Prod.ext (funext fun p => (conj_laplaceFourierExp _ _ p).symm)
      (star_semigroup_mul_unitaryGroup hS _ _).symm
  | zero => simp
  | add a b _ _ ha hb => rw [star_add]; exact add_mem ha hb
  | smul c a _ ha => rw [star_smul]; exact Submodule.smul_mem _ _ ha
omit [CompleteSpace H] in
theorem operatorPairs_continuous_bounded {x : (EnergyMomentumSpace → ℂ) × (H →L[ℂ] H)}
    (hx : x ∈ operatorPairs S V) : Continuous x.1 ∧ ∃ c : ℝ, ∀ p, ‖x.1 p‖ ≤ c := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨continuous_laplaceFourierExp _ _, 1, norm_laplaceFourierExp_le_one _ _⟩
  | zero => exact ⟨continuous_zero, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨ca, c, hc⟩ := ha
    obtain ⟨cb, d, hd⟩ := hb
    exact ⟨ca.add cb, c + d, fun p => (norm_add_le _ _).trans (add_le_add (hc p) (hd p))⟩
  | smul r a _ ha =>
    obtain ⟨ca, c, hc⟩ := ha
    refine ⟨ca.const_smul r, ‖r‖ * c, fun p => ?_⟩
    simpa [norm_smul] using mul_le_mul_of_nonneg_left (hc p) (norm_nonneg r)
omit [CompleteSpace H] in
theorem operatorPairs_memLp {x : (EnergyMomentumSpace → ℂ) × (H →L[ℂ] H)}
    (hx : x ∈ operatorPairs S V) (μ : Measure EnergyMomentumSpace) [IsFiniteMeasure μ] :
    MemLp x.1 2 μ := by
  obtain ⟨hc, c, hb⟩ := operatorPairs_continuous_bounded hx
  exact MemLp.of_bound hc.aestronglyMeasurable c (ae_of_all _ hb)
omit [CompleteSpace H] in
theorem operatorPairs_integrable {x : (EnergyMomentumSpace → ℂ) × (H →L[ℂ] H)}
    (hx : x ∈ operatorPairs S V) (μ : Measure EnergyMomentumSpace) [IsFiniteMeasure μ] :
    Integrable x.1 μ := by
  obtain ⟨hc, c, hb⟩ := operatorPairs_continuous_bounded hx
  exact Integrable.of_bound hc.aestronglyMeasurable c (ae_of_all _ hb)
omit [CompleteSpace H] in
theorem operatorPairs_inner_self_eq_integral {ψ : H} {μ : Measure EnergyMomentumSpace}
    (h : IsSpectralMeasure S V ψ μ) {x : (EnergyMomentumSpace → ℂ) × (H →L[ℂ] H)}
    (hx : x ∈ operatorPairs S V) : ⟪ψ, x.2 ψ⟫_ℂ = ∫ p, x.1 p ∂μ := by
  have := h.isFiniteMeasure
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact h.inner_eq_integral i.1 i.2
  | zero => simp
  | add a b ha' hb' ha hb =>
    have := integral_add (operatorPairs_integrable ha' μ) (operatorPairs_integrable hb' μ)
    simp only [Prod.fst_add, Prod.snd_add, add_apply, inner_add_right,
      Pi.add_apply, ha, hb, this]
  | smul c a _ ha =>
    simp only [Prod.smul_fst, Prod.smul_snd, smul_apply, inner_smul_right,
      Pi.smul_apply, smul_eq_mul, ha, integral_const_mul]
theorem operatorPairs_inner_eq_integral (hS : IsContractionSemigroupWithUnitaryGroup S V)
    {ψ : H} {μ : Measure EnergyMomentumSpace} (h : IsSpectralMeasure S V ψ μ)
    {x y : (EnergyMomentumSpace → ℂ) × (H →L[ℂ] H)} (hx : x ∈ operatorPairs S V)
    (hy : y ∈ operatorPairs S V) : ⟪x.2 ψ, y.2 ψ⟫_ℂ = ∫ p, conj (x.1 p) * y.1 p ∂μ := by
  have h₁ := operatorPairs_inner_self_eq_integral h
    (operatorPairs_mul_mem hS (operatorPairs_star_mem hS hx) hy)
  have h₂ : ⟪ψ, (star x * y).2 ψ⟫_ℂ = ⟪x.2 ψ, y.2 ψ⟫_ℂ := by
    simp only [Prod.snd_mul, Prod.snd_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right]
  rw [← h₂, h₁]
  rfl
theorem operatorPairs_enorm_eq_eLpNorm (hS : IsContractionSemigroupWithUnitaryGroup S V)
    {ψ : H} {μ : Measure EnergyMomentumSpace} (h : IsSpectralMeasure S V ψ μ)
    {z : (EnergyMomentumSpace → ℂ) × (H →L[ℂ] H)} (hz : z ∈ operatorPairs S V) :
    ‖z.2 ψ‖ₑ = eLpNorm z.1 2 μ := by
  have := h.isFiniteMeasure
  have h₁ := operatorPairs_inner_eq_integral hS h hz hz
  have h₂ : ∫ p, conj (z.1 p) * z.1 p ∂μ = ((∫ p, ‖z.1 p‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp [Complex.conj_mul']
  rw [h₂, inner_self_eq_norm_sq_to_K] at h₁
  have h₃ : ‖z.2 ψ‖ ^ 2 = ∫ p, ‖z.1 p‖ ^ 2 ∂μ := by
    refine Complex.ofReal_injective ?_
    push_cast
    simpa using h₁
  rw [(operatorPairs_memLp hz μ).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ← ofReal_norm]
  congr 1
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat, ← h₃]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num
theorem operatorPairs_edist_le (hS : IsContractionSemigroupWithUnitaryGroup S V) {ψ : H}
    {μ : Measure EnergyMomentumSpace} (h : IsSpectralMeasure S V ψ μ)
    {x y : (EnergyMomentumSpace → ℂ) × (H →L[ℂ] H)} (hx : x ∈ operatorPairs S V)
    (hy : y ∈ operatorPairs S V) {f : EnergyMomentumSpace → ℂ} (hf : MemLp f 2 μ) :
    edist (x.2 ψ) (y.2 ψ) ≤ eLpNorm (x.1 - f) 2 μ + eLpNorm (y.1 - f) 2 μ := by
  have := h.isFiniteMeasure
  have h₁ : edist (x.2 ψ) (y.2 ψ) = eLpNorm (x - y).1 2 μ := by
    rw [← operatorPairs_enorm_eq_eLpNorm hS h (sub_mem hx hy), edist_eq_enorm_sub]
    simp
  have h₂ : (x - y).1 = (x.1 - f) - (y.1 - f) := by
    simp
  rw [h₁, h₂]
  exact eLpNorm_sub_le (((operatorPairs_memLp hx μ).sub hf).aestronglyMeasurable)
    (((operatorPairs_memLp hy μ).sub hf).aestronglyMeasurable) (by norm_num)
theorem exists_tendsto_of_operatorPairs (hS : IsContractionSemigroupWithUnitaryGroup S V)
    {ψ : H} {μ : Measure EnergyMomentumSpace} (h : IsSpectralMeasure S V ψ μ)
    {f : EnergyMomentumSpace → ℂ} (hf : MemLp f 2 μ)
    (hd : ∃ x : ℕ → (EnergyMomentumSpace → ℂ) × (H →L[ℂ] H), (∀ n, x n ∈ operatorPairs S V) ∧
      TendstoSqMean μ (fun n => (x n).1) f) :
    ∃ χ : H, ∀ x : ℕ → (EnergyMomentumSpace → ℂ) × (H →L[ℂ] H),
      (∀ n, x n ∈ operatorPairs S V) →
      TendstoSqMean μ (fun n => (x n).1) f → Tendsto (fun n => (x n).2 ψ) atTop (𝓝 χ) := by
  obtain ⟨x, hx, tx⟩ := hd
  have ex := tendsto_eLpNorm_of_tendstoSqMean tx
  have hc : CauchySeq fun n => (x n).2 ψ := by
    refine EMetric.cauchySeq_iff.2 fun ε hε => ?_
    have he : ∀ᶠ n in atTop, eLpNorm ((x n).1 - f) 2 μ < ε / 2 :=
      (tendsto_order.1 ex).2 _ (ENNReal.half_pos hε.ne')
    obtain ⟨N, hN⟩ := eventually_atTop.1 he
    refine ⟨N, fun k hk l hl => lt_of_le_of_lt (operatorPairs_edist_le hS h (hx k) (hx l) hf) ?_⟩
    calc _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (hN k hk) (hN l hl)
      _ = ε := ENNReal.add_halves ε
  obtain ⟨χ, hχ⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨χ, fun y hy ty => ?_⟩
  have ey := tendsto_eLpNorm_of_tendstoSqMean ty
  have h₀ : Tendsto (fun n => edist ((x n).2 ψ) χ) atTop (𝓝 0) := tendsto_iff_edist_tendsto_0.1 hχ
  refine tendsto_iff_edist_tendsto_0.2 ?_
  have hs := (ey.add ex).add h₀
  simp only [add_zero] at hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => zero_le)
    fun n => ?_
  exact (edist_triangle _ _ _).trans
    (add_le_add (operatorPairs_edist_le hS h (hy n) (hx n) hf) le_rfl)
end Pairs
section Measure
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {S : ℝ≥0 → H →L[ℂ] H} {V : Momentum3 → H →L[ℂ] H}
def borelIndicator (Δ : BorelSubsets EnergyMomentumSpace) : EnergyMomentumSpace → ℂ :=
  Δ.1.indicator 1
theorem measurable_borelIndicator (Δ : BorelSubsets EnergyMomentumSpace) :
    Measurable (borelIndicator Δ) :=
  measurable_one.indicator Δ.2
theorem norm_borelIndicator_le (Δ : BorelSubsets EnergyMomentumSpace) (p : EnergyMomentumSpace) :
    ‖borelIndicator Δ p‖ ≤ 1 := by
  by_cases h : p ∈ Δ.1 <;> simp [borelIndicator, h]
theorem memLp_borelIndicator (Δ : BorelSubsets EnergyMomentumSpace)
    (μ : Measure EnergyMomentumSpace) [IsFiniteMeasure μ] : MemLp (borelIndicator Δ) 2 μ :=
  MemLp.of_bound (measurable_borelIndicator Δ).aestronglyMeasurable 1
    (ae_of_all _ (norm_borelIndicator_le Δ))
theorem memSqIntegrable_borelIndicator (Δ : BorelSubsets EnergyMomentumSpace)
    (μ : Measure EnergyMomentumSpace) [IsFiniteMeasure μ] :
    MemSqIntegrable μ (borelIndicator Δ) := by
  refine ⟨measurable_borelIndicator Δ,
    lt_of_le_of_lt (lintegral_mono (g := fun _ => 1) fun p => ?_) (by simp)⟩
  by_cases h : p ∈ Δ.1 <;> simp [borelIndicator, h]
theorem integral_conj_borelIndicator_mul (Δ Δ' : BorelSubsets EnergyMomentumSpace)
    (μ : Measure EnergyMomentumSpace) :
    ∫ p, conj (borelIndicator Δ p) * borelIndicator Δ' p ∂μ =
      ((μ.real (Δ.1 ∩ Δ'.1) : ℝ) : ℂ) := by
  have e : (fun p => conj (borelIndicator Δ p) * borelIndicator Δ' p) =
      (Δ.1 ∩ Δ'.1).indicator fun _ => (1 : ℂ) := by
    funext p
    by_cases h : p ∈ Δ.1 <;> by_cases h' : p ∈ Δ'.1 <;> simp [borelIndicator, h, h']
  rw [e, integral_indicator_const _ (Δ.2.inter Δ'.2)]
  simp
omit [CompleteSpace H] in
theorem exists_operatorPair_of_mem_span {q : EnergyMomentumSpace → ℂ}
    (hq : q ∈ laplaceFourierSpan) : ∃ B : H →L[ℂ] H, (q, B) ∈ operatorPairs S V := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨i, rfl⟩ := hq
    exact ⟨S i.1 * V i.2, Submodule.subset_span ⟨i, rfl⟩⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨A, hA⟩ := ha
    obtain ⟨B, hB⟩ := hb
    exact ⟨A + B, add_mem hA hB⟩
  | smul c a _ ha =>
    obtain ⟨A, hA⟩ := ha
    exact ⟨c • A, Submodule.smul_mem _ c hA⟩
omit [CompleteSpace H] in
theorem exists_operatorPairs_tendsto_indicator
    (ht : YangMills.Construction.EnergyMomentum.LaplaceFourierDenseDetermining)
    (M : Measure EnergyMomentumSpace) [IsFiniteMeasure M] (Δ : BorelSubsets EnergyMomentumSpace) :
    ∃ x : ℕ → (EnergyMomentumSpace → ℂ) × (H →L[ℂ] H), (∀ n, x n ∈ operatorPairs S V) ∧
      TendstoSqMean M (fun n => (x n).1) (borelIndicator Δ) := by
  obtain ⟨p, hp, tp⟩ := (ht M).1 _ (memSqIntegrable_borelIndicator Δ M)
  choose B hB using fun n => exists_operatorPair_of_mem_span (S := S) (V := V) (hp n)
  exact ⟨fun n => (p n, B n), hB, tp⟩
theorem op_eq_of_inner_self_eq (hops : YangMills.Construction.BoundedOperators.BoundedOperatorFacts)
    {A B : H →L[ℂ] H} (h : ∀ ψ, ⟪ψ, A ψ⟫_ℂ = ⟪ψ, B ψ⟫_ℂ) : A = B := by
  have h₀ := (hops.2.2.1 H).1 (A - B) fun ψ => by simp [h ψ]
  exact sub_eq_zero.1 h₀
theorem exists_spectralMeasure_of_diag
    (hops : YangMills.Construction.BoundedOperators.BoundedOperatorFacts)
    (ht : YangMills.Construction.EnergyMomentum.LaplaceFourierDenseDetermining)
    (hS : IsContractionSemigroupWithUnitaryGroup S V) (m : H → Measure EnergyMomentumSpace)
    (hm : ∀ ψ, IsSpectralMeasure S V ψ (m ψ)) :
    ∃ E : EuclideanSpectral.SpectralMeasure EnergyMomentumSpace H,
      ∀ (ψ : H) (Δ : BorelSubsets EnergyMomentumSpace),
        E.diagMass ψ Δ = (((m ψ).real Δ.1 : ℝ) : ℂ) := by
  have hfin : ∀ ψ, IsFiniteMeasure (m ψ) := fun ψ => (hm ψ).isFiniteMeasure
  have hex : ∀ (Δ : BorelSubsets EnergyMomentumSpace) (ψ : H), ∃ χ : H,
      ∀ x : ℕ → (EnergyMomentumSpace → ℂ) × (H →L[ℂ] H), (∀ n, x n ∈ operatorPairs S V) →
        TendstoSqMean (m ψ) (fun n => (x n).1) (borelIndicator Δ) →
          Tendsto (fun n => (x n).2 ψ) atTop (𝓝 χ) :=
    fun Δ ψ => exists_tendsto_of_operatorPairs hS (hm ψ) (memLp_borelIndicator Δ _)
      (exists_operatorPairs_tendsto_indicator ht _ Δ)
  choose Q hQ using hex
  have inner_Q : ∀ (Δ Δ' : BorelSubsets EnergyMomentumSpace) (ψ : H),
      ⟪Q Δ ψ, Q Δ' ψ⟫_ℂ = (((m ψ).real (Δ.1 ∩ Δ'.1) : ℝ) : ℂ) := by
    intro Δ Δ' ψ
    obtain ⟨x, hx, tx⟩ := exists_operatorPairs_tendsto_indicator (S := S) (V := V) ht (m ψ) Δ
    obtain ⟨y, hy, ty⟩ := exists_operatorPairs_tendsto_indicator (S := S) (V := V) ht (m ψ) Δ'
    have l₁ := Filter.Tendsto.inner (𝕜 := ℂ) (hQ Δ ψ x hx tx) (hQ Δ' ψ y hy ty)
    have l₂ := tendsto_integral_conj_mul_of_tendstoSqMean
      (fun n => operatorPairs_memLp (hx n) (m ψ))
      (fun n => operatorPairs_memLp (hy n) (m ψ)) (memLp_borelIndicator Δ _)
      (memLp_borelIndicator Δ' _) tx ty
    have l₃ := tendsto_nhds_unique
      (l₁.congr fun n => operatorPairs_inner_eq_integral hS (hm ψ) (hx n) (hy n)) l₂
    rw [l₃, integral_conj_borelIndicator_mul]
  let U : BorelSubsets EnergyMomentumSpace := ⟨univ, MeasurableSet.univ⟩
  have Q_univ : ∀ ψ, Q U ψ = ψ := by
    intro ψ
    have hmem : (laplaceFourierExp 0 0, S 0 * V 0) ∈ operatorPairs S V :=
      Submodule.subset_span ⟨(0, 0), rfl⟩
    have t : TendstoSqMean (m ψ) (fun _ : ℕ => laplaceFourierExp 0 0) (borelIndicator U) := by
      have e : ∀ p, laplaceFourierExp 0 0 p - borelIndicator U p = 0 := fun p => by
        simp [laplaceFourierExp_zero_zero, borelIndicator, U]
      simp [TendstoSqMean, e]
    have l := hQ U ψ (fun _ => (laplaceFourierExp 0 0, S 0 * V 0)) (fun _ => hmem) t
    have e₂ : (S 0 * V 0) ψ = ψ := by simp [hS.semigroup_zero, unitaryGroup_zero hS]
    simp only [e₂] at l
    exact tendsto_nhds_unique l tendsto_const_nhds
  have Q_add : ∀ (Δ : BorelSubsets EnergyMomentumSpace) (ψ χ : H),
      Q Δ (ψ + χ) = Q Δ ψ + Q Δ χ := by
    intro Δ ψ χ
    obtain ⟨x, hx, tx⟩ := exists_operatorPairs_tendsto_indicator (S := S) (V := V) ht
      (m ψ + m χ + m (ψ + χ)) Δ
    have l₁ := hQ Δ ψ x hx
      (tendstoSqMean_of_le (Measure.le_add_right (Measure.le_add_right le_rfl)) tx)
    have l₂ := hQ Δ χ x hx
      (tendstoSqMean_of_le (Measure.le_add_right (Measure.le_add_left le_rfl)) tx)
    have l₃ := hQ Δ (ψ + χ) x hx (tendstoSqMean_of_le (Measure.le_add_left le_rfl) tx)
    refine tendsto_nhds_unique l₃ ?_
    simpa only [map_add] using l₁.add l₂
  have Q_smul : ∀ (Δ : BorelSubsets EnergyMomentumSpace) (c : ℂ) (ψ : H),
      Q Δ (c • ψ) = c • Q Δ ψ := by
    intro Δ c ψ
    obtain ⟨x, hx, tx⟩ := exists_operatorPairs_tendsto_indicator (S := S) (V := V) ht
      (m ψ + m (c • ψ)) Δ
    have l₁ := hQ Δ ψ x hx (tendstoSqMean_of_le (Measure.le_add_right le_rfl) tx)
    have l₂ := hQ Δ (c • ψ) x hx (tendstoSqMean_of_le (Measure.le_add_left le_rfl) tx)
    refine tendsto_nhds_unique l₂ ?_
    simpa only [map_smul] using l₁.const_smul c
  have norm_sq : ∀ (Δ : BorelSubsets EnergyMomentumSpace) (ψ : H),
      ‖Q Δ ψ‖ ^ 2 = (m ψ).real Δ.1 := by
    intro Δ ψ
    have h := inner_Q Δ Δ ψ
    rw [inner_self_eq_norm_sq_to_K, inter_self] at h
    refine Complex.ofReal_injective ?_
    push_cast
    simpa using h
  have mass_total : ∀ ψ, (m ψ).real univ = ‖ψ‖ ^ 2 := by
    intro ψ
    have h := norm_sq U ψ
    rw [Q_univ] at h
    exact h.symm
  have Q_le : ∀ (Δ : BorelSubsets EnergyMomentumSpace) (ψ : H), ‖Q Δ ψ‖ ≤ 1 * ‖ψ‖ := by
    intro Δ ψ
    rw [one_mul]
    have h : ‖Q Δ ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
      rw [norm_sq, ← mass_total]
      exact measureReal_mono (subset_univ _)
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
  let E : BorelSubsets EnergyMomentumSpace → H →L[ℂ] H := fun Δ =>
    LinearMap.mkContinuous
      { toFun := Q Δ, map_add' := Q_add Δ, map_smul' := fun c ψ => Q_smul Δ c ψ } 1 (Q_le Δ)
  have diag : ∀ (Δ : BorelSubsets EnergyMomentumSpace) (ψ : H),
      ⟪ψ, E Δ ψ⟫_ℂ = (((m ψ).real Δ.1 : ℝ) : ℂ) := by
    intro Δ ψ
    have h := inner_Q U Δ ψ
    rw [Q_univ] at h
    change ⟪ψ, Q Δ ψ⟫_ℂ = _
    simpa [U] using h
  have sa : ∀ Δ, IsSelfAdjointOp (E Δ) := fun Δ =>
    (hops.2.2.1 H).2.1 (E Δ) fun ψ => by
      rw [diag]
      exact Complex.ofReal_im _
  refine ⟨{ borelSubset := isEuclideanBorel_energyMomentumSpace, toFun := E, selfAdjoint := sa,
            map_univ := ?_, map_inter := ?_, countablyAdditive := ?_ }, fun ψ Δ => diag Δ ψ⟩
  · exact ContinuousLinearMap.ext fun ψ => Q_univ ψ
  · intro Δ Δ'
    refine op_eq_of_inner_self_eq hops fun ψ => ?_
    rw [diag ⟨Δ.1 ∩ Δ'.1, Δ.2.inter Δ'.2⟩ ψ]
    have h₁ : ⟪ψ, (E Δ * E Δ') ψ⟫_ℂ = ⟪E Δ ψ, E Δ' ψ⟫_ℂ := sa Δ ψ (E Δ' ψ)
    rw [h₁]
    exact inner_Q Δ Δ' ψ
  · intro ψ Δ hd
    simp only [diag]
    refine Complex.hasSum_ofReal.mpr ?_
    have h₁ : (m ψ) (⋃ k, (Δ k).1) = ∑' k, m ψ (Δ k).1 :=
      measure_iUnion hd fun k => (Δ k).2
    simp only [measureReal_def]
    have h₂ : ∑' k, m ψ (Δ k).1 ≠ ∞ := by
      rw [← h₁]
      exact measure_ne_top _ _
    rw [h₁, ENNReal.tsum_toReal_eq fun k => measure_ne_top _ _]
    exact ENNReal.hasSum_toReal h₂
theorem diagMeasure_eq_of_diagMass {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (F : EuclideanSpectral.SpectralMeasure Y H) (ψ : H) (μ : Measure Y)
    [IsFiniteMeasure μ] (h : ∀ Δ, F.diagMass ψ Δ = ((μ.real Δ.1 : ℝ) : ℂ)) :
    F.diagMeasure ψ = μ := by
  refine Measure.ext fun s hs => ?_
  rw [EuclideanSpectral.SpectralMeasure.diagMeasure, Measure.ofMeasurable_apply s hs, h ⟨s, hs⟩,
    Complex.ofReal_re]
  exact ofReal_measureReal
theorem spectralMeasure_ext_of_diagMeasure
    (hcal : YangMills.Construction.EuclideanSpectral.FunctionalCalculus.FunctionalCalculusHolds)
    (hops : YangMills.Construction.BoundedOperators.BoundedOperatorFacts) {Y : Type}
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (F G : EuclideanSpectral.SpectralMeasure Y H)
    (h : ∀ ψ, F.diagMeasure ψ = G.diagMeasure ψ) : F = G := by
  have hv : ∀ Δ, F Δ = G Δ := fun Δ => op_eq_of_inner_self_eq hops fun ψ => by
    have a := (hcal Y H F).1.real_apply ψ Δ
    have b := (hcal Y H G).1.real_apply ψ Δ
    rw [h ψ] at a
    exact a.symm.trans b
  obtain ⟨a, f, _, _, _, _⟩ := F
  obtain ⟨b, g, _, _, _, _⟩ := G
  have hfg : f = g := funext hv
  subst hfg
  rfl
end Measure
section Kernel
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {S : ℝ≥0 → H →L[ℂ] H} {V : Momentum3 → H →L[ℂ] H}
theorem opKernel_semigroup_eq (hS : IsContractionSemigroupWithUnitaryGroup S V) (t : ℝ≥0) :
    opKernel (S t) = {0} := by
  ext ψ
  simp only [opKernel, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · intro h
    have step : ∀ a : ℝ≥0, S (a + a) ψ = 0 → S a ψ = 0 := by
      intro a ha
      have h₁ : ⟪S a ψ, S a ψ⟫_ℂ = ⟪ψ, S a (S a ψ)⟫_ℂ := by
        have h₂ : ContinuousLinearMap.adjoint (S a) = S a := (hS.isSelfAdjoint a).star_eq
        rw [← ContinuousLinearMap.adjoint_inner_right, h₂]
      have h₃ : S a (S a ψ) = S (a + a) ψ := by
        rw [← hS.semigroup_add]
        rfl
      rw [h₃, ha, inner_zero_right] at h₁
      exact inner_self_eq_zero.1 h₁
    have all : ∀ n : ℕ, S (t * 2⁻¹ ^ n) ψ = 0 := by
      intro n
      induction n with
      | zero => simpa using h
      | succ n ih =>
        refine step _ ?_
        have e : t * 2⁻¹ ^ (n + 1) + t * 2⁻¹ ^ (n + 1) = t * 2⁻¹ ^ n := by
          have h₂ : (2⁻¹ : ℝ≥0) + 2⁻¹ = 1 := by norm_num
          rw [pow_succ, ← mul_add, ← mul_add, h₂, mul_one]
        rw [e]
        exact ih
    have l₁ : Tendsto (fun n : ℕ => t * 2⁻¹ ^ n) atTop (𝓝 0) := by
      have h₂ := (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := 2⁻¹) (by norm_num)).const_mul t
      simpa using h₂
    have l₂ := ((hS.continuous_semigroup ψ).tendsto 0).comp l₁
    have l₃ : Tendsto (fun n : ℕ => S (t * 2⁻¹ ^ n) ψ) atTop (𝓝 (S 0 ψ)) := l₂
    simp only [all] at l₃
    have h₄ := tendsto_nhds_unique l₃ tendsto_const_nhds
    simpa [hS.semigroup_zero] using h₄
  · rintro rfl
    exact map_zero _
end Kernel
section Marginals
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {S : ℝ≥0 → H →L[ℂ] H} {V : Momentum3 → H →L[ℂ] H}
def axisEmbedding (i : Fin 3) (p : EnergyMomentumLine) : EnergyMomentumSpace :=
  (p.1, p.2 • EuclideanSpace.single i (1 : ℝ))
theorem measurable_axisEmbedding (i : Fin 3) : Measurable (axisEmbedding i) :=
  (continuous_fst.prodMk (continuous_snd.smul continuous_const)).measurable
theorem spatialDot_smul_single_left (s : ℝ) (i : Fin 3) (q : Momentum3) :
    spatialDot (s • EuclideanSpace.single i (1 : ℝ)) q = s * q i := by
  simp [spatialDot]
theorem spatialDot_smul_single_right (s : ℝ) (i : Fin 3) (y : Momentum3) :
    spatialDot y (s • EuclideanSpace.single i (1 : ℝ)) = y i * s := by
  simp [spatialDot]
theorem laplaceFourierExp_axisEmbedding (t : ℝ≥0) (y : Momentum3) (i : Fin 3)
    (p : EnergyMomentumLine) :
    laplaceFourierExp t y (axisEmbedding i p) = laplaceFourierExpLine t (y i) p := by
  simp only [laplaceFourierExp, laplaceFourierExpLine, axisEmbedding, spatialDot_smul_single_right]
theorem laplaceFourierExpLine_projMomentum (t : ℝ≥0) (s : ℝ) (i : Fin 3)
    (p : EnergyMomentumSpace) :
    laplaceFourierExpLine t s (projMomentum i p) =
      laplaceFourierExp t (s • EuclideanSpace.single i (1 : ℝ)) p := by
  simp only [laplaceFourierExp, laplaceFourierExpLine, projMomentum, spatialDot_smul_single_left]
theorem isBoundedMeasurable_laplaceFourierExp (t : ℝ≥0) (y : Momentum3) :
    IsBoundedMeasurable (laplaceFourierExp t y) :=
  ⟨(continuous_laplaceFourierExp t y).measurable, 1, norm_laplaceFourierExp_le_one t y⟩
theorem isBoundedMeasurable_laplaceFourierExpLine (t : ℝ≥0) (s : ℝ) :
    IsBoundedMeasurable (laplaceFourierExpLine t s) := by
  refine ⟨?_, 1, fun p => ?_⟩
  · have h : Continuous (laplaceFourierExpLine t s) := by
      unfold laplaceFourierExpLine
      fun_prop
    exact h.measurable
  · have h : 0 ≤ (t : ℝ) * (p.1 : ℝ) := mul_nonneg t.2 p.1.2
    simp [laplaceFourierExpLine, Complex.norm_exp, h]
theorem map_projMomentum_map_axisEmbedding (i : Fin 3) (a : Measure EnergyMomentumLine) :
    (a.map (axisEmbedding i)).map (projMomentum i) = a := by
  rw [Measure.map_map (measurable_projMomentum i) (measurable_axisEmbedding i)]
  have e : projMomentum i ∘ axisEmbedding i = id := by
    funext p
    exact Prod.ext rfl (by simp [projMomentum, axisEmbedding])
  rw [e, Measure.map_id]
theorem isMomentumMarginal_unique
    (hcal : YangMills.Construction.EuclideanSpectral.FunctionalCalculus.FunctionalCalculusHolds)
    (hops : YangMills.Construction.BoundedOperators.BoundedOperatorFacts)
    (ht : YangMills.Construction.EnergyMomentum.LaplaceFourierDenseDetermining) (i : Fin 3)
    (F G : EuclideanSpectral.SpectralMeasure EnergyMomentumLine H)
    (hF : IsMomentumMarginal S V i F) (hG : IsMomentumMarginal S V i G) : F = G := by
  refine spectralMeasure_ext_of_diagMeasure hcal hops F G fun ψ => ?_
  have key : ∀ K : EuclideanSpectral.SpectralMeasure EnergyMomentumLine H,
      IsMomentumMarginal S V i K → ∀ (t : ℝ≥0) (y : Momentum3),
        ∫ p, laplaceFourierExp t y p ∂((K.diagMeasure ψ).map (axisEmbedding i)) =
          ⟪ψ, (S t * V (y i • EuclideanSpace.single i (1 : ℝ))) ψ⟫_ℂ := by
    intro K hK t y
    rw [integral_map (measurable_axisEmbedding i).aemeasurable
      (continuous_laplaceFourierExp t y).aestronglyMeasurable]
    simp only [laplaceFourierExp_axisEmbedding]
    rw [hK t (y i)]
    exact ((hcal EnergyMomentumLine H K).2.1.isBoundedCalculus _
      (isBoundedMeasurable_laplaceFourierExpLine t (y i)) ψ).symm
  have hFf := (hcal EnergyMomentumLine H F).1.isFiniteMeasure ψ
  have hGf := (hcal EnergyMomentumLine H G).1.isFiniteMeasure ψ
  have hM := (ht ((G.diagMeasure ψ).map (axisEmbedding i))).2
    ((F.diagMeasure ψ).map (axisEmbedding i)) fun t y => by rw [key F hF, key G hG]
  rw [← map_projMomentum_map_axisEmbedding i (F.diagMeasure ψ), hM,
    map_projMomentum_map_axisEmbedding]
end Marginals
theorem jointSpectralMeasureTheorem_holds
    (hcal : YangMills.Construction.EuclideanSpectral.FunctionalCalculus.FunctionalCalculusHolds)
    (hops : YangMills.Construction.BoundedOperators.BoundedOperatorFacts)
    (hscal : YangMills.Construction.EnergyMomentum.SpectralMeasure.Statement)
    (ht : YangMills.Construction.EnergyMomentum.LaplaceFourierDenseDetermining) :
    JointSpectralMeasureTheorem := by
  intro H _ _ _ S V hS
  have hm : ∀ ψ, IsSpectralMeasure S V ψ (spectralMeasure S V ψ) :=
    fun ψ => (hscal H S V hS ψ).1
  have hfin : ∀ ψ, IsFiniteMeasure (spectralMeasure S V ψ) := fun ψ => (hm ψ).isFiniteMeasure
  have hmeasure : ∀ F : EuclideanSpectral.SpectralMeasure EnergyMomentumSpace H,
      IsJointSpectralMeasure S V F → ∀ ψ, F.diagMeasure ψ = spectralMeasure S V ψ := by
    intro F hF ψ
    have hFf := (hcal EnergyMomentumSpace H F).1.isFiniteMeasure ψ
    refine (hscal H S V hS ψ).2.1 _ ⟨hFf, fun t y => ?_⟩
    rw [hF t y]
    exact (hcal EnergyMomentumSpace H F).2.1.isBoundedCalculus _
      (isBoundedMeasurable_laplaceFourierExp t y) ψ
  have hspec : IsJointSpectralMeasure S V (jointSpectralMeasure S V) := by
    obtain ⟨E, hE⟩ := exists_spectralMeasure_of_diag hops ht hS _ hm
    have hEs : ∀ ψ, E.diagMeasure ψ = spectralMeasure S V ψ :=
      fun ψ => diagMeasure_eq_of_diagMass E ψ _ (hE ψ)
    have hJ : IsJointSpectralMeasure S V E := fun t y => op_eq_of_inner_self_eq hops fun ψ => by
      rw [(hm ψ).inner_eq_integral t y, (hcal EnergyMomentumSpace H E).2.1.isBoundedCalculus _
        (isBoundedMeasurable_laplaceFourierExp t y) ψ, hEs]
    unfold jointSpectralMeasure
    exact Classical.epsilon_spec ⟨E, hJ⟩
  have himage : ∀ i, IsMomentumMarginal S V i (momentumMarginal S V i) := by
    intro i t s
    refine op_eq_of_inner_self_eq hops fun ψ => ?_
    have hi := (hcal EnergyMomentumSpace H (jointSpectralMeasure S V)).2.2.2.2.1
      EnergyMomentumLine isEuclideanBorel_energyMomentumLine (projMomentum i)
      (measurable_projMomentum i) ψ
    have hb := (hcal EnergyMomentumLine H (momentumMarginal S V i)).2.1.isBoundedCalculus _
      (isBoundedMeasurable_laplaceFourierExpLine t s) ψ
    rw [hb]
    have hj : (momentumMarginal S V i).diagMeasure ψ =
        ((jointSpectralMeasure S V).diagMeasure ψ).map (projMomentum i) := hi
    rw [hj, integral_map (measurable_projMomentum i).aemeasurable
      (isBoundedMeasurable_laplaceFourierExpLine t s).1.aestronglyMeasurable]
    simp only [laplaceFourierExpLine_projMomentum]
    rw [hspec t (s • EuclideanSpace.single i (1 : ℝ))]
    exact (hcal EnergyMomentumSpace H _).2.1.isBoundedCalculus _
      (isBoundedMeasurable_laplaceFourierExp t _) ψ
  refine ⟨⟨hspec, fun E hE => ?_, fun ψ => hmeasure _ hspec ψ⟩,
    fun t => opKernel_semigroup_eq hS t,
    fun i => ⟨himage i, fun F hF => isMomentumMarginal_unique hcal hops ht i F _ hF (himage i)⟩⟩
  exact spectralMeasure_ext_of_diagMeasure hcal hops E _ fun ψ => by
    rw [hmeasure E hE, hmeasure _ hspec]
end YangMills.Construction.EnergyMomentum.JointSpectral.Existence
