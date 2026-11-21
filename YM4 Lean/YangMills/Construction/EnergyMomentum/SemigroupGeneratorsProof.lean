import YangMills.Construction.EnergyMomentum.SemigroupGenerators
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction.EnergyMomentum.GeneratorsProof
open YangMills.Construction.EnergyMomentum YangMills.Construction.EuclideanSpectral YangMills.Construction.EuclideanSpectral.SpectralMeasure YangMills.Construction.EuclideanSpectral.FunctionalCalculus YangMills.Construction.EnergyMomentum.JointSpectral YangMills.Construction.EnergyMomentum.Generators
section Calculus
variable {Y H : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {F : SpectralMeasure Y H}
theorem mem_calculusDomain_of_bounded (hF : UnboundedCalculusLaws F) {f : Y → ℂ}
    (hfb : IsBoundedMeasurable f) (v : H) : v ∈ F.calculusDomain f := by
  have h₁ := (hF.isCalculusOperator f hfb.1).1
  rw [← h₁, (hF.of_bounded f hfb).1]
  exact Submodule.mem_top
theorem calculusLimit_eq_boundedCalculus (hF : UnboundedCalculusLaws F) {f : Y → ℂ}
    (hfb : IsBoundedMeasurable f) (v : H) : F.calculusLimit f v = F.boundedCalculus f v := by
  have hm : v ∈ (F.calculusOperator f).domain := by
    rw [(hF.of_bounded f hfb).1]
    exact Submodule.mem_top
  have h₁ := (hF.isCalculusOperator f hfb.1).2 ⟨v, hm⟩
  have h₂ := (hF.of_bounded f hfb).2 ⟨v, hm⟩
  exact h₁.symm.trans h₂
theorem integrable_norm_sq_of_mem_calculusDomain {φ : Y → ℂ} (hφ : Measurable φ) {v : H}
    (hv : v ∈ F.calculusDomain φ) :
    Integrable (fun y => ‖φ y‖ ^ 2) (F.diagMeasure v) := by
  refine ⟨(hφ.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  have hv' : ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂F.diagMeasure v < ∞ := hv
  simpa [HasFiniteIntegral, enorm_pow] using hv'
theorem norm_boundedCalculus_sub_calculusLimit_sq (hF : UnboundedCalculusLaws F) {f φ : Y → ℂ}
    (hfb : IsBoundedMeasurable f) (hφ : Measurable φ) {v : H} (hv : v ∈ F.calculusDomain φ) :
    ‖F.boundedCalculus f v - F.calculusLimit φ v‖ ^ 2 =
      ∫ y, ‖f y - φ y‖ ^ 2 ∂F.diagMeasure v := by
  have hd : v ∈ F.calculusDomain f ∩ F.calculusDomain φ :=
    ⟨mem_calculusDomain_of_bounded hF hfb v, hv⟩
  have hm := hF.mem_calculusDomain_add f φ hfb.1 hφ 1 (-1) v hd
  have hl := hF.calculusLimit_add f φ hfb.1 hφ 1 (-1) v hd
  have hn := hF.norm_sq _ ((hfb.1.const_smul (1 : ℂ)).add (hφ.const_smul (-1 : ℂ))) v hm
  rw [hl, calculusLimit_eq_boundedCalculus hF hfb] at hn
  simpa [sub_eq_add_neg] using hn
theorem calculusLimit_eq_zero_iff (hF : UnboundedCalculusLaws F) {φ : Y → ℂ}
    (hφ : Measurable φ) (v : H) :
    (v ∈ F.calculusDomain φ ∧ F.calculusLimit φ v = 0) ↔ φ =ᵐ[F.diagMeasure v] 0 := by
  constructor
  · rintro ⟨hv, h₀⟩
    have hn := hF.norm_sq φ hφ v hv
    rw [h₀] at hn
    have hz : ∫ y, ‖φ y‖ ^ 2 ∂F.diagMeasure v = 0 := by simpa using hn.symm
    have hae := (integral_eq_zero_iff_of_nonneg (fun _ => by positivity)
      (integrable_norm_sq_of_mem_calculusDomain hφ hv)).1 hz
    filter_upwards [hae] with y hy
    simpa using hy
  · intro h
    have hv : v ∈ F.calculusDomain φ := by
      have h₀ : ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂F.diagMeasure v = 0 := by
        rw [lintegral_eq_zero_iff' ((hφ.enorm.pow_const 2).aemeasurable)]
        filter_upwards [h] with y hy
        simp [hy]
      change ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂F.diagMeasure v < ∞
      rw [h₀]
      exact ENNReal.zero_lt_top
    refine ⟨hv, ?_⟩
    have hn := hF.norm_sq φ hφ v hv
    have hz : ∫ y, ‖φ y‖ ^ 2 ∂F.diagMeasure v = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      · filter_upwards [h] with y hy
        simp [hy]
    rw [hz] at hn
    simpa using hn
theorem boundedCalculus_apply_eq_zero_iff (hF : UnboundedCalculusLaws F)
    {f : Y → ℂ} (hfb : IsBoundedMeasurable f) (v : H) :
    F.boundedCalculus f v = 0 ↔ f =ᵐ[F.diagMeasure v] 0 := by
  rw [← calculusLimit_eq_zero_iff hF hfb.1, calculusLimit_eq_boundedCalculus hF hfb]
  exact ⟨fun h₀ => ⟨mem_calculusDomain_of_bounded hF hfb v, h₀⟩, fun h₀ => h₀.2⟩
omit [TopologicalSpace Y] [BorelSpace Y] in
theorem isBoundedMeasurable_one : IsBoundedMeasurable (1 : Y → ℂ) :=
  ⟨measurable_one, 1, fun _ => by simp⟩
theorem boundedCalculus_one (hB : BoundedCalculusLaws F) : F.boundedCalculus (1 : Y → ℂ) = 1 := by
  have h := hB.indicator ⟨univ, MeasurableSet.univ⟩
  have h₁ : (univ : Set Y).indicator (1 : Y → ℂ) = 1 := indicator_univ _
  change F.boundedCalculus ((univ : Set Y).indicator 1) = _ at h
  rw [h₁] at h
  exact h.trans F.map_univ
omit [TopologicalSpace Y] [BorelSpace Y] in
theorem isBoundedMeasurable_smul_one_sub {g : Y → ℂ} (hg : IsBoundedMeasurable g) (c : ℂ) :
    IsBoundedMeasurable (c • (1 - g)) := by
  obtain ⟨hm, C, hC⟩ := hg
  refine ⟨(measurable_one.sub hm).const_smul c, ‖c‖ * (1 + C), fun y => ?_⟩
  have h₁ : ‖(1 : ℂ) - g y‖ ≤ 1 + C := (norm_sub_le _ _).trans (by simpa using hC y)
  simpa using mul_le_mul_of_nonneg_left h₁ (norm_nonneg c)
theorem boundedCalculus_smul_one_sub_apply (hB : BoundedCalculusLaws F) {g : Y → ℂ}
    (hg : IsBoundedMeasurable g) (c : ℂ) (v : H) :
    F.boundedCalculus (c • (1 - g)) v = c • (v - F.boundedCalculus g v) := by
  have hs : (1 : Y → ℂ) - g = 1 + (-1 : ℂ) • g := by
    ext y
    simp [sub_eq_add_neg]
  have hbd : IsBoundedMeasurable ((1 : Y → ℂ) - g) := by
    simpa using isBoundedMeasurable_smul_one_sub hg 1
  have hng : IsBoundedMeasurable ((-1 : ℂ) • g) := by
    obtain ⟨hm, C, hC⟩ := hg
    exact ⟨hm.const_smul _, C, fun y => by simpa using hC y⟩
  rw [hB.smul c _ hbd, hs, hB.add _ _ isBoundedMeasurable_one hng, hB.smul _ _ hg,
    boundedCalculus_one hB]
  simp [sub_eq_add_neg]
theorem boundedCalculus_apply_eq_self_iff (hB : BoundedCalculusLaws F) (hF : UnboundedCalculusLaws F)
    {g : Y → ℂ} (hg : IsBoundedMeasurable g) (v : H) :
    F.boundedCalculus g v = v ↔ g =ᵐ[F.diagMeasure v] 1 := by
  have h₁ := boundedCalculus_apply_eq_zero_iff hF (isBoundedMeasurable_smul_one_sub hg 1) v
  rw [boundedCalculus_smul_one_sub_apply hB hg, one_smul, sub_eq_zero] at h₁
  rw [eq_comm, h₁]
  constructor
  · intro h₂
    filter_upwards [h₂] with y hy
    have hy' : (1 : ℂ) - g y = 0 := by simpa using hy
    simpa using (sub_eq_zero.1 hy').symm
  · intro h₂
    filter_upwards [h₂] with y hy
    simp [hy]
omit [TopologicalSpace Y] [BorelSpace Y] in
theorem isBoundedMeasurable_indicator_one (Z : BorelSubsets Y) :
    IsBoundedMeasurable (Z.1.indicator (1 : Y → ℂ)) :=
  ⟨measurable_one.indicator Z.2, 1, fun y => by by_cases hy : y ∈ Z.1 <;> simp [hy]⟩
theorem apply_eq_self_iff_measureIsCarriedBy (hB : BoundedCalculusLaws F)
    (hF : UnboundedCalculusLaws F) (Z : BorelSubsets Y) (v : H) :
    F Z v = v ↔ MeasureIsCarriedBy (F.diagMeasure v) Z := by
  rw [← hB.indicator Z, boundedCalculus_apply_eq_self_iff hB hF (isBoundedMeasurable_indicator_one Z) v,
    MeasureIsCarriedBy, Filter.EventuallyEq, ae_iff]
  have h : {y | ¬Z.1.indicator (1 : Y → ℂ) y = (1 : Y → ℂ) y} = Z.1ᶜ := by
    ext y
    by_cases hy : y ∈ Z.1 <;> simp [hy]
  rw [h]
theorem tendsto_boundedCalculus_of_dominated (hF : UnboundedCalculusLaws F) {ι : Type*}
    {l : Filter ι} [l.IsCountablyGenerated] {b : ι → Y → ℂ} {φ : Y → ℂ}
    (hbb : ∀ i, IsBoundedMeasurable (b i)) (hφ : Measurable φ) {v : H}
    (hv : v ∈ F.calculusDomain φ) {G : Y → ℝ} (hG : Integrable G (F.diagMeasure v))
    (hbound : ∀ i y, ‖b i y - φ y‖ ^ 2 ≤ G y)
    (hlim : ∀ y, Tendsto (fun i => b i y) l (𝓝 (φ y))) :
    Tendsto (fun i => F.boundedCalculus (b i) v) l (𝓝 (F.calculusLimit φ v)) := by
  have h₀ : Tendsto (fun i => ∫ y, ‖b i y - φ y‖ ^ 2 ∂F.diagMeasure v) l (𝓝 0) := by
    have h₁ := tendsto_integral_filter_of_dominated_convergence (μ := F.diagMeasure v) (l := l)
      (F := fun i y => ‖b i y - φ y‖ ^ 2) (f := fun _ => (0 : ℝ)) G
      (Eventually.of_forall fun i =>
        ((((hbb i).1.sub hφ).norm).pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun i => Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hbound i y)
      hG
      (Eventually.of_forall fun y => by
        have h₂ : Tendsto (fun i => b i y - φ y) l (𝓝 0) := by
          simpa using (hlim y).sub_const (φ y)
        simpa using (h₂.norm).pow 2)
    simpa using h₁
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h₂ : (fun i => ‖F.boundedCalculus (b i) v - F.calculusLimit φ v‖) =
      fun i => Real.sqrt (∫ y, ‖b i y - φ y‖ ^ 2 ∂F.diagMeasure v) := by
    funext i
    rw [← norm_boundedCalculus_sub_calculusLimit_sq hF (hbb i) hφ hv, Real.sqrt_sq (norm_nonneg _)]
  rw [h₂]
  simpa using h₀.sqrt
theorem mem_calculusDomain_of_tendsto (hB : BoundedCalculusLaws F) (hV : ValuesAndDiagMeasures F)
    {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {b : ι → Y → ℂ} {φ : Y → ℂ}
    (hbb : ∀ i, IsBoundedMeasurable (b i))
    (hlim : ∀ y, Tendsto (fun i => b i y) l (𝓝 (φ y))) {v w : H}
    (hw : Tendsto (fun i => F.boundedCalculus (b i) v) l (𝓝 w)) :
    v ∈ F.calculusDomain φ := by
  obtain ⟨u, hu⟩ := exists_seq_tendsto l
  have := hV.isFiniteMeasure v
  have hint : ∀ n : ℕ, ∫⁻ y, ‖b (u n) y‖ₑ ^ 2 ∂F.diagMeasure v =
      ENNReal.ofReal (‖F.boundedCalculus (b (u n)) v‖ ^ 2) := by
    intro n
    obtain ⟨hm, C, hC⟩ := hbb (u n)
    have hi : Integrable (fun y => ‖b (u n) y‖ ^ 2) (F.diagMeasure v) := by
      refine Integrable.of_bound (C := C ^ 2) (hm.norm.pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC y) 2
    rw [hB.norm_sq _ (hbb (u n)) v, ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun y => by positivity)]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hpt : ∀ y, Tendsto (fun n => ‖b (u n) y‖ₑ ^ 2) atTop (𝓝 (‖φ y‖ₑ ^ 2)) := fun y =>
    ENNReal.Tendsto.pow ((continuous_enorm.tendsto _).comp ((hlim y).comp hu))
  have hlimit : Tendsto (fun n => ∫⁻ y, ‖b (u n) y‖ₑ ^ 2 ∂F.diagMeasure v) atTop
      (𝓝 (ENNReal.ofReal (‖w‖ ^ 2))) := by
    simp only [hint]
    exact ENNReal.tendsto_ofReal (((hw.comp hu).norm).pow 2)
  have hfatou : ∫⁻ y, liminf (fun n => ‖b (u n) y‖ₑ ^ 2) atTop ∂F.diagMeasure v ≤
      liminf (fun n => ∫⁻ y, ‖b (u n) y‖ₑ ^ 2 ∂F.diagMeasure v) atTop :=
    lintegral_liminf_le fun n => ((hbb (u n)).1.enorm.pow_const 2)
  change ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂F.diagMeasure v < ∞
  calc ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂F.diagMeasure v
      = ∫⁻ y, liminf (fun n => ‖b (u n) y‖ₑ ^ 2) atTop ∂F.diagMeasure v :=
        lintegral_congr fun y => (hpt y).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ y, ‖b (u n) y‖ₑ ^ 2 ∂F.diagMeasure v) atTop := hfatou
    _ = ENNReal.ofReal (‖w‖ ^ 2) := hlimit.liminf_eq
    _ < ∞ := ENNReal.ofReal_lt_top
theorem generator_of_tendsto (hB : BoundedCalculusLaws F) (hV : ValuesAndDiagMeasures F)
    (hF : UnboundedCalculusLaws F)
    {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {b : ι → Y → ℂ} {φ : Y → ℂ}
    (hbb : ∀ i, IsBoundedMeasurable (b i)) (hφ : Measurable φ)
    (hle : ∀ i y, ‖b i y‖ ≤ ‖φ y‖) (hlim : ∀ y, Tendsto (fun i => b i y) l (𝓝 (φ y))) (v : H) :
    (v ∈ F.calculusDomain φ ↔ ∃ w, Tendsto (fun i => F.boundedCalculus (b i) v) l (𝓝 w)) ∧
      (v ∈ F.calculusDomain φ →
        Tendsto (fun i => F.boundedCalculus (b i) v) l (𝓝 (F.calculusLimit φ v))) := by
  have hdirect : v ∈ F.calculusDomain φ →
      Tendsto (fun i => F.boundedCalculus (b i) v) l (𝓝 (F.calculusLimit φ v)) := by
    intro hv
    refine tendsto_boundedCalculus_of_dominated hF hbb hφ hv (G := fun y => 4 * ‖φ y‖ ^ 2)
      ((integrable_norm_sq_of_mem_calculusDomain hφ hv).const_mul 4) (fun i y => ?_) hlim
    have h₁ : ‖b i y - φ y‖ ≤ 2 * ‖φ y‖ := by
      have := norm_sub_le (b i y) (φ y)
      linarith [hle i y]
    calc ‖b i y - φ y‖ ^ 2 ≤ (2 * ‖φ y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
      _ = 4 * ‖φ y‖ ^ 2 := by ring
  exact ⟨⟨fun hv => ⟨_, hdirect hv⟩, fun ⟨w, hw⟩ => mem_calculusDomain_of_tendsto hB hV hbb hlim hw⟩,
    hdirect⟩
theorem mem_pmapKernel_calculusOperator_iff (hF : UnboundedCalculusLaws F) {φ : Y → ℂ}
    (hφ : Measurable φ) (v : H) :
    v ∈ pmapKernel (F.calculusOperator φ) ↔
      v ∈ F.calculusDomain φ ∧ F.calculusLimit φ v = 0 := by
  have h₁ := hF.isCalculusOperator φ hφ
  constructor
  · rintro ⟨h, h₀⟩
    have hv : v ∈ F.calculusDomain φ := by
      rw [← h₁.1]
      exact h
    exact ⟨hv, (h₁.2 ⟨v, h⟩).symm.trans h₀⟩
  · rintro ⟨hv, h₀⟩
    have h : v ∈ (F.calculusOperator φ).domain := by
      have : v ∈ ((F.calculusOperator φ).domain : Set H) := by
        rw [h₁.1]
        exact hv
      exact this
    exact ⟨h, (h₁.2 ⟨v, h⟩).trans h₀⟩
end Calculus
section Generators
theorem isBoundedMeasurable_laplaceFourierExp (t : ℝ≥0) (y : Momentum3) :
    IsBoundedMeasurable (laplaceFourierExp t y) :=
  ⟨(continuous_laplaceFourierExp t y).measurable, 1, norm_laplaceFourierExp_le_one t y⟩
theorem measurable_energyCoord : Measurable coordEnergy :=
  Complex.measurable_ofReal.comp (measurable_coe_nnreal_real.comp measurable_fst)
theorem measurable_momentumComponent (i : Fin 3) :
    Measurable fun p : EnergyMomentumSpace => p.2 i :=
  ((EuclideanSpace.proj i).continuous.comp continuous_snd).measurable
theorem measurable_momentumCoord (i : Fin 3) : Measurable (coordMomentum i) :=
  Complex.measurable_ofReal.comp (measurable_momentumComponent i)
theorem laplaceFourierExp_zero_apply (t : ℝ≥0) (p : EnergyMomentumSpace) :
    laplaceFourierExp t 0 p = ((Real.exp (-(t : ℝ) * (p.1 : ℝ)) : ℝ) : ℂ) := by
  simp [laplaceFourierExp, spatialDot]
theorem laplaceFourierExp_single_apply (s : ℝ) (i : Fin 3) (p : EnergyMomentumSpace) :
    laplaceFourierExp 0 (s • EuclideanSpace.single i (1 : ℝ)) p =
      Complex.exp (Complex.I * ((s * p.2 i : ℝ) : ℂ)) := by
  have h : spatialDot (s • EuclideanSpace.single i (1 : ℝ)) p.2 = s * p.2 i := by
    simp [spatialDot]
  simp [laplaceFourierExp, h]
def energySlope (t : ℝ≥0) : EnergyMomentumSpace → ℂ :=
  (((t : ℝ)⁻¹ : ℝ) : ℂ) • (1 - laplaceFourierExp t 0)
def momentumSlope (i : Fin 3) (s : ℝ) : EnergyMomentumSpace → ℂ :=
  (-(Complex.I * (s : ℂ))⁻¹) • (1 - laplaceFourierExp 0 (s • EuclideanSpace.single i (1 : ℝ)))
theorem energySlope_apply (t : ℝ≥0) (p : EnergyMomentumSpace) :
    energySlope t p =
      (((t : ℝ)⁻¹ * (1 - Real.exp (-(t : ℝ) * (p.1 : ℝ))) : ℝ) : ℂ) := by
  simp [energySlope, laplaceFourierExp_zero_apply]
theorem norm_energySlope_le (t : ℝ≥0) (p : EnergyMomentumSpace) :
    ‖energySlope t p‖ ≤ ‖coordEnergy p‖ := by
  have hE : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2
  have hT : (0 : ℝ) ≤ (t : ℝ) := t.2
  have hTE : 0 ≤ (t : ℝ) * (p.1 : ℝ) := mul_nonneg hT hE
  have h₁ : 0 ≤ 1 - Real.exp (-(t : ℝ) * (p.1 : ℝ)) := by
    have : Real.exp (-(t : ℝ) * (p.1 : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have h₂ : 1 - Real.exp (-(t : ℝ) * (p.1 : ℝ)) ≤ (t : ℝ) * (p.1 : ℝ) := by
    have := Real.add_one_le_exp (-(t : ℝ) * (p.1 : ℝ))
    linarith
  rw [energySlope_apply, coordEnergy, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hT) h₁), Real.norm_of_nonneg hE]
  rcases eq_or_lt_of_le hT with h₀ | hpos
  · simpa [← h₀] using hE
  · calc (t : ℝ)⁻¹ * (1 - Real.exp (-(t : ℝ) * (p.1 : ℝ)))
        ≤ (t : ℝ)⁻¹ * ((t : ℝ) * (p.1 : ℝ)) :=
          mul_le_mul_of_nonneg_left h₂ (inv_nonneg.2 hT)
      _ = (p.1 : ℝ) := by field_simp
theorem tendsto_energySlope (p : EnergyMomentumSpace) :
    Tendsto (fun t => energySlope t p) (𝓝[>] 0) (𝓝 (coordEnergy p)) := by
  have hd : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x * (p.1 : ℝ))) (p.1 : ℝ) 0 := by
    have h₁ : HasDerivAt (fun x : ℝ => -x * (p.1 : ℝ)) (-(p.1 : ℝ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).neg.mul_const (p.1 : ℝ))
    simpa using h₁.exp.const_sub 1
  have h := hd.tendsto_slope_zero_right
  have hc : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨(NNReal.continuous_coe.tendsto' 0 0 rfl).mono_left nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin.mono fun t ht => NNReal.coe_pos.2 ht⟩
  have h' := (Complex.continuous_ofReal.tendsto _).comp (h.comp hc)
  refine h'.congr fun t => ?_
  simp [energySlope_apply]
theorem momentumSlope_apply (i : Fin 3) (s : ℝ) (p : EnergyMomentumSpace) :
    momentumSlope i s p = (Complex.I * (s : ℂ))⁻¹ *
      (Complex.exp (Complex.I * ((s * p.2 i : ℝ) : ℂ)) - 1) := by
  simp only [momentumSlope, Pi.smul_apply, Pi.sub_apply, Pi.one_apply,
    laplaceFourierExp_single_apply, smul_eq_mul]
  ring
theorem norm_momentumSlope_le (i : Fin 3) (s : ℝ) (p : EnergyMomentumSpace) :
    ‖momentumSlope i s p‖ ≤ ‖coordMomentum i p‖ := by
  rw [momentumSlope_apply, coordMomentum, Complex.norm_real]
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  · have h₁ := Real.norm_exp_I_mul_ofReal_sub_one_le (x := s * p.2 i)
    have hs' : 0 < ‖s‖ := norm_pos_iff.2 hs
    rw [norm_mul, norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    calc ‖s‖⁻¹ * ‖Complex.exp (Complex.I * ((s * p.2 i : ℝ) : ℂ)) - 1‖
        ≤ ‖s‖⁻¹ * ‖s * p.2 i‖ := mul_le_mul_of_nonneg_left h₁ (inv_nonneg.2 hs'.le)
      _ = ‖p.2 i‖ := by
        rw [norm_mul]
        field_simp
theorem tendsto_momentumSlope (i : Fin 3) (p : EnergyMomentumSpace) :
    Tendsto (fun s => momentumSlope i s p) (𝓝[≠] 0) (𝓝 (coordMomentum i p)) := by
  have hz : HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * (z * ((p.2 i : ℝ) : ℂ))))
      (Complex.I * ((p.2 i : ℝ) : ℂ)) ((0 : ℝ) : ℂ) := by
    have h₁ : HasDerivAt (fun z : ℂ => Complex.I * (z * ((p.2 i : ℝ) : ℂ)))
        (Complex.I * ((p.2 i : ℝ) : ℂ)) ((0 : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id (((0 : ℝ) : ℂ))).mul_const ((p.2 i : ℝ) : ℂ)).const_mul Complex.I
    simpa using h₁.cexp
  have h := (hz.comp_ofReal.tendsto_slope_zero).const_mul Complex.I⁻¹
  have he : Complex.I⁻¹ * (Complex.I * ((p.2 i : ℝ) : ℂ)) = coordMomentum i p := by
    rw [inv_mul_cancel_left₀ Complex.I_ne_zero]
    rfl
  rw [he] at h
  refine h.congr fun s => ?_
  rw [momentumSlope_apply]
  simp only [zero_add, Complex.ofReal_zero, zero_mul, mul_zero, Complex.exp_zero,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, mul_inv]
  ring
theorem isBoundedMeasurable_energySlope (t : ℝ≥0) : IsBoundedMeasurable (energySlope t) :=
  isBoundedMeasurable_smul_one_sub (isBoundedMeasurable_laplaceFourierExp t 0) _
theorem isBoundedMeasurable_momentumSlope (i : Fin 3) (s : ℝ) :
    IsBoundedMeasurable (momentumSlope i s) :=
  isBoundedMeasurable_smul_one_sub (isBoundedMeasurable_laplaceFourierExp 0 _) _
theorem mem_zeroEnergySet_iff (p : EnergyMomentumSpace) :
    p ∈ zeroEnergySet.1 ↔ coordEnergy p = 0 := by
  simp [zeroEnergySet, coordEnergy, Set.mem_prod]
theorem mem_zeroMomentumSet_iff (i : Fin 3) (p : EnergyMomentumSpace) :
    p ∈ (zeroMomentumSet i).1 ↔ coordMomentum i p = 0 := by
  simp [zeroMomentumSet, coordMomentum]
theorem measureIsCarriedBy_iff_ae_eq_zero {m : Measure EnergyMomentumSpace}
    (Z : BorelSubsets EnergyMomentumSpace) (f : EnergyMomentumSpace → ℂ)
    (hZ : ∀ p, p ∈ Z.1 ↔ f p = 0) : MeasureIsCarriedBy m Z ↔ f =ᵐ[m] 0 := by
  rw [MeasureIsCarriedBy, Filter.EventuallyEq, ae_iff]
  have h : Z.1ᶜ = {p | ¬f p = (0 : EnergyMomentumSpace → ℂ) p} := by
    ext p
    simp [hZ p]
  rw [h]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {S : ℝ≥0 → H →L[ℂ] H} {V : Momentum3 → H →L[ℂ] H}
theorem unitaryGroup_zero (h : IsContractionSemigroupWithUnitaryGroup S V) : V 0 = 1 := by
  have h₁ := h.group_add 0 0
  rw [add_zero] at h₁
  ext v
  refine (h.isUnitary 0).bijective.1 ?_
  simpa using congrArg (fun T : H →L[ℂ] H => T v) h₁
theorem semigroup_eq_boundedCalculus (h : IsContractionSemigroupWithUnitaryGroup S V)
    (hj : IsJointSpectralMeasure S V (jointSpectralMeasure S V)) (t : ℝ≥0) :
    S t = (jointSpectralMeasure S V).boundedCalculus (laplaceFourierExp t 0) := by
  have h₁ := hj t 0
  rwa [unitaryGroup_zero h, mul_one] at h₁
theorem unitaryGroup_eq_boundedCalculus (h : IsContractionSemigroupWithUnitaryGroup S V)
    (hj : IsJointSpectralMeasure S V (jointSpectralMeasure S V)) (y : Momentum3) :
    V y = (jointSpectralMeasure S V).boundedCalculus (laplaceFourierExp 0 y) := by
  have h₁ := hj 0 y
  rwa [h.semigroup_zero, one_mul] at h₁
theorem energyDiffQuot_eq (h : IsContractionSemigroupWithUnitaryGroup S V)
    (hj : IsJointSpectralMeasure S V (jointSpectralMeasure S V))
    (hB : BoundedCalculusLaws (jointSpectralMeasure S V)) (v : H) (t : ℝ≥0) :
    energyDiffQuot S v t = (jointSpectralMeasure S V).boundedCalculus (energySlope t) v := by
  rw [energySlope, boundedCalculus_smul_one_sub_apply hB (isBoundedMeasurable_laplaceFourierExp t 0),
    ← semigroup_eq_boundedCalculus h hj]
  rfl
theorem momentumDiffQuot_eq (h : IsContractionSemigroupWithUnitaryGroup S V)
    (hj : IsJointSpectralMeasure S V (jointSpectralMeasure S V))
    (hB : BoundedCalculusLaws (jointSpectralMeasure S V)) (i : Fin 3) (v : H) (s : ℝ) :
    momentumDiffQuot V i v s =
      (jointSpectralMeasure S V).boundedCalculus (momentumSlope i s) v := by
  rw [momentumSlope, boundedCalculus_smul_one_sub_apply hB (isBoundedMeasurable_laplaceFourierExp 0 _),
    ← unitaryGroup_eq_boundedCalculus h hj, neg_smul, ← smul_neg, neg_sub]
  rfl
theorem generatorsSelfAdjoint (hF : UnboundedCalculusLaws (jointSpectralMeasure S V)) :
    GeneratorsSelfAdjoint S V := by
  refine ⟨hF.isSelfAdjoint (fun p => (p.1 : ℝ)) (measurable_coe_nnreal_real.comp measurable_fst),
    fun i => hF.isSelfAdjoint (fun p => p.2 i) (measurable_momentumComponent i), fun v => ?_⟩
  have hd := hF.isCalculusOperator coordEnergy measurable_energyCoord
  have hv : (v : H) ∈ (jointSpectralMeasure S V).calculusDomain coordEnergy := by
    rw [← hd.1]
    exact v.2
  have h₁ := hF.inner_eq coordEnergy measurable_energyCoord v hv
  have h₂ : hamiltonian S V v = (jointSpectralMeasure S V).calculusLimit coordEnergy v := hd.2 v
  rw [h₂, h₁]
  have h₃ : ∫ p, coordEnergy p ∂(jointSpectralMeasure S V).diagMeasure v =
      ((∫ p : EnergyMomentumSpace, (p.1 : ℝ) ∂(jointSpectralMeasure S V).diagMeasure v : ℝ) : ℂ) :=
    integral_ofReal
  rw [h₃, Complex.ofReal_re]
  exact integral_nonneg fun p => p.1.2
theorem hamiltonianGenerates_of_calculus (h : IsContractionSemigroupWithUnitaryGroup S V)
    (hj : IsJointSpectralMeasure S V (jointSpectralMeasure S V))
    (hV : ValuesAndDiagMeasures (jointSpectralMeasure S V))
    (hB : BoundedCalculusLaws (jointSpectralMeasure S V))
    (hF : UnboundedCalculusLaws (jointSpectralMeasure S V)) : HamiltonianGenerates S V := by
  have key := fun v => generator_of_tendsto hB hV hF (l := 𝓝[>] (0 : ℝ≥0)) (b := energySlope)
    (φ := coordEnergy) isBoundedMeasurable_energySlope measurable_energyCoord norm_energySlope_le
    tendsto_energySlope v
  have hq : ∀ v, energyDiffQuot S v =
      fun t => (jointSpectralMeasure S V).boundedCalculus (energySlope t) v :=
    fun v => funext (energyDiffQuot_eq h hj hB v)
  have hd := hF.isCalculusOperator coordEnergy measurable_energyCoord
  have hmem : ∀ v, v ∈ (hamiltonian S V).domain ↔
      v ∈ (jointSpectralMeasure S V).calculusDomain coordEnergy :=
    fun v => Set.ext_iff.1 hd.1 v
  refine ⟨fun v => ?_, fun v => ?_⟩
  · rw [hq v, hmem v]
    exact (key v).1
  · have h₂ : hamiltonian S V v = (jointSpectralMeasure S V).calculusLimit coordEnergy v := hd.2 v
    rw [hq, h₂]
    exact (key v).2 ((hmem v).1 v.2)
theorem momentumGenerates_of_calculus (h : IsContractionSemigroupWithUnitaryGroup S V)
    (hj : IsJointSpectralMeasure S V (jointSpectralMeasure S V))
    (hV : ValuesAndDiagMeasures (jointSpectralMeasure S V))
    (hB : BoundedCalculusLaws (jointSpectralMeasure S V))
    (hF : UnboundedCalculusLaws (jointSpectralMeasure S V)) (i : Fin 3) :
    MomentumGenerates S V i := by
  have key := fun v => generator_of_tendsto hB hV hF (l := 𝓝[≠] (0 : ℝ)) (b := momentumSlope i)
    (φ := coordMomentum i) (isBoundedMeasurable_momentumSlope i) (measurable_momentumCoord i)
    (norm_momentumSlope_le i) (tendsto_momentumSlope i) v
  have hq : ∀ v, momentumDiffQuot V i v =
      fun s => (jointSpectralMeasure S V).boundedCalculus (momentumSlope i s) v :=
    fun v => funext (momentumDiffQuot_eq h hj hB i v)
  have hd := hF.isCalculusOperator (coordMomentum i) (measurable_momentumCoord i)
  have hmem : ∀ v, v ∈ (momentumOp S V i).domain ↔
      v ∈ (jointSpectralMeasure S V).calculusDomain (coordMomentum i) :=
    fun v => Set.ext_iff.1 hd.1 v
  refine ⟨fun v => ?_, fun v => ?_⟩
  · rw [hq v, hmem v]
    exact (key v).1
  · have h₂ : momentumOp S V i v =
        (jointSpectralMeasure S V).calculusLimit (coordMomentum i) v := hd.2 v
    rw [hq, h₂]
    exact (key v).2 ((hmem v).1 v.2)
theorem hamiltonianKernel_of_calculus (h : IsContractionSemigroupWithUnitaryGroup S V)
    (hj : IsJointSpectralMeasure S V (jointSpectralMeasure S V))
    (hV : ValuesAndDiagMeasures (jointSpectralMeasure S V))
    (hB : BoundedCalculusLaws (jointSpectralMeasure S V))
    (hF : UnboundedCalculusLaws (jointSpectralMeasure S V)) : HamiltonianKernel S V := by
  have hker : ∀ v, v ∈ pmapKernel (hamiltonian S V) ↔
      coordEnergy =ᵐ[(jointSpectralMeasure S V).diagMeasure v] 0 := fun v =>
    (mem_pmapKernel_calculusOperator_iff hF measurable_energyCoord v).trans
      (calculusLimit_eq_zero_iff hF measurable_energyCoord v)
  have hcar : ∀ v, MeasureIsCarriedBy ((jointSpectralMeasure S V).diagMeasure v) zeroEnergySet ↔
      coordEnergy =ᵐ[(jointSpectralMeasure S V).diagMeasure v] 0 := fun v =>
    measureIsCarriedBy_iff_ae_eq_zero _ _ mem_zeroEnergySet_iff
  have hproj : ∀ v, jointSpectralMeasure S V zeroEnergySet v = v ↔
      coordEnergy =ᵐ[(jointSpectralMeasure S V).diagMeasure v] 0 := fun v =>
    (apply_eq_self_iff_measureIsCarriedBy hB hF _ v).trans (hcar v)
  have hfix : ∀ v, (∀ t, S t v = v) ↔
      coordEnergy =ᵐ[(jointSpectralMeasure S V).diagMeasure v] 0 := by
    intro v
    constructor
    · intro hs
      have h₁ := (boundedCalculus_apply_eq_self_iff hB hF
        (isBoundedMeasurable_laplaceFourierExp 1 0) v).1
        (by rw [← semigroup_eq_boundedCalculus h hj]; exact hs 1)
      filter_upwards [h₁] with p hp
      rw [laplaceFourierExp_zero_apply] at hp
      have hp' : ((Real.exp (-((1 : ℝ≥0) : ℝ) * (p.1 : ℝ)) : ℝ) : ℂ) = 1 := hp
      have h₂ : Real.exp (-((1 : ℝ≥0) : ℝ) * (p.1 : ℝ)) = 1 := by
        exact_mod_cast hp'
      rw [Real.exp_eq_one_iff] at h₂
      have h₃ : (p.1 : ℝ) = 0 := by simpa using h₂
      simp [coordEnergy, h₃]
    · intro he t
      rw [semigroup_eq_boundedCalculus h hj t]
      refine (boundedCalculus_apply_eq_self_iff hB hF
        (isBoundedMeasurable_laplaceFourierExp t 0) v).2 ?_
      filter_upwards [he] with p hp
      have h₃ : (p.1 : ℝ) = 0 := by simpa [coordEnergy] using hp
      rw [laplaceFourierExp_zero_apply, h₃]
      simp
  refine ⟨fun v => ?_, (hV.isOrthProjection _), ?_, fun v => ?_⟩
  · refine List.tfae_of_forall (coordEnergy =ᵐ[(jointSpectralMeasure S V).diagMeasure v] 0) _ ?_
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hker v
    · exact hfix v
    · exact hcar v
    · exact hproj v
  · ext v
    exact (hproj v).trans (hker v).symm
  · have hfin := hV.isFiniteMeasure v
    have hbd := isBoundedMeasurable_indicator_one (zeroEnergySet)
    have h₁ := tendsto_boundedCalculus_of_dominated hF (l := (atTop : Filter ℝ≥0))
      (F := jointSpectralMeasure S V)
      (b := fun t => laplaceFourierExp t 0) (φ := zeroEnergySet.1.indicator 1)
      (fun t => isBoundedMeasurable_laplaceFourierExp t 0) hbd.1
      (mem_calculusDomain_of_bounded hF hbd v) (G := fun _ => 4) (integrable_const _)
      (fun t p => ?_) (fun p => ?_)
    · rw [calculusLimit_eq_boundedCalculus hF hbd, hB.indicator] at h₁
      refine h₁.congr fun t => ?_
      rw [← semigroup_eq_boundedCalculus h hj]
    · have h₂ : ‖zeroEnergySet.1.indicator (1 : EnergyMomentumSpace → ℂ) p‖ ≤ 1 := by
        by_cases hp : p ∈ zeroEnergySet.1 <;> simp [hp]
      have h₃ : ‖laplaceFourierExp t 0 p - zeroEnergySet.1.indicator 1 p‖ ≤ 2 := by
        have := norm_sub_le (laplaceFourierExp t 0 p) (zeroEnergySet.1.indicator 1 p)
        have := norm_laplaceFourierExp_le_one t 0 p
        linarith
      calc ‖laplaceFourierExp t 0 p - zeroEnergySet.1.indicator 1 p‖ ^ 2 ≤ 2 ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h₃ 2
        _ = 4 := by norm_num
    · by_cases hp : p ∈ zeroEnergySet.1
      · have h₃ : (p.1 : ℝ) = 0 := by
          simpa [coordEnergy] using (mem_zeroEnergySet_iff p).1 hp
        simp only [laplaceFourierExp_zero_apply, h₃, indicator_of_mem hp]
        simp
      · have h₃ : 0 < (p.1 : ℝ) := by
          refine lt_of_le_of_ne p.1.2 fun h₄ => hp ((mem_zeroEnergySet_iff p).2 ?_)
          simp [coordEnergy, ← h₄]
        rw [indicator_of_notMem hp]
        have h₄ : Tendsto (fun t : ℝ≥0 => -(t : ℝ) * (p.1 : ℝ)) atTop atBot := by
          have h₅ : Tendsto (fun t : ℝ≥0 => (t : ℝ) * (p.1 : ℝ)) atTop atTop :=
            (NNReal.tendsto_coe_atTop.2 tendsto_id).atTop_mul_const h₃
          exact (tendsto_neg_atTop_atBot.comp h₅).congr fun t => by simp [neg_mul]
        have h₅ : Tendsto (fun t : ℝ≥0 => ((Real.exp (-(t : ℝ) * (p.1 : ℝ)) : ℝ) : ℂ)) atTop
            (𝓝 ((0 : ℝ) : ℂ)) :=
          (Complex.continuous_ofReal.tendsto 0).comp (Real.tendsto_exp_atBot.comp h₄)
        rw [Complex.ofReal_zero] at h₅
        simp only [laplaceFourierExp_zero_apply]
        exact h₅
theorem momentumKernel_of_calculus (h : IsContractionSemigroupWithUnitaryGroup S V)
    (hj : IsJointSpectralMeasure S V (jointSpectralMeasure S V))
    (hV : ValuesAndDiagMeasures (jointSpectralMeasure S V))
    (hB : BoundedCalculusLaws (jointSpectralMeasure S V))
    (hF : UnboundedCalculusLaws (jointSpectralMeasure S V)) (i : Fin 3) :
    MomentumKernel S V i := by
  intro v
  have hker : v ∈ pmapKernel (momentumOp S V i) ↔
      coordMomentum i =ᵐ[(jointSpectralMeasure S V).diagMeasure v] 0 :=
    (mem_pmapKernel_calculusOperator_iff hF (measurable_momentumCoord i) v).trans
      (calculusLimit_eq_zero_iff hF (measurable_momentumCoord i) v)
  have hcar : MeasureIsCarriedBy ((jointSpectralMeasure S V).diagMeasure v)
      (zeroMomentumSet i) ↔
      coordMomentum i =ᵐ[(jointSpectralMeasure S V).diagMeasure v] 0 :=
    measureIsCarriedBy_iff_ae_eq_zero _ _ (mem_zeroMomentumSet_iff i)
  have hfix : (∀ s : ℝ, V (s • EuclideanSpace.single i (1 : ℝ)) v = v) ↔
      coordMomentum i =ᵐ[(jointSpectralMeasure S V).diagMeasure v] 0 := by
    constructor
    · intro hs
      have key := generator_of_tendsto hB hV hF (l := 𝓝[≠] (0 : ℝ)) (b := momentumSlope i)
        (φ := coordMomentum i) (isBoundedMeasurable_momentumSlope i) (measurable_momentumCoord i)
        (norm_momentumSlope_le i) (tendsto_momentumSlope i) v
      have hq : (fun s => (jointSpectralMeasure S V).boundedCalculus (momentumSlope i s) v) =
          fun _ => (0 : H) := by
        funext s
        rw [← momentumDiffQuot_eq h hj hB i v s]
        simp [momentumDiffQuot, hs s]
      have hmem := key.1.2 ⟨0, by rw [hq]; exact tendsto_const_nhds⟩
      have hl := key.2 hmem
      rw [hq] at hl
      exact (calculusLimit_eq_zero_iff hF (measurable_momentumCoord i) v).1
        ⟨hmem, tendsto_nhds_unique hl tendsto_const_nhds⟩
    · intro he s
      rw [unitaryGroup_eq_boundedCalculus h hj]
      refine (boundedCalculus_apply_eq_self_iff hB hF
        (isBoundedMeasurable_laplaceFourierExp 0 _) v).2 ?_
      filter_upwards [he] with p hp
      have h₃ : p.2 i = 0 := by simpa [coordMomentum] using hp
      rw [laplaceFourierExp_single_apply, h₃]
      simp
  refine List.tfae_of_forall (coordMomentum i =ᵐ[(jointSpectralMeasure S V).diagMeasure v] 0) _ ?_
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact hker
  · exact hfix
  · exact hcar
end Generators
theorem generatorsTheorem_holds (hcal : FunctionalCalculusHolds)
    (hjoint : JointSpectralMeasureTheorem) : GeneratorsTheorem := by
  intro H _ _ _ S V h
  obtain ⟨hV, hB, -, -, -, hF, -⟩ := hcal EnergyMomentumSpace H (jointSpectralMeasure S V)
  have hj := (hjoint H S V h).1.1
  exact ⟨generatorsSelfAdjoint hF, hamiltonianGenerates_of_calculus h hj hV hB hF,
    momentumGenerates_of_calculus h hj hV hB hF, hamiltonianKernel_of_calculus h hj hV hB hF,
    momentumKernel_of_calculus h hj hV hB hF⟩
end YangMills.Construction.EnergyMomentum.GeneratorsProof
