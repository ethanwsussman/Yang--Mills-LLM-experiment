import YangMills.Construction.InfiniteLattice.TorusStatesAreTheVolumeLimitPoints
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.TorusLimitCharacterization
private theorem compactSpace_gaugeField (a : ℝ) : CompactSpace (GaugeField a) := by
  have hc : IsClosed {U : Link a → Matrices.ComplexMatrix2.specialUnitary | ∀ b, U b.opposite = (U b)⁻¹} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun b => isClosed_eq (continuous_apply _) (continuous_apply _).inv
  exact isCompact_iff_compactSpace.1 hc.isCompact
abbrev _root_.YangMills.SharedProofs.p823 := @compactSpace_gaugeField
private theorem isInfiniteVolumeLimit_of_mem (L K : ℕ) (hL : 2 ≤ L) (β : ℝ)
    (μ : Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ))))
    (h : μ ∈ torusLimitSet L K β) : IsInfiniteVolumeLimit L K β μ := by
  obtain ⟨hp, n, -, hs, hA⟩ := h
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hmono : Monotone (PeriodicLattice.torusSide L) := fun a b hab => by
    unfold PeriodicLattice.torusSide
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL' hab) (by norm_num)
  have hn : StrictMono n := fun a b hab => by
    by_contra hc
    exact absurd (hs hab) (not_lt.2 (hmono (not_lt.1 hc)))
  refine ⟨hp, n, hn, fun F => ?_⟩
  have h1 := hA (fun U => ((F U : ℝ) : ℂ)) (Complex.continuous_ofReal.comp F.continuous)
  have h2 := (Complex.continuous_re.tendsto _).comp h1
  simpa [Function.comp_def, integral_complex_ofReal] using h2
private theorem isFiniteMeasure_of_integral_one_ne_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (h : ∫ _, (1 : ℝ) ∂μ ≠ 0) : IsFiniteMeasure μ := by
  refine ⟨lt_top_iff_ne_top.2 fun ht => h ?_⟩
  simp [integral_const, measureReal_def, ht]
private theorem mem_of_isInfiniteVolumeLimit (L K : ℕ) (hL : 2 ≤ L) (β : ℝ)
    (μ : Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ))))
    (h : IsInfiniteVolumeLimit L K β μ) : μ ∈ torusLimitSet L K β := by
  have := compactSpace_gaugeField (PeriodicLattice.meshSize L (K : ℤ))
  obtain ⟨hp, φ, hφ, hF⟩ := h
  have hL' : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hone := hF (BoundedContinuousFunction.const _ 1)
  simp only [BoundedContinuousFunction.const_apply] at hone
  have hμ1 : ∫ _, (1 : ℝ) ∂μ = 1 := by simp
  rw [hμ1] at hone
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hone.eventually_ne (one_ne_zero (α := ℝ)))
  have hfin : ∀ i, IsFiniteMeasure (liftedWilsonMeasure L (φ (i + (N + 1))) K β) := fun i =>
    isFiniteMeasure_of_integral_one_ne_zero (hN _ (by omega))
  refine ⟨hp, fun i => φ (i + (N + 1)), fun i => lt_of_le_of_lt (Nat.zero_le _) (hφ (show 0 < i + (N + 1) by omega)),
    fun a b hab => ?_, fun A hA => ?_⟩
  · unfold PeriodicLattice.torusSide
    exact mul_lt_mul_of_pos_left (pow_lt_pow_right₀ hL' (hφ (by omega))) (by norm_num)
  let Fr : BoundedContinuousFunction (GaugeField (PeriodicLattice.meshSize L (K : ℤ))) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun U => (A U).re, Complex.continuous_re.comp hA⟩
  let Fi : BoundedContinuousFunction (GaugeField (PeriodicLattice.meshSize L (K : ℤ))) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun U => (A U).im, Complex.continuous_im.comp hA⟩
  let Fc : BoundedContinuousFunction (GaugeField (PeriodicLattice.meshSize L (K : ℤ))) ℂ :=
    BoundedContinuousFunction.mkOfCompact ⟨A, hA⟩
  have key : ∀ (m : Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) [IsFiniteMeasure m],
      ∫ U, A U ∂m = ((∫ U, Fr U ∂m : ℝ) : ℂ) + ((∫ U, Fi U ∂m : ℝ) : ℂ) * Complex.I := by
    intro m _
    exact (integral_re_add_im (Fc.integrable m)).symm
  have h1 := (hF Fr).comp (tendsto_add_atTop_nat (N + 1))
  have h2 := (hF Fi).comp (tendsto_add_atTop_nat (N + 1))
  have h3 : Tendsto (fun i : ℕ => ((∫ U, Fr U ∂liftedWilsonMeasure L (φ (i + (N + 1))) K β : ℝ) : ℂ) +
      ((∫ U, Fi U ∂liftedWilsonMeasure L (φ (i + (N + 1))) K β : ℝ) : ℂ) * Complex.I) atTop
      (𝓝 (((∫ U, Fr U ∂μ : ℝ) : ℂ) + ((∫ U, Fi U ∂μ : ℝ) : ℂ) * Complex.I)) :=
    ((Complex.continuous_ofReal.tendsto _).comp h1).add
      (((Complex.continuous_ofReal.tendsto _).comp h2).mul_const _)
  have e : ∀ i : ℕ, ∫ U, A U ∂liftedWilsonMeasure L (φ (i + (N + 1))) K β =
      ((∫ U, Fr U ∂liftedWilsonMeasure L (φ (i + (N + 1))) K β : ℝ) : ℂ) +
      ((∫ U, Fi U ∂liftedWilsonMeasure L (φ (i + (N + 1))) K β : ℝ) : ℂ) * Complex.I := fun i => by
    have := hfin i
    exact key _
  rw [key μ]
  simpa only [e] using h3
theorem torusLimitsAreInfiniteVolumeLimits_holds : TorusLimitsAreInfiniteVolumeLimits := fun L K β hL => Set.ext fun μ =>
  ⟨isInfiniteVolumeLimit_of_mem L K hL β μ, mem_of_isInfiniteVolumeLimit L K hL β μ⟩
end YangMills.Construction.InfiniteLattice.TorusLimitCharacterization
end
