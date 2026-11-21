import YangMills.Construction.HullsInEveryVolume.KernelOfAWindowIsContinuousAndBounded
import YangMills.Construction.HullsInEveryVolume.LimitPointsReadBoundedWindows
import YangMills.Construction.HullsInEveryVolume.TheToriAreInEquilibriumInAWindow
import YangMills.Construction.InfiniteLattice.WilsonKernelOfBondsWithOneOrientation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Filter InfiniteLattice
open scoped Topology ENNReal BoundedContinuousFunction
namespace HullsInEveryVolume
namespace WindowLimits
attribute [local instance] WilsonOperator.secondCountable_specialUnitary
section Abstract
variable {a : ℝ} (W : LinkWindow a)
private theorem continuous_comp_prodMk {A X Y Z : Type*} [TopologicalSpace A] [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y → Z}
    (hf : Continuous fun p : X × Y => f p.1 p.2) {g : A → X} {h : A → Y} (hg : Continuous g)
    (hh : Continuous h) : Continuous fun t => f (g t) (h t) :=
  hf.comp (hg.prodMk hh)
private theorem secondCountable_gaugeField : SecondCountableTopology (GaugeField a) := by
  have := WilsonOperator.countable_link (a := a)
  have : SecondCountableTopology (Link a → Matrices.ComplexMatrix2.specialUnitary) := inferInstance
  exact TopologicalSpace.Subtype.secondCountableTopology
    {U : Link a → Matrices.ComplexMatrix2.specialUnitary | ∀ b, U b.opposite = (U b)⁻¹}
private theorem isProbabilityMeasure_haarProd : IsProbabilityMeasure W.haarProd := by
  unfold LinkWindow.haarProd Matrices.ComplexMatrix2.haarPi
  infer_instance
private theorem continuous_restrictInside : Continuous W.restrictInside :=
  continuous_pi fun _ => continuous_gaugeField_eval _
variable {k : W.Assignments → GaugeField a → ℝ}
private theorem measurable_uncurry_kernel
    (hk : Continuous fun x : W.Assignments × GaugeField a => k x.1 x.2) :
    Measurable (Function.uncurry k) := by
  have := secondCountable_gaugeField (a := a)
  exact hk.measurable
private theorem abs_integral_kernel_le {B : ℝ} (hk0 : ∀ V U, 0 ≤ k V U) (hkB : ∀ V U, k V U ≤ B)
    (ρ : Measure (GaugeField a)) [IsProbabilityMeasure ρ] (V : W.Assignments) :
    |∫ U, k V U ∂ρ| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := ρ) (f := fun U => k V U) (C := B)
    (ae_of_all _ fun U => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hk0 V U)]
      exact hkB V U)
  simpa using h
private theorem integral_integral_kernel_swap
    (hk : Continuous fun x : W.Assignments × GaugeField a => k x.1 x.2) {B : ℝ}
    (hk0 : ∀ V U, 0 ≤ k V U) (hkB : ∀ V U, k V U ≤ B) (ρ : Measure (GaugeField a))
    [IsProbabilityMeasure ρ] {f : W.Assignments → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ V, |f V| ≤ C) :
    ∫ U, (∫ V, f V * k V U ∂W.haarProd) ∂ρ = ∫ V, f V * ∫ U, k V U ∂ρ ∂W.haarProd := by
  have := isProbabilityMeasure_haarProd W
  have hm : Measurable fun q : GaugeField a × W.Assignments => f q.2 * k q.2 q.1 :=
    (hf.comp measurable_snd).mul ((measurable_uncurry_kernel W hk).comp measurable_swap)
  have hint : Integrable (Function.uncurry fun (U : GaugeField a) (V : W.Assignments) => f V * k V U)
      (ρ.prod W.haarProd) := by
    refine Integrable.of_bound hm.aestronglyMeasurable (C * B) (ae_of_all _ fun q => ?_)
    change ‖f q.2 * k q.2 q.1‖ ≤ C * B
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hk0 _ _)]
    exact mul_le_mul (hC _) (hkB _ _) (hk0 _ _) ((abs_nonneg _).trans (hC q.2))
  rw [integral_integral_swap hint]
  exact integral_congr_ae (ae_of_all _ fun V => integral_const_mul _ _)
private theorem tendsto_integral_window
    (hk : Continuous fun x : W.Assignments × GaugeField a => k x.1 x.2) {B : ℝ}
    (hk0 : ∀ V U, 0 ≤ k V U) (hkB : ∀ V U, k V U ≤ B) {μ : ℕ → Measure (GaugeField a)}
    {ν : Measure (GaugeField a)} [IsProbabilityMeasure ν]
    (hμ : ∀ᶠ i in atTop, IsProbabilityMeasure (μ i) ∧
      ∀ f : W.Assignments → ℝ, Measurable f → (∃ C : ℝ, ∀ V, |f V| ≤ C) →
        ∫ U, f (W.restrictInside U) ∂μ i = ∫ U, (∫ V, f V * k V U ∂W.haarProd) ∂μ i)
    (hlim : ∀ A : GaugeField a → ℝ, Continuous A →
      Tendsto (fun i => ∫ U, A U ∂μ i) atTop (𝓝 (∫ U, A U ∂ν)))
    {f : W.Assignments → ℝ} (hf : Measurable f) (hfC : ∃ C : ℝ, ∀ V, |f V| ≤ C) :
    Tendsto (fun i => ∫ U, f (W.restrictInside U) ∂μ i) atTop
      (𝓝 (∫ U, f (W.restrictInside U) ∂ν)) := by
  have := isProbabilityMeasure_haarProd W
  have := secondCountable_gaugeField (a := a)
  have hkm := measurable_uncurry_kernel W hk
  have hsec : ∀ V, Continuous (k V) := fun V =>
    continuous_comp_prodMk (f := k) hk continuous_const continuous_id
  have hqm : ∀ (ρ : Measure (GaugeField a)) [IsProbabilityMeasure ρ],
      Measurable fun V => ∫ U, k V U ∂ρ := fun ρ _ =>
    (hkm.stronglyMeasurable.integral_prod_right (ν := ρ)).measurable
  have hlimit : ∀ {g : W.Assignments → ℝ}, Measurable g → (∃ C : ℝ, ∀ V, |g V| ≤ C) →
      Tendsto (fun i => ∫ U, g (W.restrictInside U) ∂μ i) atTop
        (𝓝 (∫ V, g V * ∫ U, k V U ∂ν ∂W.haarProd)) := by
    intro g hg hgC
    obtain ⟨C, hC⟩ := hgC
    have hdom : Tendsto (fun i => ∫ V, g V * ∫ U, k V U ∂μ i ∂W.haarProd) atTop
        (𝓝 (∫ V, g V * ∫ U, k V U ∂ν ∂W.haarProd)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => C * B) ?_ ?_
        (integrable_const _) (ae_of_all _ fun V => (hlim _ (hsec V)).const_mul (g V))
      · filter_upwards [hμ] with i hi
        have := hi.1
        exact (hg.mul (hqm (μ i))).aestronglyMeasurable
      · filter_upwards [hμ] with i hi
        have := hi.1
        refine ae_of_all _ fun V => ?_
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul (hC V) (abs_integral_kernel_le W hk0 hkB (μ i) V) (abs_nonneg _)
          ((abs_nonneg _).trans (hC V))
    refine hdom.congr' ?_
    filter_upwards [hμ] with i hi
    have := hi.1
    rw [hi.2 g hg ⟨C, hC⟩, integral_integral_kernel_swap W hk hk0 hkB (μ i) hg hC]
  set q : W.Assignments → ℝ := fun V => ∫ U, k V U ∂ν with hq
  have hq0 : ∀ V, 0 ≤ q V := fun V => integral_nonneg fun U => hk0 V U
  have hqM : Measurable q := hqm ν
  have hfin : IsFiniteMeasure (W.haarProd.withDensity fun V => ENNReal.ofReal (q V)) := by
    refine isFiniteMeasure_withDensity_ofReal ?_
    exact (Integrable.of_bound hqM.aestronglyMeasurable B
      (ae_of_all _ fun V => abs_integral_kernel_le W hk0 hkB ν V)).2
  have hint : ∀ g : W.Assignments → ℝ,
      ∫ V, g V ∂(W.haarProd.withDensity fun V => ENNReal.ofReal (q V)) =
        ∫ V, g V * q V ∂W.haarProd := by
    intro g
    rw [integral_withDensity_eq_integral_toReal_smul hqM.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun V => ?_)
    simp only [ENNReal.toReal_ofReal (hq0 V), smul_eq_mul, mul_comm]
  have hcr := continuous_restrictInside W
  have hlaw : ν.map W.restrictInside = W.haarProd.withDensity fun V => ENNReal.ofReal (q V) := by
    have : IsFiniteMeasure (ν.map W.restrictInside) := by infer_instance
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
    rw [hint, integral_map hcr.aemeasurable g.continuous.aestronglyMeasurable]
    have hgC : ∃ C : ℝ, ∀ V, |g V| ≤ C := ⟨‖g‖, fun V => g.norm_coe_le_norm V⟩
    exact tendsto_nhds_unique (hlim _ (g.continuous.comp hcr)) (hlimit g.continuous.measurable hgC)
  have e : ∫ U, f (W.restrictInside U) ∂ν = ∫ V, f V * q V ∂W.haarProd := by
    rw [← hint, ← hlaw, integral_map hcr.aemeasurable hf.aestronglyMeasurable]
  rw [e]
  exact hlimit hf hfC
end Abstract
private theorem finite_windowLink (R : ℕ) : Finite (TorusLimits.WindowLink R) := by
  have hfin : {b : (Fin 4 → ℤ) × Fin 4 | TorusFields.BondOffsetInBox R b}.Finite := by
    refine ((Set.finite_Icc (fun _ : Fin 4 => -(R : ℤ)) fun _ => (R : ℤ)).prod
      (Set.finite_univ (α := Fin 4))).subset ?_
    rintro ⟨h, i⟩ ⟨hb, -⟩
    exact ⟨⟨fun μ => (abs_le.mp (hb μ)).1, fun μ => (abs_le.mp (hb μ)).2⟩, Set.mem_univ _⟩
  exact hfin.to_subtype
private def cubeLink (a : ℝ) {R : ℕ} (b : TorusLimits.WindowLink R) : Link a :=
  Link.forwardFrom (TorusLimits.latticePointOfInt a b.1.1) b.1.2
private def cubeWindow (a : ℝ) (R : ℕ) : LinkWindow a where
  links := by
    have := finite_windowLink R
    exact (Set.finite_range (cubeLink a (R := R))).toFinset
  isPositive := by
    intro b hb
    have := finite_windowLink R
    obtain ⟨c, rfl⟩ := (Set.Finite.mem_toFinset _).mp hb
    exact ⟨c.1.2, by simp [cubeLink, Link.forwardFrom]⟩
private theorem cubeLink_mem (a : ℝ) {R : ℕ} (b : TorusLimits.WindowLink R) :
    cubeLink a b ∈ (cubeWindow a R).links := by
  have := finite_windowLink R
  exact (Set.Finite.mem_toFinset _).mpr ⟨b, rfl⟩
private def toValuation (a : ℝ) (R : ℕ) (V : (cubeWindow a R).Assignments) :
    TorusLimits.WindowValuation R :=
  fun b => ((V ⟨cubeLink a b, cubeLink_mem a b⟩ : Matrices.ComplexMatrix2.specialUnitary) :
    Matrices.ComplexMatrix2)
private theorem continuous_toValuation (a : ℝ) (R : ℕ) : Continuous (toValuation a R) :=
  continuous_pi fun _ => continuous_subtype_val.comp (continuous_apply _)
private theorem measurable_comp_toValuation {R : ℕ} {G : TorusLimits.WindowValuation R → ℝ}
    (hG : TorusLimits.IsBoundedWindowObservable G) (a : ℝ) :
    Measurable (G ∘ toValuation a R) := by
  let _ : MeasurableSpace (TorusLimits.WindowValuation R) := borel _
  have : BorelSpace (TorusLimits.WindowValuation R) := ⟨rfl⟩
  exact hG.measurable.comp (continuous_toValuation a R).measurable
end WindowLimits
open WindowLimits in
theorem windowIntegralConvergence (hK : windowKernelContinuousBounded)
    (hT : torusMeasuresSatisfyWindowEquilibrium) : windowIntegralConvergenceStatement := by
  intro L K R β ν ms G _ hL hβ hlim hG
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have ha : 0 < PeriodicLattice.meshSize L (K : ℤ) := by
    unfold PeriodicLattice.meshSize
    exact zpow_pos hL0 _
  set W := cubeWindow (PeriodicLattice.meshSize L (K : ℤ)) R with hW
  obtain ⟨hc, hb, -⟩ := hK _ ha β hβ W
  obtain ⟨m₀, hm₀⟩ := hT L K β ha W hL hβ
  obtain ⟨-, hmono, hconv⟩ := hlim
  have hev : ∀ᶠ i in atTop, m₀ ≤ ms i := hmono.tendsto_atTop.eventually_ge_atTop m₀
  have hreal : ∀ A : TorusLimits.FineField L K → ℝ, Continuous A →
      Tendsto (fun i => ∫ U, A U ∂liftedWilsonMeasure L (ms i) K β) atTop
        (𝓝 (∫ U, A U ∂ν)) := by
    intro A hA
    have h := hconv (fun U => (A U : ℂ)) (Complex.continuous_ofReal.comp hA)
    simp only [integral_complex_ofReal] at h
    have h' := (Complex.continuous_re.tendsto _).comp h
    simp only [Function.comp_def, Complex.ofReal_re] at h'
    exact h'
  have hν : IsProbabilityMeasure ν := by
    have h1 := hreal (fun _ => 1) continuous_const
    have h2 : Tendsto (fun i => ∫ _U : TorusLimits.FineField L K, (1 : ℝ)
        ∂liftedWilsonMeasure L (ms i) K β) atTop (𝓝 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with i hi
      have := (hm₀ _ hi).1
      simp
    have h3 := tendsto_nhds_unique h1 h2
    simp only [integral_const, smul_eq_mul, mul_one] at h3
    refine ⟨?_⟩
    have h4 : (ν Set.univ).toReal = 1 := h3
    exact (ENNReal.toReal_eq_one_iff _).mp h4
  obtain ⟨C, hC⟩ := hG.bounded
  exact tendsto_integral_window W hc (fun V U => (Real.exp_pos _).le.trans (hb V U).1)
    (fun V U => (hb V U).2) (hev.mono fun i hi => hm₀ _ hi) hreal (measurable_comp_toValuation hG _)
    ⟨C, fun V => hC _⟩
end HullsInEveryVolume
end YangMills.Construction
end
