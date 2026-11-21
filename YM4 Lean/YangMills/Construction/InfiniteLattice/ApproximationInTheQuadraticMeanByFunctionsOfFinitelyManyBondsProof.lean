import YangMills.Construction.InfiniteLattice.ApproximationInTheQuadraticMeanByFunctionsOfFinitelyManyBonds
import YangMills.Construction.InfiniteLattice.FactsFromTopologyMeasureAndFunctionTheory
import YangMills.Construction.InfiniteLattice.FunctionsOfTheBondsOfASetAndSupports
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter YangMills.Construction.InfiniteLattice
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing.QuadraticMeanApproximation
theorem secondCountableTopology_matrix : SecondCountableTopology Matrices.ComplexMatrix2 :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
attribute [local instance] secondCountableTopology_matrix
theorem secondCountableTopology_specialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
  TopologicalSpace.Subtype.secondCountableTopology _
attribute [local instance] secondCountableTopology_specialUnitary
theorem t2Space_matrix : T2Space Matrices.ComplexMatrix2 :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → ℂ))
attribute [local instance] t2Space_matrix
open Classical in
def unitOff {ι : Type} (I : Set ι) (V : LinkVariables ι) : LinkVariables ι :=
  fun i => if i ∈ I then V i else 1
theorem continuous_unitOff {ι : Type} (I : Set ι) : Continuous (unitOff I) := by
  classical
  refine continuous_pi fun i => ?_
  by_cases hi : i ∈ I
  · simpa [unitOff, hi] using continuous_apply i
  · simpa [unitOff, hi] using continuous_const
theorem dependsOnCoords_unitOff {ι : Type} (I : Set ι) (g : LinkVariables ι → ℂ) :
    DependsOnCoords I (fun V => g (unitOff I V)) := by
  classical
  intro V W hVW
  refine congrArg g (funext fun i => ?_)
  by_cases hi : i ∈ I
  · simp [unitOff, hi, hVW i hi]
  · simp [unitOff, hi]
theorem exists_finite_unitOff_close {ι : Type} (g : LinkVariables ι → ℂ) (hg : Continuous g)
    (ε : ℝ) (hε : 0 < ε) : ∃ I : Set ι, I.Finite ∧ ∀ V, ‖g V - g (unitOff I V)‖ < ε := by
  let _ : UniformSpace Matrices.ComplexMatrix2.specialUnitary := uniformSpaceOfCompactR1
  have hunif : UniformContinuous g := CompactSpace.uniformContinuous_of_continuous hg
  have hmem : {p : LinkVariables ι × LinkVariables ι | dist (g p.1) (g p.2) < ε} ∈
      uniformity (LinkVariables ι) := hunif (Metric.dist_mem_uniformity hε)
  rw [Pi.uniformity, Filter.mem_iInf] at hmem
  obtain ⟨I, hI, W, hW, hEq⟩ := hmem
  refine ⟨I, hI, fun V => ?_⟩
  have hV : (V, unitOff I V) ∈
      {p : LinkVariables ι × LinkVariables ι | dist (g p.1) (g p.2) < ε} := by
    rw [hEq]
    refine mem_iInter.2 fun i => ?_
    obtain ⟨T, hT, hsub⟩ := mem_comap.1 (hW i)
    apply hsub
    have hi : unitOff I V i.1 = V i.1 := if_pos i.2
    change (V i.1, unitOff I V i.1) ∈ T
    rw [hi]
    exact refl_mem_uniformity hT
  simpa [dist_eq_norm] using hV
theorem add_sq_le_four_mul (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 4 * x ^ 2 + 4 * y ^ 2 := by
  rcases le_total x y with hxy | hxy
  · calc (x + y) ^ 2 ≤ (y + y) ^ 2 := by gcongr
      _ = 4 * y ^ 2 := by ring
      _ ≤ 4 * x ^ 2 + 4 * y ^ 2 := le_add_self
  · calc (x + y) ^ 2 ≤ (x + x) ^ 2 := by gcongr
      _ = 4 * x ^ 2 := by ring
      _ ≤ 4 * x ^ 2 + 4 * y ^ 2 := le_self_add
theorem exists_continuous_finitely_dependent_approx {ι : Type} [Countable ι]
    (hdense : InfiniteLattice.AmbientFacts.ContinuousDenseInMeanSquare)
    (μ : Measure (LinkVariables ι)) [IsProbabilityMeasure μ] (f : LinkVariables ι → ℂ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ V, ‖f V‖ ≤ C) :
    ∃ h : ℕ → LinkVariables ι → ℂ,
      (∀ k, Continuous (h k) ∧ ∃ I : Set ι, I.Finite ∧ DependsOnCoords I (h k)) ∧
      Tendsto (fun k => ∫⁻ V, ‖f V - h k V‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hsq : IsSqIntegrable μ f := by
    refine ⟨hf, ?_⟩
    have hle : ∀ V, ‖f V‖ₑ ^ 2 ≤ ENNReal.ofReal C ^ 2 := fun V => by
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hC V)
    calc ∫⁻ V, ‖f V‖ₑ ^ 2 ∂μ ≤ ∫⁻ _, ENNReal.ofReal C ^ 2 ∂μ := lintegral_mono hle
      _ = ENNReal.ofReal C ^ 2 := by simp
      _ < ∞ := ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  let e : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have he : ∀ k, 0 < e k := fun k => by positivity
  choose g hg hgI using fun k => (hdense (LinkVariables ι) μ).2 f hsq (e k) (he k)
  choose I hI hcut using fun k => exists_finite_unitOff_close (g k) (hg k) (e k) (he k)
  refine ⟨fun k V => g k (unitOff (I k) V), fun k =>
    ⟨(hg k).comp (continuous_unitOff (I k)), I k, hI k, dependsOnCoords_unitOff (I k) (g k)⟩, ?_⟩
  have hbound : ∀ k, ∫⁻ V, ‖f V - g k (unitOff (I k) V)‖ₑ ^ 2 ∂μ ≤
      4 * ENNReal.ofReal (e k) + 4 * ENNReal.ofReal (e k) ^ 2 := fun k => by
    have hpt : ∀ V, ‖f V - g k (unitOff (I k) V)‖ₑ ^ 2 ≤
        4 * ‖f V - g k V‖ₑ ^ 2 + 4 * ENNReal.ofReal (e k) ^ 2 := fun V => by
      have h1 : ‖f V - g k (unitOff (I k) V)‖ₑ ≤ ‖f V - g k V‖ₑ + ENNReal.ofReal (e k) := by
        have h2 : ‖g k V - g k (unitOff (I k) V)‖ₑ ≤ ENNReal.ofReal (e k) := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hcut k V).le
        calc ‖f V - g k (unitOff (I k) V)‖ₑ
            = ‖(f V - g k V) + (g k V - g k (unitOff (I k) V))‖ₑ := by congr 1; ring
          _ ≤ ‖f V - g k V‖ₑ + ‖g k V - g k (unitOff (I k) V)‖ₑ := enorm_add_le _ _
          _ ≤ _ := by gcongr
      calc ‖f V - g k (unitOff (I k) V)‖ₑ ^ 2
          ≤ (‖f V - g k V‖ₑ + ENNReal.ofReal (e k)) ^ 2 := by gcongr
        _ ≤ _ := add_sq_le_four_mul _ _
    calc ∫⁻ V, ‖f V - g k (unitOff (I k) V)‖ₑ ^ 2 ∂μ
        ≤ ∫⁻ V, (4 * ‖f V - g k V‖ₑ ^ 2 + 4 * ENNReal.ofReal (e k) ^ 2) ∂μ := lintegral_mono hpt
      _ = 4 * ∫⁻ V, ‖f V - g k V‖ₑ ^ 2 ∂μ + 4 * ENNReal.ofReal (e k) ^ 2 := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by simp)]
          simp
      _ ≤ _ := by
          gcongr
          exact hgI k
  have ht : Tendsto (fun k => ENNReal.ofReal (e k)) atTop (𝓝 0) := by
    simpa [e] using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim : Tendsto (fun k => 4 * ENNReal.ofReal (e k) + 4 * ENNReal.ofReal (e k) ^ 2) atTop
      (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (a := (4 : ℝ≥0∞)) ht (Or.inr (by simp))
    have h2 := ENNReal.Tendsto.const_mul (a := (4 : ℝ≥0∞)) (ENNReal.Tendsto.pow (n := 2) ht)
      (Or.inr (by simp))
    simpa using h1.add h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hbound
variable {a : ℝ}
theorem continuous_restrictField (𝓢 : Set (Link a)) :
    Continuous fun U : GaugeField a => restrictField U 𝓢 :=
  continuous_pi fun b => (continuous_apply b.1).comp continuous_subtype_val
theorem linkMeasurableApproximable_of
    (hfactor : LinkFunctions.Assertion)
    (hdense : InfiniteLattice.AmbientFacts.ContinuousDenseInMeanSquare)
    (ha : 0 < a) (ν : BorelProb a) : LinkMeasurableApproximable ν := by
  intro 𝓢 hS F hm hb
  obtain ⟨-, hfac, -, -⟩ := hfactor a ha
  have tfae := (hfac 𝓢 hS F hb).1
  have h01 : Measurable[linkSigma 𝓢] F ↔ Measurable F ∧ DependsOnlyOnLinks 𝓢 F := tfae.out 0 1
  have h02 : Measurable[linkSigma 𝓢] F ↔ ∃ f : LinkVariables 𝓢 → ℂ,
      LinkFunctions.IsBoundedBorelFactorization 𝓢 F f := tfae.out 0 2
  have hbor : Measurable F := (h01.1 hm).1
  obtain ⟨f, hfm, ⟨C, hC⟩, hFf⟩ := h02.1 hm
  have : IsProbabilityMeasure ν.1 := ν.2
  have hπ := continuous_restrictField 𝓢
  have hπm : Measurable fun U : GaugeField a => restrictField U 𝓢 := hπ.measurable
  have hfm' : Measurable f := by
    rw [BorelSpace.measurable_eq (α := LinkVariables 𝓢)]
    exact hfm
  have : IsProbabilityMeasure (ν.1.map fun U : GaugeField a => restrictField U 𝓢) :=
    Measure.isProbabilityMeasure_map hπm.aemeasurable
  obtain ⟨h, hh, ht⟩ := exists_continuous_finitely_dependent_approx hdense
    (ν.1.map fun U : GaugeField a => restrictField U 𝓢) f hfm' C hC
  refine ⟨fun k U => h k (restrictField U 𝓢), fun k _ => ?_, ?_⟩
  · obtain ⟨hc, I, hI, hdep⟩ := hh k
    refine ⟨hc.comp hπ, Subtype.val '' I, hI.image _, ?_, ?_⟩
    · rintro _ ⟨b, -, rfl⟩
      exact b.2
    · intro U U' hUU'
      refine hdep _ _ fun b hbI => ?_
      exact congrFun hUU' ⟨b.1, b, hbI, rfl⟩
  · refine ⟨hbor, fun k _ => ((hh k).1.comp hπ).measurable, ?_⟩
    refine ht.congr fun k => ?_
    have hmeas : Measurable fun V => ‖f V - h k V‖ₑ ^ 2 :=
      ((hfm'.sub (hh k).1.measurable).enorm).pow_const 2
    refine (lintegral_map hmeas hπm).trans (lintegral_congr fun U => ?_)
    rw [hFf U]
theorem regionMeasurableApproximable_of
    (hfactor : LinkFunctions.Assertion)
    (hdense : InfiniteLattice.AmbientFacts.ContinuousDenseInMeanSquare)
    (ha : 0 < a) (ν : BorelProb a) : RegionMeasurableApproximable ν := by
  rintro S F ⟨hm, hb⟩
  obtain ⟨hA, hfac, -, -⟩ := hfactor a ha
  have hm' : Measurable[linkSigma (positiveLinksWithin a S)] F := by
    rw [← hA.2.2.2.2 S]
    exact hm
  obtain ⟨Fk, hk, hc⟩ := linkMeasurableApproximable_of hfactor hdense ha ν _ inter_subset_left F hm' hb
  refine ⟨Fk, fun k k1 => ?_, hc⟩
  obtain ⟨hcont, W, hWf, hWS, hW⟩ := hk k k1
  have : CompactSpace (GaugeField a) := (hA.1.homeomorph _).symm.compactSpace
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  have hC' : ∃ C : ℝ, ∀ U, ‖Fk k U‖ ≤ C := ⟨C, fun U => hC U (mem_univ U)⟩
  have hWB : W ⊆ positiveLinkSet a := hWS.trans inter_subset_left
  have h10 : Measurable (Fk k) ∧ DependsOnlyOnLinks W (Fk k) ↔ Measurable[linkSigma W] (Fk k) :=
    ((hfac W hWB (Fk k) hC').1).out 1 0
  have hmeas : Measurable[linkSigma W] (Fk k) := h10.1 ⟨hcont.measurable, hW⟩
  let Y : Set AmbientSpace := (fun b : Link a => (b.initial : AmbientSpace)) '' W ∪
    (fun b : Link a => (b.terminal : AmbientSpace)) '' W
  have hY : Y.Finite := (hWf.image _).union (hWf.image _)
  have hWin : ∀ b ∈ W, b ∈ linksWithin (a := a) (S ∩ Y) := fun b hbW =>
    ⟨⟨(hWS hbW).2.1, Or.inl ⟨b, hbW, rfl⟩⟩, ⟨(hWS hbW).2.2, Or.inr ⟨b, hbW, rfl⟩⟩⟩
  have hmono : linkSigma W ≤ regionSigma (a := a) (S ∩ Y) :=
    iSup₂_le fun b hbW => le_iSup₂_of_le (f := fun b (_ : b ∈ linksWithin (a := a) (S ∩ Y)) =>
      MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) b (hWin b hbW) le_rfl
  have hmono' : linkSigma W ≤ regionSigma (a := a) S :=
    iSup₂_le fun b hbW => le_iSup₂_of_le (f := fun b (_ : b ∈ linksWithin (a := a) S) =>
      MeasurableSpace.comap (fun U : GaugeField a => U b) inferInstance) b (hWS hbW).2 le_rfl
  refine ⟨hcont, mem_iUnion₂.2 ⟨Y, hY.isBounded, hmeas.mono hmono le_rfl, hC'⟩,
    hmeas.mono hmono' le_rfl, hC'⟩
theorem statement_holds (hlinks : LinkFunctions.Assertion)
    (hfacts : InfiniteLattice.AmbientFacts.AllFacts) : Statement :=
  fun _ ha ν => ⟨linkMeasurableApproximable_of hlinks hfacts.2.1 ha ν,
    regionMeasurableApproximable_of hlinks hfacts.2.1 ha ν⟩
end YangMills.Construction.GibbsAtFixedSpacing.QuadraticMeanApproximation
