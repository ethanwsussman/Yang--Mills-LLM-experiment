import YangMills.Construction.BoundsOnEverySide.MapsAndTheirLimitsFreeOfAWindow
import YangMills.Construction.BoundsOnEverySide.RecentringOfALimitFreeOfAWindow
import YangMills.Construction.InfiniteLattice.CentredIdentityInAState
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.BoundsOnEverySide
namespace LimitRecentring
variable {s : Conventions.StandingParameters}
def tupleComponentFun (X : R4TupleForms.FinTuple s)
    (i : Fin (Continuum.SeparatedFourTuples.tupleLength X)) : InfiniteLattice.AmbientSpace → ℝ :=
  Continuum.SeparatedFourTuples.tupleComponents X i
theorem tupleComponentFun_mem_compactTestFunctions (X : R4TupleForms.FinTuple s)
    (i : Fin (Continuum.SeparatedFourTuples.tupleLength X)) :
    tupleComponentFun X i ∈ InfiniteLattice.compactTestFunctions := by
  have hf : SeparatedTuples.IsC1c (tupleComponentFun X i) :=
    ((R4TupleForms.mem_separatedTuples_iff_ofFn X.1.2).1 X.2).1 _
      ((List.mem_ofFn' _ _).2 ⟨i, rfl⟩)
  have hc : Continuous (tupleComponentFun X i) := ContDiff.continuous hf.1
  obtain ⟨C, hC⟩ := hf.2.exists_bound_of_continuous hc
  exact ⟨hc.measurable, ⟨C, hC⟩, hf.2⟩
theorem isBoundedRealRV_smearedEnergy_tupleComponentFun
    (hCI : InfiniteLattice.CenteredIdentity.Statement) {k : ℕ} (hk : 0 < k)
    (μ : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (k : ℤ))))
    [hμ : IsProbabilityMeasure μ] (X : R4TupleForms.FinTuple s)
    (i : Fin (Continuum.SeparatedFourTuples.tupleLength X)) :
    Probability.IsBoundedRealRV
      (InfiniteLattice.smearedEnergy (tupleComponentFun X i) :
        InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (k : ℤ)) → ℝ) :=
  ((hCI { s with K := ⟨k, hk⟩ } μ hμ).1.1 _ (tupleComponentFun_mem_compactTestFunctions X i)).2
theorem centeredProduct_sepSubTuple {k : ℕ}
    (ν' : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (k : ℤ))))
    (X : R4TupleForms.FinTuple s) (I : Finset (Fin (Continuum.SeparatedFourTuples.tupleLength X)))
    (U : InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (k : ℤ))) :
    StateLimits.centeredProduct k ν' (Continuum.SeparatedFourTuples.sepSubTuple X I) U =
      ∏ i ∈ I, (InfiniteLattice.smearedEnergy (tupleComponentFun X i) U -
        ∫ V, InfiniteLattice.smearedEnergy (tupleComponentFun X i) V ∂ν') := by
  have h := Equiv.prod_comp (I.orderIsoOfFin rfl).toEquiv
    (fun i : I => InfiniteLattice.smearedEnergy (tupleComponentFun X i.1) U -
      ∫ V, InfiniteLattice.smearedEnergy (tupleComponentFun X i.1) V ∂ν')
  rw [Finset.prod_coe_sort I (fun i => InfiniteLattice.smearedEnergy (tupleComponentFun X i) U -
      ∫ V, InfiniteLattice.smearedEnergy (tupleComponentFun X i) V ∂ν')] at h
  rw [← h]
  rfl
theorem integral_centeredProduct_eq_sum_recentred
    (hCI : InfiniteLattice.CenteredIdentity.Statement) {k : ℕ}
    (hk : 0 < k) (μ ν' : Measure (InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (k : ℤ))))
    [hμ : IsProbabilityMeasure μ] [hν : IsProbabilityMeasure ν'] (X : R4TupleForms.FinTuple s) :
    ∫ U, StateLimits.centeredProduct k μ X U ∂μ =
      ∑ I : Finset (Fin (Continuum.SeparatedFourTuples.tupleLength X)),
        (∫ U, StateLimits.centeredProduct k ν' (Continuum.SeparatedFourTuples.sepSubTuple X I) U ∂μ) *
          ∏ i ∈ Iᶜ, (-∫ U, StateLimits.centeredProduct k ν'
            (Continuum.SeparatedFourTuples.sepSubTuple X {i}) U ∂μ) := by
  set a : Fin (Continuum.SeparatedFourTuples.tupleLength X) →
      InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (k : ℤ)) → ℝ :=
    fun i U => InfiniteLattice.smearedEnergy (tupleComponentFun X i) U -
      ∫ V, InfiniteLattice.smearedEnergy (tupleComponentFun X i) V ∂ν' with ha
  have hb := fun i => isBoundedRealRV_smearedEnergy_tupleComponentFun hCI hk μ X i
  have hint : ∀ i, Integrable (InfiniteLattice.smearedEnergy (tupleComponentFun X i) :
      InfiniteLattice.GaugeField (PeriodicLattice.meshSize s.L (k : ℤ)) → ℝ) μ := fun i => by
    obtain ⟨C, hC⟩ := (hb i).bounded
    exact Integrable.of_bound (hb i).measurable.aestronglyMeasurable C
      (ae_of_all _ fun U => by simpa using hC U)
  have hm : ∀ (I : Finset (Fin (Continuum.SeparatedFourTuples.tupleLength X))),
      Integrable (fun U => ∏ i ∈ I, a i U) μ := by
    intro I
    choose C hC using fun i => (hb i).bounded
    have hmeas : Measurable fun U => ∏ i ∈ I, a i U :=
      Finset.measurable_prod _ fun i _ => (hb i).measurable.sub_const _
    refine Integrable.of_bound hmeas.aestronglyMeasurable
      (∏ i ∈ I, (C i + |∫ V, InfiniteLattice.smearedEnergy (tupleComponentFun X i) V ∂ν'|))
      (ae_of_all _ fun U => ?_)
    rw [Real.norm_eq_abs, Finset.abs_prod]
    refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
    exact (abs_sub _ _).trans (add_le_add (hC i U) le_rfl)
  have hone : ∀ i, ∫ U, StateLimits.centeredProduct k ν'
      (Continuum.SeparatedFourTuples.sepSubTuple X {i}) U ∂μ =
      (∫ V, InfiniteLattice.smearedEnergy (tupleComponentFun X i) V ∂μ) -
        ∫ V, InfiniteLattice.smearedEnergy (tupleComponentFun X i) V ∂ν' := by
    intro i
    simp only [centeredProduct_sepSubTuple, Finset.prod_singleton]
    rw [integral_sub (hint i) (integrable_const _)]
    simp
  have hpt : ∀ U, StateLimits.centeredProduct k μ X U =
      ∑ I : Finset (Fin (Continuum.SeparatedFourTuples.tupleLength X)), (∏ i ∈ I, a i U) *
        ∏ i ∈ Iᶜ, (-∫ V, StateLimits.centeredProduct k ν'
          (Continuum.SeparatedFourTuples.sepSubTuple X {i}) V ∂μ) := by
    intro U
    have h₁ : StateLimits.centeredProduct k μ X U = ∏ i, (a i U +
        (-∫ V, StateLimits.centeredProduct k ν'
          (Continuum.SeparatedFourTuples.sepSubTuple X {i}) V ∂μ)) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hone i]
      simp only [ha]
      change InfiniteLattice.smearedEnergy (tupleComponentFun X i) U -
        ∫ V, InfiniteLattice.smearedEnergy (tupleComponentFun X i) V ∂μ = _
      ring
    rw [h₁, Finset.prod_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.compl_eq_univ_sdiff]
  simp only [hpt]
  rw [integral_finset_sum _ fun I _ => (hm I).mul_const _]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [integral_mul_const]
  congr 1
  simp only [centeredProduct_sepSubTuple]
  rfl
end LimitRecentring
open LimitRecentring in
theorem LimitRecentring.statement_holds
    (hMaps : StateMapsAndLimitsAreSeparatedFunctionals)
    (hCI : InfiniteLattice.CenteredIdentity.Statement) :
    LimitRecentring.Statement := by
  intro s K β ρ ν σ hS hlim
  have hKpos := hlim.cutoff_pos
  have hSeq := hlim.periodicGibbs
  obtain ⟨hall, -⟩ := hMaps
  obtain ⟨-, hlims⟩ := hall s K β ρ ν hKpos hSeq
  obtain ⟨-, -, -, hHigh, -, -⟩ := hlims σ hlim
  have hρp : ∀ k, IsProbabilityMeasure (ρ k) := fun k => (hSeq.left_mem k).1.1
  have hνp : ∀ k, IsProbabilityMeasure (ν k) := fun k => (hSeq.right_mem k).1.1
  have hT : ∀ X : R4TupleForms.FinTuple s, Tendsto (fun k => StateLimits.pairedValue K ρ ρ k X) atTop
      (𝓝 (PeriodicGibbsLimit.centredOfLimit σ hS X)) := by
    intro X
    have hval : ∀ k, ((StateLimits.pairedValue K ρ ρ k X : ℝ) : ℂ) =
        ∑ π ∈ SetPartition.nonSingletonPartitions X.1.1, ∏ J ∈ π.parts,
          InfiniteLattice.ursellFunction (ρ k) J.card (Cumulants.restrictTuple X.1.2 J) := by
      intro k
      have h₁ := (hCI { s with K := ⟨K k, hKpos k⟩ } (ρ k) (hρp k)).2.2 X.1.1 X.1.2
        (fun l => tupleComponentFun_mem_compactTestFunctions X l)
      have h₂ : ((StateLimits.pairedValue K ρ ρ k X : ℝ) : ℂ) =
          InfiniteLattice.centeredMoment (ρ k) X.1.2 := by
        change ((∫ U, StateLimits.centeredProduct (K k) (ρ k) X U ∂ρ k : ℝ) : ℂ) = _
        rw [← integral_complex_ofReal]
        refine integral_congr_ae (ae_of_all _ fun U => ?_)
        simp only [StateLimits.centeredProduct]
        push_cast
        refine Finset.prod_congr rfl fun i _ => ?_
        have h₃ : ((∫ V, InfiniteLattice.smearedEnergy (tupleComponentFun X i) V ∂ρ k : ℝ) : ℂ) =
            Probability.complexExpectation (ρ k) fun V =>
              ((InfiniteLattice.smearedEnergy (tupleComponentFun X i) V : ℝ) : ℂ) :=
          integral_ofReal.symm
        exact congrArg (HSub.hSub _) h₃
      exact h₂.trans h₁
    have hlimC : Tendsto (fun k => ((StateLimits.pairedValue K ρ ρ k X : ℝ) : ℂ)) atTop
        (𝓝 ((PeriodicGibbsLimit.centredOfLimit σ hS X : ℝ) : ℂ)) := by
      simp only [hval]
      rw [PeriodicGibbsLimit.centredOfLimit_apply, SetPartition.singletonFree_eq_nonSingletonPartitions]
      push_cast
      refine tendsto_finsetSum _ fun π hπ => tendsto_finsetProd _ fun J hJ => ?_
      have h2 : 2 ≤ J.card := (Finset.mem_filter.1 hπ).2 J hJ
      exact hHigh J.card h2 (AmbientPoints.restrictSeparated ⟨X.1.2, X.2⟩ J)
    have := (Complex.continuous_re.tendsto _).comp hlimC
    simpa [Function.comp_def] using this
  refine ⟨fun X => ?_, hT⟩
  refine tendsto_nhds_unique (hT X) ?_
  have hid : ∀ k, StateLimits.pairedValue K ρ ρ k X =
      ∑ I : Finset (Fin (Continuum.SeparatedFourTuples.tupleLength X)),
        StateLimits.pairedValue K ρ ν k (Continuum.SeparatedFourTuples.sepSubTuple X I) *
          ∏ i ∈ Iᶜ, (-StateLimits.pairedValue K ρ ν k
            (Continuum.SeparatedFourTuples.sepSubTuple X {i})) := fun k => by
    have := hρp k
    have := hνp k
    exact integral_centeredProduct_eq_sum_recentred hCI (hKpos k) (ρ k) (ν k) X
  simp only [hid]
  refine tendsto_finsetSum _ fun I _ => (hlim.pointwise _).mul ?_
  exact tendsto_finsetProd _ fun i _ => (hlim.pointwise _).neg
end YangMills.Construction.BoundsOnEverySide
end
