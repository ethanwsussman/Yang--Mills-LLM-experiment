import YangMills.Construction.InfiniteLattice.ComponentsAndRepresentativeOfASeparatedTupleAreLocalObservables
import YangMills.Construction.InfiniteLattice.LimitPointsOfTheTorusMeasuresArePeriodicGibbsStates
import YangMills.Construction.InfiniteLattice.RegularConditionalProbabilitiesExistAndAreMeasurable
import YangMills.Construction.TotalDensitiesGiveASystem.AConnectedFunctionReadsTheCentredMeans
import YangMills.Construction.TotalDensitiesGiveASystem.LawsWithConvergingMomentsChargeOpenSets
import YangMills.Construction.TotalDensitiesGiveASystem.TheMomentsOfThePhasesAreThoseOfTheComponents
import YangMills.Construction.TotalDensitiesGiveASystem.ThePhasesApproachEveryComponent
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open SystemsWithFiveBounds LimitTheorem SeparatedTuples
open InfiniteLattice (IsRegularConditionalByIntegrals smearedEnergyCumulant)
open TestSpaces (SepTupleOfCard)
namespace PhasesApproachComponents
private def repeatWord {k : ℕ} {T : Type} (W : Fin k → T) (a : Fin k → ℕ) : List T :=
  (List.finRange k).flatMap fun i => List.replicate (a i) (W i)
private theorem prod_map_repeatWord {k : ℕ} {T : Type} (W : Fin k → T) (a : Fin k → ℕ) (g : T → ℝ) :
    ((repeatWord W a).map g).prod = ∏ i, g (W i) ^ a i := by
  have h : ∀ l : List (Fin k), ((l.flatMap fun i => List.replicate (a i) (W i)).map g).prod =
      (l.map fun i => g (W i) ^ a i).prod := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons, ih, List.map_replicate, List.prod_replicate]
  rw [repeatWord, h, Fin.prod_univ_def]
variable {L : ℕ} {IsPair : ℕ+ → ℝ → Prop}
private theorem centredMean_measurable_and_bounded
    (hloc : CenteredRepresentatives.EntriesAreLocal.Statement) (hL : 0 < L)
    (Q : PairSequence L IsPair) (j : ℕ+) (hν : IsProbabilityMeasure (Q.state j))
    {κ : FieldAt Q j → InfiniteLattice.GaugeFieldProbability (PeriodicLattice.meshSize L (((Q.cutoff j : ℕ)) : ℤ))}
    (hκ : IsRegularConditionalByIntegrals (Q.state j) κ) (X : SepTuple) :
    Measurable (fun U => centredMean Q j (κ U).1 X) ∧ ∃ c : ℝ, ∀ U, |centredMean Q j (κ U).1 X| ≤ c := by
  have hobs := (hloc L (Q.cutoff j) hL (Q.state j) hν X).2.1
  have hval : ∀ U, (κ U).expect (CenteredRepresentatives.centeredRepObs L (Q.cutoff j) (Q.state j) X) =
      ((centredMean Q j (κ U).1 X : ℝ) : ℂ) := fun U => by
    unfold InfiniteLattice.GaugeFieldProbability.expect centredMean
      CenteredRepresentatives.centeredRepObs
    exact integral_ofReal
  constructor
  · have hm := ((hκ _ hobs).1).mono (fun _ hI => hI.1) le_rfl
    have h2 : (fun U => centredMean Q j (κ U).1 X) = fun U =>
        ((κ U).expect (CenteredRepresentatives.centeredRepObs L (Q.cutoff j) (Q.state j) X)).re := by
      funext U
      rw [hval]
      simp
    rw [h2]
    exact Complex.measurable_re.comp hm
  · obtain ⟨C, hC⟩ := hobs.2
    refine ⟨C, fun U => ?_⟩
    have hp : IsProbabilityMeasure (κ U).1 := (κ U).2
    have h1 : ‖(κ U).expect (CenteredRepresentatives.centeredRepObs L (Q.cutoff j) (Q.state j) X)‖ ≤ C := by
      unfold InfiniteLattice.GaugeFieldProbability.expect
      have := norm_integral_le_of_norm_le_const (μ := (κ U).1) (Eventually.of_forall hC)
      simpa using this
    rw [hval] at h1
    simpa using h1
private theorem centredMean_nil (Q : PairSequence L IsPair) (j : ℕ+) (ρ : Measure (FieldAt Q j))
    (hρ : IsProbabilityMeasure ρ) : centredMean Q j ρ SepTuple.nil = 1 := by
  unfold centredMean
  have h : (fun U => CenteredRepresentatives.centeredRep L (Q.cutoff j) (Q.state j) SepTuple.nil U) = fun _ => (1 : ℝ) :=
    funext fun U => CenteredRepresentatives.centeredRep_nil _ _ _ U
  rw [h]
  simp
private theorem exists_mem_of_ae_of_measure_pos {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : Ω → Prop}
    {B : Set Ω} (hp : ∀ᵐ x ∂μ, p x) (hB : 0 < μ B) : ∃ x, p x ∧ x ∈ B := by
  by_contra h
  push Not at h
  have : ∀ᵐ x ∂μ, x ∉ B := by
    filter_upwards [hp] with x hx using h x hx
  rw [ae_iff] at this
  simp only [not_not] at this
  have e : {a | a ∈ B} = B := rfl
  rw [e] at this
  exact hB.ne' this
theorem proof (hmom : phaseMomentsConvergeStatement)
    (hcharge : MomentConvergenceChargesOpenSets)
    (hconn : connectedOfCentredMeansStatement)
    (hreg : PeriodicGibbsStateSpace.ConditionalMeasurability.ExistenceAndMeasurability)
    (hdense : PeriodicGibbsStateSpace.DenseLocalFamily.denseFamilyStatement)
    (hlimit : InfiniteLattice.TorusWeakLimitsArePeriodicGibbs)
    (hloc : CenteredRepresentatives.EntriesAreLocal.Statement) :
    phasesApproachComponentsStatement := by
  intro L hL IsPair Q S hβ hS A hA ξ d hd X E hE
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL.2
  have := hA.compact
  have := hA.isProb
  obtain ⟨k, W, P, hPc, hPσ, hPρ⟩ := hconn d hd X
  have hprob : ∀ j, IsProbabilityMeasure (Q.state j) := fun j => (Q.isLimit j).1
  have hex : ∀ j, ∃ κ, IsRegularConditionalByIntegrals (Q.state j) κ := fun j => by
    have hper : Q.state j ∈ InfiniteLattice.periodicGibbsSet L (Q.cutoff j) (Q.coupling j) :=
      (hlimit L (Q.cutoff j) hL (Q.cutoff j).pos (Q.coupling j) (hβ j)).2 (Q.isLimit j)
    let D : LatticePhases.Setup := ⟨L, hL, Q.cutoff j, Q.coupling j, hβ j⟩
    obtain ⟨𝒟, h𝒟⟩ := (hdense D).1
    exact (hreg D (Q.state j) hper 𝒟 h𝒟).1
  choose κ hκ using hex
  let Φ : ∀ j, FieldAt Q j → Fin k → ℝ := fun j U i => centredMean Q j (κ j U).1 (W i)
  let Ψ : A.space → Fin k → ℝ := fun η i => A.comp η (W i)
  have hΦm : ∀ j, Measurable (Φ j) := fun j =>
    measurable_pi_lambda _ fun i => (centredMean_measurable_and_bounded hloc hL0 Q j (hprob j) (hκ j) (W i)).1
  have hΦb : ∀ j i, ∃ c : ℝ, ∀ U, |Φ j U i| ≤ c := fun j i =>
    (centredMean_measurable_and_bounded hloc hL0 Q j (hprob j) (hκ j) (W i)).2
  have hΨc : Continuous Ψ := continuous_pi fun i => hA.continuous_comp (W i)
  have hΨm : Measurable Ψ := hΨc.measurable
  let m : ℕ+ → Measure (Fin k → ℝ) := fun j => (Q.state j).map (Φ j)
  let m' : Measure (Fin k → ℝ) := A.law.map Ψ
  have hmp : ∀ j, IsProbabilityMeasure (m j) := fun j =>
    have := hprob j
    Measure.isProbabilityMeasure_map (hΦm j).aemeasurable
  have hm'p : IsProbabilityMeasure m' := Measure.isProbabilityMeasure_map hΨm.aemeasurable
  have hcompact : ∃ C : Set (Fin k → ℝ), IsCompact C ∧ m' Cᶜ = 0 := by
    refine ⟨Set.range Ψ, isCompact_range hΨc, ?_⟩
    have hcl : MeasurableSet (Set.range Ψ)ᶜ := (isCompact_range hΨc).isClosed.measurableSet.compl
    change (A.law.map Ψ) _ = 0
    rw [Measure.map_apply hΨm hcl]
    have : Ψ ⁻¹' (Set.range Ψ)ᶜ = ∅ := by
      ext η
      simp
    rw [this, measure_empty]
  have hmono : ∀ a : Fin k → ℕ, Measurable fun x : Fin k → ℝ => ∏ i, x i ^ a i := fun a =>
    Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const (a i)
  have hmoments : ∀ a : Fin k → ℕ, (∀ j, Integrable (fun x => ∏ i, x i ^ a i) (m j)) ∧
      Tendsto (fun j => ∫ x, ∏ i, x i ^ a i ∂m j) atTop (𝓝 (∫ x, ∏ i, x i ^ a i ∂m')) := by
    intro a
    refine ⟨fun j => ?_, ?_⟩
    · have := hprob j
      refine (integrable_map_measure (hmono a).aestronglyMeasurable (hΦm j).aemeasurable).2 ?_
      choose c hc using hΦb j
      refine Integrable.of_bound (((hmono a).comp (hΦm j)).aestronglyMeasurable)
        (∏ i, |c i| ^ a i) (Eventually.of_forall fun U => ?_)
      simp only [Function.comp_apply, Real.norm_eq_abs, Finset.abs_prod, abs_pow]
      exact Finset.prod_le_prod (fun i _ => by positivity) fun i _ =>
        pow_le_pow_left₀ (abs_nonneg _) ((hc i U).trans (le_abs_self _)) _
    · have h := hmom L hL IsPair Q S hβ hS κ hκ A hA SepTuple.nil (repeatWord W a)
      have e1 : (fun j => ∫ x, ∏ i, x i ^ a i ∂m j) = phaseMoment Q κ SepTuple.nil (repeatWord W a) := by
        funext j
        have := hprob j
        rw [integral_map (hΦm j).aemeasurable (hmono a).aestronglyMeasurable]
        unfold phaseMoment
        refine integral_congr_ae (Eventually.of_forall fun U => ?_)
        have hp : IsProbabilityMeasure (κ j U).1 := (κ j U).2
        beta_reduce
        rw [centredMean_nil Q j (κ j U).1 hp, one_mul]
        exact (prod_map_repeatWord W a (fun Z => centredMean Q j (κ j U).1 Z)).symm
      have e2 : ∫ x, ∏ i, x i ^ a i ∂m' =
          ∫ η, A.comp η SepTuple.nil * ((repeatWord W a).map fun Z => A.comp η Z).prod ∂A.law := by
        rw [integral_map hΨm.aemeasurable (hmono a).aestronglyMeasurable]
        refine integral_congr_ae (Eventually.of_forall fun η => ?_)
        beta_reduce
        rw [(A.comp η).map_nil, one_mul]
        exact (prod_map_repeatWord W a (fun Z => A.comp η Z)).symm
      rw [e1, e2]
      exact h
  have hball : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, 0 < m j (Metric.ball (Ψ ξ) r) := by
    intro r hr
    refine hcharge k m m' hmp hm'p hcompact hmoments _ Metric.isOpen_ball ?_
    change 0 < (A.law.map Ψ) _
    rw [Measure.map_apply hΨm Metric.isOpen_ball.measurableSet]
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have hξ : ξ ∈ measureSupport A.law := by
      rw [hA.measureSupport_eq]
      exact Set.mem_univ _
    exact hξ ⟨_, ⟨Metric.isOpen_ball.preimage hΨc, h0⟩, by simpa using hr⟩
  have hgood : ∀ j, ∀ᵐ U ∂Q.state j, (κ j U).1 ∈ E j := fun j => hE j (κ j) (hκ j)
  have hpick : ∀ j : ℕ+, ∃ U, (κ j U).1 ∈ E j ∧
      ∀ U', (κ j U').1 ∈ E j → dist (Φ j U) (Ψ ξ) < dist (Φ j U') (Ψ ξ) + 1 / (j : ℝ) := by
    intro j
    have := hprob j
    have hne : ((fun U => dist (Φ j U) (Ψ ξ)) '' {U | (κ j U).1 ∈ E j}).Nonempty := by
      obtain ⟨U, hU⟩ := (hgood j).exists
      exact ⟨_, U, hU, rfl⟩
    have hpos : (0 : ℝ) < 1 / (j : ℝ) := by
      have : (0 : ℝ) < (j : ℝ) := by exact_mod_cast j.pos
      positivity
    obtain ⟨_, ⟨U, hU, rfl⟩, hlt⟩ := Real.lt_sInf_add_pos hne hpos
    refine ⟨U, hU, fun U' hU' => hlt.trans_le ?_⟩
    have hb : BddBelow ((fun U => dist (Φ j U) (Ψ ξ)) '' {U | (κ j U).1 ∈ E j}) :=
      ⟨0, by rintro _ ⟨V, -, rfl⟩; exact dist_nonneg⟩
    have := csInf_le hb ⟨U', hU', rfl⟩
    linarith
  choose U hU hmin using hpick
  have hlim : Tendsto (fun j => Φ j (U j)) atTop (𝓝 (Ψ ξ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hinv : Tendsto (fun j : ℕ+ => 1 / ((j : ℕ) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp tendsto_PNat_val_atTop_atTop
    filter_upwards [hball (ε / 2) (by positivity), hinv.eventually (gt_mem_nhds (half_pos hε))] with j hj hj'
    change 0 < ((Q.state j).map (Φ j)) _ at hj
    rw [Measure.map_apply (hΦm j) Metric.isOpen_ball.measurableSet] at hj
    obtain ⟨U', hU', hin⟩ := exists_mem_of_ae_of_measure_pos (hgood j) hj
    have h1 := hmin j U' hU'
    have h2 : dist (Φ j U') (Ψ ξ) < ε / 2 := hin
    have h3 : 1 / ((j : ℕ) : ℝ) < ε / 2 := hj'
    exact show dist (Φ j (U j)) (Ψ ξ) < ε from by
      have : dist (Φ j (U j)) (Ψ ξ) < dist (Φ j U') (Ψ ξ) + 1 / ((j : ℕ) : ℝ) := h1
      linarith
  refine ⟨fun j => (κ j (U j)).1, hU, fun j => (κ j (U j)).2, ?_⟩
  have hval : ∀ j, smearedEnergyCumulant (κ j (U j)).1 X.1 = ((P (Φ j (U j)) : ℝ) : ℂ) := fun j =>
    (hPρ L (Q.cutoff j) hL (Q.state j) (κ j (U j)).1 (κ j (U j)).2)
  simp only [hval]
  rw [hPσ (A.comp ξ)]
  exact (Complex.continuous_ofReal.tendsto _).comp ((hPc.tendsto _).comp hlim)
end PhasesApproachComponents
end YangMills.Construction.TotalDensitiesGiveASystem
end
