import YangMills.Construction.FreeEnergiesOfTheFlow.StateOfAStepIsBorelProof
import YangMills.Construction.HullsInEveryVolume.ARuleDrawsTheChain
import YangMills.Construction.LawByMomentsOfTheFlow.ABoundAtClearStatesInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.HullsInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldsExtend
import YangMills.Construction.LawByMomentsOfTheFlow.MeansOfALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.PointsOnLargerTori
import YangMills.Construction.LawByMomentsOfTheFlow.StatesOfAPointAreLive
import YangMills.Construction.ResponseInTheExpansion.BoundedFunctionsOfTheCasesAreIntegrable
import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelow
import YangMills.Construction.ResponseInTheExpansion.LevelsFormStates
import YangMills.Construction.ResponseInTheExpansion.MeansGivenAStateAreMeansOverItsCases
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import YangMills.Construction.ResponseInTheExpansion.TheDrawBelowHasItsLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open MomentMethod WeightedResponses ResponseInTheExpansion StepSettings TorusFields TorusLumps RenormalizationStepParameters FreeEnergies ChainNoise HullTrees ClusterExpansionOfAStep LevelTestFunctions StepCosts
section Limit
variable {T : TranslatedLaws} {J : Type} {X : J → T.Family} {P : Measure (TranslateValues J)}
private theorem ae_le_of_eventually_le (hL : IsJointLimitLaw T X P) {I : Type} [Fintype I] (ι : I → J) (φ : (I → ℝ) → ℝ) (hφ : Continuous φ)
    (h : ∀ᶠ i in atTop, ∀ᵐ ω ∂(T.μ i), φ (fun c => X (ι c) i ω) ≤ 0) :
    ∀ᵐ v ∂P, φ (fun c => v (ι c, 0)) ≤ 0 := by
  classical
  have hP := hL.isProbability
  obtain ⟨e, he⟩ : ∃ e : I ≃ Fin (Fintype.card I), e = Fintype.equivFin I := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G : (Fin (Fintype.card I) → ℝ) → ℝ, G = fun w => min 1 (max (φ fun c => w (e c)) 0) := ⟨_, rfl⟩
  have hG : Continuous G := by
    rw [hGd]
    have : Continuous fun w : Fin (Fintype.card I) → ℝ => φ fun c => w (e c) :=
      hφ.comp (continuous_pi fun c => continuous_apply _)
    exact continuous_const.min (this.max continuous_const)
  have hG0 : ∀ w, 0 ≤ G w := fun w => by
    rw [hGd]
    exact le_min zero_le_one (le_max_right _ _)
  have hG1 : ∀ w, G w ≤ 1 := fun w => by
    rw [hGd]
    exact min_le_left _ _
  have hb : ∃ C : ℝ, ∀ w, |G w| ≤ C := ⟨1, fun w => by rw [abs_of_nonneg (hG0 w)]; exact hG1 w⟩
  have hlim := hL.tendsto _ (fun c => (ι (e.symm c), 0)) G hG hb
  have hval : ∀ y : I → ℝ, G (fun c => y (e.symm c)) = min 1 (max (φ y) 0) := fun y => by
    rw [hGd]
    simp
  have h0 : ∀ᶠ i in atTop, ∫ ω, G (fun c => TranslatedLaws.translate (X (ι (e.symm c))) 0 i ω) ∂(T.μ i) = 0 := by
    filter_upwards [h] with i hi
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hi] with ω hω
    have e1 := hval fun c => X (ι c) i ω
    have e2 : (fun c => TranslatedLaws.translate (X (ι (e.symm c))) 0 i ω) = fun c => X (ι (e.symm c)) i ω := rfl
    rw [e2, e1]
    simp [max_eq_right hω]
  have hz : ∫ v, G (fun c => v (ι (e.symm c), 0)) ∂P = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (h0.mono fun i hi => hi.symm))
  have hm : Measurable fun v : TranslateValues J => G (fun c => v (ι (e.symm c), 0)) :=
    hG.measurable.comp (measurable_pi_lambda _ fun c => measurable_pi_apply _)
  have hint : Integrable (fun v : TranslateValues J => G (fun c => v (ι (e.symm c), 0))) P :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 _)]
      exact hG1 _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun v => hG0 _) hint).1 hz
  filter_upwards [hae] with v hv
  have e1 := hval fun c => v (ι c, 0)
  have hv' : G (fun c => v (ι (e.symm c), 0)) = 0 := hv
  rw [hv'] at e1
  by_contra hcon
  have hpos : 0 < φ fun c => v (ι c, 0) := not_le.mp hcon
  have : 0 < min 1 (max (φ fun c => v (ι c, 0)) 0) := lt_min one_pos (lt_max_of_lt_left hpos)
  linarith
abbrev _root_.YangMills.SharedProofs.p13419 := @ae_le_of_eventually_le
private theorem shiftInvariantSigma_le : shiftInvariantSigma J ≤ (inferInstance : MeasurableSpace (TranslateValues J)) := inf_le_right
private theorem invariantCondExp_add_sum_le [IsProbabilityMeasure P] {ι : Type} (s : Finset ι) (f₀ : TranslateValues J → ℝ) (f : ι → TranslateValues J → ℝ)
    (hf₀ : Integrable f₀ P) (hf : ∀ z ∈ s, Integrable (f z) P) (b₀ e bz : ℝ) (he : 0 ≤ e)
    (h₀ : ∀ᵐ v ∂P, invariantCondExp P f₀ v ≤ b₀) (hb : ∀ z ∈ s, ∀ᵐ v ∂P, invariantCondExp P (f z) v ≤ bz) :
    ∀ᵐ v ∂P, invariantCondExp P (fun v => f₀ v + e * ∑ z ∈ s, f z v) v ≤ b₀ + e * ((s.card : ℝ) * bz) := by
  have hsum : Integrable (fun v => ∑ z ∈ s, f z v) P := integrable_finsetSum _ hf
  have h1 : invariantCondExp P (fun v => ∑ z ∈ s, f z v) =ᵐ[P] ∑ z ∈ s, invariantCondExp P (f z) := by
    have := condExp_finsetSum (μ := P) (s := s) (f := f) hf (shiftInvariantSigma J)
    refine (condExp_congr_ae (ae_of_all _ fun v => ?_)).trans this
    simp
  have h2 : invariantCondExp P (fun v => f₀ v + e * ∑ z ∈ s, f z v) =ᵐ[P] (fun v => invariantCondExp P f₀ v + e * invariantCondExp P (fun v => ∑ z ∈ s, f z v) v) := by
    have e1 := condExp_add (μ := P) hf₀ (hsum.const_mul e) (shiftInvariantSigma J)
    have e2 := condExp_smul (μ := P) e (fun v => ∑ z ∈ s, f z v) (shiftInvariantSigma J)
    unfold invariantCondExp
    filter_upwards [e1, e2] with v h₁ h₂
    have h₁' : P[fun v => f₀ v + e * ∑ z ∈ s, f z v | shiftInvariantSigma J] v =
        (P[f₀ | shiftInvariantSigma J] + P[fun v => e * ∑ z ∈ s, f z v | shiftInvariantSigma J]) v := h₁
    have h₂' : P[fun v => e * ∑ z ∈ s, f z v | shiftInvariantSigma J] v = e * P[fun v => ∑ z ∈ s, f z v | shiftInvariantSigma J] v := by
      have e4 : (fun v => e * ∑ z ∈ s, f z v) = e • (fun v => ∑ z ∈ s, f z v) := rfl
      rw [e4]
      simpa [smul_eq_mul, Pi.smul_apply] using h₂
    rw [h₁', Pi.add_apply, h₂']
  have h3 : ∀ᵐ v ∂P, ∀ z ∈ s, invariantCondExp P (f z) v ≤ bz := (ae_ball_iff s.countable_toSet).2 hb
  filter_upwards [h1, h2, h3, h₀] with v a₁ a₂ a₃ a₄
  rw [a₂, a₁, Finset.sum_apply]
  have : ∑ z ∈ s, invariantCondExp P (f z) v ≤ (s.card : ℝ) * bz := by
    simpa using Finset.sum_le_card_nsmul s _ bz a₃
  have := mul_le_mul_of_nonneg_left this he
  linarith
private theorem hasBoundedMoments_of_abs_le {T : TranslatedLaws} {X : T.Family} (hp : ∀ i, IsProbabilityMeasure (T.μ i)) (hb : ∀ i, AEMeasurable (X i) (T.μ i))
    {C : ℝ} (hC : ∀ i, ∀ᵐ ω ∂(T.μ i), |X i ω| ≤ C) : TranslatedLaws.HasBoundedMoments X := by
  refine ⟨hb, fun q => ⟨|C| ^ q, fun i => ?_⟩⟩
  haveI := hp i
  calc ∫⁻ ω, ENNReal.ofReal (|X i ω| ^ q) ∂(T.μ i) ≤ ∫⁻ _, ENNReal.ofReal (|C| ^ q) ∂(T.μ i) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hC i] with ω hω
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) (hω.trans (le_abs_self _)) _)
    _ = ENNReal.ofReal (|C| ^ q) := by simp
abbrev _root_.YangMills.SharedProofs.p39822 := @hasBoundedMoments_of_abs_le
end Limit
section Parameters
private theorem forAllHull_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁) (h₂ : ForAllHullParameters Q₂) :
    ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, h₁⟩ := h₁ a ha
  obtain ⟨L₂, r₂, C₂, hr₂, h₂⟩ := h₂ a ha
  refine ⟨max L₁ L₂, fun c => min (r₁ c) (r₂ c), max C₁ C₂, fun c => lt_min (hr₁ c) (hr₂ c), ?_⟩
  intro L hodd hL Tb e1 e2 hD hCS hCH hrt hC
  obtain ⟨M₁, h₁⟩ := h₁ L hodd ((le_max_left _ _).trans hL) Tb e1 e2 hD hCS hCH (hrt.trans (min_le_left _ _))
    ((le_max_left _ _).trans hC)
  obtain ⟨M₂, h₂⟩ := h₂ L hodd ((le_max_right _ _).trans hL) Tb e1 e2 hD hCS hCH (hrt.trans (min_le_right _ _))
    ((le_max_right _ _).trans hC)
  refine ⟨max M₁ M₂, fun Kr hM e3 e4 hK hres => ?_⟩
  obtain ⟨y₁, h₁⟩ := h₁ Kr ((le_max_left _ _).trans hM) e3 e4 hK hres
  obtain ⟨y₂, h₂⟩ := h₂ Kr ((le_max_right _ _).trans hM) e3 e4 hK hres
  refine ⟨max y₁ y₂, fun y hy hR hW g hg hgy k _ h2 h8 R d hd => ?_⟩
  exact ⟨h₁ y ((le_max_left _ _).trans hy) hR hW g hg hgy k h2 h8 R d hd,
    h₂ y ((le_max_right _ _).trans hy) hR hW g hg hgy k h2 h8 R d hd⟩
abbrev _root_.YangMills.SharedProofs.p1668 := @forAllHull_and
private theorem forAllHull_imp {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllHullParameters Q₁) (f : ∀ Λ, Λ.k ≤ 8 → Q₁ Λ → Q₂ Λ) :
    ForAllHullParameters Q₂ := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, h⟩ := h a ha
  refine ⟨L₁, r₁, C₁, hr₁, ?_⟩
  intro L hodd hL Tb e1 e2 hD hCS hCH hrt hC
  obtain ⟨M, h⟩ := h L hodd hL Tb e1 e2 hD hCS hCH hrt hC
  refine ⟨M, fun Kr hM e3 e4 hK hres => ?_⟩
  obtain ⟨y₁, h⟩ := h Kr hM e3 e4 hK hres
  refine ⟨y₁, fun y hy hR hW g hg hgy k _ h2 h8 R d hd => ?_⟩
  exact f _ h8 (h y hy hR hW g hg hgy k h2 h8 R d hd)
abbrev _root_.YangMills.SharedProofs.p30752 := @forAllHull_imp
private theorem forAllHull_of_forAll {Q : MomentParameters → Prop} (h : ForAllParameters Q) : ForAllHullParameters Q := by
  intro a ha
  obtain ⟨L₀, r₀, C₀, hr, h⟩ := h a ha
  refine ⟨L₀, r₀, C₀, hr, ?_⟩
  intro L hodd hL Tb e1 e2 hD hCS hCH hrt hC
  refine ⟨0, fun Kr _ _ _ hK _ => ?_⟩
  obtain ⟨y₀, h⟩ := h L hodd hL Tb e1 e2 hD hCS hCH hrt hC Kr hK
  exact ⟨y₀, fun y hy hR hW g hg hgy k _ h2 h8 R d hd => h y hy hR hW g hg hgy k h2 h8 R d hd⟩
abbrev _root_.YangMills.SharedProofs.p12974 := @forAllHull_of_forAll
private theorem forAllHull_of_admissibleParameters {P : ParameterAssignment → ℝ → Prop} (h : WeightedResponses.HoldsAtAdmissibleParameters P) :
    ForAllHullParameters fun Λ => P Λ.table Λ.floor := by
  intro a ha
  obtain ⟨L₀, r₀, hr, h⟩ := h a ha
  refine ⟨L₀, r₀, 0, hr, ?_⟩
  intro L hodd hL Tb e1 e2 hD _ _ hrt _
  obtain ⟨y₀, h⟩ := h L hodd hL Tb e1 e2 hD hrt
  exact ⟨0, fun Kr _ _ _ _ _ => ⟨y₀, fun y hy hR hW g _ _ k _ _ _ R d _ => h y hy hR hW⟩⟩
abbrev _root_.YangMills.SharedProofs.p3284 := @forAllHull_of_admissibleParameters
private theorem forAllHull_of_admissible {P : ParameterAssignment → ℝ → Prop}
    (h : ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → P T y) :
    ForAllHullParameters fun Λ => P Λ.table Λ.floor := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hD _ _ _ _
  obtain ⟨y₀, h⟩ := h Tb hD
  exact ⟨0, fun Kr _ _ _ _ _ => ⟨y₀, fun y hy _ _ g _ _ k _ _ _ R d _ => h y hy⟩⟩
abbrev _root_.YangMills.SharedProofs.p14065 := @forAllHull_of_admissible
end Parameters
section Samples
variable {ℓ : TorusLumps.StepParameters}
private theorem eqRec_eqRec {a b c n : ℕ} (h₁ : a = b) (h₂ : b = c) (h₃ : a = c) (w : MarkedSample ℓ a n) :
    (h₂ ▸ (h₁ ▸ w : MarkedSample ℓ b n) : MarkedSample ℓ c n) = h₃ ▸ w := by
  subst h₁
  subst h₂
  rfl
private theorem measurable_upper (T : WeightedResponses.StageTower ℓ) (v : ℕ) : ∀ (d n : ℕ) [NeZero n] {Z : Type} [MeasurableSpace Z]
    (φ : StageState T v (fineSide ℓ.side d n) → Z), Measurable φ →
    Measurable[upperSigma T v d n] (fun u : MarkedSample ℓ (v + d) n => φ (stageState T v _ (sampleBelow ℓ v d n u))) := by
  intro d
  induction d with
  | zero =>
    intro n _ Z _ φ hφ
    exact hφ.comp (comap_measurable _)
  | succ d ih =>
    intro n _ Z _ φ hφ
    have h1 := ih (n * ℓ.side) φ hφ
    let mX : MeasurableSpace (MarkedSample ℓ (v + d + 1) n) := upperSigma T v (d + 1) n
    have hfst : @Measurable _ _ mX (upperSigma T v d (n * ℓ.side)) (fun u : MarkedSample ℓ (v + d + 1) n => u.1) :=
      (comap_measurable _).mono le_sup_left le_rfl
    exact h1.comp hfst
private theorem measurable_state_upper (T : WeightedResponses.StageTower ℓ) (v d d' n : ℕ) [NeZero n] (hD : v + d = v + d') {Z : Type} [MeasurableSpace Z]
    (φ : StageState T v (fineSide ℓ.side d' n) → Z) (hφ : Measurable φ) :
    Measurable[upperSigma T v d n] (fun w : MarkedSample ℓ (v + d) n => φ (stageState T v _ (sampleBelow ℓ v d' n (hD ▸ w)))) := by
  obtain rfl : d = d' := by omega
  exact measurable_upper T v d n φ hφ
end Samples
section Point
variable {Λ : MomentParameters}
private theorem measurableSet_sigma_fst {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
private theorem eqRec_law (T : WeightedResponses.StageTower Λ.stepParams) (β : ℝ) {K K' : ℕ} (h : K = K') (n : ℕ) [NeZero n] :
    Measurable (fun w : MarkedSample Λ.stepParams K n => (h ▸ w : MarkedSample Λ.stepParams K' n)) ∧
      (markedSampleLaw T β K n).map (fun w : MarkedSample Λ.stepParams K n => (h ▸ w : MarkedSample Λ.stepParams K' n)) = markedSampleLaw T β K' n := by
  subst h
  exact ⟨measurable_id, Measure.map_id⟩
abbrev _root_.YangMills.SharedProofs.p48114 := @eqRec_law
private structure SampleFacts (S : MomentPoint Λ) : Prop where
  measurable_state : ∀ (u n : ℕ) [NeZero n], Measurable (stageState S.tower u n)
  sampleBelow_law : ∀ (s d n : ℕ) [NeZero n], Measurable (sampleBelow Λ.stepParams s d n) ∧
    Measure.map (sampleBelow Λ.stepParams s d n) (markedSampleLaw S.tower S.β (s + d) n) = markedSampleLaw S.tower S.β s (fineSide Λ.stepParams.side d n)
  isProbability : ∀ (u n : ℕ) [NeZero n], IsProbabilityMeasure (markedSampleLaw S.tower S.β u n)
  condExp_eq : ∀ u, u + 1 ≤ S.data.windowLevel → ∀ Φ : TorusField (S.sideAtLevel (u + 1)) → CaseFunction (S.tower.stage u).toStepSetup (S.sideAtLevel (u + 1)),
    Measurable (caseLift S.tower u _ Φ) → (∃ C : ℝ, ∀ x, |caseLift S.tower u _ Φ x| ≤ C) →
    ((markedSampleLaw S.tower S.β (u + 1) (S.sideAtLevel (u + 1)))[caseLift S.tower u _ Φ | stageSigma S.tower (u + 1) (S.sideAtLevel (u + 1))]) =ᵐ[markedSampleLaw S.tower S.β (u + 1) (S.sideAtLevel (u + 1))]
      caseMeanAtSample S.tower u _ Φ
  integrable : ∀ u, u + 1 ≤ S.data.windowLevel → ∀ (Φ : TorusField (S.sideAtLevel (u + 1)) → CaseFunction (S.tower.stage u).toStepSetup (S.sideAtLevel (u + 1))) (Sz : ℝ),
    (∀ V (Yt : Finset (TorusSite (S.sideAtLevel (u + 1) * Λ.stepParams.side))) (bad : Finset (TorusBond (S.sideAtLevel (u + 1) * Λ.stepParams.side))) (b : BaseChoice Λ.stepParams.side (S.sideAtLevel (u + 1))),
      Measurable fun p : TorusField (S.sideAtLevel (u + 1) * Λ.stepParams.side) × (Yt → (S.tower.stage u).toStepSetup.labels.Ω) => Φ V p.1 Yt p.2 bad b) →
    (∀ V W Yt ωt bad b, |Φ V W Yt ωt bad b| ≤ Sz) →
    ∀ᵐ x ∂(markedSampleLaw S.tower S.β (u + 1) (S.sideAtLevel (u + 1))), CaseIntegrableAtSample S.tower u _ Φ x
namespace MomentPoint
variable (S : MomentPoint Λ)
private theorem sampleAtLevel_map (h : SampleFacts S) (u : ℕ) (hu : u ≤ S.data.windowLevel) :
    Measurable (S.sampleAtLevel u hu) ∧ (S.law S.data.windowLevel (S.data.period Λ.stepParams.side)).map (S.sampleAtLevel u hu) = S.law u (S.sideAtLevel u) := by
  have hc := eqRec_law S.tower S.β (Nat.add_sub_of_le hu).symm (S.data.period Λ.stepParams.side)
  obtain ⟨m1, e1⟩ := h.sampleBelow_law u (S.data.windowLevel - u) (S.data.period Λ.stepParams.side)
  refine ⟨m1.comp hc.1, ?_⟩
  have e2 := Measure.map_map (μ := markedSampleLaw S.tower S.β S.data.windowLevel (S.data.period Λ.stepParams.side)) m1 hc.1
  rw [hc.2, e1] at e2
  exact e2.symm
private theorem ae_of_ae_level (h : SampleFacts S) (u : ℕ) (hu : u ≤ S.data.windowLevel) {p : MarkedSample Λ.stepParams u (S.sideAtLevel u) → Prop}
    (hp : ∀ᵐ x ∂(S.law u (S.sideAtLevel u)), p x) : ∀ᵐ w ∂(S.law S.data.windowLevel (S.data.period Λ.stepParams.side)), p (S.sampleAtLevel u hu w) := by
  obtain ⟨m1, e1⟩ := S.sampleAtLevel_map h u hu
  rw [← e1] at hp
  exact ae_of_ae_map m1.aemeasurable hp
private theorem aemeasurable_of_level (h : SampleFacts S) (u : ℕ) (hu : u ≤ S.data.windowLevel) {f : MarkedSample Λ.stepParams u (S.sideAtLevel u) → ℝ}
    (hf : AEMeasurable f (S.law u (S.sideAtLevel u))) : AEMeasurable (fun w => f (S.sampleAtLevel u hu w)) (S.law S.data.windowLevel (S.data.period Λ.stepParams.side)) := by
  obtain ⟨m1, e1⟩ := S.sampleAtLevel_map h u hu
  rw [← e1] at hf
  exact hf.comp_measurable m1
private theorem measurable_stateAtLevel (h : SampleFacts S) (u : ℕ) (hu : u ≤ S.data.windowLevel) : Measurable (S.stateAtLevel u hu) :=
  (h.measurable_state u (S.sideAtLevel u)).comp (S.sampleAtLevel_map h u hu).1
private theorem measurableSet_mem_support (h : SampleFacts S) (u : ℕ) (hu : u ≤ S.data.windowLevel) (y : TorusSite (S.sideAtLevel u)) :
    MeasurableSet {w | y ∈ (S.stateAtLevel u hu w).2.1} := by
  have e : {w | y ∈ (S.stateAtLevel u hu w).2.1} =
      ⋃ a ∈ {a : Finset (TorusSite (S.sideAtLevel u)) | y ∈ a}, {w | (S.stateAtLevel u hu w).2.1 = a} := by
    ext w
    simp
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ =>
    (measurable_snd.comp (S.measurable_stateAtLevel h u hu)) (measurableSet_sigma_fst a)
private theorem measurableSet_disjoint {n : ℕ} [NeZero n] (u : ℕ) (B : Finset (TorusSite n)) :
    MeasurableSet {st : StageState S.tower u n | Disjoint st.2.1 B} := by
  have e : {st : StageState S.tower u n | Disjoint st.2.1 B} =
      ⋃ a ∈ {a : Finset (TorusSite n) | Disjoint a B}, {st : StageState S.tower u n | st.2.1 = a} := by
    ext st
    simp
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ => measurable_snd (measurableSet_sigma_fst a)
open Classical in
private theorem largeHullIndicator_eq {u : ℕ} (hu : u ≤ S.data.windowLevel) (z : Fin 4 → ℤ) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) :
    largeHullIndicator u z 0 S w = if S.siteAt u z ∈ (S.stateAtLevel u hu w).2.1 then 1 else 0 := by
  unfold largeHullIndicator
  rw [dif_pos hu]
  simp only [Nat.cast_nonneg, and_true]
abbrev _root_.YangMills.SharedProofs.p14364 := @largeHullIndicator_eq
private theorem largeHullIndicator_nonneg (u : ℕ) (z : Fin 4 → ℤ) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) : 0 ≤ largeHullIndicator u z 0 S w := by
  classical
  unfold largeHullIndicator
  split_ifs <;> norm_num
abbrev _root_.YangMills.SharedProofs.p20972 := @largeHullIndicator_nonneg
private theorem abs_largeHullIndicator_le (u : ℕ) (z : Fin 4 → ℤ) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) : |largeHullIndicator u z 0 S w| ≤ 1 := by
  classical
  unfold largeHullIndicator
  split_ifs <;> norm_num
abbrev _root_.YangMills.SharedProofs.p33608 := @abs_largeHullIndicator_le
private theorem measurable_largeHullIndicator (h : SampleFacts S) (u : ℕ) (z : Fin 4 → ℤ) : Measurable (largeHullIndicator u z 0 S) := by
  classical
  by_cases hu : u ≤ S.data.windowLevel
  · have e : largeHullIndicator u z 0 S = fun w => if S.siteAt u z ∈ (S.stateAtLevel u hu w).2.1 then 1 else 0 := by
      funext w
      exact S.largeHullIndicator_eq hu z w
    rw [e]
    exact Measurable.ite (S.measurableSet_mem_support h u hu _) measurable_const measurable_const
  · have e : largeHullIndicator u z 0 S = fun _ => 0 := by
      funext w
      unfold largeHullIndicator
      rw [dif_neg hu]
    rw [e]
    exact measurable_const
private theorem abs_clearIndicator_le (u R : ℕ) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)) : |clearIndicator u R S w| ≤ 1 := by
  classical
  unfold clearIndicator
  split_ifs <;> norm_num
private theorem measurable_clearIndicator (h : SampleFacts S) (u R : ℕ) : Measurable (clearIndicator u R S) := by
  classical
  by_cases hu : u ≤ S.data.windowLevel
  · have e : clearIndicator u R S = fun w =>
        (fun st : StageState S.tower u (S.sideAtLevel u) => if Disjoint st.2.1 (supBall (S.originSite u (S.sideAtLevel u)) (R : ℝ)) then (1 : ℝ) else 0)
          (S.stateAtLevel u hu w) := by
      funext w
      exact dif_pos hu
    rw [e]
    exact (Measurable.ite (S.measurableSet_disjoint u _) measurable_const measurable_const).comp (S.measurable_stateAtLevel h u hu)
  · have e : clearIndicator u R S = fun _ => 0 := by
      funext w
      exact dif_neg hu
    rw [e]
    exact measurable_const
private theorem clearIndicator_measurableAbove (u R : ℕ) : IsMeasurableAbove S u (clearIndicator u R S) := by
  classical
  intro d h
  have hu : u ≤ S.data.windowLevel := by omega
  have hD : u + d = u + (S.data.windowLevel - u) := by omega
  have e : (fun w : MarkedSample Λ.stepParams (u + d) (S.data.period Λ.stepParams.side) => clearIndicator u R S (h ▸ w)) = fun w =>
      (fun st : StageState S.tower u (S.sideAtLevel u) => if Disjoint st.2.1 (supBall (S.originSite u (S.sideAtLevel u)) (R : ℝ)) then (1 : ℝ) else 0)
        (stageState S.tower u _ (sampleBelow Λ.stepParams u (S.data.windowLevel - u) (S.data.period Λ.stepParams.side) (hD ▸ w))) := by
    funext w
    have e₀ : S.stateAtLevel u hu (h ▸ w) = stageState S.tower u _ (sampleBelow Λ.stepParams u (S.data.windowLevel - u) (S.data.period Λ.stepParams.side) (hD ▸ w)) := by
      simp only [MomentPoint.stateAtLevel, MomentPoint.sampleAtLevel]
      rw [eqRec_eqRec h (Nat.add_sub_of_le hu).symm hD w]
    simp only [clearIndicator, dif_pos hu]
    simp only [e₀]
  rw [e]
  exact measurable_state_upper S.tower u d (S.data.windowLevel - u) (S.data.period Λ.stepParams.side) hD _
    (Measurable.ite (S.measurableSet_disjoint u _) measurable_const measurable_const)
private theorem one_le_sum_largeHullIndicator {u R : ℕ} (hu : u ≤ S.data.windowLevel) (w : MarkedSample Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side))
    (hC : ¬ Disjoint (S.stateAtLevel u hu w).2.1 (supBall (S.originSite u (S.sideAtLevel u)) (R : ℝ))) :
    1 ≤ ∑ z ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) (R : ℤ)), largeHullIndicator u z 0 S w := by
  classical
  obtain ⟨y, hy, hb⟩ := Finset.not_disjoint_iff.1 hC
  have hd : (TorusFields.supDist y (S.originSite u (S.sideAtLevel u)) : ℝ) ≤ (R : ℝ) := (Finset.mem_filter.mp hb).2
  have hd' : TorusFields.supDist y (S.originSite u (S.sideAtLevel u)) ≤ R := by exact_mod_cast hd
  have hz : (fun i => (y i - S.originSite u (S.sideAtLevel u) i).valMinAbs) ∈
      Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(R : ℤ)) (R : ℤ)) := by
    refine Fintype.mem_piFinset.2 fun i => ?_
    have h4 : ((y i - S.originSite u (S.sideAtLevel u) i).valMinAbs).natAbs ≤ R :=
      (Finset.le_sup (f := fun i => ((y i - S.originSite u (S.sideAtLevel u) i).valMinAbs).natAbs) (Finset.mem_univ i)).trans hd'
    rw [Finset.mem_Icc]
    show -(R : ℤ) ≤ (y i - S.originSite u (S.sideAtLevel u) i).valMinAbs ∧ (y i - S.originSite u (S.sideAtLevel u) i).valMinAbs ≤ (R : ℤ)
    omega
  have h5 := Finset.single_le_sum (f := fun z => largeHullIndicator u z 0 S w) (fun z _ => S.largeHullIndicator_nonneg _ _ _) hz
  have hsite : S.siteAt u (fun i => (y i - S.originSite u (S.sideAtLevel u) i).valMinAbs) = y := by
    funext i
    show S.originSite u (S.sideAtLevel u) i + ((y i - S.originSite u (S.sideAtLevel u) i).valMinAbs : ZMod (S.sideAtLevel u)) = y i
    rw [ZMod.coe_valMinAbs]
    ring
  have h6 : largeHullIndicator u (fun i => (y i - S.originSite u (S.sideAtLevel u) i).valMinAbs) 0 S w = 1 := by
    rw [S.largeHullIndicator_eq hu, hsite, if_pos hy]
  simp only [h6] at h5
  exact h5
abbrev _root_.YangMills.SharedProofs.p56626 := @one_le_sum_largeHullIndicator
private theorem caseMean_facts (h : SampleFacts S) {j : ℕ} (hj : j + 1 ≤ S.data.windowLevel)
    {Φ : TorusField (S.sideAtLevel (j + 1)) → CaseFunction (S.tower.stage j).toStepSetup (S.sideAtLevel (j + 1))} {Sz : ℝ} (hSz : 0 ≤ Sz)
    (hm : Measurable (caseLift S.tower j _ Φ)) (hb : ∀ x, |caseLift S.tower j _ Φ x| ≤ Sz) :
    AEMeasurable (caseMeanAtSample S.tower j _ Φ) (S.law (j + 1) (S.sideAtLevel (j + 1))) ∧
      ∀ᵐ x ∂(S.law (j + 1) (S.sideAtLevel (j + 1))), |caseMeanAtSample S.tower j _ Φ x| ≤ Sz := by
  have hc := h.condExp_eq j hj Φ hm ⟨Sz, hb⟩
  haveI := h.isProbability (j + 1) (S.sideAtLevel (j + 1))
  refine ⟨(integrable_condExp.aestronglyMeasurable.congr hc).aemeasurable, ?_⟩
  have h0 : ∀ᵐ x ∂(markedSampleLaw S.tower S.β (j + 1) (S.sideAtLevel (j + 1))), |caseLift S.tower j _ Φ x| ≤ (Sz.toNNReal : ℝ) :=
    ae_of_all _ fun x => (hb x).trans (Real.le_coe_toNNReal _)
  have hb1 := ae_bdd_condExp_of_ae_bdd (m := stageSigma S.tower (j + 1) (S.sideAtLevel (j + 1))) h0
  filter_upwards [hb1, hc] with x h1 h2
  rw [← h2]
  refine h1.trans ?_
  rw [Real.coe_toNNReal _ hSz]
end MomentPoint
end Point
section Field
variable {Λ : MomentParameters} {S : MomentPoint Λ}
private def LimitLawAtPoint.extend (F : LimitLawAtPoint S) {J' : Type} [Countable J'] (g' : J' → SampleObservable Λ)
    (hm : ∀ j, TranslatedLaws.HasBoundedMoments (sampleFamily F.rule F.points F.period (g' j))) (sub : ℕ → ℕ) (hsub : StrictMono sub)
    (P' : Measure (TranslateValues (F.Index ⊕ J')))
    (hL : IsJointLimitLaw ((translatedTori F.points F.period).subsequence sub)
      (fun j i => Sum.elim (fun j => sampleFamily F.rule F.points F.period (F.observables j)) (fun j => sampleFamily F.rule F.points F.period (g' j)) j (sub i)) P') :
    LimitLawAtPoint S where
  rule := F.rule
  rule_admissible := F.rule_admissible
  period := F.period
  one_le_period := F.one_le_period
  exponents := F.exponents ∘ sub
  strictMono_exponents := F.strictMono_exponents.comp hsub
  points := F.points ∘ sub
  points_eq := fun i => F.points_eq (sub i)
  Index := F.Index ⊕ J'
  countable_index := by
    haveI := F.countable_index
    infer_instance
  observables := Sum.elim F.observables g'
  hasBoundedMoments := by
    rintro (j | j)
    · exact ⟨fun i => (F.hasBoundedMoments j).aemeasurable (sub i), fun q => by
        obtain ⟨C, h⟩ := (F.hasBoundedMoments j).moment_bound q
        exact ⟨C, fun i => h (sub i)⟩⟩
    · exact ⟨fun i => (hm j).aemeasurable (sub i), fun q => by
        obtain ⟨C, h⟩ := (hm j).moment_bound q
        exact ⟨C, fun i => h (sub i)⟩⟩
  law := P'
  isJointLimitLaw := by
    have e : (fun (j : F.Index ⊕ J') => sampleFamily F.rule (F.points ∘ sub) F.period (Sum.elim F.observables g' j)) =
        fun j i => Sum.elim (fun j => sampleFamily F.rule F.points F.period (F.observables j)) (fun j => sampleFamily F.rule F.points F.period (g' j)) j (sub i) := by
      funext j
      cases j <;> rfl
    rw [e]
    exact hL
private theorem integrable_coord {F : LimitLawAtPoint S} (hM : jointLimitPropertiesStatement) (hk : (translatedTori F.points F.period).IsPreserving) (j : F.Index) :
    Integrable (fun v : TranslateValues F.Index => v (j, 0)) F.law := by
  haveI := F.countable_index
  have h := ((hM _ _ _ _ hk F.hasBoundedMoments F.isJointLimitLaw).2.1 1 fun _ => (j, 0)).1
  simpa using h
abbrev _root_.YangMills.SharedProofs.p44385 := @integrable_coord
private theorem integrable_coord_mul {F : LimitLawAtPoint S} (hM : jointLimitPropertiesStatement) (hk : (translatedTori F.points F.period).IsPreserving) (j j' : F.Index) :
    Integrable (fun v : TranslateValues F.Index => v (j, 0) * v (j', 0)) F.law := by
  haveI := F.countable_index
  have h := ((hM _ _ _ _ hk F.hasBoundedMoments F.isJointLimitLaw).2.1 2 ![(j, 0), (j', 0)]).1
  simpa [Fin.prod_univ_two] using h
private theorem condMeanAt_bounds (G : LimitLawAtPoint S) (hM : jointLimitPropertiesStatement) (hk : (translatedTori G.points G.period).IsPreserving)
    (hae : ∀ n (Q : MarkedSample Λ.stepParams (G.points n).data.windowLevel ((G.points n).data.period Λ.stepParams.side) → Prop),
      (∀ᵐ w ∂((G.points n).law (G.points n).data.windowLevel ((G.points n).data.period Λ.stepParams.side)), Q w) → ∀ᵐ ω ∂(G.points n).sampleLaw, Q ((G.points n).sampleOf G.rule ω))
    (iX iE iR : G.Index) {box : Finset (Fin 4 → ℤ)} (hz : (Fin 4 → ℤ) → G.Index) {b Sz e : ℝ} (hSz : 0 ≤ Sz)
    (hfar : G.condMean (fun v => v (iR, 0) * v (iX, 0)) =ᵐ[G.law] G.condMean (fun v => v (iR, 0) * v (iE, 0)))
    (hRE : ∀ n, ∀ᵐ w ∂((G.points n).law (G.points n).data.windowLevel ((G.points n).data.period Λ.stepParams.side)), G.observables iR (G.points n) w * G.observables iE (G.points n) w ≤ b)
    (hX : ∀ n w, G.observables iX (G.points n) w ≤ G.observables iR (G.points n) w * G.observables iX (G.points n) w + Sz * ∑ z ∈ box, G.observables (hz z) (G.points n) w)
    (hlow : ∀ n w, -Sz ≤ G.observables iX (G.points n) w)
    (hH : ∀ z ∈ box, ∀ᵐ v ∂G.law, G.condMeanAt (hz z) v ≤ e) :
    ∀ᵐ v ∂G.law, -Sz ≤ G.condMeanAt iX v ∧ G.condMeanAt iX v ≤ b + Sz * ((box.card : ℝ) * e) := by
  classical
  have hP : IsProbabilityMeasure G.law := G.isJointLimitLaw.isProbability
  have i1 := integrable_coord hM hk
  have i2 := integrable_coord_mul hM hk
  have B1 : ∀ᵐ v ∂G.law, v (iR, 0) * v (iE, 0) ≤ b := by
    have h := ae_le_of_eventually_le G.isJointLimitLaw (I := Bool) (fun x => cond x iR iE) (fun x => x true * x false - b) (by fun_prop)
      (Eventually.of_forall fun n => by
        have h0 := hae n _ (hRE n)
        filter_upwards [h0] with ω hω
        have hω' : G.observables iR (G.points n) ((G.points n).sampleOf G.rule ω) * G.observables iE (G.points n) ((G.points n).sampleOf G.rule ω) ≤ b := hω
        show G.observables iR (G.points n) ((G.points n).sampleOf G.rule ω) * G.observables iE (G.points n) ((G.points n).sampleOf G.rule ω) - b ≤ 0
        linarith)
    filter_upwards [h] with v hv
    simp only [cond_true, cond_false] at hv
    linarith
  have B2 : ∀ᵐ v ∂G.law, v (iX, 0) ≤ v (iR, 0) * v (iX, 0) + Sz * ∑ z ∈ box, v (hz z, 0) := by
    have h := ae_le_of_eventually_le G.isJointLimitLaw (I := Bool ⊕ {z // z ∈ box}) (Sum.elim (fun x => cond x iX iR) (fun z => hz z.1))
      (fun x => x (.inl true) - (x (.inl false) * x (.inl true) + Sz * ∑ z : {z // z ∈ box}, x (.inr z))) (by fun_prop)
      (Eventually.of_forall fun n => ae_of_all _ fun ω => by
        have e1 : ∀ j, sampleFamily G.rule G.points G.period (G.observables j) n ω = G.observables j (G.points n) ((G.points n).sampleOf G.rule ω) := fun j => rfl
        simp only [Sum.elim_inl, Sum.elim_inr, cond_true, cond_false, e1]
        have e3 := Finset.sum_coe_sort box fun z => G.observables (hz z) (G.points n) ((G.points n).sampleOf G.rule ω)
        rw [e3]
        linarith [hX n ((G.points n).sampleOf G.rule ω)])
    filter_upwards [h] with v hv
    simp only [Sum.elim_inl, Sum.elim_inr, cond_true, cond_false] at hv
    have e3 := Finset.sum_coe_sort box fun z => v (hz z, 0)
    rw [e3] at hv
    linarith
  have B3 : ∀ᵐ v ∂G.law, -Sz ≤ v (iX, 0) := by
    have h := ae_le_of_eventually_le G.isJointLimitLaw (I := Unit) (fun _ => iX) (fun x => -Sz - x ()) (by fun_prop)
      (Eventually.of_forall fun n => ae_of_all _ fun ω => by
        have := hlow n ((G.points n).sampleOf G.rule ω)
        show -Sz - G.observables iX (G.points n) ((G.points n).sampleOf G.rule ω) ≤ 0
        linarith)
    filter_upwards [h] with v hv
    linarith
  have hf0 : Integrable (fun v : TranslateValues G.Index => v (iR, 0) * v (iX, 0)) G.law := i2 _ _
  have hzi : ∀ z ∈ box, Integrable (fun v : TranslateValues G.Index => v (hz z, 0)) G.law := fun z _ => i1 _
  have hsum := (integrable_finsetSum box hzi).const_mul Sz
  have S0 : ∀ᵐ v ∂G.law, invariantCondExp G.law (fun v : TranslateValues G.Index => v (iR, 0) * v (iX, 0)) v ≤ b := by
    have c1 := condExp_mono (m := shiftInvariantSigma G.Index) (i2 iR iE) (integrable_const b) B1
    have c2 : G.law[fun _ : TranslateValues G.Index => b | shiftInvariantSigma G.Index] = fun _ => b := condExp_const shiftInvariantSigma_le b
    filter_upwards [c1, hfar] with v a₁ a₂
    have a₃ : G.condMean (fun v => v (iR, 0) * v (iX, 0)) v = G.condMean (fun v => v (iR, 0) * v (iE, 0)) v := a₂
    show G.condMean (fun v => v (iR, 0) * v (iX, 0)) v ≤ b
    rw [a₃]
    have a₄ : (G.law[fun v : TranslateValues G.Index => v (iR, 0) * v (iE, 0) | shiftInvariantSigma G.Index]) v ≤ (G.law[fun _ : TranslateValues G.Index => b | shiftInvariantSigma G.Index]) v := a₁
    rw [c2] at a₄
    exact a₄
  have S1 := invariantCondExp_add_sum_le box (fun v : TranslateValues G.Index => v (iR, 0) * v (iX, 0)) (fun z v => v (hz z, 0)) hf0 hzi b Sz e hSz S0
    (fun z hzb => hH z hzb)
  have c3 := condExp_mono (m := shiftInvariantSigma G.Index) (i1 iX) (hf0.add hsum) B2
  have c4 := condExp_mono (m := shiftInvariantSigma G.Index) (integrable_const (-Sz)) (i1 iX) B3
  have c5 : G.law[fun _ : TranslateValues G.Index => -Sz | shiftInvariantSigma G.Index] = fun _ => -Sz := condExp_const shiftInvariantSigma_le (-Sz)
  filter_upwards [c3, c4, S1] with v a₁ a₂ a₃
  refine ⟨?_, ?_⟩
  · have a₄ : (G.law[fun _ : TranslateValues G.Index => -Sz | shiftInvariantSigma G.Index]) v ≤ (G.law[fun v : TranslateValues G.Index => v (iX, 0) | shiftInvariantSigma G.Index]) v := a₂
    rw [c5] at a₄
    exact a₄
  · exact le_trans a₁ a₃
end Field
section Main
variable {Λ : MomentParameters}
private theorem period_facts (S : MomentPoint Λ) (hfit : Λ.stepParams.Admissible) :
    Λ.stepParams.side ∣ S.data.period Λ.stepParams.side ∧ 64 ≤ S.data.period Λ.stepParams.side := by
  have h1 := S.side_le
  have hL := hfit.L_ge
  have hn := hfit.n₀_ge
  have big : 64 ≤ Λ.stepParams.side * Λ.stepParams.n₀ := by nlinarith
  have h64 := big.trans h1
  refine ⟨?_, h64⟩
  rcases Nat.eq_zero_or_pos S.data.sideExponent with h0 | h0
  · have : S.data.period Λ.stepParams.side = 2 := by simp [LevelData.period, h0]
    omega
  · exact Dvd.dvd.mul_left (dvd_pow_self _ h0.ne') 2
abbrev _root_.YangMills.SharedProofs.p32373 := @period_facts
private theorem sideAtLevel_eq (S : MomentPoint Λ) (u : ℕ) : S.sideAtLevel u = S.data.sideAt Λ.stepParams.side u := fineSide_eq _ _ _
abbrev _root_.YangMills.DeltaSharedProofs.p7007 := @sideAtLevel_eq
private theorem isBlockTorusSide_sideAtLevel (S : MomentPoint Λ) (hfit : Λ.stepParams.Admissible) (u : ℕ) : IsBlockTorusSide Λ.stepParams (S.sideAtLevel u) := by
  have hLpos : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hside : Λ.stepParams.side * Λ.stepParams.n₀ ≤ S.data.period Λ.stepParams.side := S.side_le
  have hn₀ : 4096 ≤ Λ.stepParams.n₀ := hfit.n₀_ge
  have hm : S.data.sideExponent ≠ 0 := by
    intro h0
    unfold LevelData.period at hside
    rw [h0, pow_zero] at hside
    nlinarith
  rw [sideAtLevel_eq]
  refine ⟨?_, hside.trans (Nat.le_mul_of_pos_right _ (pow_pos hLpos _))⟩
  show Λ.stepParams.side ∣ S.data.period Λ.stepParams.side * Λ.stepParams.side ^ (S.data.windowLevel - u)
  unfold LevelData.period
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ hm) _) _
abbrev _root_.YangMills.SharedProofs.p591 := @isBlockTorusSide_sideAtLevel
private theorem stageOnFlow_of_le (S : MomentPoint Λ) {j : ℕ} (hj : j ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β j (⟨S.tower.stage j, S.resp j⟩ : StageWithResponse Λ.stepParams) := by
  rw [S.stage_eq j hj]
  exact S.onFlow j hj
abbrev _root_.YangMills.DeltaSharedProofs.p500519 := @stageOnFlow_of_le
abbrev _root_.YangMills.SharedProofs.p21183 := @stageOnFlow_of_le
private theorem isTowerOnParameters_of_lt (S : MomentPoint Λ) {s : ℕ} (hs : s + 1 ≤ S.data.windowLevel) : IsTowerAtParameters Λ.table Λ.floor S.tower S.β s where
  startsAtWilson := S.startsAtWilson
  coupling_eq := fun j hj => (stageOnFlow_of_le S (hj.trans hs)).coupling_eq
  onFamily := fun j hj => (stageOnFlow_of_le S (by omega)).onFamily.onFamily
private theorem points_data_eq {S : MomentPoint Λ} (F : LimitLawAtPoint S) (n : ℕ) :
    (F.points n).data.windowLevel = S.data.windowLevel ∧ (F.points n).β = S.β ∧ (F.points n).tower = S.tower := by
  obtain ⟨hp, hs, h⟩ := F.points_eq n
  rw [h]
  exact ⟨rfl, rfl, rfl⟩
abbrev _root_.YangMills.SharedProofs.p61479 := @points_data_eq
private theorem forAll_admissible_floor : ForAllParameters fun Λ => Λ.table.Admissible ∧ Λ.table.floorMin ≤ Λ.floor := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L _ _ Tb _ _ hD _ _ _ _ Kr _ => ?_⟩
  refine ⟨Tb.floorMin, fun y hy _ _ g _ _ k _ _ _ R d _ => ⟨hD, hy⟩⟩
abbrev _root_.YangMills.SharedProofs.p9852 := @forAll_admissible_floor
end Main
theorem clearStateBound_holds (hFar : farCopiesConditionalStatement) (hHull : limitHullBoundsStatement)
    (hExt : jointLimitExtendStatement) (hMn : jointLimitPropertiesStatement) (hPL : largerToriStatement)
    (hLive : liveStatesStatement) (hMC : conditionalMeanIsCaseMeanStatement) (hFS : StagesAreWellPosed)
    (hBI : boundedCaseFunctionIntegrableStatement) (hSB : StageStatesMeasurableStatement)
    (hLD : sampleBelowLawStatement) (hDL : forgetLastStepStatement) (hAR : ruleDrawsChainStatement) :
    clearStateBoundStatement := by
  unfold farCopiesConditionalStatement at hFar
  unfold limitHullBoundsStatement at hHull
  unfold largerToriStatement at hPL
  unfold liveStatesStatement ForAllPoints at hLive
  unfold conditionalMeanIsCaseMeanStatement at hMC
  unfold StagesAreWellPosed at hFS
  unfold clearStateBoundStatement
  refine forAllHull_imp (forAllHull_and hFar (forAllHull_and hHull (forAllHull_and hPL (forAllHull_and (forAllHull_of_forAll hLive) (forAllHull_and (forAllHull_of_admissibleParameters hMC)
    (forAllHull_and (forAllHull_of_admissible (P := fun T y => ∀ (K : ResponseParameters) (β : ℝ)
        (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup) (z₀ : StageWithResponse (T.stepParameters y)),
        IsInitialStage T y β z₀ → ∀ s : ℕ, StagesOnFlowUpTo T K y β hL z₀ s → ∀ t ≤ s,
          (flowStages T y β hL z₀ t).1.toStepSetup.IsWellPosed) hFS) (forAllHull_of_forAll forAll_admissible_floor))))))) ?_
  rintro Λ - ⟨hFr, ⟨Ch, -, hHl⟩, hP, ⟨_, _, _, _, _, hLv⟩, hMC', hFS', hDr, hy⟩
  have hfit : Λ.stepParams.Admissible := hDr.fits Λ.floor hy
  have hlam := hfit.depth_lt
  have hforms : ∀ (S : MomentPoint Λ) (u : ℕ), u ≤ S.data.windowLevel → (S.tower.stage u).toStepSetup.IsWellPosed := by
    intro S u hu
    have h := hFS' Λ.response S.β S.labelFacts S.initial S.isInitial S.data.windowLevel S.onFlow u hu
    rw [← S.stage_eq u hu] at h
    exact h
  have hPF : ∀ S : MomentPoint Λ, SampleFacts S := fun S =>
    { measurable_state := fun u n _ => hSB Λ.stepParams hfit S.tower u n
      sampleBelow_law := fun s d n _ => (hLD Λ.stepParams hfit hlam S.tower S.isCutoff S.marksMeasurable S.β (fun _ => 0)).1 s d n
      isProbability := fun u n _ => (hDL Λ.stepParams hfit hlam S.tower S.isCutoff S.marksMeasurable S.β u n).1
      condExp_eq := fun u hu Φ hm hb => by
        have hbs := isBlockTorusSide_sideAtLevel S hfit (u + 1)
        exact hMC' S.tower S.β u (S.sideAtLevel (u + 1)) (isTowerOnParameters_of_lt S hu) S.isCutoff S.marksMeasurable (hforms S u (by omega))
          ⟨Dvd.intro_left _ rfl, hbs.2.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne _)))⟩ hbs.1 Φ hm hb
      integrable := fun u hu Φ Sz hb1 hb2 => by
        have hbs := isBlockTorusSide_sideAtLevel S hfit (u + 1)
        refine (hLv S (u + 1) hu (S.sideAtLevel (u + 1)) hbs).mono fun x hx' => ?_
        have h3 : 0 < coarseWeightExpansion (S.tower.stage u).toStepSetup (S.sideAtLevel (u + 1)) (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).1
            (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2.1 (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2.2 := hx'.2
        unfold coarseWeightExpansion at h3
        rw [dif_neg (NeZero.ne _)] at h3
        have hfin : coarseStateMass (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup x.2.2.1) x.2.2.1 (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2 ≠ ⊤ := by
          intro h
          have h4 : 0 < coarseStateWeight (S.tower.stage u).toStepSetup (hotCoreSites (S.tower.stage u).toStepSetup x.2.2.1) x.2.2.1 (stageState S.tower (u + 1) (S.sideAtLevel (u + 1)) x).2 := h3
          unfold coarseStateWeight at h4
          rw [h] at h4
          simp at h4
        have hn₀ : Λ.stepParams.n₀ ≤ S.sideAtLevel (u + 1) := by
          have h5 := hbs.2
          have hLpos : 0 < Λ.stepParams.side := Nat.pos_of_ne_zero (NeZero.ne _)
          exact (Nat.le_mul_of_pos_left _ hLpos).trans h5
        exact hBI _ (hforms S u (by omega)) _ hn₀ _ _ _ hfin (Φ x.2.2.1) Sz (hb1 x.2.2.1) (hb2 x.2.2.1) }
  intro S F j Rc Rr Sz b Φ o jX hKj hSz hb hfc hlm hg hcl
  classical
  haveI := F.countable_index
  have hKi : ∀ i, j + 1 ≤ (F.points i).data.windowLevel := fun i => by rw [(points_data_eq F i).1]; exact hKj
  have hkF := ((hP S).2.2.2 F.rule F.exponents F.points F.period F.rule_admissible F.one_le_period F.strictMono_exponents F.points_eq).1
  have hdraw : ∀ i, Measurable ((F.points i).sampleOf F.rule) ∧
      (F.points i).sampleLaw.map ((F.points i).sampleOf F.rule) = (F.points i).law (F.points i).data.windowLevel ((F.points i).data.period Λ.stepParams.side) := fun i => by
    have hr : F.rule.IsAdmissible (F.points i).tower := by
      rw [(points_data_eq F i).2.2]
      exact F.rule_admissible
    obtain ⟨d1, d2⟩ := period_facts (F.points i) hfit
    exact hAR Λ.stepParams hfit (F.points i).tower F.rule (F.points i).β (F.points i).isCutoff (F.points i).marksMeasurable hr (F.points i).data.windowLevel _ d1 d2
  have hae : ∀ i (Q : MarkedSample Λ.stepParams (F.points i).data.windowLevel ((F.points i).data.period Λ.stepParams.side) → Prop),
      (∀ᵐ w ∂((F.points i).law (F.points i).data.windowLevel ((F.points i).data.period Λ.stepParams.side)), Q w) → ∀ᵐ ω ∂(F.points i).sampleLaw, Q ((F.points i).sampleOf F.rule ω) := by
    intro i Q hQ
    rw [← (hdraw i).2] at hQ
    exact ae_of_ae_map (hdraw i).1.aemeasurable hQ
  have hfam : ∀ {g : SampleObservable Λ} {C : ℝ}, (∀ i, AEMeasurable (g (F.points i)) ((F.points i).law (F.points i).data.windowLevel ((F.points i).data.period Λ.stepParams.side))) →
      (∀ i, ∀ᵐ w ∂((F.points i).law (F.points i).data.windowLevel ((F.points i).data.period Λ.stepParams.side)), |g (F.points i) w| ≤ C) →
      TranslatedLaws.HasBoundedMoments (sampleFamily F.rule F.points F.period g) := by
    intro g C h1 h2
    refine hasBoundedMoments_of_abs_le hkF.isProbability (fun i => ?_) (fun i => hae i _ (h2 i))
    have h3 := h1 i
    rw [← (hdraw i).2] at h3
    exact h3.comp_measurable (hdraw i).1
  have hbd : ∀ i x, |caseLift (F.points i).tower j _ (Φ (F.points i)) x| ≤ Sz := fun i x => by
    have h := (hfc i x.2.2.1).abs_le (topField Λ.stepParams j _ x.1) (stageState (F.points i).tower j _ x.1).2.1 (stageState (F.points i).tower j _ x.1).2.2 x.2.2.2 x.2.1
    show |Φ (F.points i) x.2.2.1 (topField Λ.stepParams j _ x.1) _ _ x.2.2.2 x.2.1| ≤ Sz
    simpa using h
  have hmean := fun i => MomentPoint.caseMean_facts (F.points i) (hPF _) (hKi i) hSz (hlm i) (hbd i)
  let g' : (Bool ⊕ (Fin 4 → ℤ)) → SampleObservable Λ := fun e => match e with
    | .inl true => caseMeanObservable j Φ
    | .inl false => clearIndicator (j + 1) Rc
    | .inr z => largeHullIndicator (j + 1) z 0
  have hEq : ∀ i w, caseMeanObservable j Φ (F.points i) w = caseMeanAtSample (F.points i).tower j _ (Φ (F.points i)) ((F.points i).sampleAtLevel (j + 1) (hKi i) w) := fun i w => dif_pos (hKi i)
  have hXq : ∀ i w, caseObservable j Φ (F.points i) w = caseLift (F.points i).tower j _ (Φ (F.points i)) ((F.points i).sampleAtLevel (j + 1) (hKi i) w) := fun i w => dif_pos (hKi i)
  have hm : ∀ e, TranslatedLaws.HasBoundedMoments (sampleFamily F.rule F.points F.period (g' e)) := by
    rintro (e | z)
    · cases e
      · exact hfam (C := 1) (fun i => (MomentPoint.measurable_clearIndicator (F.points i) (hPF _) (j + 1) Rc).aemeasurable)
          (fun i => ae_of_all _ fun w => MomentPoint.abs_clearIndicator_le (F.points i) (j + 1) Rc w)
      · refine hfam (g := caseMeanObservable j Φ) (C := Sz) (fun i => ?_) (fun i => ?_)
        · have e1 : caseMeanObservable j Φ (F.points i) = fun w => caseMeanAtSample (F.points i).tower j _ (Φ (F.points i)) ((F.points i).sampleAtLevel (j + 1) (hKi i) w) := funext (hEq i)
          rw [e1]
          exact MomentPoint.aemeasurable_of_level (F.points i) (hPF _) (j + 1) (hKi i) (hmean i).1
        · have h2 := MomentPoint.ae_of_ae_level (F.points i) (hPF _) (j + 1) (hKi i) (hmean i).2
          filter_upwards [h2] with w hw
          rw [hEq]
          exact hw
    · exact hfam (C := 1) (fun i => (MomentPoint.measurable_largeHullIndicator (F.points i) (hPF _) (j + 1) z).aemeasurable)
        (fun i => ae_of_all _ fun w => MomentPoint.abs_largeHullIndicator_le (F.points i) (j + 1) z w)
  obtain ⟨sub, P', hsub, hlim, -, htr⟩ := hExt (translatedTori F.points F.period) F.Index (Bool ⊕ (Fin 4 → ℤ))
    (fun j => sampleFamily F.rule F.points F.period (F.observables j)) (fun e => sampleFamily F.rule F.points F.period (g' e)) F.law hkF F.hasBoundedMoments hm F.isJointLimitLaw
  obtain ⟨G, hG⟩ : ∃ G : LimitLawAtPoint S, G = LimitLawAtPoint.extend F g' hm sub hsub P' hlim := ⟨_, rfl⟩
  subst hG
  set G := LimitLawAtPoint.extend F g' hm sub hsub P' hlim with hGdef
  have hkG : (translatedTori G.points G.period).IsPreserving := ⟨fun i => hkF.isProbability (sub i), fun i => hkF.measurePreserving (sub i)⟩
  have hcore := condMeanAt_bounds G hMn hkG (fun n Q hQ => hae (sub n) Q hQ) (Sum.inl jX) (Sum.inr (.inl true)) (Sum.inr (.inl false))
    (box := Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rc : ℤ)) (Rc : ℤ))) (fun z => Sum.inr (.inr z)) (b := b)
    (e := Real.exp (-(hullDecayRate Λ.table * S.coupling (j + 1)))) hSz ?_ ?_ ?_ ?_ ?_
  · have hY : Integrable (evalAtZero jX) F.law := by
      have h1 := integrable_coord hMn hkF jX
      exact h1
    have h2 := htr (evalAtZero jX) (-Sz) _ hY (by
      filter_upwards [hcore] with v hv
      exact hv)
    filter_upwards [h2] with v hv
    refine hv.2.trans (le_of_eq ?_)
    have hc : ((Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rc : ℤ)) (Rc : ℤ))).card : ℝ) = (2 * (Rc : ℝ) + 1) ^ 4 := by
      rw [Fintype.card_piFinset]
      simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have e3 : ((Rc : ℤ) + 1 - -(Rc : ℤ)).toNat = 2 * Rc + 1 := by omega
      rw [e3]
      push_cast
      ring
    rw [hc]
    ring
  · refine hFr S G j (fun i => hKi (sub i)) (fun i => Φ (G.points i)) Rr 0 Sz (fun _ => ∅) (fun i => o (sub i)) (fun _ _ => 0)
      (Sum.inl jX) (Sum.inr (.inl true)) (Sum.inr (.inl false)) (fun i V => hfc (sub i) V) (fun i => hlm (sub i))
      (fun i => (hPF _).integrable j (hKi (sub i)) (Φ (G.points i)) Sz (fun V Yt bad b => (hfc (sub i) V).measurable Yt bad b)
        (fun V W Yt ωt bad b => by
          show |Φ (F.points (sub i)) V W Yt ωt bad b| ≤ Sz
          simpa using (hfc (sub i) V).abs_le W Yt ωt bad b))
      ⟨1, fun i => ?_⟩ (fun i w => ?_) (fun i w => ?_) ⟨1, fun i w => MomentPoint.abs_clearIndicator_le (G.points i) (j + 1) Rc w⟩
      (fun i => MomentPoint.clearIndicator_measurableAbove (G.points i) (j + 1) Rc)
    · haveI := (hPF (G.points i)).isProbability (j + 1) ((G.points i).sideAtLevel (j + 1))
      simp [supportWeightOfSample]
    · show F.observables jX (G.points i) w = _
      rw [hg]
      exact hXq (sub i) w
    · exact hEq (sub i) w
  · intro n
    have h0 : ∀ᵐ x ∂((G.points n).law (j + 1) ((G.points n).sideAtLevel (j + 1))), Disjoint (stageState (G.points n).tower (j + 1) _ x).2.1
        (supBall ((G.points n).originSite (j + 1) ((G.points n).sideAtLevel (j + 1))) (Rc : ℝ)) → caseMeanAtSample (G.points n).tower j _ (Φ (G.points n)) x ≤ b := by
      have hc := (hPF (G.points n)).condExp_eq j (hKi (sub n)) (Φ (G.points n)) (hlm (sub n)) ⟨Sz, hbd (sub n)⟩
      filter_upwards [hc, hcl (sub n)] with x a₁ a₂ a₃
      rw [← a₁]
      exact a₂ a₃
    have h1 := MomentPoint.ae_of_ae_level (G.points n) (hPF _) (j + 1) (hKi (sub n)) h0
    filter_upwards [h1] with w hw
    show clearIndicator (j + 1) Rc (G.points n) w * caseMeanObservable j Φ (G.points n) w ≤ b
    have e2 : caseMeanObservable j Φ (G.points n) w = caseMeanAtSample (G.points n).tower j _ (Φ (G.points n)) ((G.points n).sampleAtLevel (j + 1) (hKi (sub n)) w) := hEq (sub n) w
    rw [e2]
    have e1 : clearIndicator (j + 1) Rc (G.points n) w = if Disjoint ((G.points n).stateAtLevel (j + 1) (hKi (sub n)) w).2.1
        (supBall ((G.points n).originSite (j + 1) ((G.points n).sideAtLevel (j + 1))) (Rc : ℝ)) then 1 else 0 := dif_pos (hKi (sub n))
    rw [e1]
    split_ifs with hc
    · rw [one_mul]
      exact hw hc
    · simpa using hb
  · intro n w
    have hgX : G.observables (Sum.inl jX) (G.points n) w = caseObservable j Φ (G.points n) w := by
      show F.observables jX (G.points n) w = _
      rw [hg]
    have hX1 : |caseObservable j Φ (G.points n) w| ≤ Sz := by
      have e2 : caseObservable j Φ (G.points n) w = caseLift (G.points n).tower j _ (Φ (G.points n)) ((G.points n).sampleAtLevel (j + 1) (hKi (sub n)) w) := hXq (sub n) w
      rw [e2]
      exact hbd (sub n) _
    have hR : G.observables (Sum.inr (.inl false)) (G.points n) w = clearIndicator (j + 1) Rc (G.points n) w := rfl
    have hH : ∀ z, G.observables (Sum.inr (.inr z)) (G.points n) w = largeHullIndicator (j + 1) z 0 (G.points n) w := fun _ => rfl
    rw [hgX, hR, Finset.sum_congr rfl fun z _ => hH z]
    have e1 : clearIndicator (j + 1) Rc (G.points n) w = if Disjoint ((G.points n).stateAtLevel (j + 1) (hKi (sub n)) w).2.1
        (supBall ((G.points n).originSite (j + 1) ((G.points n).sideAtLevel (j + 1))) (Rc : ℝ)) then 1 else 0 := dif_pos (hKi (sub n))
    have hs0 : 0 ≤ ∑ z ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(Rc : ℤ)) (Rc : ℤ)), largeHullIndicator (j + 1) z 0 (G.points n) w :=
      Finset.sum_nonneg fun z _ => MomentPoint.largeHullIndicator_nonneg (G.points n) _ _ _
    rw [e1]
    split_ifs with hc
    · have := mul_nonneg hSz hs0
      linarith
    · have h1 := MomentPoint.one_le_sum_largeHullIndicator (G.points n) (hKi (sub n)) w hc
      have h2 := mul_le_mul_of_nonneg_left h1 hSz
      have h3 := le_of_abs_le hX1
      linarith
  · intro n w
    have hX1 : |caseObservable j Φ (G.points n) w| ≤ Sz := by
      have e2 : caseObservable j Φ (G.points n) w = caseLift (G.points n).tower j _ (Φ (G.points n)) ((G.points n).sampleAtLevel (j + 1) (hKi (sub n)) w) := hXq (sub n) w
      rw [e2]
      exact hbd (sub n) _
    have hgX : G.observables (Sum.inl jX) (G.points n) w = caseObservable j Φ (G.points n) w := by
      show F.observables jX (G.points n) w = _
      rw [hg]
    rw [hgX]
    exact (abs_le.mp hX1).1
  · intro z _
    have h := (hHl S G (j + 1) z hKj).1 0 (Sum.inr (.inr z)) le_rfl rfl
    filter_upwards [h] with v hv
    simpa using hv
end YangMills.Construction.MomentLaw
end
