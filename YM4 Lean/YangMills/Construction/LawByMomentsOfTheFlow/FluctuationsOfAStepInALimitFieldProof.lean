import YangMills.Construction.ClusterExpansionOfAStep.GaugeOfACaseProof
import YangMills.Construction.LawByMomentsOfTheFlow.ABoundAtClearStatesInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.ABoundAtClearStatesInALimitField
import YangMills.Construction.ResponseInTheExpansion.FreeCoresOfAStepAreRare
import Mathlib
import YangMills.Construction.LawByMomentsOfTheFlow.FreeCoresAreRareGivenAState
import YangMills.Construction.ResponseInTheExpansion.FluctuationsOverAColdBoxAreBorel
import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelowProof
import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheFluctuationsOfAStep
import YangMills.Construction.ResponseInTheExpansion.TheCasesOffABoxAreTheMirrorProof
set_option autoImplicit false

noncomputable section
open scoped Quaternion
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps StepSettings WeightedResponses ResponseInTheExpansion MarkedIntegrals HullTrees
variable {Λ : MomentParameters}
open Classical in
def truncatedDeviationCases (k j q : ℕ) (cen : (S : MomentPoint Λ) → TorusSite (S.sideAtLevel (j + 1)))
    (Z : (S : MomentPoint Λ) → Finset (TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side)))
    (a : (S : MomentPoint Λ) → TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side) → ℝ) : LevelCaseFunction Λ j :=
  fun S V W _ _ _ _ => ∑ b ∈ Z S, a S b *
    min ‖(if IsColdOnBall Λ.stepParams.threshold V (cen S) (localBlockSide Λ.stepParams S.β k) then
      (stepDeviation S.tower j V W b : ℍ[ℝ]) else 0)‖ 1 ^ (2 * q)
def stepFluctuationBoundStatement : Prop :=
  ForAllHullParameters fun Λ => ∀ q : ℕ, ∃ C x₀ : ℝ, 0 ≤ C ∧ ∀ (S : MomentPoint Λ) (F : LimitLawAtPoint S)
    (k j' Rc Rr : ℕ)
    (cen : (S : MomentPoint Λ) → TorusSite (S.sideAtLevel (k + j' + 1)))
    (Z : (S : MomentPoint Λ) → Finset (TorusBond (S.sideAtLevel (k + j' + 1) * Λ.stepParams.side)))
    (a : (S : MomentPoint Λ) → TorusBond (S.sideAtLevel (k + j' + 1) * Λ.stepParams.side) → ℝ) (A E : ℝ)
    (o : ∀ i, TorusSite ((F.points i).sideAtLevel (k + j' + 1) * Λ.stepParams.side)) (jX : F.Index),
    1 ≤ q → j' < 2 * localChainDepth Λ.stepParams S.β k → k + j' + 1 ≤ S.data.windowLevel → 0 ≤ A → 0 ≤ E →
    (S.tower.stage (k + j')).nextCoupling ≤ 1.01 * (S.tower.stage (k + j')).coupling →
    (∀ i, IsLocalChainAbove Λ.table Λ.floor (F.points i).tower (F.points i).β k
      ((F.points i).sideAtLevel (k + j' + 1)) 1 x₀) →
    (∀ i, Z (F.points i) ⊆ chartBondsInBlocks Λ.stepParams.side
      (supBall (cen (F.points i)) ((localBlockSide Λ.stepParams (F.points i).β k : ℝ) / 8))) →
    (∀ i b, 0 ≤ a (F.points i) b) → (∀ i, ∑ b ∈ Z (F.points i), a (F.points i) b ≤ A) →
    (∀ i, supBall (cen (F.points i)) (localBlockSide Λ.stepParams (F.points i).β k) ⊆
      supBall ((F.points i).originSite (k + j' + 1) ((F.points i).sideAtLevel (k + j' + 1))) (Rc : ℝ)) →
    (∀ i, ((blocksNearFreeCores Λ.stepParams.side ((F.points i).tower.stage (k + j')).toStepSetup.range
        (supBall (cen (F.points i)) (localBlockSide Λ.stepParams (F.points i).β k))).card : ℝ) *
      Real.exp (-(7 * Λ.table.gasRate * ((F.points i).tower.stage (k + j')).coupling)) ≤ E) →
    (∀ i, ∀ b ∈ Z (F.points i), ∀ c : TorusBond ((F.points i).sideAtLevel (k + j' + 1) * Λ.stepParams.side),
      (parentBlock Λ.stepParams.side c.1 = parentBlock Λ.stepParams.side b.1 ∨
        parentBlock Λ.stepParams.side c.1 = parentBlock Λ.stepParams.side (b.1 + unitStep _ b.2)) →
      c.1 ∈ supBall (o i) (Rr : ℝ) ∧ c.1 + unitStep _ c.2 ∈ supBall (o i) (Rr : ℝ)) →
    F.observables jX = caseObservable (k + j') (truncatedDeviationCases k (k + j') q cen Z a) →
    ∀ᵐ v ∂F.law, F.condMeanAt jX v ≤
      A * ((C * flowCouplings Λ.stepParams S.β k ^ (-(1 / 2 : ℝ))) ^ (2 * q) + E) +
      A * (2 * (Rc : ℝ) + 1) ^ 4 * Real.exp (-(hullDecayRate Λ.table * S.coupling (k + j' + 1)))
end YangMills.Construction.MomentLaw
end

set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open StepSettings TorusFields TorusLumps StepCosts StepMarks BlockTrees BlockAverages LumpContours GaugeFixing TopLevelSites SettingFits RenormalizationStepParameters WeightedResponses ResponseInTheExpansion FreeEnergies LevelTestFunctions ClusterExpansionOfAStep
section Limit
private theorem condExp_le_sum_on {Ω : Type} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ m₀) {s : Set Ω}
    (hs : MeasurableSet[m] s) {H : Ω → ℝ} (hH : Integrable H μ) {ι : Type} (I : Finset ι) (g : ι → Ω → ℝ)
    (hg : ∀ i ∈ I, Integrable (g i) μ) (hle : ∀ x, s.indicator H x ≤ ∑ i ∈ I, g i x) (B : ι → ℝ)
    (hB : ∀ i ∈ I, ∀ᵐ x ∂μ, x ∈ s → (μ[g i | m]) x ≤ B i) : ∀ᵐ x ∂μ, x ∈ s → (μ[H | m]) x ≤ ∑ i ∈ I, B i := by
  have hsum : Integrable (fun x => ∑ i ∈ I, g i x) μ := integrable_finsetSum _ hg
  have c1 := condExp_indicator (m := m) hH hs
  have c2 := condExp_mono (m := m) (hH.indicator (hm _ hs)) hsum (ae_of_all _ hle)
  have c3 := condExp_finsetSum (μ := μ) (s := I) (f := g) hg m
  have c4 : (μ[fun x => ∑ i ∈ I, g i x | m]) =ᵐ[μ] μ[∑ i ∈ I, g i | m] :=
    condExp_congr_ae (ae_of_all _ fun x => by simp)
  have c5 : ∀ᵐ x ∂μ, ∀ i ∈ I, x ∈ s → (μ[g i | m]) x ≤ B i := (ae_ball_iff I.countable_toSet).2 hB
  filter_upwards [c1, c2, c3, c4, c5] with x a₁ a₂ a₃ a₄ a₅ hx
  have e1 : (μ[H | m]) x = (μ[s.indicator H | m]) x := by
    rw [a₁, Set.indicator_of_mem hx]
  rw [e1]
  refine a₂.trans ?_
  rw [a₄, a₃, Finset.sum_apply]
  exact Finset.sum_le_sum fun i hi => a₅ i hi hx
abbrev _root_.YangMills.SharedProofs.p3924 := @condExp_le_sum_on
end Limit
section Parameters
private theorem forAllHull_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁) (h₂ : ForAllHullParameters Q₂) :
    ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem forAllHull_imp {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllHullParameters Q₁) (f : ∀ Λ, Λ.k ≤ 8 → Q₁ Λ → Q₂ Λ) :
    ForAllHullParameters Q₂ := by apply _root_.YangMills.SharedProofs.p30752 <;> assumption
private theorem forAllHull_of_forAll {Q : MomentParameters → Prop} (h : ForAllParameters Q) : ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem forAllHull_of_admissibleParameters {P : ParameterAssignment → ℝ → Prop} (h : WeightedResponses.HoldsAtAdmissibleParameters P) :
    ForAllHullParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p3284 <;> assumption
private theorem forAllHull_of_parameters {P : ParameterAssignment → ℝ → Prop} (h : ResponseInTheExpansion.HoldsOnParameterFamilies P) :
    ForAllHullParameters fun Λ => P Λ.table Λ.floor := by
  intro a ha
  obtain ⟨L₀, r₀, C₀, hr, h⟩ := h a ha
  refine ⟨L₀, r₀, C₀, hr, ?_⟩
  intro L hodd hL Tb e1 e2 hD hCS hCH hrt hC
  obtain ⟨y₀, h⟩ := h L hodd hL Tb e1 e2 hD hCS hCH hrt hC
  exact ⟨0, fun Kr _ _ _ _ _ => ⟨y₀, fun y hy hR hW g _ _ k _ _ _ R d _ => h y hy hR hW⟩⟩
private theorem forAllHull_of_admissible {P : ParameterAssignment → ℝ → Prop}
    (h : ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → P T y) :
    ForAllHullParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p14065 <;> assumption
private theorem isBlockTorusSide_sideAtLevel {Λ : MomentParameters} (S : MomentPoint Λ) (hfit : Λ.stepParams.Admissible) (u : ℕ) :
    IsBlockTorusSide Λ.stepParams (S.sideAtLevel u) := by apply _root_.YangMills.SharedProofs.p591 <;> assumption
private theorem stageOnFlow_of_le {Λ : MomentParameters} (S : MomentPoint Λ) {j : ℕ} (hj : j ≤ S.data.windowLevel) :
    StageOnFlow Λ.table Λ.response Λ.floor S.β j (⟨S.tower.stage j, S.resp j⟩ : StageWithResponse Λ.stepParams) := by apply _root_.YangMills.SharedProofs.p21183 <;> assumption
private theorem isTowerOnParameters_of_lt {Λ : MomentParameters} (S : MomentPoint Λ) {s : ℕ} (hs : s + 1 ≤ S.data.windowLevel) :
    IsTowerAtParameters Λ.table Λ.floor S.tower S.β s where
  startsAtWilson := S.startsAtWilson
  coupling_eq := fun j hj => (stageOnFlow_of_le S (hj.trans hs)).coupling_eq
  onFamily := fun j hj => (stageOnFlow_of_le S (by omega)).onFamily.onFamily
private theorem points_data {Λ : MomentParameters} {S : MomentPoint Λ} (F : LimitLawAtPoint S) (n : ℕ) :
    (F.points n).data.windowLevel = S.data.windowLevel ∧ (F.points n).β = S.β ∧ (F.points n).tower = S.tower := by apply _root_.YangMills.SharedProofs.p61479 <;> assumption
private theorem forAll_admissible_floor : ForAllParameters fun Λ => Λ.table.Admissible ∧ Λ.table.floorMin ≤ Λ.floor := by apply _root_.YangMills.SharedProofs.p9852 <;> assumption
private theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
private theorem measurableSet_stageState_disjoint {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) {n : ℕ} [NeZero n] (u : ℕ)
    (B : Finset (TorusSite n)) :
    MeasurableSet {st : StageState T u n | Disjoint st.2.1 B} := by
  have e : {st : StageState T u n | Disjoint st.2.1 B} =
      ⋃ a ∈ {a : Finset (TorusSite n) | Disjoint a B}, {st : StageState T u n | st.2.1 = a} := by
    ext st
    simp
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ => measurable_snd (measurableSet_sigma_fst_eq a)
abbrev _root_.YangMills.SharedProofs.p1690 := @measurableSet_stageState_disjoint
end Parameters
section Gauge
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
private theorem torusSiteInFrame_blockSite_centre (y : TorusSite n) :
    torusSiteInFrame (stepBlockFrame R.params.side n) 0 (blockSite (L := R.params.side) y fun _ => ⟨(R.params.side - 1) / 2, by
      have := NeZero.pos R.params.side
      omega⟩) = cellCentre (F := stepBlockFrame R.params.side n) 0 (torusSiteInFrame (stepBlockFrame R.params.side n) 1 y) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.torusSiteInFrame_blockSite_centre <;> assumption
private theorem axialGauge_gaugeTransform (hodd : Odd R.params.side)
    (Wf : (stepBlockFrame R.params.side n).GaugeField (stepBlockFrame R.params.side n).depth)
    (γ : (stepBlockFrame R.params.side n).Site (stepBlockFrame R.params.side n).depth → UnitQuaternion)
    (x : (stepBlockFrame R.params.side n).Site (stepBlockFrame R.params.side n).depth) :
    axialGauge 1 (BlockAverages.gaugeTransform γ Wf) x =
      γ (cellCentre (stepBlockFrame R.params.side n).depth (enclosingCell x)) * axialGauge 1 Wf x * (γ x)⁻¹ := by apply _root_.YangMills.SharedProofs.p40454 <;> assumption
private theorem blockGauge_gaugeTransform (hodd : Odd R.params.side) (u : TorusSite (n * R.params.side) → UnitQuaternion)
    (hc : ∀ y : TorusSite n, u (blockSite y fun _ => ⟨(R.params.side - 1) / 2, by
      have := NeZero.pos R.params.side
      omega⟩) = 1) (W : TorusField (n * R.params.side)) (x : TorusSite (n * R.params.side)) :
    blockGauge R.params.side (TorusFields.gaugeTransform u W) x = blockGauge R.params.side W x * (u x)⁻¹ := by apply _root_.YangMills.DeltaSharedProofs.p501100 <;> assumption
private theorem chartCoord_gaugeTransform (hodd : Odd R.params.side) (u : TorusSite (n * R.params.side) → UnitQuaternion)
    (hc : ∀ y : TorusSite n, u (blockSite y fun _ => ⟨(R.params.side - 1) / 2, by
      have := NeZero.pos R.params.side
      omega⟩) = 1) (V : TorusField n) (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side)) :
    chartCoord R.params V (TorusFields.gaugeTransform u W) b = chartCoord R.params V W b := by apply _root_.YangMills.DeltaSharedProofs.p502171 <;> assumption
end Gauge
section Deviation
variable {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
private theorem frameDeviation_congr (hodd : Odd ℓ.side) (hn : 2 ≤ n) (ρA : ℝ) (t m₀ : ℕ) (V : TorusField n)
    (W W' : TorusField (n * ℓ.side)) (b : TorusBond (n * ℓ.side))
    (h : ∀ c : TorusBond (n * ℓ.side), (parentBlock ℓ.side c.1 = parentBlock ℓ.side b.1 ∨
      parentBlock ℓ.side c.1 = parentBlock ℓ.side (b.1 + TorusFields.unitStep _ b.2)) → W c.1 c.2 = W' c.1 c.2) :
    frameDeviation ℓ ρA t m₀ V W b = frameDeviation ℓ ρA t m₀ V W' b := by
  have e1 : blockGauge ℓ.side W b.1 = blockGauge ℓ.side W' b.1 :=
    blockGauge_congr hodd hn W W' b.1 fun z i hz _ => h (z, i) (Or.inl hz)
  have e2 : blockGauge ℓ.side W (b.1 + TorusFields.unitStep _ b.2) = blockGauge ℓ.side W' (b.1 + TorusFields.unitStep _ b.2) :=
    blockGauge_congr hodd hn W W' _ fun z i hz _ => h (z, i) (Or.inr hz)
  have e3 : W b.1 b.2 = W' b.1 b.2 := h b (Or.inl rfl)
  unfold frameDeviation
  rw [chartCoord_eq, chartCoord_eq, e1, e2, e3]
private theorem measurable_norm_quaternion {Ξ : Type} [MeasurableSpace Ξ] {f : Ξ → ℍ[ℝ]} (hf : MeasurableQuaternion f) :
    Measurable fun ξ => ‖f ξ‖ := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  have e : (fun ξ => ‖f ξ‖) = fun ξ => Real.sqrt ((f ξ).re ^ 2 + (f ξ).imI ^ 2 + (f ξ).imJ ^ 2 + (f ξ).imK ^ 2) := by
    funext ξ
    rw [← Quaternion.normSq_def', Quaternion.normSq_eq_norm_mul_self, Real.sqrt_mul_self (norm_nonneg _)]
  rw [e]
  exact (((h1.pow_const 2).add (h2.pow_const 2)).add (h3.pow_const 2)).add (h4.pow_const 2) |>.sqrt
abbrev _root_.YangMills.SharedProofs.p6605 := @measurable_norm_quaternion
private theorem measurable_marked_lower (ℓ : TorusLumps.StepParameters) (h n : ℕ) :
    Measurable fun u : MarkedSample ℓ (h + 1) n => u.1 := by apply _root_.YangMills.SharedProofs.p1941 <;> assumption
private theorem measurable_topField (ℓ : TorusLumps.StepParameters) : ∀ (s n : ℕ), Measurable (WeightedResponses.topField ℓ s n)
  | 0, _ => measurable_id
  | _ + 1, _ => measurable_fst.comp (measurable_snd.comp measurable_snd)
end Deviation
section Sum
variable {Λ : MomentParameters}
open Classical in
private def truncatedDeviationSum (S : MomentPoint Λ) (k j q : ℕ) (c : TorusSite (S.sideAtLevel (j + 1)))
    (Z : Finset (TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side)))
    (a : TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side) → ℝ) (V : TorusField (S.sideAtLevel (j + 1)))
    (W : TorusField (S.sideAtLevel (j + 1) * Λ.stepParams.side)) : ℝ :=
  ∑ b ∈ Z, a b * min ‖(if IsColdOnBall Λ.stepParams.threshold V c (localBlockSide Λ.stepParams S.β k) then
    (stepDeviation S.tower j V W b : ℍ[ℝ]) else 0)‖ 1 ^ (2 * q)
private theorem truncatedDeviationCases_eq (k j q : ℕ) (cen : (S : MomentPoint Λ) → TorusSite (S.sideAtLevel (j + 1)))
    (Z : (S : MomentPoint Λ) → Finset (TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side)))
    (a : (S : MomentPoint Λ) → TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side) → ℝ) (S : MomentPoint Λ)
    (V : TorusField (S.sideAtLevel (j + 1))) :
    ∀ W Yt ωt bad b, truncatedDeviationCases k j q cen Z a S V W Yt ωt bad b =
      truncatedDeviationSum S k j q (cen S) (Z S) (a S) V W := fun _ _ _ _ _ => rfl
private theorem caseLift_truncated_eq (k j q : ℕ) (cen : (S : MomentPoint Λ) → TorusSite (S.sideAtLevel (j + 1)))
    (Z : (S : MomentPoint Λ) → Finset (TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side)))
    (a : (S : MomentPoint Λ) → TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side) → ℝ) (S : MomentPoint Λ)
    (x : MarkedSample Λ.stepParams (j + 1) (S.sideAtLevel (j + 1))) :
    caseLift S.tower j _ (truncatedDeviationCases k j q cen Z a S) x =
      truncatedDeviationSum S k j q (cen S) (Z S) (a S) x.2.2.1 (WeightedResponses.topField Λ.stepParams j _ x.1) := rfl
private theorem measurable_of_factor {α β : Type} [MeasurableSpace α] [MeasurableSpace β] {g : β → ℝ} {f : α → β} {h : α → ℝ}
    (hg : Measurable g) (hf : Measurable f) (e : ∀ a, h a = g (f a)) : Measurable h := by
  have e' : h = g ∘ f := funext e
  rw [e']
  exact hg.comp hf
private theorem measurable_truncatedDeviationSum_lift (S : MomentPoint Λ) (k j q : ℕ) (c : TorusSite (S.sideAtLevel (j + 1)))
    (Z : Finset (TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side)))
    (a : TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side) → ℝ)
    (hJ : Measurable fun p : TorusField (S.sideAtLevel (j + 1)) × TorusField (S.sideAtLevel (j + 1) * Λ.stepParams.side) =>
      truncatedDeviationSum S k j q c Z a p.1 p.2) :
    Measurable fun x : MarkedSample Λ.stepParams (j + 1) (S.sideAtLevel (j + 1)) =>
      truncatedDeviationSum S k j q c Z a x.2.2.1 (WeightedResponses.topField Λ.stepParams j _ x.1) := by
  have hp : Measurable fun x : MarkedSample Λ.stepParams (j + 1) (S.sideAtLevel (j + 1)) =>
      ((x.2.2.1, WeightedResponses.topField Λ.stepParams j _ x.1) :
        TorusField (S.sideAtLevel (j + 1)) × TorusField (S.sideAtLevel (j + 1) * Λ.stepParams.side)) :=
    (measurable_topField Λ.stepParams (j + 1) _).prodMk
      ((measurable_topField Λ.stepParams _ _).comp (measurable_marked_lower Λ.stepParams _ _))
  exact measurable_of_factor hJ hp fun _ => rfl
private theorem measurable_truncatedDeviationSum_fine (S : MomentPoint Λ) (k j q : ℕ) (c : TorusSite (S.sideAtLevel (j + 1)))
    (Z : Finset (TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side)))
    (a : TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side) → ℝ)
    (hJ : Measurable fun p : TorusField (S.sideAtLevel (j + 1)) × TorusField (S.sideAtLevel (j + 1) * Λ.stepParams.side) =>
      truncatedDeviationSum S k j q c Z a p.1 p.2) (V : TorusField (S.sideAtLevel (j + 1))) :
    Measurable fun W : TorusField (S.sideAtLevel (j + 1) * Λ.stepParams.side) => truncatedDeviationSum S k j q c Z a V W := by
  have hp : Measurable fun W : TorusField (S.sideAtLevel (j + 1) * Λ.stepParams.side) =>
      ((V, W) : TorusField (S.sideAtLevel (j + 1)) × TorusField (S.sideAtLevel (j + 1) * Λ.stepParams.side)) :=
    measurable_const.prodMk measurable_id
  exact measurable_of_factor hJ hp fun _ => rfl
private theorem measurable_fst_of {R : StepSettings.StepSetup} {n : ℕ} {X : Type} [MeasurableSpace X] (Yt : Finset (TorusSite n))
    (f : X → ℝ) (hf : Measurable f) :
    Measurable fun p : X × (Yt → R.labels.Ω) => f p.1 := hf.comp measurable_fst
private theorem pow_two_mul_abs (C y : ℝ) (hy : 0 ≤ y) (q : ℕ) : (C * y) ^ (2 * q) = (|C| * y) ^ (2 * q) := by
  rw [pow_mul, pow_mul]
  congr 1
  rw [mul_pow, mul_pow, sq_abs]
open Classical in
private theorem condExp_truncatedDeviationSum_le (S : MomentPoint Λ) (k j q : ℕ) (hq : 1 ≤ q) (c : TorusSite (S.sideAtLevel (j + 1)))
    (Z : Finset (TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side)))
    (a : TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side) → ℝ) (Bx : Finset (TorusSite (S.sideAtLevel (j + 1)))) (cq E : ℝ)
    [IsProbabilityMeasure (markedSampleLaw S.tower S.β (j + 1) (S.sideAtLevel (j + 1)))]
    (hmF : stageSigma S.tower (j + 1) (S.sideAtLevel (j + 1)) ≤ markedSampleMeasurableSpace Λ.stepParams (j + 1) (S.sideAtLevel (j + 1)))
    (hsub : supBall c (localBlockSide Λ.stepParams S.β k) ⊆ Bx) (ha : ∀ b, 0 ≤ a b)
    (hG : Integrable (fun x : MarkedSample Λ.stepParams (j + 1) (S.sideAtLevel (j + 1)) =>
        truncatedDeviationSum S k j q c Z a x.2.2.1 (WeightedResponses.topField Λ.stepParams j _ x.1))
      (markedSampleLaw S.tower S.β (j + 1) (S.sideAtLevel (j + 1))))
    (hχ : ∀ b ∈ Z, Integrable (Set.indicator
        {u' | Disjoint (stageState S.tower (j + 1) (S.sideAtLevel (j + 1)) u').2.1 (supBall c (localBlockSide Λ.stepParams S.β k)) ∧
          StepAvoids S.tower j (localBlockSide Λ.stepParams S.β k) c u'}
        (fun u' => ‖(stepDeviation S.tower j u'.2.2.1
          (WeightedResponses.topField Λ.stepParams j (S.sideAtLevel (j + 1) * Λ.stepParams.side) u'.1) b : Quaternion ℝ)‖ ^ (2 * q)))
      (markedSampleLaw S.tower S.β (j + 1) (S.sideAtLevel (j + 1))))
    (hIm : MeasurableSet {u | ¬ StepAvoids S.tower j (localBlockSide Λ.stepParams S.β k) c u})
    (hIb : ∀ᵐ u ∂(markedSampleLaw S.tower S.β (j + 1) (S.sideAtLevel (j + 1))),
      ((markedSampleLaw S.tower S.β (j + 1) (S.sideAtLevel (j + 1)))[{u | ¬ StepAvoids S.tower j (localBlockSide Λ.stepParams S.β k) c u}.indicator
        (fun _ => (1 : ℝ)) | stageSigma S.tower (j + 1) (S.sideAtLevel (j + 1))]) u ≤ E)
    (hm : ∀ b ∈ Z, ∀ᵐ u ∂(markedSampleLaw S.tower S.β (j + 1) (S.sideAtLevel (j + 1))),
      Disjoint (stageState S.tower (j + 1) (S.sideAtLevel (j + 1)) u).2.1 (supBall c (localBlockSide Λ.stepParams S.β k)) →
      ((markedSampleLaw S.tower S.β (j + 1) (S.sideAtLevel (j + 1)))[Set.indicator
        {u' | Disjoint (stageState S.tower (j + 1) (S.sideAtLevel (j + 1)) u').2.1 (supBall c (localBlockSide Λ.stepParams S.β k)) ∧
          StepAvoids S.tower j (localBlockSide Λ.stepParams S.β k) c u'}
        (fun u' => ‖(stepDeviation S.tower j u'.2.2.1
          (WeightedResponses.topField Λ.stepParams j (S.sideAtLevel (j + 1) * Λ.stepParams.side) u'.1) b : Quaternion ℝ)‖ ^ (2 * q)) |
        stageSigma S.tower (j + 1) (S.sideAtLevel (j + 1))]) u ≤ cq) :
    ∀ᵐ x ∂(markedSampleLaw S.tower S.β (j + 1) (S.sideAtLevel (j + 1))),
      Disjoint (stageState S.tower (j + 1) (S.sideAtLevel (j + 1)) x).2.1 Bx →
      ((markedSampleLaw S.tower S.β (j + 1) (S.sideAtLevel (j + 1)))[fun x : MarkedSample Λ.stepParams (j + 1) (S.sideAtLevel (j + 1)) =>
        truncatedDeviationSum S k j q c Z a x.2.2.1 (WeightedResponses.topField Λ.stepParams j _ x.1) |
          stageSigma S.tower (j + 1) (S.sideAtLevel (j + 1))]) x ≤ (∑ b ∈ Z, a b) * (cq + E) := by
  have hs : MeasurableSet[stageSigma S.tower (j + 1) (S.sideAtLevel (j + 1))]
      {x | Disjoint (stageState S.tower (j + 1) (S.sideAtLevel (j + 1)) x).2.1 Bx} :=
    ⟨{st | Disjoint st.2.1 Bx}, measurableSet_stageState_disjoint _ _ _, rfl⟩
  set I : MarkedSample Λ.stepParams (j + 1) (S.sideAtLevel (j + 1)) → ℝ :=
    {u | ¬ StepAvoids S.tower j (localBlockSide Λ.stepParams S.β k) c u}.indicator (fun _ => (1 : ℝ)) with hIdef
  set χ : TorusBond (S.sideAtLevel (j + 1) * Λ.stepParams.side) → MarkedSample Λ.stepParams (j + 1) (S.sideAtLevel (j + 1)) → ℝ :=
    fun b => Set.indicator
      {u' | Disjoint (stageState S.tower (j + 1) (S.sideAtLevel (j + 1)) u').2.1 (supBall c (localBlockSide Λ.stepParams S.β k)) ∧
        StepAvoids S.tower j (localBlockSide Λ.stepParams S.β k) c u'}
      (fun u' => ‖(stepDeviation S.tower j u'.2.2.1
        (WeightedResponses.topField Λ.stepParams j (S.sideAtLevel (j + 1) * Λ.stepParams.side) u'.1) b : Quaternion ℝ)‖ ^ (2 * q))
    with hχdef
  have hI : Integrable I (markedSampleLaw S.tower S.β (j + 1) (S.sideAtLevel (j + 1))) := (integrable_const (1 : ℝ)).indicator hIm
  have hI0 : ∀ x, 0 ≤ I x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hχ0 : ∀ b x, 0 ≤ χ b x := fun b x => Set.indicator_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _) x
  have hc := condExp_le_sum_on hmF hs hG Z (fun b x => a b * (χ b x + I x))
    (fun b hb => ((hχ b hb).add hI).const_mul (a b)) (fun x => ?_) (fun b => a b * (cq + E)) (fun b hb => ?_)
  · filter_upwards [hc] with x hx hd
    rw [Finset.sum_mul]
    exact hx hd
  · by_cases hx : x ∈ {x | Disjoint (stageState S.tower (j + 1) (S.sideAtLevel (j + 1)) x).2.1 Bx}
    · rw [Set.indicator_of_mem hx]
      show ∑ b ∈ Z, a b * min ‖(if IsColdOnBall Λ.stepParams.threshold x.2.2.1 c (localBlockSide Λ.stepParams S.β k) then
        (stepDeviation S.tower j x.2.2.1 (WeightedResponses.topField Λ.stepParams j _ x.1) b : ℍ[ℝ]) else 0)‖ 1 ^ (2 * q) ≤ _
      refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (ha b)
      by_cases hSM : StepAvoids S.tower j (localBlockSide Λ.stepParams S.β k) c x
      · have hmem : x ∈ {u' | Disjoint (stageState S.tower (j + 1) (S.sideAtLevel (j + 1)) u').2.1
            (supBall c (localBlockSide Λ.stepParams S.β k)) ∧ StepAvoids S.tower j (localBlockSide Λ.stepParams S.β k) c u'} :=
          ⟨Finset.disjoint_of_subset_right hsub hx, hSM⟩
        have e1 : χ b x = ‖(stepDeviation S.tower j x.2.2.1
            (WeightedResponses.topField Λ.stepParams j (S.sideAtLevel (j + 1) * Λ.stepParams.side) x.1) b : Quaternion ℝ)‖ ^ (2 * q) :=
          Set.indicator_of_mem hmem _
        rw [e1]
        have h1 : min ‖(if IsColdOnBall Λ.stepParams.threshold x.2.2.1 c (localBlockSide Λ.stepParams S.β k) then
            (stepDeviation S.tower j x.2.2.1 (WeightedResponses.topField Λ.stepParams j _ x.1) b : ℍ[ℝ]) else 0)‖ 1 ^ (2 * q) ≤
            ‖(stepDeviation S.tower j x.2.2.1
              (WeightedResponses.topField Λ.stepParams j (S.sideAtLevel (j + 1) * Λ.stepParams.side) x.1) b : Quaternion ℝ)‖ ^ (2 * q) := by
          refine pow_le_pow_left₀ (le_min (norm_nonneg _) zero_le_one) ((min_le_left _ _).trans ?_) _
          split_ifs
          · exact le_rfl
          · simp
        linarith [hI0 x]
      · have e1 : I x = 1 := Set.indicator_of_mem hSM _
        rw [e1]
        have h1 : min ‖(if IsColdOnBall Λ.stepParams.threshold x.2.2.1 c (localBlockSide Λ.stepParams S.β k) then
            (stepDeviation S.tower j x.2.2.1 (WeightedResponses.topField Λ.stepParams j _ x.1) b : ℍ[ℝ]) else 0)‖ 1 ^ (2 * q) ≤ 1 :=
          pow_le_one₀ (le_min (norm_nonneg _) zero_le_one) (min_le_right _ _)
        linarith [hχ0 b x]
    · rw [Set.indicator_of_notMem hx]
      exact Finset.sum_nonneg fun b _ => mul_nonneg (ha b) (add_nonneg (hχ0 b x) (hI0 x))
  · have c1 := condExp_smul (μ := markedSampleLaw S.tower S.β (j + 1) (S.sideAtLevel (j + 1))) (a b) (χ b + I)
      (stageSigma S.tower (j + 1) (S.sideAtLevel (j + 1)))
    have c2 := condExp_add (μ := markedSampleLaw S.tower S.β (j + 1) (S.sideAtLevel (j + 1))) (hχ b hb) hI
      (stageSigma S.tower (j + 1) (S.sideAtLevel (j + 1)))
    filter_upwards [c1, c2, hm b hb, hIb] with x a₁ a₂ a₃ a₄ hx
    have e1 : (fun x => a b * (χ b x + I x)) = a b • (χ b + I) := rfl
    rw [e1, a₁, Pi.smul_apply, smul_eq_mul, a₂, Pi.add_apply]
    refine mul_le_mul_of_nonneg_left ?_ (ha b)
    have h3 := a₃ (Finset.disjoint_of_subset_right hsub hx)
    exact add_le_add h3 a₄
end Sum
set_option maxHeartbeats 400000 in
theorem stepFluctuationBound_proof (hS : clearStateBoundStatement) (hFree : freeCoresRareGivenStateStatement)
    (hMom : ResponseInTheExpansion.stepDeviationMomentsStatement) (hCB : ResponseInTheExpansion.coldBallDeviationMeasurableStatement)
    (hFS : ResponseInTheExpansion.StagesAreWellPosed) (hSB : ResponseInTheExpansion.StageStatesMeasurableStatement)
    (hDL : WeightedResponses.forgetLastStepStatement) :
    stepFluctuationBoundStatement := by
  unfold clearStateBoundStatement at hS
  unfold freeCoresRareGivenStateStatement at hFree
  unfold ResponseInTheExpansion.stepDeviationMomentsStatement at hMom
  unfold ResponseInTheExpansion.coldBallDeviationMeasurableStatement at hCB
  unfold ResponseInTheExpansion.StagesAreWellPosed at hFS
  unfold stepFluctuationBoundStatement
  refine forAllHull_imp (forAllHull_and hS (forAllHull_and (forAllHull_of_admissibleParameters hFree)
    (forAllHull_and (forAllHull_of_parameters hMom) (forAllHull_and (forAllHull_of_parameters hCB)
    (forAllHull_and (forAllHull_of_admissible (P := fun T y => ∀ (K : ResponseParameters) (β : ℝ)
        (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup) (z₀ : StageWithResponse (T.stepParameters y)),
        IsInitialStage T y β z₀ → ∀ s : ℕ, StagesOnFlowUpTo T K y β hL z₀ s → ∀ t ≤ s,
          (flowStages T y β hL z₀ t).1.toStepSetup.IsWellPosed) hFS) (forAllHull_of_forAll forAll_admissible_floor)))))) ?_
  rintro Λ - ⟨hBd, hFr, hMo, ⟨x₂, hBo⟩, hFS', hDr, hy⟩
  have hfit : Λ.stepParams.Admissible := hDr.fits Λ.floor hy
  have hlam := hfit.depth_lt
  have hodd : Odd Λ.stepParams.side := hDr.L_odd
  have hforms : ∀ (S : MomentPoint Λ) (u : ℕ), u ≤ S.data.windowLevel → (S.tower.stage u).toStepSetup.IsWellPosed := by
    intro S u hu
    have h := hFS' Λ.response S.β S.labelFacts S.initial S.isInitial S.data.windowLevel S.onFlow u hu
    rw [← S.stage_eq u hu] at h
    exact h
  intro q
  obtain ⟨C, x₁, hC⟩ := hMo (2 * q)
  refine ⟨|C|, max (max x₁ x₂) 1, abs_nonneg _, ?_⟩
  intro S F k j' Rc Rr cen Z a A E o jX hq hj hK hA hE hx hloc hZ ha hsum hbox hEb hlocal hg
  classical
  have hKi : ∀ i, k + j' + 1 ≤ (F.points i).data.windowLevel := fun i => by rw [(points_data F i).1]; exact hK
  have hjM : ∀ i, j' < 2 * localChainDepth Λ.stepParams (F.points i).β k := fun i => by rw [(points_data F i).2.1]; exact hj
  have hOn₁ : ∀ i, IsLocalChainAbove Λ.table Λ.floor (F.points i).tower (F.points i).β k
      ((F.points i).sideAtLevel (k + j' + 1)) 1 x₁ := fun i =>
    { hloc i with floor_le := ((le_max_left _ _).trans (le_max_left _ _)).trans (hloc i).floor_le }
  have hOn₂ : ∀ i, IsLocalChainAbove Λ.table Λ.floor (F.points i).tower (F.points i).β k
      ((F.points i).sideAtLevel (k + j' + 1)) 1 x₂ := fun i =>
    { hloc i with floor_le := ((le_max_right _ _).trans (le_max_left _ _)).trans (hloc i).floor_le }
  have hx1 : ∀ i, 1 ≤ flowCouplings Λ.stepParams (F.points i).β k := fun i => (le_max_right _ _).trans (hloc i).floor_le
  have hbs := fun i => isBlockTorusSide_sideAtLevel (F.points i) hfit (k + j' + 1)
  have hn2 : ∀ i, 2 ≤ (F.points i).sideAtLevel (k + j' + 1) := fun i => by
    have h1 := (hbs i).2
    have h2 : 4096 ≤ Λ.stepParams.n₀ := hfit.n₀_ge
    have h3 : 2 ≤ Λ.stepParams.side := by
      have := hfit.L_ge
      omega
    nlinarith
  have hJ : ∀ i, Measurable fun p : TorusField ((F.points i).sideAtLevel (k + j' + 1)) ×
      TorusField ((F.points i).sideAtLevel (k + j' + 1) * Λ.stepParams.side) =>
      truncatedDeviationSum (F.points i) k (k + j') q (cen (F.points i)) (Z (F.points i)) (a (F.points i)) p.1 p.2 := by
    intro i
    unfold truncatedDeviationSum
    refine Finset.measurable_sum _ fun b hb => ?_
    have h1 := hBo (F.points i).tower (F.points i).β k ((F.points i).sideAtLevel (k + j' + 1)) 1 j' (cen (F.points i)) b
      (hOn₂ i) (hbs i).1 (hjM i) (hZ i hb)
    exact ((measurable_norm_quaternion h1).min measurable_const |>.pow_const _).const_mul _
  have hHb : ∀ i (V : TorusField ((F.points i).sideAtLevel (k + j' + 1))) W,
      |truncatedDeviationSum (F.points i) k (k + j') q (cen (F.points i)) (Z (F.points i)) (a (F.points i)) V W| ≤ A := by
    intro i V W
    unfold truncatedDeviationSum
    have h0 : ∀ b ∈ Z (F.points i), 0 ≤ a (F.points i) b * min ‖(if IsColdOnBall Λ.stepParams.threshold V (cen (F.points i))
        (localBlockSide Λ.stepParams (F.points i).β k) then
        (stepDeviation (F.points i).tower (k + j') V W b : ℍ[ℝ]) else 0)‖ 1 ^ (2 * q) := fun b _ =>
      mul_nonneg (ha i b) (pow_nonneg (le_min (norm_nonneg _) zero_le_one) _)
    rw [abs_of_nonneg (Finset.sum_nonneg h0)]
    refine le_trans (Finset.sum_le_sum fun b _ => ?_) (hsum i)
    have h1 : min ‖(if IsColdOnBall Λ.stepParams.threshold V (cen (F.points i)) (localBlockSide Λ.stepParams (F.points i).β k) then
        (stepDeviation (F.points i).tower (k + j') V W b : ℍ[ℝ]) else 0)‖ 1 ^ (2 * q) ≤ 1 :=
      pow_le_one₀ (le_min (norm_nonneg _) zero_le_one) (min_le_right _ _)
    exact (mul_le_mul_of_nonneg_left h1 (ha i b)).trans (by simp)
  have hBor : ∀ i, Measurable (caseLift (F.points i).tower (k + j') _ (truncatedDeviationCases k (k + j') q cen Z a (F.points i))) := by
    intro i
    have e : caseLift (F.points i).tower (k + j') _ (truncatedDeviationCases k (k + j') q cen Z a (F.points i)) = fun x =>
        truncatedDeviationSum (F.points i) k (k + j') q (cen (F.points i)) (Z (F.points i)) (a (F.points i)) x.2.2.1
          (WeightedResponses.topField Λ.stepParams (k + j') _ x.1) :=
      funext (caseLift_truncated_eq k (k + j') q cen Z a (F.points i))
    rw [e]
    exact measurable_truncatedDeviationSum_lift (F.points i) k (k + j') q _ _ _ (hJ i)
  have hb : 0 ≤ A * ((|C| * flowCouplings Λ.stepParams S.β k ^ (-(1 / 2 : ℝ))) ^ (2 * q) + E) := by
    have hx0 : 0 ≤ flowCouplings Λ.stepParams S.β k := by
      have := hx1 0
      rw [(points_data F 0).2.1] at this
      linarith
    have := Real.rpow_nonneg hx0 (-(1 / 2 : ℝ))
    positivity
  have h := hBd S F (k + j') Rc Rr A (A * ((|C| * flowCouplings Λ.stepParams S.β k ^ (-(1 / 2 : ℝ))) ^ (2 * q) + E))
    (truncatedDeviationCases k (k + j') q cen Z a) o jX hK hA hb ?_ hBor hg ?_
  · exact h
  · intro i V
    refine
      { mem_ball := fun y hy => absurd hy (Finset.notMem_empty y)
        weight_measurable := measurable_const
        weight_nonneg := fun _ => le_rfl
        weight_gauge := fun _ _ _ _ => rfl
        abs_le := fun W Yt ωt bad b => ?_
        measurable := fun Yt bad b => ?_
        gaugeInvariant := fun W Yt ωt bad b u _ _ hc => ?_
        sub_le_of_agree := fun m' _ W W' Yt Yt' ωt ωt' bad bad' b b' _ _ hW hY _ => ?_ }
    · rw [truncatedDeviationCases_eq]
      simpa using hHb i V W
    · exact measurable_fst_of (R := ((F.points i).tower.stage (k + j')).toStepSetup) Yt _
        (measurable_truncatedDeviationSum_fine (F.points i) k (k + j') q _ _ _ (hJ i) V)
    · have e : ∀ b', stepDeviation (F.points i).tower (k + j') V (TorusFields.gaugeTransform u W) b' =
          stepDeviation (F.points i).tower (k + j') V W b' := fun b' => by
        unfold stepDeviation frameDeviation
        rw [chartCoord_gaugeTransform (R := ((F.points i).tower.stage (k + j')).toStepSetup) hodd u hc]
      rw [truncatedDeviationCases_eq, truncatedDeviationCases_eq]
      unfold truncatedDeviationSum
      refine Finset.sum_congr rfl fun b' _ => ?_
      simp only [e]
    · have hmono : supBall (o i) (Rr : ℝ) ⊆ supBall (o i) ((Rr : ℝ) + m') := fun z hz => by
        simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        have : (0 : ℝ) ≤ m' := Nat.cast_nonneg _
        linarith
      have e : ∀ b' ∈ Z (F.points i), stepDeviation (F.points i).tower (k + j') V W b' =
          stepDeviation (F.points i).tower (k + j') V W' b' := fun b' hb' => by
        refine frameDeviation_congr hodd (hn2 i) _ _ _ V W W' b' fun c hc => ?_
        obtain ⟨h1, h2⟩ := hlocal i b' hb' c hc
        exact (hW c (hmono h1) (hmono h2)).1
      have e2 : truncatedDeviationSum (F.points i) k (k + j') q (cen (F.points i)) (Z (F.points i)) (a (F.points i)) V W =
          truncatedDeviationSum (F.points i) k (k + j') q (cen (F.points i)) (Z (F.points i)) (a (F.points i)) V W' := by
        unfold truncatedDeviationSum
        exact Finset.sum_congr rfl fun b' hb' => by rw [e b' hb']
      rw [truncatedDeviationCases_eq, truncatedDeviationCases_eq, e2, sub_self, abs_zero]
      simp only [Finset.sum_empty, add_zero, pow_zero, mul_one]
      exact mul_nonneg hA (Real.exp_pos _).le
  · intro i
    obtain ⟨-, hβ, hT⟩ := points_data F i
    have hprob : IsProbabilityMeasure (markedSampleLaw (F.points i).tower (F.points i).β (k + j' + 1)
        ((F.points i).sideAtLevel (k + j' + 1))) :=
      (hDL Λ.stepParams hfit hlam (F.points i).tower (F.points i).isCutoff (F.points i).marksMeasurable (F.points i).β (k + j' + 1)
        ((F.points i).sideAtLevel (k + j' + 1))).1
    have hmF : stageSigma (F.points i).tower (k + j' + 1) ((F.points i).sideAtLevel (k + j' + 1)) ≤
        markedSampleMeasurableSpace Λ.stepParams (k + j' + 1) ((F.points i).sideAtLevel (k + j' + 1)) :=
      (hSB Λ.stepParams hfit (F.points i).tower (k + j' + 1) ((F.points i).sideAtLevel (k + j' + 1))).comap_le
    have hFx : ((F.points i).tower.stage (k + j')).nextCoupling ≤ 1.01 * ((F.points i).tower.stage (k + j')).coupling := by
      rw [hT]
      exact hx
    obtain ⟨hIm, hIb⟩ := hFr (F.points i).tower (F.points i).β (k + j') ((F.points i).sideAtLevel (k + j' + 1))
      (isTowerOnParameters_of_lt _ (hKi i)) (F.points i).isCutoff (F.points i).marksMeasurable
      (hforms _ (k + j') (by have := hKi i; omega)) hFx (hbs i) (localBlockSide Λ.stepParams (F.points i).β k) (cen (F.points i))
    have hy0 : 0 ≤ flowCouplings Λ.stepParams S.β k ^ (-(1 / 2 : ℝ)) := by
      have h2 := hx1 i
      rw [hβ] at h2
      exact Real.rpow_nonneg (by linarith) _
    have hmom : ∀ b ∈ Z (F.points i), _ := fun b hb =>
      hC (F.points i).tower (F.points i).β k ((F.points i).sideAtLevel (k + j' + 1)) 1 j' (cen (F.points i)) {b} (hOn₁ i) (hbs i).1
        (hjM i) (Finset.singleton_subset_iff.mpr (hZ i hb)) (by simpa using hx1 i)
    have hG : Integrable (fun x : MarkedSample Λ.stepParams (k + j' + 1) ((F.points i).sideAtLevel (k + j' + 1)) =>
        truncatedDeviationSum (F.points i) k (k + j') q (cen (F.points i)) (Z (F.points i)) (a (F.points i)) x.2.2.1
          (WeightedResponses.topField Λ.stepParams (k + j') _ x.1))
        (markedSampleLaw (F.points i).tower (F.points i).β (k + j' + 1) ((F.points i).sideAtLevel (k + j' + 1))) :=
      Integrable.of_bound (measurable_truncatedDeviationSum_lift (F.points i) k (k + j') q _ _ _ (hJ i)).aestronglyMeasurable A
        (ae_of_all _ fun x => hHb i _ _)
    have h1 := condExp_truncatedDeviationSum_le (F.points i) k (k + j') q hq (cen (F.points i)) (Z (F.points i)) (a (F.points i))
      (supBall ((F.points i).originSite (k + j' + 1) ((F.points i).sideAtLevel (k + j' + 1))) (Rc : ℝ))
      ((|C| * flowCouplings Λ.stepParams S.β k ^ (-(1 / 2 : ℝ))) ^ (2 * q)) E hmF (hbox i) (ha i) hG
      (fun b hb => (hmom b hb).1 b (Finset.mem_singleton_self b)) hIm (hIb.mono fun u hu => hu.trans (hEb i))
      (fun b hb => ((hmom b hb).2.2).mono fun u hu hd => by
        have h2 := ((hu hd).1 b (Finset.mem_singleton_self b))
        rw [hβ, pow_two_mul_abs C _ hy0 q] at h2
        rw [← hβ] at h2 ⊢
        exact h2)
    filter_upwards [h1] with x hx' hd
    have e : caseLift (F.points i).tower (k + j') _ (truncatedDeviationCases k (k + j') q cen Z a (F.points i)) = fun x =>
        truncatedDeviationSum (F.points i) k (k + j') q (cen (F.points i)) (Z (F.points i)) (a (F.points i)) x.2.2.1
          (WeightedResponses.topField Λ.stepParams (k + j') _ x.1) :=
      funext (caseLift_truncated_eq k (k + j') q cen Z a (F.points i))
    rw [e]
    refine (hx' hd).trans (mul_le_mul_of_nonneg_right (hsum i) ?_)
    have := pow_nonneg (mul_nonneg (abs_nonneg C) hy0) (2 * q)
    linarith
end YangMills.Construction.MomentLaw
end
