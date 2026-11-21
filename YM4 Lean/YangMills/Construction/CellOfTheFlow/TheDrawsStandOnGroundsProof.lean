import YangMills.Construction.CellOfTheFlow.TheDrawsStandOnGrounds
import YangMills.Construction.ClusterExpansionOfAStep.AZeroFactorKillsTheState
import YangMills.Construction.LawOnABoxOfTheFlow.DensityOfTheStateAlongTheFlow
import YangMills.Construction.ResponseInTheExpansion.MassAlongTheLevelsProof
import YangMills.Construction.ResponseInTheExpansion.MeanGivenTheStateOfAStepProof
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChainAreBorel
import YangMills.Construction.ResponseInTheExpansion.TheChainIsALaw
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open StepSettings RenormalizationStepParameters StepGas StepReturn StepFloors TorusLumps TorusFields WeightedResponses StageDensity
private theorem measurableEmbedding_sigmaMk {A : Type} {B : A → Type} [∀ a, MeasurableSpace (B a)] (a : A) :
    MeasurableEmbedding (Sigma.mk a : B a → Sigma B) := by apply _root_.YangMills.SharedProofs.p4862 <;> assumption
private theorem measurable_prod_sigma_of_forall {X A : Type} [MeasurableSpace X] [Countable A] {B : A → Type}
    [∀ a, MeasurableSpace (B a)] {Z : Type} [MeasurableSpace Z] {g : X × Sigma B → Z}
    (hg : ∀ a, Measurable fun p : X × B a => g (p.1, ⟨a, p.2⟩)) : Measurable g := by
  intro s hs
  have hpre : g ⁻¹' s = ⋃ a, Prod.map id (Sigma.mk a) '' ((fun p : X × B a => g (p.1, ⟨a, p.2⟩)) ⁻¹' s) := by
    ext ⟨x, a, b⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq]
    constructor
    · exact fun hx => ⟨a, x, b, hx, rfl, rfl⟩
    · rintro ⟨a', x', b', hx, rfl, hab⟩
      obtain ⟨rfl, hb⟩ := Sigma.mk.inj_iff.mp hab
      obtain rfl := eq_of_heq hb
      exact hx
  rw [hpre]
  exact MeasurableSet.iUnion fun a =>
    (MeasurableEmbedding.id.prodMap (measurableEmbedding_sigmaMk a)).measurableSet_image.2 (hg a hs)
abbrev _root_.YangMills.SharedProofs.p5842 := @measurable_prod_sigma_of_forall
private theorem hasExpansion_expansionCoupling {P : StepParameters} (hret : ExpansionReturnsAt P) {t : ℕ} {x : ℝ}
    {D : TorusFunctional} (hx : P.y₁ ≤ x) (hD : HasExpansion P t x D) :
    HasExpansion P (t + 1) (expansionCoupling P t x D) (kernelImage P x D) ∧
      |expansionCoupling P t x D - x| ≤ 2 * P.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem hasExpansion_couplingFlow {P : StepParameters} (hret : ExpansionReturnsAt P) {β : ℝ}
    (h₀ : HasExpansion P 0 β (wilsonWeight β)) (t : ℕ) (ht : ∀ i < t, P.y₁ ≤ (couplingFlow P β i).1) :
    HasExpansion P t (couplingFlow P β t).1 (couplingFlow P β t).2 := by apply _root_.YangMills.SharedProofs.p3977 <;> assumption
private theorem functional_eq_couplingFlow {Tb : ParameterAssignment} {y : ℝ} {T : StageTower (Tb.stepParameters y)}
    {β : ℝ} {k : ℕ} (hT : IsTowerAtParametersMeasurable Tb y T β k) (u : ℕ) (hu : u ≤ k + 1) :
    (T.stage u).functional = (couplingFlow (Tb.stepParameters y) β u).2 := by
  induction u with
  | zero => exact hT.onFamily.startsAtWilson.functional_eq
  | succ u ih =>
    have hx := hT.onFamily.coupling_eq u (by omega)
    have hD := ih (by omega)
    show kernelImage (Tb.stepParameters y) (T.stage u).coupling (T.stage u).functional = _
    rw [hx, hD]
    rfl
private theorem stage_isSymmetricWeight_of_tower {Tb : ParameterAssignment} {y : ℝ}
    (hret : ExpansionReturnsAt (Tb.stepParameters y))
    (hW : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β))
    {T : StageTower (Tb.stepParameters y)} {β : ℝ} {k u : ℕ} (hT : IsTowerAtParametersMeasurable Tb y T β k)
    (hu : u ≤ k) :
    (T.stage u).toStepSetup.IsSymmetricWeight ∧
      |(T.stage u).toStepSetup.nextCoupling - (T.stage u).toStepSetup.coupling| ≤ 2 * Tb.B := by
  have hc := hT.onFamily.coupling_eq
  have hfloor : ∀ i ≤ k, y ≤ (couplingFlow (Tb.stepParameters y) β i).1 := fun i hi => by
    rw [← hc i (by omega)]
    exact (hT.onFamily.onFamily i hi).le_coupling
  have hexp := hasExpansion_couplingFlow hret (hW β (hfloor 0 (Nat.zero_le _))) u fun i hi => hfloor i (by omega)
  have hmove := (hasExpansion_expansionCoupling hret (hfloor u hu) hexp).2
  have e₀ : (T.stage u).coupling = (couplingFlow (Tb.stepParameters y) β u).1 := hc u (by omega)
  have e₁ : (T.stage u).nextCoupling = (couplingFlow (Tb.stepParameters y) β (u + 1)).1 := hc (u + 1) (by omega)
  have e₂ : (couplingFlow (Tb.stepParameters y) β (u + 1)).1 =
      expansionCoupling (Tb.stepParameters y) u (couplingFlow (Tb.stepParameters y) β u).1
        (couplingFlow (Tb.stepParameters y) β u).2 := rfl
  constructor
  · unfold StepSetup.IsSymmetricWeight
    show ∀ n [NeZero n], (Tb.stepParameters y).n₀ ≤ n → _
    have e₃ := functional_eq_couplingFlow hT u (by omega)
    simp only [e₃]
    exact hexp.1
  · show |(T.stage u).nextCoupling - (T.stage u).coupling| ≤ 2 * Tb.B
    rw [e₁, e₀, e₂]
    exact hmove
private theorem isWellPosed_of_onParameters {T : ParameterAssignment} (hT : T.Admissible) {y : ℝ} (hy₀ : T.floorMin ≤ y)
    (hy₁ : 1 ≤ y) {R : StepSetup} (hon : R.OnParameters T y) (hmoved : |R.nextCoupling - R.coupling| ≤ 2 * T.B)
    (hsym : R.IsSymmetricWeight)
    (hF : T.FloorConditions (2 ^ 40 * T.side + 4 * T.n₀ + 2 ^ 17) 1 R.coupling) : R.IsWellPosed := by apply _root_.YangMills.SharedProofs.p3707 <;> assumption
section Live
variable {P : StepParameters} (T : StageTower P)
open Classical in
private def deadIndicator (w n : ℕ) [NeZero n] (q : StageState T w n) : ENNReal :=
  if IsLiveState P (T.stage w).coupling (T.stage w).labelWeight q.1 q.2.1 q.2.2 then 0 else 1
private theorem measurable_deadIndicator (w n : ℕ) [NeZero n] (hb : IsBlockTorusSide P n)
    (hexp : HullExpansion P (T.stage w).depth (T.stage w).coupling (T.stage w).functional (T.stage w).density
      (T.stage w).labels (T.stage w).labelWeight (T.stage w).clusterFactor (T.stage w).siteDensity) :
    Measurable (deadIndicator T w n) := by
  classical
  refine measurable_prod_sigma_of_forall fun Y => ?_
  have h₁ := (hexp.borel n hb Y).1
  have hset : MeasurableSet {p : TorusField n × (Y → (T.stage w).labels.Ω) |
      0 < (if IsHullState P (clusterRange (T.stage w).coupling) p.1 Y then
        (T.stage w).labelWeight n p.1 Y p.2 else 0)} :=
    measurableSet_lt measurable_const h₁
  have hfun : (fun p : TorusField n × (Y → (T.stage w).labels.Ω) => deadIndicator T w n (p.1, ⟨Y, p.2⟩)) =
      fun p => if 0 < (if IsHullState P (clusterRange (T.stage w).coupling) p.1 Y then
        (T.stage w).labelWeight n p.1 Y p.2 else 0) then 0 else 1 := by
    funext p
    unfold deadIndicator IsLiveState
    by_cases hh : IsHullState P (clusterRange (T.stage w).coupling) p.1 Y
    · simp [hh]
    · simp [hh]
  rw [hfun]
  exact Measurable.ite hset measurable_const measurable_const
end Live
theorem drawsStandOnGrounds_of_stageDensity (hDen : stageStateDensityStatement)
    (hGr : HullStateIsHotCase) (hZero : ClusterExpansionOfAStep.CoarseWeightZeroOfFactorZero)
    (hFl : EventuallyFloorConditions) (hLaw : ChainIsProbabilityLaw)
    (hSt : ResponseInTheExpansion.StageStatesMeasurableStatement) : drawsStandOnGroundsStatement := by
  intro a ha
  obtain ⟨L₀, r₀, hr₀, hDen'⟩ := hDen a ha
  refine ⟨L₀, r₀, hr₀, fun L hodd hL Tb hTa hTL hAdm hr => ?_⟩
  obtain ⟨yD, hyD⟩ := hDen' L hodd hL Tb hTa hTL hAdm hr
  obtain ⟨yG, hyG⟩ := hGr Tb hAdm
  have hCpos : (0 : ℝ) < 2 ^ 40 * Tb.side + 4 * Tb.n₀ + 2 ^ 17 := by positivity
  obtain ⟨yF, hyF⟩ := hFl Tb hAdm _ 1 hCpos one_pos
  refine ⟨max (max yD yG) (max yF (max Tb.floorMin 1)), fun y hy hret hW T β j hT n _ hn => ?_⟩
  have hyD' : yD ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans hy
  have hyG' : yG ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans hy
  have hyF' : yF ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy₀' : Tb.floorMin ≤ y := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hy₁' : 1 ≤ y := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hy
  have hadm : (Tb.stepParameters y).Admissible := hAdm.fits y hy₀'
  have hon : (T.stage j).toStepSetup.OnParameters Tb y := hT.onFamily.onFamily j (Nat.le_succ j)
  have hwp : (T.stage j).toStepSetup.IsWellPosed := by
    obtain ⟨hsym, hmoved⟩ := stage_isSymmetricWeight_of_tower hret hW hT (Nat.le_succ j)
    exact isWellPosed_of_onParameters hAdm hy₀' hy₁' hon hmoved hsym (hyF _ (hyF'.trans hon.le_coupling))
  have hlive : ∀ᵐ d ∂(markedSampleLaw T β (j + 1) n), IsLiveState (Tb.stepParameters y)
      (T.stage (j + 1)).coupling (T.stage (j + 1)).labelWeight (stageState T (j + 1) n d).1
      (stageState T (j + 1) n d).2.1 (stageState T (j + 1) n d).2.2 := by
    have hm := measurable_deadIndicator T (j + 1) n hn (hT.onFamily.onFamily (j + 1) le_rfl).isStep.1.2
    have hd := hyD y hyD' hret hW T β (j + 1) n hT.onFamily hT.measurable hn (deadIndicator T (j + 1) n) hm
    have hzero : (∫⁻ W, (open Classical in
        ∑ Y ∈ Finset.univ.filter (IsHullState (Tb.stepParameters y) (clusterRange (T.stage (j + 1)).coupling) W),
          ∫⁻ ω, deadIndicator T (j + 1) n (W, ⟨Y, ω⟩) * ENNReal.ofReal ((T.stage (j + 1)).labelWeight n W Y ω)
            ∂(Measure.pi fun _ : Y => (T.stage (j + 1)).labels.μ)) ∂(fieldHaar n)) = 0 := by
      refine (lintegral_congr fun W => ?_).trans lintegral_zero
      classical
      refine Finset.sum_eq_zero fun Y hY => ?_
      have hH : IsHullState (Tb.stepParameters y) (clusterRange (T.stage (j + 1)).coupling) W Y :=
        (Finset.mem_filter.mp hY).2
      refine (lintegral_congr fun ω => ?_).trans lintegral_zero
      unfold deadIndicator
      by_cases hp : 0 < (T.stage (j + 1)).labelWeight n W Y ω
      · rw [if_pos ⟨hH, hp⟩, zero_mul]
      · rw [ENNReal.ofReal_of_nonpos (not_lt.mp hp), mul_zero]
    have hZ : (0 : ℝ) < ∫ W, wilsonWeight β (fineSide (Tb.stepParameters y).side (j + 1) n) W
        ∂(fieldHaar (fineSide (Tb.stepParameters y).side (j + 1) n)) :=
      (hLaw (Tb.stepParameters y) hadm hadm.depth_lt β (fun _ => 0) (j + 1) n).2.1
    rw [hzero] at hd
    have hz := (mul_eq_zero.mp hd).resolve_left (by simpa using hZ)
    have hm₂ : Measurable fun d => deadIndicator T (j + 1) n (stageState T (j + 1) n d) :=
      hm.comp (hSt _ hadm T (j + 1) n)
    have hae := (lintegral_eq_zero_iff hm₂).mp hz
    filter_upwards [hae] with d hd₀
    by_contra hcon
    have h₁ : deadIndicator T (j + 1) n (stageState T (j + 1) n d) = 1 := by
      unfold deadIndicator
      exact if_neg hcon
    rw [show deadIndicator T (j + 1) n (stageState T (j + 1) n d) = 0 from hd₀] at h₁
    exact zero_ne_one h₁
  filter_upwards [hlive] with d hd
  obtain ⟨hH, hpos⟩ := hd
  refine Or.inr (hyG y hyG' (T.stage j).toStepSetup hon hwp n hn d.2.2.1 _ hH ?_)
  intro X hX h₀
  have hz := hZero (T.stage j).toStepSetup hwp n hn d.2.2.1 _ hH ⟨X, hX, h₀⟩
  have hpos' : 0 < coarseStateWeight (T.stage j).toStepSetup (hotCoreSites (T.stage j).toStepSetup d.2.2.1)
      d.2.2.1 (stageState T (j + 1) n d).2 := by
    have e : (T.stage (j + 1)).labelWeight n (stageState T (j + 1) n d).1 (stageState T (j + 1) n d).2.1
        (stageState T (j + 1) n d).2.2 = coarseStateWeight (T.stage j).toStepSetup
          (hotCoreSites (T.stage j).toStepSetup d.2.2.1) d.2.2.1 (stageState T (j + 1) n d).2 := by
      show coarseWeightExpansion (T.stage j).toStepSetup n _ _ _ = _
      simp only [coarseWeightExpansion, NeZero.ne n, dite_false]
      rfl
    rw [← e]
    exact hpos
  exact absurd hz hpos'.ne'
end YangMills.Construction.CellWindows
end
