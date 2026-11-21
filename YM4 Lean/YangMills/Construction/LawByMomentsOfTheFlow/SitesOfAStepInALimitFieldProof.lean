import YangMills.Construction.LawByMomentsOfTheFlow.FluctuationsOfAStepInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.SitesOfAStepInALimitField
import YangMills.Construction.ResponseInTheExpansion.OneStepDownKeepsTheBoxClearProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.TorusLumps YangMills.Construction.StepSettings YangMills.Construction.RenormalizationStepParameters YangMills.Construction.TorusFields YangMills.Construction.WeightedResponses YangMills.Construction.ResponseInTheExpansion YangMills.Construction.ClusterExpansionOfAStep YangMills.Construction.LevelTestFunctions YangMills.Construction.MomentMethod YangMills.Construction.FreeEnergies
section Conditional
private theorem condExp_le_sum_on {Ω : Type} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ m₀) {s : Set Ω}
    (hs : MeasurableSet[m] s) {H : Ω → ℝ} (hH : Integrable H μ) {ι : Type} (I : Finset ι) (g : ι → Ω → ℝ)
    (hg : ∀ i ∈ I, Integrable (g i) μ) (hle : ∀ x, s.indicator H x ≤ ∑ i ∈ I, g i x) (B : ι → ℝ)
    (hB : ∀ i ∈ I, ∀ᵐ x ∂μ, x ∈ s → (μ[g i | m]) x ≤ B i) : ∀ᵐ x ∂μ, x ∈ s → (μ[H | m]) x ≤ ∑ i ∈ I, B i := by apply _root_.YangMills.SharedProofs.p3924 <;> assumption
end Conditional
section Parameters
private theorem forAllHull_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁) (h₂ : ForAllHullParameters Q₂) :
    ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem forAllHull_imp {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllHullParameters Q₁) (f : ∀ Λ, Λ.k ≤ 8 → Q₁ Λ → Q₂ Λ) :
    ForAllHullParameters Q₂ := by apply _root_.YangMills.SharedProofs.p30752 <;> assumption
private theorem forAllHull_of_forAll {Q : MomentParameters → Prop} (h : ForAllParameters Q) : ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem forAllHull_of_admissibleParameters {P : ParameterAssignment → ℝ → Prop} (h : HoldsAtAdmissibleParameters P) :
    ForAllHullParameters fun Λ => P Λ.table Λ.floor := by apply _root_.YangMills.SharedProofs.p3284 <;> assumption
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
private theorem points_windowLevel_eq {Λ : MomentParameters} {S : MomentPoint Λ} (F : LimitLawAtPoint S) (n : ℕ) :
    (F.points n).data.windowLevel = S.data.windowLevel ∧ (F.points n).β = S.β ∧ (F.points n).tower = S.tower := by apply _root_.YangMills.SharedProofs.p61479 <;> assumption
private theorem forAll_admissible_floor : ForAllParameters fun Λ => Λ.table.Admissible ∧ Λ.table.floorMin ≤ Λ.floor := by apply _root_.YangMills.SharedProofs.p9852 <;> assumption
private theorem measurableSet_sigma_fst_eq {A : Type} {β : A → Type} [∀ a, MeasurableSpace (β a)] (a : A) :
    MeasurableSet {z : Sigma β | z.1 = a} := by apply _root_.YangMills.SharedProofs.p1937 <;> assumption
private theorem measurableSet_disjoint_support {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) {n : ℕ} [NeZero n] (u : ℕ)
    (B : Finset (TorusSite n)) :
    MeasurableSet {st : StageState T u n | Disjoint st.2.1 B} := by apply _root_.YangMills.SharedProofs.p1690 <;> assumption
end Parameters
section Cores
variable (R : StepSetup) {n : ℕ} [NeZero n]
private theorem parentBlock_not_mem (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (C Z : Finset (TorusSite n))
    (hY : Disjoint (coarseHull R.params.side R.range R.nextRange bad Yt C) Z) (hF : FreeCoresAvoid R Yt bad C Z)
    {z : TorusSite (n * R.params.side)} (hz : z ∈ bad.image Prod.fst ∪ Yt ∪ sitesInBlocks R.params.side C) :
    parentBlock R.params.side z ∉ Z := by apply _root_.YangMills.SharedProofs.p27757 <;> assumption
end Cores
theorem siteIndicatorLimitBoundStatement_holds (hS : clearStateBoundStatement) (hFree : freeCoresRareGivenStateStatement)
    (hFS : StagesAreWellPosed) (hSB : StageStatesMeasurableStatement) (hDL : forgetLastStepStatement) :
    siteIndicatorLimitBoundStatement := by
  unfold clearStateBoundStatement at hS
  unfold freeCoresRareGivenStateStatement at hFree
  unfold StagesAreWellPosed at hFS
  unfold siteIndicatorLimitBoundStatement
  refine forAllHull_imp (forAllHull_and hS (forAllHull_and (forAllHull_of_admissibleParameters hFree)
    (forAllHull_and (forAllHull_of_admissible (P := fun T y => ∀ (K : ResponseParameters) (β : ℝ)
        (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup) (z₀ : StageWithResponse (T.stepParameters y)),
        IsInitialStage T y β z₀ → ∀ s : ℕ, StagesOnFlowUpTo T K y β hL z₀ s → ∀ t ≤ s,
          (flowStages T y β hL z₀ t).1.toStepSetup.IsWellPosed) hFS) (forAllHull_of_forAll forAll_admissible_floor)))) ?_
  rintro Λ - ⟨hBd, hFr, hFS', hDr, hy⟩
  have hfit : Λ.stepParams.Admissible := hDr.fits Λ.floor hy
  have hlam := hfit.depth_lt
  have hforms : ∀ (S : MomentPoint Λ) (u : ℕ), u ≤ S.data.windowLevel → (S.tower.stage u).toStepSetup.IsWellPosed := by
    intro S u hu
    have h := hFS' Λ.response S.β S.labelFacts S.initial S.isInitial S.data.windowLevel S.onFlow u hu
    rw [← S.stage_eq u hu] at h
    exact h
  intro S F j Rc Rr Z m Nz E o jX hK hm hE hNz hx hcard hbox hEb hloc hg
  classical
  have hKi : ∀ i, j + 1 ≤ (F.points i).data.windowLevel := fun i => by rw [(points_windowLevel_eq F i).1]; exact hK
  have hb : 0 ≤ Nz * E := mul_nonneg hNz hE
  have hBor : ∀ i, Measurable (caseLift (F.points i).tower j _ (badOrSupportSiteCase j Z (F.points i))) := by
    intro i
    have hbs := isBlockTorusSide_sideAtLevel (F.points i) hfit (j + 1)
    have hSt := hSB Λ.stepParams hfit (F.points i).tower j ((F.points i).sideAtLevel (j + 1) * Λ.stepParams.side)
    obtain ⟨hprob, hpres⟩ := hDL Λ.stepParams hfit hlam (F.points i).tower (F.points i).isCutoff (F.points i).marksMeasurable
      (F.points i).β j ((F.points i).sideAtLevel (j + 1))
    have hfst : Measurable (fun u : MarkedSample Λ.stepParams (j + 1) ((F.points i).sideAtLevel (j + 1)) => u.1) := hpres.measurable
    have hsnd : Measurable (fun u : MarkedSample Λ.stepParams (j + 1) ((F.points i).sideAtLevel (j + 1)) => u.2) := measurable_snd
    have hBm : Measurable (fun u : MarkedSample Λ.stepParams (j + 1) ((F.points i).sideAtLevel (j + 1)) => u.2.2.2) :=
      measurable_snd.comp (measurable_snd.comp hsnd)
    have hStm := hSt.comp hfst
    have e : caseLift (F.points i).tower j _ (badOrSupportSiteCase j Z (F.points i)) = fun u =>
        if (((show Finset (TorusBond ((F.points i).sideAtLevel (j + 1) * Λ.stepParams.side)) from u.2.2.2).image Prod.fst ∪
          (stageState (F.points i).tower j _ u.1).2.1) ∩ Z (F.points i)).Nonempty then (1 : ℝ) else 0 := rfl
    rw [e]
    refine Measurable.ite ?_ measurable_const measurable_const
    have e2 : {u : MarkedSample Λ.stepParams (j + 1) ((F.points i).sideAtLevel (j + 1)) |
        (((show Finset (TorusBond ((F.points i).sideAtLevel (j + 1) * Λ.stepParams.side)) from u.2.2.2).image Prod.fst ∪
        (stageState (F.points i).tower j _ u.1).2.1) ∩ Z (F.points i)).Nonempty} =
        ⋃ d ∈ {d : Finset (TorusSite ((F.points i).sideAtLevel (j + 1) * Λ.stepParams.side)) ×
            Finset (TorusBond ((F.points i).sideAtLevel (j + 1) * Λ.stepParams.side)) |
            ((d.2.image Prod.fst ∪ d.1) ∩ Z (F.points i)).Nonempty},
          ({u | (stageState (F.points i).tower j _ u.1).2.1 = d.1} ∩
            {u | (u.2.2.2 : Finset (TorusBond ((F.points i).sideAtLevel (j + 1) * Λ.stepParams.side))) = d.2}) := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop, Prod.exists]
      constructor
      · intro h1
        exact ⟨_, _, h1, rfl, rfl⟩
      · rintro ⟨a, c, h1, rfl, rfl⟩
        exact h1
    rw [e2]
    refine MeasurableSet.biUnion (Set.to_countable _) fun d _ => MeasurableSet.inter ?_ ?_
    · exact hStm (measurable_snd (measurableSet_sigma_fst_eq d.1))
    · exact hBm (MeasurableSpace.measurableSet_top (s := {d.2}))
  have h := hBd S F j Rc Rr 1 (Nz * E) (badOrSupportSiteCase j Z) o jX hK zero_le_one hb ?_ hBor hg ?_
  · filter_upwards [h] with v hv
    simpa using hv
  · intro i V
    refine
      { mem_ball := fun y hy => absurd hy (Finset.notMem_empty y)
        weight_measurable := measurable_const
        weight_nonneg := fun _ => le_rfl
        weight_gauge := fun _ _ _ _ => rfl
        abs_le := fun W Yt ωt bad b => ?_
        measurable := fun Yt bad b => measurable_const
        gaugeInvariant := fun W Yt ωt bad b u _ _ _ => rfl
        sub_le_of_agree := fun m' _ W W' Yt Yt' ωt ωt' bad bad' b b' _ _ hW hY _ => ?_ }
    · simp only [badOrSupportSiteCase, Finset.sum_empty, add_zero, pow_zero, mul_one]
      split_ifs <;> simp
    · have hsame : ∀ y ∈ Z (F.points i), y ∈ bad.image Prod.fst ∪ Yt ↔ y ∈ bad'.image Prod.fst ∪ Yt' := by
        intro y hyZ
        obtain ⟨h1, h2⟩ := hloc i y hyZ
        have hmono : supBall (o i) (Rr : ℝ) ⊆ supBall (o i) ((Rr : ℝ) + m') := fun z hz => by
          simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
          have : (0 : ℝ) ≤ m' := Nat.cast_nonneg _
          linarith
        have hYt := (hY y (hmono h1)).1
        have hbad : ∀ c : TorusBond ((F.points i).sideAtLevel (j + 1) * Λ.stepParams.side), c.1 = y → (c ∈ bad ↔ c ∈ bad') := by
          rintro ⟨c1, c2⟩ rfl
          exact (hW (c1, c2) (hmono h1) (hmono (h2 c2))).2
        simp only [Finset.mem_union, Finset.mem_image]
        constructor
        · rintro (⟨c, hc, rfl⟩ | h3)
          · exact Or.inl ⟨c, (hbad c rfl).1 hc, rfl⟩
          · exact Or.inr (hYt.1 h3)
        · rintro (⟨c, hc, rfl⟩ | h3)
          · exact Or.inl ⟨c, (hbad c rfl).2 hc, rfl⟩
          · exact Or.inr (hYt.2 h3)
      have e : (((bad.image Prod.fst ∪ Yt) ∩ Z (F.points i)).Nonempty ↔ ((bad'.image Prod.fst ∪ Yt') ∩ Z (F.points i)).Nonempty) := by
        constructor
        · rintro ⟨y, hy⟩
          obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hy
          exact ⟨y, Finset.mem_inter.mpr ⟨(hsame y h2).1 h1, h2⟩⟩
        · rintro ⟨y, hy⟩
          obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hy
          exact ⟨y, Finset.mem_inter.mpr ⟨(hsame y h2).2 h1, h2⟩⟩
      simp only [badOrSupportSiteCase, Finset.sum_empty, add_zero, pow_zero, mul_one, one_mul]
      rw [if_congr e rfl rfl, sub_self, abs_zero]
      exact (Real.exp_pos _).le
  · intro i
    have hbs := isBlockTorusSide_sideAtLevel (F.points i) hfit (j + 1)
    obtain ⟨-, -, hT⟩ := points_windowLevel_eq F i
    haveI hprob : IsProbabilityMeasure (markedSampleLaw (F.points i).tower (F.points i).β (j + 1) ((F.points i).sideAtLevel (j + 1))) :=
      (hDL Λ.stepParams hfit hlam (F.points i).tower (F.points i).isCutoff (F.points i).marksMeasurable (F.points i).β (j + 1)
        ((F.points i).sideAtLevel (j + 1))).1
    have hmF : stageSigma (F.points i).tower (j + 1) ((F.points i).sideAtLevel (j + 1)) ≤
        markedSampleMeasurableSpace Λ.stepParams (j + 1) ((F.points i).sideAtLevel (j + 1)) :=
      (hSB Λ.stepParams hfit (F.points i).tower (j + 1) ((F.points i).sideAtLevel (j + 1))).comap_le
    have hs : MeasurableSet[stageSigma (F.points i).tower (j + 1) ((F.points i).sideAtLevel (j + 1))]
        {x | Disjoint (stageState (F.points i).tower (j + 1) ((F.points i).sideAtLevel (j + 1)) x).2.1
          (supBall ((F.points i).originSite (j + 1) ((F.points i).sideAtLevel (j + 1))) (Rc : ℝ))} :=
      ⟨{st | Disjoint st.2.1 (supBall ((F.points i).originSite (j + 1) ((F.points i).sideAtLevel (j + 1))) (Rc : ℝ))},
        measurableSet_disjoint_support _ _ _, rfl⟩
    have hFx : ((F.points i).tower.stage j).nextCoupling ≤ 1.01 * ((F.points i).tower.stage j).coupling := by
      rw [hT]
      exact hx
    have hfr := fun c : TorusSite ((F.points i).sideAtLevel (j + 1)) => hFr (F.points i).tower (F.points i).β j
      ((F.points i).sideAtLevel (j + 1)) (isTowerOnParameters_of_lt _ (hKi i)) (F.points i).isCutoff (F.points i).marksMeasurable
      (hforms _ j (by have := hKi i; omega)) hFx hbs m c
    have hH : Integrable (caseLift (F.points i).tower j _ (badOrSupportSiteCase j Z (F.points i)))
        (markedSampleLaw (F.points i).tower (F.points i).β (j + 1) ((F.points i).sideAtLevel (j + 1))) := by
      refine Integrable.of_bound (hBor i).aestronglyMeasurable 1 (ae_of_all _ fun x => ?_)
      show ‖(if _ then (1 : ℝ) else 0)‖ ≤ 1
      split_ifs <;> simp
    have hI0 : ∀ (y : TorusSite ((F.points i).sideAtLevel (j + 1) * Λ.stepParams.side)) x,
        0 ≤ ({u | ¬ StepAvoids (F.points i).tower j m (parentBlock Λ.stepParams.side y) u}.indicator (fun _ => (1 : ℝ))) x :=
      fun y x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have hc := condExp_le_sum_on hmF hs hH (Z (F.points i))
      (fun y => {u | ¬ StepAvoids (F.points i).tower j m (parentBlock Λ.stepParams.side y) u}.indicator (fun _ => (1 : ℝ)))
      (fun y _ => (integrable_const (1 : ℝ)).indicator (hfr _).1) (fun x => ?_) (fun _ => E)
      (fun y _ => ((hfr (parentBlock Λ.stepParams.side y)).2).mono fun x hx _ => hx.trans (hEb i _))
    · refine hc.mono fun x hx hxs => (hx hxs).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (hcard i) hE
    · by_cases hxs : x ∈ {x | Disjoint (stageState (F.points i).tower (j + 1) ((F.points i).sideAtLevel (j + 1)) x).2.1
          (supBall ((F.points i).originSite (j + 1) ((F.points i).sideAtLevel (j + 1))) (Rc : ℝ))}
      · rw [Set.indicator_of_mem hxs]
        show (if (((show Finset (TorusBond ((F.points i).sideAtLevel (j + 1) * Λ.stepParams.side)) from x.2.2.2).image Prod.fst ∪
          (stageState (F.points i).tower j _ x.1).2.1) ∩ Z (F.points i)).Nonempty then (1 : ℝ) else 0) ≤ _
        split_ifs with hne
        · obtain ⟨z, hz⟩ := hne
          obtain ⟨hz1, hz2⟩ := Finset.mem_inter.mp hz
          have hsm : ¬ StepAvoids (F.points i).tower j m (parentBlock Λ.stepParams.side z) x := fun hF => by
            have hYR : Disjoint (coarseHull ((F.points i).tower.stage j).toStepSetup.params.side
                ((F.points i).tower.stage j).toStepSetup.range ((F.points i).tower.stage j).toStepSetup.nextRange x.2.2.2
                (stageState (F.points i).tower j _ x.1).2.1 (hotCoreSites ((F.points i).tower.stage j).toStepSetup x.2.2.1))
                (supBall (parentBlock Λ.stepParams.side z) m) :=
              Finset.disjoint_of_subset_right (hbox i z hz2) hxs
            refine parentBlock_not_mem ((F.points i).tower.stage j).toStepSetup _ _ _ _ hYR hF (Finset.mem_union_left _ hz1) ?_
            simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and, supDist_self]
            simpa using hm
          have h1 := Finset.single_le_sum
            (f := fun y => ({u | ¬ StepAvoids (F.points i).tower j m (parentBlock Λ.stepParams.side y) u}.indicator (fun _ => (1 : ℝ))) x)
            (fun y _ => hI0 y x) hz2
          have h2 : ({u | ¬ StepAvoids (F.points i).tower j m (parentBlock Λ.stepParams.side z) u}.indicator (fun _ => (1 : ℝ))) x = 1 :=
            Set.indicator_of_mem hsm _
          simp only [h2] at h1
          exact h1
        · exact Finset.sum_nonneg fun y _ => hI0 y x
      · rw [Set.indicator_of_notMem hxs]
        exact Finset.sum_nonneg fun y _ => hI0 y x
end YangMills.Construction.MomentLaw
end
