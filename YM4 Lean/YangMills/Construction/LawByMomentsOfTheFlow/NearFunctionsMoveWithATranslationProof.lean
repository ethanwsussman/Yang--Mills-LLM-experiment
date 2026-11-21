import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import YangMills.Construction.LawByMomentsOfTheFlow.NearFunctionsMoveWithATranslation
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings WeightedResponses ResponseInTheExpansion ClusterExpansionOfAStep BlockAverages CellWindows
  BaseTranslations TopLevelSites TorusContours HullTrees RenormalizationStepParameters
namespace MomentLaw
section TranslateSets
variable {m : ℕ} [NeZero m]
private theorem mem_translateSet_iff {a z : TorusSite m} {Y : Finset (TorusSite m)} :
    z ∈ translateSet a Y ↔ z + a ∈ Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.mem_translateSet <;> assumption
private theorem translateSet_neg_translateSet (a : TorusSite m) (Y : Finset (TorusSite m)) :
    translateSet (-a) (translateSet a Y) = Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translateSet_neg_translateSet <;> assumption
private theorem supDist_add_add (a x y : TorusSite m) : supDist (x + a) (y + a) = supDist x y := by
  simp [supDist]
private theorem thickening_translateSet (k : ℕ) (a : TorusSite m) (X : Finset (TorusSite m)) :
    thickening k (translateSet a X) = translateSet a (thickening k X) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.thickening_translateSet <;> assumption
private theorem chainComponents_translateSet (r : ℕ) (a : TorusSite m) (Y : Finset (TorusSite m)) :
    chainComponents r (translateSet a Y) = (chainComponents r Y).image (translateSet a) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.chainComponents_translateSet <;> assumption
end TranslateSets
section BlockScaling
variable {n L : ℕ}
private abbrev scaleCoords (L : ℕ) (v : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (L : ℤ) * v i
private theorem exists_cast_add_intCast {m : ℕ} [NeZero m] (x : ZMod m) (z : ℤ) :
    ∃ k : ℤ, (((x + (z : ZMod m) : ZMod m)).cast : ℤ) = (x.cast : ℤ) + z + (m : ℤ) * k := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.exists_cast_add_intCast <;> assumption
private theorem parentBlock_add_siteOfInt [NeZero n] [NeZero L] (x : TorusSite (n * L)) (v : Fin 4 → ℤ) :
    parentBlock L (x + siteOfInt (scaleCoords L v)) = parentBlock L x + siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.parentBlock_add_scale <;> assumption
private theorem blockSite_add_siteOfInt [NeZero n] [NeZero L] (y : TorusSite n) (o : BlockOffset L)
    (v : Fin 4 → ℤ) :
    (blockSite (y + siteOfInt v) o : TorusSite (n * L)) = blockSite y o + siteOfInt (scaleCoords L v) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.blockSite_add <;> assumption
end BlockScaling
section HotLumps
variable {ℓ : StepParameters} {m : ℕ} [NeZero m]
private theorem translateSet_inter_nonempty_iff {m : ℕ} [NeZero m] (a : TorusSite m) (X Y : Finset (TorusSite m)) :
    (open Classical in (translateSet a X ∩ translateSet a Y).Nonempty) ↔ (open Classical in (X ∩ Y).Nonempty) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translateSet_inter_nonempty <;> assumption
private theorem curvature_translate_apply (a : TorusSite m) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    curvature (TorusFields.translate a W) x μ ν = curvature W (x + a) μ ν := by
  simp only [curvature, holonomy, TorusFields.translate, add_right_comm x a]
private theorem torusHotLumps_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ)
    (W : TorusField m) :
    torusHotLumps ℓ (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) W) =
      (torusHotLumps ℓ W).image (translateSet (siteOfInt (scaleCoords ℓ.side w))) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusHotLumps_translate <;> assumption
private theorem torusHotSites_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ)
    (W : TorusField m) :
    torusHotSites ℓ (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) W) =
      translateSet (siteOfInt (scaleCoords ℓ.side w)) (torusHotSites ℓ W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusHotSites_translate <;> assumption
private theorem isHullState_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (r : ℕ)
    {W : TorusField m} {Y : Finset (TorusSite m)} (h : IsHullState ℓ r W Y) :
    IsHullState ℓ r (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) W)
      (translateSet (siteOfInt (scaleCoords ℓ.side w)) Y) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.isHullState_translate <;> assumption
private theorem translate_neg_translate (a : TorusSite m) (W : TorusField m) :
    TorusFields.translate (-a) (TorusFields.translate a W) = W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translate_neg_translate <;> assumption
private theorem isHullState_translate_iff (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (r : ℕ)
    {W : TorusField m} {Y : Finset (TorusSite m)} :
    IsHullState ℓ r (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) W)
      (translateSet (siteOfInt (scaleCoords ℓ.side w)) Y) ↔ IsHullState ℓ r W Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.isHullState_translate_iff <;> assumption
end HotLumps
section CoarseStates
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def translateState (q : CoarseState R n) (a : TorusSite n) : CoarseState R n :=
  ⟨translateSet a q.1, translateLabel a q.1 q.2⟩
private theorem markAt_translateState (q : CoarseState R n) (a y : TorusSite n) :
    (translateState q a).markAt y = q.markAt (y + a) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.markAt_translateState <;> assumption
private theorem labelAt_translateState (q : CoarseState R n) (v : Fin 4 → ℤ) (z : TorusSite (n * R.params.side)) :
    (translateState q (siteOfInt v)).labelAt z = q.labelAt (z + siteOfInt (scaleCoords R.params.side v)) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.labelAt_translateState <;> assumption
end CoarseStates
section FrameSites
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
private theorem toTorusSite_fine_add (v : Fin 4 → ℤ)
    (x : (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth) :
    toTorusSite (n * ℓ.side)
        (x + siteOfCoords (F := stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth (scaleCoords ℓ.side v)) =
      toTorusSite (n * ℓ.side) x + siteOfInt (scaleCoords ℓ.side v) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.toTorusSite_add_fine <;> assumption
private theorem toTorusSite_coarse_add (v : Fin 4 → ℤ) (y : (stepBlockFrame ℓ.side n).Cell) :
    toTorusSite n (y + siteOfCoords (stepBlockFrame ℓ.side n).top v) = toTorusSite n y + siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.toTorusSite_add_coarse <;> assumption
private theorem toTorusSite_sub_add (v : Fin 4 → ℤ) (p : (stepBlockFrame ℓ.side n).Site 0) :
    toTorusSite (n * ℓ.side) (p - siteOfCoords (F := stepBlockFrame ℓ.side n) 0 (scaleCoords ℓ.side v)) +
        siteOfInt (scaleCoords ℓ.side v) = toTorusSite (n * ℓ.side) p :=
  (toTorusSite_fine_add (ℓ := ℓ) (n := n) v
      (p - siteOfCoords (F := stepBlockFrame ℓ.side n) 0 (scaleCoords ℓ.side v))).symm.trans
    (congrArg (toTorusSite (n * ℓ.side))
      (sub_add_cancel p (siteOfCoords (F := stepBlockFrame ℓ.side n) 0 (scaleCoords ℓ.side v))))
end FrameSites
section GaugeActions
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem labelSet_translateState (q : CoarseState R n) (v : Fin 4 → ℤ) :
    (translateState q (siteOfInt v)).labelSet = translateSet (siteOfInt (scaleCoords R.params.side v)) q.labelSet := by
  ext z
  rw [mem_translateSet_iff, mem_labelSet, mem_labelSet, labelAt_translateState]
private theorem labeling_translateState (q : CoarseState R n) (v : Fin 4 → ℤ) (z : TorusSite (n * R.params.side))
    (hz : z ∈ (translateState q (siteOfInt v)).labelSet)
    (hz' : z + siteOfInt (scaleCoords R.params.side v) ∈ q.labelSet) :
    (translateState q (siteOfInt v)).labeling ⟨z, hz⟩ =
      q.labeling ⟨z + siteOfInt (scaleCoords R.params.side v), hz'⟩ := by
  have e1 := labelAt_eq_inr_labeling (translateState q (siteOfInt v)) ⟨z, hz⟩
  have e2 := labelAt_eq_inr_labeling q ⟨_, hz'⟩
  simp only at e1 e2
  rw [labelAt_translateState, e2] at e1
  exact (Sum.inr_injective e1).symm
private def ActCommutesWithTranslation (Λ : LabelSpace) : Prop :=
  ∀ (m : ℕ) [NeZero m] (v : Fin 4 → ℤ) (Y : Finset (TorusSite m)) (g : TorusSite m → UnitQuaternion) (ω : Y → Λ.Ω),
    translateLabel (siteOfInt v) Y (Λ.act Y g ω) =
      Λ.act (translateSet (siteOfInt v) Y) (fun z => g (z + siteOfInt v)) (translateLabel (siteOfInt v) Y ω)
private theorem act_apply_translate {Λ : LabelSpace} (hΛ : ActCommutesWithTranslation Λ) {m : ℕ} [NeZero m]
    (v : Fin 4 → ℤ) (Y Y' : Finset (TorusSite m)) (hY : Y' = translateSet (siteOfInt v) Y)
    (g g' : TorusSite m → UnitQuaternion) (hg : ∀ z, g' z = g (z + siteOfInt v)) (ω : Y → Λ.Ω) (ω' : Y' → Λ.Ω)
    (hω : ∀ z (hz : z ∈ Y') (hz' : z + siteOfInt v ∈ Y), ω' ⟨z, hz⟩ = ω ⟨z + siteOfInt v, hz'⟩) (z : TorusSite m)
    (hz : z ∈ Y') (hz' : z + siteOfInt v ∈ Y) : Λ.act Y' g' ω' ⟨z, hz⟩ = Λ.act Y g ω ⟨z + siteOfInt v, hz'⟩ := by
  subst hY
  have e1 : g' = fun z => g (z + siteOfInt v) := funext hg
  have e2 : ω' = translateLabel (siteOfInt v) Y ω := funext fun x => hω x.1 x.2 (mem_translateSet_iff.mp x.2)
  subst e1
  subst e2
  exact (congrFun (hΛ m v Y g ω) ⟨z, hz⟩).symm
private theorem gaugeOnCoarseState_translateState (hΛ : ActCommutesWithTranslation R.labels) (q : CoarseState R n)
    (v : Fin 4 → ℤ) (g : TorusSite n → UnitQuaternion) (y : TorusSite n) (s : BlockLabels R.labels.Ω R.params.side) :
    gaugeOnCoarseState (translateState q (siteOfInt v)) (fun z => g (z + siteOfInt v)) y s =
      gaugeOnCoarseState q g (y + siteOfInt v) s := by
  classical
  have hl : ∀ x : TorusSite (n * R.params.side),
      TorusLumps.blockConstantGauge R.params.side (fun z => g (z + siteOfInt v)) x =
        TorusLumps.blockConstantGauge R.params.side g (x + siteOfInt (scaleCoords R.params.side v)) := by
    intro x
    simp only [TorusLumps.blockConstantGauge]
    rw [parentBlock_add_siteOfInt]
  simp only [gaugeOnCoarseState]
  congr 1
  · funext o
    have e : (blockSite (y + siteOfInt v) o : TorusSite (n * R.params.side)) =
        blockSite y o + siteOfInt (scaleCoords R.params.side v) := blockSite_add_siteOfInt y o v
    by_cases h : blockSite y o + siteOfInt (scaleCoords R.params.side v) ∈ q.labelSet
    · have h1 : blockSite y o ∈ (translateState q (siteOfInt v)).labelSet := by
        rw [labelSet_translateState]
        exact mem_translateSet_iff.mpr h
      have h2 : blockSite (y + siteOfInt v) o ∈ q.labelSet := by
        rw [e]
        exact h
      rw [dif_pos h1, dif_pos h2]
      have h3 := act_apply_translate hΛ (scaleCoords R.params.side v) q.labelSet
        (translateState q (siteOfInt v)).labelSet (labelSet_translateState q v)
        (TorusLumps.blockConstantGauge R.params.side g)
        (TorusLumps.blockConstantGauge R.params.side fun z => g (z + siteOfInt v)) hl q.labeling
        (translateState q (siteOfInt v)).labeling (fun z hz hz' => labeling_translateState q v z hz hz')
        (blockSite y o) h1 h
      rw [h3]
      congr 2
      exact Subtype.ext e.symm
    · have h1 : blockSite y o ∉ (translateState q (siteOfInt v)).labelSet := by
        rw [labelSet_translateState]
        exact fun e' => h (mem_translateSet_iff.mp e')
      have h2 : blockSite (y + siteOfInt v) o ∉ q.labelSet := by
        rw [e]
        exact h
      rw [dif_neg h1, dif_neg h2]
  · funext c
    have e : (blockSite (y + siteOfInt v) c.1 : TorusSite (n * R.params.side)) =
        blockSite y c.1 + siteOfInt (scaleCoords R.params.side v) := blockSite_add_siteOfInt y c.1 v
    rcases s.linkValue c with a | a
    · rfl
    · simp only
      rw [hl, hl, e, add_right_comm]
private theorem coarseLabelSpace_actCommutes (hΛ : ActCommutesWithTranslation R.labels) (h : CoarseLabelFacts R) :
    ActCommutesWithTranslation (coarseLabelSpace R h) := by
  intro m _ v Y g ω
  funext ⟨z, hz⟩
  have hz' : z + siteOfInt v ∈ Y := mem_translateSet_iff.mp hz
  show coarseGaugeAct (R := R) Y g ω ⟨z + siteOfInt v, hz'⟩ =
    coarseGaugeAct (R := R) (translateSet (siteOfInt v) Y) (fun z => g (z + siteOfInt v))
      (translateLabel (siteOfInt v) Y ω) ⟨z, hz⟩
  rcases hs : ω ⟨z + siteOfInt v, hz'⟩ with a | s
  · simp only [coarseGaugeAct, translateLabel, hs]
  · rw [coarseGaugeAct_of_inr hs,
      coarseGaugeAct_of_inr (ω := translateLabel (siteOfInt v) Y ω) (y := ⟨z, hz⟩) (s := s) hs]
    exact congrArg Sum.inr (gaugeOnCoarseState_translateState hΛ ⟨Y, ω⟩ v g z s).symm
end GaugeActions
private theorem stageTower_actCommutes {ℓ : StepParameters} (T : StageTower ℓ)
    (h : ∀ ω : T.base.labels.Ω, ω = T.basePoint) : ∀ t, ActCommutesWithTranslation (T.stage t).labels
  | 0 => fun _ _ _ _ _ _ => funext fun _ => (h _).trans (h _).symm
  | t + 1 => coarseLabelSpace_actCommutes (R := (T.stage t).toStepSetup) (stageTower_actCommutes T h t)
      (T.labelFacts _ T.two_le_side)
section NearlyLocal
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem mem_translateBonds_iff {m : ℕ} [NeZero m] {a : TorusSite m} {B : Finset (TorusBond m)}
    {c : TorusBond m} : c ∈ translateBonds a B ↔ (c.1 + a, c.2) ∈ B := by
  classical
  simp only [translateBonds, Finset.mem_image]
  constructor
  · rintro ⟨d, hd, rfl⟩
    simpa using hd
  · intro h
    exact ⟨_, h, by simp⟩
private theorem add_mem_supBall_add {m : ℕ} [NeZero m] {o x a : TorusSite m} {r : ℝ} (h : x ∈ supBall o r) :
    x + a ∈ supBall (o + a) r := by
  simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  rwa [supDist_add_add]
private theorem translate_gaugeTransform {m : ℕ} [NeZero m] (a : TorusSite m) (g : TorusSite m → UnitQuaternion)
    (W : TorusField m) : TorusFields.translate a (TorusFields.gaugeTransform g W) =
      TorusFields.gaugeTransform (fun z => g (z + a)) (TorusFields.translate a W) := by
  funext x i
  simp only [TorusFields.translate, TorusFields.gaugeTransform]
  rw [add_right_comm x a]
private theorem measurable_translate_pair (a : TorusSite (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) :
    Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
      (TorusFields.translate a p.1, translateLabel a Yt p.2) := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun i =>
      (measurable_pi_apply i).comp ((measurable_pi_apply (x + a)).comp measurable_fst)
  · exact measurable_pi_lambda _ fun z => (measurable_pi_apply _).comp measurable_snd
private theorem isNearlyLocal_translate (hfit : R.params.Admissible)
    (hrow : HullExpansion R.params R.depth R.coupling R.functional R.density R.labels R.labelWeight R.clusterFactor
      R.siteDensity)
    (hside : IsBlockTorusSide R.params (n * R.params.side)) (hΛ : ActCommutesWithTranslation R.labels)
    (w : Fin 4 → ℤ) (o : TorusSite (n * R.params.side)) (Rr : ℕ) (Sz : ℝ) (F : CaseFunction R n)
    (hF : IsNearlyLocalCaseFunction R o Rr Sz F) :
    IsNearlyLocalCaseFunction R (o + siteOfInt fun i => (R.params.side : ℤ) * ((R.params.side : ℤ) * w i)) Rr Sz
      (translateCaseFunction (fun i => (R.params.side : ℤ) * w i) F) := by
  set v : Fin 4 → ℤ := fun i => (R.params.side : ℤ) * w i with hv
  set A : TorusSite (n * R.params.side) := siteOfInt fun i => (R.params.side : ℤ) * v i with hA
  have hdvd : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
  have live : ∀ {W : TorusField (n * R.params.side)} {Y : Finset (TorusSite (n * R.params.side))}
      {ω : Y → R.labels.Ω}, IsLiveState R.params R.coupling R.labelWeight W Y ω →
      IsLiveState R.params R.coupling R.labelWeight (TorusFields.translate A W) (translateSet A Y) (translateLabel A Y ω) := by
    intro W Y ω h
    refine ⟨(isHullState_translate_iff hfit hdvd v (clusterRange R.coupling)).mpr h.1, ?_⟩
    rw [hrow.translation (n * R.params.side) hside W Y ω A ⟨v, rfl⟩ h.1]
    exact h.2
  refine ⟨fun W Yt ωt bad b => hF.abs_le _ _ _ _ _, fun Yt bad b => ?_, ?_, ?_⟩
  · exact (hF.measurable (translateSet A Yt) (translateBonds A bad) (translateBases v b)).comp
      (measurable_translate_pair A Yt)
  · intro W Yt ωt bad b g hl hb hc
    show F (TorusFields.translate A (TorusFields.gaugeTransform g W)) (translateSet A Yt)
        (translateLabel A Yt (R.labels.act Yt g ωt))
        (translateBonds A bad) (translateBases v b) =
      F (TorusFields.translate A W) (translateSet A Yt) (translateLabel A Yt ωt) (translateBonds A bad)
        (translateBases v b)
    rw [translate_gaugeTransform, hΛ (n * R.params.side) (fun i => (R.params.side : ℤ) * v i) Yt g ωt]
    refine hF.gaugeInvariant (TorusFields.translate A W) (translateSet A Yt) (translateLabel A Yt ωt) (translateBonds A bad)
      (translateBases v b) (fun z => g (z + A)) (live hl) (fun c => ?_) (fun y => ?_)
    · exact (congrArg g (toTorusSite_sub_add (ℓ := R.params) (n := n) v
        (b (c + siteOfCoords (stepBlockFrame R.params.side n).top v)))).trans (hb _)
    · show g (blockSite y _ + siteOfInt (scaleCoords R.params.side v)) = 1
      rw [← blockSite_add_siteOfInt]
      exact hc _
  · intro m hm W W' Yt Yt' ωt ωt' bad bad' b b' hl hl' h1 h2 h3
    refine hF.abs_sub_le m hm _ _ _ _ _ _ (translateBonds A bad) (translateBonds A bad') (translateBases v b)
      (translateBases v b') (live hl) (live hl') ?_ ?_ ?_
    · intro c hc1 hc2
      have h4 := h1 (c.1 + A, c.2) (add_mem_supBall_add hc1) (by
        have := add_mem_supBall_add (a := A) hc2
        simpa only [add_right_comm c.1] using this)
      exact ⟨h4.1, by rw [mem_translateBonds_iff, mem_translateBonds_iff]; exact h4.2⟩
    · intro x hx
      have h4 := h2 (x + A) (add_mem_supBall_add hx)
      exact ⟨by rw [mem_translateSet_iff, mem_translateSet_iff]; exact h4.1, fun hy hy' =>
        h4.2 (mem_translateSet_iff.mp hy) (mem_translateSet_iff.mp hy')⟩
    · intro c hc
      have e1 := toTorusSite_coarse_add (ℓ := R.params) (n := n) v c
      have e2 : parentBlock R.params.side (o + A) = parentBlock R.params.side o + siteOfInt v :=
        parentBlock_add_siteOfInt (L := R.params.side) o v
      have e3 := supDist_add_add (siteOfInt v) (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c)
        (parentBlock R.params.side o)
      have h4 := h3 (c + siteOfCoords (stepBlockFrame R.params.side n).top v) (by
        refine le_trans (le_of_eq ?_) hc
        exact congrArg (fun k : ℕ => (k : ℝ)) ((congrArg₂ supDist e1 e2).trans e3))
      exact congrArg (fun z => z - siteOfCoords (F := stepBlockFrame R.params.side n)
        (stepBlockFrame R.params.side n).depth fun i => (R.params.side : ℤ) * v i) h4
end NearlyLocal
theorem nearlyLocalTranslateStatement_proof : nearlyLocalTranslateStatement := by
  intro a ha
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, fun L hodd hLe Tb hTa hTL hDr hCold hHalf hrt hCder =>
    ⟨0, fun Kr hKc hη hN hfit hret =>
      ⟨Tb.floorMin, fun y hy hRet hWil g β K m T u n _ hA w o Rr Sz F hF => ?_⟩⟩⟩
  have hfits : (Tb.stepParameters y).Admissible := hDr.fits y hy
  have hL1 : 1 ≤ (Tb.stepParameters y).side := le_trans (by norm_num) T.two_le_side
  have hside : IsBlockTorusSide (Tb.stepParameters y) (n * (Tb.stepParameters y).side) := by
    refine ⟨Dvd.intro_left n rfl, ?_⟩
    have hvol : Tb.side * Tb.n₀ ≤ 2 * Tb.side ^ m := hA.chain.volume_le
    have hL1' : 1 ≤ Tb.side := hL1
    have h1 : Tb.n₀ ≤ Tb.side * Tb.n₀ := Nat.le_mul_of_pos_left _ hL1'
    have h2 : 2 * Tb.side ^ m ≤ n := by
      rw [hA.side_eq, torusSideAtLevel, fineSide_eq]
      exact Nat.le_mul_of_pos_right _ (Nat.pow_pos hL1')
    have h3 : (Tb.stepParameters y).n₀ ≤ n := h1.trans (hvol.trans h2)
    rw [mul_comm]
    exact Nat.mul_le_mul_right _ h3
  exact isNearlyLocal_translate (R := (T.stage u).toStepSetup) hfits
    (hA.chain.expansions u (Nat.le_of_succ_le hA.le)).2 hside
    (stageTower_actCommutes T hA.chain.reads_flow.startsAtWilson.eq_basePoint u) w o Rr Sz F hF
end MomentLaw
end YangMills.Construction
end
