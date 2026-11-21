import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import YangMills.Construction.CellOfTheFlow.TranslationsCarryTheMeansOfACellProof
import YangMills.Construction.LawByMomentsOfTheFlow.ScoresInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.TheChainMovesWithATranslation
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps StepSettings StepCosts RenormalizationStepParameters StepReturn StepMarks ColdChain BaseTranslations
  BlockAverages LumpContours TopLevelSites TorusContours HullTrees ChainNoise WeightedResponses ResponseInTheExpansion
  ClusterExpansionOfAStep StepFrames
open CellWindows (translateBonds translateOutcome)
namespace ChainTranslation
section Sets
variable {m : ℕ} [NeZero m]
private theorem mem_translateSet_iff {a z : TorusSite m} {Y : Finset (TorusSite m)} :
    z ∈ translateSet a Y ↔ z + a ∈ Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.mem_translateSet <;> assumption
private theorem thickening_translateSet (k : ℕ) (a : TorusSite m) (X : Finset (TorusSite m)) :
    thickening k (translateSet a X) = translateSet a (thickening k X) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.thickening_translateSet <;> assumption
private theorem chainComponents_translateSet (r : ℕ) (a : TorusSite m) (Y : Finset (TorusSite m)) :
    chainComponents r (translateSet a Y) = (chainComponents r Y).image (translateSet a) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.chainComponents_translateSet <;> assumption
private def translateBondSet (a : TorusSite m) (B : Finset (TorusBond m)) : Finset (TorusBond m) :=
  open Classical in Finset.univ.filter fun c => (c.1 + a, c.2) ∈ B
private theorem mem_translateBondSet {a : TorusSite m} {B : Finset (TorusBond m)} {c : TorusBond m} :
    c ∈ translateBondSet a B ↔ (c.1 + a, c.2) ∈ B := by
  classical
  simp [translateBondSet]
private theorem image_fst_translateBondSet (a : TorusSite m) (B : Finset (TorusBond m)) :
    (open Classical in (translateBondSet a B).image Prod.fst) =
      translateSet a (open Classical in B.image Prod.fst) := by
  classical
  ext z
  simp only [Finset.mem_image, mem_translateSet_iff, mem_translateBondSet]
  constructor
  · rintro ⟨⟨x, i⟩, h, rfl⟩
    exact ⟨_, h, rfl⟩
  · rintro ⟨⟨x, i⟩, h, e⟩
    simp only at e
    exact ⟨(z, i), by simpa [← e] using h, rfl⟩
end Sets
section Lift
variable {n L : ℕ}
private abbrev scaleCoords (L : ℕ) (v : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (L : ℤ) * v i
private theorem exists_cast_add_intCast {m : ℕ} [NeZero m] (x : ZMod m) (z : ℤ) :
    ∃ k : ℤ, (((x + (z : ZMod m) : ZMod m)).cast : ℤ) = (x.cast : ℤ) + z + (m : ℤ) * k := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.exists_cast_add_intCast <;> assumption
private theorem parentBlock_add_scale [NeZero n] [NeZero L] (x : TorusSite (n * L)) (v : Fin 4 → ℤ) :
    parentBlock L (x + siteOfInt (scaleCoords L v)) = parentBlock L x + siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.parentBlock_add_scale <;> assumption
private theorem blockSite_add [NeZero n] [NeZero L] (y : TorusSite n) (o : BlockOffset L) (v : Fin 4 → ℤ) :
    (blockSite (y + siteOfInt v) o : TorusSite (n * L)) = blockSite y o + siteOfInt (scaleCoords L v) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.blockSite_add <;> assumption
private theorem siteOfInt_scaleCoords_neg (v : Fin 4 → ℤ) :
    (siteOfInt (scaleCoords L (-v)) : TorusSite (n * L)) = - siteOfInt (scaleCoords L v) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.siteOfInt_scaleCoords_neg <;> assumption
private theorem siteOfInt_neg {m : ℕ} (v : Fin 4 → ℤ) : (siteOfInt (-v) : TorusSite m) = - siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.siteOfInt_neg <;> assumption
end Lift
section Clusters
variable {n L : ℕ} [NeZero n] [NeZero L]
private theorem mem_sitesInBlocks_iff {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.mem_sitesInBlocks <;> assumption
private theorem sitesInBlocks_translateSet (v : Fin 4 → ℤ) (S : Finset (TorusSite n)) :
    sitesInBlocks L (translateSet (siteOfInt v) S) =
      translateSet (siteOfInt (scaleCoords L v)) (sitesInBlocks L S) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.sitesInBlocks_translateSet <;> assumption
private theorem translateSet_inter_nonempty {m : ℕ} [NeZero m] (a : TorusSite m) (X Y : Finset (TorusSite m)) :
    (open Classical in (translateSet a X ∩ translateSet a Y).Nonempty) ↔
      (open Classical in (X ∩ Y).Nonempty) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translateSet_inter_nonempty <;> assumption
variable (r r' : ℕ) (v : Fin 4 → ℤ) (bad : Finset (TorusBond (n * L))) (Yt : Finset (TorusSite (n * L)))
  (C : Finset (TorusSite n))
private theorem clusterComponents_translate :
    clusterComponents L r (translateBondSet (siteOfInt (scaleCoords L v)) bad)
        (translateSet (siteOfInt (scaleCoords L v)) Yt) (translateSet (siteOfInt v) C) =
      (clusterComponents L r bad Yt C).image (translateSet (siteOfInt (scaleCoords L v))) := by
  classical
  unfold clusterComponents
  rw [← chainComponents_translateSet]
  congr 1
  rw [image_fst_translateBondSet, sitesInBlocks_translateSet]
  ext z
  simp [mem_translateSet_iff]
private theorem attachedSites_translate :
    attachedSites L r (translateBondSet (siteOfInt (scaleCoords L v)) bad)
        (translateSet (siteOfInt (scaleCoords L v)) Yt) (translateSet (siteOfInt v) C) =
      translateSet (siteOfInt (scaleCoords L v)) (attachedSites L r bad Yt C) := by
  classical
  ext z
  rw [mem_translateSet_iff]
  simp only [attachedSites, Finset.mem_biUnion, Finset.mem_filter, id, clusterComponents_translate,
    Finset.mem_image]
  constructor
  · rintro ⟨X', ⟨⟨X, hX, rfl⟩, hn⟩, hz⟩
    rw [sitesInBlocks_translateSet] at hn
    exact ⟨X, ⟨hX, (translateSet_inter_nonempty _ _ _).mp (by convert hn)⟩, mem_translateSet_iff.mp hz⟩
  · rintro ⟨X, ⟨hX, hn⟩, hz⟩
    refine ⟨_, ⟨⟨X, hX, rfl⟩, ?_⟩, mem_translateSet_iff.mpr hz⟩
    rw [sitesInBlocks_translateSet]
    convert (translateSet_inter_nonempty (siteOfInt (scaleCoords L v)) X (sitesInBlocks L C)).mpr
      (by convert hn)
private theorem coreBlocks_translate (θ : Finset (TorusSite (n * L))) :
    coreBlocks L r (translateSet (siteOfInt (scaleCoords L v)) θ) =
      translateSet (siteOfInt v) (coreBlocks L r θ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.coreBlocks_translateSet <;> assumption
private theorem storedBlocks_translate :
    storedBlocks L r (translateBondSet (siteOfInt (scaleCoords L v)) bad)
        (translateSet (siteOfInt (scaleCoords L v)) Yt) (translateSet (siteOfInt v) C) =
      translateSet (siteOfInt v) (storedBlocks L r bad Yt C) := by
  classical
  unfold storedBlocks
  rw [attachedSites_translate, coreBlocks_translate]
  ext z
  simp [mem_translateSet_iff]
private theorem coarseHull_translate :
    coarseHull L r r' (translateBondSet (siteOfInt (scaleCoords L v)) bad)
        (translateSet (siteOfInt (scaleCoords L v)) Yt) (translateSet (siteOfInt v) C) =
      translateSet (siteOfInt v) (coarseHull L r r' bad Yt C) := by
  unfold coarseHull
  rw [storedBlocks_translate, thickening_translateSet]
end Clusters
section Hot
variable {ℓ : StepParameters} {m : ℕ} [NeZero m]
private theorem curvature_translate_apply (a : TorusSite m) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    curvature (TorusFields.translate a W) x μ ν = curvature W (x + a) μ ν := by
  simp only [curvature, holonomy, TorusFields.translate, add_right_comm x a]
private theorem mem_plaquetteVertices_add (a : TorusSite m) (x z : TorusSite m) (μ ν : Fin 4) :
    z ∈ plaquetteVertices x μ ν ↔ z + a ∈ plaquetteVertices (x + a) μ ν := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.mem_plaquetteVertices_add <;> assumption
private theorem translateSet_torusLumpOf (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ)
    (z : TorusSite m) :
    translateSet (siteOfInt (scaleCoords ℓ.side w)) (torusLumpOf ℓ (z + siteOfInt (scaleCoords ℓ.side w))) =
      torusLumpOf ℓ z := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translateSet_torusLumpOf <;> assumption
private theorem torusHotLumps_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ)
    (W : TorusField m) :
    torusHotLumps ℓ (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) W) =
      (torusHotLumps ℓ W).image (translateSet (siteOfInt (scaleCoords ℓ.side w))) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusHotLumps_translate <;> assumption
private theorem torusHotSites_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ)
    (W : TorusField m) :
    torusHotSites ℓ (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) W) =
      translateSet (siteOfInt (scaleCoords ℓ.side w)) (torusHotSites ℓ W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusHotSites_translate <;> assumption
private theorem translate_neg_translate (a : TorusSite m) (W : TorusField m) :
    TorusFields.translate (-a) (TorusFields.translate a W) = W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translate_neg_translate <;> assumption
end Hot
section States
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def translateState (q : CoarseState R n) (a : TorusSite n) : CoarseState R n :=
  ⟨translateSet a q.1, translateLabel a q.1 q.2⟩
private theorem coarseState_ext (q q' : CoarseState R n) (h1 : q.1 = q'.1)
    (h2 : ∀ y, q.markAt y = q'.markAt y) : q = q' := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coarseState_ext <;> assumption
private theorem markAt_translateState (q : CoarseState R n) (a y : TorusSite n) :
    (translateState q a).markAt y = q.markAt (y + a) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.markAt_translateState <;> assumption
end States
section Chart
variable {F : BlockFrame} (u : Fin 4 → ℤ)
private def fineTranslation : F.Site F.depth := siteOfCoords F.depth fun i => (F.blockSide : ℤ) * u i
private def translateFine (X : F.GaugeField F.depth) : F.GaugeField F.depth :=
  fun x i => X (x + fineTranslation u) i
private def translateCoarse (U : F.GaugeField F.top) : F.GaugeField F.top :=
  fun y i => U (y + siteOfCoords F.top u) i
private theorem pathHolonomy_translateFine (X : F.GaugeField F.depth) (x : F.Site F.depth) (l : List PathStep) :
    pathHolonomy (translateFine u X) x l = pathHolonomy X (x + fineTranslation u) l := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.pathHolonomy_translateFine <;> assumption
private theorem enclosingCell_translate (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (x : F.Site F.depth) :
    enclosingCell (x + fineTranslation u) = enclosingCell x + siteOfCoords F.top u := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.enclosingCell_add_translation <;> assumption
private theorem axialGauge_translate (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (π : Equiv.Perm (Fin 4)) (X : F.GaugeField F.depth) (x : F.Site F.depth) :
    axialGauge π (translateFine u X) x = axialGauge π X (x + fineTranslation u) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.axialGauge_translateFine <;> assumption
private theorem bondCoordinate_translate (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (π : Equiv.Perm (Fin 4)) (U : F.GaugeField F.top) (X : F.GaugeField F.depth)
    (x : F.Site F.depth) (i : Fin 4) :
    bondCoordinate π (translateCoarse u U) (translateFine u X) (x, i) =
      bondCoordinate π U X (x + fineTranslation u, i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.bondCoordinate_translate <;> assumption
end Chart
section Step
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
private theorem torusSiteInFrame_add_scale (v : Fin 4 → ℤ) (x : TorusSite (n * ℓ.side)) :
    torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth (x + siteOfInt (scaleCoords ℓ.side v)) =
      torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth x +
        fineTranslation (F := stepBlockFrame ℓ.side n) v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusSiteInFrame_add_scale <;> assumption
private theorem toTorusSite_fine_add (v : Fin 4 → ℤ)
    (x : (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth) :
    toTorusSite (n * ℓ.side) (x + fineTranslation (F := stepBlockFrame ℓ.side n) v) =
      toTorusSite (n * ℓ.side) x + siteOfInt (scaleCoords ℓ.side v) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.toTorusSite_add_fine <;> assumption
private theorem toTorusSite_coarse_add (v : Fin 4 → ℤ) (y : (stepBlockFrame ℓ.side n).Cell) :
    toTorusSite n (y + siteOfCoords (stepBlockFrame ℓ.side n).top v) = toTorusSite n y + siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.toTorusSite_add_coarse <;> assumption
private theorem stepBlockFrame_extent_ge (hn : 2 ≤ n) : ∀ i, 2 ≤ (stepBlockFrame ℓ.side n).extent i :=
  fun _ => hn
private theorem chartCoord_translate (hL : Odd ℓ.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (x : TorusSite (n * ℓ.side)) (i : Fin 4) :
    chartCoord ℓ (TorusFields.translate (siteOfInt v) V)
      (TorusFields.translate (siteOfInt (scaleCoords ℓ.side v)) W) (x, i) =
      chartCoord ℓ V W (x + siteOfInt (scaleCoords ℓ.side v), i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.chartCoord_translate <;> assumption
private theorem mem_chartBonds_translate (hL : Odd ℓ.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ)
    (x : TorusSite (n * ℓ.side)) (i : Fin 4) :
    (x + siteOfInt (scaleCoords ℓ.side v), i) ∈ chartBonds ℓ.side n ↔ (x, i) ∈ chartBonds ℓ.side n := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.add_mem_chartBonds_iff <;> assumption
end Step
section StatesOfCases
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem baseOffset_translateBases (v : Fin 4 → ℤ) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    baseOffset R (translateBases v b) y = baseOffset R b (y + siteOfInt v) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.baseOffset_translateBases <;> assumption
private theorem blockConfigAt_translate (v : Fin 4 → ℤ) (C Z : Finset (TorusSite n))
    (F : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    blockConfigAt R (translateSet (siteOfInt v) C) (translateSet (siteOfInt v) Z)
        (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) F)
        (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt)
        (translateLabel (siteOfInt (scaleCoords R.params.side v)) Yt ωt)
        (translateBondSet (siteOfInt (scaleCoords R.params.side v)) bad) (translateBases v b) y =
      blockConfigAt R C Z F Yt ωt bad b (y + siteOfInt v) := by
  classical
  refine blockConfig_ext ?_ ?_ ?_ ?_ ?_
  · simp only [blockConfigAt, mem_translateSet_iff]
  · funext c
    simp only [blockConfigAt, mem_translateBondSet, blockSite_add]
  · funext o
    simp only [blockConfigAt]
    by_cases h : blockSite (y + siteOfInt v) o ∈ Yt
    · have h' : blockSite y o ∈ translateSet (siteOfInt (scaleCoords R.params.side v)) Yt := by
        rw [mem_translateSet_iff, ← blockSite_add]
        exact h
      rw [dif_pos h, dif_pos h']
      simp only [translateLabel, Sum.inr.injEq]
      congr 2
      exact (blockSite_add y o v).symm
    · have h' : blockSite y o ∉ translateSet (siteOfInt (scaleCoords R.params.side v)) Yt := by
        rw [mem_translateSet_iff, ← blockSite_add]
        exact h
      rw [dif_neg h, dif_neg h']
  · exact baseOffset_translateBases v b y
  · funext c
    have e : parentBlock R.params.side (blockSite (L := R.params.side) y c.1 +
          TorusFields.unitStep (n * R.params.side) c.2) + siteOfInt v =
        parentBlock R.params.side (blockSite (L := R.params.side) (y + siteOfInt v) c.1 +
          TorusFields.unitStep (n * R.params.side) c.2) := by
      rw [blockSite_add, add_right_comm, parentBlock_add_scale]
    simp only [blockConfigAt, mem_translateSet_iff, e, TorusFields.translate, blockSite_add]
private theorem markAt_coarseStateOf (C : Finset (TorusSite n)) (F : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    (coarseStateOf R C F Yt ωt bad b).markAt y = open Classical in
      if y ∈ storedBlocks R.params.side R.range bad Yt C then
        some (blockConfigAt R C (storedBlocks R.params.side R.range bad Yt C) F Yt ωt bad b y) else none := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.markAt_coarseStateOf <;> assumption
private theorem coarseStateOf_translate (v : Fin 4 → ℤ) (C : Finset (TorusSite n))
    (F : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    coarseStateOf R (translateSet (siteOfInt v) C)
      (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) F)
        (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt)
        (translateLabel (siteOfInt (scaleCoords R.params.side v)) Yt ωt)
        (translateBondSet (siteOfInt (scaleCoords R.params.side v)) bad) (translateBases v b) =
      translateState (coarseStateOf R C F Yt ωt bad b) (siteOfInt v) := by
  classical
  refine coarseState_ext _ _ (coarseHull_translate R.range R.nextRange v bad Yt C) fun y => ?_
  rw [markAt_translateState, markAt_coarseStateOf, markAt_coarseStateOf, storedBlocks_translate]
  by_cases hy : y + siteOfInt v ∈ storedBlocks R.params.side R.range bad Yt C
  · have hy' : y ∈ translateSet (siteOfInt v) (storedBlocks R.params.side R.range bad Yt C) :=
      mem_translateSet_iff.mpr hy
    rw [if_pos hy, if_pos hy', blockConfigAt_translate]
  · have hy' : y ∉ translateSet (siteOfInt v) (storedBlocks R.params.side R.range bad Yt C) :=
      fun h => hy (mem_translateSet_iff.mp h)
    rw [if_neg hy, if_neg hy']
end StatesOfCases
section Moves
variable {ℓ : StepParameters}
private theorem stepOutcome_field_translate (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T)
    (s n : ℕ) [NeZero n] (v : Fin 4 → ℤ) (W : TorusField (n * ℓ.side)) (U : StepNoise ℓ n) :
    (rule.stepOutcome T s n (TorusFields.translate (siteOfInt (scaleCoords ℓ.side v)) W)
        (fun y => U.1 (y + siteOfInt v), fun c => U.2.1 (c.1 + siteOfInt v, c.2),
          fun b => U.2.2 (b.1 + siteOfInt (scaleCoords ℓ.side v), b.2))).2.1 =
      TorusFields.translate (siteOfInt v) (rule.stepOutcome T s n W U).2.1 := by apply _root_.YangMills.DeltaSharedProofs.p501493 <;> assumption
private theorem mem_stepOutcome_bad (rule : NoiseRule ℓ) (T : StageTower ℓ) (s n : ℕ) [NeZero n]
    (W : TorusField (n * ℓ.side)) (U : StepNoise ℓ n) (b : TorusBond (n * ℓ.side)) :
    b ∈ (show Finset (TorusBond (n * ℓ.side)) from (rule.stepOutcome T s n W U).2.2) ↔
      b ∈ markedBonds (T.stage s).toStepSetup
          (hotCoreSites (T.stage s).toStepSetup (rule.stepOutcome T s n W U).2.1) ∧
        ¬ ((U.2.2 b : ℝ) < bondMark (T.stage s).toStepSetup (rule.stepOutcome T s n W U).2.1 W b) :=
  Finset.mem_filter
private theorem mem_markedBonds_translate (R : StepSetup) {n : ℕ} [NeZero n] (hL : Odd R.params.side)
    (hn : 2 ≤ n) (v : Fin 4 → ℤ) (C : Finset (TorusSite n)) (x : TorusSite (n * R.params.side)) (i : Fin 4) :
    (x, i) ∈ markedBonds R (translateSet (siteOfInt v) C) ↔
      (x + siteOfInt (scaleCoords R.params.side v), i) ∈ markedBonds R C := by
  classical
  simp only [markedBonds, Finset.mem_filter, mem_translateSet_iff]
  rw [mem_chartBonds_translate hL hn, parentBlock_add_scale]
abbrev _root_.YangMills.DeltaSharedProofs.p502462 := @mem_markedBonds_translate
private theorem bondMark_translate (R : StepSetup) {n : ℕ} [NeZero n] (hL : Odd R.params.side) (hn : 2 ≤ n)
    (v : Fin 4 → ℤ) (V : TorusField n) (W : TorusField (n * R.params.side)) (x : TorusSite (n * R.params.side))
    (i : Fin 4)
    (h : frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt v) V) (x, i) =
      frameCoord R.params R.anchorRadius R.depth R.frameReach V (x + siteOfInt (scaleCoords R.params.side v), i)) :
    bondMark R (TorusFields.translate (siteOfInt v) V)
      (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) W) (x, i) =
      bondMark R V W (x + siteOfInt (scaleCoords R.params.side v), i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.bondMark_translate <;> assumption
private theorem mem_stepOutcome_bad_translate (hfit : ℓ.Admissible) (rule : NoiseRule ℓ) (T : StageTower ℓ)
    (hr : rule.IsAdmissible T) (s n : ℕ) [NeZero n] (hB : IsBlockTorusSide ℓ n) (w : Fin 4 → ℤ)
    (hfr : ∀ V : TorusField n, ∀ c ∈ markedBonds (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V),
      frameCoord ℓ (T.stage s).anchorRadius (T.stage s).depth (T.stage s).toStepSetup.frameReach
        (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) V)
        (c.1 - siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w)), c.2) =
      frameCoord ℓ (T.stage s).anchorRadius (T.stage s).depth (T.stage s).toStepSetup.frameReach V c)
    (W : TorusField (n * ℓ.side)) (U : StepNoise ℓ n) (x : TorusSite (n * ℓ.side)) (i : Fin 4) :
    (x, i) ∈ (show Finset (TorusBond (n * ℓ.side)) from (rule.stepOutcome T s n
        (TorusFields.translate (siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w))) W)
        (fun y => U.1 (y + siteOfInt (scaleCoords ℓ.side w)),
          fun c => U.2.1 (c.1 + siteOfInt (scaleCoords ℓ.side w), c.2),
          fun b => U.2.2 (b.1 + siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w)), b.2))).2.2) ↔
      (x + siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w)), i) ∈
        (show Finset (TorusBond (n * ℓ.side)) from (rule.stepOutcome T s n W U).2.2) := by
  classical
  have hn2 : 2 ≤ n := by
    have h1 := hB.2
    have h2 := hfit.L_ge
    have h3 := hfit.n₀_ge
    nlinarith
  rw [mem_stepOutcome_bad, mem_stepOutcome_bad,
    stepOutcome_field_translate rule T hr s n (scaleCoords ℓ.side w) W U]
  generalize hV : (rule.stepOutcome T s n W U).2.1 = V
  have hhull : hotCoreSites (T.stage s).toStepSetup (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) V) =
      translateSet (siteOfInt (scaleCoords ℓ.side w)) (hotCoreSites (T.stage s).toStepSetup V) := by
    show thickening _ (torusHotSites ℓ (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) V)) =
      translateSet _ (thickening _ (torusHotSites ℓ V))
    rw [torusHotSites_translate hfit hB.1, thickening_translateSet]
  rw [hhull]
  have hmb := mem_markedBonds_translate (T.stage s).toStepSetup hfit.L_odd hn2 (scaleCoords ℓ.side w)
    (hotCoreSites (T.stage s).toStepSetup V) x i
  have key : (x + siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w)), i) ∈
        markedBonds (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V) →
      bondMark (T.stage s).toStepSetup (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) V)
          (TorusFields.translate (siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w))) W) (x, i) =
        bondMark (T.stage s).toStepSetup V W (x + siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w)), i) := by
    intro hc
    have h := hfr V _ hc
    simp only [add_sub_cancel_right] at h
    exact bondMark_translate (T.stage s).toStepSetup hfit.L_odd hn2 (scaleCoords ℓ.side w) V W x i h
  constructor
  · rintro ⟨h1, h2⟩
    have hc := hmb.mp h1
    refine ⟨hc, fun h => h2 ?_⟩
    show ((U.2.2 (x + siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w)), i) : ℝ) <
      bondMark (T.stage s).toStepSetup (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) V)
        (TorusFields.translate (siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w))) W) (x, i))
    rw [key hc]
    exact h
  · rintro ⟨h1, h2⟩
    refine ⟨hmb.mpr h1, fun h => h2 ?_⟩
    have h' : ((U.2.2 (x + siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w)), i) : ℝ) <
      bondMark (T.stage s).toStepSetup (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) V)
        (TorusFields.translate (siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w))) W) (x, i)) := h
    rw [key h1] at h'
    exact h'
abbrev _root_.YangMills.DeltaSharedProofs.p983 := @mem_stepOutcome_bad_translate
end Moves
section ScaleFlow
variable {ℓ : StepParameters}
private theorem next_of_expansionReturns (hret : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ} {D : TorusFunctional}
    (hy : ℓ.y₁ ≤ x) (hD : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem flow_bounds {Tb : ParameterAssignment} {y g β : ℝ} {K : ℕ} (hB : 0 ≤ Tb.B)
    (hret : ExpansionReturnsAt (Tb.stepParameters y))
    (h0 : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β))
    (hp : FlowCrossing Tb y g β K) :
    ∀ j ≤ K, y ≤ (couplingFlow (Tb.stepParameters y) β j).1 ∧
      HasExpansion (Tb.stepParameters y) j (couplingFlow (Tb.stepParameters y) β j).1
        (couplingFlow (Tb.stepParameters y) β j).2 ∧
      (j < K → |(couplingFlow (Tb.stepParameters y) β (j + 1)).1 -
        (couplingFlow (Tb.stepParameters y) β j).1| ≤ 2 * Tb.B) := by
  have hnext : ∀ j, y ≤ (couplingFlow (Tb.stepParameters y) β j).1 →
      HasExpansion (Tb.stepParameters y) j (couplingFlow (Tb.stepParameters y) β j).1
        (couplingFlow (Tb.stepParameters y) β j).2 →
      HasExpansion (Tb.stepParameters y) (j + 1) (couplingFlow (Tb.stepParameters y) β (j + 1)).1
          (couplingFlow (Tb.stepParameters y) β (j + 1)).2 ∧
        |(couplingFlow (Tb.stepParameters y) β (j + 1)).1 - (couplingFlow (Tb.stepParameters y) β j).1| ≤
          2 * Tb.B :=
    fun j h1 h2 => next_of_expansionReturns hret h1 h2
  have hfloor : y ≤ windowUpper (Tb.stepParameters y) g - 2 * Tb.B := by
    have := hp.le_inv_sq
    show y ≤ (g ^ 2)⁻¹ + 2 * Tb.B - 2 * Tb.B
    linarith
  have hbelow : ∀ j ≤ K, y ≤ (couplingFlow (Tb.stepParameters y) β j).1 ∧
      HasExpansion (Tb.stepParameters y) j (couplingFlow (Tb.stepParameters y) β j).1
        (couplingFlow (Tb.stepParameters y) β j).2 := by
    intro j
    induction j with
    | zero =>
      intro _
      have hb : y ≤ β := by
        have := hp.upper_le
        linarith
      exact ⟨hb, h0 β hb⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      obtain ⟨h3, h4⟩ := hnext j h1 h2
      refine ⟨?_, h3⟩
      have h5 := hp.isFirst.2 j (by omega)
      have h6 := (abs_le.mp h4).1
      linarith
  intro j hj
  obtain ⟨h1, h2⟩ := hbelow j hj
  exact ⟨h1, h2, fun _ => (hnext j h1 h2).2⟩
abbrev _root_.YangMills.SharedProofs.p36592 := @flow_bounds
private theorem clusterRange_mono {x x' : ℝ} (h0 : 0 ≤ x) (h : x ≤ x') : clusterRange x ≤ clusterRange x' := by apply _root_.YangMills.Construction.WilsonExpansion.clusterRange_mono <;> assumption
private theorem clusterRange_le_succ {x x' b : ℝ} (hb : 0 ≤ b) (h1 : 1 ≤ x') (h2 : (2 * b) ^ 2 ≤ x')
    (hx : 0 ≤ x) (h : x ≤ x' + 2 * b) : clusterRange x ≤ clusterRange x' + 1 := by
  set a : ℝ := x' ^ ((1 : ℝ) / 100) with ha
  have ha1 : 1 ≤ a := Real.one_le_rpow h1 (by norm_num)
  have hpow : a ^ 100 = x' := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have h50 : 2 * b ≤ a ^ 50 := by
    have e : (a ^ 50) ^ 2 = x' := by rw [← pow_mul, hpow]
    have hp : 0 ≤ a ^ 50 := by positivity
    nlinarith [h2, e, hp, sq_nonneg (a ^ 50 - 2 * b)]
  have h99 : a ^ 50 ≤ a ^ 99 := pow_le_pow_right₀ ha1 (by norm_num)
  have hle : x ≤ (a + 1) ^ 100 := by
    have e2 : a ^ 99 ≤ (a + 1) ^ 99 := pow_le_pow_left₀ (by linarith) (by linarith) 99
    have e3 : a ^ 100 = a * a ^ 99 := by ring
    have e4 : (a + 1) * a ^ 99 ≤ (a + 1) * (a + 1) ^ 99 := mul_le_mul_of_nonneg_left e2 (by linarith)
    nlinarith
  have hroot : x ^ ((1 : ℝ) / 100) ≤ a + 1 := by
    have := Real.rpow_le_rpow hx hle (by norm_num : (0 : ℝ) ≤ 1 / 100)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), show (((100 : ℕ) : ℝ) * (1 / 100)) = 1 by norm_num,
      Real.rpow_one] at this
  calc clusterRange x ≤ ⌈a + 1⌉₊ := Nat.ceil_mono hroot
    _ ≤ clusterRange x' + 1 := by
      rw [Nat.ceil_add_one (by linarith)]
      rfl
abbrev _root_.YangMills.SharedProofs.p16909 := @clusterRange_le_succ
private theorem stage_anchorRadius {ℓ : StepParameters} (T : StageTower ℓ) :
    ∀ j, (T.stage j).anchorRadius = T.base.anchorRadius := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => exact ih
abbrev _root_.YangMills.SharedProofs.p36710 := @stage_anchorRadius
private theorem isBlockTorusSide_of_level {Tb : ParameterAssignment} {y g β : ℝ} {K m : ℕ}
    {T : StageTower (Tb.stepParameters y)} {u n : ℕ}
    (hD : Tb.Admissible) (hlev : HullChainAtLevel Tb y g β K m T u n) :
    IsBlockTorusSide (Tb.stepParameters y) n := by
  have hv : Tb.side * Tb.n₀ ≤ 2 * Tb.side ^ m := hlev.chain.volume_le
  have hL : 2 ^ 40 ≤ Tb.side := hD.L_ge
  have hn0 : 4096 ≤ Tb.n₀ := hD.n₀_ge
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp only [pow_zero, mul_one] at hv
      nlinarith
    · exact h
  have hside : n = 2 * Tb.side ^ m * Tb.side ^ (K - u) := by
    rw [hlev.side_eq]
    exact fineSide_eq _ _ _
  show Tb.side ∣ n ∧ Tb.side * Tb.n₀ ≤ n
  refine ⟨?_, ?_⟩
  · rw [hside]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _) _
  · rw [hside]
    exact le_trans hv (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
abbrev _root_.YangMills.SharedProofs.p59774 := @isBlockTorusSide_of_level
end ScaleFlow
section Draws
variable {ℓ : StepParameters}
private theorem translateBonds_eq {m : ℕ} [NeZero m] (a : TorusSite m) (B : Finset (TorusBond m)) :
    translateBonds a B = translateBondSet a B := by
  classical
  ext ⟨x, i⟩
  rw [mem_translateBondSet]
  unfold translateBonds
  simp only [Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨y, j⟩, hc, h1, h2⟩
    simp only at h1 h2
    subst h2
    have : x + a = y := by rw [← h1]; abel
    rwa [this]
  · intro h
    exact ⟨(x + a, i), h, by simp, rfl⟩
private theorem coarseStateOf_translateBonds {R : StepSetup} {n : ℕ} [NeZero n] (v : Fin 4 → ℤ)
    (C : Finset (TorusSite n)) (F : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
    (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    coarseStateOf R (translateSet (siteOfInt v) C)
      (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) F)
        (translateSet (siteOfInt (scaleCoords R.params.side v)) Yt)
        (translateLabel (siteOfInt (scaleCoords R.params.side v)) Yt ωt)
        (translateBonds (siteOfInt (scaleCoords R.params.side v)) bad) (translateBases v b) =
      translateState (coarseStateOf R C F Yt ωt bad b) (siteOfInt v) := by
  rw [translateBonds_eq]
  exact coarseStateOf_translate v C F Yt ωt bad b
private theorem topField_translateSample (s n : ℕ) [NeZero n] (v : Fin 4 → ℤ) (u : MarkedSample ℓ s n) :
    topField ℓ s n (translateSample s n v u) =
      TorusFields.translate (siteOfInt v) (topField ℓ s n u) := by
  cases s <;> rfl
private theorem baseChoiceOfOffsets_translate {n : ℕ} [NeZero n] (v : Fin 4 → ℤ)
    (o : TorusSite n → BlockOffset ℓ.side) :
    baseChoiceOfOffsets (ℓ := ℓ) (fun y => o (y + siteOfInt v)) =
      translateBases v (baseChoiceOfOffsets (ℓ := ℓ) o) := by apply _root_.YangMills.SharedProofs.p71065 <;> assumption
private theorem stepOutcome_translate (hfit : ℓ.Admissible) (rule : NoiseRule ℓ) (T : StageTower ℓ)
    (hr : rule.IsAdmissible T) (s n : ℕ) [NeZero n] (hB : IsBlockTorusSide ℓ n) (w : Fin 4 → ℤ)
    (hfr : ∀ V : TorusField n, ∀ c ∈ markedBonds (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V),
      frameCoord ℓ (T.stage s).anchorRadius (T.stage s).depth (T.stage s).toStepSetup.frameReach
        (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) V)
        (c.1 - siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w)), c.2) =
      frameCoord ℓ (T.stage s).anchorRadius (T.stage s).depth (T.stage s).toStepSetup.frameReach V c)
    (W : TorusField (n * ℓ.side)) (U : StepNoise ℓ n) :
    rule.stepOutcome T s n (TorusFields.translate (siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w))) W)
        (fun y => U.1 (y + siteOfInt (scaleCoords ℓ.side w)),
          fun c => U.2.1 (c.1 + siteOfInt (scaleCoords ℓ.side w), c.2),
          fun b => U.2.2 (b.1 + siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w)), b.2)) =
      translateOutcome (scaleCoords ℓ.side w) (rule.stepOutcome T s n W U) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show baseChoiceOfOffsets (fun y => rule.base s n
        (TorusFields.translate (siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w))) W) y
        (U.1 (y + siteOfInt (scaleCoords ℓ.side w)))) =
      translateBases (scaleCoords ℓ.side w) (baseChoiceOfOffsets fun y => rule.base s n W y (U.1 y))
    rw [← baseChoiceOfOffsets_translate]
    congr 1
    funext y
    exact hr.base_translate s n W (scaleCoords ℓ.side w) y _
  · exact stepOutcome_field_translate rule T hr s n (scaleCoords ℓ.side w) W U
  · refine Eq.trans ?_ (translateBonds_eq (siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w)))
      (rule.stepOutcome T s n W U).2.2).symm
    refine Finset.ext fun c => ?_
    obtain ⟨x, i⟩ := c
    exact (mem_stepOutcome_bad_translate hfit rule T hr s n hB w hfr W U x i).trans
      (mem_translateBondSet (a := siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w)))
        (B := (rule.stepOutcome T s n W U).2.2) (c := (x, i))).symm
private theorem isBlockTorusSide_mul (hfit : ℓ.Admissible) {n : ℕ} (hB : IsBlockTorusSide ℓ n) :
    IsBlockTorusSide ℓ (n * ℓ.side) :=
  ⟨Dvd.intro_left n rfl, le_trans hB.2 (Nat.le_mul_of_pos_right n (by have := hfit.L_ge; omega))⟩
private theorem chain_translate (hfit : ℓ.Admissible) (rule : NoiseRule ℓ) (T : StageTower ℓ)
    (hr : rule.IsAdmissible T) (K : ℕ)
    (hfr : ∀ s < K, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ (w : Fin 4 → ℤ) (V : TorusField n),
      ∀ c ∈ markedBonds (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V),
      frameCoord ℓ (T.stage s).anchorRadius (T.stage s).depth (T.stage s).toStepSetup.frameReach
        (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) V)
        (c.1 - siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w)), c.2) =
      frameCoord ℓ (T.stage s).anchorRadius (T.stage s).depth (T.stage s).toStepSetup.frameReach V c) :
    ∀ s : ℕ, s ≤ K → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ (w : Fin 4 → ℤ)
      (W : TorusField (fineSide ℓ.side s n)) (U : ChainNoise.ChainNoise ℓ s n),
      rule.chain T s n (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ s * scaleCoords ℓ.side w i) W)
          (noiseTranslate ℓ s n (scaleCoords ℓ.side w) U) =
        translateSample s n (scaleCoords ℓ.side w) (rule.chain T s n W U) := by
  intro s
  induction s with
  | zero =>
    intro _ n _ _ w W U
    have e : (fun i => (ℓ.side : ℤ) ^ 0 * scaleCoords ℓ.side w i) = scaleCoords ℓ.side w := by
      funext i
      simp
    simp only [e]
    rfl
  | succ s ih =>
    intro hs n _ hB w W U
    have e : (fun i => (ℓ.side : ℤ) ^ (s + 1) * scaleCoords ℓ.side w i) =
        fun i => (ℓ.side : ℤ) ^ s * scaleCoords ℓ.side (scaleCoords ℓ.side w) i := by
      funext i
      simp only [scaleCoords]
      ring
    rw [e]
    have h := ih (by omega) (n * ℓ.side) (isBlockTorusSide_mul hfit hB) (scaleCoords ℓ.side w) W U.1
    refine Prod.ext h ?_
    show rule.stepOutcome T s n (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side)
        (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ s * scaleCoords ℓ.side (scaleCoords ℓ.side w) i) W)
        (noiseTranslate ℓ s (n * ℓ.side) (scaleCoords ℓ.side (scaleCoords ℓ.side w)) U.1)))
        (fun y => U.2.1 (y + siteOfInt (scaleCoords ℓ.side w)),
          fun c => U.2.2.1 (c.1 + siteOfInt (scaleCoords ℓ.side w), c.2),
          fun b => U.2.2.2 (b.1 + siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w)), b.2)) =
      translateOutcome (scaleCoords ℓ.side w)
        (rule.stepOutcome T s n (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) W U.1)) U.2)
    rw [h, topField_translateSample]
    exact stepOutcome_translate hfit rule T hr s n hB w (fun V c hc => hfr s (by omega) n hB w V c hc) _ U.2
private theorem sigma_const_congr {m : ℕ} {Ω : Type} (p : Ω) {Y Y' : Finset (TorusSite m)} (h : Y = Y') :
    (⟨Y, fun _ => p⟩ : Σ Y : Finset (TorusSite m), (Y → Ω)) = ⟨Y', fun _ => p⟩ := by
  subst h
  rfl
private theorem stageState_translate (hfit : ℓ.Admissible) (T : StageTower ℓ) :
    ∀ (s n : ℕ) [NeZero n], ℓ.side ∣ n → ∀ (w : Fin 4 → ℤ) (x : MarkedSample ℓ s n),
      stageState T s n (translateSample s n (scaleCoords ℓ.side w) x) =
        translateStageState T s n (scaleCoords ℓ.side w) (stageState T s n x) := by
  intro s
  induction s with
  | zero =>
    intro n _ hL w (W : TorusField n)
    refine congrArg (Prod.mk _) ?_
    refine sigma_const_congr T.basePoint ?_
    show thickening _ (torusHotSites ℓ (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) W)) =
      translateSet _ (thickening _ (torusHotSites ℓ W))
    rw [torusHotSites_translate hfit hL, thickening_translateSet]
  | succ s ih =>
    intro n _ hL w x
    obtain ⟨u, e⟩ := x
    have h := ih (n * ℓ.side) (Dvd.intro_left n rfl) (scaleCoords ℓ.side w) u
    have hh : hotCoreSites (T.stage s).toStepSetup (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) e.2.1) =
        translateSet (siteOfInt (scaleCoords ℓ.side w)) (hotCoreSites (T.stage s).toStepSetup e.2.1) := by
      show thickening _ (torusHotSites ℓ (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) e.2.1)) =
        translateSet _ (thickening _ (torusHotSites ℓ e.2.1))
      rw [torusHotSites_translate hfit hL, thickening_translateSet]
    refine congrArg (Prod.mk _) ?_
    show coarseStateOf (T.stage s).toStepSetup
        (hotCoreSites (T.stage s).toStepSetup (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) e.2.1))
        (stageState T s (n * ℓ.side) (translateSample s (n * ℓ.side) (scaleCoords ℓ.side (scaleCoords ℓ.side w)) u)).1
        (stageState T s (n * ℓ.side)
          (translateSample s (n * ℓ.side) (scaleCoords ℓ.side (scaleCoords ℓ.side w)) u)).2.1
        (stageState T s (n * ℓ.side)
          (translateSample s (n * ℓ.side) (scaleCoords ℓ.side (scaleCoords ℓ.side w)) u)).2.2
        (translateBonds (siteOfInt (scaleCoords ℓ.side (scaleCoords ℓ.side w))) e.2.2)
        (translateBases (scaleCoords ℓ.side w) e.1) =
      translateState (coarseStateOf (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup e.2.1)
        (stageState T s (n * ℓ.side) u).1 (stageState T s (n * ℓ.side) u).2.1
        (stageState T s (n * ℓ.side) u).2.2 e.2.2 e.1) (siteOfInt (scaleCoords ℓ.side w))
    rw [h, hh]
    exact coarseStateOf_translateBonds (scaleCoords ℓ.side w) _ _ _ _ _ _
end Draws
section Borel
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
private theorem measurable_translate {m : ℕ} (a : TorusSite m) :
    Measurable (TorusFields.translate a : TorusField m → TorusField m) :=
  measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun i =>
    (measurable_pi_apply i).comp (measurable_pi_apply (x + a))
private theorem measurable_translateOutcome (v : Fin 4 → ℤ) :
    Measurable (translateOutcome v : StepOutcome ℓ n → StepOutcome ℓ n) := by apply _root_.YangMills.SharedProofs.p19720 <;> assumption
private theorem translateOutcome_neg (v : Fin 4 → ℤ) (e : StepOutcome ℓ n) :
    translateOutcome (-v) (translateOutcome v e) = e := by apply _root_.YangMills.SharedProofs.p77001 <;> assumption
private theorem translateSample_neg (s : ℕ) : ∀ (n : ℕ) [NeZero n] (v : Fin 4 → ℤ) (x : MarkedSample ℓ s n),
    translateSample s n (-v) (translateSample s n v x) = x := by
  induction s with
  | zero =>
    intro n _ v W
    show TorusFields.translate (siteOfInt (-v)) (TorusFields.translate (siteOfInt v) W) = W
    rw [siteOfInt_neg]
    exact translate_neg_translate _ W
  | succ s ih =>
    intro n _ v x
    have e : (fun i => (ℓ.side : ℤ) * (-v) i) = -(fun i => (ℓ.side : ℤ) * v i) := by
      funext i
      simp
    refine Prod.ext ?_ (translateOutcome_neg v x.2)
    show translateSample s (n * ℓ.side) (fun i => (ℓ.side : ℤ) * (-v) i)
      (translateSample s (n * ℓ.side) (fun i => (ℓ.side : ℤ) * v i) x.1) = x.1
    rw [e]
    exact ih (n * ℓ.side) _ x.1
private theorem measurable_translateSample (s : ℕ) : ∀ (n : ℕ) [NeZero n] (v : Fin 4 → ℤ),
    Measurable (translateSample (ℓ := ℓ) s n v) := by
  induction s with
  | zero =>
    intro n _ v
    exact measurable_translate _
  | succ s ih =>
    intro n _ v
    let _ := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
    exact ((ih (n * ℓ.side) (scaleCoords ℓ.side v)).comp measurable_fst).prodMk
      ((measurable_translateOutcome v).comp measurable_snd)
private theorem measurable_sigma_mk {α : Type} {β : α → Type} [∀ a, MeasurableSpace (β a)] (a : α) :
    Measurable (Sigma.mk a : β a → Sigma β) :=
  fun _ hS => (MeasurableSpace.measurableSet_iInf.mp hS) a
private theorem measurable_translateLabel {m : ℕ} [NeZero m] {Ω : Type} [MeasurableSpace Ω] (a : TorusSite m)
    (Y : Finset (TorusSite m)) :
    Measurable (translateLabel a Y : (Y → Ω) → (translateSet a Y → Ω)) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _
private theorem measurable_translateSigma {m : ℕ} [NeZero m] {Ω : Type} [MeasurableSpace Ω] (a : TorusSite m) :
    Measurable fun q : (Σ Y : Finset (TorusSite m), (Y → Ω)) =>
      (⟨translateSet a q.1, translateLabel a q.1 q.2⟩ : Σ Y : Finset (TorusSite m), (Y → Ω)) := by
  intro S hS
  refine MeasurableSpace.measurableSet_iInf.mpr fun Y => ?_
  exact ((measurable_sigma_mk (β := fun Y : Finset (TorusSite m) => (Y → Ω)) (translateSet a Y)).comp
    (measurable_translateLabel a Y)) hS
private theorem measurable_translateStageState (T : StageTower ℓ) (s n : ℕ) [NeZero n] (v : Fin 4 → ℤ) :
    Measurable (translateStageState T s n v) :=
  ((measurable_translate _).comp measurable_fst).prodMk ((measurable_translateSigma (siteOfInt v)).comp measurable_snd)
private theorem measurable_translateSample_upperSigma (hfit : ℓ.Admissible) (T : StageTower ℓ) (t : ℕ) :
    ∀ (d n : ℕ) [NeZero n], ℓ.side ∣ n → ∀ w : Fin 4 → ℤ,
      @Measurable _ _ (upperSigma T t d n) (upperSigma T t d n) (translateSample (t + d) n (scaleCoords ℓ.side w)) := by
  intro d
  induction d with
  | zero =>
    intro n _ hL w
    rintro S ⟨S', hS', rfl⟩
    refine ⟨translateStageState T t n (scaleCoords ℓ.side w) ⁻¹' S',
      measurable_translateStageState T t n _ hS', ?_⟩
    ext x
    show translateStageState T t n (scaleCoords ℓ.side w) (stageState T t n x) ∈ S' ↔
      stageState T t n (translateSample t n (scaleCoords ℓ.side w) x) ∈ S'
    rw [stageState_translate hfit T t n hL w x]
  | succ d ih =>
    intro n _ hL w
    have h1 := ih (n * ℓ.side) (Dvd.intro_left n rfl) (scaleCoords ℓ.side w)
    refine measurable_iff_comap_le.mpr ?_
    show MeasurableSpace.comap (translateSample (t + d + 1) n (scaleCoords ℓ.side w))
        ((upperSigma T t d (n * ℓ.side)).comap (fun u : MarkedSample ℓ (t + d + 1) n => u.1) ⊔
          (inferInstance : MeasurableSpace (StepOutcome ℓ n)).comap (fun u : MarkedSample ℓ (t + d + 1) n => u.2)) ≤
      (upperSigma T t d (n * ℓ.side)).comap (fun u : MarkedSample ℓ (t + d + 1) n => u.1) ⊔
        (inferInstance : MeasurableSpace (StepOutcome ℓ n)).comap (fun u : MarkedSample ℓ (t + d + 1) n => u.2)
    rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
    refine sup_le_sup ?_ ?_
    · have e : (fun u : MarkedSample ℓ (t + d + 1) n => u.1) ∘ translateSample (t + d + 1) n (scaleCoords ℓ.side w) =
          translateSample (t + d) (n * ℓ.side) (scaleCoords ℓ.side (scaleCoords ℓ.side w)) ∘
            fun u : MarkedSample ℓ (t + d + 1) n => u.1 := rfl
      rw [e, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp h1)
    · have e : (fun u : MarkedSample ℓ (t + d + 1) n => u.2) ∘ translateSample (t + d + 1) n (scaleCoords ℓ.side w) =
          translateOutcome (scaleCoords ℓ.side w) ∘ fun u : MarkedSample ℓ (t + d + 1) n => u.2 := rfl
      rw [e, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp (measurable_translateOutcome _))
end Borel
end ChainTranslation
open ChainTranslation in
theorem chainTranslationStatement_holds (hF : FrameCovariance) : chainTranslationStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hD _ _ _ _
  refine ⟨0, ?_⟩
  intro Kr _ _ _ _ _
  refine ⟨max Tb.floorMin ((2 * Tb.B) ^ 2), ?_⟩
  intro y hy hret h0 g β K m T t d n _ hlev w
  have hy1 : Tb.floorMin ≤ y := le_trans (le_max_left _ _) hy
  have hy2 : (2 * Tb.B) ^ 2 ≤ y := le_trans (le_max_right _ _) hy
  have hfits : (Tb.stepParameters y).Admissible := hD.fits y hy1
  have hB : 0 ≤ Tb.B := le_trans zero_le_one hD.B_ge
  have hblock : IsBlockTorusSide (Tb.stepParameters y) n := isBlockTorusSide_of_level hD hlev
  have hfrAll : ∀ s < K, ∀ (n' : ℕ) [NeZero n'], IsBlockTorusSide (Tb.stepParameters y) n' →
      ∀ (w' : Fin 4 → ℤ) (V : TorusField n'),
      ∀ c ∈ markedBonds (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V),
      frameCoord (Tb.stepParameters y) (T.stage s).anchorRadius (T.stage s).depth
        (T.stage s).toStepSetup.frameReach
        (TorusFields.translate (siteOfInt (scaleCoords (Tb.stepParameters y).side w')) V)
        (c.1 - siteOfInt (scaleCoords (Tb.stepParameters y).side (scaleCoords (Tb.stepParameters y).side w')), c.2) =
      frameCoord (Tb.stepParameters y) (T.stage s).anchorRadius (T.stage s).depth
        (T.stage s).toStepSetup.frameReach V c := by
    intro s hs n' _ hblock' w' V c hc
    have hrun := flow_bounds hB hret h0 hlev.chain.toCrossingVolume.toFlowCrossing
    obtain ⟨hy0, -, hmove⟩ := hrun s (by omega)
    obtain ⟨hy1', -, -⟩ := hrun (s + 1) hs
    have hmove' := hmove hs
    have hx : (T.stage s).coupling = (couplingFlow (Tb.stepParameters y) β s).1 := hlev.chain.follows s (by omega)
    have hx' : (T.stage s).nextCoupling = (couplingFlow (Tb.stepParameters y) β (s + 1)).1 :=
      hlev.chain.follows (s + 1) (by omega)
    have hone : (1 : ℝ) ≤ y := hfits.y₁_ge
    have hr1 : 2 ^ 16 ≤ clusterRange y := hfits.range_ge
    have hfit2 : RangesAdmissible (T.stage s).toStepSetup.range (T.stage s).toStepSetup.nextRange := by
      have e1 : (T.stage s).toStepSetup.range = clusterRange (couplingFlow (Tb.stepParameters y) β s).1 := by
        show clusterRange (T.stage s).coupling = _
        rw [hx]
      have e2 : (T.stage s).toStepSetup.nextRange =
          clusterRange (couplingFlow (Tb.stepParameters y) β (s + 1)).1 := by
        show clusterRange (T.stage s).nextCoupling = _
        rw [hx']
      rw [e1, e2]
      refine ⟨clusterRange_le_succ hB (by linarith) (by linarith) (by linarith)
          (by linarith [(abs_le.mp hmove').1]),
        le_trans hr1 (clusterRange_mono (by linarith) hy1'), ?_⟩
      have h3 := le_trans hr1 (clusterRange_mono (by linarith) hy0)
      exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (le_trans (by norm_num) h3)
    have hρ : (T.stage s).anchorRadius = Tb.ρA := (stage_anchorRadius T s).trans hlev.chain.anchor_bottom
    have hC : ColdChainConstants (Tb.stepParameters y).coupling Tb.δ₁ (Tb.stepParameters y).side Tb.lam
        (T.stage s).anchorRadius Tb.σA Tb.cg Tb.N := by
      rw [hρ]
      exact hD.chain
    classical
    obtain ⟨hc1, hc2⟩ := Finset.mem_filter.mp hc
    exact (hF (Tb.stepParameters y) Tb.δ₁ Tb.lam (T.stage s).anchorRadius Tb.σA Tb.cg Tb.N hfits hC hD.σ_le
      (T.stage s).depth (T.stage s).toStepSetup.range (T.stage s).toStepSetup.nextRange n' V _ _ _ hfit2
      (Or.inl ⟨hblock', rfl, rfl, rfl⟩) c hc1 hc2).2 _
  refine ⟨fun rule hr p => ?_, fun x => ?_, fun x => ?_, measurable_translateSample _ _ _, ?_⟩
  · exact chain_translate hfits rule T hr K hfrAll (t + d) hlev.le n hblock w p.1 p.2
  · exact stageState_translate hfits T (t + d) n hblock.1 w x
  · have e : (fun i => ((Tb.stepParameters y).side : ℤ) * -w i) =
        -(fun i => ((Tb.stepParameters y).side : ℤ) * w i) := by
      funext i
      simp
    rw [e]
    exact translateSample_neg _ n _ x
  · exact measurable_translateSample_upperSigma hfits T t d n hblock.1 w
end YangMills.Construction.MomentLaw
end
