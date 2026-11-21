import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStepKeepsTranslations
import YangMills.Construction.ResponseInTheExpansion.ScoreIsCarriedByTranslations
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepSettings StepCosts StepGas RenormalizationStepParameters StepMarks ColdChain BlockAverages LumpContours
  ClusterExpansionOfAStep BaseTranslations
namespace StepResponseTranslation
section TranslatedSets
variable {m : ℕ} [NeZero m]
private theorem mem_translateSet_iff {a z : TorusSite m} {Y : Finset (TorusSite m)} :
    z ∈ translateSet a Y ↔ z + a ∈ Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.mem_translateSet <;> assumption
private theorem translateSet_neg_translateSet (a : TorusSite m) (Y : Finset (TorusSite m)) :
    translateSet (-a) (translateSet a Y) = Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translateSet_neg_translateSet <;> assumption
private theorem translateSet_translateSet_neg (a : TorusSite m) (Y : Finset (TorusSite m)) :
    translateSet a (translateSet (-a) Y) = Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translateSet_translateSet_neg <;> assumption
private theorem thickening_translateSet (k : ℕ) (a : TorusSite m) (X : Finset (TorusSite m)) :
    thickening k (translateSet a X) = translateSet a (thickening k X) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.thickening_translateSet <;> assumption
private theorem chainComponents_translateSet (r : ℕ) (a : TorusSite m) (Y : Finset (TorusSite m)) :
    chainComponents r (translateSet a Y) = (chainComponents r Y).image (translateSet a) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.chainComponents_translateSet <;> assumption
private def translateBonds (a : TorusSite m) (B : Finset (TorusBond m)) : Finset (TorusBond m) :=
  open Classical in Finset.univ.filter fun c => (c.1 + a, c.2) ∈ B
private theorem mem_translateBonds_iff {a : TorusSite m} {B : Finset (TorusBond m)} {c : TorusBond m} :
    c ∈ translateBonds a B ↔ (c.1 + a, c.2) ∈ B := by
  classical
  simp [translateBonds]
private theorem image_fst_translateBonds (a : TorusSite m) (B : Finset (TorusBond m)) :
    (open Classical in (translateBonds a B).image Prod.fst) =
      translateSet a (open Classical in B.image Prod.fst) := by
  classical
  ext z
  simp only [Finset.mem_image, mem_translateSet_iff, mem_translateBonds_iff]
  constructor
  · rintro ⟨⟨x, i⟩, h, rfl⟩
    exact ⟨_, h, rfl⟩
  · rintro ⟨⟨x, i⟩, h, e⟩
    simp only at e
    exact ⟨(z, i), by simpa [← e] using h, rfl⟩
private def translateSetEquiv (a : TorusSite m) : Finset (TorusSite m) ≃ Finset (TorusSite m) where
  toFun := translateSet a
  invFun := translateSet (-a)
  left_inv := translateSet_neg_translateSet a
  right_inv := translateSet_translateSet_neg a
private theorem translateBonds_neg_translateBonds (a : TorusSite m) (B : Finset (TorusBond m)) :
    translateBonds (-a) (translateBonds a B) = B := by
  ext c
  simp [mem_translateBonds_iff]
private theorem translateBonds_translateBonds_neg (a : TorusSite m) (B : Finset (TorusBond m)) :
    translateBonds a (translateBonds (-a) B) = B := by
  ext c
  simp [mem_translateBonds_iff]
end TranslatedSets
section BlockScale
variable {n L : ℕ}
private abbrev blockScale (L : ℕ) (v : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (L : ℤ) * v i
private theorem exists_cast_add_intCast {m : ℕ} [NeZero m] (x : ZMod m) (z : ℤ) :
    ∃ k : ℤ, (((x + (z : ZMod m) : ZMod m)).cast : ℤ) = (x.cast : ℤ) + z + (m : ℤ) * k := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.exists_cast_add_intCast <;> assumption
private theorem parentBlock_add_siteOfInt [NeZero n] [NeZero L] (x : TorusSite (n * L)) (v : Fin 4 → ℤ) :
    parentBlock L (x + siteOfInt (blockScale L v)) = parentBlock L x + siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.parentBlock_add_scale <;> assumption
private theorem blockSite_add_siteOfInt [NeZero n] [NeZero L] (y : TorusSite n) (o : BlockOffset L)
    (v : Fin 4 → ℤ) :
    (blockSite (y + siteOfInt v) o : TorusSite (n * L)) = blockSite y o + siteOfInt (blockScale L v) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.blockSite_add <;> assumption
end BlockScale
section Clusters
variable {n L : ℕ} [NeZero n] [NeZero L]
private theorem mem_sitesInBlocks_iff {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.mem_sitesInBlocks <;> assumption
private theorem sitesInBlocks_translateSet (v : Fin 4 → ℤ) (S : Finset (TorusSite n)) :
    sitesInBlocks L (translateSet (siteOfInt v) S) =
      translateSet (siteOfInt (blockScale L v)) (sitesInBlocks L S) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.sitesInBlocks_translateSet <;> assumption
private theorem translateSet_inter_nonempty_iff {m : ℕ} [NeZero m] (a : TorusSite m) (X Y : Finset (TorusSite m)) :
    (open Classical in (translateSet a X ∩ translateSet a Y).Nonempty) ↔ (open Classical in (X ∩ Y).Nonempty) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translateSet_inter_nonempty <;> assumption
variable (r r' : ℕ) (v : Fin 4 → ℤ) (bad : Finset (TorusBond (n * L))) (Yt : Finset (TorusSite (n * L)))
  (C : Finset (TorusSite n))
private theorem clusterComponents_translate :
    clusterComponents L r (translateBonds (siteOfInt (blockScale L v)) bad)
        (translateSet (siteOfInt (blockScale L v)) Yt) (translateSet (siteOfInt v) C) =
      (clusterComponents L r bad Yt C).image (translateSet (siteOfInt (blockScale L v))) := by
  classical
  unfold clusterComponents
  rw [← chainComponents_translateSet]
  congr 1
  rw [image_fst_translateBonds, sitesInBlocks_translateSet]
  ext z
  simp [mem_translateSet_iff]
private theorem attachedSites_translate :
    attachedSites L r (translateBonds (siteOfInt (blockScale L v)) bad)
        (translateSet (siteOfInt (blockScale L v)) Yt) (translateSet (siteOfInt v) C) =
      translateSet (siteOfInt (blockScale L v)) (attachedSites L r bad Yt C) := by
  classical
  ext z
  rw [mem_translateSet_iff]
  simp only [attachedSites, Finset.mem_biUnion, Finset.mem_filter, id, clusterComponents_translate,
    Finset.mem_image]
  constructor
  · rintro ⟨X', ⟨⟨X, hX, rfl⟩, hn⟩, hz⟩
    rw [sitesInBlocks_translateSet] at hn
    exact ⟨X, ⟨hX, (translateSet_inter_nonempty_iff _ _ _).mp (by convert hn)⟩, mem_translateSet_iff.mp hz⟩
  · rintro ⟨X, ⟨hX, hn⟩, hz⟩
    refine ⟨_, ⟨⟨X, hX, rfl⟩, ?_⟩, mem_translateSet_iff.mpr hz⟩
    rw [sitesInBlocks_translateSet]
    convert (translateSet_inter_nonempty_iff (siteOfInt (blockScale L v)) X (sitesInBlocks L C)).mpr
      (by convert hn)
private theorem coreBlocks_translate (θ : Finset (TorusSite (n * L))) :
    coreBlocks L r (translateSet (siteOfInt (blockScale L v)) θ) = translateSet (siteOfInt v) (coreBlocks L r θ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.coreBlocks_translateSet <;> assumption
private theorem storedBlocks_translate :
    storedBlocks L r (translateBonds (siteOfInt (blockScale L v)) bad)
        (translateSet (siteOfInt (blockScale L v)) Yt) (translateSet (siteOfInt v) C) =
      translateSet (siteOfInt v) (storedBlocks L r bad Yt C) := by
  classical
  unfold storedBlocks
  rw [attachedSites_translate, coreBlocks_translate]
  ext z
  simp [mem_translateSet_iff]
private theorem coarseHull_translate :
    coarseHull L r r' (translateBonds (siteOfInt (blockScale L v)) bad)
        (translateSet (siteOfInt (blockScale L v)) Yt) (translateSet (siteOfInt v) C) =
      translateSet (siteOfInt v) (coarseHull L r r' bad Yt C) := by
  unfold coarseHull
  rw [storedBlocks_translate, thickening_translateSet]
end Clusters
section HotLumps
variable {ℓ : StepParameters} {m : ℕ} [NeZero m]
private theorem curvature_translate_apply (a : TorusSite m) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    curvature (TorusFields.translate a W) x μ ν = curvature W (x + a) μ ν := by
  simp only [curvature, holonomy, TorusFields.translate, add_right_comm x a]
private theorem translateSet_torusLumpOf (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ)
    (z : TorusSite m) :
    translateSet (siteOfInt (blockScale ℓ.side w)) (torusLumpOf ℓ (z + siteOfInt (blockScale ℓ.side w))) =
      torusLumpOf ℓ z := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translateSet_torusLumpOf <;> assumption
private theorem torusHotLumps_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ)
    (W : TorusField m) :
    torusHotLumps ℓ (TorusFields.translate (siteOfInt (blockScale ℓ.side w)) W) =
      (torusHotLumps ℓ W).image (translateSet (siteOfInt (blockScale ℓ.side w))) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusHotLumps_translate <;> assumption
private theorem torusHotSites_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ)
    (W : TorusField m) :
    torusHotSites ℓ (TorusFields.translate (siteOfInt (blockScale ℓ.side w)) W) =
      translateSet (siteOfInt (blockScale ℓ.side w)) (torusHotSites ℓ W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusHotSites_translate <;> assumption
private theorem translate_neg_translate (a : TorusSite m) (W : TorusField m) :
    TorusFields.translate (-a) (TorusFields.translate a W) = W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translate_neg_translate <;> assumption
private theorem isHullState_translate_iff (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (r : ℕ)
    {W : TorusField m} {Y : Finset (TorusSite m)} :
    IsHullState ℓ r (TorusFields.translate (siteOfInt (blockScale ℓ.side w)) W) (translateSet (siteOfInt (blockScale ℓ.side w)) Y) ↔
      IsHullState ℓ r W Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.isHullState_translate_iff <;> assumption
end HotLumps
section CoarseStates
variable {R : StepSetup} {n : ℕ} [NeZero n]
private def translateState (q : CoarseState R n) (a : TorusSite n) : CoarseState R n :=
  ⟨translateSet a q.1, translateLabel a q.1 q.2⟩
private theorem coarseState_ext_of_labelAt (q q' : CoarseState R n) (h1 : q.1 = q'.1)
    (h2 : ∀ y, q.markAt y = q'.markAt y) : q = q' := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.coarseState_ext <;> assumption
private theorem markAt_translateState (q : CoarseState R n) (a y : TorusSite n) :
    (translateState q a).markAt y = q.markAt (y + a) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.markAt_translateState <;> assumption
private theorem translateState_injective (a : TorusSite n) :
    Function.Injective fun q : CoarseState R n => translateState q a := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translateState_injective <;> assumption
private theorem labelAt_translateState (q : CoarseState R n) (v : Fin 4 → ℤ) (z : TorusSite (n * R.params.side)) :
    (translateState q (siteOfInt v)).labelAt z = q.labelAt (z + siteOfInt (blockScale R.params.side v)) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.labelAt_translateState <;> assumption
private theorem fieldWithStoredLinks_translateState (q : CoarseState R n) (v : Fin 4 → ℤ)
    (W : TorusField (n * R.params.side)) :
    (translateState q (siteOfInt v)).fieldWithStoredLinks
        (TorusFields.translate (siteOfInt (blockScale R.params.side v)) W) =
      TorusFields.translate (siteOfInt (blockScale R.params.side v)) (q.fieldWithStoredLinks W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.fieldWithStoredLinks_translateState <;> assumption
private theorem mem_unlabelled_iff {q : CoarseState R n} {Yt : Finset (TorusSite (n * R.params.side))}
    {z : TorusSite (n * R.params.side)} : z ∈ q.unlabelled Yt ↔ z ∈ Yt ∧ q.labelAt z = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.mem_unlabelled <;> assumption
private def unlabelledEquiv (q : CoarseState R n) (v : Fin 4 → ℤ) (Yt : Finset (TorusSite (n * R.params.side))) :
    (translateState q (siteOfInt v)).unlabelled (translateSet (siteOfInt (blockScale R.params.side v)) Yt) ≃
      q.unlabelled Yt where
  toFun z := ⟨z.1 + siteOfInt (blockScale R.params.side v), by
    have h := mem_unlabelled_iff.mp z.2
    exact mem_unlabelled_iff.mpr ⟨mem_translateSet_iff.mp h.1, by rw [← labelAt_translateState]; exact h.2⟩⟩
  invFun z := ⟨z.1 - siteOfInt (blockScale R.params.side v), by
    have h := mem_unlabelled_iff.mp z.2
    refine mem_unlabelled_iff.mpr ⟨mem_translateSet_iff.mpr (by simpa using h.1), ?_⟩
    rw [labelAt_translateState, sub_add_cancel]
    exact h.2⟩
  left_inv z := by simp
  right_inv z := by simp
private theorem fillLabels_translateState (q : CoarseState R n) (v : Fin 4 → ℤ)
    (Yt : Finset (TorusSite (n * R.params.side))) (ν : q.unlabelled Yt → R.labels.Ω) :
    (translateState q (siteOfInt v)).fillLabels (translateSet (siteOfInt (blockScale R.params.side v)) Yt)
        (fun z => ν (unlabelledEquiv q v Yt z)) =
      translateLabel (siteOfInt (blockScale R.params.side v)) Yt (q.fillLabels Yt ν) := by
  funext ⟨z, hz⟩
  have hz' : z + siteOfInt (blockScale R.params.side v) ∈ Yt := mem_translateSet_iff.mp hz
  show _ = q.fillLabels Yt ν ⟨z + siteOfInt (blockScale R.params.side v), hz'⟩
  by_cases h : q.labelAt (z + siteOfInt (blockScale R.params.side v)) = Sum.inl ()
  · have h1 : z + siteOfInt (blockScale R.params.side v) ∈ q.unlabelled Yt := mem_unlabelled_iff.mpr ⟨hz', h⟩
    have h2 : z ∈ (translateState q (siteOfInt v)).unlabelled (translateSet (siteOfInt (blockScale R.params.side v)) Yt) :=
      mem_unlabelled_iff.mpr ⟨hz, by rw [labelAt_translateState]; exact h⟩
    rw [fillLabels_of_mem_unlabelled _ _ _ _ hz h2, fillLabels_of_mem_unlabelled _ _ _ _ hz' h1]
    rfl
  · have h1 : z + siteOfInt (blockScale R.params.side v) ∈ q.labelSet := mem_labelSet.mpr h
    have h2 : z ∈ (translateState q (siteOfInt v)).labelSet :=
      mem_labelSet.mpr (by rw [labelAt_translateState]; exact h)
    rw [fillLabels_of_mem _ _ _ _ hz h2, fillLabels_of_mem _ _ _ _ hz' h1]
    have e1 := labelAt_eq_inr_labeling (translateState q (siteOfInt v)) ⟨z, h2⟩
    have e2 := labelAt_eq_inr_labeling q ⟨_, h1⟩
    simp only at e1 e2
    rw [labelAt_translateState, e2] at e1
    exact (Sum.inr_injective e1).symm
end CoarseStates
section CellCharts
variable {F : BlockFrame} (u : Fin 4 → ℤ)
private def fineCellTranslation : F.Site F.depth := siteOfCoords F.depth fun i => (F.blockSide : ℤ) * u i
private def translateFine (X : F.GaugeField F.depth) : F.GaugeField F.depth :=
  fun x i => X (x + fineCellTranslation u) i
private def translateCoarse (U : F.GaugeField F.top) : F.GaugeField F.top :=
  fun y i => U (y + siteOfCoords F.top u) i
private theorem pathHolonomy_translateFine (X : F.GaugeField F.depth) (x : F.Site F.depth) (l : List PathStep) :
    pathHolonomy (translateFine u X) x l = pathHolonomy X (x + fineCellTranslation u) l := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.pathHolonomy_translateFine <;> assumption
private theorem cellCentre_add_siteOfCoords (z : F.Cell) :
    cellCentre F.depth (z + siteOfCoords F.top u) = cellCentre F.depth z + fineCellTranslation u := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.cellCentre_add_siteOfCoords <;> assumption
private theorem enclosingCell_add_translation (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (x : F.Site F.depth) :
    enclosingCell (x + fineCellTranslation u) = enclosingCell x + siteOfCoords F.top u := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.enclosingCell_add_translation <;> assumption
private theorem cellOffset_add_translation (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (x : F.Site F.depth) :
    cellOffset (x + fineCellTranslation u) = cellOffset x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.cellOffset_add_translation <;> assumption
private theorem axialGauge_translateFine (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (π : Equiv.Perm (Fin 4)) (X : F.GaugeField F.depth) (x : F.Site F.depth) :
    axialGauge π (translateFine u X) x = axialGauge π X (x + fineCellTranslation u) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.axialGauge_translateFine <;> assumption
private theorem bondCoordinate_translate (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (π : Equiv.Perm (Fin 4)) (U : F.GaugeField F.top) (X : F.GaugeField F.depth)
    (x : F.Site F.depth) (i : Fin 4) :
    bondCoordinate π (translateCoarse u U) (translateFine u X) (x, i) =
      bondCoordinate π U X (x + fineCellTranslation u, i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.bondCoordinate_translate <;> assumption
end CellCharts
section StepFrame
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
private theorem readAtLevel_zero_translate (v : Fin 4 → ℤ) (W : TorusField (n * ℓ.side)) :
    readAtLevel (stepBlockFrame ℓ.side n) 0 (TorusFields.translate (siteOfInt (blockScale ℓ.side v)) W) =
      translateFine (F := stepBlockFrame ℓ.side n) v (readAtLevel (stepBlockFrame ℓ.side n) 0 W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.readAtLevel_translate_fine <;> assumption
private theorem readAtLevel_one_translate (v : Fin 4 → ℤ) (V : TorusField n) :
    readAtLevel (stepBlockFrame ℓ.side n) 1 (TorusFields.translate (siteOfInt v) V) =
      translateCoarse (F := stepBlockFrame ℓ.side n) v (readAtLevel (stepBlockFrame ℓ.side n) 1 V) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.readAtLevel_translate_coarse <;> assumption
private theorem stepBlockFrame_extent_ge (hn : 2 ≤ n) : ∀ i, 2 ≤ (stepBlockFrame ℓ.side n).extent i :=
  fun _ => hn
private theorem chartCoord_translate (hL : Odd ℓ.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (x : TorusSite (n * ℓ.side)) (i : Fin 4) :
    chartCoord ℓ (TorusFields.translate (siteOfInt v) V)
        (TorusFields.translate (siteOfInt (blockScale ℓ.side v)) W) (x, i) =
      chartCoord ℓ V W (x + siteOfInt (blockScale ℓ.side v), i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.chartCoord_translate <;> assumption
private theorem add_blockScale_mem_chartBonds_iff (hL : Odd ℓ.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ)
    (x : TorusSite (n * ℓ.side)) (i : Fin 4) :
    (x + siteOfInt (blockScale ℓ.side v), i) ∈ chartBonds ℓ.side n ↔ (x, i) ∈ chartBonds ℓ.side n := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.add_mem_chartBonds_iff <;> assumption
end StepFrame
section StepWeights
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem markedBonds_translateSet (hL : Odd R.params.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ)
    (C : Finset (TorusSite n)) :
    markedBonds R (translateSet (siteOfInt v) C) =
      translateBonds (siteOfInt (blockScale R.params.side v)) (markedBonds R C) := by
  classical
  ext ⟨x, i⟩
  rw [mem_translateBonds_iff]
  simp only [markedBonds, Finset.mem_filter, mem_translateSet_iff]
  rw [add_blockScale_mem_chartBonds_iff hL hn, parentBlock_add_siteOfInt]
private theorem bondMark_translate (hL : Odd R.params.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (h : frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt v) V) (x, i) =
      frameCoord R.params R.anchorRadius R.depth R.frameReach V (x + siteOfInt (blockScale R.params.side v), i)) :
    bondMark R (TorusFields.translate (siteOfInt v) V)
        (TorusFields.translate (siteOfInt (blockScale R.params.side v)) W) (x, i) =
      bondMark R V W (x + siteOfInt (blockScale R.params.side v), i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.bondMark_translate <;> assumption
private theorem markProduct_translate (hL : Odd R.params.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ)
    (C : Finset (TorusSite n)) (V : TorusField n) (W : TorusField (n * R.params.side))
    (bad : Finset (TorusBond (n * R.params.side)))
    (hfr : ∀ c ∈ markedBonds R C,
      frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt v) V)
      (c.1 - siteOfInt (blockScale R.params.side v), c.2) =
        frameCoord R.params R.anchorRadius R.depth R.frameReach V c) :
    markProduct R (translateSet (siteOfInt v) C) (TorusFields.translate (siteOfInt v) V)
        (TorusFields.translate (siteOfInt (blockScale R.params.side v)) W)
        (translateBonds (siteOfInt (blockScale R.params.side v)) bad) = markProduct R C V W bad := by
  classical
  unfold markProduct
  rw [markedBonds_translateSet hL hn]
  refine Finset.prod_nbij' (fun c => (c.1 + siteOfInt (blockScale R.params.side v), c.2))
    (fun c => (c.1 - siteOfInt (blockScale R.params.side v), c.2))
    (fun c hc => mem_translateBonds_iff.mp hc) (fun c hc => mem_translateBonds_iff.mpr (by simpa using hc))
    (fun c _ => by simp) (fun c _ => by simp) ?_
  rintro ⟨x, i⟩ hc
  have hc' : (x + siteOfInt (blockScale R.params.side v), i) ∈ markedBonds R C := mem_translateBonds_iff.mp hc
  have h := hfr _ hc'
  simp only [add_sub_cancel_right] at h
  have hm := bondMark_translate (R := R) hL hn v V W x i h
  simp only [mem_translateBonds_iff]
  rw [hm]
private theorem stepWeight_translate (hR : R.IsWellPosed) (hK : BaseTranslations.TranslationPreservesBaseKernel)
    (hn : R.params.n₀ ≤ n) (v : Fin 4 → ℤ) (C : Finset (TorusSite n)) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hull : IsHullState R.params R.range W Yt)
    (hfr : ∀ c ∈ markedBonds R C,
      frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt v) V)
      (c.1 - siteOfInt (blockScale R.params.side v), c.2) =
        frameCoord R.params R.anchorRadius R.depth R.frameReach V c) :
    stepWeight R (translateSet (siteOfInt v) C) (TorusFields.translate (siteOfInt v) V)
        (TorusFields.translate (siteOfInt (blockScale R.params.side v)) W)
        (translateSet (siteOfInt (blockScale R.params.side v)) Yt)
        (translateLabel (siteOfInt (blockScale R.params.side v)) Yt ωt)
        (translateBonds (siteOfInt (blockScale R.params.side v)) bad) (translateBases v b) =
      stepWeight R C V W Yt ωt bad b := by
  classical
  have hfit := hR.admissible
  have hn2 : 2 ≤ n := by
    have := hfit.n₀_ge
    omega
  obtain ⟨h1, h2, h3⟩ := hK R.params hfit R.coupling n hn v W V b
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hD := hR.hasExpansions.2.translation (n * R.params.side) hside W Yt ωt
    (siteOfInt (blockScale R.params.side v)) ⟨v, rfl⟩ hull
  unfold stepWeight
  rw [markProduct_translate hfit.L_odd hn2 v C V W bad hfr, hD]
  by_cases hb : b ∈ baseChoices R.params (fineLevelField R.params n W)
  · have e3 := h3 hb
    have e : baseLaw (R := R) (TorusFields.translate (siteOfInt (blockScale R.params.side v)) W)
        (translateBases v b) =
        baseLaw (R := R) W b := by
      unfold baseLaw
      rw [if_pos (h1.mpr hb), if_pos hb, h2]
    rw [e]
    congr 2
  · have e : baseLaw (R := R) (TorusFields.translate (siteOfInt (blockScale R.params.side v)) W)
        (translateBases v b) =
        baseLaw (R := R) W b := by
      unfold baseLaw
      rw [if_neg (fun h => hb (h1.mp h)), if_neg hb]
    have e0 : baseLaw (R := R) W b = 0 := by
      unfold baseLaw
      rw [if_neg hb]
    rw [e, e0]
    simp
end StepWeights
section BaseChoices
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem translateBases_neg_translateBases (v : Fin 4 → ℤ) (b : BaseChoice L n) :
    translateBases (-v) (translateBases v b) = b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translateBases_neg_translateBases <;> assumption
private def translateBasesEquiv (v : Fin 4 → ℤ) : BaseChoice L n ≃ BaseChoice L n where
  toFun := translateBases v
  invFun := translateBases (-v)
  left_inv := translateBases_neg_translateBases v
  right_inv b := by simpa using translateBases_neg_translateBases (-v) b
end BaseChoices
section StatesOfCases
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem baseOffset_translateBases (v : Fin 4 → ℤ) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    baseOffset R (translateBases v b) y = baseOffset R b (y + siteOfInt v) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.baseOffset_translateBases <;> assumption
private theorem blockConfigAt_translate (v : Fin 4 → ℤ) (C Z : Finset (TorusSite n))
    (F : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) (y : TorusSite n) :
    blockConfigAt R (translateSet (siteOfInt v) C) (translateSet (siteOfInt v) Z)
        (TorusFields.translate (siteOfInt (blockScale R.params.side v)) F)
        (translateSet (siteOfInt (blockScale R.params.side v)) Yt)
        (translateLabel (siteOfInt (blockScale R.params.side v)) Yt ωt)
        (translateBonds (siteOfInt (blockScale R.params.side v)) bad) (translateBases v b) y =
      blockConfigAt R C Z F Yt ωt bad b (y + siteOfInt v) := by
  classical
  refine blockConfig_ext ?_ ?_ ?_ ?_ ?_
  · simp only [blockConfigAt, mem_translateSet_iff]
  · funext c
    simp only [blockConfigAt, mem_translateBonds_iff, blockSite_add_siteOfInt]
  · funext o
    simp only [blockConfigAt]
    by_cases h : blockSite (y + siteOfInt v) o ∈ Yt
    · have h' : blockSite y o ∈ translateSet (siteOfInt (blockScale R.params.side v)) Yt := by
        rw [mem_translateSet_iff, ← blockSite_add_siteOfInt]
        exact h
      rw [dif_pos h, dif_pos h']
      simp only [translateLabel, Sum.inr.injEq]
      congr 2
      exact (blockSite_add_siteOfInt y o v).symm
    · have h' : blockSite y o ∉ translateSet (siteOfInt (blockScale R.params.side v)) Yt := by
        rw [mem_translateSet_iff, ← blockSite_add_siteOfInt]
        exact h
      rw [dif_neg h, dif_neg h']
  · exact baseOffset_translateBases v b y
  · funext c
    have e : parentBlock R.params.side (blockSite (L := R.params.side) y c.1 +
          TorusFields.unitStep (n * R.params.side) c.2) + siteOfInt v =
        parentBlock R.params.side (blockSite (L := R.params.side) (y + siteOfInt v) c.1 +
          TorusFields.unitStep (n * R.params.side) c.2) := by
      rw [blockSite_add_siteOfInt, add_right_comm, parentBlock_add_siteOfInt]
    simp only [blockConfigAt, mem_translateSet_iff, e, TorusFields.translate, blockSite_add_siteOfInt]
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
        (TorusFields.translate (siteOfInt (blockScale R.params.side v)) F)
        (translateSet (siteOfInt (blockScale R.params.side v)) Yt)
        (translateLabel (siteOfInt (blockScale R.params.side v)) Yt ωt)
        (translateBonds (siteOfInt (blockScale R.params.side v)) bad) (translateBases v b) =
      translateState (coarseStateOf R C F Yt ωt bad b) (siteOfInt v) := by
  classical
  refine coarseState_ext_of_labelAt _ _ (coarseHull_translate R.range R.nextRange v bad Yt C) fun y => ?_
  rw [markAt_translateState, markAt_coarseStateOf, markAt_coarseStateOf, storedBlocks_translate]
  by_cases hy : y + siteOfInt v ∈ storedBlocks R.params.side R.range bad Yt C
  · have hy' : y ∈ translateSet (siteOfInt v) (storedBlocks R.params.side R.range bad Yt C) :=
      mem_translateSet_iff.mpr hy
    rw [if_pos hy, if_pos hy', blockConfigAt_translate]
  · have hy' : y ∉ translateSet (siteOfInt v) (storedBlocks R.params.side R.range bad Yt C) :=
      fun h => hy (mem_translateSet_iff.mp h)
    rw [if_neg hy, if_neg hy']
end StatesOfCases
section HaarIntegrals
private theorem lintegral_pi_comp_equiv {ι κ X : Type} [Fintype ι] [Fintype κ] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (e : ι ≃ κ) (f : (ι → X) → ENNReal) :
    ∫⁻ a, f (fun i => a (e i)) ∂(Measure.pi fun _ : κ => μ) = ∫⁻ b, f b ∂(Measure.pi fun _ : ι => μ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.lintegral_pi_comp_equiv <;> assumption
private theorem lintegral_fieldHaar_translate {m : ℕ} [NeZero m] (a : TorusSite m) (f : TorusField m → ENNReal) :
    ∫⁻ W, f (TorusFields.translate a W) ∂(fieldHaar m) = ∫⁻ W, f W ∂(fieldHaar m) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.lintegral_translate <;> assumption
end HaarIntegrals
section Mass
variable {R : StepSetup} {n : ℕ} [NeZero n]
open Classical in
private theorem stateTerm_translate (hR : R.IsWellPosed) (hK : BaseTranslations.TranslationPreservesBaseKernel)
    (hn : R.params.n₀ ≤ n) (v : Fin 4 → ℤ) (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n)
    (hfr : ∀ c ∈ markedBonds R C,
      frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt v) V)
      (c.1 - siteOfInt (blockScale R.params.side v), c.2) =
        frameCoord R.params R.anchorRadius R.depth R.frameReach V c) :
    (∫⁻ W, ∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
      (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
          coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
        ENNReal.ofReal (stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) else 0)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))) =
    ∫⁻ W, ∫⁻ ν : (translateState q (siteOfInt v)).unlabelled
        (translateSet (siteOfInt (blockScale R.params.side v)) Yt) → R.labels.Ω,
      (if IsHullState R.params R.range ((translateState q (siteOfInt v)).fieldWithStoredLinks W)
            (translateSet (siteOfInt (blockScale R.params.side v)) Yt) ∧
          coarseStateOf R (translateSet (siteOfInt v) C) ((translateState q (siteOfInt v)).fieldWithStoredLinks W)
            (translateSet (siteOfInt (blockScale R.params.side v)) Yt)
            ((translateState q (siteOfInt v)).fillLabels (translateSet (siteOfInt (blockScale R.params.side v)) Yt) ν)
            (translateBonds (siteOfInt (blockScale R.params.side v)) bad) (translateBases v b) =
            translateState q (siteOfInt v) then
        ENNReal.ofReal (stepWeight R (translateSet (siteOfInt v) C) (TorusFields.translate (siteOfInt v) V)
          ((translateState q (siteOfInt v)).fieldWithStoredLinks W)
          (translateSet (siteOfInt (blockScale R.params.side v)) Yt)
          ((translateState q (siteOfInt v)).fillLabels (translateSet (siteOfInt (blockScale R.params.side v)) Yt) ν)
          (translateBonds (siteOfInt (blockScale R.params.side v)) bad) (translateBases v b)) else 0)
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  symm
  rw [← lintegral_fieldHaar_translate (siteOfInt (blockScale R.params.side v))]
  refine lintegral_congr fun W => ?_
  rw [← lintegral_pi_comp_equiv R.labels.μ (unlabelledEquiv q v Yt)]
  refine lintegral_congr fun ν => ?_
  have hLm : R.params.side ∣ n * R.params.side := Dvd.intro_left _ rfl
  rw [fieldWithStoredLinks_translateState, fillLabels_translateState, coarseStateOf_translate,
    isHullState_translate_iff hR.admissible hLm]
  by_cases h : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q
  · have h' : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
        translateState (coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) (siteOfInt v) =
          translateState q (siteOfInt v) :=
      ⟨h.1, by rw [h.2]⟩
    rw [if_pos h, if_pos h', stepWeight_translate hR hK hn v C V _ Yt _ bad b h.1 hfr]
  · have h' : ¬ (IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
        translateState (coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) (siteOfInt v) =
          translateState q (siteOfInt v)) :=
      fun c => h ⟨c.1, translateState_injective _ c.2⟩
    rw [if_neg h, if_neg h']
private theorem coarseStateMass_translate (hR : R.IsWellPosed) (hK : BaseTranslations.TranslationPreservesBaseKernel)
    (hn : R.params.n₀ ≤ n) (v : Fin 4 → ℤ) (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (hfr : ∀ c ∈ markedBonds R C,
      frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt v) V)
      (c.1 - siteOfInt (blockScale R.params.side v), c.2) =
        frameCoord R.params R.anchorRadius R.depth R.frameReach V c) :
    coarseStateMass R (translateSet (siteOfInt v) C) (TorusFields.translate (siteOfInt v) V) (translateState q (siteOfInt v)) =
      coarseStateMass R C V q := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.coarseStateMass_translate <;> assumption
private theorem integral_pi_comp_equiv {ι κ X : Type} [Fintype ι] [Fintype κ] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (e : ι ≃ κ) (f : (ι → X) → ℝ) :
    ∫ a, f (fun i => a (e i)) ∂(Measure.pi fun _ : κ => μ) = ∫ b, f b ∂(Measure.pi fun _ : ι => μ) := by
  let E : (κ → X) ≃ᵐ (ι → X) :=
    { toFun := fun a i => a (e i)
      invFun := fun b k => b (e.symm k)
      left_inv := fun a => by funext k; simp
      right_inv := fun b => by funext i; simp
      measurable_toFun := measurable_pi_lambda _ fun i => measurable_pi_apply _
      measurable_invFun := measurable_pi_lambda _ fun i => measurable_pi_apply _ }
  exact (measurePreserving_comp_equiv μ e).integral_comp E.measurableEmbedding f
private theorem integral_fieldHaar_translate {m : ℕ} [NeZero m] (a : TorusSite m) (f : TorusField m → ℝ) :
    ∫ W, f (TorusFields.translate a W) ∂(fieldHaar m) = ∫ W, f W ∂(fieldHaar m) := by
  unfold fieldHaar
  exact integral_pi_comp_equiv (Measure.pi fun _ : Fin 4 => haarUnit) (Equiv.addRight a) f
private theorem caseTermIntegral_translate (hR : R.IsWellPosed) (hK : BaseTranslations.TranslationPreservesBaseKernel)
    (hn : R.params.n₀ ≤ n) (v : Fin 4 → ℤ) (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n)
    (hfr : ∀ c ∈ markedBonds R C,
      frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt v) V)
      (c.1 - siteOfInt (blockScale R.params.side v), c.2) =
        frameCoord R.params R.anchorRadius R.depth R.frameReach V c)
    (Fn Fn' : CaseFunction R n)
    (hFF : ∀ (W : TorusField (n * R.params.side)) (Yt' : Finset (TorusSite (n * R.params.side)))
      (ωt : Yt' → R.labels.Ω) (bad' : Finset (TorusBond (n * R.params.side))) (b' : BaseChoice R.params.side n),
      IsLiveState R.params R.coupling R.labelWeight W Yt' ωt →
      b' ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) →
      Fn' (TorusFields.translate (siteOfInt (blockScale R.params.side v)) W)
        (translateSet (siteOfInt (blockScale R.params.side v)) Yt')
        (translateLabel (siteOfInt (blockScale R.params.side v)) Yt' ωt)
        (translateBonds (siteOfInt (blockScale R.params.side v)) bad') (translateBases v b') = Fn W Yt' ωt bad' b') :
    (∫ W, ∫ ν : q.unlabelled Yt → R.labels.Ω, caseTerm R C V q Fn bad Yt b W ν
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side))) =
    ∫ W, ∫ ν : (translateState q (siteOfInt v)).unlabelled
        (translateSet (siteOfInt (blockScale R.params.side v)) Yt) → R.labels.Ω,
      caseTerm R (translateSet (siteOfInt v) C) (TorusFields.translate (siteOfInt v) V) (translateState q (siteOfInt v)) Fn'
        (translateBonds (siteOfInt (blockScale R.params.side v)) bad)
        (translateSet (siteOfInt (blockScale R.params.side v)) Yt) (translateBases v b) W ν
      ∂(Measure.pi fun _ => R.labels.μ) ∂(fieldHaar (n * R.params.side)) := by
  classical
  symm
  rw [← integral_fieldHaar_translate (siteOfInt (blockScale R.params.side v))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  beta_reduce
  rw [← integral_pi_comp_equiv R.labels.μ (unlabelledEquiv q v Yt)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ν => ?_)
  beta_reduce
  have hLm : R.params.side ∣ n * R.params.side := Dvd.intro_left _ rfl
  unfold caseTerm
  rw [fieldWithStoredLinks_translateState, fillLabels_translateState, coarseStateOf_translate,
    isHullState_translate_iff hR.admissible hLm]
  by_cases h : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q
  · have h' : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
        translateState (coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) (siteOfInt v) =
          translateState q (siteOfInt v) :=
      ⟨h.1, by rw [h.2]⟩
    rw [if_pos h, if_pos h', stepWeight_translate hR hK hn v C V _ Yt _ bad b h.1 hfr]
    by_cases hw : stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = 0
    · rw [hw, mul_zero, mul_zero]
    · have hside : IsBlockTorusSide R.params (n * R.params.side) :=
        ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
      have hlive : IsLiveState R.params R.coupling R.labelWeight (q.fieldWithStoredLinks W) Yt
          (q.fillLabels Yt ν) := by
        refine ⟨h.1, lt_of_le_of_ne (hR.hasExpansions.2.nonneg _ hside _ _ _ h.1) fun h0 => hw ?_⟩
        unfold stepWeight
        rw [← h0]
        ring
      have hb : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 (q.fieldWithStoredLinks W)) := by
        by_contra hb
        apply hw
        unfold stepWeight baseLaw
        rw [if_neg hb]
        ring
      rw [hFF _ Yt _ bad b hlive hb]
  · have h' : ¬ (IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
        translateState (coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) (siteOfInt v) =
          translateState q (siteOfInt v)) :=
      fun c => h ⟨c.1, translateState_injective _ c.2⟩
    rw [if_neg h, if_neg h']
theorem caseIntegral_translate (hR : R.IsWellPosed) (hK : BaseTranslations.TranslationPreservesBaseKernel)
    (hn : R.params.n₀ ≤ n) (v : Fin 4 → ℤ) (C : Finset (TorusSite n)) (V : TorusField n) (q : CoarseState R n)
    (hfr : ∀ c ∈ markedBonds R C,
      frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt v) V)
      (c.1 - siteOfInt (blockScale R.params.side v), c.2) =
        frameCoord R.params R.anchorRadius R.depth R.frameReach V c)
    (Fn Fn' : CaseFunction R n)
    (hFF : ∀ (W : TorusField (n * R.params.side)) (Yt' : Finset (TorusSite (n * R.params.side)))
      (ωt : Yt' → R.labels.Ω) (bad' : Finset (TorusBond (n * R.params.side))) (b' : BaseChoice R.params.side n),
      IsLiveState R.params R.coupling R.labelWeight W Yt' ωt →
      b' ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W) →
      Fn' (TorusFields.translate (siteOfInt (blockScale R.params.side v)) W)
        (translateSet (siteOfInt (blockScale R.params.side v)) Yt')
        (translateLabel (siteOfInt (blockScale R.params.side v)) Yt' ωt)
        (translateBonds (siteOfInt (blockScale R.params.side v)) bad') (translateBases v b') = Fn W Yt' ωt bad' b') :
    caseIntegral R (translateSet (siteOfInt v) C) (TorusFields.translate (siteOfInt v) V) (translateState q (siteOfInt v)) Fn' =
      caseIntegral R C V q Fn := by
  classical
  have hfit := hR.admissible
  have hn2 : 2 ≤ n := by
    have := hfit.n₀_ge
    omega
  symm
  unfold caseIntegral
  rw [markedBonds_translateSet hfit.L_odd hn2]
  refine Finset.sum_nbij' (translateBonds (siteOfInt (blockScale R.params.side v)))
    (translateBonds (-siteOfInt (blockScale R.params.side v))) ?_ ?_ ?_ ?_ ?_
  · intro B hB
    refine Finset.mem_powerset.mpr fun c hc => ?_
    exact mem_translateBonds_iff.mpr (Finset.mem_powerset.mp hB (mem_translateBonds_iff.mp hc))
  · intro B hB
    refine Finset.mem_powerset.mpr fun c hc => ?_
    have := mem_translateBonds_iff.mp (Finset.mem_powerset.mp hB (mem_translateBonds_iff.mp hc))
    simpa using this
  · exact fun B _ => translateBonds_neg_translateBonds _ B
  · exact fun B _ => translateBonds_translateBonds_neg _ B
  · intro bad _
    refine Fintype.sum_equiv (translateSetEquiv (siteOfInt (blockScale R.params.side v))) _ _ fun Yt => ?_
    refine Fintype.sum_equiv (translateBasesEquiv v) _ _ fun b => ?_
    exact caseTermIntegral_translate hR hK hn v C V q bad Yt b hfr Fn Fn' hFF
end Mass
section BlockMeans
private theorem plaquetteVertices_add {n : ℕ} (a : TorusSite n) (p : TorusPlaquette n) :
    plaquetteVertices (p.1 + a) p.2.1 p.2.2 = (plaquetteVertices p.1 p.2.1 p.2.2).map (· + a) := by
  have h1 : ∀ x e : TorusSite n, x + a + e = x + e + a := fun x e => add_right_comm _ _ _
  simp only [plaquetteVertices, List.map_cons, List.map_nil, h1]
private theorem vertexMultiplicity_add_add {n : ℕ} (a y : TorusSite n) (p : TorusPlaquette n) :
    vertexMultiplicity (y + a) (p.1 + a, p.2) = vertexMultiplicity y p := by
  unfold vertexMultiplicity
  show (((plaquetteVertices (p.1 + a) p.2.1 p.2.2).count (y + a) : ℕ) : ℝ) = _
  rw [plaquetteVertices_add, List.count_map_of_injective _ _ (add_left_injective a)]
private theorem sum_sitesInBlocks_translate {n L : ℕ} [NeZero n] [NeZero L] (u : Fin 4 → ℤ) (Y : TorusSite n)
    (f : TorusSite (n * L) → ℝ) :
    ∑ z ∈ sitesInBlocks L {Y}, f (z + siteOfInt (blockScale L u)) = ∑ z ∈ sitesInBlocks L {Y + siteOfInt u}, f z := by
  refine Finset.sum_nbij' (· + siteOfInt (blockScale L u)) (· - siteOfInt (blockScale L u)) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [mem_sitesInBlocks_iff] at hz ⊢
    rw [parentBlock_add_siteOfInt, Finset.mem_singleton.mp hz]
    exact Finset.mem_singleton_self _
  · intro z hz
    rw [mem_sitesInBlocks_iff] at hz ⊢
    have h1 := parentBlock_add_siteOfInt (L := L) (z - siteOfInt (blockScale L u)) u
    rw [sub_add_cancel, Finset.mem_singleton.mp hz] at h1
    exact Finset.mem_singleton.mpr (add_right_cancel h1).symm
  · intro z _
    simp
  · intro z _
    simp
  · intro z _
    rfl
private theorem fineTranslate_succ (L t n : ℕ) (u : Fin 4 → ℤ) :
    (fineTranslate L (t + 1) n u : TorusSite (fineSide L t (n * L))) = fineTranslate L t (n * L) (blockScale L u) := by
  show (siteOfInt (fun i => (L : ℤ) ^ (t + 1) * u i) : TorusSite (fineSide L t (n * L))) =
    siteOfInt fun i => (L : ℤ) ^ t * ((L : ℤ) * u i)
  congr 1
  funext i
  ring
private theorem sum_vertexMultiplicity_translate {n : ℕ} [NeZero n] (a y : TorusSite n) (h : TorusPlaquette n → ℝ) :
    ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * h (p.1 + a, p.2) =
      ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity (y + a) p * h p := by
  refine Finset.sum_nbij' (fun p => (p.1 + a, p.2)) (fun p => (p.1 - a, p.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa [plaquettesIn] using hp
  · intro p hp
    simpa [plaquettesIn] using hp
  · intro p _
    exact Prod.ext (add_sub_cancel_right _ _) rfl
  · intro p _
    exact Prod.ext (sub_add_cancel _ _) rfl
  · intro p _
    show vertexMultiplicity y p * _ = vertexMultiplicity (y + a) (p.1 + a, p.2) * _
    rw [vertexMultiplicity_add_add]
private theorem blockMean_translateWeight (L : ℕ) [NeZero L] : ∀ (t n : ℕ) [NeZero n] (y : TorusSite n)
    (u : Fin 4 → ℤ) (h : PlaquetteWeight (fineSide L t n)),
    blockMean L t n y (translateWeight (fineTranslate L t n u) h) = blockMean L t n (y + siteOfInt u) h
  | 0, n, _, y, u, h => by
    have e : (fineTranslate L 0 n u : TorusSite n) = siteOfInt u := by
      funext j
      show (((L : ℤ) ^ 0 * u j : ℤ) : ZMod n) = ((u j : ℤ) : ZMod n)
      simp
    have e2 : (translateWeight (fineTranslate L 0 n u) h : PlaquetteWeight n) = translateWeight (siteOfInt u) h := by
      funext p
      have e3 : ∀ w : TorusSite n, w = siteOfInt u → h (p.1 + w, p.2) = h (p.1 + siteOfInt u, p.2) := fun w hw => by
        subst hw
        rfl
      exact e3 _ e
    have e4 : blockMean L 0 n y (translateWeight (fineTranslate L 0 n u) h) =
        blockMean L 0 n y (translateWeight (siteOfInt u) h : PlaquetteWeight n) :=
      congrArg _ e2
    rw [e4]
    show (1 / 24) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * h (p.1 + siteOfInt u, p.2) =
      (1 / 24) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity (y + siteOfInt u) p * h p
    exact congrArg (fun r : ℝ => (1 / 24) * r) (sum_vertexMultiplicity_translate (siteOfInt u) y h)
  | t + 1, n, _, Y, u, h => by
    have e : ∀ z : TorusSite (n * L), blockMean L t (n * L) z (translateWeight (fineTranslate L (t + 1) n u) h) =
        blockMean L t (n * L) (z + siteOfInt (blockScale L u)) h := fun z => by
      rw [fineTranslate_succ]
      exact blockMean_translateWeight L t (n * L) z (blockScale L u) h
    show ((L : ℝ) ^ 4)⁻¹ * ∑ z ∈ sitesInBlocks L {Y},
        blockMean L t (n * L) z (translateWeight (fineTranslate L (t + 1) n u) h) =
      ((L : ℝ) ^ 4)⁻¹ * ∑ z ∈ sitesInBlocks L {Y + siteOfInt u}, blockMean L t (n * L) z h
    rw [Finset.sum_congr rfl fun z _ => e z, sum_sitesInBlocks_translate u Y fun z => blockMean L t (n * L) z h]
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem blockBondScores_translate (hsc : BondScores.BondScoreTranslationInvariant)
    (hfit : R.params.Admissible) (hn : R.params.n₀ ≤ n) (u : Fin 4 → ℤ) (W : TorusField (n * R.params.side))
    (V : TorusField n) (b : BaseChoice R.params.side n) (y : TorusSite n)
    (hb : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)) :
    blockBondScores (R := R) (TorusFields.translate (siteOfInt (blockScale R.params.side u)) W)
        (TorusFields.translate (siteOfInt u) V)
        (translateBases u b) y =
      blockBondScores (R := R) W V b (y + siteOfInt u) := by
  unfold blockBondScores
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := hsc R.params hfit R.coupling n hn u W V b (y + siteOfInt u, i) hb
  have h2 := hsc R.params hfit R.coupling n hn u W V b (y + siteOfInt u - TorusFields.unitStep n i, i) hb
  have e1 : y + siteOfInt u - siteOfInt u = y := add_sub_cancel_right _ _
  have e2 : y + siteOfInt u - TorusFields.unitStep n i - siteOfInt u = y - TorusFields.unitStep n i := by abel
  simp only [e1] at h1
  simp only [e2] at h2
  rw [h1, h2]
private theorem caseResponse_translate (hsc : BondScores.BondScoreTranslationInvariant) (hfit : R.params.Admissible)
    {A : ResponseSetup R} (hA : A.IsAdmissible) (hn : R.params.n₀ ≤ n) (u : Fin 4 → ℤ) (V : TorusField n)
    (y : TorusSite n) (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt)
    (hb : b ∈ baseChoices R.params (readAtLevel (stepBlockFrame R.params.side n) 0 W)) :
    caseResponse A (TorusFields.translate (siteOfInt u) V) y
        (translateWeight (fineTranslate R.params.side (R.depth + 1) n u) h)
        (TorusFields.translate (siteOfInt (blockScale R.params.side u)) W) (translateSet (siteOfInt (blockScale R.params.side u)) Yt)
        (translateLabel (siteOfInt (blockScale R.params.side u)) Yt ωt)
        (translateBonds (siteOfInt (blockScale R.params.side u)) bad) (translateBases u b) =
      caseResponse A V (y + siteOfInt u) h W Yt ωt bad b := by
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have e : ∀ z, A.hull (n * R.params.side) z (TorusFields.translate (siteOfInt (blockScale R.params.side u)) W)
      (translateSet (siteOfInt (blockScale R.params.side u)) Yt)
      (translateLabel (siteOfInt (blockScale R.params.side u)) Yt ωt)
      (translateWeight (fineTranslate R.params.side (R.depth + 1) n u) h) =
      A.hull (n * R.params.side) (z + siteOfInt (blockScale R.params.side u)) W Yt ωt h := fun z => by
    rw [fineTranslate_succ]
    exact hA.bounds.hull_translation (n * R.params.side) hside z u W Yt ωt hl h
  show ∑ z ∈ sitesInBlocks R.params.side {y}, A.hull (n * R.params.side) z
        (TorusFields.translate (siteOfInt (blockScale R.params.side u)) W)
        (translateSet (siteOfInt (blockScale R.params.side u)) Yt)
        (translateLabel (siteOfInt (blockScale R.params.side u)) Yt ωt)
        (translateWeight (fineTranslate R.params.side (R.depth + 1) n u) h) +
      R.params.coupling / 2 * A.coeff *
        blockMean R.params.side (R.depth + 1) n y (translateWeight (fineTranslate R.params.side (R.depth + 1) n u) h) *
        blockBondScores (TorusFields.translate (siteOfInt (blockScale R.params.side u)) W)
          (TorusFields.translate (siteOfInt u) V)
          (translateBases u b) y =
    ∑ z ∈ sitesInBlocks R.params.side {y + siteOfInt u}, A.hull (n * R.params.side) z W Yt ωt h +
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n (y + siteOfInt u) h *
        blockBondScores W V b (y + siteOfInt u)
  rw [Finset.sum_congr rfl fun z _ => e z,
    sum_sitesInBlocks_translate u y fun z => A.hull (n * R.params.side) z W Yt ωt h,
    blockMean_translateWeight R.params.side (R.depth + 1) n y u h, blockBondScores_translate hsc hfit hn u W V b y hb]
end BlockMeans
end StepResponseTranslation
open StepResponseTranslation in
theorem stepResponseTranslationInvariant (hK : BaseTranslations.TranslationPreservesBaseKernel)
    (hFr : StepFrames.FrameCovariance) (hsc : BondScores.BondScoreTranslationInvariant) :
    StepResponseTranslationInvariant := by
  classical
  refine ⟨fun _ => 1, fun _ => one_pos, fun T hT _ K => ⟨0, fun y _ R A _ hAt hS hL => ?_⟩⟩
  have hOn := hAt.onFamily
  have hresp := hAt.admissible
  have hfits := hS.admissible
  have hL0 : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have ha : R.params.coupling = T.coupling := by rw [hOn.params_eq]; rfl
  have hLT : R.params.side = T.side := by rw [hOn.params_eq]; rfl
  have hσ : R.params.threshold = T.threshold := by rw [hOn.params_eq]; rfl
  have hchain : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [ha, hLT, hOn.anchorRadius_eq]
    exact hT.chain
  have hσ2 : 2 * R.params.threshold ≤ T.σA := by rw [hσ]; exact hT.σ_le
  have hfit2 : RangesAdmissible R.range R.nextRange := by
    refine ⟨hS.range_le, hS.nextRange_ge, ?_⟩
    have h3 := hS.range_ge_side
    have h4 := hfits.L_ge
    refine (Nat.le_div_iff_mul_le (by norm_num)).mpr ?_
    calc 16 * 2 ^ 11 ≤ 2 ^ 40 * R.params.side := by nlinarith
      _ ≤ R.range := h3
  refine ⟨fun n _ hn y' v W hc h => ?_, fun n _ hB y' v W Y ω hl h => ?_⟩
  · set u : Fin 4 → ℤ := blockScale R.params.side v with hu
    have hfr : ∀ c ∈ markedBonds R (∅ : Finset (TorusSite n)),
        frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt u) W)
            (c.1 - siteOfInt (blockScale R.params.side u), c.2) =
          frameCoord R.params R.anchorRadius R.depth R.frameReach W c := by
      intro c hc'
      obtain ⟨hc1, hc2⟩ := Finset.mem_filter.mp hc'
      exact (hFr R.params T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N hfits hchain hσ2 R.depth R.range R.nextRange n W
        _ _ _ hfit2 (Or.inr ⟨hn, fun x μ ν h => (hc x μ ν h).trans (by linarith [hfits.σ_pos]), rfl, rfl, rfl⟩)
        c hc1 hc2).2 _
    have hC : translateSet (siteOfInt u) (∅ : Finset (TorusSite n)) = ∅ := by
      ext z
      simp [mem_translateSet_iff]
    have hq : translateState (emptyCoarseState R (n := n)) (siteOfInt u) = emptyCoarseState R := by
      refine coarseState_ext_of_labelAt _ _ ?_ fun y => ?_
      · ext z
        simp [translateState, emptyCoarseState, mem_translateSet_iff]
      · rw [markAt_translateState]
        simp [CoarseState.markAt, emptyCoarseState]
    have key := caseIntegral_translate hS hK hn u ∅ W (emptyCoarseState R) hfr
      (caseResponse A W (y' + siteOfInt u) h)
      (caseResponse A (TorusFields.translate (siteOfInt u) W) y'
        (translateWeight (fineTranslate R.params.side (R.depth + 1) n u) h))
      fun W' Yt ωt bad b hl hb => caseResponse_translate hsc hfits hresp hn u W y' h W' Yt ωt bad b hl hb
    have main2 := coarseStateMass_translate hS hK hn u ∅ W (emptyCoarseState R) hfr
    rw [hq, hC] at key main2
    show caseMean R ∅ (TorusFields.translate (siteOfInt u) W) (emptyCoarseState R)
        (caseResponse A (TorusFields.translate (siteOfInt u) W) y'
          (translateWeight (fineTranslate R.params.side (R.depth + 1) n u) h)) =
      caseMean R ∅ W (emptyCoarseState R) (caseResponse A W (y' + siteOfInt u) h)
    unfold caseMean coarseStateWeight
    rw [key, main2]
  · set u : Fin 4 → ℤ := blockScale R.params.side v with hu
    have hn : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hL0) hB.2
    have hhull : hotCoreSites R (TorusFields.translate (siteOfInt u) W) =
        translateSet (siteOfInt u) (hotCoreSites R W) := by
      unfold hotCoreSites
      rw [torusHotSites_translate hfits hB.1, thickening_translateSet]
    have hfr : ∀ c ∈ markedBonds R (hotCoreSites R W),
        frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt u) W)
            (c.1 - siteOfInt (blockScale R.params.side u), c.2) =
          frameCoord R.params R.anchorRadius R.depth R.frameReach W c := by
      intro c hc
      obtain ⟨hc1, hc2⟩ := Finset.mem_filter.mp hc
      exact (hFr R.params T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N hfits hchain hσ2 R.depth R.range R.nextRange n W
        _ _ _ hfit2 (Or.inl ⟨hB, rfl, rfl, rfl⟩) c hc1 hc2).2 _
    have key := caseIntegral_translate hS hK hn u (hotCoreSites R W) W ⟨Y, ω⟩ hfr
      (caseResponse A W (y' + siteOfInt u) h)
      (caseResponse A (TorusFields.translate (siteOfInt u) W) y'
        (translateWeight (fineTranslate R.params.side (R.depth + 1) n u) h))
      fun W' Yt ωt bad b hl hb => caseResponse_translate hsc hfits hresp hn u W y' h W' Yt ωt bad b hl hb
    have main2 := coarseStateMass_translate hS hK hn u (hotCoreSites R W) W ⟨Y, ω⟩ hfr
    rw [← hhull] at key main2
    show caseMean R (hotCoreSites R (TorusFields.translate (siteOfInt u) W)) (TorusFields.translate (siteOfInt u) W)
        (translateState ⟨Y, ω⟩ (siteOfInt u))
        (caseResponse A (TorusFields.translate (siteOfInt u) W) y'
          (translateWeight (fineTranslate R.params.side (R.depth + 1) n u) h)) =
      caseMean R (hotCoreSites R W) W ⟨Y, ω⟩ (caseResponse A W (y' + siteOfInt u) h)
    unfold caseMean coarseStateWeight
    rw [key, main2]
end YangMills.Construction.WeightedResponses
end
