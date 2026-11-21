import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import YangMills.Construction.CellOfTheFlow.TheCellEventReadsItsCellProof
import YangMills.Construction.CellOfTheFlow.TheLowerSumReadsItsCellProof
import YangMills.Construction.CellOfTheFlow.TheStepDrawHasItsWeight
import YangMills.Construction.CellOfTheFlow.TranslationsCarryTheMeansOfACell
import YangMills.Construction.CellOfTheFlow.TranslationsCarryTheWeightOfADraw
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsAreCarriedProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings RenormalizationStepParameters StepMarks BaseTranslations WeightedResponses BlockAverages ClusterExpansionOfAStep
namespace CellWindows
namespace TranslationCellMeans
section Sets
variable {m : ℕ} [NeZero m]
private theorem mem_translateSet {a z : TorusSite m} {Y : Finset (TorusSite m)} : z ∈ translateSet a Y ↔ z + a ∈ Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.mem_translateSet <;> assumption
private theorem supDist_add_right (a x y : TorusSite m) : supDist (x + a) (y + a) = supDist x y := by
  simp [supDist]
private theorem thickening_translateSet (k : ℕ) (a : TorusSite m) (X : Finset (TorusSite m)) :
    thickening k (translateSet a X) = translateSet a (thickening k X) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.thickening_translateSet <;> assumption
private theorem chainComponents_translateSet (r : ℕ) (a : TorusSite m) (Y : Finset (TorusSite m)) :
    chainComponents r (translateSet a Y) = (chainComponents r Y).image (translateSet a) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.chainComponents_translateSet <;> assumption
private def bondsTranslate (a : TorusSite m) (B : Finset (TorusBond m)) : Finset (TorusBond m) :=
  open Classical in Finset.univ.filter fun c => (c.1 + a, c.2) ∈ B
private theorem mem_bondsTranslate {a : TorusSite m} {B : Finset (TorusBond m)} {c : TorusBond m} :
    c ∈ bondsTranslate a B ↔ (c.1 + a, c.2) ∈ B := by
  classical
  simp [bondsTranslate]
private theorem bondsTranslate_neg_bondsTranslate (a : TorusSite m) (B : Finset (TorusBond m)) :
    bondsTranslate (-a) (bondsTranslate a B) = B := by
  ext c
  simp [mem_bondsTranslate]
end Sets
section Lift
variable {n L : ℕ}
private abbrev scaleBy (L : ℕ) (v : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (L : ℤ) * v i
private theorem exists_cast_add_intCast {m : ℕ} [NeZero m] (x : ZMod m) (z : ℤ) :
    ∃ k : ℤ, (((x + (z : ZMod m) : ZMod m)).cast : ℤ) = (x.cast : ℤ) + z + (m : ℤ) * k := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.exists_cast_add_intCast <;> assumption
private theorem parentBlock_add_scaleBy [NeZero n] [NeZero L] (x : TorusSite (n * L)) (v : Fin 4 → ℤ) :
    parentBlock L (x + siteOfInt (scaleBy L v)) = parentBlock L x + siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.parentBlock_add_scale <;> assumption
private theorem siteOfInt_neg {m : ℕ} (v : Fin 4 → ℤ) : (siteOfInt (-v) : TorusSite m) = - siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.siteOfInt_neg <;> assumption
end Lift
section Clusters
variable {n L : ℕ} [NeZero n] [NeZero L]
private theorem mem_sitesInBlocks {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.mem_sitesInBlocks <;> assumption
private theorem sitesInBlocks_translateSet (v : Fin 4 → ℤ) (S : Finset (TorusSite n)) :
    sitesInBlocks L (translateSet (siteOfInt v) S) = translateSet (siteOfInt (scaleBy L v)) (sitesInBlocks L S) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.sitesInBlocks_translateSet <;> assumption
private theorem translateSet_inter_nonempty_iff {m : ℕ} [NeZero m] (a : TorusSite m) (X Y : Finset (TorusSite m)) :
    (open Classical in (translateSet a X ∩ translateSet a Y).Nonempty) ↔ (open Classical in (X ∩ Y).Nonempty) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translateSet_inter_nonempty <;> assumption
variable (r r' : ℕ) (v : Fin 4 → ℤ) (bad : Finset (TorusBond (n * L))) (Yt : Finset (TorusSite (n * L)))
  (C : Finset (TorusSite n))
private theorem coreBlocks_translateSet (θ : Finset (TorusSite (n * L))) :
    coreBlocks L r (translateSet (siteOfInt (scaleBy L v)) θ) = translateSet (siteOfInt v) (coreBlocks L r θ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.coreBlocks_translateSet <;> assumption
end Clusters
section Hot
variable {ℓ : StepParameters} {m : ℕ} [NeZero m]
private theorem curvature_translate_apply (a : TorusSite m) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    curvature (TorusFields.translate a W) x μ ν = curvature W (x + a) μ ν := by
  simp only [curvature, holonomy, TorusFields.translate, add_right_comm x a]
private theorem mem_plaquetteVertices_add (a : TorusSite m) (x z : TorusSite m) (μ ν : Fin 4) :
    z ∈ plaquetteVertices x μ ν ↔ z + a ∈ plaquetteVertices (x + a) μ ν := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.mem_plaquetteVertices_add <;> assumption
private theorem torusHotLumps_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (W : TorusField m) :
    torusHotLumps ℓ (TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) W) =
      (torusHotLumps ℓ W).image (translateSet (siteOfInt (scaleBy ℓ.side w))) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusHotLumps_translate <;> assumption
private theorem torusHotSites_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (W : TorusField m) :
    torusHotSites ℓ (TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) W) =
      translateSet (siteOfInt (scaleBy ℓ.side w)) (torusHotSites ℓ W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusHotSites_translate <;> assumption
private theorem translate_neg_translate (a : TorusSite m) (W : TorusField m) : TorusFields.translate (-a) (TorusFields.translate a W) = W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translate_neg_translate <;> assumption
end Hot
section Bases
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem translateBases_neg_translateBases (v : Fin 4 → ℤ) (b : StepCosts.BaseChoice L n) :
    translateBases (-v) (translateBases v b) = b := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translateBases_neg_translateBases <;> assumption
private def translateBasesEquiv (v : Fin 4 → ℤ) : StepCosts.BaseChoice L n ≃ StepCosts.BaseChoice L n where
  toFun := translateBases v
  invFun := translateBases (-v)
  left_inv := translateBases_neg_translateBases v
  right_inv b := by simpa using translateBases_neg_translateBases (-v) b
end Bases
section Integrals
private theorem lintegral_fieldHaar_translate {m : ℕ} [NeZero m] (a : TorusSite m) (f : TorusField m → ENNReal) :
    ∫⁻ W, f (TorusFields.translate a W) ∂(fieldHaar m) = ∫⁻ W, f W ∂(fieldHaar m) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.lintegral_translate <;> assumption
end Integrals
section Windows
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem interiorAtDepth_translateSet (k : ℕ) (a : TorusSite n) (c : Finset (TorusSite n)) :
    interiorAtDepth k (translateSet a c) = translateSet a (interiorAtDepth k c) := by
  classical
  ext z
  rw [mem_translateSet]
  simp only [interiorAtDepth, Finset.mem_filter, mem_translateSet]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h w hw
    have h1 := h (w - a) (by simpa using hw)
    rwa [← supDist_add_right a z (w - a), sub_add_cancel] at h1
  · intro h w hw
    have h1 := h (w + a) hw
    rwa [supDist_add_right] at h1
private theorem exists_fst_bondsTranslate_iff {m : ℕ} [NeZero m] (a : TorusSite m) (B : Finset (TorusBond m))
    (z : TorusSite m) : (∃ b ∈ bondsTranslate a B, b.1 = z) ↔ ∃ b ∈ B, b.1 = z + a := by
  constructor
  · rintro ⟨⟨x, i⟩, hb, rfl⟩
    exact ⟨_, mem_bondsTranslate.mp hb, rfl⟩
  · rintro ⟨⟨x, i⟩, hb, h⟩
    simp only at h
    subst h
    exact ⟨(z, i), mem_bondsTranslate.mpr hb, rfl⟩
variable (v : Fin 4 → ℤ)
private theorem windowSeeds_translateSet (bad : Finset (TorusBond (n * L))) (Yw Rw : Finset (TorusSite (n * L)))
    (C : Finset (TorusSite n)) :
    windowSeeds L (bondsTranslate (siteOfInt (scaleBy L v)) bad) (translateSet (siteOfInt (scaleBy L v)) Yw)
        (translateSet (siteOfInt v) C) (translateSet (siteOfInt (scaleBy L v)) Rw) =
      translateSet (siteOfInt (scaleBy L v)) (windowSeeds L bad Yw C Rw) := by
  classical
  ext z
  rw [mem_translateSet]
  simp only [windowSeeds, Finset.mem_inter, Finset.mem_union, Finset.mem_image, exists_fst_bondsTranslate_iff,
    mem_sitesInBlocks, mem_translateSet, parentBlock_add_scaleBy]
private theorem lowerAttached_translateSet (r : ℕ) (X LC : Finset (TorusSite (n * L))) :
    lowerAttached L r (translateSet (siteOfInt (scaleBy L v)) X) (translateSet (siteOfInt (scaleBy L v)) LC) =
      translateSet (siteOfInt (scaleBy L v)) (lowerAttached (n := n) L r X LC) := by
  classical
  ext z
  rw [mem_translateSet]
  simp only [lowerAttached, Finset.mem_biUnion, Finset.mem_filter, id, chainComponents_translateSet, Finset.mem_image]
  constructor
  · rintro ⟨X', ⟨⟨K, hK, rfl⟩, hn⟩, hz⟩
    exact ⟨K, ⟨hK, (translateSet_inter_nonempty_iff _ _ _).mp (by convert hn)⟩, mem_translateSet.mp hz⟩
  · rintro ⟨K, ⟨hK, hn⟩, hz⟩
    exact ⟨_, ⟨⟨K, hK, rfl⟩,
      by convert (translateSet_inter_nonempty_iff (siteOfInt (scaleBy L v)) K LC).mpr (by convert hn)⟩,
      mem_translateSet.mpr hz⟩
private theorem exists_far_translateSet_iff {m : ℕ} [NeZero m] (a : TorusSite m) (K Rw : Finset (TorusSite m)) (d : ℕ) :
    (∃ u ∈ translateSet a K, ∃ w, w ∉ translateSet a Rw ∧ supDist u w ≤ d) ↔
      ∃ u ∈ K, ∃ w, w ∉ Rw ∧ supDist u w ≤ d := by
  constructor
  · rintro ⟨u, hu, w, hw, h⟩
    refine ⟨u + a, mem_translateSet.mp hu, w + a, fun hc => hw (mem_translateSet.mpr hc), ?_⟩
    rwa [supDist_add_right]
  · rintro ⟨u, hu, w, hw, h⟩
    refine ⟨u - a, mem_translateSet.mpr (by simpa using hu), w - a,
      fun hc => hw (by simpa using mem_translateSet.mp hc), ?_⟩
    rwa [← supDist_add_right a, sub_add_cancel, sub_add_cancel]
private theorem upperAttached_translateSet (r : ℕ) (X LC Rw : Finset (TorusSite (n * L))) :
    upperAttached L r (translateSet (siteOfInt (scaleBy L v)) X) (translateSet (siteOfInt (scaleBy L v)) LC)
        (translateSet (siteOfInt (scaleBy L v)) Rw) =
      translateSet (siteOfInt (scaleBy L v)) (upperAttached (n := n) L r X LC Rw) := by
  classical
  ext z
  rw [mem_translateSet]
  simp only [upperAttached, Finset.mem_biUnion, Finset.mem_filter, id, chainComponents_translateSet, Finset.mem_image]
  constructor
  · rintro ⟨X', ⟨⟨K, hK, rfl⟩, hn⟩, hz⟩
    refine ⟨K, ⟨hK, ?_⟩, mem_translateSet.mp hz⟩
    rcases hn with hn | hn
    · exact Or.inl ((translateSet_inter_nonempty_iff _ _ _).mp (by convert hn))
    · exact Or.inr ((exists_far_translateSet_iff _ _ _ _).mp hn)
  · rintro ⟨K, ⟨hK, hn⟩, hz⟩
    refine ⟨_, ⟨⟨K, hK, rfl⟩, ?_⟩, mem_translateSet.mpr hz⟩
    rcases hn with hn | hn
    · exact Or.inl (by convert (translateSet_inter_nonempty_iff (siteOfInt (scaleBy L v)) K LC).mpr (by convert hn))
    · exact Or.inr ((exists_far_translateSet_iff _ _ _ _).mpr hn)
private theorem windowZone_translateSet (r : ℕ) (θ : Finset (TorusSite (n * L))) (C D : Finset (TorusSite n)) :
    windowZone L r (translateSet (siteOfInt (scaleBy L v)) θ) (translateSet (siteOfInt v) C)
        (translateSet (siteOfInt v) D) =
      translateSet (siteOfInt v) (windowZone L r θ C D) := by
  classical
  unfold windowZone
  rw [coreBlocks_translateSet]
  ext z
  simp [mem_translateSet]
end Windows
section Moves
variable {ℓ : StepParameters}
private theorem translateBonds_eq_bondsTranslate {m : ℕ} [NeZero m] (a : TorusSite m) (B : Finset (TorusBond m)) :
    translateBonds a B = bondsTranslate a B := by
  classical
  ext ⟨x, i⟩
  rw [mem_bondsTranslate]
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
private def translateSample : (s n : ℕ) → [NeZero n] → (Fin 4 → ℤ) → MarkedSample ℓ s n → MarkedSample ℓ s n
  | 0, _, _, v, W => TorusFields.translate (siteOfInt v) W
  | s + 1, n, _, v, u => (translateSample s (n * ℓ.side) (scaleBy ℓ.side v) u.1, translateOutcome v u.2)
private theorem topField_translateSample (s n : ℕ) [NeZero n] (v : Fin 4 → ℤ) (u : MarkedSample ℓ s n) :
    topField ℓ s n (translateSample s n v u) = TorusFields.translate (siteOfInt v) (topField ℓ s n u) := by
  cases s <;> rfl
private theorem hotCoreSites_translate (hfit : ℓ.Admissible) (R : StepSetup) (hR : R.params = ℓ) {n : ℕ} [NeZero n]
    (hL : R.params.side ∣ n) (w : Fin 4 → ℤ) (V : TorusField n) :
    hotCoreSites R (TorusFields.translate (siteOfInt (scaleBy R.params.side w)) V) =
      translateSet (siteOfInt (scaleBy R.params.side w)) (hotCoreSites R V) := by
  subst hR
  unfold hotCoreSites
  rw [torusHotSites_translate hfit hL, thickening_translateSet]
variable (T : StageTower ℓ) (k : ℕ)
private theorem upperZone_translateSet (s : ℕ) {n : ℕ} [NeZero n] (v : Fin 4 → ℤ) (C : Finset (TorusSite n))
    (bad : Finset (TorusBond (n * ℓ.side))) (Yw : Finset (TorusSite (n * ℓ.side))) (c : Finset (TorusSite n)) :
    upperZone T k s (translateSet (siteOfInt v) C) (bondsTranslate (siteOfInt (scaleBy ℓ.side v)) bad)
        (translateSet (siteOfInt (scaleBy ℓ.side v)) Yw) (translateSet (siteOfInt v) c) =
      translateSet (siteOfInt v) (upperZone T k s C bad Yw c) := by
  unfold upperZone
  rw [interiorAtDepth_translateSet, sitesInBlocks_translateSet, windowSeeds_translateSet, sitesInBlocks_translateSet,
    upperAttached_translateSet, windowZone_translateSet]
private theorem lowerZone_translateSet (s : ℕ) {n : ℕ} [NeZero n] (v : Fin 4 → ℤ) (C : Finset (TorusSite n))
    (bad : Finset (TorusBond (n * ℓ.side))) (Yw : Finset (TorusSite (n * ℓ.side))) (c : Finset (TorusSite n)) :
    lowerZone T k s (translateSet (siteOfInt v) C) (bondsTranslate (siteOfInt (scaleBy ℓ.side v)) bad)
        (translateSet (siteOfInt (scaleBy ℓ.side v)) Yw) (translateSet (siteOfInt v) c) =
      translateSet (siteOfInt v) (lowerZone T k s C bad Yw c) := by
  unfold lowerZone
  rw [interiorAtDepth_translateSet, sitesInBlocks_translateSet, windowSeeds_translateSet, sitesInBlocks_translateSet,
    lowerAttached_translateSet, windowZone_translateSet]
private theorem hotCoreSites_stage_translate (hfit : ℓ.Admissible) (s : ℕ) {n : ℕ} [NeZero n] (hL : ℓ.side ∣ n)
    (w : Fin 4 → ℤ) (V : TorusField n) :
    hotCoreSites (T.stage s).toStepSetup (TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) V) =
      translateSet (siteOfInt (scaleBy ℓ.side w)) (hotCoreSites (T.stage s).toStepSetup V) :=
  hotCoreSites_translate hfit (T.stage s).toStepSetup rfl hL w V
private theorem upperZone_translate_step (hfit : ℓ.Admissible) (s : ℕ) {n : ℕ} [NeZero n] (hL : ℓ.side ∣ n)
    (w : Fin 4 → ℤ) (V : TorusField n) (bad : Finset (TorusBond (n * ℓ.side))) (Y' Y : Finset (TorusSite (n * ℓ.side)))
    (c : Finset (TorusSite n)) (h : Y' = translateSet (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) Y) :
    upperZone T k s (hotCoreSites (T.stage s).toStepSetup (TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) V))
        (translateBonds (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) bad) Y'
        (translateSet (siteOfInt (scaleBy ℓ.side w)) c) =
      translateSet (siteOfInt (scaleBy ℓ.side w)) (upperZone T k s (hotCoreSites (T.stage s).toStepSetup V) bad Y c) := by
  subst h
  rw [translateBonds_eq_bondsTranslate, hotCoreSites_stage_translate T hfit s hL, upperZone_translateSet]
private theorem upperHull_translate_step (hfit : ℓ.Admissible) (s : ℕ) {n : ℕ} [NeZero n] (hL : ℓ.side ∣ n)
    (w : Fin 4 → ℤ) (V : TorusField n) (bad : Finset (TorusBond (n * ℓ.side))) (Y' Y : Finset (TorusSite (n * ℓ.side)))
    (c : Finset (TorusSite n)) (d m : ℕ) (h : Y' = translateSet (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) Y) :
    interiorAtDepth d (translateSet (siteOfInt (scaleBy ℓ.side w)) c) ∩ thickening m (upperZone T k s
        (hotCoreSites (T.stage s).toStepSetup (TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) V))
        (translateBonds (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) bad) Y'
        (translateSet (siteOfInt (scaleBy ℓ.side w)) c)) =
      translateSet (siteOfInt (scaleBy ℓ.side w)) (interiorAtDepth d c ∩
        thickening m (upperZone T k s (hotCoreSites (T.stage s).toStepSetup V) bad Y c)) := by
  rw [upperZone_translate_step T k hfit s hL w V bad Y' Y c h, thickening_translateSet, interiorAtDepth_translateSet]
  ext z
  simp only [Finset.mem_inter, mem_translateSet]
private theorem lowerZone_translate_step (hfit : ℓ.Admissible) (s : ℕ) {n : ℕ} [NeZero n] (hL : ℓ.side ∣ n)
    (w : Fin 4 → ℤ) (V : TorusField n) (bad : Finset (TorusBond (n * ℓ.side))) (Y' Y : Finset (TorusSite (n * ℓ.side)))
    (c : Finset (TorusSite n)) (h : Y' = translateSet (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) Y) :
    lowerZone T k s (hotCoreSites (T.stage s).toStepSetup (TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) V))
        (translateBonds (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) bad) Y'
        (translateSet (siteOfInt (scaleBy ℓ.side w)) c) =
      translateSet (siteOfInt (scaleBy ℓ.side w)) (lowerZone T k s (hotCoreSites (T.stage s).toStepSetup V) bad Y c) := by
  subst h
  rw [translateBonds_eq_bondsTranslate, hotCoreSites_stage_translate T hfit s hL, lowerZone_translateSet]
private theorem lowerHull_translate_step (hfit : ℓ.Admissible) (s : ℕ) {n : ℕ} [NeZero n] (hL : ℓ.side ∣ n)
    (w : Fin 4 → ℤ) (V : TorusField n) (bad : Finset (TorusBond (n * ℓ.side))) (Y' Y : Finset (TorusSite (n * ℓ.side)))
    (c : Finset (TorusSite n)) (m : ℕ) (h : Y' = translateSet (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) Y) :
    thickening m (lowerZone T k s (hotCoreSites (T.stage s).toStepSetup (TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) V))
        (translateBonds (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) bad) Y'
        (translateSet (siteOfInt (scaleBy ℓ.side w)) c)) =
      translateSet (siteOfInt (scaleBy ℓ.side w))
        (thickening m (lowerZone T k s (hotCoreSites (T.stage s).toStepSetup V) bad Y c)) := by
  rw [lowerZone_translate_step T k hfit s hL w V bad Y' Y c h, thickening_translateSet]
private theorem base_translate (hfit : ℓ.Admissible) {n : ℕ} [NeZero n] (hL : ℓ.side ∣ n) (w : Fin 4 → ℤ)
    (W : TorusField n) (d : ℕ) (c : Finset (TorusSite n)) :
    (stageState T 0 n (TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) W : TorusField n)).2.1 ∩
        interiorAtDepth d (translateSet (siteOfInt (scaleBy ℓ.side w)) c) =
      translateSet (siteOfInt (scaleBy ℓ.side w)) ((stageState T 0 n W).2.1 ∩ interiorAtDepth d c) := by
  classical
  show thickening _ (torusHotSites ℓ (TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) W)) ∩ _ =
    translateSet _ (thickening _ (torusHotSites ℓ W) ∩ _)
  rw [torusHotSites_translate hfit hL, thickening_translateSet, interiorAtDepth_translateSet]
  ext z
  simp only [Finset.mem_inter, mem_translateSet]
private theorem upperHull_translateSample (hfit : ℓ.Admissible) : ∀ (s n : ℕ) [NeZero n], ℓ.side ∣ n →
    ∀ (w : Fin 4 → ℤ) (u : MarkedSample ℓ s n) (c : Finset (TorusSite n)),
    upperHull T k s n (translateSample s n (scaleBy ℓ.side w) u) (translateSet (siteOfInt (scaleBy ℓ.side w)) c) =
      translateSet (siteOfInt (scaleBy ℓ.side w)) (upperHull T k s n u c) := by
  intro s
  induction s with
  | zero =>
    intro n _ hL w u c
    exact base_translate T hfit hL w u _ c
  | succ s ih =>
    intro n _ hL w u c
    classical
    have hL' : ℓ.side ∣ n * ℓ.side := Dvd.intro_left n rfl
    have h1 := ih (n * ℓ.side) hL' (scaleBy ℓ.side w) u.1 (sitesInBlocks ℓ.side c)
    rw [← sitesInBlocks_translateSet] at h1
    show interiorAtDepth _ (translateSet _ c) ∩ thickening _ (upperZone T k s
        (hotCoreSites (T.stage s).toStepSetup (TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) u.2.2.1))
        (translateBonds (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) u.2.2.2)
        (upperHull T k s (n * ℓ.side) (translateSample s (n * ℓ.side) (scaleBy ℓ.side (scaleBy ℓ.side w)) u.1)
          (sitesInBlocks ℓ.side (translateSet (siteOfInt (scaleBy ℓ.side w)) c))) (translateSet _ c)) =
      translateSet _ (interiorAtDepth _ c ∩ thickening _ (upperZone T k s
        (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2
        (upperHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) c))
    exact upperHull_translate_step T k hfit s hL w u.2.2.1 u.2.2.2 _ _ c _ _ h1
private theorem lowerHull_translateSample (hfit : ℓ.Admissible) : ∀ (s n : ℕ) [NeZero n], ℓ.side ∣ n →
    ∀ (w : Fin 4 → ℤ) (u : MarkedSample ℓ s n) (c : Finset (TorusSite n)),
    lowerHull T k s n (translateSample s n (scaleBy ℓ.side w) u) (translateSet (siteOfInt (scaleBy ℓ.side w)) c) =
      translateSet (siteOfInt (scaleBy ℓ.side w)) (lowerHull T k s n u c) := by
  intro s
  induction s with
  | zero =>
    intro n _ hL w u c
    exact base_translate T hfit hL w u _ c
  | succ s ih =>
    intro n _ hL w u c
    have hL' : ℓ.side ∣ n * ℓ.side := Dvd.intro_left n rfl
    have h1 := ih (n * ℓ.side) hL' (scaleBy ℓ.side w) u.1 (sitesInBlocks ℓ.side c)
    rw [← sitesInBlocks_translateSet] at h1
    show thickening _ (lowerZone T k s
        (hotCoreSites (T.stage s).toStepSetup (TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) u.2.2.1))
        (translateBonds (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) u.2.2.2)
        (lowerHull T k s (n * ℓ.side) (translateSample s (n * ℓ.side) (scaleBy ℓ.side (scaleBy ℓ.side w)) u.1)
          (sitesInBlocks ℓ.side (translateSet (siteOfInt (scaleBy ℓ.side w)) c))) (translateSet _ c)) =
      translateSet _ (thickening _ (lowerZone T k s (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2
        (lowerHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) c))
    exact lowerHull_translate_step T k hfit s hL w u.2.2.1 u.2.2.2 _ _ c _ h1
private theorem lowerZone_translateSample (hfit : ℓ.Admissible) (s n : ℕ) [NeZero n] (hL : ℓ.side ∣ n)
    (w : Fin 4 → ℤ) (u : MarkedSample ℓ (s + 1) n) (c : Finset (TorusSite n)) :
    lowerZone T k s (hotCoreSites (T.stage s).toStepSetup (translateSample (s + 1) n (scaleBy ℓ.side w) u).2.2.1)
        (translateSample (s + 1) n (scaleBy ℓ.side w) u).2.2.2
        (lowerHull T k s (n * ℓ.side) (translateSample (s + 1) n (scaleBy ℓ.side w) u).1
          (sitesInBlocks ℓ.side (translateSet (siteOfInt (scaleBy ℓ.side w)) c)))
        (translateSet (siteOfInt (scaleBy ℓ.side w)) c) =
      translateSet (siteOfInt (scaleBy ℓ.side w)) (lowerZone T k s (hotCoreSites (T.stage s).toStepSetup u.2.2.1)
        u.2.2.2 (lowerHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) c) := by
  have hL' : ℓ.side ∣ n * ℓ.side := Dvd.intro_left n rfl
  have h1 := lowerHull_translateSample T k hfit s (n * ℓ.side) hL' (scaleBy ℓ.side w) u.1 (sitesInBlocks ℓ.side c)
  rw [← sitesInBlocks_translateSet] at h1
  show lowerZone T k s (hotCoreSites (T.stage s).toStepSetup (TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) u.2.2.1))
      (translateBonds (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) u.2.2.2)
      (lowerHull T k s (n * ℓ.side) (translateSample s (n * ℓ.side) (scaleBy ℓ.side (scaleBy ℓ.side w)) u.1)
        (sitesInBlocks ℓ.side (translateSet (siteOfInt (scaleBy ℓ.side w)) c))) (translateSet _ c) = _
  exact lowerZone_translate_step T k hfit s hL w u.2.2.1 u.2.2.2 _ _ c h1
private theorem lowerScore_translateSample (hfit : ℓ.Admissible) (s₀ s₁ : ℝ) : ∀ (s n : ℕ) [NeZero n], ℓ.side ∣ n →
    ∀ (w : Fin 4 → ℤ) (u : MarkedSample ℓ s n) (c : Finset (TorusSite n)) (y : TorusSite n),
    lowerScore T k s₀ s₁ s n (translateSample s n (scaleBy ℓ.side w) u)
        (translateSet (siteOfInt (scaleBy ℓ.side w)) c) y =
      lowerScore T k s₀ s₁ s n u c (y + siteOfInt (scaleBy ℓ.side w)) := by
  classical
  intro s
  induction s with
  | zero =>
    intro n _ hL w u c y
    have hmem : y ∈ lowerHull T k 0 n (translateSample 0 n (scaleBy ℓ.side w) u)
          (translateSet (siteOfInt (scaleBy ℓ.side w)) c) ↔
        y + siteOfInt (scaleBy ℓ.side w) ∈ lowerHull T k 0 n u c := by
      rw [lowerHull_translateSample T k hfit 0 n hL, mem_translateSet]
    simp only [lowerScore]
    exact if_congr hmem rfl rfl
  | succ s ih =>
    intro n _ hL w u c y
    have hL' : ℓ.side ∣ n * ℓ.side := Dvd.intro_left n rfl
    have hmem : y ∈ lowerHull T k (s + 1) n (translateSample (s + 1) n (scaleBy ℓ.side w) u)
          (translateSet (siteOfInt (scaleBy ℓ.side w)) c) ↔
        y + siteOfInt (scaleBy ℓ.side w) ∈ lowerHull T k (s + 1) n u c := by
      rw [lowerHull_translateSample T k hfit (s + 1) n hL, mem_translateSet]
    have hzone : y ∈ lowerZone T k s
          (hotCoreSites (T.stage s).toStepSetup (translateSample (s + 1) n (scaleBy ℓ.side w) u).2.2.1)
          (translateSample (s + 1) n (scaleBy ℓ.side w) u).2.2.2
          (lowerHull T k s (n * ℓ.side) (translateSample (s + 1) n (scaleBy ℓ.side w) u).1
            (sitesInBlocks ℓ.side (translateSet (siteOfInt (scaleBy ℓ.side w)) c)))
          (translateSet (siteOfInt (scaleBy ℓ.side w)) c) ↔
        y + siteOfInt (scaleBy ℓ.side w) ∈ lowerZone T k s (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2
          (lowerHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) c := by
      have hz := lowerZone_translateSample T k hfit s n hL w u c
      exact (Finset.ext_iff.mp hz y).trans mem_translateSet
    simp only [lowerScore]
    refine if_congr hmem (congrArg (s₁ + ·) (if_congr hzone ?_ rfl)) rfl
    have h1 : ∀ z, lowerScore T k s₀ s₁ s (n * ℓ.side) (translateSample (s + 1) n (scaleBy ℓ.side w) u).1
        (sitesInBlocks ℓ.side (translateSet (siteOfInt (scaleBy ℓ.side w)) c)) z =
        lowerScore T k s₀ s₁ s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)
          (z + siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) := by
      intro z
      have h := ih (n * ℓ.side) hL' (scaleBy ℓ.side w) u.1 (sitesInBlocks ℓ.side c) z
      rw [← sitesInBlocks_translateSet] at h
      exact h
    simp only [h1]
    refine Finset.sum_nbij' (fun z => z + siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w)))
      (fun z => z - siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) ?_ ?_ (fun z _ => by simp) (fun z _ => by simp)
      (fun z _ => rfl)
    · intro z hz
      have hz' := Finset.mem_singleton.mp (mem_sitesInBlocks.mp hz)
      exact mem_sitesInBlocks.mpr (Finset.mem_singleton.mpr (by rw [parentBlock_add_scaleBy, hz']))
    · intro z hz
      have hz' := Finset.mem_singleton.mp (mem_sitesInBlocks.mp hz)
      refine mem_sitesInBlocks.mpr (Finset.mem_singleton.mpr ?_)
      have h2 := parentBlock_add_scaleBy (n := n) (L := ℓ.side)
        (z - siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) (scaleBy ℓ.side w)
      rw [sub_add_cancel, hz'] at h2
      exact (add_right_cancel h2).symm
private theorem lowerScoreSum_translateSample (hfit : ℓ.Admissible) (s₀ s₁ : ℝ) (s n : ℕ) [NeZero n]
    (hL : ℓ.side ∣ n) (w : Fin 4 → ℤ) (u : MarkedSample ℓ s n) (c : Finset (TorusSite n)) :
    lowerScoreSum T k s₀ s₁ s n (translateSample s n (scaleBy ℓ.side w) u)
        (translateSet (siteOfInt (scaleBy ℓ.side w)) c) =
      lowerScoreSum T k s₀ s₁ s n u c := by
  classical
  unfold lowerScoreSum
  rw [lowerHull_translateSample T k hfit s n hL]
  simp only [lowerScore_translateSample T k hfit s₀ s₁ s n hL]
  refine Finset.sum_nbij' (fun z => z + siteOfInt (scaleBy ℓ.side w)) (fun z => z - siteOfInt (scaleBy ℓ.side w)) ?_ ?_
    (fun z _ => by simp) (fun z _ => by simp) (fun z _ => rfl)
  · intro z hz
    exact mem_translateSet.mp hz
  · intro z hz
    exact mem_translateSet.mpr (by simpa using hz)
private theorem cellEvent_translateSample_iff (hfit : ℓ.Admissible) (n : ℕ) [NeZero n] (hL : ℓ.side ∣ n)
    (w : Fin 4 → ℤ) (u : MarkedSample ℓ k n) (c : Finset (TorusSite n)) :
    CellEvent T k n (translateSample k n (scaleBy ℓ.side w) u) (translateSet (siteOfInt (scaleBy ℓ.side w)) c) ↔
      CellEvent T k n u c := by
  classical
  unfold CellEvent
  rw [upperHull_translateSample T k hfit k n hL, interiorAtDepth_translateSet]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hz
    exact ⟨_, Finset.mem_inter.mpr ⟨mem_translateSet.mp h1, mem_translateSet.mp h2⟩⟩
  · rintro ⟨z, hz⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hz
    exact ⟨z - siteOfInt (scaleBy ℓ.side w), Finset.mem_inter.mpr
      ⟨mem_translateSet.mpr (by simpa using h1), mem_translateSet.mpr (by simpa using h2)⟩⟩
end Moves
section Borel
variable {ℓ : StepParameters}
variable (T : StageTower ℓ) (k : ℕ)
private theorem measurable_lowerScoreSum (hfit : ℓ.Admissible) (s₀ s₁ : ℝ) (s n : ℕ) [NeZero n] (hL : ℓ.side ∣ n)
    (c : Finset (TorusSite n)) : Measurable fun u : MarkedSample ℓ s n => lowerScoreSum T k s₀ s₁ s n u c := by apply _root_.YangMills.SharedProofs.p15189 <;> assumption
private theorem measurableSet_fibre_upperHull (hfit : ℓ.Admissible) : ∀ (s n : ℕ) [NeZero n], ℓ.side ∣ n →
    ∀ (c A : Finset (TorusSite n)), MeasurableSet {u : MarkedSample ℓ s n | upperHull T k s n u c = A} := by apply _root_.YangMills.SharedProofs.p56010 <;> assumption
private theorem measurableSet_cellEvent (hfit : ℓ.Admissible) (n : ℕ) [NeZero n] (hL : ℓ.side ∣ n)
    (c : Finset (TorusSite n)) : MeasurableSet {u : MarkedSample ℓ k n | CellEvent T k n u c} := by
  classical
  have e : {u : MarkedSample ℓ k n | CellEvent T k n u c} =
      ⋃ a ∈ {a : Finset (TorusSite n) | (a ∩ interiorAtDepth (8 * stageRange T k) c).Nonempty},
        {u | upperHull T k k n u c = a} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, CellEvent]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨a, h, h'⟩ => by rw [h']; exact h⟩
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ => measurableSet_fibre_upperHull T k hfit k n hL c a
end Borel
section Measures
private instance (m : ℕ) : DiscreteMeasurableSpace (BondSet m) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private instance (m : ℕ) [NeZero m] : Fintype (BondSet m) := inferInstanceAs (Fintype (Finset (TorusBond m)))
private instance (L n : ℕ) : DiscreteMeasurableSpace (StepCosts.BaseChoice L n) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
private theorem lintegral_count_fintype {α : Type} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (f : α → ℝ≥0∞) : ∫⁻ a, f a ∂(Measure.count : Measure α) = ∑ a, f a := by
  rw [lintegral_count, tsum_fintype]
private theorem measurePreserving_count_equiv {α : Type} [MeasurableSpace α] [Fintype α] [DiscreteMeasurableSpace α]
    (e : α ≃ α) : MeasurePreserving e (Measure.count : Measure α) Measure.count := by
  refine ⟨.of_discrete, Measure.ext_of_lintegral _ fun f hf => ?_⟩
  rw [lintegral_map hf .of_discrete, lintegral_count_fintype, lintegral_count_fintype]
  exact Equiv.sum_comp e f
private theorem measurable_translate {m : ℕ} (a : TorusSite m) : Measurable (TorusFields.translate a : TorusField m → TorusField m) :=
  measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun i =>
    (measurable_pi_apply i).comp (measurable_pi_apply (x + a))
private theorem measurePreserving_translate {m : ℕ} [NeZero m] (a : TorusSite m) :
    MeasurePreserving (TorusFields.translate a : TorusField m → TorusField m) (fieldHaar m) (fieldHaar m) := by
  refine ⟨measurable_translate a, Measure.ext_of_lintegral _ fun f hf => ?_⟩
  rw [lintegral_map hf (measurable_translate a)]
  exact lintegral_fieldHaar_translate a f
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
private theorem translateBonds_neg_translateBonds {m : ℕ} [NeZero m] (a : TorusSite m) (B : Finset (TorusBond m)) :
    translateBonds (-a) (translateBonds a B) = B := by
  rw [translateBonds_eq_bondsTranslate, translateBonds_eq_bondsTranslate]
  exact bondsTranslate_neg_bondsTranslate a B
private def translateBondSet {m : ℕ} [NeZero m] (a : TorusSite m) : BondSet m → BondSet m := translateBonds a
private def translateBondSetEquiv {m : ℕ} [NeZero m] (a : TorusSite m) : BondSet m ≃ BondSet m where
  toFun := translateBondSet a
  invFun := translateBondSet (-a)
  left_inv := translateBonds_neg_translateBonds a
  right_inv B := by
    have h := translateBonds_neg_translateBonds (-a) B
    rw [neg_neg] at h
    exact h
private theorem measurable_translateOutcome (v : Fin 4 → ℤ) :
    Measurable (translateOutcome v : StepOutcome ℓ n → StepOutcome ℓ n) := by
  have hb : Measurable (translateBases v : StepCosts.BaseChoice ℓ.side n → StepCosts.BaseChoice ℓ.side n) := .of_discrete
  have hd : Measurable (translateBondSet (siteOfInt fun i => (ℓ.side : ℤ) * v i) :
      BondSet (n * ℓ.side) → BondSet (n * ℓ.side)) := .of_discrete
  exact (hb.comp measurable_fst).prodMk (((measurable_translate _).comp (measurable_fst.comp measurable_snd)).prodMk
    (hd.comp (measurable_snd.comp measurable_snd)))
abbrev _root_.YangMills.SharedProofs.p19720 := @measurable_translateOutcome
private theorem siteOfInt_mul_neg {m : ℕ} (L : ℕ) (v : Fin 4 → ℤ) :
    (siteOfInt (fun i => (L : ℤ) * (-v) i) : TorusSite m) = - siteOfInt (fun i => (L : ℤ) * v i) := by
  funext i
  simp [siteOfInt]
private theorem translateOutcome_neg_translateOutcome (v : Fin 4 → ℤ) (e : StepOutcome ℓ n) :
    translateOutcome (-v) (translateOutcome v e) = e := by
  obtain ⟨b, V, bad⟩ := e
  have h1 : translateBases (-v) (translateBases v b) = b := translateBases_neg_translateBases v b
  have h2 : TorusFields.translate (siteOfInt (-v)) (TorusFields.translate (siteOfInt v) V) = V := by
    rw [siteOfInt_neg]
    exact translate_neg_translate _ V
  have h3 : translateBonds (siteOfInt fun i => (ℓ.side : ℤ) * (-v) i)
      (translateBonds (siteOfInt fun i => (ℓ.side : ℤ) * v i) bad) = bad := by
    rw [siteOfInt_mul_neg]
    exact translateBonds_neg_translateBonds _ bad
  exact congrArg₂ Prod.mk h1 (congrArg₂ Prod.mk h2 h3)
abbrev _root_.YangMills.SharedProofs.p77001 := @translateOutcome_neg_translateOutcome
private def translateOutcomeEquiv (v : Fin 4 → ℤ) : StepOutcome ℓ n ≃ᵐ StepOutcome ℓ n where
  toFun := translateOutcome v
  invFun := translateOutcome (-v)
  left_inv := translateOutcome_neg_translateOutcome v
  right_inv e := by simpa using translateOutcome_neg_translateOutcome (-v) e
  measurable_toFun := measurable_translateOutcome v
  measurable_invFun := measurable_translateOutcome (-v)
private theorem lintegral_stepReferenceMeasure_translateOutcome (v : Fin 4 → ℤ) (H : StepOutcome ℓ n → ℝ≥0∞) :
    ∫⁻ e, H (translateOutcome v e) ∂(stepReferenceMeasure ℓ n) = ∫⁻ e, H e ∂(stepReferenceMeasure ℓ n) := by
  have hb : MeasurePreserving (translateBases v : StepCosts.BaseChoice ℓ.side n → StepCosts.BaseChoice ℓ.side n)
      Measure.count Measure.count :=
    measurePreserving_count_equiv (translateBasesEquiv v)
  have hd : MeasurePreserving (translateBondSet (siteOfInt fun i => (ℓ.side : ℤ) * v i) :
      BondSet (n * ℓ.side) → BondSet (n * ℓ.side)) Measure.count Measure.count :=
    measurePreserving_count_equiv (translateBondSetEquiv (m := n * ℓ.side) (siteOfInt fun i => (ℓ.side : ℤ) * v i))
  have hp : MeasurePreserving (translateOutcome v : StepOutcome ℓ n → StepOutcome ℓ n)
      (stepReferenceMeasure ℓ n) (stepReferenceMeasure ℓ n) := by
    have h := hb.prod ((measurePreserving_translate (m := n) (siteOfInt v)).prod hd)
    exact h
  exact hp.lintegral_comp_emb (translateOutcomeEquiv v).measurableEmbedding H
end Measures
section Law
variable {ℓ : StepParameters}
private theorem measurable_translateSample (s : ℕ) : ∀ (n : ℕ) [NeZero n] (v : Fin 4 → ℤ),
    Measurable (translateSample (ℓ := ℓ) s n v) := by
  induction s with
  | zero =>
    intro n _ v
    exact measurable_translate _
  | succ s ih =>
    intro n _ v
    letI := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
    exact ((ih (n * ℓ.side) (scaleBy ℓ.side v)).comp measurable_fst).prodMk
      ((measurable_translateOutcome v).comp measurable_snd)
private theorem measurable_topField (s n : ℕ) : Measurable (topField ℓ s n) := by apply _root_.YangMills.SharedProofs.p12845 <;> assumption
private theorem stage_isCutoff (T : StageTower ℓ)
    (h : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (t : ℕ) :
    ColdStepAtMirrorFrames.IsCutoff (T.stage t).toStepSetup.ballRadius (T.stage t).toStepSetup.barrierFn := by apply _root_.YangMills.SharedProofs.p16 <;> assumption
private theorem isProbabilityMeasure_stepNoiseMeasure (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (stepNoiseMeasure ℓ n) := by
  unfold stepNoiseMeasure
  infer_instance
private theorem isProbabilityMeasure_chainNoiseMeasure (s : ℕ) : ∀ (n : ℕ) [NeZero n],
    IsProbabilityMeasure (chainNoiseMeasure ℓ s n) := by
  induction s with
  | zero =>
    intro n _
    exact Measure.dirac.isProbabilityMeasure
  | succ s ih =>
    intro n _
    have h1 := ih (n * ℓ.side)
    have h2 := isProbabilityMeasure_stepNoiseMeasure (ℓ := ℓ) n
    exact Measure.prod.instIsProbabilityMeasure (chainNoiseMeasure ℓ s (n * ℓ.side)) (stepNoiseMeasure ℓ n)
private theorem lintegral_chainNoiseMeasure_succ (s n : ℕ) [NeZero n] (G : ChainNoise ℓ (s + 1) n → ℝ≥0∞)
    (hG : Measurable G) :
    ∫⁻ ξ, G ξ ∂(chainNoiseMeasure ℓ (s + 1) n) =
      ∫⁻ ξ₁ : ChainNoise ℓ s (n * ℓ.side), ∫⁻ ξ₂ : StepNoise ℓ n, G (ξ₁, ξ₂) ∂(stepNoiseMeasure ℓ n)
        ∂(chainNoiseMeasure ℓ s (n * ℓ.side)) := by
  letI := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
  haveI := isProbabilityMeasure_chainNoiseMeasure (ℓ := ℓ) s (n * ℓ.side)
  haveI := isProbabilityMeasure_stepNoiseMeasure (ℓ := ℓ) n
  exact lintegral_prod G hG.aemeasurable
private theorem le_of_isBlockTorusSide (hfit : ℓ.Admissible) {n : ℕ} (hB : IsBlockTorusSide ℓ n) :
    ℓ.n₀ ≤ n ∧ 64 ≤ n := by
  have h1 := hfit.L_ge
  have h2 := hfit.n₀_ge
  have h3 := hB.2
  have h4 : ℓ.n₀ ≤ ℓ.side * ℓ.n₀ := Nat.le_mul_of_pos_left _ (by omega)
  omega
variable (hA : stepOutcomeDensityStatement) (hW : translationPreservesOutcomeDensityStatement)
  (hN : sampleChainMeasurableStatement) (hfit : ℓ.Admissible) (T : StageTower ℓ) (S : ChainSampler T)
  (hcoin : T.MarksMeasurable) (hD : ∀ s, (S s).IsFaithful)
  (hcut : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (k : ℕ)
  (hFr : ∀ j < k, (T.stage j).toStepSetup.ColdChainFits ∧
    RangesAdmissible (T.stage j).toStepSetup.range (T.stage j).toStepSetup.nextRange)
include hA hW hN hfit hcoin hD hcut hFr in
private theorem lintegral_sampleChain_translate (s : ℕ) : s ≤ k → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n →
    ∀ (w : Fin 4 → ℤ) (U : TorusField (fineSide ℓ.side s n)) (F : MarkedSample ℓ s n → ℝ≥0∞), Measurable F →
    ∫⁻ ξ, F (sampleChain T S s n (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ s * scaleBy ℓ.side w i) U) ξ)
        ∂(chainNoiseMeasure ℓ s n) =
      ∫⁻ ξ, F (translateSample s n (scaleBy ℓ.side w) (sampleChain T S s n U ξ)) ∂(chainNoiseMeasure ℓ s n) := by
  induction s with
  | zero =>
    intro _ n _ hB w U F hF
    have e : (fun i => (ℓ.side : ℤ) ^ 0 * scaleBy ℓ.side w i) = scaleBy ℓ.side w := by
      funext i
      simp
    refine lintegral_congr fun ξ => ?_
    rw [e]
    rfl
  | succ s ih =>
    intro hs n _ hB w U F hF
    letI := markedSampleMeasurableSpace ℓ s (n * ℓ.side)
    letI := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    haveI := isProbabilityMeasure_stepNoiseMeasure (ℓ := ℓ) n
    obtain ⟨hn₀, h64⟩ := le_of_isBlockTorusSide hfit hB
    have hBn : IsBlockTorusSide ℓ (n * ℓ.side) :=
      ⟨Dvd.intro_left _ rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
    obtain ⟨hm, hlaw⟩ := hA (T.stage s).toStepSetup (S s) (hD s) (stage_isCutoff T hcut s) n hB.1 h64
      (fun bad => hcoin s n bad)
    have hF' : Measurable fun q : MarkedSample ℓ s (n * ℓ.side) × StepOutcome ℓ n => F q := hF
    have hnd : ∀ (t m : ℕ) [NeZero m], IsBlockTorusSide ℓ m → ∀ U : TorusField (fineSide ℓ.side t m),
        Measurable (sampleChain T S t m U) := fun t m _ hb U =>
      (hN ℓ hfit T S hcoin hD t m hb.1 (le_of_isBlockTorusSide hfit hb).2).comp measurable_prodMk_left
    set G : MarkedSample ℓ s (n * ℓ.side) → ℝ≥0∞ := fun u =>
      ∫⁻ ξ₂ : StepNoise ℓ n, F (u, (S s).sample (topField ℓ s (n * ℓ.side) u) ξ₂) ∂(stepNoiseMeasure ℓ n) with hGdef
    have hfull : Measurable fun q : MarkedSample ℓ s (n * ℓ.side) × StepNoise ℓ n =>
        F (q.1, (S s).sample (topField ℓ s (n * ℓ.side) q.1) q.2) :=
      hF'.comp (measurable_fst.prodMk (hm.comp
        (((measurable_topField s (n * ℓ.side)).comp measurable_fst).prodMk measurable_snd)))
    have hG : Measurable G := hfull.lintegral_prod_right'
    have e : (fun i => (ℓ.side : ℤ) ^ (s + 1) * scaleBy ℓ.side w i) =
        fun i => (ℓ.side : ℤ) ^ s * scaleBy ℓ.side (scaleBy ℓ.side w) i := by
      funext i
      show (ℓ.side : ℤ) ^ (s + 1) * ((ℓ.side : ℤ) * w i) = (ℓ.side : ℤ) ^ s * ((ℓ.side : ℤ) * ((ℓ.side : ℤ) * w i))
      ring
    have hpoint : ∀ u : MarkedSample ℓ s (n * ℓ.side),
        G (translateSample s (n * ℓ.side) (scaleBy ℓ.side (scaleBy ℓ.side w)) u) =
        ∫⁻ ξ₂ : StepNoise ℓ n, F (translateSample s (n * ℓ.side) (scaleBy ℓ.side (scaleBy ℓ.side w)) u,
          translateOutcome (scaleBy ℓ.side w) ((S s).sample (topField ℓ s (n * ℓ.side) u) ξ₂))
          ∂(stepNoiseMeasure ℓ n) := by
      intro u
      have hF1 : Measurable fun e : StepOutcome ℓ n =>
          F (translateSample s (n * ℓ.side) (scaleBy ℓ.side (scaleBy ℓ.side w)) u, e) :=
        hF'.comp measurable_prodMk_left
      have hF2 : Measurable fun e : StepOutcome ℓ n =>
          F (translateSample s (n * ℓ.side) (scaleBy ℓ.side (scaleBy ℓ.side w)) u, translateOutcome (scaleBy ℓ.side w) e) :=
        hF1.comp (measurable_translateOutcome _)
      simp only [hGdef]
      rw [topField_translateSample, hlaw _ _ hF1, hlaw _ _ hF2,
        ← lintegral_stepReferenceMeasure_translateOutcome (scaleBy ℓ.side w)]
      refine lintegral_congr fun e => ?_
      have hw := hW (T.stage s).toStepSetup hfit (hFr s (by omega)).1 (hFr s (by omega)).2 n hB w
        (topField ℓ s (n * ℓ.side) u) e
      exact congrArg (fun t => F _ * ENNReal.ofReal t) hw
    have hL1 := lintegral_chainNoiseMeasure_succ (ℓ := ℓ) s n
      (fun ξ => F (sampleChain T S (s + 1) n
        (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ (s + 1) * scaleBy ℓ.side w i) U) ξ))
      (hF.comp (hnd (s + 1) n hB _))
    have hL2 := lintegral_chainNoiseMeasure_succ (ℓ := ℓ) s n
      (fun ξ => F (translateSample (s + 1) n (scaleBy ℓ.side w) (sampleChain T S (s + 1) n U ξ)))
      (hF.comp ((measurable_translateSample (s + 1) n _).comp (hnd (s + 1) n hB _)))
    rw [hL1, hL2]
    have hih := ih (by omega) (n * ℓ.side) hBn (scaleBy ℓ.side w) U G hG
    rw [← e] at hih
    refine hih.trans (lintegral_congr fun ξ₁ => ?_)
    exact hpoint _
include hA hW hN hfit hcoin hD hcut hFr in
private theorem means_translate (s₀ s₁ : ℝ) (n : ℕ) [NeZero n] (hB : IsBlockTorusSide ℓ n) (w : Fin 4 → ℤ)
    (c : Finset (TorusSite n)) (U : TorusField (fineSide ℓ.side k n)) :
    lowerSumExpMean T S s₀ s₁ k n c (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ k * scaleBy ℓ.side w i) U) =
        lowerSumExpMean T S s₀ s₁ k n (c.image (· + siteOfInt (scaleBy ℓ.side w))) U ∧
      cellEventProb T S k n c (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ k * scaleBy ℓ.side w i) U) =
        cellEventProb T S k n (c.image (· + siteOfInt (scaleBy ℓ.side w))) U := by
  classical
  haveI := isProbabilityMeasure_chainNoiseMeasure (ℓ := ℓ) k n
  have hnd : ∀ U : TorusField (fineSide ℓ.side k n), Measurable (sampleChain T S k n U) := fun U =>
    (hN ℓ hfit T S hcoin hD k n hB.1 (le_of_isBlockTorusSide hfit hB).2).comp measurable_prodMk_left
  have hM := measurable_translateSample (ℓ := ℓ) k n (scaleBy ℓ.side w)
  have hMD : Measurable fun ξ => translateSample k n (scaleBy ℓ.side w) (sampleChain T S k n U ξ) := hM.comp (hnd U)
  set U' := TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ k * scaleBy ℓ.side w i) U with hU'
  have hmap : Measure.map (sampleChain T S k n U') (chainNoiseMeasure ℓ k n) =
      Measure.map (fun ξ => translateSample k n (scaleBy ℓ.side w) (sampleChain T S k n U ξ))
        (chainNoiseMeasure ℓ k n) := by
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    rw [lintegral_map hf (hnd U'), lintegral_map hf hMD]
    exact lintegral_sampleChain_translate hA hW hN hfit T S hcoin hD hcut k hFr k le_rfl n hB w U f hf
  have hc : c = translateSet (siteOfInt (scaleBy ℓ.side w)) (c.image (· + siteOfInt (scaleBy ℓ.side w))) := by
    ext z
    rw [mem_translateSet]
    simp
  constructor
  · unfold lowerSumExpMean
    have hf : Measurable fun u : MarkedSample ℓ k n => Real.exp (lowerScoreSum T k s₀ s₁ k n u c) :=
      Real.measurable_exp.comp (measurable_lowerScoreSum T k hfit s₀ s₁ k n hB.1 c)
    rw [← integral_map (hnd U').aemeasurable hf.aestronglyMeasurable (f := fun u : MarkedSample ℓ k n =>
      Real.exp (lowerScoreSum T k s₀ s₁ k n u c)), hmap,
      integral_map hMD.aemeasurable hf.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have h := lowerScoreSum_translateSample T k hfit s₀ s₁ k n hB.1 w (sampleChain T S k n U ξ)
      (c.image (· + siteOfInt (scaleBy ℓ.side w)))
    rw [← hc] at h
    show Real.exp _ = Real.exp _
    rw [h]
  · unfold cellEventProb
    have hA' := measurableSet_cellEvent T k hfit n hB.1 c
    have h1 : chainNoiseMeasure ℓ k n {ξ | CellEvent T k n (sampleChain T S k n U' ξ) c} =
        chainNoiseMeasure ℓ k n
          {ξ | CellEvent T k n (sampleChain T S k n U ξ) (c.image (· + siteOfInt (scaleBy ℓ.side w)))} := by
      have e1 : {ξ | CellEvent T k n (sampleChain T S k n U' ξ) c} =
          sampleChain T S k n U' ⁻¹' {u | CellEvent T k n u c} := rfl
      rw [e1, ← Measure.map_apply (hnd U') hA', hmap, Measure.map_apply hMD hA']
      congr 1
      ext ξ
      have h := cellEvent_translateSample_iff T k hfit n hB.1 w (sampleChain T S k n U ξ)
        (c.image (· + siteOfInt (scaleBy ℓ.side w)))
      rw [← hc] at h
      exact h
    rw [h1]
end Law
private theorem pow_le_clusterRange {y : ℝ} {k : ℕ} (hy : (2 : ℝ) ^ (100 * k) ≤ y) : 2 ^ k ≤ clusterRange y := by apply _root_.YangMills.Construction.StepInvariance.pow_le_clusterRange <;> assumption
end TranslationCellMeans
open TranslationCellMeans in
theorem translationCarriesCellMeans (hA : stepOutcomeDensityStatement)
    (hW : translationPreservesOutcomeDensityStatement) (hN : sampleChainMeasurableStatement) :
    translationCarriesCellMeansStatement := by
  intro a ha
  refine ⟨0, fun _ => 1, fun _ => one_pos, fun L hodd _ Tb hTa hTL hD hrt => ?_⟩
  refine ⟨max Tb.floorMin ((2 : ℝ) ^ (100 * 16)), fun y hy hrow hwil => ?_⟩
  have hfit : (Tb.stepParameters y).Admissible := hD.fits y ((le_max_left _ _).trans hy)
  have hy2 : (2 : ℝ) ^ (100 * 16) ≤ y := (le_max_right _ _).trans hy
  intro T S β s₀ s₁ k e hrun hS hside v hv c U
  have hcut : ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn := by
    have h₁ : (T.stage 0).toStepSetup.barrierFn = Tb.cutoff := (hrun.onFamily.onFamily 0 (Nat.zero_le _)).barrierFn_eq
    have h₂ : T.base.barrierFn = Tb.cutoff := h₁
    rw [h₂]
    exact hD.cut
  have hFr : ∀ j < k, (T.stage j).toStepSetup.ColdChainFits ∧
      RangesAdmissible (T.stage j).toStepSetup.range (T.stage j).toStepSetup.nextRange := by
    intro j hj
    have hOn := hrun.onFamily.onFamily j hj.le
    have hOn' := hrun.onFamily.onFamily (j + 1) hj
    have hchain : ColdChain.ColdChainConstants (Tb.stepParameters y).coupling Tb.δ₁ (Tb.stepParameters y).side Tb.lam
        (T.stage j).toStepSetup.anchorRadius Tb.σA Tb.cg Tb.N := by
      rw [hOn.anchorRadius_eq]
      exact hD.chain
    refine ⟨⟨Tb.δ₁, Tb.lam, Tb.σA, Tb.cg, Tb.N, hchain, hD.σ_le, hD.σ_one⟩, hOn.isStep.2.2, ?_, ?_⟩
    · have hx : y ≤ (T.stage j).nextCoupling := hOn'.le_coupling
      exact pow_le_clusterRange (k := 16) (hy2.trans hx)
    · have hx : y ≤ (T.stage j).coupling := hOn.le_coupling
      have h := pow_le_clusterRange (k := 16) (hy2.trans hx)
      refine (Nat.le_div_iff_mul_le (by norm_num)).mpr ?_
      have h' : 2 ^ 16 ≤ (T.stage j).toStepSetup.range := h
      norm_num at h' ⊢
      omega
  have hBlk : IsBlockTorusSide (Tb.stepParameters y) (2 * (Tb.stepParameters y).side ^ e) := by
    refine ⟨?_, hside⟩
    have he : e ≠ 0 := by
      rintro rfl
      have h1 := hfit.L_ge
      have h2 := hfit.n₀_ge
      have h3 : (Tb.stepParameters y).side ≤ (Tb.stepParameters y).side * (Tb.stepParameters y).n₀ :=
        Nat.le_mul_of_pos_right _ (by omega)
      simp only [pow_zero, mul_one] at hside
      omega
    exact Dvd.dvd.mul_left (dvd_pow_self _ he) 2
  choose w hw using hv
  obtain rfl : v = scaleBy (Tb.stepParameters y).side w := funext hw
  exact means_translate hA hW hN hfit T S hrun.measurable hS hcut k hFr s₀ s₁ _ hBlk w c U
end CellWindows
end YangMills.Construction
end
