import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import YangMills.Construction.HullsInEveryVolume.ARuleDrawsTheChain
import YangMills.Construction.HullsInEveryVolume.TranslationsCarryTheBasesAtEverySide
import YangMills.Construction.LawByMomentsOfTheFlow.DistanceOfTheSitesOfTwoSupports
import YangMills.Construction.LawByMomentsOfTheFlow.MeansOfALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.ScoresInALimitField
import YangMills.Construction.LawByMomentsOfTheFlow.SupTestFunctionsAreTestFunctions
import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelow
import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheMarksBelowALevelProof
import YangMills.Construction.SixteenPointsOnASmallTorus.CopiesAboutASiteProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentLaw
namespace LimitScoreMeans
open TorusFields TorusLumps StepCosts StepSettings WeightedResponses ChainNoise MomentMethod LevelTestFunctions
  TopLevelSites TorusContours BaseTranslations ResponseInTheExpansion LumpContours RenormalizationStepParameters
private abbrev scaleVec (L : ℕ) (v : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (L : ℤ) * v i
section Sites
variable {n L : ℕ}
private theorem blockSite_add_siteOfInt [NeZero n] [NeZero L] (y : TorusSite n) (o : BlockOffset L) (v : Fin 4 → ℤ) :
    (blockSite (y + siteOfInt v) o : TorusSite (n * L)) = blockSite y o + siteOfInt (scaleVec L v) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.blockSite_add <;> assumption
end Sites
section FrameSites
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
private theorem frameSite_fine_translate (v : Fin 4 → ℤ) (x : TorusSite (n * ℓ.side)) :
    torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth (x + siteOfInt (scaleVec ℓ.side v)) =
      torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth x +
        BlockAverages.siteOfCoords (stepBlockFrame ℓ.side n).depth (scaleVec ℓ.side v) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusSiteInFrame_add_scale <;> assumption
private theorem frameSite_coarse_translate (v : Fin 4 → ℤ) (x : TorusSite n) :
    torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (x + siteOfInt v) =
      torusSiteInFrame (stepBlockFrame ℓ.side n) 1 x + BlockAverages.siteOfCoords (stepBlockFrame ℓ.side n).top v := by
  rw [torusSiteInFrame_add (F := stepBlockFrame ℓ.side n) (j := 1) (N := n) TorusContours.stepBlockFrame_period_one,
    torusSiteInFrame_siteOfInt (F := stepBlockFrame ℓ.side n) (j := 1) (N := n)
      TorusContours.stepBlockFrame_period_one]
  rfl
private theorem toTorusSite_coarse_translate (v : Fin 4 → ℤ) (y : (stepBlockFrame ℓ.side n).Cell) :
    toTorusSite n (y + BlockAverages.siteOfCoords (stepBlockFrame ℓ.side n).top v) = toTorusSite n y + siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.toTorusSite_add_coarse <;> assumption
private theorem baseChoice_translate (v : Fin 4 → ℤ) (o : TorusSite n → BlockOffset ℓ.side) :
    baseChoiceOfOffsets (ℓ := ℓ) (fun y => o (y + siteOfInt v)) = translateBases v (baseChoiceOfOffsets (ℓ := ℓ) o) := by
  funext y
  have hy := toTorusSite_coarse_translate (ℓ := ℓ) v y
  unfold translateBases
  refine eq_sub_of_add_eq ?_
  show torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth
        (blockSite (toTorusSite n y) (o (toTorusSite n y + siteOfInt v))) +
      BlockAverages.siteOfCoords (stepBlockFrame ℓ.side n).depth (scaleVec ℓ.side v) =
    torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth
      (blockSite (toTorusSite n (y + BlockAverages.siteOfCoords (stepBlockFrame ℓ.side n).top v))
        (o (toTorusSite n (y + BlockAverages.siteOfCoords (stepBlockFrame ℓ.side n).top v))))
  rw [hy, blockSite_add_siteOfInt, frameSite_fine_translate]
  rfl
abbrev _root_.YangMills.SharedProofs.p71065 := @baseChoice_translate
end FrameSites
section Translations
variable {ℓ : StepParameters}
private def translateChain (ℓ : StepParameters) : (s n : ℕ) → (Fin 4 → ℤ) → ChainSample ℓ s n → ChainSample ℓ s n
  | 0, _, a, W => TorusFields.translate (siteOfInt a) W
  | s + 1, n, a, u =>
    (translateChain ℓ s (n * ℓ.side) (scaleVec ℓ.side a) u.1, translateBases a u.2.1,
      TorusFields.translate (siteOfInt a) u.2.2)
private def translateWeights (ℓ : StepParameters) {m : ℕ} :
    (s n : ℕ) → (Fin 4 → ℤ) → ScoreWeights ℓ m s n → ScoreWeights ℓ m s n
  | 0, _, _, w => w
  | s + 1, n, a, w =>
    (translateWeights ℓ s (n * ℓ.side) (scaleVec ℓ.side a) w.1, fun j c => w.2 j (c.1 - siteOfInt a, c.2))
private theorem finalField_translateChain (s n : ℕ) (a : Fin 4 → ℤ) (v : ChainSample ℓ s n) :
    finalField ℓ s n (translateChain ℓ s n a v) = TorusFields.translate (siteOfInt a) (finalField ℓ s n v) := by
  cases s <;> rfl
private theorem initialField_translateChain : ∀ (s n : ℕ) (a : Fin 4 → ℤ) (v : ChainSample ℓ s n),
    initialField ℓ s n (translateChain ℓ s n a v) =
      TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ s * a i) (initialField ℓ s n v)
  | 0, n, a, v => by
    have e : (fun i => (ℓ.side : ℤ) ^ 0 * a i) = a := by
      funext i
      simp
    rw [e]
    rfl
  | s + 1, n, a, v => by
    have e : (fun i => (ℓ.side : ℤ) ^ s * scaleVec ℓ.side a i) = fun i => (ℓ.side : ℤ) ^ (s + 1) * a i := by
      funext i
      simp only [scaleVec]
      ring
    have ih := initialField_translateChain s (n * ℓ.side) (scaleVec ℓ.side a) v.1
    rw [e] at ih
    exact ih
private theorem bondScore_translate (hSc : BondScoreProperties) (hB : HullTrees.translationCarriesBasesStatement)
    (hf : ℓ.Admissible) (x : ℝ) (n : ℕ) [NeZero n] (a : Fin 4 → ℤ) (W : TorusField (n * ℓ.side)) (V : TorusField n)
    (b : BaseChoice ℓ.side n) (c : TorusBond n) :
    bondScore ℓ x (TorusFields.translate (siteOfInt (scaleVec ℓ.side a)) W) (TorusFields.translate (siteOfInt a) V)
        (translateBases a b) c =
      bondScore ℓ x W V b (c.1 + siteOfInt a, c.2) := by
  have hm := (hB ℓ n a W).2 b (translateBases a b) (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)
    (fun y => sub_add_cancel _ _)
  have hs := frameSite_coarse_translate (ℓ := ℓ) a c.1
  have hm' : contourMean ℓ.baseDepth
      (fineHotLumps ℓ (fineLevelField ℓ n (TorusFields.translate (siteOfInt (scaleVec ℓ.side a)) W)))
      (translateBases a b) (fineLevelField ℓ n (TorusFields.translate (siteOfInt (scaleVec ℓ.side a)) W))
      (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2) =
      contourMean ℓ.baseDepth (fineHotLumps ℓ (fineLevelField ℓ n W)) b (fineLevelField ℓ n W)
        (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 (c.1 + siteOfInt a), c.2) := by
    rw [hs]
    exact hm
  have e1 : meanNorm ℓ (TorusFields.translate (siteOfInt (scaleVec ℓ.side a)) W) (translateBases a b) c =
      meanNorm ℓ W b (c.1 + siteOfInt a, c.2) := congrArg norm hm'
  have e2 : bondMean ℓ
      (readAtLevel (stepBlockFrame ℓ.side n) 0 (TorusFields.translate (siteOfInt (scaleVec ℓ.side a)) W))
      (translateBases a b) c =
      bondMean ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) b (c.1 + siteOfInt a, c.2) := hm'
  rw [(hSc ℓ hf x n (translateBases a b) c).2.1, (hSc ℓ hf x n b (c.1 + siteOfInt a, c.2)).2.1, e1, e2]
  rfl
private theorem weightedScoreSum_translateChain (hSc : BondScoreProperties)
    (hB : HullTrees.translationCarriesBasesStatement) (hf : ℓ.Admissible) (x : ℕ → ℝ) {m : ℕ} :
    ∀ (s n : ℕ) [NeZero n] (a : Fin 4 → ℤ) (w : ScoreWeights ℓ m s n) (j : Fin m) (v : ChainSample ℓ s n),
      weightedScoreSum ℓ x s n w j (translateChain ℓ s n a v) =
        weightedScoreSum ℓ x s n (translateWeights ℓ s n a w) j v
  | 0, _, _, _, _, _, _ => rfl
  | s + 1, n, _, a, w, j, v => by
    show weightedScoreSum ℓ x s (n * ℓ.side) w.1 j (translateChain ℓ s (n * ℓ.side) (scaleVec ℓ.side a) v.1) +
        ∑ c : TorusBond n, w.2 j c * bondScore ℓ (x s)
          (finalField ℓ s (n * ℓ.side) (translateChain ℓ s (n * ℓ.side) (scaleVec ℓ.side a) v.1))
          (TorusFields.translate (siteOfInt a) v.2.2) (translateBases a v.2.1) c =
      weightedScoreSum ℓ x s (n * ℓ.side) (translateWeights ℓ s (n * ℓ.side) (scaleVec ℓ.side a) w.1) j v.1 +
        ∑ c : TorusBond n, w.2 j (c.1 - siteOfInt a, c.2) *
          bondScore ℓ (x s) (finalField ℓ s (n * ℓ.side) v.1) v.2.2 v.2.1 c
    rw [weightedScoreSum_translateChain hSc hB hf x s (n * ℓ.side) (scaleVec ℓ.side a) w.1 j v.1,
      finalField_translateChain]
    congr 1
    simp only [bondScore_translate hSc hB hf]
    refine Fintype.sum_equiv ((Equiv.addRight (siteOfInt a)).prodCongr (Equiv.refl _)) _ _ fun c => ?_
    show w.2 j c * bondScore ℓ (x s) (finalField ℓ s (n * ℓ.side) v.1) v.2.2 v.2.1 (c.1 + siteOfInt a, c.2) =
      w.2 j (c.1 + siteOfInt a - siteOfInt a, c.2) *
        bondScore ℓ (x s) (finalField ℓ s (n * ℓ.side) v.1) v.2.2 v.2.1 (c.1 + siteOfInt a, c.2)
    rw [add_sub_cancel_right]
private theorem finalField_forgetMarks (s n : ℕ) (u : MarkedSample ℓ s n) :
    finalField ℓ s n (forgetMarks ℓ s n u) = topField ℓ s n u := by apply _root_.YangMills.SharedProofs.p8091 <;> assumption
private theorem stepOutcome_field_translate (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T)
    (s n : ℕ) [NeZero n] (v : Fin 4 → ℤ) (W : TorusField (n * ℓ.side)) (U : StepNoise ℓ n) :
    (rule.stepOutcome T s n (TorusFields.translate (siteOfInt (scaleVec ℓ.side v)) W)
        (fun y => U.1 (y + siteOfInt v), fun c => U.2.1 (c.1 + siteOfInt v, c.2),
          fun b => U.2.2 (b.1 + siteOfInt (scaleVec ℓ.side v), b.2))).2.1 =
      TorusFields.translate (siteOfInt v) (rule.stepOutcome T s n W U).2.1 := by
  funext y i
  simp only [NoiseRule.stepOutcome, TorusFields.translate]
  have ho : (fun y => rule.base s n (TorusFields.translate (siteOfInt (scaleVec ℓ.side v)) W) y
      (U.1 (y + siteOfInt v))) =
      fun y => (fun y => rule.base s n W y (U.1 y)) (y + siteOfInt v) :=
    funext fun y => hr.base_translate s n W v y _
  rw [ho]
  exact hr.value_translate s n W (fun y => rule.base s n W y (U.1 y)) v (y, i) _
abbrev _root_.YangMills.DeltaSharedProofs.p501493 := @stepOutcome_field_translate
private theorem stepOutcome_bases_translate (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T)
    (s n : ℕ) [NeZero n] (v : Fin 4 → ℤ) (W : TorusField (n * ℓ.side)) (U : StepNoise ℓ n) :
    (rule.stepOutcome T s n (TorusFields.translate (siteOfInt (scaleVec ℓ.side v)) W)
        (fun y => U.1 (y + siteOfInt v), fun c => U.2.1 (c.1 + siteOfInt v, c.2),
          fun b => U.2.2 (b.1 + siteOfInt (scaleVec ℓ.side v), b.2))).1 =
      translateBases v (rule.stepOutcome T s n W U).1 := by
  simp only [NoiseRule.stepOutcome]
  have ho : (fun y => rule.base s n (TorusFields.translate (siteOfInt (scaleVec ℓ.side v)) W) y
      (U.1 (y + siteOfInt v))) =
      fun y => (fun y => rule.base s n W y (U.1 y)) (y + siteOfInt v) :=
    funext fun y => hr.base_translate s n W v y _
  rw [ho]
  exact baseChoice_translate (ℓ := ℓ) (n := n) v (fun y => rule.base s n W y (U.1 y))
private theorem chain_translate (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T) :
    ∀ (s n : ℕ) [NeZero n] (a : Fin 4 → ℤ) (W : TorusField (fineSide ℓ.side s n))
      (U : ChainNoise.ChainNoise ℓ s n),
      forgetMarks ℓ s n (rule.chain T s n (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ s * a i) W)
          (noiseTranslate ℓ s n a U)) =
        translateChain ℓ s n a (forgetMarks ℓ s n (rule.chain T s n W U))
  | 0, n, _, a, W, U => by
    have e : (fun i => (ℓ.side : ℤ) ^ 0 * a i) = a := by
      funext i
      simp
    rw [e]
    rfl
  | s + 1, n, _, a, W, U => by
    have e : (fun i => (ℓ.side : ℤ) ^ (s + 1) * a i) = fun i => (ℓ.side : ℤ) ^ s * scaleVec ℓ.side a i := by
      funext i
      simp only [scaleVec]
      ring
    rw [e]
    have ih := chain_translate rule T hr s (n * ℓ.side) (scaleVec ℓ.side a) W U.1
    have hX : topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side)
        (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ s * scaleVec ℓ.side a i) W)
        (noiseTranslate ℓ s (n * ℓ.side) (scaleVec ℓ.side a) U.1)) =
        TorusFields.translate (siteOfInt (scaleVec ℓ.side a))
          (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) W U.1)) := by
      rw [← finalField_forgetMarks, ih, finalField_translateChain, finalField_forgetMarks]
    refine Prod.ext ih (Prod.ext ?_ ?_)
    · show (rule.stepOutcome T s n (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side)
          (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ s * scaleVec ℓ.side a i) W)
          (noiseTranslate ℓ s (n * ℓ.side) (scaleVec ℓ.side a) U.1)))
          (fun y => U.2.1 (y + siteOfInt a), fun c => U.2.2.1 (c.1 + siteOfInt a, c.2),
            fun b => U.2.2.2 (b.1 + siteOfInt (scaleVec ℓ.side a), b.2))).1 = _
      rw [hX]
      exact stepOutcome_bases_translate rule T hr s n a _ U.2
    · show (rule.stepOutcome T s n (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side)
          (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ s * scaleVec ℓ.side a i) W)
          (noiseTranslate ℓ s (n * ℓ.side) (scaleVec ℓ.side a) U.1)))
          (fun y => U.2.1 (y + siteOfInt a), fun c => U.2.2.1 (c.1 + siteOfInt a, c.2),
            fun b => U.2.2.2 (b.1 + siteOfInt (scaleVec ℓ.side a), b.2))).2.1 = _
      rw [hX]
      exact stepOutcome_field_translate rule T hr s n a _ U.2
private def chainPrefix (ℓ : StepParameters) (s : ℕ) :
    (d n : ℕ) → ChainSample ℓ (s + d) n → ChainSample ℓ s (fineSide ℓ.side d n)
  | 0, _, v => v
  | d + 1, n, v => chainPrefix ℓ s d (n * ℓ.side) v.1
private theorem forgetMarks_sampleBelow (s : ℕ) : ∀ (d n : ℕ) (w : MarkedSample ℓ (s + d) n),
    forgetMarks ℓ s (fineSide ℓ.side d n) (sampleBelow ℓ s d n w) = chainPrefix ℓ s d n (forgetMarks ℓ (s + d) n w)
  | 0, _, _ => rfl
  | d + 1, n, w => forgetMarks_sampleBelow s d (n * ℓ.side) w.1
private theorem chainPrefix_translate (s : ℕ) : ∀ (d n : ℕ) (a : Fin 4 → ℤ) (v : ChainSample ℓ (s + d) n),
    chainPrefix ℓ s d n (translateChain ℓ (s + d) n a v) =
      translateChain ℓ s (fineSide ℓ.side d n) (fun i => (ℓ.side : ℤ) ^ d * a i) (chainPrefix ℓ s d n v)
  | 0, n, a, v => by
    have e : (fun i => (ℓ.side : ℤ) ^ 0 * a i) = a := by
      funext i
      simp
    rw [e]
    rfl
  | d + 1, n, a, v => by
    have e : (fun i => (ℓ.side : ℤ) ^ d * scaleVec ℓ.side a i) = fun i => (ℓ.side : ℤ) ^ (d + 1) * a i := by
      funext i
      simp only [scaleVec]
      ring
    have ih := chainPrefix_translate s d (n * ℓ.side) (scaleVec ℓ.side a) v.1
    rw [e] at ih
    exact ih
end Translations
section Weights
variable {ℓ : StepParameters}
private theorem sum_bond_endpoints {n : ℕ} [NeZero n] (h : TorusSite n → ℝ) (A : TorusBond n → ℝ) :
    ∑ Y : TorusSite n, h Y * ∑ i : Fin 4, (A (Y, i) + A (Y - unitStep n i, i)) =
      ∑ c : TorusBond n, (h c.1 + h (c.1 + unitStep n c.2)) * A c := by apply _root_.YangMills.SharedProofs.p11136 <;> assumption
private def bondCoeff (ℓ : StepParameters) (al : ℝ) (s : ℕ) {n : ℕ} [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) (c : TorusBond n) : ℝ :=
  ℓ.coupling / 2 * al *
    (blockMean ℓ.side (s + 1) n c.1 h + blockMean ℓ.side (s + 1) n (c.1 + unitStep n c.2) h)
private theorem stepSourceTerm_eq (x al : ℝ) (s : ℕ) {n : ℕ} [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) (W : TorusField (n * ℓ.side)) (d : StepOutcome ℓ n) :
    stepSourceTerm ℓ x al s h W d = ∑ c : TorusBond n, bondCoeff ℓ al s h c * bondScore ℓ x W d.2.1 d.1 c := by
  unfold stepSourceTerm bondCoeff
  rw [sum_bond_endpoints (fun Y => blockMean ℓ.side (s + 1) n Y h) (fun c => bondScore ℓ x W d.2.1 d.1 c),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring
private def scoreWeightsOf (ℓ : StepParameters) (al : ℕ → ℝ) {m : ℕ} : (s n : ℕ) → [NeZero n] →
    (Fin m → PlaquetteWeight (fineSide ℓ.side s n)) → ScoreWeights ℓ m s n
  | 0, _, _, _ => ()
  | s + 1, n, _, h => (scoreWeightsOf ℓ al s (n * ℓ.side) h, fun i c => bondCoeff ℓ (al s) s (h i) c)
private theorem initialField_forgetMarks (ℓ : StepParameters) : (s n : ℕ) → (u : MarkedSample ℓ s n) →
    initialField ℓ s n (forgetMarks ℓ s n u) = bottomField ℓ s n u
  | 0, _, _ => rfl
  | s + 1, n, u => initialField_forgetMarks ℓ s (n * ℓ.side) u.1
private theorem weightedScoreSum_scoreWeightsOf (T : StageTower ℓ) (al : ℕ → ℝ) {m : ℕ} : (s n : ℕ) → [NeZero n] →
    (h : Fin m → PlaquetteWeight (fineSide ℓ.side s n)) → (j : Fin m) → (u : MarkedSample ℓ s n) →
    weightedScoreSum ℓ (fun j => (T.stage j).coupling) s n (scoreWeightsOf ℓ al s n h) j (forgetMarks ℓ s n u) =
      cumulativeSource T al s n (h j) u
  | 0, _, _, _, _, _ => rfl
  | s + 1, n, _, h, j, u => by
    have ih := weightedScoreSum_scoreWeightsOf T al s (n * ℓ.side) h j u.1
    show weightedScoreSum ℓ (fun j => (T.stage j).coupling) s (n * ℓ.side) (scoreWeightsOf ℓ al s (n * ℓ.side) h) j
        (forgetMarks ℓ s (n * ℓ.side) u.1) +
      ∑ c : TorusBond n, bondCoeff ℓ (al s) s (h j) c *
        bondScore ℓ (T.stage s).coupling (finalField ℓ s (n * ℓ.side) (forgetMarks ℓ s (n * ℓ.side) u.1))
          u.2.2.1 u.2.1 c =
      cumulativeSource T al s (n * ℓ.side) (h j) u.1 + sourceTerm T al s n (h j) u
    rw [ih, finalField_forgetMarks]
    congr 1
    exact (stepSourceTerm_eq (T.stage s).coupling (al s) s (h j) (topField ℓ s (n * ℓ.side) u.1) u.2).symm
private theorem mem_weightSupportSites_of_blockMean (L : ℕ) [NeZero L] : ∀ (t n : ℕ) [NeZero n] (y : TorusSite n)
    (h : PlaquetteWeight (fineSide L t n)), blockMean L t n y h ≠ 0 → y ∈ weightSupportSites L t n h := by apply _root_.YangMills.SharedProofs.p53316 <;> assumption
private theorem supDist_endpoints_le {n : ℕ} [NeZero n] (c : TorusBond n) {y y' : TorusSite n}
    (hy : y = c.1 ∨ y = c.1 + unitStep n c.2) (hy' : y' = c.1 ∨ y' = c.1 + unitStep n c.2) :
    TorusFields.supDist y y' ≤ 1 := by apply _root_.YangMills.SharedProofs.p28905 <;> assumption
private theorem exists_endpoint_of_bondCoeff (al : ℝ) (s n : ℕ) [NeZero n]
    (h : PlaquetteWeight (fineSide ℓ.side (s + 1) n)) (c : TorusBond n) (hc : bondCoeff ℓ al s h c ≠ 0) :
    ∃ y : TorusSite n, (y = c.1 ∨ y = c.1 + unitStep n c.2) ∧ blockMean ℓ.side (s + 1) n y h ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hc
  unfold bondCoeff
  rw [hcon c.1 (Or.inl rfl), hcon _ (Or.inr rfl)]
  simp
private theorem sideAt_succ_mul {k : ℕ} (P : LevelData k) (L v : ℕ) (hv : v + 1 ≤ P.windowLevel) :
    P.sideAt L (v + 1) * L = P.sideAt L v := by
  unfold LevelData.sideAt
  have : P.windowLevel - v = (P.windowLevel - (v + 1)) + 1 := by omega
  rw [this, pow_succ, mul_assoc]
abbrev _root_.YangMills.SharedProofs.p32891 := @sideAt_succ_mul
private theorem disjoint_scoreWeightsOf {k m : ℕ} (P : LevelData k) (al : ℕ → ℝ) (idx : Fin m → Fin k)
    (hidx : Function.Injective idx) :
    ∀ (v : ℕ), v ≤ P.windowLevel → ∀ (N : ℕ) [NeZero N], N = P.sideAt ℓ.side v →
      (∀ u < v, 8 < P.separation ℓ.side u) →
      ScoreWeights.Disjoint v N
        (scoreWeightsOf ℓ al v N fun j => P.testWeight ℓ.side (idx j) (fineSide ℓ.side v N)) := by
  intro v
  induction v with
  | zero =>
    intro _ N _ _ _
    exact trivial
  | succ v ih =>
    intro hv N _ hN hgap
    refine ⟨ih (by omega) (N * ℓ.side) (by rw [hN]; exact sideAt_succ_mul P ℓ.side v hv)
      fun u hu => hgap u (by omega), ?_⟩
    intro c j j' hjj
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    subst hN
    obtain ⟨y, hy, hyn⟩ := exists_endpoint_of_bondCoeff _ _ _ _ c h1
    obtain ⟨y', hy', hyn'⟩ := exists_endpoint_of_bondCoeff _ _ _ _ c h2
    have hA := mem_weightSupportSites_of_blockMean ℓ.side _ _ _ _ hyn
    have hA' := mem_weightSupportSites_of_blockMean ℓ.side _ _ _ _ hyn'
    have hle : P.separation ℓ.side v ≤ TorusFields.supDist y y' := by
      refine Nat.sInf_le ⟨idx j, idx j', fun h => hjj (hidx h), y, ?_, y', ?_, rfl⟩
      · simp only [thickening, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨y, hA, by rw [supDist_self]; exact Nat.zero_le _⟩
      · simp only [thickening, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨y', hA', by rw [supDist_self]; exact Nat.zero_le _⟩
    have := supDist_endpoints_le c hy hy'
    have h8 := hgap v (Nat.lt_succ_self v)
    omega
private theorem measurable_initialField (ℓ : StepParameters) : (s n : ℕ) → Measurable (initialField ℓ s n)
  | 0, _ => measurable_id
  | s + 1, n => (measurable_initialField ℓ s (n * ℓ.side)).comp measurable_fst
private theorem measurable_forgetMarks (s : ℕ) : ∀ n : ℕ, Measurable (forgetMarks ℓ s n) := by apply _root_.YangMills.SharedProofs.p23598 <;> assumption
private theorem measurable_bondScore_step (hT : BondScoreProperties) (ℓ : StepParameters) (hfit : ℓ.Admissible)
    (y : ℝ) (s n : ℕ) [NeZero n] (c : TorusBond n) :
    Measurable fun u : ChainSample ℓ s (n * ℓ.side) × BaseChoice ℓ.side n × TorusField n =>
      bondScore ℓ y (finalField ℓ s (n * ℓ.side) u.1) u.2.2 u.2.1 c := by apply _root_.YangMills.SharedProofs.p2216 <;> assumption
private theorem measurable_weightedScoreSum (hT : BondScoreProperties) (ℓ : StepParameters) (hfit : ℓ.Admissible)
    (x : ℕ → ℝ) {m : ℕ} :
    (s n : ℕ) → [NeZero n] → (w : ScoreWeights ℓ m s n) → (i : Fin m) →
      Measurable (weightedScoreSum ℓ x s n w i)
  | 0, _, _, _, _ => measurable_const
  | s + 1, n, _, w, i =>
    ((measurable_weightedScoreSum hT ℓ hfit x s (n * ℓ.side) w.1 i).comp measurable_fst).add
      (Finset.measurable_sum _ fun c _ =>
        (measurable_bondScore_step hT ℓ hfit (x s) s n c).const_mul (w.2 i c))
private theorem continuous_curvatureObservable {m : ℕ} [NeZero m] (h : PlaquetteWeight m) :
    Continuous (curvatureObservable h) := by apply _root_.YangMills.SharedProofs.p1196 <;> assumption
end Weights
section Appending
variable {ℓ : StepParameters}
private def appendWeights (ℓ : StepParameters) {b : ℕ} (e e' : ℝ) : (s n : ℕ) → ScoreWeights ℓ b s n →
    ScoreWeights ℓ b s n → ScoreWeights ℓ (b + b) s n
  | 0, _, _, _ => ()
  | s + 1, n, w, w' => (appendWeights ℓ e e' s (n * ℓ.side) w.1 w'.1, fun i c =>
      Fin.addCases (motive := fun _ => ℝ) (fun j => e * w.2 j c) (fun j => e' * w'.2 j c) i)
private def NoSharedBond (ℓ : StepParameters) {b : ℕ} :
    (s n : ℕ) → ScoreWeights ℓ b s n → ScoreWeights ℓ b s n → Prop
  | 0, _, _, _ => True
  | s + 1, n, w, w' =>
    NoSharedBond ℓ s (n * ℓ.side) w.1 w'.1 ∧ ∀ (c : TorusBond n) (j j' : Fin b), w.2 j c = 0 ∨ w'.2 j' c = 0
private theorem weightedScoreSum_appendWeights_left (x : ℕ → ℝ) {b : ℕ} (e e' : ℝ) :
    ∀ (s n : ℕ) [NeZero n] (w w' : ScoreWeights ℓ b s n) (j : Fin b) (v : ChainSample ℓ s n),
    weightedScoreSum ℓ x s n (appendWeights ℓ e e' s n w w') (Fin.castAdd b j) v = e * weightedScoreSum ℓ x s n w j v
  | 0, _, _, _, _, _, _ => by simp [weightedScoreSum]
  | s + 1, n, _, w, w', j, v => by
    show weightedScoreSum ℓ x s (n * ℓ.side) (appendWeights ℓ e e' s (n * ℓ.side) w.1 w'.1) (Fin.castAdd b j) v.1 +
        ∑ c : TorusBond n, (Fin.addCases (motive := fun _ => ℝ) (fun j => e * w.2 j c) (fun j => e' * w'.2 j c)
          (Fin.castAdd b j)) * bondScore ℓ (x s) (finalField ℓ s (n * ℓ.side) v.1) v.2.2 v.2.1 c =
      e * (weightedScoreSum ℓ x s (n * ℓ.side) w.1 j v.1 +
        ∑ c : TorusBond n, w.2 j c * bondScore ℓ (x s) (finalField ℓ s (n * ℓ.side) v.1) v.2.2 v.2.1 c)
    rw [weightedScoreSum_appendWeights_left x e e' s (n * ℓ.side) w.1 w'.1 j v.1]
    simp only [Fin.addCases_left, mul_add, Finset.mul_sum, mul_assoc]
private theorem weightedScoreSum_appendWeights_right (x : ℕ → ℝ) {b : ℕ} (e e' : ℝ) :
    ∀ (s n : ℕ) [NeZero n] (w w' : ScoreWeights ℓ b s n) (j : Fin b) (v : ChainSample ℓ s n),
    weightedScoreSum ℓ x s n (appendWeights ℓ e e' s n w w') (Fin.natAdd b j) v = e' * weightedScoreSum ℓ x s n w' j v
  | 0, _, _, _, _, _, _ => by simp [weightedScoreSum]
  | s + 1, n, _, w, w', j, v => by
    show weightedScoreSum ℓ x s (n * ℓ.side) (appendWeights ℓ e e' s (n * ℓ.side) w.1 w'.1) (Fin.natAdd b j) v.1 +
        ∑ c : TorusBond n, (Fin.addCases (motive := fun _ => ℝ) (fun j => e * w.2 j c) (fun j => e' * w'.2 j c)
          (Fin.natAdd b j)) * bondScore ℓ (x s) (finalField ℓ s (n * ℓ.side) v.1) v.2.2 v.2.1 c =
      e' * (weightedScoreSum ℓ x s (n * ℓ.side) w'.1 j v.1 +
        ∑ c : TorusBond n, w'.2 j c * bondScore ℓ (x s) (finalField ℓ s (n * ℓ.side) v.1) v.2.2 v.2.1 c)
    rw [weightedScoreSum_appendWeights_right x e e' s (n * ℓ.side) w.1 w'.1 j v.1]
    simp only [Fin.addCases_right, mul_add, Finset.mul_sum, mul_assoc]
private theorem fin_add_cases {b : ℕ} (i : Fin (b + b)) : (∃ j, i = Fin.castAdd b j) ∨ ∃ j, i = Fin.natAdd b j :=
  Fin.addCases (motive := fun i => (∃ j, i = Fin.castAdd b j) ∨ ∃ j, i = Fin.natAdd b j)
    (fun j => Or.inl ⟨j, rfl⟩) (fun j => Or.inr ⟨j, rfl⟩) i
private theorem disjoint_appendWeights {b : ℕ} (e e' : ℝ) : ∀ (s n : ℕ) (w w' : ScoreWeights ℓ b s n),
    ScoreWeights.Disjoint s n w → ScoreWeights.Disjoint s n w' → NoSharedBond ℓ s n w w' →
    ScoreWeights.Disjoint s n (appendWeights ℓ e e' s n w w')
  | 0, _, _, _, _, _, _ => trivial
  | s + 1, n, w, w', h, h', hc => by
    refine ⟨disjoint_appendWeights e e' s (n * ℓ.side) w.1 w'.1 h.1 h'.1 hc.1, fun c i i' hi => ?_⟩
    show Fin.addCases (motive := fun _ => ℝ) (fun j => e * w.2 j c) (fun j => e' * w'.2 j c) i = 0 ∨
      Fin.addCases (motive := fun _ => ℝ) (fun j => e * w.2 j c) (fun j => e' * w'.2 j c) i' = 0
    have hl : ∀ j, Fin.addCases (motive := fun _ => ℝ) (fun j => e * w.2 j c) (fun j => e' * w'.2 j c)
        (Fin.castAdd b j) = e * w.2 j c := fun j => Fin.addCases_left _
    have hr : ∀ j, Fin.addCases (motive := fun _ => ℝ) (fun j => e * w.2 j c) (fun j => e' * w'.2 j c)
        (Fin.natAdd b j) = e' * w'.2 j c := fun j => Fin.addCases_right _
    rcases fin_add_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;> rcases fin_add_cases i' with ⟨j', rfl⟩ | ⟨j', rfl⟩
    · have hj : j ≠ j' := fun q => hi (by rw [q])
      rw [hl, hl]
      rcases h.2 c j j' hj with q | q
      · exact Or.inl (by rw [q, mul_zero])
      · exact Or.inr (by rw [q, mul_zero])
    · rw [hl, hr]
      rcases hc.2 c j j' with q | q
      · exact Or.inl (by rw [q, mul_zero])
      · exact Or.inr (by rw [q, mul_zero])
    · rw [hr, hl]
      rcases hc.2 c j' j with q | q
      · exact Or.inr (by rw [q, mul_zero])
      · exact Or.inl (by rw [q, mul_zero])
    · have hj : j ≠ j' := fun q => hi (by rw [q])
      rw [hr, hr]
      rcases h'.2 c j j' hj with q | q
      · exact Or.inl (by rw [q, mul_zero])
      · exact Or.inr (by rw [q, mul_zero])
private theorem disjoint_translateWeights {b : ℕ} :
    ∀ (s n : ℕ) [NeZero n] (a : Fin 4 → ℤ) (w : ScoreWeights ℓ b s n),
    ScoreWeights.Disjoint s n w → ScoreWeights.Disjoint s n (translateWeights ℓ s n a w)
  | 0, _, _, _, _, _ => trivial
  | s + 1, n, _, a, w, h =>
    ⟨disjoint_translateWeights s (n * ℓ.side) (scaleVec ℓ.side a) w.1 h.1,
      fun c i i' hi => h.2 (c.1 - siteOfInt a, c.2) i i' hi⟩
private theorem noSharedBond_translate {k m : ℕ} (P : LevelData k) (al : ℕ → ℝ) (idx : Fin m → Fin k)
    (base : Fin 4 → ℤ) :
    ∀ (v : ℕ), v ≤ P.windowLevel → ∀ (N : ℕ) [NeZero N], N = P.sideAt ℓ.side v →
      (∀ u < v, ∀ i j : Fin k, ∀ y ∈ P.supportSites ℓ.side (u + 1) i, ∀ y' ∈ P.supportSites ℓ.side (u + 1) j,
        1 < TorusFields.supDist y (y' + siteOfInt fun b => (ℓ.side : ℤ) ^ (P.windowLevel - (u + 1)) * base b)) →
      ∀ a : Fin 4 → ℤ, a = (fun b => (ℓ.side : ℤ) ^ (P.windowLevel - v) * base b) →
      NoSharedBond ℓ v N (scoreWeightsOf ℓ al v N fun j => P.testWeight ℓ.side (idx j) (fineSide ℓ.side v N))
        (translateWeights ℓ v N a
          (scoreWeightsOf ℓ al v N fun j => P.testWeight ℓ.side (idx j) (fineSide ℓ.side v N))) := by
  intro v
  induction v with
  | zero =>
    intro _ N _ _ _ _ _
    exact trivial
  | succ v ih =>
    intro hv N _ hN hfar a ha
    refine ⟨ih (by omega) (N * ℓ.side) (by rw [hN]; exact sideAt_succ_mul P ℓ.side v hv)
      (fun u hu => hfar u (by omega)) (scaleVec ℓ.side a) ?_, ?_⟩
    · rw [ha]
      funext b
      have : P.windowLevel - v = (P.windowLevel - (v + 1)) + 1 := by omega
      simp only [scaleVec]
      rw [this, pow_succ]
      ring
    intro c j j'
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    subst hN
    have ha' : a = fun b => (ℓ.side : ℤ) ^ (P.windowLevel - (v + 1)) * base b := ha
    obtain ⟨y, hy, hyn⟩ := exists_endpoint_of_bondCoeff _ _ _ _ c h1
    obtain ⟨y', hy', hyn'⟩ := exists_endpoint_of_bondCoeff _ _ _ _ (c.1 - siteOfInt a, c.2) h2
    have hA := mem_weightSupportSites_of_blockMean ℓ.side _ _ _ _ hyn
    have hA' := mem_weightSupportSites_of_blockMean ℓ.side _ _ _ _ hyn'
    have hf := hfar v (Nat.lt_succ_self v) (idx j) (idx j') y hA y' hA'
    rw [← ha'] at hf
    have he : y' + siteOfInt a = c.1 ∨ y' + siteOfInt a = c.1 + unitStep _ c.2 := by
      rcases hy' with q | q
      · left
        rw [q]
        simp
      · right
        rw [q]
        show c.1 - siteOfInt a + unitStep _ c.2 + siteOfInt a = _
        abel
    have := supDist_endpoints_le c hy he
    omega
end Appending
section FarSites
variable {ℓ : StepParameters}
private theorem supDist_translate_supportSites (hD : SupportSiteDistanceBounds) (hodd : Odd ℓ.side) {k : ℕ}
    (P : LevelData k) (R d : ℝ) (hd : 0 < d) (hP : P.Admissible ℓ.side (2 * R) d) (κ : ℕ)
    (hκ : 4 * |R| + 3 ≤ (κ : ℝ)) (htop : 2 * (κ * ℓ.side) ≤ P.period ℓ.side)
    (u : ℕ) (hu : u + 1 ≤ P.windowLevel) (i j : Fin k) (y : TorusSite (P.sideAt ℓ.side (u + 1)))
    (hy : y ∈ P.supportSites ℓ.side (u + 1) i)
    (y' : TorusSite (P.sideAt ℓ.side (u + 1))) (hy' : y' ∈ P.supportSites ℓ.side (u + 1) j) :
    1 < TorusFields.supDist y (y' + siteOfInt fun b => (ℓ.side : ℤ) ^ (P.windowLevel - (u + 1)) *
      (Pi.single 0 ((κ * ℓ.side : ℕ) : ℤ) : Fin 4 → ℤ) b) := by
  by_contra hcon
  push_neg at hcon
  set Q : ℕ := ℓ.side ^ (P.windowLevel - (u + 1)) with hQ
  have hL1 : 1 ≤ ℓ.side := hodd.pos
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ hodd.pos
  set A : TorusSite (P.sideAt ℓ.side (u + 1)) :=
    siteOfInt fun b => (ℓ.side : ℤ) ^ (P.windowLevel - (u + 1)) *
      (Pi.single 0 ((κ * ℓ.side : ℕ) : ℤ) : Fin 4 → ℤ) b with hA
  have hdist := (hD ℓ.side hodd k (2 * R) d hd P hP (u + 1) hu i j y hy y' hy').1
  have htri : TorusFields.supDist y' (y' + A) ≤ TorusFields.supDist y' y + TorusFields.supDist y (y' + A) :=
    supDist_triangle _ _ _
  have hlow : Q * (κ * ℓ.side) ≤ TorusFields.supDist y' (y' + A) := by
    rw [supDist_comm]
    have hA0 : (y' + A) 0 - y' 0 = ((Q * (κ * ℓ.side) : ℕ) : ZMod (P.sideAt ℓ.side (u + 1))) := by
      simp [hA, siteOfInt, hQ]
    have hhalf : Q * (κ * ℓ.side) ≤ P.sideAt ℓ.side (u + 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      have : P.sideAt ℓ.side (u + 1) = P.period ℓ.side * Q := rfl
      rw [this]
      calc Q * (κ * ℓ.side) * 2 = (2 * (κ * ℓ.side)) * Q := by ring
        _ ≤ P.period ℓ.side * Q := Nat.mul_le_mul_right _ htop
    have hv := ZMod.valMinAbs_natCast_of_le_half hhalf
    have hle : (((y' + A) 0 - y' 0).valMinAbs).natAbs ≤ TorusFields.supDist (y' + A) y' :=
      Finset.le_sup (f := fun i => (((y' + A) i - y' i).valMinAbs).natAbs) (Finset.mem_univ (0 : Fin 4))
    rw [hA0, hv, Int.natAbs_natCast] at hle
    exact hle
  have hreal : ((Q * (κ * ℓ.side) : ℕ) : ℝ) ≤
      2 * (2 * R) * (ℓ.side : ℝ) ^ ((P.scaleLevel : ℤ) - ((u + 1 : ℕ) : ℤ)) + 2 := by
    have h1 : ((Q * (κ * ℓ.side) : ℕ) : ℝ) ≤
        ((TorusFields.supDist y' y + TorusFields.supDist y (y' + A) : ℕ) : ℝ) := by
      exact_mod_cast hlow.trans htri
    have h2 : ((TorusFields.supDist y (y' + A) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hcon
    have h3 : ((TorusFields.supDist y' y : ℕ) : ℝ) = (TorusFields.supDist y y' : ℝ) := by rw [supDist_comm]
    push_cast at h1 ⊢
    push_cast at hdist
    linarith
  have hL1r : (1 : ℝ) ≤ (ℓ.side : ℝ) := by exact_mod_cast hL1
  have hQr : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
  have hz : (ℓ.side : ℝ) ^ ((P.scaleLevel : ℤ) - ((u + 1 : ℕ) : ℤ)) ≤ (Q : ℝ) := by
    have hs : P.scaleLevel ≤ P.windowLevel := hP.scaleLevel_le
    have : (Q : ℝ) = (ℓ.side : ℝ) ^ (((P.windowLevel - (u + 1) : ℕ) : ℤ)) := by
      rw [hQ, zpow_natCast]
      push_cast
      rfl
    rw [this]
    refine zpow_le_zpow_right₀ hL1r ?_
    omega
  have hz0 : 0 ≤ (ℓ.side : ℝ) ^ ((P.scaleLevel : ℤ) - ((u + 1 : ℕ) : ℤ)) := by positivity
  have hb : 2 * (2 * R) * (ℓ.side : ℝ) ^ ((P.scaleLevel : ℤ) - ((u + 1 : ℕ) : ℤ)) ≤ 4 * |R| * (Q : ℝ) := by
    have h1 : R ≤ |R| := le_abs_self R
    have h2 : 0 ≤ |R| := abs_nonneg R
    nlinarith
  have hbig : ((4 * |R| + 3) * (Q : ℝ)) ≤ ((Q * (κ * ℓ.side) : ℕ) : ℝ) := by
    push_cast
    have h1 : (κ : ℝ) ≤ (κ : ℝ) * (ℓ.side : ℝ) := by nlinarith
    have h2 : 4 * |R| + 3 ≤ (κ : ℝ) * (ℓ.side : ℝ) := hκ.trans h1
    nlinarith
  nlinarith
end FarSites
section ErgodicMeans
variable {J : Type} {P : Measure (TranslateValues J)} [IsProbabilityMeasure P]
private theorem translateShift_iterate_apply (k : ℕ) (v : TranslateValues J) (a : J) (m : ℕ) :
    ((translateShift (J := J))^[k] v) (a, m) = v (a, m + k) := by
  induction k generalizing v m with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    rfl
abbrev _root_.YangMills.SharedProofs.p49195 := @translateShift_iterate_apply
private theorem invariantCondExp_eq_of_far_uncorrelated (hS : MeasurePreserving (translateShift (J := J)) P P)
    {j j' : J}
    (hint : ∀ (a b : J) (k l : ℕ), Integrable (fun v : TranslateValues J => v (a, k) * v (b, l)) P)
    (havg : ∀ j, Tendsto (fun M : ℕ => eLpNorm (fun v : TranslateValues J =>
        (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (j, k) - invariantCondExp P (evalAtZero j) v) 2 P) atTop (𝓝 0))
    (k₀ : ℕ)
    (hfar : ∀ k, k₀ ≤ k → ∫ v : TranslateValues J, (v (j', 0) - v (j, 0)) * (v (j', k) - v (j, k)) ∂P = 0) :
    invariantCondExp P (evalAtZero j') =ᵐ[P] invariantCondExp P (evalAtZero j) := by
  have hmeas : ∀ (a : J) (k : ℕ), Measurable fun v : TranslateValues J => v (a, k) := fun a k =>
    measurable_pi_apply _
  have hL2 : ∀ (a : J) (k : ℕ), MemLp (fun v : TranslateValues J => v (a, k)) 2 P := fun a k =>
    (memLp_two_iff_integrable_sq (hmeas a k).aestronglyMeasurable).2 (by simpa [sq] using hint a a k k)
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → TranslateValues J → ℝ, Y = fun k v => v (j', k) - v (j, k) := ⟨_, rfl⟩
  have hYv : ∀ k v, Y k v = v (j', k) - v (j, k) := fun k v => by rw [hY]
  have hYm : ∀ k, Measurable (Y k) := fun k => by
    rw [hY]
    exact (hmeas j' k).sub (hmeas j k)
  have hY2 : ∀ k, MemLp (Y k) 2 P := fun k => by
    rw [hY]
    exact (hL2 j' k).sub (hL2 j k)
  have hYY : ∀ k l, Integrable (fun v => Y k v * Y l v) P := fun k l => (hY2 k).integrable_mul (hY2 l)
  obtain ⟨aa, haa⟩ : ∃ aa : ℕ → ℝ, aa = fun d => ∫ v, Y 0 v * Y d v ∂P := ⟨_, rfl⟩
  have hshift : ∀ k d, ∫ v, Y k v * Y (k + d) v ∂P = aa d := by
    intro k d
    have hp := hS.iterate k
    have hm : AEStronglyMeasurable (fun v => Y 0 v * Y d v) (Measure.map ((translateShift (J := J))^[k]) P) :=
      ((hYm 0).mul (hYm d)).aestronglyMeasurable
    have h1 : ∫ v, Y k v * Y (k + d) v ∂P =
        ∫ v, (fun v => Y 0 v * Y d v) ((translateShift (J := J))^[k] v) ∂P := by
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [hYv, translateShift_iterate_apply, zero_add, add_comm d k]
    rw [h1, ← integral_map hp.aemeasurable hm, hp.map_eq, haa]
  have hzero : ∀ d, k₀ ≤ d → aa d = 0 := by
    intro d hd
    rw [haa]
    simp only [hYv]
    exact hfar d hd
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ d ∈ Finset.range k₀, |aa d| := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hle : ∀ d, d < k₀ → |aa d| ≤ A := fun d hd => by
    rw [hA]
    exact Finset.single_le_sum (f := fun d => |aa d|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 hd)
  have hent : ∀ k l, |∫ v, Y k v * Y l v ∂P| ≤ if l ∈ Finset.Ico (k + 1 - k₀) (k + k₀) then A else 0 := by
    intro k l
    rcases le_total k l with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [hshift]
      by_cases hd : d < k₀
      · rw [if_pos (Finset.mem_Ico.2 ⟨by omega, by omega⟩)]
        exact hle d hd
      · rw [hzero d (by omega), abs_zero]
        split_ifs
        · exact hA0
        · exact le_rfl
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      have e : ∫ v, Y (l + d) v * Y l v ∂P = aa d := by
        rw [← hshift l d]
        exact integral_congr_ae (Eventually.of_forall fun v => mul_comm _ _)
      rw [e]
      by_cases hd : d < k₀
      · rw [if_pos (Finset.mem_Ico.2 ⟨by omega, by omega⟩)]
        exact hle d hd
      · rw [hzero d (by omega), abs_zero]
        split_ifs
        · exact hA0
        · exact le_rfl
  have hrow : ∀ k M, ∑ l ∈ Finset.range M, |∫ v, Y k v * Y l v ∂P| ≤ (2 * k₀ : ℝ) * A := by
    intro k M
    calc ∑ l ∈ Finset.range M, |∫ v, Y k v * Y l v ∂P|
        ≤ ∑ l ∈ Finset.range M, if l ∈ Finset.Ico (k + 1 - k₀) (k + k₀) then A else 0 :=
          Finset.sum_le_sum fun l _ => hent k l
      _ = ((Finset.range M ∩ Finset.Ico (k + 1 - k₀) (k + k₀)).card : ℝ) * A := by
          rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * k₀ : ℝ) * A := by
          refine mul_le_mul_of_nonneg_right ?_ hA0
          have h1 : (Finset.range M ∩ Finset.Ico (k + 1 - k₀) (k + k₀)).card ≤ 2 * k₀ := by
            refine (Finset.card_le_card Finset.inter_subset_right).trans ?_
            rw [Nat.card_Ico]
            omega
          exact_mod_cast h1
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (2 * k₀ : ℝ) * A := ⟨_, rfl⟩
  obtain ⟨Bm, hBm⟩ : ∃ Bm : ℕ → TranslateValues J → ℝ,
      Bm = fun (M : ℕ) v => (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, Y k v := ⟨_, rfl⟩
  have hBv : ∀ M v, Bm M v = (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, Y k v := fun M v => by rw [hBm]
  have hB2 : ∀ M, MemLp (Bm M) 2 P := fun M => by
    rw [hBm]
    exact (memLp_finset_sum _ fun k _ => hY2 k).const_mul _
  have hsq : ∀ M : ℕ, ∫ v, Bm M v ^ 2 ∂P ≤ C * (M : ℝ)⁻¹ := by
    intro M
    have h1 : ∫ v, Bm M v ^ 2 ∂P =
        ((M : ℝ)⁻¹) ^ 2 * ∑ k ∈ Finset.range M, ∑ l ∈ Finset.range M, ∫ v, Y k v * Y l v ∂P := by
      have e : ∀ v, Bm M v ^ 2 =
          ((M : ℝ)⁻¹) ^ 2 * ∑ k ∈ Finset.range M, ∑ l ∈ Finset.range M, Y k v * Y l v := fun v => by
        rw [hBv, mul_pow, sq (∑ k ∈ Finset.range M, Y k v), Finset.sum_mul_sum]
      simp only [e]
      rw [integral_const_mul, integral_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => hYY k l]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finset_sum _ fun l _ => hYY k l]
    have h2 : ∑ k ∈ Finset.range M, ∑ l ∈ Finset.range M, ∫ v, Y k v * Y l v ∂P ≤ (M : ℝ) * C := by
      calc ∑ k ∈ Finset.range M, ∑ l ∈ Finset.range M, ∫ v, Y k v * Y l v ∂P
          ≤ ∑ k ∈ Finset.range M, C := by
            refine Finset.sum_le_sum fun k _ => ?_
            calc ∑ l ∈ Finset.range M, ∫ v, Y k v * Y l v ∂P
                ≤ ∑ l ∈ Finset.range M, |∫ v, Y k v * Y l v ∂P| := Finset.sum_le_sum fun l _ => le_abs_self _
              _ ≤ C := by
                  rw [hC]
                  exact hrow k M
        _ = (M : ℝ) * C := by simp
    rw [h1]
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · have hM' : (0 : ℝ) < M := by exact_mod_cast hM
      calc ((M : ℝ)⁻¹) ^ 2 * ∑ k ∈ Finset.range M, ∑ l ∈ Finset.range M, ∫ v, Y k v * Y l v ∂P
          ≤ ((M : ℝ)⁻¹) ^ 2 * ((M : ℝ) * C) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = C * (M : ℝ)⁻¹ := by
            field_simp
  have hsq0 : Tendsto (fun M : ℕ => ∫ v, Bm M v ^ 2 ∂P) atTop (𝓝 0) := by
    have hup : Tendsto (fun M : ℕ => C * (M : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    exact squeeze_zero (fun M => integral_nonneg fun v => sq_nonneg _) hsq hup
  have hnorm : ∀ M, eLpNorm (Bm M) 2 P = ENNReal.ofReal ((∫ v, Bm M v ^ 2 ∂P) ^ (2 : ℝ)⁻¹) := by
    intro M
    rw [(hB2 M).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hB0 : Tendsto (fun M => eLpNorm (Bm M) 2 P) atTop (𝓝 0) := by
    simp only [hnorm]
    have h1 : Tendsto (fun M : ℕ => (∫ v, Bm M v ^ 2 ∂P) ^ (2 : ℝ)⁻¹) atTop (𝓝 ((0 : ℝ) ^ (2 : ℝ)⁻¹)) :=
      hsq0.rpow_const (Or.inr (by norm_num))
    rw [Real.zero_rpow (by norm_num)] at h1
    simpa using ENNReal.tendsto_ofReal h1
  have hstar : ∀ a : J, AEStronglyMeasurable (invariantCondExp P (evalAtZero a)) P := fun a =>
    (stronglyMeasurable_condExp.mono inf_le_right).aestronglyMeasurable
  obtain ⟨E, hE⟩ : ∃ E : J → ℕ → TranslateValues J → ℝ, E = fun a (M : ℕ) v =>
      (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (a, k) - invariantCondExp P (evalAtZero a) v := ⟨_, rfl⟩
  have hEm : ∀ a M, AEStronglyMeasurable (E a M) P := fun a M => by
    rw [hE]
    exact (((Finset.measurable_sum _ fun k _ => hmeas a k).const_mul _).aestronglyMeasurable).sub (hstar a)
  have hbound : ∀ M, eLpNorm (invariantCondExp P (evalAtZero j') - invariantCondExp P (evalAtZero j)) 2 P ≤
      eLpNorm (Bm M) 2 P + (eLpNorm (E j' M) 2 P + eLpNorm (E j M) 2 P) := by
    intro M
    have e : invariantCondExp P (evalAtZero j') - invariantCondExp P (evalAtZero j) = Bm M - (E j' M - E j M) := by
      funext v
      simp only [Pi.sub_apply, hBv, hYv, hE, Finset.sum_sub_distrib]
      ring
    rw [e]
    refine (eLpNorm_sub_le (hB2 M).1 ((hEm j' M).sub (hEm j M)) (by norm_num)).trans ?_
    gcongr
    exact eLpNorm_sub_le (hEm j' M) (hEm j M) (by norm_num)
  have hlim : Tendsto (fun M => eLpNorm (Bm M) 2 P + (eLpNorm (E j' M) 2 P + eLpNorm (E j M) 2 P)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun M => eLpNorm (E j' M) 2 P) atTop (𝓝 0) := by
      rw [hE]
      exact havg j'
    have h2 : Tendsto (fun M => eLpNorm (E j M) 2 P) atTop (𝓝 0) := by
      rw [hE]
      exact havg j
    simpa using hB0.add (h1.add h2)
  have h0 : eLpNorm (invariantCondExp P (evalAtZero j') - invariantCondExp P (evalAtZero j)) 2 P = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) (by simp)
  have h1 := (eLpNorm_eq_zero_iff ((hstar j').sub (hstar j)) two_ne_zero).1 h0
  filter_upwards [h1] with v hv
  exact sub_eq_zero.1 hv
end ErgodicMeans
section TorusProducts
variable {ℓ : StepParameters}
private theorem curvature_bottomField_sampleBelow (g : (m : ℕ) → PlaquetteWeight m) (t : ℕ) :
    ∀ (d N : ℕ) [NeZero N] (w : MarkedSample ℓ (t + d) N),
    curvatureObservable (g (fineSide ℓ.side (t + d) N)) (bottomField ℓ (t + d) N w) =
      curvatureObservable (g (fineSide ℓ.side t (fineSide ℓ.side d N)))
        (bottomField ℓ t (fineSide ℓ.side d N) (sampleBelow ℓ t d N w))
  | 0, _, _, _ => rfl
  | d + 1, N, _, w => curvature_bottomField_sampleBelow g t d (N * ℓ.side) w.1
private def centredProduct (T : StageTower ℓ) (al : ℕ → ℝ) {k : ℕ} (P : LevelData k) (cc : Fin k → ℝ)
    (B : Finset (Fin k)) (K t d : ℕ) (e : t + d = K) (N : ℕ) [NeZero N] : Bool → MarkedSample ℓ K N → ℝ
  | true, w => ∏ i ∈ B, (WeightedResponses.completedObservable T al t (fineSide ℓ.side d N)
      (P.testWeight ℓ.side i _) (sampleBelow ℓ t d N (e.symm ▸ w)) - cc i)
  | false, w => ∏ i ∈ B, (curvatureObservable (P.testWeight ℓ.side i _) (bottomField ℓ K N w) - cc i)
private def indicatorValue : Bool → ℝ
  | true => 1
  | false => 0
private theorem integral_centredProduct_translate (hS : ScoresPreserveCorrelations)
    (hT : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement) (hSc : BondScoreProperties)
    (hBs : HullTrees.translationCarriesBasesStatement) (hB : ResponseInTheExpansion.sampleBelowLawStatement)
    (hR : ruleDrawsChainStatement) (hf : ℓ.Admissible) (T : StageTower ℓ)
    (hcut : ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn) (hcoin : T.MarksMeasurable)
    (rule : NoiseRule ℓ) (hr : rule.IsAdmissible T) (β : ℝ) (al : ℕ → ℝ) {k : ℕ} (P : LevelData k)
    (cc : Fin k → ℝ) (B : Finset (Fin k)) (K t d : ℕ) (e : t + d = K) (hK : P.windowLevel = K)
    (N : ℕ) [NeZero N] (hN : N = P.period ℓ.side) (hLN : ℓ.side ∣ N) (h64 : 64 ≤ N)
    (hgap : ∀ u < t, 8 < P.separation ℓ.side u) (a : Fin 4 → ℤ)
    (hcr : ∀ u < t, ∀ i j : Fin k, ∀ y ∈ P.supportSites ℓ.side (u + 1) i, ∀ y' ∈ P.supportSites ℓ.side (u + 1) j,
      1 < TorusFields.supDist y (y' + siteOfInt fun b => (ℓ.side : ℤ) ^ (P.windowLevel - (u + 1)) * a b))
    (ε ε' : Bool) :
    ∫ ω, centredProduct T al P cc B K t d e N ε (rule.chain T K N ω.1 ω.2) *
        centredProduct T al P cc B K t d e N ε'
          (rule.chain T K N (pairTranslate ℓ K N a ω).1 (pairTranslate ℓ K N a ω).2)
        ∂((wilsonLaw β (fineSide ℓ.side K N)).prod (chainNoiseLaw ℓ K N)) =
      ∫ ω, centredProduct T al P cc B K t d e N false (rule.chain T K N ω.1 ω.2) *
        centredProduct T al P cc B K t d e N false
          (rule.chain T K N (pairTranslate ℓ K N a ω).1 (pairTranslate ℓ K N a ω).2)
        ∂((wilsonLaw β (fineSide ℓ.side K N)).prod (chainNoiseLaw ℓ K N)) := by
  subst e
  have hL := hf.depth_lt
  have hside : fineSide ℓ.side d N = P.sideAt ℓ.side t := by
    rw [fineSide_eq, hN]
    unfold LevelData.sideAt
    rw [hK, Nat.add_sub_cancel_left]
  have htK : t ≤ P.windowLevel := by omega
  have hd' : P.windowLevel - t = d := by omega
  have hmw := measurable_forgetMarks (ℓ := ℓ) t (fineSide ℓ.side d N)
  obtain ⟨-, -, -, hchain, -, -⟩ := hT ℓ hf hL T hcut hcoin β al t (fineSide ℓ.side d N)
  obtain ⟨hbm, hbl⟩ := (hB ℓ hf hL T hcut hcoin β al).1 t d N
  obtain ⟨hcm, hcl⟩ := hR ℓ hf T rule β hcut hcoin hr (t + d) N hLN h64
  let e₀ : Fin B.card ≃ {i // i ∈ B} := B.equivFin.symm
  let idx : Fin B.card → Fin k := fun j => (e₀ j).1
  have hidx : Function.Injective idx := fun a b h => e₀.injective (Subtype.ext h)
  let h : Fin B.card → PlaquetteWeight (fineSide ℓ.side t (fineSide ℓ.side d N)) :=
    fun j => P.testWeight ℓ.side (idx j) _
  let w₀ := scoreWeightsOf ℓ al t (fineSide ℓ.side d N) h
  have hsep₀ : ScoreWeights.Disjoint t (fineSide ℓ.side d N) w₀ :=
    disjoint_scoreWeightsOf P al idx hidx t htK _ hside hgap
  let a' : Fin 4 → ℤ := fun i => (ℓ.side : ℤ) ^ d * a i
  let w₁ := translateWeights ℓ t (fineSide ℓ.side d N) a' w₀
  have hsep₁ : ScoreWeights.Disjoint t (fineSide ℓ.side d N) w₁ := disjoint_translateWeights t _ a' w₀ hsep₀
  have hcross : NoSharedBond ℓ t (fineSide ℓ.side d N) w₀ w₁ :=
    noSharedBond_translate P al idx a t htK _ hside hcr a' (by rw [hd'])
  let x : ℕ → ℝ := fun j => (T.stage j).coupling
  let X : Fin B.card → TorusField (fineSide ℓ.side t (fineSide ℓ.side d N)) → ℝ := fun j => curvatureObservable (h j)
  have hXm : ∀ j, Measurable (X j) := fun j => (continuous_curvatureObservable (h j)).measurable
  have hXb : ∀ j, ∃ C : ℝ, ∀ W, |X j W| ≤ C := by
    intro j
    obtain ⟨C, hC⟩ :=
      isCompact_univ.exists_bound_of_continuousOn (continuous_curvatureObservable (h j)).continuousOn
    exact ⟨C, fun W => by simpa using hC W (Set.mem_univ _)⟩
  let A : TorusSite (fineSide ℓ.side t (fineSide ℓ.side d N)) := siteOfInt fun i => (ℓ.side : ℤ) ^ t * a' i
  have hAm : Measurable (TorusFields.translate A : TorusField _ → TorusField _) :=
    measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
      (measurable_pi_apply i).comp (measurable_pi_apply (x + A))
  let Z : Fin (B.card + B.card) → TorusField (fineSide ℓ.side t (fineSide ℓ.side d N)) → ℝ :=
    Fin.addCases (motive := fun _ => TorusField (fineSide ℓ.side t (fineSide ℓ.side d N)) → ℝ) X
      (fun j W => X j (TorusFields.translate A W))
  let κ : Fin (B.card + B.card) → ℝ :=
    Fin.addCases (motive := fun _ => ℝ) (fun j => cc (idx j)) (fun j => cc (idx j))
  have hZl : ∀ j, Z (Fin.castAdd B.card j) = X j := fun j => Fin.addCases_left _
  have hZr : ∀ j, Z (Fin.natAdd B.card j) = fun W => X j (TorusFields.translate A W) :=
    fun j => Fin.addCases_right _
  have hκl : ∀ j, κ (Fin.castAdd B.card j) = cc (idx j) := fun j => Fin.addCases_left _
  have hκr : ∀ j, κ (Fin.natAdd B.card j) = cc (idx j) := fun j => Fin.addCases_right _
  have hZm : ∀ i, Measurable (Z i) := by
    intro i
    rcases fin_add_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [hZl]
      exact hXm j
    · rw [hZr]
      exact (hXm j).comp hAm
  have hZb : ∀ i, ∃ C : ℝ, ∀ W, |Z i W| ≤ C := by
    intro i
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ j W, |X j W| ≤ C := by
      choose Cj hCj using hXb
      refine ⟨∑ j, |Cj j|, fun j W => (hCj j W).trans ((le_abs_self _).trans ?_)⟩
      exact Finset.single_le_sum (f := fun j => |Cj j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    refine ⟨C, fun W => ?_⟩
    rcases fin_add_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [hZl]
      exact hC j W
    · rw [hZr]
      exact hC j _
  have hprod : ∀ g : Fin k → ℝ, ∏ i ∈ B, g i = ∏ j : Fin B.card, g (idx j) := by
    intro g
    rw [← Finset.prod_coe_sort B g]
    exact (Equiv.prod_comp e₀ fun i : {i // i ∈ B} => g i.1).symm
  let Φ : Bool → ChainSample ℓ t (fineSide ℓ.side d N) → ℝ := fun ε v =>
    ∏ j, (X j (initialField ℓ t _ v) + indicatorValue ε * weightedScoreSum ℓ x t _ w₀ j v - cc (idx j))
  have hread : ∀ (ε : Bool) (w : MarkedSample ℓ (t + d) N), centredProduct T al P cc B (t + d) t d rfl N ε w =
      Φ ε (forgetMarks ℓ t _ (sampleBelow ℓ t d N w)) := by
    intro ε w
    cases ε with
    | false =>
      show ∏ i ∈ B, (curvatureObservable (P.testWeight ℓ.side i _) (bottomField ℓ (t + d) N w) - cc i) = _
      rw [hprod]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [curvature_bottomField_sampleBelow (P.testWeight ℓ.side (idx j)) t d N w, initialField_forgetMarks]
      simp [indicatorValue, X, h]
    | true =>
      show ∏ i ∈ B, (WeightedResponses.completedObservable T al t (fineSide ℓ.side d N) (P.testWeight ℓ.side i _)
        (sampleBelow ℓ t d N w) - cc i) = _
      rw [hprod]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [initialField_forgetMarks, weightedScoreSum_scoreWeightsOf T al t (fineSide ℓ.side d N) h j]
      simp only [indicatorValue, one_mul]
      rfl
  have hmove : ∀ ω : TorusField (fineSide ℓ.side (t + d) N) × ChainNoise.ChainNoise ℓ (t + d) N,
      forgetMarks ℓ t _ (sampleBelow ℓ t d N (rule.chain T (t + d) N (pairTranslate ℓ (t + d) N a ω).1
        (pairTranslate ℓ (t + d) N a ω).2)) =
        translateChain ℓ t _ a' (forgetMarks ℓ t _ (sampleBelow ℓ t d N (rule.chain T (t + d) N ω.1 ω.2))) := by
    intro ω
    show forgetMarks ℓ t _ (sampleBelow ℓ t d N (rule.chain T (t + d) N
      (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ (t + d) * a i) ω.1)
        (noiseTranslate ℓ (t + d) N a ω.2))) = _
    rw [forgetMarks_sampleBelow, chain_translate rule T hr, chainPrefix_translate, ← forgetMarks_sampleBelow]
  have hΦ : ∀ (ε : Bool) (v : ChainSample ℓ t (fineSide ℓ.side d N)), Φ ε (translateChain ℓ t _ a' v) =
      ∏ j, (X j (TorusFields.translate A (initialField ℓ t _ v)) + indicatorValue ε * weightedScoreSum ℓ x t _ w₁ j v -
        cc (idx j)) := by
    intro ε v
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [initialField_translateChain, weightedScoreSum_translateChain hSc hBs hf x]
  have key : ∀ ε ε' : Bool, ∫ ω, centredProduct T al P cc B (t + d) t d rfl N ε (rule.chain T (t + d) N ω.1 ω.2) *
        centredProduct T al P cc B (t + d) t d rfl N ε'
          (rule.chain T (t + d) N (pairTranslate ℓ (t + d) N a ω).1 (pairTranslate ℓ (t + d) N a ω).2)
        ∂((wilsonLaw β (fineSide ℓ.side (t + d) N)).prod (chainNoiseLaw ℓ (t + d) N)) =
      ∫ v, ∏ i, (Z i (initialField ℓ t _ v) - κ i) ∂(chainJointLaw ℓ β x t (fineSide ℓ.side d N)) := by
    intro ε ε'
    let Jc := appendWeights ℓ (indicatorValue ε) (indicatorValue ε') t (fineSide ℓ.side d N) w₀ w₁
    have hJ : ScoreWeights.Disjoint t (fineSide ℓ.side d N) Jc :=
      disjoint_appendWeights _ _ t _ w₀ w₁ hsep₀ hsep₁ hcross
    have main := hS ℓ hf hL β x t (fineSide ℓ.side d N) (B.card + B.card) Z Jc κ hZm hZb hJ
    rw [← main]
    let F : ChainSample ℓ t (fineSide ℓ.side d N) → ℝ := fun v =>
      ∏ i, (Z i (initialField ℓ t _ v) + weightedScoreSum ℓ x t _ Jc i v - κ i)
    have hFm : Measurable F := Finset.measurable_fun_prod _ fun i _ =>
      (((hZm i).comp (measurable_initialField ℓ _ _)).add
        (measurable_weightedScoreSum hSc ℓ hf _ t _ Jc i)).sub measurable_const
    have hpt : ∀ v, Φ ε v * Φ ε' (translateChain ℓ t _ a' v) = F v := by
      intro v
      rw [hΦ]
      show _ = ∏ i, (Z i (initialField ℓ t _ v) + weightedScoreSum ℓ x t _ Jc i v - κ i)
      rw [Fin.prod_univ_add]
      congr 1
      · refine Finset.prod_congr rfl fun j _ => ?_
        rw [hZl, hκl, weightedScoreSum_appendWeights_left]
      · refine Finset.prod_congr rfl fun j _ => ?_
        rw [hZr, hκr, weightedScoreSum_appendWeights_right]
    have hstep : ∫ ω, F (forgetMarks ℓ t _ (sampleBelow ℓ t d N (rule.chain T (t + d) N ω.1 ω.2)))
        ∂((wilsonLaw β (fineSide ℓ.side (t + d) N)).prod (chainNoiseLaw ℓ (t + d) N)) =
        ∫ v, F v ∂(chainJointLaw ℓ β x t (fineSide ℓ.side d N)) := by
      rw [← hchain, integral_map hmw.aemeasurable hFm.aestronglyMeasurable, ← hbl,
        integral_map (f := fun u => F (forgetMarks ℓ t _ u)) hbm.aemeasurable (hFm.comp hmw).aestronglyMeasurable,
        ← hcl,
        integral_map (f := fun u => F (forgetMarks ℓ t _ (sampleBelow ℓ t d N u))) hcm.aemeasurable
          ((hFm.comp hmw).comp hbm).aestronglyMeasurable]
    refine Eq.trans (integral_congr_ae (Eventually.of_forall fun ω => ?_)) hstep
    show centredProduct T al P cc B (t + d) t d rfl N ε _ * centredProduct T al P cc B (t + d) t d rfl N ε' _ = _
    rw [hread, hread, hmove, hpt]
  exact (key ε ε').trans (key false false).symm
end TorusProducts
section Invariance
variable {ℓ : StepParameters}
private theorem chainNoiseLaw_isProbability : ∀ (s n : ℕ) [NeZero n], IsProbabilityMeasure (chainNoiseLaw ℓ s n)
  | 0, _, _ => by
    show IsProbabilityMeasure (Measure.dirac () : Measure Unit)
    infer_instance
  | s + 1, n, _ => by
    letI := instMeasurableSpaceChainNoise ℓ s (n * ℓ.side)
    haveI := chainNoiseLaw_isProbability s (n * ℓ.side)
    haveI : IsProbabilityMeasure (stepNoiseLaw ℓ n) := by
      unfold stepNoiseLaw
      infer_instance
    show IsProbabilityMeasure ((chainNoiseLaw ℓ s (n * ℓ.side)).prod (stepNoiseLaw ℓ n))
    infer_instance
private theorem measurePreserving_pi_perm {J : Type} [Fintype J] (e : J ≃ J) :
    MeasurePreserving (fun (x : J → unitInterval) j => x (e j))
      (Measure.pi fun _ : J => (volume : Measure unitInterval))
      (Measure.pi fun _ : J => (volume : Measure unitInterval)) := by
  have hm : Measurable fun (x : J → unitInterval) j => x (e j) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  refine ⟨hm, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun (x : J → unitInterval) j => x (e j)) ⁻¹' Set.univ.pi s = Set.univ.pi fun j => s (e.symm j) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    exact ⟨fun h j => by simpa using h (e.symm j), fun h j => by simpa using h (e j)⟩
  rw [this, Measure.pi_pi]
  exact Fintype.prod_equiv e.symm _ _ fun _ => rfl
abbrev _root_.YangMills.SharedProofs.p46286 := @measurePreserving_pi_perm
private theorem measurePreserving_noiseTranslate : ∀ (u n : ℕ) [NeZero n] (h : Fin 4 → ℤ),
    MeasurePreserving (noiseTranslate ℓ u n h) (chainNoiseLaw ℓ u n) (chainNoiseLaw ℓ u n)
  | 0, n, _, h => MeasurePreserving.id (chainNoiseLaw ℓ 0 n)
  | u + 1, n, _, h => by
    letI := instMeasurableSpaceChainNoise ℓ u (n * ℓ.side)
    haveI := chainNoiseLaw_isProbability (ℓ := ℓ) u (n * ℓ.side)
    have h0 := measurePreserving_noiseTranslate u (n * ℓ.side) (fun i => (ℓ.side : ℤ) * h i)
    have h1 := measurePreserving_pi_perm (J := TorusSite n) (Equiv.addRight (siteOfInt h))
    have h2 := measurePreserving_pi_perm (J := TorusBond n)
      ((Equiv.addRight (siteOfInt h)).prodCongr (Equiv.refl _))
    have h3 := measurePreserving_pi_perm (J := TorusBond (n * ℓ.side))
      ((Equiv.addRight (siteOfInt fun i => (ℓ.side : ℤ) * h i)).prodCongr (Equiv.refl _))
    exact h0.prod (h1.prod (h2.prod h3))
private theorem measurePreserving_wilsonLaw_of_haar {N : ℕ} [NeZero N] (β : ℝ) (T : TorusField N ≃ᵐ TorusField N)
    (hT : MeasurePreserving T (fieldHaar N) (fieldHaar N))
    (hw : ∀ W, wilsonAction Finset.univ (T W) = wilsonAction Finset.univ W) :
    MeasurePreserving T (wilsonLaw β N) (wilsonLaw β N) := by
  refine ⟨T.measurable, Measure.ext fun s hs => ?_⟩
  rw [T.map_apply]
  unfold wilsonLaw
  rw [withDensity_apply _ hs, withDensity_apply _ (T.measurable hs)]
  have key := hT.setLIntegral_comp_preimage_emb T.measurableEmbedding
    (fun W => ENNReal.ofReal (Real.exp (-β * wilsonAction Finset.univ W) /
      ∫ W', Real.exp (-β * wilsonAction Finset.univ W') ∂(fieldHaar N))) s
  rw [← key]
  simp only [hw]
private def translateEquiv {N : ℕ} (z : TorusSite N) : TorusField N ≃ᵐ TorusField N :=
  MeasurableEquiv.piCongrLeft (fun _ : TorusSite N => Fin 4 → BlockAverages.UnitQuaternion) (Equiv.addRight (-z))
private theorem translateEquiv_apply {N : ℕ} (z : TorusSite N) (W : TorusField N) :
    translateEquiv z W = TorusFields.translate z W := by apply _root_.YangMills.DeltaSharedProofs.p502299 <;> assumption
private theorem measurePreserving_translateEquiv {N : ℕ} [NeZero N] (z : TorusSite N) :
    MeasurePreserving (translateEquiv z) (fieldHaar N) (fieldHaar N) := by apply _root_.YangMills.DeltaSharedProofs.p500734 <;> assumption
private theorem wilsonAction_translate {N : ℕ} [NeZero N] (z : TorusSite N) (W : TorusField N) :
    wilsonAction (Finset.univ : Finset (TorusSite N)) (TorusFields.translate z W) = wilsonAction Finset.univ W := by apply _root_.YangMills.SharedProofs.p7329 <;> assumption
private theorem measurePreserving_translate_wilsonLaw {N : ℕ} [NeZero N] (β : ℝ) (z : TorusSite N) :
    MeasurePreserving (TorusFields.translate z : TorusField N → TorusField N) (wilsonLaw β N) (wilsonLaw β N) := by
  have h := measurePreserving_wilsonLaw_of_haar β (translateEquiv z) (measurePreserving_translateEquiv z)
    fun W => by rw [translateEquiv_apply, wilsonAction_translate]
  have e : (⇑(translateEquiv z) : TorusField N → TorusField N) = TorusFields.translate z :=
    funext (translateEquiv_apply z)
  rwa [e] at h
private theorem measurePreserving_pairTranslate (u n : ℕ) [NeZero n] (β : ℝ)
    [IsProbabilityMeasure (wilsonLaw β (fineSide ℓ.side u n))] (h : Fin 4 → ℤ) :
    MeasurePreserving (pairTranslate ℓ u n h) ((wilsonLaw β (fineSide ℓ.side u n)).prod (chainNoiseLaw ℓ u n))
      ((wilsonLaw β (fineSide ℓ.side u n)).prod (chainNoiseLaw ℓ u n)) := by
  haveI := chainNoiseLaw_isProbability (ℓ := ℓ) u n
  exact (measurePreserving_translate_wilsonLaw β _).prod (measurePreserving_noiseTranslate u n h)
private theorem noiseTranslate_add : ∀ (u n : ℕ) [NeZero n] (h h' : Fin 4 → ℤ) (U : ChainNoise.ChainNoise ℓ u n),
    noiseTranslate ℓ u n h (noiseTranslate ℓ u n h' U) = noiseTranslate ℓ u n (h + h') U
  | 0, _, _, _, _, _ => rfl
  | u + 1, n, _, h, h', U => by
    have e : scaleVec ℓ.side (h + h') = scaleVec ℓ.side h + scaleVec ℓ.side h' := by
      funext i
      simp only [scaleVec, Pi.add_apply]
      ring
    have e1 : ∀ y : TorusSite n, y + siteOfInt h + siteOfInt h' = y + siteOfInt (h + h') := fun y => by
      rw [siteOfInt_add]
      abel
    have e2 : ∀ y : TorusSite (n * ℓ.side), y + siteOfInt (scaleVec ℓ.side h) + siteOfInt (scaleVec ℓ.side h') =
        y + siteOfInt (scaleVec ℓ.side (h + h')) := fun y => by
      rw [e, siteOfInt_add]
      abel
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · show noiseTranslate ℓ u (n * ℓ.side) (scaleVec ℓ.side h)
          (noiseTranslate ℓ u (n * ℓ.side) (scaleVec ℓ.side h') U.1) =
        noiseTranslate ℓ u (n * ℓ.side) (scaleVec ℓ.side (h + h')) U.1
      rw [noiseTranslate_add, e]
    · funext y
      show U.2.1 (y + siteOfInt h + siteOfInt h') = U.2.1 (y + siteOfInt (h + h'))
      rw [e1]
    · funext c
      show U.2.2.1 (c.1 + siteOfInt h + siteOfInt h', c.2) = U.2.2.1 (c.1 + siteOfInt (h + h'), c.2)
      rw [e1]
    · funext b
      show U.2.2.2 (b.1 + siteOfInt (scaleVec ℓ.side h) + siteOfInt (scaleVec ℓ.side h'), b.2) =
        U.2.2.2 (b.1 + siteOfInt (scaleVec ℓ.side (h + h')), b.2)
      rw [e2]
private theorem noiseTranslate_zero : ∀ (u n : ℕ) [NeZero n] (U : ChainNoise.ChainNoise ℓ u n),
    noiseTranslate ℓ u n 0 U = U
  | 0, _, _, _ => rfl
  | u + 1, n, _, U => by
    have e : scaleVec ℓ.side (0 : Fin 4 → ℤ) = 0 := by
      funext i
      simp [scaleVec]
    have e1 : ∀ {m : ℕ} (y : TorusSite m), y + siteOfInt (0 : Fin 4 → ℤ) = y := fun y => by
      funext i
      simp [siteOfInt]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · show noiseTranslate ℓ u (n * ℓ.side) (scaleVec ℓ.side 0) U.1 = U.1
      rw [e, noiseTranslate_zero]
    · funext y
      show U.2.1 (y + siteOfInt 0) = U.2.1 y
      rw [e1]
    · funext c
      show U.2.2.1 (c.1 + siteOfInt 0, c.2) = U.2.2.1 c
      rw [e1]
    · funext b
      show U.2.2.2 (b.1 + siteOfInt (scaleVec ℓ.side 0), b.2) = U.2.2.2 b
      rw [e, e1]
private theorem pairTranslate_iterate (u n : ℕ) [NeZero n] (h : Fin 4 → ℤ) (k : ℕ)
    (p : TorusField (fineSide ℓ.side u n) × ChainNoise.ChainNoise ℓ u n) :
    (pairTranslate ℓ u n h)^[k] p = pairTranslate ℓ u n (fun i => (k : ℤ) * h i) p := by
  induction k with
  | zero =>
    have e : (fun i => ((0 : ℕ) : ℤ) * h i) = 0 := by
      funext i
      simp
    rw [e]
    refine (Prod.ext ?_ ?_)
    · funext x i
      show p.1 x i = p.1 (x + siteOfInt fun i => (ℓ.side : ℤ) ^ u * (0 : Fin 4 → ℤ) i) i
      have e2 : (siteOfInt fun i => (ℓ.side : ℤ) ^ u * (0 : Fin 4 → ℤ) i : TorusSite (fineSide ℓ.side u n)) = 0 := by
        funext i
        simp [siteOfInt]
      rw [e2, add_zero]
    · exact (noiseTranslate_zero u n p.2).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have e : (fun i => ((k + 1 : ℕ) : ℤ) * h i) = h + fun i => (k : ℤ) * h i := by
      funext i
      simp only [Pi.add_apply]
      push_cast
      ring
    rw [e]
    refine (Prod.ext ?_ ?_)
    · funext x i
      show p.1 (x + siteOfInt (fun i => (ℓ.side : ℤ) ^ u * h i) +
          siteOfInt fun i => (ℓ.side : ℤ) ^ u * ((k : ℤ) * h i)) i =
        p.1 (x + siteOfInt fun i => (ℓ.side : ℤ) ^ u * (h + fun i => (k : ℤ) * h i) i) i
      have e2 : (fun i => (ℓ.side : ℤ) ^ u * (h + fun i => (k : ℤ) * h i) i) =
          (fun i => (ℓ.side : ℤ) ^ u * h i) + fun i => (ℓ.side : ℤ) ^ u * ((k : ℤ) * h i) := by
        funext i
        simp only [Pi.add_apply]
        ring
      rw [e2, siteOfInt_add, add_assoc]
    · exact noiseTranslate_add u n _ _ p.2
end Invariance
section LimitPoint
variable {Λ : MomentParameters}
open Classical in
private theorem separatedBelow_lastSeparated (S : MomentPoint Λ) :
    S.data.SeparatedBelow Λ.stepParams S.β S.lastSeparated := by
  unfold MomentPoint.lastSeparated
  exact Nat.findGreatest_spec (m := 0) (Nat.zero_le _) fun u hu => absurd hu (Nat.not_lt_zero u)
private theorem period_facts (hf : Λ.stepParams.Admissible) (S : MomentPoint Λ) :
    Λ.stepParams.side ∣ S.data.period Λ.stepParams.side ∧ 64 ≤ S.data.period Λ.stepParams.side := by
  have hLge : 2 ^ 16 ≤ Λ.stepParams.side := hf.L_ge
  have hn₀ : 4096 ≤ Λ.stepParams.n₀ := hf.n₀_ge
  have hvol : Λ.stepParams.side * Λ.stepParams.n₀ ≤ 2 * Λ.stepParams.side ^ S.data.sideExponent := S.side_le
  have hbig : 64 ≤ Λ.stepParams.side * Λ.stepParams.n₀ := by nlinarith
  have hm : S.data.sideExponent ≠ 0 := by
    intro h0
    rw [h0] at hvol
    simp only [pow_zero, mul_one] at hvol
    omega
  exact ⟨Dvd.dvd.mul_left (dvd_pow_self _ hm) 2, hbig.trans hvol⟩
private def productOf (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)) : Bool → SampleObservable Λ
  | true => completedProduct c B
  | false => bottomProduct c B
private theorem integral_productOf_translate (hS : ScoresPreserveCorrelations)
    (hT : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement) (hSc : BondScoreProperties)
    (hBs : HullTrees.translationCarriesBasesStatement) (hB : ResponseInTheExpansion.sampleBelowLawStatement)
    (hR : ruleDrawsChainStatement) (hD : SupportSiteDistanceBounds) (hSup : supTestFamilyIsTestFamilyStatement)
    (hf : Λ.stepParams.Admissible) (hd : 0 < Λ.d) (S : MomentPoint Λ)
    (rule : NoiseRule Λ.stepParams) (hr : rule.IsAdmissible S.tower) (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k))
    (p k : ℕ) (hκ : 4 * |Λ.R| + 3 ≤ ((k * p : ℕ) : ℝ))
    (htop : 2 * (k * p * Λ.stepParams.side) ≤ S.data.period Λ.stepParams.side) (ε ε' : Bool) :
    ∫ ω, productOf c B ε S (S.sampleOf rule ω) *
        productOf c B ε' S (S.sampleOf rule
          ((pairTranslate Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)
            (translationVector Λ.stepParams.side p))^[k] ω)) ∂S.sampleLaw =
      ∫ ω, productOf c B false S (S.sampleOf rule ω) *
        productOf c B false S (S.sampleOf rule
          ((pairTranslate Λ.stepParams S.data.windowLevel (S.data.period Λ.stepParams.side)
            (translationVector Λ.stepParams.side p))^[k] ω)) ∂S.sampleLaw := by
  have hfar := separatedBelow_lastSeparated S
  have hP : S.data.Admissible Λ.stepParams.side (2 * Λ.R) Λ.d :=
    ⟨hSup _ _ _ _ S.supAdmissible.isSupTestFamily, S.supAdmissible.scaleLevel_le, S.supAdmissible.support_small,
      S.supAdmissible.exists_ne_zero⟩
  have ha : (fun i => (k : ℤ) * translationVector Λ.stepParams.side p i) =
      (Pi.single 0 ((k * p * Λ.stepParams.side : ℕ) : ℤ) : Fin 4 → ℤ) := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [translationVector]
      ring
    · simp [translationVector, Pi.single_apply, hi]
  have hcr : ∀ u < S.lastSeparated, ∀ i j : Fin Λ.k, ∀ y ∈ S.data.supportSites Λ.stepParams.side (u + 1) i,
      ∀ y' ∈ S.data.supportSites Λ.stepParams.side (u + 1) j,
      1 < TorusFields.supDist y (y' + siteOfInt fun b => (Λ.stepParams.side : ℤ) ^ (S.data.windowLevel - (u + 1)) *
        (fun i => (k : ℤ) * translationVector Λ.stepParams.side p i) b) := by
    intro u hu i j y hy y' hy'
    rw [ha]
    exact supDist_translate_supportSites hD hf.L_odd S.data Λ.R Λ.d hd hP (k * p) hκ htop u
      (by have := S.lastSeparated_le; omega) i j y hy y' hy'
  have core := integral_centredProduct_translate hS hT hSc hBs hB hR hf S.tower S.isCutoff S.marksMeasurable rule hr
    S.β S.coeff S.data c B S.data.windowLevel S.lastSeparated (S.data.windowLevel - S.lastSeparated)
    (Nat.add_sub_of_le S.lastSeparated_le) rfl (S.data.period Λ.stepParams.side) rfl (period_facts hf S).1
    (period_facts hf S).2 (fun u hu => (hfar u hu).2) (fun i => (k : ℤ) * translationVector Λ.stepParams.side p i)
    hcr ε ε'
  simp only [pairTranslate_iterate]
  cases ε <;> cases ε' <;> exact core
private theorem condMeanAt_ae_eq (hM : jointLimitPropertiesStatement) (hS : ScoresPreserveCorrelations)
    (hT : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement) (hSc : BondScoreProperties)
    (hBs : HullTrees.translationCarriesBasesStatement) (hB : ResponseInTheExpansion.sampleBelowLawStatement)
    (hR : ruleDrawsChainStatement) (hD : SupportSiteDistanceBounds)
    (hSup : supTestFamilyIsTestFamilyStatement) (hf : Λ.stepParams.Admissible) (hd : 0 < Λ.d) (S : MomentPoint Λ)
    (F : LimitLawAtPoint S) (c : Fin Λ.k → ℝ) (B : Finset (Fin Λ.k)) (j j' : F.Index)
    (hj : F.observables j = bottomProduct c B) (hj' : F.observables j' = completedProduct c B) :
    F.condMeanAt j =ᵐ[F.law] F.condMeanAt j' := by
  haveI := F.countable_index
  haveI := F.isJointLimitLaw.isProbability
  have hTi : ∀ i, (F.points i).tower = S.tower := fun i => by
    obtain ⟨hp, hs, e⟩ := F.points_eq i
    rw [e]
    rfl
  have hri : ∀ i, F.rule.IsAdmissible (F.points i).tower := fun i => by
    rw [hTi]
    exact F.rule_admissible
  have hw : ∀ S' : MomentPoint Λ,
      IsProbabilityMeasure (wilsonLaw S'.β (fineSide Λ.stepParams.side S'.data.windowLevel
        (S'.data.period Λ.stepParams.side))) :=
    fun S' => (hT Λ.stepParams hf hf.depth_lt S'.tower S'.isCutoff S'.marksMeasurable S'.β S'.coeff 0
      (fineSide Λ.stepParams.side S'.data.windowLevel (S'.data.period Λ.stepParams.side))).1
  have hKeep : (translatedTori F.points F.period).IsPreserving := by
    refine ⟨fun i => ?_, fun i => ?_⟩
    · haveI := hw (F.points i)
      haveI := chainNoiseLaw_isProbability (ℓ := Λ.stepParams) (F.points i).data.windowLevel
        ((F.points i).data.period Λ.stepParams.side)
      show IsProbabilityMeasure ((wilsonLaw (F.points i).β _).prod
        (chainNoiseLaw Λ.stepParams (F.points i).data.windowLevel _))
      infer_instance
    · haveI := hw (F.points i)
      exact measurePreserving_pairTranslate _ _ _ _
  obtain ⟨hsh, hpr, -, hav, -, -⟩ := hM (translatedTori F.points F.period) F.Index
    (fun j => sampleFamily F.rule F.points F.period (F.observables j)) F.law hKeep F.hasBoundedMoments
    F.isJointLimitLaw
  have hint : ∀ (a b : F.Index) (k l : ℕ),
      Integrable (fun v : TranslateValues F.Index => v (a, k) * v (b, l)) F.law := by
    intro a b k l
    have := (hpr 2 ![(a, k), (b, l)]).1
    simpa [Fin.prod_univ_two] using this
  have hlim : ∀ (a b : F.Index) (k : ℕ), Tendsto (fun i => ∫ ω, F.observables a (F.points i)
      ((F.points i).sampleOf F.rule ω) *
      F.observables b (F.points i) ((F.points i).sampleOf F.rule
        ((pairTranslate Λ.stepParams (F.points i).data.windowLevel ((F.points i).data.period Λ.stepParams.side)
          (translationVector Λ.stepParams.side F.period))^[k] ω)) ∂(F.points i).sampleLaw)
      atTop (𝓝 (∫ v : TranslateValues F.Index, v (a, 0) * v (b, k) ∂F.law)) := by
    intro a b k
    have h2 := (hpr 2 ![(a, 0), (b, k)]).2
    simp [Fin.prod_univ_two, TranslatedLaws.translate] at h2
    exact h2
  have hm : ∀ i, (F.points i).data.sideExponent = F.exponents i := fun i => by
    obtain ⟨hp, hs, e⟩ := F.points_eq i
    rw [e]
    rfl
  have hL1 : 1 < Λ.stepParams.side := by
    have : 2 ^ 16 ≤ Λ.stepParams.side := hf.L_ge
    omega
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge (4 * |Λ.R| + 3)
  have hfar : ∀ k, k₀ ≤ k →
      ∫ v : TranslateValues F.Index, (v (j', 0) - v (j, 0)) * (v (j', k) - v (j, k)) ∂F.law = 0 := by
    intro k hk
    have hev : ∀ᶠ i in atTop, 2 * (k * F.period * Λ.stepParams.side) ≤ (F.points i).data.period Λ.stepParams.side := by
      filter_upwards [eventually_ge_atTop (k * F.period * Λ.stepParams.side)] with i hi
      show _ ≤ 2 * Λ.stepParams.side ^ (F.points i).data.sideExponent
      rw [hm]
      have h1 : i ≤ F.exponents i := F.strictMono_exponents.le_apply
      have h2 : F.exponents i < Λ.stepParams.side ^ F.exponents i := Nat.lt_pow_self hL1
      exact Nat.mul_le_mul_left 2 (hi.trans (h1.trans h2.le))
    have hκ : 4 * |Λ.R| + 3 ≤ ((k * F.period : ℕ) : ℝ) := by
      have h1 : k₀ ≤ k * F.period := hk.trans (Nat.le_mul_of_pos_right _ F.one_le_period)
      exact hk₀.trans (by exact_mod_cast h1)
    have heq : ∀ (ε ε' : Bool) (a b : F.Index), F.observables a = productOf c B ε →
        F.observables b = productOf c B ε' →
        ∫ v : TranslateValues F.Index, v (a, 0) * v (b, k) ∂F.law =
          ∫ v : TranslateValues F.Index, v (j, 0) * v (j, k) ∂F.law := by
      intro ε ε' a b ha hb
      refine tendsto_nhds_unique_of_eventuallyEq (hlim a b k) (hlim j j k) ?_
      filter_upwards [hev] with i hi
      have hc := integral_productOf_translate hS hT hSc hBs hB hR hD hSup hf hd (F.points i) F.rule (hri i) c B
        F.period k hκ hi ε ε'
      rw [ha, hb, hj]
      exact hc
    have e₁ := heq true true j' j' hj' hj'
    have e₂ := heq true false j' j hj' hj
    have e₃ := heq false true j j' hj hj'
    have hexp : ∀ v : TranslateValues F.Index, (v (j', 0) - v (j, 0)) * (v (j', k) - v (j, k)) =
        v (j', 0) * v (j', k) - v (j', 0) * v (j, k) - (v (j, 0) * v (j', k) - v (j, 0) * v (j, k)) :=
      fun v => by ring
    simp only [hexp]
    have i₁ : Integrable (fun v : TranslateValues F.Index => v (j', 0) * v (j', k) - v (j', 0) * v (j, k)) F.law :=
      (hint _ _ _ _).sub (hint _ _ _ _)
    have i₂ : Integrable (fun v : TranslateValues F.Index => v (j, 0) * v (j', k) - v (j, 0) * v (j, k)) F.law :=
      (hint _ _ _ _).sub (hint _ _ _ _)
    rw [integral_sub i₁ i₂, integral_sub (hint _ _ _ _) (hint _ _ _ _), integral_sub (hint _ _ _ _) (hint _ _ _ _),
      e₁, e₂, e₃]
    ring
  exact (invariantCondExp_eq_of_far_uncorrelated hsh hint hav k₀ hfar).symm
end LimitPoint
end LimitScoreMeans
theorem limitScoresMeanStatement_proof (hM : MomentMethod.jointLimitPropertiesStatement)
    (hS : WeightedResponses.ScoresPreserveCorrelations)
    (hT : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement) (hSc : WeightedResponses.BondScoreProperties)
    (hBs : HullTrees.translationCarriesBasesStatement) (hB : ResponseInTheExpansion.sampleBelowLawStatement)
    (hR : ChainNoise.ruleDrawsChainStatement) (hD : LevelTestFunctions.SupportSiteDistanceBounds)
    (hSup : supTestFamilyIsTestFamilyStatement) : limitScoresMeanStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hdrawn _ _ _ _
  refine ⟨0, ?_⟩
  intro Kr _ _ _ _ _
  refine ⟨Tb.floorMin, ?_⟩
  intro y hy _ _ g _ _ k _ _ _ R d hd S F c B j j' hj hj'
  exact LimitScoreMeans.condMeanAt_ae_eq hM hS hT hSc hBs hB hR hD hSup (hdrawn.fits y hy) hd S F c B j j' hj hj'
end YangMills.Construction.MomentLaw
end
