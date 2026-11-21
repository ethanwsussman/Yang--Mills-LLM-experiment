import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import YangMills.Construction.HullsInEveryVolume.LocalHullLiesInTheHull
import YangMills.Construction.LawByMomentsOfTheFlow.TheChainMovesWithATranslationProof
import YangMills.Construction.LawByMomentsOfTheFlow.TranslationsMoveTheHull
import YangMills.Construction.ResponseInTheExpansion.TheLocalEventIsLikelyProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings StepCosts BlockAverages LumpContours
namespace TranslationLemmas
section Sets
variable {m : ℕ} [NeZero m]
private theorem mem_translateSet_iff {a z : TorusSite m} {Y : Finset (TorusSite m)} :
    z ∈ translateSet a Y ↔ z + a ∈ Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.mem_translateSet <;> assumption
private theorem mem_thickening_iff {k : ℕ} {X : Finset (TorusSite m)} {z : TorusSite m} :
    z ∈ thickening k X ↔ ∃ x ∈ X, _root_.YangMills.Construction.TorusFields.supDist z x ≤ k := by apply _root_.YangMills.Construction.TorusFields.mem_thickening <;> assumption
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
end Sets
section Scale
variable {n L : ℕ}
private abbrev scaleBy (L : ℕ) (v : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (L : ℤ) * v i
private theorem exists_cast_add_intCast {m : ℕ} [NeZero m] (x : ZMod m) (z : ℤ) :
    ∃ k : ℤ, (((x + (z : ZMod m) : ZMod m)).cast : ℤ) = (x.cast : ℤ) + z + (m : ℤ) * k := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.exists_cast_add_intCast <;> assumption
private theorem parentBlock_add_scaleBy [NeZero n] [NeZero L] (x : TorusSite (n * L)) (v : Fin 4 → ℤ) :
    parentBlock L (x + siteOfInt (scaleBy L v)) = parentBlock L x + siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.parentBlock_add_scale <;> assumption
private theorem siteOfInt_neg {m : ℕ} (v : Fin 4 → ℤ) : (siteOfInt (-v) : TorusSite m) = - siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.siteOfInt_neg <;> assumption
end Scale
section Clusters
variable {n L : ℕ} [NeZero n] [NeZero L]
private theorem mem_sitesInBlocks_iff {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.mem_sitesInBlocks <;> assumption
private theorem sitesInBlocks_translateSet (v : Fin 4 → ℤ) (S : Finset (TorusSite n)) :
    sitesInBlocks L (translateSet (siteOfInt v) S) =
      translateSet (siteOfInt (scaleBy L v)) (sitesInBlocks L S) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.sitesInBlocks_translateSet <;> assumption
private theorem translateSet_inter_nonempty_iff {m : ℕ} [NeZero m] (a : TorusSite m) (X Y : Finset (TorusSite m)) :
    (open Classical in (translateSet a X ∩ translateSet a Y).Nonempty) ↔ (open Classical in (X ∩ Y).Nonempty) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translateSet_inter_nonempty <;> assumption
variable (r r' : ℕ) (v : Fin 4 → ℤ) (bad : Finset (TorusBond (n * L))) (Yt : Finset (TorusSite (n * L)))
  (C : Finset (TorusSite n))
private theorem clusterComponents_translate :
    clusterComponents L r (translateBonds (siteOfInt (scaleBy L v)) bad) (translateSet (siteOfInt (scaleBy L v)) Yt)
        (translateSet (siteOfInt v) C) =
      (clusterComponents L r bad Yt C).image (translateSet (siteOfInt (scaleBy L v))) := by
  classical
  unfold clusterComponents
  rw [← chainComponents_translateSet]
  congr 1
  rw [image_fst_translateBonds, sitesInBlocks_translateSet]
  ext z
  simp [mem_translateSet_iff]
private theorem attachedSites_translate :
    attachedSites L r (translateBonds (siteOfInt (scaleBy L v)) bad) (translateSet (siteOfInt (scaleBy L v)) Yt)
        (translateSet (siteOfInt v) C) =
      translateSet (siteOfInt (scaleBy L v)) (attachedSites L r bad Yt C) := by
  classical
  ext z
  rw [mem_translateSet_iff]
  simp only [attachedSites, Finset.mem_biUnion, Finset.mem_filter, id, clusterComponents_translate, Finset.mem_image]
  constructor
  · rintro ⟨X', ⟨⟨X, hX, rfl⟩, hn⟩, hz⟩
    rw [sitesInBlocks_translateSet] at hn
    exact ⟨X, ⟨hX, (translateSet_inter_nonempty_iff _ _ _).mp (by convert hn)⟩, mem_translateSet_iff.mp hz⟩
  · rintro ⟨X, ⟨hX, hn⟩, hz⟩
    refine ⟨_, ⟨⟨X, hX, rfl⟩, ?_⟩, mem_translateSet_iff.mpr hz⟩
    rw [sitesInBlocks_translateSet]
    convert (translateSet_inter_nonempty_iff (siteOfInt (scaleBy L v)) X (sitesInBlocks L C)).mpr (by convert hn)
private theorem coreBlocks_translateSet (θ : Finset (TorusSite (n * L))) :
    coreBlocks L r (translateSet (siteOfInt (scaleBy L v)) θ) = translateSet (siteOfInt v) (coreBlocks L r θ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.coreBlocks_translateSet <;> assumption
end Clusters
section Hot
variable {ℓ : StepParameters} {m : ℕ} [NeZero m]
private theorem curvature_translate_apply (a : TorusSite m) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    curvature (TorusFields.translate a W) x μ ν = curvature W (x + a) μ ν := by
  simp only [curvature, holonomy, TorusFields.translate, add_right_comm x a]
private theorem torusHotLumps_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ)
    (W : TorusField m) :
    torusHotLumps ℓ (TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) W) =
      (torusHotLumps ℓ W).image (translateSet (siteOfInt (scaleBy ℓ.side w))) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusHotLumps_translate <;> assumption
private theorem torusHotSites_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ)
    (W : TorusField m) :
    torusHotSites ℓ (TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) W) =
      translateSet (siteOfInt (scaleBy ℓ.side w)) (torusHotSites ℓ W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusHotSites_translate <;> assumption
end Hot
section Chart
variable {F : BlockFrame} (u : Fin 4 → ℤ)
private def topShift : F.Site F.depth := siteOfCoords F.depth fun i => (F.blockSide : ℤ) * u i
private def translateFine (X : F.GaugeField F.depth) : F.GaugeField F.depth := fun x i => X (x + topShift u) i
private def translateCoarse (U : F.GaugeField F.top) : F.GaugeField F.top := fun y i => U (y + siteOfCoords F.top u) i
private theorem pathHolonomy_translateFine (X : F.GaugeField F.depth) (x : F.Site F.depth) (l : List PathStep) :
    pathHolonomy (translateFine u X) x l = pathHolonomy X (x + topShift u) l := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.pathHolonomy_translateFine <;> assumption
private theorem cellCentre_add_siteOfCoords (z : F.Cell) :
    cellCentre F.depth (z + siteOfCoords F.top u) = cellCentre F.depth z + topShift u := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.cellCentre_add_siteOfCoords <;> assumption
private theorem axialGauge_translateFine (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (π : Equiv.Perm (Fin 4)) (X : F.GaugeField F.depth) (x : F.Site F.depth) :
    axialGauge π (translateFine u X) x = axialGauge π X (x + topShift u) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.axialGauge_translateFine <;> assumption
private theorem bondCoordinate_translate (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (π : Equiv.Perm (Fin 4)) (U : F.GaugeField F.top) (X : F.GaugeField F.depth)
    (x : F.Site F.depth) (i : Fin 4) :
    bondCoordinate π (translateCoarse u U) (translateFine u X) (x, i) = bondCoordinate π U X (x + topShift u, i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.bondCoordinate_translate <;> assumption
end Chart
section Step
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
private theorem toTorusSite_add_siteOfCoords (v : Fin 4 → ℤ) (y : (stepBlockFrame ℓ.side n).Cell) :
    toTorusSite n (y + siteOfCoords (stepBlockFrame ℓ.side n).top v) = toTorusSite n y + siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.toTorusSite_add_coarse <;> assumption
private theorem readAtLevel_zero_translate (v : Fin 4 → ℤ) (W : TorusField (n * ℓ.side)) :
    readAtLevel (stepBlockFrame ℓ.side n) 0 (TorusFields.translate (siteOfInt (scaleBy ℓ.side v)) W) =
      translateFine (F := stepBlockFrame ℓ.side n) v (readAtLevel (stepBlockFrame ℓ.side n) 0 W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.readAtLevel_translate_fine <;> assumption
private theorem readAtLevel_one_translate (v : Fin 4 → ℤ) (V : TorusField n) :
    readAtLevel (stepBlockFrame ℓ.side n) 1 (TorusFields.translate (siteOfInt v) V) =
      translateCoarse (F := stepBlockFrame ℓ.side n) v (readAtLevel (stepBlockFrame ℓ.side n) 1 V) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.readAtLevel_translate_coarse <;> assumption
private theorem stepBlockFrame_extent_ge (hn : 2 ≤ n) : ∀ i, 2 ≤ (stepBlockFrame ℓ.side n).extent i :=
  fun _ => hn
private theorem chartCoord_translate (hL : Odd ℓ.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (x : TorusSite (n * ℓ.side)) (i : Fin 4) :
    chartCoord ℓ (TorusFields.translate (siteOfInt v) V) (TorusFields.translate (siteOfInt (scaleBy ℓ.side v)) W) (x, i) =
      chartCoord ℓ V W (x + siteOfInt (scaleBy ℓ.side v), i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.chartCoord_translate <;> assumption
private theorem mem_chartBonds_add_iff (hL : Odd ℓ.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (x : TorusSite (n * ℓ.side))
    (i : Fin 4) :
    (x + siteOfInt (scaleBy ℓ.side v), i) ∈ chartBonds ℓ.side n ↔ (x, i) ∈ chartBonds ℓ.side n := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.add_mem_chartBonds_iff <;> assumption
end Step
section Weights
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem markedBonds_translateSet (hL : Odd R.params.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ)
    (C : Finset (TorusSite n)) :
    markedBonds R (translateSet (siteOfInt v) C) =
      translateBonds (siteOfInt (scaleBy R.params.side v)) (markedBonds R C) := by
  classical
  ext ⟨x, i⟩
  rw [mem_translateBonds_iff]
  simp only [markedBonds, Finset.mem_filter, mem_translateSet_iff]
  rw [mem_chartBonds_add_iff hL hn, parentBlock_add_scaleBy]
private theorem bondMark_translate (hL : Odd R.params.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (h : frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt v) V) (x, i) =
      frameCoord R.params R.anchorRadius R.depth R.frameReach V (x + siteOfInt (scaleBy R.params.side v), i)) :
    bondMark R (TorusFields.translate (siteOfInt v) V) (TorusFields.translate (siteOfInt (scaleBy R.params.side v)) W) (x, i) =
      bondMark R V W (x + siteOfInt (scaleBy R.params.side v), i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.bondMark_translate <;> assumption
end Weights
end TranslationLemmas
namespace MomentLaw
open HullTrees ChainNoise WeightedResponses StepReturn StepMarks ColdChain
open TranslationLemmas
namespace HullTranslation
section Marks
variable {ℓ : StepParameters}
open Classical in
private theorem mem_stepOutcome_bonds_iff (rule : NoiseRule ℓ) (T : StageTower ℓ) (s n : ℕ) [NeZero n]
    (W : TorusField (n * ℓ.side)) (ξ : StepNoise ℓ n) (b : TorusBond (n * ℓ.side)) :
    b ∈ (show Finset (TorusBond (n * ℓ.side)) from (rule.stepOutcome T s n W ξ).2.2) ↔
      b ∈ markedBonds (T.stage s).toStepSetup
          (hotCoreSites (T.stage s).toStepSetup (rule.stepOutcome T s n W ξ).2.1) ∧
        ¬ ((ξ.2.2 b : ℝ) < bondMark (T.stage s).toStepSetup (rule.stepOutcome T s n W ξ).2.1 W b) := by
  unfold NoiseRule.stepOutcome
  exact Finset.mem_filter
private theorem le_clusterRange {x : ℝ} {N : ℕ} (h : (N : ℝ) ^ 100 ≤ x) : N ≤ clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.NearPotentialBound.le_clusterRange_of_pow_le <;> assumption
private theorem clusterRange_le_succ {x x' B : ℝ} (hB : 1 ≤ B) (hx' : B ^ 100 ≤ x') (hx : 0 ≤ x)
    (h : x ≤ x' + 2 * B) : clusterRange x ≤ clusterRange x' + 1 := by
  have hx0 : 0 ≤ x' := le_trans (by positivity) hx'
  set b : ℝ := x' ^ ((1 : ℝ) / 100) with hb
  have hb100 : b ^ 100 = x' := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have hBb : B ≤ b := by
    calc B = (B ^ (100 : ℕ)) ^ ((1 : ℝ) / 100) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          norm_num
      _ ≤ b := Real.rpow_le_rpow (by positivity) hx' (by norm_num)
  have h1 : b ^ 99 ≤ (b + 1) ^ 99 := pow_le_pow_left₀ (by linarith) (by linarith) _
  have h2 : (b + 1) ^ 2 ≤ (b + 1) ^ 99 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h3 : b ^ 99 * b ≤ (b + 1) ^ 99 * b := mul_le_mul_of_nonneg_right h1 (by linarith)
  have h4 : x ≤ (b + 1) ^ 100 := by
    have e2 : b ^ 100 = b ^ 99 * b := by ring
    nlinarith
  have h5 : x ^ ((1 : ℝ) / 100) ≤ b + 1 := by
    calc x ^ ((1 : ℝ) / 100) ≤ ((b + 1) ^ (100 : ℕ)) ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow hx h4 (by norm_num)
      _ = b + 1 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          norm_num
  unfold clusterRange
  calc ⌈x ^ ((1 : ℝ) / 100)⌉₊ ≤ ⌈b + 1⌉₊ := Nat.ceil_mono h5
    _ = ⌈b⌉₊ + 1 := Nat.ceil_add_one (by linarith)
end Marks
section Reads
variable {ℓ : StepParameters}
open Classical in
private def hullStep (T : StageTower ℓ) (s₁ : ℝ) (j n : ℕ) [NeZero n]
    (lo : Finset (TorusSite (n * ℓ.side)) × (TorusSite (n * ℓ.side) → ℝ))
    (bad : Finset (TorusBond (n * ℓ.side))) (C Q : Finset (TorusSite n)) : Finset (TorusSite n) × (TorusSite n → ℝ) :=
  let R := (T.stage j).toStepSetup
  let Z := C ∪ (coreBlocks ℓ.side R.range (attachedSites ℓ.side R.range bad lo.1 C) ∩ Q)
  let Y := thickening (R.nextRange / 2) Z ∩ Q
  (Y, fun y => if y ∈ Z then s₁ + ∑ z ∈ sitesInBlocks ℓ.side {y} ∩ lo.1, lo.2 z else if y ∈ Y then s₁ else 0)
open Classical in
private theorem localHullData_succ (T : StageTower ℓ) (s₁ : ℝ) (j n : ℕ) [NeZero n] (w : MarkedSample ℓ (j + 1) n)
    (Q : Finset (TorusSite n)) :
    localHullData T s₁ (j + 1) n w Q =
      hullStep T s₁ j n (localHullData T s₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q))
        ((show Finset (TorusBond (n * ℓ.side)) from w.2.2.2).filter fun b => b.1 ∈ sitesInBlocks ℓ.side Q)
        (hotCoreSites (T.stage j).toStepSetup w.2.2.1 ∩ Q) Q := by
  simp only [localHullData, hullStep]
end Reads
section Moves
variable {ℓ : StepParameters}
private def IsTranslated (ℓ : StepParameters) :
    (s n : ℕ) → [NeZero n] → (Fin 4 → ℤ) → MarkedSample ℓ s n → MarkedSample ℓ s n → Prop
  | 0, n, _, v, w, w' => (show TorusField n from w') = TorusFields.translate (siteOfInt v) (show TorusField n from w)
  | s + 1, n, _, v, w, w' => IsTranslated ℓ s (n * ℓ.side) (scaleBy ℓ.side v) w.1 w'.1 ∧
      w'.2.2.1 = TorusFields.translate (siteOfInt v) w.2.2.1 ∧
      (show Finset (TorusBond (n * ℓ.side)) from w'.2.2.2) =
        translateBonds (siteOfInt (scaleBy ℓ.side v)) (show Finset (TorusBond (n * ℓ.side)) from w.2.2.2)
private theorem isTranslated_topField_eq {s n : ℕ} [NeZero n] {v : Fin 4 → ℤ} {w w' : MarkedSample ℓ s n}
    (h : IsTranslated ℓ s n v w w') : topField ℓ s n w' = TorusFields.translate (siteOfInt v) (topField ℓ s n w) := by
  cases s with
  | zero => exact h
  | succ s => exact h.2.1
private theorem isBlockTorusSide_mul_side {n : ℕ} (hB : IsBlockTorusSide ℓ n) (h0 : 0 < ℓ.side) :
    IsBlockTorusSide ℓ (n * ℓ.side) := by apply _root_.YangMills.Construction.ResponseInTheExpansion.LocalEventLikely.isBlockTorusSide_mul <;> assumption
private theorem hotCoreSites_translate (hfit : ℓ.Admissible) (R : StepSetup) (hR : R.params = ℓ) {n : ℕ} [NeZero n]
    (hLn : ℓ.side ∣ n) (w : Fin 4 → ℤ) (V : TorusField n) :
    hotCoreSites R (TorusFields.translate (siteOfInt (scaleBy R.params.side w)) V) =
      translateSet (siteOfInt (scaleBy R.params.side w)) (hotCoreSites R V) := by
  subst hR
  unfold hotCoreSites
  rw [torusHotSites_translate hfit hLn, thickening_translateSet]
private theorem stepOutcome_translate (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T)
    (hfit : ℓ.Admissible) (s n : ℕ) [NeZero n] (hLn : ℓ.side ∣ n) (h2 : 2 ≤ n) (w : Fin 4 → ℤ)
    (X : TorusField (n * ℓ.side)) (ξ : StepNoise ℓ n)
    (hfr : ∀ (V : TorusField n) (u : Fin 4 → ℤ),
      ∀ c ∈ markedBonds (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V),
      frameCoord ℓ (T.stage s).toStepSetup.anchorRadius (T.stage s).toStepSetup.depth
          (T.stage s).toStepSetup.frameReach (TorusFields.translate (siteOfInt u) V) (c.1 - siteOfInt (scaleBy ℓ.side u), c.2) =
        frameCoord ℓ (T.stage s).toStepSetup.anchorRadius (T.stage s).toStepSetup.depth
          (T.stage s).toStepSetup.frameReach V c) :
    (rule.stepOutcome T s n (TorusFields.translate (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) X)
        (fun y => ξ.1 (y + siteOfInt (scaleBy ℓ.side w)), fun c => ξ.2.1 (c.1 + siteOfInt (scaleBy ℓ.side w), c.2),
          fun b => ξ.2.2 (b.1 + siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w)), b.2))).2.1 =
      TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) (rule.stepOutcome T s n X ξ).2.1 ∧
    (show Finset (TorusBond (n * ℓ.side)) from
        (rule.stepOutcome T s n (TorusFields.translate (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) X)
          (fun y => ξ.1 (y + siteOfInt (scaleBy ℓ.side w)), fun c => ξ.2.1 (c.1 + siteOfInt (scaleBy ℓ.side w), c.2),
            fun b => ξ.2.2 (b.1 + siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w)), b.2))).2.2) =
      translateBonds (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w)))
        (show Finset (TorusBond (n * ℓ.side)) from (rule.stepOutcome T s n X ξ).2.2) := by
  classical
  set v : Fin 4 → ℤ := scaleBy ℓ.side w with hv
  set ξ' : StepNoise ℓ n := (fun y => ξ.1 (y + siteOfInt v), fun c => ξ.2.1 (c.1 + siteOfInt v, c.2),
    fun b => ξ.2.2 (b.1 + siteOfInt (scaleBy ℓ.side v), b.2)) with hξ'
  set X' : TorusField (n * ℓ.side) := TorusFields.translate (siteOfInt (scaleBy ℓ.side v)) X with hX'
  have hV : (rule.stepOutcome T s n X' ξ').2.1 = TorusFields.translate (siteOfInt v) (rule.stepOutcome T s n X ξ).2.1 := by
    funext y i
    have ho : (fun y => rule.base s n X' y (ξ'.1 y)) =
        fun y => (fun y => rule.base s n X y (ξ.1 y)) (y + siteOfInt v) := by
      funext y
      exact hr.base_translate s n X v y _
    show rule.value s n X' (fun y => rule.base s n X' y (ξ'.1 y)) (y, i) (ξ.2.1 (y + siteOfInt v, i)) =
      rule.value s n X (fun y => rule.base s n X y (ξ.1 y)) (y + siteOfInt v, i) (ξ.2.1 (y + siteOfInt v, i))
    rw [ho]
    exact hr.value_translate s n X (fun y => rule.base s n X y (ξ.1 y)) v (y, i) _
  refine ⟨hV, ?_⟩
  ext ⟨x, i⟩
  rw [mem_translateBonds_iff, mem_stepOutcome_bonds_iff, mem_stepOutcome_bonds_iff, hV]
  have hm : markedBonds (T.stage s).toStepSetup
        (hotCoreSites (T.stage s).toStepSetup (TorusFields.translate (siteOfInt v) (rule.stepOutcome T s n X ξ).2.1)) =
      translateBonds (siteOfInt (scaleBy ℓ.side v)) (markedBonds (T.stage s).toStepSetup
        (hotCoreSites (T.stage s).toStepSetup (rule.stepOutcome T s n X ξ).2.1)) := by
    rw [hv, hotCoreSites_translate hfit (T.stage s).toStepSetup rfl hLn w]
    exact markedBonds_translateSet hfit.L_odd h2 _ _
  rw [hm, mem_translateBonds_iff]
  refine and_congr_right fun hc => ?_
  have hf := hfr (rule.stepOutcome T s n X ξ).2.1 v _ hc
  simp only [add_sub_cancel_right] at hf
  have hk := bondMark_translate (R := (T.stage s).toStepSetup) hfit.L_odd h2 v (rule.stepOutcome T s n X ξ).2.1 X x i hf
  show ¬ ((ξ.2.2 (x + siteOfInt (scaleBy ℓ.side v), i) : ℝ) < bondMark (T.stage s).toStepSetup _ _ (x, i)) ↔ _
  rw [hk]
private theorem chain_translate (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T)
    (hfit : ℓ.Admissible) (u : ℕ)
    (hfr : ∀ s < u, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ (V : TorusField n) (v : Fin 4 → ℤ),
      ∀ c ∈ markedBonds (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V),
      frameCoord ℓ (T.stage s).toStepSetup.anchorRadius (T.stage s).toStepSetup.depth
          (T.stage s).toStepSetup.frameReach (TorusFields.translate (siteOfInt v) V) (c.1 - siteOfInt (scaleBy ℓ.side v), c.2) =
        frameCoord ℓ (T.stage s).toStepSetup.anchorRadius (T.stage s).toStepSetup.depth
          (T.stage s).toStepSetup.frameReach V c) :
    ∀ (s : ℕ), s ≤ u → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ (w : Fin 4 → ℤ)
      (p : TorusField (fineSide ℓ.side s n) × ChainNoise ℓ s n),
      IsTranslated ℓ s n (scaleBy ℓ.side w) (rule.chain T s n p.1 p.2)
        (rule.chain T s n (pairTranslate ℓ s n (scaleBy ℓ.side w) p).1
          (pairTranslate ℓ s n (scaleBy ℓ.side w) p).2) := by
  have hL0 : 0 < ℓ.side := hfit.L_odd.pos
  intro s
  induction s with
  | zero =>
    intro _ n _ _ w p
    show TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ 0 * scaleBy ℓ.side w i) p.1 =
      TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) p.1
    simp only [pow_zero, one_mul]
  | succ s ih =>
    intro hs n _ hB w p
    have hI := ih (by omega) (n * ℓ.side) (isBlockTorusSide_mul_side hB hL0) (scaleBy ℓ.side w) (p.1, p.2.1)
    have hshift : (fun i => (ℓ.side : ℤ) ^ (s + 1) * scaleBy ℓ.side w i) =
        fun i => (ℓ.side : ℤ) ^ s * scaleBy ℓ.side (scaleBy ℓ.side w) i := by
      funext i
      simp only [scaleBy]
      ring
    have hp : (pairTranslate ℓ (s + 1) n (scaleBy ℓ.side w) p).1 =
        (pairTranslate ℓ s (n * ℓ.side) (scaleBy ℓ.side (scaleBy ℓ.side w)) (p.1, p.2.1)).1 := by
      show TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ (s + 1) * scaleBy ℓ.side w i) p.1 = _
      rw [hshift]
      rfl
    have hq : (pairTranslate ℓ (s + 1) n (scaleBy ℓ.side w) p).2.1 =
        (pairTranslate ℓ s (n * ℓ.side) (scaleBy ℓ.side (scaleBy ℓ.side w)) (p.1, p.2.1)).2 := rfl
    have hn : 2 ≤ n := by
      have h1 := hB.2
      have h2 : ℓ.side * 1 ≤ ℓ.side * ℓ.n₀ := Nat.mul_le_mul_left _ (by have := hfit.n₀_ge; omega)
      have := hfit.L_ge
      omega
    have hstep := stepOutcome_translate rule T hr hfit s n hB.1 hn w
      (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) p.1 p.2.1)) p.2.2
      (fun V v c hc => hfr s (by omega) n hB V v c hc)
    have htop := isTranslated_topField_eq hI
    refine ⟨?_, ?_, ?_⟩
    · show IsTranslated ℓ s (n * ℓ.side) (scaleBy ℓ.side (scaleBy ℓ.side w)) (rule.chain T s (n * ℓ.side) p.1 p.2.1)
        (rule.chain T s (n * ℓ.side) (pairTranslate ℓ (s + 1) n (scaleBy ℓ.side w) p).1
          (pairTranslate ℓ (s + 1) n (scaleBy ℓ.side w) p).2.1)
      rw [hp, hq]
      exact hI
    · show (rule.stepOutcome T s n (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side)
          (pairTranslate ℓ (s + 1) n (scaleBy ℓ.side w) p).1 (pairTranslate ℓ (s + 1) n (scaleBy ℓ.side w) p).2.1))
          (pairTranslate ℓ (s + 1) n (scaleBy ℓ.side w) p).2.2).2.1 = _
      rw [hp, hq, htop]
      exact hstep.1
    · show (show Finset (TorusBond (n * ℓ.side)) from (rule.stepOutcome T s n (topField ℓ s (n * ℓ.side)
          (rule.chain T s (n * ℓ.side) (pairTranslate ℓ (s + 1) n (scaleBy ℓ.side w) p).1
            (pairTranslate ℓ (s + 1) n (scaleBy ℓ.side w) p).2.1))
          (pairTranslate ℓ (s + 1) n (scaleBy ℓ.side w) p).2.2).2.2) = _
      rw [hp, hq, htop]
      exact hstep.2
open Classical in
private theorem hullStep_translate (T : StageTower ℓ) (s₁ : ℝ) (j n : ℕ) [NeZero n] (v : Fin 4 → ℤ)
    (lo : Finset (TorusSite (n * ℓ.side)) × (TorusSite (n * ℓ.side) → ℝ)) (bad : Finset (TorusBond (n * ℓ.side)))
    (C Q : Finset (TorusSite n)) :
    hullStep T s₁ j n (translateSet (siteOfInt (scaleBy ℓ.side v)) lo.1,
          fun z => lo.2 (z + siteOfInt (scaleBy ℓ.side v)))
        (translateBonds (siteOfInt (scaleBy ℓ.side v)) bad) (translateSet (siteOfInt v) C)
        (translateSet (siteOfInt v) Q) =
      (translateSet (siteOfInt v) (hullStep T s₁ j n lo bad C Q).1,
        fun y => (hullStep T s₁ j n lo bad C Q).2 (y + siteOfInt v)) := by
  have hZ : ∀ r : ℕ, translateSet (siteOfInt v) C ∪ (coreBlocks ℓ.side r (attachedSites ℓ.side r
        (translateBonds (siteOfInt (scaleBy ℓ.side v)) bad) (translateSet (siteOfInt (scaleBy ℓ.side v)) lo.1)
        (translateSet (siteOfInt v) C)) ∩ translateSet (siteOfInt v) Q) =
      translateSet (siteOfInt v) (C ∪ (coreBlocks ℓ.side r (attachedSites ℓ.side r bad lo.1 C) ∩ Q)) := by
    intro r
    rw [attachedSites_translate, coreBlocks_translateSet]
    ext z
    simp only [Finset.mem_union, Finset.mem_inter, mem_translateSet_iff]
  have hY : ∀ (r' : ℕ) (Z : Finset (TorusSite n)),
      thickening (r' / 2) (translateSet (siteOfInt v) Z) ∩ translateSet (siteOfInt v) Q =
        translateSet (siteOfInt v) (thickening (r' / 2) Z ∩ Q) := by
    intro r' Z
    rw [thickening_translateSet]
    ext z
    simp only [Finset.mem_inter, mem_translateSet_iff]
  simp only [hullStep]
  rw [hZ, hY]
  refine Prod.ext rfl ?_
  funext y
  simp only [mem_translateSet_iff]
  by_cases h1 : y + siteOfInt v ∈ C ∪ (coreBlocks ℓ.side (T.stage j).toStepSetup.range
      (attachedSites ℓ.side (T.stage j).toStepSetup.range bad lo.1 C) ∩ Q)
  · simp only [if_pos h1]
    congr 1
    refine Finset.sum_nbij' (fun z : TorusSite (n * ℓ.side) => z + siteOfInt (scaleBy ℓ.side v))
      (fun z : TorusSite (n * ℓ.side) => z - siteOfInt (scaleBy ℓ.side v)) ?_ ?_ ?_ ?_ ?_
    · intro z hz
      obtain ⟨e1, e2⟩ := Finset.mem_inter.1 hz
      refine Finset.mem_inter.2 ⟨?_, mem_translateSet_iff.1 e2⟩
      rw [mem_sitesInBlocks_iff, parentBlock_add_scaleBy, Finset.mem_singleton.1 (mem_sitesInBlocks_iff.1 e1)]
      exact Finset.mem_singleton_self _
    · intro z hz
      obtain ⟨e1, e2⟩ := Finset.mem_inter.1 hz
      refine Finset.mem_inter.2 ⟨?_, mem_translateSet_iff.2 (by simpa using e2)⟩
      have e3 : parentBlock ℓ.side (z - siteOfInt (scaleBy ℓ.side v)) + siteOfInt v = parentBlock ℓ.side z := by
        rw [← parentBlock_add_scaleBy]
        simp
      rw [mem_sitesInBlocks_iff, Finset.mem_singleton]
      have e4 := Finset.mem_singleton.1 (mem_sitesInBlocks_iff.1 e1)
      rw [e4] at e3
      exact add_right_cancel e3
    · intro z _
      simp
    · intro z _
      simp
    · intro z _
      rfl
  · simp only [if_neg h1]
private theorem localHullData_translate (T : StageTower ℓ) (hfit : ℓ.Admissible) (s₁ : ℝ) :
    ∀ (s n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ (w : Fin 4 → ℤ) (d d' : MarkedSample ℓ s n)
      (Q : Finset (TorusSite n)),
      IsTranslated ℓ s n (scaleBy ℓ.side w) d d' →
      localHullData T s₁ s n d' (translateSet (siteOfInt (scaleBy ℓ.side w)) Q) =
        (translateSet (siteOfInt (scaleBy ℓ.side w)) (localHullData T s₁ s n d Q).1,
          fun y => (localHullData T s₁ s n d Q).2 (y + siteOfInt (scaleBy ℓ.side w))) := by
  classical
  have hL0 : 0 < ℓ.side := hfit.L_odd.pos
  intro s
  induction s with
  | zero =>
    intro n _ hB w d d' Q h
    have hh : hullSet T 0 n d' = translateSet (siteOfInt (scaleBy ℓ.side w)) (hullSet T 0 n d) := by
      show thickening (2 * clusterRange T.base.coupling) (torusHotSites ℓ (show TorusField n from d')) =
        translateSet (siteOfInt (scaleBy ℓ.side w))
          (thickening (2 * clusterRange T.base.coupling) (torusHotSites ℓ (show TorusField n from d)))
      have h' : (show TorusField n from d') = TorusFields.translate (siteOfInt (scaleBy ℓ.side w)) (show TorusField n from d) := h
      rw [h', torusHotSites_translate hfit hB.1, thickening_translateSet]
    simp only [localHullData]
    rw [hh]
    refine Prod.ext ?_ rfl
    ext z
    simp only [Finset.mem_inter, mem_translateSet_iff]
  | succ s ih =>
    intro n _ hB w d d' Q h
    obtain ⟨h0, hV, hbad⟩ := h
    have hI := ih (n * ℓ.side) (isBlockTorusSide_mul_side hB hL0) (scaleBy ℓ.side w) d.1 d'.1
      (sitesInBlocks ℓ.side Q) h0
    rw [localHullData_succ, localHullData_succ, sitesInBlocks_translateSet, hI, hV, hbad,
      hotCoreSites_translate hfit (T.stage s).toStepSetup rfl hB.1 w]
    have hf : ∀ B : Finset (TorusBond (n * ℓ.side)),
        (translateBonds (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) B).filter
          (fun b => b.1 ∈ translateSet (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w))) (sitesInBlocks ℓ.side Q)) =
        translateBonds (siteOfInt (scaleBy ℓ.side (scaleBy ℓ.side w)))
          (B.filter fun b => b.1 ∈ sitesInBlocks ℓ.side Q) := by
      intro B
      ext c
      simp only [Finset.mem_filter, mem_translateBonds_iff, mem_translateSet_iff]
    have hc : translateSet (siteOfInt (scaleBy ℓ.side w)) (hotCoreSites (T.stage s).toStepSetup d.2.2.1) ∩
          translateSet (siteOfInt (scaleBy ℓ.side w)) Q =
        translateSet (siteOfInt (scaleBy ℓ.side w)) (hotCoreSites (T.stage s).toStepSetup d.2.2.1 ∩ Q) := by
      ext z
      simp only [Finset.mem_inter, mem_translateSet_iff]
    rw [hf, hc]
    exact hullStep_translate T s₁ s n (scaleBy ℓ.side w) _ _ _ _
end Moves
section Core
variable {ℓ : StepParameters}
private theorem hasExpansion_expansionCoupling (hret : ExpansionReturnsAt ℓ) {t : ℕ} {x : ℝ} {D : TorusFunctional}
    (hy : ℓ.y₁ ≤ x) (hrow : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem hasExpansion_couplingFlow (hret : ExpansionReturnsAt ℓ) (β : ℝ)
    (h0 : HasExpansion ℓ 0 β (wilsonWeight β)) :
    ∀ t, (∀ j < t, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) → HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2 := by apply _root_.YangMills.SharedProofs.p3977 <;> assumption
private theorem stage_anchorRadius (T : StageTower ℓ) : ∀ j, (T.stage j).anchorRadius = T.base.anchorRadius := by apply _root_.YangMills.SharedProofs.p36710 <;> assumption
private theorem localHullBox_eq_univ {n : ℕ} [NeZero n] (T : StageTower ℓ) (u : ℕ) (z : TorusSite n) (D : ℝ)
    (hD : (n : ℝ) ≤ D) : localHullBox T u z D = Finset.univ := by
  ext x
  simp only [Finset.mem_univ, iff_true, localHullBox, box, mem_thickening_iff, Finset.mem_singleton, exists_eq_left]
  have h1 : _root_.YangMills.Construction.TorusFields.supDist x z ≤ n := by
    refine Finset.sup_le fun i _ => ?_
    have h2 := ZMod.natAbs_valMinAbs_le (x i - z i)
    have h3 : n / 2 ≤ n := Nat.div_le_self _ _
    omega
  have h4 : n ≤ ⌊2 * D⌋₊ := by
    refine Nat.le_floor ?_
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  omega
private theorem supDiam_lt {n : ℕ} [NeZero n] (X : Finset (TorusSite n)) : (supDiam X : ℝ) < ((n : ℝ) + 1) := by
  have h1 : supDiam X ≤ n := by
    refine Finset.sup_le fun a _ => Finset.sup_le fun b _ => Finset.sup_le fun i _ => ?_
    have h2 := ZMod.natAbs_valMinAbs_le (a i - b i)
    have h3 : n / 2 ≤ n := Nat.div_le_self _ _
    omega
  have h2 : (supDiam X : ℝ) ≤ n := by exact_mod_cast h1
  linarith
end Core
end HullTranslation
open HullTranslation in
theorem hullTranslation_holds (hmoves : StepFrames.FrameCovariance)
    (hlo : HullTrees.localHullSubsetStatement) : hullTranslationStatement := by
  intro a ha
  obtain ⟨L₁, r₁, C₁, hr₁, H₁⟩ := hlo a ha
  refine ⟨L₁, r₁, C₁, hr₁, ?_⟩
  intro L hL hLL Tb hTa hTL hdrawn hCold hOn hrt hCd
  obtain ⟨M, G⟩ := H₁ L hL hLL Tb hTa hTL hdrawn hCold hOn hrt hCd
  refine ⟨M, ?_⟩
  intro Kr hM hη hN hF hRs
  obtain ⟨y₁, G⟩ := G Kr hM hη hN hF hRs
  refine ⟨max y₁ (max Tb.floorMin (max (((2 ^ 16 + Tb.side : ℕ) : ℝ) ^ 100) (Tb.B ^ 100))), ?_⟩
  intro y hyy hret hwil g β K m T u n _ hat rule hrule z w p
  have hy := le_of_max_le_right hyy
  have hlies := G y (le_of_max_le_left hyy) hret hwil g β K m T
  have hfit := hdrawn.fits y ((le_max_left _ _).trans hy)
  have hy2 : ((2 ^ 16 + Tb.side : ℕ) : ℝ) ^ 100 ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy3 : Tb.B ^ 100 ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hB1 : 1 ≤ Tb.B := hdrawn.B_ge
  have hrun := hat.chain
  have hyB : Tb.B ≤ y := by
    have h1 : Tb.B ^ 1 ≤ Tb.B ^ 100 := pow_le_pow_right₀ hB1 (by norm_num)
    simpa using h1.trans hy3
  have hy0 : 0 < y := by linarith
  have hstand := hrun.follows
  have hfl : y ≤ (g ^ 2)⁻¹ := hrun.le_inv_sq
  have habove : (g ^ 2)⁻¹ + 2 * Tb.B ≤ β := hrun.upper_le
  have hpass := hrun.isFirst
  have hΞ : ∀ k < K, (g ^ 2)⁻¹ + 2 * Tb.B < (couplingFlow (Tb.stepParameters y) β k).1 := hpass.2
  have hβy : y ≤ β := by linarith
  have hrows := hasExpansion_couplingFlow hret β (hwil β hβy)
  have hlow : ∀ k < K, y ≤ (couplingFlow (Tb.stepParameters y) β k).1 := fun k hk => by
    have := hΞ k hk
    linarith
  have hmove : ∀ t < K, |(couplingFlow (Tb.stepParameters y) β (t + 1)).1 -
      (couplingFlow (Tb.stepParameters y) β t).1| ≤ 2 * Tb.B := fun t ht =>
    (hasExpansion_expansionCoupling hret (hlow t ht) (hrows t fun j hj => hlow j (by omega))).2
  have hxy : ∀ j ≤ K, y ≤ (couplingFlow (Tb.stepParameters y) β j).1 := by
    intro j hj
    rcases lt_or_eq_of_le hj with h | rfl
    · exact hlow j h
    · cases j with
      | zero =>
        show y ≤ β
        exact hβy
      | succ t =>
        have h1 := abs_le.1 (hmove t (by omega))
        have h2 := hΞ t (by omega)
        linarith [h1.1]
  have hbig : ∀ j ≤ u, 2 ^ 16 + (Tb.stepParameters y).side ≤ stageRange T j := fun j hj => by
    have e : stageRange T j = clusterRange (couplingFlow (Tb.stepParameters y) β j).1 := by
      unfold stageRange
      rw [hstand j (by have := hat.le; omega)]
    rw [e]
    exact le_clusterRange (hy2.trans (hxy j (hj.trans hat.le)))
  have hnear : ∀ j < u, stageRange T j ≤ stageRange T (j + 1) + 1 := fun j hj => by
    have hK := hat.le
    have e : stageRange T j = clusterRange (couplingFlow (Tb.stepParameters y) β j).1 := by
      unfold stageRange
      rw [hstand j (by omega)]
    have e' : stageRange T (j + 1) = clusterRange (couplingFlow (Tb.stepParameters y) β (j + 1)).1 := by
      unfold stageRange
      rw [hstand (j + 1) (by omega)]
    rw [e, e']
    have h1 := abs_le.1 (hmove j (by omega))
    have h2 := hxy j (by omega)
    exact clusterRange_le_succ hB1 (hy3.trans (hxy (j + 1) (by omega))) (by linarith) (by linarith [h1.1])
  have hfr : ∀ s < u, ∀ (n : ℕ) [NeZero n], IsBlockTorusSide (Tb.stepParameters y) n →
      ∀ (V : TorusField n) (v : Fin 4 → ℤ),
      ∀ c ∈ markedBonds (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V),
      frameCoord (Tb.stepParameters y) (T.stage s).toStepSetup.anchorRadius (T.stage s).toStepSetup.depth
          (T.stage s).toStepSetup.frameReach (TorusFields.translate (siteOfInt v) V)
          (c.1 - siteOfInt (scaleBy (Tb.stepParameters y).side v), c.2) =
        frameCoord (Tb.stepParameters y) (T.stage s).toStepSetup.anchorRadius (T.stage s).toStepSetup.depth
          (T.stage s).toStepSetup.frameReach V c := by
    intro s hs n _ hB V v c hc
    classical
    obtain ⟨hc1, hc2⟩ := Finset.mem_filter.1 hc
    have hρ : (T.stage s).toStepSetup.anchorRadius = Tb.ρA := (stage_anchorRadius T s).trans hrun.anchor_bottom
    have hCC : ColdChainConstants (Tb.stepParameters y).coupling Tb.δ₁ (Tb.stepParameters y).side Tb.lam
        (T.stage s).toStepSetup.anchorRadius Tb.σA Tb.cg Tb.N := by
      rw [hρ]
      exact hdrawn.chain
    have hbs := hbig s (by omega)
    have hbs' := hbig (s + 1) hs
    have hRF : RangesAdmissible (T.stage s).toStepSetup.range (T.stage s).toStepSetup.nextRange :=
      ⟨hnear s hs, by
        show 2 ^ 16 ≤ stageRange T (s + 1)
        omega, (Nat.le_div_iff_mul_le (by norm_num)).2 (by
        show 16 * 2 ^ 11 ≤ stageRange T s
        omega)⟩
    exact (hmoves (Tb.stepParameters y) Tb.δ₁ Tb.lam (T.stage s).toStepSetup.anchorRadius Tb.σA Tb.cg Tb.N hfit hCC
      hdrawn.σ_le (T.stage s).toStepSetup.depth (T.stage s).toStepSetup.range (T.stage s).toStepSetup.nextRange
      n V _ _ _ hRF (Or.inl ⟨hB, rfl, rfl, rfl⟩) c hc1 hc2).2 v
  have hBn : IsBlockTorusSide (Tb.stepParameters y) n := by
    have hL2 := hdrawn.L_ge
    have hn0 := hdrawn.n₀_ge
    have hvol : Tb.side * Tb.n₀ ≤ 2 * Tb.side ^ m := hrun.volume_le
    have hLpos : 0 < Tb.side := by omega
    have hside : n = 2 * Tb.side ^ m * Tb.side ^ (K - u) := by
      rw [hat.side_eq]
      exact fineSide_eq _ _ _
    have hm : m ≠ 0 := by
      rintro rfl
      have : 1 * 4096 ≤ Tb.side * Tb.n₀ := Nat.mul_le_mul (by omega) hn0
      simp at hvol
      omega
    refine ⟨?_, ?_⟩
    · show Tb.side ∣ n
      rw [hside]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ hm) _) _
    · show Tb.side * Tb.n₀ ≤ n
      rw [hside]
      exact hvol.trans (Nat.le_mul_of_pos_right _ (pow_pos hLpos _))
  have key : ∀ d : MarkedSample (Tb.stepParameters y) u n,
      hullSet T u n d = (localHullData T Kr.s₁ u n d Finset.univ).1 := by
    intro d
    classical
    ext x
    constructor
    · intro hx
      have h1 := ((hlies.1 u n hat d).2 x ((n : ℝ) + 1) (by positivity) hx (supDiam_lt _)).1
      rwa [localHullBox_eq_univ T u x _ (by linarith)] at h1
    · intro hx
      exact ((hlies.1 u n hat d).1 Finset.univ).1 hx
  have hm := chain_translate rule T hrule hfit u hfr u le_rfl n hBn w p
  have hh := localHullData_translate T hfit Kr.s₁ u n hBn w _ _ Finset.univ hm
  have huniv : translateSet (siteOfInt (scaleBy (Tb.stepParameters y).side w)) (Finset.univ : Finset (TorusSite n)) =
      Finset.univ := by
    ext x
    simp [mem_translateSet_iff]
  rw [huniv] at hh
  rw [key, key, hh]
  exact mem_translateSet_iff
end MomentLaw
end YangMills.Construction
end
