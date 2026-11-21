import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import YangMills.Construction.LawByMomentsOfTheFlow.ScoresInALimitFieldProof
import YangMills.Construction.HullsInEveryVolume.TranslationsMoveAUnit
import YangMills.Construction.LawByMomentsOfTheFlow.TheChainMovesWithATranslationProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.HullsInEveryVolume
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepSettings YangMills.Construction.StepCosts YangMills.Construction.TopLevelSites YangMills.Construction.TorusContours YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.HullTrees YangMills.Construction.ChainNoise YangMills.Construction.WeightedResponses YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepReturn YangMills.Construction.StepMarks YangMills.Construction.ColdChain
namespace UnitTranslation
section Sets
variable {m : ℕ} [NeZero m]
private theorem mem_translateSet {a z : TorusSite m} {Y : Finset (TorusSite m)} :
    z ∈ translateSet a Y ↔ z + a ∈ Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.mem_translateSet <;> assumption
private theorem supDist_add_add (a x y : TorusSite m) : supDist (x + a) (y + a) = supDist x y := by
  simp [TorusFields.supDist]
private theorem mem_thickening_iff {k : ℕ} {X : Finset (TorusSite m)} {z : TorusSite m} :
    z ∈ thickening k X ↔ ∃ x ∈ X, supDist z x ≤ k := by apply _root_.YangMills.Construction.TorusFields.mem_thickening <;> assumption
private theorem thickening_translateSet (k : ℕ) (a : TorusSite m) (X : Finset (TorusSite m)) :
    thickening k (translateSet a X) = translateSet a (thickening k X) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.thickening_translateSet <;> assumption
end Sets
section Scale
variable {n L : ℕ}
abbrev blockScale (L : ℕ) (v : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (L : ℤ) * v i
private theorem exists_cast_add_intCast {m : ℕ} [NeZero m] (x : ZMod m) (z : ℤ) :
    ∃ k : ℤ, (((x + (z : ZMod m) : ZMod m)).cast : ℤ) = (x.cast : ℤ) + z + (m : ℤ) * k := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.exists_cast_add_intCast <;> assumption
private theorem parentBlock_add_blockScale [NeZero n] [NeZero L] (x : TorusSite (n * L)) (v : Fin 4 → ℤ) :
    parentBlock L (x + siteOfInt (blockScale L v)) = parentBlock L x + siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.parentBlock_add_scale <;> assumption
end Scale
section Hot
variable {ℓ : TorusLumps.StepParameters} {m : ℕ} [NeZero m]
private theorem curvature_translate_apply (a : TorusSite m) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    curvature (TorusFields.translate a W) x μ ν = curvature W (x + a) μ ν := by
  simp only [curvature, holonomy, TorusFields.translate, add_right_comm x a]
private theorem mem_plaquetteVertices_translate (a : TorusSite m) (x z : TorusSite m) (μ ν : Fin 4) :
    z ∈ plaquetteVertices x μ ν ↔ z + a ∈ plaquetteVertices (x + a) μ ν := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.mem_plaquetteVertices_add <;> assumption
private theorem torusHotLumps_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (W : TorusField m) :
    torusHotLumps ℓ (TorusFields.translate (siteOfInt (blockScale ℓ.side w)) W) =
      (torusHotLumps ℓ W).image (translateSet (siteOfInt (blockScale ℓ.side w))) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusHotLumps_translate <;> assumption
private theorem torusHotSites_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (W : TorusField m) :
    torusHotSites ℓ (TorusFields.translate (siteOfInt (blockScale ℓ.side w)) W) =
      translateSet (siteOfInt (blockScale ℓ.side w)) (torusHotSites ℓ W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusHotSites_translate <;> assumption
end Hot
section Chart
variable {F : BlockFrame} (u : Fin 4 → ℤ)
private def cellTranslation : F.Site F.depth := siteOfCoords F.depth fun i => (F.blockSide : ℤ) * u i
private def translateFine (X : F.GaugeField F.depth) : F.GaugeField F.depth := fun x i => X (x + cellTranslation u) i
private def translateCoarse (U : F.GaugeField F.top) : F.GaugeField F.top := fun y i => U (y + siteOfCoords F.top u) i
private theorem pathHolonomy_translateFine (X : F.GaugeField F.depth) (x : F.Site F.depth) (l : List PathStep) :
    pathHolonomy (translateFine u X) x l = pathHolonomy X (x + cellTranslation u) l := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.pathHolonomy_translateFine <;> assumption
private theorem enclosingCell_translate (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (x : F.Site F.depth) :
    enclosingCell (x + cellTranslation u) = enclosingCell x + siteOfCoords F.top u := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.enclosingCell_add_translation <;> assumption
private theorem axialGauge_translateFine (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (π : Equiv.Perm (Fin 4)) (X : F.GaugeField F.depth) (x : F.Site F.depth) :
    axialGauge π (translateFine u X) x = axialGauge π X (x + cellTranslation u) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.axialGauge_translateFine <;> assumption
private theorem bondCoordinate_translate (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (π : Equiv.Perm (Fin 4)) (U : F.GaugeField F.top) (X : F.GaugeField F.depth)
    (x : F.Site F.depth) (i : Fin 4) :
    bondCoordinate π (translateCoarse u U) (translateFine u X) (x, i) =
      bondCoordinate π U X (x + cellTranslation u, i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.bondCoordinate_translate <;> assumption
end Chart
section Step
variable {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
private theorem toTorusSite_coarse_translate (v : Fin 4 → ℤ) (y : (stepBlockFrame ℓ.side n).Cell) :
    toTorusSite n (y + siteOfCoords (stepBlockFrame ℓ.side n).top v) = toTorusSite n y + siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.toTorusSite_add_coarse <;> assumption
private theorem two_le_extent (hn : 2 ≤ n) : ∀ i, 2 ≤ (stepBlockFrame ℓ.side n).extent i := fun _ => hn
private theorem chartCoord_translate (hL : Odd ℓ.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (x : TorusSite (n * ℓ.side)) (i : Fin 4) :
    chartCoord ℓ (TorusFields.translate (siteOfInt v) V) (TorusFields.translate (siteOfInt (blockScale ℓ.side v)) W) (x, i) =
      chartCoord ℓ V W (x + siteOfInt (blockScale ℓ.side v), i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.chartCoord_translate <;> assumption
private theorem mem_chartBonds_translate (hL : Odd ℓ.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ)
    (x : TorusSite (n * ℓ.side)) (i : Fin 4) :
    (x + siteOfInt (blockScale ℓ.side v), i) ∈ chartBonds ℓ.side n ↔ (x, i) ∈ chartBonds ℓ.side n := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.add_mem_chartBonds_iff <;> assumption
end Step
section Moves
variable {ℓ : TorusLumps.StepParameters}
private theorem mem_box_translate {m : ℕ} [NeZero m] (a : TorusSite m) (z c : TorusSite m) (k : ℕ) :
    c ∈ HullTrees.box z k ↔ c + a ∈ HullTrees.box (z + a) k := by
  simp only [HullTrees.box, mem_thickening_iff, Finset.mem_singleton, exists_eq_left]
  rw [supDist_add_add]
private theorem stepOutcome_field_translate (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T)
    (s n : ℕ) [NeZero n] (v : Fin 4 → ℤ) (W : TorusField (n * ℓ.side)) (U : StepNoise ℓ n) :
    (rule.stepOutcome T s n (TorusFields.translate (siteOfInt (blockScale ℓ.side v)) W)
        (fun y => U.1 (y + siteOfInt v), fun c => U.2.1 (c.1 + siteOfInt v, c.2),
          fun b => U.2.2 (b.1 + siteOfInt (blockScale ℓ.side v), b.2))).2.1 =
      TorusFields.translate (siteOfInt v) (rule.stepOutcome T s n W U).2.1 := by apply _root_.YangMills.DeltaSharedProofs.p501493 <;> assumption
private theorem topField_translate (rule : NoiseRule ℓ) (T : StageTower ℓ) (hr : rule.IsAdmissible T) :
    ∀ (s n : ℕ) [NeZero n] (v : Fin 4 → ℤ) (W : TorusField (fineSide ℓ.side s n)) (U : ChainNoise ℓ s n),
      topField ℓ s n (rule.chain T s n (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ s * v i) W)
          (noiseTranslate ℓ s n v U)) =
        TorusFields.translate (siteOfInt v) (topField ℓ s n (rule.chain T s n W U)) := by
  intro s
  induction s with
  | zero =>
    intro n _ v W U
    have e : (fun i => (ℓ.side : ℤ) ^ 0 * v i) = v := by
      funext i
      simp
    simp only [e]
    rfl
  | succ s ih =>
    intro n _ v W U
    have e : (fun i => (ℓ.side : ℤ) ^ (s + 1) * v i) = fun i => (ℓ.side : ℤ) ^ s * blockScale ℓ.side v i := by
      funext i
      simp only [blockScale]
      ring
    rw [e]
    have h := ih (n * ℓ.side) (blockScale ℓ.side v) W U.1
    show (rule.stepOutcome T s n (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side)
        (TorusFields.translate (siteOfInt fun i => (ℓ.side : ℤ) ^ s * blockScale ℓ.side v i) W)
        (noiseTranslate ℓ s (n * ℓ.side) (blockScale ℓ.side v) U.1)))
        (fun y => U.2.1 (y + siteOfInt v), fun c => U.2.2.1 (c.1 + siteOfInt v, c.2),
          fun b => U.2.2.2 (b.1 + siteOfInt (blockScale ℓ.side v), b.2))).2.1 =
      TorusFields.translate (siteOfInt v)
        (rule.stepOutcome T s n (topField ℓ s (n * ℓ.side) (rule.chain T s (n * ℓ.side) W U.1)) U.2).2.1
    rw [h]
    exact stepOutcome_field_translate rule T hr s n v _ U.2
private theorem containsHotPlaquette_translate {m : ℕ} [NeZero m] (a : TorusSite m) (V : TorusField m)
    (z : TorusSite m) (k : ℕ) :
    ContainsHotPlaquette ℓ (TorusFields.translate a V) (HullTrees.box z k) ↔
      ContainsHotPlaquette ℓ V (HullTrees.box (z + a) k) := by
  classical
  have hbox : ∀ c : TorusSite m, c ∈ HullTrees.box z k ↔ c + a ∈ HullTrees.box (z + a) k :=
    fun c => mem_box_translate a z c k
  constructor
  · rintro ⟨⟨x, μ, ν⟩, hp, hs⟩
    obtain ⟨-, hlt, hc⟩ := (by simpa [plaquettesIn] using hp :
      True ∧ μ < ν ∧ ∀ c ∈ plaquetteVertices x μ ν, c ∈ HullTrees.box z k)
    refine ⟨⟨x + a, μ, ν⟩, ?_, ?_⟩
    · simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hlt, fun c h => ?_⟩
      have h' : c - a ∈ plaquetteVertices x μ ν := by
        rw [mem_plaquetteVertices_translate a, sub_add_cancel]
        exact h
      have := (hbox _).mp (hc _ h')
      rwa [sub_add_cancel] at this
    · have := hs
      simp only at this
      rwa [curvature_translate_apply] at this
  · rintro ⟨⟨x, μ, ν⟩, hp, hs⟩
    obtain ⟨-, hlt, hc⟩ := (by simpa [plaquettesIn] using hp :
      True ∧ μ < ν ∧ ∀ c ∈ plaquetteVertices x μ ν, c ∈ HullTrees.box (z + a) k)
    refine ⟨⟨x - a, μ, ν⟩, ?_, ?_⟩
    · simp only [plaquettesIn, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hlt, fun c h => ?_⟩
      refine (hbox _).mpr (hc _ ?_)
      have := (mem_plaquetteVertices_translate a (x - a) c μ ν).mp h
      rwa [sub_add_cancel] at this
    · show ℓ.threshold ≤ curvature (TorusFields.translate a V) (x - a) μ ν
      rw [curvature_translate_apply, sub_add_cancel]
      exact hs
private theorem mem_markedBonds_translate (R : StepSetup) {n : ℕ} [NeZero n] (hL : Odd R.params.side) (hn : 2 ≤ n)
    (v : Fin 4 → ℤ) (C : Finset (TorusSite n)) (x : TorusSite (n * R.params.side)) (i : Fin 4) :
    (x, i) ∈ markedBonds R (translateSet (siteOfInt v) C) ↔
      (x + siteOfInt (blockScale R.params.side v), i) ∈ markedBonds R C := by apply _root_.YangMills.DeltaSharedProofs.p502462 <;> assumption
private theorem bondMark_translate (R : StepSetup) {n : ℕ} [NeZero n] (hL : Odd R.params.side) (hn : 2 ≤ n)
    (v : Fin 4 → ℤ) (V : TorusField n) (W : TorusField (n * R.params.side)) (x : TorusSite (n * R.params.side))
    (i : Fin 4)
    (h : frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.translate (siteOfInt v) V) (x, i) =
      frameCoord R.params R.anchorRadius R.depth R.frameReach V (x + siteOfInt (blockScale R.params.side v), i)) :
    bondMark R (TorusFields.translate (siteOfInt v) V) (TorusFields.translate (siteOfInt (blockScale R.params.side v)) W) (x, i) =
      bondMark R V W (x + siteOfInt (blockScale R.params.side v), i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.bondMark_translate <;> assumption
private theorem mem_badBonds_translate (hfit : ℓ.Admissible) (rule : NoiseRule ℓ) (T : StageTower ℓ)
    (hr : rule.IsAdmissible T) (s n : ℕ) [NeZero n] (hB : IsBlockTorusSide ℓ n) (w : Fin 4 → ℤ)
    (hfr : ∀ V : TorusField n, ∀ c ∈ markedBonds (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup V),
      frameCoord ℓ (T.stage s).anchorRadius (T.stage s).depth (T.stage s).toStepSetup.frameReach
          (TorusFields.translate (siteOfInt (blockScale ℓ.side w)) V)
          (c.1 - siteOfInt (blockScale ℓ.side (blockScale ℓ.side w)), c.2) =
        frameCoord ℓ (T.stage s).anchorRadius (T.stage s).depth (T.stage s).toStepSetup.frameReach V c)
    (W : TorusField (n * ℓ.side)) (U : StepNoise ℓ n) (x : TorusSite (n * ℓ.side)) (i : Fin 4) :
    (x, i) ∈ (show Finset (TorusBond (n * ℓ.side)) from
        (rule.stepOutcome T s n (TorusFields.translate (siteOfInt (blockScale ℓ.side (blockScale ℓ.side w))) W)
          (fun y => U.1 (y + siteOfInt (blockScale ℓ.side w)),
            fun c => U.2.1 (c.1 + siteOfInt (blockScale ℓ.side w), c.2),
            fun b => U.2.2 (b.1 + siteOfInt (blockScale ℓ.side (blockScale ℓ.side w)), b.2))).2.2) ↔
      (x + siteOfInt (blockScale ℓ.side (blockScale ℓ.side w)), i) ∈
        (show Finset (TorusBond (n * ℓ.side)) from (rule.stepOutcome T s n W U).2.2) := by apply _root_.YangMills.DeltaSharedProofs.p983 <;> assumption
end Moves
section Flow
variable {ℓ : TorusLumps.StepParameters}
private theorem flow_expansion {Tb : ParameterAssignment} {y g β : ℝ} {K : ℕ} (hB : 0 ≤ Tb.B)
    (hret : ExpansionReturnsAt (Tb.stepParameters y))
    (h0 : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β))
    (hp : FlowCrossing Tb y g β K) :
    ∀ j ≤ K, y ≤ (couplingFlow (Tb.stepParameters y) β j).1 ∧
      HasExpansion (Tb.stepParameters y) j (couplingFlow (Tb.stepParameters y) β j).1
        (couplingFlow (Tb.stepParameters y) β j).2 ∧
      (j < K → |(couplingFlow (Tb.stepParameters y) β (j + 1)).1 - (couplingFlow (Tb.stepParameters y) β j).1| ≤
        2 * Tb.B) := by apply _root_.YangMills.SharedProofs.p36592 <;> assumption
private theorem clusterRange_mono {x x' : ℝ} (h0 : 0 ≤ x) (h : x ≤ x') : clusterRange x ≤ clusterRange x' := by apply _root_.YangMills.Construction.WilsonExpansion.clusterRange_mono <;> assumption
private theorem clusterRange_le_succ {x x' b : ℝ} (hb : 0 ≤ b) (h1 : 1 ≤ x') (h2 : (2 * b) ^ 2 ≤ x') (hx : 0 ≤ x)
    (h : x ≤ x' + 2 * b) : clusterRange x ≤ clusterRange x' + 1 := by exact _root_.YangMills.SharedProofs.p16909 hb h1 h2 hx h
private theorem stage_anchorRadius {ℓ : TorusLumps.StepParameters} (T : StageTower ℓ) :
    ∀ j, (T.stage j).anchorRadius = T.base.anchorRadius := by apply _root_.YangMills.SharedProofs.p36710 <;> assumption
private theorem isBlockTorusSide_of_level {Tb : ParameterAssignment} {y g β : ℝ} {K m : ℕ}
    {T : StageTower (Tb.stepParameters y)} {u n : ℕ}
    (hD : Tb.Admissible) (hlev : HullChainAtLevel Tb y g β K m T u n) : IsBlockTorusSide (Tb.stepParameters y) n := by apply _root_.YangMills.SharedProofs.p59774 <;> assumption
end Flow
end UnitTranslation
open UnitTranslation in
theorem unitTranslationStatement_holds (hF : StepFrames.FrameCovariance) : unitTranslationStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hD _ _ _ _
  refine ⟨0, ?_⟩
  intro Kr _ _ _ _ _
  refine ⟨max Tb.floorMin ((2 * Tb.B) ^ 2), ?_⟩
  intro y hy hret h0 g β K m T u n _ hlev rule hr z w p
  have hy1 : Tb.floorMin ≤ y := le_trans (le_max_left _ _) hy
  have hy2 : (2 * Tb.B) ^ 2 ≤ y := le_trans (le_max_right _ _) hy
  have hfits : (Tb.stepParameters y).Admissible := hD.fits y hy1
  have hB : 0 ≤ Tb.B := le_trans zero_le_one hD.B_ge
  obtain ⟨W, U⟩ := p
  have hkey : HullTrees.IsUnit T u n (rule.chain T u n
        (TorusFields.translate (siteOfInt fun i => ((Tb.stepParameters y).side : ℤ) ^ u *
          blockScale (Tb.stepParameters y).side w i) W)
        (noiseTranslate (Tb.stepParameters y) u n (blockScale (Tb.stepParameters y).side w) U)) z ↔
      HullTrees.IsUnit T u n (rule.chain T u n W U) (z + siteOfInt (blockScale (Tb.stepParameters y).side w)) := by
    unfold HullTrees.IsUnit
    rw [topField_translate rule T hr u n (blockScale (Tb.stepParameters y).side w) W U, containsHotPlaquette_translate]
    refine or_congr Iff.rfl ?_
    cases u with
    | zero => exact Iff.rfl
    | succ s =>
      have hs : s + 1 ≤ K := hlev.le
      have hrun := flow_expansion hB hret h0 hlev.chain.toCrossingVolume.toFlowCrossing
      obtain ⟨hy0, -, hmove⟩ := hrun s (by omega)
      obtain ⟨hy1', -, -⟩ := hrun (s + 1) hs
      have hmove' := hmove (by omega)
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
      have hblock : IsBlockTorusSide (Tb.stepParameters y) n := isBlockTorusSide_of_level hD hlev
      have hfr : ∀ V : TorusField n, ∀ c ∈ markedBonds (T.stage s).toStepSetup
            (hotCoreSites (T.stage s).toStepSetup V),
          frameCoord (Tb.stepParameters y) (T.stage s).anchorRadius (T.stage s).depth
              (T.stage s).toStepSetup.frameReach
              (TorusFields.translate (siteOfInt (blockScale (Tb.stepParameters y).side w)) V)
              (c.1 - siteOfInt (blockScale (Tb.stepParameters y).side
                (blockScale (Tb.stepParameters y).side w)), c.2) =
            frameCoord (Tb.stepParameters y) (T.stage s).anchorRadius (T.stage s).depth
              (T.stage s).toStepSetup.frameReach V c := by
        intro V c hc
        classical
        obtain ⟨hc1, hc2⟩ := Finset.mem_filter.mp hc
        exact (hF (Tb.stepParameters y) Tb.δ₁ Tb.lam (T.stage s).anchorRadius Tb.σA Tb.cg Tb.N hfits hC hD.σ_le
          (T.stage s).depth (T.stage s).toStepSetup.range (T.stage s).toStepSetup.nextRange n V _ _ _ hfit2
          (Or.inl ⟨hblock, rfl, rfl, rfl⟩) c hc1 hc2).2 _
      have htop := topField_translate rule T hr s (n * (Tb.stepParameters y).side)
        (blockScale (Tb.stepParameters y).side (blockScale (Tb.stepParameters y).side w)) W U.1
      have e : (fun i => ((Tb.stepParameters y).side : ℤ) ^ (s + 1) * blockScale (Tb.stepParameters y).side w i) =
          fun i => ((Tb.stepParameters y).side : ℤ) ^ s *
            blockScale (Tb.stepParameters y).side (blockScale (Tb.stepParameters y).side w) i := by
        funext i
        simp only [blockScale]
        ring
      rw [e]
      have hb := mem_badBonds_translate hfits rule T hr s n hblock w hfr
        (topField (Tb.stepParameters y) s (n * (Tb.stepParameters y).side)
          (rule.chain T s (n * (Tb.stepParameters y).side) W U.1)) U.2
      show (∃ b : TorusBond (n * (Tb.stepParameters y).side),
            b ∈ (show Finset (TorusBond (n * (Tb.stepParameters y).side)) from
              (rule.stepOutcome T s n (topField (Tb.stepParameters y) s (n * (Tb.stepParameters y).side)
                (rule.chain T s (n * (Tb.stepParameters y).side)
                  (TorusFields.translate (siteOfInt fun i => ((Tb.stepParameters y).side : ℤ) ^ s *
                    blockScale (Tb.stepParameters y).side (blockScale (Tb.stepParameters y).side w) i) W)
                  (noiseTranslate (Tb.stepParameters y) s (n * (Tb.stepParameters y).side)
                    (blockScale (Tb.stepParameters y).side (blockScale (Tb.stepParameters y).side w)) U.1)))
                (fun y' => U.2.1 (y' + siteOfInt (blockScale (Tb.stepParameters y).side w)),
                  fun c => U.2.2.1 (c.1 + siteOfInt (blockScale (Tb.stepParameters y).side w), c.2),
                  fun b => U.2.2.2 (b.1 + siteOfInt (blockScale (Tb.stepParameters y).side
                    (blockScale (Tb.stepParameters y).side w)), b.2))).2.2) ∧
            parentBlock (Tb.stepParameters y).side b.1 ∈ HullTrees.box z (4 * stageRange T (s + 1))) ↔
        (∃ b : TorusBond (n * (Tb.stepParameters y).side),
            b ∈ (show Finset (TorusBond (n * (Tb.stepParameters y).side)) from
              (rule.stepOutcome T s n (topField (Tb.stepParameters y) s (n * (Tb.stepParameters y).side)
                (rule.chain T s (n * (Tb.stepParameters y).side) W U.1)) U.2).2.2) ∧
            parentBlock (Tb.stepParameters y).side b.1 ∈
              HullTrees.box (z + siteOfInt (blockScale (Tb.stepParameters y).side w)) (4 * stageRange T (s + 1)))
      rw [htop]
      constructor
      · rintro ⟨⟨x, i⟩, h1, h2⟩
        refine ⟨(x + siteOfInt (blockScale (Tb.stepParameters y).side
          (blockScale (Tb.stepParameters y).side w)), i), (hb x i).mp h1, ?_⟩
        show parentBlock (Tb.stepParameters y).side (x + siteOfInt (blockScale (Tb.stepParameters y).side
          (blockScale (Tb.stepParameters y).side w))) ∈ _
        rw [parentBlock_add_blockScale]
        exact (mem_box_translate _ _ _ _).mp h2
      · rintro ⟨⟨x, i⟩, h1, h2⟩
        refine ⟨(x - siteOfInt (blockScale (Tb.stepParameters y).side
          (blockScale (Tb.stepParameters y).side w)), i), (hb _ i).mpr (by simpa using h1), ?_⟩
        refine (mem_box_translate (siteOfInt (blockScale (Tb.stepParameters y).side w)) _ _ _).mpr ?_
        show _ + _ ∈ _
        rw [← parentBlock_add_blockScale]
        simpa using h2
  classical
  simp only [unitIndicator, pairTranslate]
  exact if_congr hkey rfl rfl
end YangMills.Construction.HullsInEveryVolume
end
