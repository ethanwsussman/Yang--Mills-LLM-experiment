import YangMills.Construction.CellOfTheFlow.TranslationsCarryTheWeightOfADraw
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings StepCosts BlockAverages LumpContours WeightedResponses TopLevelSites
  TorusContours BaseTranslations StepFrames
namespace TranslationDensity
section Sets
variable {m : ℕ} [NeZero m]
private theorem mem_translateSet {a z : TorusSite m} {Y : Finset (TorusSite m)} :
    z ∈ translateSet a Y ↔ z + a ∈ Y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.mem_translateSet <;> assumption
private theorem thickening_translateSet (k : ℕ) (a : TorusSite m) (X : Finset (TorusSite m)) :
    thickening k (translateSet a X) = translateSet a (thickening k X) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.thickening_translateSet <;> assumption
private def pullBonds (a : TorusSite m) (B : Finset (TorusBond m)) : Finset (TorusBond m) :=
  open Classical in Finset.univ.filter fun c => (c.1 + a, c.2) ∈ B
private theorem mem_pullBonds {a : TorusSite m} {B : Finset (TorusBond m)} {c : TorusBond m} :
    c ∈ pullBonds a B ↔ (c.1 + a, c.2) ∈ B := by
  classical
  simp [pullBonds]
end Sets
section Scaling
variable {n L : ℕ}
private abbrev scaleCoords (L : ℕ) (v : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => (L : ℤ) * v i
private theorem parentBlock_add_scale [NeZero n] [NeZero L] (x : TorusSite (n * L)) (v : Fin 4 → ℤ) :
    parentBlock L (x + siteOfInt (scaleCoords L v)) = parentBlock L x + siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.parentBlock_add_scale <;> assumption
end Scaling
section HotLumps
variable {ℓ : StepParameters} {m : ℕ} [NeZero m]
private theorem curvature_translate_eq (a : TorusSite m) (W : TorusField m) (x : TorusSite m) (μ ν : Fin 4) :
    curvature (TorusFields.translate a W) x μ ν = curvature W (x + a) μ ν := by
  simp only [curvature, holonomy, TorusFields.translate, add_right_comm x a]
private theorem mem_plaquetteVertices_translate (a : TorusSite m) (x z : TorusSite m) (μ ν : Fin 4) :
    z ∈ plaquetteVertices x μ ν ↔ z + a ∈ plaquetteVertices (x + a) μ ν := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.mem_plaquetteVertices_add <;> assumption
private theorem translateSet_torusLumpOf (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (z : TorusSite m) :
    translateSet (siteOfInt (scaleCoords ℓ.side w)) (torusLumpOf ℓ (z + siteOfInt (scaleCoords ℓ.side w))) =
      torusLumpOf ℓ z := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.translateSet_torusLumpOf <;> assumption
private theorem torusHotLumps_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (W : TorusField m) :
    torusHotLumps ℓ (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) W) =
      (torusHotLumps ℓ W).image (translateSet (siteOfInt (scaleCoords ℓ.side w))) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusHotLumps_translate <;> assumption
private theorem torusHotSites_translate (hfit : ℓ.Admissible) (hLm : ℓ.side ∣ m) (w : Fin 4 → ℤ) (W : TorusField m) :
    torusHotSites ℓ (TorusFields.translate (siteOfInt (scaleCoords ℓ.side w)) W) =
      translateSet (siteOfInt (scaleCoords ℓ.side w)) (torusHotSites ℓ W) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusHotSites_translate <;> assumption
end HotLumps
section Charts
variable {F : BlockFrame} (u : Fin 4 → ℤ)
private def cellTranslation : F.Site F.depth := siteOfCoords F.depth fun i => (F.blockSide : ℤ) * u i
private def translateFine (X : F.GaugeField F.depth) : F.GaugeField F.depth := fun x i => X (x + cellTranslation u) i
private def translateCoarse (U : F.GaugeField F.top) : F.GaugeField F.top := fun y i => U (y + siteOfCoords F.top u) i
private theorem pathHolonomy_translateFine (X : F.GaugeField F.depth) (x : F.Site F.depth) (l : List PathStep) :
    pathHolonomy (translateFine u X) x l = pathHolonomy X (x + cellTranslation u) l := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.pathHolonomy_translateFine <;> assumption
private theorem cellCentre_add_siteOfCoords (z : F.Cell) :
    cellCentre F.depth (z + siteOfCoords F.top u) = cellCentre F.depth z + cellTranslation u := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.cellCentre_add_siteOfCoords <;> assumption
private theorem axialGauge_translate (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i) [∀ j i, NeZero (F.period j i)]
    (π : Equiv.Perm (Fin 4)) (X : F.GaugeField F.depth) (x : F.Site F.depth) :
    axialGauge π (translateFine u X) x = axialGauge π X (x + cellTranslation u) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.axialGauge_translateFine <;> assumption
private theorem bondCoordinate_translate (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    [∀ j i, NeZero (F.period j i)] (π : Equiv.Perm (Fin 4))
    (U : F.GaugeField F.top) (X : F.GaugeField F.depth) (x : F.Site F.depth) (i : Fin 4) :
    bondCoordinate π (translateCoarse u U) (translateFine u X) (x, i) =
      bondCoordinate π U X (x + cellTranslation u, i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.bondCoordinate_translate <;> assumption
end Charts
section StepFrame
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
private theorem torusSiteInFrame_add_scale (v : Fin 4 → ℤ) (x : TorusSite (n * ℓ.side)) :
    torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth (x + siteOfInt (scaleCoords ℓ.side v)) =
      torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth x +
        cellTranslation (F := stepBlockFrame ℓ.side n) v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.torusSiteInFrame_add_scale <;> assumption
private theorem toTorusSite_fine_add (v : Fin 4 → ℤ)
    (x : (stepBlockFrame ℓ.side n).Site (stepBlockFrame ℓ.side n).depth) :
    toTorusSite (n * ℓ.side) (x + cellTranslation (F := stepBlockFrame ℓ.side n) v) =
      toTorusSite (n * ℓ.side) x + siteOfInt (scaleCoords ℓ.side v) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.toTorusSite_add_fine <;> assumption
private theorem toTorusSite_coarse_add (v : Fin 4 → ℤ) (y : (stepBlockFrame ℓ.side n).Cell) :
    toTorusSite n (y + siteOfCoords (stepBlockFrame ℓ.side n).top v) = toTorusSite n y + siteOfInt v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.toTorusSite_add_coarse <;> assumption
private theorem stepBlockFrame_extent_ge (hn : 2 ≤ n) : ∀ i, 2 ≤ (stepBlockFrame ℓ.side n).extent i := fun _ => hn
private theorem chartCoord_translate (hL : Odd ℓ.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (x : TorusSite (n * ℓ.side)) (i : Fin 4) :
    chartCoord ℓ (TorusFields.translate (siteOfInt v) V)
        (TorusFields.translate (siteOfInt (scaleCoords ℓ.side v)) W) (x, i) =
      chartCoord ℓ V W (x + siteOfInt (scaleCoords ℓ.side v), i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.chartCoord_translate <;> assumption
private theorem mem_chartBonds_add_scale (hL : Odd ℓ.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (x : TorusSite (n * ℓ.side))
    (i : Fin 4) :
    (x + siteOfInt (scaleCoords ℓ.side v), i) ∈ chartBonds ℓ.side n ↔ (x, i) ∈ chartBonds ℓ.side n := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.add_mem_chartBonds_iff <;> assumption
end StepFrame
section Marks
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem markedBonds_translateSet (hL : Odd R.params.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ)
    (C : Finset (TorusSite n)) :
    markedBonds R (translateSet (siteOfInt v) C) =
      pullBonds (siteOfInt (scaleCoords R.params.side v)) (markedBonds R C) := by
  classical
  ext ⟨x, i⟩
  rw [mem_pullBonds]
  simp only [markedBonds, Finset.mem_filter, mem_translateSet]
  rw [mem_chartBonds_add_scale hL hn, parentBlock_add_scale]
private theorem bondMark_translate (hL : Odd R.params.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (h : StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach
        (TorusFields.translate (siteOfInt v) V) (x, i) =
      StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach V
        (x + siteOfInt (scaleCoords R.params.side v), i)) :
    bondMark R (TorusFields.translate (siteOfInt v) V)
        (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) W) (x, i) =
      bondMark R V W (x + siteOfInt (scaleCoords R.params.side v), i) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.bondMark_translate <;> assumption
private theorem markProduct_translate (hL : Odd R.params.side) (hn : 2 ≤ n) (v : Fin 4 → ℤ) (C : Finset (TorusSite n))
    (V : TorusField n) (W : TorusField (n * R.params.side)) (bad : Finset (TorusBond (n * R.params.side)))
    (hfr : ∀ c ∈ markedBonds R C, StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach
      (TorusFields.translate (siteOfInt v) V) (c.1 - siteOfInt (scaleCoords R.params.side v), c.2) =
        StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach V c) :
    markProduct R (translateSet (siteOfInt v) C) (TorusFields.translate (siteOfInt v) V)
        (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) W)
        (pullBonds (siteOfInt (scaleCoords R.params.side v)) bad) = markProduct R C V W bad := by
  classical
  unfold markProduct
  rw [markedBonds_translateSet hL hn]
  refine Finset.prod_nbij' (fun c => (c.1 + siteOfInt (scaleCoords R.params.side v), c.2))
    (fun c => (c.1 - siteOfInt (scaleCoords R.params.side v), c.2))
    (fun c hc => mem_pullBonds.mp hc) (fun c hc => mem_pullBonds.mpr (by simpa using hc))
    (fun c _ => by simp) (fun c _ => by simp) ?_
  rintro ⟨x, i⟩ hc
  have hc' : (x + siteOfInt (scaleCoords R.params.side v), i) ∈ markedBonds R C := mem_pullBonds.mp hc
  have h := hfr _ hc'
  simp only [add_sub_cancel_right] at h
  have hm := bondMark_translate (R := R) hL hn v V W x i h
  simp only [mem_pullBonds]
  rw [hm]
end Marks
section Density
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem translateBonds_eq_pullBonds (a : TorusSite (n * R.params.side))
    (B : Finset (TorusBond (n * R.params.side))) : translateBonds a B = pullBonds a B := by
  classical
  ext ⟨x, i⟩
  rw [mem_pullBonds]
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
private theorem stepTransitionDensity_translate (hfit : R.params.Admissible) (hK : TranslationPreservesBaseKernel)
    (hn : R.params.n₀ ≤ n) (v : Fin 4 → ℤ) (W : TorusField (n * R.params.side)) (V : TorusField n)
    (b : BaseChoice R.params.side n) :
    stepTransitionDensity R.params R.coupling (TorusFields.translate (siteOfInt (scaleCoords R.params.side v)) W)
        (translateBases v b) (TorusFields.translate (siteOfInt v) V) =
      stepTransitionDensity R.params R.coupling W b V := by
  classical
  obtain ⟨h1, h2, h3⟩ := hK R.params hfit R.coupling n hn v W V b
  unfold stepTransitionDensity
  by_cases hb : b ∈ baseChoices R.params (fineLevelField R.params n W)
  · have e3 := h3 hb
    rw [if_pos (h1.mpr hb), if_pos hb, h2, e3]
  · rw [if_neg (fun h => hb (h1.mp h)), if_neg hb]
end Density
end TranslationDensity
open TranslationDensity in
theorem translationPreservesOutcomeDensity (hK : TranslationPreservesBaseKernel) (hF : FrameCovariance) :
    translationPreservesOutcomeDensityStatement := by
  intro R hfits hFit hr n _ hB w W e
  classical
  obtain ⟨δ, lam, σA, cg, N, hC, h2, -⟩ := hFit
  obtain ⟨b, V, bad₀⟩ := e
  have hLpos : 1 ≤ R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hLpos) hB.2
  have hn2 : 2 ≤ n := by
    have := hfits.n₀_ge
    omega
  have hhull : hotCoreSites R (TorusFields.translate (siteOfInt (scaleCoords R.params.side w)) V) =
      translateSet (siteOfInt (scaleCoords R.params.side w)) (hotCoreSites R V) := by
    unfold hotCoreSites
    rw [torusHotSites_translate hfits hB.1, thickening_translateSet]
  have hfr : ∀ c ∈ markedBonds R (hotCoreSites R V),
      StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach
          (TorusFields.translate (siteOfInt (scaleCoords R.params.side w)) V)
        (c.1 - siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w)), c.2) =
        StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach V c := by
    intro c hc
    obtain ⟨hc1, hc2⟩ := Finset.mem_filter.mp hc
    exact (hF R.params δ lam R.anchorRadius σA cg N hfits hC h2 R.depth R.range R.nextRange n V _ _ _ hr
      (Or.inl ⟨hB, rfl, rfl, rfl⟩) c hc1 hc2).2 _
  have hd := stepTransitionDensity_translate hfits hK hn (scaleCoords R.params.side w) W V b
  have hmark : ∀ bad : Finset (TorusBond (n * R.params.side)),
      markLaw R (TorusFields.translate (siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w))) W)
          (TorusFields.translate (siteOfInt (scaleCoords R.params.side w)) V)
        (pullBonds (siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w))) bad) =
        markLaw R W V bad := by
    intro bad
    unfold markLaw
    by_cases hg : R.params.side ∣ n ∧ 64 ≤ n
    · rw [if_pos hg, if_pos hg, hhull, markedBonds_translateSet hfits.L_odd hn2]
      by_cases hs : bad ⊆ markedBonds R (hotCoreSites R V)
      · have hs' : pullBonds (siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w))) bad ⊆
            pullBonds (siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w)))
              (markedBonds R (hotCoreSites R V)) := fun c hc =>
          mem_pullBonds.mpr (hs (mem_pullBonds.mp hc))
        rw [if_pos hs, if_pos hs', markProduct_translate hfits.L_odd hn2 _ _ _ _ _ hfr]
      · have hs' : ¬ pullBonds (siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w))) bad ⊆
            pullBonds (siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w)))
              (markedBonds R (hotCoreSites R V)) := fun h =>
          hs fun c hc => by
            have h1 : (c.1 - siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w)), c.2) ∈
                pullBonds (siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w))) bad :=
              mem_pullBonds.mpr (by simpa using hc)
            simpa using mem_pullBonds.mp (h h1)
        rw [if_neg hs, if_neg hs']
    · rw [if_neg hg, if_neg hg]
      have : pullBonds (siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w))) bad = ∅ ↔
          bad = ∅ := by
        constructor
        · intro h
          refine Finset.eq_empty_of_forall_notMem fun c hc => ?_
          have h1 : (c.1 - siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w)), c.2) ∈
              pullBonds (siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w))) bad :=
            mem_pullBonds.mpr (by simpa using hc)
          rw [h] at h1
          exact absurd h1 (Finset.notMem_empty _)
        · rintro rfl
          exact Finset.eq_empty_of_forall_notMem fun c hc => Finset.notMem_empty _ (mem_pullBonds.mp hc)
      simp only [this]
  show stepTransitionDensity R.params R.coupling
        (TorusFields.translate (siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w))) W)
        (translateBases (scaleCoords R.params.side w) b)
        (TorusFields.translate (siteOfInt (scaleCoords R.params.side w)) V) *
      markLaw R (TorusFields.translate (siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w))) W)
        (TorusFields.translate (siteOfInt (scaleCoords R.params.side w)) V)
        (translateBonds (siteOfInt (scaleCoords R.params.side (scaleCoords R.params.side w))) bad₀) =
    stepTransitionDensity R.params R.coupling W b V * markLaw R W V bad₀
  exact congrArg₂ (· * ·) hd ((congrArg (markLaw R _ _) (translateBonds_eq_pullBonds _ _)).trans (hmark _))
end YangMills.Construction.CellWindows
end
