import YangMills.Construction.ClusterExpansionOfAStep.AttachedClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.CaseOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.ContoursFromBases
import YangMills.Construction.ClusterExpansionOfAStep.FrameAgainstTheLeastFieldOfTheCut
import YangMills.Construction.ClusterExpansionOfAStep.FramesUnderGaugesAndTranslations
import YangMills.Construction.ClusterExpansionOfAStep.GaugeCarriesTheKernel
import YangMills.Construction.ClusterExpansionOfAStep.HaarOfFieldsIsKept
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTheGauge
import YangMills.Construction.ClusterExpansionOfAStep.LabelDataOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.LeastLogOfTheGroup
import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames GaugeFixing TorusContours TorusFields TorusLumps
  StepSettings StepCosts StepFrames StepMarks QuaternionLog BlockPlaces TopLevelSites FieldHaar
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem fieldWithStoredLinks_gaugeTransform (q : CoarseState R n) (g : TorusSite n → UnitQuaternion)
    (W : TorusField (n * R.params.side)) :
    (q.gaugeTransform g).fieldWithStoredLinks
        (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) =
      TorusFields.gaugeTransform (blockConstantGauge R.params.side g) (q.fieldWithStoredLinks W) := by
  classical
  funext x i
  have hst := markAt_gaugeTransform q g (parentBlock R.params.side x)
  have e : (blockSite (parentBlock R.params.side x) (siteOffset x) : TorusSite (n * R.params.side)) = x :=
    blockSite_parentBlock_siteOffset x
  rcases h : q.markAt (parentBlock R.params.side x) with ⟨⟩ | s
  · simp only [CoarseState.fieldWithStoredLinks, hst, h, Option.map_none, TorusFields.gaugeTransform]
  · simp only [CoarseState.fieldWithStoredLinks, hst, h, Option.map_some, gaugeOnCoarseState,
      TorusFields.gaugeTransform, e]
    rcases hf : s.linkValue (siteOffset x, i) with ⟨⟩ | w
    · simp
    · simp
theorem coarseStateOf_gaugeTransform (hL : R.params.side ≤ 6 * R.range) (C : Finset (TorusSite n))
    (g : TorusSite n → UnitQuaternion) (F : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (L : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    coarseStateOf R C (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) F) Yt
        (R.labels.act Yt (blockConstantGauge R.params.side g) L) bad b =
      (coarseStateOf R C F Yt L bad b).gaugeTransform g := by
  classical
  refine coarseState_ext _ _ rfl fun y => ?_
  rw [markAt_gaugeTransform, markAt_coarseStateOf, markAt_coarseStateOf]
  by_cases hy : y ∈ storedBlocks R.params.side R.range bad Yt C
  · rw [if_pos hy, if_pos hy]
    simp only [Option.map_some, Option.some.injEq]
    set q := coarseStateOf R C F Yt L bad b with hq
    refine blockConfig_ext rfl rfl ?_ rfl ?_
    · funext o
      simp only [blockConfigAt, gaugeOnCoarseState]
      have hb : parentBlock R.params.side (blockSite y o : TorusSite (n * R.params.side)) ∈
          storedBlocks R.params.side R.range bad Yt C := by
        rw [parentBlock_blockSite]
        exact hy
      have hmem : ∀ {u}, u ∈ q.labelSet ↔
          u ∈ Yt ∧ parentBlock R.params.side u ∈ storedBlocks R.params.side R.range bad Yt C :=
        mem_labelSet_coarseStateOf C F Yt L bad b
      by_cases hz : blockSite y o ∈ Yt
      · have hzq : blockSite y o ∈ q.labelSet := hmem.mpr ⟨hz, hb⟩
        rw [dif_pos hz, dif_pos hzq]
        congr 1
        have hθ := mem_attachedSites_of_parentBlock_mem R.range bad Yt C hL
          (Finset.mem_union_left _ (Finset.mem_union_right _ hz)) hb
        refine R.labels.act_local Yt q.labelSet _ _ _ _ _ hz hzq (fun _ _ => rfl) (fun u hu => ?_)
          (fun u h1 h2 hu => ?_)
        · refine ⟨fun h => hmem.mpr ⟨h, parentBlock_mem_storedBlocks_of_near R.range bad Yt C hθ ?_⟩,
            fun h => (hmem.mp h).1⟩
          have hLp : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
          omega
        · exact (labeling_coarseStateOf C F Yt L bad b u h1 h2).symm
      · have hzq : blockSite y o ∉ q.labelSet := fun h => hz (hmem.mp h).1
        rw [dif_neg hz, dif_neg hzq, dif_neg hz]
    · funext c
      simp only [blockConfigAt, gaugeOnCoarseState]
      by_cases h : parentBlock R.params.side
          (blockSite (L := R.params.side) y c.1 + TorusFields.unitStep (n * R.params.side) c.2) ∈
          storedBlocks R.params.side R.range bad Yt C
      · simp only [if_pos h]
        rfl
      · simp only [if_neg h]
  · rw [if_neg hy, if_neg hy]
    rfl
theorem parentBlock_add_unitStep {L : ℕ} [NeZero L] (x : TorusSite (n * L)) (i : Fin 4) :
    parentBlock L (x + TorusFields.unitStep (n * L) i) = parentBlock L x ∨
      parentBlock L (x + TorusFields.unitStep (n * L) i) = parentBlock L x + TorusFields.unitStep n i := by
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set h : ℤ := ((L : ℤ) - 1) / 2
  set a : ℤ := ((x i).cast : ℤ) + h with ha
  have hcast : ∃ k : ℤ, (((x + TorusFields.unitStep (n * L) i) i : ZMod (n * L)).cast : ℤ) + h =
      a + 1 + ((n * L : ℕ) : ℤ) * k := by
    have h1 : (x + TorusFields.unitStep (n * L) i) i = (((((x i).cast : ℤ) + 1) : ℤ) : ZMod (n * L)) := by
      simp [TorusFields.unitStep]
    refine ⟨-(((((x i).cast : ℤ) + 1)) / ((n * L : ℕ) : ℤ)), ?_⟩
    rw [h1, ZMod.coe_intCast, Int.emod_def, ha]
    ring
  obtain ⟨k, hk⟩ := hcast
  have hother : ∀ j, j ≠ i → parentBlock L (x + TorusFields.unitStep (n * L) i) j = parentBlock L x j := by
    intro j hj
    simp [parentBlock, TorusFields.unitStep, hj]
  have hdiv : (((x + TorusFields.unitStep (n * L) i) i : ZMod (n * L)).cast + h) / (L : ℤ) =
      (a + 1) / (L : ℤ) + (n : ℤ) * k := by
    rw [hk]
    push_cast
    rw [show a + 1 + (n : ℤ) * (L : ℤ) * k = (a + 1) + (L : ℤ) * ((n : ℤ) * k) by ring,
      Int.add_mul_ediv_left _ _ hL.ne']
  have hi : parentBlock L (x + TorusFields.unitStep (n * L) i) i = (((a + 1) / (L : ℤ) : ℤ) : ZMod n) := by
    simp only [parentBlock]
    rw [hdiv]
    push_cast
    simp
  have hbi : parentBlock L x i = ((a / (L : ℤ) : ℤ) : ZMod n) := rfl
  have hcase : (a + 1) / (L : ℤ) = a / (L : ℤ) ∨ (a + 1) / (L : ℤ) = a / (L : ℤ) + 1 := by
    have h1 := Int.mul_ediv_add_emod a L
    have h2 := Int.emod_nonneg a hL.ne'
    have h3 := Int.emod_lt_of_pos a hL
    by_cases hlt : a % (L : ℤ) + 1 < L
    · left
      have : a + 1 = (a % (L : ℤ) + 1) + (L : ℤ) * (a / (L : ℤ)) := by linarith
      rw [this, Int.add_mul_ediv_left _ _ hL.ne', Int.ediv_eq_zero_of_lt (by omega) hlt, zero_add]
    · right
      have : a + 1 = (L : ℤ) * (a / (L : ℤ) + 1) := by
        rw [mul_add, mul_one]
        linarith
      rw [this, Int.mul_ediv_cancel_left _ hL.ne']
  rcases hcase with hc | hc
  · left
    funext j
    by_cases hj : j = i
    · subst hj
      rw [hi, hbi, hc]
    · exact hother j hj
  · right
    funext j
    by_cases hj : j = i
    · subst hj
      rw [hi, Pi.add_apply, hbi, hc]
      simp [TorusFields.unitStep]
    · rw [hother j hj]
      simp [TorusFields.unitStep, hj]
theorem axialGauge_gaugeTransform (hodd : Odd R.params.side)
    (Wf : (stepBlockFrame R.params.side n).GaugeField (stepBlockFrame R.params.side n).depth)
    (γ : (stepBlockFrame R.params.side n).Site (stepBlockFrame R.params.side n).depth → UnitQuaternion)
    (hγ : ∀ x, γ (cellCentre (stepBlockFrame R.params.side n).depth (enclosingCell x)) = γ x)
    (x : (stepBlockFrame R.params.side n).Site (stepBlockFrame R.params.side n).depth) :
    axialGauge 1 (BlockAverages.gaugeTransform γ Wf) x = γ x * axialGauge 1 Wf x * (γ x)⁻¹ := by
  have hs : ∀ i, 0 < (stepBlockFrame R.params.side n).extent i := fun _ => Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨ho, hxe⟩ := cellOffset_mem_and_eq hs hodd x
  unfold axialGauge
  rw [GaugeFixing.pathHolonomy_gaugeTransform, pathDisplacement_axisPath, hxe, hγ]
theorem readAtLevel_zero_gaugeTransform (G : TorusSite (n * R.params.side) → UnitQuaternion)
    (W : TorusField (n * R.params.side)) :
    readAtLevel (stepBlockFrame R.params.side n) 0 (TorusFields.gaugeTransform G W) =
      BlockAverages.gaugeTransform (fun x => G (toTorusSite (n * R.params.side) x))
        (readAtLevel (stepBlockFrame R.params.side n) 0 W) := by
  funext x i
  have h := toTorusSite_add (F := stepBlockFrame R.params.side n) (j := 0) (m := n * R.params.side)
    (fun i => stepBlockFrame_period_zero i) x (BlockAverages.unitStep 0 i)
  rw [toTorusSite_unitStep (F := stepBlockFrame R.params.side n) (j := 0) (m := n * R.params.side)
    (fun i => stepBlockFrame_period_zero i)] at h
  show G (toTorusSite _ x) * W (toTorusSite _ x) i * (G (toTorusSite _ x + TorusFields.unitStep _ i))⁻¹ =
    G (toTorusSite _ x) * W (toTorusSite _ x) i * (G (toTorusSite _ (x + BlockAverages.unitStep 0 i)))⁻¹
  rw [h]
theorem parentBlock_toTorusSite (hodd : Odd R.params.side)
    (x : (stepBlockFrame R.params.side n).Site (stepBlockFrame R.params.side n).depth) :
    parentBlock R.params.side (toTorusSite (n * R.params.side) x) = toTorusSite n (enclosingCell x) := by
  have hs : ∀ i, 0 < (stepBlockFrame R.params.side n).extent i := fun _ => Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨ho, hxe⟩ := cellOffset_mem_and_eq hs hodd x
  have h := parentBlock_siteAtOffset (L := R.params.side) (enclosingCell x) ho
  rw [siteAtOffset, hxe] at h
  exact h
theorem parentBlock_toTorusSite_cellCentre (hodd : Odd R.params.side) (y : (stepBlockFrame R.params.side n).Cell) :
    parentBlock R.params.side
        (toTorusSite (n * R.params.side) (cellCentre (stepBlockFrame R.params.side n).depth y)) =
      toTorusSite n y := by
  have h0 : (0 : Fin 4 → ℤ) ∈ centredCube R.params.side := _root_.YangMills.Construction.TorusContours.mem_centredCube_iff.mpr fun m => by
    obtain ⟨H, hH⟩ := hodd
    have : ((R.params.side : ℤ) - 1) / 2 = (H : ℤ) := by
      rw [hH]
      push_cast
      omega
    rw [this]
    simp
  have h := parentBlock_siteAtOffset (L := R.params.side) y h0
  rw [siteAtOffset, BlockAverages.siteOfCoords_zero, add_zero] at h
  exact h
theorem norm_frameCoord_le {ℓ : StepParameters} {ρA ρ : ℝ} {t m : ℕ} {V : TorusField n}
    {b : TorusBond (n * ℓ.side)} (hρ : 0 ≤ ρ)
    (h : FrameIsMinimizing ℓ ρA ρ t m V b) : ‖(frameCoord ℓ ρA t m V b : ℍ[ℝ])‖ ≤ ρ := by
  classical
  have key : ∀ {F : BlockFrame} (S : Finset F.Cell) (V' : F.GaugeField F.top)
      (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (c : F.Site F.depth × Fin 4),
      IsMinimizingChart ℓ.coupling S V' ρ w → ‖((w c.1 c.2 : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ρ := by
    intro F S V' w c hw
    by_cases hc : c ∈ chordBonds S
    · exact hw.2.1 c hc
    · rw [hw.1 c hc]
      simpa using hρ
  by_cases hm : 4 * m + 5 < n
  · obtain ⟨w, hw, he⟩ := h.1 hm
    rw [he]
    exact key _ _ w _ hw
  · obtain ⟨w, hw, he⟩ := h.2 hm
    rw [he]
    exact key _ _ w (_, _) hw
theorem cutoffFactor_minimalLog_conj {ρ : ℝ} {p : ℝ → ℝ} (hρ : ρ ≤ 1) (u Γ : UnitQuaternion)
    (f f' : imaginaryQuaternions)
    (hf : (f' : ℍ[ℝ]) = (u : ℍ[ℝ]) * (f : ℍ[ℝ]) * ((u⁻¹ : UnitQuaternion) : ℍ[ℝ])) (hs : ‖(f : ℍ[ℝ])‖ ≤ 1) :
    cutoffFactor ρ p ‖((minimalLog (u * Γ * u⁻¹) : imaginaryQuaternions) : ℍ[ℝ]) - (f' : ℍ[ℝ])‖ =
      cutoffFactor ρ p ‖((minimalLog Γ : imaginaryQuaternions) : ℍ[ℝ]) - (f : ℍ[ℝ])‖ := by
  by_cases hΓ : Γ = -1
  · have hc : u * Γ * u⁻¹ = -1 := by
      rw [hΓ]
      simp
    have hs' : ‖(f' : ℍ[ℝ])‖ ≤ 1 := by
      rw [hf, norm_conj_unit]
      exact hs
    have hbig : ∀ a : ℍ[ℝ], ‖a‖ ≤ 1 →
        ρ ≤ ‖((minimalLog (-1 : UnitQuaternion) : imaginaryQuaternions) : ℍ[ℝ]) - a‖ := by
      intro a ha
      have h1 := norm_sub_norm_le ((minimalLog (-1 : UnitQuaternion) : imaginaryQuaternions) : ℍ[ℝ]) a
      rw [norm_minimalLog_neg_one] at h1
      have h2 := Real.pi_gt_three
      linarith
    have hzero : ∀ a : ℍ[ℝ], ‖a‖ ≤ 1 →
        cutoffFactor ρ p ‖((minimalLog (-1 : UnitQuaternion) : imaginaryQuaternions) : ℍ[ℝ]) - a‖ = 0 := by
      intro a ha
      unfold cutoffFactor
      rw [if_neg (not_lt.mpr (hbig a ha))]
    rw [hc, hΓ, hzero _ hs', hzero _ hs]
  · rw [coe_minimalLog_conj u Γ hΓ, hf, ← sub_mul, ← mul_sub, norm_conj_unit]
theorem bondMark_gaugeTransform (hR : R.IsWellPosed) (hF : R.ColdChainFits) (hfr : FrameCovariance)
    (hsz : FrameNearMinimizer) (hside : IsBlockTorusSide R.params n) (V : TorusField n)
    (g : TorusSite n → UnitQuaternion) (W : TorusField (n * R.params.side)) (c : TorusBond (n * R.params.side))
    (hc : c ∈ chartBonds R.params.side n) (hC : parentBlock R.params.side c.1 ∉ hotCoreSites R V) :
    bondMark R (TorusFields.gaugeTransform g V)
        (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) c = bondMark R V W c := by
  classical
  have hfit := hR.admissible
  obtain ⟨δ, lam, σA, cg, N, hch, hσ, hσ1⟩ := hF
  have hrf : RangesAdmissible R.range R.nextRange := ⟨hR.range_le, hR.nextRange_ge, by
    have := hR.range_ge_side
    have := hfit.L_ge
    omega⟩
  have hsit : IsStepSituation R.params R.nextRange V
      (Finset.univ \ thickening lumpRange (torusHotSites R.params V)) (hotCoreSites R V) R.params.threshold :=
    Or.inl ⟨hside, rfl, rfl, rfl⟩
  have hfr1 := (hfr R.params δ lam R.anchorRadius σA cg N hfit hch hσ R.depth R.range R.nextRange n V _ _ _
    hrf hsit c hc hC).1 g
  have hsz1 := (hsz R.params δ lam R.anchorRadius σA cg N hfit hch hσ).2 R.depth R.range R.nextRange n V _ _ _
    hrf hsit c hc hC
  have hρA : 0 < R.anchorRadius ∧ R.anchorRadius ≤ 1 := ⟨hch.2.2.2.1, hch.2.2.2.2.1⟩
  have hN0 : 0 < N 0 := hch.2.2.2.2.2.2.2.1 0
  have hsmall : ‖((frameCoord R.params R.anchorRadius R.depth R.frameReach V c : imaginaryQuaternions) :
      ℍ[ℝ])‖ ≤ 1 :=
    (norm_frameCoord_le (le_min hρA.1.le (mul_pos hN0 hfit.σ_pos).le) hsz1.1).trans
      ((min_le_left _ _).trans hρA.2)
  set h : UnitQuaternion := g (parentBlock R.params.side c.1) with hh
  have hodd := hfit.L_odd
  set F₀ := stepBlockFrame R.params.side n with hF₀
  set x : F₀.Site F₀.depth := torusSiteInFrame F₀ 0 c.1 with hx
  have hx1 : toTorusSite (n * R.params.side) x = c.1 :=
    toTorusSite_torusSiteInFrame (fun i => stepBlockFrame_period_zero i) c.1
  have hx2 : toTorusSite (n * R.params.side) (x + BlockAverages.unitStep F₀.depth c.2) =
      c.1 + TorusFields.unitStep (n * R.params.side) c.2 := by
    have h1 := toTorusSite_add (F := stepBlockFrame R.params.side n) (j := 0) (m := n * R.params.side)
      (fun i => stepBlockFrame_period_zero i) x (BlockAverages.unitStep 0 c.2)
    rw [toTorusSite_unitStep (F := stepBlockFrame R.params.side n) (j := 0) (m := n * R.params.side)
      (fun i => stepBlockFrame_period_zero i)] at h1
    exact h1.trans (congrArg (· + TorusFields.unitStep (n * R.params.side) c.2) hx1)
  set T := axialGauge 1 (readAtLevel F₀ 0 W) with hT
  set w : UnitQuaternion := BlockAverages.gaugeTransform T (readAtLevel F₀ 0 W) x c.2 with hw
  set γ : F₀.Site F₀.depth → UnitQuaternion :=
    fun x' => blockConstantGauge R.params.side g (toTorusSite (n * R.params.side) x') with hγ
  have hcentre : ∀ x', γ (cellCentre F₀.depth (enclosingCell x')) = γ x' := by
    intro x'
    show g (parentBlock R.params.side _) = g (parentBlock R.params.side _)
    rw [parentBlock_toTorusSite_cellCentre hodd, parentBlock_toTorusSite hodd]
  have hfine := readAtLevel_zero_gaugeTransform (R := R) (blockConstantGauge R.params.side g) W
  have htree : ∀ x', axialGauge 1
      (readAtLevel F₀ 0 (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W)) x' =
        γ x' * T x' * (γ x')⁻¹ := by
    intro x'
    rw [hfine]
    exact axialGauge_gaugeTransform hodd _ γ hcentre x'
  have hγx : γ x = h := by
    show g (parentBlock R.params.side _) = _
    rw [hx1]
  set h₂ : UnitQuaternion :=
    g (parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2)) with hh₂
  have hγx₂ : γ (x + BlockAverages.unitStep F₀.depth c.2) = h₂ := by
    show g (parentBlock R.params.side _) = _
    rw [hx2]
  have hw' : BlockAverages.gaugeTransform
      (axialGauge 1 (readAtLevel F₀ 0 (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W)))
      (readAtLevel F₀ 0 (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W)) x c.2 =
        h * w * h₂⁻¹ := by
    have e1 : readAtLevel F₀ 0 (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) x c.2 =
        γ x * readAtLevel F₀ 0 W x c.2 * (γ (x + BlockAverages.unitStep F₀.depth c.2))⁻¹ := by
      rw [hfine]
      rfl
    show axialGauge 1 (readAtLevel F₀ 0 (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W)) x *
      readAtLevel F₀ 0 (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W) x c.2 *
      (axialGauge 1 (readAtLevel F₀ 0 (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) W))
        (x + BlockAverages.unitStep F₀.depth c.2))⁻¹ = _
    rw [htree, htree, e1, hγx, hγx₂]
    show _ = h * (T x * readAtLevel F₀ 0 W x c.2 * (T (x + BlockAverages.unitStep F₀.depth c.2))⁻¹) * h₂⁻¹
    group
  have hρ1 : R.ballRadius ≤ 1 := by
    unfold StepSetup.ballRadius
    linarith
  have hfr2 : ((frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.gaugeTransform g V) c :
      imaginaryQuaternions) : ℍ[ℝ]) =
      (h : ℍ[ℝ]) * ((frameCoord R.params R.anchorRadius R.depth R.frameReach V c : imaginaryQuaternions) :
        ℍ[ℝ]) * ((h⁻¹ : UnitQuaternion) : ℍ[ℝ]) := hfr1
  have hy0 : toTorusSite n (enclosingCell x) = parentBlock R.params.side c.1 := by
    rw [← parentBlock_toTorusSite hodd, hx1]
  have hy2 : toTorusSite n (enclosingCell (x + BlockAverages.unitStep F₀.depth c.2)) =
      parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2) := by
    rw [← parentBlock_toTorusSite hodd, hx2]
  by_cases hcr : IsCrossingBond (x, c.2)
  · have mk : ∀ (V₁ : TorusField n) (W₁ : TorusField (n * R.params.side)), bondMark R V₁ W₁ c =
        cutoffFactor R.ballRadius R.barrierFn
        ‖((minimalLog (BlockAverages.gaugeTransform (axialGauge 1 (readAtLevel F₀ 0 W₁))
            (readAtLevel F₀ 0 W₁) x c.2 *
          (readAtLevel F₀ 1 V₁ (enclosingCell x) c.2)⁻¹) : imaginaryQuaternions) : ℍ[ℝ]) -
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach V₁ c : imaginaryQuaternions) : ℍ[ℝ])‖ := by
      intro V₁ W₁
      unfold bondMark chartCoord bondCoordinate
      rw [if_pos hcr]
    have hstep : parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2) =
        parentBlock R.params.side c.1 + TorusFields.unitStep n c.2 := by
      refine (parentBlock_add_unitStep c.1 c.2).resolve_left fun he => hcr ?_
      refine toTorusSite_injective (N := n) (fun i => stepBlockFrame_period_one i) ?_
      exact hy2.trans (he.trans hy0.symm)
    have hV : readAtLevel F₀ 1 (TorusFields.gaugeTransform g V) (enclosingCell x) c.2 =
        h * readAtLevel F₀ 1 V (enclosingCell x) c.2 * h₂⁻¹ := by
      show TorusFields.gaugeTransform g V (toTorusSite n (enclosingCell x)) c.2 =
        g (parentBlock R.params.side c.1) * V (toTorusSite n (enclosingCell x)) c.2 *
        (g (parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2)))⁻¹
      rw [hy0, hstep]
      rfl
    rw [mk, mk, hw', hV]
    have hg : h * w * h₂⁻¹ * (h * readAtLevel F₀ 1 V (enclosingCell x) c.2 * h₂⁻¹)⁻¹ =
        h * (w * (readAtLevel F₀ 1 V (enclosingCell x) c.2)⁻¹) * h⁻¹ := by
      group
    rw [hg]
    exact cutoffFactor_minimalLog_conj hρ1 h _ _ _ hfr2 hsmall
  · have mk : ∀ (V₁ : TorusField n) (W₁ : TorusField (n * R.params.side)), bondMark R V₁ W₁ c =
        cutoffFactor R.ballRadius R.barrierFn
        ‖((minimalLog (BlockAverages.gaugeTransform (axialGauge 1 (readAtLevel F₀ 0 W₁))
            (readAtLevel F₀ 0 W₁) x c.2) : imaginaryQuaternions) : ℍ[ℝ]) -
          ((frameCoord R.params R.anchorRadius R.depth R.frameReach V₁ c : imaginaryQuaternions) : ℍ[ℝ])‖ := by
      intro V₁ W₁
      unfold bondMark chartCoord bondCoordinate
      rw [if_neg hcr]
    have hsame : enclosingCell (x + BlockAverages.unitStep F₀.depth c.2) = enclosingCell x := not_not.mp hcr
    have hh₂e : h₂ = h := by
      show g _ = g _
      rw [← hy2, ← hy0, hsame]
    rw [mk, mk, hw', hh₂e]
    exact cutoffFactor_minimalLog_conj hρ1 h _ _ _ hfr2 hsmall
theorem fillLabels_gaugeTransform (q : CoarseState R n) (g : TorusSite n → UnitQuaternion)
    (Yt : Finset (TorusSite (n * R.params.side)))
    (hAY : q.labelSet ⊆ Yt) (hsep : ∀ z ∈ q.labelSet, ∀ u ∈ Yt, _root_.YangMills.Construction.TorusFields.supDist u z ≤ 1 → u ∈ q.labelSet)
    (ν : q.unlabelled Yt → R.labels.Ω) (ν' : (q.gaugeTransform g).unlabelled Yt → R.labels.Ω)
    (hν : ∀ z hz hz', ν' ⟨z, hz⟩ = R.labels.act (q.unlabelled Yt) (blockConstantGauge R.params.side g) ν ⟨z, hz'⟩) :
    (q.gaugeTransform g).fillLabels Yt ν' =
      R.labels.act Yt (blockConstantGauge R.params.side g) (q.fillLabels Yt ν) := by
  classical
  have hrest : (q.gaugeTransform g).unlabelled Yt = q.unlabelled Yt := by
    rw [unlabelled_eq_sdiff, unlabelled_eq_sdiff, labelSet_gaugeTransform]
  funext ⟨z, hz⟩
  by_cases hL : z ∈ q.labelSet
  · have hL' : z ∈ (q.gaugeTransform g).labelSet := by rw [labelSet_gaugeTransform]; exact hL
    rw [fillLabels_of_mem _ Yt ν' z hz hL', labeling_gaugeTransform q g z hL hL']
    refine R.labels.act_local q.labelSet Yt _ _ _ _ _ hL hz (fun _ _ => rfl) (fun u hu => ?_)
      (fun u h1 h2 hu => ?_)
    · exact ⟨fun h => hAY h, fun h => hsep z hL u h hu⟩
    · exact (fillLabels_of_mem q Yt ν u h2 h1).symm
  · have hr : z ∈ q.unlabelled Yt := by
      rw [unlabelled_eq_sdiff]
      exact Finset.mem_sdiff.mpr ⟨hz, hL⟩
    have hr' : z ∈ (q.gaugeTransform g).unlabelled Yt := hrest ▸ hr
    rw [fillLabels_of_mem_unlabelled _ Yt ν' z hz hr', hν z hr' hr]
    refine R.labels.act_local (q.unlabelled Yt) Yt _ _ _ _ _ hr hz (fun _ _ => rfl) (fun u hu => ?_)
      (fun u h1 h2 hu => ?_)
    · rw [unlabelled_eq_sdiff]
      refine ⟨fun h => (Finset.mem_sdiff.mp h).1, fun h => Finset.mem_sdiff.mpr ⟨h, fun hu' => hL ?_⟩⟩
      exact hsep u hu' z hz (by rw [_root_.YangMills.Construction.TorusFields.supDist_comm]; exact hu)
    · exact (fillLabels_of_mem_unlabelled q Yt ν u h2 h1).symm
theorem torusHotLumps_gaugeTransform (hfit : R.params.Admissible) {m : ℕ} [NeZero m] (hLn : R.params.side ∣ m)
    (G : TorusSite m → UnitQuaternion) (W : TorusField m) :
    torusHotLumps R.params (TorusFields.gaugeTransform G W) = torusHotLumps R.params W := by
  ext l
  simp only [mem_torusHotLumps_iff R.params hfit hLn, curvature_gaugeTransform]
theorem isHullState_gaugeTransform_iff (hfit : R.params.Admissible) {m : ℕ} [NeZero m] (hLn : R.params.side ∣ m)
    (G : TorusSite m → UnitQuaternion) (W : TorusField m) (r : ℕ) (Y : Finset (TorusSite m)) :
    IsHullState R.params r (TorusFields.gaugeTransform G W) Y ↔ IsHullState R.params r W Y := by
  have h := torusHotLumps_gaugeTransform (R := R) hfit hLn G W
  unfold IsHullState torusHotSites
  rw [h]
theorem gaugeTransform_injective (h : CoarseLabelFacts R) {x y : CoarseState R n} (g : TorusSite n → UnitQuaternion)
    (e : x.gaugeTransform g = y.gaugeTransform g) : x = y := by
  obtain ⟨Y, ω⟩ := x
  obtain ⟨Y', ω'⟩ := y
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj e
  have h3 := eq_of_heq h2
  have hinv : ∀ ρ : Y → CoarseLabel R.labels.Ω R.params.side,
      coarseGaugeAct (R := R) Y g⁻¹ (coarseGaugeAct (R := R) Y g ρ) = ρ := by
    intro ρ
    rw [← h.act_mul]
    have : g⁻¹ * g = fun _ => 1 := by
      funext z
      simp
    rw [this, h.act_one]
  have h4 := congrArg (coarseGaugeAct (R := R) Y g⁻¹) h3
  rw [hinv, hinv] at h4
  exact congrArg (Sigma.mk Y) h4
def FitsWithin (q : CoarseState R n) (Yt : Finset (TorusSite (n * R.params.side))) : Prop :=
  q.labelSet ⊆ Yt ∧ ∀ z ∈ q.labelSet, ∀ u ∈ Yt, _root_.YangMills.Construction.TorusFields.supDist u z ≤ 1 → u ∈ q.labelSet
theorem fitsWithin_coarseStateOf (hL : R.params.side ≤ 6 * R.range) (C : Finset (TorusSite n))
    (F : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (L : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n) :
    FitsWithin (coarseStateOf R C F Yt L bad b) Yt := by
  classical
  have hmem : ∀ {u}, u ∈ (coarseStateOf R C F Yt L bad b).labelSet ↔
      u ∈ Yt ∧ parentBlock R.params.side u ∈ storedBlocks R.params.side R.range bad Yt C :=
    mem_labelSet_coarseStateOf C F Yt L bad b
  refine ⟨fun z hz => (hmem.mp hz).1, fun z hz u hu hd => ?_⟩
  obtain ⟨h1, h2⟩ := hmem.mp hz
  have hθ := mem_attachedSites_of_parentBlock_mem R.range bad Yt C hL
    (Finset.mem_union_left _ (Finset.mem_union_right _ h1)) h2
  have hLp : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  exact hmem.mpr ⟨hu, parentBlock_mem_storedBlocks_of_near R.range bad Yt C hθ (by omega)⟩
theorem configurationMass_eq_zero_of_not_fitsWithin (hL : R.params.side ≤ 6 * R.range) (C : Finset (TorusSite n))
    (V : TorusField n) (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side)))
    (b : BaseChoice R.params.side n) (q : CoarseState R n) (hq : ¬ FitsWithin q Yt) :
    configurationMass R C V bad Yt b q = 0 := by
  classical
  have hno : ∀ W ν, ¬ (IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q) := by
    intro W ν h
    apply hq
    have := fitsWithin_coarseStateOf hL C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b
    rwa [h.2] at this
  have h0 : ∀ W, (∫⁻ ν : q.unlabelled Yt → R.labels.Ω,
      (if IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt ∧
          coarseStateOf R C (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q then
        ENNReal.ofReal (stepWeight R C V (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b) else 0)
      ∂(Measure.pi fun _ => R.labels.μ)) = 0 := by
    intro W
    rw [lintegral_congr fun ν => if_neg (hno W ν)]
    simp
  unfold configurationMass
  rw [lintegral_congr h0]
  simp
theorem fitsWithin_gaugeTransform_iff (q : CoarseState R n) (g : TorusSite n → UnitQuaternion)
    (Yt : Finset (TorusSite (n * R.params.side))) :
    FitsWithin (q.gaugeTransform g) Yt ↔ FitsWithin q Yt := by
  unfold FitsWithin
  rw [labelSet_gaugeTransform]
theorem lintegral_labelAct (Λ : LabelSpace) {m : ℕ} [NeZero m] (G : TorusSite m → UnitQuaternion)
    {S S' : Finset (TorusSite m)} (h : S' = S)
    (f' : (S' → Λ.Ω) → ENNReal) (f : (S → Λ.Ω) → ENNReal)
    (hf : ∀ ν ν', (∀ z hz hz', ν' ⟨z, hz⟩ = Λ.act S G ν ⟨z, hz'⟩) → f' ν' = f ν) :
    ∫⁻ ν', f' ν' ∂(Measure.pi fun _ : S' => Λ.μ) = ∫⁻ ν, f ν ∂(Measure.pi fun _ : S => Λ.μ) := by
  subst h
  have hmp := Λ.act_keeps S' G
  have hmeas : ∀ G' : TorusSite m → UnitQuaternion, Measurable (Λ.act S' G') := fun G' =>
    (Λ.act_borel S').comp (measurable_const.prodMk measurable_id)
  have hinv : ∀ (G' : TorusSite m → UnitQuaternion) ν, Λ.act S' G'⁻¹ (Λ.act S' G' ν) = ν := by
    intro G' ν
    rw [← Λ.act_mul]
    have : G'⁻¹ * G' = fun _ => 1 := by
      funext z
      simp
    rw [this, Λ.act_one]
  let e : (S' → Λ.Ω) ≃ᵐ (S' → Λ.Ω) :=
    { toFun := Λ.act S' G
      invFun := Λ.act S' G⁻¹
      left_inv := hinv G
      right_inv := fun ν => by
        have := hinv G⁻¹ ν
        rwa [inv_inv] at this
      measurable_toFun := hmeas G
      measurable_invFun := hmeas G⁻¹ }
  rw [← hmp.lintegral_comp_emb e.measurableEmbedding f']
  exact lintegral_congr fun ν => hf ν _ fun _ _ _ => rfl
theorem lintegral_fieldHaar_gaugeTransform {m : ℕ} [NeZero m] (hh : HaarInvariantUnderSymmetries)
    (G : TorusSite m → UnitQuaternion) (f' f : TorusField m → ENNReal)
    (hf : ∀ W, f' (TorusFields.gaugeTransform G W) = f W) :
    ∫⁻ W, f' W ∂(fieldHaar m) = ∫⁻ W, f W ∂(fieldHaar m) := by
  have hmp := (hh m).1 G
  have hinv : ∀ (G' : TorusSite m → UnitQuaternion) (W : TorusField m),
      TorusFields.gaugeTransform G'⁻¹ (TorusFields.gaugeTransform G' W) = W := by
    intro G' W
    funext x i
    simp [TorusFields.gaugeTransform, mul_assoc]
  let e : TorusField m ≃ᵐ TorusField m :=
    { toFun := TorusFields.gaugeTransform G
      invFun := TorusFields.gaugeTransform G⁻¹
      left_inv := hinv G
      right_inv := fun W => by
        have := hinv G⁻¹ W
        rwa [inv_inv] at this
      measurable_toFun := ((hh m).1 G).measurable
      measurable_invFun := ((hh m).1 G⁻¹).measurable }
  rw [← hmp.lintegral_comp_emb e.measurableEmbedding f']
  exact lintegral_congr hf
theorem baseLaw_gaugeTransform (hk : KernelGaugeInvariance) (hfit : R.params.Admissible)
    (g : TorusSite n → UnitQuaternion) (F : TorusField (n * R.params.side)) (b : BaseChoice R.params.side n) :
    baseLaw (R := R) (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) F) b =
      baseLaw (R := R) F b := by
  classical
  have h := (hk R.params hfit n g F (trivialField n)).2.1
  unfold baseLaw
  simp only [h]
theorem stepWeight_gaugeTransform (hR : R.IsWellPosed) (hF : R.ColdChainFits) (hfr : FrameCovariance)
    (hsz : FrameNearMinimizer) (hk : KernelGaugeInvariance)
    (hside : IsBlockTorusSide R.params n) (V : TorusField n) (g : TorusSite n → UnitQuaternion)
    (F : TorusField (n * R.params.side))
    (Yt : Finset (TorusSite (n * R.params.side))) (L : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hh : IsHullState R.params R.range F Yt) :
    stepWeight R (hotCoreSites R V) (TorusFields.gaugeTransform g V)
        (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) F) Yt
        (R.labels.act Yt (blockConstantGauge R.params.side g) L) bad b =
      stepWeight R (hotCoreSites R V) V F Yt L bad b := by
  classical
  have hsideL : IsBlockTorusSide R.params (n * R.params.side) := ⟨Dvd.intro_left n rfl, by
    rw [mul_comm R.params.side R.params.n₀]
    exact Nat.mul_le_mul_right _ (le_trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne _))) hside.2)⟩
  have hD := hR.hasExpansions.2.gauge (n * R.params.side) hsideL F Yt L (blockConstantGauge R.params.side g) hh
  have hB := baseLaw_gaugeTransform (R := R) hk hR.admissible g F b
  have hM : markProduct R (hotCoreSites R V) (TorusFields.gaugeTransform g V)
      (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) F) bad =
      markProduct R (hotCoreSites R V) V F bad := by
    unfold markProduct
    refine Finset.prod_congr rfl fun c hc => ?_
    have hm := Finset.mem_filter.mp hc
    rw [bondMark_gaugeTransform hR hF hfr hsz hside V g F c hm.1 hm.2]
  unfold stepWeight
  rw [hD, hB, hM]
  by_cases hb : b ∈ baseChoices R.params (fineLevelField R.params n F)
  · have hK := ((hk R.params hR.admissible n g F V).2.2 R.coupling).1 b hb
    have : ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4, bondKernel R.params R.coupling
          (readAtLevel (stepBlockFrame R.params.side n) 0
            (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) F))
          (readAtLevel (stepBlockFrame R.params.side n) 1 (TorusFields.gaugeTransform g V)) b c =
        ∏ c : (stepBlockFrame R.params.side n).Cell × Fin 4, bondKernel R.params R.coupling
          (readAtLevel (stepBlockFrame R.params.side n) 0 F)
          (readAtLevel (stepBlockFrame R.params.side n) 1 V) b c :=
      Finset.prod_congr rfl fun c _ => hK c
    rw [this]
  · have h0 : baseLaw (R := R) F b = 0 := by
      unfold baseLaw
      exact if_neg hb
    rw [h0]
    simp
theorem configurationMass_gaugeTransform (hl : CoarseLabelFacts R) (hR : R.IsWellPosed) (hF : R.ColdChainFits)
    (hfr : FrameCovariance) (hsz : FrameNearMinimizer)
    (hk : KernelGaugeInvariance) (hh : HaarInvariantUnderSymmetries) (hside : IsBlockTorusSide R.params n)
    (V : TorusField n) (g : TorusSite n → UnitQuaternion) (bad : Finset (TorusBond (n * R.params.side)))
    (Yt : Finset (TorusSite (n * R.params.side))) (b : BaseChoice R.params.side n) (q : CoarseState R n) :
    configurationMass R (hotCoreSites R V) (TorusFields.gaugeTransform g V) bad Yt b (q.gaugeTransform g) =
      configurationMass R (hotCoreSites R V) V bad Yt b q := by
  classical
  have hL6 : R.params.side ≤ 6 * R.range := by
    have := hR.range_ge_side
    omega
  have hLn' : R.params.side ∣ n * R.params.side := Dvd.intro_left n rfl
  by_cases hfit : FitsWithin q Yt
  · unfold configurationMass
    refine lintegral_fieldHaar_gaugeTransform hh (blockConstantGauge R.params.side g) _ _ fun W => ?_
    have hrest : (q.gaugeTransform g).unlabelled Yt = q.unlabelled Yt := by
      rw [unlabelled_eq_sdiff, unlabelled_eq_sdiff, labelSet_gaugeTransform]
    refine lintegral_labelAct R.labels (blockConstantGauge R.params.side g) hrest _ _ fun ν ν' hν => ?_
    have hf := fieldWithStoredLinks_gaugeTransform q g W
    have hlab := fillLabels_gaugeTransform q g Yt hfit.1 hfit.2 ν ν' hν
    rw [hf, hlab, coarseStateOf_gaugeTransform hL6]
    by_cases hhull : IsHullState R.params R.range (q.fieldWithStoredLinks W) Yt
    · have hh' := (isHullState_gaugeTransform_iff (R := R) hR.admissible hLn' (blockConstantGauge R.params.side g)
        (q.fieldWithStoredLinks W) R.range Yt).mpr hhull
      by_cases hs : coarseStateOf R (hotCoreSites R V) (q.fieldWithStoredLinks W) Yt (q.fillLabels Yt ν) bad b = q
      · rw [if_pos ⟨hh', by rw [hs]⟩, if_pos ⟨hhull, hs⟩,
          stepWeight_gaugeTransform hR hF hfr hsz hk hside V g _ Yt _ bad b hhull]
      · rw [if_neg fun h => hs (gaugeTransform_injective hl g h.2), if_neg fun h => hs h.2]
    · have hh' : ¬ IsHullState R.params R.range
          (TorusFields.gaugeTransform (blockConstantGauge R.params.side g) (q.fieldWithStoredLinks W)) Yt :=
        fun h => hhull ((isHullState_gaugeTransform_iff (R := R) hR.admissible hLn'
          (blockConstantGauge R.params.side g) (q.fieldWithStoredLinks W) R.range Yt).mp h)
      rw [if_neg fun h => hh' h.1, if_neg fun h => hhull h.1]
  · rw [configurationMass_eq_zero_of_not_fitsWithin hL6 _ _ _ _ _ _ hfit,
      configurationMass_eq_zero_of_not_fitsWithin hL6 _ _ _ _ _ _
        (fun h => hfit ((fitsWithin_gaugeTransform_iff q g Yt).mp h))]
theorem coarseWeightExpansion_eq_toReal (V : TorusField n) (Y : Finset (TorusSite n))
    (ω : Y → CoarseLabel R.labels.Ω R.params.side) :
    coarseWeightExpansion R n V Y ω = (coarseStateMass R (hotCoreSites R V) V ⟨Y, ω⟩).toReal :=
  dif_neg (NeZero.ne n)
theorem coarseStateMass_gaugeTransform (hl : CoarseLabelFacts R) (hR : R.IsWellPosed) (hF : R.ColdChainFits)
    (hfr : FrameCovariance) (hsz : FrameNearMinimizer)
    (hk : KernelGaugeInvariance) (hh : HaarInvariantUnderSymmetries) (hside : IsBlockTorusSide R.params n)
    (V : TorusField n) (g : TorusSite n → UnitQuaternion) (q : CoarseState R n) :
    coarseStateMass R (hotCoreSites R V) (TorusFields.gaugeTransform g V) (q.gaugeTransform g) =
      coarseStateMass R (hotCoreSites R V) V q :=
  Finset.sum_congr rfl fun bad _ => Finset.sum_congr rfl fun Yt _ => Finset.sum_congr rfl fun b _ =>
    configurationMass_gaugeTransform hl hR hF hfr hsz hk hh hside V g bad Yt b q
theorem coarseWeightExpansionGaugeInvariant_holds (hlab : CoarseLabelsStandard)
    (hfr : FrameCovariance) (hsz : FrameNearMinimizer)
    (hk : KernelGaugeInvariance) (hh : HaarInvariantUnderSymmetries) :
    CoarseWeightExpansionGaugeInvariant := by
  classical
  intro R hR hF n _ hside V Y ω g hY
  have hfit := hR.admissible
  have hl := hlab R (by have := hfit.L_ge; omega)
  have hC : hotCoreSites R (TorusFields.gaugeTransform g V) = hotCoreSites R V := by
    unfold hotCoreSites torusHotSites
    rw [torusHotLumps_gaugeTransform (R := R) hfit hside.1]
  rw [coarseWeightExpansion_eq_toReal, coarseWeightExpansion_eq_toReal, hC]
  exact congrArg ENNReal.toReal (coarseStateMass_gaugeTransform hl hR hF hfr hsz hk hh hside V g ⟨Y, ω⟩)
end YangMills.Construction.ClusterExpansionOfAStep
end
