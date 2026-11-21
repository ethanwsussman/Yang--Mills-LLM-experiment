import YangMills.Construction.LawByMomentsOfTheFlow.AStateForgetsAFieldTurnedOnABox
import YangMills.Construction.ResponseInTheExpansion.ASettingOffABoxIsTheMirrorProof
import YangMills.Construction.ResponseInTheExpansion.MomentsOfAStepOfTheCurvatureProof
import YangMills.Construction.ResponseInTheExpansion.PartsOfTheGasAreColdMeansProof
import YangMills.Construction.ResponseInTheExpansion.TheCasesOffABoxAreTheMirrorProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
namespace ForgetsRotatedField
section Read
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
open Classical in
private def liftCoords (U : TorusFields.TorusField n) (Z : Finset (TorusFields.TorusBond (n * R.params.side))) (e : ↥Z × Fin 3 → ℝ) :
    StepSettings.FreeCoords (StepSettings.coldChartSetting R U).free := fun b =>
  if h : b.1 ∈ Z then WithLp.toLp 2 (fun c => e (⟨b.1, h⟩, c)) else 0
private theorem exists_index_of_site {L : ℕ} [NeZero L] (hodd : Odd L) (o : TorusFields.TorusSite n) (z : TorusFields.TorusSite (n * L)) {k : ℕ}
    (hz : TorusFields.supDist z (StepSettings.fineSite L o 0 0) + L ≤ L * k) :
    ∃ (h oo : Fin 4 → ℤ), oo ∈ BlockAverages.centredCube L ∧ TorusFields.OffsetInBox k h ∧ StepSettings.fineSite L o h oo = z := by
  have : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have hLpos : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set y : TorusFields.TorusSite (n * L) := StepSettings.fineSite L o 0 0 with hy
  set d : Fin 4 → ℤ := MirrorDensities.offset y z with hd
  obtain ⟨kk, oo, ho, hdec⟩ := BlockOffsets.exists_block_offset hodd d
  refine ⟨kk, oo, ho, fun i => ?_, ?_⟩
  · have h1 : |d i| ≤ (TorusFields.supDist z y : ℤ) := MirrorDensities.abs_offset_le y z i
    have h2 := (BlockTrees.mem_centredCube_iff.mp ho) i
    have h4 : (L : ℤ) * |kk i| ≤ |d i| + |oo i| := by
      have e : (L : ℤ) * kk i = d i - oo i := by rw [hdec i]; ring
      have e2 : (L : ℤ) * |kk i| = |(L : ℤ) * kk i| := by rw [abs_mul, abs_of_pos hLpos]
      rw [e2, e]
      exact abs_sub _ _
    have h5 : 2 * (((L : ℤ) - 1) / 2) ≤ (L : ℤ) - 1 := by omega
    by_contra hc
    push Not at hc
    have h6 : (k : ℤ) + 1 ≤ |kk i| := hc
    have h7 : (L : ℤ) * ((k : ℤ) + 1) ≤ (L : ℤ) * |kk i| := mul_le_mul_of_nonneg_left h6 hLpos.le
    nlinarith
  · have e0 := MirrorDensities.add_siteOfInt_offset y z
    rw [← e0]
    funext i
    have e2 : (L : ℤ) * (((o i).cast : ℤ) + kk i) + oo i = ((L : ℤ) * (((o i).cast : ℤ) + 0) + 0) + d i := by
      rw [hdec i]
      ring
    simp only [StepSettings.fineSite, TorusFields.siteOfInt, hy, Pi.add_apply]
    rw [e2, Int.cast_add]
    rfl
private theorem settingsAgree_cold_of_mirror (hodd : Odd R.params.side) (hn : 2 ≤ n) {m k : ℕ} [NeZero (4 * m)] (h4 : 2 ≤ 4 * m)
    {s : StepSettings.ChartSetting R n} {o : TorusFields.TorusSite n}
    (hag : StepSettings.SettingsAgreeNear s (StepSettings.coldChartSetting R (TorusMirror.mirrorField m o s.coarse)) o 0 k) :
    StepSettings.SettingsAgreeNear s (StepSettings.coldChartSetting R s.coarse) o o k := by
  refine ⟨hag.lt_extent, hag.lt_extent, fun b _ => rfl, ?_, ?_, fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · rintro ⟨h, oo, i⟩ ⟨hh, ho⟩
    exact (hag.free_iff _ ⟨hh, ho⟩).trans (BoxAgreement.fineSite_mem_chartBonds_iff (R := R) hodd h4 hn 0 o h oo ho i)
  · intro q hq hf
    exact hag.fine_eq q hq hf
  · intro h oo hh ho
    refine (hag.support_iff h oo hh ho).trans ?_
    simp [StepSettings.coldChartSetting]
  · intro h oo hz hz' hh ho
    exact absurd hz' (Finset.notMem_empty _)
  · intro h hh
    obtain ⟨oo, ho, e1, e2⟩ := hag.bases_match h hh
    have e3 : StepSettings.fineSite R.params.side (0 : TorusFields.TorusSite (4 * m)) h oo =
        StepSettings.fineSite R.params.side (0 : TorusFields.TorusSite (4 * m)) h 0 :=
      e2.symm.trans (BoxAgreement.toTorusSite_cellCentre (R := R) (0 : TorusFields.TorusSite (4 * m)) h)
    have hLpos : (0 : ℤ) < R.params.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
    have e4 : oo = 0 := by
      have := MirrorDensities.siteOfInt_injective_of_abs_sub_lt (M := 4 * m * R.params.side) (fun i => ?_) e3
      · funext i
        have e5 := congrFun this i
        simpa using e5
      · have h2 := (BlockTrees.mem_centredCube_iff.mp ho) i
        have h5 : 2 * (((R.params.side : ℤ) - 1) / 2) ≤ (R.params.side : ℤ) - 1 := by omega
        have h6 : (2 : ℤ) ≤ ((4 * m : ℕ) : ℤ) := by exact_mod_cast h4
        have e6 : ((R.params.side : ℤ) * ((((0 : TorusFields.TorusSite (4 * m)) i).cast : ℤ) + h i) + oo i) -
            ((R.params.side : ℤ) * ((((0 : TorusFields.TorusSite (4 * m)) i).cast : ℤ) + h i) + (0 : Fin 4 → ℤ) i) = oo i := by
          simp
        rw [e6]
        push_cast at h6 ⊢
        nlinarith
    subst e4
    have h0 : (0 : Fin 4 → ℤ) ∈ BlockAverages.centredCube R.params.side := ho
    exact ⟨0, h0, e1, BoxAgreement.toTorusSite_cellCentre (R := R) o h⟩
private theorem frameDeviation_of_mem_free (s : StepSettings.ChartSetting R n) (hc : s.free ⊆ StepCosts.chartBonds R.params.side n)
    (hL : Odd R.params.side) (hn : 2 ≤ n) (hρA : 0 ≤ R.anchorRadius) (hρA' : R.anchorRadius ≤ 1) (hρ : R.ballRadius ≤ 1)
    {η : StepSettings.FreeCoords s.free} (hη : s.InBalls η) (b : s.free) :
    StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach s.coarse (s.field η) b.1 =
      ColdStepAtMirrorFrames.toImaginary (η b) := by apply _root_.YangMills.SharedProofs.p26285 <;> assumption
private theorem imaginaryComponent_toImaginary (c : Fin 3) (v : EuclideanSpace ℝ (Fin 3)) :
    BlockAverages.imaginaryComponent c (ColdStepAtMirrorFrames.toImaginary v) = v c := by
  fin_cases c <;> simp [BlockAverages.imaginaryComponent, ColdStepAtMirrorFrames.toImaginary]
private theorem parentBlock_supDist_le {L : ℕ} [NeZero L] (hodd : Odd L) (o : TorusFields.TorusSite n) {h oo : Fin 4 → ℤ} {k : ℕ}
    (hh : TorusFields.OffsetInBox k h) (ho : oo ∈ BlockAverages.centredCube L) :
    (TorusFields.supDist (TorusLumps.parentBlock L (StepSettings.fineSite L o h oo)) o : ℝ) ≤ k := by
  rw [BlockOffsets.parentBlock_fineSite hodd o h oo ho]
  have : TorusFields.supDist (o + TorusFields.siteOfInt h) o ≤ k := by
    rw [TorusFields.supDist_comm]
    exact TorusFields.supDist_add_siteOfInt_le o h k fun i => by
      have := abs_le.mp (hh i)
      omega
  exact_mod_cast this
private theorem coordsAgreeNear_of_agree {s : StepSettings.ChartSetting R n} {o : TorusFields.TorusSite n} {k mm : ℕ} {r : ℝ}
    (hkr : (k : ℝ) ≤ r) (hkm : k ≤ mm) (hL : Odd R.params.side) (hn : 2 ≤ n)
    (hρA : 0 ≤ R.anchorRadius) (hρA' : R.anchorRadius ≤ 1) (hρ : R.ballRadius ≤ 1) (hc : s.free ⊆ StepCosts.chartBonds R.params.side n)
    (hag : StepSettings.SettingsAgreeNear s (StepSettings.coldChartSetting R s.coarse) o o mm) {η : StepSettings.FreeCoords s.free}
    (hη : s.InBalls η) :
    BlockOffsets.CoordsAgreeNear s (StepSettings.coldChartSetting R s.coarse) o o k η
      (liftCoords s.coarse (MarkedIntegrals.chartBondsInBlocks R.params.side (ResponseInTheExpansion.supBall o r))
        (ResponseInTheExpansion.imaginaryComponentsOn _
          (StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach s.coarse (s.field η)))) := by
  classical
  intro q hq
  have hq' : StepSettings.IsNearIndex R.params.side mm q := ⟨fun i => (hq.1 i).trans (by exact_mod_cast hkm), hq.2⟩
  unfold StepSettings.ChartSetting.coordsByIndex
  by_cases hf : StepSettings.nearBond R.params.side o q ∈ s.free
  · have hf' : StepSettings.nearBond R.params.side o q ∈ (StepSettings.coldChartSetting R s.coarse).free := (hag.free_iff q hq').mp hf
    rw [dif_pos hf, dif_pos hf']
    have hZ : StepSettings.nearBond R.params.side o q ∈
        MarkedIntegrals.chartBondsInBlocks R.params.side (ResponseInTheExpansion.supBall o r) := by
      refine Finset.mem_filter.mpr ⟨hc hf, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      exact (parentBlock_supDist_le hL o hq.1 hq.2).trans hkr
    unfold liftCoords
    rw [dif_pos hZ]
    refine PiLp.ext fun c => ?_
    show _ = BlockAverages.imaginaryComponent c
      (StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach s.coarse (s.field η) (StepSettings.nearBond R.params.side o q))
    rw [frameDeviation_of_mem_free s hc hL hn hρA hρA' hρ hη ⟨_, hf⟩, imaginaryComponent_toImaginary]
  · have hf' : StepSettings.nearBond R.params.side o q ∉ (StepSettings.coldChartSetting R s.coarse).free :=
      fun h => hf ((hag.free_iff q hq').mpr h)
    rw [dif_neg hf, dif_neg hf']
private theorem reads_eq_of_agree {s : StepSettings.ChartSetting R n} {o : TorusFields.TorusSite n} {k mm : ℕ} {r : ℝ}
    (hkr : (k : ℝ) ≤ r) (hkm : k ≤ mm) (hfit : R.params.Admissible) (hn : 2 ≤ n)
    (hρA : 0 ≤ R.anchorRadius) (hρA' : R.anchorRadius ≤ 1) (hρ : R.ballRadius ≤ 1) (hc : s.free ⊆ StepCosts.chartBonds R.params.side n)
    (hk : 1 ≤ k)
    (hag : StepSettings.SettingsAgreeNear s (StepSettings.coldChartSetting R s.coarse) o o mm) {η : StepSettings.FreeCoords s.free}
    (hη : s.InBalls η)
    {A : Finset (TorusFields.TorusSite (n * R.params.side))} {M : ℝ}
    {f : TorusFields.TorusField (n * R.params.side) → Finset (TorusFields.TorusSite (n * R.params.side)) → ℝ}
    (hA : ∀ z ∈ A, TorusFields.supDist z (StepSettings.fineSite R.params.side o 0 0) + 1 + R.params.side ≤ R.params.side * k)
    (hf : ReadsGaugeInvariantly A M f) (Yt : Finset (TorusFields.TorusSite (n * R.params.side)))
    (hY : ∀ z ∈ A, z ∈ Yt → z ∈ s.support) :
    f (s.field η) Yt = f ((StepSettings.coldChartSetting R s.coarse).field
      (liftCoords s.coarse (MarkedIntegrals.chartBondsInBlocks R.params.side (ResponseInTheExpansion.supBall o r))
        (ResponseInTheExpansion.imaginaryComponentsOn _
          (StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach s.coarse (s.field η))))) ∅ := by
  classical
  have hL := hfit.L_odd
  have : NeZero (n * R.params.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne _)⟩
  have h0 : (0 : Fin 4 → ℤ) ∈ BlockAverages.centredCube R.params.side := by
    rw [BlockTrees.mem_centredCube_iff]
    intro i
    have : (0 : ℤ) ≤ ((R.params.side : ℤ) - 1) / 2 := by
      have : (1 : ℤ) ≤ R.params.side := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
      omega
    simpa using this
  have hF := BlockOffsets.fieldsAgreeNear_of_settings hL hn hn hc hag hk hkm
    (coordsAgreeNear_of_agree hkr hkm hL hn hρA hρA' hρ hc hag hη) h0
  refine hf.depends _ _ _ _ (fun c h1 _ => ?_) ?_
  · set y : TorusFields.TorusSite (n * R.params.side) := StepSettings.fineSite R.params.side o 0 0 with hy
    have hz := hA c.1 h1
    have hb : TorusFields.BondOffsetInBox (R.params.side * k - R.params.side) (MirrorDensities.offset y c.1, c.2) := by
      have hi : ∀ i, |MirrorDensities.offset y c.1 i| ≤ (TorusFields.supDist c.1 y : ℤ) := MirrorDensities.abs_offset_le y c.1
      have hz' : ((TorusFields.supDist c.1 y : ℤ)) + 1 ≤ ((R.params.side * k - R.params.side : ℕ) : ℤ) := by
        have : TorusFields.supDist c.1 y + 1 ≤ R.params.side * k - R.params.side := by omega
        exact_mod_cast this
      refine ⟨fun i => (hi i).trans (by omega), fun i => ?_⟩
      have h2 := abs_add_le (MirrorDensities.offset y c.1 i) ((Pi.single c.2 1 : Fin 4 → ℤ) i)
      have h3 : |(Pi.single c.2 1 : Fin 4 → ℤ) i| ≤ 1 := by
        by_cases h : i = c.2
        · subst h
          simp
        · simp [h]
      have h4 := hi i
      show |(MirrorDensities.offset y c.1 + Pi.single c.2 1 : Fin 4 → ℤ) i| ≤ _
      simp only [Pi.add_apply]
      omega
    have := hF (MirrorDensities.offset y c.1, c.2) hb
    simp only [TorusLumps.bondFrom, MirrorDensities.add_siteOfInt_offset] at this
    exact this
  · ext z
    simp only [Finset.mem_inter, Finset.notMem_empty, false_and, iff_false, not_and]
    intro hz hzA
    have hz1 := hA z hzA
    obtain ⟨h, oo, ho, hh, rfl⟩ := exists_index_of_site hL o z (k := k) (by omega)
    have := (hag.support_iff h oo (fun i => (hh i).trans (by exact_mod_cast hkm)) ho).mp (hY _ hzA hz)
    simp [StepSettings.coldChartSetting] at this
end Read
section Gauge
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
private theorem gaugeAt_trivialField (x : TorusFields.TorusSite (n * R.params.side)) :
    StepSettings.gaugeAt (R := R) (TorusFields.trivialField (n * R.params.side)) x = 1 :=
  BlockTrees.blockGauge_of_forall_eq_one (L := R.params.side) _ (fun _ _ => rfl) x
private theorem adjointAction_add (g : BlockAverages.UnitQuaternion) (X Y : BlockAverages.imaginaryQuaternions) :
    ColdStepAtMirrorFrames.adjointAction g (X + Y) =
      ColdStepAtMirrorFrames.adjointAction g X + ColdStepAtMirrorFrames.adjointAction g Y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
private theorem parentBlock_add_unitStep_of_not_crossing {L : ℕ} [NeZero L] (x : TorusFields.TorusSite (n * L)) (i : Fin 4)
    (h : ¬ BlockAverages.IsCrossingBond (F := TorusLumps.stepBlockFrame L n)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 0 x, i)) :
    TorusLumps.parentBlock L (x + TorusFields.unitStep (n * L) i) = TorusLumps.parentBlock L x := by
  have : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  have e : BlockAverages.enclosingCell (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 0 x +
        BlockAverages.unitStep (F := TorusLumps.stepBlockFrame L n) 0 i) =
      BlockAverages.enclosingCell (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 0 x) := not_not.mp h
  rw [← BlockTrees.torusSiteInFrame_unitStep, ← BlockTrees.torusSiteInFrame_add, BlockTrees.enclosingCell_torusSiteInFrame,
    BlockTrees.enclosingCell_torusSiteInFrame] at e
  exact BlockTrees.torusSiteInFrame_injective (TorusLumps.stepBlockFrame L n) 1 BlockTrees.stepBlockFrame_period_one e
private theorem coldChartSetting_field_apply (U : TorusFields.TorusField n)
    (v : StepSettings.FreeCoords (StepSettings.coldChartSetting R U).free) (x : TorusFields.TorusSite (n * R.params.side)) (i : Fin 4)
    (h : (x, i) ∈ StepCosts.chartBonds R.params.side n) :
    (StepSettings.coldChartSetting R U).field v x i =
      open Classical in if BlockAverages.IsCrossingBond (F := TorusLumps.stepBlockFrame R.params.side n)
          (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 0 x, i) then
        BlockAverages.expUnit (StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach U (x, i) +
          ColdStepAtMirrorFrames.toImaginary (v ⟨(x, i), h⟩)) * U (TorusLumps.parentBlock R.params.side x) i
      else BlockAverages.expUnit (StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach U (x, i) +
          ColdStepAtMirrorFrames.toImaginary (v ⟨(x, i), h⟩)) := by
  classical
  have hb : (StepSettings.coldChartSetting R U).fine = TorusFields.trivialField _ := rfl
  have hm : (x, i) ∈ (StepSettings.coldChartSetting R U).free := h
  unfold StepSettings.ChartSetting.field StepSettings.chartLink
  rw [dif_pos hm, hb, gaugeAt_trivialField, gaugeAt_trivialField]
  simp only [inv_one, one_mul, mul_one]
  rfl
private theorem field_eq_gaugeTransform {U V : TorusFields.TorusField n} {g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion}
    (v : StepSettings.FreeCoords (StepSettings.coldChartSetting R V).free)
    (v' : StepSettings.FreeCoords (StepSettings.coldChartSetting R U).free) (c : TorusFields.TorusBond (n * R.params.side))
    (hv : ∀ h : c ∈ StepCosts.chartBonds R.params.side n, ColdStepAtMirrorFrames.toImaginary (v' ⟨c, h⟩) =
      ColdStepAtMirrorFrames.adjointAction (g (TorusLumps.parentBlock R.params.side c.1)) (ColdStepAtMirrorFrames.toImaginary (v ⟨c, h⟩)))
    (hfr : c ∈ StepCosts.chartBonds R.params.side n → StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach U c =
      ColdStepAtMirrorFrames.adjointAction (g (TorusLumps.parentBlock R.params.side c.1))
        (StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach V c))
    (hU : BlockAverages.IsCrossingBond (F := TorusLumps.stepBlockFrame R.params.side n)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 0 c.1, c.2) →
      U (TorusLumps.parentBlock R.params.side c.1) c.2 = g (TorusLumps.parentBlock R.params.side c.1) *
        V (TorusLumps.parentBlock R.params.side c.1) c.2 *
          (g (TorusLumps.parentBlock R.params.side (c.1 + TorusFields.unitStep _ c.2)))⁻¹) :
    (StepSettings.coldChartSetting R U).field v' c.1 c.2 =
      TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g)
        ((StepSettings.coldChartSetting R V).field v) c.1 c.2 := by
  classical
  obtain ⟨x, i⟩ := c
  simp only at hv hfr hU ⊢
  show _ = g (TorusLumps.parentBlock R.params.side x) * (StepSettings.coldChartSetting R V).field v x i *
    (g (TorusLumps.parentBlock R.params.side (x + TorusFields.unitStep _ i)))⁻¹
  by_cases hc : (x, i) ∈ StepCosts.chartBonds R.params.side n
  · have hw : StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach U (x, i) +
          ColdStepAtMirrorFrames.toImaginary (v' ⟨(x, i), hc⟩) =
        ColdStepAtMirrorFrames.adjointAction (g (TorusLumps.parentBlock R.params.side x))
          (StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach V (x, i) +
            ColdStepAtMirrorFrames.toImaginary (v ⟨(x, i), hc⟩)) := by
      rw [hfr hc, hv hc, adjointAction_add]
    rw [coldChartSetting_field_apply U v' x i hc, coldChartSetting_field_apply V v x i hc, hw,
      ColdStepAtMirrorFrames.Adjoint.expUnit_adjointAction]
    by_cases hx : BlockAverages.IsCrossingBond (F := TorusLumps.stepBlockFrame R.params.side n)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 0 x, i)
    · rw [if_pos hx, if_pos hx, hU hx]
      group
    · rw [if_neg hx, if_neg hx, parentBlock_add_unitStep_of_not_crossing x i hx]
  · have hm : (x, i) ∉ (StepSettings.coldChartSetting R U).free := hc
    have hm' : (x, i) ∉ (StepSettings.coldChartSetting R V).free := hc
    have ht : BlockAverages.IsAxialTreeBond (F := TorusLumps.stepBlockFrame R.params.side n)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 0 x, i) := by
      by_contra hn
      exact hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    unfold StepSettings.ChartSetting.field
    rw [dif_neg hm, dif_neg hm', parentBlock_add_unitStep_of_not_crossing x i ht.1]
    show (1 : BlockAverages.UnitQuaternion) = _ * 1 * _
    group
private theorem parentBlock_add_unitStep_cases {L : ℕ} [NeZero L] (x : TorusFields.TorusSite (n * L)) (i : Fin 4) :
    TorusLumps.parentBlock L (x + TorusFields.unitStep (n * L) i) = TorusLumps.parentBlock L x ∨
      TorusLumps.parentBlock L (x + TorusFields.unitStep (n * L) i) = TorusLumps.parentBlock L x + TorusFields.unitStep n i := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.parentBlock_add_unitStep <;> assumption
private theorem read_eq_of_gauge {U V : TorusFields.TorusField n} {g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion}
    {A : Finset (TorusFields.TorusSite (n * R.params.side))} {M : ℝ}
    {f : TorusFields.TorusField (n * R.params.side) → Finset (TorusFields.TorusSite (n * R.params.side)) → ℝ}
    (hf : ReadsGaugeInvariantly A M f)
    (v : StepSettings.FreeCoords (StepSettings.coldChartSetting R V).free)
    (v' : StepSettings.FreeCoords (StepSettings.coldChartSetting R U).free)
    (h1 : ∀ c : TorusFields.TorusBond (n * R.params.side), c.1 ∈ A → ∀ h : c ∈ StepCosts.chartBonds R.params.side n,
      ColdStepAtMirrorFrames.toImaginary (v' ⟨c, h⟩) =
        ColdStepAtMirrorFrames.adjointAction (g (TorusLumps.parentBlock R.params.side c.1))
          (ColdStepAtMirrorFrames.toImaginary (v ⟨c, h⟩)))
    (h2 : ∀ c : TorusFields.TorusBond (n * R.params.side), c.1 ∈ A → c ∈ StepCosts.chartBonds R.params.side n →
      StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach U c =
        ColdStepAtMirrorFrames.adjointAction (g (TorusLumps.parentBlock R.params.side c.1))
          (StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach V c))
    (h3 : ∀ c : TorusFields.TorusBond (n * R.params.side), c.1 ∈ A →
      TorusLumps.parentBlock R.params.side (c.1 + TorusFields.unitStep _ c.2) =
        TorusLumps.parentBlock R.params.side c.1 + TorusFields.unitStep n c.2 →
      U (TorusLumps.parentBlock R.params.side c.1) c.2 = g (TorusLumps.parentBlock R.params.side c.1) *
        V (TorusLumps.parentBlock R.params.side c.1) c.2 *
          (g (TorusLumps.parentBlock R.params.side c.1 + TorusFields.unitStep n c.2))⁻¹) :
    f ((StepSettings.coldChartSetting R U).field v') ∅ = f ((StepSettings.coldChartSetting R V).field v) ∅ := by
  rw [← hf.gauge_invariant (TorusLumps.blockConstantGauge R.params.side g) ((StepSettings.coldChartSetting R V).field v) ∅]
  refine hf.depends _ _ _ _ (fun c hc _ => field_eq_gaugeTransform v v' c (h1 c hc) (h2 c hc) fun hx => ?_) rfl
  have hs : TorusLumps.parentBlock R.params.side (c.1 + TorusFields.unitStep (n * R.params.side) c.2) =
      TorusLumps.parentBlock R.params.side c.1 + TorusFields.unitStep n c.2 := by
    refine (parentBlock_add_unitStep_cases c.1 c.2).resolve_left fun he => hx ?_
    have e1 : StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 0 c.1 +
          BlockAverages.unitStep (F := TorusLumps.stepBlockFrame R.params.side n) 0 c.2 =
        StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 0
          (c.1 + TorusFields.unitStep (n * R.params.side) c.2) := by
      rw [BlockTrees.torusSiteInFrame_add, BlockTrees.torusSiteInFrame_unitStep]
    show BlockAverages.enclosingCell (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 0 c.1 +
        BlockAverages.unitStep (F := TorusLumps.stepBlockFrame R.params.side n) 0 c.2) =
      BlockAverages.enclosingCell (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 0 c.1)
    rw [e1, BlockTrees.enclosingCell_torusSiteInFrame, BlockTrees.enclosingCell_torusSiteInFrame, he]
  rw [h3 c hc hs, hs]
end Gauge
section Places
variable {n L : ℕ} [NeZero n] [NeZero L]
private theorem enclosingCell_reflectedBondPosition (hL : Odd L) {t m : ℕ} (hm : 0 < m) (o : TorusFields.TorusSite n)
    (c : TorusFields.TorusBond (n * L)) (a : Fin 4 → ℤ)
    (ha : ∀ i, (TorusLumps.parentBlock L c.1 i - o i).valMinAbs = a i) (hb : ∀ i, 2 * |a i| + 1 < (n : ℤ)) :
    BlockAverages.enclosingCell (ResponseInTheExpansion.reflectedBondPosition L t m o c).1 =
      BlockAverages.siteOfCoords (ResponseInTheExpansion.reflectedTorusFrame L t m n).top a := by apply _root_.YangMills.SharedProofs.p38944 <;> assumption
private theorem reflectedGauge_enclosingCell {t m : ℕ} (hm : 0 < m) (o : TorusFields.TorusSite n)
    (γ : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (y : TorusFields.TorusSite n) (a : Fin 4 → ℤ)
    (ha : ∀ i, (y i - o i).valMinAbs = a i) (hb : ∀ i, |a i| ≤ m) :
    ColdStepAtMirrorFrames.reflectedGauge m
      (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top o)
      (fun x => γ (TorusLumps.toTorusSite n x))
      (BlockAverages.siteOfCoords (ResponseInTheExpansion.reflectedTorusFrame L t m n).top a) = γ y := by apply _root_.YangMills.SharedProofs.p35238 <;> assumption
private theorem reflectedTopField_gaugeTransform (hMir : ColdStepAtMirrorFrames.ReflectedFieldOfGaugedTop) {t m : ℕ} (hm : 0 < m)
    (o : TorusFields.TorusSite n) (γ : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (V : TorusFields.TorusField n) :
    ResponseInTheExpansion.reflectedTopField L t m o (TorusFields.gaugeTransform γ V) =
      BlockAverages.gaugeTransform (ColdStepAtMirrorFrames.reflectedGauge m
          (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top o)
          (fun x => γ (TorusLumps.toTorusSite n x)))
        (ResponseInTheExpansion.reflectedTopField L t m o V) := by apply _root_.YangMills.SharedProofs.p89812 <;> assumption
end Places
section Mirror
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
private theorem toImaginary_of_components (X : BlockAverages.imaginaryQuaternions) :
    ColdStepAtMirrorFrames.toImaginary (WithLp.toLp 2 (fun c => BlockAverages.imaginaryComponent c X)) = X := by
  have e : (WithLp.toLp 2 (fun c => BlockAverages.imaginaryComponent c X) : EuclideanSpace ℝ (Fin 3)) = StepSettings.toCoords X := by
    refine PiLp.ext fun c => ?_
    fin_cases c <;> rfl
  rw [e]
  exact BlockTrees.toImaginary_toCoords X
private theorem adjointAction_zero (g : BlockAverages.UnitQuaternion) : ColdStepAtMirrorFrames.adjointAction g 0 = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_zero <;> assumption
private theorem toImaginary_liftCoords (U : TorusFields.TorusField n) (Z : Finset (TorusFields.TorusBond (n * R.params.side)))
    (e : TorusFields.TorusBond (n * R.params.side) → BlockAverages.imaginaryQuaternions)
    (b : (StepSettings.coldChartSetting R U).free) (hb : b.1 ∈ Z) :
    ColdStepAtMirrorFrames.toImaginary (liftCoords (R := R) U Z (ResponseInTheExpansion.imaginaryComponentsOn Z e) b) = e b.1 := by
  classical
  unfold liftCoords
  rw [dif_pos hb]
  exact toImaginary_of_components _
private theorem reflectedTopField_congr (hMR : ColdStepAtMirrorFrames.ReflectedBondReadsBox) {L t m : ℕ} (hm : 0 < m)
    (o : TorusFields.TorusSite n) (U W : TorusFields.TorusField n)
    (h : ∀ c : TorusFields.TorusBond n, c.1 ∈ ResponseInTheExpansion.supBall o m →
      c.1 + TorusFields.unitStep n c.2 ∈ ResponseInTheExpansion.supBall o m → U c.1 c.2 = W c.1 c.2) :
    ResponseInTheExpansion.reflectedTopField L t m o U = ResponseInTheExpansion.reflectedTopField L t m o W := by
  classical
  funext z i
  have hpt : ∀ i, (TorusFields.torusFrame L t n).period (TorusFields.torusFrame L t n).top i = n :=
    TopLevelSites.period_top_of_extent (F := TorusFields.torusFrame L t n) (n := n) fun _ => rfl
  unfold ResponseInTheExpansion.reflectedTopField
  obtain ⟨hb, hr⟩ := hMR (TorusFields.torusFrame L t n) m z i hm
  rw [hr, hr]
  have e1 : TorusLumps.toTorusSite n (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top o +
      BlockAverages.siteOfCoords (TorusFields.torusFrame L t n).top (ColdStepAtMirrorFrames.sourceOffset m z i)) =
      o + TorusFields.siteOfInt (ColdStepAtMirrorFrames.sourceOffset m z i) := by
    rw [TopLevelSites.toTorusSite_add hpt, TopLevelSites.toTorusSite_torusSiteInFrame hpt, TopLevelSites.toTorusSite_siteOfCoords hpt]
  have e : TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top U
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top o +
          BlockAverages.siteOfCoords (TorusFields.torusFrame L t n).top (ColdStepAtMirrorFrames.sourceOffset m z i)) i =
      TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top W
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top o +
          BlockAverages.siteOfCoords (TorusFields.torusFrame L t n).top (ColdStepAtMirrorFrames.sourceOffset m z i)) i := by
    show U (TorusLumps.toTorusSite n _) i = W (TorusLumps.toTorusSite n _) i
    rw [e1]
    refine h (o + TorusFields.siteOfInt (ColdStepAtMirrorFrames.sourceOffset m z i), i) ?_ ?_
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have : TorusFields.supDist (o + TorusFields.siteOfInt (ColdStepAtMirrorFrames.sourceOffset m z i)) o ≤ m := by
        rw [TorusFields.supDist_comm]
        exact TorusFields.supDist_add_siteOfInt_le o _ m fun l => by
          have := abs_le.mp (show |ColdStepAtMirrorFrames.sourceOffset m z i l| ≤ (m : ℤ) from hb.1 l)
          omega
      exact_mod_cast this
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have e2 : o + TorusFields.siteOfInt (ColdStepAtMirrorFrames.sourceOffset m z i) + TorusFields.unitStep n i =
          o + TorusFields.siteOfInt (ColdStepAtMirrorFrames.sourceOffset m z i + Pi.single i 1) := by
        rw [TorusLumps.unitStep_eq_siteOfInt, add_assoc, ← TorusFields.siteOfInt_add]
      have : TorusFields.supDist (o + TorusFields.siteOfInt (ColdStepAtMirrorFrames.sourceOffset m z i + Pi.single i 1)) o ≤ m := by
        rw [TorusFields.supDist_comm]
        exact TorusFields.supDist_add_siteOfInt_le o _ m fun l => by
          have := abs_le.mp (show |(ColdStepAtMirrorFrames.sourceOffset m z i + Pi.single i 1 : Fin 4 → ℤ) l| ≤ (m : ℤ) from hb.2 l)
          omega
      show ((TorusFields.supDist (o + TorusFields.siteOfInt (ColdStepAtMirrorFrames.sourceOffset m z i) + TorusFields.unitStep n i) o
        : ℕ) : ℝ) ≤ m
      rw [e2]
      exact_mod_cast this
  rw [e]
private theorem reflectedCoordinateAt_adjoint {L t m : ℕ} [NeZero L] (hL : Odd L) (hm : 0 < m) (o : TorusFields.TorusSite n)
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion)
    (η : ColdStepAtMirrorFrames.StepVariable (ColdStepAtMirrorFrames.finiteCells (ResponseInTheExpansion.reflectedTorusFrame L t m n)))
    (b : TorusFields.TorusBond (n * L))
    (hb : ∀ i, |(TorusLumps.parentBlock L b.1 i - o i).valMinAbs| ≤ m)
    (hb2 : ∀ i, 2 * |(TorusLumps.parentBlock L b.1 i - o i).valMinAbs| + 1 < (n : ℤ)) :
    ResponseInTheExpansion.reflectedCoordinateAt L t m o (ColdStepAtMirrorFrames.adjointStepVariable
        (ColdStepAtMirrorFrames.reflectedGauge m
          (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top o)
          (fun x => g (TorusLumps.toTorusSite n x))) η) b =
      ColdStepAtMirrorFrames.adjointAction (g (TorusLumps.parentBlock L b.1)) (ResponseInTheExpansion.reflectedCoordinateAt L t m o η b) := by
  classical
  unfold ResponseInTheExpansion.reflectedCoordinateAt ColdStepAtMirrorFrames.stepCoordinates
  by_cases h : ResponseInTheExpansion.reflectedBondPosition L t m o b ∈
      BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (ResponseInTheExpansion.reflectedTorusFrame L t m n))
  · simp only [Prod.mk.eta, dif_pos h]
    have e1 := enclosingCell_reflectedBondPosition hL (t := t) hm o b (fun i => (TorusLumps.parentBlock L b.1 i - o i).valMinAbs)
      (fun _ => rfl) hb2
    have e2 := reflectedGauge_enclosingCell (L := L) (t := t) hm o g (TorusLumps.parentBlock L b.1)
      (fun i => (TorusLumps.parentBlock L b.1 i - o i).valMinAbs) (fun _ => rfl) hb
    have e3 : ColdStepAtMirrorFrames.toImaginary (ColdStepAtMirrorFrames.adjointStepVariable
          (ColdStepAtMirrorFrames.reflectedGauge m
            (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top o)
            (fun x => g (TorusLumps.toTorusSite n x))) η ⟨ResponseInTheExpansion.reflectedBondPosition L t m o b, h⟩) =
        ColdStepAtMirrorFrames.adjointAction (ColdStepAtMirrorFrames.reflectedGauge m
            (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top o)
            (fun x => g (TorusLumps.toTorusSite n x))
            (BlockAverages.enclosingCell (ResponseInTheExpansion.reflectedBondPosition L t m o b).1))
          (ColdStepAtMirrorFrames.toImaginary (η ⟨ResponseInTheExpansion.reflectedBondPosition L t m o b, h⟩)) :=
      BlockTrees.toImaginary_toCoords _
    rw [e3, e1, e2]
  · simp only [Prod.mk.eta, dif_neg h]
    exact (adjointAction_zero _).symm
end Mirror
section Means
private theorem cutoffFactor_nonneg (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ ColdStepAtMirrorFrames.cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
private theorem abs_ratio_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {d G : α → ℝ} {B : ℝ} (hd : ∀ a, 0 ≤ d a)
    (hG : ∀ a, |G a| ≤ B) (hB : 0 ≤ B) : |(∫ a, G a * d a ∂μ) / ∫ a, d a ∂μ| ≤ B := by apply _root_.YangMills.SharedProofs.p11634 <;> assumption
private theorem weightedMean_congr {n : ℕ} {free : Finset (TorusFields.TorusBond n)} {d G G' : StepSettings.FreeCoords free → ℝ}
    (h : ∀ η, d η ≠ 0 → G η = G' η) : StepSettings.weightedMean d G = StepSettings.weightedMean d G' := by apply _root_.YangMills.SharedProofs.p17143 <;> assumption
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
private theorem chartDensity_nonneg (s : StepSettings.ChartSetting R n) (η : StepSettings.FreeCoords s.free) :
    0 ≤ WeightedResponses.chartDensity s η := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.chartDensity_nonneg <;> assumption
private theorem inBalls_of_chartDensity_ne_zero (s : StepSettings.ChartSetting R n) {η : StepSettings.FreeCoords s.free}
    (h : WeightedResponses.chartDensity s η ≠ 0) : s.InBalls η := by apply _root_.YangMills.SharedProofs.p4538 <;> assumption
private theorem parentBlock_not_mem_of_quiet {G : StepGas.GasGround R n} {σ : G.Config} {A : Finset (TorusFields.TorusSite n)}
    (hσ : ∀ Y ∈ A, σ ∈ G.NoSpinMeets Y) {θ : StepGas.GasSupport R n} (h : (G.familyOf σ).Occupies θ)
    {z : TorusFields.TorusSite (n * R.params.side)} (hz : z ∈ θ.sites) : TorusLumps.parentBlock R.params.side z ∉ A := by apply _root_.YangMills.SharedProofs.p26926 <;> assumption
private theorem parentBlock_mem_blocksNearFreeCores {Q : Finset (TorusFields.TorusSite n)}
    {v z : TorusFields.TorusSite (n * R.params.side)} (hv : TorusLumps.parentBlock R.params.side v ∈ Q)
    (h : TorusFields.supDist v z ≤ 4 * R.range) :
    TorusLumps.parentBlock R.params.side z ∈ ResponseInTheExpansion.blocksNearFreeCores R.params.side R.range Q :=
  Finset.mem_image.mpr ⟨z, (TorusFields.mem_thickening _ _ _).mpr ⟨v, ClusterExpansionOfAStep.mem_sitesInBlocks.mpr hv,
    by rw [TorusFields.supDist_comm]; exact h⟩, rfl⟩
private theorem disjoint_core_of_quiet {G : StepGas.GasGround R n} {σ : G.Config} {Q : Finset (TorusFields.TorusSite n)}
    (hσ : ∀ Y ∈ ResponseInTheExpansion.blocksNearFreeCores R.params.side R.range Q, σ ∈ G.NoSpinMeets Y) {θ : StepGas.GasSupport R n}
    (h : (G.familyOf σ).Occupies θ) : Disjoint θ.core Q := by
  refine Finset.disjoint_left.mpr fun y hy hyQ => ?_
  obtain ⟨p, hp, z, hz, hpz⟩ := StepGas.GasSupport.mem_core.mp hy
  exact parentBlock_not_mem_of_quiet hσ h hz (parentBlock_mem_blocksNearFreeCores (hp ▸ hyQ) hpz)
private theorem abs_integral_sub_le_of_good {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → ℝ}
    (hg : Integrable g P) {M ε B e : ℝ} (A : Finset ι) (N : ι → Set Ω) (hN : ∀ Y, MeasurableSet (N Y))
    (hp : ∀ Y ∈ A, 1 - e ≤ P.real (N Y))
    (hgood : ∀ᵐ σ ∂P, (∀ Y ∈ A, σ ∈ N Y) → |g σ - M| ≤ ε) (hgB : ∀ᵐ σ ∂P, |g σ| ≤ B) (hMB : |M| ≤ B)
    (hε : 0 ≤ ε) (hB : 0 ≤ B) : |∫ σ, g σ ∂P - M| ≤ ε + 2 * B * A.card * e := by apply _root_.YangMills.SharedProofs.p43034 <;> assumption
end Means
section Frames
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
private theorem add_siteOfInt_mem_supBall {o : TorusFields.TorusSite n} {y : TorusFields.TorusSite n} {m d : ℕ} {h : Fin 4 → ℤ}
    (hy : TorusFields.supDist y o + d ≤ m) (hh : TorusFields.OffsetInBox d h) :
    y + TorusFields.siteOfInt h ∈ ResponseInTheExpansion.supBall o m := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have h1 : TorusFields.supDist (y + TorusFields.siteOfInt h) y ≤ d := by
    rw [TorusFields.supDist_comm]
    exact TorusFields.supDist_add_siteOfInt_le y h d fun i => by
      have := abs_le.mp (hh i)
      omega
  have h2 := TorusFields.supDist_triangle (y + TorusFields.siteOfInt h) y o
  have : TorusFields.supDist (y + TorusFields.siteOfInt h) o ≤ m := by omega
  exact_mod_cast this
private theorem frameCoord_gaugeTransform (hFr : FrameLocality.FrameCoordLocal) (hFg : StepFrames.FrameCovariance)
    (hS : R.IsWellPosed) (hF : R.ColdChainFits) (hb : TorusLumps.IsBlockTorusSide R.params n) {m : ℕ} {o : TorusFields.TorusSite n}
    {U V : TorusFields.TorusField n} {g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion}
    (hU : ∀ c : TorusFields.TorusBond n, c.1 ∈ ResponseInTheExpansion.supBall o m →
      c.1 + TorusFields.unitStep n c.2 ∈ ResponseInTheExpansion.supBall o m → U c.1 c.2 = ResponseInTheExpansion.gaugeTransform g V c)
    (hm₀ : 0 < R.frameReach) (hside : 4 * R.frameReach + 5 < n) (c : TorusFields.TorusBond (n * R.params.side))
    (hc : c ∈ StepCosts.chartBonds R.params.side n)
    (hy : TorusFields.supDist (TorusLumps.parentBlock R.params.side c.1) o + R.frameReach ≤ m)
    (hC : TorusLumps.parentBlock R.params.side c.1 ∉ StepSettings.hotCoreSites R V) :
    StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach U c =
      ColdStepAtMirrorFrames.adjointAction (g (TorusLumps.parentBlock R.params.side c.1))
        (StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach V c) := by
  have hfit := hS.admissible
  obtain ⟨δ, lam, σA, cg, N, hch, hσ, hσ1⟩ := hF
  have hrf : StepMarks.RangesAdmissible R.range R.nextRange := ⟨hS.range_le, hS.nextRange_ge, by
    have := hS.range_ge_side
    have := hfit.L_ge
    omega⟩
  have hsit : StepMarks.IsStepSituation R.params R.nextRange V
      (Finset.univ \ TorusLumps.thickening LumpContours.lumpRange (TorusLumps.torusHotSites R.params V))
      (StepSettings.hotCoreSites R V) R.params.threshold :=
    Or.inl ⟨hb, rfl, rfl, rfl⟩
  have e1 : StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach U c =
      StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach (TorusFields.gaugeTransform g V) c := by
    refine hFr R.params R.anchorRadius R.depth R.frameReach n n U (TorusFields.gaugeTransform g V) c c hfit hm₀ hside hside rfl rfl
      fun b hbb => ?_
    refine hU (TorusLumps.bondFrom (TorusLumps.parentBlock R.params.side c.1) b) (add_siteOfInt_mem_supBall hy hbb.1) ?_
    have e : (TorusLumps.bondFrom (TorusLumps.parentBlock R.params.side c.1) b).1 +
          TorusFields.unitStep n (TorusLumps.bondFrom (TorusLumps.parentBlock R.params.side c.1) b).2 =
        TorusLumps.parentBlock R.params.side c.1 + TorusFields.siteOfInt (b.1 + Pi.single b.2 1) := by
      simp only [TorusLumps.bondFrom]
      rw [TorusLumps.unitStep_eq_siteOfInt, add_assoc, ← TorusFields.siteOfInt_add]
    rw [e]
    exact add_siteOfInt_mem_supBall hy hbb.2
  have e2 := (hFg R.params δ lam R.anchorRadius σA cg N hfit hch hσ R.depth R.range R.nextRange n V _ _ _ hrf hsit c hc hC).1 g
  rw [e1]
  exact Subtype.ext e2
end Frames
section Carry
open Classical in
private theorem cutoffMean_reflected_gauge (hCar : ResponseInTheExpansion.stepLawGaugeInvariantStatement)
    (hRB : ColdStepAtMirrorFrames.ColdExpansionRegular)
    {T : RenormalizationStepParameters.ParameterAssignment} (hD : T.Admissible) (hOn2 : T.HoldsFrom WeightedResponses.ColdRegimeEstimatesAt) {y : ℝ}
    (hyC : T.yC ≤ y) {R : StepSettings.StepSetup} (hOT : R.OnParameters T y)
    (hfit : R.params.Admissible) {m n : ℕ} [NeZero n] (hn₀ : R.params.n₀ ≤ 4 * m) (o : TorusFields.TorusSite n)
    (V : TorusFields.TorusField n)
    (hc1 : ColdStepAtMirrorFrames.IsSmallCurvature R.params.threshold (ResponseInTheExpansion.reflectedTopField R.params.side R.depth m o V))
    (Γ : (ResponseInTheExpansion.reflectedTorusFrame R.params.side R.depth m n).Cell → BlockAverages.UnitQuaternion)
    (H : ColdStepAtMirrorFrames.StepVariable
      (ColdStepAtMirrorFrames.finiteCells (ResponseInTheExpansion.reflectedTorusFrame R.params.side R.depth m n)) → ℝ) :
    ColdStepAtMirrorFrames.cutoffMean R.ballRadius R.barrierFn (ColdStepAtMirrorFrames.stepExponent false R.params.coupling
        R.anchorRadius R.coupling R.frameReach (ColdStepAtMirrorFrames.localFamilyOfDensity R.density) 1
        (BlockAverages.gaugeTransform Γ (ResponseInTheExpansion.reflectedTopField R.params.side R.depth m o V))) H =
      ColdStepAtMirrorFrames.cutoffMean R.ballRadius R.barrierFn (ColdStepAtMirrorFrames.stepExponent false R.params.coupling
          R.anchorRadius R.coupling R.frameReach (ColdStepAtMirrorFrames.localFamilyOfDensity R.density) 1
          (ResponseInTheExpansion.reflectedTopField R.params.side R.depth m o V))
        fun η => H (ColdStepAtMirrorFrames.adjointStepVariable Γ η) := by
  obtain ⟨ℓ, t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩ := R
  have hl : ℓ = T.stepParameters y := hOT.params_eq
  subst hl
  have hr : ρA = T.ρA := hOT.anchorRadius_eq
  have hp : p = T.cutoff := hOT.barrierFn_eq
  have hco : y ≤ x := hOT.le_coupling
  have hst := hOT.isStep
  obtain ⟨c₂, nss₂, hT₂, hA₂⟩ := hOn2
  have hA₃ := hCar _ hD.L_odd (by
    have := hD.n₀_ge
    show 2 ≤ T.n₀
    omega) hD.σ_pos (hA₂ y hyC).equivariance
  have hρA₂ : c₂.ρA = ρA := hT₂.2.2.1.trans hr.symm
  have hrowB : ColdStepAtMirrorFrames.IsRegularFamily (T.stepParameters y).side t (T.stepParameters y).n₀
      (T.stepParameters y).threshold (T.stepParameters y).weightRate (T.stepParameters y).E (T.stepParameters y).E₃
      (ColdStepAtMirrorFrames.localFamilyOfDensity f) :=
    hRB (T.stepParameters y) t x D f hfit rfl hst.1.1
  have hTop : ColdStepAtMirrorFrames.IsCubicTopTorus (T.stepParameters y).side t (T.stepParameters y).n₀
      (ResponseInTheExpansion.reflectedTorusFrame (T.stepParameters y).side t m n) :=
    ⟨rfl, rfl, 4 * m, fun _ => rfl, hn₀⟩
  have hσ0 : 0 < (T.stepParameters y).threshold := hfit.σ_pos
  have h := hA₃ t x hco (ColdStepAtMirrorFrames.localFamilyOfDensity f) hrowB
    (ResponseInTheExpansion.reflectedTorusFrame (T.stepParameters y).side t m n) hTop
    (ResponseInTheExpansion.reflectedTopField (T.stepParameters y).side t m o V)
    (fun q hq => (hc1 q hq).trans_le (by show (T.stepParameters y).threshold ≤ 5 / 4 * (T.stepParameters y).threshold; linarith)) Γ H
  have h' : ColdStepAtMirrorFrames.cutoffMean ((T.stepParameters y).threshold / 64) T.cutoff
      (ColdStepAtMirrorFrames.stepExponent false (T.stepParameters y).coupling c₂.ρA x (TorusLumps.clusterRange x / 2 ^ 11)
        (ColdStepAtMirrorFrames.localFamilyOfDensity f) 1
        (BlockAverages.gaugeTransform Γ (ResponseInTheExpansion.reflectedTopField (T.stepParameters y).side t m o V))) H =
    ColdStepAtMirrorFrames.cutoffMean ((T.stepParameters y).threshold / 64) T.cutoff
      (ColdStepAtMirrorFrames.stepExponent false (T.stepParameters y).coupling c₂.ρA x (TorusLumps.clusterRange x / 2 ^ 11)
        (ColdStepAtMirrorFrames.localFamilyOfDensity f) 1 (ResponseInTheExpansion.reflectedTopField (T.stepParameters y).side t m o V))
      fun η => H (ColdStepAtMirrorFrames.adjointStepVariable Γ η) := h
  rw [hρA₂, ← hp] at h'
  exact h'
end Carry
section Read2
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
private theorem measurable_liftCoords (U : TorusFields.TorusField n) (Z : Finset (TorusFields.TorusBond (n * R.params.side))) :
    Measurable (liftCoords (R := R) U Z) := by
  classical
  refine measurable_pi_lambda _ fun b => ?_
  unfold liftCoords
  by_cases h : b.1 ∈ Z
  · simp only [dif_pos h]
    have h1 : Measurable fun e : ↥Z × Fin 3 → ℝ => fun c : Fin 3 => e (⟨b.1, h⟩, c) :=
      measurable_pi_lambda _ fun c => measurable_pi_apply _
    exact (PiLp.continuous_toLp 2 _).measurable.comp h1
  · simp only [dif_neg h]
    exact measurable_const
private theorem familyOf_allVacant (G : StepGas.GasGround R n) : G.familyOf G.allVacant = StepGas.GasFamily.empty := by apply _root_.YangMills.SharedProofs.p24466 <;> assumption
end Read2
end ForgetsRotatedField
open ForgetsRotatedField in
theorem forgetsRotatedField_holds (hCM₀ : WeightedResponses.caseMeanEqGasMeanStatement) (hCol₀ : ClusterExpansionOfAStep.GasColumnsSmall)
    (hRat : ClusterExpansionOfAStep.PartitionRatioBounds) (hImg₀ : StepSettings.coarseStateGasStatement) (hGr₀ : StepGas.HullStateIsHotCase)
    (hCfg₀ : ClusterExpansionOfAStep.GasConfigIsAdmissibleSetting) (hQ : ResponseInTheExpansion.coldMirrorSettingAgreementStatement)
    (hS₀ : ResponseInTheExpansion.settingNearColdMirrorStatement) (hU : WeightedResponses.boundedCaseFunctionIntegrableStatement)
    (hFr : FrameLocality.FrameCoordLocal) (hFg : StepFrames.FrameCovariance)
    (hMir : ColdStepAtMirrorFrames.reflectedFieldReadsBox) (hCar : ResponseInTheExpansion.stepLawGaugeInvariantStatement)
    (hCold : ResponseInTheExpansion.mirrorOfColdBallSmallCurvatureStatement) (hRB : ColdStepAtMirrorFrames.ColdExpansionRegular) :
    forgetsRotatedFieldStatement := by
  classical
  obtain ⟨r1, hr1, hCM⟩ := hCM₀
  obtain ⟨r2, hr2, hCol⟩ := hCol₀
  obtain ⟨r3, hr3, hImg⟩ := hImg₀
  obtain ⟨r4, hr4, hS⟩ := hS₀
  refine ⟨fun c => min (min (r1 c) (r2 c)) (min (r3 c) (r4 c)),
    fun c => lt_min (lt_min (hr1 c) (hr2 c)) (lt_min (hr3 c) (hr4 c)), fun T hT hC hC2 hrt => ?_⟩
  have hrt1 := hrt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrt2 := hrt.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrt3 := hrt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrt4 := hrt.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨y1, h1⟩ := hCM T hT hrt1
  obtain ⟨y2, h2⟩ := hCol T hT hrt2
  obtain ⟨y3, h3⟩ := hImg T hT hrt3
  obtain ⟨y4, h4⟩ := hS T hT hC hrt4
  obtain ⟨y5, h5⟩ := hGr₀ T hT
  obtain ⟨y6, h6⟩ := hCfg₀ T hT
  refine ⟨max (max (max y1 y2) (max y3 y4)) (max (max y5 y6) T.yC), fun y hy => ?_⟩
  intro R hOn hF hx n m _ _ V U q o g hb hull hΦ hrm hmn hdis hUc hUg A M f hA hf
  have e1 : y1 ≤ y := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hy
  have e2 : y2 ≤ y := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hy
  have e3 : y3 ≤ y := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hy
  have e4 : y4 ≤ y := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hy
  have e5 : y5 ≤ y := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hy
  have e6 : y6 ≤ y := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hy
  have e7 : T.yC ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  have eL : R.params.side = T.side := by rw [hOn.params_eq]; rfl
  have eσ : R.params.threshold = T.threshold := by rw [hOn.params_eq]; rfl
  have en₀ : R.params.n₀ = T.n₀ := by rw [hOn.params_eq]; rfl
  have ea : R.params.coupling = T.coupling := by rw [hOn.params_eq]; rfl
  have hfit := hF.admissible
  have hodd := hfit.L_odd
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hm₀def : R.frameReach = R.range / 2048 := rfl
  have hrb := hF.range_ge_side
  have hrf := hF.range_ge_base
  have hrg := hF.nextRange_ge
  have hra := hF.range_le
  have hn₀L : R.params.n₀ ≤ n := le_trans (Nat.le_mul_of_pos_left _ hLpos) hb.2
  have hrL : 2 ^ 40 ≤ R.range := by
    have : 2 ^ 40 * 1 ≤ 2 ^ 40 * R.params.side := Nat.mul_le_mul_left _ hLpos
    omega
  have hm₀pos : 0 < R.frameReach := by
    rw [hm₀def]
    omega
  have hm₀r : R.frameReach ≤ R.range := by
    rw [hm₀def]
    exact Nat.div_le_self _ _
  have hmr : 4096 * R.range ≤ m := by
    have : (2 : ℕ) ^ 12 = 4096 := by norm_num
    omega
  have hn2 : 2 ≤ n := by omega
  have h4m : 2 ≤ 4 * m := by omega
  have hmpos : 0 < m := by omega
  have hσ0 : 0 < R.params.threshold := hfit.σ_pos
  obtain ⟨_, _, _, hρA0, hρA1, _⟩ := hT.chain
  have hρA0' : 0 ≤ R.anchorRadius := by rw [hOn.anchorRadius_eq]; exact hρA0.le
  have hρA1' : R.anchorRadius ≤ 1 := by rw [hOn.anchorRadius_eq]; exact hρA1
  have hρ1 : R.ballRadius ≤ 1 := by
    unfold StepSettings.StepSetup.ballRadius
    rw [eσ]
    have := hT.σ_one
    linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hf.abs_le (TorusFields.trivialField _) ∅)
  set Z : Finset (TorusFields.TorusBond (n * R.params.side)) :=
    MarkedIntegrals.chartBondsInBlocks R.params.side (ResponseInTheExpansion.supBall o ((m : ℝ) / 8)) with hZdef
  set k : ℕ := m / 8 with hkdef
  have hk1 : 1 ≤ k := by omega
  have hkr : (k : ℝ) ≤ (m : ℝ) / 8 := Nat.cast_div_le
  have hkm : k ≤ m - R.frameReach - 1 := by omega
  have hFm : ∀ U' : TorusFields.TorusField n, Measurable fun e : ↥Z × Fin 3 → ℝ =>
      f ((StepSettings.coldChartSetting R U').field (liftCoords U' Z e)) ∅ := fun U' =>
    (hf.measurable ∅).comp ((ClusterExpansionOfAStep.ChartSetting.measurable_field _).comp (measurable_liftCoords U' Z))
  have hFB : ∀ (U' : TorusFields.TorusField n) (e : ↥Z × Fin 3 → ℝ),
      |f ((StepSettings.coldChartSetting R U').field (liftCoords U' Z e)) ∅| ≤ M :=
    fun U' e => hf.abs_le _ _
  have hZ' : ∀ b ∈ Z, b ∈ StepCosts.chartBonds R.params.side n ∧
      TorusFields.supDist (TorusLumps.parentBlock R.params.side b.1) o ≤ (m - R.frameReach - 1) / 4 := by
    intro b hb'
    obtain ⟨h1', h2'⟩ := Finset.mem_filter.mp hb'
    refine ⟨h1', ?_⟩
    have h3' := (Finset.mem_filter.mp h2').2
    have h4' : 8 * TorusFields.supDist (TorusLumps.parentBlock R.params.side b.1) o ≤ m := by
      have : (8 : ℝ) * (TorusFields.supDist (TorusLumps.parentBlock R.params.side b.1) o : ℝ) ≤ m := by linarith
      exact_mod_cast this
    omega
  have hr' : (R.range : ℝ) / (4 * T.side) ≤ ((m - R.frameReach - 1 : ℕ) : ℝ) := by
    have hTL : (1 : ℝ) ≤ 4 * T.side := by
      rw [← eL]
      have : (1 : ℝ) ≤ R.params.side := by exact_mod_cast hLpos
      linarith
    have h5' : (R.range : ℝ) / (4 * T.side) ≤ R.range := div_le_self (Nat.cast_nonneg _) hTL
    have h6' : R.range ≤ m - R.frameReach - 1 := by omega
    have h7' : (R.range : ℝ) ≤ ((m - R.frameReach - 1 : ℕ) : ℝ) := by exact_mod_cast h6'
    linarith
  have hTn : T.n₀ ≤ n := en₀ ▸ hn₀L
  have hTm : T.n₀ ≤ 4 * m := by
    rw [← en₀]
    omega
  have hcase : |WeightedResponses.caseMean R (StepSettings.hotCoreSites R V) V q (fun W Yt _ _ _ => f W Yt) -
      ResponseInTheExpansion.reflectedStepMean R m o V (fun κ => f ((StepSettings.coldChartSetting R V).field
        (liftCoords V Z (ResponseInTheExpansion.imaginaryComponentsOn Z (ResponseInTheExpansion.reflectedCoordinateAt R.params.side R.depth m o κ))))
          ∅)| ≤
      2 * M * Real.exp (-(T.rt * ((m - R.frameReach - 1 : ℕ) : ℝ) / 2 ^ 3)) +
        2 * M * (ResponseInTheExpansion.blocksNearFreeCores R.params.side R.range (ResponseInTheExpansion.supBall o m)).card *
          Real.exp (-(7 * T.gasRate * R.coupling)) := by
    have hot := h5 y e5 R hOn hF n hb V q hull hΦ
    have hG : (StepGas.hotCaseGround R V q).IsAdmissibleGround := Or.inr hot
    have cols := fun off => h2 y e2 R hOn hx n (StepGas.hotCaseGround R V q) hG off
    obtain ⟨hNM, hxi, -, hratio, hbounds⟩ := hRat R n (StepGas.hotCaseGround R V q) T.gasRate cols
    obtain ⟨-, -, -, hmass, -⟩ := h3 y e3 R hOn hx n (StepGas.hotCaseGround R V q) hG
    have hpart : (StepGas.hotCaseGround R V q).partitionFunction ∅ ≠ ⊤ := by
      intro ht
      have := hxi ∅
      unfold StepGas.GasGround.xi at this
      rw [ht] at this
      simp at this
    have hfin : StepSettings.coarseStateMass R (StepGas.hotCaseGround R V q).cut (StepGas.hotCaseGround R V q).coarse
        (StepGas.hotCaseGround R V q).state ≠ ⊤ := by
      rw [hmass]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hpart
    have hborel : ∀ (Yt : Finset (TorusFields.TorusSite (n * R.params.side))) (bad : Finset (TorusFields.TorusBond (n * R.params.side)))
        (b : StepCosts.BaseChoice R.params.side n),
        Measurable fun p : TorusFields.TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
          (fun W Yt _ _ _ => f W Yt : WeightedResponses.CaseFunction R n) p.1 Yt p.2 bad b :=
      fun Yt _ _ => (hf.measurable Yt).comp measurable_fst
    have hkeeps : WeightedResponses.IsGaugeInvariantCase (R := R) (n := n) (fun W Yt _ _ _ => f W Yt) :=
      fun W Yt _ _ _ u _ _ _ => hf.gauge_invariant u W Yt
    have hint := hU R hF n hn₀L _ _ _ hfin (fun W Yt _ _ _ => f W Yt) M hborel (fun W Yt _ _ _ => hf.abs_le W Yt)
    obtain ⟨hae, hcm⟩ := h1 y e1 R hOn hx n (StepGas.hotCaseGround R V q) hG
    obtain ⟨hgi, hmean⟩ := hcm _ hborel hkeeps hint
    obtain ⟨hw, hsc⟩ := cols fun j => j.1.Touches ∅
    have hprob : IsProbabilityMeasure ((StepGas.hotCaseGround R V q).gibbsLaw ∅) := hsc.isProbabilityMeasure
    have hMB : |ResponseInTheExpansion.reflectedStepMean R m o V (fun κ => f ((StepSettings.coldChartSetting R V).field
        (liftCoords V Z (ResponseInTheExpansion.imaginaryComponentsOn Z (ResponseInTheExpansion.reflectedCoordinateAt R.params.side R.depth m o κ))))
          ∅)| ≤ M := by
      unfold ResponseInTheExpansion.reflectedStepMean ColdStepAtMirrorFrames.cutoffMean
      exact abs_ratio_integral_le (fun a => mul_nonneg (Finset.prod_nonneg fun _ _ => cutoffFactor_nonneg _ _ _) (Real.exp_pos _).le)
        (fun a => hFB V _) hM0
    show |WeightedResponses.caseMean R (StepGas.hotCaseGround R V q).cut (StepGas.hotCaseGround R V q).coarse
      (StepGas.hotCaseGround R V q).state (fun W Yt _ _ _ => f W Yt) - _| ≤ _
    rw [hmean]
    unfold WeightedResponses.gasExpectationOfCase StepGas.GasGround.expectation
    refine abs_integral_sub_le_of_good hgi (ResponseInTheExpansion.blocksNearFreeCores R.params.side R.range (ResponseInTheExpansion.supBall o m))
      (StepGas.hotCaseGround R V q).NoSpinMeets hNM (fun Y _ => ?_) ?_ ?_ hMB (by positivity) hM0
    · rw [hratio ∅ Y]
      exact (hbounds ∅ Y).1
    · filter_upwards [hae] with σ hσ' hσ
      have hset := h6 y e6 R hOn hx n (StepGas.hotCaseGround R V q) hG σ hσ'.1
      obtain ⟨hcold, hagree⟩ := hQ R n m V q ((StepGas.hotCaseGround R V q).familyOf σ) o hfit hn2 hb.1 (by omega) hm₀pos (by omega)
        (by omega) (by omega) hull hdis (fun θ hθ => disjoint_core_of_quiet hσ hθ)
      rw [eσ] at hcold
      have hag := settingsAgree_cold_of_mirror hodd hn2 h4m hagree
      have hread : (StepSettings.weightedMean (WeightedResponses.chartDensity
            (WeightedResponses.configSetting (StepGas.hotCaseGround R V q) σ)) fun η =>
          f ((WeightedResponses.configSetting (StepGas.hotCaseGround R V q) σ).field η)
            (WeightedResponses.configSetting (StepGas.hotCaseGround R V q) σ).support) =
          StepSettings.weightedMean (WeightedResponses.chartDensity (WeightedResponses.configSetting (StepGas.hotCaseGround R V q) σ))
            fun η => f ((StepSettings.coldChartSetting R V).field (liftCoords V Z (ResponseInTheExpansion.imaginaryComponentsOn Z
              (StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach V
                ((WeightedResponses.configSetting (StepGas.hotCaseGround R V q) σ).field η))))) ∅ :=
        weightedMean_congr fun η hd => reads_eq_of_agree hkr hkm hfit hn2 hρA0' hρA1' hρ1 hset.subset_chart hk1 hag
          (inBalls_of_chartDensity_ne_zero _ hd) hA hf _ (fun _ _ hz => hz)
      show |(StepSettings.weightedMean (WeightedResponses.chartDensity
            (WeightedResponses.configSetting (StepGas.hotCaseGround R V q) σ)) fun η =>
          f ((WeightedResponses.configSetting (StepGas.hotCaseGround R V q) σ).field η)
            (WeightedResponses.configSetting (StepGas.hotCaseGround R V q) σ).support) - _| ≤ _
      rw [hread]
      exact h4 y e4 R hOn n m (m - R.frameReach - 1) (WeightedResponses.configSetting (StepGas.hotCaseGround R V q) σ) o hTn hTm hset
        hcold hagree hr' Z _ M hZ' (hFm V) (hFB V)
    · refine Filter.Eventually.of_forall fun σ => ?_
      unfold StepSettings.weightedMean
      exact abs_ratio_integral_le (chartDensity_nonneg _) (fun η => hf.abs_le _ _) hM0
  have hcoldU : TorusFields.IsCold (9 / 8 * R.params.threshold) U := fun x μ ν h => (hUc x μ ν h).trans_le (by linarith)
  have hnohot : TorusLumps.torusHotSites R.params U = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨l, hl, -⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨x, μ, ν, hlt, hge, -⟩ := (TorusLumps.mem_torusHotLumps_iff R.params hfit hb.1 U l).mp hl
    exact absurd (hUc x μ ν hlt) (not_lt.mpr hge)
  have hwithin : ∀ r : ℕ, TorusLumps.thickening r (∅ : Finset (TorusFields.TorusSite n)) = ∅ := fun r => by
    refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨w, hw, -⟩ := (TorusFields.mem_thickening _ _ _).mp hz
    exact absurd hw (Finset.notMem_empty _)
  have hG0 : StepGas.hotCaseGround R U (StepGas.emptyCoarseState R) = coldGroundOver R U := by
    unfold StepGas.hotCaseGround coldGroundOver StepSettings.hotCoreSites HoledShares.coldRegion
    rw [hnohot, hwithin, hwithin]
    simp
  have hull0 : TorusLumps.IsHullState R.params R.nextRange U (StepGas.emptyCoarseState R (n := n)).1 := by
    refine ⟨?_, fun X hX => ?_⟩
    · rw [hnohot, hwithin]
      exact Finset.Subset.refl _
    · simp [TorusLumps.chainComponents, StepGas.emptyCoarseState] at hX
  obtain ⟨hcm0, hag0⟩ := hQ R n m U (StepGas.emptyCoarseState R) StepGas.GasFamily.empty o hfit hn2 hb.1 (by omega) hm₀pos
    (by omega) (by omega) (by omega)
    hull0 (Finset.disjoint_empty_left _) (fun θ hθ => by simp [StepGas.GasFamily.Occupies, StepGas.GasFamily.empty] at hθ)
  rw [hG0] at hag0
  rw [eσ] at hcm0
  have hset0 : (coldSettingOver R U).IsAdmissible := by
    have h := h6 y e6 R hOn hx n (coldGroundOver R U) (Or.inl ⟨hn₀L, hcoldU, rfl, rfl, rfl⟩) (coldGroundOver R U).allVacant
      (fun i j _ => Or.inl rfl)
    rw [familyOf_allVacant] at h
    exact h
  have hag1 := settingsAgree_cold_of_mirror (s := coldSettingOver R U) hodd hn2 h4m hag0
  have hread0 : coldExpectation R U (fun η => f ((coldSettingOver R U).field η) ∅) =
      StepSettings.weightedMean (WeightedResponses.chartDensity (coldSettingOver R U)) fun η =>
        f ((StepSettings.coldChartSetting R U).field (liftCoords U Z (ResponseInTheExpansion.imaginaryComponentsOn Z
          (StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach U ((coldSettingOver R U).field η))))) ∅ :=
    weightedMean_congr fun η hd => reads_eq_of_agree hkr hkm hfit hn2 hρA0' hρA1' hρ1 hset0.subset_chart hk1 hag1
      (inBalls_of_chartDensity_ne_zero _ hd) hA hf _ (fun _ _ hz => absurd hz (Finset.notMem_empty _))
  have hcold' : |(StepSettings.weightedMean (WeightedResponses.chartDensity (coldSettingOver R U)) fun η =>
        f ((StepSettings.coldChartSetting R U).field (liftCoords U Z (ResponseInTheExpansion.imaginaryComponentsOn Z
          (StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach U ((coldSettingOver R U).field η))))) ∅) -
      ResponseInTheExpansion.reflectedStepMean R m o U (fun κ => f ((StepSettings.coldChartSetting R U).field
        (liftCoords U Z (ResponseInTheExpansion.imaginaryComponentsOn Z (ResponseInTheExpansion.reflectedCoordinateAt R.params.side R.depth m o κ))))
          ∅)| ≤
      2 * M * Real.exp (-(T.rt * ((m - R.frameReach - 1 : ℕ) : ℝ) / 2 ^ 3)) :=
    h4 y e4 R hOn n m (m - R.frameReach - 1) (coldSettingOver R U) o hTn hTm hset0 hcm0 hag0 hr' Z _ M hZ' (hFm U) (hFB U)
  have hFF : R.ColdChainFits := by
    have hchain : ColdChain.ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
      rw [ea, eL, hOn.anchorRadius_eq]
      exact hT.chain
    exact ⟨T.δ₁, T.lam, T.σA, T.cg, T.N, hchain, by rw [eσ]; exact hT.σ_le, by rw [eσ]; exact hT.σ_one⟩
  have hcoldV : ResponseInTheExpansion.IsColdOnBall R.params.threshold V o m := by
    intro p hp
    obtain ⟨hlt, hcorn⟩ := (Finset.mem_filter.mp hp).2
    by_contra hge
    push Not at hge
    have hl : TorusLumps.torusLumpOf R.params p.1 ∈ TorusLumps.torusHotLumps R.params V :=
      (TorusLumps.mem_torusHotLumps_iff R.params hfit hb.1 V _).mpr
        ⟨p.1, p.2.1, p.2.2, hlt, hge, p.1, by simp [TorusFields.plaquetteVertices], rfl⟩
    have hz : p.1 ∈ TorusLumps.torusHotSites R.params V :=
      Finset.mem_biUnion.mpr ⟨_, hl, TorusLumps.mem_torusLumpOf_self _⟩
    have hq1 : p.1 ∈ q.1 := hull.1 ((TorusFields.mem_thickening _ _ _).mpr ⟨_, hz, by simp [TorusFields.supDist_self]⟩)
    exact Finset.disjoint_left.mp hdis hq1 (hcorn _ (by simp [TorusFields.plaquetteVertices]))
  have hc1 : ColdStepAtMirrorFrames.IsSmallCurvature R.params.threshold
      (ResponseInTheExpansion.reflectedTopField R.params.side R.depth m o V) := by
    have h := hCold R.params.side R.depth m n o V (fun _ => 1) R.params.threshold hσ0 hmpos (by omega) hodd hcoldV
    have e : TorusFields.gaugeTransform (fun _ => (1 : BlockAverages.UnitQuaternion)) V = V := by
      funext x i
      simp [TorusFields.gaugeTransform]
    rwa [e] at h
  have hblk : ∀ z ∈ A, TorusFields.supDist (TorusLumps.parentBlock R.params.side z) o ≤ k := by
    intro z hz
    have h1' := hA z hz
    obtain ⟨h, oo, ho, hh, rfl⟩ := exists_index_of_site hodd o z (k := k) (by omega)
    have := parentBlock_supDist_le hodd o hh ho
    exact_mod_cast this
  have hmirror : ResponseInTheExpansion.reflectedStepMean R m o U (fun κ => f ((StepSettings.coldChartSetting R U).field
        (liftCoords U Z (ResponseInTheExpansion.imaginaryComponentsOn Z (ResponseInTheExpansion.reflectedCoordinateAt R.params.side R.depth m o κ))))
          ∅) =
      ResponseInTheExpansion.reflectedStepMean R m o V (fun κ => f ((StepSettings.coldChartSetting R V).field
        (liftCoords V Z (ResponseInTheExpansion.imaginaryComponentsOn Z (ResponseInTheExpansion.reflectedCoordinateAt R.params.side R.depth m o κ))))
          ∅) := by
    have e1 : ResponseInTheExpansion.reflectedTopField R.params.side R.depth m o U =
        ResponseInTheExpansion.reflectedTopField R.params.side R.depth m o (TorusFields.gaugeTransform g V) :=
      reflectedTopField_congr hMir.1 hmpos o _ _ fun c a b => hUg c a b
    have e2 := reflectedTopField_gaugeTransform (L := R.params.side) hMir.2.1 (t := R.depth) hmpos o g V
    unfold ResponseInTheExpansion.reflectedStepMean
    rw [e1, e2, cutoffMean_reflected_gauge hCar hRB hT hC2 e7 hOn hfit (by omega) o V hc1]
    congr 1
    funext κ
    refine read_eq_of_gauge (g := g) hf _ _ (fun c hc h => ?_) (fun c hc h => ?_) (fun c hc hs => ?_)
    · have hd := hblk c.1 hc
      have hcZ : c ∈ Z := Finset.mem_filter.mpr ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        le_trans (by exact_mod_cast hd) hkr⟩⟩
      rw [toImaginary_liftCoords U Z _ ⟨c, h⟩ hcZ, toImaginary_liftCoords V Z _ ⟨c, h⟩ hcZ]
      have hi : ∀ i, |(TorusLumps.parentBlock R.params.side c.1 i - o i).valMinAbs| ≤ (k : ℤ) := fun i => by
        have := (TorusFields.supDist_le_iff _ _ _).mp hd i
        rw [Int.abs_eq_natAbs]
        exact_mod_cast this
      refine reflectedCoordinateAt_adjoint hodd hmpos o g κ c (fun i => (hi i).trans (by exact_mod_cast (by omega : k ≤ m))) fun i => ?_
      have h5 := hi i
      have h6' : 2 * (k : ℤ) + 1 < n := by
        have : 2 * k + 1 < n := by omega
        exact_mod_cast this
      omega
    · have hd := hblk c.1 hc
      refine frameCoord_gaugeTransform hFr hFg hF hFF hb hUg hm₀pos (by omega) c h (by omega) fun hC => ?_
      have hq1 := hull.1 hC
      refine Finset.disjoint_left.mp hdis hq1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      exact_mod_cast (by omega : TorusFields.supDist (TorusLumps.parentBlock R.params.side c.1) o ≤ m)
    · have hd := hblk c.1 hc
      have hy0 : TorusFields.supDist (TorusLumps.parentBlock R.params.side c.1) o + 1 ≤ m := by omega
      have i1 : TorusLumps.parentBlock R.params.side c.1 ∈ ResponseInTheExpansion.supBall o m := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact_mod_cast (by omega : TorusFields.supDist (TorusLumps.parentBlock R.params.side c.1) o ≤ m)
      have i2 : TorusLumps.parentBlock R.params.side c.1 + TorusFields.unitStep n c.2 ∈ ResponseInTheExpansion.supBall o m := by
        rw [TorusLumps.unitStep_eq_siteOfInt]
        refine add_siteOfInt_mem_supBall hy0 fun i => ?_
        by_cases h : i = c.2
        · subst h
          simp
        · simp [h]
      exact hUg (TorusLumps.parentBlock R.params.side c.1, c.2) i1 i2
  rw [hread0]
  rw [hmirror] at hcold'
  have t := abs_sub_le (WeightedResponses.caseMean R (StepSettings.hotCoreSites R V) V q (fun W Yt _ _ _ => f W Yt))
    (ResponseInTheExpansion.reflectedStepMean R m o V (fun κ => f ((StepSettings.coldChartSetting R V).field
      (liftCoords V Z (ResponseInTheExpansion.imaginaryComponentsOn Z (ResponseInTheExpansion.reflectedCoordinateAt R.params.side R.depth m o κ))))
        ∅))
    (StepSettings.weightedMean (WeightedResponses.chartDensity (coldSettingOver R U)) fun η =>
        f ((StepSettings.coldChartSetting R U).field (liftCoords U Z (ResponseInTheExpansion.imaginaryComponentsOn Z
          (StepMarks.frameDeviation R.params R.anchorRadius R.depth R.frameReach U ((coldSettingOver R U).field η))))) ∅)
  rw [abs_sub_comm (ResponseInTheExpansion.reflectedStepMean R m o V _)] at t
  linarith
end YangMills.Construction.MomentLaw
end
