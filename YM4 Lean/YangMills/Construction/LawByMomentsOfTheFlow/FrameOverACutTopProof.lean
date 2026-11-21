import YangMills.Construction.ColdStepAtMirrorFrames.MirrorFrameAgainstTheChain
import YangMills.Construction.LawByMomentsOfTheFlow.CoordinateOfAColdForm
import YangMills.Construction.LawByMomentsOfTheFlow.FrameOverACutTop
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheLogarithmsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MomentLaw
section FrameEvaluation
variable {P : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
private def restrictToFrame (F : BlockAverages.BlockFrame) (B : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) :
    F.Cell → Fin 4 → BlockAverages.imaginaryQuaternions :=
  fun z l => B (TorusLumps.toTorusSite n z, l)
open Classical in
private theorem responseOfLieForm_eq_flat_add_crossing (a r : ℝ) (u : ℕ) (hodd : Odd P.side) (htwo : 2 ≤ n)
    (B : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) (b : TorusFields.TorusBond (n * P.side)) :
    ResponseInTheExpansion.responseOfLieForm a r P.side u B b =
      WeightedResponses.flatLinearPart (F := TorusFields.torusFrame P.side u n) a r WeightedResponses.unitGenerator
          (StepCosts.torusSiteInFrame (TorusFields.torusFrame P.side u n) (TorusFields.torusFrame P.side u n).depth b.1, b.2)
          (restrictToFrame (TorusFields.torusFrame P.side u n) B) +
        (if BlockAverages.IsCrossingBond (F := TorusFields.torusFrame P.side u n)
            (StepCosts.torusSiteInFrame (TorusFields.torusFrame P.side u n) (TorusFields.torusFrame P.side u n).depth b.1, b.2)
          then B (TorusLumps.parentBlock P.side b.1, b.2) else 0) := by apply _root_.YangMills.DeltaSharedProofs.p502148 <;> assumption
end FrameEvaluation
section AxialBonds
variable {P : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
private theorem responseOfLieForm_eq_zero_of_axial (a r : ℝ) (u : ℕ) (hodd : Odd P.side) (htwo : 2 ≤ n)
    (B : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) {b : TorusFields.TorusBond (n * P.side)}
    (hb : b ∉ StepCosts.chartBonds P.side n) : ResponseInTheExpansion.responseOfLieForm a r P.side u B b = 0 := by apply _root_.YangMills.SharedProofs.p63547 <;> assumption
end AxialBonds
private theorem norm_unitGenerator : ‖WeightedResponses.unitGenerator‖ = 1 := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.norm_unitGenerator <;> assumption
private theorem valMinAbs_cast_sub {M N : ℕ} (h : M = N) (x y : ZMod N) :
    (((((x.cast : ℤ)) : ZMod M)) - ((((y.cast : ℤ)) : ZMod M))).valMinAbs = (x - y).valMinAbs := by
  subst h
  simp
section WeightedSizes
variable {P : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
private theorem decayWeightedNorm_restrictToFrame (κ : ℝ) (t : ℕ) (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions)
    (Y : TorusFields.TorusSite n) :
    MomentMethod.decayWeightedNorm (F := TorusFields.torusFrame P.side t n) (2 * κ)
      (StepCosts.torusSiteInFrame (TorusFields.torusFrame P.side t n) (TorusFields.torusFrame P.side t n).top Y)
      (restrictToFrame (TorusFields.torusFrame P.side t n) A) = MomentLaw.weightedFormSize κ Y A := by
  classical
  set F := TorusFields.torusFrame P.side t n with hFdef
  have hext : ∀ i, F.extent i = n := fun _ => rfl
  have hper := TopLevelSites.period_top_of_extent (F := F) hext
  unfold MomentMethod.decayWeightedNorm MomentLaw.weightedFormSize restrictToFrame
  rw [← TopLevelSites.cellsOfSites_univ hext]
  unfold TorusFields.cellsOfSites
  rw [Finset.sum_image (fun x _ y _ h => by
      have e := congrArg (TorusLumps.toTorusSite n)
        (show StepCosts.torusSiteInFrame F F.top x = StepCosts.torusSiteInFrame F F.top y from h)
      rwa [TopLevelSites.toTorusSite_torusSiteInFrame hper, TopLevelSites.toTorusSite_torusSiteInFrame hper] at e)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun l _ => ?_
  have hy : TorusLumps.toTorusSite n (StepCosts.torusSiteInFrame F F.top y) = y :=
    TopLevelSites.toTorusSite_torusSiteInFrame hper y
  have hdist : BlockAverages.cellSupDist (StepCosts.torusSiteInFrame F F.top Y) (StepCosts.torusSiteInFrame F F.top y) =
      TorusFields.supDist Y y := by
    unfold BlockAverages.cellSupDist TorusFields.supDist
    refine Finset.sup_congr rfl fun i _ => ?_
    have := valMinAbs_cast_sub (hper i) (Y i) (y i)
    exact congrArg Int.natAbs this
  change Real.exp (-(2 * κ / 2 * (BlockAverages.cellSupDist (StepCosts.torusSiteInFrame F F.top Y)
      (StepCosts.torusSiteInFrame F F.top y) : ℝ))) *
    ‖A (TorusLumps.toTorusSite n (StepCosts.torusSiteInFrame F F.top y), l)‖ =
      Real.exp (-(κ * (TorusFields.supDist Y y : ℝ))) * ‖A (y, l)‖
  rw [hdist, hy]
  congr 3
  ring
end WeightedSizes
theorem frameOverCutTop_holds (hcoord : MomentMethod.coldFormCoordinateStatement)
    (hmirror : ColdStepAtMirrorFrames.ReflectedFrameChainBounds)
    (hequiv : ColdStepAtMirrorFrames.chartEquivarianceStatement) : MomentLaw.frameOverCutTopStatement := by
  intro P c ha hodd hc
  obtain ⟨K₁, hK₁, hcoordAt⟩ := hcoord P.coupling P.side c hodd hc
  have hpos := hc.classical.1
  have hs₀ : 0 < c.s₀ := hpos.2.2.1
  have hK : 0 < c.K := hpos.2.2.2.2.2.1
  have hsσ : c.s₀ ≤ c.σA := by
    have := hc.inequalities.2.2.1
    linarith
  refine ⟨K₁ + 2 * c.K * c.s₀, by positivity, ?_⟩
  intro t m n _ A hm hbig hn64 hcold
  have htwo : 2 ≤ n := by omega
  refine ⟨fun b hb => responseOfLieForm_eq_zero_of_axial _ _ _ hodd htwo A hb, fun b hb => ?_⟩
  classical
  set F := TorusFields.torusFrame P.side t n with hFdef
  have hext : ∀ i, F.extent i = n := fun _ => rfl
  have hodd' : Odd F.blockSide := hodd
  have hext2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hext]; omega
  have hF : ColdStepAtMirrorFrames.IsBlockTorus P.side F := ⟨rfl, n, hn64, fun _ => rfl⟩
  have hper := TopLevelSites.period_top_of_extent (F := F) hext
  have hNZ : NeZero (n * F.blockSide) := (inferInstance : NeZero (n * P.side))
  have hNZs : NeZero (n * (TorusLumps.stepBlockFrame P.side n).blockSide) := (inferInstance : NeZero (n * P.side))
  set x := StepCosts.torusSiteInFrame F F.depth b.1 with hx
  set Y := TorusLumps.parentBlock P.side b.1 with hY
  have hcell : BlockAverages.enclosingCell x = StepCosts.torusSiteInFrame F F.top Y :=
    TopLevelSites.enclosingCell_torusSiteInFrame hext b.1
  have hnottree : ¬ BlockAverages.IsAxialTreeBond (x, b.2) := by
    intro h
    have h1 := (TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff hext hodd' htwo b.1 b.2).1 h
    have h3 : BlockAverages.IsAxialTreeBond (F := TorusLumps.stepBlockFrame P.side n)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame P.side n) (TorusLumps.stepBlockFrame P.side n).depth b.1, b.2) :=
      (TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := TorusLumps.stepBlockFrame P.side n) (fun _ => rfl) hodd htwo b.1 b.2).2 h1
    exact (Finset.mem_filter.mp hb).2 h3
  have hchord : (x, b.2) ∈ BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells F) :=
    (hequiv F P.coupling hodd' hext2).mem_chordBonds_of_not_tree _ hnottree
  set D : F.Cell → Fin 4 → BlockAverages.imaginaryQuaternions := restrictToFrame F A with hD
  have htranslate : ∀ u : ℝ, ColdStepAtMirrorFrames.leftTranslate (fun y i => u • D y i) (BlockAverages.flatTopField (F := F)) =
      TorusFields.readAtLevel F F.top (MomentLaw.expField u A) := by
    intro u
    funext z l
    simp only [ColdStepAtMirrorFrames.leftTranslate, BlockAverages.flatTopField, mul_one]
    rfl
  have hsmall : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ColdStepAtMirrorFrames.IsSmallCurvature c.s₀ (TorusFields.readAtLevel F F.top (MomentLaw.expField u A)) := by
    rintro u h0 h1 ⟨z, μ, ν⟩ hq
    rw [TopLevelSites.plaquetteDefect_readAtLevel_eq hper]
    exact hcold u h0 h1 _ μ ν hq
  have hsmallσ : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ColdStepAtMirrorFrames.IsSmallCurvature c.σA
      (ColdStepAtMirrorFrames.leftTranslate (fun y i => u • D y i) (BlockAverages.flatTopField (F := F))) := by
    intro u h0 h1 p hp
    rw [htranslate]
    exact (hsmall u h0 h1 p hp).trans_le hsσ
  have hunit : ColdStepAtMirrorFrames.leftTranslate D (BlockAverages.flatTopField (F := F)) =
      TorusFields.readAtLevel F F.top (MomentLaw.expField 1 A) := by
    have := htranslate 1
    simpa only [one_smul] using this
  obtain ⟨hw, hf⟩ := hcoordAt F (x, b.2) D WeightedResponses.unitGenerator hF hchord norm_unitGenerator hsmallσ
  rw [hunit] at hw
  have hnorm : MomentMethod.decayWeightedNorm c.δ₁ (BlockAverages.enclosingCell (x, b.2).1) D =
      MomentLaw.weightedFormSize (c.δ₁ / 2) Y A := by
    have := decayWeightedNorm_restrictToFrame (P := P) (c.δ₁ / 2) t A Y
    rw [show 2 * (c.δ₁ / 2) = c.δ₁ by ring] at this
    show MomentMethod.decayWeightedNorm c.δ₁ (BlockAverages.enclosingCell x) D = _
    rw [hcell]
    exact this
  rw [hnorm] at hw hf
  have hbounds := hmirror P.coupling P.side c ha hodd hc F m (4 / 5 * c.s₀)
    (TorusFields.readAtLevel F F.top (MomentLaw.expField 1 A)) hF hm (by positivity)
    (by linarith) (fun _ => hbig) (by
      have := hsmall 1 zero_le_one le_rfl
      intro p hp
      have h5 := this p hp
      linarith)
  have hdev := hbounds.deviation_le (x, b.2) hchord
  have hgap : ‖((StepCosts.frameCoord P c.ρA t m (MomentLaw.expField 1 A) b -
        ColdStepAtMirrorFrames.torusCoordinate P.coupling c.ρA (x, b.2)
          (TorusFields.readAtLevel F F.top (MomentLaw.expField 1 A)) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤
      2 * c.K * c.s₀ * Real.exp (-(c.δ₂ * m)) := by
    have e : StepCosts.frameCoord P c.ρA t m (MomentLaw.expField 1 A) b =
        ColdStepAtMirrorFrames.bondFrameCoord P.coupling c.ρA m (x, b.2)
          (TorusFields.readAtLevel F F.top (MomentLaw.expField 1 A)) := rfl
    rw [e]
    refine le_trans hdev ?_
    have h3 : 0 < Real.exp (-(c.δ₂ * m)) := Real.exp_pos _
    have : 2 * c.K * (4 / 5 * c.s₀) * Real.exp (-(c.δ₂ * m)) = 4 / 5 * (2 * c.K * c.s₀ * Real.exp (-(c.δ₂ * m))) := by ring
    rw [show ‖ColdStepAtMirrorFrames.frameDeviation P.coupling c.ρA m (x, b.2)
        (TorusFields.readAtLevel F F.top (MomentLaw.expField 1 A))‖ = _ from rfl] at *
    nlinarith [mul_pos (mul_pos hK hs₀) h3]
  have hcross : MomentLaw.crossingComponent P A b =
      if BlockAverages.IsCrossingBond (F := F) (x, b.2) then A (Y, b.2) else 0 := by
    unfold MomentLaw.crossingComponent
    have e1 := TopLevelSites.isCrossingBond_torusSiteInFrame_iff (F := TorusLumps.stepBlockFrame P.side n) (fun _ => rfl) hodd htwo b.1 b.2
    have e2 := TopLevelSites.isCrossingBond_torusSiteInFrame_iff (F := F) hext hodd' htwo b.1 b.2
    have e3 : BlockAverages.IsCrossingBond (F := TorusLumps.stepBlockFrame P.side n)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame P.side n) 0 b.1, b.2) ↔
          BlockAverages.IsCrossingBond (F := F) (x, b.2) :=
      e1.trans e2.symm
    simp only [e3]
    rfl
  have hresp := responseOfLieForm_eq_flat_add_crossing P.coupling c.ρA t hodd htwo A b
  have hsum : ResponseInTheExpansion.responseOfLieForm P.coupling c.ρA P.side t A b =
      WeightedResponses.flatLinearPart P.coupling c.ρA WeightedResponses.unitGenerator (x, b.2) D +
        MomentLaw.crossingComponent P A b := by
    rw [hresp, hcross]
  rw [hsum]
  set fs := WeightedResponses.flatLinearPart (F := F) P.coupling c.ρA WeightedResponses.unitGenerator (x, b.2) D with hfs
  set S := MomentLaw.weightedFormSize (c.δ₁ / 2) Y A with hS
  have hS0 : 0 ≤ S := by
    refine Finset.sum_nonneg fun e _ => by positivity
  have hexp : 0 ≤ Real.exp (-(c.δ₂ * m)) := (Real.exp_pos _).le
  constructor
  · have e : StepCosts.frameCoord P c.ρA t m (MomentLaw.expField 1 A) b + MomentLaw.crossingComponent P A b -
        (fs + MomentLaw.crossingComponent P A b) =
        (StepCosts.frameCoord P c.ρA t m (MomentLaw.expField 1 A) b -
          ColdStepAtMirrorFrames.torusCoordinate P.coupling c.ρA (x, b.2)
            (TorusFields.readAtLevel F F.top (MomentLaw.expField 1 A))) +
          (ColdStepAtMirrorFrames.torusCoordinate P.coupling c.ρA (x, b.2)
            (TorusFields.readAtLevel F F.top (MomentLaw.expField 1 A)) - fs) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 := hgap
    have h2' := hw
    change ‖_‖ ≤ _ at h1
    change ‖_‖ ≤ _ at h2'
    have h4 : 0 ≤ S ^ 2 := by positivity
    have h5 : 0 ≤ c.K * c.s₀ := by positivity
    nlinarith [mul_nonneg h4 h5, mul_nonneg h5 hexp]
  · have e : fs + MomentLaw.crossingComponent P A b - MomentLaw.crossingComponent P A b = fs := by abel
    rw [e]
    have h5 : 0 ≤ c.K * c.s₀ := by positivity
    nlinarith [mul_nonneg h5 hS0]
end YangMills.Construction.MomentLaw
end
