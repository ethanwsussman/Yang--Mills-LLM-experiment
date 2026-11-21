import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.LumpsOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.ColdChainAtEveryLevel.ChartsChainsAndShares
import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import YangMills.Construction.ColdStepAtMirrorFrames.TreeResponseOfTheLeastCoordinates
import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import YangMills.Construction.ClusterExpansionOfAStep.ChainOnATorus
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import YangMills.Construction.ResponseInTheExpansion.FieldsOfOneColour
import YangMills.Construction.RunningCouplingSlope.StepTotalsHaveCoefficientsProof
import YangMills.Construction.SummableBoundsOfTheFlow.ChainResponsesAreMixedResponses
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.LevelComparisons
variable {L n : ℕ} [NeZero L] [NeZero n]
private theorem isAxialTreeBond_of_not_mem_chartBonds {b : TorusFields.TorusBond (n * L)}
    (hb : b ∉ StepCosts.chartBonds L n) :
    BlockAverages.IsAxialTreeBond (F := TorusLumps.stepBlockFrame L n)
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 0 b.1, b.2) := by
  classical
  by_contra h
  exact hb (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)

private theorem isAxialTreeBond_torusFrame_iff (hL : Odd L) (hn : 2 ≤ n) (u : ℕ)
    (x : TorusFields.TorusSite (n * L)) (i : Fin 4) :
    BlockAverages.IsAxialTreeBond (F := TorusFields.torusFrame L u n)
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).depth x, i) ↔
      BlockAverages.IsAxialTreeBond (F := TorusLumps.stepBlockFrame L n)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame L n) 0 x, i) := by
  have : NeZero (n * (TorusFields.torusFrame L u n).blockSide) := inferInstanceAs (NeZero (n * L))
  have : NeZero (n * (TorusLumps.stepBlockFrame L n).blockSide) := inferInstanceAs (NeZero (n * L))
  have h1 := TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := TorusFields.torusFrame L u n) (n := n)
    (fun _ => rfl) hL hn x i
  have h2 := TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := TorusLumps.stepBlockFrame L n) (n := n)
    (fun _ => rfl) hL hn x i
  exact h1.trans h2.symm

theorem responseKernel_vanishes_off_chart (hL : Odd L) (hn : 2 ≤ n) (a ρA : ℝ) (u : ℕ)
    {b : TorusFields.TorusBond (n * L)} (c : TorusFields.TorusBond n)
    (hb : b ∉ StepCosts.chartBonds L n) : WeightedResponses.responseKernel a ρA L u b c = 0 := by
  classical
  have ht := (isAxialTreeBond_torusFrame_iff hL hn u b.1 b.2).2 (isAxialTreeBond_of_not_mem_chartBonds hb)
  have hw : (ColdStepAtMirrorFrames.torusCoordinate a ρA
      (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).depth b.1, b.2) :
      (TorusFields.torusFrame L u n).GaugeField (TorusFields.torusFrame L u n).top →
        BlockAverages.imaginaryQuaternions) = fun _ => 0 := by
    funext V
    unfold ColdStepAtMirrorFrames.torusCoordinate BlockAverages.minimizingBondCoordinate
      BlockAverages.minimizingCoordinates
    split_ifs with h
    · refine h.choose_spec.1
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame L u n) (TorusFields.torusFrame L u n).depth b.1, b.2)
        fun hm => ?_
      exact (Finset.mem_filter.1 hm).2 ht
    · rfl
  unfold WeightedResponses.responseKernel ColdStepAtMirrorFrames.minimizerResponse
  rw [hw, if_neg (fun h => ht.1 h.1)]
  unfold ColdStepAtMirrorFrames.bondDeriv
  simp

private theorem norm_unitGenerator : ‖(WeightedResponses.unitGenerator : Quaternion ℝ)‖ = 1 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SingleColourFields.norm_unitGenerator <;> assumption
private theorem abs_re_le_norm_quaternion (q : Quaternion ℝ) : |q.re| ≤ ‖q‖ := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.quaternion_abs_re_le_norm <;> assumption
private theorem abs_responseKernel_le (T : ColdStepAtMirrorFrames.StepParameters) [NeZero T.L] (hT : T.IsOrdered)
    (u n : ℕ) [NeZero n] (hn : 64 ≤ n) (c : TorusFields.TorusBond n) (b : TorusFields.TorusBond (n * T.L)) :
    |WeightedResponses.responseKernel T.a T.ρA T.L u b c| ≤
      (T.chainParams.Kk 1 + 1) * Real.exp (-(T.chainParams.κ₂ * TwoLevelMixtures.bondSiteDist T.L b c.1)) := by
  classical
  obtain ⟨⟨-, -, hs0, -, -, -, -, hKk⟩, hcl⟩ := hT.chain_admissible.classical
  have hp : ∀ i, (TorusFields.torusFrame T.L u n).period (TorusFields.torusFrame T.L u n).top i = n :=
    fun i => TopLevelSites.period_top i
  have hcold : ColdStepAtMirrorFrames.IsSmallCurvature T.chainParams.s₀
      (ColdStepAtMirrorFrames.uniformField (TorusFields.torusFrame T.L u n) (TorusFields.torusFrame T.L u n).top) := by
    intro p _
    simpa [BlockAverages.plaquetteDefect, BlockAverages.plaquetteHolonomy, BlockAverages.pathHolonomy,
      BlockAverages.linkValue, ColdStepAtMirrorFrames.uniformField] using hs0
  have hdec := (hcl (TorusFields.torusFrame T.L u n) T.chainParams.s₀ _ ⟨rfl, n, hn, fun _ => rfl⟩ hs0 le_rfl
    hcold).2.2.1
  set x := StepCosts.torusSiteInFrame (TorusFields.torusFrame T.L u n) (TorusFields.torusFrame T.L u n).depth b.1
    with hx
  set c' : (TorusFields.torusFrame T.L u n).Site (TorusFields.torusFrame T.L u n).top × Fin 4 :=
    (StepCosts.torusSiteInFrame (TorusFields.torusFrame T.L u n) (TorusFields.torusFrame T.L u n).top c.1, c.2)
    with hc'
  have hcell : BlockAverages.enclosingCell x = StepCosts.torusSiteInFrame (TorusFields.torusFrame T.L u n)
      (TorusFields.torusFrame T.L u n).top (TorusLumps.parentBlock T.L b.1) := by
    have : NeZero (n * (TorusFields.torusFrame T.L u n).blockSide) := inferInstanceAs (NeZero (n * T.L))
    exact TopLevelSites.enclosingCell_torusSiteInFrame (F := TorusFields.torusFrame T.L u n) (n := n)
      (fun _ => rfl) b.1
  have hdist : BlockAverages.bondListDistance (BlockAverages.enclosingCell x) ![c'] =
      TwoLevelMixtures.bondSiteDist T.L b c.1 := by
    unfold BlockAverages.bondListDistance TwoLevelMixtures.bondSiteDist
    simp only [Finset.univ_unique, Finset.sup_singleton]
    show BlockAverages.cellSupDist (BlockAverages.enclosingCell x)
      (StepCosts.torusSiteInFrame (TorusFields.torusFrame T.L u n) (TorusFields.torusFrame T.L u n).top c.1) = _
    rw [hcell]
    exact TorusChain.cellSupDist_torusSiteInFrame hp _ _
  have hunit : BlockAverages.AreUnitVectors ![WeightedResponses.unitGenerator] := by
    intro l
    have : ‖WeightedResponses.unitGenerator‖ = 1 := norm_unitGenerator
    fin_cases l
    simpa using this
  set dv : BlockAverages.imaginaryQuaternions := ColdStepAtMirrorFrames.bondDeriv
    (ColdStepAtMirrorFrames.torusCoordinate (F := TorusFields.torusFrame T.L u n) T.a T.ρA (x, b.2))
    (ColdStepAtMirrorFrames.uniformField (TorusFields.torusFrame T.L u n) (TorusFields.torusFrame T.L u n).top)
    ![c'] ![WeightedResponses.unitGenerator] with hdv
  set E := Real.exp (-(T.chainParams.κ₂ * TwoLevelMixtures.bondSiteDist T.L b c.1)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hK : 0 < T.chainParams.Kk 1 := hKk 1
  have hnorm : ‖dv‖ ≤ T.chainParams.Kk 1 * E := by
    by_cases hb : (x, b.2) ∈ BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame T.L u n))
    · have := hdec _ hb 1 ![c'] ![WeightedResponses.unitGenerator] le_rfl hunit
      rw [hdist] at this
      exact this
    · have hw : (ColdStepAtMirrorFrames.torusCoordinate (F := TorusFields.torusFrame T.L u n) T.a T.ρA (x, b.2) :
          (TorusFields.torusFrame T.L u n).GaugeField (TorusFields.torusFrame T.L u n).top →
            BlockAverages.imaginaryQuaternions) = fun _ => 0 := by
        funext V
        unfold ColdStepAtMirrorFrames.torusCoordinate BlockAverages.minimizingBondCoordinate
          BlockAverages.minimizingCoordinates
        split_ifs with h
        · exact h.choose_spec.1 _ hb
        · rfl
      have h0 : dv = 0 := by
        rw [hdv, hw]
        unfold ColdStepAtMirrorFrames.bondDeriv
        simp
      rw [h0, norm_zero]
      positivity
  have hre : |(((dv : BlockAverages.imaginaryQuaternions) : Quaternion ℝ) *
      ((WeightedResponses.unitGenerator : BlockAverages.imaginaryQuaternions) : Quaternion ℝ)).re| ≤
      T.chainParams.Kk 1 * E := by
    refine le_trans (abs_re_le_norm_quaternion _) ?_
    rw [norm_mul, norm_unitGenerator, mul_one]
    exact hnorm
  have hind : |(if BlockAverages.IsCrossingBond (x, b.2) ∧ BlockAverages.enclosingCell x = c'.1 ∧ b.2 = c'.2
      then (1 : ℝ) else 0)| ≤ E := by
    split_ifs with h
    · have h0 : TwoLevelMixtures.bondSiteDist T.L b c.1 = 0 := by
        rw [← hdist]
        unfold BlockAverages.bondListDistance
        simp only [Finset.univ_unique, Finset.sup_singleton]
        show BlockAverages.cellSupDist (BlockAverages.enclosingCell x) c'.1 = 0
        rw [h.2.1]
        exact TopLevelSites.cellSupDist_self _
      rw [hE, h0]
      simp
    · simpa using hE0.le
  unfold WeightedResponses.responseKernel ColdStepAtMirrorFrames.minimizerResponse
  show |-(((dv : BlockAverages.imaginaryQuaternions) : Quaternion ℝ) *
      ((WeightedResponses.unitGenerator : BlockAverages.imaginaryQuaternions) : Quaternion ℝ)).re +
    (if BlockAverages.IsCrossingBond (x, b.2) ∧ BlockAverages.enclosingCell x = c'.1 ∧ b.2 = c'.2
      then (1 : ℝ) else 0)| ≤ _
  calc _ ≤ |-(((dv : BlockAverages.imaginaryQuaternions) : Quaternion ℝ) *
          ((WeightedResponses.unitGenerator : BlockAverages.imaginaryQuaternions) : Quaternion ℝ)).re| +
        |(if BlockAverages.IsCrossingBond (x, b.2) ∧ BlockAverages.enclosingCell x = c'.1 ∧ b.2 = c'.2
          then (1 : ℝ) else 0)| := abs_add_le _ _
    _ ≤ T.chainParams.Kk 1 * E + E := by
        rw [abs_neg]
        exact add_le_add hre hind
    _ = _ := by ring
private theorem eventuallyOrdered_of_forall {P : ColdStepAtMirrorFrames.StepParameters → Prop}
    (h : ∀ T : ColdStepAtMirrorFrames.StepParameters, T.IsOrdered → 1 ≤ T.n₀ → P T) :
    ColdStepAtMirrorFrames.EventuallyOrdered P := by
  intro a _
  exact ⟨0, fun L _ _ c _ => ⟨0, fun Ct _ => ⟨1, one_pos, fun κ _ _ => ⟨1, one_pos, fun η₃ _ _ _ => ⟨0, fun b _ =>
    ⟨1, one_pos, fun σ _ _ p _ => ⟨0, fun Cs _ E _ => ⟨0, fun n₀ _ => ⟨0, fun CE _ => ⟨0, fun y₁ _ =>
      fun hT hn => h _ hT hn⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem responsesAreInterpResponses : responsesAreInterpResponsesStatement := by
  refine eventuallyOrdered_of_forall fun T hT _ => ?_
  intro _
  have hK : 0 < T.chainParams.Kk 1 := hT.chain_admissible.classical.1.2.2.2.2.2.2.2 1
  refine ⟨T.chainParams.Kk 1 + 1, by positivity, fun t n _ c hn => ?_⟩
  refine ⟨⟨fun b hb => ?_⟩, ⟨fun b hb => ?_⟩, fun b => abs_responseKernel_le T hT (t + 1) n hn c b⟩
  · exact responseKernel_vanishes_off_chart hT.odd_L (by omega) T.a T.ρA t c hb
  · exact responseKernel_vanishes_off_chart hT.odd_L (by omega) T.a T.ρA (t + 1) c hb

end YangMills.Construction.LevelComparisons
end
