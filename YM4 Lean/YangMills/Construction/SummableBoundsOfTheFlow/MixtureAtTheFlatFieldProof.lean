import YangMills.Construction.RunningCouplingSlope.LeastActionIsWellAtTheTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceGoesUpALevelProof
import YangMills.Construction.ColdChainAtEveryLevel.FlatTopCostsNothing
import YangMills.Construction.ColdChainAtEveryLevel.TotalAtComplexCoordinatesProof
import YangMills.Construction.ColdStepAtMirrorFrames.AdjointOfTheGroup
import YangMills.Construction.ColdStepAtMirrorFrames.CompositesAtAPoint
import YangMills.Construction.ColdStepAtMirrorFrames.FitsAlongMoves
import YangMills.Construction.RunningCouplingSlope.LeastPointReadsTheChainProof
import YangMills.Construction.SummableBoundsOfTheFlow.KernelsOfTheChartEnergyAtEightRates
import YangMills.Construction.SummableBoundsOfTheFlow.MixtureAtTheFlatField
import YangMills.Construction.SummableBoundsOfTheFlow.MixtureEnergyIsAnalytic
import YangMills.Construction.SummableBoundsOfTheFlow.TheStepOverColdFieldsIsNearItsCutProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology ContDiff
namespace YangMills.Construction
open BlockAverages (BlockFrame UnitQuaternion imaginaryQuaternions PathStep expUnit pathHolonomy linkValue
  stepDisplacement siteOfCoords cellCentre siteCoords sitesOfCells mem_sitesOfCells innerBonds innerPlaquettes
  plaquetteHolonomy plaquetteDefect chordBonds chartedField minimalAction blockFit blockEnergy IsAxialTreeBond
  AreUnitVectors)
open BlockAverages.VariationRates (quaternion_abs_re_le_norm hasDerivAt_contourAverage contourAverageRate
  hasDerivAt_expUnit_smul expUnit_zero_smul holonomyRate)
open ColdStepAtMirrorFrames (ColdChainParameters ChartDirection SharePeriods IsBlockTorus IsSmallCurvature
  IsAdmissibleChartPoint restrictToTorus transferField uniformField pathSum shiftedCoords translatedTop directionCell
  directionCoordinate directionDiameter directionVector directionMove finiteCells chartRestriction chartedEnergy
  chartMixedDeriv MinimalActionTransfer ChartEnergyKernelBound BlockFitAnalyticAlongTranslates
  MinimalActionGaugeInvariant)
open ColdStepAtMirrorFrames.Adjoint (adjointAction_add adjointAction_smul expUnit_adjointAction)
open TorusFields (TorusBond TorusField TorusSite actionAtLevel cellsOfSites unitStep holonomy trivialField perturb
  norm_unitQuaternion plaquetteEnergy plaquettesIn readAtLevel torusFrame wilsonAction)
open TorusLumps (toTorusSite stepBlockFrame)
open StepCosts (torusSiteInFrame chartBonds)
open TopLevelSites (enclosingCell_torusSiteInFrame cellsOfSites_univ halfWidth mem_centredCube_iff mem_finiteCells
  period_neZero norm_sq_eq_re_sq_add_norm_im_sq torusSiteInFrame_toTorusSite toTorusSite_add
  toTorusSite_torusSiteInFrame toTorusSite_unitStep period_depth_of_extent period_top_of_extent exists_centre_add
  top_sub_depth isAxialTreeBond_torusSiteInFrame_iff)
open TorusCharts (torusChart IsBlockEndBond IsBlockTreeBond chartedField_readAtLevel)
open TorusContours (blockFit_readAtLevel)
open TorusChain (cellSupDist_torusSiteInFrame)
open TwoLevelMixtures (torusChartField imagUnit imagCoord sum_imagCoord_smul contourPairing interpForm interpKinetic
  interpChartEnergy interpEnergy VanishesOnTrees analyticAt_of_finite_restrictions)
open MixtureJets (MixedBond fineCoordPerturb coarseFieldPerturb mixtureIteratedDeriv mixedBondDiam mixedBondSite
  bondIndicator)
open WeightedResponses (unitGenerator maxwellKernel maxwellForm)
open LatticePaths (card_centredCube)
namespace MixtureJets
section Frames
variable {F : BlockFrame} {n : ℕ} [NeZero n]
private theorem mem_sitesOfCells_top (hn : ∀ i, F.extent i = n) (x : F.Cell) :
    x ∈ sitesOfCells (finiteCells F) F.top := by
  exact _root_.YangMills.SharedProofs.p21834 (F := F) (n := n) hn x
private theorem mem_innerBonds_top (hn : ∀ i, F.extent i = n) (c : F.Site F.top × Fin 4) :
    c ∈ innerBonds (finiteCells F) F.top := by
  unfold innerBonds
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨mem_sitesOfCells_top hn _, Finset.mem_univ _⟩, mem_sitesOfCells_top hn _⟩
private theorem mem_sitesOfCells_depth (hL : Odd F.blockSide) (hs : ∀ i, 2 ≤ F.extent i)
    (hn : ∀ i, F.extent i = n) (x : F.Site F.depth) : x ∈ sitesOfCells (finiteCells F) F.depth := by
  exact _root_.YangMills.SharedProofs.p106137 (F := F) (n := n) hL hs hn x
private theorem sum_innerBonds_top (hn : ∀ i, F.extent i = n) (f : F.Site F.top × Fin 4 → ℝ) :
    ∑ c ∈ innerBonds (finiteCells F) F.top, f c = ∑ c : TorusBond n, f (torusSiteInFrame F F.top c.1, c.2) := by
  refine Finset.sum_nbij' (fun c => (toTorusSite n c.1, c.2)) (fun c => (torusSiteInFrame F F.top c.1, c.2))
    (fun _ _ => Finset.mem_univ _) (fun c _ => mem_innerBonds_top hn _) ?_ ?_ ?_
  · intro c _
    exact Prod.ext (torusSiteInFrame_toTorusSite (period_top_of_extent hn) c.1) rfl
  · intro c _
    exact Prod.ext (toTorusSite_torusSiteInFrame (period_top_of_extent hn) c.1) rfl
  · intro c _
    simp only [torusSiteInFrame_toTorusSite (period_top_of_extent hn)]
private theorem readAtLevel_restrictToTorus [NeZero (n * F.blockSide)] (hn : ∀ i, F.extent i = n)
    (X : F.GaugeField F.depth) : readAtLevel F F.depth (restrictToTorus (n * F.blockSide) X) = X := by
  funext y i
  exact congrFun (congrArg X (torusSiteInFrame_toTorusSite (period_depth_of_extent hn) y)) i
end Frames
private instance neZero_torusFrame {L t n : ℕ} [NeZero n] [NeZero L] : NeZero (n * (torusFrame L t n).blockSide) :=
  inferInstanceAs (NeZero (n * L))
private instance neZero_stepBlockFrame {L n : ℕ} [NeZero n] [NeZero L] :
    NeZero (n * (stepBlockFrame L n).blockSide) :=
  inferInstanceAs (NeZero (n * L))
private theorem minimalAction_eq_actionAtLevel (hla : MinimalActionTransfer) (a : ℝ) {L n : ℕ} [NeZero n] [NeZero L]
    (hL : Odd L) (h2 : 2 ≤ n) : ∀ (t : ℕ) (X : (torusFrame L t n).GaugeField (torusFrame L t n).depth),
      minimalAction a (finiteCells (torusFrame L t n)) (torusFrame L t n).depth X =
        actionAtLevel a L t Finset.univ (restrictToTorus (n * L) X) := by apply _root_.YangMills.SharedProofs.p62714 <;> assumption
section Level
variable {L n : ℕ} [NeZero n] [NeZero L]
private def levelEnergy (a : ℝ) (L : ℕ) [NeZero L] (u : ℕ) (w : TorusBond (n * L) → imaginaryQuaternions)
    (V : TorusField n) : ℝ :=
  actionAtLevel a L u Finset.univ (torusChartField L w V) +
    a * ∑ c : TorusBond n, blockFit (F := stepBlockFrame L n)
      (readAtLevel (stepBlockFrame L n) 0 (torusChartField L w V))
      (readAtLevel (stepBlockFrame L n) 1 V) (torusSiteInFrame (stepBlockFrame L n) 1 c.1, c.2)
private theorem interpChartEnergy_eq_convex (a : ℝ) (t : ℕ) (θ : ℝ) (w : TorusBond (n * L) → imaginaryQuaternions)
    (V : TorusField n) :
    interpChartEnergy a L t θ w V = (1 - θ) * levelEnergy a L t w V + θ * levelEnergy a L (t + 1) w V := by
  unfold interpChartEnergy interpEnergy levelEnergy
  ring
private def frameCoords (L u : ℕ) (w : TorusBond (n * L) → imaginaryQuaternions) :
    (torusFrame L u n).Site (torusFrame L u n).depth → Fin 4 → imaginaryQuaternions :=
  fun x i => w (toTorusSite (n * L) x, i)
private theorem restrictToTorus_chartedField (hL : Odd L) (h2 : 2 ≤ n) (u : ℕ)
    (w : TorusBond (n * L) → imaginaryQuaternions) (V : TorusField n) :
    restrictToTorus (n * L) (chartedField (F := torusFrame L u n) (frameCoords L u w)
        (readAtLevel (torusFrame L u n) (torusFrame L u n).top V)) =
      torusChartField L w V := by
  have hn : ∀ i, (torusFrame L u n).extent i = n := fun _ => rfl
  have hn' : ∀ i, (stepBlockFrame L n).extent i = n := fun _ => rfl
  have hpb := period_depth_of_extent (F := torusFrame L u n) hn
  have hpb' := period_depth_of_extent (F := stepBlockFrame L n) hn'
  funext x i
  have e1 := chartedField_readAtLevel (F := torusFrame L u n) hn hL h2 (frameCoords L u w) V x i
  have e2 := chartedField_readAtLevel (F := stepBlockFrame L n) hn' hL h2
    (fun x i => w (toTorusSite (n * L) x, i)) V x i
  have e3 : (fun b : TorusBond (n * (torusFrame L u n).blockSide) => frameCoords L u w
      (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1) b.2) = w := by
    funext b
    exact congrArg w (Prod.ext (toTorusSite_torusSiteInFrame hpb b.1) rfl)
  have e4 : (fun b : TorusBond (n * (stepBlockFrame L n).blockSide) => (fun x i => w (toTorusSite (n * L) x, i))
      (torusSiteInFrame (stepBlockFrame L n) (stepBlockFrame L n).depth b.1) b.2) = w := by
    funext b
    exact congrArg w (Prod.ext (toTorusSite_torusSiteInFrame hpb' b.1) rfl)
  show chartedField (F := torusFrame L u n) (frameCoords L u w)
      (readAtLevel (torusFrame L u n) (torusFrame L u n).top V)
      (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth x) i =
    chartedField (F := stepBlockFrame L n) (fun x i => w (toTorusSite (n * L) x, i))
      (readAtLevel (stepBlockFrame L n) (stepBlockFrame L n).top V)
      (torusSiteInFrame (stepBlockFrame L n) (stepBlockFrame L n).depth x) i
  exact e1.trans (((congrArg (fun w' => torusChart L w' V x i) e3).trans
    (congrArg (fun w' => torusChart L w' V x i) e4.symm)).trans e2.symm)
private theorem blockFit_step_eq_torusFrame (hL : Odd L) (h2 : 2 ≤ n) (u : ℕ)
    (w : TorusBond (n * L) → imaginaryQuaternions) (V : TorusField n) (c : TorusBond n) :
    blockFit (F := stepBlockFrame L n) (readAtLevel (stepBlockFrame L n) 0 (torusChartField L w V))
        (readAtLevel (stepBlockFrame L n) 1 V) (torusSiteInFrame (stepBlockFrame L n) 1 c.1, c.2) =
      blockFit (F := torusFrame L u n) (chartedField (F := torusFrame L u n) (frameCoords L u w)
          (readAtLevel (torusFrame L u n) (torusFrame L u n).top V))
        (readAtLevel (torusFrame L u n) (torusFrame L u n).top V)
        (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2) := by
  have hn : ∀ i, (torusFrame L u n).extent i = n := fun _ => rfl
  have hn' : ∀ i, (stepBlockFrame L n).extent i = n := fun _ => rfl
  have hW := restrictToTorus_chartedField hL h2 u w V
  have e3 : readAtLevel (torusFrame L u n) (torusFrame L u n).depth (torusChartField L w V) =
      chartedField (F := torusFrame L u n) (frameCoords L u w)
        (readAtLevel (torusFrame L u n) (torusFrame L u n).top V) :=
    (congrArg _ hW.symm).trans (readAtLevel_restrictToTorus (F := torusFrame L u n) hn _)
  have e1 := blockFit_readAtLevel (F := stepBlockFrame L n) hn' (torusChartField L w V) V c.1 c.2
  have e2 := blockFit_readAtLevel (F := torusFrame L u n) hn (torusChartField L w V) V c.1 c.2
  exact e1.trans (e2.symm.trans (congrArg (fun Z => blockFit (F := torusFrame L u n)
    (j := (torusFrame L u n).depth) Z (readAtLevel (torusFrame L u n) (torusFrame L u n).top V)
    (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top c.1, c.2)) e3))
private theorem levelEnergy_eq_chartedEnergy (hla : MinimalActionTransfer) (a : ℝ) (hL : Odd L) (h2 : 2 ≤ n)
    (u : ℕ) (w : TorusBond (n * L) → imaginaryQuaternions) (V : TorusField n) :
    levelEnergy a L u w V = chartedEnergy (F := torusFrame L u n) a (frameCoords L u w)
      (readAtLevel (torusFrame L u n) (torusFrame L u n).top V) := by
  have hn : ∀ i, (torusFrame L u n).extent i = n := fun _ => rfl
  have hW := restrictToTorus_chartedField hL h2 u w V
  have hA := minimalAction_eq_actionAtLevel hla a hL h2 u
    (chartedField (F := torusFrame L u n) (frameCoords L u w)
      (readAtLevel (torusFrame L u n) (torusFrame L u n).top V))
  have hc := blockFit_step_eq_torusFrame hL h2 u w V
  have hF := sum_innerBonds_top (F := torusFrame L u n) hn (fun c => blockFit (F := torusFrame L u n)
    (chartedField (F := torusFrame L u n) (frameCoords L u w)
      (readAtLevel (torusFrame L u n) (torusFrame L u n).top V))
    (readAtLevel (torusFrame L u n) (torusFrame L u n).top V) c)
  have hs := Finset.sum_congr (rfl : (Finset.univ : Finset (TorusBond n)) = Finset.univ) fun c _ => hc c
  have hA' := hA.trans (congrArg (actionAtLevel a L u Finset.univ) hW)
  show actionAtLevel a L u Finset.univ (torusChartField L w V) + a * _ =
    minimalAction a (finiteCells (torusFrame L u n)) (torusFrame L u n).depth _ + a * _
  rw [hA', hs, ← hF]
end Level
section Calculus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
private def secondDeriv (T : E → ℝ) : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ T) 0
private theorem iteratedFDeriv_two_eq_secondDeriv (T : E → ℝ) (m : Fin 2 → E) :
    iteratedFDeriv ℝ 2 T 0 m = secondDeriv T (m 0) (m 1) :=
  iteratedFDeriv_two_apply T 0 m
private theorem secondDeriv_symm [CompleteSpace E] {T : E → ℝ} (hT : AnalyticAt ℝ T 0) (u v : E) :
    secondDeriv T u v = secondDeriv T v u :=
  (hT.contDiffAt (n := ω)).isSymmSndFDerivAt_of_omega u v
private theorem secondDeriv_add {S T : E → ℝ} (hS : AnalyticAt ℝ S 0) (hT : AnalyticAt ℝ T 0) (u v : E) :
    secondDeriv (fun w => S w + T w) u v = secondDeriv S u v + secondDeriv T u v := by
  have h := iteratedFDeriv_add_apply (i := 2) (f := S) (g := T) (x := (0 : E)) hS.contDiffAt hT.contDiffAt
  have h' := congrArg (fun M => M ![u, v]) h
  have e : (fun w => S w + T w) = S + T := rfl
  rw [e]
  simpa [iteratedFDeriv_two_eq_secondDeriv] using h'
private theorem secondDeriv_const_mul (r : ℝ) {T : E → ℝ} (hT : AnalyticAt ℝ T 0) (u v : E) :
    secondDeriv (fun w => r * T w) u v = r * secondDeriv T u v := by
  have h := iteratedFDeriv_const_smul_apply (i := 2) (a := r) (f := T) (x := (0 : E)) hT.contDiffAt
  have h' := congrArg (fun M => M ![u, v]) h
  have e : (fun w => r * T w) = r • T := rfl
  rw [e]
  simpa [iteratedFDeriv_two_eq_secondDeriv] using h'
private theorem secondDeriv_sum {ι : Type} (s : Finset ι) {T : ι → E → ℝ} (hT : ∀ c ∈ s, AnalyticAt ℝ (T c) 0)
    (u v : E) : secondDeriv (fun w => ∑ c ∈ s, T c w) u v = ∑ c ∈ s, secondDeriv (T c) u v := by
  have h := iteratedFDeriv_fun_sum_apply (n := 2) (𝕜 := ℝ) (f := T) (u := s) (x := (0 : E))
    fun c hc => (hT c hc).contDiffAt
  have h' := congrArg (fun M => M ![u, v]) h
  simpa [iteratedFDeriv_two_eq_secondDeriv] using h'
private theorem secondDeriv_comp [CompleteSpace E] {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (hcp : Calculus.CompositeDerivativesAtPoint) (g : A →L[ℝ] E) {T : E → ℝ} (hT : AnalyticAt ℝ T 0)
    (v : Fin 2 → A) : iteratedFDeriv ℝ 2 (fun σ => T (g σ)) 0 v = secondDeriv T (g (v 0)) (g (v 1)) := by
  have hT' : AnalyticAt ℝ T (g 0) := by simpa using hT
  have h := hcp.1 2 A E ℝ g T 0 hT' v
  rw [map_zero] at h
  exact h.trans (iteratedFDeriv_two_eq_secondDeriv T _)
private theorem secondDeriv_line [CompleteSpace E] (hcp : Calculus.CompositeDerivativesAtPoint) {T : E → ℝ}
    (hT : AnalyticAt ℝ T 0) (u : E) : deriv (deriv fun τ : ℝ => T (τ • u)) 0 = secondDeriv T u u := by
  have h := secondDeriv_comp hcp (ContinuousLinearMap.toSpanSingleton ℝ u) hT (fun _ => (1 : ℝ))
  have e : iteratedDeriv 2 (fun τ : ℝ => T (τ • u)) 0 =
      iteratedFDeriv ℝ 2 (fun τ : ℝ => T (τ • u)) 0 fun _ => 1 := iteratedDeriv_eq_iteratedFDeriv
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
  rw [h] at e
  rw [← e, iteratedDeriv_succ, iteratedDeriv_one]
end Calculus
section Limit
open Filter
private theorem deriv_deriv_eq_of_tendsto {h : ℝ → ℝ} (hh : AnalyticAt ℝ h 0) (h0 : h 0 = 0)
    (h1 : deriv h 0 = 0) {l : ℝ} (hl : Tendsto (fun τ => h τ / τ ^ 2) (𝓝[≠] 0) (𝓝 l)) :
    deriv (deriv h) 0 = 2 * l := by
  have hd : AnalyticAt ℝ (deriv h) 0 := hh.deriv
  have hD : HasDerivAt (deriv h) (deriv (deriv h) 0) 0 := hd.differentiableAt.hasDerivAt
  have hev : ∀ᶠ x in 𝓝[≠] (0 : ℝ), HasDerivAt h (deriv h x) x :=
    (hh.eventually_analyticAt.mono fun x hx => hx.differentiableAt.hasDerivAt).filter_mono nhdsWithin_le_nhds
  have hg : ∀ᶠ x in 𝓝[≠] (0 : ℝ), HasDerivAt (fun τ : ℝ => τ ^ 2) (2 * x) x :=
    Eventually.of_forall fun x => by simpa using hasDerivAt_pow 2 x
  have hg' : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 2 * x ≠ 0 :=
    eventually_mem_nhdsWithin.mono fun x hx => mul_ne_zero two_ne_zero hx
  have hfa : Tendsto h (𝓝[≠] 0) (𝓝 0) := by
    have := hh.continuousAt.tendsto
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hga : Tendsto (fun τ : ℝ => τ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have : Continuous fun τ : ℝ => τ ^ 2 := by fun_prop
    have h2 := this.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have hdiv : Tendsto (fun x => deriv h x / (2 * x)) (𝓝[≠] 0) (𝓝 (deriv (deriv h) 0 / 2)) := by
    have h3 := hasDerivAt_iff_tendsto_slope.mp hD
    have h4 := h3.div_const 2
    refine h4.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : x ≠ 0 := hx
    simp only [slope, vsub_eq_sub, h1, sub_zero, smul_eq_mul]
    field_simp
  have h5 := HasDerivAt.lhopital_zero_nhdsNE hev hg hg' hfa hga hdiv
  have h6 := tendsto_nhds_unique h5 hl
  linarith
private theorem tendsto_norm_sub_re_div_sq {Q : ℝ → ℍ[ℝ]} {q : ℍ[ℝ]} (hQ : HasDerivAt Q q 0) (h1 : Q 0 = 1)
    (hre : q.re = 0) : Tendsto (fun τ => (‖Q τ‖ - (Q τ).re) / τ ^ 2) (𝓝[≠] 0) (𝓝 (‖q‖ ^ 2 / 2)) := by
  set S : ℝ → ℍ[ℝ] := fun τ => τ⁻¹ • (Q τ - 1) with hS
  have hSq : Tendsto S (𝓝[≠] 0) (𝓝 q) := by
    have h3 := hasDerivAt_iff_tendsto_slope.mp hQ
    refine h3.congr' ?_
    filter_upwards with x
    simp [slope, h1, hS]
  have hnum : Tendsto (fun τ => ‖S τ‖ ^ 2 - (S τ).re ^ 2) (𝓝[≠] 0) (𝓝 (‖q‖ ^ 2 - q.re ^ 2)) :=
    (hSq.norm.pow 2).sub (((Quaternion.continuous_re.tendsto q).comp hSq).pow 2)
  have hP : Tendsto (fun τ => ‖Q τ‖ + (Q τ).re) (𝓝[≠] 0) (𝓝 2) := by
    have hc : Tendsto Q (𝓝[≠] 0) (𝓝 1) := by
      have := hQ.continuousAt.tendsto
      rw [h1] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 := hc.norm.add ((Quaternion.continuous_re.tendsto 1).comp hc)
    simp only [norm_one, Quaternion.re_one] at h2
    norm_num at h2
    exact h2
  have hdiv := hnum.div hP two_ne_zero
  rw [hre] at hdiv
  have e : (‖q‖ ^ 2 - (0 : ℝ) ^ 2) / 2 = ‖q‖ ^ 2 / 2 := by ring
  rw [e] at hdiv
  refine hdiv.congr' ?_
  have hne : ∀ᶠ τ in 𝓝[≠] (0 : ℝ), ‖Q τ‖ + (Q τ).re ≠ 0 := hP.eventually_ne two_ne_zero
  filter_upwards [self_mem_nhdsWithin, hne] with τ hτ hn
  have hτ' : τ ≠ 0 := hτ
  have eQ : Q τ = 1 + τ • S τ := by
    simp only [hS, smul_smul, mul_inv_cancel₀ hτ', one_smul]
    abel
  have e1 : ‖Q τ‖ ^ 2 - (Q τ).re ^ 2 = τ ^ 2 * (‖S τ‖ ^ 2 - (S τ).re ^ 2) := by
    have p1 := norm_sq_eq_re_sq_add_norm_im_sq (Q τ)
    have p2 := norm_sq_eq_re_sq_add_norm_im_sq (S τ)
    have eim : (Q τ).im = τ • (S τ).im := by
      rw [eQ]
      ext <;> simp
    rw [p1, p2, eim, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have e2 : (‖Q τ‖ - (Q τ).re) * (‖Q τ‖ + (Q τ).re) = ‖Q τ‖ ^ 2 - (Q τ).re ^ 2 := by ring
  show (‖S τ‖ ^ 2 - (S τ).re ^ 2) / (‖Q τ‖ + (Q τ).re) = _
  rw [div_eq_div_iff hn (pow_ne_zero 2 hτ')]
  rw [e1] at e2
  linarith
end Limit
section FlatRates
variable {F : BlockFrame} {j : ℕ}
private theorem pathHolonomy_one (x : F.Site j) (l : List PathStep) :
    pathHolonomy (fun _ _ => (1 : UnitQuaternion) : F.GaugeField j) x l = 1 := by apply _root_.YangMills.SharedProofs.p3325 <;> assumption
private theorem adjointAction_one (w : ℍ[ℝ]) : BlockAverages.adjointAction (1 : UnitQuaternion) w = w := by
  simp [BlockAverages.adjointAction]
private theorem holonomyRate_one (φ ψ : F.Site j → Fin 4 → ℝ) (X X' : imaginaryQuaternions) (x : F.Site j)
    (l : List PathStep) :
    holonomyRate (fun _ _ => (1 : UnitQuaternion) : F.GaugeField j) (fun x i => φ x i • X + ψ x i • X') x l =
      pathSum φ x l • (X : ℍ[ℝ]) + pathSum ψ x l • (X' : ℍ[ℝ]) := by
  induction l generalizing x with
  | nil => simp [holonomyRate, pathSum]
  | cons st r ih =>
    have hs : linkValue (fun _ _ => (1 : UnitQuaternion) : F.GaugeField j) x st = 1 := by
      rcases st with ⟨i, b⟩
      cases b <;> simp [linkValue]
    simp only [holonomyRate, pathSum, ih, hs, adjointAction_one]
    rcases st with ⟨i, b⟩
    cases b
    · simp only [Bool.false_eq_true, if_false, inv_one, adjointAction_one, Submodule.coe_add, Submodule.coe_smul,
        add_smul, neg_smul]
      abel
    · simp only [if_true, Submodule.coe_add, Submodule.coe_smul, add_smul]
      abel
private theorem contourAverageRate_one (φ ψ : F.Site j → Fin 4 → ℝ) (X X' : imaginaryQuaternions)
    (c : F.Site (j + 1) × Fin 4) :
    contourAverageRate (fun _ _ => (1 : UnitQuaternion) : F.GaugeField j) (fun x i => φ x i • X + ψ x i • X') c =
      ColdStepAtMirrorFrames.contourAverage φ c.1 c.2 • (X : ℍ[ℝ]) +
        ColdStepAtMirrorFrames.contourAverage ψ c.1 c.2 • (X' : ℍ[ℝ]) := by
  unfold contourAverageRate ColdStepAtMirrorFrames.contourAverage
  simp only [holonomyRate_one, pathHolonomy_one, OneMemClass.coe_one, mul_one]
  simp only [Finset.sum_add_distrib, ← Finset.sum_smul, smul_add, smul_smul]
private theorem contourAverage_one (hL : Odd F.blockSide) (c : F.Site (j + 1) × Fin 4) :
    BlockAverages.contourAverage (fun _ _ => (1 : UnitQuaternion) : F.GaugeField j) c = 1 := by
  unfold BlockAverages.contourAverage
  simp only [pathHolonomy_one, OneMemClass.coe_one]
  have hL0 : (F.blockSide : ℝ) ≠ 0 := by
    have := hL.pos
    positivity
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, card_centredCube hL]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
  have : (1 / (24 * (F.blockSide : ℝ) ^ 4)) * ((F.blockSide ^ 4 : ℕ) : ℝ) * (((Nat.factorial 4 : ℕ) : ℝ)) = 1 := by
    norm_num [Nat.factorial]
    field_simp
  rw [this, one_smul]
private theorem blockFit_of_top_one (X : F.GaugeField j) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4)
    (h : X' c.1 c.2 = 1) :
    blockFit X X' c = ‖BlockAverages.contourAverage X c‖ - (BlockAverages.contourAverage X c).re := by
  unfold blockFit
  rw [h]
  simp
private theorem blockFit_nonneg (X : F.GaugeField j) (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) :
    0 ≤ blockFit X X' c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.blockFit_nonneg <;> assumption
private theorem minimalAction_nonneg {a : ℝ} (ha : 0 ≤ a) (S : Finset F.Cell) :
    ∀ (j : ℕ) (U : F.GaugeField j), 0 ≤ minimalAction a S j U
  | 0, U => by
    refine Finset.sum_nonneg fun p _ => ?_
    have h := le_of_abs_le (quaternion_abs_re_le_norm ((plaquetteHolonomy U p : UnitQuaternion) : ℍ[ℝ]))
    rw [norm_unitQuaternion] at h
    linarith
  | j + 1, V => by
    have : Nonempty (F.GaugeField j) := ⟨fun _ _ => 1⟩
    exact le_ciInf fun W => add_nonneg (minimalAction_nonneg ha S j W)
      (mul_nonneg ha (Finset.sum_nonneg fun c _ => blockFit_nonneg W V c))
end FlatRates
section Coordinates
variable {L n : ℕ} [NeZero n] [NeZero L]
private theorem torusChartField_eq_torusChart (hL : Odd L) (h2 : 2 ≤ n)
    (w : TorusBond (n * L) → imaginaryQuaternions) (V : TorusField n) :
    torusChartField L w V = torusChart L w V := by
  have hn' : ∀ i, (stepBlockFrame L n).extent i = n := fun _ => rfl
  have hpb' := period_depth_of_extent (F := stepBlockFrame L n) hn'
  funext x i
  have e2 := chartedField_readAtLevel (F := stepBlockFrame L n) hn' hL h2
    (fun x i => w (toTorusSite (n * L) x, i)) V x i
  have e4 : (fun b : TorusBond (n * (stepBlockFrame L n).blockSide) => (fun x i => w (toTorusSite (n * L) x, i))
      (torusSiteInFrame (stepBlockFrame L n) (stepBlockFrame L n).depth b.1) b.2) = w := by
    funext b
    exact congrArg w (Prod.ext (toTorusSite_torusSiteInFrame hpb' b.1) rfl)
  exact e2.trans (congrArg (fun w' => torusChart L w' V x i) e4)
private theorem torusChartField_trivial (hL : Odd L) (h2 : 2 ≤ n) (w : TorusBond (n * L) → imaginaryQuaternions)
    (hw : ∀ b, b ∉ chartBonds L n → w b = 0) (x : TorusSite (n * L)) (i : Fin 4) :
    torusChartField L w (trivialField n) x i = expUnit (w (x, i)) := by
  have hn' : ∀ i, (stepBlockFrame L n).extent i = n := fun _ => rfl
  rw [torusChartField_eq_torusChart hL h2]
  unfold torusChart
  by_cases h1 : IsBlockEndBond L x i
  · rw [if_pos h1]
    simp [trivialField]
  · rw [if_neg h1]
    by_cases h3 : IsBlockTreeBond L x i
    · rw [if_pos h3]
      have hb : (x, i) ∉ chartBonds L n := by
        simp only [chartBonds, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
        exact (isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame L n) hn' hL h2 x i).mpr h3
      rw [hw _ hb, TorusFields.expUnit_zero]
    · rw [if_neg h3]
private def flatAction (a : ℝ) (L : ℕ) [NeZero L] (u : ℕ) (w : TorusBond (n * L) → imaginaryQuaternions) : ℝ :=
  actionAtLevel a L u Finset.univ (torusChartField L w (trivialField n))
private def flatFit (L : ℕ) [NeZero L] (c : TorusBond n) (w : TorusBond (n * L) → imaginaryQuaternions) : ℝ :=
  blockFit (F := stepBlockFrame L n) (readAtLevel (stepBlockFrame L n) 0 (torusChartField L w (trivialField n)))
    (readAtLevel (stepBlockFrame L n) 1 (trivialField n)) (torusSiteInFrame (stepBlockFrame L n) 1 c.1, c.2)
private theorem levelEnergy_trivial (a : ℝ) (u : ℕ) (w : TorusBond (n * L) → imaginaryQuaternions) :
    levelEnergy a L u w (trivialField n) = flatAction a L u w + a * ∑ c : TorusBond n, flatFit L c w := rfl
private theorem interpChartEnergy_trivial (a : ℝ) (t : ℕ) (θ : ℝ) (w : TorusBond (n * L) → imaginaryQuaternions) :
    interpChartEnergy a L t θ w (trivialField n) =
      (1 - θ) * flatAction a L t w + θ * flatAction a L (t + 1) w + a * ∑ c : TorusBond n, flatFit L c w := rfl
private def directionOf (L u : ℕ) (p : MixedBond L n) (X : imaginaryQuaternions) : ChartDirection (torusFrame L u n) :=
  match p with
  | .inl b => .inl (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2, X)
  | .inr d => .inr (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top d.1, d.2, X)
private theorem frameCoords_fineCoordPerturb (u k : ℕ) (c : Fin k → MixedBond L n)
    (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) :
    frameCoords L u (fineCoordPerturb L c X σ) = shiftedCoords (fun _ _ => 0)
      (fun l => directionCoordinate (directionOf L u (c l) (X l))) σ := by
  have hn : ∀ i, (torusFrame L u n).extent i = n := fun _ => rfl
  have hpb := period_depth_of_extent (F := torusFrame L u n) hn
  funext x i
  show ∑ l, (if c l = Sum.inl (toTorusSite (n * L) x, i) then σ l • X l else 0) =
    0 + ∑ l, σ l • directionCoordinate (directionOf L u (c l) (X l)) x i
  rw [zero_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases hc : c l with b | d
  · simp only [directionOf, directionCoordinate, Sum.inl.injEq]
    by_cases hb : b = (toTorusSite (n * L) x, i)
    · subst hb
      rw [if_pos rfl, if_pos ⟨torusSiteInFrame_toTorusSite hpb x, rfl⟩]
    · rw [if_neg hb, if_neg, smul_zero]
      rintro ⟨e1, e2⟩
      refine hb (Prod.ext ?_ e2)
      rw [← e1]
      exact (toTorusSite_torusSiteInFrame hpb b.1).symm
  · simp [directionOf, directionCoordinate]
omit [NeZero L] in
private theorem readAtLevel_coarseFieldPerturb (u k : ℕ) (c : Fin k → MixedBond L n)
    (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) :
    readAtLevel (torusFrame L u n) (torusFrame L u n).top (coarseFieldPerturb L c X σ) =
      translatedTop (uniformField (torusFrame L u n) (torusFrame L u n).top)
        (fun l => directionMove (directionOf L u (c l) (X l))) σ := by
  have hn : ∀ i, (torusFrame L u n).extent i = n := fun _ => rfl
  have hpt := period_top_of_extent (F := torusFrame L u n) hn
  funext y i
  show expUnit (∑ l, if c l = Sum.inr (toTorusSite n y, i) then σ l • X l else 0) =
    expUnit (∑ l, σ l • directionMove (directionOf L u (c l) (X l)) y i) * 1
  rw [mul_one]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases hc : c l with b | d
  · simp [directionOf, directionMove]
  · simp only [directionOf, directionMove, Sum.inr.injEq]
    by_cases hb : d = (toTorusSite n y, i)
    · subst hb
      rw [if_pos rfl, if_pos ⟨torusSiteInFrame_toTorusSite hpt y, rfl⟩]
    · rw [if_neg hb, if_neg, smul_zero]
      rintro ⟨e1, e2⟩
      refine hb (Prod.ext ?_ e2)
      rw [← e1]
      exact (toTorusSite_torusSiteInFrame hpt d.1).symm
private theorem levelEnergy_eq_chartRestriction (hla : MinimalActionTransfer) (a : ℝ) (hL : Odd L) (h2 : 2 ≤ n)
    (u k : ℕ) (c : Fin k → MixedBond L n) (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) :
    levelEnergy a L u (fineCoordPerturb L c X σ) (coarseFieldPerturb L c X σ) =
      chartRestriction (F := torusFrame L u n) a (fun _ _ => 0)
        (uniformField (torusFrame L u n) (torusFrame L u n).top) (fun l => directionOf L u (c l) (X l)) σ := by
  rw [levelEnergy_eq_chartedEnergy hla a hL h2, frameCoords_fineCoordPerturb, readAtLevel_coarseFieldPerturb]
  rfl
end Coordinates
section Analytic
variable {L n : ℕ} [NeZero n] [NeZero L]
omit [NeZero n] [NeZero L] in
private theorem chartedField_zero_uniform {F : BlockFrame} :
    chartedField (F := F) (fun _ _ => 0) (uniformField F F.top) = fun _ _ => 1 := by apply _root_.YangMills.DeltaSharedProofs.p501102 <;> assumption
omit [NeZero n] [NeZero L] in
private theorem isSmallCurvature_one {F : BlockFrame} {j : ℕ} {s : ℝ} (hs : 0 < s) :
    IsSmallCurvature s (fun _ _ => (1 : UnitQuaternion) : F.GaugeField j) := by apply _root_.YangMills.DeltaSharedProofs.p500582 <;> assumption
omit [NeZero n] [NeZero L] in
private theorem isAdmissibleChartPoint_zero {F : BlockFrame} {σ : ℝ} (hσ : 0 < σ) (hL : 0 < L) :
    IsAdmissibleChartPoint L σ (fun _ _ => 0) (uniformField F F.top) := by
  refine ⟨fun b _ => ?_, ?_⟩
  · simp only [norm_zero]
    positivity
  · rw [chartedField_zero_uniform]
    exact isSmallCurvature_one hσ
private def fineBonds {k : ℕ} (c : Fin k → TorusBond (n * L)) : Fin k → MixedBond L n := fun l => Sum.inl (c l)
omit [NeZero n] [NeZero L] in
private theorem fineCoordPerturb_fineBonds {k : ℕ} (c : Fin k → TorusBond (n * L))
    (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) :
    (fun b => ∑ l, if c l = b then σ l • X l else 0) = fineCoordPerturb L (fineBonds c) X σ := by
  funext b
  simp [fineCoordPerturb, fineBonds]
omit [NeZero n] [NeZero L] in
private theorem coarseFieldPerturb_fineBonds {k : ℕ} (c : Fin k → TorusBond (n * L))
    (X : Fin k → imaginaryQuaternions) (σ : Fin k → ℝ) :
    coarseFieldPerturb L (fineBonds c) X σ = trivialField n := by
  funext x i
  simp [coarseFieldPerturb, fineBonds, trivialField, TorusFields.expUnit_zero]
private theorem analyticAt_flatFit (hfit : BlockFitAnalyticAlongTranslates) (hL : Odd L) (h2 : 2 ≤ n)
    (c : TorusBond n) : AnalyticAt ℝ (flatFit (n := n) L c) 0 := by
  refine analyticAt_of_finite_restrictions _ fun k c' X => ?_
  obtain ⟨C, -, hC⟩ := hfit L hL
  have h := (hC (torusFrame L 0 n) (fun _ _ => 0) (uniformField _ _) k
    (fun l => directionCoordinate (directionOf L 0 (fineBonds c' l) (X l)))
    (fun l => directionMove (directionOf L 0 (fineBonds c' l) (X l)))
    (torusSiteInFrame (torusFrame L 0 n) (torusFrame L 0 n).top c.1, c.2) rfl (fun _ => h2)
    (fun b _ => by simp only [norm_zero]; have := hL.pos; positivity)).1
  refine h.congr (Filter.Eventually.of_forall fun σ => ?_)
  have e := blockFit_step_eq_torusFrame hL h2 0 (fineCoordPerturb L (fineBonds c') X σ) (trivialField n) c
  have e' := coarseFieldPerturb_fineBonds c' X σ
  show _ = flatFit L c (fun b => ∑ l, if c' l = b then σ l • X l else 0)
  rw [fineCoordPerturb_fineBonds]
  unfold flatFit
  rw [e, frameCoords_fineCoordPerturb]
  have e2 := readAtLevel_coarseFieldPerturb 0 k (fineBonds c') X σ
  rw [e'] at e2
  rw [e2]
  rfl
private theorem analyticAt_levelEnergy (hla : MinimalActionTransfer) (hker : ChartEnergyKernelBound) {a : ℝ}
    (ha : 1 ≤ a) {c : ColdChainParameters} (hL : Odd L) (hL40 : 2 ^ 40 ≤ L) (hc : c.Admissible a L) (h64 : 64 ≤ n)
    (u : ℕ) : AnalyticAt ℝ (fun w : TorusBond (n * L) → imaginaryQuaternions => levelEnergy a L u w (trivialField n)) 0 := by
  refine analyticAt_of_finite_restrictions _ fun k c' X => ?_
  obtain ⟨Ck, -, hC⟩ := hker a L c ha hL hL40 hc
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  have h := (hC (torusFrame L u n) (fun _ _ => 0) (uniformField _ _) ⟨rfl, n, h64, fun _ => rfl⟩
    (isAdmissibleChartPoint_zero hσ hL.pos) k (fun l => directionOf L u (fineBonds c' l) (X l))).1
  refine h.congr (Filter.Eventually.of_forall fun σ => ?_)
  have e := levelEnergy_eq_chartRestriction hla a hL (by omega) u k (fineBonds c') X σ
  rw [coarseFieldPerturb_fineBonds] at e
  show _ = levelEnergy a L u (fun b => ∑ l, if c' l = b then σ l • X l else 0) (trivialField n)
  rw [fineCoordPerturb_fineBonds]
  exact e.symm
private theorem analyticAt_flatAction (hla : MinimalActionTransfer) (hker : ChartEnergyKernelBound)
    (hfit : BlockFitAnalyticAlongTranslates) {a : ℝ} (ha : 1 ≤ a) {c : ColdChainParameters} (hL : Odd L)
    (hL40 : 2 ^ 40 ≤ L) (hc : c.Admissible a L) (h64 : 64 ≤ n) (u : ℕ) :
    AnalyticAt ℝ (flatAction (n := n) a L u) 0 := by
  have h1 := analyticAt_levelEnergy hla hker ha hL hL40 hc h64 u
  have h2 : AnalyticAt ℝ (fun w : TorusBond (n * L) → imaginaryQuaternions =>
      a * ∑ c : TorusBond n, flatFit L c w) 0 :=
    analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun c _ => analyticAt_flatFit hfit hL (by omega) c)
  refine (h1.sub h2).congr (Filter.Eventually.of_forall fun w => ?_)
  show levelEnergy a L u w (trivialField n) - a * ∑ c : TorusBond n, flatFit L c w = flatAction a L u w
  rw [levelEnergy_trivial]
  ring
end Analytic
section FitForm
variable {L n : ℕ} [NeZero n] [NeZero L]
private instance : CompleteSpace imaginaryQuaternions := FiniteDimensional.complete ℝ imaginaryQuaternions
private def twoDirections (φ ψ : TorusBond (n * L) → ℝ) (X X' : imaginaryQuaternions) :
    TorusBond (n * L) → imaginaryQuaternions := fun b => φ b • X + ψ b • X'
omit [NeZero n] [NeZero L] in
private theorem smul_vanish {u : TorusBond (n * L) → imaginaryQuaternions} {P : TorusBond (n * L) → Prop}
    (hu : ∀ b, P b → u b = 0) (τ : ℝ) : ∀ b, P b → (τ • u) b = 0 := fun b hb => by
  simp [hu b hb]
private theorem twoDirections_vanish {φ ψ : TorusBond (n * L) → ℝ} (hφ : VanishesOnTrees L φ)
    (hψ : VanishesOnTrees L ψ) (X X' : imaginaryQuaternions) :
    ∀ b, b ∉ chartBonds L n → twoDirections φ ψ X X' b = 0 := fun b hb => by
  simp [twoDirections, hφ b hb, hψ b hb]
private theorem readAtLevel_torusChartField_trivial (hL : Odd L) (h2 : 2 ≤ n)
    (w : TorusBond (n * L) → imaginaryQuaternions) (hw : ∀ b, b ∉ chartBonds L n → w b = 0)
    (x : (stepBlockFrame L n).Site 0) (i : Fin 4) :
    readAtLevel (stepBlockFrame L n) 0 (torusChartField L w (trivialField n)) x i =
      expUnit (w (toTorusSite (n * L) x, i)) :=
  torusChartField_trivial hL h2 w hw _ _
private theorem flatFit_zero (hL : Odd L) (h2 : 2 ≤ n) (c : TorusBond n) : flatFit (n := n) L c 0 = 0 := by
  have e : readAtLevel (stepBlockFrame L n) 0
      (torusChartField L (0 : TorusBond (n * L) → imaginaryQuaternions) (trivialField n)) =
      fun _ _ => (1 : UnitQuaternion) := by
    funext x i
    rw [readAtLevel_torusChartField_trivial hL h2 0 (fun _ _ => rfl)]
    exact TorusFields.expUnit_zero
  unfold flatFit
  rw [e, blockFit_of_top_one _ _ _ rfl, contourAverage_one hL]
  simp
private theorem secondDeriv_flatFit_diag (hcp : Calculus.CompositeDerivativesAtPoint)
    (hfit : BlockFitAnalyticAlongTranslates) (hL : Odd L) (h2 : 2 ≤ n) {φ ψ : TorusBond (n * L) → ℝ}
    (hφ : VanishesOnTrees L φ) (hψ : VanishesOnTrees L ψ) (X X' : imaginaryQuaternions) (c : TorusBond n) :
    secondDeriv (flatFit L c) (twoDirections φ ψ X X') (twoDirections φ ψ X X') =
      ‖TwoLevelMixtures.contourMean L φ c • (X : ℍ[ℝ]) + TwoLevelMixtures.contourMean L ψ c • (X' : ℍ[ℝ])‖ ^ 2 := by
  set u := twoDirections φ ψ X X' with hu
  have hoff := twoDirections_vanish hφ hψ X X'
  have hana := analyticAt_flatFit hfit hL h2 c
  set Xc : ℝ → (stepBlockFrame L n).GaugeField 0 := fun τ =>
    readAtLevel (stepBlockFrame L n) 0 (torusChartField L (τ • u) (trivialField n)) with hXc
  have hX : ∀ τ x i, Xc τ x i = expUnit (τ • u (toTorusSite (n * L) x, i)) := fun τ x i =>
    readAtLevel_torusChartField_trivial hL h2 (τ • u) (smul_vanish hoff τ) x i
  have X0 : Xc 0 = fun _ _ => (1 : UnitQuaternion) := by
    funext x i
    rw [hX]
    exact expUnit_zero_smul _
  have hd : ∀ x i, HasDerivAt (fun τ => ((Xc τ x i : UnitQuaternion) : ℍ[ℝ]))
      (((fun (x : (stepBlockFrame L n).Site 0) i =>
          φ (toTorusSite (n * L) x, i) • X + ψ (toTorusSite (n * L) x, i) • X') x i : imaginaryQuaternions) *
        (((fun _ _ => (1 : UnitQuaternion)) : (stepBlockFrame L n).GaugeField 0) x i : ℍ[ℝ])) 0 := by
    intro x i
    simp only [hX, OneMemClass.coe_one, mul_one]
    exact hasDerivAt_expUnit_smul _
  set cc : (stepBlockFrame L n).Site 1 × Fin 4 := (torusSiteInFrame (stepBlockFrame L n) 1 c.1, c.2) with hcc
  have hQ := hasDerivAt_contourAverage X0 hd cc
  rw [contourAverageRate_one] at hQ
  have hQ0 : BlockAverages.contourAverage (Xc 0) cc = 1 := by
    rw [X0]
    exact contourAverage_one hL cc
  have hre : (ColdStepAtMirrorFrames.contourAverage
        (fun (x : (stepBlockFrame L n).Site 0) i => φ (toTorusSite (n * L) x, i)) cc.1 cc.2 • (X : ℍ[ℝ]) +
      ColdStepAtMirrorFrames.contourAverage
        (fun (x : (stepBlockFrame L n).Site 0) i => ψ (toTorusSite (n * L) x, i)) cc.1 cc.2 • (X' : ℍ[ℝ])).re = 0 := by
    have h1 : (X : ℍ[ℝ]).re = 0 := X.2
    have h3 : (X' : ℍ[ℝ]).re = 0 := X'.2
    simp [h1, h3]
  have hlim := tendsto_norm_sub_re_div_sq hQ hQ0 hre
  have hh : AnalyticAt ℝ (fun τ : ℝ => flatFit L c (τ • u)) 0 := by
    have h1 := (ContinuousLinearMap.toSpanSingleton ℝ u).analyticAt (0 : ℝ)
    have h3 : AnalyticAt ℝ (flatFit (n := n) L c) ((ContinuousLinearMap.toSpanSingleton ℝ u) (0 : ℝ)) := by
      simpa using hana
    exact AnalyticAt.fun_comp h3 h1
  have hval : ∀ τ : ℝ, flatFit L c (τ • u) =
      ‖BlockAverages.contourAverage (Xc τ) cc‖ - (BlockAverages.contourAverage (Xc τ) cc).re :=
    fun τ => blockFit_of_top_one _ _ _ rfl
  have h0 : flatFit L c ((0 : ℝ) • u) = 0 := by
    rw [zero_smul]
    exact flatFit_zero hL h2 c
  have h1 : deriv (fun τ : ℝ => flatFit L c (τ • u)) 0 = 0 := by
    have hm : IsLocalMin (fun τ : ℝ => flatFit L c (τ • u)) 0 := by
      refine Filter.Eventually.of_forall fun τ => ?_
      show flatFit L c ((0 : ℝ) • u) ≤ flatFit L c (τ • u)
      rw [h0]
      exact blockFit_nonneg _ _ _
    exact hm.deriv_eq_zero
  have hs := deriv_deriv_eq_of_tendsto hh h0 h1 (l := _) (by
    simp only [hval]
    exact hlim)
  have e2 : ∀ x : ℝ, 2 * (x / 2) = x := fun x => by ring
  rw [← secondDeriv_line hcp hana u, hs, e2]
  rfl
open Classical in
private def atBond (b : TorusBond (n * L)) (X : imaginaryQuaternions) : TorusBond (n * L) → imaginaryQuaternions :=
  fun b' => bondIndicator b b' • X
private theorem vanishesOnTrees_bondIndicator {b : TorusBond (n * L)} (hb : b ∈ chartBonds L n) :
    VanishesOnTrees L (bondIndicator b) := fun b' hb' => by
  have : b' ≠ b := fun e => hb' (e ▸ hb)
  simp [bondIndicator, this]
private theorem secondDeriv_polarization [CompleteSpace (TorusBond (n * L) → imaginaryQuaternions)]
    {T : (TorusBond (n * L) → imaginaryQuaternions) → ℝ} (hT : AnalyticAt ℝ T 0)
    (u v : TorusBond (n * L) → imaginaryQuaternions) :
    secondDeriv T u v = (secondDeriv T (u + v) (u + v) - secondDeriv T (u - v) (u - v)) / 4 := by
  have h := secondDeriv_symm hT v u
  simp only [map_add, map_sub, add_apply, sub_apply, h]
  ring
private theorem secondDeriv_flatFit_atBond (hcp : Calculus.CompositeDerivativesAtPoint)
    (hfit : BlockFitAnalyticAlongTranslates) (hL : Odd L) (h2 : 2 ≤ n) {b b' : TorusBond (n * L)}
    (hb : b ∈ chartBonds L n) (hb' : b' ∈ chartBonds L n) (X X' : imaginaryQuaternions) (c : TorusBond n) :
    secondDeriv (flatFit L c) (atBond b X) (atBond b' X') =
      inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) *
        (TwoLevelMixtures.contourMean L (bondIndicator b) c * TwoLevelMixtures.contourMean L (bondIndicator b') c) := by
  have hana := analyticAt_flatFit hfit hL h2 c
  have e1 : atBond b X + atBond b' X' = twoDirections (bondIndicator b) (bondIndicator b') X X' := rfl
  have e2 : atBond b X - atBond b' X' = twoDirections (bondIndicator b) (bondIndicator b') X (-X') := by
    funext b''
    simp [atBond, twoDirections, sub_eq_add_neg]
  rw [secondDeriv_polarization hana, e1, e2,
    secondDeriv_flatFit_diag hcp hfit hL h2 (vanishesOnTrees_bondIndicator hb) (vanishesOnTrees_bondIndicator hb'),
    secondDeriv_flatFit_diag hcp hfit hL h2 (vanishesOnTrees_bondIndicator hb) (vanishesOnTrees_bondIndicator hb')]
  simp only [Submodule.coe_neg, smul_neg, ← sub_eq_add_neg]
  rw [norm_add_sq_real, norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right]
  ring
end FitForm
section Colour
private theorem mem_unitary_of_sq {q : ℍ[ℝ]} (h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1) :
    q ∈ unitary ℍ[ℝ] := by apply _root_.YangMills.Construction.ComplexChartEstimates.mem_unitary_of_sum_sq <;> assumption
private def quat (a b c d : ℝ) : ℍ[ℝ] := ⟨a, b, c, d⟩
@[simp] private theorem quat_re (a b c d : ℝ) : (quat a b c d).re = a := rfl
@[simp] private theorem quat_imI (a b c d : ℝ) : (quat a b c d).imI = b := rfl
@[simp] private theorem quat_imJ (a b c d : ℝ) : (quat a b c d).imJ = c := rfl
@[simp] private theorem quat_imK (a b c d : ℝ) : (quat a b c d).imK = d := rfl
private def unitI : UnitQuaternion := ⟨quat 0 1 0 0, mem_unitary_of_sq (by norm_num)⟩
private def unitJ : UnitQuaternion := ⟨quat 0 0 1 0, mem_unitary_of_sq (by norm_num)⟩
private def unitHurwitz : UnitQuaternion := ⟨quat (1 / 2) (1 / 2) (1 / 2) (1 / 2), mem_unitary_of_sq (by norm_num)⟩
private theorem adjointAction_unitI_zero :
    ColdStepAtMirrorFrames.adjointAction unitI (imagUnit 0) = imagUnit 0 := by
  apply Subtype.ext
  show (quat 0 1 0 0) * quat 0 1 0 0 * star ((quat 0 1 0 0)) = (quat 0 1 0 0)
  ext <;> simp
private theorem adjointAction_unitI_one :
    ColdStepAtMirrorFrames.adjointAction unitI (imagUnit 1) = -imagUnit 1 := by
  apply Subtype.ext
  show (quat 0 1 0 0) * quat 0 0 1 0 * star ((quat 0 1 0 0)) = -(quat 0 0 1 0)
  ext <;> simp
private theorem adjointAction_unitI_two :
    ColdStepAtMirrorFrames.adjointAction unitI (imagUnit 2) = -imagUnit 2 := by
  apply Subtype.ext
  show (quat 0 1 0 0) * quat 0 0 0 1 * star ((quat 0 1 0 0)) = -(quat 0 0 0 1)
  ext <;> simp
private theorem adjointAction_unitJ_one :
    ColdStepAtMirrorFrames.adjointAction unitJ (imagUnit 1) = imagUnit 1 := by
  apply Subtype.ext
  show (quat 0 0 1 0) * quat 0 0 1 0 * star ((quat 0 0 1 0)) = (quat 0 0 1 0)
  ext <;> simp
private theorem adjointAction_unitJ_two :
    ColdStepAtMirrorFrames.adjointAction unitJ (imagUnit 2) = -imagUnit 2 := by
  apply Subtype.ext
  show (quat 0 0 1 0) * quat 0 0 0 1 * star ((quat 0 0 1 0)) = -(quat 0 0 0 1)
  ext <;> simp
private theorem adjointAction_unitHurwitz_zero :
    ColdStepAtMirrorFrames.adjointAction unitHurwitz (imagUnit 0) = imagUnit 1 := by
  apply Subtype.ext
  show (quat (1 / 2) (1 / 2) (1 / 2) (1 / 2)) * quat 0 1 0 0 * star ((quat (1 / 2) (1 / 2) (1 / 2) (1 / 2))) =
    (quat 0 0 1 0)
  ext <;> simp <;> norm_num
private theorem adjointAction_unitHurwitz_one :
    ColdStepAtMirrorFrames.adjointAction unitHurwitz (imagUnit 1) = imagUnit 2 := by
  apply Subtype.ext
  show (quat (1 / 2) (1 / 2) (1 / 2) (1 / 2)) * quat 0 0 1 0 * star ((quat (1 / 2) (1 / 2) (1 / 2) (1 / 2))) =
    (quat 0 0 0 1)
  ext <;> simp <;> norm_num
private theorem bilinear_eq_inner_mul_of_invariant (B : imaginaryQuaternions →L[ℝ] imaginaryQuaternions →L[ℝ] ℝ)
    (hB : ∀ (g : UnitQuaternion) (X X' : imaginaryQuaternions),
      B (ColdStepAtMirrorFrames.adjointAction g X) (ColdStepAtMirrorFrames.adjointAction g X') = B X X')
    (X X' : imaginaryQuaternions) : B X X' = inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * B (imagUnit 0) (imagUnit 0) := by
  have b01 : B (imagUnit 0) (imagUnit 1) = 0 := by
    have h := hB unitI (imagUnit 0) (imagUnit 1)
    rw [adjointAction_unitI_zero, adjointAction_unitI_one, map_neg] at h
    linarith
  have b02 : B (imagUnit 0) (imagUnit 2) = 0 := by
    have h := hB unitI (imagUnit 0) (imagUnit 2)
    rw [adjointAction_unitI_zero, adjointAction_unitI_two, map_neg] at h
    linarith
  have b10 : B (imagUnit 1) (imagUnit 0) = 0 := by
    have h := hB unitI (imagUnit 1) (imagUnit 0)
    rw [adjointAction_unitI_zero, adjointAction_unitI_one, map_neg, neg_apply] at h
    linarith
  have b20 : B (imagUnit 2) (imagUnit 0) = 0 := by
    have h := hB unitI (imagUnit 2) (imagUnit 0)
    rw [adjointAction_unitI_zero, adjointAction_unitI_two, map_neg, neg_apply] at h
    linarith
  have b12 : B (imagUnit 1) (imagUnit 2) = 0 := by
    have h := hB unitJ (imagUnit 1) (imagUnit 2)
    rw [adjointAction_unitJ_one, adjointAction_unitJ_two, map_neg] at h
    linarith
  have b21 : B (imagUnit 2) (imagUnit 1) = 0 := by
    have h := hB unitJ (imagUnit 2) (imagUnit 1)
    rw [adjointAction_unitJ_one, adjointAction_unitJ_two, map_neg, neg_apply] at h
    linarith
  have b11 : B (imagUnit 1) (imagUnit 1) = B (imagUnit 0) (imagUnit 0) := by
    have h := hB unitHurwitz (imagUnit 0) (imagUnit 0)
    rw [adjointAction_unitHurwitz_zero] at h
    exact h
  have b22 : B (imagUnit 2) (imagUnit 2) = B (imagUnit 0) (imagUnit 0) := by
    have h := hB unitHurwitz (imagUnit 1) (imagUnit 1)
    rw [adjointAction_unitHurwitz_one, b11] at h
    exact h
  have hi : inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) = imagCoord 0 X * imagCoord 0 X' + imagCoord 1 X * imagCoord 1 X' +
      imagCoord 2 X * imagCoord 2 X' := by
    have h1 : (X : ℍ[ℝ]).re = 0 := X.2
    have e0 : ∀ Y : imaginaryQuaternions, imagCoord 0 Y = (Y : ℍ[ℝ]).imI := fun _ => rfl
    have e1 : ∀ Y : imaginaryQuaternions, imagCoord 1 Y = (Y : ℍ[ℝ]).imJ := fun _ => rfl
    have e2 : ∀ Y : imaginaryQuaternions, imagCoord 2 Y = (Y : ℍ[ℝ]).imK := fun _ => rfl
    rw [e0, e0, e1, e1, e2, e2, Quaternion.inner_def]
    simp [h1]
  have hX := sum_imagCoord_smul X
  have hX' := sum_imagCoord_smul X'
  rw [hi]
  conv_lhs => rw [← hX, ← hX']
  simp only [Fin.sum_univ_three, map_add, map_smul, add_apply, smul_apply, smul_eq_mul, b01, b02, b10, b20, b12, b21,
    b11, b22]
  ring
end Colour
section ActionForm
variable {L n : ℕ} [NeZero n] [NeZero L]
private def adjointCLM (g : UnitQuaternion) : imaginaryQuaternions →L[ℝ] imaginaryQuaternions :=
  LinearMap.toContinuousLinearMap
    { toFun := ColdStepAtMirrorFrames.adjointAction g, map_add' := _root_.YangMills.Construction.ColdStepAtMirrorFrames.Adjoint.adjointAction_add g,
      map_smul' := fun r X => _root_.YangMills.Construction.ColdStepAtMirrorFrames.Adjoint.adjointAction_smul g r X }
private def adjointOnBonds (g : UnitQuaternion) :
    (TorusBond (n * L) → imaginaryQuaternions) →L[ℝ] (TorusBond (n * L) → imaginaryQuaternions) :=
  ContinuousLinearMap.pi fun b => (adjointCLM g).comp (ContinuousLinearMap.proj b)
omit [NeZero n] [NeZero L] in
private theorem adjointOnBonds_apply (g : UnitQuaternion) (w : TorusBond (n * L) → imaginaryQuaternions)
    (b : TorusBond (n * L)) : adjointOnBonds g w b = ColdStepAtMirrorFrames.adjointAction g (w b) := rfl
private theorem torusChartField_adjoint (hL : Odd L) (h2 : 2 ≤ n) (g : UnitQuaternion)
    (w : TorusBond (n * L) → imaginaryQuaternions) :
    torusChartField L (adjointOnBonds g w) (trivialField n) =
      fun x i => g * torusChartField L w (trivialField n) x i * g⁻¹ := by
  rw [torusChartField_eq_torusChart hL h2, torusChartField_eq_torusChart hL h2]
  funext x i
  unfold torusChart
  by_cases h1 : IsBlockEndBond L x i
  · simp only [if_pos h1, adjointOnBonds_apply, expUnit_adjointAction, trivialField, mul_one]
  · by_cases h3 : IsBlockTreeBond L x i
    · simp only [if_neg h1, if_pos h3]
      simp
    · simp only [if_neg h1, if_neg h3, adjointOnBonds_apply, expUnit_adjointAction]
private theorem restrictToTorus_readAtLevel (u : ℕ) (W : TorusField (n * L)) :
    restrictToTorus (n * L) (readAtLevel (torusFrame L u n) (torusFrame L u n).depth W) = W := by
  have hn : ∀ i, (torusFrame L u n).extent i = n := fun _ => rfl
  funext x i
  exact congrFun (congrArg W (toTorusSite_torusSiteInFrame (period_depth_of_extent hn) x)) i
private theorem actionAtLevel_eq_minimalAction (hla : MinimalActionTransfer) (a : ℝ) (hL : Odd L) (h2 : 2 ≤ n)
    (u : ℕ) (W : TorusField (n * L)) :
    actionAtLevel a L u Finset.univ W =
      minimalAction a (finiteCells (torusFrame L u n)) (torusFrame L u n).depth
        (readAtLevel (torusFrame L u n) (torusFrame L u n).depth W) := by
  have h := minimalAction_eq_actionAtLevel hla a hL h2 u (readAtLevel (torusFrame L u n) (torusFrame L u n).depth W)
  rw [restrictToTorus_readAtLevel] at h
  exact h.symm
private theorem flatAction_adjoint (hla : MinimalActionTransfer) (hgi : MinimalActionGaugeInvariant) (a : ℝ)
    (hL : Odd L) (h2 : 2 ≤ n) (u : ℕ) (g : UnitQuaternion) (w : TorusBond (n * L) → imaginaryQuaternions) :
    flatAction a L u (adjointOnBonds g w) = flatAction a L u w := by
  unfold flatAction
  rw [torusChartField_adjoint hL h2, actionAtLevel_eq_minimalAction hla a hL h2,
    actionAtLevel_eq_minimalAction hla a hL h2]
  exact hgi (torusFrame L u n) a _ _ (Nat.le_succ _) hL.pos (fun _ => g) _
private theorem secondDeriv_invariant (hcp : Calculus.CompositeDerivativesAtPoint)
    {T : (TorusBond (n * L) → imaginaryQuaternions) → ℝ} (hT : AnalyticAt ℝ T 0) (g : UnitQuaternion)
    (hinv : ∀ w, T (adjointOnBonds g w) = T w) (u v : TorusBond (n * L) → imaginaryQuaternions) :
    secondDeriv T (adjointOnBonds g u) (adjointOnBonds g v) = secondDeriv T u v := by
  have h := secondDeriv_comp hcp (adjointOnBonds g) hT ![u, v]
  simp only [hinv] at h
  have e := iteratedFDeriv_two_eq_secondDeriv T ![u, v]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h e
  exact h.symm.trans e
private def atBondCLM (b : TorusBond (n * L)) : imaginaryQuaternions →L[ℝ] (TorusBond (n * L) → imaginaryQuaternions) :=
  ContinuousLinearMap.pi fun b' => (bondIndicator b b') • ContinuousLinearMap.id ℝ imaginaryQuaternions
omit [NeZero n] [NeZero L] in
private theorem atBondCLM_apply (b : TorusBond (n * L)) (X : imaginaryQuaternions) : atBondCLM b X = atBond b X := rfl
private theorem secondDeriv_flatAction_atBond (hcp : Calculus.CompositeDerivativesAtPoint)
    (hla : MinimalActionTransfer) (hgi : MinimalActionGaugeInvariant) {a : ℝ} (hL : Odd L) (h2 : 2 ≤ n) (u : ℕ)
    (hT : AnalyticAt ℝ (flatAction (n := n) a L u) 0) (b b' : TorusBond (n * L)) (X X' : imaginaryQuaternions) :
    secondDeriv (flatAction a L u) (atBond b X) (atBond b' X') =
      inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) *
        secondDeriv (flatAction a L u) (atBond b unitGenerator) (atBond b' unitGenerator) := by
  have hone : ∀ (g : UnitQuaternion) (b : TorusBond (n * L)) (X : imaginaryQuaternions),
      adjointOnBonds g (atBond b X) = atBond b (ColdStepAtMirrorFrames.adjointAction g X) := by
    intro g b X
    funext b'
    exact _root_.YangMills.Construction.ColdStepAtMirrorFrames.Adjoint.adjointAction_smul g _ X
  have h := bilinear_eq_inner_mul_of_invariant
    ((secondDeriv (flatAction (n := n) a L u)).bilinearComp (atBondCLM b) (atBondCLM b')) (fun g X X' => by
      simp only [ContinuousLinearMap.bilinearComp_apply, atBondCLM_apply]
      rw [← hone, ← hone]
      exact secondDeriv_invariant hcp hT g (flatAction_adjoint hla hgi a hL h2 u g) _ _) X X'
  simp only [ContinuousLinearMap.bilinearComp_apply, atBondCLM_apply] at h
  exact h
private def pairLine (b b' : TorusBond (n * L)) (X X' : imaginaryQuaternions) :
    (Fin 2 → ℝ) →L[ℝ] (TorusBond (n * L) → imaginaryQuaternions) :=
  (ContinuousLinearMap.proj 0).smulRight (atBond b X) + (ContinuousLinearMap.proj 1).smulRight (atBond b' X')
omit [NeZero n] [NeZero L] in
private theorem pairLine_apply (b b' : TorusBond (n * L)) (X X' : imaginaryQuaternions) (σ : Fin 2 → ℝ)
    (b'' : TorusBond (n * L)) :
    pairLine b b' X X' σ b'' = ∑ l, if ![b, b'] l = b'' then σ l • ![X, X'] l else 0 := by
  simp only [pairLine, add_apply, ContinuousLinearMap.smulRight_apply, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
    atBond, bondIndicator, Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.proj_apply]
  by_cases h1 : b'' = b <;> by_cases h3 : b'' = b' <;>
    simp [h1, h3, eq_comm] <;> simp_all [eq_comm]
omit [NeZero n] [NeZero L] in
private theorem pairLine_single_zero (b b' : TorusBond (n * L)) (X X' : imaginaryQuaternions) :
    pairLine b b' X X' (Pi.single 0 1) = atBond b X := by
  simp [pairLine]
omit [NeZero n] [NeZero L] in
private theorem pairLine_single_one (b b' : TorusBond (n * L)) (X X' : imaginaryQuaternions) :
    pairLine b b' X X' (Pi.single 1 1) = atBond b' X' := by
  simp [pairLine]
private theorem torusChartField_pairLine (hL : Odd L) (h2 : 2 ≤ n) {b b' : TorusBond (n * L)}
    (hb : b ∈ chartBonds L n) (hb' : b' ∈ chartBonds L n) (X X' : imaginaryQuaternions) (σ : Fin 2 → ℝ) :
    torusChartField L (pairLine b b' X X' σ) (trivialField n) = perturb ![b, b'] ![X, X'] σ (trivialField (n * L)) := by
  have hoff : ∀ b'', b'' ∉ chartBonds L n → pairLine b b' X X' σ b'' = 0 := by
    intro b'' hb''
    have h1 : b'' ≠ b := fun e => hb'' (e ▸ hb)
    have h3 : b'' ≠ b' := fun e => hb'' (e ▸ hb')
    rw [pairLine_apply]
    simp [Fin.sum_univ_two, h1.symm, h3.symm]
  funext x i
  rw [torusChartField_trivial hL h2 _ hoff, pairLine_apply]
  simp [perturb, trivialField]
private theorem maxwellKernel_eq_secondDeriv (hcp : Calculus.CompositeDerivativesAtPoint) {a : ℝ} (hL : Odd L)
    (h2 : 2 ≤ n) (u : ℕ) (hT : AnalyticAt ℝ (flatAction (n := n) a L u) 0) {b b' : TorusBond (n * L)}
    (hb : b ∈ chartBonds L n) (hb' : b' ∈ chartBonds L n) :
    maxwellKernel a L u b b' = secondDeriv (flatAction a L u) (atBond b unitGenerator) (atBond b' unitGenerator) := by
  have h := secondDeriv_comp hcp (pairLine b b' unitGenerator unitGenerator) hT fun l => Pi.single l 1
  rw [pairLine_single_zero, pairLine_single_one] at h
  rw [← h]
  have e : (fun σ : Fin 2 → ℝ => actionAtLevel a L u Finset.univ
      (perturb ![b, b'] ![unitGenerator, unitGenerator] σ (trivialField (n * L)))) =
      fun σ => flatAction a L u (pairLine b b' unitGenerator unitGenerator σ) := by
    funext σ
    unfold flatAction
    rw [torusChartField_pairLine hL h2 hb hb']
  show iteratedFDeriv ℝ 2 (fun σ : Fin 2 → ℝ => actionAtLevel a L u Finset.univ
      (perturb ![b, b'] ![unitGenerator, unitGenerator] σ (trivialField (n * L)))) 0 (fun l => Pi.single l 1) = _
  rw [e]
end ActionForm
section Requirements
variable {L n : ℕ} [NeZero n] [NeZero L]
private theorem norm_unitGenerator_sq : ‖(unitGenerator : ℍ[ℝ])‖ ^ 2 = 1 := by
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  simp [unitGenerator]
private theorem secondDeriv_flatAction_diag (hcp : Calculus.CompositeDerivativesAtPoint) {a : ℝ} (hL : Odd L)
    (h2 : 2 ≤ n) (u : ℕ) (hT : AnalyticAt ℝ (flatAction (n := n) a L u) 0) {φ : TorusBond (n * L) → ℝ}
    (hφ : VanishesOnTrees L φ) :
    secondDeriv (flatAction a L u) (fun b => φ b • unitGenerator) (fun b => φ b • unitGenerator) =
      maxwellForm a L u φ φ := by
  classical
  have e : (fun b => φ b • unitGenerator) = ∑ b : TorusBond (n * L), φ b • atBond b unitGenerator := by
    funext b'
    simp only [Finset.sum_apply, Pi.smul_apply, atBond, bondIndicator, smul_smul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single b' (fun b _ hb => by simp [hb.symm]) (by simp)]
    simp
  rw [e]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  unfold maxwellForm
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  by_cases hb : b ∈ chartBonds L n
  · by_cases hb' : b' ∈ chartBonds L n
    · rw [maxwellKernel_eq_secondDeriv hcp hL h2 u hT hb hb', secondDeriv_symm hT (atBond b' unitGenerator)]
      ring
    · rw [hφ b' hb']
      ring
  · rw [hφ b hb]
    ring
private theorem secondDeriv_sum_flatFit_diag (hcp : Calculus.CompositeDerivativesAtPoint)
    (hfit : BlockFitAnalyticAlongTranslates) (hL : Odd L) (h2 : 2 ≤ n) {φ : TorusBond (n * L) → ℝ}
    (hφ : VanishesOnTrees L φ) :
    secondDeriv (fun w => ∑ c : TorusBond n, flatFit L c w) (fun b => φ b • unitGenerator)
      (fun b => φ b • unitGenerator) = contourPairing L φ φ := by
  rw [secondDeriv_sum _ fun c _ => analyticAt_flatFit hfit hL h2 c]
  unfold contourPairing
  refine Finset.sum_congr rfl fun c _ => ?_
  have e : (fun b => φ b • unitGenerator) = twoDirections φ φ unitGenerator 0 := by
    funext b
    simp [twoDirections]
  rw [e, secondDeriv_flatFit_diag hcp hfit hL h2 hφ hφ]
  simp only [ZeroMemClass.coe_zero, smul_zero, add_zero]
  rw [norm_smul, mul_pow, norm_unitGenerator_sq, Real.norm_eq_abs, sq_abs]
  ring
private theorem secondDeriv_sum_flatFit_atBond (hcp : Calculus.CompositeDerivativesAtPoint)
    (hfit : BlockFitAnalyticAlongTranslates) (hL : Odd L) (h2 : 2 ≤ n) {b b' : TorusBond (n * L)}
    (hb : b ∈ chartBonds L n) (hb' : b' ∈ chartBonds L n) (X X' : imaginaryQuaternions) :
    secondDeriv (fun w => ∑ c : TorusBond n, flatFit L c w) (atBond b X) (atBond b' X') =
      inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * contourPairing L (bondIndicator b) (bondIndicator b') := by
  rw [secondDeriv_sum _ fun c _ => analyticAt_flatFit hfit hL h2 c]
  unfold contourPairing
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => secondDeriv_flatFit_atBond hcp hfit hL h2 hb hb' X X' c
private theorem mem_chordBonds_iff (hL : Odd L) (h2 : 2 ≤ n) (u : ℕ)
    (b : (torusFrame L u n).Site (torusFrame L u n).depth × Fin 4) :
    b ∈ chordBonds (finiteCells (torusFrame L u n)) ↔ (toTorusSite (n * L) b.1, b.2) ∈ chartBonds L n := by
  have hn : ∀ i, (torusFrame L u n).extent i = n := fun _ => rfl
  have hn' : ∀ i, (stepBlockFrame L n).extent i = n := fun _ => rfl
  have hs : ∀ i, 2 ≤ (torusFrame L u n).extent i := fun _ => h2
  have t1 := isAxialTreeBond_torusSiteInFrame_iff (F := torusFrame L u n) hn hL h2 (toTorusSite (n * L) b.1) b.2
  have e0 : torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth (toTorusSite (n * L) b.1) = b.1 :=
    torusSiteInFrame_toTorusSite (period_depth_of_extent hn) b.1
  have t1' := (Iff.of_eq (congrArg (fun z => IsAxialTreeBond (F := torusFrame L u n) (z, b.2)) e0.symm)).trans t1
  have t2 := isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame L n) hn' hL h2 (toTorusSite (n * L) b.1) b.2
  have hb : b ∈ innerBonds (finiteCells (torusFrame L u n)) (torusFrame L u n).depth := by
    unfold innerBonds
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨mem_sitesOfCells_depth hL hs hn _, Finset.mem_univ _⟩, mem_sitesOfCells_depth hL hs hn _⟩
  simp only [chordBonds, chartBonds, Finset.mem_filter, Finset.mem_univ, true_and, hb]
  exact not_congr (t1'.trans t2.symm)
private theorem coercive_level (hcp : Calculus.CompositeDerivativesAtPoint) (hla : MinimalActionTransfer)
    (hker : ChartEnergyKernelBound) (hfit : BlockFitAnalyticAlongTranslates) {a : ℝ} (ha : 1 ≤ a)
    {c : ColdChainParameters} (hL : Odd L) (hL40 : 2 ^ 40 ≤ L) (hc : c.Admissible a L) (h64 : 64 ≤ n) (u : ℕ)
    {φ : TorusBond (n * L) → ℝ} (hφ : VanishesOnTrees L φ) :
    c.lam * ∑ b, φ b ^ 2 ≤ maxwellForm a L u φ φ + a * contourPairing L φ φ := by
  have h2 : 2 ≤ n := by omega
  have hn : ∀ i, (torusFrame L u n).extent i = n := fun _ => rfl
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  have hcl := hc.estimates (torusFrame L u n) c.σA (uniformField _ _) ⟨rfl, n, h64, fun _ => rfl⟩ hσ le_rfl
    (isSmallCurvature_one hσ)
  set u₀ : TorusBond (n * L) → imaginaryQuaternions := fun b => φ b • unitGenerator with hu₀
  have hdw : ∀ b : (torusFrame L u n).Site (torusFrame L u n).depth × Fin 4,
      b ∉ chordBonds (finiteCells (torusFrame L u n)) → frameCoords L u u₀ b.1 b.2 = 0 := by
    intro b hb
    have h1 := (not_congr (mem_chordBonds_iff hL h2 u b)).mp hb
    show φ (toTorusSite (n * L) b.1, b.2) • unitGenerator = 0
    rw [hφ _ h1, zero_smul]
  have hρ : 0 ≤ c.ρA := hc.classical.1.1.le
  have hfl := hcl.hessian (fun _ _ => 0) (frameCoords L u u₀) (fun _ _ => rfl) hdw
    (fun _ _ => by simpa using hρ) (by
      rw [chartedField_zero_uniform]
      intro p _
      unfold plaquetteDefect plaquetteHolonomy
      rw [pathHolonomy_one]
      simpa using hσ)
  have hLv := analyticAt_levelEnergy (n := n) hla hker ha hL hL40 hc h64 u
  have hG := analyticAt_flatAction (n := n) hla hker hfit ha hL hL40 hc h64 u
  have hΦ : AnalyticAt ℝ (fun w : TorusBond (n * L) → imaginaryQuaternions => ∑ c : TorusBond n, flatFit L c w) 0 :=
    Finset.analyticAt_fun_sum _ fun c _ => analyticAt_flatFit hfit hL h2 c
  have e1 : (fun τ : ℝ => blockEnergy a (finiteCells (torusFrame L u n)) (torusFrame L u n).depth
      (chartedField (fun x i => (fun _ _ => (0 : imaginaryQuaternions)) x i + τ • frameCoords L u u₀ x i)
        (uniformField _ _)) (uniformField _ _)) =
      fun τ : ℝ => levelEnergy a L u (τ • u₀) (trivialField n) := by
    funext τ
    rw [levelEnergy_eq_chartedEnergy hla a hL h2]
    have e2 : frameCoords L u (τ • u₀) = fun x i => (fun _ _ => (0 : imaginaryQuaternions)) x i +
        τ • frameCoords L u u₀ x i := by
      funext x i
      simp [frameCoords]
    rw [e2]
    rfl
  rw [e1, secondDeriv_line hcp hLv u₀] at hfl
  have e3 : secondDeriv (fun w => levelEnergy a L u w (trivialField n)) u₀ u₀ =
      maxwellForm a L u φ φ + a * contourPairing L φ φ := by
    have e4 : (fun w : TorusBond (n * L) → imaginaryQuaternions => levelEnergy a L u w (trivialField n)) =
        fun w => flatAction a L u w + a * ∑ c : TorusBond n, flatFit L c w := rfl
    have hΦa : AnalyticAt ℝ (fun w : TorusBond (n * L) → imaginaryQuaternions =>
        a * ∑ c : TorusBond n, flatFit L c w) 0 :=
      analyticAt_const.mul hΦ
    rw [e4, secondDeriv_add hG hΦa, secondDeriv_const_mul a hΦ, secondDeriv_flatAction_diag hcp hL h2 u hG hφ,
      secondDeriv_sum_flatFit_diag hcp hfit hL h2 hφ]
  rw [e3] at hfl
  have e5 : ∑ b ∈ chordBonds (finiteCells (torusFrame L u n)), ‖frameCoords L u u₀ b.1 b.2‖ ^ 2 =
      ∑ b, φ b ^ 2 := by
    have hp := period_depth_of_extent (F := torusFrame L u n) hn
    have e6 : ∑ b ∈ chordBonds (finiteCells (torusFrame L u n)), ‖frameCoords L u u₀ b.1 b.2‖ ^ 2 =
        ∑ b ∈ chartBonds L n, φ b ^ 2 := by
      refine Finset.sum_nbij' (fun b => (toTorusSite (n * L) b.1, b.2))
        (fun b => (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1, b.2)) ?_ ?_ ?_ ?_ ?_
      · intro b hb
        exact (mem_chordBonds_iff hL h2 u b).mp hb
      · intro b hb
        refine (mem_chordBonds_iff hL h2 u _).mpr ?_
        have e : (toTorusSite (n * L) (torusSiteInFrame (torusFrame L u n) (torusFrame L u n).depth b.1), b.2) = b :=
          Prod.ext (toTorusSite_torusSiteInFrame hp b.1) rfl
        exact e.symm ▸ hb
      · intro b _
        exact Prod.ext (torusSiteInFrame_toTorusSite hp b.1) rfl
      · intro b _
        exact Prod.ext (toTorusSite_torusSiteInFrame hp b.1) rfl
      · intro b _
        show ‖φ (toTorusSite (n * L) b.1, b.2) • unitGenerator‖ ^ 2 = _
        have hnu : ‖unitGenerator‖ ^ 2 = 1 := norm_unitGenerator_sq
        rw [norm_smul, mul_pow, hnu, Real.norm_eq_abs, sq_abs, mul_one]
    rw [e6]
    refine Finset.sum_subset (Finset.subset_univ _) fun b _ hb => ?_
    rw [hφ b hb]
    simp
  rw [e5] at hfl
  exact hfl
end Requirements
section Assembly
variable {L n : ℕ} [NeZero n] [NeZero L]
private theorem levelEnergy_nonneg (hla : MinimalActionTransfer) {a : ℝ} (ha : 0 ≤ a) (hL : Odd L) (h2 : 2 ≤ n)
    (u : ℕ) (w : TorusBond (n * L) → imaginaryQuaternions) (V : TorusField n) : 0 ≤ levelEnergy a L u w V := by
  rw [levelEnergy_eq_chartedEnergy hla a hL h2]
  exact add_nonneg (minimalAction_nonneg ha _ _ _)
    (mul_nonneg ha (Finset.sum_nonneg fun c _ => blockFit_nonneg _ _ _))
private theorem flatAction_zero (hla : MinimalActionTransfer) (hft : BlockAverages.flatTopVanishingStatement)
    {a : ℝ} (ha : 0 ≤ a) (hL : Odd L) (h2 : 2 ≤ n) (u : ℕ) : flatAction (n := n) a L u 0 = 0 := by
  unfold flatAction
  rw [actionAtLevel_eq_minimalAction hla a hL h2]
  have e : readAtLevel (torusFrame L u n) (torusFrame L u n).depth
      (torusChartField L (0 : TorusBond (n * L) → imaginaryQuaternions) (trivialField n)) =
      BlockAverages.flatField (torusFrame L u n) (torusFrame L u n).depth := by
    funext x i
    have h := torusChartField_trivial hL h2 (0 : TorusBond (n * L) → imaginaryQuaternions) (fun _ _ => rfl)
      (toTorusSite (n * L) x) i
    exact h.trans TorusFields.expUnit_zero
  rw [e]
  exact (hft (torusFrame L u n) a _ ha hL).2.1 _
private theorem first_deriv_vanishes (hla : MinimalActionTransfer) (hft : BlockAverages.flatTopVanishingStatement)
    {a : ℝ} (ha : 0 ≤ a) (hL : Odd L) (h2 : 2 ≤ n) (t : ℕ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (b : TorusBond (n * L)) (X : imaginaryQuaternions) :
    mixtureIteratedDeriv a L t θ (![Sum.inl b] : Fin 1 → MixedBond L n) ![X] = 0 := by
  set f : (Fin 1 → ℝ) → ℝ := fun σ => interpChartEnergy a L t θ
    (fineCoordPerturb L (![Sum.inl b] : Fin 1 → MixedBond L n) ![X] σ)
    (coarseFieldPerturb L (![Sum.inl b] : Fin 1 → MixedBond L n) ![X] σ) with hf
  have e0 : fineCoordPerturb L (![Sum.inl b] : Fin 1 → MixedBond L n) ![X] 0 = 0 := by
    funext b'
    simp [fineCoordPerturb]
  have e1 : coarseFieldPerturb L (![Sum.inl b] : Fin 1 → MixedBond L n) ![X] 0 = trivialField n := by
    funext x i
    simp [coarseFieldPerturb, trivialField, TorusFields.expUnit_zero]
  have hz : f 0 = 0 := by
    simp only [hf, e0, e1]
    rw [interpChartEnergy_trivial, flatAction_zero hla hft ha hL h2, flatAction_zero hla hft ha hL h2]
    simp [flatFit_zero hL h2]
  have hmin : IsLocalMin f 0 := by
    refine Filter.Eventually.of_forall fun σ => ?_
    rw [hz]
    simp only [hf]
    rw [interpChartEnergy_eq_convex]
    exact add_nonneg (mul_nonneg (by linarith) (levelEnergy_nonneg hla ha hL h2 _ _ _))
      (mul_nonneg h0 (levelEnergy_nonneg hla ha hL h2 _ _ _))
  show iteratedFDeriv ℝ 1 f 0 _ = 0
  rw [iteratedFDeriv_one_apply, hmin.fderiv_eq_zero]
  rfl
private theorem maxwellForm_bondIndicator (a : ℝ) (u : ℕ) (b b' : TorusBond (n * L)) :
    maxwellForm a L u (bondIndicator b) (bondIndicator b') = maxwellKernel a L u b b' := by
  classical
  unfold maxwellForm bondIndicator
  rw [Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp)]
  rw [Finset.sum_eq_single b' (fun x _ hx => by simp [hx]) (by simp)]
  simp
private theorem second_deriv_formula (hcp : Calculus.CompositeDerivativesAtPoint) (hla : MinimalActionTransfer)
    (hker : ChartEnergyKernelBound) (hfit : BlockFitAnalyticAlongTranslates) (hgi : MinimalActionGaugeInvariant)
    {a : ℝ} (ha : 1 ≤ a) {c : ColdChainParameters} (hL : Odd L) (hL40 : 2 ^ 40 ≤ L) (hc : c.Admissible a L)
    (h64 : 64 ≤ n) (t : ℕ) (θ : ℝ) {b b' : TorusBond (n * L)} (hb : b ∈ chartBonds L n)
    (hb' : b' ∈ chartBonds L n) (X X' : imaginaryQuaternions) :
    mixtureIteratedDeriv a L t θ (![Sum.inl b, Sum.inl b'] : Fin 2 → MixedBond L n) ![X, X'] =
      inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * interpForm a L t θ (bondIndicator b) (bondIndicator b') := by
  have h2 : 2 ≤ n := by omega
  have hG0 := analyticAt_flatAction (n := n) hla hker hfit ha hL hL40 hc h64 t
  have hG1 := analyticAt_flatAction (n := n) hla hker hfit ha hL hL40 hc h64 (t + 1)
  have hΦ : AnalyticAt ℝ (fun w : TorusBond (n * L) → imaginaryQuaternions => ∑ c : TorusBond n, flatFit L c w) 0 :=
    Finset.analyticAt_fun_sum _ fun c _ => analyticAt_flatFit hfit hL h2 c
  have hc2 : (![Sum.inl b, Sum.inl b'] : Fin 2 → MixedBond L n) = fineBonds ![b, b'] := by
    funext l
    fin_cases l <;> rfl
  have hA0 : AnalyticAt ℝ (fun w : TorusBond (n * L) → imaginaryQuaternions => (1 - θ) * flatAction a L t w) 0 :=
    analyticAt_const.mul hG0
  have hA1 : AnalyticAt ℝ (fun w : TorusBond (n * L) → imaginaryQuaternions => θ * flatAction a L (t + 1) w) 0 :=
    analyticAt_const.mul hG1
  have hA2 : AnalyticAt ℝ (fun w : TorusBond (n * L) → imaginaryQuaternions =>
      a * ∑ c : TorusBond n, flatFit L c w) 0 := analyticAt_const.mul hΦ
  have hA01 : AnalyticAt ℝ (fun w : TorusBond (n * L) → imaginaryQuaternions =>
      (1 - θ) * flatAction a L t w + θ * flatAction a L (t + 1) w) 0 :=
    hA0.add hA1
  set Sf : (TorusBond (n * L) → imaginaryQuaternions) → ℝ := fun w =>
    (1 - θ) * flatAction a L t w + θ * flatAction a L (t + 1) w + a * ∑ c : TorusBond n, flatFit L c w with hSf
  have hS : AnalyticAt ℝ Sf 0 := hA01.add hA2
  have e : (fun σ : Fin 2 → ℝ => interpChartEnergy a L t θ (fineCoordPerturb L (fineBonds ![b, b']) ![X, X'] σ)
      (coarseFieldPerturb L (fineBonds ![b, b']) ![X, X'] σ)) = fun σ => Sf (pairLine b b' X X' σ) := by
    funext σ
    rw [coarseFieldPerturb_fineBonds, interpChartEnergy_trivial, ← fineCoordPerturb_fineBonds]
    have e2 : (fun b'' => ∑ l, if ![b, b'] l = b'' then σ l • ![X, X'] l else 0) = pairLine b b' X X' σ := by
      funext b''
      exact (pairLine_apply b b' X X' σ b'').symm
    rw [e2]
  have h := secondDeriv_comp hcp (pairLine b b' X X') hS fun l => Pi.single l 1
  rw [pairLine_single_zero, pairLine_single_one] at h
  rw [hc2]
  show iteratedFDeriv ℝ 2 (fun σ : Fin 2 → ℝ => interpChartEnergy a L t θ
      (fineCoordPerturb L (fineBonds ![b, b']) ![X, X'] σ)
      (coarseFieldPerturb L (fineBonds ![b, b']) ![X, X'] σ)) 0 (fun l => Pi.single l 1) = _
  rw [e, h]
  rw [hSf, secondDeriv_add hA01 hA2, secondDeriv_add hA0 hA1, secondDeriv_const_mul _ hG0,
    secondDeriv_const_mul _ hG1, secondDeriv_const_mul _ hΦ,
    secondDeriv_flatAction_atBond hcp hla hgi hL h2 t hG0, secondDeriv_flatAction_atBond hcp hla hgi hL h2 (t + 1) hG1,
    ← maxwellKernel_eq_secondDeriv hcp hL h2 t hG0 hb hb', ← maxwellKernel_eq_secondDeriv hcp hL h2 (t + 1) hG1 hb hb',
    secondDeriv_sum_flatFit_atBond hcp hfit hL h2 hb hb']
  unfold interpForm interpKinetic
  rw [maxwellForm_bondIndicator, maxwellForm_bondIndicator]
  ring
end Assembly
section Kernels
variable {L n : ℕ} [NeZero n] [NeZero L]
omit [NeZero n] [NeZero L] in
private theorem directionVector_directionOf (u : ℕ) (p : MixedBond L n) (X : imaginaryQuaternions) :
    directionVector (directionOf L u p X) = X := by
  cases p <;> rfl
private theorem directionCell_directionOf (u : ℕ) (p : MixedBond L n) (X : imaginaryQuaternions) :
    directionCell (directionOf L u p X) =
      torusSiteInFrame (torusFrame L u n) (torusFrame L u n).top (mixedBondSite L p) := by
  rcases p with b | d
  · exact enclosingCell_torusSiteInFrame (F := torusFrame L u n) (fun _ => rfl) b.1
  · rfl
private theorem directionDiameter_directionOf (u k : ℕ) (c : Fin k → MixedBond L n)
    (X : Fin k → imaginaryQuaternions) :
    directionDiameter (fun l => directionOf L u (c l) (X l)) = mixedBondDiam L c := by
  have hn : ∀ i, (torusFrame L u n).extent i = n := fun _ => rfl
  unfold directionDiameter mixedBondDiam
  refine Finset.sup_congr rfl fun l _ => Finset.sup_congr rfl fun l' _ => ?_
  rw [directionCell_directionOf, directionCell_directionOf]
  have : ∀ i, NeZero ((torusFrame L u n).period (torusFrame L u n).top i) := fun i =>
    period_neZero (period_top_of_extent hn) i
  exact cellSupDist_torusSiteInFrame (period_top_of_extent hn) _ _
private theorem iteratedFDeriv_convex {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A B : E → ℝ}
    (hA : AnalyticAt ℝ A 0) (hB : AnalyticAt ℝ B 0) (r s : ℝ) (k : ℕ) (v : Fin k → E) :
    iteratedFDeriv ℝ k (fun σ => r * A σ + s * B σ) 0 v =
      r * iteratedFDeriv ℝ k A 0 v + s * iteratedFDeriv ℝ k B 0 v := by
  have hrA : AnalyticAt ℝ (r • A) 0 := analyticAt_const.smul hA
  have hsB : AnalyticAt ℝ (s • B) 0 := analyticAt_const.smul hB
  have e : (fun σ => r * A σ + s * B σ) = r • A + s • B := rfl
  rw [e, iteratedFDeriv_add_apply hrA.contDiffAt hsB.contDiffAt, iteratedFDeriv_const_smul_apply hA.contDiffAt,
    iteratedFDeriv_const_smul_apply hB.contDiffAt]
  simp
private theorem kernel_decay_bound (hla : MinimalActionTransfer) (hker : ChartEnergyKernelBound) {a : ℝ}
    (ha : 1 ≤ a) {c : ColdChainParameters} (hL : Odd L) (hL40 : 2 ^ 40 ≤ L) (hc : c.Admissible a L) (h64 : 64 ≤ n)
    {Ck : ℕ → ℝ}
    (hC : ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
      IsBlockTorus L F → IsAdmissibleChartPoint L c.σA w V → ∀ (k : ℕ) (q : Fin k → ChartDirection F), 2 ≤ k →
        (∀ l, ‖directionVector (q l)‖ = 1) →
        |chartMixedDeriv a w V q| ≤ Ck k * Real.exp (-(8 * c.δ₁ * directionDiameter q)))
    (t : ℕ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (k : ℕ) (p : Fin k → MixedBond L n)
    (X : Fin k → imaginaryQuaternions) (hk : 2 ≤ k) (hX : AreUnitVectors X) :
    |mixtureIteratedDeriv a L t θ p X| ≤ Ck k * Real.exp (-(8 * c.δ₁ * mixedBondDiam L p)) := by
  have h2 : 2 ≤ n := by omega
  obtain ⟨Ck', -, hC'⟩ := hker a L c ha hL hL40 hc
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  have hanal : ∀ u, AnalyticAt ℝ (chartRestriction (F := torusFrame L u n) a (fun _ _ => 0)
      (uniformField (torusFrame L u n) (torusFrame L u n).top) (fun l => directionOf L u (p l) (X l))) 0 := fun u =>
    (hC' (torusFrame L u n) (fun _ _ => 0) (uniformField _ _) ⟨rfl, n, h64, fun _ => rfl⟩
      (isAdmissibleChartPoint_zero hσ hL.pos) k _).1
  have hb : ∀ u, |chartMixedDeriv (F := torusFrame L u n) a (fun _ _ => 0)
      (uniformField (torusFrame L u n) (torusFrame L u n).top) (fun l => directionOf L u (p l) (X l))| ≤
      Ck k * Real.exp (-(8 * c.δ₁ * mixedBondDiam L p)) := fun u => by
    have h := hC (torusFrame L u n) (fun _ _ => 0) (uniformField _ _) ⟨rfl, n, h64, fun _ => rfl⟩
      (isAdmissibleChartPoint_zero hσ hL.pos) k (fun l => directionOf L u (p l) (X l)) hk (fun l => by
        rw [directionVector_directionOf]
        exact hX l)
    rwa [directionDiameter_directionOf] at h
  have e : (fun σ : Fin k → ℝ => interpChartEnergy a L t θ (fineCoordPerturb L p X σ) (coarseFieldPerturb L p X σ)) =
      fun σ => (1 - θ) * chartRestriction (F := torusFrame L t n) a (fun _ _ => 0)
          (uniformField (torusFrame L t n) (torusFrame L t n).top) (fun l => directionOf L t (p l) (X l)) σ +
        θ * chartRestriction (F := torusFrame L (t + 1) n) a (fun _ _ => 0)
          (uniformField (torusFrame L (t + 1) n) (torusFrame L (t + 1) n).top)
          (fun l => directionOf L (t + 1) (p l) (X l)) σ := by
    funext σ
    rw [interpChartEnergy_eq_convex, levelEnergy_eq_chartRestriction hla a hL h2,
      levelEnergy_eq_chartRestriction hla a hL h2]
  unfold mixtureIteratedDeriv
  rw [e, iteratedFDeriv_convex (hanal t) (hanal (t + 1))]
  have b0 := hb t
  have b1 := hb (t + 1)
  unfold chartMixedDeriv at b0 b1
  set K0 := iteratedFDeriv ℝ k (chartRestriction (F := torusFrame L t n) a (fun _ _ => 0)
      (uniformField (torusFrame L t n) (torusFrame L t n).top) (fun l => directionOf L t (p l) (X l))) 0
      fun l => Pi.single l 1
  set K1 := iteratedFDeriv ℝ k (chartRestriction (F := torusFrame L (t + 1) n) a (fun _ _ => 0)
      (uniformField (torusFrame L (t + 1) n) (torusFrame L (t + 1) n).top)
      (fun l => directionOf L (t + 1) (p l) (X l))) 0 fun l => Pi.single l 1
  set B := Ck k * Real.exp (-(8 * c.δ₁ * mixedBondDiam L p))
  have h3 : |(1 - θ) * K0 + θ * K1| ≤ (1 - θ) * |K0| + θ * |K1| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg (by linarith : 0 ≤ 1 - θ)]
  have h4 : (1 - θ) * |K0| ≤ (1 - θ) * B := mul_le_mul_of_nonneg_left b0 (by linarith)
  have h5 : θ * |K1| ≤ θ * B := mul_le_mul_of_nonneg_left b1 h0
  linarith
end Kernels
private theorem flatField_jet_bounds (hla : MinimalActionTransfer) (hker : ChartEnergyKernelBound)
    (hk8 : Estimates.ChartEnergyKernelDecay) (hfit : BlockFitAnalyticAlongTranslates)
    (hcp : Calculus.CompositeDerivativesAtPoint) (hgi : MinimalActionGaugeInvariant)
    (hft : BlockAverages.flatTopVanishingStatement) {a : ℝ} (ha : 1 ≤ a) {L : ℕ} [NeZero L] (hL : Odd L)
    (hL40 : 2 ^ 40 ≤ L) {c : ColdChainParameters} (hc : c.Admissible a L) :
    ∃ Cm : ℕ → ℝ, ∀ (t n : ℕ) [NeZero n] (θ : ℝ), 64 ≤ n → 0 ≤ θ → θ ≤ 1 →
      (∀ b ∈ chartBonds L n, ∀ X : imaginaryQuaternions, mixtureIteratedDeriv a L t θ ![Sum.inl b] ![X] = 0) ∧
      (∀ b ∈ chartBonds L n, ∀ b' ∈ chartBonds L n, ∀ X X' : imaginaryQuaternions,
        mixtureIteratedDeriv a L t θ ![Sum.inl b, Sum.inl b'] ![X, X'] =
          inner ℝ (X : Quaternion ℝ) (X' : Quaternion ℝ) * interpForm a L t θ (bondIndicator b) (bondIndicator b')) ∧
      (∀ φ : TorusBond (n * L) → ℝ, VanishesOnTrees L φ → c.lam * ∑ b, φ b ^ 2 ≤ interpForm a L t θ φ φ) ∧
      ∀ (k : ℕ) (p : Fin k → MixedBond L n) (X : Fin k → imaginaryQuaternions), 2 ≤ k → AreUnitVectors X →
        |mixtureIteratedDeriv a L t θ p X| ≤ Cm k * Real.exp (-(8 * c.δ₁ * mixedBondDiam L p)) := by
  obtain ⟨Ck, -, hC⟩ := hk8 a L c ha hL hL40 hc
  refine ⟨Ck, fun t n _ θ h64 h0 h1 => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro b _ X
    exact first_deriv_vanishes hla hft (by linarith) hL (by omega) t h0 h1 b X
  · intro b hb b' hb' X X'
    exact second_deriv_formula hcp hla hker hfit hgi ha hL hL40 hc h64 t θ hb hb' X X'
  · intro φ hφ
    have f0 := coercive_level (n := n) hcp hla hker hfit ha hL hL40 hc h64 t hφ
    have f1 := coercive_level (n := n) hcp hla hker hfit ha hL hL40 hc h64 (t + 1) hφ
    have m0 := mul_le_mul_of_nonneg_left f0 (by linarith : 0 ≤ 1 - θ)
    have m1 := mul_le_mul_of_nonneg_left f1 h0
    unfold interpForm interpKinetic
    nlinarith
  · intro k p X hk hX
    exact kernel_decay_bound hla hker ha hL hL40 hc h64 hC t h0 h1 k p X hk hX
theorem flatFieldJetBounds_holds (hla : MinimalActionTransfer) (hker : ChartEnergyKernelBound)
    (hk8 : Estimates.ChartEnergyKernelDecay) (hfit : BlockFitAnalyticAlongTranslates)
    (hcp : Calculus.CompositeDerivativesAtPoint) (hgi : MinimalActionGaugeInvariant)
    (hft : BlockAverages.flatTopVanishingStatement) : flatFieldJetBoundsStatement := by
  intro a ha
  refine ⟨2 ^ 40, fun L hL hL₀ c hc => ⟨0, fun Ct _ => ⟨1, one_pos, fun κ h0 hκ => ⟨1, one_pos, fun η₃ h0 h1 hη =>
    ⟨0, fun nss _ => ⟨1, one_pos, fun σ h0 hσ p hp => ⟨0, fun Cs _ E hE => ⟨0, fun n₀ _ => ⟨0, fun CE _ =>
      ⟨0, fun y₁ _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  intro _ _ hLz
  have hLz' : NeZero L := hLz
  obtain ⟨Cm, h⟩ := flatField_jet_bounds hla hker hk8 hfit hcp hgi hft ha hL hL₀ hc
  refine ⟨Cm, fun t n _ θ h64 h0 h1 => ?_⟩
  obtain ⟨c1, c2, c3, c4⟩ := h t n θ h64 h0 h1
  exact ⟨c1, c2, c3, c4⟩
end MixtureJets
end YangMills.Construction
end
