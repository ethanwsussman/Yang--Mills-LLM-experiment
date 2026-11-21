import YangMills.Construction.ColdChainAtEveryLevel.ComparisonOfAgreeingPairsProof
import YangMills.Construction.ColdStepAtMirrorFrames.ChartIsReadOffItsFieldProof
import YangMills.Construction.RunningCouplingSlope.LeastActionIsWellAtTheTopProof
import YangMills.Construction.RunningCouplingSlope.LeastChartEnergyIsAnalyticNearTheFlatFieldProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ReferenceDensity TorusFields BondCoordinates
open ColdStepAtMirrorFrames hiding bondSpread
open GaugeFixing hiding siteOfCoords_zero
section Levels
private def fintypeSiteOfPos (F : BlockFrame) (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) (j : ℕ) :
    Fintype (F.Site j) :=
  haveI : ∀ i, NeZero (F.period j i) := fun i => ⟨by
    unfold BlockFrame.period
    exact (Nat.mul_pos (hs i) (pow_pos hL _)).ne'⟩
  inferInstance
private theorem nondegenerate_at_depth (hW : WilsonActionNondegenerate) (hX : NondegenerateAcrossFrames)
    (hT : minimalActionNondegeneratePropagatesStatement) {a : ℝ} (ha : 0 < a) {L : ℕ} (hL : Odd L) :
    ∀ (t n : ℕ), 2 ≤ n → ∀ (inst : Fintype ((torusFrame L t n).Site t)),
      IsNondegenerateAtTrivial (F := torusFrame L t n) (k := t)
        (minimalAction a (finiteCells (torusFrame L t n)) t) := by apply _root_.YangMills.SharedProofs.p33643 <;> assumption
end Levels
section Charts
variable {F : BlockFrame}
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
private theorem chartedField_of_isAxialTreeBond (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (b : F.Site F.depth × Fin 4) (hb : IsAxialTreeBond b) :
    chartedField w V b.1 b.2 = 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartDeterminedByField.chartedField_eq_one <;> assumption
private theorem gauge_eq_one_of_cellCentre (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions} {V : F.GaugeField F.top}
    {g : F.Site F.depth → UnitQuaternion} (hg : ∀ z, g (cellCentre F.depth z) = 1)
    (hgw : chartedField w' V = BlockAverages.gaugeTransform g (chartedField w V)) (x : F.Site F.depth) : g x = 1 := by
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  obtain ⟨hmem, hx⟩ := cellOffset_mem_and_eq hs' hL x
  have hwalk : g (cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth (cellOffset x)) =
      g (cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth 0) :=
   apply_eq_apply_zero_of_tree_moves F.blockSide
    (fun o => g (cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth o)) (fun o i ho ho' hz => by
    have hb := isAxialTreeBond_cellCentre_add hs' hL (enclosingCell x) o i ho ho' hz
    have hlink := congrFun (congrFun hgw (cellCentre F.depth (enclosingCell x) + siteOfCoords F.depth o)) i
    rw [chartedField_of_isAxialTreeBond w' V (_, i) hb] at hlink
    unfold BlockAverages.gaugeTransform at hlink
    rw [chartedField_of_isAxialTreeBond w V (_, i) hb, cellCentre_add_siteOfCoords_add_unitStep, mul_one] at hlink
    exact (mul_inv_eq_one.1 hlink.symm)) (cellOffset x) hmem
  rw [hx] at hwalk
  rw [hwalk, siteOfCoords_zero, add_zero, hg]
private theorem eq_of_chartedField_eq {S : Finset F.Cell} {w w' : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : F.GaugeField F.top}
    (hw : ∀ b, b ∉ chordBonds S → w b.1 b.2 = 0) (hw' : ∀ b, b ∉ chordBonds S → w' b.1 b.2 = 0)
    (hn : ∀ b ∈ chordBonds S, ‖w b.1 b.2‖ ≤ 1) (hn' : ∀ b ∈ chordBonds S, ‖w' b.1 b.2‖ ≤ 1)
    (hweq : chartedField w' V = chartedField w V) : w' = w := by
  funext x i
  by_cases hb : (x, i) ∈ chordBonds S
  · have hlink := congrFun (congrFun hweq x) i
    have hnt : ¬ IsAxialTreeBond (x, i) := by
      simp only [chordBonds, Finset.mem_filter] at hb
      exact hb.2
    unfold chartedField at hlink
    by_cases hc : IsCrossingBond (x, i)
    · simp only [hc, if_true] at hlink
      exact BlockOffsets.expUnit_inj_of_norm_le_one (mul_right_cancel hlink) (hn' _ hb) (hn _ hb)
    · simp only [hc, hnt, if_false] at hlink
      exact BlockOffsets.expUnit_inj_of_norm_le_one hlink (hn' _ hb) (hn _ hb)
  · rw [show w' x i = 0 from hw' (x, i) hb, show w x i = 0 from hw (x, i) hb]
private theorem gaugeTransform_of_eq_one {k : ℕ} {g : F.Site k → UnitQuaternion} (h : ∀ x, g x = 1)
    (W : F.GaugeField k) : BlockAverages.gaugeTransform g W = W := by
  funext x i
  simp [BlockAverages.gaugeTransform, h]
private theorem stepCoordinates_zero (S : Finset F.Cell) : stepCoordinates (0 : StepVariable S) =
    fun (_ : F.Site F.depth) (_ : Fin 4) => (0 : imaginaryQuaternions) := by
  funext x i
  unfold stepCoordinates
  split_ifs with h
  · exact map_zero toImaginaryCLM
  · rfl
abbrev _root_.YangMills.SharedProofs.p23017 := @stepCoordinates_zero
private theorem fieldAboveFrame_zero (a ρ : ℝ) (V : F.GaugeField F.top) :
    fieldAboveFrame true a ρ 0 V 0 = chartedField (minimizingCoordinates a (finiteCells F) V ρ) V := by apply _root_.YangMills.SharedProofs.p22006 <;> assumption
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
private theorem analyticAt_expUnit {w : X → imaginaryQuaternions} {e : X}
    (h : AnalyticAt ℝ (fun y => (w y : ℍ[ℝ])) e) :
    AnalyticAt ℝ (fun y => ((expUnit (w y) : UnitQuaternion) : ℍ[ℝ])) e :=
  AnalyticAt.comp (g := NormedSpace.exp) (f := fun y => (w y : ℍ[ℝ])) (NormedSpace.exp_analytic (𝕂 := ℝ) _) h
private theorem analyticAt_stepCoordinates {S : Finset F.Cell} {η : X → StepVariable S} {e : X}
    (h : AnalyticAt ℝ η e) (x : F.Site F.depth) (i : Fin 4) :
    AnalyticAt ℝ (fun y => stepCoordinates (η y) x i) e := by
  unfold stepCoordinates
  by_cases hb : (x, i) ∈ chordBonds S
  · simp only [hb, dif_pos]
    have hproj : AnalyticAt ℝ (fun y => η y ⟨(x, i), hb⟩) e :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ↥(chordBonds S) => EuclideanSpace ℝ (Fin 3))
        ⟨(x, i), hb⟩).analyticAt _).comp h
    exact (toImaginaryCLM.analyticAt _).comp hproj
  · simp only [hb, dif_neg, not_false_eq_true]
    exact analyticAt_const
abbrev _root_.YangMills.SharedProofs.p31047 := @analyticAt_stepCoordinates
private theorem analyticAt_coe {w : X → imaginaryQuaternions} {e : X} (h : AnalyticAt ℝ w e) :
    AnalyticAt ℝ (fun y => (w y : ℍ[ℝ])) e :=
  (imaginaryQuaternions.subtypeL.analyticAt _).comp h
private theorem isAnalyticFieldFamily_chartedField {w : X → F.Site F.depth → Fin 4 → imaginaryQuaternions}
    {V : X → F.GaugeField F.top} {e : X}
    (hw : ∀ x i, AnalyticAt ℝ (fun y => (w y x i : ℍ[ℝ])) e) (hV : IsAnalyticFieldFamily V e) :
    IsAnalyticFieldFamily (fun y => chartedField (w y) (V y)) e := by apply _root_.YangMills.SharedProofs.p38066 <;> assumption
private theorem rotatedField_bondSpread_zero {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (A : Fin k → imaginaryQuaternions) (W : F.GaugeField F.top) :
    rotatedField (bondSpread c A 0) W = W := by apply _root_.YangMills.Construction.BlockAverages.AgreeingPairs.rotatedField_zero <;> assumption
private theorem isAnalyticFieldFamily_rotatedField {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (A : Fin k → imaginaryQuaternions) (W : F.GaugeField F.top) :
    IsAnalyticFieldFamily (fun s : Fin k → ℝ => rotatedField (bondSpread c A s) W) 0 := by
  intro y i
  have hsp : AnalyticAt ℝ (fun s : Fin k → ℝ => bondSpread c A s y i) 0 := by
    unfold bondSpread
    refine Finset.analyticAt_fun_sum _ fun l _ => ?_
    by_cases h : c l = (y, i)
    · simp only [h, if_true]
      have hp : AnalyticAt ℝ (fun s : Fin k → ℝ => s l) 0 :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) l).analyticAt _
      exact hp.smul analyticAt_const
    · simp only [h, if_false]
      exact analyticAt_const
  have hconst : AnalyticAt ℝ (fun _ : Fin k → ℝ => ((W y i : UnitQuaternion) : ℍ[ℝ])) 0 := analyticAt_const
  exact (analyticAt_expUnit (analyticAt_coe hsp)).mul hconst
abbrev _root_.YangMills.SharedProofs.p60243 := @isAnalyticFieldFamily_rotatedField
end Charts
section Requirements
variable {F : BlockFrame}
private theorem stepCoordinates_add {S : Finset F.Cell} (ξ ζ : StepVariable S) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (ξ + ζ) x i = stepCoordinates ξ x i + stepCoordinates ζ x i := by
  unfold stepCoordinates
  split_ifs with h
  · exact map_add toImaginaryCLM _ _
  · simp
private theorem chartedField_zero_trivial :
    chartedField (fun _ _ => 0) (trivialBlockField F F.top) = trivialBlockField F F.depth := by apply _root_.YangMills.SharedProofs.p20491 <;> assumption
private theorem minimizingCoordinates_eq_of_minimizer (hs : ∀ i, 2 ≤ F.extent i) (hL : Odd F.blockSide)
    {a ρ : ℝ} (hρ : ρ ≤ 1) {η : StepVariable (finiteCells F)} {V : F.GaugeField F.top} (hη : ‖η‖ ≤ ρ)
    (hmin : ∀ W', blockEnergy a (finiteCells F) F.depth (chartedField (stepCoordinates η) V) V ≤
      blockEnergy a (finiteCells F) F.depth W' V)
    (horb : ∀ W', (∀ W'', blockEnergy a (finiteCells F) F.depth W' V ≤ blockEnergy a (finiteCells F) F.depth W'' V) →
      ∃ g : F.Site F.depth → UnitQuaternion, (∀ z, g (cellCentre F.depth z) = 1) ∧
        W' = BlockAverages.gaugeTransform g (chartedField (stepCoordinates η) V)) :
    IsMinimizingChart a (finiteCells F) V ρ (stepCoordinates η) ∧
      minimizingCoordinates a (finiteCells F) V ρ = stepCoordinates η := by
  have hoff : ∀ b, b ∉ chordBonds (finiteCells F) → stepCoordinates η b.1 b.2 = 0 := fun b hb => by
    unfold stepCoordinates
    exact dif_neg hb
  have hsize : ∀ b ∈ chordBonds (finiteCells F), ‖stepCoordinates η b.1 b.2‖ ≤ ρ := fun b hb => by
    unfold stepCoordinates
    rw [dif_pos hb, norm_toImaginary]
    exact (norm_le_pi_norm η ⟨b, hb⟩).trans hη
  have hchart : IsMinimizingChart a (finiteCells F) V ρ (stepCoordinates η) := ⟨hoff, hsize, hmin⟩
  refine ⟨hchart, ?_⟩
  have hex : ∃ w, IsMinimizingChart a (finiteCells F) V ρ w := ⟨_, hchart⟩
  unfold minimizingCoordinates
  rw [dif_pos hex]
  have hspec := hex.choose_spec
  obtain ⟨g, hg, hgw⟩ := horb _ hspec.2.2
  have hone := gauge_eq_one_of_cellCentre hs hL hg hgw
  rw [gaugeTransform_of_eq_one hone] at hgw
  exact eq_of_chartedField_eq hoff hspec.1 (fun b hb => (hsize b hb).trans hρ)
    (fun b hb => (hspec.2.1 b hb).trans hρ) hgw
abbrev _root_.YangMills.SharedProofs.p92136 := @minimizingCoordinates_eq_of_minimizer
private theorem chartedHessian_posDef {a ρ : ℝ} {W : F.GaugeField F.top} {η₀ : StepVariable (finiteCells F)}
    (hc : minimizingCoordinates a (finiteCells F) W ρ = stepCoordinates η₀)
    (hΦ : AnalyticAt ℝ (fun η : StepVariable (finiteCells F) => chartedEnergy a (stepCoordinates η) W) η₀)
    (hpd : ∀ v : StepVariable (finiteCells F), v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ fun η : StepVariable (finiteCells F) => chartedEnergy a (stepCoordinates η) W) η₀ v v) :
    (chartedHessian a ρ W 0).PosDef := by
  set Φ : StepVariable (finiteCells F) → ℝ := fun η => chartedEnergy a (stepCoordinates η) W with hΦdef
  have hΨ : chartedEnergyAtMinimizer a ρ W = fun η => Φ (η₀ + η) := by
    funext η
    unfold chartedEnergyAtMinimizer
    simp only [hΦdef]
    congr 1
    funext x i
    rw [stepCoordinates_add, ← hc]
    rfl
  have hD : ∀ ζ, fderiv ℝ (chartedEnergyAtMinimizer a ρ W) ζ = fderiv ℝ Φ (η₀ + ζ) := by
    intro ζ
    rw [hΨ]
    exact fderiv_comp_add_left η₀
  set H := fderiv ℝ (fderiv ℝ Φ) η₀ with hH
  have hd : HasFDerivAt (fderiv ℝ Φ) H η₀ := hΦ.fderiv.differentiableAt.hasFDerivAt
  have hentry : ∀ u v, ColdStepAtMirrorFrames.secondDerivAlong (chartedEnergyAtMinimizer a ρ W) 0 u v = H v u := by
    intro u v
    unfold ColdStepAtMirrorFrames.secondDerivAlong
    simp only [hD]
    have happ : HasFDerivAt (fun y => fderiv ℝ Φ y u) ((ContinuousLinearMap.apply ℝ ℝ u).comp H) (η₀ + 0) := by
      rw [add_zero]
      exact (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp η₀ hd
    have hshift : HasFDerivAt (fun ζ : StepVariable (finiteCells F) => η₀ + ζ)
        (ContinuousLinearMap.id ℝ (StepVariable (finiteCells F))) 0 := (hasFDerivAt_id 0).const_add η₀
    have hcomp := happ.comp 0 hshift
    have hf : fderiv ℝ (fun ζ => fderiv ℝ Φ (η₀ + ζ) u) 0 =
        ((ContinuousLinearMap.apply ℝ ℝ u).comp H).comp (ContinuousLinearMap.id ℝ _) := hcomp.fderiv
    rw [hf]
    simp
  have hsymm : ∀ u v, H u v = H v u := fun u v =>
    (hΦ.contDiffAt (n := 2)).isSymmSndFDerivAt (by simp) u v
  set e : ChartCoord F → StepVariable (finiteCells F) :=
    fun i => bondVariation i.1 (EuclideanSpace.single i.2 1) with he
  have hM : ∀ i j, chartedHessian a ρ W 0 i j = H (e j) (e i) := fun i j => hentry _ _
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, hM, star_trivial]
    exact hsymm _ _
  · intro c hcne
    set v : StepVariable (finiteCells F) := ∑ j, c j • e j with hv
    have hcoord : ∀ i : ChartCoord F, (v i.1) i.2 = c i := by
      intro i
      have hexp : (v i.1) i.2 = ∑ j, c j * (e j i.1) i.2 := by
        simp [hv, Finset.sum_apply]
      rw [hexp, Finset.sum_eq_single i]
      · simp [he, bondVariation]
      · intro j _ hj
        by_cases hfst : j.1 = i.1
        · have hsnd : j.2 ≠ i.2 := fun h => hj (Prod.ext hfst h)
          simp [he, bondVariation, hfst, hsnd.symm]
        · have hzero : (e j) i.1 = 0 := by
            simp only [he, bondVariation]
            exact Pi.single_eq_of_ne (fun h => hfst h.symm) _
          simp [hzero]
      · simp
    have hvne : v ≠ 0 := by
      intro hvz
      apply hcne
      funext i
      rw [← hcoord i, hvz]
      simp
    have hpos := hpd v hvne
    have hquad : star c ⬝ᵥ (chartedHessian a ρ W 0).mulVec c = H v v := by
      simp only [hv, map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        dotProduct, Matrix.mulVec, hM, star_trivial, Pi.star_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsymm (e i) (e j)]
      ring
    rw [hquad]
    exact hpos
private theorem analyticAt_component {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ}
    [Fintype (F.Site k)] {q : X → F.Site k → Fin 4 → ℍ[ℝ]} {e : X} (h : AnalyticAt ℝ q e)
    (x : F.Site k) (i : Fin 4) : AnalyticAt ℝ (fun y => q y x i) e :=
  analyticAt_pi_iff.1 (analyticAt_pi_iff.1 h x) i
private theorem minimizer_properties_near_trivial [Fintype (F.Site F.top)] {a ρ : ℝ} (hs : ∀ i, 2 ≤ F.extent i)
    (hL : Odd F.blockSide) (hρpos : 0 < ρ) (hρle : ρ ≤ 1)
    (hTop : IsNondegenerateAtTrivial (F := F) (k := F.top) (minimalAction a (finiteCells F) F.top))
    (hC : MinimizerNearTrivialInChart a F) :
    (∀ᶠ W in 𝓝 (trivialBlockField F F.top),
      (∃ w, IsMinimizingChart a (finiteCells F) W ρ w) ∧
      (∀ W' : F.GaugeField F.depth,
        (∀ W'', blockEnergy a (finiteCells F) F.depth W' W ≤ blockEnergy a (finiteCells F) F.depth W'' W) →
        ∃ g : F.Site F.depth → UnitQuaternion, (∀ z : F.Cell, g (cellCentre _ z) = 1) ∧
          W' = BlockAverages.gaugeTransform g (fieldAboveFrame (F := F) true a ρ 0 W 0)) ∧
      (chartedHessian (F := F) a ρ W 0).PosDef ∧
      IsBondAnalyticAt (minimalAction a (finiteCells F) F.top) W ∧
      ∀ b ∈ chordBonds (finiteCells F), IsBondAnalyticAt (minimizingBondCoordinate a ρ (finiteCells F) b) W) ∧
    Tendsto (fun W => fieldAboveFrame (F := F) true a ρ 0 W 0) (𝓝 (trivialBlockField F F.top))
      (𝓝 (trivialBlockField F F.depth)) := by
  obtain ⟨x, hxa, hx0, hev⟩ := hC
  set q₁ := quaternionsOfField (trivialBlockField F F.top) with hq₁
  have hsmall : ∀ᶠ Y in 𝓝 q₁, ‖x Y‖ < ρ := by
    have ht : Tendsto (fun Y => ‖x Y‖) (𝓝 q₁) (𝓝 0) := by
      have := hxa.continuousAt.tendsto.norm
      simpa [hx0] using this
    exact ht.eventually (gt_mem_nhds hρpos)
  have hG := hev.and hsmall
  have hQ : Tendsto (quaternionsOfField (F := F) (k := F.top)) (𝓝 (trivialBlockField F F.top)) (𝓝 q₁) := by
    have hcont : Continuous (quaternionsOfField (F := F) (k := F.top)) :=
      continuous_pi fun y => continuous_pi fun i =>
        continuous_subtype_val.comp ((continuous_apply i).comp (continuous_apply y))
    exact hcont.tendsto _
  have hLC : ∀ Y, ((∀ W', blockEnergy a (finiteCells F) F.depth
        (chartedField (stepCoordinates (x Y)) (fieldOfQuaternions Y)) (fieldOfQuaternions Y) ≤
        blockEnergy a (finiteCells F) F.depth W' (fieldOfQuaternions Y)) ∧
      (∀ W', (∀ W'', blockEnergy a (finiteCells F) F.depth W' (fieldOfQuaternions Y) ≤
          blockEnergy a (finiteCells F) F.depth W'' (fieldOfQuaternions Y)) →
        ∃ g : F.Site F.depth → UnitQuaternion, (∀ z, g (cellCentre F.depth z) = 1) ∧
          W' = BlockAverages.gaugeTransform g (chartedField (stepCoordinates (x Y)) (fieldOfQuaternions Y))) ∧
      AnalyticAt ℝ (fun η : StepVariable (finiteCells F) =>
        chartedEnergy a (stepCoordinates η) (fieldOfQuaternions Y)) (x Y) ∧
      ∀ v : StepVariable (finiteCells F), v ≠ 0 →
        0 < fderiv ℝ (fderiv ℝ fun η : StepVariable (finiteCells F) =>
          chartedEnergy a (stepCoordinates η) (fieldOfQuaternions Y)) (x Y) v v) ∧ ‖x Y‖ < ρ →
      minimizingCoordinates a (finiteCells F) (fieldOfQuaternions Y) ρ = stepCoordinates (x Y) ∧
        IsMinimizingChart a (finiteCells F) (fieldOfQuaternions Y) ρ (stepCoordinates (x Y)) := by
    intro Y hY
    have := minimizingCoordinates_eq_of_minimizer hs hL hρle hY.2.le hY.1.1 hY.1.2.1
    exact ⟨this.2, this.1⟩
  constructor
  · filter_upwards [hQ.eventually (hG.eventually_nhds.and
      (hTop.analyticAt_trivial.eventually_analyticAt.and hxa.eventually_analyticAt))] with W hW
    obtain ⟨hnear, hAn, hxAn⟩ := hW
    have hg := hnear.self_of_nhds
    have hl := hLC _ hg
    simp only [fieldOfQuaternions_quaternionsOfField] at hg hl
    refine ⟨⟨_, hl.2⟩, fun W' hW' => ?_, chartedHessian_posDef hl.1 hg.1.2.2.1 hg.1.2.2.2, ?_, ?_⟩
    · obtain ⟨g, hgc, hgw⟩ := hg.1.2.1 W' hW'
      refine ⟨g, hgc, ?_⟩
      rw [fieldAboveFrame_zero, hl.1]
      exact hgw
    · intro k c A
      have hq : AnalyticAt ℝ (fun s : Fin k → ℝ => quaternionsOfField (rotatedField (bondSpread c A s) W)) 0 :=
        AnalyticAt.pi fun y => AnalyticAt.pi fun i => isAnalyticFieldFamily_rotatedField c A W y i
      have hcomp := AnalyticAt.comp (g := fun Y => minimalAction a (finiteCells F) F.top (fieldOfQuaternions Y))
        (f := fun s : Fin k → ℝ => quaternionsOfField (rotatedField (bondSpread c A s) W))
        (by rw [rotatedField_bondSpread_zero]; exact hAn) hq
      simpa only [Function.comp_def, fieldOfQuaternions_quaternionsOfField] using hcomp
    · intro b hb k c A
      have hq : AnalyticAt ℝ (fun s : Fin k → ℝ => quaternionsOfField (rotatedField (bondSpread c A s) W)) 0 :=
        AnalyticAt.pi fun y => AnalyticAt.pi fun i => isAnalyticFieldFamily_rotatedField c A W y i
      have hxq : AnalyticAt ℝ (fun s : Fin k → ℝ => x (quaternionsOfField (rotatedField (bondSpread c A s) W))) 0 :=
        AnalyticAt.comp (g := x) (f := fun s : Fin k → ℝ => quaternionsOfField (rotatedField (bondSpread c A s) W))
          (by rw [rotatedField_bondSpread_zero]; exact hxAn) hq
      have hco := analyticAt_stepCoordinates hxq b.1 b.2
      have ht : Tendsto (fun s : Fin k → ℝ => quaternionsOfField (rotatedField (bondSpread c A s) W)) (𝓝 0)
          (𝓝 (quaternionsOfField W)) := by
        have := hq.continuousAt.tendsto
        rwa [rotatedField_bondSpread_zero] at this
      refine hco.congr ?_
      filter_upwards [ht.eventually hnear] with s hs'
      have hmc := (hLC _ hs').1
      rw [fieldOfQuaternions_quaternionsOfField] at hmc
      unfold minimizingBondCoordinate
      rw [hmc]
  · have hΦ : IsAnalyticFieldFamily (fun Y => chartedField (stepCoordinates (x Y)) (fieldOfQuaternions Y)) q₁ :=
      isAnalyticFieldFamily_chartedField (fun y i => analyticAt_coe (analyticAt_stepCoordinates hxa y i))
        (fun y i => analyticAt_normalize (analyticAt_component analyticAt_id y i) (by
          simp [hq₁, quaternionsOfField, trivialBlockField]))
    have hone : chartedField (stepCoordinates (x q₁)) (fieldOfQuaternions q₁) = trivialBlockField F F.depth := by
      rw [hx0, stepCoordinates_zero, hq₁, fieldOfQuaternions_quaternionsOfField]
      exact chartedField_zero_trivial
    have heq : (fun W => fieldAboveFrame (F := F) true a ρ 0 W 0) =ᶠ[𝓝 (trivialBlockField F F.top)]
        fun W => chartedField (stepCoordinates (x (quaternionsOfField W)))
          (fieldOfQuaternions (quaternionsOfField W)) := by
      filter_upwards [hQ.eventually hG] with W hW
      have hl := hLC _ hW
      rw [fieldOfQuaternions_quaternionsOfField] at hl ⊢
      rw [fieldAboveFrame_zero, hl.1]
    refine Tendsto.congr' heq.symm ?_
    refine tendsto_pi_nhds.2 fun y => tendsto_pi_nhds.2 fun i => ?_
    refine tendsto_subtype_rng.2 ?_
    have hlim := ((hΦ y i).continuousAt.tendsto).comp hQ
    have hval : ((chartedField (stepCoordinates (x q₁)) (fieldOfQuaternions q₁) y i : UnitQuaternion) : ℍ[ℝ]) =
        ((trivialBlockField F F.depth y i : UnitQuaternion) : ℍ[ℝ]) := by
      rw [hone]
    rw [← hval]
    exact hlim
end Requirements
theorem minimizerNearTrivialField_holds (hW : WilsonActionNondegenerate) (hX : NondegenerateAcrossFrames)
    (hT : minimalActionNondegeneratePropagatesStatement) : MinimizerNearTrivialField := by
  intro a ha L hLs t n ρ hn hρpos hρle
  have hL : Odd L := hLs.1
  have hLpos : 0 < L := hL.pos
  have hn2 : 2 ≤ n := by
    have := hLs.2
    omega
  have hext : ∀ i : Fin 4, 0 < (torusFrame L t n).extent i := fun _ => by
    show 0 < n
    omega
  letI instDepth := fintypeSiteOfPos (torusFrame L t n) hLpos hext (torusFrame L t n).depth
  letI instTop := fintypeSiteOfPos (torusFrame L t n) hLpos hext (torusFrame L t n).top
  obtain ⟨hTop, hC⟩ := hT (torusFrame L t n) a ha hL (fun _ => hn2)
    (nondegenerate_at_depth hW hX hT ha hL t n hn2 instDepth)
  obtain ⟨hcl, htend⟩ := minimizer_properties_near_trivial (F := torusFrame L t n) (fun _ => hn2) hL hρpos hρle hTop hC
  have hread : Tendsto (fun V : TorusField n => readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
      (𝓝 (trivialField n)) (𝓝 (trivialBlockField (torusFrame L t n) (torusFrame L t n).top)) := by
    have hcont : Continuous (fun V : TorusField n => readAtLevel (torusFrame L t n) (torusFrame L t n).top V) :=
      continuous_pi fun y => continuous_pi fun i => (continuous_apply i).comp (continuous_apply _)
    exact hcont.tendsto _
  refine ⟨?_, hread.eventually hcl⟩
  have hlim := htend.comp hread
  refine tendsto_pi_nhds.2 fun z => tendsto_pi_nhds.2 fun i => ?_
  exact (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim
    (siteOfCoords (torusFrame L t n).depth fun k => ((z k).cast : ℤ)))) i
end YangMills.Construction.RunningCouplingSlope
end
