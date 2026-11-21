import YangMills.Construction.ClusterExpansionOfAStep.BallsAndBlocksOfATorusForm
import YangMills.Construction.ClusterExpansionOfAStep.ChartsOverTheTopOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.AdjointOfTheGroup
import YangMills.Construction.ColdStepAtMirrorFrames.ChartUnderGaugesAndShifts
import YangMills.Construction.ColdStepAtMirrorFrames.SmallUnitsAndTheirLogarithms
import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorusProof
import YangMills.Construction.ResponseInTheExpansion.FrameNearOneIsTheFlatSum
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheLogarithms
import YangMills.Construction.SixteenPointsOnASmallTorus.CouplingAtTheLevelOfARadiusProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages hiding adjointAction
open LumpContours ColdStepAtMirrorFrames ColdStepAtMirrorFrames.BlockOffsets
  ColdStepAtMirrorFrames.SmallUnits TorusFields TorusLumps RenormalizationStepParameters StepSettings StepCosts StepReturn
  WeightedResponses
namespace LogarithmOneStep
private theorem eventually_log_bounds (K : ℝ) : ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x, x₀ ≤ x → 17 ≤ Real.log x ∧
    Real.log x ^ 3 ≤ x ^ (1 / 200 : ℝ) ∧ K ≤ x ^ (1 / 200 : ℝ) := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, 17 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 17
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ 1 * ‖x ^ (1 / 600 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 600)).bound one_pos
  have h3 : ∀ᶠ x : ℝ in Filter.atTop, K ≤ x ^ (1 / 200 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).eventually_ge_atTop K
  have h4 : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_ge_atTop 1
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 (h1.and (h2.and (h3.and h4)))
  refine ⟨max x₁ 1, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := hx₁ x ((le_max_left _ _).trans hx)
  refine ⟨e1, ?_, e3⟩
  have hx0 : (0 : ℝ) ≤ x := by linarith
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log x),
    abs_of_nonneg (Real.rpow_nonneg hx0 _)] at e2
  have e5 : (x ^ (1 / 600 : ℝ)) ^ 3 = x ^ (1 / 200 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  rw [← e5]
  exact pow_le_pow_left₀ (by linarith) e2 3
private theorem expansion_succ_of_returns {ℓ : TorusLumps.StepParameters} (hR : ExpansionReturnsAt ℓ) {t : ℕ}
    {x : ℝ} {D : TorusFunctional} (hx : ℓ.y₁ ≤ x) (hD : HasExpansion ℓ t x D) :
    HasExpansion ℓ (t + 1) (expansionCoupling ℓ t x D) (kernelImage ℓ x D) ∧
      |expansionCoupling ℓ t x D - x| ≤ 2 * ℓ.B := by apply _root_.YangMills.SharedProofs.p2841 <;> assumption
private theorem abs_couplingFlow_sub_le {ℓ : TorusLumps.StepParameters} (hR : ExpansionReturnsAt ℓ)
    (hW : ∀ β : ℝ, ℓ.y₁ ≤ β → HasExpansion ℓ 0 β (wilsonWeight β)) {β : ℝ} {N : ℕ}
    (hflow : ∀ j ≤ N, ℓ.y₁ ≤ (couplingFlow ℓ β j).1) {u v : ℕ} (huv : u ≤ v) (hv : v ≤ N) :
    |(couplingFlow ℓ β v).1 - (couplingFlow ℓ β u).1| ≤ 2 * ℓ.B * ((v : ℝ) - (u : ℝ)) := by
  have hexp : ∀ t ≤ N, HasExpansion ℓ t (couplingFlow ℓ β t).1 (couplingFlow ℓ β t).2 := by
    intro t
    induction t with
    | zero => exact fun _ => hW β (hflow 0 (Nat.zero_le _))
    | succ t ih =>
      intro ht
      exact (expansion_succ_of_returns hR (hflow t (by omega)) (ih (by omega))).1
  have hstep : ∀ t < N, |(couplingFlow ℓ β (t + 1)).1 - (couplingFlow ℓ β t).1| ≤ 2 * ℓ.B := fun t ht =>
    (expansion_succ_of_returns hR (hflow t ht.le) (hexp t ht.le)).2
  induction v, huv using Nat.le_induction with
  | base => simp
  | succ v huv ih =>
    have h1 := ih (by omega)
    have h2 := hstep v (by omega)
    have h3 := abs_sub_le (couplingFlow ℓ β (v + 1)).1 (couplingFlow ℓ β v).1 (couplingFlow ℓ β u).1
    push_cast
    linarith
private theorem norm_log_mul_sub_le {l x y : imaginaryQuaternions} (h : expUnit l = expUnit x * expUnit y)
    (hl : ‖l‖ ≤ 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖((l - x - y : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ‖l‖ ^ 2 + ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖x‖ * ‖y‖ := by
  have e1 := norm_expUnit_sub_one_sub_le l hl
  have e2 := norm_expUnit_sub_one_sub_le x hx
  have e3 := norm_expUnit_sub_one_sub_le y hy
  have e4 : ((expUnit l : UnitQuaternion) : ℍ[ℝ]) =
      ((expUnit x : UnitQuaternion) : ℍ[ℝ]) * ((expUnit y : UnitQuaternion) : ℍ[ℝ]) := by
    rw [h]
    rfl
  set p : ℍ[ℝ] := ((expUnit x : UnitQuaternion) : ℍ[ℝ]) with hp
  set q : ℍ[ℝ] := ((expUnit y : UnitQuaternion) : ℍ[ℝ]) with hq
  set r : ℍ[ℝ] := ((expUnit l : UnitQuaternion) : ℍ[ℝ]) with hr
  have e5 : ((l - x - y : imaginaryQuaternions) : ℍ[ℝ]) =
      -(r - 1 - (l : ℍ[ℝ])) + (p - 1 - (x : ℍ[ℝ])) + (q - 1 - (y : ℍ[ℝ])) + (p - 1) * (q - 1) := by
    rw [Submodule.coe_sub, Submodule.coe_sub, e4]
    noncomm_ring
  have e6 : ‖(p - 1) * (q - 1)‖ ≤ ‖x‖ * ‖y‖ := by
    rw [norm_mul]
    exact mul_le_mul (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le x) (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le y) (norm_nonneg _) (norm_nonneg _)
  rw [e5]
  calc _ ≤ ‖-(r - 1 - (l : ℍ[ℝ]))‖ + ‖p - 1 - (x : ℍ[ℝ])‖ + ‖q - 1 - (y : ℍ[ℝ])‖ + ‖(p - 1) * (q - 1)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := by
        rw [norm_neg]
        linarith
private theorem norm_minimalLog_le (u : UnitQuaternion) (w : imaginaryQuaternions) (h : expUnit w = u) :
    ‖minimalLog u‖ ≤ ‖w‖ := by
  classical
  unfold minimalLog
  rw [dif_pos (TopLevelSites.exists_minimal_log u)]
  exact (TopLevelSites.exists_minimal_log u).choose_spec.2 w h
private theorem norm_minimalLog_le_two_mul (u : UnitQuaternion) (hu : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne u < 1) :
    ‖minimalLog u‖ ≤ 2 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne u := by
  have hsq := distFromOne_sq u
  have hg0 : 0 ≤ _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne u := _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_nonneg u
  have hre : 0 < (u : ℍ[ℝ]).re := by nlinarith
  exact (norm_minimalLog_le u _ (expUnit_logUnit u hre)).trans (norm_logUnit_le u)
abbrev _root_.YangMills.SharedProofs.p16086 := @norm_minimalLog_le_two_mul
section
variable {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
private theorem norm_adjointAction (g : UnitQuaternion) (p : imaginaryQuaternions) :
    ‖adjointAction g p‖ = ‖p‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.norm_adjointAction <;> assumption
private theorem parentBlock_add_unitStep {F : BlockFrame} (hn : ∀ i, F.extent i = n) (hL : Odd F.blockSide)
    (h2 : 2 ≤ n) [NeZero (n * F.blockSide)] (x : TorusSite (n * F.blockSide)) (i : Fin 4) :
    (IsCrossingBond (torusSiteInFrame F F.depth x, i) →
        parentBlock F.blockSide (x + TorusFields.unitStep (n * F.blockSide) i) =
          parentBlock F.blockSide x + TorusFields.unitStep n i) ∧
      (¬ IsCrossingBond (torusSiteInFrame F F.depth x, i) →
        parentBlock F.blockSide (x + TorusFields.unitStep (n * F.blockSide) i) = parentBlock F.blockSide x) := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; exact h2
  have hnext : torusSiteInFrame F F.depth (x + TorusFields.unitStep (n * F.blockSide) i) =
      torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i := by
    apply TopLevelSites.toTorusSite_injective (TopLevelSites.period_depth_of_extent hn)
    rw [TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_depth_of_extent hn),
      TopLevelSites.toTorusSite_add (TopLevelSites.period_depth_of_extent hn),
      TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_depth_of_extent hn),
      TopLevelSites.toTorusSite_unitStep (TopLevelSites.period_depth_of_extent hn)]
  have c1 := TopLevelSites.enclosingCell_torusSiteInFrame hn (x + TorusFields.unitStep (n * F.blockSide) i)
  have c0 := TopLevelSites.enclosingCell_torusSiteInFrame hn x
  refine ⟨fun hcr => ?_, fun hcr => ?_⟩
  · have := TopLevelSites.enclosingCell_add_unitStep hL hs _ i hcr
    rw [← hnext, c1, c0] at this
    have e := congrArg (toTorusSite n) this
    rw [TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn),
      TopLevelSites.toTorusSite_add (TopLevelSites.period_top_of_extent hn),
      TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn),
      TopLevelSites.toTorusSite_unitStep (TopLevelSites.period_top_of_extent hn)] at e
    exact e
  · have : enclosingCell (torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i) =
        enclosingCell (torusSiteInFrame F F.depth x) := by
      by_contra hne
      exact hcr hne
    rw [← hnext, c1, c0] at this
    have e := congrArg (toTorusSite n) this
    rw [TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn),
      TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn)] at e
    exact e
open Classical in
private theorem norm_minimalLog_gauge_sub_le (hL : Odd ℓ.side) (h2 : 2 ≤ n) (V : TorusField n)
    (W : TorusField (n * ℓ.side)) (g : TorusSite n → UnitQuaternion) (b : TorusBond (n * ℓ.side))
    (A₀ : imaginaryQuaternions) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 16)
    (hA : ResponseInTheExpansion.gaugeTransform g V (parentBlock ℓ.side b.1, b.2) = expUnit A₀) (hAs : ‖A₀‖ ≤ s)
    (hl : ‖(minimalLog (ResponseInTheExpansion.gaugeTransform
      (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ W x) W b) : ℍ[ℝ])‖ ≤ s) :
    ‖((minimalLog (ResponseInTheExpansion.gaugeTransform (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ W x) W b) -
        adjointAction (g (parentBlock ℓ.side b.1)) (chartCoord ℓ V W b) -
        (if IsCrossingBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1, b.2)
          then A₀ else 0) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ 22 * s ^ 2 := by
  obtain ⟨x, i⟩ := b
  simp only at hA hl ⊢
  have hns : ∀ i, (stepBlockFrame ℓ.side n).extent i = n := fun _ => rfl
  have hNZ : NeZero (n * (stepBlockFrame ℓ.side n).blockSide) := (inferInstance : NeZero (n * ℓ.side))
  obtain ⟨hb1, hb2⟩ := parentBlock_add_unitStep (F := stepBlockFrame ℓ.side n) hns hL h2 x i
  set Y := parentBlock ℓ.side x with hY
  set u₀ : UnitQuaternion := BlockTrees.blockGauge ℓ.side W x * W x i *
    (BlockTrees.blockGauge ℓ.side W (x + TorusFields.unitStep (n * ℓ.side) i))⁻¹ with hu₀
  set E : UnitQuaternion := ResponseInTheExpansion.gaugeTransform
    (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ W x) W (x, i) with hE
  have hEd : E = g Y * u₀ * (g (parentBlock ℓ.side (x + TorusFields.unitStep (n * ℓ.side) i)))⁻¹ := by
    change g Y * BlockTrees.blockGauge ℓ.side W x * W x i *
        (g (parentBlock ℓ.side (x + TorusFields.unitStep (n * ℓ.side) i)) *
          BlockTrees.blockGauge ℓ.side W (x + TorusFields.unitStep (n * ℓ.side) i))⁻¹ = _
    rw [hu₀]
    group
  have hlE : expUnit (minimalLog E) = E := TopLevelSites.expUnit_minimalLog E
  have hgl : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (expUnit (minimalLog E)) ≤ s := (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le _).trans hl
  have hchart := BlockTrees.chartCoord_eq ℓ V W (x, i)
  simp only at hchart
  by_cases hcr : IsCrossingBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 x, i)
  · rw [if_pos hcr] at hchart ⊢
    rw [← hu₀] at hchart
    set U : UnitQuaternion := u₀ * (V Y i)⁻¹ with hU
    set p := chartCoord ℓ V W (x, i) with hp
    have hpU : expUnit p = U := by
      rw [hchart]
      exact TopLevelSites.expUnit_minimalLog U
    have hEa : E = expUnit (adjointAction (g Y) p) * expUnit A₀ := by
      have hbc : parentBlock ℓ.side (x + TorusFields.unitStep (n * ℓ.side) i) = Y + TorusFields.unitStep n i :=
        hb1 hcr
      rw [hEd, hbc, Adjoint.expUnit_adjointAction, hpU, ← hA]
      change _ = g Y * (u₀ * (V Y i)⁻¹) * (g Y)⁻¹ * (g Y * V Y i * (g (Y + TorusFields.unitStep n i))⁻¹)
      group
    have hgA : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (expUnit A₀) ≤ s := (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_expUnit_le _).trans hAs
    have hga : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (expUnit (adjointAction (g Y) p)) ≤ 2 * s := by
      have e1 : expUnit (adjointAction (g Y) p) = expUnit (minimalLog E) * (expUnit A₀)⁻¹ := by
        rw [hlE, hEa]
        group
      rw [e1]
      have := _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_mul (expUnit (minimalLog E)) (expUnit A₀)⁻¹
      rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_inv] at this
      linarith
    have hgU : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne U ≤ 2 * s := by
      rw [Adjoint.expUnit_adjointAction, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_conj, hpU] at hga
      exact hga
    have hpn : ‖p‖ ≤ 4 * s := by
      rw [hchart]
      have := norm_minimalLog_le_two_mul U (by linarith)
      linarith
    have hap : ‖adjointAction (g Y) p‖ ≤ 4 * s := by
      rw [norm_adjointAction]
      exact hpn
    have hl' : ‖minimalLog E‖ ≤ s := hl
    have hprod := norm_log_mul_sub_le (l := minimalLog E) (x := adjointAction (g Y) p) (y := A₀)
      (by rw [hlE, hEa]) (by linarith) (by linarith) (by linarith)
    refine hprod.trans ?_
    have g1 := norm_nonneg (minimalLog E)
    have g2 := norm_nonneg (adjointAction (g Y) p)
    have g3 := norm_nonneg A₀
    nlinarith [mul_le_mul hl' hl' g1 hs0, mul_le_mul hap hap g2 (by positivity : 0 ≤ 4 * s),
      mul_le_mul hAs hAs g3 hs0, mul_le_mul hap hAs g3 (by positivity : 0 ≤ 4 * s)]
  · rw [if_neg hcr] at hchart ⊢
    rw [← hu₀] at hchart
    set p := chartCoord ℓ V W (x, i) with hp
    have hpU : expUnit p = u₀ := by
      rw [hchart]
      exact TopLevelSites.expUnit_minimalLog u₀
    have hEa : E = expUnit (adjointAction (g Y) p) := by
      have hbc : parentBlock ℓ.side (x + TorusFields.unitStep (n * ℓ.side) i) = Y := hb2 hcr
      rw [hEd, hbc, Adjoint.expUnit_adjointAction, hpU]
    have hgU : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne u₀ ≤ s := by
      have := hgl
      rw [hlE, hEa, Adjoint.expUnit_adjointAction, _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_conj, hpU] at this
      exact this
    have hpn : ‖p‖ ≤ 2 * s := by
      rw [hchart]
      have := norm_minimalLog_le_two_mul u₀ (by linarith)
      linarith
    have hpi : ‖((adjointAction (g Y) p : imaginaryQuaternions) : ℍ[ℝ])‖ < Real.pi := by
      have e : ‖((adjointAction (g Y) p : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖p‖ := norm_adjointAction _ _
      rw [e]
      linarith [Real.pi_gt_three]
    have hll : minimalLog E = adjointAction (g Y) p := by
      rw [hEa]
      exact BlockTrees.minimalLog_expUnit hpi
    rw [hll, sub_self, sub_zero]
    simp
    positivity
end
section
variable {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
private theorem sum_add_smul_eq {E ι : Type} [AddCommGroup E] [Module ℝ E] (A : Finset ι) (f g : ι → ℝ)
    (v : ι → E) : ∑ q ∈ A, (f q + g q) • v q = ∑ q ∈ A, f q • v q + ∑ q ∈ A, g q • v q := by
  simp only [add_smul, Finset.sum_add_distrib]
private def frameLieForm (F : BlockFrame) (B : TorusBond n → imaginaryQuaternions) :
    F.Cell → Fin 4 → imaginaryQuaternions := fun z l => B (toTorusSite n z, l)
open Classical in
private theorem responseOfLieForm_eq (a ρ : ℝ) (u : ℕ) (hL : Odd ℓ.side) (h2 : 2 ≤ n)
    (B : TorusBond n → imaginaryQuaternions) (b : TorusBond (n * ℓ.side)) :
    responseOfLieForm a ρ ℓ.side u B b =
      flatLinearPart (F := torusFrame ℓ.side u n) a ρ unitGenerator
          (torusSiteInFrame (torusFrame ℓ.side u n) (torusFrame ℓ.side u n).depth b.1, b.2)
          (frameLieForm (torusFrame ℓ.side u n) B) +
        (if IsCrossingBond (F := torusFrame ℓ.side u n)
            (torusSiteInFrame (torusFrame ℓ.side u n) (torusFrame ℓ.side u n).depth b.1, b.2)
          then B (parentBlock ℓ.side b.1, b.2) else 0) := by
  set F := torusFrame ℓ.side u n with hF
  have hn : ∀ i, F.extent i = n := fun _ => rfl
  have hpos : ∀ i, 0 < F.extent i := fun i => by rw [hn]; omega
  have hpt := TopLevelSites.period_top_of_extent (F := F) hn
  have hNZ : NeZero (n * F.blockSide) := (inferInstance : NeZero (n * ℓ.side))
  set bx : F.Site F.depth × Fin 4 := (torusSiteInFrame F F.depth b.1, b.2) with hbx
  unfold responseOfLieForm
  have e0 : ∀ c : TorusBond n, responseKernel a ρ ℓ.side u b c =
      flatCoefficient a ρ unitGenerator bx (torusSiteInFrame F F.top c.1, c.2) +
        (if IsCrossingBond bx ∧ enclosingCell bx.1 = torusSiteInFrame F F.top c.1 ∧ bx.2 = c.2 then 1 else 0) :=
    fun c => rfl
  simp only [e0]
  have e1 : ∑ c : TorusBond n, (flatCoefficient a ρ unitGenerator bx (torusSiteInFrame F F.top c.1, c.2) +
        (if IsCrossingBond bx ∧ enclosingCell bx.1 = torusSiteInFrame F F.top c.1 ∧ bx.2 = c.2
          then (1 : ℝ) else 0)) • B c =
      ∑ c : TorusBond n, flatCoefficient a ρ unitGenerator bx (torusSiteInFrame F F.top c.1, c.2) • B c +
      ∑ c : TorusBond n, (if IsCrossingBond bx ∧ enclosingCell bx.1 = torusSiteInFrame F F.top c.1 ∧ bx.2 = c.2
          then (1 : ℝ) else 0) • B c :=
    sum_add_smul_eq _ _ _ _
  rw [e1]
  congr 1
  · unfold flatLinearPart frameLieForm
    rw [← TopLevelSites.cellsOfSites_univ hn]
    unfold cellsOfSites
    rw [Finset.sum_image (fun x _ y _ h => by
      have e := congrArg (toTorusSite n)
        (show torusSiteInFrame F F.top x = torusSiteInFrame F F.top y from h)
      rwa [TopLevelSites.toTorusSite_torusSiteInFrame hpt, TopLevelSites.toTorusSite_torusSiteInFrame hpt] at e)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun l _ => ?_
    have e2 : toTorusSite n (siteOfCoords F.top fun i => (((y i).cast : ℤ))) = y :=
      TopLevelSites.toTorusSite_torusSiteInFrame hpt y
    rw [e2]
    rfl
  · have hcell : enclosingCell bx.1 = torusSiteInFrame F F.top (parentBlock ℓ.side b.1) :=
      TopLevelSites.enclosingCell_torusSiteInFrame hn b.1
    by_cases hcr : IsCrossingBond bx
    · rw [if_pos hcr, Finset.sum_eq_single (parentBlock ℓ.side b.1, b.2)]
      · rw [if_pos ⟨hcr, hcell, rfl⟩, one_smul]
      · intro c _ hne
        rw [if_neg, zero_smul]
        rintro ⟨-, h1, h2⟩
        apply hne
        rw [hcell] at h1
        have e := congrArg (toTorusSite n) h1
        rw [TopLevelSites.toTorusSite_torusSiteInFrame hpt, TopLevelSites.toTorusSite_torusSiteInFrame hpt] at e
        exact Prod.ext e.symm h2.symm
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg hcr]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg (fun h => hcr h.1), zero_smul]
abbrev _root_.YangMills.DeltaSharedProofs.p502148 := @responseOfLieForm_eq
end
private def ReflectedCoordinateBound (a : ℝ) (L : ℕ) (c : ColdChainParameters) (C r₀ s₁ : ℝ) : Prop :=
  ∀ (F : BlockFrame) (Y : F.Cell) (R m : ℕ) (o : Fin 4 → ℤ) (i : Fin 4) (V : F.GaugeField F.top)
      (γ : F.Cell → UnitQuaternion) (B : F.Cell → Fin 4 → imaginaryQuaternions) (X : imaginaryQuaternions) (s : ℝ),
      IsBlockTorus L F → (∀ l, 4 * m + 5 < F.extent l) → 16 ≤ R → R ≤ m → o ∈ centredCube L →
      fineBondAt Y 0 o i ∈ chordBonds (finiteCells F) → ‖X‖ = 1 → 0 ≤ s → s ≤ s₁ →
      IsSmallCurvature c.σA (reflectedField m Y V) → IsSmallCurvature c.σA (reflectedField R Y V) →
      (∀ z l, ‖B z l‖ ≤ s) →
      (∀ (h : Fin 4 → ℤ) (l : Fin 4), BondWithinRadius R (h, l) →
        BlockAverages.gaugeTransform γ V (Y + siteOfCoords F.top h) l = expUnit (B (Y + siteOfCoords F.top h) l)) →
      ‖((adjointMap (γ Y) (reflectedBondCoord a c.ρA m (fineBondAt Y 0 o i) V) -
          flatLinearPart a c.ρA X (fineBondAt Y 0 o i) B : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
        C * (s ^ 2 + Real.exp (-(r₀ * (R : ℝ))))
private theorem norm_unitGenerator : ‖unitGenerator‖ = 1 := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.norm_unitGenerator <;> assumption
private theorem isSmallCurvature_reflectedField_readAtLevel {F : BlockFrame} {n : ℕ} [NeZero n]
    (hn : ∀ i, F.extent i = n) {m : ℕ} (hm : 0 < m) {s : ℝ} (hs : 0 < s) (V : TorusField n) (y : TorusSite n)
    (hcold : ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν →
      (∀ d ∈ plaquetteOffsets μ ν, TorusFields.OffsetInBox m (a + d)) → curvature V (y + siteOfInt a) μ ν < s) :
    IsSmallCurvature s (reflectedField m (torusSiteInFrame F F.top y) (readAtLevel F F.top V)) := by
  have hz : NeZero (4 * m) := ⟨by omega⟩
  have hp' : ∀ i, (reflectedFrame F m).period (reflectedFrame F m).top i = 4 * m := fun i =>
    TopLevelSites.period_top i
  rw [TopLevelSites.reflectedField_readAtLevel hn hm]
  rintro ⟨z, μ, ν⟩ hlt
  rw [TopLevelSites.plaquetteDefect_readAtLevel_eq hp']
  exact TorusMirror.isCold_mirrorField hm y V hs hcold _ μ ν hlt
private theorem scale_inequalities {u a b c R m₀ r N nn fl : ℝ} (hu : 8192 ≤ u) (ha : 8192 * u ≤ a)
    (hb : 8192 * a ≤ b) (hc : 8192 * b ≤ c) (hR : R ≤ u) (hnn : nn ≤ b) (hrl : a / 2 ≤ r) (hrh : r ≤ 2 * a + 1)
    (hm1 : m₀ ≤ r / 2048) (hm2 : r < (m₀ + 1) * 2048) (hfl : c < fl + 1) (hN : 1024 * fl ≤ N) :
    R ≤ m₀ ∧ 4 * m₀ + 5 < N ∧ 64 ≤ N ∧ 20 * nn + R + 2 + m₀ ≤ fl := by
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩
private theorem scale_bounds {B x xt nn : ℝ} {R n : ℕ} (hB : 0 < B) (hx1 : 1 ≤ x)
    (hK : 2 ^ 13 + 4 * B ≤ x ^ (1 / 200 : ℝ)) (hxt : |xt - x| ≤ 2 * B * x ^ (1 / 200 : ℝ))
    (hnn : nn ≤ x ^ (1 / 90 : ℝ)) (hR : (R : ℝ) ≤ x ^ (1 / 200 : ℝ))
    (hN : 2 ^ 10 * ((⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℕ) : ℝ) ≤ n) :
    R ≤ clusterRange xt / 2 ^ 11 ∧ 4 * (clusterRange xt / 2 ^ 11) + 5 < n ∧ 64 ≤ n ∧
      20 * nn + R + 2 + ((clusterRange xt / 2 ^ 11 : ℕ) : ℝ) ≤ (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℕ) := by
  have hx0 : 0 ≤ x := by linarith
  set u := x ^ (1 / 200 : ℝ) with hu
  have hu1 : (8192 : ℝ) ≤ u := by linarith
  have huo : (1 : ℝ) ≤ u := by linarith
  have pw : ∀ k : ℕ, x ^ ((k : ℝ) / 200) = u ^ k := fun k => by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    congr 1
    ring
  have e2 : x ^ (1 / 100 : ℝ) = u ^ 2 := by
    have := pw 2
    norm_num at this
    rw [← this]
  have e10 : x ^ ((1 : ℝ) / 20) = u ^ 10 := by
    have := pw 10
    norm_num at this
    rw [← this]
  have e3 : x ^ (1 / 90 : ℝ) ≤ u ^ 3 := by
    have := pw 3
    norm_num at this
    rw [← this]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hx2 : u ^ 2 ≤ x := by
    rw [← e2]
    have := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 100 : ℝ) ≤ 1)
    simpa using this
  have ha : 8192 * u ≤ u ^ 2 := by nlinarith
  have hb : 8192 * u ^ 2 ≤ u ^ 3 := by
    have : u ^ 3 = u * u ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hu1 (by positivity)
  have hc : 8192 * u ^ 3 ≤ u ^ 10 := by
    have h1 : u ^ 10 = u ^ 6 * (u * u ^ 3) := by ring
    have h2 : 1 ≤ u ^ 6 := one_le_pow₀ huo
    have h3 : 8192 * u ^ 3 ≤ u * u ^ 3 := mul_le_mul_of_nonneg_right hu1 (by positivity)
    rw [h1]
    nlinarith [show 0 ≤ u * u ^ 3 by positivity]
  have hmove := abs_le.mp hxt
  have hBu : 2 * B * u ≤ x / 2 := by nlinarith
  have hlow : x / 2 ≤ xt := by linarith [hmove.1]
  have hhigh : xt ≤ 2 * x := by linarith [hmove.2]
  have hx' : 0 ≤ x / 2 := by linarith
  have hr1 : u ^ 2 / 2 ≤ xt ^ (1 / 100 : ℝ) := by
    have h1 : (x / 2) ^ (1 / 100 : ℝ) ≤ xt ^ (1 / 100 : ℝ) := Real.rpow_le_rpow hx' hlow (by norm_num)
    have h4 : (x / 2) ^ (1 / 100 : ℝ) = u ^ 2 * (1 / 2 : ℝ) ^ (1 / 100 : ℝ) := by
      rw [div_eq_mul_one_div x 2, Real.mul_rpow hx0 (by norm_num), e2]
    have h5 : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (1 / 100 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (by norm_num : (1 / 100 : ℝ) ≤ 1)
      simpa using this
    have h6 : 0 ≤ u ^ 2 := by positivity
    rw [h4] at h1
    nlinarith
  have hr2 : xt ^ (1 / 100 : ℝ) ≤ 2 * u ^ 2 := by
    have hxt0 : 0 ≤ xt := by linarith
    have h1 : xt ^ (1 / 100 : ℝ) ≤ (2 * x) ^ (1 / 100 : ℝ) := Real.rpow_le_rpow hxt0 hhigh (by norm_num)
    have h4 : (2 * x) ^ (1 / 100 : ℝ) = (2 : ℝ) ^ (1 / 100 : ℝ) * u ^ 2 := by
      rw [Real.mul_rpow (by norm_num) hx0, e2]
    have h5 : (2 : ℝ) ^ (1 / 100 : ℝ) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 100 : ℝ) ≤ 1)
      simpa using this
    have h6 : 0 ≤ u ^ 2 := by positivity
    rw [h4] at h1
    nlinarith
  set r := clusterRange xt with hr
  have hrl : u ^ 2 / 2 ≤ (r : ℝ) := hr1.trans (Nat.le_ceil _)
  have hrh : (r : ℝ) ≤ 2 * u ^ 2 + 1 := by
    have h1 : (r : ℝ) < xt ^ ((1 : ℝ) / 100) + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith) _)
    linarith
  have hdiv : r / 2 ^ 11 = r / 2048 := by norm_num
  rw [hdiv]
  set m₀ := r / 2048 with hm₀
  have hm1 : (m₀ : ℝ) ≤ (r : ℝ) / 2048 := by
    have h := Nat.cast_div_le (α := ℝ) (m := r) (n := 2048)
    simpa using h
  have hm2 : (r : ℝ) < ((m₀ : ℝ) + 1) * 2048 := by
    have h1 : r < (m₀ + 1) * 2048 := by
      rw [hm₀]
      omega
    exact_mod_cast h1
  have hfl : u ^ 10 < ((⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℕ) : ℝ) + 1 := by
    rw [← e10]
    exact Nat.lt_floor_add_one _
  obtain ⟨f1, f2, f3, f4⟩ := scale_inequalities (R := (R : ℝ)) (N := (n : ℝ)) (nn := nn) hu1 ha hb hc hR
    (hnn.trans e3) hrl hrh hm1 hm2 hfl (by norm_num at hN; linarith)
  exact ⟨by exact_mod_cast f1, by exact_mod_cast f2, by exact_mod_cast f3, f4⟩
section
variable {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
private theorem gaugeTransform_readAtLevel {F : BlockFrame} (hn : ∀ i, F.extent i = n)
    (g : TorusSite n → UnitQuaternion) (V : TorusField n) (z : F.Cell) (l : Fin 4) :
    BlockAverages.gaugeTransform (fun z => g (toTorusSite n z)) (readAtLevel F F.top V) z l =
      ResponseInTheExpansion.gaugeTransform g V (toTorusSite n z, l) := by
  have hpt := TopLevelSites.period_top_of_extent (F := F) hn
  have e : toTorusSite n (z + BlockAverages.unitStep F.top l : F.Cell) =
      toTorusSite n z + TorusFields.unitStep n l := by
    rw [TopLevelSites.toTorusSite_add hpt, TopLevelSites.toTorusSite_unitStep hpt]
  unfold BlockAverages.gaugeTransform ResponseInTheExpansion.gaugeTransform
  simp only
  rw [e]
  rfl
private theorem norm_reflected_sub_flatLinearPart_le {c : ColdChainParameters} {C r₀ s₁ : ℝ}
    (hFrame : ReflectedCoordinateBound ℓ.coupling ℓ.side c C r₀ s₁) (hCU : chartEquivarianceStatement)
    (hL : Odd ℓ.side) (hσ : 0 < c.σA) (t m R : ℕ) (hn64 : 64 ≤ n) (hbig : 4 * m + 5 < n) (hR16 : 16 ≤ R)
    (hRm : R ≤ m) (V : TorusField n) (g : TorusSite n → UnitQuaternion) (B : TorusBond n → imaginaryQuaternions)
    (b : TorusBond (n * ℓ.side)) (hb : b ∈ chartBonds ℓ.side n) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ s₁)
    (hcold : ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν →
      (∀ d ∈ plaquetteOffsets μ ν, TorusFields.OffsetInBox m (a + d)) →
        curvature V (parentBlock ℓ.side b.1 + siteOfInt a) μ ν < c.σA)
    (hBn : ∀ e, ‖B e‖ ≤ s)
    (hlog : ∀ e : TorusBond n, _root_.YangMills.Construction.TorusFields.supDist (parentBlock ℓ.side b.1) e.1 ≤ R →
      ResponseInTheExpansion.gaugeTransform g V e = expUnit (B e)) :
    ‖((adjointAction (g (parentBlock ℓ.side b.1)) (frameCoord ℓ c.ρA t m V b) -
        flatLinearPart (F := torusFrame ℓ.side t n) ℓ.coupling c.ρA unitGenerator
          (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2)
          (frameLieForm (torusFrame ℓ.side t n) B) : imaginaryQuaternions) : ℍ[ℝ])‖ ≤
      C * (s ^ 2 + Real.exp (-(r₀ * (R : ℝ)))) := by
  classical
  set F := torusFrame ℓ.side t n with hFd
  have hn : ∀ i, F.extent i = n := fun _ => rfl
  have hOdd : Odd F.blockSide := hL
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; omega
  have h2 : 2 ≤ n := by omega
  have hF : IsBlockTorus ℓ.side F := ⟨rfl, n, hn64, fun _ => rfl⟩
  have hpt := TopLevelSites.period_top_of_extent (F := F) hn
  have hNZ : NeZero (n * F.blockSide) := (inferInstance : NeZero (n * ℓ.side))
  have hNZs : NeZero (n * (stepBlockFrame ℓ.side n).blockSide) := (inferInstance : NeZero (n * ℓ.side))
  set x := torusSiteInFrame F F.depth b.1 with hx
  set Y := parentBlock ℓ.side b.1 with hY
  have hcell : enclosingCell x = torusSiteInFrame F F.top Y := TopLevelSites.enclosingCell_torusSiteInFrame hn b.1
  obtain ⟨hoc, -⟩ := TopLevelSites.centre_cellOffset hOdd hs2 x
  have hlow := TopLevelSites.fineBondAt_enclosingCell_cellOffset hOdd hs2 x b.2
  rw [hcell] at hlow
  have hnt : ¬ IsAxialTreeBond (x, b.2) := by
    intro h
    have h1 := (TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff hn hOdd h2 b.1 b.2).1 h
    have h3 : IsAxialTreeBond (F := stepBlockFrame ℓ.side n)
        (torusSiteInFrame (stepBlockFrame ℓ.side n) (stepBlockFrame ℓ.side n).depth b.1, b.2) :=
      (TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame ℓ.side n) (fun _ => rfl) hL h2
        b.1 b.2).2 h1
    exact (Finset.mem_filter.mp hb).2 h3
  have hchart : (x, b.2) ∈ chordBonds (finiteCells F) :=
    (hCU F ℓ.coupling hOdd hs2).mem_chordBonds_of_not_tree _ hnt
  have hframe : frameCoord ℓ c.ρA t m V b =
      reflectedBondCoord ℓ.coupling c.ρA m (x, b.2) (readAtLevel F F.top V) := by
    have hbig' : ∀ i : Fin 4, 4 * m + 5 < (torusFrame ℓ.side t n).extent i := fun _ => hbig
    unfold StepCosts.frameCoord bondFrameCoord
    rw [if_pos hbig']
  have hlogF : ∀ (h : Fin 4 → ℤ) (l : Fin 4), BondWithinRadius R (h, l) →
      BlockAverages.gaugeTransform (fun z => g (toTorusSite n z)) (readAtLevel F F.top V)
          (torusSiteInFrame F F.top Y + siteOfCoords F.top h) l =
        expUnit (frameLieForm F B (torusSiteInFrame F F.top Y + siteOfCoords F.top h) l) := by
    intro h l hq
    have e1 : toTorusSite n (torusSiteInFrame F F.top Y + siteOfCoords F.top h : F.Cell) = Y + siteOfInt h := by
      rw [TopLevelSites.toTorusSite_add hpt, TopLevelSites.toTorusSite_torusSiteInFrame hpt,
        TopLevelSites.toTorusSite_siteOfCoords hpt]
    have hd : _root_.YangMills.Construction.TorusFields.supDist Y (Y + siteOfInt h) ≤ R := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le Y h R fun i => by
      have h1 : |h i| ≤ (R : ℤ) := hq.1 i
      have h1' := abs_le.mp h1
      omega
    have e2 := hlog (Y + siteOfInt h, l) hd
    rw [gaugeTransform_readAtLevel hn, e1, e2]
    unfold frameLieForm
    rw [e1]
  have hcm := isSmallCurvature_reflectedField_readAtLevel (F := F) hn (m := m) (by omega) hσ V Y hcold
  have hcR := isSmallCurvature_reflectedField_readAtLevel (F := F) hn (m := R) (by omega) hσ V Y
    (fun e μ ν hlt hd => hcold e μ ν hlt (fun d hdm i => (hd d hdm i).trans (by exact_mod_cast hRm)))
  have key := hFrame F (torusSiteInFrame F F.top Y) R m (cellOffset x) b.2 (readAtLevel F F.top V)
    (fun z => g (toTorusSite n z)) (frameLieForm F B) unitGenerator s hF (fun _ => hbig) hR16 hRm hoc
    (by rw [hlow]; exact hchart) norm_unitGenerator hs0 hs1 hcm hcR (fun z l => hBn _) hlogF
  rw [hlow] at key
  have e4 : toTorusSite n (torusSiteInFrame F F.top Y) = Y := TopLevelSites.toTorusSite_torusSiteInFrame hpt Y
  simp only [e4] at key
  rw [hframe]
  exact key
end
section
variable {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n]
private theorem isAxialTreeBond_of_not_mem_chartBonds {b : TorusBond (n * ℓ.side)}
    (hb : b ∉ chartBonds ℓ.side n) :
    IsAxialTreeBond (F := stepBlockFrame ℓ.side n) (torusSiteInFrame (stepBlockFrame ℓ.side n) 0 b.1, b.2) := by
  classical
  by_contra h
  exact hb (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
private theorem minimalLog_gauge_eq_zero_of_tree (hL : Odd ℓ.side) (h2 : 2 ≤ n) (W : TorusField (n * ℓ.side))
    (g : TorusSite n → UnitQuaternion) {b : TorusBond (n * ℓ.side)} (hb : b ∉ chartBonds ℓ.side n) :
    minimalLog (ResponseInTheExpansion.gaugeTransform (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ W x) W b) =
      0 := by
  have ht := isAxialTreeBond_of_not_mem_chartBonds hb
  have hNZ : NeZero (n * (stepBlockFrame ℓ.side n).blockSide) := (inferInstance : NeZero (n * ℓ.side))
  obtain ⟨x, i⟩ := b
  have hbs : parentBlock ℓ.side (x + TorusFields.unitStep (n * ℓ.side) i) = parentBlock ℓ.side x :=
    (parentBlock_add_unitStep (F := stepBlockFrame ℓ.side n) (fun _ => rfl) hL h2 x i).2 ht.1
  have hs := BlockTrees.blockGauge_add_unitStep hL h2 W x i ht
  have e : ResponseInTheExpansion.gaugeTransform (fun x => g (parentBlock ℓ.side x) * blockTreeGauge ℓ W x) W (x, i) =
      expUnit 0 := by
    rw [TorusFields.expUnit_zero]
    change g (parentBlock ℓ.side x) * BlockTrees.blockGauge ℓ.side W x * W x i *
      (g (parentBlock ℓ.side (x + TorusFields.unitStep (n * ℓ.side) i)) *
        BlockTrees.blockGauge ℓ.side W (x + TorusFields.unitStep (n * ℓ.side) i))⁻¹ = 1
    rw [hbs, hs]
    group
  rw [e]
  exact BlockTrees.minimalLog_expUnit (by simpa using Real.pi_pos)
private theorem responseOfLieForm_eq_zero_of_tree (a ρ : ℝ) (u : ℕ) (hL : Odd ℓ.side) (h2 : 2 ≤ n)
    (B : TorusBond n → imaginaryQuaternions) {b : TorusBond (n * ℓ.side)} (hb : b ∉ chartBonds ℓ.side n) :
    responseOfLieForm a ρ ℓ.side u B b = 0 := by
  classical
  have ht := isAxialTreeBond_of_not_mem_chartBonds hb
  have hNZ : NeZero (n * (stepBlockFrame ℓ.side n).blockSide) := (inferInstance : NeZero (n * ℓ.side))
  have hNZ' : NeZero (n * (torusFrame ℓ.side u n).blockSide) := (inferInstance : NeZero (n * ℓ.side))
  have hOdd : Odd (torusFrame ℓ.side u n).blockSide := hL
  have ht' : IsAxialTreeBond (F := torusFrame ℓ.side u n)
      (torusSiteInFrame (torusFrame ℓ.side u n) (torusFrame ℓ.side u n).depth b.1, b.2) :=
    (TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := torusFrame ℓ.side u n) (fun _ => rfl) hOdd h2
      b.1 b.2).2
      ((TopLevelSites.isAxialTreeBond_torusSiteInFrame_iff (F := stepBlockFrame ℓ.side n) (fun _ => rfl) hL h2
        b.1 b.2).1 ht)
  rw [responseOfLieForm_eq a ρ u hL h2 B b, if_neg ht'.1]
  have hzero : ∀ V, torusCoordinate a ρ
      (torusSiteInFrame (torusFrame ℓ.side u n) (torusFrame ℓ.side u n).depth b.1, b.2) V = 0 := by
    intro V
    unfold torusCoordinate minimizingBondCoordinate minimizingCoordinates
    split_ifs with h
    · exact h.choose_spec.1 _ fun hm => (Finset.mem_filter.mp hm).2 ht'
    · rfl
  have hentry : ∀ e, flatCoefficient a ρ unitGenerator
      (torusSiteInFrame (torusFrame ℓ.side u n) (torusFrame ℓ.side u n).depth b.1, b.2) e = 0 := by
    intro e
    unfold flatCoefficient bondDeriv
    simp only [hzero]
    simp
  unfold flatLinearPart
  simp [hentry]
abbrev _root_.YangMills.SharedProofs.p63547 := @responseOfLieForm_eq_zero_of_tree
end
private theorem ballRadius_bounds {Lr nn Rr D : ℝ} {j : ℕ} (hL : 8 ≤ Lr) (hnn : 0 ≤ nn) (hR : 2 ≤ Rr)
    (hD : D ≤ (20 * nn / Lr ^ j + 4 * Rr) / Lr + 1) :
    D + 3 * Rr ≤ 20 * nn / Lr ^ (j + 1) + 4 * Rr ∧ D ≤ 20 * nn + Rr + 1 := by
  have hL0 : 0 < Lr := by linarith
  have e : (20 * nn / Lr ^ j + 4 * Rr) / Lr = 20 * nn / Lr ^ (j + 1) + 4 * Rr / Lr := by
    rw [pow_succ]
    field_simp
  have hP : 20 * nn / Lr ^ (j + 1) ≤ 20 * nn := by
    have h1 : (1 : ℝ) ≤ Lr ^ (j + 1) := one_le_pow₀ (by linarith)
    exact div_le_self (by positivity) h1
  have hQ : 4 * Rr / Lr ≤ Rr / 2 := by
    rw [div_le_iff₀ hL0]
    nlinarith
  rw [e] at hD
  constructor <;> linarith
section
variable (Tb : ParameterAssignment) (y : ℝ)
set_option maxHeartbeats 1000000 in
private theorem logarithmOneStepAt_of_reflectedCoord (c : ColdChainParameters) {C r₀ s₁ : ℝ} (hC : 0 ≤ C) (hr₀ : 0 < r₀)
    (hs₁ : 0 < s₁) (hFrame : ReflectedCoordinateBound Tb.coupling Tb.side c C r₀ s₁)
    (hCU : chartEquivarianceStatement) (hfit : (Tb.stepParameters y).Admissible) (eρ : c.ρA = Tb.ρA)
    (hσ : Tb.threshold ≤ c.σA) (hσA : 0 < c.σA) (hRet : ExpansionReturnsAt (Tb.stepParameters y))
    (hW : ∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β)) :
    logarithmOneStepAt Tb y := by
  classical
  have hLo : Odd (Tb.stepParameters y).side := hfit.L_odd
  have hB : 0 < (Tb.stepParameters y).B := hfit.B_pos
  obtain ⟨x₀, hx₀, hfl⟩ := eventually_log_bounds (2 ^ 13 + 4 * (Tb.stepParameters y).B + 16 + 1 / s₁)
  refine ⟨C + 22, r₀, x₀, hr₀, ?_⟩
  intro T β k n _ nn j o o' V W g s hloc hj hs0 hsx hblk hcoldV hnear hlow b hb
  set x := (couplingFlow (Tb.stepParameters y) β k).1 with hx
  have hx1 : 1 ≤ x := hx₀.trans hloc.floor_le
  obtain ⟨h17, hlog3, huK⟩ := hfl x hloc.floor_le
  set u := x ^ (1 / 200 : ℝ) with hu
  have h1s : 0 < 1 / s₁ := by positivity
  have hu16 : 16 ≤ u := by linarith [show (0 : ℝ) < 2 ^ 13 by norm_num]
  have hu0 : 0 < u := by linarith
  set R : ℕ := ⌊Real.log x ^ 3⌋₊ with hRd
  have hscale : localLogScale (Tb.stepParameters y) β k = (R : ℝ) := rfl
  have hlog0 : 0 ≤ Real.log x := by linarith
  have hlog3' : 17 ≤ Real.log x ^ 3 := by nlinarith [sq_nonneg (Real.log x)]
  have hR16 : 16 ≤ R := Nat.le_floor (by push_cast; linarith)
  have hRu : (R : ℝ) ≤ u := (Nat.floor_le (by linarith)).trans hlog3
  have hjM : (j : ℝ) ≤ Real.log x ^ 2 := (Nat.lt_of_lt_floor hj).le
  have hj3 : (j : ℝ) ≤ u := by
    have : Real.log x ^ 2 ≤ Real.log x ^ 3 := by nlinarith [sq_nonneg (Real.log x)]
    linarith
  have hjM' : j < chainDepth x := hj
  set t := k + j with ht
  have htM : t ≤ k + 2 * chainDepth x := by omega
  have hmove := abs_couplingFlow_sub_le hRet (fun β h => hW β h) hloc.coupling_ge (show k ≤ t by omega) htM
  have hmove' : |(couplingFlow (Tb.stepParameters y) β t).1 - x| ≤ 2 * (Tb.stepParameters y).B * u := by
    refine hmove.trans ?_
    have e : ((t : ℝ) - (k : ℝ)) = j := by
      rw [ht]
      push_cast
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hj3 (by positivity)
  have hcoup : (T.stage t).coupling = (couplingFlow (Tb.stepParameters y) β t).1 :=
    hloc.onFamily.coupling_eq t (Nat.le_succ_of_le htM)
  have htable := hloc.onFamily.onFamily t htM
  have hρ : (T.stage t).anchorRadius = c.ρA := htable.anchorRadius_eq.trans eρ.symm
  have hm₀ : (T.stage t).toStepSetup.frameReach = clusterRange (couplingFlow (Tb.stepParameters y) β t).1 / 2 ^ 11 := by
    rw [← hcoup]
    rfl
  obtain ⟨hRm, hbig, h64, hroom⟩ := scale_bounds (R := R) (n := n) (nn := nn) hB hx1 (show _ ≤ u by linarith)
    hmove' hloc.le_rpow hRu hloc.side_ge
  rw [← hm₀] at hRm hbig hroom
  set m₀ := (T.stage t).toStepSetup.frameReach with hm₀d
  have h2 : 2 ≤ n := by omega
  have hnn0 : 0 ≤ nn := by linarith [hloc.one_le]
  set Y := parentBlock (Tb.stepParameters y).side b.1 with hY
  have hLr : (8 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by
    have h1 : 8 ≤ (Tb.stepParameters y).side := by
      have := hfit.L_ge
      omega
    exact_mod_cast h1
  have hD : (_root_.YangMills.Construction.TorusFields.supDist Y o : ℝ) ≤ ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) j /
      ((Tb.stepParameters y).side : ℝ) + 1 := by
    have h1 := TorusBalls.supDist_parentBlock_le_div_add_one (n := n) (Tb.stepParameters y).side b.1 o'
    rw [hblk] at h1
    have h3 : (_root_.YangMills.Construction.TorusFields.supDist b.1 o' : ℝ) ≤
        ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) j := by
      have := (Finset.mem_filter.mp hb).2
      exact this
    have h4 : ((_root_.YangMills.Construction.TorusFields.supDist b.1 o' / (Tb.stepParameters y).side : ℕ) : ℝ) ≤
        (_root_.YangMills.Construction.TorusFields.supDist b.1 o' : ℝ) / ((Tb.stepParameters y).side : ℝ) := Nat.cast_div_le
    have h5 : (_root_.YangMills.Construction.TorusFields.supDist Y o : ℝ) ≤ ((_root_.YangMills.Construction.TorusFields.supDist b.1 o' / (Tb.stepParameters y).side : ℕ) : ℝ) + 1 := by
      exact_mod_cast h1
    have h6 : (_root_.YangMills.Construction.TorusFields.supDist b.1 o' : ℝ) / ((Tb.stepParameters y).side : ℝ) ≤
        ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) j /
          ((Tb.stepParameters y).side : ℝ) := by
      gcongr
    linarith
  have hR2 : (2 : ℝ) ≤ R := by
    have : (16 : ℝ) ≤ R := by exact_mod_cast hR16
    linarith
  obtain ⟨hD1, hD2⟩ := ballRadius_bounds hLr hnn0 hR2 hD
  set r₁ := ballRadius (Tb.stepParameters y).side nn (localLogScale (Tb.stepParameters y) β k) (j + 1) with hr₁
  have hr₁e : r₁ = 20 * nn / ((Tb.stepParameters y).side : ℝ) ^ (j + 1) + 4 * (R : ℝ) := rfl
  rw [← hr₁e] at hD1
  set B : TorusBond n → imaginaryQuaternions := ballLog g V o r₁ with hBd
  have hBn : ∀ e, ‖B e‖ ≤ s := fun e => by
    rw [hBd]
    unfold ballLog
    split_ifs with h
    · exact hnear.log_le e h
    · simpa using hs0
  have hlogB : ∀ e : TorusBond n, _root_.YangMills.Construction.TorusFields.supDist Y e.1 ≤ R → ResponseInTheExpansion.gaugeTransform g V e = expUnit (B e) :=
    fun e he => by
    have h1 : e.1 ∈ supBall o r₁ := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle e.1 Y o
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm e.1 Y] at h2
      have h3 : (_root_.YangMills.Construction.TorusFields.supDist e.1 o : ℝ) ≤ (_root_.YangMills.Construction.TorusFields.supDist Y e.1 : ℝ) + (_root_.YangMills.Construction.TorusFields.supDist Y o : ℝ) := by exact_mod_cast h2
      have h4 : (_root_.YangMills.Construction.TorusFields.supDist Y e.1 : ℝ) ≤ R := by exact_mod_cast he
      linarith
    rw [hBd]
    unfold ballLog
    rw [if_pos h1]
    exact (TopLevelSites.expUnit_minimalLog _).symm
  have hcold' : ∀ (a : Fin 4 → ℤ) (μ ν : Fin 4), μ < ν →
      (∀ d ∈ plaquetteOffsets μ ν, TorusFields.OffsetInBox m₀ (a + d)) → curvature V (Y + siteOfInt a) μ ν < c.σA := by
    intro a μ ν hlt hd
    refine lt_of_lt_of_le (hcoldV (Y + siteOfInt a, μ, ν) ?_) hσ
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt, fun z hz => ?_⟩
    obtain ⟨d, hd', rfl⟩ := (mem_plaquetteVertices_iff_offset _ _ _ _).1 hz
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have e1 : Y + siteOfInt a + siteOfInt d = Y + siteOfInt (a + d) := by rw [siteOfInt_add, add_assoc]
    rw [e1]
    have h1 : _root_.YangMills.Construction.TorusFields.supDist Y (Y + siteOfInt (a + d)) ≤ m₀ := _root_.YangMills.Construction.TorusFields.supDist_add_siteOfInt_le Y (a + d) m₀ fun i => by
      have h2 : |(a + d) i| ≤ (m₀ : ℤ) := hd d hd' i
      have h3 := abs_le.mp h2
      omega
    have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle (Y + siteOfInt (a + d)) Y o
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm (Y + siteOfInt (a + d)) Y] at h2
    have h3 : (_root_.YangMills.Construction.TorusFields.supDist (Y + siteOfInt (a + d)) o : ℝ) ≤
        (_root_.YangMills.Construction.TorusFields.supDist Y (Y + siteOfInt (a + d)) : ℝ) + (_root_.YangMills.Construction.TorusFields.supDist Y o : ℝ) := by
      exact_mod_cast h2
    have h4 : (_root_.YangMills.Construction.TorusFields.supDist Y (Y + siteOfInt (a + d)) : ℝ) ≤ m₀ := by exact_mod_cast h1
    have h5 : 20 * nn + R + 2 + (m₀ : ℝ) ≤ ((localBlockSide (Tb.stepParameters y) β k : ℕ) : ℝ) := hroom
    linarith
  have hx0 : 0 ≤ x := by linarith
  have hsu : s ≤ u⁻¹ := by
    have h1 : x ^ (-(1 / 4 : ℝ)) ≤ x ^ (-(1 / 200 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_neg hx0 (1 / 200 : ℝ)] at h1
    exact hsx.trans h1
  have hs16 : s ≤ 1 / 16 := by
    have h1 : u⁻¹ ≤ (16 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hu16
    have h2 : (1 / 16 : ℝ) = (16 : ℝ)⁻¹ := by norm_num
    rw [h2]
    linarith
  have hss : s ≤ s₁ := by
    have h3 : 1 / s₁ ≤ u := by linarith [show (0 : ℝ) < 2 ^ 13 by norm_num]
    have h1 : u⁻¹ ≤ (1 / s₁)⁻¹ := inv_anti₀ h1s h3
    have h2 : (1 / s₁)⁻¹ = s₁ := by simp
    rw [h2] at h1
    linarith
  have hsq : 0 ≤ s ^ 2 := by positivity
  have hEp := Real.exp_pos (-(r₀ * localLogScale (Tb.stepParameters y) β k))
  by_cases hbc : b ∈ chartBonds (Tb.stepParameters y).side n
  · have hlg := norm_minimalLog_gauge_sub_le hLo h2 V W g b (B (Y, b.2)) hs0 hs16
      (hlogB (Y, b.2) (by simp [_root_.YangMills.Construction.TorusFields.supDist_self])) (hBn _) (hlow b hb)
    have hfr := norm_reflected_sub_flatLinearPart_le (ℓ := Tb.stepParameters y) (c := c) hFrame hCU hLo hσA t m₀ R
      h64 hbig hR16 hRm V g B b hbc hs0 hss hcold' hBn hlogB
    have hYZ : Y ∈ supBall o (r₁ - 3 * localLogScale (Tb.stepParameters y) β k) := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [hscale]
      linarith
    have hNZt : NeZero (n * (torusFrame (Tb.stepParameters y).side t n).blockSide) :=
      (inferInstance : NeZero (n * (Tb.stepParameters y).side))
    have hNZs : NeZero (n * (stepBlockFrame (Tb.stepParameters y).side n).blockSide) :=
      (inferInstance : NeZero (n * (Tb.stepParameters y).side))
    have hOddt : Odd (torusFrame (Tb.stepParameters y).side t n).blockSide := hLo
    have hcross : IsCrossingBond (F := torusFrame (Tb.stepParameters y).side t n)
        (torusSiteInFrame (torusFrame (Tb.stepParameters y).side t n)
          (torusFrame (Tb.stepParameters y).side t n).depth b.1, b.2) ↔
        IsCrossingBond (F := stepBlockFrame (Tb.stepParameters y).side n)
          (torusSiteInFrame (stepBlockFrame (Tb.stepParameters y).side n) 0 b.1, b.2) :=
      (TopLevelSites.isCrossingBond_torusSiteInFrame_iff (F := torusFrame (Tb.stepParameters y).side t n)
          (fun _ => rfl) hOddt h2 b.1 b.2).trans
        (TopLevelSites.isCrossingBond_torusSiteInFrame_iff (F := stepBlockFrame (Tb.stepParameters y).side n)
          (fun _ => rfl) hLo h2 b.1 b.2).symm
    have heta : deviationInGauge T t g (supBall o (r₁ - 3 * localLogScale (Tb.stepParameters y) β k)) V W b =
        adjointAction (g Y) (chartCoord (Tb.stepParameters y) V W b -
          StepCosts.frameCoord (Tb.stepParameters y) c.ρA t m₀ V b) := by
      unfold deviationInGauge
      rw [if_pos ⟨hYZ, hbc⟩, hρ]
      rfl
    have hresp := responseOfLieForm_eq (ℓ := Tb.stepParameters y) (Tb.stepParameters y).coupling c.ρA t hLo h2 B b
    rw [hρ, heta, hresp]
    simp only [hcross]
    set l := minimalLog (ResponseInTheExpansion.gaugeTransform
      (fun x => g (parentBlock (Tb.stepParameters y).side x) * blockTreeGauge (Tb.stepParameters y) W x) W b)
    set p := chartCoord (Tb.stepParameters y) V W b
    set w := StepCosts.frameCoord (Tb.stepParameters y) c.ρA t m₀ V b
    set fS := flatLinearPart (F := torusFrame (Tb.stepParameters y).side t n) (Tb.stepParameters y).coupling c.ρA
      unitGenerator
      (torusSiteInFrame (torusFrame (Tb.stepParameters y).side t n)
        (torusFrame (Tb.stepParameters y).side t n).depth b.1, b.2)
      (frameLieForm (torusFrame (Tb.stepParameters y).side t n) B)
    set cr : imaginaryQuaternions := if IsCrossingBond (F := stepBlockFrame (Tb.stepParameters y).side n)
      (torusSiteInFrame (stepBlockFrame (Tb.stepParameters y).side n) 0 b.1, b.2) then B (Y, b.2) else 0
    have hAp : adjointAction (g Y) p = adjointAction (g Y) (p - w) + adjointAction (g Y) w := by
      rw [← Adjoint.adjointAction_add, sub_add_cancel]
    have e : l - (fS + cr) - adjointAction (g Y) (p - w) =
        (l - adjointAction (g Y) p - cr) + (adjointAction (g Y) w - fS) := by
      rw [hAp]
      abel
    rw [e]
    have n1 : ‖l - adjointAction (g Y) p - cr‖ ≤ 22 * s ^ 2 := hlg
    have n2 : ‖adjointAction (g Y) w - fS‖ ≤ C * (s ^ 2 + Real.exp (-(r₀ * (R : ℝ)))) := hfr
    have n3 := norm_add_le (l - adjointAction (g Y) p - cr) (adjointAction (g Y) w - fS)
    change ‖(l - adjointAction (g Y) p - cr) + (adjointAction (g Y) w - fS)‖ ≤ _
    have hE' : 0 < Real.exp (-(r₀ * (R : ℝ))) := Real.exp_pos _
    have p1 : 0 ≤ 22 * Real.exp (-(r₀ * (R : ℝ))) := by positivity
    rw [hscale]
    have e2 : (C + 22) * (s ^ 2 + Real.exp (-(r₀ * (R : ℝ)))) =
        C * (s ^ 2 + Real.exp (-(r₀ * (R : ℝ)))) + 22 * s ^ 2 + 22 * Real.exp (-(r₀ * (R : ℝ))) := by ring
    rw [e2]
    linarith
  · have hlg := minimalLog_gauge_eq_zero_of_tree hLo h2 W g hbc
    have hresp := responseOfLieForm_eq_zero_of_tree (ℓ := Tb.stepParameters y) (Tb.stepParameters y).coupling
      (T.stage t).anchorRadius t hLo h2 B hbc
    have heta : deviationInGauge T t g (supBall o (r₁ - 3 * localLogScale (Tb.stepParameters y) β k)) V W b = 0 := by
      unfold deviationInGauge
      rw [if_neg (fun h => hbc h.2)]
    rw [hlg, hresp, heta]
    simp only [sub_zero, ZeroMemClass.coe_zero, norm_zero]
    positivity
end
end LogarithmOneStep
open LogarithmOneStep in
theorem logarithmOneStepStatement_holds (hFr : ReflectedCoordNearFlatLinearPart)
    (hCU : chartEquivarianceStatement) : logarithmOneStepStatement := by
  intro a _
  refine ⟨0, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hDr hCS _ _ _
  obtain ⟨c, nss, hTies, -⟩ := hCS
  obtain ⟨-, -, eρ, eσ, -, -, -, hHolds⟩ := hTies
  refine ⟨Tb.floorMin, fun y hy hRet hW => ?_⟩
  have hfit := hDr.fits y hy
  obtain ⟨C, r₀, s₁, hC, hr₀, hs₁, hFrame⟩ := hFr Tb.coupling Tb.side c hDr.L_odd hHolds
  have hσA : 0 < c.σA := hHolds.positivity.2.2.2.1
  have hσ : Tb.threshold ≤ c.σA := by
    have h1 := hDr.σ_le
    have h2 := hDr.σ_pos
    rw [eσ]
    linarith
  exact logarithmOneStepAt_of_reflectedCoord Tb y c hC hr₀ hs₁ hFrame hCU hfit eρ hσ hσA hRet hW
end YangMills.Construction.ResponseInTheExpansion
end
