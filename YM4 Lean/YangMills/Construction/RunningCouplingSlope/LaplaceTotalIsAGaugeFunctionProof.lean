import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTheGaugeProof
import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingIsASettingProof
import YangMills.Construction.ClusterExpansionOfAStep.GaugeOfACaseProof
import YangMills.Construction.ColdStepAtMirrorFrames.AdjointOfTheGroup
import YangMills.Construction.ColdStepAtMirrorFrames.AdjointOnABond
import YangMills.Construction.RunningCouplingSlope.LaplaceTotalIsAGaugeFunction
import YangMills.Construction.RunningCouplingSlope.LeastPointReadsTheChainProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory
namespace YangMills.Construction.RunningCouplingSlope
namespace GaugeInvariance
private theorem pathHolonomy_one {H : BlockAverages.BlockFrame} {j : ℕ} (x : H.Site j) (l : List BlockAverages.PathStep) :
    BlockAverages.pathHolonomy (fun _ _ => (1 : BlockAverages.UnitQuaternion) : H.GaugeField j) x l = 1 := by apply _root_.YangMills.SharedProofs.p3325 <;> assumption
private theorem norm_mul_sub_one_le (a b : BlockAverages.UnitQuaternion) :
    ‖((a * b : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(a : ℍ[ℝ]) - 1‖ + ‖(b : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_mul_sub_one_le <;> assumption
private theorem norm_inv_sub_one (a : BlockAverages.UnitQuaternion) :
    ‖((a⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(a : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
private theorem curvature_le_four_mul {m : ℕ} (W : TorusFields.TorusField m) {e : ℝ}
    (h : ∀ x i, ‖(W x i : ℍ[ℝ]) - 1‖ ≤ e) (x : TorusFields.TorusSite m)
    (μ ν : Fin 4) : TorusFields.curvature W x μ ν ≤ 4 * e := by
  unfold TorusFields.curvature TorusFields.holonomy
  have h1 := norm_mul_sub_one_le (W x μ * W (x + TorusFields.unitStep m μ) ν * (W (x + TorusFields.unitStep m ν) μ)⁻¹) (W x ν)⁻¹
  have h2 := norm_mul_sub_one_le (W x μ * W (x + TorusFields.unitStep m μ) ν) (W (x + TorusFields.unitStep m ν) μ)⁻¹
  have h3 := norm_mul_sub_one_le (W x μ) (W (x + TorusFields.unitStep m μ) ν)
  rw [norm_inv_sub_one] at h1 h2
  linarith [h x μ, h (x + TorusFields.unitStep m μ) ν, h (x + TorusFields.unitStep m ν) μ, h x ν]
private theorem norm_expUnit_sub_one_le (w : BlockAverages.imaginaryQuaternions) :
    ‖((BlockAverages.expUnit w : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖(w : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.SmallCellTerms.norm_coe_expUnit_sub_one_le <;> assumption
private theorem toImaginary_toCoords (w : BlockAverages.imaginaryQuaternions) :
    ColdStepAtMirrorFrames.toImaginary (StepSettings.toCoords w) = w := by apply _root_.YangMills.Construction.BlockTrees.toImaginary_toCoords <;> assumption
private theorem norm_adjointAction (u : BlockAverages.UnitQuaternion) (X : BlockAverages.imaginaryQuaternions) :
    ‖((ColdStepAtMirrorFrames.adjointAction u X : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ = ‖(X : ℍ[ℝ])‖ := by
  show ‖(u : ℍ[ℝ]) * (X : ℍ[ℝ]) * ((u⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ])‖ = _
  rw [norm_mul, norm_mul, TorusContours.norm_coe_unitQuaternion, TorusContours.norm_coe_unitQuaternion, one_mul, mul_one]
abbrev _root_.YangMills.SharedProofs.p17728 := @norm_adjointAction
private theorem adjointAction_add_eq (u : BlockAverages.UnitQuaternion) (X X' : BlockAverages.imaginaryQuaternions) :
    ColdStepAtMirrorFrames.adjointAction u (X + X') =
      ColdStepAtMirrorFrames.adjointAction u X + ColdStepAtMirrorFrames.adjointAction u X' := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
private theorem haarLogDensity_adjoint (u : BlockAverages.UnitQuaternion) {f f' : BlockAverages.imaginaryQuaternions}
    {v v' : EuclideanSpace ℝ (Fin 3)}
    (h : f' + ColdStepAtMirrorFrames.toImaginary v' =
      ColdStepAtMirrorFrames.adjointAction u (f + ColdStepAtMirrorFrames.toImaginary v)) :
    ColdStepAtMirrorFrames.haarLogDensity (StepSettings.toCoords f' + v') =
      ColdStepAtMirrorFrames.haarLogDensity (StepSettings.toCoords f + v) := by
  have e : ‖StepSettings.toCoords f' + v'‖ = ‖StepSettings.toCoords f + v‖ := by
    rw [← SettingShifts.coordNorm_eq_norm, ← SettingShifts.coordNorm_eq_norm]
    unfold StepSettings.coordNorm
    rw [FreeBondMoves.toImaginary_add, FreeBondMoves.toImaginary_add, toImaginary_toCoords, toImaginary_toCoords, h,
      norm_adjointAction]
  unfold ColdStepAtMirrorFrames.haarLogDensity
  rw [e]
private theorem fit_conj (m : ℍ[ℝ]) (u v X : BlockAverages.UnitQuaternion) :
    ‖(u : ℍ[ℝ]) * m * ((v⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ])‖ -
        ((u : ℍ[ℝ]) * m * ((v⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) *
          (((u * X * v⁻¹)⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ])).re =
      ‖m‖ - (m * ((X⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ])).re := by
  have h1 : ((u : ℍ[ℝ]) * m * ((v⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ])) *
        (((u * X * v⁻¹)⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) =
      (u : ℍ[ℝ]) * (m * ((X⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ])) *
        ((u⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) := by
    have h2 : ((u * X * v⁻¹)⁻¹ : BlockAverages.UnitQuaternion) = v * X⁻¹ * u⁻¹ := by group
    have h3 : ((v⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * (v : ℍ[ℝ]) = 1 := by
      rw [← Submonoid.coe_mul]
      simp
    rw [h2]
    simp only [Submonoid.coe_mul]
    calc (u : ℍ[ℝ]) * m * ((v⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) *
          ((v : ℍ[ℝ]) * ((X⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * ((u⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]))
        = (u : ℍ[ℝ]) * m * (((v⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * (v : ℍ[ℝ])) *
            ((X⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) * ((u⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]) := by
          simp only [mul_assoc]
      _ = _ := by
          rw [h3]
          simp only [mul_one, mul_assoc]
  have h4 : ∀ (p q : ℍ[ℝ]), (p * q).re = (q * p).re := by
    intro p q
    simp only [Quaternion.re_mul]
    ring
  have h5 : ∀ q : ℍ[ℝ], ((u : ℍ[ℝ]) * q * ((u⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ])).re = q.re := by
    intro q
    rw [h4, ← mul_assoc, ← Submonoid.coe_mul]
    simp
  rw [h1, h5, norm_mul, norm_mul, TorusContours.norm_coe_unitQuaternion, TorusContours.norm_coe_unitQuaternion,
    one_mul, mul_one]
private theorem sum_affine_congr {ι : Type} [Fintype ι] (x : ℝ) (c c' p p' j j' : ι → ℝ)
    (hc : ∑ Y, c Y = ∑ Y, c' Y) (hp : ∀ Y, p Y = p' Y) (hj : ∀ Y, j Y = j' Y) :
    ∑ Y, (x * c Y - p Y - j Y) = ∑ Y, (x * c' Y - p' Y - j' Y) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hc]
  simp only [hp, hj]
section Blocks
variable {n : ℕ} [NeZero n]
private theorem parentBlock_add_of_crossing {F : BlockAverages.BlockFrame} (hn : ∀ i, F.extent i = n)
    (hL : Odd F.blockSide) (h2 : 2 ≤ n) [NeZero (n * F.blockSide)]
    (x : TorusFields.TorusSite (n * F.blockSide)) (i : Fin 4)
    (hcr : BlockAverages.IsCrossingBond (StepCosts.torusSiteInFrame F F.depth x, i)) :
    TorusLumps.parentBlock F.blockSide (x + TorusFields.unitStep (n * F.blockSide) i) =
      TorusLumps.parentBlock F.blockSide x + TorusFields.unitStep n i := by
  have hs : ∀ i, 2 ≤ F.extent i := fun i => by rw [hn]; exact h2
  have hnext : StepCosts.torusSiteInFrame F F.depth (x + TorusFields.unitStep (n * F.blockSide) i) =
      StepCosts.torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i := by
    apply TopLevelSites.toTorusSite_injective (TopLevelSites.period_depth_of_extent hn)
    rw [TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_depth_of_extent hn),
      TopLevelSites.toTorusSite_add (TopLevelSites.period_depth_of_extent hn),
      TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_depth_of_extent hn),
      TopLevelSites.toTorusSite_unitStep (TopLevelSites.period_depth_of_extent hn)]
  have c1 := TopLevelSites.enclosingCell_torusSiteInFrame hn (x + TorusFields.unitStep (n * F.blockSide) i)
  have c0 := TopLevelSites.enclosingCell_torusSiteInFrame hn x
  have := TopLevelSites.enclosingCell_add_unitStep hL hs _ i hcr
  rw [← hnext, c1, c0] at this
  have e := congrArg (TorusLumps.toTorusSite n) this
  rw [TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn),
    TopLevelSites.toTorusSite_add (TopLevelSites.period_top_of_extent hn),
    TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn),
    TopLevelSites.toTorusSite_unitStep (TopLevelSites.period_top_of_extent hn)] at e
  exact e
private theorem parentBlock_add_of_not_crossing {F : BlockAverages.BlockFrame} (hn : ∀ i, F.extent i = n)
    [NeZero (n * F.blockSide)] (x : TorusFields.TorusSite (n * F.blockSide)) (i : Fin 4)
    (hcr : ¬ BlockAverages.IsCrossingBond (StepCosts.torusSiteInFrame F F.depth x, i)) :
    TorusLumps.parentBlock F.blockSide (x + TorusFields.unitStep (n * F.blockSide) i) =
      TorusLumps.parentBlock F.blockSide x := by
  have hnext : StepCosts.torusSiteInFrame F F.depth (x + TorusFields.unitStep (n * F.blockSide) i) =
      StepCosts.torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i := by
    apply TopLevelSites.toTorusSite_injective (TopLevelSites.period_depth_of_extent hn)
    rw [TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_depth_of_extent hn),
      TopLevelSites.toTorusSite_add (TopLevelSites.period_depth_of_extent hn),
      TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_depth_of_extent hn),
      TopLevelSites.toTorusSite_unitStep (TopLevelSites.period_depth_of_extent hn)]
  have c1 := TopLevelSites.enclosingCell_torusSiteInFrame hn (x + TorusFields.unitStep (n * F.blockSide) i)
  have c0 := TopLevelSites.enclosingCell_torusSiteInFrame hn x
  have : BlockAverages.enclosingCell (StepCosts.torusSiteInFrame F F.depth x + BlockAverages.unitStep F.depth i) =
      BlockAverages.enclosingCell (StepCosts.torusSiteInFrame F F.depth x) := by
    by_contra hne
    exact hcr hne
  rw [← hnext, c1, c0] at this
  have e := congrArg (TorusLumps.toTorusSite n) this
  rw [TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn),
    TopLevelSites.toTorusSite_torusSiteInFrame (TopLevelSites.period_top_of_extent hn)] at e
  exact e
end Blocks
variable {R : StepSettings.StepSetup} {n : ℕ} [NeZero n]
private theorem gaugeAt_trivial (x : TorusFields.TorusSite (n * R.params.side)) :
    StepSettings.gaugeAt (R := R) (TorusFields.trivialField (n * R.params.side)) x = 1 :=
  pathHolonomy_one _ _
private theorem gaugeAt_coldChartSetting (U : TorusFields.TorusField n) (x : TorusFields.TorusSite (n * R.params.side)) :
    StepSettings.gaugeAt (R := R) (StepSettings.coldChartSetting R U).fine x = 1 :=
  gaugeAt_trivial x
private theorem field_of_mem_chart (U : TorusFields.TorusField n)
    (ζ : StepSettings.FreeCoords (StepCosts.chartBonds R.params.side n))
    {x : TorusFields.TorusSite (n * R.params.side)} {i : Fin 4}
    (hb : (x, i) ∈ StepCosts.chartBonds R.params.side n) : (StepSettings.coldChartSetting R U).field ζ x i =
      (open Classical in if BlockAverages.IsCrossingBond (F := TorusLumps.stepBlockFrame R.params.side n)
          (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 0 x, i)
        then BlockAverages.expUnit ((StepSettings.coldChartSetting R U).frame (x, i) +
          ColdStepAtMirrorFrames.toImaginary (ζ ⟨(x, i), hb⟩)) * U (TorusLumps.parentBlock R.params.side x) i
        else BlockAverages.expUnit ((StepSettings.coldChartSetting R U).frame (x, i) +
          ColdStepAtMirrorFrames.toImaginary (ζ ⟨(x, i), hb⟩))) := by
  have h : (StepSettings.coldChartSetting R U).field ζ x i =
      StepSettings.chartLink (StepSettings.coldChartSetting R U) x i
        ((StepSettings.coldChartSetting R U).frame (x, i) + ColdStepAtMirrorFrames.toImaginary (ζ ⟨(x, i), hb⟩)) :=
    dif_pos hb
  rw [h]
  unfold StepSettings.chartLink
  rw [gaugeAt_coldChartSetting, gaugeAt_coldChartSetting, inv_one, one_mul, mul_one]
  rfl
private theorem field_of_not_mem_chart (U : TorusFields.TorusField n)
    (ζ : StepSettings.FreeCoords (StepCosts.chartBonds R.params.side n))
    {x : TorusFields.TorusSite (n * R.params.side)} {i : Fin 4}
    (hb : (x, i) ∉ StepCosts.chartBonds R.params.side n) : (StepSettings.coldChartSetting R U).field ζ x i = 1 :=
  dif_neg hb
private theorem field_adjoint_eq_gaugeTransform (hodd : Odd R.params.side) (h2 : 2 ≤ n)
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (V : TorusFields.TorusField n)
    (η η' : StepSettings.FreeCoords (StepCosts.chartBonds R.params.side n))
    (h : ∀ b : ↥(StepCosts.chartBonds R.params.side n),
      (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).frame b.1 +
          ColdStepAtMirrorFrames.toImaginary (η' b) =
        ColdStepAtMirrorFrames.adjointAction (g (TorusLumps.parentBlock R.params.side b.1.1))
          ((StepSettings.coldChartSetting R V).frame b.1 + ColdStepAtMirrorFrames.toImaginary (η b))) :
    (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).field η' =
      TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g)
        ((StepSettings.coldChartSetting R V).field η) := by
  classical
  funext x i
  show _ = g (TorusLumps.parentBlock R.params.side x) * _ *
    (g (TorusLumps.parentBlock R.params.side (x + TorusFields.unitStep _ i)))⁻¹
  by_cases hb : (x, i) ∈ StepCosts.chartBonds R.params.side n
  · rw [field_of_mem_chart _ _ hb, field_of_mem_chart _ _ hb, h ⟨(x, i), hb⟩]
    by_cases hc : BlockAverages.IsCrossingBond (F := TorusLumps.stepBlockFrame R.params.side n)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 0 x, i)
    · have hB : TorusLumps.parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) =
          TorusLumps.parentBlock R.params.side x + TorusFields.unitStep n i :=
        parentBlock_add_of_crossing (F := TorusLumps.stepBlockFrame R.params.side n) (fun _ => rfl) hodd h2 x i hc
      rw [if_pos hc, if_pos hc, hB, ColdStepAtMirrorFrames.Adjoint.expUnit_adjointAction]
      show _ * (g _ * V _ i * (g (TorusLumps.parentBlock R.params.side x + TorusFields.unitStep n i))⁻¹) = _
      group
    · have hB : TorusLumps.parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) =
          TorusLumps.parentBlock R.params.side x :=
        parentBlock_add_of_not_crossing (F := TorusLumps.stepBlockFrame R.params.side n) (fun _ => rfl) x i hc
      rw [if_neg hc, if_neg hc, hB, ColdStepAtMirrorFrames.Adjoint.expUnit_adjointAction]
  · have hT : BlockAverages.IsAxialTreeBond (F := TorusLumps.stepBlockFrame R.params.side n)
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 0 x, i) := by
      by_contra hh
      exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    have hB : TorusLumps.parentBlock R.params.side (x + TorusFields.unitStep (n * R.params.side) i) =
        TorusLumps.parentBlock R.params.side x :=
      parentBlock_add_of_not_crossing (F := TorusLumps.stepBlockFrame R.params.side n) (fun _ => rfl) x i hT.1
    rw [field_of_not_mem_chart _ _ hb, field_of_not_mem_chart _ _ hb, hB]
    simp
private theorem norm_field_sub_one_le {V : TorusFields.TorusField n} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hV : ∀ x i, ‖(V x i : ℍ[ℝ]) - 1‖ ≤ ρ)
    (hf : ∀ b, ‖(((StepSettings.coldChartSetting R V).frame b : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤ ρ)
    (η : StepSettings.FreeCoords (StepCosts.chartBonds R.params.side n))
    (hη : ∀ b, ‖η b‖ ≤ ρ) (x : TorusFields.TorusSite (n * R.params.side)) (i : Fin 4) :
    ‖(((StepSettings.coldChartSetting R V).field η x i : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 3 * ρ := by
  classical
  by_cases hb : (x, i) ∈ StepCosts.chartBonds R.params.side n
  · have hw : ∀ w : BlockAverages.imaginaryQuaternions, w = (StepSettings.coldChartSetting R V).frame (x, i) +
          ColdStepAtMirrorFrames.toImaginary (η ⟨(x, i), hb⟩) →
        ‖((BlockAverages.expUnit w : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * ρ := by
      rintro w rfl
      refine (norm_expUnit_sub_one_le _).trans ?_
      have h1 : ‖(((ColdStepAtMirrorFrames.toImaginary (η ⟨(x, i), hb⟩) : BlockAverages.imaginaryQuaternions)) :
          ℍ[ℝ])‖ = ‖η ⟨(x, i), hb⟩‖ :=
        SettingShifts.coordNorm_eq_norm _
      have h2 := norm_add_le (((StepSettings.coldChartSetting R V).frame (x, i) : BlockAverages.imaginaryQuaternions) :
          ℍ[ℝ])
        (((ColdStepAtMirrorFrames.toImaginary (η ⟨(x, i), hb⟩) : BlockAverages.imaginaryQuaternions)) : ℍ[ℝ])
      have h3 := hf (x, i)
      have h4 := hη ⟨(x, i), hb⟩
      show ‖(((StepSettings.coldChartSetting R V).frame (x, i) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) +
        ((ColdStepAtMirrorFrames.toImaginary (η ⟨(x, i), hb⟩) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤ _
      linarith
    rw [field_of_mem_chart _ _ hb]
    split_ifs
    · have h1 := norm_mul_sub_one_le (BlockAverages.expUnit ((StepSettings.coldChartSetting R V).frame (x, i) +
          ColdStepAtMirrorFrames.toImaginary (η ⟨(x, i), hb⟩)))
        (V (TorusLumps.parentBlock R.params.side x) i)
      linarith [hw _ rfl, hV (TorusLumps.parentBlock R.params.side x) i]
    · linarith [hw _ rfl]
  · rw [field_of_not_mem_chart _ _ hb]
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hρ
private theorem torusHotSites_eq_empty (hfit : R.params.Admissible) {W : TorusFields.TorusField (n * R.params.side)}
    (hW : TorusFields.IsCold R.params.threshold W) :
    TorusLumps.torusHotSites R.params W = ∅ := by
  have h : TorusLumps.torusHotLumps R.params W = ∅ := Finset.eq_empty_of_forall_notMem fun l hl => by
    obtain ⟨x, μ, ν, hlt, hs, -⟩ :=
      (TorusLumps.mem_torusHotLumps_iff R.params hfit (dvd_mul_left _ _) W l).mp hl
    exact absurd (hW x μ ν hlt) (not_lt.mpr hs)
  simp [TorusLumps.torusHotSites, h]
private theorem thickening_empty {m : ℕ} [NeZero m] (k : ℕ) :
    TorusLumps.thickening k (∅ : Finset (TorusFields.TorusSite m)) = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ColdChart.thickening_empty <;> assumption
private theorem isHullState_empty (hfit : R.params.Admissible) {W : TorusFields.TorusField (n * R.params.side)}
    (hW : TorusFields.IsCold R.params.threshold W) (r : ℕ) :
    TorusLumps.IsHullState R.params r W ∅ := by
  refine ⟨?_, ?_⟩
  · rw [torusHotSites_eq_empty hfit hW, thickening_empty]
  · intro X hX
    simp [TorusLumps.chainComponents] at hX
private theorem stepHotLumps_gaugeTransform (G : TorusFields.TorusSite (n * R.params.side) → BlockAverages.UnitQuaternion)
    (W : TorusFields.TorusField (n * R.params.side)) :
    StepCosts.stepHotLumps R.params (TorusFields.gaugeTransform G W) = StepCosts.stepHotLumps R.params W := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.GaugeInvariance.stepHotLumps_gaugeTransform <;> assumption
private theorem parentBlock_cellCentre (hodd : Odd R.params.side) (y : (TorusLumps.stepBlockFrame R.params.side n).Cell) :
    TorusLumps.parentBlock R.params.side
        (TorusLumps.toTorusSite (n * R.params.side)
          (BlockAverages.cellCentre (F := TorusLumps.stepBlockFrame R.params.side n) 0 y)) =
      TorusLumps.toTorusSite n y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.parentBlock_toTorusSite_cellCentre <;> assumption
private theorem contourMean_blockGauge (hodd : Odd R.params.side)
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (W : TorusFields.TorusField (n * R.params.side))
    (c : (TorusLumps.stepBlockFrame R.params.side n).Cell × Fin 4) :
    LumpContours.contourMean R.params.baseDepth
        (StepCosts.stepHotLumps R.params (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g) W))
        (fun y => BlockAverages.cellCentre 0 y)
        (TorusFields.readAtLevel (TorusLumps.stepBlockFrame R.params.side n) 0
          (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g) W)) c =
      ((g (TorusLumps.toTorusSite n c.1) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) *
        LumpContours.contourMean R.params.baseDepth (StepCosts.stepHotLumps R.params W)
          (fun y => BlockAverages.cellCentre 0 y)
          (TorusFields.readAtLevel (TorusLumps.stepBlockFrame R.params.side n) 0 W) c *
        (((g (TorusLumps.toTorusSite n (c.1 + BlockAverages.unitStep (TorusLumps.stepBlockFrame R.params.side n).top c.2)))⁻¹ :
          BlockAverages.UnitQuaternion) : ℍ[ℝ]) := by
  rw [stepHotLumps_gaugeTransform,
    SettingFits.readAtLevel_gaugeTransform (fun i => TorusContours.stepBlockFrame_period_zero i)]
  have h := TorusContours.contourMean_gaugeTransform (F := TorusLumps.stepBlockFrame R.params.side n)
    R.params.baseDepth (StepCosts.stepHotLumps R.params W)
    (fun y => TorusLumps.blockConstantGauge R.params.side g (TorusLumps.toTorusSite (n * R.params.side) y))
    (fun y => BlockAverages.cellCentre 0 y)
    (TorusFields.readAtLevel (TorusLumps.stepBlockFrame R.params.side n) 0 W) c
  refine h.trans ?_
  have e : ∀ y : (TorusLumps.stepBlockFrame R.params.side n).Cell,
      TorusLumps.blockConstantGauge R.params.side g
          (TorusLumps.toTorusSite (n * R.params.side)
            (BlockAverages.cellCentre (F := TorusLumps.stepBlockFrame R.params.side n) 0 y)) =
        g (TorusLumps.toTorusSite n y) :=
    fun y => congrArg g (parentBlock_cellCentre hodd y)
  exact congrArg₂ (fun a b : BlockAverages.UnitQuaternion => (a : ℍ[ℝ]) *
    LumpContours.contourMean R.params.baseDepth (StepCosts.stepHotLumps R.params W)
      (fun y => BlockAverages.cellCentre 0 y)
      (TorusFields.readAtLevel (TorusLumps.stepBlockFrame R.params.side n) 0 W) c *
      ((b⁻¹ : BlockAverages.UnitQuaternion) : ℍ[ℝ]))
    (e c.1) (e (c.1 + BlockAverages.unitStep (TorusLumps.stepBlockFrame R.params.side n).top c.2))
private theorem bondFit_gaugeTransform (hodd : Odd R.params.side)
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (W : TorusFields.TorusField (n * R.params.side))
    (V : TorusFields.TorusField n) (c : TorusFields.TorusBond n) :
    StepCosts.bondFit R.params (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g) W)
        (TorusFields.gaugeTransform g V) (fun y => BlockAverages.cellCentre 0 y) c =
      StepCosts.bondFit R.params W V (fun y => BlockAverages.cellCentre 0 y) c := by
  unfold StepCosts.bondFit LumpContours.contourFit
  rw [contourMean_blockGauge hodd,
    SettingFits.readAtLevel_gaugeTransform (j := 1) (fun i => TorusContours.stepBlockFrame_period_one i) g V]
  exact fit_conj _ _ _ _
private theorem meanNorm_gaugeTransform (hodd : Odd R.params.side)
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (W : TorusFields.TorusField (n * R.params.side))
    (c : TorusFields.TorusBond n) :
    StepCosts.meanNorm R.params (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g) W)
        (fun y => BlockAverages.cellCentre 0 y) c =
      StepCosts.meanNorm R.params W (fun y => BlockAverages.cellCentre 0 y) c := by
  unfold StepCosts.meanNorm
  rw [contourMean_blockGauge hodd, norm_mul, norm_mul, TorusContours.norm_coe_unitQuaternion,
    TorusContours.norm_coe_unitQuaternion, one_mul, mul_one]
section Core
variable {δ lam σA cg : ℝ} {N : ℕ → ℝ}
private theorem norm_frame_le
    (hch : ColdChain.ColdChainConstants R.params.coupling δ R.params.side lam R.anchorRadius σA cg N)
    (hodd : Odd R.params.side) (h64 : 64 ≤ n)
    {s : ℝ} (hs : 0 < s) (hsA : s ≤ σA) {V : TorusFields.TorusField n} (hV : TorusFields.IsCold s V)
    (hbig : ¬ 4 * R.frameReach + 5 < n)
    (b : TorusFields.TorusBond (n * R.params.side)) :
    ‖(((StepSettings.coldChartSetting R V).frame b : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ ≤ N 0 * s := by
  obtain ⟨hδ, hδ8, hlam, hρ, hρ1, hσ, hcg, hN, hch'⟩ := hch
  have hside : ∀ i, (TorusFields.torusFrame R.params.side R.depth n).extent i = n := fun _ => rfl
  have hs0 : ∀ i, 0 < (TorusFields.torusFrame R.params.side R.depth n).extent i := fun i => by rw [hside]; omega
  have hs2 : ∀ i, 2 ≤ (TorusFields.torusFrame R.params.side R.depth n).extent i := fun i => by rw [hside]; omega
  have hreg : BlockAverages.IsOrthantRegular
      (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame R.params.side R.depth n)) 1024 :=
    TopLevelSites.isOrthantRegular_finiteCells hs0 1024
  have hcold : BlockAverages.IsCold (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame R.params.side R.depth n))
      (TorusFields.torusFrame R.params.side R.depth n).top s
      (TorusFields.readAtLevel (TorusFields.torusFrame R.params.side R.depth n)
        (TorusFields.torusFrame R.params.side R.depth n).top V) :=
    TopLevelSites.isCold_readAtLevel hside hV
  obtain ⟨H1, -⟩ := hch' (TorusFields.torusFrame R.params.side R.depth n) 1024 _ rfl (Or.inr fun _ => h64) le_rfl hreg
    s _ hs hsA hcold
  have hπ : R.anchorRadius < Real.pi := lt_of_le_of_lt hρ1 (lt_trans (by norm_num) Real.pi_gt_three)
  obtain ⟨w, hw, -, hlc⟩ := TopLevelSites.minimizingCoordinates_eq (ρ := R.anchorRadius) hodd hs2 hπ le_rfl H1
  have hfr : (StepSettings.coldChartSetting R V).frame b =
      w (StepCosts.torusSiteInFrame (TorusFields.torusFrame R.params.side R.depth n)
        (TorusFields.torusFrame R.params.side R.depth n).depth b.1) b.2 := by
    show StepCosts.frameCoord R.params R.anchorRadius R.depth R.frameReach V b = _
    unfold StepCosts.frameCoord ColdStepAtMirrorFrames.bondFrameCoord
    rw [if_neg (fun h => hbig (h 0))]
    unfold BlockAverages.minimizingBondCoordinate
    simp only
    rw [hlc]
  rw [hfr]
  have hNs : 0 ≤ N 0 * s := mul_nonneg (hN 0).le hs.le
  by_cases hc : (StepCosts.torusSiteInFrame (TorusFields.torusFrame R.params.side R.depth n)
      (TorusFields.torusFrame R.params.side R.depth n).depth b.1, b.2) ∈
      BlockAverages.chordBonds (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame R.params.side R.depth n))
  · exact (hw.2.1 _ hc).trans (min_le_right _ _)
  · have := hw.1 _ hc
    simp only at this
    rw [this]
    simpa using hNs
private theorem isRegularRegion_univ {m : ℕ} [NeZero m] (k : ℕ) :
    LevelAction.IsRegularRegion (Finset.univ : Finset (TorusFields.TorusSite m)) k :=
  fun _ => ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => Finset.mem_univ _⟩
private theorem isColdOn_univ {m : ℕ} [NeZero m] {s : ℝ} {W : TorusFields.TorusField m} (h : TorusFields.IsCold s W) :
    LevelAction.IsColdOn s (Finset.univ : Finset (TorusFields.TorusSite m)) W := fun p hp =>
  h _ _ _ (Finset.mem_filter.mp hp).2.1
private theorem actionAtLevel_univ_gaugeTransform (hS : StepCosts.SharesSumToAction) (ha : 0 < R.params.coupling)
    (hodd : Odd R.params.side)
    (hch : ColdChain.ColdChainConstants R.params.coupling δ R.params.side lam R.anchorRadius σA cg N) (t : ℕ)
    {m : ℕ} [NeZero m] (hm : 64 ≤ m) {W : TorusFields.TorusField m}
    (hW : TorusFields.IsCold σA W) (g : TorusFields.TorusSite m → BlockAverages.UnitQuaternion) :
    TorusFields.actionAtLevel R.params.coupling R.params.side t Finset.univ (TorusFields.gaugeTransform g W) =
      TorusFields.actionAtLevel R.params.coupling R.params.side t Finset.univ W :=
  StepCostLocality.actionAtLevel_gaugeTransform hS ha hodd hch t hm (isRegularRegion_univ 1024) (isColdOn_univ hW) g
private theorem sum_blockCost_gaugeTransform (hS : StepCosts.SharesSumToAction) (hfit : R.params.Admissible)
    (ha : 0 < R.params.coupling)
    (hch : ColdChain.ColdChainConstants R.params.coupling δ R.params.side lam R.anchorRadius σA cg N)
    (hσ : R.params.threshold ≤ σA) (h64 : 64 ≤ n)
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (V : TorusFields.TorusField n)
    {W : TorusFields.TorusField (n * R.params.side)} (hW : TorusFields.IsCold R.params.threshold W)
    (hW' : TorusFields.IsCold R.params.threshold
      (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g) W)) :
    ∑ Y, StepCosts.blockCost R.params R.depth
        (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g) W)
        (TorusFields.gaugeTransform g V) (fun y => BlockAverages.cellCentre 0 y) Y =
      ∑ Y, StepCosts.blockCost R.params R.depth W V (fun y => BlockAverages.cellCentre 0 y) Y := by
  have hodd := hfit.L_odd
  have hLp : 0 < R.params.side := hodd.pos
  have hm : 64 ≤ n * R.params.side := h64.trans (Nat.le_mul_of_pos_right _ hLp)
  have hm2 : 2 ≤ n * R.params.side := by omega
  have hsplit : ∀ (W₁ : TorusFields.TorusField (n * R.params.side)) (V₁ : TorusFields.TorusField n),
      TorusLumps.torusHotSites R.params W₁ = ∅ →
      ∑ Y, StepCosts.blockCost R.params R.depth W₁ V₁ (fun y => BlockAverages.cellCentre 0 y) Y =
        TorusFields.actionAtLevel R.params.coupling R.params.side R.depth Finset.univ W₁ +
        ∑ Y, R.params.coupling / 2 * ∑ i : Fin 4,
          (StepCosts.bondFit R.params W₁ V₁ (fun y => BlockAverages.cellCentre 0 y) (Y, i) +
          StepCosts.bondFit R.params W₁ V₁ (fun y => BlockAverages.cellCentre 0 y) (Y - TorusFields.unitStep n i, i)) := by
    intro W₁ V₁ h
    have e : ∀ Y, StepCosts.blockCost R.params R.depth W₁ V₁ (fun y => BlockAverages.cellCentre 0 y) Y =
        ∑ y ∈ TorusLumps.sitesInBlocks R.params.side {Y},
            StepCosts.levelShare R.params.coupling R.params.side R.depth Finset.univ y W₁ +
          R.params.coupling / 2 * ∑ i : Fin 4,
            (StepCosts.bondFit R.params W₁ V₁ (fun y => BlockAverages.cellCentre 0 y) (Y, i) +
            StepCosts.bondFit R.params W₁ V₁ (fun y => BlockAverages.cellCentre 0 y)
              (Y - TorusFields.unitStep n i, i)) := by
      intro Y
      unfold StepCosts.blockCost
      rw [h, thickening_empty, Finset.sdiff_empty]
    rw [Finset.sum_congr rfl fun Y _ => e Y, Finset.sum_add_distrib, FreeBonds.sum_sitesInBlocks_singleton,
      FreeBonds.sum_levelShare hS ha.le hLp hm2]
  rw [hsplit _ _ (torusHotSites_eq_empty hfit hW'), hsplit _ _ (torusHotSites_eq_empty hfit hW),
    actionAtLevel_univ_gaugeTransform hS ha hodd hch _ hm (fun x μ ν h => (hW x μ ν h).trans_le hσ)]
  simp only [bondFit_gaugeTransform hodd]
private theorem blockDensity_gaugeTransform (hrow : R.HasExpansions) (hfit : R.params.Admissible)
    (hn : R.params.n₀ ≤ n) (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (V : TorusFields.TorusField n)
    {W : TorusFields.TorusField (n * R.params.side)} (hW : TorusFields.IsCold R.params.threshold W)
    (hW' : TorusFields.IsCold R.params.threshold
      (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g) W)) (Y : TorusFields.TorusSite n) :
    (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).blockDensity
        (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g) W) Y =
      (StepSettings.coldChartSetting R V).blockDensity W Y := by
  have hLp : 0 < R.params.side := hfit.L_odd.pos
  have hbs : TorusLumps.IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨dvd_mul_left _ _, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hn' : R.params.n₀ ≤ n * R.params.side := hn.trans (Nat.le_mul_of_pos_right _ hLp)
  have key : ∀ U : TorusFields.TorusField (n * R.params.side), TorusFields.IsCold R.params.threshold U →
      ∀ (ω : (∅ : Finset (TorusFields.TorusSite (n * R.params.side))) → R.labels.Ω)
      (y : TorusFields.TorusSite (n * R.params.side)),
        R.siteDensity (n * R.params.side) y U ∅ ω = TorusLumps.centered R.density (n * R.params.side) y U :=
    fun U hU ω y => hrow.2.empty _ hbs U ω y (isHullState_empty hfit hU _)
  unfold StepSettings.ChartSetting.blockDensity
  refine Finset.sum_congr rfl fun y _ => ?_
  refine (key _ hW' _ y).trans (Eq.trans ?_ (key _ hW _ y).symm)
  unfold TorusLumps.centered
  rw [hrow.1.gauge _ hn' y _ W hW]
private theorem logJacobian_gaugeTransform (hodd : Odd R.params.side)
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (V : TorusFields.TorusField n)
    (W : TorusFields.TorusField (n * R.params.side))
    (η η' : StepSettings.FreeCoords (StepCosts.chartBonds R.params.side n))
    (h : ∀ b : ↥(StepCosts.chartBonds R.params.side n),
      (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).frame b.1 +
          ColdStepAtMirrorFrames.toImaginary (η' b) =
        ColdStepAtMirrorFrames.adjointAction (g (TorusLumps.parentBlock R.params.side b.1.1))
          ((StepSettings.coldChartSetting R V).frame b.1 + ColdStepAtMirrorFrames.toImaginary (η b)))
    (Y : TorusFields.TorusSite n) :
    (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).logJacobian
        (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g) W) η' Y =
      (StepSettings.coldChartSetting R V).logJacobian W η Y := by
  unfold StepSettings.ChartSetting.logJacobian
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) (Finset.sum_congr rfl fun b _ => ?_)
  · exact congrArg (fun u => TorusLumps.logPartitionGap (R.params.coupling * R.coupling * u))
      (meanNorm_gaugeTransform hodd g W (Y, i))
  · have e := haarLogDensity_adjoint _ (h b)
    show (if StepSettings.bondBlock (R := R) b.1 = Y then Real.log (ColdStepAtMirrorFrames.haarLogDensity
        (StepSettings.toCoords ((StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).frame b.1) + η' b))
        else 0) =
      if StepSettings.bondBlock (R := R) b.1 = Y then Real.log (ColdStepAtMirrorFrames.haarLogDensity
        (StepSettings.toCoords ((StepSettings.coldChartSetting R V).frame b.1) + η b)) else 0
    rw [e]
private theorem potential_gaugeTransform (hS : StepCosts.SharesSumToAction) (hrow : R.HasExpansions)
    (hfit : R.params.Admissible) (ha : 0 < R.params.coupling)
    (hch : ColdChain.ColdChainConstants R.params.coupling δ R.params.side lam R.anchorRadius σA cg N)
    (hσ : R.params.threshold ≤ σA) (hn : R.params.n₀ ≤ n)
    (h64 : 64 ≤ n) (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (V : TorusFields.TorusField n)
    (η η' : StepSettings.FreeCoords (StepCosts.chartBonds R.params.side n))
    (h : ∀ b : ↥(StepCosts.chartBonds R.params.side n),
      (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).frame b.1 +
          ColdStepAtMirrorFrames.toImaginary (η' b) =
        ColdStepAtMirrorFrames.adjointAction (g (TorusLumps.parentBlock R.params.side b.1.1))
          ((StepSettings.coldChartSetting R V).frame b.1 + ColdStepAtMirrorFrames.toImaginary (η b)))
    (hW : TorusFields.IsCold R.params.threshold ((StepSettings.coldChartSetting R V).field η)) :
    (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).potential η' =
      (StepSettings.coldChartSetting R V).potential η := by
  have hodd := hfit.L_odd
  have h2 : 2 ≤ n := by omega
  have hfield := field_adjoint_eq_gaugeTransform hodd h2 g V η η' h
  have hW' : TorusFields.IsCold R.params.threshold
      (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g)
        ((StepSettings.coldChartSetting R V).field η)) := by
    intro x μ ν hlt
    rw [TorusFields.curvature_gaugeTransform]
    exact hW x μ ν hlt
  unfold StepSettings.ChartSetting.potential
  rw [hfield]
  exact sum_affine_congr R.coupling
    (fun Y => StepCosts.blockCost R.params R.depth
      (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g)
        ((StepSettings.coldChartSetting R V).field η)) (TorusFields.gaugeTransform g V)
      (fun y => BlockAverages.cellCentre 0 y) Y)
    (fun Y => StepCosts.blockCost R.params R.depth ((StepSettings.coldChartSetting R V).field η) V
      (fun y => BlockAverages.cellCentre 0 y) Y)
    (fun Y => (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).blockDensity
      (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g)
        ((StepSettings.coldChartSetting R V).field η)) Y)
    (fun Y => (StepSettings.coldChartSetting R V).blockDensity ((StepSettings.coldChartSetting R V).field η) Y)
    (fun Y => (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).logJacobian
      (TorusFields.gaugeTransform (TorusLumps.blockConstantGauge R.params.side g)
        ((StepSettings.coldChartSetting R V).field η)) η' Y)
    (fun Y => (StepSettings.coldChartSetting R V).logJacobian ((StepSettings.coldChartSetting R V).field η) η Y)
    (sum_blockCost_gaugeTransform hS hfit ha hch hσ h64 g V hW hW')
    (blockDensity_gaugeTransform hrow hfit hn g V hW hW') (logJacobian_gaugeTransform hodd g V _ η η' h)
private theorem coldImageIntegral_gaugeTransform (hS : StepCosts.SharesSumToAction)
    (hAd : ColdStepAtMirrorFrames.AdjointActionLinearIsometry)
    (hrow : R.HasExpansions) (hfit : R.params.Admissible) (ha : 0 < R.params.coupling)
    (hch : ColdChain.ColdChainConstants R.params.coupling δ R.params.side lam R.anchorRadius σA cg N)
    (hσ : R.params.threshold ≤ σA) (hn : R.params.n₀ ≤ n) (h64 : 64 ≤ n)
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion) (V : TorusFields.TorusField n)
    (hfr : ∀ b ∈ StepCosts.chartBonds R.params.side n,
      (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).frame b =
        ColdStepAtMirrorFrames.adjointAction (g (TorusLumps.parentBlock R.params.side b.1))
          ((StepSettings.coldChartSetting R V).frame b))
    (hcold : ∀ η : StepSettings.FreeCoords (StepCosts.chartBonds R.params.side n), (∀ b, ‖η b‖ < R.ballRadius) →
      TorusFields.IsCold R.params.threshold ((StepSettings.coldChartSetting R V).field η)) :
    StepSettings.coldImageIntegral R (TorusFields.gaugeTransform g V) = StepSettings.coldImageIntegral R V := by
  classical
  choose A hA using fun Y : TorusFields.TorusSite n => hAd (g Y)
  let T : StepSettings.FreeCoords (StepCosts.chartBonds R.params.side n) →
      StepSettings.FreeCoords (StepCosts.chartBonds R.params.side n) :=
    fun η b => A (TorusLumps.parentBlock R.params.side b.1.1) (η b)
  have hmp : MeasurePreserving T volume volume := by
    have h := measurePreserving_pi
      (fun _ : ↥(StepCosts.chartBonds R.params.side n) => (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (fun _ : ↥(StepCosts.chartBonds R.params.side n) => (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (fun b => (A (TorusLumps.parentBlock R.params.side b.1.1)).measurePreserving)
    simpa only [volume_pi] using h
  have hemb : MeasurableEmbedding T :=
    (Homeomorph.piCongrRight fun b : ↥(StepCosts.chartBonds R.params.side n) =>
      (A (TorusLumps.parentBlock R.params.side b.1.1)).toHomeomorph).measurableEmbedding
  have hturn : ∀ (η : StepSettings.FreeCoords (StepCosts.chartBonds R.params.side n))
      (b : ↥(StepCosts.chartBonds R.params.side n)),
      (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).frame b.1 +
          ColdStepAtMirrorFrames.toImaginary (T η b) =
        ColdStepAtMirrorFrames.adjointAction (g (TorusLumps.parentBlock R.params.side b.1.1))
          ((StepSettings.coldChartSetting R V).frame b.1 + ColdStepAtMirrorFrames.toImaginary (η b)) := by
    intro η b
    show _ + ColdStepAtMirrorFrames.toImaginary (A _ (η b)) = _
    rw [hfr b.1 b.2, hA, adjointAction_add_eq]
  have hnorm : ∀ (Y : TorusFields.TorusSite n) (v : EuclideanSpace ℝ (Fin 3)),
      StepSettings.coordNorm (A Y v) = StepSettings.coordNorm v := by
    intro Y v
    rw [SettingShifts.coordNorm_eq_norm, SettingShifts.coordNorm_eq_norm]
    exact (A Y).norm_map v
  have hcuts : ∀ η : StepSettings.FreeCoords (StepCosts.chartBonds R.params.side n),
      (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).cutoffProduct (T η) =
        (StepSettings.coldChartSetting R V).cutoffProduct η := by
    intro η
    exact Finset.prod_congr rfl fun b _ =>
      congrArg (ColdStepAtMirrorFrames.cutoffFactor R.ballRadius R.barrierFn) (hnorm _ (η b))
  have hpt : ∀ η : StepSettings.FreeCoords (StepCosts.chartBonds R.params.side n),
      (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).cutoffProduct (T η) *
          Real.exp (-(StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).potential (T η)) =
        (StepSettings.coldChartSetting R V).cutoffProduct η *
          Real.exp (-(StepSettings.coldChartSetting R V).potential η) := by
    intro η
    rw [hcuts]
    by_cases hη : ∀ b, ‖η b‖ < R.ballRadius
    · rw [potential_gaugeTransform hS hrow hfit ha hch hσ hn h64 g V η (T η) (hturn η) (hcold η hη)]
    · push Not at hη
      obtain ⟨b, hb⟩ := hη
      have h0 : (StepSettings.coldChartSetting R V).cutoffProduct η = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
        unfold ColdStepAtMirrorFrames.cutoffFactor
        rw [if_neg]
        rw [SettingShifts.coordNorm_eq_norm]
        exact not_lt.mpr hb
      rw [h0, zero_mul, zero_mul]
  unfold StepSettings.coldImageIntegral
  refine congrArg (fun u => R.functional (n * R.params.side) (TorusFields.trivialField _) * u) ?_
  exact (hmp.integral_comp hemb (fun η =>
    (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).cutoffProduct η *
      Real.exp (-(StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).potential η))).symm.trans
    (integral_congr_ae (Filter.Eventually.of_forall hpt))
end Core
end GaugeInvariance
open GaugeInvariance in
theorem LaplaceRemainderIsGaugeFunctionNear.holds (hFr : StepFrames.FrameCovariance)
    (hS : StepCosts.SharesSumToAction) (hAd : ColdStepAtMirrorFrames.AdjointActionLinearIsometry) :
    LaplaceRemainderIsGaugeFunctionNear := by
  intro T hT y R hy hR n _ hn hside
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y hy
  have hodd := hfit.L_odd
  have hrow : R.HasExpansions := hR.isStep.1
  have e_a : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have e_L : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have e_σ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have e_n : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hch : ColdChain.ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [e_a, e_L, hR.anchorRadius_eq]
    exact hT.chain
  have ha : 0 < R.params.coupling := by
    rw [e_a]
    linarith [hT.a_ge]
  have hσ0 : 0 < R.params.threshold := hfit.σ_pos
  have hσ2 : 2 * R.params.threshold ≤ T.σA := by
    rw [e_σ]
    exact hT.σ_le
  have hσ1 : R.params.threshold ≤ T.σA := by linarith
  have hn₀ : R.params.n₀ ≤ n := by
    rw [e_n]
    exact hn
  have h64 : 64 ≤ n := by
    have := hT.n₀_ge
    omega
  have hbig : ¬ 4 * R.frameReach + 5 < n := by omega
  have hrf : StepMarks.RangesAdmissible R.range R.range := by
    have h1 : (1 : ℝ) ≤ y := (hT.fits y hy).y₁_ge
    have h2 : TorusLumps.clusterRange y ≤ TorusLumps.clusterRange R.coupling :=
      Nat.ceil_mono (Real.rpow_le_rpow (by linarith) hR.le_coupling (by norm_num))
    have h3 : 2 ^ 16 ≤ TorusLumps.clusterRange y := (hT.fits y hy).range_ge
    have h4 : 2 ^ 16 ≤ R.range := h3.trans h2
    refine ⟨Nat.le_succ _, h4, ?_⟩
    omega
  have hN0 : 0 < T.N 0 := hch.2.2.2.2.2.2.2.1 0
  set ρ : ℝ := R.ballRadius with hρdef
  have hρ : 0 < ρ := by
    show 0 < R.params.threshold / 64
    positivity
  set s : ℝ := ρ / (T.N 0 + 1) with hsdef
  have hs : 0 < s := by positivity
  have hsρ : s ≤ ρ := div_le_self hρ.le (by linarith)
  have hNs : T.N 0 * s ≤ ρ := by
    rw [hsdef, ← mul_div_assoc, div_le_iff₀ (by linarith)]
    nlinarith
  have hρσ : ρ = R.params.threshold / 64 := rfl
  have hsA : s ≤ T.σA := by linarith
  have hV : ∀ᶠ V : TorusFields.TorusField n in 𝓝 (TorusFields.trivialField n),
      ∀ x i, ‖(V x i : ℍ[ℝ]) - 1‖ < s / 8 := by
    refine Filter.eventually_all.mpr fun x => Filter.eventually_all.mpr fun i => ?_
    have hc : Continuous fun V : TorusFields.TorusField n => ‖(V x i : ℍ[ℝ]) - 1‖ :=
      ((continuous_subtype_val.comp ((continuous_apply i).comp (continuous_apply x))).sub continuous_const).norm
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    simpa [TorusFields.trivialField] using (by positivity : 0 < s / 8)
  have hq := (continuous_snd.tendsto
    ((1 : TorusFields.TorusSite n → BlockAverages.UnitQuaternion), TorusFields.trivialField n)).eventually hV
  filter_upwards [hq] with q hq
  obtain ⟨g, V⟩ := q
  simp only at hq ⊢
  have hVc : TorusFields.IsCold s V := by
    intro x μ ν _
    have h1 := curvature_le_four_mul V (e := s / 8) (fun x i => (hq x i).le) x μ ν
    linarith
  have hV98 : TorusFields.IsCold (9 / 8 * R.params.threshold) V := fun x μ ν h => by
    have := hVc x μ ν h
    linarith
  have hVA : TorusFields.IsCold T.σA V := fun x μ ν h => by
    have := hVc x μ ν h
    linarith
  have hsit : StepMarks.IsStepSituation R.params R.range V Finset.univ ∅ (9 / 8 * R.params.threshold) :=
    Or.inr ⟨hn₀, hV98, rfl, rfl, rfl⟩
  have hfr : ∀ b ∈ StepCosts.chartBonds R.params.side n,
      (StepSettings.coldChartSetting R (TorusFields.gaugeTransform g V)).frame b =
        ColdStepAtMirrorFrames.adjointAction (g (TorusLumps.parentBlock R.params.side b.1))
          ((StepSettings.coldChartSetting R V).frame b) := fun b hb =>
    Subtype.ext ((hFr R.params T.δ₁ T.lam R.anchorRadius T.σA T.cg T.N hfit hch hσ2 R.depth R.range R.range n V
      Finset.univ ∅ _ hrf hsit b hb (Finset.notMem_empty _)).1 g)
  have hcold : ∀ η : StepSettings.FreeCoords (StepCosts.chartBonds R.params.side n), (∀ b, ‖η b‖ < R.ballRadius) →
      TorusFields.IsCold R.params.threshold ((StepSettings.coldChartSetting R V).field η) := by
    intro η hη x μ ν _
    have hb := norm_field_sub_one_le (R := R) (V := V) hρ.le (fun x i => by
      have := hq x i
      linarith) (fun b => (norm_frame_le hch hodd h64 hs hsA hVc hbig b).trans hNs) η
      (fun b => (hη b).le)
    have h1 := curvature_le_four_mul _ hb x μ ν
    linarith
  have himage := coldImageIntegral_gaugeTransform hS hAd hrow hfit ha hch hσ1 hn₀ h64 g V hfr hcold
  have haction := actionAtLevel_univ_gaugeTransform hS ha hodd hch (R.depth + 1) h64 hVA g
  have hne : n ≠ 0 := NeZero.ne n
  unfold laplaceRemainder goodFieldLogIntegral minimalActionTotal
  simp only [dif_neg hne]
  rw [himage, haction]
end YangMills.Construction.RunningCouplingSlope
end
