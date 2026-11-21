import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsInvariantAtParametersProof
import YangMills.Construction.RunningCouplingSlope.LeastChartEnergyIsAnalyticNearTheFlatField
import YangMills.Construction.RunningCouplingSlope.TotalAtTheLeastFieldProof
import YangMills.Construction.RunningCouplingSlope.TotalOfAStepIsGaugeInvariant
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace SlopeCoefficient
section Derivatives
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem secondDerivAlong_comp_equiv (R : BondField ι ≃L[ℝ] BondField ι) (f : BondField ι → ℝ)
    (u v : BondField ι) :
    ColdStepAtMirrorFrames.secondDerivAlong (fun η => f (R η)) 0 u v =
      ColdStepAtMirrorFrames.secondDerivAlong f 0 (R u) (R v) := by apply _root_.YangMills.SharedProofs.p72470 <;> assumption
private theorem secondDerivAlong_eq_fderiv_fderiv {f : BondField ι → ℝ} (hf : AnalyticAt ℝ f 0)
    (u v : BondField ι) :
    ColdStepAtMirrorFrames.secondDerivAlong f 0 u v = fderiv ℝ (fderiv ℝ f) 0 v u := by apply _root_.YangMills.SharedProofs.p53373 <;> assumption
private def coordVector (k : ι × Fin 3) : BondField ι := bondVariation k.1 (EuclideanSpace.single k.2 1)
private theorem coordVector_apply (k : ι × Fin 3) (b : ι) (α : Fin 3) :
    coordVector k b α = if k = (b, α) then 1 else 0 := by apply _root_.YangMills.DeltaSharedProofs.p501987 <;> assumption
private theorem eq_sum_coordVector (u : BondField ι) : u = ∑ k : ι × Fin 3, u k.1 k.2 • coordVector k := by apply _root_.YangMills.DeltaSharedProofs.p501785 <;> assumption
private def bondwiseIsometry (T : ι → BondVector ≃ₗᵢ[ℝ] BondVector) : BondField ι ≃L[ℝ] BondField ι :=
  (LinearEquiv.piCongrRight fun b => (T b).toLinearEquiv).toContinuousLinearEquiv
private theorem bondwiseIsometry_apply (T : ι → BondVector ≃ₗᵢ[ℝ] BondVector) (η : BondField ι) (b : ι) :
    bondwiseIsometry T η b = T b (η b) := rfl
private def bondwiseMatrix (T : ι → BondVector ≃ₗᵢ[ℝ] BondVector) : Matrix (ι × Fin 3) (ι × Fin 3) ℝ :=
  fun k i => bondwiseIsometry T (coordVector i) k.1 k.2
private theorem transpose_mul_bondwiseMatrix (T : ι → BondVector ≃ₗᵢ[ℝ] BondVector) :
    (bondwiseMatrix T).transpose * bondwiseMatrix T = 1 := by
  have key : ∀ (b : ι) (x y : BondVector), ∑ α, T b x α * T b y α = ∑ α, x α * y α := fun b x y => by
    have h := (T b).inner_map_map x y
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h
    simpa [mul_comm] using h
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, bondwiseMatrix]
  rw [Fintype.sum_prod_type]
  simp only [bondwiseIsometry_apply, key]
  rw [← Fintype.sum_prod_type (f := fun k : ι × Fin 3 => coordVector i k.1 k.2 * coordVector j k.1 k.2)]
  simp only [coordVector_apply, Prod.mk.eta, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]
private theorem hessian_bondwiseIsometry (T : ι → BondVector ≃ₗᵢ[ℝ] BondVector) {f : BondField ι → ℝ}
    (hf : AnalyticAt ℝ f 0) (H' : Matrix (ι × Fin 3) (ι × Fin 3) ℝ)
    (hH' : ∀ i j, H' i j = ColdStepAtMirrorFrames.secondDerivAlong (fun η => f (bondwiseIsometry T η)) 0
      (coordVector i) (coordVector j)) :
    H' = (bondwiseMatrix T).transpose *
      (Matrix.of fun i j => ColdStepAtMirrorFrames.secondDerivAlong f 0 (coordVector i) (coordVector j)) *
        bondwiseMatrix T := by
  ext i j
  have ei := eq_sum_coordVector (bondwiseIsometry T (coordVector i))
  have ej := eq_sum_coordVector (bondwiseIsometry T (coordVector j))
  rw [hH', secondDerivAlong_comp_equiv, secondDerivAlong_eq_fderiv_fderiv hf]
  rw [ei, ej]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, secondDerivAlong_eq_fderiv_fderiv hf,
    bondwiseMatrix, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring
end Derivatives
section Rotations
private theorem norm_toImaginary (v : BondVector) : ‖(toImaginary v : imaginaryQuaternions)‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.norm_toImaginary <;> assumption
private def imaginaryCoords (q : imaginaryQuaternions) : BondVector :=
  !₂[(q : ℍ[ℝ]).imI, (q : ℍ[ℝ]).imJ, (q : ℍ[ℝ]).imK]
private theorem toImaginary_imaginaryCoords (q : imaginaryQuaternions) : toImaginary (imaginaryCoords q) = q := by
  apply Subtype.ext
  have hq : (q : ℍ[ℝ]).re = 0 := q.2
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
  · simpa [toImaginary] using hq.symm
  all_goals simp [toImaginary, imaginaryCoords]
private theorem imaginaryCoords_toImaginary (v : BondVector) : imaginaryCoords (toImaginary v) = v := by
  ext α
  fin_cases α <;> simp [imaginaryCoords, toImaginary]
private def imaginaryEquiv : BondVector ≃ₗ[ℝ] imaginaryQuaternions where
  toFun := toImaginary
  invFun := imaginaryCoords
  map_add' u v := map_add BondCoordinates.toImaginaryCLM u v
  map_smul' r v := map_smul BondCoordinates.toImaginaryCLM r v
  left_inv := imaginaryCoords_toImaginary
  right_inv := toImaginary_imaginaryCoords
private theorem adjointMap_adjointMap_inv (g : UnitQuaternion) (v : imaginaryQuaternions) :
    adjointMap g (adjointMap g⁻¹ v) = v := by apply _root_.YangMills.SharedProofs.p92515 <;> assumption
private theorem norm_adjointMap (g : UnitQuaternion) (v : imaginaryQuaternions) : ‖adjointMap g v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.MinimalChart.norm_adjointMap <;> assumption
private def adjointEquiv (g : UnitQuaternion) : imaginaryQuaternions ≃ₗ[ℝ] imaginaryQuaternions where
  toLinearMap := adjointMap g
  invFun := adjointMap g⁻¹
  left_inv v := by
    have h := adjointMap_adjointMap_inv g⁻¹ v
    rwa [inv_inv] at h
  right_inv v := adjointMap_adjointMap_inv g v
private def adjointIsometry (g : UnitQuaternion) : BondVector ≃ₗᵢ[ℝ] BondVector where
  toLinearEquiv := (imaginaryEquiv.trans (adjointEquiv g)).trans imaginaryEquiv.symm
  norm_map' v := by
    show ‖imaginaryCoords (adjointMap g (toImaginary v))‖ = ‖v‖
    rw [← norm_toImaginary, toImaginary_imaginaryCoords, norm_adjointMap, norm_toImaginary]
private theorem toImaginary_adjointIsometry (g : UnitQuaternion) (v : BondVector) :
    toImaginary (adjointIsometry g v) = adjointMap g (toImaginary v) :=
  toImaginary_imaginaryCoords _
end Rotations
section OnFrames
variable {F : BlockFrame} {a ρ : ℝ}
private theorem coordsAboveFrame_apply (V : F.GaugeField F.top) (η : StepVariable (finiteCells F))
    (x : F.Site F.depth) (i : Fin 4) :
    coordsAboveFrame true a ρ 0 V η x i = minimizingCoordinates a (finiteCells F) V ρ x i + stepCoordinates η x i := by
  simp [coordsAboveFrame, ColdStepAtMirrorFrames.stepFrame, minimizingBondCoordinate]
section Gauge
variable {γ : F.Cell → UnitQuaternion} {V : F.GaugeField F.top}
private def gaugeRotation (γ : F.Cell → UnitQuaternion) (b : ↥(chordBonds (finiteCells F))) :
    BondVector ≃ₗᵢ[ℝ] BondVector :=
  adjointIsometry (γ (enclosingCell b.1.1))⁻¹
private theorem stepCoordinates_gaugeRotation (η : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (bondwiseIsometry (gaugeRotation γ) η) x i =
      adjointMap (γ (enclosingCell x))⁻¹ (stepCoordinates η x i) := by
  unfold stepCoordinates
  split_ifs with h
  · exact toImaginary_adjointIsometry _ _
  · simp
private theorem coordsAboveFrame_gaugeTransform
    (hw : minimizingCoordinates a (finiteCells F) (BlockAverages.gaugeTransform γ V) ρ =
      fun x i => adjointMap (γ (enclosingCell x)) (minimizingCoordinates a (finiteCells F) V ρ x i))
    (η : StepVariable (finiteCells F)) :
    coordsAboveFrame true a ρ 0 (BlockAverages.gaugeTransform γ V) η =
      fun x i => ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell x))
        (coordsAboveFrame true a ρ 0 V (bondwiseIsometry (gaugeRotation γ) η) x i) := by
  funext x i
  rw [coordsAboveFrame_apply, coordsAboveFrame_apply, hw, stepCoordinates_gaugeRotation]
  have e : ∀ (g : UnitQuaternion) (X : imaginaryQuaternions),
      ColdStepAtMirrorFrames.adjointAction g X = adjointMap g X := fun _ _ => rfl
  rw [e, map_add, adjointMap_adjointMap_inv]
private theorem chartedEnergyAtMinimizer_gaugeTransform (hM : ChartEquivariance F a)
    (hw : minimizingCoordinates a (finiteCells F) (BlockAverages.gaugeTransform γ V) ρ =
      fun x i => adjointMap (γ (enclosingCell x)) (minimizingCoordinates a (finiteCells F) V ρ x i))
    (η : StepVariable (finiteCells F)) :
    ReferenceDensity.chartedEnergyAtMinimizer a ρ (BlockAverages.gaugeTransform γ V) η =
      ReferenceDensity.chartedEnergyAtMinimizer a ρ V (bondwiseIsometry (gaugeRotation γ) η) := by
  unfold ReferenceDensity.chartedEnergyAtMinimizer chartedEnergy
  rw [coordsAboveFrame_gaugeTransform hw, hM.chartedField_gaugeTransform, hM.energy_gaugeTransform]
private theorem fieldAboveFrame_gaugeTransform (hM : ChartEquivariance F a)
    (hw : minimizingCoordinates a (finiteCells F) (BlockAverages.gaugeTransform γ V) ρ =
      fun x i => adjointMap (γ (enclosingCell x)) (minimizingCoordinates a (finiteCells F) V ρ x i)) :
    fieldAboveFrame true a ρ 0 (BlockAverages.gaugeTransform γ V) 0 =
      BlockAverages.gaugeTransform (ColdStepAtMirrorFrames.blockConstantGauge γ) (fieldAboveFrame true a ρ 0 V 0) := by
  unfold fieldAboveFrame
  rw [coordsAboveFrame_gaugeTransform hw, hM.chartedField_gaugeTransform, map_zero]
private theorem stepLogAmplitude_gaugeTransform (hM : ChartEquivariance F a)
    (hw : minimizingCoordinates a (finiteCells F) (BlockAverages.gaugeTransform γ V) ρ =
      fun x i => adjointMap (γ (enclosingCell x)) (minimizingCoordinates a (finiteCells F) V ρ x i))
    (hf : AnalyticAt ℝ (ReferenceDensity.chartedEnergyAtMinimizer a ρ V) 0) :
    stepLogAmplitude a ρ (BlockAverages.gaugeTransform γ V) = stepLogAmplitude a ρ V := by
  have hfun : ReferenceDensity.chartedEnergyAtMinimizer a ρ (BlockAverages.gaugeTransform γ V) =
      fun η => ReferenceDensity.chartedEnergyAtMinimizer a ρ V (bondwiseIsometry (gaugeRotation γ) η) :=
    funext (chartedEnergyAtMinimizer_gaugeTransform hM hw)
  have hH : ReferenceDensity.chartedHessian a ρ (BlockAverages.gaugeTransform γ V) 0 =
      (bondwiseMatrix (gaugeRotation γ)).transpose * ReferenceDensity.chartedHessian a ρ V 0 *
        bondwiseMatrix (gaugeRotation γ) :=
    hessian_bondwiseIsometry (gaugeRotation γ) hf _ fun i j => by
      show ColdStepAtMirrorFrames.secondDerivAlong
        (ReferenceDensity.chartedEnergyAtMinimizer a ρ (BlockAverages.gaugeTransform γ V)) 0 _ _ = _
      rw [hfun]
      rfl
  have hdet : (ReferenceDensity.chartedHessian a ρ (BlockAverages.gaugeTransform γ V) 0).det =
      (ReferenceDensity.chartedHessian a ρ V 0).det := by
    have hO := congrArg Matrix.det (transpose_mul_bondwiseMatrix (gaugeRotation γ))
    rw [Matrix.det_mul, Matrix.det_one] at hO
    rw [hH, Matrix.det_mul, Matrix.det_mul]
    calc (bondwiseMatrix (gaugeRotation γ)).transpose.det * (ReferenceDensity.chartedHessian a ρ V 0).det *
          (bondwiseMatrix (gaugeRotation γ)).det
        = ((bondwiseMatrix (gaugeRotation γ)).transpose.det * (bondwiseMatrix (gaugeRotation γ)).det) *
            (ReferenceDensity.chartedHessian a ρ V 0).det := by ring
      _ = (ReferenceDensity.chartedHessian a ρ V 0).det := by rw [hO, one_mul]
  have h2 : (∑ c ∈ innerBonds (finiteCells F) F.top,
        Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true a ρ 0 (BlockAverages.gaugeTransform γ V) 0) c‖) =
      ∑ c ∈ innerBonds (finiteCells F) F.top, Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true a ρ 0 V 0) c‖ :=
    Finset.sum_congr rfl fun c _ => by
      rw [fieldAboveFrame_gaugeTransform hM hw, hM.norm_contourAverage_gaugeTransform]
  have h3 : (∑ b : ↥(chordBonds (finiteCells F)),
        haarLogRatio (coordsAboveFrame true a ρ 0 (BlockAverages.gaugeTransform γ V) 0 b.1.1 b.1.2)) =
      ∑ b : ↥(chordBonds (finiteCells F)), haarLogRatio (coordsAboveFrame true a ρ 0 V 0 b.1.1 b.1.2) :=
    Finset.sum_congr rfl fun b _ => by
      have e := congrFun (congrFun (coordsAboveFrame_gaugeTransform hw 0) b.1.1) b.1.2
      rw [map_zero] at e
      have e2 : ‖coordsAboveFrame true a ρ 0 (BlockAverages.gaugeTransform γ V) 0 b.1.1 b.1.2‖ =
          ‖coordsAboveFrame true a ρ 0 V 0 b.1.1 b.1.2‖ := by
        rw [e]
        exact norm_adjointMap _ _
      unfold haarLogRatio
      rw [e2]
  unfold stepLogAmplitude
  rw [hdet, h2, h3]
private theorem isMinimizingChart_radius_one {S : Finset F.Cell} {V : F.GaugeField F.top}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h : IsMinimizingChart a S V ρ w) (h1 : ρ ≤ 1) : IsMinimizingChart a S V 1 w :=
  ⟨h.1, fun b hb => (h.2.1 b hb).trans h1, h.2.2⟩
private theorem isMinimizingChart_minimizingCoordinates {S : Finset F.Cell} {V : F.GaugeField F.top}
    (h : ∃ w, IsMinimizingChart a S V ρ w) : IsMinimizingChart a S V ρ (minimizingCoordinates a S V ρ) := by apply _root_.YangMills.SharedProofs.p13409 <;> assumption
private theorem isCold_three (S : Finset F.Cell) (j : ℕ) (X : F.GaugeField j) : IsCold S j (24 / 8) X := by apply _root_.YangMills.SharedProofs.p32772 <;> assumption
private theorem fieldAboveFrame_zero (V : F.GaugeField F.top) :
    fieldAboveFrame true a ρ 0 V 0 = chartedField (minimizingCoordinates a (finiteCells F) V ρ) V := by apply _root_.YangMills.SharedProofs.p22006 <;> assumption
private theorem minimizingCoordinates_gaugeTransform (hOL : MinimizingChartUnique)
    (hG : MinimalActionGaugeCovariance) (hL : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (h1 : ρ ≤ 1) (hex : ∃ w, IsMinimizingChart a (finiteCells F) V ρ w)
    (hex' : ∃ w, IsMinimizingChart a (finiteCells F) (BlockAverages.gaugeTransform γ V) ρ w)
    (horb : ∀ W' : F.GaugeField F.depth, (∀ W'', blockEnergy a (finiteCells F) F.depth W'
        (BlockAverages.gaugeTransform γ V) ≤
        blockEnergy a (finiteCells F) F.depth W'' (BlockAverages.gaugeTransform γ V)) →
      ∃ g : F.Site F.depth → UnitQuaternion, (∀ z : F.Cell, g (cellCentre _ z) = 1) ∧
        W' = BlockAverages.gaugeTransform g (fieldAboveFrame true a ρ 0 (BlockAverages.gaugeTransform γ V) 0)) :
    minimizingCoordinates a (finiteCells F) (BlockAverages.gaugeTransform γ V) ρ =
      fun x i => adjointMap (γ (enclosingCell x)) (minimizingCoordinates a (finiteCells F) V ρ x i) := by
  have hw := isMinimizingChart_radius_one (isMinimizingChart_minimizingCoordinates hex') h1
  have ht := isMinimizingChart_radius_one (hG.2 F a ρ V _ γ hL hs (isMinimizingChart_minimizingCoordinates hex)) h1
  have hOne : HasColdMinimizer a 1 1 24 (finiteCells F) (BlockAverages.gaugeTransform γ V) := by
    refine ⟨minimizingCoordinates a (finiteCells F) (BlockAverages.gaugeTransform γ V) ρ, ?_, isCold_three _ _ _, ?_⟩
    · have e : min (1 : ℝ) (1 * 24) = 1 := by norm_num
      rw [e]
      exact hw
    · intro W' hW'
      obtain ⟨g, hg, e⟩ := horb W' hW'
      refine ⟨g, hg, fun b _ => ?_⟩
      rw [e, fieldAboveFrame_zero]
  exact ((hOL F a 1 1 24 _ _ hL hs le_rfl hOne hw).1 _ ht).symm
end Gauge
end OnFrames
private theorem continuous_torusGaugeTransform {n : ℕ} :
    Continuous (fun p : (TorusFields.TorusSite n → UnitQuaternion) × TorusFields.TorusField n =>
      TorusFields.gaugeTransform p.1 p.2) := by apply _root_.YangMills.SharedProofs.p21641 <;> assumption
private theorem torusGaugeTransform_one_trivialField {n : ℕ} :
    TorusFields.gaugeTransform (1 : TorusFields.TorusSite n → UnitQuaternion) (TorusFields.trivialField n) =
      TorusFields.trivialField n := by
  funext y i
  simp [TorusFields.gaugeTransform, TorusFields.trivialField]
theorem stepGaugeTotalInvariant (hN : RunningCouplingSlope.MinimizerNearTrivialField)
    (hA : ChartedEnergyAnalyticNearTrivial) (hOL : MinimizingChartUnique)
    (hC : chartEquivarianceStatement) (hG : MinimalActionGaugeCovariance) :
    StepGaugeTotalInvariant := by
  intro a ha L hL t ρ h0 h1
  filter_upwards [eventually_ge_atTop (2 * L)] with n hn
  have hL13 := hL.2
  have : NeZero n := ⟨by omega⟩
  have hs : ∀ i, 2 ≤ (TorusFields.torusFrame L t n).extent i := fun _ => by
    show 2 ≤ n
    omega
  have hodd : Odd (TorusFields.torusFrame L t n).blockSide := hL.1
  have hp : ∀ i, (TorusFields.torusFrame L t n).period (TorusFields.torusFrame L t n).top i = n :=
    fun i => TopLevelSites.period_top i
  have hE := (hN a ha L hL t n ρ hn h0 h1).2.and (hA a ha L hL t n ρ hn h0 h1)
  have hc : Tendsto (fun p : (TorusFields.TorusSite n → UnitQuaternion) × TorusFields.TorusField n =>
      TorusFields.gaugeTransform p.1 p.2)
      (𝓝 (1, TorusFields.trivialField n)) (𝓝 (TorusFields.trivialField n)) := by
    have := continuous_torusGaugeTransform.tendsto
      ((1 : TorusFields.TorusSite n → UnitQuaternion), TorusFields.trivialField n)
    simpa only [torusGaugeTransform_one_trivialField] using this
  have hsnd : Tendsto (fun p : (TorusFields.TorusSite n → UnitQuaternion) × TorusFields.TorusField n => p.2)
      (𝓝 (1, TorusFields.trivialField n)) (𝓝 (TorusFields.trivialField n)) :=
    continuous_snd.tendsto ((1 : TorusFields.TorusSite n → UnitQuaternion), TorusFields.trivialField n)
  filter_upwards [hsnd.eventually hE, hc.eventually hE] with p hV hV'
  obtain ⟨g, W⟩ := p
  have e : TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top
      (TorusFields.gaugeTransform g W) =
      BlockAverages.gaugeTransform (fun z => g (TorusLumps.toTorusSite n z))
        (TorusFields.readAtLevel (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top W) := by
    funext x i
    show g (TorusLumps.toTorusSite n x) * W (TorusLumps.toTorusSite n x) i *
        (g (TorusLumps.toTorusSite n x + TorusFields.unitStep n i))⁻¹ =
      g (TorusLumps.toTorusSite n x) * W (TorusLumps.toTorusSite n x) i *
        (g (TorusLumps.toTorusSite n (x + BlockAverages.unitStep (TorusFields.torusFrame L t n).top i)))⁻¹
    rw [TopLevelSites.toTorusSite_add hp, TopLevelSites.toTorusSite_unitStep hp]
  simp only at hV hV' ⊢
  obtain ⟨⟨hw, -, -, -, -⟩, hf⟩ := hV
  obtain ⟨⟨hw', hu', -, -, -⟩, -⟩ := hV'
  rw [e] at hw' hu'
  unfold stepGaugeTotal
  rw [e, stepLogAmplitude_gaugeTransform (hC _ a hodd hs)
    (minimizingCoordinates_gaugeTransform hOL hG hodd hs h1 hw hw' hu') hf]
end SlopeCoefficient
end YangMills.Construction
end
