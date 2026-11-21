import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.ClusterExpansionOfAStep.ContoursFromBases
import YangMills.Construction.ColdStepAtMirrorFrames.ChartUnderGaugesAndShifts
import YangMills.Construction.ColdStepAtMirrorFrames.GaugeOfTheLeastChartProof
import YangMills.Construction.ColdStepAtMirrorFrames.TranslationOfTheLeastChart
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsInvariantAtParameters
import YangMills.Construction.RunningCouplingSlope.ValueOfTheDensityOfTheStepOnTwoToriAtParametersProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.StepDensity
open BlockAverages ColdStepAtMirrorFrames
section Matrices
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem conj_resolvent (O H : Matrix ι ι ℝ) (l τ : ℝ) (hO : O.transpose * O = 1) :
    (O.transpose * H * O - l • (1 : Matrix ι ι ℝ)) *
        (τ • (O.transpose * H * O) + (1 - τ) • l • (1 : Matrix ι ι ℝ))⁻¹ =
      O.transpose * ((H - l • (1 : Matrix ι ι ℝ)) * (τ • H + (1 - τ) • l • (1 : Matrix ι ι ℝ))⁻¹) * O := by
  have hO' : O * O.transpose = 1 := mul_eq_one_comm.mp hO
  have one_conj : ∀ r : ℝ, r • (1 : Matrix ι ι ℝ) = O.transpose * (r • (1 : Matrix ι ι ℝ)) * O := fun r => by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hO]
  have e1 : O.transpose * H * O - l • (1 : Matrix ι ι ℝ) = O.transpose * (H - l • (1 : Matrix ι ι ℝ)) * O := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← one_conj]
  have e2 : τ • (O.transpose * H * O) + (1 - τ) • l • (1 : Matrix ι ι ℝ) =
      O.transpose * (τ • H + (1 - τ) • l • (1 : Matrix ι ι ℝ)) * O := by
    rw [Matrix.mul_add, Matrix.add_mul, smul_smul, ← one_conj, Matrix.mul_smul, Matrix.smul_mul]
  have i1 : O⁻¹ = O.transpose := Matrix.inv_eq_left_inv hO
  have i2 : O.transpose⁻¹ = O := Matrix.inv_eq_left_inv hO'
  have cancel : ∀ X : Matrix ι ι ℝ, O * (O.transpose * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hO', Matrix.one_mul]
  rw [e1, e2, Matrix.mul_inv_rev, Matrix.mul_inv_rev, i1, i2]
  simp only [Matrix.mul_assoc, cancel]
private theorem weightedTrace_conj (O M : Matrix ι ι ℝ) (d : ι → ℝ) (hO : O.transpose * O = 1)
    (hd : ∀ i j, O i j ≠ 0 → d i = d j) :
    ∑ i, d i * (O.transpose * M * O) i i = ∑ i, d i * M i i := by
  have hO' : O * O.transpose = 1 := mul_eq_one_comm.mp hO
  have hc : O * Matrix.diagonal d = Matrix.diagonal d * O := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h : O i j = 0
    · simp [h]
    · rw [hd i j h, mul_comm]
  have t : ∀ X : Matrix ι ι ℝ, ∑ i, d i * X i i = (Matrix.diagonal d * X).trace := fun X => by
    simp [Matrix.trace, Matrix.diagonal_mul]
  rw [t, t]
  calc (Matrix.diagonal d * (O.transpose * M * O)).trace
      = (O * (Matrix.diagonal d * (O.transpose * M))).trace := by
        rw [Matrix.trace_mul_comm O]
        simp only [Matrix.mul_assoc]
    _ = (Matrix.diagonal d * M).trace := by
        rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, ← Matrix.mul_assoc O, hO', Matrix.one_mul]
private theorem resolventTrace_reindex (π : ι ≃ ι) (H H' : Matrix ι ι ℝ) (l τ : ℝ) (hH : H = H'.submatrix π π)
    {c c' : ι → Prop} [DecidablePred c] [DecidablePred c'] (hc : ∀ i, c' (π i) ↔ c i) :
    (∑ i, if c' i then ((H' - l • (1 : Matrix ι ι ℝ)) * (τ • H' + (1 - τ) • l • (1 : Matrix ι ι ℝ))⁻¹) i i else 0) =
      ∑ i, if c i then ((H - l • (1 : Matrix ι ι ℝ)) * (τ • H + (1 - τ) • l • (1 : Matrix ι ι ℝ))⁻¹) i i else 0 := by
  have e1 : H - l • (1 : Matrix ι ι ℝ) = (H' - l • (1 : Matrix ι ι ℝ)).submatrix π π := by
    rw [hH]
    ext i j
    simp [Matrix.one_apply]
  have e2 : τ • H + (1 - τ) • l • (1 : Matrix ι ι ℝ) =
      (τ • H' + (1 - τ) • l • (1 : Matrix ι ι ℝ)).submatrix π π := by
    rw [hH]
    ext i j
    simp [Matrix.one_apply]
  rw [e1, e2, Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv]
  rw [← π.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hc i, Matrix.submatrix_apply]
end Matrices
section Derivatives
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem secondDerivAlong_comp (R : BondField ι ≃L[ℝ] BondField ι) (f : BondField ι → ℝ)
    (u v : BondField ι) :
    secondDerivAlong (fun η => f (R η)) 0 u v = secondDerivAlong f 0 (R u) (R v) := by
  unfold secondDerivAlong
  have h1 : ∀ ζ, fderiv ℝ (fun η => f (R η)) ζ u = fderiv ℝ f (R ζ) (R u) := fun ζ => by
    have h := R.comp_right_fderiv (f := f) (x := ζ)
    have h' := congrArg (fun T : BondField ι →L[ℝ] ℝ => T u) h
    exact h'
  simp only [h1]
  have h2 := R.comp_right_fderiv (f := fun ζ => fderiv ℝ f ζ (R u)) (x := 0)
  have h3 := congrArg (fun T : BondField ι →L[ℝ] ℝ => T v) h2
  simp only [map_zero] at h3
  exact h3
abbrev _root_.YangMills.SharedProofs.p72470 := @secondDerivAlong_comp
private theorem secondDerivAlong_eq_fderiv_fderiv {f : BondField ι → ℝ} (hf : AnalyticAt ℝ f 0) (u v : BondField ι) :
    secondDerivAlong f 0 u v = fderiv ℝ (fderiv ℝ f) 0 v u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) 0 := hf.fderiv.differentiableAt
  have h := ((ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp 0 hd.hasFDerivAt).fderiv
  unfold secondDerivAlong
  have e : (fun ζ => fderiv ℝ f ζ u) = (ContinuousLinearMap.apply ℝ ℝ u) ∘ fderiv ℝ f := rfl
  rw [e, h]
  rfl
abbrev _root_.YangMills.SharedProofs.p53373 := @secondDerivAlong_eq_fderiv_fderiv
private def coordUnit (k : ι × Fin 3) : BondField ι := bondVariation k.1 (EuclideanSpace.single k.2 1)
private theorem coordUnit_apply (k : ι × Fin 3) (b : ι) (α : Fin 3) :
    coordUnit k b α = if k = (b, α) then 1 else 0 := by
  unfold coordUnit bondVariation
  by_cases hb : b = k.1
  · subst hb
    by_cases hα : α = k.2
    · subst hα
      simp
    · have : k ≠ (k.1, α) := fun e => hα (congrArg Prod.snd e).symm
      simp [this, hα]
  · have : k ≠ (b, α) := fun e => hb (congrArg Prod.fst e).symm
    simp [this, Pi.single_eq_of_ne hb]
abbrev _root_.YangMills.DeltaSharedProofs.p501987 := @coordUnit_apply
private theorem eq_sum_coordUnit (u : BondField ι) : u = ∑ k : ι × Fin 3, u k.1 k.2 • coordUnit k := by
  funext b
  ext α
  have h : (∑ k : ι × Fin 3, u k.1 k.2 • coordUnit k) b α = ∑ k : ι × Fin 3, u k.1 k.2 * coordUnit k b α := by
    simp [Finset.sum_apply]
  rw [h]
  simp only [coordUnit_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (b, α)]
  simp
abbrev _root_.YangMills.DeltaSharedProofs.p501785 := @eq_sum_coordUnit
private def rotateBonds (T : ι → BondVector ≃ₗᵢ[ℝ] BondVector) : BondField ι ≃L[ℝ] BondField ι :=
  (LinearEquiv.piCongrRight fun b => (T b).toLinearEquiv).toContinuousLinearEquiv
private theorem rotateBonds_apply (T : ι → BondVector ≃ₗᵢ[ℝ] BondVector) (η : BondField ι) (b : ι) :
    rotateBonds T η b = T b (η b) := rfl
private def rotationMatrix (T : ι → BondVector ≃ₗᵢ[ℝ] BondVector) : Matrix (ι × Fin 3) (ι × Fin 3) ℝ :=
  fun k i => rotateBonds T (coordUnit i) k.1 k.2
private theorem rotationMatrix_ne (T : ι → BondVector ≃ₗᵢ[ℝ] BondVector) {k i : ι × Fin 3}
    (h : rotationMatrix T k i ≠ 0) : k.1 = i.1 := by
  by_contra hne
  apply h
  have e : coordUnit i k.1 = 0 := by
    unfold coordUnit bondVariation
    exact Pi.single_eq_of_ne hne _
  simp [rotationMatrix, rotateBonds_apply, e]
private theorem rotationMatrix_orthogonal (T : ι → BondVector ≃ₗᵢ[ℝ] BondVector) :
    (rotationMatrix T).transpose * rotationMatrix T = 1 := by
  have key : ∀ (b : ι) (x y : BondVector), ∑ α, T b x α * T b y α = ∑ α, x α * y α := fun b x y => by
    have h := (T b).inner_map_map x y
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h
    simpa [mul_comm] using h
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, rotationMatrix]
  rw [Fintype.sum_prod_type]
  simp only [rotateBonds_apply, key]
  rw [← Fintype.sum_prod_type (f := fun k : ι × Fin 3 => coordUnit i k.1 k.2 * coordUnit j k.1 k.2)]
  simp only [coordUnit_apply, Prod.mk.eta, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]
private theorem hessian_rotate (T : ι → BondVector ≃ₗᵢ[ℝ] BondVector) {f : BondField ι → ℝ} (hf : AnalyticAt ℝ f 0)
    (H' : Matrix (ι × Fin 3) (ι × Fin 3) ℝ)
    (hH' : ∀ i j, H' i j = secondDerivAlong (fun η => f (rotateBonds T η)) 0 (coordUnit i) (coordUnit j)) :
    H' = (rotationMatrix T).transpose *
      (Matrix.of fun i j => secondDerivAlong f 0 (coordUnit i) (coordUnit j)) * rotationMatrix T := by
  ext i j
  have ei := eq_sum_coordUnit (rotateBonds T (coordUnit i))
  have ej := eq_sum_coordUnit (rotateBonds T (coordUnit j))
  rw [hH', secondDerivAlong_comp, secondDerivAlong_eq_fderiv_fderiv hf]
  rw [ei, ej]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, secondDerivAlong_eq_fderiv_fderiv hf,
    rotationMatrix, Finset.sum_mul, Finset.mul_sum]
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
    adjointMap g (adjointMap g⁻¹ v) = v := by
  apply Subtype.ext
  show (g : ℍ[ℝ]) * (((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (v : ℍ[ℝ]) * (((g⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ])) *
    ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = v
  rw [inv_inv]
  have e1 : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul]
    simp
  calc (g : ℍ[ℝ]) * (((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (v : ℍ[ℝ]) * (g : ℍ[ℝ])) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])
      = ((g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) * (v : ℍ[ℝ]) *
          ((g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
        simp only [mul_assoc]
    _ = v := by rw [e1, one_mul, mul_one]
abbrev _root_.YangMills.SharedProofs.p92515 := @adjointMap_adjointMap_inv
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
    coordsAboveFrame true a ρ 0 V η x i =
      minimizingCoordinates a (finiteCells F) V ρ x i + stepCoordinates η x i := by
  simp [coordsAboveFrame, stepFrame, minimizingBondCoordinate]
section Gauge
variable {γ : F.Cell → UnitQuaternion} {V : F.GaugeField F.top}
private def gaugeRotation (γ : F.Cell → UnitQuaternion) (b : ↥(chordBonds (finiteCells F))) :
    BondVector ≃ₗᵢ[ℝ] BondVector :=
  adjointIsometry (γ (enclosingCell b.1.1))⁻¹
private theorem stepCoordinates_rotate (η : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (rotateBonds (gaugeRotation γ) η) x i =
      adjointMap (γ (enclosingCell x))⁻¹ (stepCoordinates η x i) := by
  unfold stepCoordinates
  split_ifs with h
  · exact toImaginary_adjointIsometry _ _
  · simp
private theorem coordsAboveFrame_gaugeTransform
    (hw : minimizingCoordinates a (finiteCells F) (gaugeTransform γ V) ρ =
      fun x i => adjointMap (γ (enclosingCell x)) (minimizingCoordinates a (finiteCells F) V ρ x i))
    (η : StepVariable (finiteCells F)) :
    coordsAboveFrame true a ρ 0 (gaugeTransform γ V) η =
      fun x i => ColdStepAtMirrorFrames.adjointAction (γ (enclosingCell x))
        (coordsAboveFrame true a ρ 0 V (rotateBonds (gaugeRotation γ) η) x i) := by
  funext x i
  rw [coordsAboveFrame_apply, coordsAboveFrame_apply, hw, stepCoordinates_rotate]
  have e : ∀ (g : UnitQuaternion) (X : imaginaryQuaternions),
      ColdStepAtMirrorFrames.adjointAction g X = adjointMap g X :=
    fun _ _ => rfl
  rw [e, map_add, adjointMap_adjointMap_inv]
private theorem chartedEnergyAtMinimizer_gaugeTransform (hM : ChartEquivariance F a)
    (hw : minimizingCoordinates a (finiteCells F) (gaugeTransform γ V) ρ =
      fun x i => adjointMap (γ (enclosingCell x)) (minimizingCoordinates a (finiteCells F) V ρ x i))
    (η : StepVariable (finiteCells F)) :
    ReferenceDensity.chartedEnergyAtMinimizer a ρ (gaugeTransform γ V) η =
      ReferenceDensity.chartedEnergyAtMinimizer a ρ V (rotateBonds (gaugeRotation γ) η) := by
  unfold ReferenceDensity.chartedEnergyAtMinimizer chartedEnergy
  rw [coordsAboveFrame_gaugeTransform hw, hM.chartedField_gaugeTransform, hM.energy_gaugeTransform]
private theorem fieldAboveFrame_gaugeTransform (hM : ChartEquivariance F a)
    (hw : minimizingCoordinates a (finiteCells F) (gaugeTransform γ V) ρ =
      fun x i => adjointMap (γ (enclosingCell x)) (minimizingCoordinates a (finiteCells F) V ρ x i)) :
    fieldAboveFrame true a ρ 0 (gaugeTransform γ V) 0 =
      gaugeTransform (ColdStepAtMirrorFrames.blockConstantGauge γ) (fieldAboveFrame true a ρ 0 V 0) := by
  unfold fieldAboveFrame
  rw [coordsAboveFrame_gaugeTransform hw, hM.chartedField_gaugeTransform, map_zero]
private theorem stepDensity_gaugeTransform (hM : ChartEquivariance F a)
    (hw : minimizingCoordinates a (finiteCells F) (gaugeTransform γ V) ρ =
      fun x i => adjointMap (γ (enclosingCell x)) (minimizingCoordinates a (finiteCells F) V ρ x i))
    (hf : AnalyticAt ℝ (ReferenceDensity.chartedEnergyAtMinimizer a ρ V) 0) (lam : ℝ) (Y : F.Cell) :
    ReferenceDensity.stepDensity a ρ lam Y (gaugeTransform γ V) = ReferenceDensity.stepDensity a ρ lam Y V := by
  have hfun : ReferenceDensity.chartedEnergyAtMinimizer a ρ (gaugeTransform γ V) =
      fun η => ReferenceDensity.chartedEnergyAtMinimizer a ρ V (rotateBonds (gaugeRotation γ) η) :=
    funext (chartedEnergyAtMinimizer_gaugeTransform hM hw)
  have hH : ReferenceDensity.chartedHessian a ρ (gaugeTransform γ V) 0 = (rotationMatrix (gaugeRotation γ)).transpose *
      ReferenceDensity.chartedHessian a ρ V 0 * rotationMatrix (gaugeRotation γ) :=
    hessian_rotate (gaugeRotation γ) hf _ fun i j => by
      show secondDerivAlong (ReferenceDensity.chartedEnergyAtMinimizer a ρ (gaugeTransform γ V)) 0 _ _ = _
      rw [hfun]
      rfl
  have hS : ∀ τ, ReferenceDensity.hessianCellShare a ρ lam Y (gaugeTransform γ V) τ =
      ReferenceDensity.hessianCellShare a ρ lam Y V τ := fun τ => by
    unfold ReferenceDensity.hessianCellShare
    rw [hH, conj_resolvent _ _ _ _ (rotationMatrix_orthogonal _)]
    have c : ∀ M : Matrix (ReferenceDensity.ChartCoord F) (ReferenceDensity.ChartCoord F) ℝ,
        (∑ i : ReferenceDensity.ChartCoord F, if enclosingCell i.1.1.1 = Y then M i i else 0) =
          ∑ i : ReferenceDensity.ChartCoord F, (if enclosingCell i.1.1.1 = Y then (1 : ℝ) else 0) * M i i := fun M =>
      Finset.sum_congr rfl fun i _ => by
        split_ifs <;> simp
    refine (c _).trans ((weightedTrace_conj _ _ _ (rotationMatrix_orthogonal _) ?_).trans (c _).symm)
    intro i j h
    simp only [rotationMatrix_ne _ h]
  have h1 : (∫ τ in (0 : ℝ)..1, ReferenceDensity.hessianCellShare a ρ lam Y (gaugeTransform γ V) τ) =
      ∫ τ in (0 : ℝ)..1, ReferenceDensity.hessianCellShare a ρ lam Y V τ := by
    simp only [hS]
  have h2 : (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        Real.log ‖contourAverage (fieldAboveFrame true a ρ 0 (gaugeTransform γ V) 0) c‖) =
      ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        Real.log ‖contourAverage (fieldAboveFrame true a ρ 0 V 0) c‖ :=
    Finset.sum_congr rfl fun c _ => by
      rw [fieldAboveFrame_gaugeTransform hM hw, hM.norm_contourAverage_gaugeTransform]
  have h3 : (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
        haarLogRatio (coordsAboveFrame true a ρ 0 (gaugeTransform γ V) 0 b.1.1 b.1.2) else 0) =
      ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
        haarLogRatio (coordsAboveFrame true a ρ 0 V 0 b.1.1 b.1.2) else 0 :=
    Finset.sum_congr rfl fun b _ => by
      have e := congrFun (congrFun (coordsAboveFrame_gaugeTransform hw 0) b.1.1) b.1.2
      rw [map_zero] at e
      have e2 : ‖coordsAboveFrame true a ρ 0 (gaugeTransform γ V) 0 b.1.1 b.1.2‖ =
          ‖coordsAboveFrame true a ρ 0 V 0 b.1.1 b.1.2‖ := by
        rw [e]
        exact norm_adjointMap _ _
      unfold haarLogRatio
      rw [e2]
  unfold ReferenceDensity.stepDensity
  rw [h1, h2, h3]
end Gauge
section Shift
variable {h : F.Cell} {V : F.GaugeField F.top}
private def bondTranslation (hM : ChartEquivariance F a) (h : F.Cell) :
    ↥(chordBonds (finiteCells F)) ≃ ↥(chordBonds (finiteCells F)) where
  toFun b := ⟨(b.1.1 + cellCentre F.depth h, b.1.2), (hM.chordBonds_translate h b.1).mpr b.2⟩
  invFun b := ⟨(b.1.1 - cellCentre F.depth h, b.1.2),
    (hM.chordBonds_translate h (b.1.1 - cellCentre F.depth h, b.1.2)).mp (by simpa using b.2)⟩
  left_inv b := Subtype.ext (by simp)
  right_inv b := Subtype.ext (by simp)
private def permuteBonds {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ ι) : BondField ι ≃L[ℝ] BondField ι :=
  (LinearEquiv.funCongrLeft ℝ BondVector e.symm).toContinuousLinearEquiv
private theorem permuteBonds_apply {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ ι) (η : BondField ι) (b : ι) :
    permuteBonds e η b = η (e.symm b) := rfl
private theorem permuteBonds_coordUnit {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ ι) (k : ι × Fin 3) :
    permuteBonds e (coordUnit k) = coordUnit (Equiv.prodCongr e (Equiv.refl _) k) := by
  funext b
  rw [permuteBonds_apply]
  unfold coordUnit bondVariation
  by_cases hb : b = e k.1
  · subst hb
    simp
  · have h1 : e.symm b ≠ k.1 := fun h2 => hb (by rw [← h2]; simp)
    have l : (Pi.single k.1 (EuclideanSpace.single k.2 (1 : ℝ)) : ι → BondVector) (e.symm b) = 0 :=
      Pi.single_eq_of_ne h1 _
    have r : (Pi.single (e k.1) (EuclideanSpace.single k.2 (1 : ℝ)) : ι → BondVector) b = 0 :=
      Pi.single_eq_of_ne hb _
    exact l.trans r.symm
private theorem stepCoordinates_permute (hM : ChartEquivariance F a) (η : StepVariable (finiteCells F))
    (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (permuteBonds (bondTranslation hM h) η) x i = stepCoordinates η (x - cellCentre F.depth h) i := by
  unfold stepCoordinates
  by_cases h1 : (x, i) ∈ chordBonds (finiteCells F)
  · have h2 : (x - cellCentre F.depth h, i) ∈ chordBonds (finiteCells F) :=
      (hM.chordBonds_translate h (x - cellCentre F.depth h, i)).mp (by simpa using h1)
    rw [dif_pos h1, dif_pos h2]
    rfl
  · have h2 : (x - cellCentre F.depth h, i) ∉ chordBonds (finiteCells F) := fun h3 =>
      h1 (by simpa using (hM.chordBonds_translate h (x - cellCentre F.depth h, i)).mpr h3)
    rw [dif_neg h1, dif_neg h2]
private theorem coordsAboveFrame_translate (hM : ChartEquivariance F a)
    (hw : minimizingCoordinates a (finiteCells F) (translateField h V) ρ =
      fun x i => minimizingCoordinates a (finiteCells F) V ρ (x - cellCentre F.depth h) i)
    (η : StepVariable (finiteCells F)) :
    coordsAboveFrame true a ρ 0 (translateField h V) (permuteBonds (bondTranslation hM h) η) =
      fun x i => coordsAboveFrame true a ρ 0 V η (x - cellCentre F.depth h) i := by
  funext x i
  rw [coordsAboveFrame_apply, coordsAboveFrame_apply, hw, stepCoordinates_permute]
private theorem chartedEnergyAtMinimizer_translate (hM : ChartEquivariance F a)
    (hw : minimizingCoordinates a (finiteCells F) (translateField h V) ρ =
      fun x i => minimizingCoordinates a (finiteCells F) V ρ (x - cellCentre F.depth h) i)
    (η : StepVariable (finiteCells F)) :
    ReferenceDensity.chartedEnergyAtMinimizer a ρ (translateField h V) (permuteBonds (bondTranslation hM h) η) =
      ReferenceDensity.chartedEnergyAtMinimizer a ρ V η := by
  unfold ReferenceDensity.chartedEnergyAtMinimizer chartedEnergy
  rw [coordsAboveFrame_translate hM hw, hM.chartedField_translate, hM.energy_translate]
private theorem fieldAboveFrame_translate (hM : ChartEquivariance F a)
    (hw : minimizingCoordinates a (finiteCells F) (translateField h V) ρ =
      fun x i => minimizingCoordinates a (finiteCells F) V ρ (x - cellCentre F.depth h) i) :
    fieldAboveFrame true a ρ 0 (translateField h V) 0 =
      translateField (cellCentre F.depth h) (fieldAboveFrame true a ρ 0 V 0) := by
  have e := coordsAboveFrame_translate hM hw 0
  rw [map_zero] at e
  unfold fieldAboveFrame
  rw [e, hM.chartedField_translate]
private theorem stepDensity_translate (hM : ChartEquivariance F a)
    (hw : minimizingCoordinates a (finiteCells F) (translateField h V) ρ =
      fun x i => minimizingCoordinates a (finiteCells F) V ρ (x - cellCentre F.depth h) i) (lam : ℝ) (Y : F.Cell) :
    ReferenceDensity.stepDensity a ρ lam (Y + h) (translateField h V) = ReferenceDensity.stepDensity a ρ lam Y V := by
  set e := bondTranslation hM h with he
  have hfun : (fun η => ReferenceDensity.chartedEnergyAtMinimizer a ρ (translateField h V) (permuteBonds e η)) =
      ReferenceDensity.chartedEnergyAtMinimizer a ρ V :=
    funext (chartedEnergyAtMinimizer_translate hM hw)
  have hH : ReferenceDensity.chartedHessian a ρ V 0 =
      (ReferenceDensity.chartedHessian a ρ (translateField h V) 0).submatrix (Equiv.prodCongr e (Equiv.refl _))
        (Equiv.prodCongr e (Equiv.refl _)) := by
    ext i j
    show secondDerivAlong (ReferenceDensity.chartedEnergyAtMinimizer a ρ V) 0 (coordUnit i) (coordUnit j) =
      secondDerivAlong (ReferenceDensity.chartedEnergyAtMinimizer a ρ (translateField h V)) 0
        (coordUnit (Equiv.prodCongr e (Equiv.refl _) i)) (coordUnit (Equiv.prodCongr e (Equiv.refl _) j))
    rw [← hfun, secondDerivAlong_comp, permuteBonds_coordUnit, permuteBonds_coordUnit]
  have hcell : ∀ b : ↥(chordBonds (finiteCells F)), enclosingCell (e b).1.1 = enclosingCell b.1.1 + h := fun b =>
    hM.enclosingCell_translate h b.1.1
  have hS : ∀ τ, ReferenceDensity.hessianCellShare a ρ lam (Y + h) (translateField h V) τ =
      ReferenceDensity.hessianCellShare a ρ lam Y V τ := fun τ => by
    unfold ReferenceDensity.hessianCellShare
    refine resolventTrace_reindex (Equiv.prodCongr e (Equiv.refl _)) _ _ lam τ hH
      (c := fun i : ReferenceDensity.ChartCoord F => enclosingCell i.1.1.1 = Y)
      (c' := fun i : ReferenceDensity.ChartCoord F => enclosingCell i.1.1.1 = Y + h) fun i => ?_
    show enclosingCell (e i.1).1.1 = Y + h ↔ _
    rw [hcell, add_left_inj]
  have h1 : (∫ τ in (0 : ℝ)..1, ReferenceDensity.hessianCellShare a ρ lam (Y + h) (translateField h V) τ) =
      ∫ τ in (0 : ℝ)..1, ReferenceDensity.hessianCellShare a ρ lam Y V τ := by
    simp only [hS]
  have h2 : (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y + h),
        Real.log ‖contourAverage (fieldAboveFrame true a ρ 0 (translateField h V) 0) c‖) =
      ∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
        Real.log ‖contourAverage (fieldAboveFrame true a ρ 0 V 0) c‖ := by
    rw [fieldAboveFrame_translate hM hw]
    refine Finset.sum_nbij' (fun c => (c.1 - h, c.2)) (fun c => (c.1 + h, c.2)) ?_ ?_ ?_ ?_ ?_
    · intro c hc
      obtain ⟨h3, h4⟩ := Finset.mem_filter.mp hc
      refine Finset.mem_filter.mpr ⟨(hM.innerBonds_translate h (c.1 - h, c.2)).mp (by simpa using h3), ?_⟩
      simp [h4]
    · intro c hc
      obtain ⟨h3, h4⟩ := Finset.mem_filter.mp hc
      exact Finset.mem_filter.mpr ⟨(hM.innerBonds_translate h c).mpr h3, by simp [h4]⟩
    · intro c _
      simp
    · intro c _
      simp
    · intro c _
      rw [hM.contourAverage_translate]
  have h3 : (∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y + h then
        haarLogRatio (coordsAboveFrame true a ρ 0 (translateField h V) 0 b.1.1 b.1.2) else 0) =
      ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
        haarLogRatio (coordsAboveFrame true a ρ 0 V 0 b.1.1 b.1.2) else 0 := by
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e1 := congrFun (congrFun (coordsAboveFrame_translate hM hw 0) (e b).1.1) (e b).1.2
    rw [map_zero] at e1
    have e2 : (e b).1.1 - cellCentre F.depth h = b.1.1 := by
      show b.1.1 + cellCentre F.depth h - cellCentre F.depth h = b.1.1
      simp
    have e3 : (e b).1.2 = b.1.2 := rfl
    have e4 : (enclosingCell b.1.1 + h = Y + h) ↔ enclosingCell b.1.1 = Y := add_left_inj h
    rw [hcell]
    simp only [e4]
    rw [e1, e2, e3]
  unfold ReferenceDensity.stepDensity
  rw [h1, h2, h3]
end Shift
end OnFrames
section AtABlockTorus
variable {F : BlockFrame}
private theorem sum_smul_imaginaryUnit (v : BondVector) : ∑ α, v α • imaginaryUnit α = toImaginary v := by
  apply Subtype.ext
  rw [Fin.sum_univ_three]
  refine Quaternion.ext _ _ ?_ ?_ ?_ ?_
  · show v 0 * 0 + v 1 * 0 + v 2 * 0 = 0
    ring
  · show v 0 * 1 + v 1 * 0 + v 2 * 0 = v 0
    ring
  · show v 0 * 0 + v 1 * 1 + v 2 * 0 = v 1
    ring
  · show v 0 * 0 + v 1 * 0 + v 2 * 1 = v 2
    ring
private theorem analyticAt_chartedEnergyAtMinimizer (hK : ChartEnergyKernelBound) {a : ℝ} {L : ℕ}
    {c : ColdChainParameters} (ha : 1 ≤ a) (hL : Odd L) (hL40 : 2 ^ 40 ≤ L) (hc : c.Admissible a L)
    (hF : IsBlockTorus L F) {ρ : ℝ} {V : F.GaugeField F.top}
    (hpt : IsAdmissibleChartPoint L c.σA (fun x i => stepFrame true a ρ 0 (x, i) V) V) :
    AnalyticAt ℝ (ReferenceDensity.chartedEnergyAtMinimizer a ρ V) 0 := by
  obtain ⟨Ck, -, hker⟩ := hK a L c ha hL hL40 hc
  let e := Fintype.equivFin (↥(chordBonds (finiteCells F)) × Fin 3)
  let q : Fin (Fintype.card (↥(chordBonds (finiteCells F)) × Fin 3)) → ChartDirection F :=
    fun n => Sum.inl ((e.symm n).1.1.1, (e.symm n).1.1.2, imaginaryUnit (e.symm n).2)
  have hf := (hker F _ V hF hpt _ q).1
  let P : StepVariable (finiteCells F) →L[ℝ] (Fin (Fintype.card (↥(chordBonds (finiteCells F)) × Fin 3)) → ℝ) :=
    ContinuousLinearMap.pi fun n =>
      (EuclideanSpace.proj (e.symm n).2 : BondVector →L[ℝ] ℝ).comp (ContinuousLinearMap.proj (e.symm n).1)
  have hP : ∀ (η : StepVariable (finiteCells F)) n, P η n = η (e.symm n).1 (e.symm n).2 := fun _ _ => rfl
  have heq : ReferenceDensity.chartedEnergyAtMinimizer a ρ V =
      chartRestriction a (fun x i => stepFrame true a ρ 0 (x, i) V) V q ∘ P := by
    funext η
    have hexp : expUnit (0 : imaginaryQuaternions) = 1 := Subtype.ext (by simp [expUnit])
    have e1 : leftTranslate (fun y i => ∑ l, P η l • directionMove (q l) y i) V = V := by
      funext y i
      have h0 : ∀ l, directionMove (q l) y i = 0 := fun _ => rfl
      simp only [leftTranslate, h0, smul_zero, Finset.sum_const_zero, hexp, one_mul]
    have e2 : ∀ (x : F.Site F.depth) (i : Fin 4),
        ∑ l, P η l • directionCoordinate (q l) x i = stepCoordinates η x i := by
      intro x i
      rw [← e.sum_comp]
      have g : ∀ k : ↥(chordBonds (finiteCells F)) × Fin 3, P η (e k) • directionCoordinate (q (e k)) x i =
          η k.1 k.2 • (if k.1.1.1 = x ∧ k.1.1.2 = i then imaginaryUnit k.2 else 0) := fun k => by
        have hq : q (e k) = Sum.inl (k.1.1.1, k.1.1.2, imaginaryUnit k.2) := by simp [q]
        rw [hq, hP]
        simp [directionCoordinate]
      simp only [g]
      rw [Fintype.sum_prod_type]
      unfold stepCoordinates
      by_cases hb : (x, i) ∈ chordBonds (finiteCells F)
      · rw [dif_pos hb, Finset.sum_eq_single (⟨(x, i), hb⟩ : ↥(chordBonds (finiteCells F)))]
        · simpa using sum_smul_imaginaryUnit _
        · intro b _ hne
          refine Finset.sum_eq_zero fun α _ => ?_
          rw [if_neg, smul_zero]
          rintro ⟨h1, h2⟩
          exact hne (Subtype.ext (Prod.ext h1 h2))
        · simp
      · rw [dif_neg hb]
        refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun α _ => ?_
        rw [if_neg, smul_zero]
        rintro ⟨h1, h2⟩
        apply hb
        have h3 : b.1 = (x, i) := Prod.ext h1 h2
        rw [← h3]
        exact b.2
    show chartedEnergy a (coordsAboveFrame true a ρ 0 V η) V = chartedEnergy a
      (fun x i => stepFrame true a ρ 0 (x, i) V + ∑ l, P η l • directionCoordinate (q l) x i)
      (leftTranslate (fun y i => ∑ l, P η l • directionMove (q l) y i) V)
    rw [e1]
    simp only [e2]
    rfl
  rw [heq]
  exact AnalyticAt.comp_of_eq hf (P.analyticAt 0) (map_zero P)
private theorem isSmallCurvature_of_isCold (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j ≤ F.top) {s : ℝ} {X : F.GaugeField j}
    (h : IsCold (finiteCells F) j s X) : IsSmallCurvature s X := by apply _root_.YangMills.SharedProofs.p16091 <;> assumption
private theorem minimizer_facts (hOL : MinimizingChartUnique) {a : ℝ} {L : ℕ} {c : ColdChainParameters}
    (hL : Odd L) (hc : c.Admissible a L) (hF : IsBlockTorus L F) {s : ℝ} (hs : 0 < s) (hsσ : s ≤ c.σA)
    {V : F.GaugeField F.top} (hV : IsSmallCurvature s V) :
    IsMinimizingChart a (finiteCells F) V c.ρA (minimizingCoordinates a (finiteCells F) V c.ρA) ∧
      (∀ w', IsMinimizingChart a (finiteCells F) V c.ρA w' → w' = minimizingCoordinates a (finiteCells F) V c.ρA) ∧
      (∀ b ∈ chordBonds (finiteCells F), ‖minimizingCoordinates a (finiteCells F) V c.ρA b.1 b.2‖ ≤ c.N 0 * s) ∧
      IsCold (finiteCells F) F.depth (s / 8) (chartedField (minimizingCoordinates a (finiteCells F) V c.ρA) V) := by
  have hodd : Odd F.blockSide := by
    rw [hF.1]
    exact hL
  obtain ⟨n, hn, hside⟩ := hF.2
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    omega
  have hcl := hc.estimates F s V hF hs hsσ hV
  obtain ⟨w, hw, hcold, -⟩ := hcl.minimizer
  have hρ1 := hc.classical.1.2.1
  have hwρ : IsMinimizingChart a (finiteCells F) V c.ρA w :=
    ⟨hw.1, fun b hb => (hw.2.1 b hb).trans (min_le_left _ _), hw.2.2⟩
  have hone := (hOL F a c.ρA (c.N 0) s V w hodd hs2 hρ1 hcl.minimizer hwρ).1
  have hex : ∃ w, IsMinimizingChart a (finiteCells F) V c.ρA w := ⟨w, hwρ⟩
  have hlc : minimizingCoordinates a (finiteCells F) V c.ρA = w := by
    unfold minimizingCoordinates
    rw [dif_pos hex]
    exact hone _ hex.choose_spec
  rw [hlc]
  exact ⟨hwρ, hone, fun b hb => (hw.2.1 b hb).trans (min_le_right _ _), hcold⟩
private theorem isAdmissibleChartPoint_minimizer {a : ℝ} {L : ℕ} {c : ColdChainParameters} (hF : IsBlockTorus L F)
    (hL : Odd L) {s : ℝ} (hs : 0 < s)
    (hsσ : s ≤ c.σA) (hsm : c.N 0 * s ≤ 1 / (64 * (L : ℝ))) {V : F.GaugeField F.top}
    (h1 : ∀ b ∈ chordBonds (finiteCells F), ‖minimizingCoordinates a (finiteCells F) V c.ρA b.1 b.2‖ ≤ c.N 0 * s)
    (h2 : IsCold (finiteCells F) F.depth (s / 8) (chartedField (minimizingCoordinates a (finiteCells F) V c.ρA) V)) :
    IsAdmissibleChartPoint L c.σA (fun x i => stepFrame true a c.ρA 0 (x, i) V) V := by
  have hodd : Odd F.blockSide := by
    rw [hF.1]
    exact hL
  obtain ⟨n, hn, hside⟩ := hF.2
  have hs1 : ∀ i, 0 < F.extent i := fun i => by
    rw [hside]
    omega
  have hfun : (fun x i => stepFrame true a c.ρA 0 (x, i) V) = minimizingCoordinates a (finiteCells F) V c.ρA := by
    funext x i
    simp [stepFrame, minimizingBondCoordinate]
  rw [hfun]
  exact ⟨fun b hb => (h1 b hb).trans hsm, fun p hp =>
    (isSmallCurvature_of_isCold hodd hs1 (Nat.le_succ _) h2 p hp).trans_le (by linarith)⟩
private theorem stepDensity_gauge_invariant (hOL : MinimizingChartUnique) (hK : ChartEnergyKernelBound)
    (hC : chartEquivarianceStatement) (hG : MinimalActionGaugeCovariance) {a : ℝ} {L : ℕ}
    {c : ColdChainParameters}
    (ha : 1 ≤ a) (hL : Odd L) (hL40 : 2 ^ 40 ≤ L) (hc : c.Admissible a L) (hF : IsBlockTorus L F) {s : ℝ}
    (hs : 0 < s) (hsσ : s ≤ c.σA) (hsm : c.N 0 * s ≤ 1 / (64 * (L : ℝ))) {V : F.GaugeField F.top}
    (hV : IsSmallCurvature s V) (γ : F.Cell → UnitQuaternion) (lam : ℝ) (Y : F.Cell) :
    ReferenceDensity.stepDensity a c.ρA lam Y (gaugeTransform γ V) = ReferenceDensity.stepDensity a c.ρA lam Y V := by
  have hodd : Odd F.blockSide := by
    rw [hF.1]
    exact hL
  obtain ⟨n, hn, hside⟩ := id hF.2
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    omega
  obtain ⟨hl, -, h1, h2⟩ := minimizer_facts hOL hL hc hF hs hsσ hV
  have hV' : IsSmallCurvature s (gaugeTransform γ V) := fun p hp => by
    rw [TorusContours.plaquetteDefect_gaugeTransform]
    exact hV p hp
  obtain ⟨-, hu, -, -⟩ := minimizer_facts hOL hL hc hF hs hsσ hV'
  have hw := hu _ (hG.2 F a c.ρA V _ γ hodd hs2 hl)
  exact stepDensity_gaugeTransform (hC F a hodd hs2) hw.symm
    (analyticAt_chartedEnergyAtMinimizer hK ha hL hL40 hc hF
      (isAdmissibleChartPoint_minimizer hF hL hs hsσ hsm h1 h2)) lam Y
private theorem stepDensity_translate_invariant (hOL : MinimizingChartUnique) (hC : chartEquivarianceStatement)
    (hT : TranslationOfMinimizingChart) {a : ℝ} {L : ℕ} {c : ColdChainParameters}
    (hL : Odd L) (hc : c.Admissible a L) (hF : IsBlockTorus L F) {s : ℝ} (hs : 0 < s)
    (hsσ : s ≤ c.σA) {V : F.GaugeField F.top} (hV : IsSmallCurvature s V)
    (h : F.Cell) (lam : ℝ) (Y : F.Cell) :
    ReferenceDensity.stepDensity a c.ρA lam (Y + h) (translateField h V) =
      ReferenceDensity.stepDensity a c.ρA lam Y V := by
  have hodd : Odd F.blockSide := by
    rw [hF.1]
    exact hL
  obtain ⟨n, hn, hside⟩ := id hF.2
  have hs2 : ∀ i, 2 ≤ F.extent i := fun i => by
    rw [hside]
    omega
  obtain ⟨hl, -, -, -⟩ := minimizer_facts hOL hL hc hF hs hsσ hV
  have hV' : IsSmallCurvature s (translateField h V) := by
    rintro ⟨x, μ, ν⟩ hp
    have hc' := hV (x - h, μ, ν) hp
    unfold plaquetteDefect at hc' ⊢
    have e : plaquetteHolonomy (translateField h V) (x, μ, ν) = plaquetteHolonomy V (x - h, μ, ν) := by
      simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false,
        translateField, add_sub_right_comm, sub_right_comm x (unitStep F.top μ) h,
        sub_right_comm x (unitStep F.top ν) h]
    rw [e]
    exact hc'
  obtain ⟨-, hu, -, -⟩ := minimizer_facts hOL hL hc hF hs hsσ hV'
  have hw := hu _ (hT.2.2 F a c.ρA V _ h hodd hs2 hl)
  exact stepDensity_translate (hC F a hodd hs2) hw.symm lam Y
end AtABlockTorus
theorem invariantAtAdmissibleParameters_of (hCl : AdmissibleParametersExist)
    (hOL : MinimizingChartUnique) (hK : ChartEnergyKernelBound)
    (hC : chartEquivarianceStatement) (hG : MinimalActionGaugeCovariance)
    (hT : TranslationOfMinimizingChart) : InvariantAtAdmissibleParameters := by
  intro T hD t n _ hn W hW
  obtain ⟨c, -, -, -, hρ, hσ, -, hN, hc⟩ :=
    hCl T.coupling T.δ₁ T.side T.lam T.ρA T.σA T.cg T.N hD.a_ge hD.L_odd hD.chain
  have hp : ∀ i, (TorusFields.torusFrame T.side t n).period (TorusFields.torusFrame T.side t n).top i = n :=
    fun i => TopLevelSites.period_top i
  have hF : IsBlockTorus T.side (TorusFields.torusFrame T.side t n) := ⟨rfl, n, hn, fun _ => rfl⟩
  have hs : 0 < T.threshold := hD.σ_pos
  have hsσ : T.threshold ≤ c.σA := by
    rw [hσ]
    linarith [hD.σ_le]
  have hLpos : (0 : ℝ) < T.side := by
    have : 0 < T.side := hD.L_odd.pos
    exact_mod_cast this
  have hN0 : 0 < T.N 0 := hD.chain.2.2.2.2.2.2.2.1 0
  have hsm : c.N 0 * T.threshold ≤ 1 / (64 * (T.side : ℝ)) := by
    rw [hN, le_div_iff₀ (by positivity)]
    have h1 := hD.σ_L
    have h2 : 0 ≤ (960 * T.N 0 + 1024) * ((T.side : ℝ) * T.threshold) := by positivity
    nlinarith
  have hcold : IsSmallCurvature (F := TorusFields.torusFrame T.side t n) T.threshold
      (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top W) := by
    rintro ⟨x, μ, ν⟩ hlt
    rw [TopLevelSites.plaquetteDefect_readAtLevel_eq hp]
    exact hW _ μ ν hlt
  refine ⟨fun y g => ?_, fun y u => ?_⟩
  · have e : TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top
          (TorusFields.gaugeTransform g W) =
        gaugeTransform (fun z => g (TorusLumps.toTorusSite n z))
          (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top W) := by
      funext x i
      show g (TorusLumps.toTorusSite n x) * W (TorusLumps.toTorusSite n x) i *
          (g (TorusLumps.toTorusSite n x + TorusFields.unitStep n i))⁻¹ =
        g (TorusLumps.toTorusSite n x) * W (TorusLumps.toTorusSite n x) i *
          (g (TorusLumps.toTorusSite n (x + unitStep (TorusFields.torusFrame T.side t n).top i)))⁻¹
      rw [TopLevelSites.toTorusSite_add hp, TopLevelSites.toTorusSite_unitStep hp]
    show ReferenceDensity.stepDensity T.coupling T.ρA T.lam _
        (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top
          (TorusFields.gaugeTransform g W)) =
      ReferenceDensity.stepDensity T.coupling T.ρA T.lam _
        (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top W)
    rw [e, ← hρ]
    exact stepDensity_gauge_invariant hOL hK hC hG hD.a_ge hD.L_odd hD.L_ge hc hF hs hsσ hsm hcold _ _ _
  · have e : TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top
          (TorusFields.translate u W) =
        translateField
          (-StepCosts.torusSiteInFrame (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top u)
          (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top W) := by
      funext x i
      show W (TorusLumps.toTorusSite n x + u) i = W (TorusLumps.toTorusSite n
        (x - -StepCosts.torusSiteInFrame (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top u)) i
      rw [sub_neg_eq_add, TopLevelSites.toTorusSite_add hp, TopLevelSites.toTorusSite_torusSiteInFrame hp]
    have e2 : StepCosts.torusSiteInFrame (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top y =
        StepCosts.torusSiteInFrame (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top (y + u) +
          -StepCosts.torusSiteInFrame (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top u := by
      rw [TopLevelSites.torusSiteInFrame_add hp]
      abel
    show ReferenceDensity.stepDensity T.coupling T.ρA T.lam
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top y)
        (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top
          (TorusFields.translate u W)) =
      ReferenceDensity.stepDensity T.coupling T.ρA T.lam
        (StepCosts.torusSiteInFrame (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top (y + u))
        (TorusFields.readAtLevel (TorusFields.torusFrame T.side t n) (TorusFields.torusFrame T.side t n).top W)
    rw [e, e2, ← hρ]
    exact stepDensity_translate_invariant hOL hC hT hD.L_odd hc hF hs hsσ hcold _ _ _
end YangMills.Construction.StepDensity
end
