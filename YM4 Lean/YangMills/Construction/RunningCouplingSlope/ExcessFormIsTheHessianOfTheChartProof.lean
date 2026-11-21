import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.ClusterExpansionOfAStep.ShareOfAChainSplitsProof
import YangMills.Construction.ColdChainAtEveryLevel.LeastQuarticGaugeProof
import YangMills.Construction.ColdStepAtMirrorFrames.ChartEnergyInCoordinatesProof
import YangMills.Construction.ColdStepAtMirrorFrames.CovarianceOfAConvexMeasureProof
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionIsGaugeInvariant
import YangMills.Construction.RunningCouplingSlope.ExcessFormIsTheHessianOfTheChart
import YangMills.Construction.RunningCouplingSlope.ExcessOfAStepIsTwiceDifferentiable
import YangMills.Construction.RunningCouplingSlope.LeastFieldNearTheFlatField
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeOfTheExcessReadsTheVelocities
import YangMills.Construction.RunningCouplingSlope.SecondVariationOfAPartialMinimum
import YangMills.Construction.SummableBoundsOfTheFlow.MoveOfTheTopAlongItsFieldProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
namespace ExcessHessianChart
open BlockAverages ReferenceDensity
open ColdStepAtMirrorFrames hiding bondSpread
open TorusFields hiding unitStep
private theorem quatExp_neg_mul (q : ℍ[ℝ]) : NormedSpace.exp (-q) * NormedSpace.exp q = 1 := by
  have hr : ∀ p : ℍ[ℝ], p ∈ Metric.eball (0 : ℍ[ℝ]) (NormedSpace.expSeries ℝ ℍ[ℝ]).radius := fun p => by
    rw [NormedSpace.expSeries_radius_eq_top]
    simp
  rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (Commute.neg_left (Commute.refl q)) (hr _) (hr _),
    neg_add_cancel, NormedSpace.exp_zero]
private theorem quatExp_contDiffAt (q : ℍ[ℝ]) : ContDiffAt ℝ 2 (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) q :=
  (NormedSpace.exp_analytic (𝕂 := ℝ) q).contDiffAt
private theorem quatExp_hasFDerivAt (q : ℍ[ℝ]) :
    HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (fderiv ℝ NormedSpace.exp q) q :=
  ((quatExp_contDiffAt q).differentiableAt (by norm_num)).hasFDerivAt
private theorem hasDerivAt_quatExp_line (w x : ℍ[ℝ]) :
    HasDerivAt (fun r : ℝ => NormedSpace.exp (w + r • x)) (fderiv ℝ NormedSpace.exp w x) 0 := by
  have h : HasDerivAt (fun r : ℝ => w + r • x) x 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const x).const_add w
  have h2 : HasFDerivAt (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) (fderiv ℝ NormedSpace.exp w) (w + (0 : ℝ) • x) := by
    simpa using quatExp_hasFDerivAt w
  exact h2.comp_hasDerivAt (0 : ℝ) h
private theorem expLeftDeriv_eq (w x : ℍ[ℝ]) :
    expLeftDeriv w x = fderiv ℝ NormedSpace.exp w x * NormedSpace.exp (-w) := by
  unfold expLeftDeriv
  exact ((hasDerivAt_quatExp_line w x).mul_const _).deriv
private theorem expLeftDeriv_add (w x y : ℍ[ℝ]) :
    expLeftDeriv w (x + y) = expLeftDeriv w x + expLeftDeriv w y := by
  simp only [expLeftDeriv_eq, map_add, add_mul]
private theorem expLeftDeriv_smul (w x : ℍ[ℝ]) (c : ℝ) :
    expLeftDeriv w (c • x) = c • expLeftDeriv w x := by
  simp only [expLeftDeriv_eq, map_smul, smul_mul_assoc]
private theorem hasDerivAt_expChord (w x : ℍ[ℝ]) :
    HasDerivAt (fun r : ℝ => NormedSpace.exp (w + r • x)) (expLeftDeriv w x * NormedSpace.exp w) 0 := by
  rw [expLeftDeriv_eq, mul_assoc, quatExp_neg_mul, mul_one]
  exact hasDerivAt_quatExp_line w x
private theorem hasDerivAt_quatExp_smul (q : ℍ[ℝ]) :
    HasDerivAt (fun r : ℝ => NormedSpace.exp (r • q)) q 0 := by
  have := hasDerivAt_exp_smul_const (𝕂 := ℝ) q (0 : ℝ)
  simpa using this
private theorem contDiffAt_quatExp_comp {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
    {f : Y → ℍ[ℝ]} (h : ContDiffAt ℝ 2 f y₀) :
    ContDiffAt ℝ 2 (fun y => NormedSpace.exp (f y)) y₀ :=
  (quatExp_contDiffAt (f y₀)).comp y₀ h
private theorem coe_expUnit (w : imaginaryQuaternions) :
    ((expUnit w : UnitQuaternion) : ℍ[ℝ]) = NormedSpace.exp (w : ℍ[ℝ]) := rfl
private theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem expUnit_inv (w : imaginaryQuaternions) : (expUnit w)⁻¹ = expUnit (-w) := by apply _root_.YangMills.Construction.LeastQuarticGauge.expUnit_inv <;> assumption
private theorem coe_inv_mul_self (g : UnitQuaternion) : (((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) * (g : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_inv_mul_coe <;> assumption
private theorem re_eq_zero_of_unit_curve {Z : ℝ → UnitQuaternion} {q : ℍ[ℝ]}
    (h : HasDerivAt (fun r => (Z r : ℍ[ℝ])) (q * (Z 0 : ℍ[ℝ])) 0) : q.re = 0 := by
  have h2 := h.inner ℝ h
  have hc : (fun r => inner ℝ (Z r : ℍ[ℝ]) (Z r : ℍ[ℝ])) = fun _ => (1 : ℝ) := by
    funext r
    rw [Quaternion.inner_def, Unitary.mul_star_self_of_mem (Z r).2]
    simp
  have h3 : HasDerivAt (fun r => inner ℝ (Z r : ℍ[ℝ]) (Z r : ℍ[ℝ])) (0 : ℝ) 0 := by
    rw [hc]
    exact hasDerivAt_const _ _
  have h4 := h2.unique h3
  have e' : (Z 0 : ℍ[ℝ]) * star ((Z 0 : ℍ[ℝ])) = 1 := Unitary.mul_star_self_of_mem (Z 0).2
  have h5 : inner ℝ (q * (Z 0 : ℍ[ℝ])) (Z 0 : ℍ[ℝ]) = q.re := by
    rw [Quaternion.inner_def, mul_assoc, e', mul_one]
  rw [real_inner_comm, h5] at h4
  linarith
private theorem quaternion_ext_of_components {p q : ℍ[ℝ]} (h0 : p.re = q.re)
    (h : ∀ α, imaginaryComponents p α = imaginaryComponents q α) : p = q := by
  have h1 := h 0
  have h2 := h 1
  have h3 := h 2
  simp [imaginaryComponents] at h1 h2 h3
  exact Quaternion.ext _ _ h0 h1 h2 h3
variable {F : BlockFrame}
private def gaugePath (γ : F.Site F.depth → imaginaryQuaternions) (r : ℝ) : F.Site F.depth → UnitQuaternion :=
  fun y => expUnit (r • (-γ y))
private def chartPath (w ξ : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (r : ℝ) : F.GaugeField F.depth :=
  chartedField (fun y i => w y i + r • ξ y i) (rotatedField (r • v) V)
private def fieldPath (γ : F.Site F.depth → imaginaryQuaternions) (w ξ : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (r : ℝ) : F.GaugeField F.depth :=
  BlockAverages.gaugeTransform (gaugePath γ r) (chartPath w ξ v V r)
open Classical in
private def chartLeftVelocity (w ξ : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (y : F.Site F.depth) (i : Fin 4) : ℍ[ℝ] :=
  if IsCrossingBond (y, i) then
    expLeftDeriv (w y i) (ξ y i) + NormedSpace.exp (w y i : ℍ[ℝ]) * (v (enclosingCell y) i : ℍ[ℝ]) *
      NormedSpace.exp (-(w y i : ℍ[ℝ]))
  else if IsAxialTreeBond (y, i) then 0 else expLeftDeriv (w y i) (ξ y i)
private theorem rotatedField_zero (V : F.GaugeField F.top) :
    rotatedField (0 : F.Site F.top → Fin 4 → imaginaryQuaternions) V = V := by
  funext y i
  simp [rotatedField, expUnit_zero]
private theorem chartPath_zero (w ξ : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) :
    chartPath w ξ v V 0 = chartedField w V := by
  simp [chartPath, zero_smul, rotatedField_zero]
private theorem fieldPath_zero (γ : F.Site F.depth → imaginaryQuaternions)
    (w ξ : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) :
    fieldPath γ w ξ v V 0 = chartedField w V := by
  funext y i
  simp [fieldPath, BlockAverages.gaugeTransform, gaugePath, chartPath_zero, zero_smul, expUnit_zero]
private theorem hasDerivAt_chartPath (w ξ : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (y : F.Site F.depth) (i : Fin 4) :
    HasDerivAt (fun r => ((chartPath w ξ v V r y i : UnitQuaternion) : ℍ[ℝ]))
      (chartLeftVelocity w ξ v y i * ((chartedField w V y i : UnitQuaternion) : ℍ[ℝ])) 0 := by
  classical
  by_cases hc : IsCrossingBond (y, i)
  · have e : (fun r => ((chartPath w ξ v V r y i : UnitQuaternion) : ℍ[ℝ])) = fun r : ℝ =>
        NormedSpace.exp ((w y i : ℍ[ℝ]) + r • (ξ y i : ℍ[ℝ])) *
          (NormedSpace.exp (r • (v (enclosingCell y) i : ℍ[ℝ])) *
            ((V (enclosingCell y) i : UnitQuaternion) : ℍ[ℝ])) := by
      funext r
      simp [chartPath, chartedField, if_pos hc, rotatedField, coe_expUnit]
    rw [e]
    have h1 := hasDerivAt_expChord (w y i : ℍ[ℝ]) (ξ y i : ℍ[ℝ])
    have h2 := (hasDerivAt_quatExp_smul (v (enclosingCell y) i : ℍ[ℝ])).mul_const
      ((V (enclosingCell y) i : UnitQuaternion) : ℍ[ℝ])
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    simp only [chartLeftVelocity, chartedField, if_pos hc, zero_smul, add_zero, NormedSpace.exp_zero, one_mul,
      Submonoid.coe_mul, coe_expUnit]
    have e1 := quatExp_neg_mul (w y i : ℍ[ℝ])
    set E := NormedSpace.exp (w y i : ℍ[ℝ])
    set E' := NormedSpace.exp (-(w y i : ℍ[ℝ]))
    set T := expLeftDeriv (w y i : ℍ[ℝ]) (ξ y i : ℍ[ℝ])
    set U := (v (enclosingCell y) i : ℍ[ℝ])
    set Vq := ((V (enclosingCell y) i : UnitQuaternion) : ℍ[ℝ])
    symm
    calc (T + E * U * E') * (E * Vq) = T * E * Vq + E * U * (E' * E) * Vq := by noncomm_ring
      _ = T * E * Vq + E * (U * Vq) := by rw [e1]; noncomm_ring
  · by_cases ht : IsAxialTreeBond (y, i)
    · have e : (fun r => ((chartPath w ξ v V r y i : UnitQuaternion) : ℍ[ℝ])) = fun _ => 1 := by
        funext r
        simp [chartPath, chartedField, if_neg hc, if_pos ht]
      rw [e]
      simpa [chartLeftVelocity, if_neg hc, if_pos ht] using hasDerivAt_const (0 : ℝ) (1 : ℍ[ℝ])
    · have e : (fun r => ((chartPath w ξ v V r y i : UnitQuaternion) : ℍ[ℝ])) = fun r : ℝ =>
          NormedSpace.exp ((w y i : ℍ[ℝ]) + r • (ξ y i : ℍ[ℝ])) := by
        funext r
        simp [chartPath, chartedField, if_neg hc, if_neg ht, coe_expUnit]
      rw [e]
      simpa [chartLeftVelocity, chartedField, if_neg hc, if_neg ht, coe_expUnit] using
        hasDerivAt_expChord (w y i : ℍ[ℝ]) (ξ y i : ℍ[ℝ])
private theorem coe_fieldPath (γ : F.Site F.depth → imaginaryQuaternions)
    (w ξ : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (r : ℝ)
    (y : F.Site F.depth) (i : Fin 4) :
    ((fieldPath γ w ξ v V r y i : UnitQuaternion) : ℍ[ℝ]) =
      NormedSpace.exp (r • (-(γ y : ℍ[ℝ]))) * ((chartPath w ξ v V r y i : UnitQuaternion) : ℍ[ℝ]) *
        NormedSpace.exp (r • (γ (y + unitStep F.depth i) : ℍ[ℝ])) := by
  simp only [fieldPath, BlockAverages.gaugeTransform, gaugePath, expUnit_inv, Submonoid.coe_mul, coe_expUnit]
  simp
private theorem hasDerivAt_fieldPath (γ : F.Site F.depth → imaginaryQuaternions)
    (w ξ : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (y : F.Site F.depth) (i : Fin 4) :
    HasDerivAt (fun r => ((fieldPath γ w ξ v V r y i : UnitQuaternion) : ℍ[ℝ]))
      ((chartLeftVelocity w ξ v y i + covariantDifference (chartedField w V) γ (y, i)) *
        ((chartedField w V y i : UnitQuaternion) : ℍ[ℝ])) 0 := by
  have e : (fun r => ((fieldPath γ w ξ v V r y i : UnitQuaternion) : ℍ[ℝ])) = fun r =>
      NormedSpace.exp (r • (-(γ y : ℍ[ℝ]))) * ((chartPath w ξ v V r y i : UnitQuaternion) : ℍ[ℝ]) *
        NormedSpace.exp (r • (γ (y + unitStep F.depth i) : ℍ[ℝ])) := by
    funext r
    exact coe_fieldPath γ w ξ v V r y i
  rw [e]
  have h := ((hasDerivAt_quatExp_smul (-(γ y : ℍ[ℝ]))).mul (hasDerivAt_chartPath w ξ v V y i)).mul
    (hasDerivAt_quatExp_smul (γ (y + unitStep F.depth i) : ℍ[ℝ]))
  refine h.congr_deriv ?_
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, chartPath_zero, covariantDifference,
    Pi.mul_apply]
  have e1 := coe_inv_mul_self (chartedField w V y i)
  set W := ((chartedField w V y i : UnitQuaternion) : ℍ[ℝ])
  set W' := (((chartedField w V y i)⁻¹ : UnitQuaternion) : ℍ[ℝ])
  set T := chartLeftVelocity w ξ v y i
  set g := (γ y : ℍ[ℝ])
  set g' := (γ (y + unitStep F.depth i) : ℍ[ℝ])
  symm
  calc (T + (W * g' * W' - g)) * W = T * W + W * g' * (W' * W) - g * W := by noncomm_ring
    _ = -g * W + T * W + W * g' := by rw [e1]; noncomm_ring
private theorem contDiffAt_quatExp_smul (q : ℍ[ℝ]) :
    ContDiffAt ℝ 2 (fun r : ℝ => NormedSpace.exp (r • q)) 0 :=
  contDiffAt_quatExp_comp (contDiffAt_id.smul contDiffAt_const)
private theorem contDiffAt_fieldPath (γ : F.Site F.depth → imaginaryQuaternions)
    (w ξ : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (y : F.Site F.depth) (i : Fin 4) :
    ContDiffAt ℝ 2 (fun r => ((fieldPath γ w ξ v V r y i : UnitQuaternion) : ℍ[ℝ])) 0 := by
  classical
  have e : (fun r => ((fieldPath γ w ξ v V r y i : UnitQuaternion) : ℍ[ℝ])) = fun r =>
      NormedSpace.exp (r • (-(γ y : ℍ[ℝ]))) * ((chartPath w ξ v V r y i : UnitQuaternion) : ℍ[ℝ]) *
        NormedSpace.exp (r • (γ (y + unitStep F.depth i) : ℍ[ℝ])) := by
    funext r
    exact coe_fieldPath γ w ξ v V r y i
  rw [e]
  refine ((contDiffAt_quatExp_smul _).mul ?_).mul (contDiffAt_quatExp_smul _)
  have hl : ContDiffAt ℝ 2 (fun r : ℝ => NormedSpace.exp ((w y i : ℍ[ℝ]) + r • (ξ y i : ℍ[ℝ]))) 0 :=
    contDiffAt_quatExp_comp (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  by_cases hc : IsCrossingBond (y, i)
  · have e2 : (fun r => ((chartPath w ξ v V r y i : UnitQuaternion) : ℍ[ℝ])) = fun r : ℝ =>
        NormedSpace.exp ((w y i : ℍ[ℝ]) + r • (ξ y i : ℍ[ℝ])) *
          (NormedSpace.exp (r • (v (enclosingCell y) i : ℍ[ℝ])) *
            ((V (enclosingCell y) i : UnitQuaternion) : ℍ[ℝ])) := by
      funext r
      simp [chartPath, chartedField, if_pos hc, rotatedField, coe_expUnit]
    rw [e2]
    exact hl.mul ((contDiffAt_quatExp_smul _).mul contDiffAt_const)
  · by_cases ht : IsAxialTreeBond (y, i)
    · have e2 : (fun r => ((chartPath w ξ v V r y i : UnitQuaternion) : ℍ[ℝ])) = fun _ => 1 := by
        funext r
        simp [chartPath, chartedField, if_neg hc, if_pos ht]
      rw [e2]
      exact contDiffAt_const
    · have e2 : (fun r => ((chartPath w ξ v V r y i : UnitQuaternion) : ℍ[ℝ])) = fun r : ℝ =>
          NormedSpace.exp ((w y i : ℍ[ℝ]) + r • (ξ y i : ℍ[ℝ])) := by
        funext r
        simp [chartPath, chartedField, if_neg hc, if_neg ht, coe_expUnit]
      rw [e2]
      exact hl
private theorem refineSite_eq (y : F.Site (F.depth + 1)) : refineSite y = cellCentre F.depth y := by apply _root_.YangMills.Construction.GaugeFixing.refineSite_eq_cellCentre <;> assumption
private theorem gaugeTransform_one {j : ℕ} (X : F.GaugeField j) :
    BlockAverages.gaugeTransform (fun _ => (1 : UnitQuaternion)) X = X := by apply _root_.YangMills.Construction.GaugedCriticality.gaugeTransform_one <;> assumption
private theorem excessEnergy_gaugeTransform (hLA : MinimalActionGaugeInvariant)
    (hGC : gaugeCovarianceStatement) (hL : 0 < F.blockSide) (a : ℝ) (g : F.Site F.depth → UnitQuaternion)
    (hg : ∀ z : F.Cell, g (cellCentre F.depth z) = 1) (W : F.GaugeField F.depth) (V : F.GaugeField F.top) :
    excessEnergy a (BlockAverages.gaugeTransform g W) V = excessEnergy a W V := by
  unfold excessEnergy blockEnergy
  rw [hLA F a (finiteCells F) F.depth (by simp) hL g W]
  congr 2
  refine congrArg (a * ·) (Finset.sum_congr rfl fun c _ => ?_)
  have h := (hGC F F.depth (by simp) hL).2.2.2 g (fun _ => 1) W V c
    (by rw [refineSite_eq]; exact hg _) (by rw [refineSite_eq]; exact hg _)
  rwa [gaugeTransform_one] at h
private def toEuclid (u : imaginaryQuaternions) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (imaginaryComponents (u : ℍ[ℝ]))
private theorem toImaginary_toEuclid (u : imaginaryQuaternions) : toImaginary (toEuclid u) = u := by
  apply Subtype.ext
  have h : (u : ℍ[ℝ]).re = 0 := u.2
  apply Quaternion.ext <;> simp [toImaginary, toEuclid, imaginaryComponents, h]
private theorem toImaginary_zero : toImaginary 0 = 0 := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
private theorem toImaginary_add (u v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (u + v) = toImaginary u + toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
private theorem toImaginary_smul (c : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (c • u) = c • toImaginary u := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_smul <;> assumption
private theorem imaginaryComponents_add (p q : ℍ[ℝ]) (α : Fin 3) :
    imaginaryComponents (p + q) α = imaginaryComponents p α + imaginaryComponents q α := by
  fin_cases α <;> simp [imaginaryComponents]
private theorem imaginaryComponents_smul (c : ℝ) (p : ℍ[ℝ]) (α : Fin 3) :
    imaginaryComponents (c • p) α = c * imaginaryComponents p α := by
  fin_cases α <;> simp [imaginaryComponents]
private def toImaginaryCLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (toImaginary v : ℍ[ℝ])
      map_add' := fun u v => by rw [toImaginary_add]; rfl
      map_smul' := fun c u => by rw [toImaginary_smul]; rfl }
private theorem toImaginaryCLM_apply (v : EuclideanSpace ℝ (Fin 3)) :
    toImaginaryCLM v = (toImaginary v : ℍ[ℝ]) := rfl
private theorem toEuclid_add (u v : imaginaryQuaternions) : toEuclid (u + v) = toEuclid u + toEuclid v := by
  ext α
  simp only [toEuclid, Submodule.coe_add, PiLp.add_apply]
  exact imaginaryComponents_add _ _ α
private theorem toEuclid_smul (c : ℝ) (u : imaginaryQuaternions) : toEuclid (c • u) = c • toEuclid u := by
  ext α
  simp only [toEuclid, Submodule.coe_smul, PiLp.smul_apply, smul_eq_mul]
  exact imaginaryComponents_smul _ _ α
private def toEuclidCLM : imaginaryQuaternions →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearMap.toContinuousLinearMap
    { toFun := toEuclid
      map_add' := toEuclid_add
      map_smul' := toEuclid_smul }
private theorem stepCoordinates_zero : stepCoordinates (0 : StepVariable (finiteCells F)) = 0 := by
  funext x i
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · simp [stepCoordinates, dif_pos h, toImaginary_zero]
  · simp [stepCoordinates, dif_neg h]
private theorem stepCoordinates_smul (c : ℝ) (η : StepVariable (finiteCells F)) :
    stepCoordinates (c • η) = c • stepCoordinates η := by
  funext x i
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · simp [stepCoordinates, dif_pos h, toImaginary_smul]
  · simp [stepCoordinates, dif_neg h]
private theorem contDiff_stepCoordinates (x : F.Site F.depth) (i : Fin 4) :
    ContDiff ℝ 2 (fun η : StepVariable (finiteCells F) => (stepCoordinates η x i : ℍ[ℝ])) := by
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · have e : (fun η : StepVariable (finiteCells F) => (stepCoordinates η x i : ℍ[ℝ])) =
        fun η => toImaginaryCLM (η ⟨(x, i), h⟩) := by
      funext η
      simp [stepCoordinates, dif_pos h, toImaginaryCLM_apply]
    rw [e]
    exact toImaginaryCLM.contDiff.comp (contDiff_apply ℝ _ _)
  · have e : (fun η : StepVariable (finiteCells F) => (stepCoordinates η x i : ℍ[ℝ])) = fun _ => 0 := by
      funext η
      simp [stepCoordinates, dif_neg h]
    rw [e]
    exact contDiff_const
private abbrev topDimension (F : BlockFrame) : ℕ := Fintype.card (TopCoord F)
private def topCoordEquiv (F : BlockFrame) : TopCoord F ≃ Fin (topDimension F) := Fintype.equivFin _
private def imaginaryUnit (α : Fin 3) : imaginaryQuaternions := toImaginary (EuclideanSpace.single α 1)
private def topRotation (σ : Fin (topDimension F) → ℝ) : F.Site F.top → Fin 4 → imaginaryQuaternions :=
  bondSpread (fun l => ((topCoordEquiv F).symm l).1.1) (fun l => imaginaryUnit ((topCoordEquiv F).symm l).2) σ
private def rotationCoords (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : Fin (topDimension F) → ℝ :=
  fun l => topCoords v ((topCoordEquiv F).symm l)
private theorem topRotation_rotationCoords (hTop : ∀ y i, (y, i) ∈ innerBonds (finiteCells F) F.top)
    (v : F.Site F.top → Fin 4 → imaginaryQuaternions) : topRotation (rotationCoords v) = v := by
  funext y i
  have hb := hTop y i
  unfold topRotation bondSpread rotationCoords
  rw [← Equiv.sum_comp (topCoordEquiv F)]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (⟨(y, i), hb⟩ : ↥(innerBonds (finiteCells F) F.top))]
  · simp only [if_true]
    rw [Fin.sum_univ_three]
    simp only [imaginaryUnit]
    rw [← toImaginary_smul, ← toImaginary_smul, ← toImaginary_smul, ← toImaginary_add, ← toImaginary_add]
    conv_rhs => rw [← toImaginary_toEuclid (v y i)]
    congr 1
    ext α
    fin_cases α <;> simp [toEuclid, topCoords, imaginaryComponents]
  · intro b _ hne
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [if_neg]
    intro h
    exact hne (Subtype.ext h)
  · intro h
    exact absurd (Finset.mem_univ _) h
private theorem topRotation_zero : topRotation (0 : Fin (topDimension F) → ℝ) = 0 := by
  funext y i
  simp [topRotation, bondSpread]
private theorem topRotation_add (σ τ : Fin (topDimension F) → ℝ) (y : F.Site F.top) (i : Fin 4) :
    topRotation (σ + τ) y i = topRotation σ y i + topRotation τ y i := by
  simp only [topRotation, bondSpread, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp [add_smul]
private theorem topRotation_smul (c : ℝ) (σ : Fin (topDimension F) → ℝ) (y : F.Site F.top) (i : Fin 4) :
    topRotation (c • σ) y i = c • topRotation σ y i := by
  simp only [topRotation, bondSpread, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp [mul_smul]
private theorem contDiff_topRotation (y : F.Site F.top) (i : Fin 4) :
    ContDiff ℝ 2 (fun σ : Fin (topDimension F) → ℝ => (topRotation σ y i : ℍ[ℝ])) := by
  have e : (fun σ : Fin (topDimension F) → ℝ => (topRotation σ y i : ℍ[ℝ])) = fun σ =>
      ∑ l, if ((topCoordEquiv F).symm l).1.1 = (y, i) then
        σ l • (imaginaryUnit ((topCoordEquiv F).symm l).2 : ℍ[ℝ]) else 0 := by
    funext σ
    simp only [topRotation, bondSpread]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  rw [e]
  refine ContDiff.sum fun l _ => ?_
  split_ifs
  · exact (contDiff_apply ℝ ℝ l).smul contDiff_const
  · exact contDiff_const
private theorem minimalAction_eq {a ρ : ℝ} {V : F.GaugeField F.top}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h : IsMinimizingChart a (finiteCells F) V ρ w) :
    minimalAction a (finiteCells F) F.top V = blockEnergy a (finiteCells F) F.depth (chartedField w V) V := by
  have hm := h.2.2
  show (⨅ W : F.GaugeField F.depth, blockEnergy a (finiteCells F) F.depth W V) = _
  refine le_antisymm (ciInf_le (f := fun W => blockEnergy a (finiteCells F) F.depth W V)
    ⟨blockEnergy a (finiteCells F) F.depth (chartedField w V) V, ?_⟩ (chartedField w V)) (le_ciInf hm)
  rintro _ ⟨W, rfl⟩
  exact hm W
private theorem excessEnergy_minimizer {a ρ : ℝ} {V : F.GaugeField F.top}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h : IsMinimizingChart a (finiteCells F) V ρ w) : excessEnergy a (chartedField w V) V = 0 := by
  unfold excessEnergy
  rw [minimalAction_eq h, sub_self]
private theorem excessEnergy_nonneg {a ρ : ℝ} {V : F.GaugeField F.top}
    {w : F.Site F.depth → Fin 4 → imaginaryQuaternions}
    (h : IsMinimizingChart a (finiteCells F) V ρ w) (W : F.GaugeField F.depth) :
    0 ≤ excessEnergy a W V := by
  unfold excessEnergy
  rw [minimalAction_eq h, sub_nonneg]
  exact h.2.2 W
private theorem eventually_differentiableAt_of_contDiffAt {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : Y → ℝ} {y₀ : Y} (hf : ContDiffAt ℝ 2 f y₀) : ∀ᶠ y in 𝓝 y₀, DifferentiableAt ℝ f y := by
  filter_upwards [hf.eventually (by simp)] with y hy
  exact hy.differentiableAt (by norm_num)
private theorem hasFDerivAt_fderiv_of_contDiffAt {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : Y → ℝ} {y₀ : Y} (hf : ContDiffAt ℝ 2 f y₀) :
    HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y₀) y₀ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GridBochner.hasFDerivAt_fderiv_of_contDiffAt <;> assumption
private theorem deriv_deriv_along_line {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : Y → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (p : Y) :
    deriv (deriv fun r : ℝ => f (r • p)) 0 = fderiv ℝ (fderiv ℝ f) 0 p p := by
  have hline : ∀ r : ℝ, HasDerivAt (fun r : ℝ => r • p) p r := fun r => by
    simpa using (hasDerivAt_id r).smul_const p
  have hc : Tendsto (fun r : ℝ => r • p) (𝓝 0) (𝓝 0) := by
    have := (hline 0).continuousAt.tendsto
    simpa using this
  have hev : deriv (fun r : ℝ => f (r • p)) =ᶠ[𝓝 0] fun r => fderiv ℝ f (r • p) p := by
    filter_upwards [hc.eventually (eventually_differentiableAt_of_contDiffAt hf)] with r hr
    exact (hr.hasFDerivAt.comp_hasDerivAt r (hline r)).deriv
  rw [hev.deriv_eq]
  have hH : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) ((0 : ℝ) • p) := by
    simpa using hasFDerivAt_fderiv_of_contDiffAt hf
  have h1 := hH.comp_hasDerivAt (0 : ℝ) (hline 0)
  have h2 := h1.clm_apply (hasDerivAt_const (0 : ℝ) p)
  have h3 := h2.deriv
  simpa using h3
private theorem fderiv_inl_eq_zero_of_isMin {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {E : A × B → ℝ} {x : A} {y : B}
    (hd : DifferentiableAt ℝ E (x, y)) (hmin : ∀ e, E (x, y) ≤ E (e, y)) (e : A) :
    fderiv ℝ E (x, y) (e, 0) = 0 := by
  have h1 : HasDerivAt (fun r : ℝ => x + r • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have h2 : HasDerivAt (fun r : ℝ => (x + r • e, y)) (e, (0 : B)) 0 :=
    h1.prodMk (hasDerivAt_const _ _)
  have hE : HasFDerivAt E (fderiv ℝ E (x, y)) (x + (0 : ℝ) • e, y) := by
    simpa using hd.hasFDerivAt
  have h3 := hE.comp_hasDerivAt (0 : ℝ) h2
  have hl : IsLocalMin (E ∘ fun r : ℝ => (x + r • e, y)) 0 := by
    refine Eventually.of_forall fun r => ?_
    simpa using hmin (x + r • e)
  exact hl.hasDerivAt_eq_zero h3
private def stepPointOf (x : ChartCoord F → ℝ) : StepVariable (finiteCells F) :=
  fun b => WithLp.toLp 2 fun c => x (b, c)
private theorem stepPointOf_eq (x : ChartCoord F → ℝ) :
    stepPointOf x = ∑ i : ChartCoord F, x i • bondVariation i.1 (EuclideanSpace.single i.2 (1 : ℝ)) := by
  funext b
  ext c
  simp only [Finset.sum_apply, Pi.smul_apply, bondVariation]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · rw [Fin.sum_univ_three]
    fin_cases c <;> simp [stepPointOf]
  · intro b' _ hb
    refine Finset.sum_eq_zero fun d _ => ?_
    simp [Pi.single_eq_of_ne hb.symm]
  · simp
private theorem second_fderiv_eq_chartedHessian_form {a ρ : ℝ} {V : F.GaugeField F.top} {B : Type}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {E : StepVariable (finiteCells F) × B → ℝ} (hE : ContDiffAt ℝ 2 E (0, 0)) (c : ℝ)
    (hEq : ∀ η, chartedEnergyAtMinimizer a ρ V η = E (η, 0) + c) (x : ChartCoord F → ℝ) :
    fderiv ℝ (fderiv ℝ E) (0, 0) (stepPointOf x, 0) (stepPointOf x, 0) =
      dotProduct x (Matrix.mulVec (chartedHessian a ρ V 0) x) := by
  set H := fderiv ℝ (fderiv ℝ E) (0, 0) with hH
  have hin : ∀ ζ : StepVariable (finiteCells F),
      HasFDerivAt (fun η : StepVariable (finiteCells F) => (η, (0 : B)))
        (ContinuousLinearMap.inl ℝ (StepVariable (finiteCells F)) B) ζ := fun ζ =>
    (ContinuousLinearMap.inl ℝ (StepVariable (finiteCells F)) B).hasFDerivAt
  have hc : Tendsto (fun η : StepVariable (finiteCells F) => (η, (0 : B))) (𝓝 0) (𝓝 (0, 0)) :=
    (hin 0).continuousAt.tendsto
  have hsec : ∀ u w : StepVariable (finiteCells F),
      secondDerivAlong (chartedEnergyAtMinimizer a ρ V) 0 u w = H (w, 0) (u, 0) := by
    intro u w
    have hPsi : chartedEnergyAtMinimizer a ρ V = fun η => E (η, 0) + c := funext hEq
    have hev : (fun ζ => fderiv ℝ (chartedEnergyAtMinimizer a ρ V) ζ u) =ᶠ[𝓝 0]
        fun ζ => fderiv ℝ E (ζ, 0) (u, 0) := by
      filter_upwards [hc.eventually (eventually_differentiableAt_of_contDiffAt hE)] with ζ hζ
      have h1 : HasFDerivAt (fun η => E (η, (0 : B)))
          ((fderiv ℝ E (ζ, 0)).comp (ContinuousLinearMap.inl ℝ (StepVariable (finiteCells F)) B)) ζ :=
        hζ.hasFDerivAt.comp ζ (hin ζ)
      have h2 := h1.add_const c
      rw [hPsi, h2.fderiv]
      simp
    unfold secondDerivAlong
    rw [hev.fderiv_eq]
    have h1 : HasFDerivAt (fun ζ => fderiv ℝ E (ζ, (0 : B)))
        (H.comp (ContinuousLinearMap.inl ℝ (StepVariable (finiteCells F)) B)) 0 :=
      (hasFDerivAt_fderiv_of_contDiffAt hE).comp (0 : StepVariable (finiteCells F)) (hin 0)
    have h2 := h1.clm_apply (hasFDerivAt_const ((u, (0 : B))) (0 : StepVariable (finiteCells F)))
    rw [h2.fderiv]
    simp
  have hS : ∀ i j, chartedHessian a ρ V 0 i j =
      H (bondVariation j.1 (EuclideanSpace.single j.2 1), 0)
        (bondVariation i.1 (EuclideanSpace.single i.2 1), 0) :=
    fun i j => hsec _ _
  have hx : (stepPointOf x, (0 : B)) =
      ∑ i : ChartCoord F, x i • ((bondVariation i.1 (EuclideanSpace.single i.2 (1 : ℝ)) :
        StepVariable (finiteCells F)), (0 : B)) := by
    rw [stepPointOf_eq]
    ext1
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum]
  rw [hx]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    dotProduct, Matrix.mulVec, hS, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
private abbrev minimizerChart (a ρ : ℝ) (V : F.GaugeField F.top) : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  coordsAboveFrame true a ρ 0 V 0
private def chartExcess (a ρ : ℝ) (V : F.GaugeField F.top)
    (p : StepVariable (finiteCells F) × (Fin (topDimension F) → ℝ)) : ℝ :=
  excessEnergy a
    (chartedField (fun y i => minimizerChart a ρ V y i + stepCoordinates p.1 y i) (rotatedField (topRotation p.2) V))
    (rotatedField (topRotation p.2) V)
private def minimizerBranch (a ρ : ℝ) (V : F.GaugeField F.top) (σ : Fin (topDimension F) → ℝ) :
    StepVariable (finiteCells F) :=
  fun b => toEuclid (minimizingBondCoordinate a ρ (finiteCells F) b.1 (rotatedField (topRotation σ) V) -
    minimizerChart a ρ V b.1.1 b.1.2)
private theorem coordsAboveFrame_eq (a ρ : ℝ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    coordsAboveFrame true a ρ 0 V η = fun y i => minimizerChart a ρ V y i + stepCoordinates η y i := by
  funext y i
  simp [coordsAboveFrame, stepCoordinates_zero]
private theorem minimizerChart_eq (a ρ : ℝ) (V : F.GaugeField F.top) (y : F.Site F.depth) (i : Fin 4) :
    minimizerChart a ρ V y i = minimizingCoordinates a (finiteCells F) V ρ y i := by
  simp [coordsAboveFrame, stepCoordinates_zero, ColdStepAtMirrorFrames.stepFrame, minimizingBondCoordinate]
private theorem contDiffAt_rotatedField (V : F.GaugeField F.top) (x : F.Site F.top) (i : Fin 4)
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] {f : B → Fin (topDimension F) → ℝ} {b₀ : B}
    (hf : ContDiffAt ℝ 2 f b₀) :
    ContDiffAt ℝ 2 (fun b => ((rotatedField (topRotation (f b)) V x i : UnitQuaternion) : ℍ[ℝ])) b₀ := by
  have e : (fun b => ((rotatedField (topRotation (f b)) V x i : UnitQuaternion) : ℍ[ℝ])) = fun b =>
      NormedSpace.exp (topRotation (f b) x i : ℍ[ℝ]) * ((V x i : UnitQuaternion) : ℍ[ℝ]) := by
    funext b
    simp [rotatedField, coe_expUnit]
  rw [e]
  exact (contDiffAt_quatExp_comp ((contDiff_topRotation x i).contDiffAt.comp b₀ hf)).mul contDiffAt_const
private theorem contDiffAt_chartExcess (a ρ : ℝ) (V : F.GaugeField F.top)
    (hC2 : ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (y₀ : Y)
        (Z : Y → F.GaugeField F.depth) (Z' : Y → F.GaugeField F.top),
        Z y₀ = stepMinimizer a ρ V → Z' y₀ = V →
        (∀ x i, ContDiffAt ℝ 2 (fun y => ((Z y x i : UnitQuaternion) : ℍ[ℝ])) y₀) →
        (∀ x i, ContDiffAt ℝ 2 (fun y => ((Z' y x i : UnitQuaternion) : ℍ[ℝ])) y₀) →
        ContDiffAt ℝ 2 (fun y => excessEnergy a (Z y) (Z' y)) y₀) :
    ContDiffAt ℝ 2 (chartExcess a ρ V) (0, 0) := by
  classical
  have hsnd : ContDiffAt ℝ 2
      (fun p : StepVariable (finiteCells F) × (Fin (topDimension F) → ℝ) => p.2) (0, 0) :=
    contDiffAt_snd
  refine hC2 _ (0, 0)
    (fun p => chartedField (fun y i => minimizerChart a ρ V y i + stepCoordinates p.1 y i)
      (rotatedField (topRotation p.2) V))
    (fun p => rotatedField (topRotation p.2) V) ?_ ?_ ?_ (fun x i => contDiffAt_rotatedField V x i hsnd)
  · simp only [topRotation_zero, rotatedField_zero, stepCoordinates_zero]
    simp [stepMinimizer, fieldAboveFrame]
  · simp only [topRotation_zero, rotatedField_zero]
  · intro x i
    have hl : ContDiffAt ℝ 2 (fun p : StepVariable (finiteCells F) × (Fin (topDimension F) → ℝ) =>
        NormedSpace.exp ((minimizerChart a ρ V x i : ℍ[ℝ]) + (stepCoordinates p.1 x i : ℍ[ℝ]))) (0, 0) :=
      contDiffAt_quatExp_comp (contDiffAt_const.add
        ((contDiff_stepCoordinates x i).contDiffAt.comp (0, 0) contDiffAt_fst))
    by_cases hc : IsCrossingBond (x, i)
    · have e : (fun p : StepVariable (finiteCells F) × (Fin (topDimension F) → ℝ) =>
          ((chartedField (fun y i => minimizerChart a ρ V y i + stepCoordinates p.1 y i)
            (rotatedField (topRotation p.2) V) x i : UnitQuaternion) : ℍ[ℝ])) =
          fun p => NormedSpace.exp ((minimizerChart a ρ V x i : ℍ[ℝ]) + (stepCoordinates p.1 x i : ℍ[ℝ])) *
            ((rotatedField (topRotation p.2) V (enclosingCell x) i : UnitQuaternion) : ℍ[ℝ]) := by
        funext p
        simp [chartedField, if_pos hc, coe_expUnit]
      rw [e]
      exact hl.mul (contDiffAt_rotatedField V _ i hsnd)
    · by_cases ht : IsAxialTreeBond (x, i)
      · have e : (fun p : StepVariable (finiteCells F) × (Fin (topDimension F) → ℝ) =>
            ((chartedField (fun y i => minimizerChart a ρ V y i + stepCoordinates p.1 y i)
              (rotatedField (topRotation p.2) V) x i : UnitQuaternion) : ℍ[ℝ])) =
            fun _ => 1 := by
          funext p
          simp [chartedField, if_neg hc, if_pos ht]
        rw [e]
        exact contDiffAt_const
      · have e : (fun p : StepVariable (finiteCells F) × (Fin (topDimension F) → ℝ) =>
            ((chartedField (fun y i => minimizerChart a ρ V y i + stepCoordinates p.1 y i)
              (rotatedField (topRotation p.2) V) x i : UnitQuaternion) : ℍ[ℝ])) =
            fun p => NormedSpace.exp ((minimizerChart a ρ V x i : ℍ[ℝ]) + (stepCoordinates p.1 x i : ℍ[ℝ])) := by
          funext p
          simp [chartedField, if_neg hc, if_neg ht, coe_expUnit]
        rw [e]
        exact hl
private theorem minimizerBranch_zero (a ρ : ℝ) (V : F.GaugeField F.top) : minimizerBranch a ρ V 0 = 0 := by
  funext b
  have h : minimizingBondCoordinate a ρ (finiteCells F) b.1
      (rotatedField (topRotation (0 : Fin (topDimension F) → ℝ)) V) -
      minimizerChart a ρ V b.1.1 b.1.2 = 0 := by
    rw [minimizerChart_eq, topRotation_zero, rotatedField_zero]
    exact sub_self _
  simp only [minimizerBranch, h]
  exact toEuclidCLM.map_zero
private theorem analyticAt_minimizerBranch {a ρ : ℝ} {V : F.GaugeField F.top}
    (hana : ∀ b ∈ chordBonds (finiteCells F),
      IsBondAnalyticAt (minimizingBondCoordinate a ρ (finiteCells F) b) V) :
    AnalyticAt ℝ (minimizerBranch a ρ V) 0 := by
  refine analyticAt_pi_iff.2 fun b => ?_
  have h := hana b.1 b.2 (topDimension F) (fun l => ((topCoordEquiv F).symm l).1.1)
    (fun l => imaginaryUnit ((topCoordEquiv F).symm l).2)
  exact toEuclidCLM.analyticAt _ |>.comp (h.sub analyticAt_const)
private theorem minimizerBranch_isMinimizingChart {a ρ : ℝ} {V : F.GaugeField F.top}
    {σ : Fin (topDimension F) → ℝ}
    (h0 : ∀ b, b ∉ chordBonds (finiteCells F) → minimizerChart a ρ V b.1 b.2 = 0)
    (hσ : ∃ w, IsMinimizingChart a (finiteCells F) (rotatedField (topRotation σ) V) ρ w) :
    IsMinimizingChart a (finiteCells F) (rotatedField (topRotation σ) V) ρ
      (fun y i => minimizerChart a ρ V y i + stepCoordinates (minimizerBranch a ρ V σ) y i) := by
  have hl : IsMinimizingChart a (finiteCells F) (rotatedField (topRotation σ) V) ρ
      (minimizingCoordinates a (finiteCells F) (rotatedField (topRotation σ) V) ρ) := by
    unfold minimizingCoordinates
    rw [dif_pos hσ]
    exact hσ.choose_spec
  have e : (fun y i => minimizerChart a ρ V y i + stepCoordinates (minimizerBranch a ρ V σ) y i) =
      minimizingCoordinates a (finiteCells F) (rotatedField (topRotation σ) V) ρ := by
    funext y i
    by_cases hb : (y, i) ∈ chordBonds (finiteCells F)
    · simp only [stepCoordinates, dif_pos hb, minimizerBranch, toImaginary_toEuclid]
      exact add_sub_cancel _ _
    · have h1 := h0 (y, i) hb
      have h2 := hl.1 (y, i) hb
      simp only at h1 h2
      simp only [stepCoordinates, dif_neg hb, h1, h2, add_zero]
  rw [e]
  exact hl
private theorem tendsto_minimizerBranch {a ρ : ℝ} {V : F.GaugeField F.top}
    (hana : ∀ b ∈ chordBonds (finiteCells F),
      IsBondAnalyticAt (minimizingBondCoordinate a ρ (finiteCells F) b) V) :
    Tendsto (fun σ : Fin (topDimension F) → ℝ => (minimizerBranch a ρ V σ, σ)) (𝓝 0) (𝓝 (0, 0)) := by
  have h := (analyticAt_minimizerBranch hana).continuousAt.tendsto
  rw [minimizerBranch_zero] at h
  exact h.prodMk_nhds tendsto_id
private theorem chartExcess_minimizerBranch {a ρ : ℝ} {V : F.GaugeField F.top}
    {σ : Fin (topDimension F) → ℝ}
    (h0 : ∀ b, b ∉ chordBonds (finiteCells F) → minimizerChart a ρ V b.1 b.2 = 0)
    (hσ : ∃ w, IsMinimizingChart a (finiteCells F) (rotatedField (topRotation σ) V) ρ w) :
    chartExcess a ρ V (minimizerBranch a ρ V σ, σ) = 0 :=
  excessEnergy_minimizer (minimizerBranch_isMinimizingChart h0 hσ)
private theorem chartExcess_nonneg {a ρ : ℝ} {V : F.GaugeField F.top} {σ : Fin (topDimension F) → ℝ}
    (hσ : ∃ w, IsMinimizingChart a (finiteCells F) (rotatedField (topRotation σ) V) ρ w)
    (η : StepVariable (finiteCells F)) : 0 ≤ chartExcess a ρ V (η, σ) := by
  obtain ⟨w, hw⟩ := hσ
  exact excessEnergy_nonneg hw _
private def topCoordsOf (u : TopCoord F → ℝ) : Fin (topDimension F) → ℝ := fun l => u ((topCoordEquiv F).symm l)
open Classical in
private theorem exists_top_matrix (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (hTop : ∀ y i, (y, i) ∈ innerBonds (finiteCells F) F.top)
    (P : (Fin (topDimension F) → ℝ) →L[ℝ] StepVariable (finiteCells F)) :
    ∃ M : Matrix (ChartCoord F) (TopCoord F) ℝ,
      ∀ (v : F.Site F.top → Fin 4 → imaginaryQuaternions) (i : ChartCoord F),
      Matrix.mulVec M (topCoords v) i =
        imaginaryComponents (expLeftDeriv (w i.1.1.1 i.1.1.2) (toImaginary (P (rotationCoords v) i.1))) i.2 +
        if IsCrossingBond i.1.1 then
          imaginaryComponents (NormedSpace.exp (w i.1.1.1 i.1.1.2 : ℍ[ℝ]) *
            (v (enclosingCell i.1.1.1) i.1.1.2 : ℍ[ℝ]) *
            NormedSpace.exp (-(w i.1.1.1 i.1.1.2 : ℍ[ℝ]))) i.2
        else 0 := by
  let N : (TopCoord F → ℝ) → ChartCoord F → ℝ := fun u i =>
    imaginaryComponents (expLeftDeriv (w i.1.1.1 i.1.1.2) (toImaginary (P (topCoordsOf u) i.1))) i.2 +
      if IsCrossingBond i.1.1 then
        imaginaryComponents (NormedSpace.exp (w i.1.1.1 i.1.1.2 : ℍ[ℝ]) *
          (topRotation (topCoordsOf u) (enclosingCell i.1.1.1) i.1.1.2 : ℍ[ℝ]) *
          NormedSpace.exp (-(w i.1.1.1 i.1.1.2 : ℍ[ℝ]))) i.2
      else 0
  let Nl : (TopCoord F → ℝ) →ₗ[ℝ] (ChartCoord F → ℝ) :=
    { toFun := N
      map_add' := fun u u' => by
        funext i
        have e : topCoordsOf (u + u') = topCoordsOf u + topCoordsOf u' := rfl
        simp only [N, Pi.add_apply, e, map_add, toImaginary_add, Submodule.coe_add, expLeftDeriv_add,
          imaginaryComponents_add, topRotation_add, mul_add, add_mul]
        split_ifs <;> (try simp only [add_zero]) <;> ring
      map_smul' := fun c u => by
        funext i
        have e : topCoordsOf (c • u) = c • topCoordsOf u := rfl
        simp only [N, Pi.smul_apply, e, map_smul, toImaginary_smul, Submodule.coe_smul, expLeftDeriv_smul,
          imaginaryComponents_smul, topRotation_smul, mul_smul_comm, smul_mul_assoc, RingHom.id_apply,
          smul_eq_mul]
        split_ifs <;> (try simp only [mul_zero, add_zero]) <;> ring }
  refine ⟨LinearMap.toMatrix' Nl, fun v i => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  show N (topCoords v) i = _
  have e : topCoordsOf (topCoords v) = rotationCoords v := rfl
  simp only [N, e, topRotation_rotationCoords hTop]
private theorem excessHessian_eq_chartedHessian_of_hypotheses
    (hSV : ParametricMinima.HessianSplitsAtPartialMinimum) (a ρ : ℝ) (V : F.GaugeField F.top)
    (hTop : ∀ y i, (y, i) ∈ innerBonds (finiteCells F) F.top)
    (hLow : ∀ y i, (y, i) ∈ innerBonds (finiteCells F) F.depth)
    (hmin : ∀ᶠ σ in 𝓝 (0 : Fin (topDimension F) → ℝ),
      ∃ w, IsMinimizingChart a (finiteCells F) (rotatedField (topRotation σ) V) ρ w)
    (hana : ∀ b ∈ chordBonds (finiteCells F),
      IsBondAnalyticAt (minimizingBondCoordinate a ρ (finiteCells F) b) V)
    (hC2 : ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (y₀ : Y)
        (Z : Y → F.GaugeField F.depth) (Z' : Y → F.GaugeField F.top),
        Z y₀ = stepMinimizer a ρ V → Z' y₀ = V →
        (∀ x i, ContDiffAt ℝ 2 (fun y => ((Z y x i : UnitQuaternion) : ℍ[ℝ])) y₀) →
        (∀ x i, ContDiffAt ℝ 2 (fun y => ((Z' y x i : UnitQuaternion) : ℍ[ℝ])) y₀) →
        ContDiffAt ℝ 2 (fun y => excessEnergy a (Z y) (Z' y)) y₀)
    (hvel : ∀ (Z : ℝ → F.GaugeField F.depth) (Z' : ℝ → F.GaugeField F.top)
        (A : F.Site F.depth → Fin 4 → imaginaryQuaternions) (v : F.Site F.top → Fin 4 → imaginaryQuaternions),
        Z 0 = stepMinimizer a ρ V → Z' 0 = V →
        (∀ x i, ContDiffAt ℝ 2 (fun r => ((Z r x i : UnitQuaternion) : ℍ[ℝ])) 0) →
        (∀ x i, ContDiffAt ℝ 2 (fun r => ((Z' r x i : UnitQuaternion) : ℍ[ℝ])) 0) →
        (∀ x i, HasDerivAt (fun r => ((Z r x i : UnitQuaternion) : ℍ[ℝ]))
          ((A x i : ℍ[ℝ]) * ((Z 0 x i : UnitQuaternion) : ℍ[ℝ])) 0) →
        (∀ x i, HasDerivAt (fun r => ((Z' r x i : UnitQuaternion) : ℍ[ℝ]))
          ((v x i : ℍ[ℝ]) * ((Z' 0 x i : UnitQuaternion) : ℍ[ℝ])) 0) →
        ContDiffAt ℝ 2 (fun r => excessEnergy a (Z r) (Z' r)) 0 ∧
          deriv (deriv fun r => excessEnergy a (Z r) (Z' r)) 0 = excessHessian a (Z 0) (Z' 0) A v)
    (hgauge : ∀ (g : F.Site F.depth → UnitQuaternion), (∀ z : F.Cell, g (cellCentre F.depth z) = 1) →
      ∀ (W : F.GaugeField F.depth) (V' : F.GaugeField F.top),
        excessEnergy a (BlockAverages.gaugeTransform g W) V' = excessEnergy a W V') :
    ∃ M : Matrix (ChartCoord F) (TopCoord F) ℝ,
      ∀ (A : F.Site F.depth → Fin 4 → imaginaryQuaternions) (v : F.Site F.top → Fin 4 → imaginaryQuaternions)
        (x : ChartCoord F → ℝ) (γ : F.Site F.depth → imaginaryQuaternions),
        (∀ z : F.Cell, γ (cellCentre F.depth z) = 0) →
        (∀ i : ChartCoord F, imaginaryComponents (A i.1.1.1 i.1.1.2 : ℍ[ℝ]) i.2 =
          chartTangentCoords a ρ V x i +
            imaginaryComponents (covariantDifference (stepMinimizer a ρ V) γ i.1.1) i.2 +
            Matrix.mulVec M (topCoords v) i) →
        (∀ i : TreeCoord F, imaginaryComponents (A i.1.1.1 i.1.1.2 : ℍ[ℝ]) i.2 =
          imaginaryComponents (covariantDifference (stepMinimizer a ρ V) γ i.1.1) i.2) →
        excessHessian a (stepMinimizer a ρ V) V A v =
          dotProduct x (Matrix.mulVec (chartedHessian a ρ V 0) x) := by
  classical
  have hE := contDiffAt_chartExcess a ρ V hC2
  have hV0 : ∃ w, IsMinimizingChart a (finiteCells F) V ρ w := by
    have h := hmin.self_of_nhds
    rwa [topRotation_zero, rotatedField_zero] at h
  have h0 : ∀ b, b ∉ chordBonds (finiteCells F) → minimizerChart a ρ V b.1 b.2 = 0 := by
    intro b hb
    rw [minimizerChart_eq]
    unfold minimizingCoordinates
    rw [dif_pos hV0]
    exact hV0.choose_spec.1 b hb
  have hbr := analyticAt_minimizerBranch hana
  have hbd : ∀ᶠ σ in 𝓝 (0 : Fin (topDimension F) → ℝ), DifferentiableAt ℝ (minimizerBranch a ρ V) σ := by
    filter_upwards [hbr.eventually_analyticAt] with σ hσ
    exact hσ.differentiableAt
  have hPd : HasFDerivAt (minimizerBranch a ρ V) (fderiv ℝ (minimizerBranch a ρ V) 0) 0 :=
    hbd.self_of_nhds.hasFDerivAt
  have hcrit : ∀ᶠ σ in 𝓝 (0 : Fin (topDimension F) → ℝ), ∀ e : StepVariable (finiteCells F),
      fderiv ℝ (chartExcess a ρ V) (minimizerBranch a ρ V σ, σ) (e, 0) = 0 := by
    filter_upwards [(tendsto_minimizerBranch hana).eventually (eventually_differentiableAt_of_contDiffAt hE),
      hmin] with σ hd hσ e
    refine fderiv_inl_eq_zero_of_isMin hd (fun e' => ?_) e
    rw [chartExcess_minimizerBranch h0 hσ]
    exact chartExcess_nonneg hσ e'
  have hm0 : fderiv ℝ (fderiv ℝ fun b => chartExcess a ρ V (minimizerBranch a ρ V b, b)) 0 = 0 := by
    have hev : (fun b => chartExcess a ρ V (minimizerBranch a ρ V b, b)) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      filter_upwards [hmin] with σ hσ
      exact chartExcess_minimizerBranch h0 hσ
    rw [hev.fderiv.fderiv_eq]
    simp
  obtain ⟨M, hM⟩ := exists_top_matrix (minimizerChart a ρ V) hTop (fderiv ℝ (minimizerBranch a ρ V) 0)
  refine ⟨M, fun A v x γ hγ hch htr => ?_⟩
  set P := fderiv ℝ (minimizerBranch a ρ V) 0 with hP
  set σ := rotationCoords v with hσ
  set η' := stepPointOf x + P σ with hη
  set ξ := stepCoordinates η' with hξ
  set w := minimizerChart a ρ V with hw
  have hA : ∀ y i, (A y i : ℍ[ℝ]) =
      chartLeftVelocity w ξ v y i + covariantDifference (chartedField w V) γ (y, i) := by
    intro y i
    have hd := hasDerivAt_fieldPath γ w ξ v V y i
    have hre : (chartLeftVelocity w ξ v y i + covariantDifference (chartedField w V) γ (y, i)).re = 0 := by
      refine re_eq_zero_of_unit_curve (Z := fun r => fieldPath γ w ξ v V r y i) ?_
      rw [fieldPath_zero]
      exact hd
    refine quaternion_ext_of_components (by rw [hre]; exact (A y i).2) fun α => ?_
    have hb := hLow y i
    by_cases ht : IsAxialTreeBond (y, i)
    · have hb' : (y, i) ∈ treeEdges F := Finset.mem_filter.2 ⟨hb, ht⟩
      have h1 : imaginaryComponents (A y i : ℍ[ℝ]) α =
          imaginaryComponents (covariantDifference (chartedField w V) γ (y, i)) α := htr ⟨⟨(y, i), hb'⟩, α⟩
      have hnc : ¬ IsCrossingBond (y, i) := ht.1
      rw [show chartLeftVelocity w ξ v y i = 0 by simp [chartLeftVelocity, if_neg hnc, if_pos ht], zero_add]
      exact h1
    · have hb' : (y, i) ∈ chordBonds (finiteCells F) := Finset.mem_filter.2 ⟨hb, ht⟩
      have h1 : imaginaryComponents (A y i : ℍ[ℝ]) α =
          imaginaryComponents (expLeftDeriv (w y i) (toImaginary (stepPointOf x ⟨(y, i), hb'⟩))) α +
            imaginaryComponents (covariantDifference (chartedField w V) γ (y, i)) α +
            Matrix.mulVec M (topCoords v) (⟨(y, i), hb'⟩, α) := hch ⟨⟨(y, i), hb'⟩, α⟩
      have h2 := hM v (⟨(y, i), hb'⟩, α)
      simp only at h2
      have hξy : (ξ y i : ℍ[ℝ]) = (toImaginary (stepPointOf x ⟨(y, i), hb'⟩) : ℍ[ℝ]) +
          (toImaginary (P σ ⟨(y, i), hb'⟩) : ℍ[ℝ]) := by
        simp only [hξ, stepCoordinates, dif_pos hb', hη, Pi.add_apply, toImaginary_add, Submodule.coe_add]
      rw [imaginaryComponents_add]
      by_cases hc : IsCrossingBond (y, i)
      · rw [if_pos hc] at h2
        simp only [chartLeftVelocity, if_pos hc, hξy, expLeftDeriv_add, imaginaryComponents_add]
        rw [h1, h2]
        ring
      · rw [if_neg hc] at h2
        simp only [chartLeftVelocity, if_neg hc, if_neg ht, hξy, expLeftDeriv_add, imaginaryComponents_add]
        rw [h1, h2]
        ring
  have hZ0 : fieldPath γ w ξ v V 0 = stepMinimizer a ρ V := fieldPath_zero γ w ξ v V
  have hZ'0 : (fun r : ℝ => rotatedField (r • v) V) 0 = V := by simp [rotatedField_zero]
  have hc2 : ∀ x i, ContDiffAt ℝ 2 (fun r : ℝ => ((rotatedField (r • v) V x i : UnitQuaternion) : ℍ[ℝ])) 0 := by
    intro y i
    have e : (fun r : ℝ => ((rotatedField (r • v) V y i : UnitQuaternion) : ℍ[ℝ])) = fun r : ℝ =>
        NormedSpace.exp (r • (v y i : ℍ[ℝ])) * ((V y i : UnitQuaternion) : ℍ[ℝ]) := by
      funext r
      simp [rotatedField, coe_expUnit]
    rw [e]
    exact (contDiffAt_quatExp_smul _).mul contDiffAt_const
  have hd2 : ∀ x i, HasDerivAt (fun r : ℝ => ((rotatedField (r • v) V x i : UnitQuaternion) : ℍ[ℝ]))
      ((v x i : ℍ[ℝ]) * (((fun r : ℝ => rotatedField (r • v) V) 0 x i : UnitQuaternion) : ℍ[ℝ])) 0 := by
    intro y i
    have e : (fun r : ℝ => ((rotatedField (r • v) V y i : UnitQuaternion) : ℍ[ℝ])) = fun r : ℝ =>
        NormedSpace.exp (r • (v y i : ℍ[ℝ])) * ((V y i : UnitQuaternion) : ℍ[ℝ]) := by
      funext r
      simp [rotatedField, coe_expUnit]
    rw [e, hZ'0]
    exact (hasDerivAt_quatExp_smul _).mul_const _
  have hd1 : ∀ x i, HasDerivAt (fun r => ((fieldPath γ w ξ v V r x i : UnitQuaternion) : ℍ[ℝ]))
      ((A x i : ℍ[ℝ]) * ((fieldPath γ w ξ v V 0 x i : UnitQuaternion) : ℍ[ℝ])) 0 := by
    intro y i
    rw [fieldPath_zero, hA]
    exact hasDerivAt_fieldPath γ w ξ v V y i
  have hv := (hvel (fieldPath γ w ξ v V) (fun r => rotatedField (r • v) V) A v hZ0 hZ'0
    (contDiffAt_fieldPath γ w ξ v V) hc2 hd1 hd2).2
  have hZ'1 : rotatedField ((0 : ℝ) • v) V = V := hZ'0
  rw [hZ0, hZ'1] at hv
  have hkey : (fun r : ℝ => excessEnergy a (fieldPath γ w ξ v V r) (rotatedField (r • v) V)) =
      fun r : ℝ => chartExcess a ρ V
        (r • ((η', σ) : StepVariable (finiteCells F) × (Fin (topDimension F) → ℝ))) := by
    funext r
    have hcentre : ∀ z : F.Cell, gaugePath γ r (cellCentre F.depth z) = 1 := by
      intro z
      simp [gaugePath, hγ, expUnit_zero]
    have htop : topRotation (r • σ) = r • v := by
      funext y i
      rw [topRotation_smul, hσ, topRotation_rotationCoords hTop]
      rfl
    unfold fieldPath
    rw [hgauge _ hcentre]
    simp only [chartPath, chartExcess, Prod.smul_fst, Prod.smul_snd, htop, stepCoordinates_smul]
    rfl
  rw [← hv, hkey]
  have h1 := deriv_deriv_along_line (f := chartExcess a ρ V) hE (η', σ)
  have h2 := hSV _ _ (chartExcess a ρ V) (minimizerBranch a ρ V) P hE (minimizerBranch_zero a ρ V) hbd hPd
    hcrit η' σ
  have h3 := second_fderiv_eq_chartedHessian_form (V := V) (a := a) (ρ := ρ) hE
    (minimalAction a (finiteCells F) F.top V) (fun η => by
    have e : chartedEnergyAtMinimizer a ρ V η = blockEnergy a (finiteCells F) F.depth
        (chartedField (fun y i => minimizerChart a ρ V y i + stepCoordinates η y i) V) V := by
      show blockEnergy a (finiteCells F) F.depth (chartedField (coordsAboveFrame true a ρ 0 V η) V) V = _
      rw [coordsAboveFrame_eq a ρ V η]
    rw [e]
    simp only [chartExcess, topRotation_zero, rotatedField_zero, excessEnergy]
    ring) x
  have h4 : η' - P σ = stepPointOf x := by
    rw [hη]
    exact add_sub_cancel_right _ _
  rw [h1]
  have h1' : fderiv ℝ (fderiv ℝ (chartExcess a ρ V)) 0 (η', σ) (η', σ) =
      fderiv ℝ (fderiv ℝ (chartExcess a ρ V)) (0, 0) (η', σ) (η', σ) := rfl
  rw [h1', h2, hm0, h4, h3]
  simp
private theorem period_top (i : Fin 4) : F.period F.top i = F.extent i := by apply _root_.YangMills.Construction.GaugeFixing.period_top <;> assumption
private theorem mem_sitesOfCells_top (hs : ∀ i, 2 ≤ F.extent i) (z : F.Cell) :
    z ∈ sitesOfCells (finiteCells F) F.top := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedEnergyCoordinates.mem_sitesOfCells_top <;> assumption
private theorem zmod_cast_cast {p q : ℕ} (h : p = q) (y : ZMod p) :
    ((((((y.cast : ℤ) : ZMod q)).cast : ℤ)) : ZMod p) = y := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LevelShare.cast_cast_of_eq <;> assumption
private def torusLift {L t m : ℕ} (U : (torusFrame L t m).GaugeField (torusFrame L t m).top) : TorusField m :=
  fun z i => U (siteOfCoords (torusFrame L t m).top fun k => ((z k).cast : ℤ)) i
private theorem readAtLevel_torusLift {L t m : ℕ} (U : (torusFrame L t m).GaugeField (torusFrame L t m).top) :
    readAtLevel (torusFrame L t m) (torusFrame L t m).top (torusLift U) = U := by
  funext x i
  show U (siteOfCoords (torusFrame L t m).top fun k => ((((siteCoords x k : ℤ) : ZMod m)).cast : ℤ)) i = U x i
  congr 1
  funext k
  exact zmod_cast_cast (p := (torusFrame L t m).period (torusFrame L t m).top k) (q := m) (period_top k) (x k)
private theorem torusLift_readAtLevel {L t m : ℕ} (V : TorusField m) :
    torusLift (readAtLevel (torusFrame L t m) (torusFrame L t m).top V) = V := by
  funext z i
  show V (fun k => ((siteCoords (siteOfCoords (F := torusFrame L t m) (torusFrame L t m).top
    fun k => ((z k).cast : ℤ)) k : ℤ) : ZMod m)) i = V z i
  congr 1
  funext k
  exact zmod_cast_cast (p := m) (q := (torusFrame L t m).period (torusFrame L t m).top k)
    (period_top (F := torusFrame L t m) k).symm (z k)
private theorem continuous_torusLift {L t m : ℕ} (V : (torusFrame L t m).GaugeField (torusFrame L t m).top) :
    Continuous fun σ : Fin (topDimension (torusFrame L t m)) → ℝ =>
      torusLift (rotatedField (topRotation σ) V) := by
  refine continuous_pi fun z => continuous_pi fun i => ?_
  show Continuous fun σ : Fin (topDimension (torusFrame L t m)) → ℝ =>
    expUnit (topRotation σ (siteOfCoords (torusFrame L t m).top fun k => ((z k).cast : ℤ)) i) *
      V (siteOfCoords (torusFrame L t m).top fun k => ((z k).cast : ℤ)) i
  refine Continuous.mul (Continuous.subtype_mk ?_ _) continuous_const
  have hexp : Continuous (NormedSpace.exp : ℍ[ℝ] → ℍ[ℝ]) :=
    continuous_iff_continuousAt.2 fun q => (quatExp_contDiffAt q).continuousAt
  exact hexp.comp (contDiff_topRotation _ _).continuous
end ExcessHessianChart
open BlockAverages ColdStepAtMirrorFrames ReferenceDensity TorusFields ExcessHessianChart in
theorem excessHessianEqChartHessian_holds
    (hD : ExcessEnergyIsContDiffTwo)
    (hR : SecondDerivExcessEnergyEqExcessHessian)
    (hN : MinimizerNearTrivialField)
    (hSV : ParametricMinima.HessianSplitsAtPartialMinimum)
    (hLA : ColdStepAtMirrorFrames.MinimalActionGaugeInvariant)
    (hGC : BlockAverages.gaugeCovarianceStatement)
    (hB : ColdStepAtMirrorFrames.BlocksCoverLowerLevel) :
    ExcessHessianEqChartHessian := by
  intro a ha L hL t m ρ hm h0 h1
  have hL0 : 0 < L := by have := hL.2; omega
  have hs : ∀ i, 2 ≤ (torusFrame L t m).extent i := fun _ => by
    show 2 ≤ m
    have := hL.2
    omega
  have hTop : ∀ (y : (torusFrame L t m).Site (torusFrame L t m).top) (i : Fin 4),
      (y, i) ∈ BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells (torusFrame L t m))
        (torusFrame L t m).top := by
    intro y i
    exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨mem_sitesOfCells_top hs y, Finset.mem_univ _⟩,
      mem_sitesOfCells_top hs _⟩
  have hLow : ∀ (y : (torusFrame L t m).Site (torusFrame L t m).depth) (i : Fin 4),
      (y, i) ∈ BlockAverages.innerBonds (ColdStepAtMirrorFrames.finiteCells (torusFrame L t m))
        (torusFrame L t m).depth := by
    intro y i
    have hc := fun x => hB (torusFrame L t m) hL.1 (fun j => (by have := hs j; omega)) x
    exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hc y, Finset.mem_univ _⟩, hc _⟩
  filter_upwards [eventually_eventually_nhds.2 (hN a ha L hL t m ρ hm h0 h1).2,
    hD a ha L hL t m ρ hm h0 h1, hR a ha L hL t m ρ hm h0 h1] with V₀ hQ hC2 hvel
  set V := readAtLevel (torusFrame L t m) (torusFrame L t m).top V₀ with hV
  have hT : Tendsto (fun σ : Fin (topDimension (torusFrame L t m)) → ℝ =>
      torusLift (rotatedField (topRotation σ) V)) (𝓝 0) (𝓝 V₀) := by
    have h := (continuous_torusLift V).tendsto 0
    simp only [topRotation_zero, rotatedField_zero] at h
    rwa [hV, torusLift_readAtLevel] at h
  have hmin : ∀ᶠ σ in 𝓝 (0 : Fin (topDimension (torusFrame L t m)) → ℝ),
      ∃ w, BlockAverages.IsMinimizingChart a (ColdStepAtMirrorFrames.finiteCells (torusFrame L t m))
        (BlockAverages.rotatedField (topRotation σ) V) ρ w := by
    filter_upwards [hT.eventually hQ] with σ hσ
    have h := hσ.1
    rwa [readAtLevel_torusLift] at h
  exact excessHessian_eq_chartedHessian_of_hypotheses hSV a ρ V hTop hLow hmin hQ.self_of_nhds.2.2.2.2 hC2 hvel
    (fun g hg W V' => excessEnergy_gaugeTransform hLA hGC hL0 a g hg W V')
end YangMills.Construction.RunningCouplingSlope
end
