import YangMills.Construction.ResponseInTheExpansion.CalculusOfTheColdHalf
import YangMills.Construction.ResponseInTheExpansion.FieldsOfTheTopAreBounded
import YangMills.Construction.ResponseInTheExpansion.RightShiftsAreOne
import YangMills.Construction.SummableBoundsOfTheFlow.BlockExpansionHasTheConditionsOfThirdOrderProof
import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftOfTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation WeightedResponses
namespace ResponseInTheExpansion
namespace TopVariation
variable {F : BlockFrame}
theorem norm_imaginaryCoords (w : imaginaryQuaternions) : ‖_root_.YangMills.Construction.Interpolation.imaginaryCoords w‖ = ‖w‖ := by apply _root_.YangMills.SharedProofs.p6124 <;> assumption
theorem norm_toImaginary (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.norm_toImaginary <;> assumption
def imaginaryCoordsCLM : imaginaryQuaternions →L[ℝ] BondVector :=
  LinearMap.mkContinuous
    { toFun := _root_.YangMills.Construction.Interpolation.imaginaryCoords
      map_add' := fun a b => by
        ext i
        fin_cases i <;> simp [_root_.YangMills.Construction.Interpolation.imaginaryCoords]
      map_smul' := fun r a => by
        ext i
        fin_cases i <;> simp [_root_.YangMills.Construction.Interpolation.imaginaryCoords] } 1 (fun w => by
    show ‖_root_.YangMills.Construction.Interpolation.imaginaryCoords w‖ ≤ 1 * ‖w‖
    rw [norm_imaginaryCoords, one_mul])
theorem imaginaryCoordsCLM_apply (w : imaginaryQuaternions) : imaginaryCoordsCLM w = _root_.YangMills.Construction.Interpolation.imaginaryCoords w := rfl
theorem cellSupDist_le_bondSpan (z : F.Cell) (c : F.Site F.top × Fin 4) :
    cellSupDist z c.1 ≤ bondSpan z (Fin.cons c ![] : Fin (0 + 1) → F.Site F.top × Fin 4) := by
  unfold bondSpan
  refine le_trans ?_ (le_max_left _ _)
  exact Finset.le_sup (f := fun l : Fin (0 + 1) =>
    siteSupDist z ((Fin.cons c ![] : Fin (0 + 1) → F.Site F.top × Fin 4) l).1) (Finset.mem_univ (0 : Fin (0 + 1)))
theorem topVariationBounded_of_chart (hOne : rightTranslationDerivUniqueStatement)
    {T₂ : imaginaryQuaternions → imaginaryQuaternions →L[ℝ] imaginaryQuaternions} {CT : ℝ} (hCT : 0 ≤ CT)
    (hsh : ∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (T₂ w X))
    (hsm : ∀ w : imaginaryQuaternions, ‖w‖ ≤ 1 → ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) T₂ w)
    (hbd : ∀ (w : imaginaryQuaternions) (j : ℕ), ‖w‖ ≤ 1 → j ≤ 2 → ‖iteratedFDeriv ℝ j T₂ w‖ ≤ CT)
    {Q : ColdHalfLaw} {Cs : ℝ} {V : F.GaugeField F.top} (hCs : 0 ≤ Cs) (hκ : 0 ≤ Q.rate)
    (hfr : ∀ b : ↥(chordBonds (finiteCells F)),
      ‖interpolatedFrame 1 Q.a Q.chartRadius Q.mirrorRadius b.1 V‖ + Q.ballRadius ≤ 1 / 2)
    (hT : TopVariationRepresentation 1 Q.a Q.chartRadius Q.ballRadius Q.rate Cs Q.mirrorRadius V) :
    TopVariationBounded Q (Cs + CT) V := by
  classical
  intro T hT' c X b v hX hv
  obtain ⟨T₀, hT₀, -, hb₀⟩ := hT.exists_representation
  set w₀ : imaginaryQuaternions := interpolatedFrame 1 Q.a Q.chartRadius Q.mirrorRadius b.1 V with hw₀
  set d₀ : imaginaryQuaternions :=
    bondDeriv (interpolatedFrame 1 Q.a Q.chartRadius Q.mirrorRadius b.1) V (fun _ : Fin 1 => c) (fun _ => X) with hd₀
  have hw : ∀ v' : BondVector, ‖v'‖ < Q.ballRadius → ‖w₀ + toImaginary v'‖ < 1 := fun v' hv' => by
    have h1 := hfr b
    have h2 := norm_add_le w₀ (toImaginary v')
    rw [norm_toImaginary] at h2
    linarith
  have hπ : ∀ v' : BondVector, ‖v'‖ < Q.ballRadius → ‖w₀ + toImaginary v'‖ < Real.pi := fun v' hv' =>
    (hw v' hv').trans (by linarith [Real.pi_gt_three])
  have hsame : ∀ v' : BondVector, ‖v'‖ < Q.ballRadius →
      T (w₀ + toImaginary v') X = T₂ (w₀ + toImaginary v') X := fun v' hv' =>
    hOne _ X _ _ (hπ v' hv') (hT' _ X (hπ v' hv')) (hsh _ X (hπ v' hv'))
  have hsame₀ : ∀ v' : BondVector, ‖v'‖ < Q.ballRadius →
      T (w₀ + toImaginary v') X = T₀ (w₀ + toImaginary v') X := fun v' hv' =>
    hOne _ X _ _ (hπ v' hv') (hT' _ X (hπ v' hv')) (hT₀ _ X (hπ v' hv'))
  have hdc0 : (0 : ℝ) ≤ bondDistToTopBond b c := Nat.cast_nonneg _
  have he0 : 0 < Real.exp (-(2 ^ 8 * Q.rate * bondDistToTopBond b c)) := Real.exp_pos _
  have hvalue : ‖_root_.YangMills.Construction.Interpolation.imaginaryCoords
      (topVariationField T 1 Q.a Q.chartRadius Q.mirrorRadius c X b.1 (toImaginary v) V)‖ ≤
      (Cs + CT) * Real.exp (-(2 ^ 8 * Q.rate * bondDistToTopBond b c)) := by
    have e0 : topVariationField T 1 Q.a Q.chartRadius Q.mirrorRadius c X b.1 (toImaginary v) V =
        topVariationField T₀ 1 Q.a Q.chartRadius Q.mirrorRadius c X b.1 (toImaginary v) V := by
      unfold topVariationField
      rw [hsame₀ v hv]
    have h1 := hb₀ c X b (toImaginary v) 0 ![] ![] hX (by rw [norm_toImaginary]; exact hv) (by omega)
      (fun l => l.elim0)
    have e1 : bondDeriv (topVariationField T₀ 1 Q.a Q.chartRadius Q.mirrorRadius c X b.1 (toImaginary v)) V ![] ![] =
        topVariationField T₀ 1 Q.a Q.chartRadius Q.mirrorRadius c X b.1 (toImaginary v) V := by
      simp only [bondDeriv, iteratedFDeriv_zero_apply]
      rw [ResponseInTheExpansion.leftTranslate_bondSpread_zero]
    rw [e1] at h1
    rw [norm_imaginaryCoords, e0]
    refine h1.trans ?_
    have h2 : (bondDistToTopBond b c : ℝ) ≤
        (bondSpan (enclosingCell b.1.1) (Fin.cons c ![] : Fin (0 + 1) → F.Site F.top × Fin 4) : ℕ) :=
      Nat.cast_le.2 (cellSupDist_le_bondSpan _ c)
    have h3 : Real.exp (-(2 ^ 8 * Q.rate *
        (bondSpan (enclosingCell b.1.1) (Fin.cons c ![] : Fin (0 + 1) → F.Site F.top × Fin 4) : ℕ))) ≤
        Real.exp (-(2 ^ 8 * Q.rate * bondDistToTopBond b c)) := by
      rw [Real.exp_le_exp]
      have h4 : 0 ≤ 2 ^ 8 * Q.rate := by positivity
      nlinarith
    exact mul_le_mul (by linarith) h3 (Real.exp_pos _).le (by linarith)
  by_cases hcr : IsCrossingBond b.1 ∧ (enclosingCell b.1.1, b.1.2) = c
  · have hdc : bondDistToTopBond b c = 0 := by
      have h1 : c.1 = enclosingCell b.1.1 := (congrArg Prod.fst hcr.2).symm
      simp only [bondDistToTopBond, h1]
      have : cellSupDist (enclosingCell b.1.1) (enclosingCell b.1.1) = 0 := by
        simp [cellSupDist]
      simp [this]
    let z₂ : BondVector → BondVector := fun v' =>
      imaginaryCoordsCLM (d₀ + T₂ (w₀ + BondCoordinates.toImaginaryCLM v') X)
    have hO : IsOpen {v' : BondVector | ‖v'‖ < Q.ballRadius} := isOpen_lt continuous_norm continuous_const
    have hev : (fun v' : BondVector => _root_.YangMills.Construction.Interpolation.imaginaryCoords
        (topVariationField T 1 Q.a Q.chartRadius Q.mirrorRadius c X b.1 (toImaginary v') V)) =ᶠ[𝓝 v] z₂ := by
      filter_upwards [hO.mem_nhds hv] with v' hv'
      simp only [z₂, topVariationField, if_pos hcr]
      rw [hsame v' hv']
      rfl
    have hwv := hw v hv
    have hTd : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) T₂ (w₀ + BondCoordinates.toImaginaryCLM v) := hsm _ hwv.le
    have hline : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞)
        (fun v' : BondVector => w₀ + BondCoordinates.toImaginaryCLM v') v :=
      contDiffAt_const.add BondCoordinates.toImaginaryCLM.contDiff.contDiffAt
    have hcomp : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞)
        (fun v' : BondVector => T₂ (w₀ + BondCoordinates.toImaginaryCLM v')) v :=
      ContDiffAt.comp v hTd hline
    have hz₂ : ContDiffAt ℝ 1 z₂ v := by
      have h1 : ContDiffAt ℝ 1 (fun v' : BondVector => T₂ (w₀ + BondCoordinates.toImaginaryCLM v')) v :=
        hcomp.of_le (by norm_num)
      have h2 : ContDiffAt ℝ 1 (fun v' : BondVector => T₂ (w₀ + BondCoordinates.toImaginaryCLM v') X) v :=
        h1.clm_apply contDiffAt_const
      exact ContDiffAt.comp (g := imaginaryCoordsCLM)
        (f := fun v' : BondVector => d₀ + T₂ (w₀ + BondCoordinates.toImaginaryCLM v') X) v
        imaginaryCoordsCLM.contDiff.contDiffAt (contDiffAt_const.add h2)
    refine ⟨hz₂.congr_of_eventuallyEq hev, hvalue, ?_⟩
    rw [hev.fderiv_eq, hdc]
    have hT1 : HasFDerivAt T₂ (fderiv ℝ T₂ (w₀ + BondCoordinates.toImaginaryCLM v))
        (w₀ + BondCoordinates.toImaginaryCLM v) :=
      (hTd.differentiableAt (by norm_num)).hasFDerivAt
    have hl : HasFDerivAt (fun v' : BondVector => w₀ + BondCoordinates.toImaginaryCLM v')
        BondCoordinates.toImaginaryCLM v :=
      BondCoordinates.toImaginaryCLM.hasFDerivAt.const_add w₀
    set D := fderiv ℝ T₂ (w₀ + BondCoordinates.toImaginaryCLM v) with hD
    have e1 : HasFDerivAt (fun v' : BondVector => T₂ (w₀ + BondCoordinates.toImaginaryCLM v'))
        (D.comp BondCoordinates.toImaginaryCLM) v :=
      HasFDerivAt.comp (g := T₂) (f := fun v' : BondVector => w₀ + BondCoordinates.toImaginaryCLM v') v hT1 hl
    have e2 := e1.clm_apply (hasFDerivAt_const X v)
    have h2 := HasFDerivAt.comp (g := imaginaryCoordsCLM)
      (f := fun v' : BondVector => d₀ + T₂ (w₀ + BondCoordinates.toImaginaryCLM v') X) v
      imaginaryCoordsCLM.hasFDerivAt (e2.const_add d₀)
    have h2' : HasFDerivAt z₂ _ v := h2
    rw [h2'.fderiv]
    have h3 : ∀ y : imaginaryQuaternions, ‖D y‖ ≤ CT * ‖y‖ := fun y => by
      have h := (iteratedFDeriv ℝ 1 T₂ (w₀ + BondCoordinates.toImaginaryCLM v)).le_opNorm (fun _ => y)
      rw [iteratedFDeriv_one_apply] at h
      simp only [Finset.univ_unique, Finset.prod_singleton] at h
      exact h.trans (mul_le_mul_of_nonneg_right (hbd _ 1 hwv.le (by omega)) (norm_nonneg _))
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
    refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun e => ?_
    have e3 : ‖imaginaryCoordsCLM (D (BondCoordinates.toImaginaryCLM e) X)‖ ≤ CT * ‖e‖ := by
      rw [imaginaryCoordsCLM_apply, norm_imaginaryCoords]
      have h4 := (D (BondCoordinates.toImaginaryCLM e)).le_opNorm X
      have h5 := h3 (BondCoordinates.toImaginaryCLM e)
      rw [hX, mul_one] at h4
      rw [BondCoordinates.toImaginaryCLM_apply, norm_toImaginary] at h5
      rw [BondCoordinates.toImaginaryCLM_apply] at h4 ⊢
      exact h4.trans h5
    have e4 : ((imaginaryCoordsCLM.comp ((T₂ (w₀ + BondCoordinates.toImaginaryCLM v)).comp
        (0 : BondVector →L[ℝ] imaginaryQuaternions) + (D.comp BondCoordinates.toImaginaryCLM).flip X)) e) =
        imaginaryCoordsCLM (D (BondCoordinates.toImaginaryCLM e) X) := by
      simp
    have e5 : CT * ‖e‖ ≤ (Cs + CT) * ‖e‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    calc _ = ‖imaginaryCoordsCLM (D (BondCoordinates.toImaginaryCLM e) X)‖ := by
          rw [← e4]
      _ ≤ _ := e3.trans e5
  · have hconst : (fun v' : BondVector => _root_.YangMills.Construction.Interpolation.imaginaryCoords
        (topVariationField T 1 Q.a Q.chartRadius Q.mirrorRadius c X b.1 (toImaginary v') V)) =
        fun _ => _root_.YangMills.Construction.Interpolation.imaginaryCoords (d₀ + 0) := by
      funext v'
      simp only [topVariationField, if_neg hcr]
      rfl
    refine ⟨?_, hvalue, ?_⟩
    · rw [hconst]
      exact contDiffAt_const
    · rw [hconst]
      simp only [fderiv_fun_const, Pi.zero_apply, norm_zero]
      exact mul_nonneg (by linarith) he0.le
end TopVariation
open TopVariation in
theorem topVariationBoundedOnSchedule_holds (hOne : rightTranslationDerivUniqueStatement)
    (hFB : interpolatedFramesStatement) (hChart : rightTranslationChartStatement)
    (hJ : EventuallyInParametersCombines) : TopVariationBoundedOnParameters := by
  classical
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cq, Cz, Cr, hP⟩ := hFB
  obtain ⟨T₂, CT, hCT, hsh, hsm, hbd⟩ := hChart
  have hσ : EventuallyInParameters fun T => T.σ * (|T.Ct| + 1) ≤ 1 / 2 ∧ 0 ≤ T.Cs :=
    fun _ _ => ⟨0, fun _ _ _ _ _ => ⟨0, fun Ct _ =>
    ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, fun _ _ _ _ => ⟨0, fun _ _ => ⟨(1 / 2) / (|Ct| + 1), by positivity,
      fun σ _ hσ1 _ _ => ⟨0, fun _ hCs _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
        ⟨by
          have h1 : (0 : ℝ) < |Ct| + 1 := by positivity
          exact (le_div_iff₀ h1).1 hσ1, hCs⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  refine ⟨fun U => |U.Cs| + CT, fun T => by positivity, ?_⟩
  refine weaken _ _ ?_ (join _ _ hP hσ)
  rintro T hDr ⟨hPT, hσ1, hCs0⟩ t x f F V hst
  have h1 := (hPT t x hst.coupling_le).one_torus F V 1 hst.torus hst.small_curvature zero_le_one le_rfl
  have hσ0 := hDr.σ_pos
  have hκ := hDr.κ_pos
  have hc : TopVariationBounded (coldHalfLawAt T x f) (T.Cs + CT) V := by
    refine topVariationBounded_of_chart hOne hCT hsh hsm hbd hCs0 hκ.le (fun b => ?_) h1.variation
    have h2 := h1.small.norm_le b.1 b.2
    show ‖interpolatedFrame 1 T.a T.chainParams.ρA (frameRadius x) b.1 V‖ + T.σ / 64 ≤ 1 / 2
    have h3 : T.Ct * T.σ ≤ |T.Ct| * T.σ := mul_le_mul_of_nonneg_right (le_abs_self _) hσ0.le
    nlinarith
  have e : |(parametersBeforeSide T).Cs| + CT = T.Cs + CT := by
    show |T.Cs| + CT = T.Cs + CT
    rw [abs_of_nonneg hCs0]
  show TopVariationBounded (coldHalfLawAt T x f) (|(parametersBeforeSide T).Cs| + CT) V
  rw [e]
  exact hc
end ResponseInTheExpansion
end YangMills.Construction
end
