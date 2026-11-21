import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsInvariantAtParametersProof
import YangMills.Construction.ColdStepAtMirrorFrames.DistancesOfSitesAndCells
import YangMills.Construction.ColdStepAtMirrorFrames.LieCoordinatesProof
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfADecayOnATorus
import YangMills.Construction.ResponseInTheExpansion.EnergyAboveAFramePoint
import YangMills.Construction.ResponseInTheExpansion.SlopeOfTheOtherTerms
import YangMills.Construction.ResponseInTheExpansion.SlopeToSecondOrder
import YangMills.Construction.ResponseInTheExpansion.StepNearItsHessian
import YangMills.Construction.RunningCouplingSlope.InverseOfTheHessianOfTheChartProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.LinearResponse YangMills.Construction.WeightedResponses
namespace YangMills.Construction.ResponseInTheExpansion.StepNearHessianProof
variable {F : BlockFrame}
abbrev ChartBond (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F))
theorem toImaginary_smul (c : ℝ) (v : BondVector) : toImaginary (c • v) = c • toImaginary v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.toImaginary_smul <;> assumption
theorem toImaginary_zero : toImaginary (0 : BondVector) = 0 := by apply _root_.YangMills.SharedProofs.p2840 <;> assumption
theorem norm_toImaginary (v : BondVector) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ImaginaryCoordinates.norm_toImaginary <;> assumption
theorem add_stepCoordinates_eq_update (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (b : ChartBond F) (e : BondVector) (u : ℝ) :
    (fun x i => w x i + stepCoordinates (u • (bondVariation b e : StepVariable (finiteCells F))) x i) =
      Function.update w b.1.1 (Function.update (w b.1.1) b.1.2 (w b.1.1 b.1.2 + u • toImaginary e)) := by
  classical
  funext x i
  unfold stepCoordinates
  by_cases h : (x, i) ∈ chordBonds (finiteCells F)
  · rw [dif_pos h]
    by_cases h2 : (⟨(x, i), h⟩ : ChartBond F) = b
    · subst h2
      simp [bondVariation, toImaginary_smul]
    · have hv : (u • (bondVariation b e : StepVariable (finiteCells F))) ⟨(x, i), h⟩ = 0 := by
        have : (bondVariation b e : StepVariable (finiteCells F)) ⟨(x, i), h⟩ = 0 :=
          Pi.single_eq_of_ne h2 _
        simp [this]
      rw [hv, toImaginary_zero, add_zero]
      by_cases hx : x = b.1.1
      · subst hx
        have hi : i ≠ b.1.2 := by
          intro hi
          apply h2
          apply Subtype.ext
          exact Prod.ext rfl hi
        simp [Function.update_of_ne hi]
      · simp [Function.update_of_ne hx]
  · rw [dif_neg h, add_zero]
    have hne : ¬ (x = b.1.1 ∧ i = b.1.2) := by
      rintro ⟨rfl, rfl⟩
      exact h b.2
    by_cases hx : x = b.1.1
    · subst hx
      have hi : i ≠ b.1.2 := fun hi => hne ⟨rfl, hi⟩
      simp [Function.update_of_ne hi]
    · simp [Function.update_of_ne hx]
theorem chartedSlope_eq_fderiv (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (b : ChartBond F) (e : BondVector)
    (hd : DifferentiableAt ℝ (chartedEnergyAt a w V) 0) :
    chartedSlope a w V b.1 (toImaginary e) = fderiv ℝ (chartedEnergyAt a w V) 0 (bondVariation b e) := by
  have hf : (fun u : ℝ => chartedEnergy a (Function.update w b.1.1 (Function.update (w b.1.1) b.1.2
      (w b.1.1 b.1.2 + u • toImaginary e))) V) =
      fun u : ℝ => chartedEnergyAt a w V (u • bondVariation b e) := by
    funext u
    unfold chartedEnergyAt
    rw [add_stepCoordinates_eq_update]
  unfold chartedSlope
  rw [hf]
  have hl : HasDerivAt (fun s : ℝ => s • (bondVariation b e : StepVariable (finiteCells F)))
      (bondVariation b e) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (bondVariation b e : StepVariable (finiteCells F))
  have hd' : HasFDerivAt (chartedEnergyAt a w V) (fderiv ℝ (chartedEnergyAt a w V) 0)
      ((0 : ℝ) • (bondVariation b e : StepVariable (finiteCells F))) := by
    simpa using hd.hasFDerivAt
  exact (hd'.comp_hasDerivAt (0 : ℝ) hl).deriv
section Abstract
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem eq_sum_bondCoordinateVector (η : BondField ι) :
    η = ∑ r : ι × Fin 3, η r.1 r.2 • bondCoordinateVector r := by apply _root_.YangMills.DeltaSharedProofs.p501785 <;> assumption
theorem secondDerivAlong_eq_mulVec (E : BondField ι → ℝ) (η : BondField ι) (r : ι × Fin 3) :
    secondDerivAlong E 0 (bondCoordinateVector r) η =
      (bondCoordinateHessian E).mulVec (fun c => η c.1 c.2) r := by
  have e1 : secondDerivAlong E 0 (bondCoordinateVector r) η =
      fderiv ℝ (fun ζ => fderiv ℝ E ζ (bondCoordinateVector r)) 0 η := rfl
  rw [e1]
  conv_lhs => rw [eq_sum_bondCoordinateVector η]
  rw [map_sum]
  simp only [Matrix.mulVec, dotProduct, bondCoordinateHessian, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : secondDerivAlong E 0 (bondCoordinateVector r) (bondCoordinateVector c) =
      fderiv ℝ (fun ζ => fderiv ℝ E ζ (bondCoordinateVector r)) 0 (bondCoordinateVector c) := rfl
  rw [this]
  ring
omit [DecidableEq ι] in
theorem abs_fderiv_sub_hessian_le {E O : BondField ι → ℝ} {η u : BondField ι} {x C2 Mo Tn : ℝ}
    (hx0 : 0 < x) (hC2 : 0 ≤ C2) (hMo : 0 ≤ Mo) (hdE : DifferentiableAt ℝ E η)
    (hdO : DifferentiableAt ℝ O η)
    (hrem : |fderiv ℝ E η u - fderiv ℝ E 0 u - secondDerivAlong E 0 u η| ≤ C2 * Tn ^ 2)
    (hsl0 : x * |fderiv ℝ E 0 u| ≤ 1) (hOr : |fderiv ℝ O η u| ≤ Mo) :
    |fderiv ℝ (fun ζ => x * E ζ + O ζ) η u - x * secondDerivAlong E 0 u η| ≤
      (1 + Mo + C2) * (1 + x * Tn ^ 2) := by
  have h1 : HasFDerivAt (fun ζ => x * E ζ + O ζ) (x • fderiv ℝ E η + fderiv ℝ O η) η :=
    (hdE.hasFDerivAt.const_mul x).add hdO.hasFDerivAt
  have hfd : fderiv ℝ (fun ζ => x * E ζ + O ζ) η u = x * fderiv ℝ E η u + fderiv ℝ O η u := by
    rw [h1.fderiv]
    simp
  rw [hfd]
  generalize fderiv ℝ E η u = A at *
  generalize fderiv ℝ E 0 u = B at *
  generalize secondDerivAlong E 0 u η = D at *
  generalize fderiv ℝ O η u = G at *
  have e2 : x * A + G - x * D = x * (A - B - D) + x * B + G := by ring
  rw [e2]
  have b1 : |x * (A - B - D)| ≤ x * (C2 * Tn ^ 2) := by
    rw [abs_mul, abs_of_pos hx0]
    exact mul_le_mul_of_nonneg_left hrem hx0.le
  have b2 : |x * B| ≤ 1 := by
    rw [abs_mul, abs_of_pos hx0]
    exact hsl0
  have hq : 0 ≤ x * Tn ^ 2 := by positivity
  calc |x * (A - B - D) + x * B + G| ≤ |x * (A - B - D)| + |x * B| + |G| := abs_add_three _ _ _
    _ ≤ x * (C2 * Tn ^ 2) + 1 + Mo := by linarith
    _ ≤ (1 + Mo + C2) * (1 + x * Tn ^ 2) := by nlinarith [mul_nonneg hMo hq]
end Abstract
theorem isChartBasePoint_frameCoordField {T : StepParameters} {C : ℝ} {m : ℕ} {V : F.GaugeField F.top}
    (hFL : F.blockSide = T.L) (hroomL : C * T.σ + T.σ / 64 ≤ 1 / (64 * (T.L : ℝ)))
    (hcontL : C * T.σ + 5 * (T.L : ℝ) * (T.σ / 64) ≤ 1 / 2)
    (hsmall : FrameSmallness false T.a T.chainParams.ρA T.chainParams.δ₂ T.chainParams.κ₂ C T.σ
      T.chainParams.Kk m V) :
    IsChartBasePoint T (frameCoordField false T.a T.chainParams.ρA m V) V := by
  refine ⟨fun b hb => hsmall.norm_add_le b hb, fun b hb => ?_, ?_, fun c h π hh => ?_⟩
  · have h2 : ‖frameCoordField false T.a T.chainParams.ρA m V b.1 b.2‖ ≤ C * T.σ := hsmall.norm_le b hb
    have h3 : T.ballRadius = T.σ / 64 := rfl
    linarith
  · have h1 := hsmall.small_curvature
    simpa using h1
  · have h1 := hsmall.holonomy_ratio c h π (hFL ▸ hh)
    have h3 : T.ballRadius = T.σ / 64 := rfl
    rw [h3]
    linarith
set_option maxHeartbeats 4000000 in
theorem stepNearHessian_holds (hFr : FrameBoundsEventually) (hJ : EventuallyInParametersCombines)
    (hCv : ConvexAboveChartPoint) (hEn : EnergyAboveBasePoint)
    (hS2 : EnergySlopeSecondOrder) (hOt : RemainderSlopeBound)
    (hInv : CoordinateHessianInverseBound) (hSum : decaySumOnTorusStatement)
    (hD : SupDistCellComparison) : StepNearHessian := by
  classical
  refine hJ.2 _ _ ?_ (hJ.1 _ _ hFr (hJ.1 _ _ hCv (hJ.1 _ _ hEn (hJ.1 _ _ hS2 hOt))))
  rintro T hT ⟨hfr, hcv, hen, ⟨C2, hC20, hs2⟩, ⟨Mo, hMo0, hot⟩⟩
  obtain ⟨Cf, C, hCf0, hC1, hCfT, _, hL40, hn64, hκ1, hσ1, hroomL, hcontL, hσA, hy1, hay, hfrAll⟩ := hfr
  have hOdd : Odd T.L := hT.odd_L
  have hκ0 : 0 < T.κ := hT.κ_pos
  have hσ0 : 0 < T.σ := hT.σ_pos
  have hlam : 0 < T.chainParams.lam := hT.chain_admissible.positivity.2.2.1
  have hδ₁ : 0 < T.chainParams.δ₁ := hT.chain_admissible.positivity.1
  have hρ0 : 0 < T.ballRadius := by
    unfold StepParameters.ballRadius
    positivity
  obtain ⟨W₀, hW₀⟩ := hSum T.L (2 * T.κ) hOdd (by positivity)
  obtain ⟨S₀, hS₀⟩ := hSum T.L (T.chainParams.δ₁ / 2) hOdd (by positivity)
  set W := max W₀ 0 with hWd
  set S := max S₀ 0 with hSd
  have hW0 : 0 ≤ W := le_max_right _ _
  have hS0 : 0 ≤ S := le_max_right _ _
  have hCt0 : 0 < T.Ct := by linarith
  refine ⟨T.Ct * T.ballRadius + T.chainParams.lam + 1, W, 1 + Mo + C2, 6 * W / T.chainParams.lam, S,
    by positivity, hW0, by positivity, by positivity, hS0, ?_⟩
  intro t x f F V hx hrow hF hV
  have hx1 : 1 ≤ x := hy1.trans hx
  have hx0 : 0 < x := by linarith
  refine ⟨hx1, ?_⟩
  have hV5 : IsSmallCurvature (5 / 4 * T.σ) V := fun p hp' => (hV p hp').trans_le (by linarith)
  obtain ⟨_, hsmF, hstF, _⟩ := hfrAll t x F V hx hF hV5
  have hsmall := hsmF false
  have hstat := hstF false
  set m := frameRadius x with hm
  set w : F.Site F.depth → Fin 4 → imaginaryQuaternions :=
    frameCoordField false T.a T.chainParams.ρA m V with hw
  have hFcopy := hF
  obtain ⟨hFL, hFt, n, hside, hn⟩ := hFcopy
  have hn2 : 2 ≤ n := by omega
  have hfp : IsChartBasePoint T w V := isChartBasePoint_frameCoordField hFL hroomL hcontL hsmall
  obtain ⟨hCT, hpts, hfl, K, hK, hKrow⟩ := hen t F V w hF hV5 hfp
  set E : StepVariable (finiteCells F) → ℝ := chartedEnergyAt T.a w V with hE
  have h00 : ∀ b, ‖(0 : StepVariable (finiteCells F)) b‖ ≤ T.ballRadius := fun b => by
    simpa using hρ0.le
  have hE0 : ContDiffAt ℝ 3 E 0 := (hpts 0 h00).2
  have hEd0 : DifferentiableAt ℝ E 0 := hE0.differentiableAt (by norm_num)
  refine ⟨hE0, ?_⟩
  have hs1 : ∀ (b : ChartBond F) (e : BondVector), ‖e‖ = 1 → x * |bondPartialDeriv E b 0 e| ≤ 1 := by
    intro b e he
    have h1 := hstat.firstDeriv_bound b.1 b.2 (toImaginary e) (by rw [norm_toImaginary, he])
    have h2 : frameFirstDeriv false T.a T.chainParams.ρA m b.1 (toImaginary e) V =
        fderiv ℝ E 0 (bondVariation b e) :=
      chartedSlope_eq_fderiv T.a w V b e hEd0
    rw [h2] at h1
    exact h1
  obtain ⟨hmem, hslp⟩ :=
    hcv t x f F V w 1 hx ⟨hrow.smooth, hrow.decay⟩ hF hV5 hfp hs1 zero_le_one le_rfl
  have hP : stepExponent false T.a T.chainParams.ρA x m f 1 V = exponentInChart T.a x w f 1 V := rfl
  rw [hP]
  have hdist : IsPseudoMetricOnBonds (chordBondDist F) := by
    refine ⟨fun b => ?_, fun b b' => ?_, fun b b' b'' => ?_⟩
    · have := (hD.1 F F.top (enclosingCell b.1.1) (enclosingCell b.1.1) (enclosingCell b.1.1)).1
      change ((siteSupDist (enclosingCell b.1.1) (enclosingCell b.1.1) : ℕ) : ℝ) = 0
      simp [this]
    · have := (hD.1 F F.top (enclosingCell b.1.1) (enclosingCell b'.1.1) (enclosingCell b.1.1)).2.1
      change ((siteSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℕ) : ℝ) = _
      rw [this]
      rfl
    · have := (hD.1 F F.top (enclosingCell b.1.1) (enclosingCell b'.1.1) (enclosingCell b''.1.1)).2.2
      change ((siteSupDist (enclosingCell b.1.1) (enclosingCell b''.1.1) : ℕ) : ℝ) ≤
        ((siteSupDist (enclosingCell b.1.1) (enclosingCell b'.1.1) : ℕ) : ℝ) +
          ((siteSupDist (enclosingCell b'.1.1) (enclosingCell b''.1.1) : ℕ) : ℝ)
      exact_mod_cast this
  have hweights : ∀ b₀ : ChartBond F, ∑ b, Real.exp (-(2 * T.κ * chordBondDist F b b₀)) ≤ W := fun b₀ =>
    ((hW₀ F n hFL hn2 hside (enclosingCell b₀.1.1)).1).trans (le_max_left _ _)
  obtain ⟨hsym, hdet, hinv⟩ := hInv (ChartBond F) E K (chordBondDist F) T.chainParams.lam T.κ W hlam
    hκ0.le hdist hE0 hfl hK hKrow hweights
  refine ⟨hdist, hmem, hweights, hslp, hsym, hdet, hinv, ?_, fun _ _ => (Real.exp_pos _).le, ?_⟩
  · intro η hη r
    have hη' : ∀ b, ‖η b‖ ≤ T.ballRadius := fun b => (hη b).le
    have hdE : DifferentiableAt ℝ E η := (hpts η hη').2.differentiableAt (by norm_num)
    obtain ⟨hdO, hOb⟩ :=
      hot t x f F V w 1 hx ⟨hrow.smooth, hrow.decay⟩ hF hfp zero_le_one le_rfl η hη'
    have he1 : ‖(EuclideanSpace.single r.2 (1 : ℝ) : BondVector)‖ = 1 := by simp
    have hsplit : exponentInChart T.a x w f 1 V =
        fun ζ => x * E ζ + exponentMinusEnergy T.a x w f 1 V ζ := by
      funext ζ
      simp only [exponentMinusEnergy, hE]
      ring
    have hseg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        IsAdmissibleChartPoint T.L T.chainParams.σA (shiftCoordinates w (s • η)) V := by
      intro s h0 h1
      refine (hpts (s • η) fun b => ?_).1
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
      have := hη' b
      have h2 := norm_nonneg (η b)
      nlinarith
    have hrem := hs2 F V w η hCT hseg r.1 (EuclideanSpace.single r.2 1) he1
    have hsl0 := hs1 r.1 _ he1
    have hOr := hOb r.1 (EuclideanSpace.single r.2 1)
    rw [he1, mul_one] at hOr
    rw [hsplit, ← secondDerivAlong_eq_mulVec]
    exact abs_fderiv_sub_hessian_le hx0 hC20.le hMo0 hdE hdO hrem hsl0 hOr
  · intro b
    have hsymm : ∀ b' : ChartBond F,
        chordBondDist F b b' = (cellSupDist (enclosingCell b'.1.1) (enclosingCell b.1.1) : ℝ) := by
      intro b'
      exact hdist.symm b b'
    have h1 := ((hS₀ F n hFL hn2 hside (enclosingCell b.1.1)).1).trans (le_max_left S₀ 0)
    simp only [hsymm]
    exact h1
end YangMills.Construction.ResponseInTheExpansion.StepNearHessianProof
end
