import YangMills.Construction.ClusterExpansionOfAStep.MovesOfFreeBondsForm
import YangMills.Construction.ClusterExpansionOfAStep.PlaquettesUnderGaugesAndMoves
import YangMills.Construction.ColdStepAtMirrorFrames.ConvexAboveAChartPointProof
import YangMills.Construction.ColdStepAtMirrorFrames.SecondDerivativeThroughTheChart
import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAlongAMotion
import YangMills.Construction.SummableBoundsOfTheFlow.ExponentBetweenBoundsProof
import YangMills.Construction.SummableBoundsOfTheFlow.MoveOfTheTopAlongItsField
import YangMills.Construction.SummableBoundsOfTheFlow.RightShiftMovesTheLogarithm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Estimates
namespace Interpolation
namespace TopVariation
variable {F : BlockFrame}
theorem toImaginary_add (u v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (u + v) = toImaginary u + toImaginary v := by apply _root_.YangMills.Construction.FreeBondMoves.toImaginary_add <;> assumption
theorem toImaginary_smul (r : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (r • u) = r • toImaginary u := by apply _root_.YangMills.Construction.FreeBondMoves.toImaginary_smul <;> assumption
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem toImaginary_imaginaryCoords (y : imaginaryQuaternions) : toImaginary (imaginaryCoords y) = y := by
  apply Subtype.ext
  have hy : (y : ℍ[ℝ]).re = 0 := y.2
  ext <;> simp [toImaginary, imaginaryCoords, hy]
theorem stepCoordinates_add (ζ ζ' : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (ζ + ζ') x i = stepCoordinates ζ x i + stepCoordinates ζ' x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_add <;> assumption
theorem stepCoordinates_smul (r : ℝ) (ζ : StepVariable (finiteCells F)) (x : F.Site F.depth) (i : Fin 4) :
    stepCoordinates (r • ζ) x i = r • stepCoordinates ζ x i := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HessianConvexity.stepCoordinates_smul <;> assumption
theorem expUnit_zero : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
theorem chartedField_eq_leftTranslate {Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
    {U : Set (imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)}
    (hexp : ∀ w ∈ U, expUnit (Θ w) = expUnit w.1 * expUnit w.2.1 * (expUnit w.2.2)⁻¹)
    (A q v : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V V' : F.GaugeField F.top)
    (hU : ∀ x i, ¬ IsAxialTreeBond (x, i) → (A x i, q x i, v x i) ∈ U)
    (hcross : ∀ x i, IsCrossingBond (x, i) → V' (enclosingCell x) i = expUnit (q x i) * V (enclosingCell x) i)
    (hchord : ∀ x i, ¬ IsCrossingBond (x, i) → q x i = 0) :
    chartedField A V' = leftTranslate (fun x i => open Classical in
      if IsAxialTreeBond (x, i) then 0 else Θ (A x i, q x i, v x i)) (chartedField v V) := by
  classical
  funext x i
  simp only [leftTranslate, chartedField]
  by_cases hc : IsCrossingBond (x, i)
  · have ht : ¬ IsAxialTreeBond (x, i) := fun h => h.1 hc
    rw [if_pos hc, if_pos hc, if_neg ht, hexp _ (hU x i ht), hcross x i hc]
    simp [mul_assoc]
  · rw [if_neg hc, if_neg hc]
    by_cases ht : IsAxialTreeBond (x, i)
    · rw [if_pos ht, if_pos ht, if_pos ht, expUnit_zero, mul_one]
    · rw [if_neg ht, if_neg ht, if_neg ht, hexp _ (hU x i ht), hchord x i hc, expUnit_zero]
      simp [mul_assoc]
theorem motionComponent_eq_of_deriv_eq {j : ℕ} {r : ℕ}
    (α β : (Fin 1 → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions) (e : Fin r → Fin 1) (hr : 0 < r)
    (he : Function.Injective e)
    (h : ∀ x i, iteratedFDeriv ℝ 1 (fun τ => α τ x i) 0 (fun _ => Pi.single 0 1) =
      iteratedFDeriv ℝ 1 (fun τ => β τ x i) 0 (fun _ => Pi.single 0 1)) :
    motionComponent α e = motionComponent β e := by
  have hle : r ≤ 1 := by
    have := Fintype.card_le_of_injective e he
    simpa using this
  obtain rfl : r = 1 := by omega
  funext x i
  unfold motionComponent
  have hconst : (fun l : Fin 1 => (Pi.single (e l) 1 : Fin 1 → ℝ)) = fun _ => Pi.single 0 1 := by
    funext l
    rw [Subsingleton.elim (e l) 0]
  rw [hconst]
  exact h x i
def topPerturbation (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (V : F.GaugeField F.top)
    (τ : Fin 1 → ℝ) : F.GaugeField F.top :=
  leftTranslate (ColdStepAtMirrorFrames.bondSpread (fun _ : Fin 1 => c) (fun _ => X) τ) V
open Classical in
def crossingComponent (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (x : F.Site F.depth) (i : Fin 4) :
    imaginaryQuaternions :=
  if IsCrossingBond (x, i) ∧ c = (enclosingCell x, i) then X else 0
open Classical in
def topMotion (Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions)
    (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F))
    (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (τ : Fin 1 → ℝ) (x : F.Site F.depth) (i : Fin 4) :
    imaginaryQuaternions :=
  if IsAxialTreeBond (x, i) then 0 else
    Θ (interpolatedCoords s a ρA m (topPerturbation c X V τ) η x i, τ 0 • crossingComponent c X x i,
      interpolatedCoords s a ρA m V η x i)
open Classical in
def chordMotion (Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions)
    (s a ρA : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η z : StepVariable (finiteCells F)) (τ : Fin 1 → ℝ) (x : F.Site F.depth) (i : Fin 4) :
    imaginaryQuaternions :=
  if IsAxialTreeBond (x, i) then 0 else
    Θ (interpolatedCoords s a ρA m V η x i + τ 0 • stepCoordinates z x i, 0, interpolatedCoords s a ρA m V η x i)
theorem bondSpread_single {j : ℕ} (c : F.Site j × Fin 4) (X : imaginaryQuaternions) (τ : Fin 1 → ℝ)
    (y : F.Site j) (i : Fin 4) :
    ColdStepAtMirrorFrames.bondSpread (fun _ : Fin 1 => c) (fun _ => X) τ y i = τ 0 • (if c = (y, i) then X else 0) := by
  simp only [ColdStepAtMirrorFrames.bondSpread, Finset.univ_unique, Finset.sum_singleton]
  split_ifs <;> simp
theorem leftTranslate_bondSpread_zero {j : ℕ} {W : F.GaugeField j} {k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    leftTranslate (ColdStepAtMirrorFrames.bondSpread c X 0) W = W := by
  funext y i
  simp [leftTranslate, ColdStepAtMirrorFrames.bondSpread, expUnit_zero]
theorem topPerturbation_zero (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (V : F.GaugeField F.top) :
    topPerturbation c X V 0 = V :=
  leftTranslate_bondSpread_zero _ _
theorem topPerturbation_crossing (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (V : F.GaugeField F.top)
    (τ : Fin 1 → ℝ) (x : F.Site F.depth) (i : Fin 4) (h : IsCrossingBond (x, i)) :
    topPerturbation c X V τ (enclosingCell x) i =
      expUnit (τ 0 • crossingComponent c X x i) * V (enclosingCell x) i := by
  classical
  simp only [topPerturbation, leftTranslate, bondSpread_single, crossingComponent]
  by_cases hc : c = (enclosingCell x, i)
  · simp [hc, h]
  · simp [hc]
theorem crossingComponent_of_not_crossing (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions)
    (x : F.Site F.depth) (i : Fin 4) (h : ¬ IsCrossingBond (x, i)) :
    crossingComponent c X x i = 0 := by
  classical
  simp [crossingComponent, h]
theorem iteratedFDeriv_comp_diagonalTriple
    {Θ : imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions → imaginaryQuaternions}
    {w : imaginaryQuaternions} (hΘ : DifferentiableAt ℝ Θ (diagonalTriple w))
    (g : (Fin 1 → ℝ) → imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions)
    (hg : DifferentiableAt ℝ g 0) (h0 : g 0 = diagonalTriple w) :
    iteratedFDeriv ℝ 1 (fun τ => Θ (g τ)) 0 (fun _ => Pi.single 0 1) =
      fderiv ℝ Θ (diagonalTriple w) (fderiv ℝ g 0 (Pi.single 0 1)) := by
  rw [iteratedFDeriv_one_apply]
  have hΘg : HasFDerivAt Θ (fderiv ℝ Θ (diagonalTriple w)) (g 0) := by
    rw [h0]
    exact hΘ.hasFDerivAt
  have hcomp := (hΘg.comp 0 hg.hasFDerivAt).fderiv
  change fderiv ℝ (Θ ∘ g) 0 (Pi.single 0 1) = _
  rw [hcomp]
  rfl
theorem fderiv_curve_through_top (P : (Fin 1 → ℝ) → imaginaryQuaternions) (y w : imaginaryQuaternions)
    (hP : DifferentiableAt ℝ P 0) :
    fderiv ℝ (fun τ : Fin 1 → ℝ => (P τ, τ 0 • y, w)) 0 (Pi.single 0 1) =
      (fderiv ℝ P 0 (Pi.single 0 1), y, 0) := by
  have hl : HasFDerivAt (fun τ : Fin 1 → ℝ => τ 0 • y)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight y) 0 :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight y).hasFDerivAt
  have h := hP.hasFDerivAt.prodMk (hl.prodMk (hasFDerivAt_const w (0 : Fin 1 → ℝ)))
  rw [h.fderiv]
  simp
theorem fderiv_curve_through_chart (y w : imaginaryQuaternions) :
    fderiv ℝ (fun τ : Fin 1 → ℝ => (w + τ 0 • y, (0 : imaginaryQuaternions), w)) 0 (Pi.single 0 1) =
      (y, 0, 0) := by
  have hl : HasFDerivAt (fun τ : Fin 1 → ℝ => w + τ 0 • y)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight y) 0 :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight y).hasFDerivAt.const_add w
  have h := hl.prodMk ((hasFDerivAt_const (0 : imaginaryQuaternions) (0 : Fin 1 → ℝ)).prodMk
    (hasFDerivAt_const w (0 : Fin 1 → ℝ)))
  rw [h.fderiv]
  simp
end TopVariation
open TopVariation in
set_option maxHeartbeats 1600000 in
theorem topVariationAlongField_proof (hExp : expansionAlongMotionStatement)
    (hLog : ConjugatedExpLogSmooth) (hSh : logDerivAlongRightTranslationStatement)
    (hSec : ChartSecondDerivBound) (hCov : BlocksCoverLowerLevel) :
    topVariationAlongField := by
  classical
  intro F s a ρA ρ m V Th hL hs hρ hTh hAn hroom G η c X hη hG
  obtain ⟨Θ, U, C₀, hU, -, hdiag, hsm, hexp, hzero, -, -, -⟩ := hLog
  have hM := hSh Θ U hU hdiag hsm hexp hzero
  have hsd : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hper : ∀ i, F.period F.depth i ≠ 0 := by
    intro i
    have h1 : F.extent i ≠ 0 := (hsd i).ne'
    have h2 : F.blockSide ≠ 0 := by have := hL.pos; omega
    simp [BlockFrame.period, h1, h2]
  have hnz : ∀ i, NeZero (F.period F.depth i) := fun i => ⟨hper i⟩
  have hfin : Finite (F.Site F.depth) := by
    have : ∀ i, Finite (ZMod (F.period F.depth i)) := fun i => by
      have := hnz i
      infer_instance
    exact Pi.finite
  set v := interpolatedCoords s a ρA m V η with hv
  have hW : interpolatedField s a ρA m V η = chartedField v V := rfl
  have hchart : ∀ x i, ¬ IsAxialTreeBond (x, i) → (x, i) ∈ chordBonds (finiteCells F) := by
    intro x i h
    unfold chordBonds innerBonds
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨⟨hCov F hL hsd x, hCov F hL hsd _⟩, h⟩
  have hcoordη : ∀ x i (h : ¬ IsAxialTreeBond (x, i)),
      stepCoordinates η x i = toImaginary (η ⟨(x, i), hchart x i h⟩) := by
    intro x i h
    unfold stepCoordinates
    rw [dif_pos (hchart x i h)]
  have hvsmall : ∀ x i, ¬ IsAxialTreeBond (x, i) → ‖v x i‖ ≤ 1 := by
    intro x i h
    have h1 := hroom (x, i) (hchart x i h)
    have h2 := hη ⟨(x, i), hchart x i h⟩
    have h3 : v x i = interpolatedFrame s a ρA m (x, i) V + stepCoordinates η x i := rfl
    rw [h3, hcoordη x i h]
    have h4 := norm_add_le (interpolatedFrame s a ρA m (x, i) V) (toImaginary (η ⟨(x, i), hchart x i h⟩))
    rw [norm_toImaginary] at h4
    linarith
  have hvπ : ∀ x i, ¬ IsAxialTreeBond (x, i) → ‖v x i‖ < Real.pi := fun x i h =>
    lt_of_le_of_lt (hvsmall x i h) (by linarith [Real.pi_gt_three])
  set z : StepVariable (finiteCells F) := fun b =>
    imaginaryCoords (topVariationField Th s a ρA m c X b.1 (toImaginary (η b)) V) with hz
  have hz' : ∀ x i, ¬ IsAxialTreeBond (x, i) → stepCoordinates z x i =
      bondDeriv (interpolatedFrame s a ρA m (x, i)) V (fun _ : Fin 1 => c) (fun _ => X) +
        if IsCrossingBond (x, i) ∧ (enclosingCell x, i) = c then Th (v x i) X else 0 := by
    intro x i h
    have e1 : stepCoordinates z x i = toImaginary (z ⟨(x, i), hchart x i h⟩) := by
      unfold stepCoordinates
      rw [dif_pos (hchart x i h)]
    rw [e1, hz]
    simp only [toImaginary_imaginaryCoords, topVariationField]
    have e2 : v x i = interpolatedFrame s a ρA m (x, i) V + toImaginary (η ⟨(x, i), hchart x i h⟩) := by
      rw [← hcoordη x i h]
      rfl
    rw [e2]
  have hΘd : ∀ w : imaginaryQuaternions, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) Θ (diagonalTriple w) := fun w =>
    (hsm.contDiffAt (hU.mem_nhds (hdiag w))).of_le (by norm_num)
  have hp : ∀ x i, ¬ IsAxialTreeBond (x, i) → ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun τ : Fin 1 → ℝ => interpolatedCoords s a ρA m (topPerturbation c X V τ) η x i) 0 := by
    intro x i h
    have h1 := (hAn (x, i) (hchart x i h) 1 (fun _ => c) (fun _ => X)).contDiffAt (n := ((1 : ℕ) : WithTop ℕ∞))
    exact h1.add contDiffAt_const
  have hτ : ∀ y : imaginaryQuaternions, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun τ : Fin 1 → ℝ => τ 0 • y) 0 :=
    fun y => ((contDiff_apply ℝ ℝ (0 : Fin 1)).smul contDiff_const).contDiffAt
  have hg₁ : ∀ x i, ¬ IsAxialTreeBond (x, i) → ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun τ : Fin 1 → ℝ => (interpolatedCoords s a ρA m (topPerturbation c X V τ) η x i,
        τ 0 • crossingComponent c X x i, v x i)) 0 :=
    fun x i h => (hp x i h).prodMk ((hτ _).prodMk contDiffAt_const)
  have hg₂ : ∀ x i, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun τ : Fin 1 → ℝ => (v x i + τ 0 • stepCoordinates z x i, (0 : imaginaryQuaternions), v x i)) 0 :=
    fun x i => (contDiffAt_const.add (hτ _)).prodMk (contDiffAt_const.prodMk contDiffAt_const)
  have h0₁ : ∀ x i, ((interpolatedCoords s a ρA m (topPerturbation c X V 0) η x i,
      (0 : Fin 1 → ℝ) 0 • crossingComponent c X x i, v x i) :
      imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) = diagonalTriple (v x i) := by
    intro x i
    simp [topPerturbation_zero, diagonalTriple, hv]
  have h0₂ : ∀ x i, ((v x i + (0 : Fin 1 → ℝ) 0 • stepCoordinates z x i, (0 : imaginaryQuaternions), v x i) :
      imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) = diagonalTriple (v x i) := by
    intro x i
    simp [diagonalTriple]
  have hs₁ : ∀ x i, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun τ => topMotion Θ s a ρA m V η c X τ x i) 0 := by
    intro x i
    by_cases h : IsAxialTreeBond (x, i)
    · simp only [topMotion, if_pos h]
      exact contDiffAt_const
    · simp only [topMotion, if_neg h]
      have h1 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) Θ
          (interpolatedCoords s a ρA m (topPerturbation c X V 0) η x i,
            (0 : Fin 1 → ℝ) 0 • crossingComponent c X x i, v x i) := by
        rw [h0₁]
        exact hΘd _
      exact ContDiffAt.comp (0 : Fin 1 → ℝ) h1 (hg₁ x i h)
  have hs₂ : ∀ x i, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun τ => chordMotion Θ s a ρA m V η z τ x i) 0 := by
    intro x i
    by_cases h : IsAxialTreeBond (x, i)
    · simp only [chordMotion, if_pos h]
      exact contDiffAt_const
    · simp only [chordMotion, if_neg h]
      have h1 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) Θ
          (v x i + (0 : Fin 1 → ℝ) 0 • stepCoordinates z x i, (0 : imaginaryQuaternions), v x i) := by
        rw [h0₂]
        exact hΘd _
      exact ContDiffAt.comp (0 : Fin 1 → ℝ) h1 (hg₂ x i)
  have hz₁ : ∀ x i, topMotion Θ s a ρA m V η c X 0 x i = 0 := by
    intro x i
    by_cases h : IsAxialTreeBond (x, i)
    · simp only [topMotion, if_pos h]
    · simp only [topMotion, if_neg h]
      rw [show _ = diagonalTriple (v x i) from h0₁ x i, hzero]
  have hz₂ : ∀ x i, chordMotion Θ s a ρA m V η z 0 x i = 0 := by
    intro x i
    by_cases h : IsAxialTreeBond (x, i)
    · simp only [chordMotion, if_pos h]
    · simp only [chordMotion, if_neg h]
      rw [show _ = diagonalTriple (v x i) from h0₂ x i, hzero]
  have hev₁ : ∀ᶠ τ in 𝓝 (0 : Fin 1 → ℝ), interpolatedField s a ρA m (topPerturbation c X V τ) η =
      leftTranslate (topMotion Θ s a ρA m V η c X τ) (interpolatedField s a ρA m V η) := by
    have h1 : ∀ᶠ τ in 𝓝 (0 : Fin 1 → ℝ), ∀ x i, ¬ IsAxialTreeBond (x, i) →
        ((interpolatedCoords s a ρA m (topPerturbation c X V τ) η x i, τ 0 • crossingComponent c X x i, v x i) :
          imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) ∈ U := by
      refine Filter.eventually_all.2 fun x => Filter.eventually_all.2 fun i => ?_
      by_cases h : IsAxialTreeBond (x, i)
      · exact Filter.Eventually.of_forall fun τ h' => absurd h h'
      · have h2 := (hg₁ x i h).continuousAt.eventually
          (hU.mem_nhds (by
            have e := h0₁ x i
            beta_reduce
            rw [e]
            exact hdiag _))
        filter_upwards [h2] with τ hτ _
        exact hτ
    filter_upwards [h1] with τ hτ
    exact chartedField_eq_leftTranslate hexp _ (fun x i => τ 0 • crossingComponent c X x i) v V
      (topPerturbation c X V τ) hτ
      (fun x i h => topPerturbation_crossing c X V τ x i h)
      (fun x i h => by simp [crossingComponent_of_not_crossing c X x i h])
  have hev₂ : ∀ᶠ τ in 𝓝 (0 : Fin 1 → ℝ), interpolatedField s a ρA m V (η + τ 0 • z) =
      leftTranslate (chordMotion Θ s a ρA m V η z τ) (interpolatedField s a ρA m V η) := by
    have h1 : ∀ᶠ τ in 𝓝 (0 : Fin 1 → ℝ), ∀ x i, ¬ IsAxialTreeBond (x, i) →
        ((v x i + τ 0 • stepCoordinates z x i, (0 : imaginaryQuaternions), v x i) :
          imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) ∈ U := by
      refine Filter.eventually_all.2 fun x => Filter.eventually_all.2 fun i => ?_
      by_cases h : IsAxialTreeBond (x, i)
      · exact Filter.Eventually.of_forall fun τ h' => absurd h h'
      · have h2 := (hg₂ x i).continuousAt.eventually
          (hU.mem_nhds (by
            have e := h0₂ x i
            beta_reduce
            rw [e]
            exact hdiag _))
        filter_upwards [h2] with τ hτ _
        exact hτ
    filter_upwards [h1] with τ hτ
    have e1 : interpolatedCoords s a ρA m V (η + τ 0 • z) = fun x i => v x i + τ 0 • stepCoordinates z x i := by
      funext x i
      simp only [interpolatedCoords, hv, stepCoordinates_add, stepCoordinates_smul]
      rw [add_assoc]
    have e2 : interpolatedField s a ρA m V (η + τ 0 • z) =
        chartedField (fun x i => v x i + τ 0 • stepCoordinates z x i) V := by
      unfold interpolatedField
      rw [e1]
    rw [e2]
    exact chartedField_eq_leftTranslate hexp _ (fun _ _ => 0) v V V hτ (fun x i _ => by simp [expUnit_zero])
      (fun _ _ _ => rfl)
  have hparts : ∀ x i, iteratedFDeriv ℝ 1 (fun τ => topMotion Θ s a ρA m V η c X τ x i) 0
      (fun _ => Pi.single 0 1) =
      iteratedFDeriv ℝ 1 (fun τ => chordMotion Θ s a ρA m V η z τ x i) 0 (fun _ => Pi.single 0 1) := by
    intro x i
    by_cases h : IsAxialTreeBond (x, i)
    · simp only [topMotion, chordMotion, if_pos h]
    · simp only [topMotion, chordMotion, if_neg h]
      have d0 := ((hΘd (v x i)).differentiableAt (by simp))
      have dg₁ := (hg₁ x i h).differentiableAt (by simp)
      have dg₂ := (hg₂ x i).differentiableAt (by simp)
      rw [iteratedFDeriv_comp_diagonalTriple d0 _ dg₁ (h0₁ x i),
        iteratedFDeriv_comp_diagonalTriple d0 _ dg₂ (h0₂ x i)]
      have hdp : DifferentiableAt ℝ
          (fun τ : Fin 1 → ℝ => interpolatedCoords s a ρA m (topPerturbation c X V τ) η x i) 0 :=
        (hp x i h).differentiableAt (by simp)
      have hD : fderiv ℝ (fun τ : Fin 1 → ℝ => interpolatedCoords s a ρA m (topPerturbation c X V τ) η x i) 0
          (Pi.single 0 1) =
          bondDeriv (interpolatedFrame s a ρA m (x, i)) V (fun _ : Fin 1 => c) (fun _ => X) := by
        unfold bondDeriv
        rw [iteratedFDeriv_one_apply]
        change fderiv ℝ (fun τ : Fin 1 → ℝ =>
            interpolatedFrame s a ρA m (x, i) (topPerturbation c X V τ) + stepCoordinates η x i) 0
          (Pi.single 0 1) = fderiv ℝ (fun τ : Fin 1 → ℝ =>
            interpolatedFrame s a ρA m (x, i) (topPerturbation c X V τ)) 0 (Pi.single 0 1)
        rw [fderiv_add_const]
      rw [fderiv_curve_through_top _ _ _ hdp, fderiv_curve_through_chart, hD, hz' x i h]
      by_cases hm : IsCrossingBond (x, i) ∧ (enclosingCell x, i) = c
      · have hc : crossingComponent c X x i = X := by
          simp [crossingComponent, hm.1, hm.2.symm]
        rw [hc, if_pos hm]
        have e1 : ((bondDeriv (interpolatedFrame s a ρA m (x, i)) V (fun _ : Fin 1 => c) (fun _ => X), X, 0) :
            imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) =
            (bondDeriv (interpolatedFrame s a ρA m (x, i)) V (fun _ : Fin 1 => c) (fun _ => X), 0, 0) +
              (0, X, 0) := by
          simp
        have e2 : ((bondDeriv (interpolatedFrame s a ρA m (x, i)) V (fun _ : Fin 1 => c) (fun _ => X) +
              Th (v x i) X, 0, 0) :
            imaginaryQuaternions × imaginaryQuaternions × imaginaryQuaternions) =
            (bondDeriv (interpolatedFrame s a ρA m (x, i)) V (fun _ : Fin 1 => c) (fun _ => X), 0, 0) +
              (Th (v x i) X, 0, 0) := by
          simp
        rw [e1, e2, map_add, map_add]
        congr 1
        apply Subtype.ext
        rw [(hM (v x i) X).1, (hM (v x i) X).2 _ (hTh _ _ (hvπ x i h))]
      · have hc : crossingComponent c X x i = 0 := by
          simp only [crossingComponent]
          rw [if_neg]
          rintro ⟨h1, h2⟩
          exact hm ⟨h1, h2.symm⟩
        rw [hc, if_neg hm, add_zero]
  have E₁ := hExp.1 F F.depth 1 G (interpolatedField s a ρA m V η) (topMotion Θ s a ρA m V η c X) hper
    (fun q c' X' => (hG q c' X').of_le (by norm_num)) hs₁ hz₁
  have E₂ := hExp.1 F F.depth 1 G (interpolatedField s a ρA m V η) (chordMotion Θ s a ρA m V η z) hper
    (fun q c' X' => (hG q c' X').of_le (by norm_num)) hs₂ hz₂
  have hsame : iteratedFDeriv ℝ 1 (fun τ => G (leftTranslate (topMotion Θ s a ρA m V η c X τ)
      (interpolatedField s a ρA m V η))) 0 (fun l => Pi.single l 1) =
      iteratedFDeriv ℝ 1 (fun τ => G (leftTranslate (chordMotion Θ s a ρA m V η z τ)
      (interpolatedField s a ρA m V η))) 0 (fun l => Pi.single l 1) := by
    rw [E₁.2, E₂.2]
    refine Finset.sum_congr rfl fun o _ => ?_
    congr 1
    funext l
    exact motionComponent_eq_of_deriv_eq _ _ (o.emb l) (o.partSize_pos l) (o.emb_strictMono l).injective hparts
  have hleft : bondDeriv (fun V' => G (interpolatedField s a ρA m V' η)) V (fun _ : Fin 1 => c) (fun _ => X) =
      iteratedFDeriv ℝ 1 (fun τ => G (leftTranslate (topMotion Θ s a ρA m V η c X τ)
        (interpolatedField s a ρA m V η))) 0 (fun l => Pi.single l 1) := by
    have e1 : (fun τ : Fin 1 → ℝ => G (interpolatedField s a ρA m (topPerturbation c X V τ) η)) =ᶠ[𝓝 0]
        fun τ => G (leftTranslate (topMotion Θ s a ρA m V η c X τ) (interpolatedField s a ρA m V η)) := by
      filter_upwards [hev₁] with τ hτ
      rw [hτ]
    rw [← (Filter.EventuallyEq.iteratedFDeriv ℝ e1 1).self_of_nhds]
    rfl
  obtain ⟨Cs, -, hsec⟩ := hSec
  have hread := (hsec F V v ℝ G (fun b hb => hvsmall b.1 b.2 (by
    have : b ∈ chordBonds (finiteCells F) := hb
    simp only [chordBonds, Finset.mem_filter] at this
    exact this.2)) hG).1
  have hshift : (fun ζ => G (interpolatedField s a ρA m V ζ)) = fun ζ => readInChart G v V (ζ - η) := by
    funext ζ
    have e : interpolatedCoords s a ρA m V ζ = fun x i => v x i + stepCoordinates (ζ - η) x i := by
      funext x i
      have : stepCoordinates ζ x i = stepCoordinates η x i + stepCoordinates (ζ - η) x i := by
        rw [← stepCoordinates_add]
        simp
      simp only [interpolatedCoords, hv, this]
      rw [add_assoc]
    change G (chartedField (interpolatedCoords s a ρA m V ζ) V) =
      G (chartedField (fun x i => v x i + stepCoordinates (ζ - η) x i) V)
    rw [e]
  have hd : DifferentiableAt ℝ (fun ζ => G (interpolatedField s a ρA m V ζ)) η := by
    rw [hshift]
    have h1 : DifferentiableAt ℝ (readInChart G v V) (η - η) := by
      rw [sub_self]
      exact hread.differentiableAt (by simp)
    have h2 : DifferentiableAt ℝ (fun ζ : StepVariable (finiteCells F) => ζ - η) η :=
      differentiableAt_id.sub_const η
    exact DifferentiableAt.comp (g := readInChart G v V) (f := fun ζ : StepVariable (finiteCells F) => ζ - η) η h1 h2
  have hsum : ∑ b : ↥(chordBonds (finiteCells F)),
      bondPartialDeriv (fun ζ => G (interpolatedField s a ρA m V ζ)) b η (z b) =
      fderiv ℝ (fun ζ => G (interpolatedField s a ρA m V ζ)) η z := by
    simp only [bondPartialDeriv, bondVariation]
    rw [← map_sum]
    congr 1
    exact Finset.univ_sum_single z
  have hright : iteratedFDeriv ℝ 1 (fun τ => G (leftTranslate (chordMotion Θ s a ρA m V η z τ)
      (interpolatedField s a ρA m V η))) 0 (fun l => Pi.single l 1) =
      fderiv ℝ (fun ζ => G (interpolatedField s a ρA m V ζ)) η z := by
    have e1 : (fun τ : Fin 1 → ℝ => G (interpolatedField s a ρA m V (η + τ 0 • z))) =ᶠ[𝓝 0]
        fun τ => G (leftTranslate (chordMotion Θ s a ρA m V η z τ) (interpolatedField s a ρA m V η)) := by
      filter_upwards [hev₂] with τ hτ
      rw [hτ]
    rw [← (Filter.EventuallyEq.iteratedFDeriv ℝ e1 1).self_of_nhds, iteratedFDeriv_one_apply]
    have hl : HasFDerivAt (fun τ : Fin 1 → ℝ => η + τ 0 • z)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight z) 0 := by
      have := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight z).hasFDerivAt
        (x := (0 : Fin 1 → ℝ))
      exact this.const_add η
    have hd' : HasFDerivAt (fun ζ => G (interpolatedField s a ρA m V ζ))
        (fderiv ℝ (fun ζ => G (interpolatedField s a ρA m V ζ)) η) (η + (0 : Fin 1 → ℝ) 0 • z) := by
      simpa using hd.hasFDerivAt
    have := (hd'.comp (0 : Fin 1 → ℝ) hl).fderiv
    change fderiv ℝ ((fun ζ => G (interpolatedField s a ρA m V ζ)) ∘ fun τ : Fin 1 → ℝ => η + τ 0 • z) 0 _ = _
    rw [this]
    simp
  rw [hleft, hsame, hright, ← hsum]
end Interpolation
end YangMills.Construction
end
