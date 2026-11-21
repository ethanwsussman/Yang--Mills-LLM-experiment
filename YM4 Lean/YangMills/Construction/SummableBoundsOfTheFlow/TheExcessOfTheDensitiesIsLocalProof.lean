import YangMills.Construction.SummableBoundsOfTheFlow.FreezingOfABlockExpansion
import YangMills.Construction.SummableBoundsOfTheFlow.FreezingOfTheWeightPart
import YangMills.Construction.SummableBoundsOfTheFlow.ParityOfTheScaledMeans
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreMeansAtAScale
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAtTheScaleZero
import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessIsADensityProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheMeansMoveWithTheirWeight
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledPartsAreSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory Set
namespace YangMills.Construction.StepDensities
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ScaledVariables YangMills.Construction.Interpolation YangMills.Construction.TorusFreezing YangMills.Construction.FamilyNorms YangMills.Construction.TorusComparison YangMills.Construction.ReferenceDensity
variable {F : BlockFrame}
private theorem coordsAboveFrame_true_indep (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    coordsAboveFrame true a ρ m V η = coordsAboveFrame true a ρ 0 V η := by
  funext x i
  simp [coordsAboveFrame, ColdStepAtMirrorFrames.stepFrame]
private theorem fieldAboveFrame_true_indep (a ρ : ℝ) (m : ℕ) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    fieldAboveFrame true a ρ m V η = fieldAboveFrame true a ρ 0 V η := by
  unfold fieldAboveFrame
  rw [coordsAboveFrame_true_indep]
private theorem centredExpansion_true_indep (a ρ : ℝ) (m : ℕ) (f : LocalFamily) (y : F.Site F.depth)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    centredExpansion true a ρ m f y η V = centredExpansion true a ρ 0 f y η V := by
  unfold centredExpansion
  rw [fieldAboveFrame_true_indep]
private theorem stepExponent_true_indep (a ρ x : ℝ) (m : ℕ) (f : LocalFamily) (ν : ℝ)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    stepExponent true a ρ x m f ν V η = stepExponent true a ρ x 0 f ν V η := by apply _root_.YangMills.SharedProofs.p27308 <;> assumption
private theorem cellExponent_true_indep (a ρ x : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    cellExponent true a ρ x m Y V η = cellExponent true a ρ x 0 Y V η := by
  unfold cellExponent
  simp only [coordsAboveFrame_true_indep a ρ m, fieldAboveFrame_true_indep a ρ m]
private theorem centredExpansion_smul (a ρ ν : ℝ) (m : ℕ) (f : LocalFamily) (y : F.Site F.depth)
    (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    centredExpansion true a ρ m (ν • f) y η V = ν * centredExpansion true a ρ 0 f y η V := by
  rw [centredExpansion_true_indep]
  unfold centredExpansion ColdStepAtMirrorFrames.subtractTrivial
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
private theorem stepExponent_smul_one (a ρ x ν : ℝ) (m : ℕ) (f : LocalFamily) (V : F.GaugeField F.top)
    (η : StepVariable (finiteCells F)) :
    stepExponent true a ρ x m (ν • f) 1 V η = stepExponent true a ρ x 0 f ν V η := by
  unfold stepExponent
  simp only [coordsAboveFrame_true_indep a ρ m, fieldAboveFrame_true_indep a ρ m, centredExpansion_smul,
    one_mul, Finset.mul_sum]
private theorem remainder_expectation_eq_cutoffMean (hE : interpolationAtEndpoints)
    (a ρA ρ lam x τ : ℝ) (p : ℝ → ℝ) (m : ℕ) (f : LocalFamily) (Y : F.Cell) (V : F.GaugeField F.top) :
    ballExpectation (cutoffFactor ρ p) (weightLawExponent 0 a ρA lam x m τ V)
        (cellExponentRemainder 0 a ρA lam x m Y V) =
      cutoffMean ρ p (fun η => τ * stepExponent true a ρA x 0 f 0 V η + (1 - τ) * totalQuadratic lam x η)
        (fun η => cellExponent true a ρA x 0 Y V η - cellQuadratic lam x Y η) := by
  obtain ⟨-, -, -, -, h5, -, h7⟩ := hE F true a ρA lam x τ m V
  simp only [segmentEnd, if_true] at h5 h7
  have e1 : weightLawExponent 0 a ρA lam x m τ V =
      fun η => τ * stepExponent true a ρA x 0 f 0 V η + (1 - τ) * totalQuadratic lam x η := by
    funext η
    rw [h7 f η, stepExponent_true_indep]
  have e2 : cellExponentRemainder 0 a ρA lam x m Y V =
      fun η => cellExponent true a ρA x 0 Y V η - cellQuadratic lam x Y η := by
    funext η
    unfold cellExponentRemainder
    rw [h5 Y η, cellExponent_true_indep]
  rw [e1, e2]
  rfl
private theorem expansion_expectation_eq_cutoffMean (hE : interpolationAtEndpoints) (a ρA ρ x ν : ℝ)
    (p : ℝ → ℝ) (m : ℕ) (f : LocalFamily) (Y : F.Cell) (V : F.GaugeField F.top) :
    ballExpectation (cutoffFactor ρ p) (familyLawExponent 0 a ρA x m (ν • f) V)
        (fun η => interpolatedBlockExpansion 0 a ρA m f Y η V) =
      cutoffMean ρ p (stepExponent true a ρA x 0 f ν V) (fun η => cellCentredExpansion true a ρA 0 f Y η V) := by
  obtain ⟨-, -, -, h4, -, h6, -⟩ := hE F true a ρA 0 x 0 m V
  simp only [segmentEnd, if_true] at h4 h6
  have e1 : familyLawExponent 0 a ρA x m (ν • f) V = stepExponent true a ρA x 0 f ν V := by
    funext η
    rw [h6 (ν • f) η, stepExponent_smul_one]
  have e2 : (fun η => interpolatedBlockExpansion 0 a ρA m f Y η V) =
      fun η => cellCentredExpansion true a ρA 0 f Y η V := by
    funext η
    unfold interpolatedBlockExpansion cellCentredExpansion
    apply Finset.sum_congr rfl
    intro y _
    rw [h4 f y η, centredExpansion_true_indep]
  rw [e1, e2]
  rfl
private theorem isNormBoundedLocalFamily_smul (L t n₀ : ℕ) (σ δ E E₃ ν : ℝ) (f : LocalFamily)
    (h0 : 0 ≤ ν) (h1 : ν ≤ 1) (hE : 0 ≤ E) (hE₃ : 0 ≤ E₃) (hδ : 0 ≤ δ)
    (hf : IsNormBoundedLocalFamily L t n₀ σ δ E E₃ f) : IsNormBoundedLocalFamily L t n₀ σ δ E E₃ (ν • f) := by
  have hw : ∀ x : ℝ, 0 < torusDecayFactor L δ x := by
    intro x
    unfold torusDecayFactor
    exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
  have hder : ∀ (F : BlockFrame) (G : F.GaugeField F.depth → ℝ) (W : F.GaugeField F.depth) (k : ℕ)
      (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 →
      ContDiffThreeAlongBonds G W →
      bondDeriv (fun W' => ν * G W') W c X = ν * bondDeriv G W c X := by
    intro F G W k c X hk hG
    unfold bondDeriv
    have hc : ContDiffAt ℝ k (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0 :=
      (hG k c X).of_le (by exact_mod_cast hk)
    have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := ν) hc
    have h2 : (fun τ : Fin k → ℝ => ν * G (leftTranslate (bondSpread c X τ) W)) =
        ν • fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W) := rfl
    rw [h2, this]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro F hF y W hW k c X
    exact (hf.smooth F hF y W hW k c X).const_smul ν
  · intro F hF y W γ hW
    simp only [Pi.smul_apply]
    rw [hf.gauge_invariant F hF y W γ hW]
  · intro F hF y h W hW
    simp only [Pi.smul_apply]
    rw [hf.translation_invariant F hF y h W hW]
  · intro F hF y W k c X hW h1k hk hX
    have hb := hf.decay F hF y W k c X hW h1k hk hX
    have he : bondDeriv ((ν • f) F y) W c X = ν * bondDeriv (f F y) W c X :=
      hder F (f F y) W k c X hk (hf.smooth F hF y W hW)
    rw [he, abs_mul, abs_of_nonneg h0]
    calc ν * |bondDeriv (f F y) W c X| ≤ 1 * |bondDeriv (f F y) W c X| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hb
  · intro F F' hF hF' y y' W W' r k h X hW hW' hag hk hb hX
    have hc : ∀ (F : BlockFrame) (y : F.Site F.depth) (W : F.GaugeField F.depth),
        IsCubicTorusAbove L t n₀ F → IsSmallCurvature σ W →
        ContDiffThreeAlongBonds (ColdStepAtMirrorFrames.subtractTrivial f F y) W := by
      intro F y W hF hW k c X
      exact (hf.smooth F hF y W hW k c X).sub contDiffAt_const
    have hcs : ∀ (F : BlockFrame) (y : F.Site F.depth), ColdStepAtMirrorFrames.subtractTrivial (ν • f) F y =
        fun W => ν * ColdStepAtMirrorFrames.subtractTrivial f F y W := by
      intro F y
      funext W
      unfold ColdStepAtMirrorFrames.subtractTrivial
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hb' := hf.locality F F' hF hF' y y' W W' r k h X hW hW' hag hk hb hX
    rw [hcs F y, hcs F' y', hder F _ W k _ X (by omega) (hc F y W hF hW),
      hder F' _ W' k _ X (by omega) (hc F' y' W' hF' hW'), ← mul_sub, abs_mul, abs_of_nonneg h0]
    calc _ ≤ 1 * |bondDeriv (ColdStepAtMirrorFrames.subtractTrivial f F y) W (bondsAt y h) X -
            bondDeriv (ColdStepAtMirrorFrames.subtractTrivial f F' y') W' (bondsAt y' h) X| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hb'
private theorem bondDeriv_zero_order (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top)
    (c : Fin 0 → F.Site F.top × Fin 4) (X : Fin 0 → imaginaryQuaternions) : bondDeriv G V c X = G V := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
private theorem densityExcess_eq_weight_integrals (T : StepParameters) (t : ℕ) (x l : ℝ)
    (hxl : l⁻¹ ^ 2 = x) (Y : F.Cell) (V : F.GaugeField F.top)
    (u₁ : interactionDensity true T.a T.ρA T.ballRadius T.lam (l⁻¹ ^ 2) 0 T.p (T.localReference t) Y V =
      -∫ θ in (0 : ℝ)..1, observableMean T.a T.ρA T.ballRadius T.lam T.p (T.localReference t)
        (.interpolated θ) (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) l V)
    (u₂ : expansionDensity true T.a T.ρA T.ballRadius (l⁻¹ ^ 2) 0 T.p (T.localReference t) Y V =
      ∫ θ in (0 : ℝ)..1, observableMean T.a T.ρA T.ballRadius T.lam T.p (T.localReference t) (.tilted θ)
        (fun l ζ V' => rescaledCellExpansion T.a T.ρA (T.localReference t) l Y V' ζ) l V)
    (z₁ : (-∫ τ in (0 : ℝ)..1, observableGaussianMean T.a T.ρA T.lam (T.localReference t)
        (.interpolated τ) (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) V) =
      stepDensity T.a T.ρA T.lam Y V)
    (z₂ : (∫ ν in (0 : ℝ)..1, observableGaussianMean T.a T.ρA T.lam (T.localReference t) (.tilted ν)
        (fun l ζ V' => rescaledCellExpansion T.a T.ρA (T.localReference t) l Y V' ζ) V) =
      cellCentredExpansion true T.a T.ρA 0 (T.localReference t) Y 0 V) :
    densityExcess T t x F Y V =
      (-(∫ θ in (0 : ℝ)..1, observableMean T.a T.ρA T.ballRadius T.lam T.p (T.localReference t)
          (.interpolated θ) (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) l V) +
        ∫ θ in (0 : ℝ)..1, observableGaussianMean T.a T.ρA T.lam (T.localReference t) (.interpolated θ)
          (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) V) +
      ((∫ θ in (0 : ℝ)..1, observableMean T.a T.ρA T.ballRadius T.lam T.p (T.localReference t)
          (.tilted θ) (fun l ζ V' => rescaledCellExpansion T.a T.ρA (T.localReference t) l Y V' ζ) l V) -
        ∫ θ in (0 : ℝ)..1, observableGaussianMean T.a T.ρA T.lam (T.localReference t) (.tilted θ)
          (fun l ζ V' => rescaledCellExpansion T.a T.ρA (T.localReference t) l Y V' ζ) V) := by
  unfold densityExcess
  rw [← hxl, u₁, u₂, ← z₁, ← z₂]
  ring
private theorem abs_sub_le_of_near_sq (g g' : ℝ → ℝ) (g₀ g₀' B D l₀ : ℝ) (hl₀ : 0 < l₀) (hD : 0 ≤ D)
    (h1 : ∀ l, 0 < l → l ≤ l₀ → |g l - g₀| ≤ D * l ^ 2)
    (h2 : ∀ l, 0 < l → l ≤ l₀ → |g' l - g₀'| ≤ D * l ^ 2)
    (h3 : ∀ l, 0 < l → l ≤ l₀ → |g l - g' l| ≤ B) : |g₀ - g₀'| ≤ B := by
  apply le_of_forall_pos_le_add
  intro ε hε
  set l : ℝ := min l₀ (Real.sqrt (ε / (2 * (D + 1)))) with hl
  have hq : 0 < ε / (2 * (D + 1)) := by positivity
  have hl0 : 0 < l := lt_min hl₀ (Real.sqrt_pos.mpr hq)
  have hl1 : l ≤ l₀ := min_le_left _ _
  have hl2 : l ^ 2 ≤ ε / (2 * (D + 1)) := by
    have h : l ≤ Real.sqrt (ε / (2 * (D + 1))) := min_le_right _ _
    calc l ^ 2 ≤ (Real.sqrt (ε / (2 * (D + 1)))) ^ 2 := pow_le_pow_left₀ hl0.le h 2
      _ = _ := Real.sq_sqrt hq.le
  have hDl : D * l ^ 2 ≤ ε / 2 := by
    have : (D + 1) * l ^ 2 ≤ ε / 2 := by
      calc (D + 1) * l ^ 2 ≤ (D + 1) * (ε / (2 * (D + 1))) := by
            apply mul_le_mul_of_nonneg_left hl2
            positivity
        _ = ε / 2 := by field_simp
    nlinarith [sq_nonneg l]
  have a1 := h1 l hl0 hl1
  have a2 := h2 l hl0 hl1
  have a3 := h3 l hl0 hl1
  have e : g₀ - g₀' = (g l - g' l) - (g l - g₀) + (g' l - g₀') := by ring
  rw [e]
  calc |(g l - g' l) - (g l - g₀) + (g' l - g₀')| ≤ |(g l - g' l) - (g l - g₀)| + |g' l - g₀'| :=
        abs_add_le _ _
    _ ≤ |g l - g' l| + |g l - g₀| + |g' l - g₀'| := by
        have := abs_sub (g l - g' l) (g l - g₀)
        linarith
    _ ≤ B + ε := by linarith
private theorem abs_intervalIntegral_sub_le (M M' : ℝ → ℝ) (B : ℝ) (hM : IntervalIntegrable M volume 0 1)
    (hM' : IntervalIntegrable M' volume 0 1) (h : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → |M θ - M' θ| ≤ B) :
    |(∫ θ in (0 : ℝ)..1, M θ) - ∫ θ in (0 : ℝ)..1, M' θ| ≤ B := by
  rw [← intervalIntegral.integral_sub hM hM']
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := B)
    (f := fun θ => M θ - M' θ) (fun θ hθ => by
      rw [Set.uIoc_of_le zero_le_one] at hθ
      exact h θ hθ.1.le hθ.2)
  simpa using this
set_option maxHeartbeats 4000000 in
theorem densityExcessLocal (hP : scaledMeanParity)
    (hS : rescaledPartsSmoothStatement) (hW : meansDifferentiableInWeightStatement)
    (hZ : DensitiesAtScaleZero) (hM : DensitiesAreRescaledMeans)
    (hR : localReferenceBoundedFamily) (hF₁ : remainderExpectationDecouples)
    (hF₂ : blockExpansionExpectationDecouples) (hEnd : interpolationAtEndpoints) :
    densityExcessLocalStatement := by
  have hF₁' : EventuallyOrdered RemainderExpectationDecouples := EventuallyInParameters.mono hF₁ fun _ g _ _ => g
  have hF₂' : EventuallyOrdered BlockExpansionExpectationDecouples := EventuallyInParameters.mono hF₂ fun _ g _ _ => g
  refine EventuallyOrdered.mono (((((((hP.and hS).and hW).and hZ).and hM).and hR).and hF₁').and hF₂') ?_
  rintro T hT hn ⟨⟨⟨⟨⟨⟨⟨cP, cS⟩, cW⟩, cZ⟩, cM⟩, cR⟩, cF₁⟩, cF₂⟩ hroom
  obtain ⟨e, he⟩ := cR hroom
  obtain ⟨l₁, C₁, hl₁, hC₁, gP⟩ := cP e
  obtain ⟨l₂, K, hl₂, hK, gS⟩ := cS e
  obtain ⟨l₃, hl₃, gW⟩ := cW e
  obtain ⟨l₄, hl₄, gM⟩ := cM
  have hE₁ : (1 : ℝ) ≤ T.E := hT.one_le_E
  have hκ := hT.κ_pos
  have hη₃ := hT.η₃_pos
  set l₀ : ℝ := min (min (min l₁ (l₂ / 2)) (min l₃ l₄)) ((Real.sqrt (max T.coupling 1))⁻¹) with hl₀def
  have hsy : 0 < Real.sqrt (max T.coupling 1) :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hl₀ : 0 < l₀ := lt_min (lt_min (lt_min hl₁ (half_pos hl₂)) (lt_min hl₃ hl₄)) (inv_pos.mpr hsy)
  have hle₅ : l₀ ≤ min (min l₁ (l₂ / 2)) (min l₃ l₄) := min_le_left _ _
  have hle₁ : l₀ ≤ l₁ := hle₅.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hle₂' : l₀ ≤ l₂ / 2 := hle₅.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hle₂ : l₀ ≤ l₂ := by linarith
  have hdbl : 2 * l₀ ≤ l₂ := by linarith
  have hdbl₀ : 0 < 2 * l₀ := by positivity
  have hle₃ : l₀ ≤ l₃ := hle₅.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hle₄ : l₀ ≤ l₄ := hle₅.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hy₁ : ∀ l : ℝ, 0 < l → l ≤ l₀ → T.coupling ≤ l⁻¹ ^ 2 := by
    intro l hl hll
    have h1 : l ≤ (Real.sqrt (max T.coupling 1))⁻¹ := hll.trans (min_le_right _ _)
    have h2 : Real.sqrt (max T.coupling 1) ≤ l⁻¹ := by
      rw [le_inv_comm₀ hsy hl]
      exact h1
    have h3 : max T.coupling 1 ≤ l⁻¹ ^ 2 := by
      rw [← Real.sq_sqrt (le_trans zero_le_one (le_max_right T.coupling 1))]
      exact pow_le_pow_left₀ hsy.le h2 2
    exact (le_max_left _ _).trans h3
  have hCs := T.Cs
  refine ⟨l₀⁻¹ ^ 2, 2 * (|T.Cs| + |T.CE * T.E|) + 1, by positivity, by positivity, ?_⟩
  intro t x hx F F' Y Y' V V' r hFt hFt' hV hV' hag
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  set l : ℝ := (Real.sqrt x)⁻¹ with hldef
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hl : 0 < l := inv_pos.mpr hsq
  have hxl : l⁻¹ ^ 2 = x := by
    rw [hldef, inv_inv, Real.sq_sqrt hx0.le]
  have hll : l ≤ l₀ := by
    rw [hldef]
    have h1 : l₀⁻¹ ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hx
    exact inv_le_of_inv_le₀ hl₀ h1
  set f : LocalFamily := T.localReference t with hf
  have hfam := he t
  have hfam₁ : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f := hfam.1
  set ee : ℝ := Real.exp (-(T.κ * r / 2 ^ 7)) with hee
  have hee0 : 0 < ee := Real.exp_pos _
  have hA : ∀ l' : ℝ, 0 < l' → l' ≤ l₀ → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      |observableMean T.a T.ρA T.ballRadius T.lam T.p f (.interpolated θ)
          (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) l' V -
        observableMean T.a T.ρA T.ballRadius T.lam T.p f (.interpolated θ)
          (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y' V' ζ) l' V'| ≤ T.Cs * ee := by
    intro l' hl' hll' θ h0 h1
    obtain ⟨m₁, -, -, -⟩ := gM t F V f l' Y hFt hV hl' (hll'.trans hle₄)
    obtain ⟨m₂, -, -, -⟩ := gM t F' V' f l' Y' hFt' hV' hl' (hll'.trans hle₄)
    rw [← m₁, ← m₂, ← remainder_expectation_eq_cutoffMean hEnd T.a T.ρA T.ballRadius T.lam (l'⁻¹ ^ 2) θ T.p
        (frameRadius (l'⁻¹ ^ 2)) f Y V,
      ← remainder_expectation_eq_cutoffMean hEnd T.a T.ρA T.ballRadius T.lam (l'⁻¹ ^ 2) θ T.p
        (frameRadius (l'⁻¹ ^ 2)) f Y' V']
    exact cF₁ t (l'⁻¹ ^ 2) 0 θ F F' V V' Y Y' r (hy₁ l' hl' hll') le_rfl zero_le_one h0 h1 hFt hFt' hV hV' hag
  have hB : ∀ l' : ℝ, 0 < l' → l' ≤ l₀ → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      |observableMean T.a T.ρA T.ballRadius T.lam T.p f (.tilted θ)
          (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) l' V -
        observableMean T.a T.ρA T.ballRadius T.lam T.p f (.tilted θ)
          (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y' V' ζ) l' V'| ≤ T.CE * T.E * ee := by
    intro l' hl' hll' θ h0 h1
    obtain ⟨-, m₁, -, -⟩ := gM t F V f l' Y hFt hV hl' (hll'.trans hle₄)
    obtain ⟨-, m₂, -, -⟩ := gM t F' V' f l' Y' hFt' hV' hl' (hll'.trans hle₄)
    rw [← m₁, ← m₂, ← expansion_expectation_eq_cutoffMean hEnd T.a T.ρA T.ballRadius (l'⁻¹ ^ 2) θ T.p
        (frameRadius (l'⁻¹ ^ 2)) f Y V,
      ← expansion_expectation_eq_cutoffMean hEnd T.a T.ρA T.ballRadius (l'⁻¹ ^ 2) θ T.p
        (frameRadius (l'⁻¹ ^ 2)) f Y' V']
    have hδ : 0 ≤ T.decayRate := by
      unfold StepParameters.decayRate
      positivity
    have hE₃ : 0 ≤ T.energyRatio := by
      unfold StepParameters.energyRatio
      positivity
    exact cF₂ t (l'⁻¹ ^ 2) 0 T.E (θ • f) f F F' V V' Y Y' r (hy₁ l' hl' hll') le_rfl zero_le_one
      (by linarith) (isNormBoundedLocalFamily_smul _ _ _ _ _ _ _ _ f h0 h1 (by linarith) hE₃ hδ hfam₁)
      hfam₁ hFt hFt' hV hV' hag
  have hX₀ : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun l => l.elim0
  have sm₁ : ∀ (F : BlockFrame) (Y : F.Cell), IsCubicTopTorus T.L t T.n₀ F →
      IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius l₀ K Y
        (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) :=
    fun F Y hF V' hV' => (gS l₀ hl₀ hle₂ t f F V' Y hfam hF hV').1
  have sm₂ : ∀ (F : BlockFrame) (Y : F.Cell), IsCubicTopTorus T.L t T.n₀ F →
      IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius l₀ K Y
        (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) :=
    fun F Y hF V' hV' => (gS l₀ hl₀ hle₂ t f F V' Y hfam hF hV').2
  have db₁ : ∀ (F : BlockFrame) (Y : F.Cell), IsCubicTopTorus T.L t T.n₀ F →
      IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (2 * l₀) K Y
        (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) :=
    fun F Y hF V' hV' => (gS (2 * l₀) hdbl₀ hdbl t f F V' Y hfam hF hV').1
  have db₂ : ∀ (F : BlockFrame) (Y : F.Cell), IsCubicTopTorus T.L t T.n₀ F →
      IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (2 * l₀) K Y
        (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) :=
    fun F Y hF V' hV' => (gS (2 * l₀) hdbl₀ hdbl t f F V' Y hfam hF hV').2
  have hD : 0 ≤ C₁ * K := by positivity
  have near₀ : ∀ (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top) (law : ScaledVariables.StepLaw)
      (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V → ScaledVariables.StepLaw.IsUnitWeight law →
      IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (2 * l₀) K Y Ob →
      ∀ l', 0 < l' → l' ≤ l₀ →
        |observableMean T.a T.ρA T.ballRadius T.lam T.p f law Ob l' V -
            observableGaussianMean T.a T.ρA T.lam f law Ob V| ≤
          C₁ * K * l' ^ 2 := by
    intro F Y V law Ob h1 h2 h3 h4 l' hl' hll'
    have := (gP l₀ hl₀ hle₁ t f F V Y law K Ob 0 Fin.elim0 Fin.elim0 hfam h1 h2 h3 hK h4 hX₀).sub_gaussianMean_le
      (by norm_num) l' hl' hll'
    rw [bondDeriv_zero_order, bondDeriv_zero_order] at this
    have h5 : Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ T.κ / 2 ^ 6 * (bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : ℝ) := by positivity
      linarith
    have h6 : 0 ≤ C₁ * K * l' ^ 2 := by positivity
    calc _ ≤ C₁ * K * l' ^ 2 *
          Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4))) := this
      _ ≤ C₁ * K * l' ^ 2 * 1 := mul_le_mul_of_nonneg_left h5 h6
      _ = _ := mul_one _
  have hZ₁ : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      |observableGaussianMean T.a T.ρA T.lam f (.interpolated θ)
          (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) V -
        observableGaussianMean T.a T.ρA T.lam f (.interpolated θ)
          (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y' V' ζ) V'| ≤
      T.Cs * ee := fun θ h0 h1 =>
    abs_sub_le_of_near_sq _ _ _ _ _ (C₁ * K) l₀ hl₀ hD
      (near₀ F Y V (.interpolated θ) _ hFt hV ⟨h0, h1⟩ (db₁ F Y hFt))
      (near₀ F' Y' V' (.interpolated θ) _ hFt' hV' ⟨h0, h1⟩ (db₁ F' Y' hFt'))
      (fun l' hl' hll' => hA l' hl' hll' θ h0 h1)
  have hZ₂ : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      |observableGaussianMean T.a T.ρA T.lam f (.tilted θ)
          (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) V -
        observableGaussianMean T.a T.ρA T.lam f (.tilted θ)
          (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y' V' ζ) V'| ≤
      T.CE * T.E * ee := fun θ h0 h1 =>
    abs_sub_le_of_near_sq _ _ _ _ _ (C₁ * K) l₀ hl₀ hD
      (near₀ F Y V (.tilted θ) _ hFt hV ⟨h0, h1⟩ (db₂ F Y hFt))
      (near₀ F' Y' V' (.tilted θ) _ hFt' hV' ⟨h0, h1⟩ (db₂ F' Y' hFt'))
      (fun l' hl' hll' => hB l' hl' hll' θ h0 h1)
  have int₀ : ∀ (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top) (kind : ℝ → ScaledVariables.StepLaw)
      (Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ), IsCubicTopTorus T.L t T.n₀ F →
      IsSmallCurvature (5 / 4 * T.σ) V →
      (kind = ScaledVariables.StepLaw.tilted ∨ kind = ScaledVariables.StepLaw.interpolated) →
      IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius l₀ K Y Ob →
      IntervalIntegrable (fun θ => observableMean T.a T.ρA T.ballRadius T.lam T.p f (kind θ) Ob l V)
        volume 0 1 ∧
      IntervalIntegrable (fun θ => observableGaussianMean T.a T.ρA T.lam f (kind θ) Ob V) volume 0 1 := by
    intro F Y V kind Ob h1 h2 h3 h4
    obtain ⟨w₁, w₂⟩ := (gW l₀ hl₀ hle₃ t f F V Y kind K Ob 0 Fin.elim0 Fin.elim0 hfam h1 h2 h3 hK h4 hX₀).1
      (by norm_num)
    have i₁ := (w₁ l hl hll).integrable
    have i₂ := w₂.integrable
    simp only [bondDeriv_zero_order] at i₁ i₂
    exact ⟨i₁, i₂⟩
  obtain ⟨i₁, i₂⟩ := int₀ F Y V ScaledVariables.StepLaw.interpolated _ hFt hV (Or.inr rfl) (sm₁ F Y hFt)
  obtain ⟨i₃, i₄⟩ := int₀ F Y V ScaledVariables.StepLaw.tilted _ hFt hV (Or.inl rfl) (sm₂ F Y hFt)
  obtain ⟨j₁, j₂⟩ := int₀ F' Y' V' ScaledVariables.StepLaw.interpolated _ hFt' hV' (Or.inr rfl) (sm₁ F' Y' hFt')
  obtain ⟨j₃, j₄⟩ := int₀ F' Y' V' ScaledVariables.StepLaw.tilted _ hFt' hV' (Or.inl rfl) (sm₂ F' Y' hFt')
  have d₁ := abs_intervalIntegral_sub_le _ _ _ i₁ j₁ (hA l hl hll)
  have d₂ := abs_intervalIntegral_sub_le _ _ _ i₂ j₂ hZ₁
  have d₃ := abs_intervalIntegral_sub_le _ _ _ i₃ j₃ (hB l hl hll)
  have d₄ := abs_intervalIntegral_sub_le _ _ _ i₄ j₄ hZ₂
  obtain ⟨z₁, z₂⟩ := cZ t f F V Y hFt hV
  obtain ⟨z₃, z₄⟩ := cZ t f F' V' Y' hFt' hV'
  obtain ⟨-, -, u₁, u₂⟩ := gM t F V f l Y hFt hV hl (hll.trans hle₄)
  obtain ⟨-, -, u₃, u₄⟩ := gM t F' V' f l Y' hFt' hV' hl (hll.trans hle₄)
  rw [densityExcess_eq_weight_integrals T t x l hxl Y V u₁ u₂ z₁ z₂,
    densityExcess_eq_weight_integrals T t x l hxl Y' V' u₃ u₄ z₃ z₄]
  generalize (∫ θ in (0 : ℝ)..1, observableMean T.a T.ρA T.ballRadius T.lam T.p (T.localReference t)
    (.interpolated θ) (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) l V) = A₁ at d₁ ⊢
  generalize (∫ θ in (0 : ℝ)..1, observableMean T.a T.ρA T.ballRadius T.lam T.p (T.localReference t)
    (.interpolated θ) (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y' V' ζ) l V') = A₂ at d₁ ⊢
  generalize (∫ θ in (0 : ℝ)..1, observableGaussianMean T.a T.ρA T.lam (T.localReference t)
    (.interpolated θ) (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) V) = B₁ at d₂ ⊢
  generalize (∫ θ in (0 : ℝ)..1, observableGaussianMean T.a T.ρA T.lam (T.localReference t)
    (.interpolated θ) (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y' V' ζ) V') = B₂ at d₂ ⊢
  generalize (∫ θ in (0 : ℝ)..1, observableMean T.a T.ρA T.ballRadius T.lam T.p (T.localReference t)
    (.tilted θ) (fun l ζ V' => rescaledCellExpansion T.a T.ρA (T.localReference t) l Y V' ζ) l V) = D₁ at d₃ ⊢
  generalize (∫ θ in (0 : ℝ)..1, observableMean T.a T.ρA T.ballRadius T.lam T.p (T.localReference t)
    (.tilted θ) (fun l ζ V' => rescaledCellExpansion T.a T.ρA (T.localReference t) l Y' V' ζ) l V') = D₂ at d₃ ⊢
  generalize (∫ θ in (0 : ℝ)..1, observableGaussianMean T.a T.ρA T.lam (T.localReference t)
    (.tilted θ) (fun l ζ V' => rescaledCellExpansion T.a T.ρA (T.localReference t) l Y V' ζ) V) = H₁ at d₄ ⊢
  generalize (∫ θ in (0 : ℝ)..1, observableGaussianMean T.a T.ρA T.lam (T.localReference t)
    (.tilted θ) (fun l ζ V' => rescaledCellExpansion T.a T.ρA (T.localReference t) l Y' V' ζ) V') = H₂ at d₄ ⊢
  have e1 := abs_le.mp d₁
  have e2 := abs_le.mp d₂
  have e3 := abs_le.mp d₃
  have e4 := abs_le.mp d₄
  have c₁ : T.Cs * ee ≤ |T.Cs| * ee := mul_le_mul_of_nonneg_right (le_abs_self _) hee0.le
  have c₂ : T.CE * T.E * ee ≤ |T.CE * T.E| * ee := mul_le_mul_of_nonneg_right (le_abs_self _) hee0.le
  rw [abs_le]
  constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]
end YangMills.Construction.StepDensities
end
