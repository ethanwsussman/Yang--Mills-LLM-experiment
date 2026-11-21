import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessHasItsSecondOrder
import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessOfTheDensitiesIsSmallProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages hiding bondSpread
open YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ScaledVariables YangMills.Construction.StepDensities YangMills.Construction.ReferenceDensity YangMills.Construction.TorusFields MeasureTheory Set
namespace YangMills.Construction.StepDensities
variable {F : BlockFrame}
private theorem eventually_isSmallCurvature_leftTranslate {k : ℕ} (hF : ∀ i, F.extent i ≠ 0) (s : ℝ)
    (V : F.GaugeField F.top) (hV : IsSmallCurvature s V) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by apply _root_.YangMills.SharedProofs.p8866 <;> assumption
theorem densityExcessSecondOrder (hP : scaledMeanParity)
    (hS : rescaledPartsSmoothStatement) (hW : meansDifferentiableInWeightStatement)
    (hZ : DensitiesAtScaleZero) (hE : DensitiesAreRescaledMeans)
    (hR : localReferenceBoundedFamily) : densityExcessSecondOrderStatement := by
  refine EventuallyOrdered.mono (((((hP.and hS).and hW).and hZ).and hE).and hR) ?_
  rintro T hT hn ⟨⟨⟨⟨⟨cP, cS⟩, cW⟩, cZ⟩, cE⟩, cR⟩ hroom
  obtain ⟨e, he⟩ := cR hroom
  obtain ⟨l₁, C₁, hl₁, hC₁, gP⟩ := cP e
  obtain ⟨l₂, K, hl₂, hK, gS⟩ := cS e
  obtain ⟨l₃, hl₃, gW⟩ := cW e
  obtain ⟨l₄, hl₄, gE⟩ := cE
  set l₀ : ℝ := min (min l₁ (l₂ / 2)) (min l₃ l₄) with hl₀def
  have hl₀ : 0 < l₀ := lt_min (lt_min hl₁ (half_pos hl₂)) (lt_min hl₃ hl₄)
  have hle₁ : l₀ ≤ l₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hle₂' : l₀ ≤ l₂ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hle₂ : l₀ ≤ l₂ := by linarith
  have hdbl : 2 * l₀ ≤ l₂ := by linarith
  have hdbl₀ : 0 < 2 * l₀ := by positivity
  have hle₃ : l₀ ≤ l₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hle₄ : l₀ ≤ l₄ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨l₀⁻¹ ^ 2, 2 * (C₁ * K) + 1, by positivity, by positivity, ?_⟩
  intro t x hx F Y V hF hV
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  set l : ℝ := (Real.sqrt x)⁻¹ with hldef
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hl : 0 < l := inv_pos.mpr hsq
  have hxl : l⁻¹ ^ 2 = x := by
    rw [hldef, inv_inv, Real.sq_sqrt hx0.le]
  have hl2 : l ^ 2 = x⁻¹ := by
    rw [hldef, inv_pow, Real.sq_sqrt hx0.le]
  have hll : l ≤ l₀ := by
    rw [hldef]
    have h1 : l₀⁻¹ ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hx
    exact inv_le_of_inv_le₀ hl₀ h1
  have hside : ∀ i, F.extent i ≠ 0 := by
    obtain ⟨_, _, n, hn', hn₀⟩ := hF
    intro i
    rw [hn' i]
    omega
  set f : LocalFamily := T.localReference t with hf
  set O₁ : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
    fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ with hO₁
  set O₂ : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
    fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ with hO₂
  have hs₁ : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius l₀ K Y O₁ :=
    fun V' hV' => (gS l₀ hl₀ hle₂ t f F V' Y (he t) hF hV').1
  have hs₂ : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius l₀ K Y O₂ :=
    fun V' hV' => (gS l₀ hl₀ hle₂ t f F V' Y (he t) hF hV').2
  have hd₁ : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (2 * l₀) K Y O₁ :=
    fun V' hV' => (gS (2 * l₀) hdbl₀ hdbl t f F V' Y (he t) hF hV').1
  have hd₂ : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (2 * l₀) K Y O₂ :=
    fun V' hV' => (gS (2 * l₀) hdbl₀ hdbl t f F V' Y (he t) hF hV').2
  have hX₀ : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun l => l.elim0
  obtain ⟨v₁l, v₁z⟩ := (gW l₀ hl₀ hle₃ t f F V Y StepLaw.interpolated K O₁ 0 Fin.elim0 Fin.elim0
    (he t) hF hV (Or.inr rfl) hK hs₁ hX₀).1 (by norm_num)
  obtain ⟨v₂l, v₂z⟩ := (gW l₀ hl₀ hle₃ t f F V Y StepLaw.tilted K O₂ 0 Fin.elim0 Fin.elim0
    (he t) hF hV (Or.inl rfl) hK hs₂ hX₀).1 (by norm_num)
  have qGU := v₁l l hl hll
  have qGS := v₂l l hl hll
  set GU : F.GaugeField F.top → ℝ := fun V' => ∫ θ in (0 : ℝ)..1,
    observableMean T.a T.ρA T.ballRadius T.lam T.p f (.interpolated θ) O₁ l V' with hGU
  set GS : F.GaugeField F.top → ℝ := fun V' => ∫ θ in (0 : ℝ)..1,
    observableMean T.a T.ρA T.ballRadius T.lam T.p f (.tilted θ) O₂ l V' with hGS
  set HU : F.GaugeField F.top → ℝ := fun V' => ∫ θ in (0 : ℝ)..1,
    observableGaussianMean T.a T.ρA T.lam f (.interpolated θ) O₁ V' with hHU
  set HS : F.GaugeField F.top → ℝ := fun V' => ∫ θ in (0 : ℝ)..1,
    observableGaussianMean T.a T.ρA T.lam f (.tilted θ) O₂ V' with hHS
  have hform : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      densityExcess T t x F Y V' = (-GU V' + HU V') + (GS V' - HS V') := by
    intro V' hV'
    obtain ⟨z₁, z₂⟩ := cZ t f F V' Y hF hV'
    obtain ⟨-, -, u₁, u₂⟩ := gE t F V' f l Y hF hV' hl (hll.trans hle₄)
    unfold densityExcess
    rw [← hxl, u₁, u₂, ← z₁, ← z₂]
    ring
  have hev : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      (fun τ : Fin k → ℝ => densityExcess T t x F Y (leftTranslate (bondSpread c X τ) V)) =ᶠ[𝓝 0]
      ((-(fun τ => GU (leftTranslate (bondSpread c X τ) V)) +
          fun τ => HU (leftTranslate (bondSpread c X τ) V)) +
        ((fun τ => GS (leftTranslate (bondSpread c X τ) V)) -
          fun τ => HS (leftTranslate (bondSpread c X τ) V))) := by
    intro k c X
    filter_upwards [eventually_isSmallCurvature_leftTranslate hside _ V hV c X] with τ hτ
    simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
    exact hform _ hτ
  set SU : F.GaugeField F.top → ℝ := fun V' => ∫ θ in (0 : ℝ)..1,
    observableSecondOrderCoeff T.a T.ρA T.lam f (.interpolated θ) O₁ V' with hSU
  set SS : F.GaugeField F.top → ℝ := fun V' => ∫ θ in (0 : ℝ)..1,
    observableSecondOrderCoeff T.a T.ρA T.lam f (.tilted θ) O₂ V' with hSS
  have hsec : secondOrderDensityCoeff T.a T.ρA T.lam f F Y = fun V' => -SU V' + SS V' := rfl
  obtain ⟨v₃⟩ : Nonempty (DerivUnderWeightIntegral
      (fun θ => observableSecondOrderCoeff T.a T.ρA T.lam f (.interpolated θ) O₁) V
      (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) :=
    ⟨(gW l₀ hl₀ hle₃ t f F V Y StepLaw.interpolated K O₁ 0 Fin.elim0 Fin.elim0 (he t) hF hV
      (Or.inr rfl) hK hs₁ hX₀).2 (by norm_num)⟩
  obtain ⟨v₄⟩ : Nonempty (DerivUnderWeightIntegral
      (fun θ => observableSecondOrderCoeff T.a T.ρA T.lam f (.tilted θ) O₂) V
      (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) :=
    ⟨(gW l₀ hl₀ hle₃ t f F V Y StepLaw.tilted K O₂ 0 Fin.elim0 Fin.elim0 (he t) hF hV
      (Or.inl rfl) hK hs₂ hX₀).2 (by norm_num)⟩
  refine ⟨?_, ?_⟩
  · rw [hsec]
    intro k c X
    have rA : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => SU (leftTranslate (bondSpread c X τ) V)) 0 :=
      v₃.contDiff k c X
    have rB : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => SS (leftTranslate (bondSpread c X τ) V)) 0 :=
      v₄.contDiff k c X
    exact rA.neg.add rB
  intro k c X hk hX
  have hk3 : k ≤ 3 := by omega
  have par₁ : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ParityExpansionBounds T C₁ K l₀ f (.interpolated θ) Y V O₁ c X :=
    fun θ h0 h1 => gP l₀ hl₀ hle₁ t f F V Y (.interpolated θ) K O₁ k c X (he t) hF hV ⟨h0, h1⟩ hK hd₁ hX
  have par₂ : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ParityExpansionBounds T C₁ K l₀ f (.tilted θ) Y V O₂ c X :=
    fun θ h0 h1 => gP l₀ hl₀ hle₁ t f F V Y (.tilted θ) K O₂ k c X (he t) hF hV ⟨h0, h1⟩ hK hd₂ hX
  have W₁ := gW l₀ hl₀ hle₃ t f F V Y StepLaw.interpolated K O₁ k c X (he t) hF hV (Or.inr rfl) hK hs₁ hX
  have W₂ := gW l₀ hl₀ hle₃ t f F V Y StepLaw.tilted K O₂ k c X (he t) hF hV (Or.inl rfl) hK hs₂ hX
  obtain ⟨w₁l, w₁z⟩ := W₁.1 hk3
  obtain ⟨w₂l, w₂z⟩ := W₂.1 hk3
  have w₃ := W₁.2 hk
  have w₄ := W₂.2 hk
  have pGU := w₁l l hl hll
  have pGS := w₂l l hl hll
  have hk' : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk3
  have rU : ContDiffAt ℝ k (fun τ : Fin k → ℝ => GU (leftTranslate (bondSpread c X τ) V)) 0 :=
    (pGU.contDiff k c X).of_le hk'
  have rH : ContDiffAt ℝ k (fun τ : Fin k → ℝ => HU (leftTranslate (bondSpread c X τ) V)) 0 :=
    (w₁z.contDiff k c X).of_le hk'
  have rS : ContDiffAt ℝ k (fun τ : Fin k → ℝ => GS (leftTranslate (bondSpread c X τ) V)) 0 :=
    (pGS.contDiff k c X).of_le hk'
  have rZ : ContDiffAt ℝ k (fun τ : Fin k → ℝ => HS (leftTranslate (bondSpread c X τ) V)) 0 :=
    (w₂z.contDiff k c X).of_le hk'
  have rA : ContDiffAt ℝ k (fun τ : Fin k → ℝ => SU (leftTranslate (bondSpread c X τ) V)) 0 :=
    (w₃.contDiff k c X).of_le hk'
  have rB : ContDiffAt ℝ k (fun τ : Fin k → ℝ => SS (leftTranslate (bondSpread c X τ) V)) 0 :=
    (w₄.contDiff k c X).of_le hk'
  have a3 : ContDiffAt ℝ k (-(fun τ : Fin k → ℝ => GU (leftTranslate (bondSpread c X τ) V))) 0 := rU.neg
  have a1 : ContDiffAt ℝ k ((-(fun τ : Fin k → ℝ => GU (leftTranslate (bondSpread c X τ) V))) +
      fun τ : Fin k → ℝ => HU (leftTranslate (bondSpread c X τ) V)) 0 := a3.add rH
  have a2 : ContDiffAt ℝ k ((fun τ : Fin k → ℝ => GS (leftTranslate (bondSpread c X τ) V)) -
      fun τ : Fin k → ℝ => HS (leftTranslate (bondSpread c X τ) V)) 0 := rS.sub rZ
  have a4 : ContDiffAt ℝ k (-(fun τ : Fin k → ℝ => SU (leftTranslate (bondSpread c X τ) V))) 0 := rA.neg
  have hval : bondDeriv (densityExcess T t x F Y) V c X =
      (-bondDeriv GU V c X + bondDeriv HU V c X) + (bondDeriv GS V c X - bondDeriv HS V c X) := by
    unfold bondDeriv
    rw [((hev k c X).iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_add_apply a1 a2,
      iteratedFDeriv_add_apply a3 rH, iteratedFDeriv_neg_apply, iteratedFDeriv_sub_apply rS rZ]
    rfl
  have hval₂ : bondDeriv (secondOrderDensityCoeff T.a T.ρA T.lam f F Y) V c X =
      -bondDeriv SU V c X + bondDeriv SS V c X := by
    rw [hsec]
    unfold bondDeriv
    have h2 : (fun τ : Fin k → ℝ => -SU (leftTranslate (bondSpread c X τ) V) +
          SS (leftTranslate (bondSpread c X τ) V)) =
        (-(fun τ : Fin k → ℝ => SU (leftTranslate (bondSpread c X τ) V))) +
          fun τ : Fin k → ℝ => SS (leftTranslate (bondSpread c X τ) V) := rfl
    rw [h2, iteratedFDeriv_add_apply a4 rB, iteratedFDeriv_neg_apply]
    rfl
  set ee : ℝ := Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c)) with hee
  have hee0 : 0 < ee := Real.exp_pos _
  have hb₁ : ∀ θ ∈ Set.uIoc (0 : ℝ) 1,
      ‖(bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f (.interpolated θ) O₁ l) V c X -
          bondDeriv (observableGaussianMean T.a T.ρA T.lam f (.interpolated θ) O₁) V c X) -
        l ^ 2 * bondDeriv (observableSecondOrderCoeff T.a T.ρA T.lam f (.interpolated θ) O₁) V c X‖ ≤
        C₁ * K * l ^ 3 * ee := by
    intro θ hθ
    rw [Set.uIoc_of_le zero_le_one] at hθ
    have := (par₁ θ hθ.1.le hθ.2).secondOrderExpansion_le hk l hl hll
    rw [Real.norm_eq_abs, mul_comm (l ^ 2)]
    exact this
  have hb₂ : ∀ θ ∈ Set.uIoc (0 : ℝ) 1,
      ‖(bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f (.tilted θ) O₂ l) V c X -
          bondDeriv (observableGaussianMean T.a T.ρA T.lam f (.tilted θ) O₂) V c X) -
        l ^ 2 * bondDeriv (observableSecondOrderCoeff T.a T.ρA T.lam f (.tilted θ) O₂) V c X‖ ≤
        C₁ * K * l ^ 3 * ee := by
    intro θ hθ
    rw [Set.uIoc_of_le zero_le_one] at hθ
    have := (par₂ θ hθ.1.le hθ.2).secondOrderExpansion_le hk l hl hll
    rw [Real.norm_eq_abs, mul_comm (l ^ 2)]
    exact this
  have hc₁ : ∀ θ ∈ Set.uIoc (0 : ℝ) 1,
      ‖bondDeriv (observableSecondOrderCoeff T.a T.ρA T.lam f (.interpolated θ) O₁) V c X‖ ≤
        C₁ * K * ee := by
    intro θ hθ
    rw [Set.uIoc_of_le zero_le_one] at hθ
    exact (par₁ θ hθ.1.le hθ.2).secondOrderCoeff_le hk
  have hc₂ : ∀ θ ∈ Set.uIoc (0 : ℝ) 1,
      ‖bondDeriv (observableSecondOrderCoeff T.a T.ρA T.lam f (.tilted θ) O₂) V c X‖ ≤
        C₁ * K * ee := by
    intro θ hθ
    rw [Set.uIoc_of_le zero_le_one] at hθ
    exact (par₂ θ hθ.1.le hθ.2).secondOrderCoeff_le hk
  have i₁ := intervalIntegral.norm_integral_le_of_norm_le_const hb₁
  have i₂ := intervalIntegral.norm_integral_le_of_norm_le_const hb₂
  have i₃ := intervalIntegral.norm_integral_le_of_norm_le_const hc₁
  have i₄ := intervalIntegral.norm_integral_le_of_norm_le_const hc₂
  rw [intervalIntegral.integral_sub (pGU.integrable.sub w₁z.integrable) (w₃.integrable.const_mul _),
    intervalIntegral.integral_sub pGU.integrable w₁z.integrable, intervalIntegral.integral_const_mul,
    ← pGU.deriv_integral_eq, ← w₁z.deriv_integral_eq, ← w₃.deriv_integral_eq] at i₁
  rw [intervalIntegral.integral_sub (pGS.integrable.sub w₂z.integrable) (w₄.integrable.const_mul _),
    intervalIntegral.integral_sub pGS.integrable w₂z.integrable, intervalIntegral.integral_const_mul,
    ← pGS.deriv_integral_eq, ← w₂z.deriv_integral_eq, ← w₄.deriv_integral_eq] at i₂
  rw [← w₃.deriv_integral_eq] at i₃
  rw [← w₄.deriv_integral_eq] at i₄
  simp only [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at i₁ i₂ i₃ i₄
  have hl3 : l ^ 3 = x ^ (-(3 / 2 : ℝ)) := by
    have h1 : x ^ (-(3 / 2 : ℝ)) = (x ^ ((1 : ℝ) / 2)) ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_mul hx0.le]
      norm_num
    rw [h1, ← Real.sqrt_eq_rpow, Real.rpow_neg hsq.le, hldef, inv_pow]
    norm_num
  rw [hl3] at i₁ i₂
  rw [hl2] at i₁ i₂
  rw [hval₂, hval]
  constructor
  · calc |-bondDeriv SU V c X + bondDeriv SS V c X| ≤ |bondDeriv SU V c X| + |bondDeriv SS V c X| := by
          have := abs_add_le (-bondDeriv SU V c X) (bondDeriv SS V c X)
          rwa [abs_neg] at this
      _ ≤ C₁ * K * ee + C₁ * K * ee := add_le_add i₃ i₄
      _ ≤ (2 * (C₁ * K) + 1) * ee := by nlinarith
  · generalize bondDeriv GU V c X = A at i₁ ⊢
    generalize bondDeriv HU V c X = B at i₁ ⊢
    generalize bondDeriv SU V c X = D at i₁ i₃ ⊢
    generalize bondDeriv GS V c X = G at i₂ ⊢
    generalize bondDeriv HS V c X = H at i₂ ⊢
    generalize bondDeriv SS V c X = S at i₂ i₄ ⊢
    have e : (-A + B + (G - H)) - x⁻¹ * (-D + S) = -(A - B - x⁻¹ * D) + (G - H - x⁻¹ * S) := by ring
    rw [e]
    set P : ℝ := x ^ (-(3 / 2 : ℝ)) with hP'
    have hP0 : 0 < P := Real.rpow_pos_of_pos hx0 _
    calc |-(A - B - x⁻¹ * D) + (G - H - x⁻¹ * S)| ≤ |A - B - x⁻¹ * D| + |G - H - x⁻¹ * S| := by
          have := abs_add_le (-(A - B - x⁻¹ * D)) (G - H - x⁻¹ * S)
          rwa [abs_neg] at this
      _ ≤ C₁ * K * P * ee + C₁ * K * P * ee := add_le_add i₁ i₂
      _ ≤ (2 * (C₁ * K) + 1) * P * ee := by
          have : 0 < P * ee := by positivity
          nlinarith
end YangMills.Construction.StepDensities
end
