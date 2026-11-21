import YangMills.Construction.ColdStepAtMirrorFrames.ColdChainAboveLevelZeroProof
import YangMills.Construction.SummableBoundsOfTheFlow.ParityOfTheScaledMeans
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreMeansAtAScale
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAtTheScaleZero
import YangMills.Construction.SummableBoundsOfTheFlow.TheExcessOfTheDensitiesIsSmall
import YangMills.Construction.SummableBoundsOfTheFlow.TheMeansMoveWithTheirWeight
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsAFamilyBelow
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledPartsAreSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open MeasureTheory Set
namespace YangMills.Construction
open BlockAverages hiding bondSpread
open ColdStepAtMirrorFrames ScaledVariables ReferenceDensity
namespace StepDensities
variable {F : BlockFrame}
private theorem continuous_leftTranslate_bondSpread {j k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (U : F.GaugeField j) (y : F.Site j) (i : Fin 4) :
    Continuous fun τ : Fin k → ℝ => leftTranslate (bondSpread c X τ) U y i := by apply _root_.YangMills.SharedProofs.p21885 <;> assumption
private theorem leftTranslate_bondSpread_zero {j k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (U : F.GaugeField j) :
    leftTranslate (bondSpread c X 0) U = U := by apply _root_.YangMills.SharedProofs.p1939 <;> assumption
private theorem continuous_pathHolonomy_leftTranslate {j k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (U : F.GaugeField j) (γ : List PathStep) : ∀ x : F.Site j,
    Continuous fun τ : Fin k → ℝ => pathHolonomy (leftTranslate (bondSpread c X τ) U) x γ := by
  induction γ with
  | nil => intro x; exact continuous_const
  | cons st r ih =>
    intro x
    simp only [pathHolonomy]
    refine Continuous.mul ?_ (ih _)
    unfold linkValue
    split_ifs
    · exact continuous_leftTranslate_bondSpread c X U _ _
    · exact (continuous_leftTranslate_bondSpread c X U _ _).inv
private theorem eventually_isSmallCurvature_leftTranslate {k : ℕ} (hF : ∀ i, F.extent i ≠ 0) (s : ℝ)
    (V : F.GaugeField F.top) (hV : IsSmallCurvature s V) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), IsSmallCurvature s (leftTranslate (bondSpread c X τ) V) := by
  have hfin : Finite (F.Site F.top × Fin 4 × Fin 4) := by
    have h : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by simp [BlockFrame.period, hF i]⟩
    have : Finite (F.Site F.top) := Pi.finite
    exact Finite.instProd
  unfold IsSmallCurvature
  rw [Filter.eventually_all]
  intro p
  by_cases hp : p.2.1 < p.2.2
  · have hcont : Continuous fun τ : Fin k → ℝ =>
        plaquetteDefect (leftTranslate (bondSpread c X τ) V) p := by
      unfold plaquetteDefect plaquetteHolonomy
      exact ((continuous_subtype_val.comp
        (continuous_pathHolonomy_leftTranslate c X V _ _)).sub continuous_const).norm
    have h0 : plaquetteDefect (leftTranslate (bondSpread c X 0) V) p < s := by
      rw [leftTranslate_bondSpread_zero]
      exact hV p hp
    filter_upwards [hcont.continuousAt.eventually_lt continuousAt_const h0] with τ hτ _
    exact hτ
  · exact Filter.Eventually.of_forall fun τ h => absurd h hp
abbrev _root_.YangMills.SharedProofs.p8866 := @eventually_isSmallCurvature_leftTranslate
theorem densityExcessSmall_of_parts (hP : scaledMeanParity)
    (hS : rescaledPartsSmoothStatement) (hW : meansDifferentiableInWeightStatement)
    (hZ : DensitiesAtScaleZero) (hE : DensitiesAreRescaledMeans)
    (hR : localReferenceBoundedFamily) : densityExcessSmallStatement := by
  refine EventuallyOrdered.mono (((((hP.and hS).and hW).and hZ).and hE).and hR) ?_
  rintro T hT hn ⟨⟨⟨⟨⟨cP, cS⟩, cW⟩, cZ⟩, cE⟩, cR⟩ hroom
  obtain ⟨e, he⟩ := cR hroom
  obtain ⟨h₁, C₁, hh₁, hC₁, gP⟩ := cP e
  obtain ⟨h₂, K, hh₂, hK, gS⟩ := cS e
  obtain ⟨h₃, hh₃, gW⟩ := cW e
  obtain ⟨h₄, hh₄, gE⟩ := cE
  set h₀ : ℝ := min (min h₁ (h₂ / 2)) (min h₃ h₄) with hh₀def
  have hh₀ : 0 < h₀ := lt_min (lt_min hh₁ (half_pos hh₂)) (lt_min hh₃ hh₄)
  have hle₁ : h₀ ≤ h₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hle₂' : h₀ ≤ h₂ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hle₂ : h₀ ≤ h₂ := by linarith
  have hdbl : 2 * h₀ ≤ h₂ := by linarith
  have hdbl₀ : 0 < 2 * h₀ := by positivity
  have hle₃ : h₀ ≤ h₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hle₄ : h₀ ≤ h₄ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨h₀⁻¹ ^ 2, 2 * (C₁ * K) + 1, by positivity, by positivity, ?_⟩
  intro t x hx F Y V hF hV
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  set h : ℝ := (Real.sqrt x)⁻¹ with hhdef
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hh : 0 < h := inv_pos.mpr hsq
  have hxh : h⁻¹ ^ 2 = x := by
    rw [hhdef, inv_inv, Real.sq_sqrt hx0.le]
  have hh2 : h ^ 2 = x⁻¹ := by
    rw [hhdef, inv_pow, Real.sq_sqrt hx0.le]
  have hhh : h ≤ h₀ := by
    rw [hhdef]
    have h1 : h₀⁻¹ ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hx
    exact inv_le_of_inv_le₀ hh₀ h1
  have hside : ∀ i, F.extent i ≠ 0 := by
    obtain ⟨_, _, n, hn', hn₀⟩ := hF
    intro i
    rw [hn' i]
    omega
  set f : LocalFamily := T.localReference t with hf
  set O₁ : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
    fun h ζ V' => rescaledCellRemainder T.a T.ρA T.lam h Y V' ζ with hO₁
  set O₂ : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
    fun h ζ V' => rescaledCellExpansion T.a T.ρA f h Y V' ζ with hO₂
  have hs₁ : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius h₀ K Y O₁ :=
    fun V' hV' => (gS h₀ hh₀ hle₂ t f F V' Y (he t) hF hV').1
  have hs₂ : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius h₀ K Y O₂ :=
    fun V' hV' => (gS h₀ hh₀ hle₂ t f F V' Y (he t) hF hV').2
  have hd₁ : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (2 * h₀) K Y O₁ :=
    fun V' hV' => (gS (2 * h₀) hdbl₀ hdbl t f F V' Y (he t) hF hV').1
  have hd₂ : IsSmoothAtSmallCurvature (5 / 4 * T.σ) T.κ T.ballRadius (2 * h₀) K Y O₂ :=
    fun V' hV' => (gS (2 * h₀) hdbl₀ hdbl t f F V' Y (he t) hF hV').2
  have hX₀ : AreUnitVectors (Fin.elim0 : Fin 0 → imaginaryQuaternions) := fun m => m.elim0
  obtain ⟨v₁h, v₁z⟩ := (gW h₀ hh₀ hle₃ t f F V Y StepLaw.interpolated K O₁ 0 Fin.elim0 Fin.elim0
    (he t) hF hV (Or.inr rfl) hK hs₁ hX₀).1 (by norm_num)
  obtain ⟨v₂h, v₂z⟩ := (gW h₀ hh₀ hle₃ t f F V Y StepLaw.tilted K O₂ 0 Fin.elim0 Fin.elim0
    (he t) hF hV (Or.inl rfl) hK hs₂ hX₀).1 (by norm_num)
  have qGU := v₁h h hh hhh
  have qGS := v₂h h hh hhh
  set GU : F.GaugeField F.top → ℝ := fun V' => ∫ θ in (0 : ℝ)..1,
    observableMean T.a T.ρA T.ballRadius T.lam T.p f (.interpolated θ) O₁ h V' with hGU
  set GS : F.GaugeField F.top → ℝ := fun V' => ∫ θ in (0 : ℝ)..1,
    observableMean T.a T.ρA T.ballRadius T.lam T.p f (.tilted θ) O₂ h V' with hGS
  set HU : F.GaugeField F.top → ℝ := fun V' => ∫ θ in (0 : ℝ)..1,
    observableGaussianMean T.a T.ρA T.lam f (.interpolated θ) O₁ V' with hHU
  set HS : F.GaugeField F.top → ℝ := fun V' => ∫ θ in (0 : ℝ)..1,
    observableGaussianMean T.a T.ρA T.lam f (.tilted θ) O₂ V' with hHS
  have hform : ∀ V' : F.GaugeField F.top, IsSmallCurvature (5 / 4 * T.σ) V' →
      densityExcess T t x F Y V' = (-GU V' + HU V') + (GS V' - HS V') := by
    intro V' hV'
    obtain ⟨z₁, z₂⟩ := cZ t f F V' Y hF hV'
    obtain ⟨-, -, u₁, u₂⟩ := gE t F V' f h Y hF hV' hh (hhh.trans hle₄)
    unfold densityExcess
    rw [← hxh, u₁, u₂, ← z₁, ← z₂]
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
  refine ⟨?_, ?_⟩
  · intro k c X
    refine ContDiffAt.congr_of_eventuallyEq ?_ (hev k c X)
    have rU : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => GU (leftTranslate (bondSpread c X τ) V)) 0 :=
      qGU.contDiff k c X
    have rH : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => HU (leftTranslate (bondSpread c X τ) V)) 0 :=
      v₁z.contDiff k c X
    have rS : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => GS (leftTranslate (bondSpread c X τ) V)) 0 :=
      qGS.contDiff k c X
    have rZ : ContDiffAt ℝ 3 (fun τ : Fin k → ℝ => HS (leftTranslate (bondSpread c X τ) V)) 0 :=
      v₂z.contDiff k c X
    exact (rU.neg.add rH).add (rS.sub rZ)
  intro k c X hk hX
  have par₁ : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ParityExpansionBounds T C₁ K h₀ f (.interpolated θ) Y V O₁ c X :=
    fun θ h0 h1 => gP h₀ hh₀ hle₁ t f F V Y (.interpolated θ) K O₁ k c X (he t) hF hV ⟨h0, h1⟩ hK hd₁ hX
  have par₂ : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ParityExpansionBounds T C₁ K h₀ f (.tilted θ) Y V O₂ c X :=
    fun θ h0 h1 => gP h₀ hh₀ hle₁ t f F V Y (.tilted θ) K O₂ k c X (he t) hF hV ⟨h0, h1⟩ hK hd₂ hX
  obtain ⟨w₁h, w₁z⟩ := (gW h₀ hh₀ hle₃ t f F V Y StepLaw.interpolated K O₁ k c X (he t) hF hV
    (Or.inr rfl) hK hs₁ hX).1 hk
  obtain ⟨w₂h, w₂z⟩ := (gW h₀ hh₀ hle₃ t f F V Y StepLaw.tilted K O₂ k c X (he t) hF hV
    (Or.inl rfl) hK hs₂ hX).1 hk
  have pGU := w₁h h hh hhh
  have pGS := w₂h h hh hhh
  have hval : bondDeriv (densityExcess T t x F Y) V c X =
      (-bondDeriv GU V c X + bondDeriv HU V c X) + (bondDeriv GS V c X - bondDeriv HS V c X) := by
    have hk' : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
    have rU : ContDiffAt ℝ k (fun τ : Fin k → ℝ => GU (leftTranslate (bondSpread c X τ) V)) 0 :=
      (pGU.contDiff k c X).of_le hk'
    have rH : ContDiffAt ℝ k (fun τ : Fin k → ℝ => HU (leftTranslate (bondSpread c X τ) V)) 0 :=
      (w₁z.contDiff k c X).of_le hk'
    have rS : ContDiffAt ℝ k (fun τ : Fin k → ℝ => GS (leftTranslate (bondSpread c X τ) V)) 0 :=
      (pGS.contDiff k c X).of_le hk'
    have rZ : ContDiffAt ℝ k (fun τ : Fin k → ℝ => HS (leftTranslate (bondSpread c X τ) V)) 0 :=
      (w₂z.contDiff k c X).of_le hk'
    have a3 : ContDiffAt ℝ k (-(fun τ : Fin k → ℝ => GU (leftTranslate (bondSpread c X τ) V))) 0 :=
      rU.neg
    have a1 : ContDiffAt ℝ k ((-(fun τ : Fin k → ℝ => GU (leftTranslate (bondSpread c X τ) V))) +
        fun τ : Fin k → ℝ => HU (leftTranslate (bondSpread c X τ) V)) 0 := a3.add rH
    have a2 : ContDiffAt ℝ k ((fun τ : Fin k → ℝ => GS (leftTranslate (bondSpread c X τ) V)) -
        fun τ : Fin k → ℝ => HS (leftTranslate (bondSpread c X τ) V)) 0 := rS.sub rZ
    unfold bondDeriv
    rw [((hev k c X).iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_add_apply a1 a2,
      iteratedFDeriv_add_apply a3 rH, iteratedFDeriv_neg_apply, iteratedFDeriv_sub_apply rS rZ]
    rfl
  have hb : ∀ θ ∈ Set.uIoc (0 : ℝ) 1,
      ‖bondDeriv (observableGaussianMean T.a T.ρA T.lam f (.interpolated θ) O₁) V c X -
        bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f (.interpolated θ) O₁ h) V c X‖ ≤
      C₁ * K * h ^ 2 * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c)) := by
    intro θ hθ
    rw [Set.uIoc_of_le zero_le_one] at hθ
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact (par₁ θ hθ.1.le hθ.2).sub_gaussianMean_le hk h hh hhh
  have hb₂ : ∀ θ ∈ Set.uIoc (0 : ℝ) 1,
      ‖bondDeriv (observableMean T.a T.ρA T.ballRadius T.lam T.p f (.tilted θ) O₂ h) V c X -
        bondDeriv (observableGaussianMean T.a T.ρA T.lam f (.tilted θ) O₂) V c X‖ ≤
      C₁ * K * h ^ 2 * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c)) := by
    intro θ hθ
    rw [Set.uIoc_of_le zero_le_one] at hθ
    exact (par₂ θ hθ.1.le hθ.2).sub_gaussianMean_le hk h hh hhh
  have i₁ := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have i₂ := intervalIntegral.norm_integral_le_of_norm_le_const hb₂
  rw [intervalIntegral.integral_sub w₁z.integrable pGU.integrable, ← w₁z.deriv_integral_eq,
    ← pGU.deriv_integral_eq] at i₁
  rw [intervalIntegral.integral_sub pGS.integrable w₂z.integrable, ← pGS.deriv_integral_eq,
    ← w₂z.deriv_integral_eq] at i₂
  simp only [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at i₁ i₂
  rw [hval]
  set ee : ℝ := Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c)) with hee
  have hee0 : 0 < ee := Real.exp_pos _
  have hxi : 0 < x⁻¹ := inv_pos.mpr hx0
  rw [hh2] at i₁ i₂
  calc |(-bondDeriv GU V c X + bondDeriv HU V c X) + (bondDeriv GS V c X - bondDeriv HS V c X)|
      ≤ |bondDeriv HU V c X - bondDeriv GU V c X| + |bondDeriv GS V c X - bondDeriv HS V c X| := by
        have : (-bondDeriv GU V c X + bondDeriv HU V c X) = bondDeriv HU V c X - bondDeriv GU V c X := by
          ring
        rw [this]
        exact abs_add_le _ _
    _ ≤ C₁ * K * x⁻¹ * ee + C₁ * K * x⁻¹ * ee := add_le_add i₁ i₂
    _ ≤ (2 * (C₁ * K) + 1) * x⁻¹ * ee := by
        have : 0 < x⁻¹ * ee := by positivity
        nlinarith
end StepDensities
end YangMills.Construction
end
