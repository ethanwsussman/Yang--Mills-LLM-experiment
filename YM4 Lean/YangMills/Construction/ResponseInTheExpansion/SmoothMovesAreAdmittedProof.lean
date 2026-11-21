import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ResponseInTheExpansion.BoundsOfTheSmoothMoves
import YangMills.Construction.ResponseInTheExpansion.SmoothMovesAreAdmitted
import YangMills.Construction.ResponseInTheExpansion.SmoothMovesOnTwoTori
import YangMills.Construction.SummableBoundsOfTheFlow.ParametersHaveACouplingAboveOne
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusComparison WeightedResponses SummableBounds
namespace ResponseInTheExpansion
section GradientBounds
variable {F : BlockFrame}
theorem vanishingMove_mono {ρ x κ g₀ g₁ G₀ G₁ : ℝ} {Y : F.Cell} {A : StepVariable (finiteCells F) → ℝ} (hx : 0 ≤ x)
    (hg₀ : g₀ ≤ G₀) (hg₁ : g₁ ≤ G₁) (hA : IsVanishingMoveWithGradient ρ x κ g₀ g₁ Y A) :
    IsVanishingMoveWithGradient ρ x κ G₀ G₁ Y A := by
  refine ⟨hA.smooth, hA.bounded, hA.map_zero, fun η hη b => (hA.gradient_le η hη b).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_right hg₁ (mul_nonneg hx (Real.sqrt_nonneg (localSqNorm κ Y η)))
  linarith
end GradientBounds
theorem smoothIncrementsComparable (hC : comparisonFromGradientBoundsStatement) (hB : smoothIncrementBounds)
    (hT : SmoothIncrementsOnTwoTori) (hJ : EventuallyInParametersCombines) (hOne : couplingAtLeastOneStatement) :
    smoothIncrementsComparableStatement := by
  obtain ⟨C₁, h₁, hc⟩ := hC
  obtain ⟨C₂, h₂, hb⟩ := hB
  obtain ⟨C₃, h₃, ht⟩ := hT
  refine ⟨fun U => 2 * C₁ U * (C₂ U + C₃ U), fun U => ?_, ?_⟩
  · have := h₁ U
    have := h₂ U
    have := h₃ U
    positivity
  refine hJ.2 _ _ (fun T _ h => ?_) (hOne _ (hJ.1 _ _ (hJ.1 _ _ hc hb) ht))
  obtain ⟨⟨⟨hcT, hbT⟩, htT, hwT⟩, hy⟩ := h
  set c₁ := C₁ (parametersBeforeSide T) with hc₁
  set c₂ := C₂ (parametersBeforeSide T) with hc₂
  set c₃ := C₃ (parametersBeforeSide T) with hc₃
  have p₁ : 0 ≤ c₁ := h₁ _
  have p₂ : 0 ≤ c₂ := h₂ _
  have p₃ : 0 ≤ c₃ := h₃ _
  set G := c₂ + c₃ with hG
  have pG : 0 ≤ G := by positivity
  have e₂ : c₂ ≤ G := by linarith
  have e₃ : c₃ ≤ G := by linarith
  have hx1 : ∀ {x : ℝ}, T.coupling ≤ x → 1 ≤ x := fun h => hy.trans h
  have troot : ∀ {x : ℝ}, 1 ≤ x → 0 < x ^ (-(1 / 2) : ℝ) ∧ x ^ (-(1 / 2) : ℝ) ≤ 1 := fun {x} h =>
    ⟨Real.rpow_pos_of_pos (by linarith) _, Real.rpow_le_one_of_one_le_of_nonpos h (by norm_num)⟩
  have hweight : ∀ {F : BlockFrame} {ι : Type} [Fintype ι] (Y : F.Cell) (j : ι → ↥(chordBonds (finiteCells F)))
      (ζ : BondField ι), 0 ≤ weightedBondNorm T.κ Y j ζ := fun Y j ζ =>
    Finset.sum_nonneg fun i _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  refine ⟨?_, ?_⟩
  · intro t x f F F' V V' Y Y' q ι _ _ j j' hs hs' hrow hag hnp
    have hx := hx1 hs.coupling_le
    obtain ⟨tp, tl⟩ := troot hx
    obtain ⟨a₁, a₂, a₃, -⟩ := hbT t x f F V Y hs hrow
    obtain ⟨b₁, b₂, b₃, -⟩ := hbT t x f F' V' Y' hs' hrow
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have two := fun hq ζ hζ => htT t x f F F' V V' Y Y' q ι j j' ζ hs hs' hrow hag hnp hq hζ
    refine ⟨⟨a₁.smooth, b₁.smooth, ?_⟩, ⟨a₂.smooth, b₂.smooth, ?_⟩, fun i back =>
      ⟨(a₃ i back).smooth, (b₃ i back).smooth, ?_⟩⟩
    · refine hcT t x f F F' V V' Y Y' q ι j j' G 0 _ _ _ hs hs' hag hnp pG le_rfl ?_
        (vanishingMove_mono hx0 e₂ le_rfl a₁) (vanishingMove_mono hx0 e₂ le_rfl b₁) fun hq ζ hζ => ?_
      · have : 0 ≤ c₁ * G * x ^ (-(1 / 2) : ℝ) := by positivity
        nlinarith
      · refine (two hq ζ hζ).1.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
        have := mul_le_mul_of_nonneg_right e₃ (hweight Y j ζ)
        simpa [weightedBondNorm] using this
    · refine hcT t x f F F' V V' Y Y' q ι j j' G G _ _ _ hs hs' hag hnp pG pG ?_
        (vanishingMove_mono hx0 e₂ e₂ a₂) (vanishingMove_mono hx0 e₂ e₂ b₂) fun hq ζ hζ => ?_
      · have hle : c₁ * G * x ^ (-(1 / 2) : ℝ) ≤ c₁ * G := by
          have : 0 ≤ c₁ * G := by positivity
          nlinarith
        nlinarith
      · refine (two hq ζ hζ).2.1.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
        have w1 := mul_le_mul_of_nonneg_right e₃ (hweight Y j ζ)
        have hs0 : 0 ≤ weightedBondNormSq T.κ Y j ζ :=
          Finset.sum_nonneg fun b _ => mul_nonneg (Real.exp_pos _).le (by positivity)
        have w2 := mul_le_mul_of_nonneg_right e₃ (add_nonneg (mul_nonneg hx0 hs0) zero_le_one)
        have e : weightedBondNorm T.κ Y j ζ = ∑ i, Real.exp (-(T.κ * bondDistToCell Y (j i))) * ‖ζ i‖ := rfl
        have e' : weightedBondNormSq T.κ Y j ζ =
            ∑ i, Real.exp (-(2 ^ 5 * T.κ * bondDistToCell Y (j i))) * ‖ζ i‖ ^ 2 := rfl
        rw [← e, ← e']
        linarith
    · refine hcT t x f F F' V V' Y Y' q ι j j' G 0 _ _ _ hs hs' hag hnp pG le_rfl ?_
        (vanishingMove_mono hx0 e₂ le_rfl (a₃ i back)) (vanishingMove_mono hx0 e₂ le_rfl (b₃ i back)) fun hq ζ hζ => ?_
      · have : 0 ≤ c₁ * G * x ^ (-(1 / 2) : ℝ) := by positivity
        nlinarith
      · refine ((two hq ζ hζ).2.2 i back).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
        have := mul_le_mul_of_nonneg_right e₃ (hweight Y j ζ)
        simpa [weightedBondNorm] using this
  · intro t x f F V V' Y q ι _ _ j j' w B hs hs' hrow hag hnp hB0 hw
    have hx := hx1 hs.coupling_le
    obtain ⟨tp, tl⟩ := troot hx
    obtain ⟨-, -, -, a₄⟩ := hbT t x f F V Y hs hrow
    obtain ⟨-, -, -, b₄⟩ := hbT t x f F V' Y hs' hrow
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hGB : c₂ * B ≤ G * B := mul_le_mul_of_nonneg_right e₂ hB0.le
    have pGB : 0 ≤ G * B := by positivity
    refine ⟨(a₄ w B hB0 hw).smooth, (b₄ w B hB0 hw).smooth, ?_⟩
    refine hcT t x f F F V V' Y Y q ι j j' (G * B) 0 _ _ _ hs hs' hag hnp pGB le_rfl ?_
      (vanishingMove_mono hx0 hGB le_rfl (a₄ w B hB0 hw)) (vanishingMove_mono hx0 hGB le_rfl (b₄ w B hB0 hw))
      fun hq ζ hζ => ?_
    · have : 0 ≤ c₁ * G * B * x ^ (-(1 / 2) : ℝ) := by positivity
      nlinarith
    · refine (hwT t x f F V V' Y q ι j j' ζ w B hs hs' hrow hag hnp hq hζ hB0 hw).trans
        (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e₃ hB0.le) (hweight Y j ζ)
      simpa [weightedBondNorm] using this
end ResponseInTheExpansion
end YangMills.Construction
end
