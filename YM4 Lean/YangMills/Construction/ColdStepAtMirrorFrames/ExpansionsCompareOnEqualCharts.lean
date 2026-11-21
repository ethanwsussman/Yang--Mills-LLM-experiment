import YangMills.Construction.ColdStepAtMirrorFrames.PullbackThroughTheChartForm
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages YangMills.Construction.FamilyNorms
def ExpansionDifferenceBoundOnAgreeingCharts : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily), Odd L → 0 ≤ E →
    IsNormBoundedLocalFamily L t n₀ σ δ E E₃ f →
    ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
      (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
      (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r s s₂ : ℕ) (h o : Fin 4 → ℤ),
      IsCubicTorusAbove L t n₀ F → IsCubicTorusAbove L t n₀ F' → (∀ i, 2 * r + 2 < F.extent i) →
      (∀ i, 2 * r + 2 < F'.extent i) →
      IsSmallCurvature σ (chartedField w V) → IsSmallCurvature σ (chartedField w' V') →
      (∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ 1) →
      (∀ b ∈ chordBonds (finiteCells F'), ‖w' b.1 b.2‖ ≤ 1) →
      AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
      (∀ (h₁ o₁ : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h₁ → o₁ ∈ centredCube L →
        fineBondAt Y h₁ o₁ i ∈ chordBonds (finiteCells F) →
        w (fineBondAt Y h₁ o₁ i).1 i = w' (fineBondAt Y' h₁ o₁ i).1 i) →
      WithinRadius s h → s + 2 ≤ r → o ∈ centredCube L →
      |subtractTrivial f F' (fineBondAt Y' h o 0).1 (chartedField w' V') -
          subtractTrivial f F (fineBondAt Y h o 0).1 (chartedField w V)| ≤
        E / torusDecayFactor L δ ((L : ℝ) * ((r : ℝ) - s - 2)) ∧
      ∀ (h₂ o₂ : Fin 4 → ℤ) (i : Fin 4) (k : ↥(chordBonds (finiteCells F)))
        (k' : ↥(chordBonds (finiteCells F'))) (e : BondVector),
        WithinRadius s₂ h₂ → o₂ ∈ centredCube L → s₂ + 2 * s + 4 ≤ r →
        k.1 = fineBondAt Y h₂ o₂ i → k'.1 = fineBondAt Y' h₂ o₂ i →
        |fderiv ℝ (readInChart (subtractTrivial f F' (fineBondAt Y' h o 0).1) w' V') 0 (bondVariation k' e) -
          fderiv ℝ (readInChart (subtractTrivial f F (fineBondAt Y h o 0).1) w V) 0 (bondVariation k e)| ≤
          C * E * ‖e‖ / torusDecayFactor L δ ((L : ℝ) * ((r : ℝ) - s - 2))
end YangMills.Construction.ColdStepAtMirrorFrames
end
