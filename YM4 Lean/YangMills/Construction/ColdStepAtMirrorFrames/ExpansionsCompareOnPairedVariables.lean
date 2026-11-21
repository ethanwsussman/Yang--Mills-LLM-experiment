import YangMills.Construction.ColdStepAtMirrorFrames.ChartPointsNearABox
import YangMills.Construction.ColdStepAtMirrorFrames.PairedVariablesOfTwoTori
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.FamilyNorms
namespace YangMills.Construction.ColdStepAtMirrorFrames
def PairedExpansionsComparison : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (L t n₀ : ℕ) (σ δ ε ε₃ : ℝ) (f : LocalFamily), Odd L → 0 ≤ δ → 0 ≤ ε →
    IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ f →
    ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
      (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
      (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (q r₂ s : ℕ) (θ ρ hh : ℝ)
      (Δ : StepVariable (finiteCells F))
      (ι : Type) [Fintype ι] [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F)))
      (j' : ι → ↥(chordBonds (finiteCells F'))) (h o : Fin 4 → ℤ),
      IsCubicTorusAbove L t n₀ F → IsCubicTorusAbove L t n₀ F' → 0 ≤ θ → 0 < ρ → 0 < hh → hh ≤ ρ →
      r₂ ≤ q →
      (∀ i, 2 * q + 2 < F.extent i) → (∀ i, 2 * q + 2 < F'.extent i) →
      Function.Injective j → Function.Injective j' → AreOffsetPaired Y Y' q j j' →
      (∀ b, ‖Δ b‖ ≤ θ) → (∀ b, b ∉ ballChordBonds F Y r₂ → Δ b = 0) →
      (∀ (h₁ o₁ : Fin 4 → ℤ) (i : Fin 4), WithinRadius r₂ h₁ → o₁ ∈ centredCube L →
        fineBondAt Y h₁ o₁ i ∈ chordBonds (finiteCells F) →
        shiftCoordinates w Δ (fineBondAt Y h₁ o₁ i).1 i = w' (fineBondAt Y' h₁ o₁ i).1 i) →
      (∀ ξ ∈ openPolyball ι (2 * ρ), ∀ v ∈ Set.Icc (0 : ℝ) 1,
        IsSmallCurvature σ (chartedField (shiftCoordinates w (pushforwardField j ξ + v • Δ)) V) ∧
          ∀ b ∈ chordBonds (finiteCells F),
            ‖shiftCoordinates w (pushforwardField j ξ + v • Δ) b.1 b.2‖ ≤ 1) →
      (∀ ξ ∈ openPolyball ι (2 * ρ),
        IsSmallCurvature σ (chartedField (shiftCoordinates w' (pushforwardField j' ξ)) V') ∧
          ∀ b ∈ chordBonds (finiteCells F'), ‖shiftCoordinates w' (pushforwardField j' ξ) b.1 b.2‖ ≤ 1) →
      AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r₂ → WithinRadius s h →
      q / 2 + 2 * s + 4 ≤ r₂ → o ∈ centredCube L →
      ContDiffOn ℝ 2 (fun ξ => subtractTrivial f F (fineBondAt Y h o 0).1
        (chartedField (shiftCoordinates w (pushforwardField j ξ)) V)) (openPolyball ι (2 * ρ)) ∧
      ContDiffOn ℝ 2 (fun ξ => subtractTrivial f F' (fineBondAt Y' h o 0).1
        (chartedField (shiftCoordinates w' (pushforwardField j' ξ)) V')) (openPolyball ι (2 * ρ)) ∧
      ∀ ξ ∈ openPolyball ι ρ,
        |subtractTrivial f F' (fineBondAt Y' h o 0).1
              (chartedField (shiftCoordinates w' (pushforwardField j' ξ)) V') -
            subtractTrivial f F (fineBondAt Y h o 0).1
              (chartedField (shiftCoordinates w (pushforwardField j ξ)) V)| ≤
          ε / torusDecayFactor L δ ((L : ℝ) * ((r₂ : ℝ) - s - 2)) +
            C * ε * θ * (ballChordBonds F Y r₂).card ∧
        ∀ (k : ι) (u : BondVector), ‖u‖ = 1 →
          |bondPartialDeriv (fun ξ => subtractTrivial f F' (fineBondAt Y' h o 0).1
                (chartedField (shiftCoordinates w' (pushforwardField j' ξ)) V')) k ξ u -
            bondPartialDeriv (fun ξ => subtractTrivial f F (fineBondAt Y h o 0).1
                (chartedField (shiftCoordinates w (pushforwardField j ξ)) V)) k ξ u| ≤
            C * ε / torusDecayFactor L δ ((L : ℝ) * ((r₂ : ℝ) - s - 2)) +
              2 * (C * ε * θ * (ballChordBonds F Y r₂).card) / hh + 2 * (C * ε) * hh +
              2 * (C * ε) * Real.exp (-(δ * L * (((q / 2 : ℕ) : ℝ) - s)))
end YangMills.Construction.ColdStepAtMirrorFrames
end
