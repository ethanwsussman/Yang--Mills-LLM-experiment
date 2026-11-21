import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.Interpolation
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def cellObservable (a ρA lam x : ℝ) (m : ℕ) (Y : F.Cell) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (η : StepVariable (finiteCells F)) : ℝ :=
  bondDeriv (fun V' => cellExponent false a ρA x m Y V' η - cellQuadratic lam x Y η) V c X
def exponentObservable (a ρA x : ℝ) (m : ℕ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ Y ∈ finiteCells F, bondDeriv (fun V' => cellExponent false a ρA x m Y V' η) V c X
structure ObservableBounds (a ρA ρ lam x κ : ℝ) (m : ℕ) (p : ℝ → ℝ) (Cq : ℕ → ℝ)
    (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ) (Y : F.Cell) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) : Prop where
  contDiffOn_cell : ContDiffOn ℝ 1 (cellObservable a ρA lam x m Y V c X) {η | ∀ b, ‖η b‖ < ρ}
  contDiffOn_exponent : ContDiffOn ℝ 1 (exponentObservable a ρA x m V c X) {η | ∀ b, ‖η b‖ < ρ}
  moment_cell : MomentBound (cutoffFactor ρ p) Ψ (cellObservable a ρA lam x m Y V c X) 1
    (Cq 1 * Real.exp (-(2 ^ 5 * κ * bondSpan Y c)))
  localSize_cell : HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ (Real.exp (-(2 ^ 5 * κ * bondSpan Y c)))
    (fun b => (cellSupDist (enclosingCell b.1.1) Y : ℝ)) (cellObservable a ρA lam x m Y V c X)
  localSize_exponent : ∀ (v : ℝ) (l : Fin k), 0 ≤ v → v ≤ 1 →
    HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ (Real.exp (-(2 ^ 4 * κ * bondSpan (c l).1 c)))
      (fun b => (cellSupDist (enclosingCell b.1.1) (c l).1 : ℝ))
      (fun η => v * exponentObservable a ρA x m V c X η)
def ObservableBoundsWithConstants (L : ℕ) (κ lam C : ℝ) (Cq : ℕ → ℝ) : Prop :=
      ∀ (F : BlockFrame) (a ρA ρ x : ℝ) (m : ℕ) (p : ℝ → ℝ) (V : F.GaugeField F.top)
        (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ) (K : ↥(chordBonds (finiteCells F)) →
          ↥(chordBonds (finiteCells F)) → ℝ) (Y : F.Cell),
        F.blockSide = L → (∀ i, 2 ≤ F.extent i) → 0 < ρ → 1 ≤ x → IsCutoff ρ p →
        CellExponentBounds false a ρA ρ x κ C m V →
        (∀ (Y' : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
          (η : StepVariable (finiteCells F)), (∀ b, ‖η b‖ ≤ ρ) →
          ContDiffAt ℝ 4 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
            cellExponent false a ρA x m Y' (leftTranslate (bondSpread c X q.1) V) q.2) (0, η)) →
        IsUniformlyConvexDecaying ρ (x * lam / 4) κ (chordBondDist F) Ψ K →
        (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
          |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) →
        ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 → AreUnitVectors X →
          ObservableBounds a ρA ρ lam x κ m p Cq Ψ Y V c X
def ExponentObservableBounds : Prop :=
  ∀ (L : ℕ) (κ lam C : ℝ), Odd L → 0 < κ → 0 < lam → 0 ≤ C →
    ∃ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) ∧ ObservableBoundsWithConstants L κ lam C Cq
end YangMills.Construction.ColdStepAtMirrorFrames
end
