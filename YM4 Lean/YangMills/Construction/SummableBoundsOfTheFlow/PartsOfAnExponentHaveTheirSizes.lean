import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
open BlockAverages ColdStepAtMirrorFrames
variable {F : BlockFrame}
abbrev ExponentParts (F : BlockFrame) : Type := F.Cell → F.GaugeField F.top → StepVariable (finiteCells F) → ℝ
def partCentredDeriv (ψ : ExponentParts F) (lam x : ℝ) (Y : F.Cell) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (η : StepVariable (finiteCells F)) : ℝ :=
  bondDeriv (fun W => ψ Y W η - cellQuadratic lam x Y η) V c X
def exponentDerivSum (ψ : ExponentParts F) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (η : StepVariable (finiteCells F)) : ℝ :=
  ∑ Y ∈ finiteCells F, bondDeriv (fun W => ψ Y W η) V c X
structure ExponentPartsBounds (ρ x κ C : ℝ) (ψ : ExponentParts F) (V : F.GaugeField F.top) : Prop where
  deriv_top : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ < ρ) → k ≤ 3 → AreUnitVectors X →
    |bondDeriv (fun W => ψ Y W η) V c X| ≤
      C * (x * localSqNorm κ Y η + 1) * Real.exp (-(2 ^ 6 * κ * bondSpan Y c))
  deriv_top_partial : ∀ (Y : F.Cell) (η : StepVariable (finiteCells F)) (b : ↥(chordBonds (finiteCells F)))
    (e : BondVector) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), (∀ b, ‖η b‖ < ρ) →
    k ≤ 3 → AreUnitVectors X → ‖e‖ = 1 →
    |bondDeriv (fun W => bondPartialDeriv (ψ Y W) b η e) V c X| ≤
      C * (x * Real.sqrt (localSqNorm κ Y η) + 1) *
        Real.exp (-(2 ^ 6 * κ * bondSpanWithCell Y (enclosingCell b.1.1) c))
structure ExponentPartsSizes (ρ lam x κ : ℝ) (p : ℝ → ℝ) (Cq : ℕ → ℝ) (ψ : ExponentParts F)
    (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ) (Y : F.Cell) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) : Prop where
  smooth_centred : ContDiffOn ℝ 1 (partCentredDeriv ψ lam x Y V c X) {η | ∀ b, ‖η b‖ < ρ}
  smooth_sum : ContDiffOn ℝ 1 (exponentDerivSum ψ V c X) {η | ∀ b, ‖η b‖ < ρ}
  moment_centred : MomentBound (cutoffFactor ρ p) Ψ (partCentredDeriv ψ lam x Y V c X) 1
    (Cq 1 * Real.exp (-(2 ^ 5 * κ * bondSpan Y c)))
  size_centred : HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ (Real.exp (-(2 ^ 5 * κ * bondSpan Y c)))
    (fun b => (cellSupDist (enclosingCell b.1.1) Y : ℝ)) (partCentredDeriv ψ lam x Y V c X)
  size_sum : ∀ (v : ℝ) (l : Fin k), 0 ≤ v → v ≤ 1 →
    HasLocalSize ρ (cutoffFactor ρ p) Ψ Cq x κ (Real.exp (-(2 ^ 4 * κ * bondSpan (c l).1 c)))
      (fun b => (cellSupDist (enclosingCell b.1.1) (c l).1 : ℝ))
      (fun η => v * exponentDerivSum ψ V c X η)
def ExponentPartsConstants (L : ℕ) (κ lam C : ℝ) (Cq : ℕ → ℝ) : Prop :=
      ∀ (F : BlockFrame) (ρ x : ℝ) (p : ℝ → ℝ) (ψ : ExponentParts F) (V : F.GaugeField F.top)
        (Ψ : BondField ↥(chordBonds (finiteCells F)) → ℝ) (K : ↥(chordBonds (finiteCells F)) →
          ↥(chordBonds (finiteCells F)) → ℝ) (Y : F.Cell),
        F.blockSide = L → (∀ i, 2 ≤ F.extent i) → 0 < ρ → 1 ≤ x → IsCutoff ρ p →
        ExponentPartsBounds ρ x κ C ψ V →
        (∀ (Y' : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
          (η : StepVariable (finiteCells F)), k ≤ 3 → (∀ b, ‖η b‖ ≤ ρ) →
          ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
            ψ Y' (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V) q.2) (0, η)) →
        IsUniformlyConvexDecaying ρ (x * lam / 4) κ (chordBondDist F) Ψ K →
        (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
          |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) →
        ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 3 → AreUnitVectors X →
          ExponentPartsSizes ρ lam x κ p Cq ψ Ψ Y V c X
def exponentPartsSizes : Prop :=
  ∀ (L : ℕ) (κ lam C : ℝ), Odd L → 0 < κ → 0 < lam → 0 ≤ C →
    ∃ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) ∧ ExponentPartsConstants L κ lam C Cq
end YangMills.Construction.Interpolation
end
