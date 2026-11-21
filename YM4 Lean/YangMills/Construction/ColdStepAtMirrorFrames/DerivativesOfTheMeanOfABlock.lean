import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import YangMills.Construction.ColdStepAtMirrorFrames.ObservablesOfTheExponent
import YangMills.Construction.ColdStepAtMirrorFrames.RimMeanIsAWeightedMean
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
structure IsCellFamily (a ρA ρ lam x v : ℝ) (m : ℕ) (Φ : StepVariable (finiteCells F) → ℝ) (Y : F.Cell)
    (U : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (A H : (Fin k → ℝ) → StepVariable (finiteCells F) → ℝ) : Prop where
  apply_zero : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) → A 0 η = Φ η
  deriv_potential : ∀ (j : ℕ) (l : Fin (j + 1) → Fin k), j + 1 ≤ 3 → ∀ η : StepVariable (finiteCells F),
    (∀ b, ‖η b‖ < ρ) → paramIteratedDeriv A (fun i => Pi.single (l i) 1) 0 η =
      v * exponentObservable a ρA x m U (c ∘ l) (X ∘ l) η
  deriv_observable : ∀ (j : ℕ) (l : Fin j → Fin k), j ≤ 3 → ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < ρ) →
    paramIteratedDeriv H (fun i => Pi.single (l i) 1) 0 η = cellObservable a ρA lam x m Y U (c ∘ l) (X ∘ l) η
def CellMeanDerivBound (N : ℕ) (κ lam : ℝ) (Cq : ℕ → ℝ) (Kc : ℝ) : Prop :=
      ∀ (F : BlockFrame) (a ρA ρ x v : ℝ) (m : ℕ) (p : ℝ → ℝ) (U : F.GaugeField F.top)
        (Φ : BondField ↥(chordBonds (finiteCells F)) → ℝ) (K : ↥(chordBonds (finiteCells F)) →
          ↥(chordBonds (finiteCells F)) → ℝ) (Y : F.Cell) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
        (X : Fin k → imaginaryQuaternions) (A H : (Fin k → ℝ) → StepVariable (finiteCells F) → ℝ)
        (B : Set (Fin k → ℝ)) (M : ℝ),
        0 < ρ → 0 < x → IsCutoff ρ p → 0 ≤ v → v ≤ 1 → k ≤ 3 →
        (∀ z : F.Cell, (Finset.univ.filter fun b : ↥(chordBonds (finiteCells F)) => enclosingCell b.1.1 = z).card ≤ N) →
        IsUniformlyConvexDecaying ρ (x * lam / 4) κ (chordBondDist F) Φ K →
        (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
          |bondPartialDeriv Φ b 0 e| ≤ Real.sqrt (x * lam / 4) * ‖e‖) →
        IsOpen B → (0 : Fin k → ℝ) ∈ B →
        IsDominatedSmoothFamily (cutoffLaw F ρ p) 3 B M A → IsDominatedSmoothFamily (cutoffLaw F ρ p) 3 B M H →
        IsCellFamily a ρA ρ lam x v m Φ Y U c X A H →
        (∀ (j : ℕ) (l : Fin j → Fin k), j ≤ 3 →
          ObservableBounds a ρA ρ lam x κ m p Cq Φ Y U (c ∘ l) (X ∘ l)) →
        |iteratedFDeriv ℝ k (fun s => gibbsMean (cutoffLaw F ρ p) (A s) (H s)) 0 (fun l => Pi.single l 1)| ≤
          Kc * Real.exp (-(κ / 2 ^ 6 * bondSpan Y c))
def CellMeanDerivBoundExists : Prop :=
  ∀ (N : ℕ) (κ lam : ℝ) (Cq : ℕ → ℝ), 0 < κ → 0 < lam → (∀ q, 0 ≤ Cq q) →
    ∃ Kc : ℝ, 0 ≤ Kc ∧ CellMeanDerivBound N κ lam Cq Kc
end ColdStepAtMirrorFrames
end YangMills.Construction
end
