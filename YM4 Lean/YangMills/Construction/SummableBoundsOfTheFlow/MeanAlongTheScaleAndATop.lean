import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongParametersIsASumOfCumulants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ScaleDerivatives
open MeasureTheory ColdStepAtMirrorFrames DensityMeans Cumulants
variable {ι : Type} [Fintype ι] {k : ℕ}
def scaledCutoff (ρ : ℝ) (p : ℝ → ℝ) (l : ℝ) (ζ : BondField ι) : ℝ := ∏ b, cutoffFactor ρ p ‖l • ζ b‖
def scaledDensity (ρ : ℝ) (p : ℝ → ℝ) (A : (ℝ × BondField ι) × (Fin k → ℝ) → ℝ) (q : ℝ × (Fin k → ℝ))
    (ζ : BondField ι) : ℝ :=
  scaledCutoff ρ p q.1 ζ * Real.exp (-A ((q.1, ζ), q.2))
def scaledTopMean (ρ : ℝ) (p : ℝ → ℝ) (A G : (ℝ × BondField ι) × (Fin k → ℝ) → ℝ)
    (q : ℝ × (Fin k → ℝ)) : ℝ :=
  densityMean volume (scaledDensity ρ p A q) fun ζ => G ((q.1, ζ), q.2)
def scaleTopSplit (i k : ℕ) (τ : Fin (i + k) → ℝ) : ℝ × (Fin k → ℝ) :=
  (∑ a : Fin i, τ (Fin.castAdd k a), fun b => τ (Fin.natAdd i b))
def shiftedAlongScale (i : ℕ) (l : ℝ) (f : (ℝ × BondField ι) × (Fin k → ℝ) → ℝ) (τ : Fin (i + k) → ℝ)
    (ζ : BondField ι) : ℝ :=
  f ((l + (scaleTopSplit i k τ).1, ζ), (scaleTopSplit i k τ).2)
def cutoffDerivAlong (i k : ℕ) (p : ℝ → ℝ) (l : ℝ) (J : Finset (Fin (i + k))) (b : ι) (ζ : BondField ι) : ℝ :=
  if ∀ a ∈ J, (a : ℕ) < i then ‖ζ b‖ ^ J.card * iteratedDeriv J.card p (l * ‖ζ b‖) else 0
def scaleCumulantEntries (i : ℕ) (p : ℝ → ℝ) (l : ℝ) (A G : (ℝ × BondField ι) × (Fin k → ℝ) → ℝ)
    (I : Finset (Fin (i + k))) : Option (Finset (Fin (i + k))) → BondField ι → ℝ
  | none => mixedDerivAt (shiftedAlongScale i l G) I
  | some J => fun ζ => -mixedDerivAt (shiftedAlongScale i l A) J ζ - ∑ b, cutoffDerivAlong i k p l J b ζ
def ScaledMeanCumulantExpansion : Prop :=
  ∀ (ι : Type) [Fintype ι] (ρ : ℝ) (p : ℝ → ℝ) (i k : ℕ) (A G : (ℝ × BondField ι) × (Fin k → ℝ) → ℝ)
    (l : ℝ), 0 < ρ → IsCutoff ρ p → 0 < l →
    (∀ ζ : BondField ι, (∀ b, l * ‖ζ b‖ ≤ ρ) → ContDiffAt ℝ (i + k : ℕ) A ((l, ζ), 0)) →
    (∀ ζ : BondField ι, (∀ b, l * ‖ζ b‖ ≤ ρ) → ContDiffAt ℝ (i + k : ℕ) G ((l, ζ), 0)) →
    (∀ (j q : ℕ) (b : ι), 1 ≤ j → 1 ≤ q →
      Integrable fun ζ => |iteratedDeriv j p (l * ‖ζ b‖)| ^ q * scaledDensity ρ p A (l, 0) ζ) →
    (1 ≤ i → ContDiffAt ℝ (i + k : ℕ) (scaledTopMean ρ p A G) (l, 0)) ∧
    iteratedDeriv i (fun l' => iteratedFDeriv ℝ k (fun τ => scaledTopMean ρ p A G (l', τ)) 0
        fun j => Pi.single j 1) l =
      ∑ I ∈ (Finset.univ : Finset (Fin (i + k))).powerset, ∑ π : Finpartition (Finset.univ \ I),
        jointCumulant (densityMean volume (scaledDensity ρ p A (l, 0))) (insert none (π.parts.image some))
          (scaleCumulantEntries i p l A G I)
end YangMills.Construction.ScaleDerivatives
end
