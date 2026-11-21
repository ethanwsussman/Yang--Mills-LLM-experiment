import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantOfOneMore
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Cumulants
namespace YangMills.Construction
namespace DensityMeans
variable {Ω : Type} [MeasurableSpace Ω] {n : ℕ}
def densityMean (μ : Measure Ω) (Z H : Ω → ℝ) : ℝ := (∫ ω, H ω * Z ω ∂μ) / ∫ ω, Z ω ∂μ
def mixedDerivAt (G : (Fin n → ℝ) → Ω → ℝ) (I : Finset (Fin n)) (ω : Ω) : ℝ :=
  iteratedFDeriv ℝ I.card (fun τ => G τ ω) 0 fun j => Pi.single (I.orderEmbOfFin rfl j) 1
def logDensity (Z : (Fin n → ℝ) → Ω → ℝ) : (Fin n → ℝ) → Ω → ℝ := fun τ ω => Real.log (Z τ ω)
def cumulantEntry (G Z : (Fin n → ℝ) → Ω → ℝ) (I : Finset (Fin n)) : Option (Finset (Fin n)) → Ω → ℝ
  | none => mixedDerivAt G I
  | some J => mixedDerivAt (logDensity Z) J
structure IsFlatDensity (μ : Measure Ω) (B : Set (Fin n → ℝ)) (K : ℝ) (Z : (Fin n → ℝ) → Ω → ℝ) : Prop where
  dominated : IsDominatedSmoothFamily μ n B K Z
  nonneg : ∀ᵐ ω ∂μ, ∀ τ ∈ B, 0 ≤ Z τ ω
  iteratedFDeriv_eq_zero : ∀ᵐ ω ∂μ, ∀ τ ∈ B, Z τ ω = 0 → ∀ j : ℕ, j ≤ n → iteratedFDeriv ℝ j (fun τ' => Z τ' ω) τ = 0
  integral_pos : 0 < ∫ ω, Z 0 ω ∂μ
  integrable_prod : ∀ (S : Finset (Fin n)) (π : Finpartition S),
    Integrable (fun ω => (∏ J ∈ π.parts, mixedDerivAt (logDensity Z) J ω) * Z 0 ω) μ
def DensityMeanCumulantExpansion : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (n : ℕ) (B : Set (Fin n → ℝ)) (K K' : ℝ)
    (G Z : (Fin n → ℝ) → Ω → ℝ), IsOpen B → (0 : Fin n → ℝ) ∈ B → IsDominatedSmoothFamily μ n B K G →
    IsFlatDensity μ B K' Z →
    ContDiffAt ℝ n (fun τ => densityMean μ (Z τ) (G τ)) 0 ∧
    iteratedFDeriv ℝ n (fun τ => densityMean μ (Z τ) (G τ)) 0 (fun i => Pi.single i 1) =
      ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset, ∑ π : Finpartition (Finset.univ \ I),
        jointCumulant (densityMean μ (Z 0)) (insert none (π.parts.image some)) (cumulantEntry G Z I)
end DensityMeans
end YangMills.Construction
end
