import YangMills.Construction.ColdStepAtMirrorFrames.BirthsAlongTwoSegments
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames
open scoped Topology
namespace YangMills.Construction.GibbsMeans
variable {Ω : Type} [MeasurableSpace Ω] {k : ℕ}
def partialFamily (H : ℝ → (Fin k → ℝ) → Ω → ℝ) (i : Fin k) : ℝ → (Fin k → ℝ) → Ω → ℝ :=
  fun t τ ω => fderiv ℝ (fun τ' => H t τ' ω) τ (Pi.single i 1)
structure IsModerateValue (t₀ : ℝ) (B : Set (Fin k → ℝ)) (s : Ω → ℝ) (H : ℝ → (Fin k → ℝ) → Ω → ℝ) : Prop where
  measurable : ∀ t ∈ Set.Icc 0 t₀, ∀ τ ∈ B, Measurable (H t τ)
  abs_le_pow : ∃ (C : ℝ) (m : ℕ), ∀ t ∈ Set.Icc 0 t₀, ∀ τ ∈ B, ∀ ω, |H t τ ω| ≤ C * s ω ^ m
  continuousOn : ∀ t ∈ Set.Icc 0 t₀, ∀ ω, ContinuousOn (fun τ => H t τ ω) B
  tendsto_zero : ∀ ω, Filter.Tendsto (fun t => H t 0 ω) (𝓝[>] 0) (𝓝 (H 0 0 ω))
def IsModerate (t₀ : ℝ) (B : Set (Fin k → ℝ)) (s : Ω → ℝ) : ℕ → (ℝ → (Fin k → ℝ) → Ω → ℝ) → Prop
  | 0, H => IsModerateValue t₀ B s H
  | n + 1, H => IsModerateValue t₀ B s H ∧
      (∀ t ∈ Set.Icc 0 t₀, ∀ τ ∈ B, ∀ ω, DifferentiableAt ℝ (fun τ' => H t τ' ω) τ) ∧
      ∀ i, IsModerate t₀ B s n (partialFamily H i)
structure AreDominatedGibbsLaws (t₀ : ℝ) (B : Set (Fin k → ℝ)) (s : Ω → ℝ) (ν : ℝ → Measure Ω)
    (U : ℝ → (Fin k → ℝ) → Ω → ℝ) : Prop where
  dominated : ∀ t ∈ Set.Icc 0 t₀, ∃ W : Ω → ℝ, (∀ τ ∈ B, ∀ ω, Real.exp (-U t τ ω) ≤ W ω) ∧
    ∀ m : ℕ, Integrable (fun ω => s ω ^ m * W ω) (ν t)
  integral_pos : ∀ t ∈ Set.Icc 0 t₀, ∀ τ ∈ B, 0 < ∫ ω, Real.exp (-U t τ ω) ∂ν t
def coordIteratedDeriv (G : ℝ → (Fin k → ℝ) → Ω → ℝ) {j : ℕ} (c : Fin j → Fin k) : ℝ → (Fin k → ℝ) → Ω → ℝ :=
  fun t τ ω => iteratedFDeriv ℝ j (fun τ' => G t τ' ω) τ fun i => Pi.single (c i) 1
def GibbsMeanIteratedDerivTendsto : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (k n : ℕ) (t₀ : ℝ) (B : Set (Fin k → ℝ)) (s : Ω → ℝ) (ν : ℝ → Measure Ω)
    (U H : ℝ → (Fin k → ℝ) → Ω → ℝ),
    0 < t₀ → IsOpen B → (0 : Fin k → ℝ) ∈ B → (∀ ω, 1 ≤ s ω) → AreDominatedGibbsLaws t₀ B s ν U →
    IsModerate t₀ B s n U → IsModerate t₀ B s n H →
    (∀ H' : ℝ → (Fin k → ℝ) → Ω → ℝ, IsModerateValue t₀ B s H' →
      Filter.Tendsto (fun t => gibbsMean (ν t) (U t 0) (H' t 0)) (𝓝[>] 0)
        (𝓝 (gibbsMean (ν 0) (U 0 0) (H' 0 0)))) →
    (∀ t ∈ Set.Icc 0 t₀, ContDiffOn ℝ n (fun τ => gibbsMean (ν t) (U t τ) (H t τ)) B) ∧
    ∀ v : Fin n → Fin k → ℝ, Filter.Tendsto
      (fun t => iteratedFDeriv ℝ n (fun τ => gibbsMean (ν t) (U t τ) (H t τ)) 0 v) (𝓝[>] 0)
      (𝓝 (iteratedFDeriv ℝ n (fun τ => gibbsMean (ν 0) (U 0 τ) (H 0 τ)) 0 v))
def IsModerateLinearCombination : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (k n : ℕ) (t₀ : ℝ) (B : Set (Fin k → ℝ)) (s : Ω → ℝ) (a b : ℝ)
    (H K : ℝ → (Fin k → ℝ) → Ω → ℝ), 0 < t₀ → IsOpen B → (0 : Fin k → ℝ) ∈ B → (∀ ω, 1 ≤ s ω) →
    IsModerate t₀ B s n H → IsModerate t₀ B s n K → IsModerate t₀ B s n fun t τ ω => a * H t τ ω + b * K t τ ω
def IsModerateOfCoordDerivBounds : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (k n : ℕ) (t₀ : ℝ) (B : Set (Fin k → ℝ)) (s : Ω → ℝ)
    (G : ℝ → (Fin k → ℝ) → Ω → ℝ), 0 < t₀ → IsOpen B → (0 : Fin k → ℝ) ∈ B →
    (∀ t ∈ Set.Icc 0 t₀, ∀ τ ∈ B, Measurable (G t τ)) →
    (∀ t ∈ Set.Icc 0 t₀, ∀ ω, ContDiffOn ℝ n (fun τ => G t τ ω) B) →
    (∃ (C : ℝ) (m : ℕ), ∀ (j : ℕ) (c : Fin j → Fin k), j ≤ n → ∀ t ∈ Set.Icc 0 t₀, ∀ τ ∈ B, ∀ ω,
      |coordIteratedDeriv G c t τ ω| ≤ C * s ω ^ m) →
    (∀ (j : ℕ) (c : Fin j → Fin k), j ≤ n → ∀ ω,
      Filter.Tendsto (fun t => coordIteratedDeriv G c t 0 ω) (𝓝[>] 0) (𝓝 (coordIteratedDeriv G c 0 0 ω))) →
    IsModerate t₀ B s n G
def GibbsMeanDerivativesConverge : Prop :=
  GibbsMeanIteratedDerivTendsto ∧ IsModerateLinearCombination ∧ IsModerateOfCoordDerivBounds
end YangMills.Construction.GibbsMeans
end
