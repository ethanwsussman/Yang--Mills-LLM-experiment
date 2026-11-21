import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAlongAMotion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages Estimates
namespace ColdStepAtMirrorFrames
structure DerivativesCompare {F F' : BlockFrame} {j j' : ℕ} {κ : Type} (G : F.GaugeField j → ℝ)
    (G' : F'.GaugeField j' → ℝ) (W : F.GaugeField j) (W' : F'.GaugeField j') (I : Finset κ)
    (ι : κ → F.Site j × Fin 4) (ι' : κ → F'.Site j' × Fin 4) (ε₁ ε₂ E : ℝ) : Prop where
  labelled_first : ∀ (p : κ) (X : imaginaryQuaternions), p ∈ I → ‖X‖ = 1 →
    |bondDeriv G W ![ι p] ![X] - bondDeriv G' W' ![ι' p] ![X]| ≤ ε₁
  labelled_second : ∀ (p q : κ) (X Y : imaginaryQuaternions), p ∈ I → q ∈ I → ‖X‖ = 1 → ‖Y‖ = 1 →
    |bondDeriv G W ![ι p, ι q] ![X, Y] - bondDeriv G' W' ![ι' p, ι' q] ![X, Y]| ≤ ε₁
  unlabelled_first : ∀ (b : F.Site j × Fin 4) (X : imaginaryQuaternions), b ∉ ι '' I → ‖X‖ = 1 →
    |bondDeriv G W ![b] ![X]| ≤ ε₂
  unlabelled_first' : ∀ (b : F'.Site j' × Fin 4) (X : imaginaryQuaternions), b ∉ ι' '' I → ‖X‖ = 1 →
    |bondDeriv G' W' ![b] ![X]| ≤ ε₂
  unlabelled_second : ∀ (b b' : F.Site j × Fin 4) (X Y : imaginaryQuaternions),
    (b ∉ ι '' I ∨ b' ∉ ι '' I) → ‖X‖ = 1 → ‖Y‖ = 1 → |bondDeriv G W ![b, b'] ![X, Y]| ≤ ε₂
  unlabelled_second' : ∀ (b b' : F'.Site j' × Fin 4) (X Y : imaginaryQuaternions),
    (b ∉ ι' '' I ∨ b' ∉ ι' '' I) → ‖X‖ = 1 → ‖Y‖ = 1 → |bondDeriv G' W' ![b, b'] ![X, Y]| ≤ ε₂
  bound_first' : ∀ (b : F'.Site j' × Fin 4) (X : imaginaryQuaternions), ‖X‖ = 1 →
    |bondDeriv G' W' ![b] ![X]| ≤ E
  bound_second' : ∀ (b b' : F'.Site j' × Fin 4) (X Y : imaginaryQuaternions), ‖X‖ = 1 → ‖Y‖ = 1 →
    |bondDeriv G' W' ![b, b'] ![X, Y]| ≤ E
def TwoMotionsCompare : Prop :=
  ∀ (F F' : BlockFrame) (j j' : ℕ) (κ : Type) (T : Finset (F.Site j × Fin 4))
    (T' : Finset (F'.Site j' × Fin 4)) (G : F.GaugeField j → ℝ) (G' : F'.GaugeField j' → ℝ)
    (W : F.GaugeField j) (W' : F'.GaugeField j') (I : Finset κ)
    (ι : κ → F.Site j × Fin 4) (ι' : κ → F'.Site j' × Fin 4) (ε₁ ε₂ E K μ : ℝ)
    (α : (Fin 2 → ℝ) → F.Site j → Fin 4 → imaginaryQuaternions)
    (α' : (Fin 2 → ℝ) → F'.Site j' → Fin 4 → imaginaryQuaternions),
    (∀ b, b ∈ T) → (∀ b, b ∈ T') → Set.InjOn ι I → Set.InjOn ι' I →
    ContDiffThreeAlongBonds G W → ContDiffThreeAlongBonds G' W' →
    0 ≤ ε₁ → 0 ≤ ε₂ → 0 ≤ E → 0 ≤ K → 0 ≤ μ → DerivativesCompare G G' W W' I ι ι' ε₁ ε₂ E →
    (∀ x b, α 0 x b = 0) → (∀ x b, α' 0 x b = 0) →
    (∀ x b, ContDiffAt ℝ 3 (fun τ => α τ x b) 0) → (∀ x b, ContDiffAt ℝ 3 (fun τ => α' τ x b) 0) →
    (∀ l, ∑ b ∈ T, ‖motionComponent α ![l] b.1 b.2‖ ≤ K) →
    (∀ l, ∑ b ∈ T', ‖motionComponent α' ![l] b.1 b.2‖ ≤ K) →
    ∑ b ∈ T, ‖motionComponent α ![0, 1] b.1 b.2‖ ≤ K →
    ∑ b ∈ T', ‖motionComponent α' ![0, 1] b.1 b.2‖ ≤ K →
    (∀ l, ∑ p ∈ I, ‖motionComponent α ![l] (ι p).1 (ι p).2 -
      motionComponent α' ![l] (ι' p).1 (ι' p).2‖ ≤ μ) →
    ∑ p ∈ I, ‖motionComponent α ![0, 1] (ι p).1 (ι p).2 -
      motionComponent α' ![0, 1] (ι' p).1 (ι' p).2‖ ≤ μ →
    (∀ l : Fin 2, |iteratedFDeriv ℝ 1 (fun τ => G (leftTranslate (α τ) W)) 0 ![Pi.single l 1] -
      iteratedFDeriv ℝ 1 (fun τ => G' (leftTranslate (α' τ) W')) 0 ![Pi.single l 1]| ≤
        ε₁ * K + 2 * ε₂ * K + E * μ) ∧
    |iteratedFDeriv ℝ 2 (fun τ => G (leftTranslate (α τ) W)) 0 ![Pi.single 0 1, Pi.single 1 1] -
      iteratedFDeriv ℝ 2 (fun τ => G' (leftTranslate (α' τ) W')) 0 ![Pi.single 0 1, Pi.single 1 1]| ≤
      ε₁ * (K ^ 2 + K) + 2 * ε₂ * (K ^ 2 + K) + E * (2 * K + 1) * μ
end ColdStepAtMirrorFrames
end YangMills.Construction
end
