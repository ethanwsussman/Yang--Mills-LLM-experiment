import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction
namespace MomentMethod
structure TranslatedLaws where
  Ω : ℕ → Type
  [mΩ : ∀ i, MeasurableSpace (Ω i)]
  μ : ∀ i, Measure (Ω i)
  τ : ∀ i, Ω i → Ω i
attribute [instance] TranslatedLaws.mΩ
namespace TranslatedLaws
variable (T : TranslatedLaws)
abbrev Family : Type := ∀ i, T.Ω i → ℝ
variable {T}
def translate (X : T.Family) (k : ℕ) : T.Family := fun i ω => X i ((T.τ i)^[k] ω)
variable (T)
structure IsPreserving : Prop where
  isProbability : ∀ i, IsProbabilityMeasure (T.μ i)
  measurePreserving : ∀ i, MeasurePreserving (T.τ i) (T.μ i) (T.μ i)
def subsequence (φ : ℕ → ℕ) : TranslatedLaws where
  Ω i := T.Ω (φ i)
  μ i := T.μ (φ i)
  τ i := T.τ (φ i)
variable {T}
structure HasBoundedMoments (X : T.Family) : Prop where
  aemeasurable : ∀ i, AEMeasurable (X i) (T.μ i)
  moment_bound : ∀ q : ℕ, ∃ C : ℝ, ∀ i, ∫⁻ ω, ENNReal.ofReal (|X i ω| ^ q) ∂(T.μ i) ≤ ENNReal.ofReal C
end TranslatedLaws
abbrev TranslateValues (J : Type) : Type := J × ℕ → ℝ
def translateShift {J : Type} (v : TranslateValues J) : TranslateValues J := fun a => v (a.1, a.2 + 1)
def shiftInvariantSigma (J : Type) : MeasurableSpace (TranslateValues J) :=
  MeasurableSpace.invariants (translateShift (J := J)) ⊓ MeasurableSpace.pi
structure IsJointLimitLaw (T : TranslatedLaws) {J : Type} (X : J → T.Family) (P : Measure (TranslateValues J)) : Prop where
  isProbability : IsProbabilityMeasure P
  tendsto : ∀ (l : ℕ) (a : Fin l → J × ℕ) (G : (Fin l → ℝ) → ℝ), Continuous G → (∃ C : ℝ, ∀ w, |G w| ≤ C) →
    Tendsto (fun i => ∫ ω, G (fun c => TranslatedLaws.translate (X (a c).1) (a c).2 i ω) ∂(T.μ i)) atTop
      (𝓝 (∫ v, G (fun c => v (a c)) ∂P))
def invariantCondExp {J : Type} (P : Measure (TranslateValues J)) (Y : TranslateValues J → ℝ) : TranslateValues J → ℝ :=
  P[Y | shiftInvariantSigma J]
def evalAtZero {J : Type} (j : J) (v : TranslateValues J) : ℝ := v (j, 0)
end MomentMethod
end YangMills.Construction
end
