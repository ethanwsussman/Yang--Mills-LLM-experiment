import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.LeftChartSecondDerivative
section Definitions
variable {α : Type*} {N : ℕ}
def chartPoint (b : Fin N → α) (U X : α → Matrices.ComplexMatrix2) :
    Fin N → Matrices.ComplexMatrix2 :=
  fun i => Matrices.ComplexMatrix2.matExp (Complex.I • X (b i)) * U (b i)
def chartValue {E : Type*} (f : (Fin N → Matrices.ComplexMatrix2) → E) (b : Fin N → α)
    (U X : α → Matrices.ComplexMatrix2) : E :=
  f (chartPoint b U X)
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
def mixedAt (f : (Fin N → Matrices.ComplexMatrix2) → E) (b : Fin N → α)
    (U A A' : α → Matrices.ComplexMatrix2) : E :=
  mixedDirectionalDeriv 𝕜 (chartValue f b U) A A'
def MixedPartialExists (O : Set (Fin N → Matrices.ComplexMatrix2))
    (f : (Fin N → Matrices.ComplexMatrix2) → E) (b : Fin N → α)
    (U A A' : α → Matrices.ComplexMatrix2) : Prop :=
  (∀ᶠ p : 𝕜 × 𝕜 in 𝓝 0,
    chartPoint b U (algebraMap 𝕜 ℂ p.1 • A + algebraMap 𝕜 ℂ p.2 • A') ∈ O) ∧
  (∀ᶠ p : 𝕜 × 𝕜 in 𝓝 0, DifferentiableAt 𝕜
    (fun t : 𝕜 => chartValue f b U (algebraMap 𝕜 ℂ p.1 • A + algebraMap 𝕜 ℂ t • A')) p.2) ∧
  DifferentiableAt 𝕜
    (fun s : 𝕜 =>
      deriv (fun t : 𝕜 => chartValue f b U (algebraMap 𝕜 ℂ s • A + algebraMap 𝕜 ℂ t • A')) 0)
    0
def MixedPartialProperties (𝒮 : Set (α → Matrices.ComplexMatrix2))
    (O : Set (Fin N → Matrices.ComplexMatrix2))
    (f : (Fin N → Matrices.ComplexMatrix2) → E) (b : Fin N → α)
    (U : α → Matrices.ComplexMatrix2) : Prop :=
  (∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, MixedPartialExists 𝕜 O f b U A A') ∧
  (∀ A₁ ∈ 𝒮, ∀ A₂ ∈ 𝒮, ∀ A' ∈ 𝒮, ∀ c : 𝕜,
    mixedAt 𝕜 f b U (algebraMap 𝕜 ℂ c • A₁ + A₂) A' =
      c • mixedAt 𝕜 f b U A₁ A' + mixedAt 𝕜 f b U A₂ A') ∧
  (∀ A ∈ 𝒮, ∀ A₁' ∈ 𝒮, ∀ A₂' ∈ 𝒮, ∀ c : 𝕜,
    mixedAt 𝕜 f b U A (algebraMap 𝕜 ℂ c • A₁' + A₂') =
      c • mixedAt 𝕜 f b U A A₁' + mixedAt 𝕜 f b U A A₂') ∧
  (∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, mixedAt 𝕜 f b U A A' = mixedAt 𝕜 f b U A' A) ∧
  (∀ A₁ ∈ 𝒮, ∀ A₂ ∈ 𝒮, ∀ A₁' ∈ 𝒮, ∀ A₂' ∈ 𝒮,
    (∀ i, A₁ (b i) = A₂ (b i)) → (∀ i, A₁' (b i) = A₂' (b i)) →
      mixedAt 𝕜 f b U A₁ A₁' = mixedAt 𝕜 f b U A₂ A₂')
end Definitions
variable {N : ℕ}
def HoldsRealVariables {α : Type} (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 𝒱 : Set (α → Matrices.ComplexMatrix2)) (b : Fin N → α) : Prop :=
  ∀ (O : Set (Fin N → Matrices.ComplexMatrix2)) (f : (Fin N → Matrices.ComplexMatrix2) → E),
    Matrices.specialUnitaryPower.IsOpenSubset O →
    Matrices.EmbeddedSubmanifold.HasDifferentiablePartialsOn
      (Matrices.specialUnitaryPower (Fin N)) O f →
    ∀ U ∈ 𝒱, (fun i => U (b i)) ∈ O → MixedPartialProperties ℝ 𝒜 O f b U
def HoldsComplexVariables {σ : Type} (𝒰 : Set (σ → Matrices.ComplexMatrix2)) (b : Fin N → σ) :
    Prop :=
  ∀ (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless)
    (O : Set (Fin N → Matrices.ComplexMatrix2)) (f : (Fin N → Matrices.ComplexMatrix2) → ℂ),
    Matrices.ComplexMatrix2.IsRelativelyOpen (Matrices.GroupLieProduct.unimodularPi (Fin N)) O →
    Matrices.GroupLieProduct.IsHolomorphicToCoords β (Equiv.funUnique (Fin 1) ℂ).symm
      (Matrices.GroupLieProduct.asGroupFactors '' O) (fun p => f fun i => p (.inl i)) →
    ∀ U ∈ 𝒰, (fun i => U (b i)) ∈ O →
      MixedPartialProperties ℂ
        (Matrices.GroupLieProduct.tracelessFunctions σ : Set (σ → Matrices.ComplexMatrix2)) O f b U
def HoldsOnLevel {α σ : Type} (N : ℕ) (toEdge : σ → α) (𝒜 𝒱 : Set (α → Matrices.ComplexMatrix2))
    (𝒰 : Set (σ → Matrices.ComplexMatrix2)) : Prop :=
  ∀ b : Fin N → σ,
    HoldsRealVariables ℝ 𝒜 𝒱 (toEdge ∘ b) ∧ HoldsRealVariables ℂ 𝒜 𝒱 (toEdge ∘ b) ∧
      HoldsComplexVariables 𝒰 b
def MainStatement : Prop :=
  ∀ L k j N : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k → 1 ≤ N →
    (∀ n : ℕ, 1 ≤ n →
      HoldsOnLevel N (fun e : PositiveEdge L n k j => (e.1 : Edge L n k j))
        (edgeFormSpace L n k j : Set (Edge L n k j → Matrices.ComplexMatrix2)) (fieldSpace L n k j)
        (restrictToPositiveEdges '' fieldsIn L n k j PeriodicLattice.complexGaugeGroup)) ∧
    HoldsOnLevel N
      (fun e : FullSpace.PositiveEdge (meshAt L k j) => (e.1 : FullSpace.Edge L k j))
      (FullSpace.edgeFormSpace (meshAt L k j) : Set (FullSpace.Edge L k j → Matrices.ComplexMatrix2))
      (FullSpace.fieldSpace L k j)
      (FullSpace.restrictToPositiveEdges ''
        FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
end YangMills.Construction.Tower.LeftChartSecondDerivative
end
