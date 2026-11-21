import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.Matrices
def GroupLieProduct (ι κ : Type) : Set (ι ⊕ κ → ComplexMatrix2) :=
  ComplexMatrix2.complexifiedProduct
    (Sum.elim (fun _ => ComplexMatrix2.FactorKind.group) fun _ => ComplexMatrix2.FactorKind.algebra)
namespace GroupLieProduct
variable {σ ι κ ι' κ' 𝔖 E : Type}
def tracelessPi (σ : Type) : Set (σ → ComplexMatrix2) :=
  ComplexMatrix2.complexifiedProduct fun _ => ComplexMatrix2.FactorKind.algebra
def unimodularPi (σ : Type) : Set (σ → ComplexMatrix2) :=
  ComplexMatrix2.complexifiedProduct fun _ => ComplexMatrix2.FactorKind.group
def supNorm (A : σ → ComplexMatrix2) : ℝ := ⨆ i, ComplexMatrix2.operatorNorm (A i)
def supBall (σ : Type) (s : ℝ) : Set (σ → ComplexMatrix2) :=
  {A ∈ tracelessPi σ | supNorm A < s}
def IsSupOpen (O : Set (σ → ComplexMatrix2)) : Prop :=
  O ⊆ tracelessPi σ ∧
    ∀ A ∈ O, ∃ s > 0, ∀ B ∈ tracelessPi σ, supNorm (B - A) < s → B ∈ O
def tupleOfCoords [Fintype σ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (ν : σ ≃ Fin (Fintype.card σ))
    (w : Coordinates.ComplexCoordinates (Fintype.card σ * 3)) (i : σ) : ComplexMatrix2 :=
  Coordinates.ComplexCoordinates.tracelessTuple b w (ν i)
def matrixPiEquiv {k : ℕ} (ν : σ ≃ Fin k) :
    (σ → ComplexMatrix2) ≃ Coordinates.ComplexCoordinates
      (Coordinates.ComplexCoordinates.productDim
        fun _ : Fin k => Coordinates.ComplexCoordinates.Component.matrix) :=
  (Equiv.arrowCongr ν (Equiv.refl ComplexMatrix2)).trans
    (Coordinates.ComplexCoordinates.productEquiv
      fun _ : Fin k => Coordinates.ComplexCoordinates.Component.matrix)
def IsHolomorphicOnTraceless [Fintype σ] {l : ℕ}
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E ≃ Coordinates.ComplexCoordinates l) (O : Set (σ → ComplexMatrix2))
    (f : (σ → ComplexMatrix2) → E) : Prop :=
  IsSupOpen O ∧ ∀ ν : σ ≃ Fin (Fintype.card σ),
    Coordinates.ComplexCoordinates.IsHolomorphicIn (tupleOfCoords b ν ⁻¹' O)
      (e ∘ f ∘ tupleOfCoords b ν)
def expChartAt (p A : ι ⊕ κ → ComplexMatrix2) : ι ⊕ κ → ComplexMatrix2
  | .inl i => ComplexMatrix2.matExp (A (.inl i)) * p (.inl i)
  | .inr k => p (.inr k) + A (.inr k)
def IsHolomorphicToCoords [Fintype ι] [Fintype κ] {l : ℕ}
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (e : E ≃ Coordinates.ComplexCoordinates l)
    (W : Set (ι ⊕ κ → ComplexMatrix2)) (Φ : (ι ⊕ κ → ComplexMatrix2) → E) : Prop :=
  ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W ∧ ContinuousOn (e ∘ Φ) W ∧
    ∀ p ∈ W, ∃ O : Set (ι ⊕ κ → ComplexMatrix2), 0 ∈ O ∧ (∀ A ∈ O, expChartAt p A ∈ W) ∧
      IsHolomorphicOnTraceless b e O (Φ ∘ expChartAt p)
def IsHolomorphicToTraceless [Fintype ι] [Fintype κ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (ι ⊕ κ → ComplexMatrix2)) (Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  MapsTo Φ W (ComplexMatrix2.traceless : Set ComplexMatrix2) ∧
    IsHolomorphicToCoords b Coordinates.ComplexCoordinates.matrixEquiv W Φ
def IsHolomorphicToUnimodular [Fintype ι] [Fintype κ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (ι ⊕ κ → ComplexMatrix2)) (Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W ∧
    MapsTo Φ W ComplexMatrix2.unitDeterminant ∧ ContinuousOn Φ W ∧
    ∀ p ∈ W, ∃ O : Set (ι ⊕ κ → ComplexMatrix2), 0 ∈ O ∧
      (∀ A ∈ O, expChartAt p A ∈ W ∧
        Φ (expChartAt p A) * (Φ p)⁻¹ ∈ ComplexMatrix2.logBall) ∧
      IsHolomorphicOnTraceless b Coordinates.ComplexCoordinates.matrixEquiv O
        fun A => ComplexMatrix2.logSeries (Φ (expChartAt p A) * (Φ p)⁻¹)
def IsHolomorphicToProduct [Fintype ι] [Fintype κ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (ι ⊕ κ → ComplexMatrix2))
    (Ψ : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ κ' → ComplexMatrix2) : Prop :=
  ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W ∧
    (∀ i, IsHolomorphicToUnimodular b W fun p => Ψ p (.inl i)) ∧
    ∀ k, IsHolomorphicToTraceless b W fun p => Ψ p (.inr k)
end GroupLieProduct
end YangMills.Construction.Matrices
