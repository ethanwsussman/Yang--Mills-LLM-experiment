import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct
namespace ExpChartHolomorphy
def logChart {ι κ : Type} (p q : ι ⊕ κ → ComplexMatrix2) : ι ⊕ κ → ComplexMatrix2
  | .inl i => ComplexMatrix2.logSeries (q (.inl i) * (p (.inl i))⁻¹)
  | .inr k => q (.inr k) - p (.inr k)
def pointOfUnimodularPower {n : ℕ} {κ : Type} [IsEmpty κ] (X : Fin n → ComplexMatrix2) :
    Fin n ⊕ κ → ComplexMatrix2 :=
  Sum.elim X fun k => isEmptyElim k
def AffineHolomorphy : Prop :=
  ∀ (N N' : ℕ) (P : Fin N' → MvPolynomial (Fin N) ℂ), (∀ j, (P j).totalDegree ≤ 1) →
    Coordinates.ComplexCoordinates.IsHolomorphicIn univ fun z j => MvPolynomial.eval z (P j)
def TracelessTopologiesAgree (σ : Type) [Fintype σ] : Prop :=
  ∀ O ⊆ tracelessPi σ, (IsSupOpen O ↔ ComplexMatrix2.IsRelativelyOpen (tracelessPi σ) O) ∧
    ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (ν : σ ≃ Fin (Fintype.card σ)),
      IsSupOpen O ↔ IsOpen (tupleOfCoords b ν ⁻¹' O)
def TracelessHolomorphyBasisFree (σ : Type) [Fintype σ] : Prop :=
  ∀ (E : Type) (l : ℕ) (e : E ≃ Coordinates.ComplexCoordinates l)
    (b b' : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (O : Set (σ → ComplexMatrix2)) (f : (σ → ComplexMatrix2) → E),
    IsHolomorphicOnTraceless b e O f ↔ IsHolomorphicOnTraceless b' e O f
def TracelessRestrictionHolomorphy (σ : Type) [Fintype σ] : Prop :=
  ∀ (E : Type) (l k : ℕ) (e : E ≃ Coordinates.ComplexCoordinates l) (ν : σ ≃ Fin k)
    (O : Set (σ → ComplexMatrix2)) (h : (σ → ComplexMatrix2) → E),
    Coordinates.ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν) e O h →
    ∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
      IsHolomorphicOnTraceless b e (O ∩ tracelessPi σ) h
def TracelessCoordsHolomorphy (σ τ : Type) [Fintype σ] [Fintype τ] : Prop :=
  ∀ (k : ℕ) (ν : τ ≃ Fin k) (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (O : Set (σ → ComplexMatrix2)) (f : (σ → ComplexMatrix2) → τ → ComplexMatrix2),
    IsHolomorphicOnTraceless b (matrixPiEquiv ν) O f →
    MapsTo f O (tracelessPi τ) →
    ∀ (b' : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (ν' : τ ≃ Fin (Fintype.card τ)),
      ∃ g : (σ → ComplexMatrix2) → Coordinates.ComplexCoordinates (Fintype.card τ * 3),
        IsHolomorphicOnTraceless b (Equiv.refl _) O g ∧
          ∀ A ∈ O, tupleOfCoords b' ν' (g A) = f A
def ExpChartLocalHomeomorph (ι κ : Type) [Fintype ι] [Fintype κ] : Prop :=
  ∀ p ∈ GroupLieProduct ι κ,
    (∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (k : ℕ) (ν : ι ⊕ κ ≃ Fin k),
      IsHolomorphicOnTraceless b (matrixPiEquiv ν) (tracelessPi (ι ⊕ κ))
        (expChartAt p)) ∧
    ContinuousOn (expChartAt p) (tracelessPi (ι ⊕ κ)) ∧
    MapsTo (expChartAt p) (tracelessPi (ι ⊕ κ)) (GroupLieProduct ι κ) ∧
    expChartAt p 0 = p ∧
    ∀ s : ℝ, 0 < s → Real.exp s ≤ 19 / 10 →
      InjOn (expChartAt p) (supBall (ι ⊕ κ) s) ∧
      ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) (expChartAt p '' supBall (ι ⊕ κ) s) ∧
      InvOn (logChart p) (expChartAt p) (supBall (ι ⊕ κ) s)
        (expChartAt p '' supBall (ι ⊕ κ) s) ∧
      ContinuousOn (logChart p) (expChartAt p '' supBall (ι ⊕ κ) s)
def UnimodularValuedHolomorphy (ι κ : Type) [Fintype ι] [Fintype κ] : Prop :=
  ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (W : Set (ι ⊕ κ → ComplexMatrix2))
    (Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2),
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W →
    MapsTo Φ W ComplexMatrix2.unitDeterminant →
    (IsHolomorphicToUnimodular b W Φ ↔
      IsHolomorphicToCoords b Coordinates.ComplexCoordinates.matrixEquiv W Φ)
def ProductRestrictionHolomorphy (ι κ : Type) [Fintype ι] [Fintype κ] : Prop :=
  ∀ (E : Type) (l k : ℕ) (e : E ≃ Coordinates.ComplexCoordinates l) (ν : ι ⊕ κ ≃ Fin k)
    (O : Set (ι ⊕ κ → ComplexMatrix2)) (Φ : (ι ⊕ κ → ComplexMatrix2) → E),
    Coordinates.ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν) e O Φ →
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) (O ∩ GroupLieProduct ι κ) ∧
      ∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
        IsHolomorphicToCoords b e (O ∩ GroupLieProduct ι κ) Φ
def CompHolomorphy (ι κ ι' κ' : Type) [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'] :
    Prop :=
  ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (W : Set (ι ⊕ κ → ComplexMatrix2))
    (Ψ : (ι ⊕ κ → ComplexMatrix2) → ι' ⊕ κ' → ComplexMatrix2),
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W → IsHolomorphicToProduct b W Ψ →
    ∀ (E : Type) (l : ℕ) (e : E ≃ Coordinates.ComplexCoordinates l)
      (W' : Set (ι' ⊕ κ' → ComplexMatrix2))
      (Φ : (ι' ⊕ κ' → ComplexMatrix2) → E), IsHolomorphicToCoords b e W' Φ →
      ContinuousOn Ψ W ∧ ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) (W ∩ Ψ ⁻¹' W') ∧
        IsHolomorphicToCoords b e (W ∩ Ψ ⁻¹' W') (Φ ∘ Ψ)
def UnimodularPowerHolomorphy (κ : Type) [Fintype κ] [IsEmpty κ] : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (b b' : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (Fin n ⊕ κ → ComplexMatrix2))
    (Φ : (Fin n ⊕ κ → ComplexMatrix2) → ComplexMatrix2),
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (Fin n) κ) W →
    MapsTo Φ W ComplexMatrix2.unitDeterminant →
    (IsHolomorphicToUnimodular b W Φ ↔
      Coordinates.ComplexCoordinates.IsHolomorphicOnSL2Power b' (pointOfUnimodularPower ⁻¹' W)
        (Φ ∘ pointOfUnimodularPower))
def TracelessPowerHolomorphy (ι κ : Type) [Fintype ι] [Fintype κ] [IsEmpty ι] : Prop :=
  ∀ (E : Type) (l : ℕ) (e : E ≃ Coordinates.ComplexCoordinates l)
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (ι ⊕ κ → ComplexMatrix2)) (Φ : (ι ⊕ κ → ComplexMatrix2) → E),
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W →
    (IsHolomorphicToCoords b e W Φ ↔ IsHolomorphicOnTraceless b e W Φ)
def ExpChartTheory : Prop :=
  AffineHolomorphy ∧
  (∀ (σ : Type) [Fintype σ], TracelessTopologiesAgree σ ∧
    TracelessHolomorphyBasisFree σ ∧ TracelessRestrictionHolomorphy σ) ∧
  (∀ (σ τ : Type) [Fintype σ] [Fintype τ], TracelessCoordsHolomorphy σ τ) ∧
  (∀ (ι κ : Type) [Fintype ι] [Fintype κ], ExpChartLocalHomeomorph ι κ ∧
    UnimodularValuedHolomorphy ι κ ∧ ProductRestrictionHolomorphy ι κ) ∧
  (∀ (ι κ ι' κ' : Type) [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'],
    CompHolomorphy ι κ ι' κ') ∧
  (∀ (κ : Type) [Fintype κ] [IsEmpty κ], UnimodularPowerHolomorphy κ) ∧
  (∀ (ι κ : Type) [Fintype ι] [Fintype κ] [IsEmpty ι], TracelessPowerHolomorphy ι κ)
end ExpChartHolomorphy
end YangMills.Construction.Matrices.GroupLieProduct
end
