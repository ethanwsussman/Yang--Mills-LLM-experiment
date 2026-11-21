import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMaps
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Matrices
namespace GroupLieProduct
namespace Subspaces
namespace LocalAnalyticity
open AnalyticCalculus
variable {S R S' : Type}
def RestrictionPreservesAnalytic [Fintype S] [Fintype R] (E : Submodule ℝ (S → ComplexMatrix2))
    (E' : Submodule ℝ (S' → ComplexMatrix2)) (R' : Type) (W : Set (R ⊕ S → ComplexMatrix2)) : Prop :=
  ∀ W₁ : Set (R ⊕ S → ComplexMatrix2), W₁ ⊆ W →
    ComplexMatrix2.IsRelativelyOpen (subspaceTimesGroup E R) W₁ →
    (∀ (l : ℕ) (f : (R ⊕ S → ComplexMatrix2) → Coordinates.ComplexCoordinates l),
      IsSubspaceAnalyticToCoords E W f → IsSubspaceAnalyticToCoords E W₁ f) ∧
    ∀ f : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2,
      IsSubspaceAnalyticToProduct E E' W f → IsSubspaceAnalyticToProduct E E' W₁ f
def AnalyticOfLocallyAnalytic [Fintype S] [Fintype R] (E : Submodule ℝ (S → ComplexMatrix2))
    (E' : Submodule ℝ (S' → ComplexMatrix2)) (R' : Type) (W : Set (R ⊕ S → ComplexMatrix2)) : Prop :=
  (∀ (l : ℕ) (f : (R ⊕ S → ComplexMatrix2) → Coordinates.ComplexCoordinates l),
    (∀ p ∈ W, ∃ W₁ : Set (R ⊕ S → ComplexMatrix2), W₁ ⊆ W ∧ p ∈ W₁ ∧
      ComplexMatrix2.IsRelativelyOpen (subspaceTimesGroup E R) W₁ ∧
        IsSubspaceAnalyticToCoords E W₁ f) →
    IsSubspaceAnalyticToCoords E W f) ∧
  ∀ f : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2,
    MapsTo f W (subspaceTimesGroup E' R') →
    (∀ p ∈ W, ∃ W₁ : Set (R ⊕ S → ComplexMatrix2), W₁ ⊆ W ∧ p ∈ W₁ ∧
      ComplexMatrix2.IsRelativelyOpen (subspaceTimesGroup E R) W₁ ∧
        IsSubspaceAnalyticToProduct E E' W₁ f) →
    IsSubspaceAnalyticToProduct E E' W f
def AddPreservesAnalytic [Fintype S] [Fintype R] (E : Submodule ℝ (S → ComplexMatrix2))
    (W : Set (R ⊕ S → ComplexMatrix2)) : Prop :=
  ∀ (l : ℕ) (f g : (R ⊕ S → ComplexMatrix2) → Coordinates.ComplexCoordinates l),
    IsSubspaceAnalyticToCoords E W f → IsSubspaceAnalyticToCoords E W g →
      IsSubspaceAnalyticToCoords E W fun p => f p + g p
def ChartMapsNhdInto [Fintype R] {n : ℕ} {E : Submodule ℝ (S → ComplexMatrix2)}
    (b : Module.Basis (Fin n) ℝ E) (σ : IndexEnum R) (x₀ : R ⊕ S → ComplexMatrix2)
    (W : Set (R ⊕ S → ComplexMatrix2)) : Prop :=
  ContinuousOn (basisExpChart b σ x₀)
      (Coordinates.ComplexCoordinates.realLocus (n + 3 * Fintype.card R)) ∧
    MapsTo (basisExpChart b σ x₀)
      (Coordinates.ComplexCoordinates.realLocus (n + 3 * Fintype.card R))
      (subspaceTimesGroup E R) ∧
    basisExpChart b σ x₀ 0 = x₀ ∧
    ComplexMatrix2.IsRelativelyOpen (basisExpChartSource n σ)
      (basisExpChartSource n σ ∩ basisExpChart b σ x₀ ⁻¹' W) ∧
    (x₀ ∈ W → (0 : ParamSpace n R) ∈ basisExpChartSource n σ ∩ basisExpChart b σ x₀ ⁻¹' W ∧
      ∃ U : Set (ParamSpace n R), ComplexMatrix2.IsRelativelyOpen (basisExpChartSource n σ) U ∧
        0 ∈ U ∧ basisExpChart b σ x₀ '' U ⊆ W)
def AnalyticReadInChart [Fintype S] [Fintype R] {n : ℕ}
    {E : Submodule ℝ (S → ComplexMatrix2)} (E' : Submodule ℝ (S' → ComplexMatrix2)) (R' : Type)
    (b : Module.Basis (Fin n) ℝ E) (σ : IndexEnum R) (x₀ : R ⊕ S → ComplexMatrix2)
    (W : Set (R ⊕ S → ComplexMatrix2)) : Prop :=
  ∀ U : Set (ParamSpace n R), ComplexMatrix2.IsRelativelyOpen (basisExpChartSource n σ) U →
    0 ∈ U → basisExpChart b σ x₀ '' U ⊆ W →
    ComplexMatrix2.IsRelativelyOpen (subspaceTimesGroup E R) (basisExpChart b σ x₀ '' U) ∧
    x₀ ∈ basisExpChart b σ x₀ '' U ∧
    (∀ (l : ℕ) (f : (R ⊕ S → ComplexMatrix2) → Coordinates.ComplexCoordinates l),
      IsSubspaceAnalyticToCoords E W f →
        IsSubspaceAnalyticToCoords E (basisExpChart b σ x₀ '' U) f ∧
          IsAnalyticInParams U (f ∘ basisExpChart b σ x₀)) ∧
    ∀ f : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2,
      IsSubspaceAnalyticToProduct E E' W f →
      IsSubspaceAnalyticToProduct E E' (basisExpChart b σ x₀ '' U) f ∧
        ∀ (k : ℕ) (μ : R' ⊕ S' ≃ Fin k),
          IsAnalyticInParams U (matrixPiEquiv μ ∘ f ∘ basisExpChart b σ x₀)
def AnalyticOfChartwiseAnalytic [Fintype S] [Fintype R]
    (E : Submodule ℝ (S → ComplexMatrix2)) (σ : IndexEnum R)
    (W : Set (R ⊕ S → ComplexMatrix2)) : Prop :=
  ∀ (l : ℕ) (f : (R ⊕ S → ComplexMatrix2) → Coordinates.ComplexCoordinates l),
    (∀ x₀ ∈ W, ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ E) (U : Set (ParamSpace n R)),
      ComplexMatrix2.IsRelativelyOpen (basisExpChartSource n σ) U ∧ 0 ∈ U ∧
        basisExpChart b σ x₀ '' U ⊆ W ∧
        Coordinates.ComplexCoordinates.IsRealAnalyticIn U (f ∘ basisExpChart b σ x₀)) →
    IsSubspaceAnalyticToCoords E W f
def LocalAnalyticityStatement : Prop :=
  ∀ (S R S' R' : Type) [Fintype S] [Fintype R] [Fintype S'] [Fintype R']
    (E : Submodule ℝ (S → ComplexMatrix2)) (E' : Submodule ℝ (S' → ComplexMatrix2)),
    E ≤ hermitianTracelessFunctions S → E' ≤ hermitianTracelessFunctions S' →
    ∀ W : Set (R ⊕ S → ComplexMatrix2), IsOpenInSubspaceTimesGroup E W →
      RestrictionPreservesAnalytic E E' R' W ∧
      AnalyticOfLocallyAnalytic E E' R' W ∧
      AddPreservesAnalytic E W ∧
      ∀ σ : IndexEnum R,
        (∀ (n : ℕ) (b : Module.Basis (Fin n) ℝ E) (x₀ : R ⊕ S → ComplexMatrix2),
          x₀ ∈ subspaceTimesGroup E R →
            ChartMapsNhdInto b σ x₀ W ∧
            (x₀ ∈ W → AnalyticReadInChart E' R' b σ x₀ W)) ∧
        AnalyticOfChartwiseAnalytic E σ W
end LocalAnalyticity
end Subspaces
end GroupLieProduct
end Matrices
end YangMills.Construction
end
