import YangMills.Construction.Matrices.RealAnalyticMapsOnSubspacesOfProducts
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct.Subspaces.Swap
variable {S R : Type}
def familyToMatrices (u : R → ComplexMatrix2.specialUnitary) : R → ComplexMatrix2 := fun r => u r
def PowerTopologiesCoincide (R : Type) : Prop :=
  ∀ V ⊆ compactPi R,
    (IsOpen (familyToMatrices ⁻¹' V) ↔ ComplexMatrix2.IsRelativelyOpen (compactPi R) V) ∧
    (ComplexMatrix2.IsRelativelyOpen (compactPi R) V ↔
      IsOpenInSubspaceTimesGroup (hermitianTracelessFunctions Empty)
        {q : R ⊕ Empty → ComplexMatrix2 | groupComponent q ∈ V})
def IsOpenInFactorProduct (E : Submodule ℝ (S → ComplexMatrix2)) (D : Set (R ⊕ S → ComplexMatrix2)) :
    Prop :=
  D ⊆ subspaceTimesGroup E R ∧
    ∀ p ∈ D, ∃ (U : Set (S → ComplexMatrix2)) (V : Set (R → ComplexMatrix2)),
      IsOpenInSubspaceTimesGroup E {q : Empty ⊕ S → ComplexMatrix2 | algebraComponent q ∈ U} ∧
        ComplexMatrix2.IsRelativelyOpen (compactPi R) V ∧ algebraComponent p ∈ U ∧
        groupComponent p ∈ V ∧
        ∀ q ∈ subspaceTimesGroup E R, algebraComponent q ∈ U → groupComponent q ∈ V → q ∈ D
def SubspaceTopologyIsProduct (S R : Type) : Prop :=
  ∀ E : Submodule ℝ (S → ComplexMatrix2), E ≤ hermitianTracelessFunctions S →
    ∀ D : Set (R ⊕ S → ComplexMatrix2), IsOpenInSubspaceTimesGroup E D ↔ IsOpenInFactorProduct E D
def ExpChartViaSwap (S R : Type) : Prop :=
  ∀ (Z₀ : S → ComplexMatrix2) (W₀ : R → ComplexMatrix2), ofParts W₀ Z₀ ∈ GroupLieProduct R S →
    (∀ q : R ⊕ S → ComplexMatrix2, q ∈ tracelessPi (R ⊕ S) ↔
      ∃ A ∈ tracelessPi S, ∃ B ∈ tracelessPi R, q = ofParts B A) ∧
    ∀ A ∈ tracelessPi S, ∀ B ∈ tracelessPi R,
      expChartAt (ofParts W₀ Z₀) (ofParts B A) =
        ofParts (fun ρ => ComplexMatrix2.matExp (B ρ) * W₀ ρ) fun σ => Z₀ σ + A σ
def pairEquiv {k : ℕ} (μ : S ⊕ R ≃ Fin k) :
    (S → ComplexMatrix2) × (R → ComplexMatrix2) ≃ Coordinates.ComplexCoordinates
      (Coordinates.ComplexCoordinates.productDim
        fun _ : Fin k => Coordinates.ComplexCoordinates.Component.matrix) :=
  (Equiv.sumArrowEquivProdArrow S R ComplexMatrix2).symm.trans (matrixPiEquiv μ)
def swapSet (O : Set ((S → ComplexMatrix2) × (R → ComplexMatrix2))) :
    Set (R ⊕ S → ComplexMatrix2) :=
  {q | (algebraComponent q, groupComponent q) ∈ O}
def swapMap {T : Type} (Φ : (S → ComplexMatrix2) × (R → ComplexMatrix2) → T) :
    (R ⊕ S → ComplexMatrix2) → T :=
  fun q => Φ (algebraComponent q, groupComponent q)
def HolomorphicViaSwap (S R : Type) : Prop :=
  ∀ (T : Type) (l k : ℕ) (e : T ≃ Coordinates.ComplexCoordinates l) (μ : S ⊕ R ≃ Fin k)
    (O : Set ((S → ComplexMatrix2) × (R → ComplexMatrix2)))
    (Φ : (S → ComplexMatrix2) × (R → ComplexMatrix2) → T),
    IsOpen O → Coordinates.ComplexCoordinates.IsHolomorphicVia (pairEquiv μ) e O Φ →
    IsOpen (swapSet O) ∧
      ∀ (k' : ℕ) (ν : R ⊕ S ≃ Fin k'),
        Coordinates.ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν) e (swapSet O)
          (swapMap Φ)
def SwapTheory : Prop :=
  ∀ (S R : Type) [Fintype S] [Fintype R],
    PowerTopologiesCoincide R ∧ SubspaceTopologyIsProduct S R ∧
      ExpChartViaSwap S R ∧ HolomorphicViaSwap S R
end YangMills.Construction.Matrices.GroupLieProduct.Subspaces.Swap
