import YangMills.Construction.Matrices.HilbertSchmidtOperatorsTraceClassAndTraceOnG
import YangMills.Construction.TransferOperators.KernelBetweenSquareRootsOfTheBondKernel
import YangMills.Construction.TransferOperators.TransferOperatorOfACubicTorus
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics YangMills.Construction.InfiniteLattice YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.TransferOperators
section
variable {B B' : Type} [Finite B] [Finite B']
def linkRelabel (f : B → B') (φ : HaarL2 B) : HaarL2 B' :=
  toHaarL2 fun v => (φ : (B → ComplexMatrix2.specialUnitary) → ℂ) (v ∘ f)
def linkRelabelOp (f : B → B') (X : HaarL2 B →L[ℂ] HaarL2 B) :
    HaarL2 B' →L[ℂ] HaarL2 B' :=
  Classical.epsilon fun A =>
    ∀ ψ, A ψ = linkRelabel f (X (Function.invFun (linkRelabel f) ψ))
end
section
variable {B : Type} [Finite B]
def IsPartitionWithRest {n : ℕ} (parts : Fin n → Set B) (R : Set B) : Prop :=
  (∀ i, (parts i).Nonempty) ∧ Pairwise (Function.onFun Disjoint parts) ∧
    (∀ i, Disjoint (parts i) R) ∧ (⋃ i, parts i) ∪ R = Set.univ
def tensorOneProduct {n : ℕ} (parts : Fin n → Set B)
    (Xs : ∀ i, HaarL2 ↥(parts i) →L[ℂ] HaarL2 ↥(parts i)) :
    HaarL2 B →L[ℂ] HaarL2 B :=
  (List.ofFn fun i => tensorOne (parts i) (Xs i)).prod
end
namespace SandwichConditions
variable (β : ℝ)
def KernelBoundedContinuousSeries {B : Type} [Finite B]
    (X : HaarL2 B →L[ℂ] HaarL2 B) : Prop :=
  (∀ v : B → ComplexMatrix2.specialUnitary, ‖sqrtLinkKernelSlice β v‖ = 1) ∧
    Continuous (fun q : (B → ComplexMatrix2.specialUnitary) × (B → ComplexMatrix2.specialUnitary) =>
      sqrtKernelSandwich β X q.1 q.2) ∧
    (∀ v w : B → ComplexMatrix2.specialUnitary, ‖sqrtKernelSandwich β X v w‖ ≤ ‖X‖) ∧
    (∀ v w : B → ComplexMatrix2.specialUnitary,
      HasSum (fun q : PeterWeylIndex B × PeterWeylIndex B =>
        (sqrtPeterWeylCoeff β q.1 : ℂ) * (sqrtPeterWeylCoeff β q.2 : ℂ) *
          peterWeylEntry X q.1 q.2 * peterWeylFn q.1 v * star (peterWeylFn q.2 w))
        (sqrtKernelSandwich β X v w)) ∧
    Summable fun q : PeterWeylIndex B × PeterWeylIndex B =>
      sqrtPeterWeylCoeff β q.1 * sqrtPeterWeylCoeff β q.2 *
        ‖peterWeylEntry X q.1 q.2‖ * ‖peterWeylFn q.1‖ * ‖peterWeylFn q.2‖
def SandwichTraceClassWithKernel {B : Type} [Finite B]
    (X : HaarL2 B →L[ℂ] HaarL2 B) : Prop :=
  IsTraceClassPW (sqrtLinkOperator β B * X * sqrtLinkOperator β B) ∧
    Schatten.HasKernel (ComplexMatrix2.haarPi B)
      (fun q => sqrtKernelSandwich β X q.1 q.2) (sqrtLinkOperator β B * X * sqrtLinkOperator β B)
def KernelLinearReal (B : Type) [Finite B] : Prop :=
  (∀ (a b : ℂ) (X Y : HaarL2 B →L[ℂ] HaarL2 B) (v w : B → ComplexMatrix2.specialUnitary),
    sqrtKernelSandwich β (a • X + b • Y) v w =
      a * sqrtKernelSandwich β X v w + b * sqrtKernelSandwich β Y v w) ∧
    (∀ v w : B → ComplexMatrix2.specialUnitary, sqrtKernelSandwich β 1 v w = linkProductKernel β v w) ∧
    ∀ X : HaarL2 B →L[ℂ] HaarL2 B, IsRealPreserving X →
      ∀ v w : B → ComplexMatrix2.specialUnitary, (sqrtKernelSandwich β X v w).im = 0
def KernelGaugeInvariant {μ : Fin 4} (B : Block μ)
    (X : HaarL2 (B.links : Set (SliceLink μ)) →L[ℂ]
      HaarL2 (B.links : Set (SliceLink μ))) : Prop :=
  (∀ g : B.vertices → ComplexMatrix2.specialUnitary, Commute X (blockGaugeRep B g)) →
    ∀ (g : B.vertices → ComplexMatrix2.specialUnitary)
      (v w : ↥(B.links : Set (SliceLink μ)) → ComplexMatrix2.specialUnitary),
      sqrtKernelSandwich β X (gaugeAct B.links_subset_linksWithin g v)
        (gaugeAct B.links_subset_linksWithin g w) = sqrtKernelSandwich β X v w
def KernelProductFormula {B : Type} [Finite B] {n : ℕ} (parts : Fin n → Set B) (R : Set B)
    (Xs : ∀ i, HaarL2 ↥(parts i) →L[ℂ] HaarL2 ↥(parts i)) : Prop :=
  ‖tensorOneProduct parts Xs‖ ≤ ∏ i, ‖Xs i‖ ∧
    ∀ v w : B → ComplexMatrix2.specialUnitary,
      sqrtKernelSandwich β (tensorOneProduct parts Xs) v w =
        (∏ i, sqrtKernelSandwich β (Xs i) (restrictTo (parts i) v) (restrictTo (parts i) w)) *
          ∏ᶠ b : ↥R, singleBondWeight β (v b * (w b)⁻¹)
def KernelRelabelEquivariant {B B' : Type} [Finite B] [Finite B'] (f : B → B')
    (X : HaarL2 B →L[ℂ] HaarL2 B) : Prop :=
  Function.Surjective (linkRelabel f) ∧
    (∀ φ ψ : HaarL2 B,
      inner ℂ (linkRelabel f φ) (linkRelabel f ψ) = inner ℂ φ ψ) ∧
    (∀ ψ, linkRelabelOp f X ψ =
      linkRelabel f (X (Function.invFun (linkRelabel f) ψ))) ∧
    ‖linkRelabelOp f X‖ = ‖X‖ ∧
    ∀ v w : B' → ComplexMatrix2.specialUnitary,
      sqrtKernelSandwich β (linkRelabelOp f X) v w = sqrtKernelSandwich β X (v ∘ f) (w ∘ f)
end SandwichConditions
end YangMills.Construction.TransferOperators
end
