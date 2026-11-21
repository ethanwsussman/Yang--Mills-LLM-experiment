import YangMills.Construction.EuclideanFunctionals.OnePlatePrefixedToARaisedElement
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ProductInsertionOp
variable {m : SharpScale} {S : ConnFamily}
def ActsOnReconClasses (σ : EuclidFunctionalWithRecon m S) (η : ℝ)
    (α : RealPlane → ℂ) (φ : RealPlane → ℝ)
    (B : σ.space →L[ℂ] σ.space) : Prop :=
  ∀ A ∈ finCombIn upperHalf, B (reconClass σ A) = reconClass σ (productTimesLifted η α φ A)
def IsInsertionFormOp (σ : EuclidFunctionalWithRecon m S) (η : ℝ)
    (α : RealPlane → ℂ) (φ : RealPlane → ℝ)
    (B : σ.space →L[ℂ] σ.space) : Prop :=
  ∀ F ∈ finCombIn {y | η / 4 < y 3}, ∀ A ∈ finCombIn {y | η / 4 < y 3},
    ⟪reconClass σ (pullDown (η / 4) F), B (reconClass σ (pullDown (η / 4) A))⟫_ℂ =
      insertion S F (productFunction α φ) A
structure LiftedProductMapFacts (η : ℝ) (α : RealPlane → ℂ)
    (φ : RealPlane → ℝ) : Prop where
  maps_to : ∀ A ∈ finCombIn upperHalf,
    productTimesLifted η α φ A ∈ finCombIn upperHalf
  map_add_smul : ∀ A ∈ finCombIn upperHalf, ∀ A' ∈ finCombIn upperHalf,
    ∀ z : ℂ, productTimesLifted η α φ (A + z • A') =
      productTimesLifted η α φ A + z • productTimesLifted η α φ A'
  tensorCompZero_eq : ∀ A ∈ finCombIn upperHalf,
    tensorCompZero (productTimesLifted η α φ A) = 0
  tensorComp_succ : ∀ A ∈ finCombIn upperHalf, ∀ (q : ℕ) (x : TestSpaces.PointTuple (q + 1)),
    tensorComp (q + 1) (productTimesLifted η α φ A) x =
      liftedProduct η α φ (x 0) * tensorComp q (liftedElement η A) fun l => x l.succ
  tensorComp_succ_apply : ∀ A ∈ finCombIn upperHalf, ∀ (q : ℕ)
    (x : TestSpaces.PointTuple (q + 1)),
    tensorComp (q + 1) (productTimesLifted η α φ A) x =
      productFunction α φ (x 0 - (η / 4) • timeVec) *
        tensorComp q A fun l => x l.succ - (η / 2) • timeVec
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon m S) (p : ℝ)
    (C : (RealPlane → ℝ) → ℝ) (c η : ℝ) (α : RealPlane → ℂ) (φ : RealPlane → ℝ),
    ProductBoundHolds σ p C c → IsLiftedProductDatum c η α φ →
    LiftedProductMapFacts η α φ ∧
      ∃ B : σ.space →L[ℂ] σ.space,
        ActsOnReconClasses σ η α φ B ∧
        ‖B‖ ≤ C φ * η ^ (-p) * profileL1Norm α ∧
        (∀ B' : σ.space →L[ℂ] σ.space, ActsOnReconClasses σ η α φ B' → B' = B) ∧
        IsInsertionFormOp σ η α φ B
end YangMills.Construction.EuclideanFunctionals.ProductInsertionOp
