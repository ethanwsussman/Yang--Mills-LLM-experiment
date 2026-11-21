import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConstrainedForms
open LinearMap (adjoint ker range)
variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
def IsNonnegOp (X : Module.End ℝ H) : Prop :=
  X.IsSymmetric ∧ ∀ f : H, 0 ≤ inner ℝ f (X f)
def IsPosDefOp (X : Module.End ℝ H) : Prop :=
  X.IsSymmetric ∧ ∀ f : H, f ≠ 0 → 0 < inner ℝ f (X f)
def IsOrthProj (χ : Module.End ℝ H) : Prop :=
  IsIdempotentElem χ ∧ χ.IsSymmetric
def augmentedOp (X : Module.End ℝ H) (q : H →ₗ[ℝ] K) (m : Module.End ℝ K) : Module.End ℝ H :=
  X + adjoint q ∘ₗ m ∘ₗ q
structure Setting (X : Module.End ℝ H) (q : H →ₗ[ℝ] K) (m : Module.End ℝ K) : Prop where
  nonneg : IsNonnegOp X
  surjective : Function.Surjective q
  weight_nonneg : IsNonnegOp m
  augmented_posDef : IsPosDefOp (augmentedOp X q m)
def augmentedInv (X : Module.End ℝ H) (q : H →ₗ[ℝ] K) (m : Module.End ℝ K) : Module.End ℝ H :=
  Ring.inverse (augmentedOp X q m)
def schurOp (X : Module.End ℝ H) (q : H →ₗ[ℝ] K) (m : Module.End ℝ K) : Module.End ℝ K :=
  q ∘ₗ augmentedInv X q m ∘ₗ adjoint q
def compress (χ ψ A : Module.End ℝ H) : range ψ →ₗ[ℝ] range χ :=
  LinearMap.codRestrict (range χ) (χ ∘ₗ A ∘ₗ ψ ∘ₗ (range ψ).subtype)
    (fun _ => LinearMap.mem_range_self χ _)
end YangMills.Construction.ConstrainedForms
end
