import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace BondMaps
open YangMills.Construction.Matrices
abbrev BondValued (B : Type*) : Type _ := B → ↥ComplexMatrix2.traceless
abbrev BondLinearMap (B C : Type*) : Type _ := BondValued B →ₗ[ℂ] BondValued C
namespace BondLinearMap
variable {B C : Type*} [Fintype B] [Fintype C]
open Classical in
def kernel (K : BondLinearMap B C) (c : C) (b : B) :
    ↥ComplexMatrix2.traceless →ₗ[ℂ] ↥ComplexMatrix2.traceless :=
  LinearMap.proj c ∘ₗ K ∘ₗ LinearMap.single ℂ (fun _ : B => ↥ComplexMatrix2.traceless) b
def kernelNorm (K : BondLinearMap B C) (c : C) (b : B) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (K.kernel c b)‖
end BondLinearMap
end BondMaps
end YangMills.Construction
