import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Matrices.GroupLieProduct
variable {σ ι' κ' T : Type}
def compactPi (σ : Type) : Set (σ → ComplexMatrix2) :=
  ComplexMatrix2.compactProduct fun _ => ComplexMatrix2.FactorKind.group
def tracelessFunctions (σ : Type) : Submodule ℂ (σ → ComplexMatrix2) :=
  Submodule.pi univ fun _ => ComplexMatrix2.traceless
def hermitianTracelessFunctions (σ : Type) : Submodule ℝ (σ → ComplexMatrix2) :=
  Submodule.pi univ fun _ => ComplexMatrix2.hermitianTraceless
theorem coe_tracelessFunctions (σ : Type) :
    (tracelessFunctions σ : Set (σ → ComplexMatrix2)) = tracelessPi σ := by
  ext B
  simp [tracelessFunctions, tracelessPi, ComplexMatrix2.complexifiedProduct,
    ComplexMatrix2.FactorKind.complexified]
def expTimesUnitaryFamily (B V : σ → ComplexMatrix2) : σ → ComplexMatrix2 :=
  fun b => ComplexMatrix2.expTimesUnitary (B b) (V b)
def asGroupFactors (V : σ → ComplexMatrix2) : σ ⊕ Empty → ComplexMatrix2 := Sum.elim V Empty.elim
end Matrices.GroupLieProduct
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def restrictToPositive (B : Set (Bond L m j)) (U : Bond L m j → Matrices.ComplexMatrix2) :
    PositiveBondOf B → Matrices.ComplexMatrix2 :=
  fun b => U b.1
def extendFromPositive (B : Set (Bond L m j)) (v : PositiveBondOf B → Matrices.ComplexMatrix2)
    (b : Bond L m j) : Matrices.ComplexMatrix2 :=
  open Classical in
  if h : b ∈ B ∧ b.IsPositivelyOriented then v ⟨b, h⟩
  else if h' : b.opposite ∈ B ∧ b.opposite.IsPositivelyOriented then (v ⟨b.opposite, h'⟩)⁻¹
  else 1
end PeriodicLattice
end YangMills.Construction
