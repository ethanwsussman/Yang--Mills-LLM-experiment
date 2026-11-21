import YangMills.Construction.Lattice.BondLinearMaps
import YangMills.Construction.Lattice.FormsOperatorsAndWeightedNormsOnTheBareLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice Matrices
open scoped Matrix.Norms.L2Operator
namespace Matrices.ComplexMatrix2
def endTranspose (T : ↥traceless →ₗ[ℂ] ↥traceless) : ↥traceless →ₗ[ℂ] ↥traceless :=
  Classical.epsilon fun S : ↥traceless →ₗ[ℂ] ↥traceless => ∀ Y Y' : ↥traceless,
    halfTracePairing (T Y : ComplexMatrix2) (Y' : ComplexMatrix2) =
      halfTracePairing (Y : ComplexMatrix2) (S Y' : ComplexMatrix2)
end Matrices.ComplexMatrix2
namespace SeparatedSequence
namespace DepthChain
variable {L m : ℕ} {N : DepthParameters L m} (A : DepthChain N)
def formSpace : Submodule ℂ (BondAtLevel L m N.K 0 → ComplexMatrix2) where
  carrier := A.bondForms complexLieAlgebra
  add_mem' := by
    rintro a a' ⟨⟨hp, hr⟩, hi⟩ ⟨⟨hp', hr'⟩, hi'⟩
    refine ⟨⟨fun b hb => ComplexMatrix2.traceless.add_mem (hp b hb) (hp' b hb), fun b => ?_⟩, ?_⟩
    · simp only [Pi.add_apply, hr, hr', neg_add]
    · rw [Set.indicator_add', hi, hi']
  zero_mem' := by
    refine ⟨⟨fun b _ => ComplexMatrix2.traceless.zero_mem, fun b => by simp⟩, by simp⟩
  smul_mem' := by
    rintro z a ⟨⟨hp, hr⟩, hi⟩
    refine ⟨⟨fun b hb => ComplexMatrix2.traceless.smul_mem z (hp b hb), fun b => ?_⟩, ?_⟩
    · simp only [Pi.smul_apply, hr, smul_neg]
    · change (bondsInside (A.region 0)).indicator (fun b => z • a b) = z • a
      rw [Set.indicator_const_smul, hi]
      rfl
def formEval (a : ↥A.formSpace) (b : ↥A.orientedBaseBonds) : ↥ComplexMatrix2.traceless :=
  ⟨a.1 b.1, a.2.1.1 b.1 b.2.2⟩
variable {C : Type*}
def plainInner (ω ω' : BondMaps.BondValued C) : ℂ :=
  ∑ᶠ c : C, halfTracePairing (ω c : ComplexMatrix2) (ω' c : ComplexMatrix2)
def formTranspose (K : ↥A.formSpace →ₗ[ℂ] BondMaps.BondValued C) (ω : BondMaps.BondValued C) :
    ↥A.formSpace :=
  Classical.epsilon fun B : ↥A.formSpace => ∀ a : ↥A.formSpace,
    plainInner (K a) ω = A.bondInner a.1 B.1
end DepthChain
end SeparatedSequence
end YangMills.Construction
