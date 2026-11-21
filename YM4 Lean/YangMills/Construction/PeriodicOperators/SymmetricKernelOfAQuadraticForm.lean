import YangMills.Construction.Towers.PeriodicExtensionsLocalKernelsAndKernelsThatDescend
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
section Basics
variable {N : Type}
def finsuppFunctions (N : Type) : Submodule ℂ (N → ℂ) where
  carrier := {f | (Function.support f).Finite}
  add_mem' := fun hf hg => (hf.union hg).subset (Function.support_add _ _)
  zero_mem' := by simp
  smul_mem' := fun c _ hf => hf.subset (Function.support_const_smul_subset c _)
def basisFunction (ι : N) : finsuppFunctions N :=
  open Classical in
  ⟨fun ι' => if ι' = ι then 1 else 0, (finite_singleton ι).subset fun ι' h => by
    by_contra h'
    exact h (if_neg h')⟩
def kernelPairing (w : N → ℝ) (X : KernelMatrix N N) (g f : N → ℂ) : ℂ :=
  ∑ᶠ q : N × N, (w q.1 : ℂ) * g q.1 * X q.1 q.2 * f q.2
def IsSymmKernel (w : N → ℝ) (X : KernelMatrix N N) : Prop := wTranspose w w X = X
def bilinKernel (w : N → ℝ)
    (β : finsuppFunctions N →ₗ[ℂ] finsuppFunctions N →ₗ[ℂ] ℂ) :
    KernelMatrix N N :=
  fun ι' ι => (((w ι')⁻¹ : ℝ) : ℂ) * β (basisFunction ι') (basisFunction ι)
end Basics
namespace SymmetricKernels
def BilinFormKernel {N : Type} (w : N → ℝ)
    (β : finsuppFunctions N →ₗ[ℂ] finsuppFunctions N →ₗ[ℂ] ℂ) : Prop :=
  (∃! Y : KernelMatrix N N, ∀ f g : finsuppFunctions N,
    kernelPairing w Y g f = β g f) ∧
  (∀ f g : finsuppFunctions N, kernelPairing w (bilinKernel w β) g f = β g f) ∧
  (∀ f g : finsuppFunctions N,
    kernelPairing w (wTranspose w w (bilinKernel w β)) g f = β f g) ∧
  (IsSymmKernel w (bilinKernel w β) ↔
    ∀ f g : finsuppFunctions N, β g f = β f g)
def QuadFormKernel {N : Type} (w : N → ℝ)
    (β : finsuppFunctions N →ₗ[ℂ] finsuppFunctions N →ₗ[ℂ] ℂ) : Prop :=
  (∃! X : KernelMatrix N N, IsSymmKernel w X ∧
    ∀ f : finsuppFunctions N, kernelPairing w X f f = β f f) ∧
  (IsSymmKernel w ((1 / 2 : ℂ) • (bilinKernel w β +
      wTranspose w w (bilinKernel w β))) ∧
    ∀ f : finsuppFunctions N,
      kernelPairing w ((1 / 2 : ℂ) • (bilinKernel w β +
        wTranspose w w (bilinKernel w β))) f f = β f f) ∧
  ((∀ f g : finsuppFunctions N, β g f = β f g) →
    (1 / 2 : ℂ) • (bilinKernel w β + wTranspose w w (bilinKernel w β)) =
      bilinKernel w β)
def HasPauliCoordinates (σ : Type) (a : ℝ) : Prop :=
  ∀ f g : σ → Matrices.ComplexMatrix2, f ∈ Matrices.GroupLieProduct.tracelessFunctions σ →
    g ∈ Matrices.GroupLieProduct.tracelessFunctions σ →
    Tower.HasFiniteSupp f → Tower.HasFiniteSupp g →
    Tower.toPauliCoeffs f ∈ finsuppFunctions (Fin 3 × σ) ∧
    (∀ w : ℝ, 0 < w → (w : ℂ) * Tower.traceFinsumPairing f g =
      wPairing (fun _ : Fin 3 × σ => w) (Tower.toPauliCoeffs f)
        (Tower.toPauliCoeffs g)) ∧
    Tower.traceFinsumPairing f g =
      wPairing (fun _ : Fin 3 × σ => (1 : ℝ)) (Tower.toPauliCoeffs f)
        (Tower.toPauliCoeffs g) ∧
    Tower.meshPairing a f g =
      wPairing (fun _ : Fin 3 × σ => a ^ 4) (Tower.toPauliCoeffs f)
        (Tower.toPauliCoeffs g)
def Claim : Prop :=
  (∀ (N : Type) (w : N → ℝ), (∀ ι, 0 < w ι) →
    ∀ β : finsuppFunctions N →ₗ[ℂ] finsuppFunctions N →ₗ[ℂ] ℂ,
      BilinFormKernel w β ∧ QuadFormKernel w β) ∧
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    ∀ c : LocalKernels.CellType,
    HasPauliCoordinates (LocalKernels.Cell L k j c) (Tower.meshAt L k j) ∧
    ∀ m : ℕ, 0 < m →
      HasPauliCoordinates (LocalKernels.QuotientCell L m k j c) (Tower.meshAt L k j)
end SymmetricKernels
end YangMills.Construction.PeriodicOperators
end
