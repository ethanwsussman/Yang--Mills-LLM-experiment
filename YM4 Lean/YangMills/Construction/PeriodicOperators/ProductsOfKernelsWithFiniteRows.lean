import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
section Preliminaries
variable {N N' N'' : Type}
def RowFinite (T : KernelMatrix N N') : Prop :=
  ∀ a : N', {b : N | T a b ≠ 0}.Finite
def ApplySummable (T : KernelMatrix N N') (f : N → ℂ) : Prop :=
  ∀ a : N', ApplySummableAt T f a
def CompSummable (T : KernelMatrix N' N'') (S : KernelMatrix N N') : Prop :=
  ∀ (c : N'') (b : N), CompSummableAt T S c b
def unitKernel (N : Type) : KernelMatrix N N :=
  open Classical in fun a b => if a = b then 1 else 0
end Preliminaries
namespace RowFiniteKernels
def ApplyComp : Prop :=
  ∀ (N₁ N₂ : Type) (S : KernelMatrix N₂ N₁), RowFinite S →
    (∀ f : N₂ → ℂ, ApplySummable S f) ∧
    ∀ (N₀ : Type) (T : KernelMatrix N₁ N₀), RowFinite T →
      CompSummable T S ∧ RowFinite (compKernel T S) ∧
      ∀ f : N₂ → ℂ, ApplySummable (compKernel T S) f ∧
        ApplySummable T (applyKernel S f) ∧
        applyKernel (compKernel T S) f = applyKernel T (applyKernel S f)
def CompAssoc : Prop :=
  ∀ (N₀ N₁ N₂ N₃ : Type) (T : KernelMatrix N₁ N₀) (S : KernelMatrix N₂ N₁)
    (S' : KernelMatrix N₃ N₂), RowFinite T → RowFinite S →
    CompSummable S S' ∧ CompSummable (compKernel T S) S' ∧
      CompSummable T (compKernel S S') ∧
      compKernel (compKernel T S) S' = compKernel T (compKernel S S')
def UnitLaws : Prop :=
  ∀ N₁ : Type, RowFinite (unitKernel N₁) ∧
    (∀ (N₀ : Type) (T : KernelMatrix N₁ N₀),
      CompSummable T (unitKernel N₁) ∧ compKernel T (unitKernel N₁) = T) ∧
    ∀ (N₂ : Type) (S : KernelMatrix N₂ N₁),
      CompSummable (unitKernel N₁) S ∧ compKernel (unitKernel N₁) S = S
def TransposeDuality : Prop :=
  ∀ (N₀ N₁ : Type) (T : KernelMatrix N₁ N₀) (w₀ : N₀ → ℝ) (w₁ : N₁ → ℝ), RowFinite T →
    (∀ i, 0 < w₀ i) → (∀ j, 0 < w₁ j) →
    ∀ g : N₀ → ℂ, HasFiniteSupport g → ∀ f : N₁ → ℂ,
      ApplySummable T f ∧ ApplySummable (wTranspose w₁ w₀ T) g ∧
      HasFiniteSupport (applyKernel (wTranspose w₁ w₀ T) g) ∧
      HasFiniteSupport
        (fun j => (w₁ j : ℂ) * (applyKernel (wTranspose w₁ w₀ T) g j * f j)) ∧
      HasFiniteSupport (fun i => (w₀ i : ℂ) * (g i * applyKernel T f i)) ∧
      ∑ᶠ j, (w₁ j : ℂ) * (applyKernel (wTranspose w₁ w₀ T) g j * f j) =
        ∑ᶠ i, (w₀ i : ℂ) * (g i * applyKernel T f i)
def Claim : Prop :=
  ApplyComp ∧ CompAssoc ∧ UnitLaws ∧ TransposeDuality
end RowFiniteKernels
end YangMills.Construction.PeriodicOperators
end
