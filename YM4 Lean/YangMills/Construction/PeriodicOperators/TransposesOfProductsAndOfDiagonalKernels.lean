import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
inductive KernelDomain : Type 1 where
  | lattice (I : PeriodicData) (hI : IsPeriodic I) : KernelDomain
  | quot (I : PeriodicData) (hI : IsPeriodic I) (s : ℕ) (hs : 0 < s) : KernelDomain
namespace KernelDomain
def Elem : KernelDomain → Type
  | lattice I _ => I.Carrier
  | quot I _ s _ => I.QuotMod s
def weight : (D : KernelDomain) → D.Elem → ℝ
  | lattice I _ => I.weightOf
  | quot I _ s _ => I.quotWeight s
end KernelDomain
def TransposeCompDiag : Prop :=
  (∀ (D E F : KernelDomain) (K : E.Elem → D.Elem → ℂ)
      (L : D.Elem → F.Elem → ℂ),
    (∀ y z, {x | K y x * L x z ≠ 0}.Finite) →
      (∀ z y, {x | wTranspose F.weight D.weight L z x *
          wTranspose D.weight E.weight K x y ≠ 0}.Finite) ∧
      wTranspose F.weight E.weight (compKernel K L) =
        compKernel (wTranspose F.weight D.weight L) (wTranspose D.weight E.weight K)) ∧
  (∀ (D : KernelDomain) (K : D.Elem → D.Elem → ℂ),
    (∀ x, wTranspose D.weight D.weight K x x = K x x) ∧
    ((∀ y x, y ≠ x → K y x = 0) → wTranspose D.weight D.weight K = K) ∧
    (∀ [Fintype D.Elem], ∑ x, wTranspose D.weight D.weight K x x = ∑ x, K x x))
end YangMills.Construction.PeriodicOperators
end
