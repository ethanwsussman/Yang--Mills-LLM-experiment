import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import Mathlib
set_option autoImplicit false
open Set Filter Topology Asymptotics
noncomputable section
namespace YangMills.Construction.PeriodicOperators.LocalTorusMatrices
section Kernels
variable (P P' : PeriodicData)
def PeriodSumFiniteOnQuot (K : P'.Carrier → P.Carrier → ℂ) (s : ℕ) : Prop :=
  (∀ x' x, PeriodSumFinite P P' K s x' x) ∧
    ∀ x₁' x₂' x₁ x₂, P'.mkQuot s x₁' = P'.mkQuot s x₂' → P.mkQuot s x₁ = P.mkQuot s x₂ →
      periodization P P' K s x₁' x₁ = periodization P P' K s x₂' x₂
def ActsViaPeriodization (K : P'.Carrier → P.Carrier → ℂ) (s : ℕ) : Prop :=
  ∀ f : P.QuotMod s → ℂ,
    (∀ x', {x | K x' x * liftQuotField P s f x ≠ 0}.Finite) ∧
    (∀ x₁' x₂', P'.mkQuot s x₁' = P'.mkQuot s x₂' →
      applyKernel K (liftQuotField P s f) x₁' = applyKernel K (liftQuotField P s f) x₂') ∧
    ∀ x', applyKernel K (liftQuotField P s f) x' =
      applyKernel (descendMatrix P P' s (periodization P P' K s)) f (P'.mkQuot s x')
end Kernels
section Coefficients
variable (Q P P' : PeriodicData)
def IsExpansionKernel (T : (Q.Carrier → ℂ) → P'.Carrier → P.Carrier → ℂ) (ρ : ℝ) (s : ℕ)
    (u u' : Q.QuotMod s → ℂ) (K : P'.Carrier → P.Carrier → ℂ) : Prop :=
  (IsSupBelow Q (liftQuotField Q s u) ρ ∧ K = T (liftQuotField Q s u)) ∨
    K = coeffZero Q P P' T ∨
    K = coeffOne Q P P' T (liftQuotField Q s u) ∨
    K = coeffTwo Q P P' T (liftQuotField Q s u) (liftQuotField Q s u')
def supModulus (s : ℕ) (u : Q.QuotMod s → ℂ) : ℝ := ⨆ c, ‖u c‖
def PeriodicCoeffsAreTaylor (T : (Q.Carrier → ℂ) → P'.Carrier → P.Carrier → ℂ) (ρ : ℝ)
    (s : ℕ) : Prop :=
  ∀ x' x,
    IsLinearMap ℂ (fun u : Q.QuotMod s → ℂ => periodicCoeffOne Q P P' T s u x' x) ∧
    (∀ u' : Q.QuotMod s → ℂ,
      IsLinearMap ℂ (fun u : Q.QuotMod s → ℂ => periodicCoeffTwo Q P P' T s u u' x' x)) ∧
    (∀ u : Q.QuotMod s → ℂ,
      IsLinearMap ℂ (fun u' : Q.QuotMod s → ℂ => periodicCoeffTwo Q P P' T s u u' x' x)) ∧
    (∀ u u' : Q.QuotMod s → ℂ,
      periodicCoeffTwo Q P P' T s u u' x' x = periodicCoeffTwo Q P P' T s u' u x' x) ∧
    (fun u : Q.QuotMod s → ℂ =>
        periodicValue Q P P' T s u x' x -
          (periodicCoeffZero Q P P' T s x' x + periodicCoeffOne Q P P' T s u x' x +
            (1 / 2 : ℂ) * periodicCoeffTwo Q P P' T s u u x' x))
      =O[𝓝[{u : Q.QuotMod s → ℂ | IsSupBelow Q (liftQuotField Q s u) ρ}] 0]
        fun u => supModulus Q s u ^ 3
end Coefficients
def LocalTorusMatricesClaim : Prop :=
  ∀ Q P P' : PeriodicData, IsPeriodic Q → IsPeriodic P → IsPeriodic P' →
    ∀ (T : (Q.Carrier → ℂ) → P'.Carrier → P.Carrier → ℂ) (ρ R : ℝ), IsLocalWith Q P P' T ρ R →
    ∀ s : ℕ, 0 < s → 4 * R < s →
      (∀ (u u' : Q.QuotMod s → ℂ) (K : P'.Carrier → P.Carrier → ℂ),
        IsExpansionKernel Q P P' T ρ s u u' K →
          PeriodSumFiniteOnQuot P P' K s ∧ ActsViaPeriodization P P' K s) ∧
      PeriodicCoeffsAreTaylor Q P P' T ρ s
end YangMills.Construction.PeriodicOperators.LocalTorusMatrices
end
