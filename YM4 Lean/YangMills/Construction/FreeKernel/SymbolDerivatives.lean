import YangMills.Construction.Constants.HeatKernelGaussianNumbers
import YangMills.Construction.FreeKernel.OneDimensionalLatticeKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeKernel
open YangMills.Construction.Constants.HeatKernel
def HomotopySymbolLowerBound : Prop :=
  ∀ x ∈ Set.Icc (-Real.pi) Real.pi, ∀ s ∈ Set.Icc (0 : ℝ) 1,
    homotopySymbol s x ≥ 4 / Real.pi ^ 2 * x ^ 2
def SymbolVanishingOrders : Prop :=
  (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ,
    |deriv (homotopySymbol s) x| ≤ symmetryConstant * |x| ∧
    (∀ k : ℕ, 2 ≤ k → |iteratedDeriv k (homotopySymbol s) x| ≤ symmetryConstant)) ∧
  (∀ (k : ℕ) (x : ℝ), |iteratedDeriv k symbolError x| ≤ symmetryConstant * |x| ^ (4 - k)) ∧
  (∀ (a : DiffKind) (k : ℕ), ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
    ‖iteratedDeriv k (diffMultiplier a) x‖ ≤ symmetryConstant * |x| ^ (diffOrder a - k) ∧
    ‖iteratedDeriv k (multiplierError a) x‖ ≤ symmetryConstant * |x| ^ (diffOrder a + 1 - k))
def ExpSymbolRange (t s x : ℝ) : Prop :=
  (1 ≤ t ∧ 0 ≤ s ∧ s ≤ 1 ∧ |x| ≤ Real.pi) ∨ (s = 0 ∧ 0 < t)
def ExpSymbolDerivativeBounds : Prop :=
  ∀ (n : ℕ) (t s x : ℝ), ExpSymbolRange t s x →
    |iteratedDeriv n (fun y => Real.exp (-t * homotopySymbol s y)) x| ≤
        factorialPower n * t ^ ((n : ℝ) / 2) * (1 + Real.sqrt t * |x|) ^ n *
          Real.exp (-t * homotopySymbol s x) ∧
      ENNReal.ofReal
          (factorialPower n * t ^ ((n : ℝ) / 2) * (1 + Real.sqrt t * |x|) ^ n *
            Real.exp (-t * homotopySymbol s x)) ≤
        weightedFactorialPower n * ENNReal.ofReal (t ^ ((n : ℝ) / 2) * Real.exp (-(heatDecay * t * x ^ 2)))
def SymbolDerivativeBounds : Prop :=
  1 ≤ symmetryConstant ∧ 0 < heatDecay ∧ HomotopySymbolLowerBound ∧ SymbolVanishingOrders ∧
    ExpSymbolDerivativeBounds
end YangMills.Construction.LatticeKernel
end
