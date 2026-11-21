import YangMills.Construction.FreeKernel.KernelsAndAbbreviationsInFourDimensions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open Complex LatticeKernel
def SymbolRelations : Prop :=
  (∀ θ : ℝ, laplacianSymbol θ = 4 * Real.sin (θ / 2) ^ 2) ∧
  (∀ k : Fin 4 → ℝ,
    PeriodicLattice.ShortDistanceTwoPoint.laplacianSymbol k = ∑ μ, laplacianSymbol (k μ)) ∧
  (∀ θ : ℝ, homotopySymbol 0 θ = θ ^ 2) ∧
  (∀ θ : ℝ, homotopySymbol 1 θ = laplacianSymbol θ) ∧
  (∀ (t : ℝ) (u : Fin 4 → ℝ), 0 < t →
    FourDimKernel.gaussianHeatKernel4 t u =
      (4 * Real.pi * t) ^ (-2 : ℤ) *
        Real.exp (-FourDimKernel.realVecNorm u ^ 2 / (4 * t)))
def FourierIntegralForms : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ (j : ℤ) (ξ : ℝ) (α : DiffKind),
    ((gaussianHeatKernel t ξ : ℝ) : ℂ) =
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * (Real.exp (-t * θ ^ 2) : ℂ) ∧
    diffOp α (discreteHeatKernel t) j =
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ θ in (-Real.pi)..Real.pi,
            Complex.exp (I * (j : ℂ) * (θ : ℂ)) * diffMultiplier α θ *
              (Real.exp (-t * laplacianSymbol θ) : ℂ) ∧
    ((gaussianHeatKernelDeriv (diffOrder α) t ξ : ℝ) : ℂ) =
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * (I * (θ : ℂ)) ^ diffOrder α *
            (Real.exp (-t * θ ^ 2) : ℂ)
def symbolsAndFourierIntegrals : Prop :=
  SymbolRelations ∧ FourierIntegralForms
end YangMills.Construction.FreeKernel
end
