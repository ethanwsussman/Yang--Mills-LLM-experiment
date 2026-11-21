import YangMills.Construction.OneLoopLaw.CoefficientOfAFunctional
import YangMills.Construction.PeriodicOperators.RiemannSumsAndShifts
import Mathlib
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology
noncomputable section
namespace YangMills.Construction.OneLoopLaw.TemperedStiffness
open Tower PeriodicOperators PeriodicOperators.Tempered
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec l1NormVec)
def symbolKernel (g : (Fin 4 → ℂ) → ℂ) (u : Fin 4 → ℤ) : ℂ :=
  torusAverage fun p => g (toComplexVec p) *
    Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec (castVec u)))
def secondPartialAtZero (g : (Fin 4 → ℂ) → ℂ) (μ ν : Fin 4) : ℂ :=
  deriv (fun s : ℝ => deriv (fun t : ℝ =>
    g (toComplexVec (Pi.single μ s + Pi.single ν t))) 0) 0
def FirstVariationVanishes (L : ℕ) (F : FieldFamily L) : Prop :=
  EventuallyForSides L fun n => ∀ B ∈ Tower.edgeFormSpace L n 0 0,
    Tower.leftDeriv (k := 0) (j := 0) (F n) (identityField L n) B = 0
def KernelsTendTo (L : ℕ) (F : FieldFamily L) (π : SymbolArray) : Prop :=
  ∀ (x y : EffectiveAction.IntBond) (a a' : Fin 3),
    Tendsto (fun n => complexHessian F n
        (FunctionalStiffness.liftedPauliForm L n a x) (FunctionalStiffness.liftedPauliForm L n a' y))
      atTop (𝓝 (if a = a' then symbolKernel (π x.2 y.2) (y.1 - x.1) else 0))
def KernelsRealAndDecaying (δ : ℝ) (π : SymbolArray) : Prop :=
  ∀ (μ ν : Fin 4) (u : Fin 4 → ℤ), (symbolKernel (π μ ν) u).im = 0 ∧
    ‖symbolKernel (π μ ν) u‖ ≤
      RiemannSums.stripSup δ (π μ ν) * Real.exp (-δ * l1NormVec (castVec u))
def transverseTensor (b : ℝ) (μ ν : Fin 4) (p : AmbientSpace) : ℝ :=
  b * (euclidNormVec p ^ 2 * (if μ = ν then 1 else 0) - p μ * p ν)
def HasTransverseForm (π : SymbolArray) (b : ℝ) : Prop :=
  ∀ μ ν : Fin 4,
    (fun p : AmbientSpace => Complex.exp (Complex.I * (((p μ - p ν) / 2 : ℝ) : ℂ)) *
        π μ ν (toComplexVec p) - (transverseTensor b μ ν p : ℂ)) =O[𝓝 0]
      fun p => euclidNormVec p ^ 4
structure StiffnessFormulas (π : SymbolArray) (c b : ℝ) (μ ν : Fin 4) : Prop where
  hasSum_mixed : HasSum (fun u : Fin 4 → ℤ => symbolKernel (π μ ν) u * (u μ : ℂ) * (u ν : ℂ)) (c : ℂ)
  neg_secondPartial_mixed : -secondPartialAtZero (π μ ν) μ ν = (c : ℂ)
  eq_coeff : c = b
  half_secondPartial_diag : (1 / 2 : ℂ) * secondPartialAtZero (π ν ν) μ μ = (b : ℂ)
  hasSum_diag : HasSum
    (fun u : Fin 4 → ℤ => -(1 / 2 : ℂ) * (symbolKernel (π ν ν) u * (u μ : ℂ) ^ 2)) (b : ℂ)
def twistedSymbol (π : SymbolArray) (μ ν : Fin 4) (κ : Fin 4 → ℂ) : ℂ :=
  Complex.exp (Complex.I * ((κ μ - κ ν) / 2)) * π μ ν κ
def SatisfiesWardIdentity (δ : ℝ) (π : SymbolArray) : Prop :=
  ∀ κ ∈ imStrip δ, ∀ ν : Fin 4, ∑ μ, (Complex.exp (Complex.I * κ μ) - 1) * π μ ν κ = 0
def PermutationCovariant (δ : ℝ) (π : SymbolArray) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 4)), ∀ κ ∈ imStrip δ, ∀ μ ν : Fin 4,
    twistedSymbol π (σ μ) (σ ν) (κ ∘ σ.symm) = twistedSymbol π μ ν κ
def reflectCoord (ρ : Fin 4) (κ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  Function.update κ ρ (-κ ρ)
def reflectSign (ρ μ : Fin 4) : ℂ := if μ = ρ then -1 else 1
def ReflectionCovariant (δ : ℝ) (π : SymbolArray) : Prop :=
  ∀ (ρ : Fin 4), ∀ κ ∈ imStrip δ, ∀ μ ν : Fin 4,
    twistedSymbol π μ ν (reflectCoord ρ κ) =
      reflectSign ρ μ * reflectSign ρ ν * twistedSymbol π μ ν κ
end YangMills.Construction.OneLoopLaw.TemperedStiffness
end
