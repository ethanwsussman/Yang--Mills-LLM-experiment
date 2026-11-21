import YangMills.Construction.PeriodicOperators.TemperedFunctionals
import YangMills.Construction.Towers.SignsOfTheResponseOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.CriticalBranchResponse
def CompositeDerivativeEquation (L n k : ℕ) (B : Edge L n k k → Matrices.ComplexMatrix2) : Prop :=
  leftDifferential (chosenProlongComp L n k k) (trivialField L n k k) B -
      (meshScaledResponse L n k B : Edge L n k 0 → Matrices.ComplexMatrix2) ∈
    vertexCoboundary '' (vertexFunctionSpace L n k 0 : Set (Vertex L n k 0 → Matrices.ComplexMatrix2))
structure GradientDerivativeCondition (L n k : ℕ) (B : Edge L n k k → Matrices.ComplexMatrix2) : Prop where
  energy_gradient_eventually : ∀ᶠ t in 𝓝 (0 : ℝ),
    GradientExistsAt (chosenEnergy L n k k) (expLineField L n k B t)
  action_gradient_eventually : ∀ᶠ t in 𝓝 (0 : ℝ),
    GradientExistsAt (plaquetteAction L n k) (chosenProlongComp L n k k (expLineField L n k B t))
  hasDeriv_energy_gradient : IsFormCurveDerivAtZero
    (fun t => (chosenCriticalBranch L n k).energyGradient k (expLineField L n k B t))
    (periodicDefect L n k B)
  hasDeriv_action_gradient : IsFormCurveDerivAtZero
    (fun t => leftGradient (fieldSpace L n k 0) (fun U => (plaquetteAction L n k U : ℂ))
      (chosenProlongComp L n k k (expLineField L n k B t)))
    (formCoboundaryTranspose L n k (formCoboundary L n k (meshScaledResponse L n k B)))
  coboundary_square_eq : formCoboundaryTranspose L n k (formCoboundary L n k (meshScaledResponse L n k B)) =
    crossingSmoothingTranspose L n k (periodicDefect L n k B)
def ProlongDerivativeCondition (L n i : ℕ) (B : Edge L n (i + 1) (i + 1) → Matrices.ComplexMatrix2) : Prop :=
  leftDifferential (chosenProlong L n (i + 1) i) (trivialField L n (i + 1) (i + 1)) B -
      crossingSmoothingIter L n (i + 1) i (meshScaledResponse L n (i + 1) B) ∈
    vertexCoboundary '' (vertexFunctionSpace L n (i + 1) i : Set (Vertex L n (i + 1) i → Matrices.ComplexMatrix2))
def ResponseConditions : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ i : ℕ,
    PeriodicOperators.Tempered.EventuallyForSides L fun n => ∀ B ∈ edgeFormSpace L n (i + 1) (i + 1),
      CompositeDerivativeEquation L n (i + 1) B ∧ GradientDerivativeCondition L n (i + 1) B ∧
        ProlongDerivativeCondition L n i B
end YangMills.Construction.Tower.CriticalBranchResponse
end
