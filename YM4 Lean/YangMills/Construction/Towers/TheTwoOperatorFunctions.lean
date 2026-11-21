import YangMills.Construction.PeriodicOperators.KernelOfAMatrixFunction
import YangMills.Construction.PeriodicOperators.SecondDifferentialsOfLogarithmsOfDeterminants
import YangMills.Construction.Towers.TheJetsOfTheTwoOperatorFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.OperatorFunctions
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs (quotOperator)
variable {L k : ℕ}
def KernelRepresentsWithTranspose (r r' : Tower.PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → Matrices.ComplexMatrix2) → r'.space.index → Matrices.ComplexMatrix2) : Prop :=
  Represents (r.kernel r' m) (r.mapOnCoeffs r' m) ∧
    Represents (swapKernel (r.kernel r' m)) (r.transposeOnCoeffs r' m)
def KernelsDefined (U J : FullSpace.Edge L k 0 → Matrices.ComplexMatrix2)
    (μ : FullSpace.Edge L k k → Matrices.ComplexMatrix2) : Prop :=
  (∃ X, FullSpace.IsHessianKernel U J μ X) ∧
    KernelRepresentsWithTranspose (FullSpace.edgePauliCoordinates L k 0) (FullSpace.edgePauliCoordinates L k k)
      (FullSpace.iterCovariantDeriv L k U k) ∧
    KernelRepresentsWithTranspose (Tower.vertexCoordinate (FullSpace.Vertex L k 0))
      (Tower.vertexCoordinate (FullSpace.Vertex L k k))
      (FullSpace.iterAdjointCubeAverage L k U k) ∧
    KernelRepresentsWithTranspose (Tower.vertexCoordinate (FullSpace.Vertex L k 0))
      (FullSpace.edgePauliCoordinates L k 0) (FullSpace.covDiff U) ∧
    (∀ i' i, CompSummableAt (swapKernel (FullSpace.covDiffKernel L k 0 U))
      (FullSpace.covDiffKernel L k 0 U) i' i) ∧
    Represents
      (compKernel (swapKernel (FullSpace.covDiffKernel L k 0 U))
        (FullSpace.covDiffKernel L k 0 U))
      ((Tower.vertexCoordinate (FullSpace.Vertex L k 0)).mapOnCoeffs
        (Tower.vertexCoordinate (FullSpace.Vertex L k 0))
        fun g => FullSpace.covDiffTranspose L k U (FullSpace.covDiff U g))
def HoldsBelowRadius (L k : ℕ) (hL : 0 < L) (ρ : ℝ) : Prop :=
  ∀ ζ : FullSpace.FullField L k, IsSupBelow (FullSpace.fieldPeriodicData L k hL) (ζ.pauliCoeffs hL) ρ →
    ζ.gaugeField ∈ FullSpace.smallIterateFields L k ∧
    KernelsDefined ζ.gaugeField ζ.2.1 ζ.2.2 ∧
    (ζ.IsCompactValued → (∀ i' i, (FullSpace.vectorOp ζ i' i).im = 0) ∧
      ∀ i' i, (FullSpace.ghostOp ζ i' i).im = 0)
def logDetCombination {n : ℕ} (hL : 0 < L) (ζ : Tower.PeriodicField L n k) : ℝ :=
  -(1 / 2) * Real.log ‖LinearMap.det (quotOperator (FullSpace.fieldPeriodicData L k hL)
      (FullSpace.vectorIndices L k) (FullSpace.vectorOpFn L k hL) (2 * L ^ n) (ζ.onQuotient hL))‖ +
    Real.log ‖LinearMap.det (quotOperator (FullSpace.fieldPeriodicData L k hL)
      (FullSpace.ghostIndices L k) (FullSpace.ghostOpFn L k hL) (2 * L ^ n) (ζ.onQuotient hL))‖
def FunctionalEqLogDetNearZero (L n k : ℕ) (hL : 0 < L) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ (ζ : Tower.PeriodicField L n k) (r : Tower.RealPeriodicField L n k),
    ζ.RealizedBy r →
    IsSupBelow (FullSpace.fieldPeriodicData L k hL) (ζ.pauliCoeffs hL) ε →
      Tower.BackgroundFunctionalWellDefined
        (IdentityExpChart.expForm (r.1 : Tower.Edge L n k 0 → Matrices.ComplexMatrix2)) r.2.1 r.2.2 ∧
      Tower.fieldFunctional r = logDetCombination hL ζ
def OperatorFunctionsTheorem : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∃ ρ : ℝ, 0 < ρ ∧ HoldsBelowRadius L k hL ρ ∧
      IsLocalOpFun (FullSpace.fieldPeriodicData L k hL) (FullSpace.vectorIndices L k)
        (FullSpace.vectorIndices L k) (FullSpace.vectorOpFn L k hL) ∧
      IsLocalOpFun (FullSpace.fieldPeriodicData L k hL) (FullSpace.ghostIndices L k)
        (FullSpace.ghostIndices L k) (FullSpace.ghostOpFn L k hL)) ∧
    (∀ R : ℝ,
      (∃ ρ : ℝ, IsLocalWith (FullSpace.fieldPeriodicData L k hL) (FullSpace.vectorIndices L k)
        (FullSpace.vectorIndices L k) (FullSpace.vectorOpFn L k hL) ρ R) →
      (∃ ρ : ℝ, IsLocalWith (FullSpace.fieldPeriodicData L k hL) (FullSpace.ghostIndices L k)
        (FullSpace.ghostIndices L k) (FullSpace.ghostOpFn L k hL) ρ R) →
      ∀ n : ℕ, 0 < n → 4 * R < ((2 * L ^ n : ℕ) : ℝ) → FunctionalEqLogDetNearZero L n k hL) ∧
    SymbolInvertibleOnReals (FullSpace.vectorIndices L k) (FullSpace.vectorOpFn L k hL 0) ∧
    SymbolInvertibleOnReals (FullSpace.ghostIndices L k) (FullSpace.ghostOpFn L k hL 0)
end YangMills.Construction.Tower.FullSpace.OperatorFunctions
end
