import YangMills.Construction.Lattice.FibreAndStepFunctionalOfAStep
import YangMills.Construction.Lattice.LinearisedConstraint
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open Matrices
section PairedSpaces
variable {F F' : Type*} [AddCommGroup F] [Module ℝ F] [AddCommGroup F'] [Module ℝ F']
def IsOrthonormalBasisFor (P : F → F → ℝ) (E : Set F) {n : ℕ} (e : Fin n → F) : Prop :=
  (∀ i, e i ∈ E) ∧ (∀ i j, P (e i) (e j) = if i = j then 1 else 0) ∧
    ∀ v ∈ E, ∃ x : Fin n → ℝ, v = ∑ i, x i • e i
def pairedSpaceIntegral (P : F → F → ℝ) (E : Set F) (Ψ : F → ℝ) : ℝ :=
  Classical.epsilon fun I => ∃ (n : ℕ) (e : Fin n → F), IsOrthonormalBasisFor P E e ∧
    I = ∫ x : Fin n → ℝ, Ψ (∑ i, x i • e i)
def gramDeterminantOf (P : F → F → ℝ) (E : Set F) (P' : F' → F' → ℝ) (E' : Set F')
    (Q : F → F') : ℝ :=
  Classical.epsilon fun d => ∃ (n r : ℕ) (e : Fin n → F) (f : Fin r → F'),
    IsOrthonormalBasisFor P E e ∧ IsOrthonormalBasisFor P' E' f ∧
      d = (Matrix.of (fun a i => P' (f a) (Q (e i))) *
        (Matrix.of (fun a i => P' (f a) (Q (e i))) : Matrix (Fin r) (Fin n) ℝ).transpose).det
end PairedSpaces
def realBondFormsOn {L m : ℕ} {j : ℤ} (Y : Set (Bond L m j)) : Set (Bond L m j → ComplexMatrix2) :=
  {B | IsBondForm compactLieAlgebra B ∧ ∀ b : Bond L m j, b.IsPositivelyOriented → b ∉ Y → B b = 0}
def unitBondInner {L m : ℕ} {j : ℤ} (A B : Bond L m j → ComplexMatrix2) : ℝ :=
  (bondFormInner 1 A B).re
namespace CubesOfStep
variable (c : ParameterChoice.ChoiceUpToDegreeConstants) {m K k : ℕ} (D : StepData c.L m K k)
def IsAllSmallField : Prop :=
  (∀ i, 1 ≤ i → i ≤ k → D.domains i = univ) ∧ D.region = univ
def IsBranchCase (N : Set (BondAtLevel c.L m K (k + 1) → ComplexMatrix2)) : Prop :=
  IsAllSmallField c D ∧ D.next ∈ N
def backgroundPoint (N : Set (BondAtLevel c.L m K (k + 1) → ComplexMatrix2))
    (branch : (BondAtLevel c.L m K (k + 1) → ComplexMatrix2) → BondAtLevel c.L m K k → ComplexMatrix2) :
    BondAtLevel c.L m K k → ComplexMatrix2 :=
  open Classical in
  if IsBranchCase c D N then branch D.next else backgroundField c D
def HasBackgroundPoint (N : Set (BondAtLevel c.L m K (k + 1) → ComplexMatrix2)) : Prop :=
  IsBranchCase c D N ∨ HasUniqueBackgroundMinimizer c D
variable (p : BondAtLevel c.L m K k → ComplexMatrix2)
def linearConstraint (B : BondAtLevel c.L m K k → ComplexMatrix2) :
    BondAtLevel c.L m K (k + 1) → ComplexMatrix2 :=
  (positiveRegionBonds c D).indicator
    (linearizedConstraintReal (Averaging.smoothingRadius c.L) p B)
def tangentSpace : Set (BondAtLevel c.L m K k → ComplexMatrix2) :=
  {B | B ∈ realBondFormsOn (touchingBonds c D) ∧ linearConstraint c D p B = 0}
def IsTwiceDiffAtZero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : Prop :=
  (∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f t) ∧ DifferentiableAt ℝ (deriv f) 0
def IsFiberCurve (B : BondAtLevel c.L m K k → ComplexMatrix2)
    (γ : ℝ → BondAtLevel c.L m K k → ComplexMatrix2) : Prop :=
  (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ averagingFiber c D) ∧ γ 0 = p ∧
    (∀ b, IsTwiceDiffAtZero fun t => γ t b) ∧ ∀ b : BondAtLevel c.L m K k, b.IsPositivelyOriented →
      HasDerivAt (fun t => γ t b * (p b)⁻¹) (Complex.I • B b) 0
def HasHessianValue (B : BondAtLevel c.L m K k → ComplexMatrix2) (q : ℝ) : Prop :=
  (∃ γ, IsFiberCurve c D p B γ) ∧ ∀ γ, IsFiberCurve c D p B γ →
    (∀ᶠ t in 𝓝 (0 : ℝ), StepActionDefinedAt c D (γ t)) ∧
      IsTwiceDiffAtZero (fun t => stepAction c D (γ t)) ∧
      iteratedDeriv 2 (fun t => stepAction c D (γ t)) 0 = q
def hessianForm (B : BondAtLevel c.L m K k → ComplexMatrix2) : ℝ :=
  Classical.epsilon (HasHessianValue c D p B)
def HessianFormDefined : Prop :=
  ∀ B ∈ tangentSpace c D p, ∃ q, HasHessianValue c D p B q
def hessianBilin (B₁ B₂ : BondAtLevel c.L m K k → ComplexMatrix2) : ℝ :=
  (1 / 2) * (hessianForm c D p (B₁ + B₂) - hessianForm c D p B₁ -
    hessianForm c D p B₂)
def eliminateAt (B : BondAtLevel c.L m K k → ComplexMatrix2) :
    BondAtLevel c.L m K k → ComplexMatrix2 :=
  eliminate p (positiveRegionBonds c D) B
def realCoarseFunctions : Set (BondAtLevel c.L m K (k + 1) → ComplexMatrix2) :=
  {f | (∀ e ∈ positiveRegionBonds c D, f e ∈ compactLieAlgebra) ∧
    ∀ e ∉ positiveRegionBonds c D, f e = 0}
def coarseFunctionInner (f g : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) : ℝ :=
  (∑ᶠ e ∈ positiveRegionBonds c D, ComplexMatrix2.halfTrace (f e * g e)).re
def IsHessianPosDef : Prop :=
  ∀ B ∈ tangentSpace c D p, B ≠ 0 → 0 < hessianForm c D p B
def gaussianNormalizer : ℝ :=
  gramDeterminantOf unitBondInner (realBondFormsOn (touchingBonds c D))
      (coarseFunctionInner c D) (realCoarseFunctions c D) (linearConstraint c D p) ^ (-(1 / 2) : ℝ) *
    pairedSpaceIntegral unitBondInner (tangentSpace c D p)
      fun B => Real.exp (-(1 / 2) * hessianForm c D p B)
variable (x : ℕ → ℝ)
def couplingScaledElimination (B : BondAtLevel c.L m K k → ComplexMatrix2) :
    SupportBond (levelDepth K k) (positiveRegionBonds c D) → ComplexMatrix2 :=
  fun b => ((Thresholds.couplingAt x k : ℝ) : ℂ) • eliminateAt c D p B b
def linearizedVariable (B : BondAtLevel c.L m K k → ComplexMatrix2) :
    BondAtLevel c.L m K k → ComplexMatrix2 :=
  extendForm (linearizingChange p (positiveRegionBonds c D) (couplingScaledElimination c D p x B))
end CubesOfStep
end PeriodicLattice
end YangMills.Construction
