import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace LeftChartFields
open YangMills.Construction.Matrices
def leftExpMul (X V : ComplexMatrix2) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (Complex.I • X) * V
def scalarCoords : ℂ ≃ Coordinates.ComplexCoordinates 1 := (Equiv.funUnique (Fin 1) ℂ).symm
def CurveLogDerivative (𝕜 : Type) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 ComplexMatrix2]
    (D : Set 𝕜) (G 𝔥 : Set ComplexMatrix2) : Prop :=
  ∀ W : 𝕜 → ComplexMatrix2, MapsTo W D G → DifferentiableAt 𝕜 W 0 →
    (∀ᶠ t in 𝓝 (0 : 𝕜), ComplexMatrix2.operatorNorm (W t * (W 0)⁻¹ - 1) < 1) ∧
    DifferentiableAt 𝕜 (fun t => ComplexMatrix2.logSeries (W t * (W 0)⁻¹)) 0 ∧
    Complex.I⁻¹ • deriv (fun t => ComplexMatrix2.logSeries (W t * (W 0)⁻¹)) 0 =
      Complex.I⁻¹ • (deriv W 0 * (W 0)⁻¹) ∧
    Complex.I⁻¹ • (deriv W 0 * (W 0)⁻¹) ∈ 𝔥
structure LatticeData where
  Link : Type
  PosLink : Type
  incl : PosLink → Link
  fields : Set ComplexMatrix2 → Set (Link → ComplexMatrix2)
  forms : Submodule ℝ (Link → ComplexMatrix2)
  cforms : Submodule ℂ (Link → ComplexMatrix2)
  IsCurve : Set ℝ → (ℝ → Link → ComplexMatrix2) → Prop
namespace LatticeData
variable (Λ : LatticeData)
def onPositive {Λ : LatticeData} (B : Λ.Link → ComplexMatrix2) : Λ.PosLink → ComplexMatrix2 :=
  fun b => B (Λ.incl b)
def LeftExpMulMemGroup : Prop :=
  (∀ U ∈ Λ.fields PeriodicLattice.compactGaugeGroup, ∀ B ∈ Λ.forms, ∀ b : Λ.PosLink,
    (∀ t : ℝ, leftExpMul ((t : ℂ) • onPositive B b) (onPositive U b) ∈
      PeriodicLattice.compactGaugeGroup) ∧
    HasDerivAt (fun t : ℝ => leftExpMul ((t : ℂ) • onPositive B b) (onPositive U b))
      (Complex.I • onPositive B b * onPositive U b) 0) ∧
  ∀ U ∈ Λ.fields PeriodicLattice.complexGaugeGroup, ∀ B ∈ Λ.cforms, ∀ b : Λ.PosLink,
    (∀ t : ℂ, leftExpMul (t • onPositive B b) (onPositive U b) ∈
      PeriodicLattice.complexGaugeGroup) ∧
    HasDerivAt (fun t : ℂ => leftExpMul (t • onPositive B b) (onPositive U b))
      (Complex.I • onPositive B b * onPositive U b) 0
def IsCurveTangent (U : Λ.Link → ComplexMatrix2) (Y : Λ.PosLink → ComplexMatrix2) : Prop :=
  ∃ (J : Set ℝ) (γ : ℝ → Λ.Link → ComplexMatrix2), Λ.IsCurve J γ ∧ γ 0 = U ∧
    ∀ b : Λ.PosLink, deriv (fun t => γ t (Λ.incl b)) 0 = Y b
def CurveTangentsEqForms : Prop :=
  ∀ U ∈ Λ.fields PeriodicLattice.compactGaugeGroup,
    (∀ Y : Λ.PosLink → ComplexMatrix2, Λ.IsCurveTangent U Y ↔
      ∃ B ∈ Λ.forms, ∀ b, Y b = Complex.I • onPositive B b * onPositive U b) ∧
    ∀ B ∈ Λ.forms, ∀ B' ∈ Λ.forms,
      (∀ b, Complex.I • onPositive B b * onPositive U b =
        Complex.I • onPositive B' b * onPositive U b) → B = B'
def leftPoint {Λ : LatticeData} {r : ℕ} (bs : Fin r → Λ.PosLink)
    (U X : Λ.Link → ComplexMatrix2) : Fin r → ComplexMatrix2 :=
  fun i => leftExpMul (onPositive X (bs i)) (onPositive U (bs i))
def leftDeriv (𝕜 : Type) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {Λ : LatticeData}
    {r : ℕ} (bs : Fin r → Λ.PosLink) (f : (Fin r → ComplexMatrix2) → ℂ)
    (U B : Λ.Link → ComplexMatrix2) : ℂ :=
  directionalDeriv 𝕜 (fun X => f (leftPoint bs U X)) B
def IsGradient (𝕜 : Type) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    [Module 𝕜 ComplexMatrix2] {Λ : LatticeData} (F : Submodule 𝕜 (Λ.Link → ComplexMatrix2))
    {r : ℕ} (bs : Fin r → Λ.PosLink) (f : (Fin r → ComplexMatrix2) → ℂ)
    (U : Λ.Link → ComplexMatrix2) (X : Λ.PosLink → ComplexMatrix2) : Prop :=
  (∀ b, X b ∈ ComplexMatrix2.traceless) ∧ ∀ B ∈ F, HasFiniteSupp (onPositive B) →
    traceFinsumPairing X (onPositive B) = leftDeriv 𝕜 bs f U B
def LeftDerivEqPair (𝕜 : Type) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    [Module 𝕜 ComplexMatrix2] {Λ : LatticeData} (F : Submodule 𝕜 (Λ.Link → ComplexMatrix2))
    {r : ℕ} (bs : Fin r → Λ.PosLink) (O : Set (Fin r → ComplexMatrix2))
    (f : (Fin r → ComplexMatrix2) → ℂ) (U : Λ.Link → ComplexMatrix2) : Prop :=
  (∀ B ∈ F, ∀ᶠ t in 𝓝 (0 : 𝕜), leftPoint bs U (algebraMap 𝕜 ℂ t • B) ∈ O) ∧
  (∀ B ∈ F, DifferentiableAt 𝕜 (fun t : 𝕜 => f (leftPoint bs U (algebraMap 𝕜 ℂ t • B))) 0) ∧
  (∃ φ : F →ₗ[𝕜] ℂ, ∀ B : F, φ B = leftDeriv 𝕜 bs f U B) ∧
  (∀ B ∈ F, ∀ B' ∈ F, (∀ i, onPositive B (bs i) = onPositive B' (bs i)) →
    leftDeriv 𝕜 bs f U B = leftDeriv 𝕜 bs f U B') ∧
  (∃! X : Λ.PosLink → ComplexMatrix2, IsGradient 𝕜 F bs f U X) ∧
  ∀ X : Λ.PosLink → ComplexMatrix2, IsGradient 𝕜 F bs f U X →
    (∀ b, b ∉ range bs → X b = 0) ∧
    ∀ B ∈ F, traceFinsumPairing X (onPositive B) = leftDeriv 𝕜 bs f U B
def RealGradientExists : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ (bs : Fin r → Λ.PosLink) (O : Set (Fin r → ComplexMatrix2))
    (f : (Fin r → ComplexMatrix2) → ℂ) (U : Λ.Link → ComplexMatrix2),
    specialUnitaryPower.IsOpenSubset O →
    EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower (Fin r)) O f →
    U ∈ Λ.fields PeriodicLattice.compactGaugeGroup → (fun i => onPositive U (bs i)) ∈ O →
    LeftDerivEqPair ℝ Λ.forms bs O f U ∧
    ((∀ p ∈ O, (f p).im = 0) → ∀ X, IsGradient ℝ Λ.forms bs f U X →
      ∀ b, X b ∈ ComplexMatrix2.hermitianTraceless)
def HolomorphicGradientExists : Prop :=
  ∀ (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (r : ℕ), 1 ≤ r →
    ∀ (bs : Fin r → Λ.PosLink) (O : Set (Fin r → ComplexMatrix2))
      (f : (Fin r → ComplexMatrix2) → ℂ) (U : Λ.Link → ComplexMatrix2),
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct.unimodularPi (Fin r)) O →
    GroupLieProduct.IsHolomorphicToCoords β scalarCoords
      (GroupLieProduct.asGroupFactors '' O) (fun p => f fun i => p (.inl i)) →
    U ∈ Λ.fields PeriodicLattice.complexGaugeGroup → (fun i => onPositive U (bs i)) ∈ O →
    LeftDerivEqPair ℂ Λ.cforms bs O f U
def Conditions : Prop :=
  Λ.LeftExpMulMemGroup ∧ Λ.CurveTangentsEqForms ∧
    Λ.RealGradientExists ∧ Λ.HolomorphicGradientExists
end LatticeData
def finiteData (L n k j : ℕ) : LatticeData where
  Link := Edge L n k j
  PosLink := PositiveEdge L n k j
  incl := fun b => b
  fields := fieldsIn L n k j
  forms := edgeFormSpace L n k j
  cforms := complexEdgeForms L n k j
  IsCurve := IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup
def fullData (L k j : ℕ) : LatticeData where
  Link := FullSpace.Edge L k j
  PosLink := FullSpace.PositiveEdge (meshAt L k j)
  incl := fun b => b
  fields := FullSpace.fieldsValuedIn L k j
  forms := FullSpace.edgeFormSpace (meshAt L k j)
  cforms := FullSpace.complexEdgeForms (meshAt L k j)
  IsCurve := FullSpace.IsDifferentiableFieldCurve PeriodicLattice.compactGaugeGroup
def FiniteTangentSpaceEq (L n k j : ℕ) : Prop :=
  Finite (PositiveEdge L n k j) ∧
  BijOn restrictToPositiveEdges (fieldSpace L n k j) (specialUnitaryPower (PositiveEdge L n k j)) ∧
  ∀ _ : Fintype (PositiveEdge L n k j), ∀ U ∈ fieldSpace L n k j,
    (tangentAt U : Set (PositiveEdge L n k j → ComplexMatrix2)) =
      {Y | (finiteData L n k j).IsCurveTangent U Y} ∧
    ∃ T : edgeFormSpace L n k j →ₗ[ℝ] tangentAt U, Function.Bijective T ∧
      ∀ B : edgeFormSpace L n k j,
        (T B : PositiveEdge L n k j → ComplexMatrix2) = leftChartTangent U B
def HasUniqueTranspose (S S' : PairedFunctionSpace) : Prop :=
  ∀ T : S.complexSubmodule →ₗ[ℂ] S'.complexSubmodule,
    PairedFunctionSpace.PreservesFiniteSupport T →
    ∃ T' : S'.complexSubmodule →ₗ[ℂ] S.complexSubmodule,
      PairedFunctionSpace.IsTransposeMap T T' ∧
      ∀ R : S'.complexSubmodule → S.complexSubmodule,
        (∀ (g : S'.complexSubmodule) (f : S.complexSubmodule), S.IsFinitelySupported f →
          S.pair (R g) f = S'.pair g (T f)) → R = T'
inductive FiniteCarrier (L n k : ℕ) : Type
  | vertices (j : ℕ) (hj : j ≤ k) (S : Set (Vertex L n k j))
  | edges (j : ℕ) (hj : j ≤ k) (S : Set (PositiveEdge L n k j))
  | faces (j : ℕ) (hj : j ≤ k) (S : Set (Face L n k j))
def FiniteCarrier.carrier {L n k : ℕ} : FiniteCarrier L n k → Type
  | .vertices _ _ S => S
  | .edges _ _ S => S
  | .faces _ _ S => S
inductive FullCarrier (L k : ℕ) : Type
  | vertices (j : ℕ) (hj : j ≤ k) (S : Set (FullSpace.Vertex L k j))
  | edges (j : ℕ) (hj : j ≤ k) (S : Set (FullSpace.PositiveEdge (meshAt L k j)))
  | faces (j : ℕ) (hj : j ≤ k) (S : Set (FullSpace.Face L k j))
def FullCarrier.carrier {L k : ℕ} : FullCarrier L k → Type
  | .vertices _ _ S => S
  | .edges _ _ S => S
  | .faces _ _ S => S
def Claim : Prop :=
  (∀ I : Set ℝ, IsOpenIntervalAroundZero I →
    CurveLogDerivative ℝ I PeriodicLattice.compactGaugeGroup PeriodicLattice.compactLieAlgebra ∧
    CurveLogDerivative ℝ I PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra) ∧
  (∀ ρ : ℝ, 0 < ρ →
    CurveLogDerivative ℂ (Metric.ball 0 ρ) PeriodicLattice.complexGaugeGroup
      PeriodicLattice.complexLieAlgebra) ∧
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → j ≤ k →
    (∀ n : ℕ, 0 < n →
      (finiteData L n k j).Conditions ∧ FiniteTangentSpaceEq L n k j ∧
      ∀ c c' : FiniteCarrier L n k,
        HasUniqueTranspose (pairedFunctions c.carrier) (pairedFunctions c'.carrier) ∧
        ∀ T : (pairedFunctions c.carrier).complexSubmodule →ₗ[ℂ]
            (pairedFunctions c'.carrier).complexSubmodule,
          PairedFunctionSpace.PreservesFiniteSupport T) ∧
    (fullData L k j).Conditions ∧
    ∀ c c' : FullCarrier L k,
      HasUniqueTranspose (pairedFunctions c.carrier) (pairedFunctions c'.carrier)
end LeftChartFields
end Tower
end YangMills.Construction
end
