import YangMills.Construction.Lattice.OperationsOfTheTwoClasses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set MeasureTheory ParameterChoice
namespace PeriodicLattice.LargeFieldExpansion
open CentralBlock LargeFieldCompletion ComponentReferenceLaw CubesOfStep ClassOperations TermForms
inductive ConnectionType
  | literal
  | viaCubes
section Components
variable {L m : ℕ} (K : ℕ) (i : ℤ)
def termSupport (C D : Set (Set (FourTorus L m))) : Set (FourTorus L m) :=
  ⋃₀ D ∪ ⋃₀ C
def componentsOutsideSecond (𝒴 C D : Set (Set (FourTorus L m))) : Set (Set (FourTorus L m)) :=
  regionComponents i (regionDiff i (termSupport C D) (⋃₀ 𝒴))
def Linked (evalOnSigma : ConnectionType) (D : Set (Set (FourTorus L m)))
    (A B : Set (FourTorus L m)) : Prop :=
  match evalOnSigma with
  | .literal => ∃ Y ∈ D, A ⊆ Y ∧ B ⊆ Y
  | .viaCubes => ∃ Y ∈ D, SharesCube K A Y ∧ SharesCube K B Y
def linkClass (evalOnSigma : ConnectionType) (𝒴 C D : Set (Set (FourTorus L m)))
    (A : Set (FourTorus L m)) : Set (Set (FourTorus L m)) :=
  {B | Relation.EqvGen (fun A₁ A₂ => A₁ ∈ componentsOutsideSecond i 𝒴 C D ∧
      A₂ ∈ componentsOutsideSecond i 𝒴 C D ∧ Linked K evalOnSigma D A₁ A₂) A B}
def classRegion (C D 𝒜 : Set (Set (FourTorus L m))) : Set (FourTorus L m) :=
  ⋃₀ 𝒜 ∪ ⋃₀ {W | (W ∈ C ∨ W ∈ D) ∧ ∃ A ∈ 𝒜, SharesCube K W A}
def polymerDecomposition (evalOnSigma : ConnectionType) (𝒴 C D : Set (Set (FourTorus L m))) :
    Set (Set (FourTorus L m)) :=
  (fun A => classRegion K C D (linkClass K i evalOnSigma 𝒴 C D A)) ''
    componentsOutsideSecond i 𝒴 C D
end Components
section Bracket
variable {N : AnalyticityConstants} {a : FullChoice} {m K : ℕ} {x : ℕ → ℝ} {E : ℕ → Type}
  {k : ℕ}
section Term
variable (t : ClassedTerm N a m K x E k)
def termCubeIndex (_ : ClassedTerm N a m K x E k) : ℤ :=
  coarseCubeIndex K (Nat.log a.L (degreeChoice a).M) k
def expDomains : Set (Set (FourTorus a.L m)) :=
  nonComponentRegions (radiiChoice a) (Nat.log a.L (degreeChoice a).M) K k t.remainingComponents
def domainTerm (VΛ : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) (Y : Set (FourTorus a.L m))
    (R : FluctuationFieldPair a.L m K) : ℂ :=
  resummedPieceAt (stepConstants N (degreeChoice a)) t.completionData Y
    (completedBackgroundField (radiiChoice a) t.stepLabel t.remainingComponents R.2
      (relativeVariable t.innerBoxBondSet (R.2 k) VΛ) VΛ)
    (fluctuationVariables (radiiChoice a) t.stepLabel t.remainingComponents R.1)
    (R.2 (outerShellLevel (degreeChoice a) x k))
def mayerIntegrand (VΛ : BondAtLevel a.L m K k → Matrices.ComplexMatrix2)
    (D : Finset (Set (FourTorus a.L m))) (τ : ↥D → ℝ) (R : FluctuationFieldPair a.L m K) : ℂ :=
  (∏ Y : ↥D, domainTerm t VΛ Y.1 R) *
    Complex.exp (∑ Y : ↥D, (τ Y : ℂ) * domainTerm t VΛ Y.1 R)
def termFrames (r : Set (FourTorus a.L m) → SignedFrame) (ρ : ↥t.firstClass → SignedFrame) :
    ↥t.remainingComponents → SignedFrame :=
  open Classical in
  fun Y => if h : Y.1 ∈ t.firstClass then ρ ⟨Y.1, h⟩ else r Y.1
def termPair (α : ℝ) (r : Set (FourTorus a.L m) → SignedFrame) (ρ : ↥t.firstClass → SignedFrame)
    (R : FluctuationFieldPair a.L m K) :
    (BondAtLevel a.L m K k → Matrices.ComplexMatrix2) × (BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2) :=
  t.framePair α (termFrames t r ρ) (R.2 k)
end Term
section Activities
variable (𝒯 : Set (ClassedTerm N a m K x E k)) (t₀ : ClassedTerm N a m K x E k)
def bracketTerms : Set (ClassedTerm N a m K x E k) :=
  {t | t ∈ 𝒯 ∧ t.exteriorData = t₀.exteriorData ∧ t.secondClass = t₀.secondClass ∧
    ∀ Y ∈ t₀.secondClass, t.localizedSequence Y = t₀.localizedSequence Y}
variable (form : DisplayForm) (α : ℝ) (r : Set (FourTorus a.L m) → SignedFrame)
def stepDomains (t : ClassedTerm N a m K x E k) : Set (Set (FourTorus a.L m)) :=
  connectedRegions a.L m (termCubeIndex t)
def boundaryRegion : Set (FourTorus a.L m) :=
  addCubeLayer (termCubeIndex t₀) t₀.exteriorData.1 ∪
    ⋃ Y ∈ t₀.secondClass, addCubeLayer (termCubeIndex t₀) Y
def interiorDomains : Set (Set (FourTorus a.L m)) :=
  {X | X ∈ stepDomains t₀ ∧ ¬SharesCube K X (boundaryRegion t₀)}
end Activities
section SecondClass
variable (t : ClassedTerm N a m K x E k)
def componentField (Y : Set (FourTorus a.L m)) (V' VΛ V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel a.L m K k → Matrices.ComplexMatrix2 :=
  open Classical in
  fun e => if e ∈ innerBoxBonds (radiiChoice a) t.stepLabel t.remainingComponents Y then
      extendedField (innerBoxBonds (radiiChoice a) t.stepLabel t.remainingComponents Y) V' VΛ e
    else V e
end SecondClass
section Output
variable (t₀ : ClassedTerm N a m K x E k)
def extendedFrames (ρ : ↥t₀.remainingComponents → SignedFrame) (Y : Set (FourTorus a.L m)) :
    SignedFrame :=
  open Classical in
  if h : Y ∈ t₀.remainingComponents then ρ ⟨Y, h⟩ else 1
variable (𝒯 : Set (ClassedTerm N a m K x E k)) (form : DisplayForm) (α : ℝ)
  (evalOnSigma : ConnectionType)
end Output
end Bracket
end PeriodicLattice.LargeFieldExpansion
end YangMills.Construction
