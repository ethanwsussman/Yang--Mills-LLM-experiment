import YangMills.Construction.Lattice.BoxAndTreeOfAClassComponent
import YangMills.Construction.Lattice.ObjectsOfTheCentralBox
import YangMills.Construction.Lattice.RegionCutoffs
import YangMills.Construction.Lattice.WeightedWilsonActions
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
open ParameterChoice Matrices
namespace PeriodicLattice.ComponentReferenceLaw
open CentralBlock CubesOfStep
section Forms
variable {L m K k : ℕ}
def logSmallnessIndicator (B : Set (BondAtLevel L m K k)) (ρ : ℝ)
    (U : BondAtLevel L m K k → ComplexMatrix2) : ℝ :=
  open Classical in
  if ∀ e ∈ B, U e ∈ ComplexMatrix2.unitaryLogDomain ∧
      ComplexMatrix2.operatorNorm (Complex.I⁻¹ • ComplexMatrix2.unitaryLog (U e)) < ρ
  then 1 else 0
def extendedField (B : Set (BondAtLevel L m K k)) (U W : BondAtLevel L m K k → ComplexMatrix2) :
    BondAtLevel L m K k → ComplexMatrix2 :=
  open Classical in
  fun e => if e ∈ B then
      (if e.IsPositivelyOriented then U e * W e else (U e.opposite * W e.opposite)⁻¹)
    else W e
def relativeVariable (B : Set (BondAtLevel L m K k)) (V W : BondAtLevel L m K k → ComplexMatrix2) :
    BondAtLevel L m K k → ComplexMatrix2 :=
  open Classical in
  fun e => if e ∈ B then
      (if e.IsPositivelyOriented then V e * (W e)⁻¹ else (V e.opposite * (W e.opposite)⁻¹)⁻¹)
    else 1
def restrictToRegion (X : Set (FourTorus L m)) (W : BondAtLevel L m K k → ComplexMatrix2) :
    BondAtLevel L m K k → ComplexMatrix2 :=
  open Classical in
  fun e => if e ∈ (bondsMeeting X : Set (BondAtLevel L m K k)) then W e else 1
def weightFactor (B : Set (BondAtLevel L m K k)) (ρ β : ℝ) (ζ : FourTorus L m → ℝ)
    (A : (BondAtLevel L m K k → ComplexMatrix2) → BondAtLevel L m K 0 → ComplexMatrix2)
    (W U : BondAtLevel L m K k → ComplexMatrix2) : ℂ :=
  (logSmallnessIndicator B ρ U : ℂ) *
    Complex.exp (-(β : ℂ) * variableCouplingEnergy ζ (A (extendedField B U W)))
def WeightFactorDefined (B : Set (BondAtLevel L m K k)) (ρ : ℝ)
    (Defined : (BondAtLevel L m K k → ComplexMatrix2) → Prop) (W : BondAtLevel L m K k → ComplexMatrix2) :
    Prop :=
  ∀ U, logSmallnessIndicator B ρ U = 1 → Defined (extendedField B U W)
def bondsAsSigma (B : Set (BondAtLevel L m K k)) : Set (Σ q : ℕ, BondAtLevel L m K q) :=
  (fun e => (⟨k, e⟩ : Σ q : ℕ, BondAtLevel L m K q)) '' B
def normalizingIntegral {c : ChoiceUpToDegreeConstants} {m K k : ℕ}
    (B : Set (BondAtLevel c.L m K k)) (T : Set (IndexedBond c.L m)) (ρ β : ℝ)
    (ζ : FourTorus c.L m → ℝ)
    (A : (BondAtLevel c.L m K k → ComplexMatrix2) → BondAtLevel c.L m K 0 → ComplexMatrix2)
    (W : BondAtLevel c.L m K k → ComplexMatrix2) : ℂ :=
  gaugeFixedIntegral (c := c) (bondsAsSigma B) T fun U => weightFactor B ρ β ζ A W (U k)
end Forms
section Component
variable (c : ChoiceUpToRadii) {m K : ℕ} {x : ℕ → ℝ} {k : ℕ}
  (S : LabelAtLevel c.toChoiceUpToDegreeConstants m K x k) (Q : Set (Set (FourTorus c.L m)))
  (X : Set (FourTorus c.L m))
def innerBoxBonds : Set (BondAtLevel c.L m K k) :=
  bondsMeeting (S.innerBoxIn c.r x Q X)
def boxTreeRotated (f : SignedFrame) : Set (IndexedBond c.L m) :=
  liftTree (levelDepth K k) (S.componentAxialTreeRotated f c.r x Q X)
def componentNestTreeRotated (f : SignedFrame) : Set (IndexedBond c.L m) :=
  nestTreeInFrame c.toChoiceUpToDegreeConstants S Q X f
def componentCutoff (K : ℕ) (x : ℕ → ℝ) (k : ℕ) (p : FourTorus c.L m) : ℝ :=
  regionCutoffFn (nestedCubeIndex c.L c.r x K (Nat.log c.L c.M) k) 2 X p
def innerBoxRadius (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  c.M₀ * Thresholds.epsThreshold c.A₀ c.𝔭₀ x k
def innerBoxIndicator (U : BondAtLevel c.L m K k → ComplexMatrix2) : ℝ :=
  logSmallnessIndicator (innerBoxBonds c S Q X) (innerBoxRadius c x k) U
def lawBackground (W : BondAtLevel c.L m K k → ComplexMatrix2) : BondAtLevel c.L m K 0 → ComplexMatrix2 :=
  componentBackground c.εv (Nat.log c.L c.M₁) X W
def componentFactor (W U : BondAtLevel c.L m K k → ComplexMatrix2) : ℂ :=
  weightFactor (innerBoxBonds c S Q X) (innerBoxRadius c x k) (x k) (componentCutoff c X K x k)
    (lawBackground c X) (restrictToRegion X W) U
def ComponentFactorDefined (W : BondAtLevel c.L m K k → ComplexMatrix2) : Prop :=
  WeightFactorDefined (innerBoxBonds c S Q X) (innerBoxRadius c x k)
    (HasComponentBackground c.εv (Nat.log c.L c.M₁) X) (restrictToRegion X W)
def componentNormalizer (f : SignedFrame) (W : BondAtLevel c.L m K k → ComplexMatrix2) : ℂ :=
  normalizingIntegral (c := c.toChoiceUpToDegreeConstants) (innerBoxBonds c S Q X)
    (boxTreeRotated c S Q X f) (innerBoxRadius c x k) (x k) (componentCutoff c X K x k)
    (lawBackground c X) (restrictToRegion X W)
end Component
end PeriodicLattice.ComponentReferenceLaw
end YangMills.Construction
