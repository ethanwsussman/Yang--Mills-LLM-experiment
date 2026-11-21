import YangMills.Construction.Lattice.FaddeevPopovProcedureAndItsReverse
import YangMills.Construction.Lattice.GaugeFixingLawsAndTheProcedure
import YangMills.Construction.Lattice.HowATermIsRead
import YangMills.Construction.Thresholds.DegreeFunctions
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ConfigSpaces
open YangMills.Construction.BorelKernels YangMills.Construction.PeriodicLattice.FaddeevPopov YangMills.Construction.PeriodicLattice.TermEvaluation
universe u
structure IsAxialLawRange (A₀ : ℝ) (𝔭₀ : ℕ) (x : ℕ → ℝ) (j : ℕ) : Prop where
  one_lt : 1 < x j
  pos : 0 < Thresholds.epsThreshold A₀ 𝔭₀ x j
  le_one : Thresholds.epsThreshold A₀ 𝔭₀ x j ≤ 1
structure GaugeMoveData (L m K k : ℕ) (Stored : Type) where
  siteSet : Finset (FourTorus L m)
  moved : BondField L m K k Stored
  bondSet : Finset (GradedBond L m K)
  fixedSpace : Type u
  [measurableFixedSpace : MeasurableSpace fixedSpace]
  blockMap : (bondSet → Matrices.ComplexMatrix2.specialUnitary) × fixedSpace → BlockFields L m K k
  kernel : ∀ (𝒴' : Type u) [MeasurableSpace 𝒴'],
    ConfigSpace bondSet (fixedSpace × 𝒴') → Measure (SiteGaugeGroup siteSet)
attribute [instance] GaugeMoveData.measurableFixedSpace
namespace GaugeMoveData
variable {L m K k : ℕ} {Stored : Type} (M : GaugeMoveData.{u} L m K k Stored)
abbrev Space (𝒴' : Type u) : Type u :=
  ConfigSpace M.bondSet (M.fixedSpace × 𝒴')
structure IsConfigSpace (𝒴' : Type u) [MeasurableSpace 𝒴'] : Prop where
  auxStandardBorel : IsStandardBorelSpace 𝒴'
  configData : IsConfigSpaceData M.bondSet (M.fixedSpace × 𝒴')
variable {𝒴' : Type u} [MeasurableSpace 𝒴']
def blockFieldOf (ξ : M.Space 𝒴') : BlockFields L m K k :=
  M.blockMap (ξ.1, ξ.2.1)
def fixGaugeMeasure (ν : FiniteComplexMeasure (M.Space 𝒴')) :
    FiniteComplexMeasure (M.Space 𝒴') :=
  fixingImage (M.kernel 𝒴') ν
def IsTermPresentation (τ : ComplexMeasure (BlockFields L m K k))
    (ν : FiniteComplexMeasure (M.Space 𝒴')) : Prop :=
  IsPushforwardPresentation τ ν M.blockFieldOf
section EvaluationMaps
variable {Λ Named : Type} {O : Named → Type u} [∀ n, MeasurableSpace (O n)]
abbrev FixedVariable (Λ : Type) : Type :=
  {g : GroupCoordinate L m K k Stored // g ∉ M.moved.movedCoords M.bondSet} ⊕ Λ
variable {M} in
def AgreeOn (N : Set (M.FixedVariable Λ))
    (a a' : FixedValues M.moved M.bondSet Λ) : Prop :=
  (∀ g, Sum.inl g ∈ N → a.1 g = a'.1 g) ∧ ∀ l, Sum.inr l ∈ N → a.2 l = a'.2 l
structure IsMoveRepresentation (N : Set (M.FixedVariable Λ))
    (holds : M.fixedSpace × 𝒴' ≃ᵐ FixedValues M.moved M.bondSet Λ × ∀ n, O n)
    (object : ∀ n, FixedValues M.moved M.bondSet Λ → O n) : Prop where
  evalOnSigma : IsConfigRepresentation M.moved M.siteSet M.bondSet holds object
  fixedPart : ∀ a a' o, AgreeOn N a a' →
    (holds.symm (a, o)).1 = (holds.symm (a', o)).1
  freePart : ∀ a a' o o', AgreeOn Nᶜ a a' →
    (holds.symm (a, o)).2 = (holds.symm (a', o')).2
structure IsFramedMoveRepresentation {C : Type} (N : Set (M.FixedVariable Λ))
    (holds : M.fixedSpace × 𝒴' ≃ᵐ FramedFixedValues C M.moved M.bondSet Λ × ∀ n, O n)
    (object : ∀ n, FramedFixedValues C M.moved M.bondSet Λ → O n) : Prop where
  evalOnSigma : IsFramedConfigRepresentation M.moved M.siteSet M.bondSet holds object
  fixedPart : ∀ r r' a a' o, AgreeOn N a a' →
    (holds.symm ((r, a), o)).1 = (holds.symm ((r', a'), o)).1
  freePart : ∀ r a a' o o', AgreeOn Nᶜ a a' →
    (holds.symm ((r, a), o)).2 = (holds.symm ((r, a'), o')).2
end EvaluationMaps
end GaugeMoveData
end YangMills.Construction.PeriodicLattice.ConfigSpaces
