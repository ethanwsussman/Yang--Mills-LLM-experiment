import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import YangMills.Construction.LargeField.StateSpaceMeasures
import YangMills.Construction.Lattice.AxialGauges
import YangMills.Construction.Lattice.GaugeConfigSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicLattice.TermEvaluation
open BorelKernels
universe u
variable {L m K k : ℕ} {Stored Lebesgue Factor : Type}
abbrev GroupCoordinate (L m K k : ℕ) (Stored : Type) : Type :=
  PositivelyOrientedBond L m (levelDepth K k) ⊕ Stored
abbrev AuxiliaryValues (Stored Lebesgue : Type) : Type :=
  (Stored → Matrices.ComplexMatrix2.specialUnitary) × (Lebesgue → ℝ)
abbrev TermPoint (L m K k : ℕ) (Stored Lebesgue : Type) : Type :=
  LevelStateSpace L m K k (AuxiliaryValues Stored Lebesgue)
def groupCoordinateValue (y : TermPoint L m K k Stored Lebesgue) :
    GroupCoordinate L m K k Stored → Matrices.ComplexMatrix2.specialUnitary
  | .inl b => gaugeFieldAtLevelValues y.1 b
  | .inr s => y.2.1 s
def FrameChoice (C : Type) : Type := C → SignedFrame
instance measurableSpaceFrameChoice (C : Type) : MeasurableSpace (FrameChoice C) := ⊤
open ConfigSpaces FaddeevPopov
structure BondField (L m K k : ℕ) (Stored : Type) where
  support : Finset (GradedBond L m K)
  support_one_orientation : ∀ b ∈ support, OrientedEdgeEnds.flip b ∉ support
  coord : support → GroupCoordinate L m K k Stored
  coord_injective : Function.Injective coord
namespace BondField
def Covers (v : BondField L m K k Stored) (b : GradedBond L m K) : Prop :=
  b ∈ v.support ∨ OrientedEdgeEnds.flip b ∈ v.support
def valueOn (v : BondField L m K k Stored) (y : TermPoint L m K k Stored Lebesgue)
    (b : GradedBond L m K) : Matrices.ComplexMatrix2.specialUnitary :=
  linkValue (fun c : v.support => groupCoordinateValue y (v.coord c)) b
def movedCoords (v : BondField L m K k Stored) (𝔅 : Finset (GradedBond L m K)) :
    Set (GroupCoordinate L m K k Stored) :=
  {g | ∃ c : v.support, (c.1 ∈ 𝔅 ∨ OrientedEdgeEnds.flip c.1 ∈ 𝔅) ∧ v.coord c = g}
end BondField
structure IsOperationBondSet (v : BondField L m K k Stored) (S : Finset (FourTorus L m))
    (𝔅 : Finset (GradedBond L m K)) : Prop where
  configBondSet : IsConfigBondSet 𝔅
  covered : ∀ b ∈ 𝔅, v.Covers b
  meets : ∀ b ∈ 𝔅, OrientedEdgeEnds.src b ∈ S ∨ OrientedEdgeEnds.tgt b ∈ S
  complete : ∀ b, v.Covers b → (OrientedEdgeEnds.src b ∈ S ∨ OrientedEdgeEnds.tgt b ∈ S) →
    b ∈ 𝔅 ∨ OrientedEdgeEnds.flip b ∈ 𝔅
abbrev FixedValues (v : BondField L m K k Stored) (𝔅 : Finset (GradedBond L m K))
    (Lebesgue : Type) : Type :=
  ({g : GroupCoordinate L m K k Stored // g ∉ v.movedCoords 𝔅} →
    Matrices.ComplexMatrix2.specialUnitary) × (Lebesgue → ℝ)
def fixedValues (v : BondField L m K k Stored) (𝔅 : Finset (GradedBond L m K))
    (y : TermPoint L m K k Stored Lebesgue) : FixedValues v 𝔅 Lebesgue :=
  (fun g => groupCoordinateValue y g.1, y.2.2)
section ConfigEvaluations
variable {Named : Type} {O : Named → Type u} [∀ n, MeasurableSpace (O n)]
  {𝒴 : Type u} [MeasurableSpace 𝒴]
structure IsConfigRepresentation (v : BondField L m K k Stored) (S : Finset (FourTorus L m))
    (𝔅 : Finset (GradedBond L m K))
    (_holds : 𝒴 ≃ᵐ FixedValues v 𝔅 Lebesgue × ∀ n, O n)
    (object : ∀ n, FixedValues v 𝔅 Lebesgue → O n) : Prop where
  bondSet : IsOperationBondSet v S 𝔅
  standardBorel : BorelKernels.IsStandardBorelSpace 𝒴
  object_standardBorel : ∀ n, BorelKernels.IsStandardBorelSpace (O n)
  object_borel : ∀ n, BorelKernels.IsBorelMeasurable (object n)
def configPoint (v : BondField L m K k Stored) (𝔅 : Finset (GradedBond L m K))
    (holds : 𝒴 ≃ᵐ FixedValues v 𝔅 Lebesgue × ∀ n, O n)
    (object : ∀ n, FixedValues v 𝔅 Lebesgue → O n) (y : TermPoint L m K k Stored Lebesgue) :
    ConfigSpaces.ConfigSpace 𝔅 𝒴 :=
  (fun b => v.valueOn y b.1,
    holds.symm (fixedValues v 𝔅 y, fun n => object n (fixedValues v 𝔅 y)))
abbrev FramedFixedValues (C : Type) (v : BondField L m K k Stored)
    (𝔅 : Finset (GradedBond L m K)) (Lebesgue : Type) : Type :=
  FrameChoice C × FixedValues v 𝔅 Lebesgue
structure IsFramedConfigRepresentation {C : Type} (v : BondField L m K k Stored)
    (S : Finset (FourTorus L m)) (𝔅 : Finset (GradedBond L m K))
    (_holds : 𝒴 ≃ᵐ FramedFixedValues C v 𝔅 Lebesgue × ∀ n, O n)
    (object : ∀ n, FramedFixedValues C v 𝔅 Lebesgue → O n) : Prop where
  bondSet : IsOperationBondSet v S 𝔅
  standardBorel : BorelKernels.IsStandardBorelSpace 𝒴
  object_standardBorel : ∀ n, BorelKernels.IsStandardBorelSpace (O n)
  object_borel : ∀ n, BorelKernels.IsBorelMeasurable (object n)
def framedConfigPoint {C : Type} (v : BondField L m K k Stored)
    (𝔅 : Finset (GradedBond L m K))
    (holds : 𝒴 ≃ᵐ FramedFixedValues C v 𝔅 Lebesgue × ∀ n, O n)
    (object : ∀ n, FramedFixedValues C v 𝔅 Lebesgue → O n)
    (p : FrameChoice C × TermPoint L m K k Stored Lebesgue) : ConfigSpaces.ConfigSpace 𝔅 𝒴 :=
  (fun b => v.valueOn p.2 b.1,
    holds.symm ((p.1, fixedValues v 𝔅 p.2), fun n => object n (p.1, fixedValues v 𝔅 p.2)))
end ConfigEvaluations
end YangMills.Construction.PeriodicLattice.TermEvaluation
