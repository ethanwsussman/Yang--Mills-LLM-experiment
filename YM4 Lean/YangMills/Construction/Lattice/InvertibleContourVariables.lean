import YangMills.Construction.Lattice.BlockAveraging
import YangMills.Construction.Matrices.SmallDiameterMean
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open Matrices
def averagingRadiusCap (L : ℕ) : ℝ := 1 / (200 * (L : ℝ) ^ 2)
variable {L m : ℕ} {j j' : ℤ}
def extendByInverses (P : Set (Bond L m j')) (V : P → ComplexMatrix2) (b : Bond L m j') :
    ComplexMatrix2 :=
  open Classical in
  if hb : b ∈ P then V ⟨b, hb⟩
  else if hb' : b.opposite ∈ P then (V ⟨b.opposite, hb'⟩)⁻¹
  else 1
def positiveBondsInDoubleBlock (c : Bond L m j) : Set (Bond L m j') :=
  {b | b.IsPositivelyOriented ∧ b ∈ bondsInDoubleBlock c}
def restrictToPositiveDoubleBlock (c : Bond L m j) (U : Bond L m j' → ComplexMatrix2) :
    positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2 :=
  fun b => U b
def holonomyInDoubleBlock (c : Bond L m j)
    (V : positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2)
    (γ : List (Bond L m j')) : ComplexMatrix2 :=
  pathHolonomy (extendByInverses (positiveBondsInDoubleBlock c) V) γ
def contourHolonomyFamily (c : Bond L m j)
    (V : positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2)
    (y : Site L m j) (x : Site L m j') : Fin (Fintype.card (AxisOrdering y x)) → ComplexMatrix2 :=
  fun i => holonomyInDoubleBlock c V
    (orderedContour y x ((Fintype.equivFin (AxisOrdering y x)).symm i))
def configurationContourFamily (c : Bond L m j) (U : Bond L m j' → ComplexMatrix2)
    (y : Site L m j) (x : Site L m j') :
    Fin (Fintype.card (AxisOrdering y x)) → ComplexMatrix2 :=
  contourHolonomyFamily c (restrictToPositiveDoubleBlock c U) y x
def invertibleContourSet (c : Bond L m j) :
    Set (positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2) :=
  {V | (∀ b, IsUnit (V b)) ∧
    (∀ x ∈ sitesInBlock j' c.source,
      ComplexMatrix2.unitFamilyDiameter (contourHolonomyFamily c V c.source x) < 1 / 40) ∧
    ∀ x ∈ sitesInBlock j' c.target,
      ComplexMatrix2.unitFamilyDiameter (contourHolonomyFamily c V c.target x) < 1 / 40}
def contourVariable (c : Bond L m j)
    (V : positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2)
    (y : Site L m j) (x : Site L m j') : ComplexMatrix2 :=
  SmallDiameterMean.average (contourHolonomyFamily c V y x)
def contourVariableInverse (c : Bond L m j)
    (V : positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2)
    (y : Site L m j) (x : Site L m j') : ComplexMatrix2 :=
  (contourVariable c V y x)⁻¹
def valuesOnPositiveBonds (U : Bond L m j' → ComplexMatrix2) :
    PositivelyOrientedBond L m j' → ComplexMatrix2 := fun b => U b
def fieldOfPositiveValues (v : PositivelyOrientedBond L m j' → ComplexMatrix2) :
    Bond L m j' → ComplexMatrix2 :=
  extendByInverses {b | b.IsPositivelyOriented} v
def ContourMeansAnalyticOn [Fintype (PositivelyOrientedBond L m j')] (Y : Set (Site L m j))
    (D : Set (Bond L m j' → ComplexMatrix2)) : Prop :=
  D ⊆ compactGaugeFields L m j' ∧ ∀ y ∈ Y, ∀ x ∈ sitesInBlock j' y,
    (∀ U ∈ D, HasContourMean U y x) ∧
    ComplexMatrix2.IsRealAnalyticBetween
      (fun _ : PositivelyOrientedBond L m j' => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 2 => ComplexMatrix2.FactorKind.group) (valuesOnPositiveBonds '' D)
      fun v => ![meanContourHolonomy (fieldOfPositiveValues v) y x,
        (meanContourHolonomy (fieldOfPositiveValues v) y x)⁻¹]
def IsNearIdentity (X : ComplexMatrix2) : Prop := ComplexMatrix2.operatorNorm (X - 1) < 1
end PeriodicLattice
end YangMills.Construction
