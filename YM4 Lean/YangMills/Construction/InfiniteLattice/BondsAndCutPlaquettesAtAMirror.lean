import YangMills.Construction.InfiniteLattice.OneLatticeAtOneSpacing
import YangMills.Construction.InfiniteLattice.SixteenFamiliesHeightsPositionsAndSides
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix
noncomputable section
namespace YangMills.Construction
namespace NormalFamilies
open InfiniteLattice
open PeriodicLattice (coordVec)
variable {a : ℝ}
def plaquetteCorners (p : ElementaryPlaquette a) : Set (LatticePoint a) :=
  {p.corner, p.corner + axisStep a p.lowAxis, p.corner + axisStep a p.lowAxis + axisStep a p.highAxis,
    p.corner + axisStep a p.highAxis}
def HasDiagonalCornersAtLevel (n : AmbientSpace) (c : ℝ) (p : ElementaryPlaquette a) : Prop :=
  (linearHeight n (p.corner : LatticePoint a) = c ∧
      linearHeight n (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis : LatticePoint a) = c) ∨
    (linearHeight n (p.corner + axisStep a p.lowAxis : LatticePoint a) = c ∧
      linearHeight n (p.corner + axisStep a p.highAxis : LatticePoint a) = c)
def levelCornerOne (n : AmbientSpace) (p : ElementaryPlaquette a) : LatticePoint a :=
  open Classical in if n p.highAxis = 1 then p.corner + axisStep a p.lowAxis else p.corner
def levelCornerTwo (n : AmbientSpace) (p : ElementaryPlaquette a) : LatticePoint a :=
  open Classical in
  if n p.highAxis = 1 then p.corner + axisStep a p.highAxis
  else p.corner + axisStep a p.lowAxis + axisStep a p.highAxis
def raisedCorner (n : AmbientSpace) (p : ElementaryPlaquette a) : LatticePoint a :=
  open Classical in
  if n p.highAxis = 1 then p.corner + axisStep a p.lowAxis + axisStep a p.highAxis
  else p.corner + axisStep a p.lowAxis
def loweredCorner (n : AmbientSpace) (p : ElementaryPlaquette a) : LatticePoint a :=
  open Classical in if n p.highAxis = 1 then p.corner else p.corner + axisStep a p.highAxis
def linkToRaised (n : AmbientSpace) (p : ElementaryPlaquette a) : Link a where
  initial := levelCornerOne n p
  terminal := raisedCorner n p
  isAdjacent := by
    unfold levelCornerOne raisedCorner
    split_ifs
    · exact ⟨p.highAxis, Or.inl (by abel)⟩
    · exact ⟨p.lowAxis, Or.inl (by abel)⟩
def linkFromRaised (n : AmbientSpace) (p : ElementaryPlaquette a) : Link a where
  initial := raisedCorner n p
  terminal := levelCornerTwo n p
  isAdjacent := by
    unfold levelCornerTwo raisedCorner
    split_ifs
    · exact ⟨p.lowAxis, Or.inr (by abel)⟩
    · exact ⟨p.highAxis, Or.inl (by abel)⟩
def linkToLowered (n : AmbientSpace) (p : ElementaryPlaquette a) : Link a where
  initial := levelCornerOne n p
  terminal := loweredCorner n p
  isAdjacent := by
    unfold levelCornerOne loweredCorner
    split_ifs
    · exact ⟨p.lowAxis, Or.inr (by abel)⟩
    · exact ⟨p.highAxis, Or.inl (by abel)⟩
def linkFromLowered (n : AmbientSpace) (p : ElementaryPlaquette a) : Link a where
  initial := loweredCorner n p
  terminal := levelCornerTwo n p
  isAdjacent := by
    unfold levelCornerTwo loweredCorner
    split_ifs
    · exact ⟨p.highAxis, Or.inl (by abel)⟩
    · exact ⟨p.lowAxis, Or.inl (by abel)⟩
def raisedPathHolonomy (n : AmbientSpace) (p : ElementaryPlaquette a) (U : GaugeField a) :
    Matrices.ComplexMatrix2.specialUnitary :=
  U (linkToRaised n p) * U (linkFromRaised n p)
def lowerCutLink (lam : Fin 4) (p : ElementaryPlaquette a) : Link a := Link.forwardFrom p.corner lam
def upperCutLink (μ lam : Fin 4) (p : ElementaryPlaquette a) : Link a :=
  Link.forwardFrom (p.corner + axisStep a μ) lam
def crossingHolonomy (μ : Fin 4) (U : GaugeField a) (x : LatticePoint a) :
    Matrices.ComplexMatrix2.specialUnitary :=
  U (Link.forwardFrom x μ)
def NormalLevelPair.reflectedLink (P : NormalLevelPair a) (b : Link a) : Link a :=
  (P.reflectSymmetry.linkMap b).orientedRepresentative
def HeightIncrementAlongLinks (n : AmbientSpace) : Prop :=
  ∀ (x : LatticePoint 1) (ρ : Fin 4),
    linearHeight n (x + axisStep 1 ρ : LatticePoint 1) - linearHeight n (x : LatticePoint 1) =
        n ⬝ᵥ coordVec ρ ∧
      n ⬝ᵥ coordVec ρ = n ρ ∧ (n ρ = 0 ∨ n ρ = 1 ∨ n ρ = -1)
def LinksAtIntegerLevel (P : NormalLevelPair 1) : Prop :=
  crossingLinks 1 P.normal P.level = ∅ ∧
    ∀ b ∈ planeLinks 1 P.normal P.level,
      reflectAcross P.normal P.level (b.initial : LatticePoint 1) = (b.initial : LatticePoint 1) ∧
        reflectAcross P.normal P.level (b.terminal : LatticePoint 1) = (b.terminal : LatticePoint 1) ∧
          P.reflectSymmetry.linkMap b = b
def LinksAtHalfIntegerLevel (P : NormalLevelPair 1) : Prop :=
  ∃ μ : Fin 4, P.normal = coordVec μ ∧
    planeLinks 1 P.normal P.level = ∅ ∧
    crossingLinks 1 P.normal P.level =
      {b | ∃ x : LatticePoint 1, (x : AmbientSpace) μ = P.level - 1 / 2 ∧ b = Link.forwardFrom x μ} ∧
    ∀ x : LatticePoint 1, (x : AmbientSpace) μ = P.level - 1 / 2 →
      reflectAcross P.normal P.level (x : LatticePoint 1) = (x + axisStep 1 μ : LatticePoint 1) ∧
        reflectAcross P.normal P.level (x + axisStep 1 μ : LatticePoint 1) = (x : LatticePoint 1) ∧
          P.reflectSymmetry.linkMap (Link.forwardFrom x μ) = (Link.forwardFrom x μ).opposite
def HalfSpaceLinksCorrespond (P : NormalLevelPair 1) : Prop :=
  BijOn P.reflectedLink (halfSpaceLinks 1 P.normal P.level 1)
    (halfSpaceLinks 1 P.normal P.level (-1))
def DiagonalCutProperties (P : NormalLevelPair 1) (μ lam : Fin 4) (p : ElementaryPlaquette 1) :
    Prop :=
  (P.normal = coordVec μ - coordVec lam →
      levelCornerOne P.normal p = p.corner ∧
        levelCornerTwo P.normal p = p.corner + axisStep 1 μ + axisStep 1 lam ∧
        raisedCorner P.normal p = p.corner + axisStep 1 μ ∧
        loweredCorner P.normal p = p.corner + axisStep 1 lam) ∧
    (P.normal = coordVec μ + coordVec lam →
      levelCornerOne P.normal p = p.corner + axisStep 1 μ ∧
        levelCornerTwo P.normal p = p.corner + axisStep 1 lam ∧
        raisedCorner P.normal p = p.corner + axisStep 1 μ + axisStep 1 lam ∧
        loweredCorner P.normal p = p.corner) ∧
    plaquetteCorners p =
      {levelCornerOne P.normal p, levelCornerTwo P.normal p, raisedCorner P.normal p,
        loweredCorner P.normal p} ∧
    linearHeight P.normal (levelCornerOne P.normal p : LatticePoint 1) = P.level ∧
    linearHeight P.normal (levelCornerTwo P.normal p : LatticePoint 1) = P.level ∧
    linearHeight P.normal (raisedCorner P.normal p : LatticePoint 1) = P.level + 1 ∧
    linearHeight P.normal (loweredCorner P.normal p : LatticePoint 1) = P.level - 1 ∧
    reflectAcross P.normal P.level (raisedCorner P.normal p : LatticePoint 1) =
      (loweredCorner P.normal p : LatticePoint 1) ∧
    (∀ i j : Fin 2,
      (fun U : GaugeField 1 =>
          ((raisedPathHolonomy P.normal p U : Matrices.ComplexMatrix2.specialUnitary) :
            Matrices.ComplexMatrix2) i j) ∈
        halfSpaceContinuousLocal 1 P.normal P.level 1) ∧
    ∀ U : GaugeField 1,
      (Matrices.ComplexMatrix2.fullTrace (faceHolonomy U p : Matrices.ComplexMatrix2)).re =
          (Matrices.ComplexMatrix2.fullTrace ((raisedPathHolonomy P.normal p U *
            (raisedPathHolonomy P.normal p (P.reflectSymmetry.pullbackField U))⁻¹ :
              Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re ∧
        raisedPathHolonomy P.normal p (P.reflectSymmetry.pullbackField U) =
          U (linkToLowered P.normal p) * U (linkFromLowered P.normal p)
def DiagonalCutCharacterization (P : NormalLevelPair 1) : Prop :=
  ∀ μ lam : Fin 4, μ < lam →
    (P.normal = coordVec μ - coordVec lam ∨ P.normal = coordVec μ + coordVec lam) →
    ∀ p : ElementaryPlaquette 1,
      (IsCutBy p P.normal P.level ↔
        p.LiesInPlane μ lam ∧ HasDiagonalCornersAtLevel P.normal P.level p) ∧
      (P.normal = coordVec μ - coordVec lam →
        (IsCutBy p P.normal P.level ↔
          p.LiesInPlane μ lam ∧ linearHeight P.normal (p.corner : LatticePoint 1) = P.level)) ∧
      (P.normal = coordVec μ + coordVec lam →
        (IsCutBy p P.normal P.level ↔
          p.LiesInPlane μ lam ∧ linearHeight P.normal (p.corner : LatticePoint 1) = P.level - 1)) ∧
      (IsCutBy p P.normal P.level → DiagonalCutProperties P μ lam p)
def AxisCutProperties (P : NormalLevelPair 1) (μ lam : Fin 4) (p : ElementaryPlaquette 1) : Prop :=
  plaquetteCorners p =
      {p.corner, p.corner + axisStep 1 μ, p.corner + axisStep 1 μ + axisStep 1 lam,
        p.corner + axisStep 1 lam} ∧
    lowerCutLink lam p ∈ halfSpaceLinks 1 P.normal P.level (-1) ∧
    upperCutLink μ lam p ∈ halfSpaceLinks 1 P.normal P.level 1 ∧
    P.reflectSymmetry.linkMap (lowerCutLink lam p) = upperCutLink μ lam p ∧
    ∀ U : GaugeField 1,
      (Matrices.ComplexMatrix2.fullTrace (faceHolonomy U p : Matrices.ComplexMatrix2)).re =
        (Matrices.ComplexMatrix2.fullTrace ((crossingHolonomy μ U p.corner *
          U (upperCutLink μ lam p) *
          (crossingHolonomy μ U (p.corner + axisStep 1 lam))⁻¹ *
            (U (lowerCutLink lam p))⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
              Matrices.ComplexMatrix2)).re
def HasBaseEdgeAtLevel (n : AmbientSpace) (c : ℝ) (lam : Fin 4) (p : ElementaryPlaquette 1) :
    Prop :=
  linearHeight n (p.corner : LatticePoint 1) = c - 1 / 2 ∧
    linearHeight n (p.corner + axisStep 1 lam : LatticePoint 1) = c - 1 / 2
def AxisCutCharacterization (P : NormalLevelPair 1) : Prop :=
  ∀ μ : Fin 4, P.normal = coordVec μ → (∃ k : ℤ, P.level = (k : ℝ) + 1 / 2) →
    ∀ p : ElementaryPlaquette 1,
      (IsCutBy p P.normal P.level ↔
        ∃ lam : Fin 4, lam ≠ μ ∧ p.LiesInPlane μ lam ∧
          HasBaseEdgeAtLevel P.normal P.level lam p) ∧
      ∀ lam : Fin 4, lam ≠ μ → p.LiesInPlane μ lam →
        HasBaseEdgeAtLevel P.normal P.level lam p → AxisCutProperties P μ lam p
def LinksAndCutPlaquettesAtLevel : Prop :=
  ∀ P : NormalLevelPair 1,
    HeightIncrementAlongLinks P.normal ∧
    ((∃ k : ℤ, P.level = (k : ℝ)) → LinksAtIntegerLevel P) ∧
    ((∃ k : ℤ, P.level = (k : ℝ) + 1 / 2) → LinksAtHalfIntegerLevel P) ∧
    HalfSpaceLinksCorrespond P ∧
    (P.IsSitePair → ∀ p : ElementaryPlaquette 1, ¬ IsCutBy p P.normal P.level) ∧
    DiagonalCutCharacterization P ∧
    AxisCutCharacterization P
end NormalFamilies
end YangMills.Construction
