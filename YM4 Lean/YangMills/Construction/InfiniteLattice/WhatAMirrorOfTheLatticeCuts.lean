import YangMills.Construction.InfiniteLattice.BondsAndCutPlaquettesAtAMirror
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open YangMills.Construction.InfiniteLattice
open YangMills.Construction.PeriodicLattice (coordVec)
open YangMills.Construction.Matrices (ComplexMatrix2)
def IsDiagonalCornerPair (p : ElementaryPlaquette 1) (y y' : LatticePoint 1) : Prop :=
  (y = p.corner ∧ y' = p.corner + axisStep 1 p.lowAxis + axisStep 1 p.highAxis) ∨
    (y = p.corner + axisStep 1 p.lowAxis + axisStep 1 p.highAxis ∧ y' = p.corner) ∨
    (y = p.corner + axisStep 1 p.lowAxis ∧ y' = p.corner + axisStep 1 p.highAxis) ∨
    (y = p.corner + axisStep 1 p.highAxis ∧ y' = p.corner + axisStep 1 p.lowAxis)
def twoLinkHolonomy (b b' : Link 1) (U : GaugeField 1) : ComplexMatrix2.specialUnitary :=
  U b * U b'
def SplitsThroughCorners (P : NormalLevelPair 1) (p : ElementaryPlaquette 1)
    (y y' : LatticePoint 1) : Prop :=
  ∃ (zUp zDown : LatticePoint 1) (b₁ b₂ b₃ b₄ : Link 1),
    plaquetteCorners p = {y, y', zUp, zDown} ∧
    linearHeight P.normal (zUp : LatticePoint 1) = P.level + 1 ∧
    linearHeight P.normal (zDown : LatticePoint 1) = P.level - 1 ∧
    reflectAcross P.normal P.level (zUp : LatticePoint 1) = (zDown : LatticePoint 1) ∧
    b₁.initial = y ∧ b₁.terminal = zUp ∧ b₂.initial = zUp ∧ b₂.terminal = y' ∧
    b₃.initial = y ∧ b₃.terminal = zDown ∧ b₄.initial = zDown ∧ b₄.terminal = y' ∧
    ∀ U : GaugeField 1,
      (ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re =
          (ComplexMatrix2.fullTrace ((twoLinkHolonomy b₁ b₂ U *
            (twoLinkHolonomy b₁ b₂ (P.reflectSymmetry.pullbackField U))⁻¹ :
              ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re ∧
        twoLinkHolonomy b₁ b₂ (P.reflectSymmetry.pullbackField U) =
          twoLinkHolonomy b₃ b₄ U
def CutsAtDiagonalMirror (P : NormalLevelPair 1) : Prop :=
  ∀ μ ρ : Fin 4, μ < ρ →
    (P.normal = coordVec μ - coordVec ρ ∨ P.normal = coordVec μ + coordVec ρ) →
    (∃ k : ℤ, P.level = (k : ℝ)) →
    ∀ p : ElementaryPlaquette 1,
      (IsCutBy p P.normal P.level ↔
        p.LiesInPlane μ ρ ∧ ∃ y y' : LatticePoint 1, IsDiagonalCornerPair p y y' ∧
          linearHeight P.normal (y : LatticePoint 1) = P.level ∧
          linearHeight P.normal (y' : LatticePoint 1) = P.level) ∧
      ∀ y y' : LatticePoint 1, p.LiesInPlane μ ρ → IsDiagonalCornerPair p y y' →
        linearHeight P.normal (y : LatticePoint 1) = P.level →
        linearHeight P.normal (y' : LatticePoint 1) = P.level →
        SplitsThroughCorners P p y y'
def HasCornerSquare (p : ElementaryPlaquette 1) (x : LatticePoint 1) (μ ρ : Fin 4) : Prop :=
  plaquetteCorners p = {x, x + axisStep 1 μ, x + axisStep 1 μ + axisStep 1 ρ, x + axisStep 1 ρ}
def CutsAtLinkMirror (P : NormalLevelPair 1) : Prop :=
  ∀ μ : Fin 4, P.normal = coordVec μ → (∃ k : ℤ, P.level = (k : ℝ) + 1 / 2) →
    ∀ p : ElementaryPlaquette 1,
      (IsCutBy p P.normal P.level ↔
        ∃ (x : LatticePoint 1) (ρ : Fin 4), ρ ≠ μ ∧ HasCornerSquare p x μ ρ ∧
          linearHeight P.normal (x : LatticePoint 1) = P.level - 1 / 2) ∧
      ∀ (x : LatticePoint 1) (ρ : Fin 4), ρ ≠ μ → HasCornerSquare p x μ ρ →
        linearHeight P.normal (x : LatticePoint 1) = P.level - 1 / 2 →
        P.reflectSymmetry.linkMap (Link.forwardFrom x ρ) = Link.forwardFrom (x + axisStep 1 μ) ρ ∧
        ∀ U : GaugeField 1,
          (ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re =
            (ComplexMatrix2.fullTrace ((crossingHolonomy μ U x *
              U (Link.forwardFrom (x + axisStep 1 μ) ρ) *
              (crossingHolonomy μ U (x + axisStep 1 ρ))⁻¹ *
                (U (Link.forwardFrom x ρ))⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re
def CutPlaquettesOfMirror : Prop :=
  ∀ P : NormalLevelPair 1,
    (normSq P.normal = 1 → (∃ k : ℤ, P.level = (k : ℝ)) →
      ∀ p : ElementaryPlaquette 1, ¬ IsCutBy p P.normal P.level) ∧
    CutsAtDiagonalMirror P ∧
    CutsAtLinkMirror P
end YangMills.Construction.NormalFamilies
