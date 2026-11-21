import YangMills.Construction.InfiniteLattice.WhatAMirrorOfTheLatticeCuts
import YangMills.Construction.ReflectionPositivity.HalvesOfASplitTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open YangMills.Construction.NormalFamilies
open YangMills.Construction.PeriodicLattice (coordVec)
namespace PeriodSublattice
variable (Γ : PeriodSublattice 1)
def HasTwoVerticesAtHeight (v : AmbientSpace) (w : ℤ) (q : Γ.QuotientPlaquette) (u : ℝ) : Prop :=
  ∃ s ∈ Γ.plaquetteVertices q, ∃ s' ∈ Γ.plaquetteVertices q, s ≠ s' ∧
    Γ.HasHeight v w s u ∧ Γ.HasHeight v w s' u
def HasVertexHeightsAround (v : AmbientSpace) (w : ℤ) (q : Γ.QuotientPlaquette) (u : ℝ) : Prop :=
  (∀ s ∈ Γ.plaquetteVertices q, Γ.HasHeight v w s (u - 1 / 2) ∨ Γ.HasHeight v w s (u + 1 / 2)) ∧
    (∃ s ∈ Γ.plaquetteVertices q, Γ.HasHeight v w s (u - 1 / 2)) ∧
    ∃ s ∈ Γ.plaquetteVertices q, Γ.HasHeight v w s (u + 1 / 2)
def LoopIdentityDescends (Q : NormalLevelPair 1) (p : ElementaryPlaquette 1) (y y' : LatticePoint 1) : Prop :=
  ∃ (zUp zDown : LatticePoint 1) (l₁ l₂ l₃ l₄ : Link 1),
    plaquetteCorners p = {y, y', zUp, zDown} ∧
    linearHeight Q.normal (zUp : LatticePoint 1) = Q.level + 1 ∧
    linearHeight Q.normal (zDown : LatticePoint 1) = Q.level - 1 ∧
    l₁.initial = y ∧ l₁.terminal = zUp ∧ l₂.initial = zUp ∧ l₂.terminal = y' ∧
    l₃.initial = y ∧ l₃.terminal = zDown ∧ l₄.initial = zDown ∧ l₄.terminal = y' ∧
    ∀ U : Γ.QuotientField,
      (Matrices.ComplexMatrix2.fullTrace (faceHolonomy (Γ.lift U) p : Matrices.ComplexMatrix2)).re =
          (Matrices.ComplexMatrix2.fullTrace ((twoLinkHolonomy l₁ l₂ (Γ.lift U) *
            (twoLinkHolonomy l₁ l₂
              (Q.reflectSymmetry.pullbackField (Γ.lift U)))⁻¹ :
                Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re ∧
        twoLinkHolonomy l₁ l₂
            (Q.reflectSymmetry.pullbackField (Γ.lift U)) =
          twoLinkHolonomy l₃ l₄ (Γ.lift U)
def CrossingIdentityDescends (μ ν : Fin 4) (p : ElementaryPlaquette 1) (x : LatticePoint 1) : Prop :=
  ∀ U : Γ.QuotientField,
    (Matrices.ComplexMatrix2.fullTrace (faceHolonomy (Γ.lift U) p : Matrices.ComplexMatrix2)).re =
      (Matrices.ComplexMatrix2.fullTrace ((crossingHolonomy μ (Γ.lift U) x *
        Γ.lift U (Link.forwardFrom (x + axisStep 1 μ) ν) *
          (crossingHolonomy μ (Γ.lift U) (x + axisStep 1 ν))⁻¹ *
            (Γ.lift U (Link.forwardFrom x ν))⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
              Matrices.ComplexMatrix2)).re
end PeriodSublattice
def IsCutThroughDiagonalBy (Q : NormalLevelPair 1) (μ ν : Fin 4) (p : ElementaryPlaquette 1)
    (y y' : LatticePoint 1) : Prop :=
  p.LiesInPlane μ ν ∧ IsDiagonalCornerPair p y y' ∧
    linearHeight Q.normal (y : LatticePoint 1) = Q.level ∧
    linearHeight Q.normal (y' : LatticePoint 1) = Q.level ∧
    IsCutBy p Q.normal Q.level ∧ SplitsThroughCorners Q p y y'
def IsCutAlongLinksBy (Q : NormalLevelPair 1) (μ ν : Fin 4) (p : ElementaryPlaquette 1)
    (x : LatticePoint 1) : Prop :=
  ν ≠ μ ∧ HasCornerSquare p x μ ν ∧ linearHeight Q.normal (x : LatticePoint 1) = Q.level - 1 / 2 ∧
    IsCutBy p Q.normal Q.level
def TwoLevelsOfOneReflection : Prop :=
  ∀ (Γ : PeriodSublattice 1) (v : AmbientSpace) (hv : v ∈ normalSet) (w : ℤ) (c : ℝ)
    (hc : IsAllowedLevel 1 v c), Γ.SplitsAlongWithHalfPeriod v w →
    ∃ hw : IsAllowedLevel 1 v (c + (w : ℝ)),
    let P : NormalLevelPair 1 := ⟨v, hv, c, hc⟩
    let P' : NormalLevelPair 1 := ⟨v, hv, c + (w : ℝ), hw⟩
    Γ.sharedLinks v w c =
      {b | (∀ s ∈ Γ.linkEndpoints b, Γ.HasHeight v w s c) ∨
        ∀ s ∈ Γ.linkEndpoints b, Γ.HasHeight v w s (c + (w : ℝ))} ∧
    ((∃ k : ℤ, c = (k : ℝ)) →
      Γ.crossingLinks v w c = ∅ ∧
      (∀ b ∈ Γ.sharedLinks v w c,
        Γ.descendOrientedLink P.reflectSymmetry (Γ.orientedOfLink b) = Γ.orientedOfLink b) ∧
      (normSq v = 1 → ∀ q : Γ.QuotientPlaquette, ¬ Γ.IsSplitPlaquette v w c q) ∧
      ∀ μ ν : Fin 4, μ < ν →
        (v = coordVec μ - coordVec ν ∨ v = coordVec μ + coordVec ν) →
        (∀ q : Γ.QuotientPlaquette, Γ.IsSplitPlaquette v w c q ↔
          Γ.PlaquetteLiesInPlane q μ ν ∧
            (Γ.HasTwoVerticesAtHeight v w q c ∨ Γ.HasTwoVerticesAtHeight v w q (c + (w : ℝ)))) ∧
        ∀ Q : NormalLevelPair 1, Q = P ∨ Q = P' → ∀ q : Γ.QuotientPlaquette,
          Γ.PlaquetteLiesInPlane q μ ν → Γ.HasTwoVerticesAtHeight v w q Q.level →
          ∃ (p : ElementaryPlaquette 1) (y y' : LatticePoint 1), Γ.IsLiftOfPlaquette p q ∧
            IsCutThroughDiagonalBy Q μ ν p y y') ∧
    ((∃ k : ℤ, c = (k : ℝ) + 1 / 2) →
      ∃ μ : Fin 4, v = coordVec μ ∧
        Γ.sharedLinks v w c = ∅ ∧
        Γ.crossingLinks v w c =
          {b | ∃ x : LatticePoint 1,
            (Γ.HasHeight v w (Γ.quotientMap x) (c - 1 / 2) ∨
              Γ.HasHeight v w (Γ.quotientMap x) (c + (w : ℝ) - 1 / 2)) ∧
            Γ.orientedOfLink b = Γ.orientedClass (Link.forwardFrom x μ)} ∧
        (∀ b ∈ Γ.crossingLinks v w c,
          Γ.descendOrientedLink P.reflectSymmetry (Γ.orientedOfLink b) =
            Γ.oppositeOriented (Γ.orientedOfLink b)) ∧
        (∀ q : Γ.QuotientPlaquette, Γ.IsSplitPlaquette v w c q ↔
          Γ.HasVertexHeightsAround v w q c ∨ Γ.HasVertexHeightsAround v w q (c + (w : ℝ))) ∧
        ∀ Q : NormalLevelPair 1, Q = P ∨ Q = P' → ∀ q : Γ.QuotientPlaquette,
          Γ.HasVertexHeightsAround v w q Q.level →
          ∃ (p : ElementaryPlaquette 1) (x : LatticePoint 1) (ν : Fin 4), Γ.IsLiftOfPlaquette p q ∧
            IsCutAlongLinksBy Q μ ν p x) ∧
    Γ.descendPoint P.reflectSymmetry '' Γ.plusHalf v w c = Γ.minusHalf v w c ∧
    BijOn (Γ.linkImage P.reflectSymmetry)
      (Γ.plusLinks v w c \ Γ.sharedLinks v w c)
      (Γ.minusLinks v w c \ Γ.sharedLinks v w c) ∧
    Γ.linkImage P.reflectSymmetry '' Γ.sharedLinks v w c =
      Γ.sharedLinks v w c ∧
    Γ.conjReflect P '' (Γ.plusAlgebra v w c : Set (Γ.QuotientField → ℂ)) =
      (Γ.minusAlgebra v w c : Set (Γ.QuotientField → ℂ)) ∧
    Γ.conjReflect P '' (Γ.minusAlgebra v w c : Set (Γ.QuotientField → ℂ)) =
      (Γ.plusAlgebra v w c : Set (Γ.QuotientField → ℂ)) ∧
    (∀ Q : NormalLevelPair 1, Q = P ∨ Q = P' →
      (∀ μ ν : Fin 4, μ < ν →
        (v = coordVec μ - coordVec ν ∨ v = coordVec μ + coordVec ν) →
        (∃ k : ℤ, c = (k : ℝ)) →
        ∀ (p : ElementaryPlaquette 1) (y y' : LatticePoint 1), IsCutThroughDiagonalBy Q μ ν p y y' →
          Γ.LoopIdentityDescends Q p y y') ∧
      (∀ μ : Fin 4, v = coordVec μ → (∃ k : ℤ, c = (k : ℝ) + 1 / 2) →
        ∀ (p : ElementaryPlaquette 1) (x : LatticePoint 1) (ν : Fin 4), IsCutAlongLinksBy Q μ ν p x →
          Γ.CrossingIdentityDescends μ ν p x)) ∧
    (∀ (q : Γ.QuotientPlaquette) (p : ElementaryPlaquette 1), Γ.IsLiftOfPlaquette p q →
      (∀ U : Γ.QuotientField, Γ.quotientFaceEnergy U q =
        1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
          (faceHolonomy (Γ.lift U) p : Matrices.ComplexMatrix2)).re) ∧
      (∀ (U : Γ.QuotientField) (b : PositiveLink 1), b.1 ∈ p.linkSet →
        Γ.lift U b.1 = U (Γ.linkClass b)) ∧
      Γ.plaquetteLinks q = {d | ∃ b : PositiveLink 1, b.1 ∈ p.linkSet ∧ d = Γ.linkClass b} ∧
      (Γ.plaquetteLinks q).ncard = 4) ∧
    ∀ U : Γ.QuotientField,
      P'.reflectSymmetry.pullbackField (Γ.lift U) =
        P.reflectSymmetry.pullbackField (Γ.lift U) ∧
      P.reflectSymmetry.pullbackField (Γ.lift U) =
        Γ.lift (Γ.pullbackField P.reflectSymmetry U)
end YangMills.Construction.InfiniteLattice
