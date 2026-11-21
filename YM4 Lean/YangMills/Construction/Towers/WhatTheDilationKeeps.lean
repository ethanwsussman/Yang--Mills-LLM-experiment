import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.DilationOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
section PeriodicSide
variable {L n k j : ℕ}
structure ScalingPreservesOnEdges (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (ℬ : Set (Edge L n k i)) :
    Prop where
  reversal_closed :
    PeriodicLattice.IsReversalClosed (scaleEdge hL hj i '' ℬ)
  compactField_iff : ∀ V : Edge L n k i → Matrices.ComplexMatrix2,
    PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup ℬ V ↔
      PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup (scaleEdge hL hj i '' ℬ)
        (transportTotal (scaleEdge hL hj i) V)
  complexField_iff : ∀ V : Edge L n k i → Matrices.ComplexMatrix2,
    PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup ℬ V ↔
      PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup (scaleEdge hL hj i '' ℬ)
        (transportTotal (scaleEdge hL hj i) V)
  holonomy_eq : ∀ V : Edge L n k i → Matrices.ComplexMatrix2,
    PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup ℬ V →
    ∀ γ : List (Edge L n k i), PeriodicLattice.IsBondPath γ → (∀ b ∈ γ, b ∈ ℬ) →
      PeriodicLattice.pathHolonomy (transportTotal (scaleEdge hL hj i) V)
        (scalePath hL hj i γ) = PeriodicLattice.pathHolonomy V γ
  plaquetteHolonomy_eq : ∀ V : Edge L n k i → Matrices.ComplexMatrix2,
    PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup ℬ V →
    ∀ p : Face L n k i, (∀ b ∈ p.boundaryBonds, b ∈ ℬ) →
      PeriodicLattice.plaquetteHolonomy (transportTotal (scaleEdge hL hj i) V)
        (scaleFace hL hj i p) = PeriodicLattice.plaquetteHolonomy V p
  antisymm_iff : ∀ B : Edge L n k i → Matrices.ComplexMatrix2,
    (∀ b ∈ ℬ, B b.opposite = -B b) ↔
      ∀ e ∈ scaleEdge hL hj i '' ℬ,
        transportTotal (scaleEdge hL hj i) B e.opposite =
          -transportTotal (scaleEdge hL hj i) B e
  sumAlong_eq : ∀ B : Edge L n k i → Matrices.ComplexMatrix2,
    ∀ γ : List (Edge L n k i), PeriodicLattice.IsBondPath γ → (∀ b ∈ γ, b ∈ ℬ) →
      PeriodicLattice.bondFormSumAlong (transportTotal (scaleEdge hL hj i) B)
        (scalePath hL hj i γ) = PeriodicLattice.bondFormSumAlong B γ
def ScalingPreservesGaugeAct (hL : 0 < L) (hj : j ≤ k) (n i : ℕ) : Prop :=
  ∀ (V : Edge L n k i → Matrices.ComplexMatrix2) (u : Vertex L n k i → Matrices.ComplexMatrix2),
    PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ V →
    PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup u →
    transportTotal (scaleEdge hL hj i) (PeriodicLattice.gaugeTransform u V) =
      PeriodicLattice.gaugeTransform (transportTotal (scaleVertex hL hj i).toEquiv u)
        (transportTotal (scaleEdge hL hj i) V)
structure ScalingPreservesSymmetry (hL : 0 < L) (hj : j ≤ k) (i : ℕ)
    (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n) : Prop where
  distancePreserving : IsDistancePreserving (conjMap (scaling hL n k j).toEquiv f)
  mapsSublattice : MapsSublatticeOnto j i (conjMap (scaling hL n k j).toEquiv f)
  edge_comm : ∀ b : Edge L n k i,
    scaleEdge hL hj i (edgeImage f b) =
      edgeImage (conjMap (scaling hL n k j).toEquiv f) (scaleEdge hL hj i b)
  field_comm : ∀ V : Edge L n k i → Matrices.ComplexMatrix2,
    PeriodicLattice.IsGaugeField PeriodicLattice.compactGaugeGroup univ V ∨
        PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ V →
      transportTotal (scaleEdge hL hj i) (pushField f V) =
        pushField (conjMap (scaling hL n k j).toEquiv f)
          (transportTotal (scaleEdge hL hj i) V)
  siteFunction_comm : ∀ g : Vertex L n k i → Matrices.ComplexMatrix2,
    transportTotal (scaleVertex hL hj i).toEquiv (pushSiteFunction f g) =
      pushSiteFunction (conjMap (scaling hL n k j).toEquiv f)
        (transportTotal (scaleVertex hL hj i).toEquiv g)
end PeriodicSide
namespace FullSpace
open InfiniteLattice (AmbientSpace)
variable {L k j : ℕ}
structure ScalingPreservesOnEdges (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (ℬ : Set (Edge L k i)) :
    Prop where
  reversal_closed : ∀ e ∈ scaleEdge hL hj i '' ℬ,
    e.opposite ∈ scaleEdge hL hj i '' ℬ
  compactField_iff : ∀ V : Edge L k i → Matrices.ComplexMatrix2,
    IsFieldOn PeriodicLattice.compactGaugeGroup ℬ V ↔
      IsFieldOn PeriodicLattice.compactGaugeGroup (scaleEdge hL hj i '' ℬ)
        (transportTotal (scaleEdge hL hj i) V)
  complexField_iff : ∀ V : Edge L k i → Matrices.ComplexMatrix2,
    IsFieldOn PeriodicLattice.complexGaugeGroup ℬ V ↔
      IsFieldOn PeriodicLattice.complexGaugeGroup (scaleEdge hL hj i '' ℬ)
        (transportTotal (scaleEdge hL hj i) V)
  holonomy_eq : ∀ V : Edge L k i → Matrices.ComplexMatrix2,
    IsFieldOn PeriodicLattice.complexGaugeGroup ℬ V →
    ∀ γ : List (Edge L k i), IsLinkPath γ → (∀ b ∈ γ, b ∈ ℬ) →
      linkHolonomy (transportTotal (scaleEdge hL hj i) V)
        (scalePath hL hj i γ) = linkHolonomy V γ
  faceVariable_eq : ∀ V : Edge L k i → Matrices.ComplexMatrix2,
    IsFieldOn PeriodicLattice.complexGaugeGroup ℬ V →
    ∀ p : Face L k i, (∀ b ∈ faceBoundary p, b ∈ ℬ) →
      faceVariable (transportTotal (scaleEdge hL hj i) V)
        (scaleFace hL hj i p) = faceVariable V p
  antisymm_iff : ∀ B : Edge L k i → Matrices.ComplexMatrix2,
    (∀ b ∈ ℬ, B b.opposite = -B b) ↔
      ∀ e ∈ scaleEdge hL hj i '' ℬ,
        transportTotal (scaleEdge hL hj i) B e.opposite =
          -transportTotal (scaleEdge hL hj i) B e
  sumAlong_eq : ∀ B : Edge L k i → Matrices.ComplexMatrix2,
    ∀ γ : List (Edge L k i), IsLinkPath γ → (∀ b ∈ γ, b ∈ ℬ) →
      sumAlong (transportTotal (scaleEdge hL hj i) B)
        (scalePath hL hj i γ) = sumAlong B γ
def ScalingPreservesGaugeAct (hL : 0 < L) (hj : j ≤ k) (i : ℕ) : Prop :=
  ∀ (V : Edge L k i → Matrices.ComplexMatrix2) (u : Vertex L k i → Matrices.ComplexMatrix2),
    IsFieldIn PeriodicLattice.complexGaugeGroup V →
    (∀ x, u x ∈ PeriodicLattice.complexGaugeGroup) →
    transportTotal (scaleEdge hL hj i) (gaugeAct u V) =
      gaugeAct (transportTotal (scaleVertex hL hj i).toEquiv u)
        (transportTotal (scaleEdge hL hj i) V)
structure ScalingPreservesSymmetry (hL : 0 < L) (hj : j ≤ k) (i : ℕ)
    (f : AmbientSpace → AmbientSpace) : Prop where
  distancePreserving : IsDistancePreserving (conjMap (scaling hL k j).toEquiv f)
  mapsSublattice :
    MapsSublatticeOnto (meshAt L j i) (conjMap (scaling hL k j).toEquiv f)
  edge_comm : ∀ b : Edge L k i,
    scaleEdge hL hj i (edgeImage f b) =
      edgeImage (conjMap (scaling hL k j).toEquiv f) (scaleEdge hL hj i b)
  field_comm : ∀ V : Edge L k i → Matrices.ComplexMatrix2,
    IsFieldIn PeriodicLattice.compactGaugeGroup V ∨
        IsFieldIn PeriodicLattice.complexGaugeGroup V →
      transportTotal (scaleEdge hL hj i) (pushField f V) =
        pushField (conjMap (scaling hL k j).toEquiv f)
          (transportTotal (scaleEdge hL hj i) V)
  siteFunction_comm : ∀ g : Vertex L k i → Matrices.ComplexMatrix2,
    transportTotal (scaleVertex hL hj i).toEquiv (pushSiteFunction f g) =
      pushSiteFunction (conjMap (scaling hL k j).toEquiv f)
        (transportTotal (scaleVertex hL hj i).toEquiv g)
end FullSpace
end Tower
open Tower in
def ScalingCompatibility.Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ (hL : 0 < L) (k j i : ℕ) (hj : j ≤ k),
    i ≤ j →
    (∀ n : ℕ, 0 < n →
      (∀ ℬ : Set (Edge L n k i), PeriodicLattice.IsReversalClosed ℬ →
        ScalingPreservesOnEdges hL hj i ℬ) ∧
      ScalingPreservesGaugeAct hL hj n i ∧
      ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
        IsDistancePreserving f → MapsSublatticeOnto k i f → ScalingPreservesSymmetry hL hj i f) ∧
    (∀ ℬ : Set (FullSpace.Edge L k i), (∀ b ∈ ℬ, b.opposite ∈ ℬ) →
      FullSpace.ScalingPreservesOnEdges hL hj i ℬ) ∧
    FullSpace.ScalingPreservesGaugeAct hL hj i ∧
    ∀ f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace,
      FullSpace.IsDistancePreserving f → FullSpace.MapsSublatticeOnto (meshAt L k i) f →
        FullSpace.ScalingPreservesSymmetry hL hj i f
end YangMills.Construction
end
