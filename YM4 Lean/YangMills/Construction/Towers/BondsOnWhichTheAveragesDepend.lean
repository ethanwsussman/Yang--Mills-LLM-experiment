import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevel
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.SupportOfMeans
section Vocabulary
def IsHolomorphicOnProduct {σ : Type} [Fintype σ] (O : Set (σ → Matrices.ComplexMatrix2))
    (f : (σ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) : Prop :=
  ∀ e : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
    Matrices.GroupLieProduct.IsHolomorphicToUnimodular e
      (Matrices.GroupLieProduct.asGroupFactors '' O)
      fun p => f fun s => p (.inl s)
def DefinedAlike (p q : Option Matrices.ComplexMatrix2) : Prop :=
  (p.isSome ↔ q.isSome) ∧ ∀ X Y : Matrices.ComplexMatrix2, p = some X → q = some Y → X = Y
variable {β : Type} (Ws : Set (β → Matrices.ComplexMatrix2)) (F : Finset β)
def definedLocus (mean : (β → Matrices.ComplexMatrix2) → Option Matrices.ComplexMatrix2) :
    Set (F → Matrices.ComplexMatrix2) :=
  {w | w ∈ Matrices.GroupLieProduct.unimodularPi F ∧
    ∀ W ∈ Ws, (fun e : F => W e) = w → (mean W).isSome}
structure RepresentsMean (mean : (β → Matrices.ComplexMatrix2) → Option Matrices.ComplexMatrix2)
    (O : Set (F → Matrices.ComplexMatrix2))
    (f : (F → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) : Prop where
  mapsTo_complexGaugeGroup : MapsTo f O PeriodicLattice.complexGaugeGroup
  eq_some : ∀ W ∈ Ws, (fun e : F => W e) ∈ O → mean W = some (f fun e => W e)
def HolomorphicInRestriction (O : Set (F → Matrices.ComplexMatrix2))
    (v : (β → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) : Prop :=
  ∃ f : (F → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2, IsHolomorphicOnProduct O f ∧
    ∀ W ∈ Ws, (fun e : F => W e) ∈ O → f (fun e => W e) = v W
structure DependsOnlyOn (pos : β → Prop)
    (twist : (β → Matrices.ComplexMatrix2) → (β → Matrices.ComplexMatrix2) → β → Matrices.ComplexMatrix2)
    (mean : (β → Matrices.ComplexMatrix2) → Option Matrices.ComplexMatrix2) : Prop where
  definedAlike_of_eqOn : ∀ W ∈ Ws, ∀ W' ∈ Ws, (∀ e ∈ F, W e = W' e) → DefinedAlike (mean W) (mean W')
  isOpen : Matrices.ComplexMatrix2.IsRelativelyOpen (Matrices.GroupLieProduct.unimodularPi F)
    (definedLocus Ws F mean)
  isSome_iff : ∀ W ∈ Ws, (mean W).isSome ↔ (fun e : F => W e) ∈ definedLocus Ws F mean
  exists_representation : ∃ f, RepresentsMean Ws F mean (definedLocus Ws F mean) f
  representation_unique : ∀ f g, RepresentsMean Ws F mean (definedLocus Ws F mean) f →
    RepresentsMean Ws F mean (definedLocus Ws F mean) g → EqOn f g (definedLocus Ws F mean)
  representation_holomorphic : ∀ f, RepresentsMean Ws F mean (definedLocus Ws F mean) f →
    IsHolomorphicOnProduct (definedLocus Ws F mean) f
  definedAlike_twist : ∀ U ∈ Ws, ∀ U' ∈ Ws, ∀ C C' : β → Matrices.ComplexMatrix2,
    (∀ e, pos e → C e ∈ PeriodicLattice.complexLieAlgebra) →
    (∀ e, pos e → C' e ∈ PeriodicLattice.complexLieAlgebra) →
    (∀ e ∈ F, U e = U' e ∧ C e = C' e) → DefinedAlike (mean (twist C U)) (mean (twist C' U'))
end Vocabulary
section Periodic
variable {L n k : ℕ}
def endpointBlocks {u : ℕ} (c : Tower.Edge L n k u) : Set (PeriodicLattice.FourTorus L n) :=
  PeriodicLattice.refinedBlock u c.source ∪ PeriodicLattice.refinedBlock u c.target
def HasEndpointsIn {u : ℕ} (c : Tower.Edge L n k u) (e : Tower.Edge L n k 0) : Prop :=
  (e.source : PeriodicLattice.FourTorus L n) ∈ endpointBlocks c ∧
    (e.target : PeriodicLattice.FourTorus L n) ∈ endpointBlocks c
def supportEdges {u : ℕ} (c : Tower.Edge L n k u) : Set (Tower.Edge L n k 0) :=
  {e | e.IsPositivelyOriented ∧ HasEndpointsIn c e}
abbrev baseFields (L n k : ℕ) : Set (Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :=
  Tower.fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup
abbrev meanAt {u : ℕ} (c : Tower.Edge L n k u) (W : Tower.Edge L n k 0 → Matrices.ComplexMatrix2) :
    Option Matrices.ComplexMatrix2 :=
  Tower.LevelwiseMeans.levelwiseMean W u c
structure StepConditions {i : ℕ} (c : Tower.Edge L n k (i + 1)) (F : Finset (Tower.Edge L n k 0)) :
    Prop where
  defined_mem_polydisc : ∀ W ∈ baseFields L n k,
    (fun e : F => W e) ∈ definedLocus (baseFields L n k) F (meanAt c) →
      (∀ e' ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k i)),
        (Tower.LevelwiseMeans.levelwiseMean W i e').isSome) ∧
      Tower.LevelwiseMeans.valuesOrOne (Tower.LevelwiseMeans.levelwiseMean W i) ∈
        Tower.nearIdentityPolydisc (Tower.polydiscRadius L) c
  holomorphic_edge : ∀ e' ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k i)),
    HolomorphicInRestriction (baseFields L n k) F
      (definedLocus (baseFields L n k) F (meanAt c))
      fun W => Tower.LevelwiseMeans.valuesOrOne (Tower.LevelwiseMeans.levelwiseMean W i) e'
  holomorphic_contour : ∀ y ∈ ({c.source, c.target} : Set (Tower.Vertex L n k (i + 1))),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
      HolomorphicInRestriction (baseFields L n k) F
        (definedLocus (baseFields L n k) F (meanAt c))
        fun W => PeriodicLattice.complexMeanContourHolonomy
          (Tower.LevelwiseMeans.valuesOrOne (Tower.LevelwiseMeans.levelwiseMean W i)) y x
structure SideRequirements (L n k : ℕ) : Prop where
  finite_nonempty : ∀ u ≤ k, ∀ c : Tower.Edge L n k u,
    (supportEdges c).Finite ∧ (supportEdges c).Nonempty
  hasEndpointsIn_of_doubleBlock : ∀ i < k, ∀ c : Tower.Edge L n k (i + 1), c.IsPositivelyOriented →
    ∀ e' ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k i)), ∀ e : Tower.Edge L n k 0,
      HasEndpointsIn e' e → HasEndpointsIn c e
  dependsOnlyOn : ∀ u ≤ k, ∀ c : Tower.Edge L n k u, ∀ F : Finset (Tower.Edge L n k 0),
    (F : Set (Tower.Edge L n k 0)) = supportEdges c →
      DependsOnlyOn (baseFields L n k) F (fun e => e.IsPositivelyOriented)
        PeriodicLattice.expTwist (meanAt c)
  step : ∀ i < k, ∀ c : Tower.Edge L n k (i + 1), c.IsPositivelyOriented →
    ∀ F : Finset (Tower.Edge L n k 0),
    (F : Set (Tower.Edge L n k 0)) = supportEdges c → StepConditions c F
end Periodic
namespace Unbounded
variable {L k : ℕ}
def endpointBlocks {u : ℕ} (c : Tower.FullSpace.Edge L k u) : Set InfiniteLattice.AmbientSpace :=
  Tower.FullSpace.cubeOfOrder L (Tower.meshAt L k 0) u c.initial ∪
    Tower.FullSpace.cubeOfOrder L (Tower.meshAt L k 0) u c.terminal
def HasEndpointsIn {u : ℕ} (c : Tower.FullSpace.Edge L k u) (e : Tower.FullSpace.Edge L k 0) : Prop :=
  (e.initial : InfiniteLattice.AmbientSpace) ∈ endpointBlocks c ∧
    (e.terminal : InfiniteLattice.AmbientSpace) ∈ endpointBlocks c
def supportEdges {u : ℕ} (c : Tower.FullSpace.Edge L k u) : Set (Tower.FullSpace.Edge L k 0) :=
  {e | e.IsPositivelyOriented ∧ HasEndpointsIn c e}
abbrev baseFields (L k : ℕ) : Set (Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) :=
  Tower.FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup
abbrev meanAt {u : ℕ} (c : Tower.FullSpace.Edge L k u)
    (W : Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) : Option Matrices.ComplexMatrix2 :=
  Tower.LevelwiseMeans.Unbounded.levelwiseMean W u c
structure StepConditions {i : ℕ} (c : Tower.FullSpace.Edge L k (i + 1))
    (F : Finset (Tower.FullSpace.Edge L k 0)) : Prop where
  defined_mem_polydisc : ∀ W ∈ baseFields L k,
    (fun e : F => W e) ∈ definedLocus (baseFields L k) F (meanAt c) →
      (∀ e' ∈ Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c,
        (Tower.LevelwiseMeans.Unbounded.levelwiseMean W i e').isSome) ∧
      Tower.LevelwiseMeans.valuesOrOne (Tower.LevelwiseMeans.Unbounded.levelwiseMean W i) ∈
        Tower.FullSpace.nearIdentityPolydisc L k i (Tower.polydiscRadius L) c
  holomorphic_edge : ∀ e' ∈ Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c,
    HolomorphicInRestriction (baseFields L k) F
      (definedLocus (baseFields L k) F (meanAt c))
      fun W => Tower.LevelwiseMeans.valuesOrOne (Tower.LevelwiseMeans.Unbounded.levelwiseMean W i) e'
  holomorphic_contour : ∀ y ∈ ({c.initial, c.terminal} : Set (Tower.FullSpace.Vertex L k (i + 1))),
    ∀ x ∈ Tower.FullSpace.cubeVertices L (Tower.meshAt L k i) y,
      HolomorphicInRestriction (baseFields L k) F
        (definedLocus (baseFields L k) F (meanAt c))
        fun W => Tower.FullSpace.complexContourMean L
          (Tower.LevelwiseMeans.valuesOrOne (Tower.LevelwiseMeans.Unbounded.levelwiseMean W i)) y x
structure SideRequirements (L k : ℕ) : Prop where
  finite_nonempty : ∀ u ≤ k, ∀ c : Tower.FullSpace.Edge L k u,
    (supportEdges c).Finite ∧ (supportEdges c).Nonempty
  hasEndpointsIn_of_doubleBlock : ∀ i < k, ∀ c : Tower.FullSpace.Edge L k (i + 1),
    c.IsPositivelyOriented →
    ∀ e' ∈ Tower.FullSpace.doubleCubeLinks L (Tower.meshAt L k i) c, ∀ e : Tower.FullSpace.Edge L k 0,
      HasEndpointsIn e' e → HasEndpointsIn c e
  dependsOnlyOn : ∀ u ≤ k, ∀ c : Tower.FullSpace.Edge L k u, ∀ F : Finset (Tower.FullSpace.Edge L k 0),
    (F : Set (Tower.FullSpace.Edge L k 0)) = supportEdges c →
      DependsOnlyOn (baseFields L k) F (fun e => e.IsPositivelyOriented) Tower.FullSpace.expTwist
        (meanAt c)
  step : ∀ i < k, ∀ c : Tower.FullSpace.Edge L k (i + 1), c.IsPositivelyOriented →
    ∀ F : Finset (Tower.FullSpace.Edge L k 0),
    (F : Set (Tower.FullSpace.Edge L k 0)) = supportEdges c → StepConditions c F
end Unbounded
def SupportOfMeansHolds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∀ n : ℕ, 0 < n → SideRequirements L n k) ∧ Unbounded.SideRequirements L k
end YangMills.Construction.Tower.SupportOfMeans
end
