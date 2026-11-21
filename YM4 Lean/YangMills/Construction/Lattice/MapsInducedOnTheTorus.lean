import YangMills.Construction.Lattice.GridCellsAndFaceReflections
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.BoxTorus (IsLiftOf hyperplane slab image projection translate basisVector)
noncomputable section
namespace YangMills.Construction.TorusDescent
variable {L : ℕ} {κ : ℤ}
def IsSignMatrix (R : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∃ r : Fin 4 → ℝ, (∀ μ, r μ = 1 ∨ r μ = -1) ∧ R = Matrix.diagonal r
def signAffine (R : Matrix (Fin 4) (Fin 4) ℝ) (w x : AmbientSpace) : AmbientSpace := R.mulVec x + w
def signAffineGroup : Set (AmbientSpace → AmbientSpace) :=
  {g | ∃ (R : Matrix (Fin 4) (Fin 4) ℝ) (w : AmbientSpace), IsSignMatrix R ∧ g = signAffine R w}
def descend (d : CellGrid L κ) (g : AmbientSpace → AmbientSpace) : d.Space → d.Space :=
  haveI : Nonempty (d.Space → d.Space) := ⟨id⟩
  Classical.epsilon fun gbar => d.IsInducedMap gbar g
def coordReflection (μ : Fin 4) (c : ℝ) (x : AmbientSpace) : AmbientSpace :=
  x - (2 * (x μ - c)) • basisVector μ
def addPeriodMultiples (E : Set ℝ) (p : ℝ) : Set ℝ := {t | ∃ s ∈ E, ∃ k : ℤ, t = s + k * p}
def posHalf (d : CellGrid L κ) (μ : Fin 4) (c : ℝ) : Set d.Space :=
  slab d.sideLengths μ c (c + 1 / 2 * d.sideLengths μ)
def negHalf (d : CellGrid L κ) (μ : Fin 4) (c : ℝ) : Set d.Space :=
  slab d.sideLengths μ (c - 1 / 2 * d.sideLengths μ) c
def fixedPlanes (d : CellGrid L κ) (μ : Fin 4) (c : ℝ) : Set d.Space :=
  hyperplane d.sideLengths μ c ∪ hyperplane d.sideLengths μ (c + 1 / 2 * d.sideLengths μ)
def partition (d : CellGrid L κ) (μ : Fin 4) (c : ℝ) : Fin 4 → Set d.Space :=
  ![posHalf d μ c, negHalf d μ c, hyperplane d.sideLengths μ c,
    hyperplane d.sideLengths μ (c + 1 / 2 * d.sideLengths μ)]
def ProjectionContinuousOpen (d : CellGrid L κ) : Prop :=
  Continuous (projection d.sideLengths) ∧ IsOpenMap (projection d.sideLengths)
def SignAffineIsGroup : Prop :=
  id ∈ signAffineGroup ∧
  (∀ g ∈ signAffineGroup, ∀ h ∈ signAffineGroup, g ∘ h ∈ signAffineGroup) ∧
  ∀ g ∈ signAffineGroup, ∃ g' ∈ signAffineGroup, g ∘ g' = id ∧ g' ∘ g = id
def DescentProperties (d : CellGrid L κ) : Prop :=
  (∀ g ∈ signAffineGroup, ∃! gbar : d.Space → d.Space, d.IsInducedMap gbar g) ∧
  (∀ g ∈ signAffineGroup, d.IsInducedMap (descend d g) g) ∧
  (∀ g ∈ signAffineGroup, ∀ h ∈ signAffineGroup,
    descend d (g ∘ h) = descend d g ∘ descend d h) ∧
  descend d id = id ∧
  ∀ g ∈ signAffineGroup,
    BoxTorus.IsDistPreserving (descend d g) ∧ IsHomeomorph (descend d g)
def DescentImageRules (d : CellGrid L κ) : Prop :=
  ∀ (R : Matrix (Fin 4) (Fin 4) ℝ) (w : AmbientSpace), IsSignMatrix R →
    (∀ S : Set AmbientSpace, descend d (signAffine R w) '' image d.sideLengths S =
      image d.sideLengths (signAffine R w '' S)) ∧
    (∀ (x : d.Space) (w' : AmbientSpace), descend d (signAffine R w) (translate x w') =
      translate (descend d (signAffine R w) x) (R.mulVec w')) ∧
    (signAffine R w '' (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L κ) : Set AmbientSpace) =
        (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L κ) : Set AmbientSpace) →
      descend d (signAffine R w) '' (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) =
        (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space))
def LiftCharacterization (d : CellGrid L κ) (μ : Fin 4) (c : ℝ) : Prop :=
  (∀ (x : d.Space) (y : AmbientSpace), IsLiftOf y x →
    (x ∈ posHalf d μ c ↔ y μ ∈ addPeriodMultiples (Ioo c (c + 1 / 2 * d.sideLengths μ)) (d.sideLengths μ)) ∧
    (x ∈ negHalf d μ c ↔ y μ ∈ addPeriodMultiples (Ioo (c - 1 / 2 * d.sideLengths μ) c) (d.sideLengths μ)) ∧
    (x ∈ hyperplane d.sideLengths μ c ↔ y μ ∈ addPeriodMultiples {c} (d.sideLengths μ)) ∧
    (x ∈ hyperplane d.sideLengths μ (c + 1 / 2 * d.sideLengths μ) ↔
      y μ ∈ addPeriodMultiples {c + 1 / 2 * d.sideLengths μ} (d.sideLengths μ))) ∧
  (⋃ i, partition d μ c i) = univ ∧
  Pairwise fun i j => Disjoint (partition d μ c i) (partition d μ c j)
def ReflectionInvolutive (d : CellGrid L κ) (μ : Fin 4) (c : ℝ) : Prop :=
  descend d (coordReflection μ c) ∘ descend d (coordReflection μ c) = id ∧
  {x | descend d (coordReflection μ c) x = x} = fixedPlanes d μ c
def HalvesAreComponents (d : CellGrid L κ) (μ : Fin 4) (c : ℝ) : Prop :=
  {C | ∃ x ∈ (fixedPlanes d μ c)ᶜ, C = connectedComponentIn (fixedPlanes d μ c)ᶜ x} =
    {posHalf d μ c, negHalf d μ c} ∧
  posHalf d μ c ≠ negHalf d μ c ∧
  IsOpen (posHalf d μ c) ∧ IsOpen (negHalf d μ c) ∧
  descend d (coordReflection μ c) '' posHalf d μ c = negHalf d μ c ∧
  descend d (coordReflection μ c) '' negHalf d μ c = posHalf d μ c
def ShiftedMirrorAgrees (d : CellGrid L κ) (μ : Fin 4) (c : ℝ) : Prop :=
  d.IsInducedMap (descend d (coordReflection μ c)) (coordReflection μ (c + 1 / 2 * d.sideLengths μ)) ∧
  posHalf d μ (c + 1 / 2 * d.sideLengths μ) = negHalf d μ c ∧
  negHalf d μ (c + 1 / 2 * d.sideLengths μ) = posHalf d μ c
def DescentTheorem : Prop :=
  ∀ (L : ℕ) (κ : ℤ) (d : CellGrid L κ),
    ProjectionContinuousOpen d ∧ SignAffineIsGroup ∧ DescentProperties d ∧
      DescentImageRules d ∧
      ∀ (μ : Fin 4) (c : ℝ), coordReflection μ c ∈ signAffineGroup ∧ LiftCharacterization d μ c ∧
        ReflectionInvolutive d μ c ∧ HalvesAreComponents d μ c ∧
        ShiftedMirrorAgrees d μ c
end YangMills.Construction.TorusDescent
end
