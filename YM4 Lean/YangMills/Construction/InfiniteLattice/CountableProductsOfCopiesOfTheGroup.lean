import YangMills.Construction.InfiniteLattice.CopiesOfTheGroupAndBoundedConvergence
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def IsEnumerationDomain (D : Set ℕ) : Prop :=
  D = Set.Ici 1 ∨ ∃ m : ℕ, 1 ≤ m ∧ D = Set.Icc 1 m
def enumDistTerm {J : Type} {D : Set ℕ} (e : D → J) (g h : LinkVariables J) (k : D) : ℝ :=
  (2 : ℝ) ^ (-((k : ℕ) : ℤ)) * groupDist (g (e k)) (h (e k))
def enumDist {J : Type} {D : Set ℕ} (e : D → J) (g h : LinkVariables J) : ℝ :=
  ∑' k : D, enumDistTerm e g h k
def IsTopologyMetric {X : Type*} [TopologicalSpace X] (d : X → X → ℝ) : Prop :=
  (∀ x y, 0 ≤ d x y) ∧ (∀ x y, d x y = 0 ↔ x = y) ∧ (∀ x y, d x y = d y x) ∧
    (∀ x y z, d x z ≤ d x y + d y z) ∧
    ∀ x, (𝓝 x).HasBasis (fun r : ℝ => 0 < r) fun r => {y | d x y < r}
def IsBorelGeneratingPiSystem {X : Type*} [TopologicalSpace X] (S : Set (Set X)) : Prop :=
  IsInterClosed S ∧ univ ∈ S ∧ borel X = MeasurableSpace.generateFrom S
def cylinderBoxes (J : Type) : Set (Set (LinkVariables J)) :=
  {C | ∃ (K : Set J) (E : J → Set Matrices.ComplexMatrix2.specialUnitary), K.Finite ∧
    (∀ i ∈ K, MeasurableSet (E i)) ∧ C = {g | ∀ i ∈ K, g i ∈ E i}}
def splitRectangles {J : Type} (J₁ J₂ : Set J) : Set (Set (LinkVariables J)) :=
  {C | ∃ (B₁ : Set (LinkVariables J₁)) (B₂ : Set (LinkVariables J₂)),
    MeasurableSet[borel (LinkVariables J₁)] B₁ ∧ MeasurableSet[borel (LinkVariables J₂)] B₂ ∧
      C = {g | restrictFamily J₁ g ∈ B₁ ∧ restrictFamily J₂ g ∈ B₂}}
def reindexInvert {J J₀ : Type} (σ : J ≃ J₀) (S : Set J) (g : LinkVariables J) : LinkVariables J₀ :=
  open Classical in fun i => if σ.symm i ∈ S then (g (σ.symm i))⁻¹ else g (σ.symm i)
def CompactMetrizableWithEnumDist (J : Type) : Prop :=
  (CompactSpace (LinkVariables J) ∧ TopologicalSpace.MetrizableSpace (LinkVariables J)) ∧
    ∀ (D : Set ℕ) (e : D ≃ J), Nonempty J → IsEnumerationDomain D →
      (∀ g h : LinkVariables J, Summable (enumDistTerm e g h)) ∧
      IsTopologyMetric (enumDist (J := J) e) ∧
      ∀ (N : ℕ) (g h : LinkVariables J), (∀ k : D, (k : ℕ) ≤ N → g (e k) = h (e k)) →
        enumDist e g h ≤ (2 : ℝ) ^ (1 - (N : ℤ))
def BorelGeneratedByCoordinates (J : Type) : Prop :=
  IsBorelGeneratingPiSystem (cylinderBoxes J) ∧
    borel (LinkVariables J) =
      ⨆ i : J, (borel Matrices.ComplexMatrix2.specialUnitary).comap fun g : LinkVariables J => g i
def SplitsAlongPartition {J : Type} (J₁ J₂ : Set J) : Prop :=
  IsHomeomorph (fun g : LinkVariables J => (restrictFamily J₁ g, restrictFamily J₂ g)) ∧
    IsBorelGeneratingPiSystem (splitRectangles J₁ J₂) ∧
    borel (LinkVariables J₁ × LinkVariables J₂) =
      (borel (LinkVariables J₁)).prod (borel (LinkVariables J₂))
def ContinuousApproxByCylinderFunctions (J : Type) : Prop :=
  ∀ F : LinkVariables J → ℂ, Continuous F → ∀ r : ℝ, 0 < r →
    ∃ K : Set J, K.Finite ∧ ∃ F' : LinkVariables J → ℂ, Continuous F' ∧
      DependsOnlyOnCoords K F' ∧ boundedSupValue (F - F') ≤ r
def HaarInvariantUnderReindexInvert (J : Type) [Finite J] : Prop :=
  (BorelSpace (LinkVariables J) ∧ IsProbabilityMeasure (LinkVariables.haarMeasure J)) ∧
    ∀ (J₀ : Type) [Finite J₀] (σ : J ≃ J₀) (S : Set J),
      Continuous (reindexInvert σ S) ∧
      ∀ Φ : boundedBorelSpace (LinkVariables J₀),
        ∫ g, (Φ : LinkVariables J₀ → ℂ) (reindexInvert σ S g) ∂LinkVariables.haarMeasure J =
          ∫ h, (Φ : LinkVariables J₀ → ℂ) h ∂LinkVariables.haarMeasure J₀
def CountableProductTheorem : Prop :=
  (∀ J : Type, IsAtMostCountable J →
    CompactMetrizableWithEnumDist J ∧
    BorelGeneratedByCoordinates J ∧
    (∀ J₁ J₂ : Set J, Disjoint J₁ J₂ → J₁ ∪ J₂ = univ → SplitsAlongPartition J₁ J₂) ∧
    ContinuousApproxByCylinderFunctions J) ∧
  ∀ (J : Type) [Finite J], HaarInvariantUnderReindexInvert J
end YangMills.Construction.InfiniteLattice
