import YangMills.Construction.ReflectionPositivity.LatticeRepresentativesAndLatticeApproximations
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AdicLattices
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Mirrors (ReflectingHyperplane sixteenNormals)
open YangMills.Construction.PeriodicLattice (adicGridPoints meshSize)
open YangMills.Construction.SeparatedTuples (IsAdicPlaced latticeSpacing scaleLattice posAdicGridPoints)
variable (L : ℕ) (K : ℕ+ → ℕ+)
def NestedScales : Prop :=
  ∀ j : ℕ+,
    latticeSpacing L (K j) / latticeSpacing L (K (j + 1)) =
        (L : ℝ) ^ ((K (j + 1) : ℕ) - (K j : ℕ)) ∧
      0 < (K (j + 1) : ℕ) - (K j : ℕ) ∧
      scaleLattice L (K j) ≤ scaleLattice L (K (j + 1))
def MultiplesUnionAgree : Prop :=
  (⋃ k : ℕ, {x : ℝ | ∃ n : ℤ, x = (n : ℝ) * meshSize L (k : ℤ)}) =
    ⋃ j : ℕ+, {x : ℝ | ∃ n : ℤ, x = (n : ℝ) * latticeSpacing L (K j)}
def AdicDenseSubgroup : Prop :=
  (∃ G : AddSubgroup ℝ, (G : Set ℝ) = adicGridPoints L) ∧
    Dense (adicGridPoints L) ∧
    Set.Ioi (0 : ℝ) ⊆ closure (posAdicGridPoints L) ∧
    AccPt (0 : ℝ) (𝓟 (posAdicGridPoints L))
def AdicPointsEventuallyOnLattice : Prop :=
  ∀ x : AmbientSpace, (∀ μ, x μ ∈ adicGridPoints L) →
    ∃ j₀ : ℕ+, ∀ j, j₀ ≤ j → x ∈ scaleLattice L (K j)
def AdicTimesEventuallyMultiples : Prop :=
  ∀ t ∈ posAdicGridPoints L,
    ∃ j₀ : ℕ+, ∀ j, j₀ ≤ j → ∃ m : ℕ, 0 < m ∧ t / latticeSpacing L (K j) = (m : ℝ)
def AdicHyperplanesLatticeSymmetric : Prop :=
  ∀ H : ReflectingHyperplane,
    (IsAdicPlaced L H ↔ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → H.IsLatticeSymmetric (meshSize L (k : ℤ))) ∧
      (IsAdicPlaced L H ↔ ∃ k : ℕ, H.IsLatticeSymmetric (meshSize L (k : ℤ))) ∧
      (IsAdicPlaced L H →
        ∃ j₀ : ℕ+, ∀ j, j₀ ≤ j → H.IsLatticeSymmetric (latticeSpacing L (K j)))
def AdicApproxFromBelow : Prop :=
  ∀ c : ℝ, ∃ c' : ℕ+ → ℝ,
    (∀ r, c' r ∈ adicGridPoints L ∧ c' r ≤ c) ∧
      Tendsto c' atTop (𝓝 c) ∧
      ∀ (n : AmbientSpace) (hn : n ∈ sixteenNormals) (r : ℕ+), IsAdicPlaced L ⟨n, hn, c' r⟩
def HyperplanesApproxFromBelow : Prop :=
  ∀ H : ReflectingHyperplane, ∃ H' : ℕ+ → ReflectingHyperplane,
    (∀ r, (H' r).normalVec = H.normalVec ∧ IsAdicPlaced L (H' r) ∧
        (H' r).offset ≤ H.offset) ∧
      Tendsto (fun r => (H' r).offset) atTop (𝓝 H.offset)
def Assertion : Prop :=
  ∀ L : ℕ, 13 ≤ L → ∀ K : ℕ+ → ℕ+, StrictMono K →
    NestedScales L K ∧
      MultiplesUnionAgree L K ∧
      AdicDenseSubgroup L ∧
      AdicPointsEventuallyOnLattice L K ∧
      AdicTimesEventuallyMultiples L K ∧
      AdicHyperplanesLatticeSymmetric L K ∧
      AdicApproxFromBelow L ∧
      HyperplanesApproxFromBelow L
end YangMills.Construction.ReflectionPositivity.AdicLattices
