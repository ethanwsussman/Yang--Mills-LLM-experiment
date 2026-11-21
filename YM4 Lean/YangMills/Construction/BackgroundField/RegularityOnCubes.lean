import YangMills.Construction.BackgroundField.GaugeFixedOperators
import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.BackgroundField
variable {L m t : ℕ}
def coarseCubeUnion (K j e n : ℕ) (y : Site L m (scaledCubeIndex K j e)) :
    Set (FourTorus L m) :=
  ⋃ a : Fin 4 → Fin n,
    cubeAround (y + ∑ μ, (a μ : ℕ) • unitStep L m (scaledCubeIndex K j e) μ)
variable (𝔰 : NestedRegions L m t)
def IsShellCube (e K : ℕ) (c : ℝ) (j : ℕ) (Q : Set (FourTorus L m)) : Prop :=
  ∃ (n : ℕ) (y : Site L m (scaledCubeIndex K j e)), 1 ≤ n ∧ (n : ℝ) ≤ c ∧
    -(m : ℤ) ≤ scaledCubeIndex K j e ∧
    (n : ℝ) * meshSize L (scaledCubeIndex K j e) < torusSide L m ∧
    Q = coarseCubeUnion K j e n y ∧
    (sitesIn Q : Set (FineSite L m K)) ⊆
      fineBlockUnion (𝔰.shellSites K j) ∪ fineBlockUnion (𝔰.shellSites K (j + 1)) ∧
    ((sitesIn Q : Set (FineSite L m K)) ∩ fineBlockUnion (𝔰.shellSites K j)).Nonempty
def RegularOnShellCubes (e K : ℕ) (c α₀ : ℝ) (U : FineBond L m K → ComplexMatrix2) : Prop :=
  ∀ j ≤ t, ∀ Q, IsShellCube 𝔰 e K c j Q →
    ∃ (u : FineSite L m K → ComplexMatrix2) (A : FineBond L m K → ComplexMatrix2),
      (∀ x ∈ (sitesIn Q : Set (FineSite L m K)), u x ∈ compactGaugeGroup) ∧
      IsBondForm compactLieAlgebra A ∧
      (∀ b ∈ (bondsInside Q : Set (FineBond L m K)),
        gaugeTransform u U b =
          ComplexMatrix2.matExp
            (Complex.I • (((finestMeshInLevelUnits L t : ℝ) : ℂ) • A b)) ∧
        ComplexMatrix2.operatorNorm (A b) < c * (L : ℝ) ^ e * α₀ * (meshAtLevel L t j)⁻¹) ∧
      ∀ (x : FineSite L m K) (μ ν : Fin 4),
        Bond.forwardFrom x μ ∈ (bondsInside Q : Set (FineBond L m K)) →
        Bond.forwardFrom x ν ∈ (bondsInside Q : Set (FineBond L m K)) →
        Bond.forwardFrom (x + unitStep L m (levelDepth K 0) μ) ν ∈
            (bondsInside Q : Set (FineBond L m K)) →
          ComplexMatrix2.operatorNorm
              (covDeriv (finestMeshInLevelUnits L t) trivialGaugeField μ
                (bondFormComponent A ν) x) <
            c * (L : ℝ) ^ e * α₀ * (meshAtLevel L t j ^ 2)⁻¹
end YangMills.Construction.BackgroundField
