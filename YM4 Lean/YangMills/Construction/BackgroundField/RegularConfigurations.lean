import YangMills.Construction.BackgroundField.GaugeFixedOperators
import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices PeriodicLattice
namespace BackgroundField
variable {L m K t : ℕ}
def IsUnionOfPartitionCubes (i : ℤ) (X : Set (FourTorus L m)) : Prop :=
  ∃ C ⊆ {Q | -(m : ℤ) ≤ i ∧ Q ∈ standardCubePartition L m i}, X = ⋃₀ C
def scaledTorusDistance (L K t : ℕ) {m : ℕ} (x y : FourTorus L m) : ℝ :=
  (L : ℝ) ^ (levelDepth K t) * TorusMetric.torusSupNorm (x - y)
structure IsDomainSequence (e r K : ℕ) (D : NestedRegions L m t) : Prop where
  level_le : t ≤ K
  fineSites_eq : ∀ k ≤ t, D.fineSitesOf K k = fineBlockUnion (levelSitesOf k (D.fineSitesOf K k))
  isUnion : ∀ k ≤ t, IsUnionOfPartitionCubes (scaledCubeIndex K k e) (D.regionAt k)
  dist_gt : ∀ k < t, ∀ x : FineSite L m K, x ∉ D.fineSitesOf K k →
    ∀ y ∈ D.fineSitesOf K (k + 1),
      (L : ℝ) ^ r * (L : ℝ) ^ e * meshAtLevel L t k <
        scaledTorusDistance L K t (x : FourTorus L m) (y : FourTorus L m)
def covariantBackwardDifference (t : ℕ) (U : FineBond L m K → ComplexMatrix2) (ν : Fin 4)
    (F : FineSite L m K → ComplexMatrix2) (x : FineSite L m K) : ComplexMatrix2 :=
  ((finestMeshInLevelUnits L t : ℂ))⁻¹ •
    (ComplexMatrix2.conjugateBy (U (Bond.backwardFrom x ν)) (F (x - unitStep L m (levelDepth K 0) ν)) - F x)
def plaquetteCovariantDivergence (t : ℕ) (U : FineBond L m K → ComplexMatrix2)
    (F : FinePlaquette L m K → ComplexMatrix2) (μ : Fin 4) (x : FineSite L m K) : ComplexMatrix2 :=
  ∑ ν : Fin 4,
    if h : ν < μ then covariantBackwardDifference t U ν (fun y => F ⟨y, ν, μ, h⟩) x
    else if h' : μ < ν then -covariantBackwardDifference t U ν (fun y => F ⟨y, μ, ν, h'⟩) x
    else 0
def plaquettesTouching (S : Set (FineSite L m K)) : Set (FinePlaquette L m K) :=
  {p | (p.vertices ∩ S).Nonempty}
variable (D : NestedRegions L m t)
def smallFieldConfigurations (K : ℕ) (α₀ : ℝ) : Set (FineBond L m K → ComplexMatrix2) :=
  {U | IsGaugeField compactGaugeGroup univ U ∧ ∀ k ≤ t,
    (∀ p ∈ plaquettesTouching (D.fineSitesOf K k),
      ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) < α₀ * ((L : ℝ) ^ (2 * k))⁻¹) ∧
    ∀ (x : FineSite L m K) (μ : Fin 4), Bond.forwardFrom x μ ∈ bondsTouching (D.fineSitesOf K k) →
      ComplexMatrix2.operatorNorm (plaquetteCovariantDivergence t U (plaquetteHolonomy U) μ x) <
        α₀ * ((L : ℝ) ^ (2 * k))⁻¹ * (meshAtLevel L t k)⁻¹}
end BackgroundField
end YangMills.Construction
