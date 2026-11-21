import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.CubePartitionsAndRegions
import YangMills.Construction.Lattice.WeightedWilsonActions
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric PeriodicLattice
namespace PeriodicLattice.CubeGeometry
def MaxNormFacts (L m : ℕ) (i : ℤ) : Prop :=
  (∀ x y : FourTorus L m, torusSupNorm (x + y) ≤ torusSupNorm x + torusSupNorm y) ∧
  (∀ Q ∈ standardCubePartition L m i, ∀ p ∈ Q, ∀ p' ∈ Q, torusSupNorm (p - p') ≤ meshSize L i) ∧
  ∀ A B : Set (FourTorus L m), A.Nonempty → B.Nonempty → IsCompact A → IsCompact B →
    ∃ a ∈ A, ∃ b ∈ B, setSupDist A B = ENNReal.ofReal (torusSupNorm (a - b))
def CubesCoverTorus (L m : ℕ) (i : ℤ) : Prop :=
  ⋃₀ standardCubePartition L m i = univ ∧
  (∀ Q ∈ standardCubePartition L m i, ∀ x ∈ interior Q,
    ∀ Q' ∈ standardCubePartition L m i, x ∈ Q' → Q' = Q) ∧
  ∀ X : Set (FourTorus L m), IsPartitionRegion i X → X ∪ complementRegion i X = univ
def CubesNest (L m : ℕ) (i i' : ℤ) : Prop :=
  (∀ Q ∈ standardCubePartition L m i, Q = ⋃₀ partitionCubesIn i' Q) ∧
  ∀ Q' ∈ standardCubePartition L m i', ∃! Q, Q ∈ standardCubePartition L m i ∧ Q' ⊆ Q
def BlocksPartitionSublattice (L m : ℕ) (i i' : ℤ) : Prop :=
  (∀ y : Site L m i,
    refinedBlock (i' - i).toNat y = cubeAround y ∩ (sublattice L m i' : Set (FourTorus L m))) ∧
  (∀ y : Site L m i, (refinedBlock (i' - i).toNat y).Nonempty) ∧
  (⋃ y : Site L m i, refinedBlock (i' - i).toNat y) = (sublattice L m i' : Set (FourTorus L m)) ∧
  ∀ y y' : Site L m i, y ≠ y' →
    Disjoint (refinedBlock (i' - i).toNat y) (refinedBlock (i' - i).toNat y')
def centeredBox (v : Fin 4 → ℝ) (a : ℝ) : Set (Fin 4 → ℝ) :=
  TorusBox.boxOfIntervals (fun μ => v μ - a / 2) fun μ => v μ + a / 2
def IsProgressionOfMultiples (a : ℝ) (r : ℕ) (T : Set ℝ) : Prop :=
  ∃ c : ℤ, T = {t | ∃ n : ℕ, n < r ∧ t = ((c : ℝ) + (n : ℝ)) * a}
def BlocksInChart (L m : ℕ) (i i' : ℤ) : Prop :=
  ∀ (y : Site L m i) (v : Fin 4 → ℝ), torusProj (torusSide L m) v = (y : FourTorus L m) →
    InjOn (torusProj (torusSide L m)) (centeredBox v (meshSize L i)) ∧
    ∃ T : Fin 4 → Set ℝ,
      (∀ μ, IsProgressionOfMultiples (meshSize L i') (L ^ (i' - i).toNat) (T μ)) ∧
      pi univ T ⊆ centeredBox v (meshSize L i) ∧
      torusProj (torusSide L m) '' pi univ T = refinedBlock (i' - i).toNat y
def TraceRealityAndPlaquettes (L m K : ℕ) : Prop :=
  (∀ V ∈ Matrices.ComplexMatrix2.specialUnitary, (Matrices.ComplexMatrix2.fullTrace V).im = 0) ∧
  ∀ U ∈ compactGaugeFields L m (K : ℤ),
    (∀ p : Plaquette L m (K : ℤ), ((plaquetteCost U p : ℝ) : ℂ) = plaquetteEnergy U p) ∧
    wilsonAction U = ∑ᶠ p : Plaquette L m (K : ℤ), plaquetteCost U p ∧
    ((wilsonAction U : ℝ) : ℂ) = ∑ᶠ p : Plaquette L m (K : ℤ), plaquetteEnergy U p
def ElementaryLatticeFacts : Prop :=
  ∀ s : Conventions.StandingParameters,
    (∀ i i' : ℤ, -((s.m : ℕ) : ℤ) ≤ i → i ≤ i' →
      MaxNormFacts s.L s.m i ∧
      CubesCoverTorus s.L s.m i ∧
      CubesNest s.L s.m i i' ∧
      BlocksPartitionSublattice s.L s.m i i' ∧
      BlocksInChart s.L s.m i i') ∧
    TraceRealityAndPlaquettes s.L s.m s.K
end PeriodicLattice.CubeGeometry
end YangMills.Construction
end
