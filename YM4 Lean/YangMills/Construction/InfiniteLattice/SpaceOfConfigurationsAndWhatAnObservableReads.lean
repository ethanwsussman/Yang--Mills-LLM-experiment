import YangMills.Construction.InfiniteLattice.ObservablesHypercubicLatticeMapsAndHyperplanes
import YangMills.Construction.InfiniteLattice.OneLatticeItsConfigurationsAndMeasuresOnCompactSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter YangMills.Construction.InfiniteLattice
open scoped Topology ComplexConjugate
noncomputable section
namespace YangMills.Construction.LatticePhases.ObservableRegions
variable (D : Setup)
def scaledCube (j : ℕ) : Set AmbientSpace :=
  {x | ∀ μ, x μ ∈ Icc (D.mesh * -(j : ℝ)) (D.mesh * (j : ℝ))}
def FieldDistMetrizes : Prop :=
  ∃ m : MetricSpace (GaugeField D.mesh),
    (∀ A B : GaugeField D.mesh, @dist _ m.toDist A B = D.fieldDist A B) ∧
      m.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace (GaugeField D.mesh))
def CompactnessAndTruncation (S : Set AmbientSpace) : Prop :=
  FieldDistMetrizes D ∧
    CompactSpace (GaugeField D.mesh) ∧
    borel (GaugeField D.mesh) = linkSigma (positiveLinks D.mesh) ∧
    Continuous (truncate S : GaugeField D.mesh → GaugeField D.mesh) ∧
    Measurable[regionSigma S] (truncate S : GaugeField D.mesh → GaugeField D.mesh)
def RegionObservableEquivalences (S : Set AmbientSpace) : Prop :=
  ∀ G : GaugeField D.mesh → ℂ, IsBoundedObservable G →
    List.TFAE
      [G ∈ regionObservables D.mesh S,
        ∀ A B : GaugeField D.mesh, (∀ b : Link D.mesh, b ∈ linksWithin S → A b = B b) → G A = G B,
        G = G ∘ truncate S]
def RegionStarSubalgebra (S : Set AmbientSpace) : Prop :=
  (∀ c : ℂ, (fun _ => c) ∈ regionObservables D.mesh S) ∧
    (∀ G ∈ regionObservables D.mesh S, ∀ G' ∈ regionObservables D.mesh S,
      G + G' ∈ regionObservables D.mesh S ∧ G * G' ∈ regionObservables D.mesh S) ∧
    (∀ c : ℂ, ∀ G ∈ regionObservables D.mesh S, c • G ∈ regionObservables D.mesh S) ∧
    ∀ G ∈ regionObservables D.mesh S, (fun A => conj (G A)) ∈ regionObservables D.mesh S
def TruncatedContinuous (S : Set AmbientSpace) : Prop :=
  ∀ G : C(GaugeField D.mesh, ℂ),
    Continuous (G ∘ truncate S) ∧ G ∘ truncate S ∈ regionObservables D.mesh S ∧
      uniformSup (G ∘ truncate S) ≤ uniformSup G
def L2Approximable (S : Set AmbientSpace) : Prop :=
  Bornology.IsBounded S → ∀ σ : ProbMeasure (GaugeField D.mesh), ∀ G ∈ regionObservables D.mesh S,
    ∃ Gs : ℕ+ → GaugeField D.mesh → ℂ,
      (∀ k, Gs k ∈ continuousLocalFunctions D.mesh ∩ regionObservables D.mesh S) ∧
        Tendsto (fun k => σ.eval fun A => ((‖G A - Gs k A‖ ^ 2 : ℝ) : ℂ)) atTop (𝓝 0)
def Statement : Prop :=
  ∀ (D : Setup) (S S' : Set AmbientSpace),
    CompactnessAndTruncation D S ∧
    RegionObservableEquivalences D S ∧
    (RegionStarSubalgebra D S ∧
      (S ⊆ S' → regionObservables D.mesh S ⊆ regionObservables D.mesh S') ∧
      regionObservables D.mesh S ∩ regionObservables D.mesh S' = regionObservables D.mesh (S ∩ S') ∧
      ∀ G : GaugeField D.mesh → ℂ, IsBoundedObservable G → IsLocalObservable G →
        ∃ j : ℕ, 1 ≤ j ∧ G ∈ regionObservables D.mesh (scaledCube D j)) ∧
    TruncatedContinuous D S ∧
    L2Approximable D S
end YangMills.Construction.LatticePhases.ObservableRegions
