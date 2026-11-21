import YangMills.Construction.Lattice.GaugeFieldSpacesAndRealAnalyticMaps
import YangMills.Construction.Matrices.HolomorphicDeterminedNearRealPoint
import YangMills.Construction.Matrices.LogChartsAroundFamily
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Matrices.ConfigurationLogCharts
open YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.LogChartsAroundFamily
variable {σ : Type}
def IsNeighbourhoodBasis {E : Type} [TopologicalSpace E] (P : Set E) (x : E) (ρ : ℝ)
    (N : ℝ → Set E) : Prop :=
  (∀ r, 0 < r → r ≤ ρ → ComplexMatrix2.IsRelativelyOpen P (N r) ∧ x ∈ N r) ∧
    ∀ D : Set E, ComplexMatrix2.IsRelativelyOpen P D → x ∈ D → ∃ r, 0 < r ∧ r ≤ ρ ∧ N r ⊆ D
def logOnProduct (V₀ : σ → ComplexMatrix2) (p : σ ⊕ Empty → ComplexMatrix2) :
    Empty ⊕ σ → ComplexMatrix2 :=
  tracelessPoint (chartLog V₀ fun b => p (.inl b))
def expOnProduct (V₀ : σ → ComplexMatrix2) (q : Empty ⊕ σ → ComplexMatrix2) :
    σ ⊕ Empty → ComplexMatrix2 :=
  asGroupFactors (expTimesUnitaryFamily (fun b => q (.inr b)) V₀)
def NeighbourhoodsBasis (V₀ : σ → ComplexMatrix2) (ρ : ℝ) : Prop :=
  IsNeighbourhoodBasis (unimodularPi σ) V₀ ρ (fun r => chartNeighbourhood r V₀) ∧
    IsNeighbourhoodBasis (compactPi σ) V₀ ρ fun r => chartNeighbourhood r V₀ ∩ compactPi σ
def LogHolomorphic [Fintype σ] (V₀ : σ → ComplexMatrix2) (ρ : ℝ) : Prop :=
  MapsTo (chartLog V₀) (chartNeighbourhood ρ V₀)
      (tracelessFunctions σ : Set (σ → ComplexMatrix2)) ∧
    ∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
      IsHolomorphicToProduct b (asGroupFactors '' chartNeighbourhood ρ V₀) (logOnProduct V₀)
def LeftInverseOfExp (V₀ : σ → ComplexMatrix2) (ρ : ℝ) : Prop :=
  (∀ W ∈ chartNeighbourhood ρ V₀,
    expTimesUnitaryFamily (chartLog V₀ W) V₀ = W ∧ supNorm (chartLog V₀ W) < -Real.log (1 - ρ)) ∧
    ∀ W ∈ chartNeighbourhood ρ V₀ ∩ compactPi σ, chartLog V₀ W ∈ hermitianTracelessFunctions σ
def ExpRightInverse (V₀ : σ → ComplexMatrix2) (ρ : ℝ) : Prop :=
  ∀ B ∈ tracelessFunctions σ, supNorm B < Real.log (1 + ρ) →
    expTimesUnitaryFamily B V₀ ∈ chartNeighbourhood ρ V₀ ∧
      chartLog V₀ (expTimesUnitaryFamily B V₀) = B
def ExpHolomorphic [Fintype σ] (V₀ : σ → ComplexMatrix2) : Prop :=
  MapsTo (fun B => expTimesUnitaryFamily B V₀) (tracelessFunctions σ : Set (σ → ComplexMatrix2))
      (unimodularPi σ) ∧
    ∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
      IsHolomorphicToProduct b (GroupLieProduct Empty σ) (expOnProduct V₀)
def Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (V₀ : σ → ComplexMatrix2) (ρ : ℝ), IsChartCentre V₀ ρ →
    NeighbourhoodsBasis V₀ ρ ∧ LogHolomorphic V₀ ρ ∧ LeftInverseOfExp V₀ ρ ∧
      ExpRightInverse V₀ ρ ∧ ExpHolomorphic V₀
end YangMills.Construction.Matrices.ConfigurationLogCharts
