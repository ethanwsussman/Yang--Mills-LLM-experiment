import YangMills.Construction.BackgroundField.GaugeFixedOperators
import YangMills.Construction.Lattice.DirichletOperatorsOfASeparatedSequence
import YangMills.Construction.Lattice.GeometryOfASeparatedSequence
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators FiniteDimReal RealInnerForms
noncomputable section
namespace SeparatedSequences.BaseParameters
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus) (φ : BondFrame)
def weightedSquareSumOnLayerBlocks (n : ℕ) (f : ZeroForms D.L D.m D.K) : ℝ :=
  ∑ᶠ x : {x : BareSite D.L D.m D.K // (x : D.Torus) ∈ refinedBlockUnion n (D.layerSites Ω n)},
    D.levelMeshRatio 0 ^ BaseParameters.dimension * |f x.1| ^ 2
def MassiveZeroOperatorLowerBound (c : ℕ → ℝ) : Prop :=
  ∀ f : ↥(zeroFormsOn D.K (Ω 0)),
    ∑ n ∈ Finset.range (D.t + 1), min (D.levelWeight n) (c n) * (D.levelMeshRatio n ^ 2)⁻¹ *
        D.weightedSquareSumOnLayerBlocks Ω n f.1 ≤
      D.restrictedZeroInner Ω f (D.massiveZeroOperator Ω f)
def LaplacianLowerBoundOnAverageZeroKernel (c : ℕ → ℝ) : Prop :=
  ∀ f ∈ D.averageZeroKernel Ω,
    ∑ n ∈ Finset.Icc 1 D.t, c n * (D.levelMeshRatio n ^ 2)⁻¹ *
        D.weightedSquareSumOnLayerBlocks Ω n f.1 ≤
      D.restrictedZeroInner Ω f (dirichletLaplacian D.K D.t (Ω 0) f)
def blockSpectralGap (n : ℕ) : ℝ :=
  4 * (D.L : ℝ) ^ (2 * n) * Real.sin (Real.pi / (2 * (D.L : ℝ) ^ n)) ^ 2
def blockSpectralGapExtended (n : ℕ) : ℝ := if n = 0 then 4 else D.blockSpectralGap n
structure ZeroOperatorBounds : Prop where
  massive_bound : D.MassiveZeroOperatorLowerBound Ω fun _ => 4
  laplacian_bound : D.LaplacianLowerBoundOnAverageZeroKernel Ω fun _ => 4
  massive_bound_sharper : D.MassiveZeroOperatorLowerBound Ω D.blockSpectralGapExtended
  laplacian_bound_sharper : D.LaplacianLowerBoundOnAverageZeroKernel Ω D.blockSpectralGap
  four_le_blockSpectralGap : ∀ n, 1 ≤ n → n ≤ D.t → 4 ≤ D.blockSpectralGap n
  blockSpectralGap_lt : ∀ n, 1 ≤ n → n ≤ D.t → D.blockSpectralGap n < Real.pi ^ 2
  massive_positive : IsPosDefFor (D.restrictedZeroInner Ω) (D.massiveZeroOperator Ω)
  massive_invertible : IsUnit (D.massiveZeroOperator Ω)
  green_positive : IsPosDefFor (D.restrictedZeroInner Ω) (D.zeroGreen Ω)
  laplacian_injective :
    InjOn (dirichletLaplacian D.K D.t (Ω 0)) (D.averageZeroKernel Ω : Set ↥(zeroFormsOn D.K (Ω 0)))
structure AverageZeroProperties : Prop where
  adjoint_apply : ∀ (ω : D.CoarseZeroForms Ω) (x : BareSite D.L D.m D.K),
    x ∈ sitesOfRegion D.K (Ω 0) →
    (D.averageZeroAdjoint Ω ω).1 x = pointValue ω ((D.blockCentre Ω (x : D.Torus)).2 : D.Torus)
  average_comp_adjoint : D.averageZero Ω ∘ₗ D.averageZeroAdjoint Ω = LinearMap.id
  surjective : Function.Surjective (D.averageZero Ω)
  green_sq_positive :
    IsPosDefFor (D.coarseZeroInner Ω) (D.averagedZeroGreenSq Ω)
  green_positive : IsPosDefFor (D.coarseZeroInner Ω)
    (D.averageZero Ω ∘ₗ D.zeroGreen Ω ∘ₗ D.averageZeroAdjoint Ω)
structure ClosedOneFormsWithZeroAverage : Prop where
  eq_image : {A : ↥(oneFormsOn D.K (Ω 0) φ) | curl D.t A.1 = 0 ∧ D.averageOne Ω φ A = 0} =
    dirichletGrad D.K D.t (Ω 0) φ '' (D.averageZeroKernel Ω : Set ↥(zeroFormsOn D.K (Ω 0)))
  injective : InjOn (dirichletGrad D.K D.t (Ω 0) φ)
    (D.averageZeroKernel Ω : Set ↥(zeroFormsOn D.K (Ω 0)))
structure OneOperatorProperties : Prop where
  massive_positive :
    IsPosDefFor (D.restrictedOneInner Ω φ) (D.massiveOneOperator Ω φ)
  massive_invertible : IsUnit (D.massiveOneOperator Ω φ)
  green_positive : IsPosDefFor (D.restrictedOneInner Ω φ) (D.oneGreen Ω φ)
  surjective : Function.Surjective (D.averageOne Ω φ)
  averaged_green_positive :
    IsPosDefFor (D.coarseOneInner Ω φ) (D.averagedOneGreen Ω φ)
structure OperatorsWellDefined : Prop where
  averaged_zero_green_sq_invertible : IsUnit (D.averagedZeroGreenSq Ω)
  averaged_one_green_invertible : IsUnit (D.averagedOneGreen Ω φ)
  zero_adjoint : IsAdjointFor (D.restrictedZeroInner Ω) (D.coarseZeroInner Ω)
    (D.averageZero Ω) (D.averageZeroAdjoint Ω)
  one_adjoint : IsAdjointFor (D.restrictedOneInner Ω φ) (D.coarseOneInner Ω φ)
    (D.averageOne Ω φ) (D.averageOneAdjoint Ω φ)
  gauge_projection : IsOrthogonalProjectionFor (D.restrictedZeroInner Ω)
    (D.laplacianImageOfAverageZeroKernel Ω) (D.gaugeRangeProjection Ω)
  coarse_zero_projection : IsOrthogonalProjectionFor (D.coarseZeroInner (D.withWholeTorus Ω))
    (D.coarseZeroSupported Ω) (D.coarseZeroSupportProjection Ω)
  coarse_one_projection : IsOrthogonalProjectionFor (D.coarseOneInner (D.withWholeTorus Ω) φ)
    (D.coarseOneSupported Ω φ) (D.coarseOneSupportProjection Ω φ)
def constantWholeTorus : ℕ → Set D.Torus := fun _ => univ
def IsSineInFirstCoordinate (s : ℝ) (f : ZeroForms D.L D.m D.K) : Prop :=
  ∀ (x : BareSite D.L D.m D.K) (r : ℝ), (r : AddCircle (torusSide D.L D.m)) = (x : D.Torus) 0 →
    f x = Real.sin (Real.pi * (D.lengthInUnits r - s))
def HasSineRayleighQuotient (f : ZeroForms D.L D.m D.K) : Prop :=
  latticeInner D.L D.t f (scalarLaplacian D.L D.m D.K D.t f) =
      4 * (D.levelMeshRatio 0 ^ 2)⁻¹ * Real.sin (Real.pi * D.levelMeshRatio 0 / 2) ^ 2 *
        latticeInner D.L D.t f f ∧
    4 * (D.levelMeshRatio 0 ^ 2)⁻¹ * Real.sin (Real.pi * D.levelMeshRatio 0 / 2) ^ 2 *
        latticeInner D.L D.t f f <
      Real.pi ^ 2 * (D.levelMeshRatio D.t ^ 2)⁻¹ * latticeInner D.L D.t f f
def CornerBlockAveragesZero (f : ZeroForms D.L D.m D.K) : Prop :=
  ∀ n ≤ D.t, ∀ y ∈ D.layerSites Ω n,
    ((D.L : ℝ) ^ (n * BaseParameters.dimension))⁻¹ *
      ∑ᶠ x : {x : BareSite D.L D.m D.K //
          (x : D.Torus) ∈ BackgroundField.blockFromCorner D.L D.m D.K 0 n (y : D.Torus)},
        f x.1 = 0
structure LaplacianBoundFailsAtPiSq : Prop where
  separated : SeparatedSequences.IsBlockUnion D.scales D.t (univ : Set D.Torus) →
    SeparatedSequences.IsSeparatedSequence D.scales (D.gapSize : ℝ) D.constantWholeTorus
  sine : ∃ f : ↥(zeroFormsOn D.K (D.constantWholeTorus 0)), D.IsSineInFirstCoordinate 0 f.1 ∧
    f ∈ D.averageZeroKernel D.constantWholeTorus ∧ D.HasSineRayleighQuotient f.1
  shifted_sine : ∃ f : ↥(zeroFormsOn D.K (D.constantWholeTorus 0)),
    D.IsSineInFirstCoordinate ((1 - D.levelMeshRatio 0) / 2) f.1 ∧
      D.CornerBlockAveragesZero D.constantWholeTorus f.1 ∧ D.HasSineRayleighQuotient f.1
  bound_fails :
    ¬ D.LaplacianLowerBoundOnAverageZeroKernel D.constantWholeTorus fun _ => Real.pi ^ 2
end SeparatedSequences.BaseParameters
def SeparatedSequences.OperatorExistenceStatement : Prop :=
  (∀ (D : SeparatedSequences.SequenceDatum) (φ : BondFrame),
    D.ZeroOperatorBounds D.region ∧ D.AverageZeroProperties D.region ∧
      D.ClosedOneFormsWithZeroAverage D.region φ ∧ D.OneOperatorProperties D.region φ ∧
      D.OperatorsWellDefined D.region φ) ∧
    ∀ D : SeparatedSequences.BaseParameters, 1 ≤ D.t → D.LaplacianBoundFailsAtPiSq
end
end YangMills.Construction
