import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.SourcesAndGluing.GridsAndTheirGroups
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesArrays
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesCellAlgebras
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesExpectationsAndObservables
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesGridSidesAndCells
import YangMills.Construction.SourcesAndGluing.SimilarityCarriesTheGroup
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.ReflectionProductsUnderRescaling
theorem transportGaugeField_mem_gaugeFields
    (hSymm : PeriodicLattice.WilsonMeasureIsometryInvariant)
    (hGrid : CubicGridsAndReflectionGroups.Statement) {S : GluingSetup} (G : CubicGrid S)
    (σ : G.reflectionGroup)
    {V : S.PeriodicLink → Matrices.ComplexMatrix2} (hV : V ∈ S.gaugeFields) :
    PeriodicLattice.transportGaugeField (σ : Equiv.Perm S.Torus).symm V ∈
      S.gaugeFields := by
  obtain ⟨⟨n, hn⟩, -⟩ := G.isGridScale
  obtain ⟨-, -, -, -, ⟨-, -, -, hτ, -⟩, -⟩ := hGrid S G n hn
  obtain ⟨τ, hτ⟩ := hτ (σ⁻¹ : G.reflectionGroup).1 (σ⁻¹ : G.reflectionGroup).2
  have hL : 1 < S.L := by
    have := S.isAdmissible.2
    omega
  have hinv : τ.toEquiv = (σ : Equiv.Perm S.Torus).symm := hτ
  have hsub := τ.isSublatticeIsometry_toEquiv
  rw [hinv] at hsub
  exact ((hSymm S.L S.m S.K S.β hL S.m.pos S.K.pos).2.2 _ hsub).2.1 V hV
theorem expectation_congr (hGauge : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    {S : GluingSetup}
    {Φ Χ : (S.PeriodicLink → Matrices.ComplexMatrix2) → ℂ} (h : EqOn Φ Χ S.gaugeFields) :
    S.expectation Φ = S.expectation Χ := by
  have hL : 1 < S.L := by
    have := S.isAdmissible.2
    omega
  have hzero := (hGauge S.L S.m S.K S.β hL S.m.pos S.K.pos).2.2.2.2.2.2.2.2.1
  have hae : ∀ᵐ V ∂(PeriodicLattice.wilsonGibbsMeasure S.L S.m S.K S.β),
      V ∈ PeriodicLattice.compactGaugeFields S.L S.m ((S.K : ℕ) : ℤ) := by
    rw [ae_iff]
    exact hzero
  exact integral_congr_ae (hae.mono fun V hV => h hV)
theorem reflectionProductsClaim_proof (hConj : RescalingConjugatesGroupClaim)
    (hCube : LatticeRescalingCubeAlgebrasClaim)
    (hObs : RescalingKeepsExpectationsAndObservables.Statement)
    (hScale : RescalingKeepsGridScalesAndCubes.Statement)
    (hGrid : CubicGridsAndReflectionGroups.Statement)
    (hSymm : PeriodicLattice.WilsonMeasureIsometryInvariant)
    (hGauge : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    LatticeRescalingReflectionProductsClaim := by
  intro S R G hG n Φ hΦ
  obtain ⟨θ, -, hsign, hconj⟩ := hConj S R G hG
  have hpull := (hCube S R G hG n).2 Φ hΦ
  have hsc : ∀ (σ : G.reflectionGroup)
      (W : R.scaleExponent.target.PeriodicLink → Matrices.ComplexMatrix2),
      W ∈ R.scaleExponent.target.gaugeFields →
      signedCopy (σ : Equiv.Perm S.Torus) Φ (R.pullTorus W) =
        signedCopy (θ σ : Equiv.Perm R.scaleExponent.target.Torus) (R.precompose Φ) W := by
    intro σ W hW
    have e1 := hconj σ (S.pullToTorus Φ) hW
    have e2 := hpull (transportGaugeField_mem_gaugeFields hSymm hGrid (R.mappedGrid G hG) (θ σ) hW)
    change Conventions.signedConj (orientationSign (σ : Equiv.Perm S.Torus)) _ =
      Conventions.signedConj
        (orientationSign (θ σ : Equiv.Perm R.scaleExponent.target.Torus)) _
    rw [hsign σ]
    exact congrArg _ (e1.trans e2.symm)
  have hprod : EqOn (R.precomposeTorus (G.reflectionProduct Φ))
      ((R.mappedGrid G hG).reflectionProduct (R.precompose Φ))
      R.scaleExponent.target.gaugeFields := by
    intro W hW
    change (∏ᶠ σ : G.reflectionGroup, signedCopy (σ : Equiv.Perm S.Torus) Φ (R.pullTorus W)) =
      ∏ᶠ σ : (R.mappedGrid G hG).reflectionGroup,
        signedCopy (σ : Equiv.Perm R.scaleExponent.target.Torus) (R.precompose Φ) W
    rw [finprod_congr fun σ => hsc σ W hW]
    exact finprod_comp_equiv θ.toEquiv
      (f := fun σ : (R.mappedGrid G hG).reflectionGroup =>
        signedCopy (σ : Equiv.Perm R.scaleExponent.target.Torus) (R.precompose Φ) W)
  refine ⟨hprod, ?_⟩
  obtain ⟨⟨n', hn'⟩, -⟩ := G.isGridScale
  obtain ⟨-, -, -, -, -, hfn, -⟩ := hGrid S G n' hn'
  obtain ⟨-, -, hob, -⟩ := hfn n Φ hΦ
  have hex := (hObs S R).1 (G.reflectionProduct Φ) hob
  have hcount := ((hScale S R).1 G.edge G.isGridScale).2.1
  change ‖S.expectation (G.reflectionProduct Φ)‖ ^ (1 / S.cellCount G.edge ^ 4) =
    ‖R.scaleExponent.target.expectation
        ((R.mappedGrid G hG).reflectionProduct (R.precompose Φ))‖ ^
      (1 / R.scaleExponent.target.cellCount ((S.L : ℝ) ^ R.exp * G.edge) ^ 4)
  rw [hex, expectation_congr hGauge hprod, hcount]
end YangMills.Construction.SourcesAndGluing.ReflectionProductsUnderRescaling
end
