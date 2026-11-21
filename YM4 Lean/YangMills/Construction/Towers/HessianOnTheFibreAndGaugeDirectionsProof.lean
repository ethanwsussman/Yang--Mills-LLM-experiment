import YangMills.Construction.Towers.ActionAlongACurveInTheLeftChart
import YangMills.Construction.Towers.ContourDerivativeOfGaugeDirections
import YangMills.Construction.Towers.CurvesAndHessianOfTheFibreOfTheIterate
import YangMills.Construction.Towers.GaugeImagesOfCurvesInTheFibre
import YangMills.Construction.Towers.HessianOnAFibreOfTheCriticalBranchProof
import YangMills.Construction.Towers.HessianOnTheFibreAndGaugeDirections
import YangMills.Construction.Towers.MultiplierPairingOfTheChain
import YangMills.Construction.Towers.RealAndCovariantDifferentialsOfTheChain
import YangMills.Construction.Towers.SecondDerivativeOfTheActionInGaugeDirections
import YangMills.Construction.Towers.SecondOrderRelationOnTheFibreOfTheIterate
import YangMills.Construction.Towers.TriangularMapOfTheLayersOfSites
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Tower
namespace FibreHessianProof
theorem traceFinsumPairing_neg_right {ι : Type*} (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f (-g) = -traceFinsumPairing f g := by apply _root_.YangMills.Construction.Tower.FibreHessian.traceFinsumPairing_neg_right <;> assumption
end FibreHessianProof
theorem fibreHessianAndGaugeDirections_holds
    (h1 : HessianAlongGaugeDirection)
    (h2 : FibreCurvesAndHessian)
    (h3 : RealDerivEqComplexAtChainBottom)
    (h4 : LeftChartCurveAction.Statement)
    (h5 : FibreSecondOrderRelation)
    (h6 : ChainMultiplierPairing.Statement)
    (h7 : GaugeImageCurvesInFibre)
    (h8 : GaugeDirectionContourDerivative)
    (h9 : LayerDifferenceTriangular)
    (hY : RealLinearMaps.RealLinearMapsStatement) :
    FibreHessianAndGaugeDirections := by
  intro L n k hL hn hk
  refine ⟨h1 L n k hL hn hk, ?_⟩
  refine Filter.Eventually.mono (Filter.Eventually.and (h2 L n k hL hn hk)
    (Filter.Eventually.and (h3 L n k hL hn hk) (Filter.Eventually.and (h5 L n k hL hn hk)
      (Filter.Eventually.and (h6 L n k hL hn hk) (Filter.Eventually.and (h7 L n k hL hn hk)
        (h8 L n k hL hn hk)))))) ?_
  rintro W ⟨⟨hUc, hcrit, hHess, hcurve, htan⟩, a3, a5, a6, a7, a8⟩
  have killed_mem : ∀ B : edgeFormSpace L n k 0, IsInCovariantIterKernel W B →
      B ∈ LinearMap.ker (topConstraintMap L n k W) := by
    intro B hB
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show (smoothingIterDifferential L n k k (chainBottom W) B : Edge L n k k → ComplexMatrix2) = 0
    rw [a3 k le_rfl B]
    exact hB
  have same_second : ∀ (J : Set ℝ) (f g : ℝ → ℝ), IsOpenIntervalAroundZero J →
      (∀ t ∈ J, f t = g t) → deriv (deriv f) 0 = deriv (deriv g) 0 := by
    intro J f g hJ e
    have hm : J ∈ 𝓝 (0 : ℝ) := hJ.1.mem_nhds hJ.2.2
    have e' : f =ᶠ[𝓝 0] g := Filter.eventually_of_mem hm e
    exact e'.deriv.deriv_eq
  refine ⟨?_, ?_⟩
  · intro B hB
    have hk' := killed_mem B hB
    refine ⟨hk', ?_⟩
    obtain ⟨I, γ, hγ, hγN, hγ0, hγt⟩ := hcurve ⟨B, hk'⟩
    obtain ⟨X, ξ, hX, hlim, ho, hval⟩ := h4 L n k hL hn _ hUc I γ hγ hγ0 B hγt
    have hI : I ∈ 𝓝 (0 : ℝ) := hγ.1.1.1.mem_nhds hγ.1.1.2.2
    have hfib : ∀ᶠ t in 𝓝 (0 : ℝ), smoothingIter L n k k
        (PeriodicLattice.expTwist (X t : Edge L n k 0 → ComplexMatrix2) (chainBottom W)) = W := by
      filter_upwards [hX, hI] with t e ht
      rw [← e]
      exact (hγN ht).2
    have hQ := a5 X B ξ hB hlim ho hfib
    have hH := hHess I γ ⟨B, hk'⟩ hγ hγN hγ0 hγt
    have e6 := a6 ξ
    have hq : restrictToPositiveEdges
        (topConstraintMap L n k W ξ : Edge L n k k → ComplexMatrix2) =
        -iterQuadraticTerm (chainBottom W) B B := by
      funext c
      show (smoothingIterDifferential L n k k (chainBottom W) ξ :
        Edge L n k k → ComplexMatrix2) c = _
      rw [a3 k le_rfl ξ]
      exact hQ c
    rw [hq, FibreHessianProof.traceFinsumPairing_neg_right] at e6
    rw [hH, hval, e6, sub_eq_add_neg]
  · obtain ⟨hstep, htower⟩ := hY L n k hL hn hk
    obtain ⟨T₀, hT₀⟩ := htower.covDiff_isLinear 0 (Nat.zero_le k) _ hUc
    let ι : vertexFunctionsVanishingAtTop L n k →ₗ[ℝ] vertexFunctionSpace L n k 0 :=
      Submodule.inclusion fun l h => h.1
    let D : vertexFunctionsVanishingAtTop L n k →ₗ[ℝ] edgeFormSpace L n k 0 := T₀ ∘ₗ ι
    have hDv : IsGaugeDirectionEmbedding W D := fun κ => hT₀ (ι κ)
    have hgauge : ∀ (κ : vertexFunctionsVanishingAtTop L n k)
        (v : LinearMap.ker (topConstraintMap L n k W)),
        ∃ (hv : D κ + v.1 ∈ LinearMap.ker (topConstraintMap L n k W)),
          fibreRestrictedHessian L n k W ⟨D κ + v.1, hv⟩ = fibreRestrictedHessian L n k W v := by
      intro κ v
      obtain ⟨I, γ, hγ, hγN, hγ0, hγt⟩ := hcurve v
      obtain ⟨J, hJI, hγ', hγ'N, hγ'0, hγ't, hA⟩ := a7 κ I γ hγ hγN hγ0
      obtain ⟨v', hv'⟩ := htan J _ hγ' hγ'N hγ'0
      have hval : (v'.1 : edgeFormSpace L n k 0) = D κ + v.1 := by
        apply Subtype.ext
        have : ((D κ + v.1 : edgeFormSpace L n k 0) : Edge L n k 0 → ComplexMatrix2) =
            D κ + v.1 := rfl
        rw [this, ← hv', hγ't, hγt, hDv κ, add_comm]
      have hmem : D κ + v.1 ∈ LinearMap.ker (topConstraintMap L n k W) := hval ▸ v'.2
      refine ⟨hmem, ?_⟩
      have e₁ := hHess J _ ⟨D κ + v.1, hmem⟩ hγ' hγ'N hγ'0 (by rw [hv', hval])
      have e₂ := hHess I γ v hγ hγN hγ0 hγt
      rw [e₁, e₂]
      refine same_second J _ _ hγ'.1.1 fun t ht => ?_
      exact hA t ht
    have hker : ∀ κ, D κ ∈ LinearMap.ker (topConstraintMap L n k W) := by
      intro κ
      obtain ⟨hv, -⟩ := hgauge κ 0
      simpa using hv
    refine ⟨D, hDv, ⟨hker, ?_⟩, ?_, ?_⟩
    · intro κ B hB
      have hk' := killed_mem B hB
      refine ⟨hk', ?_⟩
      obtain ⟨hv, e⟩ := hgauge κ ⟨B, hk'⟩
      have : (⟨B, hk'⟩ + ⟨D κ, hker κ⟩ : LinearMap.ker (topConstraintMap L n k W)) =
          ⟨D κ + B, hv⟩ := by
        apply Subtype.ext
        exact add_comm _ _
      rw [this]
      exact e
    · intro κ i y x hx hxy
      exact a8 κ (D κ) (hDv κ) i y x hx hxy
    · obtain ⟨T, hT, hdet⟩ := h9 L n k hL hn hk
      refine ⟨T, fun κ => ?_, hdet⟩
      funext i x
      have hxmem : x.1 ∈ {x : Vertex L n k (i : ℕ) | (x : PeriodicLattice.FourTorus L n) ∉
          PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k ((i : ℕ) + 1))} := x.2
      rw [← (hstep (i : ℕ) i.is_lt).iUnion_blocks] at hxmem
      obtain ⟨y, hy, hne⟩ := mem_iUnion.1 hxmem
      rw [hT κ i y x hy hne, a8 κ (D κ) (hDv κ) i y x hy hne]
end YangMills.Construction.Tower
end
