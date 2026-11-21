import YangMills.Construction.ComplexAnalysis.RealAnalyticInCoordinates
import YangMills.Construction.TwoPoints.ApproximateIdentitiesAndTheirTranslates
import YangMills.Construction.TwoPoints.FormIsTheIntegralOfALocalKernel
import YangMills.Construction.TwoPoints.LimitAtApproximateIdentitiesIsAnalytic
import YangMills.Construction.TwoPoints.LimitAtApproximateIdentitiesIsEvenAndInvariant
import YangMills.Construction.TwoPoints.RealAnalyticKernelOfAForm
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
theorem ofReal_preimage_realLocus_diff_zero :
    (fun (u : Fin 4 → ℝ) (i : Fin 4) => (u i : ℂ)) ⁻¹'
        (Coordinates.ComplexCoordinates.realLocus 4 \ {0}) = {0}ᶜ := by
  ext u
  simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_compl_iff]
  constructor
  · rintro ⟨-, h⟩ rfl
    exact h (by funext i; simp)
  · intro h
    refine ⟨fun i => by simp, fun h0 => h ?_⟩
    funext i
    simpa using congrFun h0 i
theorem isRealAnalyticAwayFromZero_of_analyticOnNhd
    (hA : RealAnalyticity.CoordRealAnalyticIffAnalytic)
    {K : AmbientSpace → ℝ} (hK : AnalyticOnNhd ℝ (fun x => (K x : ℂ)) {0}ᶜ) :
    IsRealAnalyticAwayFromZero K := by
  refine (hA 4 (Coordinates.ComplexCoordinates.realLocus 4 \ {0})
    (fun z => ((K fun i => (z i).re : ℝ) : ℂ)) Set.sdiff_subset).2 ?_
  rw [ofReal_preimage_realLocus_diff_zero]
  refine ⟨isOpen_compl_singleton, ?_⟩
  simpa using hK
theorem AnalyticKernel.proof (hA : RealAnalyticity.CoordRealAnalyticIffAnalytic)
    (hB : MollifierTranslatesDisjoint.Statement)
    (hC : MollifierLimitAnalytic)
    (hD : KernelRepresentsForm.Statement)
    (hE : MollifierLimitSymmetric.Statement) :
    AnalyticKernel.Statement := by
  intro sc S hS hP
  obtain ⟨K, hKan, hKlim, hKloc⟩ := hC sc S hS hP
  have hexists : IsAnalyticKernel S K :=
    { analytic := isRealAnalyticAwayFromZero_of_analyticOnNhd hA hKan
      even := fun ξ h => (hE sc S hS hP K hKlim ξ h).1
      invariant := fun g hg ξ h => (hE sc S hS hP K hKlim ξ h).2 g hg
      represents := fun f hf h hh hd =>
        hD sc S hS hP K hKan.continuousOn hKloc f hf h hh hd
      limit := hKlim }
  have hchosen : IsAnalyticKernel S (analyticKernel S) :=
    Classical.epsilon_spec (p := IsAnalyticKernel S) ⟨K, hexists⟩
  refine ⟨hchosen, hB.2, hB.1, ?_⟩
  intro K' hK' ξ hξ
  obtain ⟨ρ, hρ⟩ := hB.1
  exact tendsto_nhds_unique (hK' ξ hξ ρ hρ) (hchosen.limit ξ hξ ρ hρ)
end YangMills.Construction.TwoPoints
end
