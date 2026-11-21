import YangMills.Construction.TwoPoints.ConvolutionIsOfClassC1
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Convolution Pointwise
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
namespace ConvolveC1
theorem convolve_eq_convolution (k φ : AmbientSpace → ℂ) :
    convolve k φ = k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] φ := by
  funext x
  rfl
theorem holds : ConvolveC1.Statement := by
  intro k hk φ hφ
  obtain ⟨hkcont, hkcpt, -⟩ := (mem_ccIn_iff _ _).1 hk
  obtain ⟨hφdiff, hφcpt, -⟩ : ContDiff ℝ 1 φ ∧ IsCompact (tsupport φ) ∧ tsupport φ ⊆ univ := hφ
  have hφsupp : HasCompactSupport φ := hφcpt
  have hsumcpt : IsCompact (tsupport k + tsupport φ) := hkcpt.add hφcpt
  have hinside : tsupport (convolve k φ) ⊆ tsupport k + tsupport φ := by
    rw [convolve_eq_convolution]
    refine closure_minimal ?_ hsumcpt.isClosed
    exact (support_convolution_subset _).trans
      (add_subset_add (subset_tsupport k) (subset_tsupport φ))
  refine ⟨⟨?_, hsumcpt.of_isClosed_subset (isClosed_tsupport _) hinside, subset_univ _⟩, ?_⟩
  · rw [convolve_eq_convolution]
    exact hφsupp.contDiff_convolution_right _ hkcont.locallyIntegrable hφdiff
  · intro z hz
    obtain ⟨y, hy, y', hy', rfl⟩ := mem_add.1 (hinside hz)
    exact ⟨y, hy, y', hy', rfl⟩
end ConvolveC1
end YangMills.Construction.TwoPoints
end
