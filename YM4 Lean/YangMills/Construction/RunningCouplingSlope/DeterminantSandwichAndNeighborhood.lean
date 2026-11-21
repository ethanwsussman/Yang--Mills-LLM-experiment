import Mathlib

namespace YangMills.Construction.RunningCouplingSlope.DirectDeterminants

open Matrix Filter
open scoped Topology

theorem det_ne_zero_of_inverse_sandwich
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Nonempty J]
    (A : Matrix I I ℂ) (B : Matrix J I ℂ) (C : Matrix I J ℂ)
    (h : det (B * A⁻¹ * C) ≠ 0) : det A ≠ 0 := by
  intro hA
  have hi : A⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit A (by simp [hA])
  exact h (by simp [hi])

theorem eventually_det_ne_zero
    {I : Type} [Fintype I] [DecidableEq I] {T : ℝ → ℝ → Matrix I I ℂ}
    (hc : ∀ p q, ContDiffAt ℝ 2 (fun w : ℝ × ℝ => T w.1 w.2 p q) 0)
    (hu : IsUnit (det (T 0 0))) :
    ∀ᶠ w : ℝ × ℝ in 𝓝 0, det (T w.1 w.2) ≠ 0 := by
  have hm : Tendsto (fun w : ℝ × ℝ => T w.1 w.2) (𝓝 0) (𝓝 (T 0 0)) :=
    tendsto_pi_nhds.2 fun p => tendsto_pi_nhds.2 fun q => (hc p q).continuousAt
  have hd : Tendsto (fun w : ℝ × ℝ => det (T w.1 w.2)) (𝓝 0) (𝓝 (det (T 0 0))) :=
    ((continuous_id.matrix_det).tendsto (T 0 0)).comp hm
  exact hd.eventually_ne (isUnit_iff_ne_zero.mp hu)

end YangMills.Construction.RunningCouplingSlope.DirectDeterminants
