import YangMills.Construction.InfiniteLattice.MeanPlaquetteActionAndRiemannSumsOfACutoff
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
abbrev realRiemannSum (L K : ℕ) (F : AmbientSpace → ℝ) : ℂ :=
  refinedRiemannSum L K fun y => (F y : ℂ)
theorem finite_shifted_latticePoints_ne_zero {a : ℝ} (ha : 0 < a) {F : AmbientSpace → ℝ}
    (hF : HasCompactSupport F) (v : AmbientSpace) :
    {x : LatticePoint a | F ((x : AmbientSpace) + v) ≠ 0}.Finite := by
  obtain ⟨R, hR⟩ := hF.isCompact.isBounded.subset_closedBall (0 : AmbientSpace)
  set M : ℤ := ⌈(R + ‖v‖) / a⌉ with hM
  have hbox : (Set.Icc (fun _ => -M) (fun _ => M) : Set (Fin 4 → ℤ)).Finite := Set.finite_Icc _ _
  let g : (Fin 4 → ℤ) → LatticePoint a := fun n => ⟨fun μ => (n μ : ℝ) * a, n, fun _ => rfl⟩
  refine (hbox.image g).subset fun x hx => ?_
  obtain ⟨n, hn⟩ := x.2
  have hmem : (x : AmbientSpace) + v ∈ Metric.closedBall (0 : AmbientSpace) R :=
    hR (subset_tsupport F (Function.mem_support.mpr hx))
  have hnorm : ‖(x : AmbientSpace) + v‖ ≤ R := by simpa using hmem
  have hbound : ∀ μ, |(n μ : ℝ)| ≤ (M : ℝ) := fun μ => by
    have h1 : |(x : AmbientSpace) μ + v μ| ≤ R :=
      (norm_le_pi_norm ((x : AmbientSpace) + v) μ).trans hnorm
    have h2 : |v μ| ≤ ‖v‖ := norm_le_pi_norm v μ
    have h3 : |(x : AmbientSpace) μ| ≤ R + ‖v‖ := by
      have := abs_sub ((x : AmbientSpace) μ + v μ) (v μ)
      simp only [add_sub_cancel_right] at this
      linarith
    rw [hn μ, abs_mul, abs_of_pos ha] at h3
    exact ((le_div_iff₀ ha).mpr h3).trans (Int.le_ceil _)
  refine ⟨n, ⟨fun μ => ?_, fun μ => ?_⟩, Subtype.ext (funext fun μ => (hn μ).symm)⟩
  · have := (abs_le.mp (hbound μ)).1
    exact_mod_cast this
  · have := (abs_le.mp (hbound μ)).2
    exact_mod_cast this
end YangMills.Construction.InfiniteLattice
end
