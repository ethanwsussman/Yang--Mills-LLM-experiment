import YangMills.Construction.Coordinates.BoundedHolomorphicLipschitz
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Coordinates.ComplexCoordinates.BoundedHolomorphicLipschitz
open PowerSeriesHolomorphy
variable {n : ℕ}
theorem differentiableAt_comp_update {O : Set (ComplexCoordinates n)} {f : ComplexCoordinates n → ℂ}
    (hf : IsHolomorphicIn (N' := 1) O (fun z _ => f z)) (y : ComplexCoordinates n) (k : Fin n)
    (w : ℂ) (hw : Function.update y k w ∈ O) :
    DifferentiableAt ℂ (fun ζ : ℂ => f (Function.update y k ζ)) w := by
  obtain ⟨-, -, h⟩ := hf
  have h0 := (h _ hw k).self_of_nhds
  have h1 : DifferentiableAt ℂ
      (fun ζ : ℂ => f (Function.update y k w + ζ • stdBasisVector k)) (w - w) := by
    rw [sub_self]
    exact (differentiableAt_pi.1 h0) 0
  have h2 : DifferentiableAt ℂ (fun ζ : ℂ => ζ - w) w := by fun_prop
  have h3 : DifferentiableAt ℂ
      ((fun ζ : ℂ => f (Function.update y k w + ζ • stdBasisVector k)) ∘ fun ζ : ℂ => ζ - w) w :=
    DifferentiableAt.comp w h1 h2
  have h4 : ((fun ζ : ℂ => f (Function.update y k w + ζ • stdBasisVector k)) ∘
      fun ζ : ℂ => ζ - w) = fun ζ : ℂ => f (Function.update y k ζ) := by
    funext ζ
    simp only [Function.comp]
    congr 1
    funext j
    by_cases hj : j = k
    · subst hj
      simp [stdBasisVector]
    · simp [stdBasisVector, Function.update_of_ne hj, Pi.single_eq_of_ne hj]
  rwa [h4] at h3
theorem update_mem_closedPolydisk {a y : ComplexCoordinates n} {r R : ℝ}
    (hy : y ∈ closedPolydisk a r) (hrR : r ≤ R) (k : Fin n) {v : ℂ} (hv : ‖v - a k‖ ≤ R) :
    Function.update y k v ∈ closedPolydisk a R := by
  intro j
  by_cases hj : j = k
  · subst hj
    simpa using hv
  · rw [Function.update_of_ne hj]
    exact (hy j).trans hrR
theorem norm_sub_update_le_mul {O : Set (ComplexCoordinates n)} {f : ComplexCoordinates n → ℂ}
    {b ρ : ℝ} {a : ComplexCoordinates n} (hf : IsHolomorphicIn (N' := 1) O (fun z _ => f z))
    (hb : ∀ z ∈ O, ‖f z‖ ≤ b) (hρ : 0 < ρ) (hsub : closedPolydisk a (2 * ρ) ⊆ O)
    {y : ComplexCoordinates n} (hy : y ∈ closedPolydisk a ρ) (k : Fin n) {w : ℂ}
    (hw : ‖w - a k‖ ≤ ρ) :
    ‖f (Function.update y k w) - f y‖ ≤ b / ρ * ‖w - y k‖ := by
  have hρ2 : ρ ≤ 2 * ρ := by linarith
  have hin : ∀ v : ℂ, ‖v - a k‖ ≤ 2 * ρ → Function.update y k v ∈ O := fun v hv =>
    hsub (update_mem_closedPolydisk hy hρ2 k hv)
  have hdiff : ∀ v : ℂ, ‖v - a k‖ ≤ 2 * ρ →
      DifferentiableAt ℂ (fun ζ : ℂ => f (Function.update y k ζ)) v := fun v hv =>
    differentiableAt_comp_update hf y k v (hin v hv)
  have hnear : ∀ u ∈ Metric.closedBall (a k) ρ, ∀ v ∈ Metric.closedBall u ρ,
      ‖v - a k‖ ≤ 2 * ρ := by
    intro u hu v hv
    rw [mem_closedBall_iff_norm] at hu hv
    calc ‖v - a k‖ = ‖(v - u) + (u - a k)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖v - u‖ + ‖u - a k‖ := norm_add_le _ _
      _ ≤ 2 * ρ := by linarith
  have hderiv : ∀ u ∈ Metric.closedBall (a k) ρ,
      ‖deriv (fun ζ : ℂ => f (Function.update y k ζ)) u‖ ≤ b / ρ := by
    intro u hu
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ ?_ ?_
    · refine DifferentiableOn.diffContOnCl_ball (U := Metric.closedBall u ρ) ?_ subset_rfl
      intro v hv
      exact (hdiff v (hnear u hu v hv)).differentiableWithinAt
    · intro v hv
      exact hb _ (hin v (hnear u hu v (Metric.sphere_subset_closedBall hv)))
  have hmem : ∀ v : ℂ, ‖v - a k‖ ≤ ρ → v ∈ Metric.closedBall (a k) ρ := fun v hv =>
    mem_closedBall_iff_norm.2 hv
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun ζ : ℂ => f (Function.update y k ζ)) (s := Metric.closedBall (a k) ρ)
    (fun u hu => hdiff u ((mem_closedBall_iff_norm.1 hu).trans hρ2)) hderiv
    (convex_closedBall _ _) (hmem _ (hy k)) (hmem _ hw)
  simpa using hmv
theorem bound_holds : Bound := by
  intro n _ O _ f b hf hb ρ a hρ2 ha hsub z hz z' hz'
  have hρ : 0 < ρ := by linarith
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb a ha)
  have hC : b / ρ ≤ 2 * b / ρ := by
    apply div_le_div_of_nonneg_right _ hρ.le
    linarith
  have key : ∀ s : Finset (Fin n),
      ‖f z - f (fun j => if j ∈ s then z' j else z j)‖ ≤ b / ρ * ∑ k ∈ s, ‖z k - z' k‖ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert k s hk ih =>
      have hy : (fun j => if j ∈ s then z' j else z j) ∈ closedPolydisk a ρ := by
        intro j
        by_cases hj : j ∈ s
        · simpa [hj] using hz' j
        · simpa [hj] using hz j
      have hstep := norm_sub_update_le_mul hf hb hρ hsub hy k (hz' k)
      have hupd : Function.update (fun j => if j ∈ s then z' j else z j) k (z' k) =
          fun j => if j ∈ insert k s then z' j else z j := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp
        · simp [Finset.mem_insert, hj]
      rw [hupd] at hstep
      have hyk : (if k ∈ s then z' k else z k) = z k := if_neg hk
      rw [hyk, norm_sub_rev (z' k) (z k)] at hstep
      rw [Finset.sum_insert hk, mul_add]
      calc _ ≤ ‖f z - f (fun j => if j ∈ s then z' j else z j)‖ +
            ‖f (fun j => if j ∈ s then z' j else z j) -
              f (fun j => if j ∈ insert k s then z' j else z j)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := by
          rw [norm_sub_rev (f (fun j => if j ∈ s then z' j else z j))]
          linarith
  have hall := key Finset.univ
  simp only [Finset.mem_univ, if_true] at hall
  exact hall.trans (mul_le_mul_of_nonneg_right hC (Finset.sum_nonneg fun _ _ => norm_nonneg _))
end YangMills.Construction.Coordinates.ComplexCoordinates.BoundedHolomorphicLipschitz
