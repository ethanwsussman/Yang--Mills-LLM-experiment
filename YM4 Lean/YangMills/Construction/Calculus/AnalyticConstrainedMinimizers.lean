import Mathlib
set_option autoImplicit false
open Set
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace ConstrainedMinima
variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]
abbrev tangentKernel (m : E → G) : Submodule ℝ E := LinearMap.ker (fderiv ℝ m 0 : E →ₗ[ℝ] G)
structure IsNondegConstrainedCritical (m : E → G) (f : E → ℝ) : Prop where
  analyticAt_map : AnalyticAt ℝ m 0
  analyticAt_fun : AnalyticAt ℝ f 0
  map_zero : m 0 = 0
  fderiv_surjective : Function.Surjective (fderiv ℝ m 0)
  fderiv_eq_zero : fderiv ℝ f 0 = 0
  hessian_pos : ∀ ξ : E, fderiv ℝ m 0 ξ = 0 → ξ ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) 0 ξ ξ
def restrictToFiber {K : Type} (f : E → ℝ) (c : K → G → E) (Z : G) : K → ℝ := fun x => f (c x Z)
def fiberMinimizer {K : Type} (c : K → G → E) (b : G → K) (Z : G) : E := c (b Z) Z
structure IsMinimizerChart (m : E → G) (f : E → ℝ) (N : Set E) (O : Set (tangentKernel m))
    (W : Set G) (ρ : E →L[ℝ] tangentKernel m) (c : tangentKernel m → G → E)
    (b : G → tangentKernel m) : Prop where
  isOpen_nhd : IsOpen N
  zero_mem_nhd : (0 : E) ∈ N
  isOpen_params : IsOpen O
  zero_mem_params : (0 : tangentKernel m) ∈ O
  convex_params : Convex ℝ O
  isOpen_values : IsOpen W
  zero_mem_values : (0 : G) ∈ W
  analyticOnNhd_map : AnalyticOnNhd ℝ m N
  analyticOnNhd_fun : AnalyticOnNhd ℝ f N
  proj_apply_kernel : ∀ x : tangentKernel m, ρ (x : E) = x
  analyticOnNhd_chart : AnalyticOnNhd ℝ (fun q : tangentKernel m × G => c q.1 q.2) (O ×ˢ W)
  chart_zero_zero : c 0 0 = 0
  chart_mem_nhd : ∀ x ∈ O, ∀ Z ∈ W, c x Z ∈ N
  map_chart : ∀ x ∈ O, ∀ Z ∈ W, m (c x Z) = Z
  proj_chart : ∀ x ∈ O, ∀ Z ∈ W, ρ (c x Z) = x
  chart_surj : ∀ y ∈ N, ρ y ∈ O ∧ m y ∈ W ∧ c (ρ y) (m y) = y
  hessian_pos_params : ∀ Z ∈ W, ∀ x ∈ O, ∀ h : tangentKernel m, h ≠ 0 →
    0 < fderiv ℝ (fderiv ℝ (restrictToFiber f c Z)) x h h
  analyticOnNhd_min : AnalyticOnNhd ℝ b W
  min_zero : b 0 = 0
  min_mem : ∀ Z ∈ W, b Z ∈ O
  fderiv_min_eq_zero : ∀ Z ∈ W, fderiv ℝ (restrictToFiber f c Z) (b Z) = 0
  eq_min_of_critical : ∀ Z ∈ W, ∀ x ∈ O, fderiv ℝ (restrictToFiber f c Z) x = 0 → x = b Z
  min_lt : ∀ Z ∈ W, ∀ x ∈ O, x ≠ b Z → restrictToFiber f c Z (b Z) < restrictToFiber f c Z x
  fderiv_section : ∀ Z : G, fderiv ℝ m 0 (fderiv ℝ (fiberMinimizer c b) 0 Z) = Z
  hessian_orthogonal : ∀ (Z : G) (ξ : tangentKernel m),
    fderiv ℝ (fderiv ℝ f) 0 (fderiv ℝ (fiberMinimizer c b) 0 Z) (ξ : E) = 0
def ExistsMinimizerChart : Prop :=
  ∀ (E G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] (m : E → G) (f : E → ℝ),
    IsNondegConstrainedCritical m f → ∀ T ∈ 𝓝 (0 : E),
      ∃ (N : Set E) (O : Set (tangentKernel m)) (W : Set G)
        (ρ : E →L[ℝ] tangentKernel m)
        (c : tangentKernel m → G → E) (b : G → tangentKernel m),
        IsMinimizerChart m f N O W ρ c b ∧ N ⊆ T
end ConstrainedMinima
end YangMills.Construction
