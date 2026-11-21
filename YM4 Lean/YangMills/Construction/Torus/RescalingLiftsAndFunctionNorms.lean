import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.TorusAnalysis
open YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions
variable {ℓ : ℝ}
def l1Dist (y y' : Torus4 ℓ) : ℝ := torusL1Norm (y - y')
theorem torusEuclidNorm_eq_sqrt_sum_norm_sq (x : Torus4 ℓ) :
    torusEuclidNorm x = Real.sqrt (∑ μ, ‖x μ‖ ^ 2) := by apply _root_.YangMills.Construction.AmbientPoints.torusEuclidNorm_eq_sqrt <;> assumption
theorem pi_norm_le_torusEuclidNorm (x : Torus4 ℓ) : ‖x‖ ≤ torusEuclidNorm x := by
  rw [torusEuclidNorm_eq_sqrt_sum_norm_sq]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun μ => ?_
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun ν => ‖x ν‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ μ)
theorem torusEuclidNorm_le_two_mul_pi_norm (x : Torus4 ℓ) : torusEuclidNorm x ≤ 2 * ‖x‖ := by
  rw [torusEuclidNorm_eq_sqrt_sum_norm_sq]
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  calc ∑ μ, ‖x μ‖ ^ 2 ≤ ∑ _μ : Fin 4, ‖x‖ ^ 2 :=
        Finset.sum_le_sum fun μ _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x μ) 2
    _ = (2 * ‖x‖) ^ 2 := by simp; ring
@[reducible] def euclidTopology (ℓ : ℝ) : TopologicalSpace (Torus4 ℓ) where
  IsOpen U := ∀ y ∈ U, ∃ r > 0, ∀ y', torusEuclidNorm (y' - y) < r → y' ∈ U
  isOpen_univ := fun _ _ => ⟨1, one_pos, fun _ _ => mem_univ _⟩
  isOpen_inter := by
    intro U V hU hV y hy
    obtain ⟨r, hr, h⟩ := hU y hy.1
    obtain ⟨r', hr', h'⟩ := hV y hy.2
    exact ⟨min r r', lt_min hr hr', fun y' hy' =>
      ⟨h y' (hy'.trans_le (min_le_left _ _)), h' y' (hy'.trans_le (min_le_right _ _))⟩⟩
  isOpen_sUnion := by
    intro 𝒰 h𝒰 y ⟨U, hU, hy⟩
    obtain ⟨r, hr, h⟩ := h𝒰 U hU y hy
    exact ⟨r, hr, fun y' hy' => ⟨U, hU, h y' hy'⟩⟩
theorem euclidTopology_eq_instTopology (ℓ : ℝ) :
    euclidTopology ℓ = (inferInstance : TopologicalSpace (Torus4 ℓ)) := by
  refine TopologicalSpace.ext (funext fun U => propext ?_)
  change (∀ y ∈ U, ∃ r > 0, ∀ y', torusEuclidNorm (y' - y) < r → y' ∈ U) ↔ IsOpen U
  rw [Metric.isOpen_iff]
  constructor
  · intro h y hy
    obtain ⟨r, hr, hU⟩ := h y hy
    refine ⟨r / 2, half_pos hr, fun y' hy' => hU y' ?_⟩
    have hd : ‖y' - y‖ < r / 2 := by simpa [dist_eq_norm] using hy'
    linarith [torusEuclidNorm_le_two_mul_pi_norm (y' - y)]
  · intro h y hy
    obtain ⟨r, hr, hU⟩ := h y hy
    refine ⟨r, hr, fun y' hy' => hU ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    exact (pi_norm_le_torusEuclidNorm _).trans_lt hy'
end YangMills.Construction.TorusAnalysis
end
