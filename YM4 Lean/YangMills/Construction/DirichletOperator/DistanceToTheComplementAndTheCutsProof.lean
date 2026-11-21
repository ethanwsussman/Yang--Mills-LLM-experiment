import YangMills.Construction.DirichletOperator.DerivativeBoundsOfTheFunctionsOfACubeProof
import YangMills.Construction.DirichletOperator.DistanceToTheComplementAndTheCuts
import YangMills.Construction.PartitionCubes.SmoothedIndicatorDerivBoundsProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction
open Torus
namespace PartitionCubes.OutsideDistanceAndCutoffs
theorem norm_torusProj_le {S : ℝ} (v : Fin 4 → ℝ) : ‖torusProj 4 S v‖ ≤ ‖v‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.norm_torusProj_le <;> assumption
theorem supNorm_eq_norm {S : ℝ} (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
variable (𝒮 : RegionSequence.NestedRegions)
theorem distToOutside_eq_iInf (n : ℕ) (x : 𝒮.Point) :
    distToOutside 𝒮 n x = ⨅ q ∈ closure (𝒮.Ω n)ᶜ, ENNReal.ofReal ‖x - q‖ := by
  simp [distToOutside, supSetDist, supNorm_eq_norm]
theorem distToOutside_le_add (n : ℕ) (x y : 𝒮.Point) :
    distToOutside 𝒮 n x ≤ distToOutside 𝒮 n y + ENNReal.ofReal ‖x - y‖ := by
  rw [← tsub_le_iff_right, distToOutside_eq_iInf 𝒮 n y]
  refine le_iInf₂ fun q hq => ?_
  rw [tsub_le_iff_right, distToOutside_eq_iInf]
  refine (iInf₂_le q hq).trans ?_
  rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖x - q‖ = ‖(y - q) + (x - y)‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _
theorem distToOutside_sub_proj_le (n : ℕ) (x : 𝒮.Point) (v : Fin 4 → ℝ) :
    distToOutside 𝒮 n (x - torusProj 4 𝒮.side v) ≤
      distToOutside 𝒮 n x + ENNReal.ofReal ‖v‖ := by
  refine (distToOutside_le_add 𝒮 n _ x).trans ?_
  gcongr
  rw [sub_sub_cancel_left, norm_neg]
  exact norm_torusProj_le v
theorem distToOutside_le_sub_proj (n : ℕ) (x : 𝒮.Point) (v : Fin 4 → ℝ) :
    distToOutside 𝒮 n x ≤
      distToOutside 𝒮 n (x - torusProj 4 𝒮.side v) + ENNReal.ofReal ‖v‖ := by
  refine (distToOutside_le_add 𝒮 n x (x - torusProj 4 𝒮.side v)).trans ?_
  gcongr
  rw [sub_sub_cancel]
  exact norm_torusProj_le v
theorem ofReal_norm_sub_le_of_dist_lt {ε : ℝ≥0} {x y : 𝒮.Point} (h : dist x y < ε) :
    ENNReal.ofReal ‖y - x‖ ≤ ε := by
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_sub_rev, ← dist_eq_norm]
  exact h.le
theorem isClosed_le_distToOutside (n : ℕ) (c : ℝ≥0∞) :
    IsClosed {x : 𝒮.Point | c ≤ distToOutside 𝒮 n x} := by apply _root_.YangMills.Construction.PartitionCubes.CubeFunctionDerivBounds.isClosed_le_distToOutside <;> assumption
theorem isClosed_distToOutside_le (n : ℕ) (c : ℝ≥0∞) :
    IsClosed {x : 𝒮.Point | distToOutside 𝒮 n x ≤ c} := by
  refine isClosed_of_closure_subset fun x hx => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx ε (by exact_mod_cast hε)
  refine (distToOutside_le_add 𝒮 n x y).trans ?_
  refine add_le_add hy ?_
  rw [norm_sub_rev]
  exact ofReal_norm_sub_le_of_dist_lt 𝒮 hxy
theorem mollifyRadius_pos {K m M R₁ : ℕ} (h : 𝒮.IsLevelUnitChain K m M R₁) (n : ℕ) :
    0 < mollifyRadius 𝒮 M n := by apply _root_.YangMills.Construction.PartitionCubes.CubeFunctionDerivBounds.mollifyRadius_pos <;> assumption
theorem mollifierScaled_eq_zero_of_lt_norm {ρ : ℝ} (hρ : 0 < ρ) {v : Fin 4 → ℝ} (hv : ρ < ‖v‖) :
    mollifierScaled ρ v = 0 := by
  have hn : ρ⁻¹ • v ∉ tsupport mollifierBump := by
    intro hmem
    have h := mollifierBump_spec.support_subset hmem
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hρ.le,
      inv_mul_le_iff₀ hρ, mul_one] at h
    exact absurd h (not_le.2 hv)
  simp [mollifierScaled, image_eq_zero_of_notMem_tsupport hn]
theorem integral_mollifierScaled {ρ : ℝ} (hρ : 0 < ρ) : ∫ v, mollifierScaled ρ v = 1 := by apply _root_.YangMills.Construction.PartitionCubes.SmoothedIndicatorBounds.integral_mollifierScaled <;> assumption
theorem ofReal_three_halves_mul (r : ℝ) (hr : 0 < r) :
    ENNReal.ofReal (3 / 2 * r) = ENNReal.ofReal r + ENNReal.ofReal (r / 2) := by
  rw [← ENNReal.ofReal_add hr.le (by positivity)]
  congr 1
  ring
theorem ofReal_two_mul_eq (r : ℝ) (hr : 0 < r) :
    ENNReal.ofReal (2 * r) = ENNReal.ofReal (3 / 2 * r) + ENNReal.ofReal (r / 2) := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring
variable {𝒮} {M n : ℕ}
theorem levelTransition_eq_zero (hr : 0 < mollifyRadius 𝒮 M n) {x : 𝒮.Point}
    (hx : distToOutside 𝒮 n x < ENNReal.ofReal (mollifyRadius 𝒮 M n)) :
    levelTransition 𝒮 M n x = 0 := by
  unfold levelTransition smoothedIndicator
  have hzero : ∀ v : Fin 4 → ℝ,
      indicator {x | ENNReal.ofReal (3 / 2 * mollifyRadius 𝒮 M n) ≤ distToOutside 𝒮 n x}
        (fun _ => (1 : ℝ)) (x - torusProj 4 𝒮.side v) *
          mollifierScaled (mollifyRadius 𝒮 M n / 2) v = 0 := by
    intro v
    by_cases hv : mollifyRadius 𝒮 M n / 2 < ‖v‖
    · rw [mollifierScaled_eq_zero_of_lt_norm (half_pos hr) hv, mul_zero]
    · rw [indicator_of_notMem, zero_mul]
      intro hmem
      have h₁ : ENNReal.ofReal (mollifyRadius 𝒮 M n) + ENNReal.ofReal (mollifyRadius 𝒮 M n / 2) ≤
          distToOutside 𝒮 n x + ENNReal.ofReal (mollifyRadius 𝒮 M n / 2) := by
        rw [← ofReal_three_halves_mul _ hr]
        refine le_trans hmem ((distToOutside_sub_proj_le 𝒮 n x v).trans ?_)
        gcongr
        exact not_lt.1 hv
      have h₂ := (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h₁
      exact absurd hx (not_lt.2 h₂)
  simp only [hzero, integral_zero]
theorem levelTransition_eq_one (hr : 0 < mollifyRadius 𝒮 M n) {x : 𝒮.Point}
    (hx : ENNReal.ofReal (2 * mollifyRadius 𝒮 M n) ≤ distToOutside 𝒮 n x) :
    levelTransition 𝒮 M n x = 1 := by
  unfold levelTransition smoothedIndicator
  refine Eq.trans ?_ (integral_mollifierScaled (half_pos hr))
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  by_cases hv : mollifyRadius 𝒮 M n / 2 < ‖v‖
  · simp only [mollifierScaled_eq_zero_of_lt_norm (half_pos hr) hv, mul_zero]
  · have hmem : x - torusProj 4 𝒮.side v ∈
        {x | ENNReal.ofReal (3 / 2 * mollifyRadius 𝒮 M n) ≤ distToOutside 𝒮 n x} := by
      have h₁ : ENNReal.ofReal (3 / 2 * mollifyRadius 𝒮 M n) +
            ENNReal.ofReal (mollifyRadius 𝒮 M n / 2) ≤
          distToOutside 𝒮 n (x - torusProj 4 𝒮.side v) +
            ENNReal.ofReal (mollifyRadius 𝒮 M n / 2) := by
        rw [← ofReal_two_mul_eq _ hr]
        refine hx.trans ((distToOutside_le_sub_proj 𝒮 n x v).trans ?_)
        gcongr
        exact not_lt.1 hv
      exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h₁
    simp only [indicator_of_mem hmem, one_mul]
theorem claim_holds : Claim := by
  intro 𝒮 K m M R₁ h n hn₁ _
  have hr := mollifyRadius_pos 𝒮 h n
  have hn : n ≠ 0 := by omega
  have hsin : ∀ x, sinCutoff 𝒮 M n x = Real.sin (Real.pi / 2 * levelTransition 𝒮 M n x) :=
    fun x => if_neg hn
  have hcos : ∀ x, cosCutoff 𝒮 M n x = Real.cos (Real.pi / 2 * levelTransition 𝒮 M n x) :=
    fun _ => rfl
  refine ⟨?_, fun x hx => levelTransition_eq_zero hr hx, fun x hx => levelTransition_eq_one hr hx,
    ?_, ?_, ?_, ?_⟩
  · intro hΩ x x'
    obtain ⟨q, hq⟩ := (ne_univ_iff_exists_notMem _).1 hΩ
    have hfin : ∀ y : 𝒮.Point, distToOutside 𝒮 n y ≠ ⊤ := by
      intro y
      rw [distToOutside_eq_iInf]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iInf₂_le q (subset_closure hq))
    refine ⟨hfin x, ?_⟩
    have hbound : ∀ y y' : 𝒮.Point, (distToOutside 𝒮 n y).toReal ≤
        (distToOutside 𝒮 n y').toReal + supNorm (y - y') := by
      intro y y'
      have h₁ := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin y', ENNReal.ofReal_ne_top⟩)
        (distToOutside_le_add 𝒮 n y y')
      rwa [ENNReal.toReal_add (hfin y') ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (norm_nonneg _), ← supNorm_eq_norm] at h₁
    have h₂ : supNorm (x' - x) = supNorm (x - x') := by
      rw [supNorm_eq_norm, supNorm_eq_norm, norm_sub_rev]
    refine abs_sub_le_iff.2 ⟨?_, ?_⟩
    · linarith [hbound x x']
    · linarith [hbound x' x]
  · intro x
    rw [hsin, hcos]
    exact Real.sin_sq_add_cos_sq _
  · refine closure_minimal (fun x hx => ?_) (isClosed_le_distToOutside 𝒮 n _)
    by_contra hlt
    apply hx
    rw [hsin, levelTransition_eq_zero hr (not_le.1 hlt)]
    simp
  · intro x hx
    rw [hsin, hcos, levelTransition_eq_one hr hx]
    simp
  · refine closure_minimal (fun x hx => ?_) (isClosed_distToOutside_le 𝒮 n _)
    by_contra hlt
    apply hx
    rw [hcos, levelTransition_eq_one hr (not_le.1 hlt).le]
    simp
end PartitionCubes.OutsideDistanceAndCutoffs
end YangMills.Construction
end
