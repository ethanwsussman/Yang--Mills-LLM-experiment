import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.Torus.CoverOfTheConstructedConstantExistsProof
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.TorusMetric
open scoped ENNReal NNReal Topology
noncomputable section
namespace YangMills.Construction.Weighted
namespace LayerCutoff
variable {S : ℝ}
theorem torusSupNorm_neg (x : Torus4 S) : torusSupNorm (-x) = torusSupNorm x := by apply _root_.YangMills.Construction.SequenceGeometryProof.torusSupNorm_neg <;> assumption
theorem torusSupNorm_sub_comm (x y : Torus4 S) : torusSupNorm (x - y) = torusSupNorm (y - x) := by
  rw [← neg_sub, torusSupNorm_neg]
theorem torusSupNorm_zero_nonpos : torusSupNorm (0 : Torus4 S) ≤ 0 := by
  have h0 : torusProj S (0 : Fin 4 → ℝ) = 0 := by
    funext μ
    simp [torusProj]
  have hv : supNormVec (0 : Fin 4 → ℝ) = 0 := by simp [supNormVec]
  refine csInf_le ⟨0, ?_⟩ ⟨0, h0, hv⟩
  rintro _ ⟨v, -, rfl⟩
  exact (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
theorem continuous_of_lipschitzL1 {f : Torus4 S → ℝ} (h : LipschitzL1 f) :
    Continuous f := by
  obtain ⟨C, hC⟩ := h
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hl : Continuous fun y : Torus4 S => (C : ℝ) * ∑ μ, ‖(y - x) μ‖ := by
    fun_prop
  have h0 : Tendsto (fun y : Torus4 S => (C : ℝ) * torusL1Norm (y - x)) (𝓝 x) (𝓝 0) := by
    have := hl.tendsto x
    simpa [torusL1Norm_eq_sum_norm] using this
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun y => ?_) h0
  rw [Real.dist_eq]
  exact hC x y
theorem distInftyToSet_eq_zero_of_mem {A : Set (Torus4 S)} {x : Torus4 S} (hx : x ∈ A) :
    distInftyToSet A x = 0 := by
  have h : setSupDist {x} A ≤ ENNReal.ofReal (torusSupNorm (x - x)) :=
    iInf₂_le_of_le x rfl (iInf₂_le x hx)
  rw [sub_self, ENNReal.ofReal_of_nonpos torusSupNorm_zero_nonpos] at h
  simp [distInftyToSet, le_antisymm h bot_le]
theorem setSupDist_singleton_ne_top {A : Set (Torus4 S)} (x : Torus4 S) (hA : A.Nonempty) :
    setSupDist {x} A ≠ ⊤ := by
  obtain ⟨a, ha⟩ := hA
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iInf₂_le_of_le x rfl (iInf₂_le a ha))
def clamp01 (s : ℝ) : ℝ := max 0 (min 1 s)
variable {D : TorusData} (B : SeparatedChain D)
theorem blockNumber_pos_real (D : TorusData) : (0 : ℝ) < D.blockNumber := by
  have hL : 0 < D.L := by have := D.blocking.three_le_factor; omega
  have : 0 < D.blockNumber := lt_of_lt_of_le hL D.le_blockNumber
  exact_mod_cast this
theorem three_le_L_real (D : TorusData) : (3 : ℝ) ≤ D.L := by apply _root_.YangMills.Construction.Weighted.LocalComparison.three_le_L <;> assumption
theorem scale_pos (D : TorusData) (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
theorem scale_succ (D : TorusData) (n : ℕ) : D.scale (n + 1) = D.L * D.scale n := by apply _root_.YangMills.Construction.Weighted.DistBounds.scale_succ <;> assumption
def innerRadius (D : TorusData) (n : ℕ) : ℝ := 1 / 3 * ((D.blockNumber : ℝ) * D.scale n)
theorem innerRadius_pos (D : TorusData) (n : ℕ) : 0 < innerRadius D n := by
  have := blockNumber_pos_real D
  have := scale_pos D n
  unfold innerRadius
  positivity
abbrev complementOf (j : ℕ) : Set D.Space := D.closedComplement (B.stage j)
open Classical in
def cutoffLevel (j : ℕ) (x : D.Space) : ℝ :=
  if j = 0 then 1 else if D.top < j then 0 else
    if (complementOf B j).Nonempty then
      clamp01 (distInftyToSet (complementOf B j) x / innerRadius D (j - 1)) else 1
theorem weightDensity_term_nonneg (n : ℕ) (x : D.Space) :
    0 ≤ (D.scale n)⁻¹ * (B.layer n).indicator (fun _ => (1 : ℝ)) x :=
  mul_nonneg (inv_nonneg.2 (scale_pos D n).le) (indicator_nonneg (fun _ _ => zero_le_one) x)
theorem inv_scale_le_weightDensity (n : ℕ) (x : D.Space) (hx : x ∉ B.stage (n + 1)) :
    (D.scale n)⁻¹ ≤ B.weightDensity x := by apply _root_.YangMills.Construction.Weighted.DistBounds.inv_scale_le_weightDensity <;> assumption
end LayerCutoff
end YangMills.Construction.Weighted
end
