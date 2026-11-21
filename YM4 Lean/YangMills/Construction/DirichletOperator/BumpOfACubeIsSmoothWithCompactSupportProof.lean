import YangMills.Construction.DirichletOperator.AveragingOperatorsAgreeOnTheLocalTorusProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped ContDiff
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Torus YangMills.Construction.RegionSequence
open YangMills.Construction.RegionSequence.NestedRegions
namespace PartitionCubes.ProductBump
theorem exists_rep_mem_Ico {S : ℝ} (hS : 0 < S) (θ : AddCircle S) :
    ∃ v : ℝ, v ∈ Ico (-(S / 2)) (S / 2) ∧ (v : AddCircle S) = θ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.exists_centred_rep <;> assumption
theorem circleCentredRep_spec {S : ℝ} (hS : 0 < S) (θ : AddCircle S) :
    circleCentredRep θ ∈ Ico (-(S / 2)) (S / 2) ∧ (circleCentredRep θ : AddCircle S) = θ :=
  Classical.epsilon_spec (exists_rep_mem_Ico hS θ)
theorem abs_circleCentredRep_le {S : ℝ} (hS : 0 < S) (θ : AddCircle S) :
    |circleCentredRep θ| ≤ S / 2 := by
  have hmem := (circleCentredRep_spec hS θ).1
  exact abs_le.2 ⟨hmem.1, hmem.2.le⟩
theorem norm_eq_abs_circleCentredRep {S : ℝ} (hS : 0 < S) (θ : AddCircle S) :
    ‖θ‖ = |circleCentredRep θ| := by
  have hnorm := (AddCircle.norm_coe_eq_abs_iff S (x := circleCentredRep θ) hS.ne').2
    (by rw [abs_of_pos hS]; exact abs_circleCentredRep_le hS θ)
  rwa [(circleCentredRep_spec hS θ).2] at hnorm
theorem exists_radius_sqPartitionBump_eq_zero :
    ∃ r : ℝ, 0 ≤ r ∧ r < 2 / 3 ∧ ∀ u, r < |u| → sqPartitionBump u = 0 := by
  have hT : IsCompact (tsupport sqPartitionBump) := sqPartitionBump_spec.compact_support
  have h0 : (0 : ℝ) ∈ tsupport sqPartitionBump := by
    apply subset_tsupport
    have hone : sqPartitionBump 0 = 1 :=
      sqPartitionBump_spec.eq_one 0 ⟨by norm_num, by norm_num⟩
    simp [hone]
  obtain ⟨u₀, hu₀, hmax⟩ := hT.exists_isMaxOn ⟨0, h0⟩ continuous_abs.continuousOn
  refine ⟨|u₀|, abs_nonneg _, ?_, fun u hu => ?_⟩
  · have hsub := sqPartitionBump_spec.support_subset hu₀
    exact abs_lt.2 ⟨hsub.1, hsub.2⟩
  · by_contra hne
    have hut : u ∈ tsupport sqPartitionBump := subset_tsupport _ hne
    have hle : |u| ≤ |u₀| := isMaxOn_iff.1 hmax u hut
    linarith
theorem sqPartitionBump_eq_zero_of_le_abs {u : ℝ} (hu : 2 / 3 ≤ |u|) :
    sqPartitionBump u = 0 := by
  obtain ⟨r, -, hr, hz⟩ := exists_radius_sqPartitionBump_eq_zero
  exact hz u (by linarith)
theorem sqPartitionBump_div_eq_zero {B v : ℝ} (hB : 0 < B) (hv : 2 / 3 * B ≤ |v|) :
    sqPartitionBump (v / B) = 0 := by
  apply sqPartitionBump_eq_zero_of_le_abs
  rw [abs_div, abs_of_pos hB, le_div_iff₀ hB]
  exact hv
theorem sqPartitionBump_div_eq_of_coe_eq {S B a b : ℝ} (hS : 0 < S) (hB : 0 < B)
    (hBS : B ≤ S / 2) (hab : (a : AddCircle S) = b) (ha : |a| < 2 / 3 * S)
    (hb : |b| ≤ S / 2) :
    sqPartitionBump (a / B) = sqPartitionBump (b / B) := by
  have h0 : ((a - b : ℝ) : AddCircle S) = 0 := by rw [AddCircle.coe_sub, hab, sub_self]
  obtain ⟨j, hj⟩ := (AddCircle.coe_eq_zero_iff S).1 h0
  by_cases hj0 : j = 0
  · have hab' : a = b := by
      rw [hj0, zsmul_eq_mul, Int.cast_zero, zero_mul] at hj
      linarith
    rw [hab']
  · have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
      have hint : 1 ≤ |j| := Int.one_le_abs hj0
      exact_mod_cast hint
    have hdiff : S ≤ |a - b| := by
      rw [← hj, zsmul_eq_mul, abs_mul, abs_of_pos hS]
      exact le_mul_of_one_le_left hS.le hj1
    have hsum : |a - b| ≤ |a| + |b| := by
      have h := abs_add_le a (-b)
      rwa [abs_neg, ← sub_eq_add_neg] at h
    have ha' : 2 / 3 * B ≤ |a| := by linarith
    have hb' : 2 / 3 * B ≤ |b| := by linarith
    rw [sqPartitionBump_div_eq_zero hB ha', sqPartitionBump_div_eq_zero hB hb']
theorem tsupport_productBump_subset {𝒮 : NestedRegions} {M : ℕ} (Q : LevelCube 𝒮 M)
    (hB : 0 < cubeSide 𝒮 M Q.level) :
    tsupport Q.productBump ⊆
      {x | supNorm (x - Q.centre) < 2 / 3 * cubeSide 𝒮 M Q.level} := by
  have hS := 𝒮.side_pos
  obtain ⟨r, hr0, hr, hz⟩ := exists_radius_sqPartitionBump_eq_zero
  set B := cubeSide 𝒮 M Q.level with hBdef
  have hclosed : IsClosed {x : 𝒮.Point | ∀ μ, ‖x μ - Q.centre μ‖ ≤ r * B} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun μ =>
      isClosed_le ((continuous_apply μ).sub continuous_const).norm continuous_const
  have hsub : tsupport Q.productBump ⊆ {x : 𝒮.Point | ∀ μ, ‖x μ - Q.centre μ‖ ≤ r * B} := by
    refine closure_minimal (fun x hx μ => ?_) hclosed
    have hne : ∀ ν, sqPartitionBump (circleCentredRep (x ν - Q.centre ν) / B) ≠ 0 := by
      intro ν hν
      apply hx
      exact Finset.prod_eq_zero (Finset.mem_univ ν) hν
    have hle : |circleCentredRep (x μ - Q.centre μ) / B| ≤ r := by
      by_contra hlt
      exact hne μ (hz _ (not_le.1 hlt))
    rw [abs_div, abs_of_pos hB, div_le_iff₀ hB] at hle
    rw [norm_eq_abs_circleCentredRep hS]
    exact hle
  intro x hx
  have hx' := hsub hx
  have hmem : ‖fun μ => circleCentredRep (x μ - Q.centre μ)‖ ≤ r * B := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hr0 hB.le)).2 fun μ => ?_
    show ‖circleCentredRep (x μ - Q.centre μ)‖ ≤ r * B
    rw [Real.norm_eq_abs, ← norm_eq_abs_circleCentredRep hS]
    exact hx' μ
  have hinf : supNorm (x - Q.centre) ≤ ‖fun μ => circleCentredRep (x μ - Q.centre μ)‖ := by
    refine csInf_le ⟨0, ?_⟩ ⟨fun μ => circleCentredRep (x μ - Q.centre μ), ?_, rfl⟩
    · rintro _ ⟨v, -, rfl⟩
      exact norm_nonneg _
    · funext μ
      exact (circleCentredRep_spec hS (x μ - Q.centre μ)).2
  show supNorm (x - Q.centre) < 2 / 3 * B
  exact (hinf.trans hmem).trans_lt (mul_lt_mul_of_pos_right hr hB)
end PartitionCubes.ProductBump
end YangMills.Construction
