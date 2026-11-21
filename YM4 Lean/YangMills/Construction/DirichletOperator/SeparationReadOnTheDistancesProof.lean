import YangMills.Construction.DirichletOperator.AveragingOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.DirichletOperator.BoundsOnTheCoefficientsOfACubeProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open Torus
namespace PartitionCubes.DistanceSeparation
theorem supNorm_eq_norm {S : ℝ} (x : PeriodicTorus 4 S) : supNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem exists_mem_cubePartition {S σ : ℝ} (hσ : 0 < σ) (q : PeriodicTorus 4 S) :
    ∃ Q ∈ cubePartition 4 S σ, q ∈ Q := by
  choose v hv _ using fun μ => TorusMetric.exists_coe_eq_abs_eq_norm (q μ)
  set k : Fin 4 → ℤ := fun μ => round (v μ / σ) with hk
  have hc : torusProj 4 S (fun μ => (k μ : ℝ) * σ) ∈ spacingLattice 4 S σ := ⟨k, rfl⟩
  refine ⟨cubeAt (torusProj 4 S fun μ => (k μ : ℝ) * σ) σ, ⟨_, hc, rfl⟩, ?_⟩
  change supNorm _ ≤ σ / 2
  rw [supNorm_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (half_pos hσ).le).2 fun μ => ?_
  have e : (q - torusProj 4 S fun μ => (k μ : ℝ) * σ) μ =
      ((v μ - (k μ : ℝ) * σ : ℝ) : AddCircle S) := by
    show q μ - (((k μ : ℝ) * σ : ℝ) : AddCircle S) = _
    rw [AddCircle.coe_sub, hv μ]
  rw [e]
  refine (TorusMetric.addCircle_norm_coe_le_abs _).trans ?_
  have h₁ : v μ - (k μ : ℝ) * σ = (v μ / σ - k μ) * σ := by
    rw [sub_mul, div_mul_cancel₀ _ hσ.ne']
  rw [h₁, abs_mul, abs_of_pos hσ]
  have h₂ : |v μ / σ - (k μ : ℝ)| ≤ 1 / 2 := abs_sub_round (v μ / σ)
  have h₃ := mul_le_mul_of_nonneg_right h₂ hσ.le
  linarith
variable {𝒮 : RegionSequence.NestedRegions}
theorem cast_L_pos : 0 < (𝒮.L : ℝ) := by apply _root_.YangMills.Construction.RegionSequence.ShellDecomposition.blockFactor_pos <;> assumption
theorem thirteen_le_cast_L : (13 : ℝ) ≤ 𝒮.L := by
  exact_mod_cast 𝒮.thirteen_le_L
theorem scale_pos (n : ℕ) : 0 < 𝒮.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
theorem scale_succ (n : ℕ) : 𝒮.scale (n + 1) = (𝒮.L : ℝ) * 𝒮.scale n := by apply _root_.YangMills.Construction.PartitionCoefficients.nestedScale_succ <;> assumption
theorem lt_distToOutside_of_mem {M R₁ : ℕ} (h : IsSeparatedChain 𝒮.L 𝒮.ξ M R₁ 𝒮.s 𝒮.Ω)
    (hM : 0 < M) {n : ℕ} (hn : n < 𝒮.s) {x : 𝒮.Point} (hx : x ∈ 𝒮.Ω (n + 1)) :
    ENNReal.ofReal ((R₁ : ℝ) * cubeSide 𝒮 M n) < distToOutside 𝒮 n x := by
  have hσ : 0 < (M : ℝ) * scaleSpacing 𝒮.L 𝒮.ξ n :=
    mul_pos (by exact_mod_cast hM) (scale_pos (𝒮 := 𝒮) n)
  have hgap := h.separated n hn
  set D := supSetDist (cubeComplement ((M : ℝ) * scaleSpacing 𝒮.L 𝒮.ξ n) (𝒮.Ω n))
    (𝒮.Ω (n + 1)) with hD
  have key : ∀ q ∈ (𝒮.Ω n)ᶜ, D ≤ ENNReal.ofReal ‖x - q‖ := by
    intro q hq
    obtain ⟨Q, hQ, hqQ⟩ := exists_mem_cubePartition hσ q
    have hout : q ∈ cubeComplement ((M : ℝ) * scaleSpacing 𝒮.L 𝒮.ξ n) (𝒮.Ω n) :=
      ⟨Q, ⟨hQ, fun hsub => hq (hsub hqQ)⟩, hqQ⟩
    have h₁ : D ≤ ENNReal.ofReal (supNorm (q - x)) :=
      iInf₂_le_of_le q hout (iInf₂_le x hx)
    rwa [supNorm_eq_norm, norm_sub_rev] at h₁
  have hclosed : IsClosed {q : 𝒮.Point | D ≤ ENNReal.ofReal ‖x - q‖} :=
    isClosed_le continuous_const
      (ENNReal.continuous_ofReal.comp (continuous_const.sub continuous_id).norm)
  have hcl : closure (𝒮.Ω n)ᶜ ⊆ {q : 𝒮.Point | D ≤ ENNReal.ofReal ‖x - q‖} :=
    closure_minimal key hclosed
  have hle : D ≤ distToOutside 𝒮 n x := by
    refine le_iInf₂ fun p hp => le_iInf₂ fun q hq => ?_
    rw [mem_singleton_iff.1 hp, supNorm_eq_norm]
    exact hcl hq
  refine lt_of_lt_of_le ?_ hle
  have e : (R₁ : ℝ) * cubeSide 𝒮 M n = (R₁ : ℝ) * (M : ℝ) * scaleSpacing 𝒮.L 𝒮.ξ n := by
    simp only [cubeSide, RegionSequence.NestedRegions.scale]
    ring
  rw [e]
  exact hgap
theorem exists_mem_supp_supNorm_le {M : ℕ} (Q : LevelCube 𝒮 M) {ς : ℝ}
    (hr : 0 ≤ ς * mollifyRadius 𝒮 M Q.level) {x : 𝒮.Point} (hx : x ∈ Q.thicken ς) :
    ∃ y ∈ Q.supp, supNorm (x - y) ≤ ς * mollifyRadius 𝒮 M Q.level := by
  have : Fact (0 < 𝒮.side) := ⟨𝒮.side_pos⟩
  have hx' : supSetDist {x} Q.supp ≤ ENNReal.ofReal (ς * mollifyRadius 𝒮 M Q.level) := hx
  have hc : IsCompact Q.supp := (isClosed_tsupport Q.partitionFn).isCompact
  rcases Q.supp.eq_empty_or_nonempty with he | hne
  · exfalso
    have htop : supSetDist {x} Q.supp = ⊤ := by
      simp [supSetDist, he]
    rw [htop] at hx'
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hx')
  · obtain ⟨y, hy, hmin⟩ := hc.exists_isMinOn hne
      (f := fun y : 𝒮.Point => ‖x - y‖) (continuous_const.sub continuous_id).norm.continuousOn
    refine ⟨y, hy, ?_⟩
    have hle : ENNReal.ofReal ‖x - y‖ ≤ supSetDist {x} Q.supp := by
      refine le_iInf₂ fun p hp => le_iInf₂ fun q hq => ?_
      rw [mem_singleton_iff.1 hp, supNorm_eq_norm]
      exact ENNReal.ofReal_le_ofReal (isMinOn_iff.1 hmin q hq)
    rw [supNorm_eq_norm]
    exact (ENNReal.ofReal_le_ofReal_iff hr).1 (hle.trans hx')
theorem statement_holds : Statement := by
  intro K m M R₁ 𝒮 h hM
  have hsep := h.separated
  have hL : (0 : ℝ) < 𝒮.L := cast_L_pos
  have hL13 : (13 : ℝ) ≤ 𝒮.L := thirteen_le_cast_L
  have hML : ((𝒮.L : ℝ)) ^ 5 ≤ M := by exact_mod_cast hM
  have hMpos' : (0 : ℝ) < M := lt_of_lt_of_le (pow_pos hL 5) hML
  have hMpos : 0 < M := by exact_mod_cast hMpos'
  have hside : ∀ n, 0 < cubeSide 𝒮 M n := fun n => mul_pos hMpos' (scale_pos n)
  have hsucc : ∀ n, cubeSide 𝒮 M (n + 1) = (𝒮.L : ℝ) * cubeSide 𝒮 M n := by
    intro n
    simp only [cubeSide]
    rw [scale_succ]
    ring
  have h6L : (0 : ℝ) < 6 * 𝒮.L := mul_pos (by norm_num) hL
  have hrad : ∀ n, 0 ≤ mollifyRadius 𝒮 M n := fun n => (div_pos (hside n) h6L).le
  refine ⟨fun n hn x hx => lt_distToOutside_of_mem hsep hMpos hn hx, hsep.gapSize_isPowerGe.1,
    𝒮.thirteen_le_L, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simp only [mollifyRadius]
    rw [hsucc, mul_comm (6 : ℝ), mul_div_mul_left _ _ hL.ne']
    ring
  · intro n
    simp only [mollifyRadius]
    exact div_le_div_of_nonneg_left (hside n).le (by norm_num) (by linarith)
  · intro n
    simp only [mollifyRadius]
    rw [hsucc]
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_left (hside n).le (by linarith)) h6L.le
  · intro n
    have ht := scale_pos (𝒮 := 𝒮) n
    have h3 : (2197 : ℝ) ≤ (𝒮.L : ℝ) ^ 3 := by
      calc (2197 : ℝ) = 13 ^ 3 := by norm_num
        _ ≤ (𝒮.L : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hL13 3
    have h5 : 2196 * (𝒮.L : ℝ) ^ 2 ≤ (M : ℝ) :=
      calc 2196 * (𝒮.L : ℝ) ^ 2 ≤ (𝒮.L : ℝ) ^ 3 * (𝒮.L : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith) (pow_pos hL 2).le
        _ = (𝒮.L : ℝ) ^ 5 := by ring
        _ ≤ M := hML
    simp only [mollifyRadius, cubeSide]
    rw [scale_succ, le_div_iff₀ h6L]
    calc 366 * ((𝒮.L : ℝ) * 𝒮.scale n) * (6 * (𝒮.L : ℝ))
        = 2196 * (𝒮.L : ℝ) ^ 2 * 𝒮.scale n := by ring
      _ ≤ (M : ℝ) * 𝒮.scale n := mul_le_mul_of_nonneg_right h5 ht.le
  · intro Q ς hς x hx
    exact exists_mem_supp_supNorm_le Q (mul_nonneg hς (hrad _)) hx
end PartitionCubes.DistanceSeparation
end YangMills.Construction
