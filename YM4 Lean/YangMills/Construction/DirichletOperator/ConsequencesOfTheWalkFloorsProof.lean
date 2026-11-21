import YangMills.Construction.DirichletOperator.ConsequencesOfTheWalkFloors
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
open YangMills.Construction.WeightedGreen YangMills.Construction.Dirichlet.WalkExpansion
namespace YangMills.Construction.Dirichlet.ThresholdConsequences
theorem claim_holds (partition : Dirichlet.PartitionOfUnity.PartitionClaim)
    (regions : Dirichlet.RegionBounds.RegionBoundsStatement) : Claim := by
  intro d L lo hi params S 𝒮 above
  rcases above with ⟨hblock, hgap⟩
  unfold gapLowerBound at hgap
  have hL : (3 : ℝ) ≤ L := by exact_mod_cast params.three_le_blockFactor
  have hd : (3 : ℝ) ≤ d := by exact_mod_cast params.three_le_dim
  have hd0 : (0 : ℝ) < d := by linarith
  have hhi : 0 < hi := params.lower_pos.trans_le params.lower_le_upper
  have hδ : 0 < expDecayRate d L lo hi := by
    have hγ : 0 < coercivityConst lo := lt_min (by norm_num) params.lower_pos
    unfold expDecayRate
    positivity
  have hκ : 0 < sumRate d L lo hi := by
    unfold sumRate
    positivity
  have hM2 : 2 * walkConstC d L lo hi ≤ (𝒮.M : ℝ) :=
    le_trans (le_max_right (3 * (L : ℝ) * (L + 12)) _) hblock
  have hM1 : 3 * (L : ℝ) * (L + 12) ≤ 𝒮.M :=
    le_trans (le_max_left _ (2 * walkConstC d L lo hi)) hblock
  have hR3 := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hgap)
  have hR2 := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hgap)
  have hR1 := le_trans (le_max_left _ _) hgap
  have hR : L * (L + 9) ≤ 𝒮.R₁ * 𝒮.M := by exact_mod_cast hR1
  have hM : 3 * L * (L + 12) ≤ 𝒮.M := by exact_mod_cast hM1
  have hMpos : (0 : ℝ) < 𝒮.M := hM1.trans_lt' (by positivity)
  obtain ⟨-, bumps, diffs, -⟩ := partition d L lo hi params S 𝒮 hM hR
  have hξ : 0 < 𝒮.ξ := 𝒮.isSeparatedChain.scale_pos
  have hzero : supNorm (0 : PeriodicTorus d S) ≤ 0 := by
    refine csInf_le ⟨0, ?_⟩ ⟨0, ?_, ?_⟩
    · rintro r ⟨v, -, rfl⟩
      exact norm_nonneg v
    · funext μ
      simp [torusProj]
    · simp
  have hch : 0 ≤ Dirichlet.PartitionOfUnity.partitionConst d := by
    obtain ⟨p, hp⟩ := 𝒮.isSeparatedChain.zero_nonempty
    obtain ⟨𝒞, h𝒞, hΩ⟩ := 𝒮.isSeparatedChain.isCubeUnion 0 (Nat.zero_le _)
    have hp' := hp
    rw [hΩ] at hp'
    obtain ⟨Q₀, hQ₀, -⟩ := hp'
    obtain ⟨c, ⟨k, hk⟩, rfl⟩ := h𝒞 hQ₀
    have hσ : 0 ≤ ((𝒮.M : ℝ) * scaleSpacing L 𝒮.ξ ((0 : ℕ) : ℤ)) / 2 := by
      unfold scaleSpacing
      positivity
    have hcΩ : c ∈ 𝒮.Ω 0 := by
      rw [hΩ]
      refine ⟨_, hQ₀, ?_⟩
      show supNorm (c - c) ≤ _
      rw [sub_self]
      exact hzero.trans hσ
    have hcsite : c ∈ spacingLattice d S 𝒮.ξ := by
      have h0 : scaleSpacing L 𝒮.ξ ((0 : ℕ) : ℤ) = 𝒮.ξ := by simp [scaleSpacing]
      refine ⟨fun μ => k μ * (𝒮.M : ℤ), ?_⟩
      rw [hk, h0]
      congr 1
      funext μ
      push_cast
      ring
    have hdist : ∀ r : ℝ, 0 ≤ r → supSetDist {c} (𝒮.Ω 0) ≤ ENNReal.ofReal r := by
      intro r hr
      unfold supSetDist
      refine iInf₂_le_of_le c rfl (iInf₂_le_of_le c hcΩ ?_)
      rw [sub_self]
      exact ENNReal.ofReal_le_ofReal (hzero.trans hr)
    have hU : c ∈ 𝒮.baseNbhd := hdist _ (by positivity)
    have hcubes : 𝒮.coverCubes.Nonempty := by
      by_contra hempty
      rw [not_nonempty_iff_eq_empty] at hempty
      have h1 := (bumps.squares_between c hU).1
      unfold BlockSetting.bumpSqSum at h1
      rw [hempty, finsum_mem_empty] at h1
      linarith
    obtain ⟨Q, hQ⟩ := hcubes
    have hdpos : 0 < d := by exact_mod_cast hd0
    let x : LatticeSite d S 𝒮.ξ := ⟨c, hcsite⟩
    have hbound := diffs.diff_at_bond Q hQ x (x + unitStep d S 𝒮.ξ ⟨0, hdpos⟩) hU
      (hdist _ (by positivity)) ⟨⟨0, hdpos⟩, Or.inl rfl⟩
    have hsp : ∀ n : ℕ, 0 < scaleSpacing L 𝒮.ξ n := fun n => by
      unfold scaleSpacing
      positivity
    have hρ : 0 < 𝒮.localScale x := by
      unfold BlockSetting.localScale
      split_ifs <;> first | exact hξ | exact hsp _
    by_contra hneg
    have hlt : Dirichlet.PartitionOfUnity.partitionConst d * (L : ℝ) ^ 2 * 𝒮.ξ /
        ((𝒮.M : ℝ) * 𝒮.localScale x) < 0 :=
      div_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (not_le.mp hneg) (by positivity)) hξ)
        (by positivity)
    linarith [abs_nonneg (𝒮.latticeCutoff Q (x + unitStep d S 𝒮.ξ ⟨0, hdpos⟩) - 𝒮.latticeCutoff Q x)]
  have hC₁ : 0 < Dirichlet.RegionBounds.decayConstant d L lo hi :=
    (regions d L lo hi params).1.1
  have hsum : 1 ≤ intExpSum (1 / 2 * sumRate d L lo hi) := by
    obtain ⟨a, ha, hae⟩ : ∃ a : ℝ, 0 < a ∧ a = 1 / 2 * sumRate d L lo hi := ⟨_, by positivity, rfl⟩
    rw [← hae]
    have hgeom : Summable fun n : ℕ => Real.exp (-a) ^ n :=
      summable_geometric_of_lt_one (Real.exp_nonneg _) (Real.exp_lt_one_iff.mpr (by linarith))
    have hterm : ∀ n : ℕ, Real.exp (-a * |((n : ℤ) : ℝ)|) = Real.exp (-a) ^ n ∧
        Real.exp (-a * |((-(n : ℤ) : ℤ) : ℝ)|) = Real.exp (-a) ^ n := by
      intro n
      rw [← Real.exp_nat_mul]
      constructor <;>
      · push_cast
        simp only [abs_neg, Nat.abs_cast]
        congr 1
        ring
    have hZ : Summable fun z : ℤ => Real.exp (-a * |(z : ℝ)|) :=
      Summable.of_nat_of_neg (hgeom.congr fun n => (hterm n).1.symm)
        (hgeom.congr fun n => (hterm n).2.symm)
    calc (1 : ℝ) = Real.exp (-a * |((0 : ℤ) : ℝ)|) := by simp
      _ ≤ intExpSum a := hZ.le_tsum 0 fun z _ => (Real.exp_pos _).le
  have hc₁ : 1 ≤ sumBound d L lo hi := by
    have hE : 1 ≤ Real.exp (1 / 2 * sumRate d L lo hi * (d : ℝ) * ((L : ℝ) + 3)) :=
      Real.one_le_exp (by positivity)
    have hP : 1 ≤ intExpSum (1 / 2 * sumRate d L lo hi) ^ (3 * d) :=
      one_le_pow₀ hsum
    unfold sumBound blockSumConst
    nlinarith [mul_le_mul hE hP zero_le_one (by positivity)]
  have hCR : 0 ≤ remainderConstC d L lo hi := by
    unfold remainderConstC remainderConst
    generalize Dirichlet.PartitionOfUnity.partitionConst d = c at hch
    generalize Dirichlet.RegionBounds.decayConstant d L lo hi = C at hC₁
    positivity
  have hCT : 0 < crossConstC d L lo hi := by
    unfold crossConstC crossConst
    generalize Dirichlet.PartitionOfUnity.partitionConst d = c at hch
    generalize Dirichlet.RegionBounds.decayConstant d L lo hi = C at hC₁
    refine mul_pos hC₁ (lt_of_lt_of_le ?_ (le_max_right _ _))
    positivity
  have hmult : (1 : ℝ) ≤ (cubeOverlap d : ℝ) := by
    have h2 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    unfold cubeOverlap
    push_cast
    linarith
  have hfactor : 1 ≤ (cubeOverlap d : ℝ) * sumBound d L lo hi := by
    nlinarith
  have hmaxpos : 0 < max (remainderConstC d L lo hi) (crossConstC d L lo hi) :=
    lt_of_lt_of_le hCT (le_max_right _ _)
  have hwalk : walkConstC d L lo hi = (cubeOverlap d : ℝ) *
      sumBound d L lo hi *
      max (remainderConstC d L lo hi) (crossConstC d L lo hi) := rfl
  have hmaxle : max (remainderConstC d L lo hi) (crossConstC d L lo hi) ≤
      walkConstC d L lo hi := by
    rw [hwalk]
    exact le_mul_of_one_le_left hmaxpos.le hfactor
  refine
    { blockSize_floor := hM
      gap_floor := hR
      floors := ?_
      sumRate_floor := ?_
      partitionConst_nonneg := hch
      one_le_sumBound := hc₁
      remainderConst_nonneg := hCR
      crossConst_nonneg := hCT.le
      walkConst_pos := ?_
      remainderConst_le_walkConst := (le_max_left _ _).trans hmaxle
      crossConst_le_walkConst := (le_max_right _ _).trans hmaxle
      two_mul_walkConst_le := hM2 }
  · refine ⟨?_, max_le hR1 hR2⟩
    show (𝒮.M : ℝ) ≥ (L : ℝ) + 10
    nlinarith
  · unfold Dirichlet.WeightedDistance.RateAboveFloor
    generalize 2 * (d : ℝ) *
        Real.log (intExpSum (1 / 2 * sumRate d L lo hi)) +
      1 / 4 * sumRate d L lo hi * (d : ℝ) * ((L : ℝ) + 3) +
      Real.log 2 + 1 = X at hR3 ⊢
    have hmul := mul_le_mul_of_nonneg_left hR3 (by positivity :
      0 ≤ 1 / 4 * sumRate d L lo hi)
    have hcancel : 1 / 4 * sumRate d L lo hi *
        (4 * (sumRate d L lo hi)⁻¹ * X) = X := by
      field_simp
    rw [hcancel] at hmul
    linarith
  · exact lt_of_lt_of_le hmaxpos hmaxle
end YangMills.Construction.Dirichlet.ThresholdConsequences
