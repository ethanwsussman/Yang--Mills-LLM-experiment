import YangMills.Construction.ClusterExpansionOfAStep.NearSitesOfAClass
import YangMills.Construction.ClusterExpansionOfAStep.SumOfAClassAtAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusLumps TorusFields BlockAverages
theorem classExponent_arith {κ κ₁ s cE ch Q x x' A b h v ν c : ℝ}
    (hκ : 0 < κ) (hκ₁ : 0 < κ₁) (hs : 0 < s) (hcE : 0 < cE)
    (h1 : κ₁ ≤ κ / 16) (h2 : κ₁ * s ≤ cE / 4)
    (hchκ : ch ≤ κ * s / 256) (hch1 : ch ≤ κ₁ * s / 256) (hch0 : 0 ≤ ch)
    (hx : 0 < x) (hx' : x' ≤ 1.01 * x)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hh : 0 ≤ h) (hv : 0 ≤ v) (hν : 0 ≤ ν) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2)
    (hlen : ν ≤ b + c * (h + v)) (hQ : Q ≤ ch * x * (A + ν)) :
    -x * (6 * κ * s * A + κ / 4 * s * h + cE * b + κ₁ * s * v) + Q ≤
      -(x' * κ * s * A) - κ₁ * x' * s * ν := by
  have hks : 0 < κ * s := mul_pos hκ hs
  have hk1s : 0 < κ₁ * s := mul_pos hκ₁ hs
  have e1 : x' * κ * s * A ≤ 1.01 * x * κ * s * A := by
    have : x' * (κ * s * A) ≤ 1.01 * x * (κ * s * A) :=
      mul_le_mul_of_nonneg_right hx' (by positivity)
    nlinarith
  have e2 : κ₁ * x' * s * ν ≤ 1.01 * x * (κ₁ * s) * ν := by
    have : x' * (κ₁ * s * ν) ≤ 1.01 * x * (κ₁ * s * ν) :=
      mul_le_mul_of_nonneg_right hx' (by positivity)
    nlinarith
  set g := 1.01 * (κ₁ * s) + ch with hg
  have hg0 : 0 ≤ g := by positivity
  have hg1 : g ≤ 1.02 * (κ₁ * s) := by rw [hg]; linarith
  have e3 : g * ν ≤ g * b + g * c * h + g * c * v := by
    have := mul_le_mul_of_nonneg_left hlen hg0
    nlinarith
  have e4 : g * b ≤ cE * b := by
    refine mul_le_mul_of_nonneg_right ?_ hb
    linarith
  have hgc : g * c ≤ 0.51 * (κ₁ * s) := by
    have : g * c ≤ g * (1 / 2) := mul_le_mul_of_nonneg_left hc hg0
    linarith
  have e5 : g * c * h ≤ κ / 4 * s * h := by
    refine mul_le_mul_of_nonneg_right ?_ hh
    have : κ₁ * s ≤ κ / 16 * s := mul_le_mul_of_nonneg_right h1 hs.le
    nlinarith
  have e6 : g * c * v ≤ κ₁ * s * v := by
    refine mul_le_mul_of_nonneg_right ?_ hv
    linarith
  have e7 : (1.01 * κ * s + ch) * A ≤ 6 * κ * s * A := by
    refine mul_le_mul_of_nonneg_right ?_ hA
    nlinarith
  have I : (1.01 * κ * s + ch) * A + g * ν ≤
      6 * κ * s * A + κ / 4 * s * h + cE * b + κ₁ * s * v := by linarith
  have hI := mul_le_mul_of_nonneg_left I hx.le
  have eq1 : x * ((1.01 * κ * s + ch) * A + g * ν) =
      1.01 * x * κ * s * A + ch * x * (A + ν) + 1.01 * x * (κ₁ * s) * ν := by
    rw [hg]; ring
  have eq2 : -x * (6 * κ * s * A + κ / 4 * s * h + cE * b + κ₁ * s * v) =
      -(x * (6 * κ * s * A + κ / 4 * s * h + cE * b + κ₁ * s * v)) := by ring
  rw [eq2]
  rw [eq1] at hI
  linarith
theorem nearSitesCost_arith {CE r r' lg N S x6 chx : ℝ} (hCE : 0 ≤ CE) (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hrr : r' ≤ 2 * r) (hlg : 0 ≤ lg) (hN : N ≤ (10 * r') ^ 4 * S) (hS : 0 ≤ S)
    (hb : 2 ^ 18 * CE * r ^ 12 * lg ≤ x6) (hs : x6 ≤ chx) : CE * r ^ 8 * lg * N ≤ chx * S := by
  have hq0 : 0 ≤ CE * r ^ 8 * lg := by positivity
  have hbase : 0 ≤ CE * r ^ 12 * lg * S := by positivity
  have hpow : (10 * r') ^ 4 ≤ 160000 * r ^ 4 := by
    have h1 : (10 * r') ^ 4 ≤ (10 * (2 * r)) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    calc (10 * r') ^ 4 ≤ (10 * (2 * r)) ^ 4 := h1
      _ = 160000 * r ^ 4 := by ring
  calc CE * r ^ 8 * lg * N ≤ CE * r ^ 8 * lg * ((10 * r') ^ 4 * S) :=
        mul_le_mul_of_nonneg_left hN hq0
    _ ≤ CE * r ^ 8 * lg * (160000 * r ^ 4 * S) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hS) hq0
    _ = 160000 * (CE * r ^ 12 * lg * S) := by ring
    _ ≤ 2 ^ 18 * (CE * r ^ 12 * lg * S) := mul_le_mul_of_nonneg_right (by norm_num) hbase
    _ = 2 ^ 18 * CE * r ^ 12 * lg * S := by ring
    _ ≤ x6 * S := mul_le_mul_of_nonneg_right hb hS
    _ ≤ chx * S := mul_le_mul_of_nonneg_right hs hS
theorem classSumRate_bounds {ℓ : StepParameters} {cE : ℝ} (hcE : 0 < cE) (hκ : 0 < ℓ.κ)
    (hκ₁ : 0 < ℓ.κ₁) (hσ : 0 < ℓ.threshold ^ 2) :
    0 ≤ classSumRate ℓ cE ∧ classSumRate ℓ cE ≤ ℓ.κ * ℓ.threshold ^ 2 / 256 ∧
      classSumRate ℓ cE ≤ ℓ.κ₁ * ℓ.threshold ^ 2 / 256 := by
  unfold classSumRate
  have h1 : min cE (min (ℓ.κ * ℓ.threshold ^ 2) (ℓ.κ₁ * ℓ.threshold ^ 2)) ≤ ℓ.κ * ℓ.threshold ^ 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have h2 : min cE (min (ℓ.κ * ℓ.threshold ^ 2) (ℓ.κ₁ * ℓ.threshold ^ 2)) ≤ ℓ.κ₁ * ℓ.threshold ^ 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨by positivity, ?_, ?_⟩ <;> norm_num <;> linarith
theorem classExponentLePrice_holds (hlen : ImageUnionLengthBound)
    (hnear : NearSitesLeLumpsAndLength) : ClassExponentLePrice := by
  classical
  intro ℓ cE CE hfit hask x x' hx hxx n _ hLn V W bad Yt P hP
  obtain ⟨hx1, hx2, hr1, hr2⟩ := hask.coupling_shift x x' hx hxx
  have hy1 : (1 : ℝ) ≤ ℓ.y₁ := hfit.y₁_ge
  have hx0 : 0 < x := by linarith
  have hxge1 : 1 ≤ x := by linarith
  have hmono : clusterRange ℓ.y₁ ≤ clusterRange x := by
    unfold clusterRange
    exact Nat.ceil_mono (Real.rpow_le_rpow (by linarith) hx (by norm_num))
  have hr0 : 2 ^ 16 + 1 ≤ clusterRange x := le_trans hask.range_ge hmono
  have hr' : 2 ^ 16 ≤ clusterRange x' := by omega
  have hrone : 1 ≤ clusterRange x := le_trans (by norm_num) hr0
  have hr'one : 1 ≤ clusterRange x' := le_trans (by norm_num) hr'
  have hL := hlen ℓ hfit (clusterRange x) (clusterRange x') hrone hr1 hr' n hLn V W bad Yt P hP
  have hN := (hnear ℓ n (clusterRange x') (P.biUnion id) V hr'one).2
  have hLpos : (0 : ℝ) < (ℓ.side : ℝ) := by
    have := hask.side_ge
    have : 0 < ℓ.side := by omega
    exact_mod_cast this
  have hc : 40 / (ℓ.side : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hLpos]
    have : (80 : ℝ) ≤ (ℓ.side : ℝ) := by exact_mod_cast hask.side_ge
    linarith
  have hσ : 0 < ℓ.threshold ^ 2 := by have := hfit.σ_pos; positivity
  have hκ := hfit.κ_pos
  have hκ₁ := hfit.κ₁_pos
  have hcE := hask.cE_pos
  obtain ⟨hch0, hchκ, hch1⟩ := classSumRate_bounds hcE hκ hκ₁ hσ
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hxge1
  have hrr : (clusterRange x' : ℝ) ≤ 2 * (clusterRange x : ℝ) := by
    have : clusterRange x' ≤ 2 * clusterRange x := by omega
    exact_mod_cast this
  have hNreal : ((nearSites (clusterRange x') (P.biUnion id)).card : ℝ) ≤
      (10 * (clusterRange x' : ℝ)) ^ 4 * ((((torusHotLumps ℓ V).filter (· ⊆ P.biUnion id)).card : ℝ) +
        (excessLength ℓ (clusterRange x') (P.biUnion id) V : ℝ)) := by
    have : (((nearSites (clusterRange x') (P.biUnion id)).card : ℕ) : ℝ) ≤
        (((10 * clusterRange x') ^ 4 * (((torusHotLumps ℓ V).filter (· ⊆ P.biUnion id)).card +
          excessLength ℓ (clusterRange x') (P.biUnion id) V) : ℕ) : ℝ) := by
      exact_mod_cast hN
    push_cast at this
    exact this
  have hA0 : (0 : ℝ) ≤ (((torusHotLumps ℓ V).filter (· ⊆ P.biUnion id)).card : ℝ) := Nat.cast_nonneg _
  have hν0 : (0 : ℝ) ≤ (excessLength ℓ (clusterRange x') (P.biUnion id) V : ℝ) := Nat.cast_nonneg _
  have hQ := nearSitesCost_arith hask.CE_nonneg (Nat.cast_nonneg (clusterRange x))
    (Nat.cast_nonneg (clusterRange x')) hrr hlog hNreal (add_nonneg hA0 hν0)
    (hask.log_bound x hx) (hask.root_le_rate x hx)
  exact classExponent_arith
    (b := (badBlocksInAttached ℓ (clusterRange x) bad Yt
      (thickening (2 * clusterRange x') (torusHotSites ℓ V)) (P.biUnion id) : ℝ))
    (h := (hotLumpsInAttached ℓ (clusterRange x) W bad Yt
      (thickening (2 * clusterRange x') (torusHotSites ℓ V)) (P.biUnion id) : ℝ))
    (v := (lengthInAttached ℓ (clusterRange x) W bad Yt
      (thickening (2 * clusterRange x') (torusHotSites ℓ V)) (P.biUnion id) : ℝ))
    hκ hκ₁ hσ hcE hask.κ₁_le hask.κ₁_le_cE hchκ hch1 hch0 hx0 hx1 hA0
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hν0 (by positivity) hc hL hQ
end YangMills.Construction.ClusterExpansionOfAStep
end
