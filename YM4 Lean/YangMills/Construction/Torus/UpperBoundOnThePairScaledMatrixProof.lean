import YangMills.Construction.Torus.BoundsOnTheWeightedDistanceProof
import YangMills.Construction.Torus.CoercivityAndWeightedBoundsOfAnAdmissiblePair
import YangMills.Construction.Torus.OperatorsOfAnAdmissiblePair
import YangMills.Construction.Torus.UpperBoundOnThePairScaledMatrix
import YangMills.Construction.Weighted.ChainSiteSums
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
open GivenChainGeneral
namespace ScaledMatrixBound
theorem scale_pos (D : TorusData) (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
variable {D : TorusData} (B : SeparatedChain D)
theorem siteScale_pos (y : D.Space) : 0 < B.siteScale y := scale_pos D _
theorem weightedDistance_comm (x x' : D.Space) :
    B.weightedDistance x x' = B.weightedDistance x' x := by apply _root_.YangMills.Construction.Weighted.DistBounds.weightedDistance_comm <;> assumption
theorem finite_allSites (hb : BlockPartition B) : Finite ↥B.allSites := by
  have := D.bareSite_finite
  choose g hg using fun y : ↥B.allSites => hb.block_nonempty y y.2
  refine Finite.of_injective g fun y y' h => ?_
  by_contra hne
  have hd := hb.block_pairwise_disjoint y y.2 y' y'.2 fun e => hne (Subtype.ext e)
  exact Set.disjoint_left.1 hd (hg y) (h ▸ hg y')
theorem bareInner_eq_sum (hb : BlockPartition B) (u v : D.BareSite → ℝ) :
    B.bareInner u v =
      ∑ᶠ z : ↥B.allSites, D.scale 0 ^ 4 * ∑ᶠ x ∈ B.block z, u x * v x := by
  have := D.bareSite_finite
  have := finite_allSites B hb
  have hU : D.bareSites (B.stage 0) = ⋃ z : ↥B.allSites, B.block z := by
    rw [← hb.iUnion_block, Set.biUnion_eq_iUnion]
  have hdis : Pairwise (Function.onFun Disjoint fun z : ↥B.allSites => B.block z) := by
    intro z z' hne
    exact hb.block_pairwise_disjoint z z.2 z' z'.2 fun e => hne (Subtype.ext e)
  unfold SeparatedChain.bareInner
  rw [hU, finsum_mem_iUnion hdis fun _ => toFinite _, mul_finsum _ _]
theorem abs_inner_on_sites_le (E : Set D.BareSite) (u v : D.BareSite → ℝ) :
    |D.scale 0 ^ 4 * ∑ᶠ x ∈ E, u x * v x| ≤ TorusData.siteNorm E u * TorusData.siteNorm E v := by
  have := D.bareSite_finite
  have hc : 0 ≤ D.scale 0 ^ 4 := (pow_pos (scale_pos D 0) 4).le
  set F : Finset D.BareSite := (toFinite E).toFinset with hF
  have h₁ : ∑ᶠ x ∈ E, u x * v x = ∑ x ∈ F, u x * v x :=
    finsum_mem_eq_finite_toFinset_sum _ _
  have h₂ : ∑ᶠ x ∈ E, u x ^ 2 = ∑ x ∈ F, u x ^ 2 := finsum_mem_eq_finite_toFinset_sum _ _
  have h₃ : ∑ᶠ x ∈ E, v x ^ 2 = ∑ x ∈ F, v x ^ 2 := finsum_mem_eq_finite_toFinset_sum _ _
  unfold TorusData.siteNorm
  rw [h₁, h₂, h₃, ← Real.sqrt_mul (mul_nonneg hc (Finset.sum_nonneg fun _ _ => sq_nonneg _))]
  apply Real.abs_le_sqrt
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq F u v
  calc (D.scale 0 ^ 4 * ∑ x ∈ F, u x * v x) ^ 2
      = (D.scale 0 ^ 4) ^ 2 * (∑ x ∈ F, u x * v x) ^ 2 := by ring
    _ ≤ (D.scale 0 ^ 4) ^ 2 * ((∑ x ∈ F, u x ^ 2) * ∑ x ∈ F, v x ^ 2) := by gcongr
    _ = D.scale 0 ^ 4 * (∑ x ∈ F, u x ^ 2) * (D.scale 0 ^ 4 * ∑ x ∈ F, v x ^ 2) := by ring
theorem term_le {ξ ξ₁ ξ₂ C L ε ϱ r r' d a b : ℝ} (hξ : 0 < ξ) (hξ₁ : 0 < ξ₁) (hξ₂ : 0 < ξ₂)
    (hL : 0 ≤ L) (hε : 0 ≤ ε) (hϱ : ϱ ≤ 1 / 4 * ε) (hr : 0 ≤ r) (hr' : 0 ≤ r') (hd : d ≤ r + r')
    (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b)
    (ha : a ≤ C * ξ * ξ₁ * Real.exp (-(ε * r)) * ξ₁ ^ 2)
    (hb : b ≤ C * ξ * ξ₂ * Real.exp (-(ε * r')) * ξ₂ ^ 2)
    (h₁ : ξ / ξ₁ ≤ L * Real.exp (ϱ * r)) (h₂ : ξ / ξ₂ ≤ L * Real.exp (ϱ * r')) :
    ξ₁ ^ (-4 : ℤ) * ξ₂ ^ (-4 : ℤ) * (a * b) ≤
      C ^ 2 * L ^ 2 * Real.exp (-(1 / 2 * ε * d)) * Real.exp (-(1 / 4 * ε) * r) := by
  have hq₁ : 0 ≤ ξ / ξ₁ := (div_pos hξ hξ₁).le
  have hq₂ : 0 ≤ ξ / ξ₂ := (div_pos hξ hξ₂).le
  calc ξ₁ ^ (-4 : ℤ) * ξ₂ ^ (-4 : ℤ) * (a * b)
      ≤ ξ₁ ^ (-4 : ℤ) * ξ₂ ^ (-4 : ℤ) *
          ((C * ξ * ξ₁ * Real.exp (-(ε * r)) * ξ₁ ^ 2) *
            (C * ξ * ξ₂ * Real.exp (-(ε * r')) * ξ₂ ^ 2)) := by
        have hp : 0 ≤ ξ₁ ^ (-4 : ℤ) * ξ₂ ^ (-4 : ℤ) := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul ha hb hb₀ (ha₀.trans ha)) hp
    _ = C ^ 2 * ((ξ / ξ₁) * (ξ / ξ₂)) * (Real.exp (-(ε * r)) * Real.exp (-(ε * r'))) := by
        have h₁' : ξ₁ ^ (-4 : ℤ) = (ξ₁ ^ 4)⁻¹ := by
          rw [zpow_neg]
          norm_cast
        have h₂' : ξ₂ ^ (-4 : ℤ) = (ξ₂ ^ 4)⁻¹ := by
          rw [zpow_neg]
          norm_cast
        rw [h₁', h₂']
        field_simp
    _ ≤ C ^ 2 * ((L * Real.exp (ϱ * r)) * (L * Real.exp (ϱ * r'))) *
          (Real.exp (-(ε * r)) * Real.exp (-(ε * r'))) := by
        have : (ξ / ξ₁) * (ξ / ξ₂) ≤ (L * Real.exp (ϱ * r)) * (L * Real.exp (ϱ * r')) :=
          mul_le_mul h₁ h₂ hq₂ (hq₁.trans h₁)
        gcongr
    _ = C ^ 2 * L ^ 2 * Real.exp (ϱ * r + ϱ * r' + (-(ε * r) + -(ε * r'))) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add]
        ring
    _ ≤ C ^ 2 * L ^ 2 * Real.exp (-(1 / 2 * ε * d) + -(1 / 4 * ε) * r) := by
        have hexp : ϱ * r + ϱ * r' + (-(ε * r) + -(ε * r')) ≤ -(1 / 2 * ε * d) + -(1 / 4 * ε) * r := by
          have hs : 0 ≤ r + r' := add_nonneg hr hr'
          have k₁ : ϱ * (r + r') ≤ 1 / 4 * ε * (r + r') := mul_le_mul_of_nonneg_right hϱ hs
          have k₂ : ε * d ≤ ε * (r + r') := mul_le_mul_of_nonneg_left hd hε
          have k₃ : 0 ≤ ε * r' := mul_nonneg hε hr'
          nlinarith
        have := Real.exp_le_exp.2 hexp
        gcongr
    _ = C ^ 2 * L ^ 2 * Real.exp (-(1 / 2 * ε * d)) * Real.exp (-(1 / 4 * ε) * r) := by
        rw [Real.exp_add]
        ring
theorem bound_of_hyps (hb : BlockPartition B) (W : Set D.Space) (𝔟 : Set D.Bond)
    (hdist : ∀ x x' x'' : D.Space, B.weightedDistance x x'' ≤
      B.weightedDistance x x' + B.weightedDistance x' x'')
    (hnn : ∀ y ∈ B.allSites, ∀ y' ∈ B.allSites, 0 ≤ B.weightedDistance y y')
    (hrate : D.scaleRatioRate ≤ 1 / 4 * greenDecayRate 4 D.L)
    (hratio : ∀ y ∈ B.allSites, ∀ y' ∈ B.allSites, B.siteScale y / B.siteScale y' ≤
      (D.L : ℝ) * Real.exp (D.scaleRatioRate * B.weightedDistance y y'))
    (hsum : ∀ y : ↥B.allSites,
      ∑ᶠ y' : ↥B.allSites, Real.exp (-(1 / 4 * greenDecayRate 4 D.L) * B.weightedDistance y y') ≤
        latticeSumConst 4 D.L (1 / 4 * greenDecayRate 4 D.L))
    (hnorm : ∀ y : ↥B.allSites, B.bareSpaceNorm (B.blockIndicator y) ^ 2 = B.siteScale y ^ 4)
    (hdecay : B.AdmissibleGreenDecay W 𝔟) (hmat : B.AdmissibleScaledMatrixEq W 𝔟)
    (y y' : ↥B.allSites) (hy : (y : D.Space) ∈ B.sitesIn W)
    (hy' : (y' : D.Space) ∈ B.sitesIn W) :
    |B.admissibleScaledMatrix W 𝔟 y y'| ≤
      upperBoundConst 4 D.L *
        Real.exp (-(1 / 2 * greenDecayRate 4 D.L * B.weightedDistance (y : D.Space) (y' : D.Space))) := by
  have := finite_allSites B hb
  let _ : Fintype ↥B.allSites := Fintype.ofFinite _
  have hLpos : (0 : ℝ) < D.L := by
    have := D.blocking.three_le_factor
    have h : 0 < D.L := by omega
    exact_mod_cast h
  have hε : 0 < greenDecayRate 4 D.L := by
    unfold greenDecayRate
    positivity
  have hsub : ∀ z : ↥B.allSites, B.block z ⊆ D.bareSites (B.stage 0) := by
    intro z x hx
    rw [← hb.iUnion_block]
    exact mem_biUnion z.2 hx
  have hmem : ∀ z : ↥B.allSites, B.blockIndicator z ∈ B.bareSpace := by
    intro z x hx
    exact indicator_of_notMem (fun h => hx (hsub z h)) _
  have hres : ∀ z : ↥B.allSites,
      B.restrictBare W ⟨B.blockIndicator z, hmem z⟩ = B.blockIndicatorIn W z := by
    intro z
    apply Subtype.ext
    funext x
    change (D.bareSites W).indicator (B.blockIndicator z) x =
      (D.bareSites (B.stage 0) ∩ D.bareSites W).indicator (B.blockIndicator z) x
    by_cases hx : x ∈ D.bareSites W
    · by_cases hx₀ : x ∈ D.bareSites (B.stage 0)
      · rw [indicator_of_mem hx, indicator_of_mem (mem_inter hx₀ hx)]
      · rw [indicator_of_mem hx, indicator_of_notMem (fun h => hx₀ h.1)]
        exact hmem z x hx₀
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx h.2)]
  have hvan : ∀ z : ↥B.allSites, ∀ x, x ∉ B.block z → B.blockIndicator z x = 0 :=
    fun z x hx => indicator_of_notMem hx _
  have hchi : ∀ z : ↥B.allSites, B.bareSpaceNorm (B.blockIndicator z) = B.siteScale z ^ 2 := by
    intro z
    have h₀ : 0 ≤ B.bareSpaceNorm (B.blockIndicator z) := Real.sqrt_nonneg _
    have h₁ : 0 ≤ B.siteScale z ^ 2 := sq_nonneg _
    have h₂ : B.bareSpaceNorm (B.blockIndicator z) ^ 2 = (B.siteScale z ^ 2) ^ 2 := by
      rw [hnorm z]
      ring
    exact (pow_left_inj₀ h₀ h₁ two_ne_zero).1 h₂
  set U : ↥B.allSites → D.BareSite → ℝ := fun z =>
    (B.admissibleGreen W 𝔟 (B.blockIndicatorIn W z) : D.BareSite → ℝ) with hUdef
  have hbound : ∀ w : ↥B.allSites, (w : D.Space) ∈ B.sitesIn W → ∀ z : ↥B.allSites,
      TorusData.siteNorm (B.block z) (U w) ≤
        weightedBoundConst 4 D.L * B.siteScale z * B.siteScale w *
          Real.exp (-(greenDecayRate 4 D.L * B.weightedDistance z w)) * B.siteScale w ^ 2 := by
    intro w hw z
    have h := (hdecay w hw ⟨B.blockIndicator w, hmem w⟩ (hvan w) z z.2).2
    have hco : (B.admissibleGreenExt W 𝔟 ⟨B.blockIndicator w, hmem w⟩ : D.BareSite → ℝ) = U w := by
      change (B.admissibleGreen W 𝔟
        (B.restrictBare W ⟨B.blockIndicator w, hmem w⟩) : D.BareSite → ℝ) = U w
      rw [hres w]
    rw [hco] at h
    change _ ≤ _ * B.bareSpaceNorm (B.blockIndicator w) at h
    rwa [hchi w] at h
  have hprod : |B.bareInner (U y) (U y')| ≤
      ∑ z : ↥B.allSites,
        TorusData.siteNorm (B.block z) (U y) * TorusData.siteNorm (B.block z) (U y') := by
    rw [bareInner_eq_sum B hb, finsum_eq_sum_of_fintype]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun z _ => abs_inner_on_sites_le _ _ _)
  set K : ℝ := weightedBoundConst 4 D.L ^ 2 * (D.L : ℝ) ^ 2 *
    Real.exp (-(1 / 2 * greenDecayRate 4 D.L * B.weightedDistance (y : D.Space) (y' : D.Space)))
    with hK
  have hK₀ : 0 ≤ K := by
    rw [hK]
    positivity
  have hterm : ∀ z : ↥B.allSites,
      B.siteScale y ^ (-4 : ℤ) * B.siteScale y' ^ (-4 : ℤ) *
          (TorusData.siteNorm (B.block z) (U y) * TorusData.siteNorm (B.block z) (U y')) ≤
        K * Real.exp (-(1 / 4 * greenDecayRate 4 D.L) * B.weightedDistance y z) := by
    intro z
    have h₁ := hbound y hy z
    rw [weightedDistance_comm B (z : D.Space) (y : D.Space)] at h₁
    have h₂ := hratio z z.2 y y.2
    rw [weightedDistance_comm B (z : D.Space) (y : D.Space)] at h₂
    exact term_le (siteScale_pos B z) (siteScale_pos B y) (siteScale_pos B y')
      hLpos.le hε.le hrate (hnn y y.2 z z.2) (hnn z z.2 y' y'.2) (hdist y z y')
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) h₁ (hbound y' hy' z) h₂ (hratio z z.2 y' y'.2)
  have hp : 0 ≤ B.siteScale y ^ (-4 : ℤ) * B.siteScale y' ^ (-4 : ℤ) := by
    have h₁ := siteScale_pos B y
    have h₂ := siteScale_pos B y'
    positivity
  have hsum' : ∑ z : ↥B.allSites,
      Real.exp (-(1 / 4 * greenDecayRate 4 D.L) * B.weightedDistance y z) ≤
        latticeSumConst 4 D.L (1 / 4 * greenDecayRate 4 D.L) := by
    have h := hsum y
    rwa [finsum_eq_sum_of_fintype] at h
  rw [hmat y y' hy hy', abs_mul, abs_of_nonneg hp]
  calc B.siteScale y ^ (-4 : ℤ) * B.siteScale y' ^ (-4 : ℤ) * |B.bareInner (U y) (U y')|
      ≤ B.siteScale y ^ (-4 : ℤ) * B.siteScale y' ^ (-4 : ℤ) *
          ∑ z : ↥B.allSites,
            TorusData.siteNorm (B.block z) (U y) * TorusData.siteNorm (B.block z) (U y') :=
        mul_le_mul_of_nonneg_left hprod hp
    _ = ∑ z : ↥B.allSites, B.siteScale y ^ (-4 : ℤ) * B.siteScale y' ^ (-4 : ℤ) *
          (TorusData.siteNorm (B.block z) (U y) * TorusData.siteNorm (B.block z) (U y')) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ z : ↥B.allSites,
          K * Real.exp (-(1 / 4 * greenDecayRate 4 D.L) * B.weightedDistance y z) :=
        Finset.sum_le_sum fun z _ => hterm z
    _ = K * ∑ z : ↥B.allSites,
          Real.exp (-(1 / 4 * greenDecayRate 4 D.L) * B.weightedDistance y z) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ K * latticeSumConst 4 D.L (1 / 4 * greenDecayRate 4 D.L) :=
        mul_le_mul_of_nonneg_left hsum' hK₀
    _ = upperBoundConst 4 D.L *
          Real.exp (-(1 / 2 * greenDecayRate 4 D.L *
            B.weightedDistance (y : D.Space) (y' : D.Space))) := by
        rw [hK]
        unfold upperBoundConst
        ring
theorem exists_layer_of_mem_allSites {y : D.Space} (hy : y ∈ B.allSites) : ∃ n, y ∈ B.layer n := by
  unfold SeparatedChain.allSites at hy
  simp only [mem_iUnion] at hy
  obtain ⟨n, -, h⟩ := hy
  exact ⟨n, h.2⟩
theorem statement_holds (hSums : ChainSiteSumBounds)
    (hWeighted : CoercivityWeightedBounds)
    (hPairs : AdmissiblePairOperators)
    (hAveraging : AvgAndMatrixFacts)
    (hSetting : GivenChainGeneralFacts) : Statement := by
  intro G hR W 𝔟 hW y y' hy hy'
  obtain ⟨-, -, hlayer, hratio, hk⟩ := hSums G.data G.chain
  obtain ⟨-, -, hdecay⟩ := hWeighted G.data G.chain W 𝔟 hW
  obtain ⟨hop, -⟩ := hPairs G
  obtain ⟨-, -, -, -, -, hmat⟩ := hop W 𝔟 hW
  obtain ⟨⟨-, -, -, hnorm, -⟩, -⟩ := hAveraging G
  obtain ⟨-, -, -, -, hb, hdist⟩ := hSetting G
  have hL1 : (1 : ℝ) ≤ G.data.L := by
    have := G.data.blocking.three_le_factor
    have h : 1 ≤ G.data.L := by omega
    exact_mod_cast h
  have hLpos : (0 : ℝ) < G.data.L := by linarith
  have hlog : 0 ≤ Real.log (G.data.L : ℝ) := Real.log_nonneg hL1
  have hε : 0 < greenDecayRate 4 G.data.L := by
    unfold greenDecayRate
    positivity
  have hRM : (0 : ℝ) ≤ (G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) := by positivity
  have hR' : 8 * (4 * Real.log (G.data.L : ℝ) + 1) ≤
      (G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) * greenDecayRate 4 G.data.L :=
    (div_le_iff₀ hε).1 hR
  have hRMpos : (0 : ℝ) < (G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) := by
    rcases hRM.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hR'
      linarith
  have hrate : G.data.scaleRatioRate ≤ 1 / 4 * greenDecayRate 4 G.data.L := by
    unfold TorusData.scaleRatioRate
    rw [div_le_iff₀ hRMpos]
    linarith
  have hfloor : latticeSumRadius 4 G.data.L (1 / 4 * greenDecayRate 4 G.data.L) ≤
      (G.data.gapNumber : ℝ) * (G.data.blockNumber : ℝ) := by
    have h : latticeSumRadius 4 G.data.L (1 / 4 * greenDecayRate 4 G.data.L) =
        8 * (4 * Real.log (G.data.L : ℝ) + 1) / greenDecayRate 4 G.data.L := by
      unfold latticeSumRadius
      push_cast
      field_simp
      ring
    rw [h]
    exact hR
  have hκ : 0 < 1 / 4 * greenDecayRate 4 G.data.L := by positivity
  have hnn : ∀ z ∈ G.chain.allSites, ∀ z' ∈ G.chain.allSites,
      0 ≤ G.chain.weightedDistance z z' := by
    intro z hz z' hz'
    obtain ⟨n, hn⟩ := exists_layer_of_mem_allSites G.chain hz
    obtain ⟨n', hn'⟩ := exists_layer_of_mem_allSites G.chain hz'
    exact (mul_nonneg hRM (le_max_right _ _)).trans (hlayer n n' z hn z' hn')
  have hratio' : ∀ z ∈ G.chain.allSites, ∀ z' ∈ G.chain.allSites,
      G.chain.siteScale z / G.chain.siteScale z' ≤
        (G.data.L : ℝ) * Real.exp (G.data.scaleRatioRate * G.chain.weightedDistance z z') := by
    intro z hz z' hz'
    have h := hratio 1 z hz z' hz'
    simpa only [abs_one, Real.rpow_one, one_mul] using h
  exact bound_of_hyps G.chain hb W 𝔟 hdist hnn hrate hratio'
    (fun z => (hk _ hκ hfloor).1 z) hnorm hdecay hmat y y' hy hy'
end ScaledMatrixBound
end YangMills.Construction.Weighted
