import YangMills.Construction.Torus.BlockIndicatorOnAUnionOfBlocksProof
import YangMills.Construction.Torus.CoercivityAndWeightedBoundsOfAnAdmissiblePairProof
import YangMills.Construction.Torus.DistanceAveragesWholePairMatricesAndNorms
import YangMills.Construction.Torus.OperatorsOfAnAdmissiblePair
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.Weighted.DistanceAvgPairMatrixNormProof
section Numbers
variable (D : TorusData)
theorem L_ge_three : 3 ≤ D.L := D.blocking.three_le_factor
theorem L_pos_real : (0 : ℝ) < D.L := by
  have := L_ge_three D
  exact_mod_cast (by omega : 0 < D.L)
theorem scale_pos (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
end Numbers
section Weights
theorem avgWeight_succ_eq (L : ℕ) (hL : 3 ≤ L) (n : ℕ) :
    avgWeight L (n + 1) =
      (1 - ((L : ℝ) ^ 2)⁻¹) / (1 - (((L : ℝ) ^ 2)⁻¹) ^ (n + 1)) := by
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  set u : ℝ := ((L : ℝ) ^ 2)⁻¹ with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u < 1 := by
    rw [hu]
    apply inv_lt_one_of_one_lt₀
    nlinarith only [hL']
  have hv : ∀ k : ℕ, u ^ (k + 1) < 1 := fun k => pow_lt_one₀ hu0.le hu1 (by omega)
  induction n with
  | zero =>
    have : 1 - u ≠ 0 := (sub_pos.2 hu1).ne'
    simp [avgWeight, this]
  | succ n ih =>
    have h1 : avgWeight L (n + 1 + 1) =
        avgWeight L (n + 1) / (((L : ℝ) ^ 2)⁻¹ + avgWeight L (n + 1)) := by
      rw [avgWeight]
    rw [h1, ih]
    have hA : 1 - u ^ (n + 1) ≠ 0 := (sub_pos.2 (hv n)).ne'
    have hB : 1 - u ^ (n + 1 + 1) ≠ 0 := (sub_pos.2 (hv (n + 1))).ne'
    have hC : 1 - u ≠ 0 := (sub_pos.2 hu1).ne'
    have hD : u + (1 - u) / (1 - u ^ (n + 1)) ≠ 0 :=
      (add_pos hu0 (div_pos (sub_pos.2 hu1) (sub_pos.2 (hv n)))).ne'
    rw [div_eq_div_iff hD hB]
    field_simp
    ring
theorem avgWeightClosedForm_holds (L : ℕ) (hL : 3 ≤ L) : AvgWeightClosedForm L := by
  have hL' : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hu0 : 0 < ((L : ℝ) ^ 2)⁻¹ := by positivity
  have hu1 : ((L : ℝ) ^ 2)⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀
    nlinarith only [hL']
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [avgWeight_succ_eq L hL k, pow_mul, inv_pow]
  · intro n
    cases n with
    | zero =>
      simp only [avgWeight]
      exact ⟨by linarith only [hu0], le_refl _⟩
    | succ k =>
      rw [avgWeight_succ_eq L hL k]
      set u : ℝ := ((L : ℝ) ^ 2)⁻¹ with hu
      have hvu : u ^ (k + 1) ≤ u := by
        calc u ^ (k + 1) ≤ u ^ 1 := pow_le_pow_of_le_one hu0.le hu1.le (by omega)
          _ = u := pow_one u
      have hv0 : 0 < u ^ (k + 1) := by positivity
      have hd : 0 < 1 - u ^ (k + 1) := by linarith only [hvu, hu1]
      constructor
      · rw [lt_div_iff₀ hd]
        nlinarith only [mul_pos (sub_pos.2 hu1) hv0]
      · rw [div_le_one hd]
        linarith only [hvu]
end Weights
section Distance
variable {D : TorusData} (B : SeparatedChain D)
theorem torusProj_surjective (x : D.Space) : ∃ v, torusProj D.side v = x := by
  choose v hv using fun μ => QuotientAddGroup.mk_surjective (x μ)
  exact ⟨v, funext hv⟩
theorem torusProj_continuous : Continuous (torusProj D.side) :=
  continuous_pi fun _ => (continuous_quotient_mk').comp (continuous_apply _)
theorem segment_isConnected (s : LiftedSegment) : IsConnected (s.support D.side) := by
  refine IsConnected.image ⟨⟨0, by simp⟩, isPreconnected_Icc⟩ _ ?_
  refine Continuous.continuousOn ?_
  unfold LiftedSegment.pointAt
  exact (torusProj_continuous (D := D)).comp (by fun_prop)
theorem segmentsSupport_singleton (s : LiftedSegment) :
    segmentsSupport D.side [s] = s.support D.side := by
  simp [segmentsSupport]
theorem segmentsSupport_append (Γ Γ' : List LiftedSegment) :
    segmentsSupport D.side (Γ ++ Γ') = segmentsSupport D.side Γ ∪ segmentsSupport D.side Γ' := by
  ext x
  simp only [segmentsSupport, mem_iUnion, mem_union, List.mem_append, exists_prop]
  constructor
  · rintro ⟨s, hs | hs, hx⟩
    · exact Or.inl ⟨s, hs, hx⟩
    · exact Or.inr ⟨s, hs, hx⟩
  · rintro (⟨s, hs, hx⟩ | ⟨s, hs, hx⟩)
    · exact ⟨s, Or.inl hs, hx⟩
    · exact ⟨s, Or.inr hs, hx⟩
theorem pathLengthIn_append (Γ Γ' : List LiftedSegment) (A : Set D.Space) :
    pathLengthIn D.side (Γ ++ Γ') A = pathLengthIn D.side Γ A + pathLengthIn D.side Γ' A := by
  simp [pathLengthIn, List.map_append, List.sum_append]
theorem chainLength_nonneg (Γ : List LiftedSegment) : 0 ≤ B.weightedLength Γ := by apply _root_.YangMills.Construction.Weighted.DistBounds.weightedLength_nonneg <;> assumption
theorem chainLength_append (Γ Γ' : List LiftedSegment) :
    B.weightedLength (Γ ++ Γ') = B.weightedLength Γ + B.weightedLength Γ' := by
  unfold SeparatedChain.weightedLength
  simp only [pathLengthIn_append, mul_add, Finset.sum_add_distrib]
  ring
theorem exists_tree_joining (x x' : D.Space) : ∃ Γ : List LiftedSegment,
    IsTreeGraph D.side Γ ∧ x ∈ segmentsSupport D.side Γ ∧ x' ∈ segmentsSupport D.side Γ := by
  obtain ⟨v, rfl⟩ := torusProj_surjective x
  obtain ⟨v', rfl⟩ := torusProj_surjective x'
  refine ⟨[⟨v, v'⟩], ?_, ?_, ?_⟩
  · unfold IsTreeGraph
    rw [segmentsSupport_singleton]
    exact segment_isConnected _
  · rw [segmentsSupport_singleton]
    exact ⟨0, by simp, by simp [LiftedSegment.pointAt]⟩
  · rw [segmentsSupport_singleton]
    exact ⟨1, by simp, by simp [LiftedSegment.pointAt, LiftedSegment.displacement]⟩
theorem lengths_bddBelow (x x' : D.Space) : BddBelow {r | ∃ Γ : List LiftedSegment,
    IsTreeGraph D.side Γ ∧ x ∈ segmentsSupport D.side Γ ∧ x' ∈ segmentsSupport D.side Γ ∧
      r = B.weightedLength Γ} := by
  refine ⟨0, ?_⟩
  rintro r ⟨Γ, -, -, -, rfl⟩
  exact chainLength_nonneg B Γ
theorem lengthSet_nonempty (x x' : D.Space) : {r | ∃ Γ : List LiftedSegment,
    IsTreeGraph D.side Γ ∧ x ∈ segmentsSupport D.side Γ ∧ x' ∈ segmentsSupport D.side Γ ∧
      r = B.weightedLength Γ}.Nonempty := by
  obtain ⟨Γ, h1, h2, h3⟩ := exists_tree_joining x x'
  exact ⟨_, Γ, h1, h2, h3, rfl⟩
theorem weightedDist_nonneg (x x' : D.Space) : 0 ≤ B.weightedDistance x x' := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.weightedDistance_nonneg <;> assumption
theorem weightedDist_comm (x x' : D.Space) :
    B.weightedDistance x x' = B.weightedDistance x' x := by apply _root_.YangMills.Construction.Weighted.DistBounds.weightedDistance_comm <;> assumption
theorem weightedDist_triangle (x x' x'' : D.Space) :
    B.weightedDistance x x'' ≤ B.weightedDistance x x' + B.weightedDistance x' x'' := by
  have key : ∀ Γ Γ' : List LiftedSegment, IsTreeGraph D.side Γ → x ∈ segmentsSupport D.side Γ →
      x' ∈ segmentsSupport D.side Γ → IsTreeGraph D.side Γ' → x' ∈ segmentsSupport D.side Γ' →
      x'' ∈ segmentsSupport D.side Γ' →
      B.weightedDistance x x'' ≤ B.weightedLength Γ + B.weightedLength Γ' := by
    intro Γ Γ' h1 h2 h3 h1' h2' h3'
    rw [← chainLength_append]
    refine csInf_le (lengths_bddBelow B _ _) ⟨Γ ++ Γ', ?_, ?_, ?_, rfl⟩
    · unfold IsTreeGraph at h1 h1' ⊢
      rw [segmentsSupport_append]
      exact IsConnected.union ⟨x', h3, h2'⟩ h1 h1'
    · rw [segmentsSupport_append]
      exact Or.inl h2
    · rw [segmentsSupport_append]
      exact Or.inr h3'
  have step : ∀ Γ' : List LiftedSegment, IsTreeGraph D.side Γ' → x' ∈ segmentsSupport D.side Γ' →
      x'' ∈ segmentsSupport D.side Γ' →
      B.weightedDistance x x'' - B.weightedLength Γ' ≤ B.weightedDistance x x' := by
    intro Γ' h1' h2' h3'
    refine le_csInf (lengthSet_nonempty B _ _) ?_
    rintro r ⟨Γ, h1, h2, h3, rfl⟩
    have := key Γ Γ' h1 h2 h3 h1' h2' h3'
    linarith only [this]
  have final : B.weightedDistance x x'' - B.weightedDistance x x' ≤ B.weightedDistance x' x'' := by
    refine le_csInf (lengthSet_nonempty B _ _) ?_
    rintro r ⟨Γ', h1', h2', h3', rfl⟩
    have := step Γ' h1' h2' h3'
    linarith only [this]
  linarith only [final]
theorem weightedDist_symm_triangle : B.WeightedDistanceSymmTriangle :=
  ⟨weightedDist_comm B, weightedDist_triangle B⟩
end Distance
section Blocks
variable {D : TorusData} (B : SeparatedChain D)
theorem partition_facts (hP : CubesLayersBlocksBallsHold) :
    B.SiteCubesTile ∧ B.BlocksPartition ∧
      ∀ n, ∀ y ∈ B.layerSites n, B.BlockDescription n y := by
  obtain ⟨m, hm⟩ := D.blockNumber_power
  have hL : (1 : ℝ) ≤ D.L := by
    have := L_ge_three D
    exact_mod_cast (by omega : 1 ≤ D.L)
  have hbn : (1 : ℝ) ≤ D.blockNumber := by
    have h1 : 3 ≤ D.blockNumber := le_trans (L_ge_three D) D.le_blockNumber
    exact_mod_cast (by omega : 1 ≤ D.blockNumber)
  have hle : D.scale 0 ≤ (D.blockNumber : ℝ) * D.scale D.top := by
    have hb := D.bareSpacing_pos
    have h1 : (1 : ℝ) ≤ (D.L : ℝ) ^ D.top := one_le_pow₀ hL
    have h2 : D.bareSpacing ≤ (D.L : ℝ) ^ D.top * D.bareSpacing :=
      le_mul_of_one_le_left hb.le h1
    have h3 : 0 ≤ (D.L : ℝ) ^ D.top * D.bareSpacing := by positivity
    simp only [TorusData.scale, pow_zero, one_mul]
    nlinarith only [h2, h3, hbn]
  obtain ⟨-, -, -, -, h1, h2, h3, -⟩ := hP D B m hm 0 0 le_rfl hle
  exact ⟨h1, h2, h3⟩
theorem mem_layerSites_at_level {y : D.Space} (hy : y ∈ B.allSites) :
    y ∈ B.layerSites (B.level y) := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.mem_layerSites_level <;> assumption
theorem siteScale_pos (y : D.Space) : 0 < B.siteScale y := scale_pos D _
theorem siteScale_eq (y : D.Space) : B.siteScale y = D.scale (B.level y) := rfl
variable (hP : CubesLayersBlocksBallsHold)
include hP
theorem block_description {y : D.Space} (hy : y ∈ B.allSites) :
    B.BlockDescription (B.level y) y :=
  (partition_facts B hP).2.2 _ _ (mem_layerSites_at_level B hy)
theorem allSites_finite : Finite ↥B.allSites := by
  have := D.bareSite_finite
  refine Set.Finite.to_subtype ((finite_range (Subtype.val : D.BareSite → D.Space)).subset ?_)
  intro y hy
  obtain ⟨x, -, rfl⟩ := (block_description B hP hy).2.2.2.2.1
  exact ⟨x, rfl⟩
theorem block_subset_base {y : D.Space} (hy : y ∈ B.allSites) :
    B.block y ⊆ D.bareSites (B.stage 0) := by apply _root_.YangMills.Construction.Weighted.BlockUnionIndicator.block_subset_bareSites_stage_zero <;> assumption
theorem blockCenter_spec {x : D.BareSite} (hx : x ∈ D.bareSites (B.stage 0)) :
    B.blockCenter x ∈ B.allSites ∧ x ∈ B.block (B.blockCenter x) := by
  have hex : ∃ y, y ∈ B.allSites ∧ x ∈ B.block y := by
    rw [← (partition_facts B hP).2.1.2] at hx
    simp only [mem_iUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨y, hy, hxy⟩
  exact Classical.epsilon_spec hex
theorem eq_of_mem_blocks {y y' : D.Space} (hy : y ∈ B.allSites) (hy' : y' ∈ B.allSites)
    {x : D.BareSite} (h : x ∈ B.block y) (h' : x ∈ B.block y') : y = y' := by
  exact _root_.YangMills.Construction.Weighted.BlockUnionIndicator.eq_of_mem_block_of_mem_block
    B hP hy hy' h h'
omit hP
theorem finsum_blockIndicator_mul (f : D.BareSite → ℝ) {y : D.Space}
    (hs : B.block y ⊆ D.bareSites (B.stage 0)) :
    ∑ᶠ x ∈ D.bareSites (B.stage 0), B.blockIndicator y x * f x = ∑ᶠ x ∈ B.block y, f x := by
  rw [finsum_mem_def, finsum_mem_def]
  congr 1
  funext x
  by_cases hx : x ∈ B.block y
  · have := hs hx
    simp [indicator, hx, this, SeparatedChain.blockIndicator]
  · simp [indicator, hx, SeparatedChain.blockIndicator]
include hP
theorem avgOp_eq_inner (f : ↥B.bareSpace) (y : ↥B.allSites) :
    B.avgOp f y =
      B.siteScale y ^ (-4 : ℤ) * B.bareInner (B.blockIndicator y) (f : D.BareSite → ℝ) := by
  have hs := block_subset_base B hP y.2
  have h1 : B.avgOp f y =
      ((D.L : ℝ) ^ (B.level y * 4))⁻¹ * ∑ᶠ x ∈ B.block y, (f : D.BareSite → ℝ) x := rfl
  rw [h1, SeparatedChain.bareInner, finsum_blockIndicator_mul B _ hs, siteScale_eq]
  have hL := L_pos_real D
  have hb := D.bareSpacing_pos
  simp only [TorusData.scale, pow_zero, one_mul]
  rw [zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, mul_pow, ← pow_mul]
  field_simp
theorem avgOp_at_base (f : ↥B.bareSpace) (y : ↥B.allSites) (x : D.BareSite)
    (hy : (y : D.Space) ∈ B.layerSites 0) (hx : (x : D.Space) = y) :
    B.avgOp f y = (f : D.BareSite → ℝ) x := by
  have hlev : B.level y = 0 := by
    have : B.level y ≤ 0 := Nat.sInf_le hy
    omega
  have hb := block_description B hP y.2
  rw [hlev] at hb
  have hxb : x ∈ B.block y := by
    obtain ⟨x', hx', he⟩ := hb.2.2.2.2.1
    have : x' = x := Subtype.ext (he.trans hx.symm)
    exact this ▸ hx'
  have hcard : (B.block y).ncard = 1 := by
    simpa using hb.2.2.1
  obtain ⟨a, ha⟩ := ncard_eq_one.1 hcard
  have hax : a = x := by
    rw [ha] at hxb
    exact (mem_singleton_iff.1 hxb).symm
  have h1 : B.avgOp f y =
      ((D.L : ℝ) ^ (B.level y * 4))⁻¹ * ∑ᶠ x ∈ B.block y, (f : D.BareSite → ℝ) x := rfl
  rw [h1, hlev, ha, hax, finsum_mem_singleton]
  simp
theorem avgOpAdjoint_eq_sum (hT : ∀ w : B.LayerFn,
      ∀ x ∈ D.bareSites (B.stage 0),
      (B.avgOpAdjoint w : D.BareSite → ℝ) x = B.layerEval w (B.blockCenter x))
    (w : B.LayerFn) :
    (B.avgOpAdjoint w : D.BareSite → ℝ) =
      fun x => ∑ᶠ y : ↥B.allSites, w y * B.blockIndicator y x := by
  funext x
  by_cases hx : x ∈ D.bareSites (B.stage 0)
  · rw [hT w x hx]
    obtain ⟨hc, hxc⟩ := blockCenter_spec B hP hx
    rw [finsum_eq_single _ (⟨B.blockCenter x, hc⟩ : ↥B.allSites)]
    · have : B.blockIndicator (B.blockCenter x) x = 1 := by
        simp [SeparatedChain.blockIndicator, hxc]
      simp [SeparatedChain.layerEval, hc, this]
    · intro y hy
      have hnot : x ∉ B.block y := fun h =>
        hy (Subtype.ext (eq_of_mem_blocks B hP y.2 hc h hxc))
      simp [SeparatedChain.blockIndicator, hnot]
  · have h0 : (B.avgOpAdjoint w : D.BareSite → ℝ) x = 0 := (B.avgOpAdjoint w).2 x hx
    rw [h0]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro y
    have hnot : x ∉ B.block y := fun h => hx (block_subset_base B hP y.2 h)
    simp [SeparatedChain.blockIndicator, hnot]
theorem avgAndAdjoint_holds (hne : (B.stage 0).Nonempty)
    (hO : AvgAndMatrixFacts) : B.AvgAndAdjointFormulas := by
  have hR : B.AvgRelations := (hO ⟨D, B, hne⟩).1
  have hsum := avgOpAdjoint_eq_sum B hP hR.2.1
  refine ⟨avgOp_eq_inner B hP, fun f y x hy hx => avgOp_at_base B hP f y x hy hx, ?_,
    hR.1, hsum, hR.2.1⟩
  intro f w
  rw [hR.1 f w, hsum w]
omit hP
theorem weightedAvgForm_holds (hne : (B.stage 0).Nonempty)
    (hO : AvgAndMatrixFacts) : B.WeightedAvgQuadratic := by
  have hR : B.WeightedAvgForm := (hO ⟨D, B, hne⟩).2.1
  refine ⟨hR.1, hR.2, ?_⟩
  intro f hf
  apply Subtype.ext
  funext x
  have h1 : ((B.weightedAvg f : ↥B.bareSpace) : D.BareSite → ℝ) x =
      (D.bareSites (B.stage 0)).indicator (fun x =>
        avgWeight D.L (B.bareLevel x) * (B.bareScale x ^ 2)⁻¹ *
          B.layerEval (B.avgOp f) (B.blockCenter x)) x := rfl
  rw [h1, hf]
  simp
end Blocks
section Laplacian
variable {D : TorusData}
theorem torusProj_add (a b : Fin 4 → ℝ) :
    torusProj D.side (a + b) = torusProj D.side a + torusProj D.side b := by
  funext μ
  simp [torusProj]
theorem bareShift_coe (x : D.BareSite) (σ : Fin 4 → ℤ) :
    ((TorusData.bareShift x σ : D.BareSite) : D.Space) =
      (x : D.Space) + torusProj D.side fun μ => D.scale 0 * (σ μ : ℝ) := rfl
theorem bareShift_bareShift (x : D.BareSite) (σ τ : Fin 4 → ℤ) :
    TorusData.bareShift (TorusData.bareShift x σ) τ = TorusData.bareShift x (σ + τ) := by
  apply Subtype.ext
  simp only [bareShift_coe]
  rw [add_assoc, ← torusProj_add]
  congr 2
  funext μ
  simp [mul_add]
theorem bareShift_zero (x : D.BareSite) : TorusData.bareShift x 0 = x := by
  apply Subtype.ext
  rw [bareShift_coe]
  have : torusProj D.side (fun μ => D.scale 0 * (((0 : Fin 4 → ℤ) μ : ℤ) : ℝ)) = 0 := by
    funext μ
    simp [torusProj]
  rw [this, add_zero]
def unitStepEquiv (μ : Fin 4) : D.BareSite ≃ D.BareSite where
  toFun x := TorusData.bareShift x (Pi.single μ 1)
  invFun x := TorusData.bareShift x (Pi.single μ (-1))
  left_inv x := by
    change TorusData.bareShift (TorusData.bareShift x (Pi.single μ 1)) (Pi.single μ (-1)) = x
    rw [bareShift_bareShift, ← Pi.single_add]
    simp [bareShift_zero]
  right_inv x := by
    change TorusData.bareShift (TorusData.bareShift x (Pi.single μ (-1))) (Pi.single μ 1) = x
    rw [bareShift_bareShift, ← Pi.single_add]
    simp [bareShift_zero]
theorem unitStepEquiv_sub (x : D.BareSite) (μ : Fin 4) :
    ((unitStepEquiv μ x : D.BareSite) : D.Space) - (x : D.Space) = D.unitStep μ := by
  change ((TorusData.bareShift x (Pi.single μ 1) : D.BareSite) : D.Space) - _ = _
  rw [bareShift_coe, add_sub_cancel_left]
  unfold TorusData.unitStep
  congr 1
  funext ν
  by_cases h : ν = μ
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]
def bondAt (x : D.BareSite) (μ : Fin 4) : D.Bond := ⟨x, unitStepEquiv μ x, μ, unitStepEquiv_sub x μ⟩
theorem scale_zero_lt_side : D.scale 0 < D.side := by
  obtain ⟨k, hk, hs⟩ := D.side_multiple
  have hb := D.bareSpacing_pos
  have hL : (1 : ℝ) ≤ D.L := by
    have := L_ge_three D
    exact_mod_cast (by omega : 1 ≤ D.L)
  have hbn : (1 : ℝ) ≤ D.blockNumber := by
    have h1 : 3 ≤ D.blockNumber := le_trans (L_ge_three D) D.le_blockNumber
    exact_mod_cast (by omega : 1 ≤ D.blockNumber)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (1 : ℝ) ≤ (D.L : ℝ) ^ D.top := one_le_pow₀ hL
  have h2 : (1 : ℝ) ≤ (D.blockNumber : ℝ) * (D.L : ℝ) ^ D.top := by nlinarith only [hbn, h1]
  have h3 : (2 : ℝ) ≤ 2 * k * ((D.blockNumber : ℝ) * (D.L : ℝ) ^ D.top) := by
    nlinarith only [hk', h2]
  have h4 : D.side = 2 * k * ((D.blockNumber : ℝ) * (D.L : ℝ) ^ D.top) * D.bareSpacing := by
    rw [hs]
    ring
  simp only [TorusData.scale, pow_zero, one_mul]
  rw [h4]
  nlinarith only [h3, hb]
theorem scale_zero_coe_ne_zero : ((D.scale 0 : ℝ) : AddCircle D.side) ≠ 0 := by
  intro h
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hlt := scale_zero_lt_side (D := D)
  have hpos := scale_pos D 0
  have hs : 0 < D.side := hpos.trans hlt
  rw [zsmul_eq_mul] at hn
  rcases le_or_gt n 0 with h0 | h0
  · have : (n : ℝ) ≤ 0 := by exact_mod_cast h0
    nlinarith only [this, hs, hpos, hn]
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h0
    nlinarith only [this, hs, hlt, hn]
theorem unitStep_injective : Function.Injective D.unitStep := by
  intro μ ν h
  by_contra hne
  have h1 := congrFun h μ
  simp only [TorusData.unitStep, torusProj, Pi.single_eq_same, Pi.single_eq_of_ne hne] at h1
  exact scale_zero_coe_ne_zero (D := D) (by simpa using h1)
theorem bondAt_bijective :
    Function.Bijective (fun p : D.BareSite × Fin 4 => bondAt p.1 p.2) := by
  constructor
  · rintro ⟨x, μ⟩ ⟨x', μ'⟩ h
    have ht : x = x' := congrArg TorusData.Bond.source h
    subst ht
    have hh : unitStepEquiv μ x = unitStepEquiv μ' x := congrArg TorusData.Bond.target h
    have : D.unitStep μ = D.unitStep μ' := by
      rw [← unitStepEquiv_sub x μ, ← unitStepEquiv_sub x μ', hh]
    rw [unitStep_injective this]
  · intro b
    obtain ⟨μ, hμ⟩ := b.isPositive
    refine ⟨(b.source, μ), ?_⟩
    apply TorusData.Bond.ext
    · rfl
    · apply Subtype.ext
      have h1 := unitStepEquiv_sub b.source μ
      have : ((unitStepEquiv μ b.source : D.BareSite) : D.Space) - (b.source : D.Space) =
          (b.target : D.Space) - (b.source : D.Space) := by rw [h1, hμ]
      exact sub_left_injective this
theorem sum_shift_identity [Fintype D.BareSite] (μ : Fin 4) (f g : D.BareSite → ℝ) :
    ∑ x, (g (unitStepEquiv μ x) - g x) * (f (unitStepEquiv μ x) - f x) =
      ∑ x, g x * (2 * f x - f (unitStepEquiv μ x) - f ((unitStepEquiv μ).symm x)) := by
  have h1 : ∑ x, g (unitStepEquiv μ x) * f (unitStepEquiv μ x) = ∑ x, g x * f x :=
    Equiv.sum_comp (unitStepEquiv μ) (fun x => g x * f x)
  have h2 : ∑ x, g (unitStepEquiv μ x) * f x = ∑ x, g x * f ((unitStepEquiv μ).symm x) := by
    have := Equiv.sum_comp (unitStepEquiv μ) (fun x => g x * f ((unitStepEquiv μ).symm x))
    simpa using this
  calc ∑ x, (g (unitStepEquiv μ x) - g x) * (f (unitStepEquiv μ x) - f x)
      = ∑ x, g (unitStepEquiv μ x) * f (unitStepEquiv μ x) - ∑ x, g (unitStepEquiv μ x) * f x
          - ∑ x, g x * f (unitStepEquiv μ x) + ∑ x, g x * f x := by
        simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ = ∑ x, g x * f x - ∑ x, g x * f ((unitStepEquiv μ).symm x)
          - ∑ x, g x * f (unitStepEquiv μ x) + ∑ x, g x * f x := by rw [h1, h2]
    _ = _ := by
        simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
theorem bondForm_eq_lap (E : Set D.BareSite) (f g : D.BareSite → ℝ)
    (hg : ∀ x, x ∉ E → g x = 0) :
    D.scale 0 ^ 4 * ∑ᶠ b ∈ TorusData.bondsMeeting E,
        TorusData.bondGrad g b * TorusData.bondGrad f b =
      D.scale 0 ^ 4 * ∑ᶠ x ∈ E, g x * TorusData.bareLap f x := by
  classical
  have := D.bareSite_finite
  have : Finite D.Bond := Finite.of_surjective _ (bondAt_bijective (D := D)).2
  let _ : Fintype D.BareSite := Fintype.ofFinite _
  let _ : Fintype D.Bond := Fintype.ofFinite _
  have hξ := scale_pos D 0
  have h1 : ∑ᶠ b ∈ TorusData.bondsMeeting E, TorusData.bondGrad g b * TorusData.bondGrad f b =
      ∑ b, TorusData.bondGrad g b * TorusData.bondGrad f b := by
    rw [finsum_mem_def, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ∈ TorusData.bondsMeeting E
    · simp [indicator, hb]
    · have hb' : b.source ∉ E ∧ b.target ∉ E := by
        simpa [TorusData.bondsMeeting, not_or] using hb
      simp [indicator, hb, TorusData.bondGrad, TorusData.bondDiff, hg _ hb'.1, hg _ hb'.2]
  have h2 : ∑ᶠ x ∈ E, g x * TorusData.bareLap f x = ∑ x, g x * TorusData.bareLap f x := by
    rw [finsum_mem_def, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ E
    · simp [indicator, hx]
    · simp [indicator, hx, hg x hx]
  rw [h1, h2]
  congr 1
  have h3 : ∑ b, TorusData.bondGrad g b * TorusData.bondGrad f b =
      ∑ x, ∑ μ, TorusData.bondGrad g (bondAt x μ) * TorusData.bondGrad f (bondAt x μ) := by
    rw [← Fintype.sum_prod_type']
    exact (Equiv.sum_comp (Equiv.ofBijective _ (bondAt_bijective (D := D)))
      (fun b => TorusData.bondGrad g b * TorusData.bondGrad f b)).symm
  rw [h3, Finset.sum_comm]
  have h4 : ∀ μ : Fin 4,
      ∑ x, TorusData.bondGrad g (bondAt x μ) * TorusData.bondGrad f (bondAt x μ) =
      (D.scale 0 ^ 2)⁻¹ *
        ∑ x, g x * (2 * f x - f (unitStepEquiv μ x) - f ((unitStepEquiv μ).symm x)) := by
    intro μ
    rw [← sum_shift_identity, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [TorusData.bondGrad, TorusData.bondDiff, bondAt]
    field_simp
  have h5 : ∀ x, g x * TorusData.bareLap f x = (D.scale 0 ^ 2)⁻¹ *
      ∑ μ, g x * (2 * f x - f (unitStepEquiv μ x) - f ((unitStepEquiv μ).symm x)) := by
    intro x
    unfold TorusData.bareLap
    rw [← mul_assoc, mul_comm (g x), mul_assoc, Finset.mul_sum]
    rfl
  simp only [h4, h5]
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
theorem bareLap_add (f g : D.BareSite → ℝ) (x : D.BareSite) :
    TorusData.bareLap (f + g) x = TorusData.bareLap f x + TorusData.bareLap g x := by
  simp only [TorusData.bareLap, ← mul_add, ← Finset.sum_add_distrib, Pi.add_apply]
  congr 1
  exact Finset.sum_congr rfl fun μ _ => by ring
theorem bareLap_smul (c : ℝ) (f : D.BareSite → ℝ) (x : D.BareSite) :
    TorusData.bareLap (c • f) x = c * TorusData.bareLap f x := by
  simp only [TorusData.bareLap, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun μ _ => by ring
variable (B : SeparatedChain D)
def restrictedLap : Module.End ℝ ↥B.bareSpace where
  toFun f := ⟨(D.bareSites (B.stage 0)).indicator (TorusData.bareLap (f : D.BareSite → ℝ)),
    fun _ hx => indicator_of_notMem hx _⟩
  map_add' f g := by
    ext x
    by_cases h : x ∈ D.bareSites (B.stage 0)
    · simp [h, bareLap_add]
    · simp [h]
  map_smul' c f := by
    ext x
    by_cases h : x ∈ D.bareSites (B.stage 0)
    · simp [h, bareLap_smul]
    · simp [h]
theorem restrictedLap_apply (f : ↥B.bareSpace) {x : D.BareSite}
    (hx : x ∈ D.bareSites (B.stage 0)) :
    ((restrictedLap B f : ↥B.bareSpace) : D.BareSite → ℝ) x =
      TorusData.bareLap (f : D.BareSite → ℝ) x := by
  simp [restrictedLap, hx]
theorem bareInner_comm (f g : D.BareSite → ℝ) : B.bareInner f g = B.bareInner g f := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass.bareInner_comm <;> assumption
theorem bareInner_add_right (a b c : D.BareSite → ℝ) :
    B.bareInner a (b + c) = B.bareInner a b + B.bareInner a c := by
  have := D.bareSite_finite
  simp only [SeparatedChain.bareInner, Pi.add_apply, mul_add]
  rw [finsum_mem_add_distrib (toFinite _)]
  ring
theorem bareInner_sub_right (a b c : D.BareSite → ℝ) :
    B.bareInner a (b - c) = B.bareInner a b - B.bareInner a c := by
  have h := bareInner_add_right B a (b - c) c
  rw [sub_add_cancel] at h
  linarith only [h]
theorem bareInner_add_left (a b c : D.BareSite → ℝ) :
    B.bareInner (a + b) c = B.bareInner a c + B.bareInner b c := by apply _root_.YangMills.Construction.Weighted.CoercivityProof.bareInner_add_left <;> assumption
theorem eq_zero_of_bareInner_self (u : ↥B.bareSpace)
    (h : B.bareInner (u : D.BareSite → ℝ) u = 0) : u = 0 := by
  classical
  have := D.bareSite_finite
  let _ : Fintype D.BareSite := Fintype.ofFinite _
  have hξ := scale_pos D 0
  have h1 : ∑ᶠ x ∈ D.bareSites (B.stage 0),
      (u : D.BareSite → ℝ) x * (u : D.BareSite → ℝ) x = 0 := by
    have := (mul_eq_zero.1 h).resolve_left (by positivity)
    exact this
  rw [finsum_mem_eq_finite_toFinset_sum _ (toFinite _)] at h1
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ D.bareSites (B.stage 0)
  · have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_self_nonneg _)).1 h1 x
      (by simpa using hx)
    simpa using h2
  · exact u.2 x hx
theorem bareInner_polarization (P : Module.End ℝ ↥B.bareSpace)
    (hP : ∀ f g : ↥B.bareSpace, B.bareInner (P f) g = B.bareInner f (P g))
    (f g : ↥B.bareSpace) :
    B.bareInner f (P g) = (B.bareInner (f + g : ↥B.bareSpace) (P (f + g)) -
      B.bareInner f (P f) - B.bareInner g (P g)) / 2 := by
  have e : ((f + g : ↥B.bareSpace) : D.BareSite → ℝ) = f + g := rfl
  have e' : ((P (f + g) : ↥B.bareSpace) : D.BareSite → ℝ) = P f + P g := by
    rw [map_add]
    rfl
  rw [e, e', bareInner_add_left, bareInner_add_right, bareInner_add_right]
  have h := hP f g
  rw [bareInner_comm] at h
  linarith only [h]
theorem isDirichletLap_unique {P Q : Module.End ℝ ↥B.bareSpace}
    (hP : B.IsDirichletLap P) (hQ : B.IsDirichletLap Q) : P = Q := by
  ext1 g
  have hh : ∀ f : ↥B.bareSpace, B.bareInner f (P g) = B.bareInner f (Q g) := by
    intro f
    rw [bareInner_polarization B P hP.1, bareInner_polarization B Q hQ.1, hP.2, hP.2, hP.2,
      hQ.2, hQ.2, hQ.2]
  have h0 : P g - Q g = 0 := by
    apply eq_zero_of_bareInner_self
    have e : ((P g - Q g : ↥B.bareSpace) : D.BareSite → ℝ) = P g - Q g := rfl
    have h1 := hh (P g - Q g)
    rw [e] at h1 ⊢
    rw [bareInner_sub_right, h1, sub_self]
  exact sub_eq_zero.1 h0
theorem restrictedLap_form (f g : ↥B.bareSpace) :
    B.bareInner g (restrictedLap B f) =
      D.scale 0 ^ 4 * ∑ᶠ b ∈ TorusData.bondsMeeting (D.bareSites (B.stage 0)),
        TorusData.bondGrad (g : D.BareSite → ℝ) b * TorusData.bondGrad (f : D.BareSite → ℝ) b := by
  rw [bondForm_eq_lap _ _ _ g.2]
  simp only [SeparatedChain.bareInner]
  congr 1
  exact finsum_mem_congr rfl fun x hx => by rw [restrictedLap_apply B f hx]
theorem restrictedLap_isDirichletLap : B.IsDirichletLap (restrictedLap B) := by
  refine ⟨?_, ?_⟩
  · intro f g
    rw [bareInner_comm, restrictedLap_form, restrictedLap_form]
    simp only [mul_comm (TorusData.bondGrad (g : D.BareSite → ℝ) _)]
  · intro f
    rw [restrictedLap_form, TorusData.bondNorm, Real.sq_sqrt]
    · simp only [sq]
    · have hξ := scale_pos D 0
      refine mul_nonneg (by positivity) (finsum_mem_induction (fun r => 0 ≤ r) le_rfl
        (fun _ _ => add_nonneg) fun _ _ => sq_nonneg _)
theorem dirichletLap_eq_restrictedLap : B.dirichletLap = restrictedLap B :=
  isDirichletLap_unique B (Classical.epsilon_spec ⟨_, restrictedLap_isDirichletLap B⟩)
    (restrictedLap_isDirichletLap B)
theorem dirichletLapOnBase_holds : B.DirichletLapOnBase := by
  intro f x hx
  rw [dirichletLap_eq_restrictedLap, restrictedLap_apply B f hx]
end Laplacian
section Matrices
variable {D : TorusData} (B : SeparatedChain D)
theorem layerInner_comm (w w' : B.LayerFn) : B.layerInner w w' = B.layerInner w' w := by apply _root_.YangMills.Construction.SeparatedClasses.WeightedProjectionsOfClass.layerInner_comm <;> assumption
theorem siteScale_zpow_neg_two (y : D.Space) :
    B.siteScale y ^ (-2 : ℤ) = (B.siteScale y ^ 2)⁻¹ := by
  rw [zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
theorem mulOp_apply (m : ↥B.allSites → ℝ) (w : B.LayerFn) (y : ↥B.allSites) :
    B.mulOp m w y = m y * w y := rfl
theorem mulOp_comp_comm (m m' : ↥B.allSites → ℝ) :
    B.mulOp m ∘ₗ B.mulOp m' = B.mulOp m' ∘ₗ B.mulOp m := by
  refine LinearMap.ext fun w => funext fun y => ?_
  simp only [LinearMap.comp_apply, mulOp_apply]
  ring
theorem inverse_scaleOnLayer :
    Ring.inverse B.scaleOnLayer = B.mulOp fun y => (B.siteScale y)⁻¹ := by
  have h1 : (B.scaleOnLayer : Module.End ℝ B.LayerFn) *
      B.mulOp (fun y => (B.siteScale y)⁻¹) = 1 := by
    refine LinearMap.ext fun w => funext fun y => ?_
    have := (siteScale_pos B (y : D.Space)).ne'
    change B.siteScale y * ((B.siteScale y)⁻¹ * w y) = w y
    field_simp
  have h2 : (B.mulOp (fun y => (B.siteScale y)⁻¹) :
      Module.End ℝ B.LayerFn) * B.scaleOnLayer = 1 := by
    refine LinearMap.ext fun w => funext fun y => ?_
    have := (siteScale_pos B (y : D.Space)).ne'
    change (B.siteScale y)⁻¹ * (B.siteScale y * w y) = w y
    field_simp
  exact Ring.inverse_unit (⟨_, _, h1, h2⟩ : (Module.End ℝ B.LayerFn)ˣ)
theorem mulOp_commute (m m' : ↥B.allSites → ℝ) :
    Commute (B.mulOp m : Module.End ℝ B.LayerFn) (B.mulOp m') := mulOp_comp_comm B m m'
variable [Fintype ↥B.allSites]
theorem layerInner_eq_sum (w w' : B.LayerFn) :
    B.layerInner w w' = ∑ y : ↥B.allSites, B.siteScale y ^ 4 * (w y * w' y) :=
  finsum_eq_sum_of_fintype _
theorem layerInner_basisVec_left (y : ↥B.allSites) (w : B.LayerFn) :
    B.layerInner (B.basisVec y) w = B.siteScale y ^ 2 * w y := by
  classical
  rw [layerInner_eq_sum, Finset.sum_eq_single y]
  · have := (siteScale_pos B (y : D.Space)).ne'
    simp only [SeparatedChain.basisVec, indicator_of_mem (mem_singleton y),
      siteScale_zpow_neg_two]
    field_simp
  · intro y' _ hy
    simp [SeparatedChain.basisVec, hy]
  · simp
theorem matrixOf_eq (K : B.LayerOp) (y y' : ↥B.allSites) :
    B.matrixOf K y y' = B.siteScale y ^ 2 * K (B.basisVec y') y :=
  layerInner_basisVec_left B y _
theorem basisVec_expansion (w : B.LayerFn) :
    w = ∑ y : ↥B.allSites, (B.siteScale y ^ 2 * w y) • B.basisVec y := by
  classical
  funext y'
  rw [Finset.sum_apply, Finset.sum_eq_single y']
  · have := (siteScale_pos B (y' : D.Space)).ne'
    simp only [SeparatedChain.basisVec, Pi.smul_apply, smul_eq_mul,
      indicator_of_mem (mem_singleton y'), siteScale_zpow_neg_two]
    field_simp
  · intro y _ hy
    simp [SeparatedChain.basisVec, hy.symm]
  · simp
theorem apply_eq_matrix_sum (K : B.LayerOp) (w : B.LayerFn) (y : ↥B.allSites) :
    B.siteScale y ^ 2 * K w y =
      ∑ y' : ↥B.allSites, B.matrixOf K y y' * (B.siteScale y' ^ 2 * w y') := by
  conv_lhs => rw [basisVec_expansion B w]
  rw [map_sum, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, matrixOf_eq]
  ring
theorem matrixOf_comp (K K' : B.LayerOp) (y y' : ↥B.allSites) :
    B.matrixOf (K ∘ₗ K') y y' =
      ∑ y'' : ↥B.allSites, B.matrixOf K y y'' * B.matrixOf K' y'' y' := by
  rw [matrixOf_eq, LinearMap.comp_apply, apply_eq_matrix_sum]
  refine Finset.sum_congr rfl fun y'' _ => ?_
  rw [matrixOf_eq B K' y'' y']
omit [Fintype ↥B.allSites] in
theorem mulOp_basisVec (m : ↥B.allSites → ℝ) (y : ↥B.allSites) :
    B.mulOp m (B.basisVec y) = m y • B.basisVec y := by
  classical
  funext y'
  rw [mulOp_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : y' = y
  · rw [h]
  · simp [SeparatedChain.basisVec, h]
theorem matrixOf_mulOp_comp (K : B.LayerOp) (m m' : ↥B.allSites → ℝ) (y y' : ↥B.allSites) :
    B.matrixOf (B.mulOp m ∘ₗ K ∘ₗ B.mulOp m') y y' =
      m y * B.matrixOf K y y' * m' y' := by
  rw [matrixOf_eq, matrixOf_eq, LinearMap.comp_apply, LinearMap.comp_apply, mulOp_basisVec,
    map_smul, mulOp_apply, Pi.smul_apply, smul_eq_mul]
  ring
theorem layerInner_eq_coords (w w' : B.LayerFn) :
    B.layerInner w w' =
      ∑ y : ↥B.allSites, (B.siteScale y ^ 2 * w y) * (B.siteScale y ^ 2 * w' y) := by
  rw [layerInner_eq_sum]
  exact Finset.sum_congr rfl fun y _ => by ring
theorem layerInner_apply_eq_matrix (K : B.LayerOp) (w w' : B.LayerFn) :
    B.layerInner w (K w') =
      ∑ y : ↥B.allSites, ∑ y' : ↥B.allSites,
        (B.siteScale y ^ 2 * w y) * B.matrixOf K y y' * (B.siteScale y' ^ 2 * w' y') := by
  rw [layerInner_eq_coords]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [apply_eq_matrix_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y' _ => by ring
theorem selfAdjoint_iff_matrix_symm (K : B.LayerOp) :
    (∀ w w' : B.LayerFn, B.layerInner (K w) w' = B.layerInner w (K w')) ↔
      ∀ y y' : ↥B.allSites, B.matrixOf K y y' = B.matrixOf K y' y := by
  constructor
  · intro h y y'
    change B.layerInner (B.basisVec y) (K (B.basisVec y')) =
      B.layerInner (B.basisVec y') (K (B.basisVec y))
    rw [layerInner_comm, h]
  · intro h w w'
    rw [layerInner_comm, layerInner_apply_eq_matrix, layerInner_apply_eq_matrix, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
    rw [h y' y]
    ring
theorem sum_coords_sq (w : B.LayerFn) :
    ∑ y : ↥B.allSites, (B.siteScale y ^ 2 * w y) ^ 2 = B.layerSpaceNorm w ^ 2 := by
  have h0 : 0 ≤ B.layerInner w w := by
    rw [layerInner_eq_coords]
    exact Finset.sum_nonneg fun y _ => mul_self_nonneg _
  rw [SeparatedChain.layerSpaceNorm, Real.sq_sqrt h0, layerInner_eq_coords]
  exact Finset.sum_congr rfl fun y _ => by ring
theorem layerMatrixCalculus_holds (hL : B.BasisRelations) :
    B.LayerMatrixCalculus := by
  refine ⟨hL.1, hL.2.1, hL.2.2.1, hL.2.2.2.1, ?_, ?_, mulOp_comp_comm B, ?_, ?_, ?_, ?_, ?_⟩
  · intro K K' y y'
    rw [finsum_eq_sum_of_fintype]
    exact matrixOf_comp B K K' y y'
  · intro K m m' y y'
    exact matrixOf_mulOp_comp B K m m' y y'
  · intro m k
    exact (mulOp_commute B m _).pow_right k
  · intro m k
    rw [inverse_scaleOnLayer]
    exact (mulOp_commute B m _).pow_right k
  · exact selfAdjoint_iff_matrix_symm B
  · intro K w w'
    simp only [finsum_eq_sum_of_fintype]
    exact layerInner_apply_eq_matrix B K w w'
  · intro w
    rw [finsum_eq_sum_of_fintype]
    exact sum_coords_sq B w
theorem row_sum_le (δ : ℝ) (M : B.LayerMat) (y : ↥B.allSites) :
    ∑ y' : ↥B.allSites, |M y y'| * Real.exp (δ * B.weightedDistance y y') ≤
      B.expWeightedMatrixNorm δ M := by
  simp only [SeparatedChain.expWeightedMatrixNorm, finsum_eq_sum_of_fintype]
  exact le_max_of_le_left (le_ciSup (f := fun y : ↥B.allSites => ∑ y' : ↥B.allSites,
    |M y y'| * Real.exp (δ * B.weightedDistance y y')) (Set.finite_range _).bddAbove y)
theorem col_sum_le (δ : ℝ) (M : B.LayerMat) (y' : ↥B.allSites) :
    ∑ y : ↥B.allSites, |M y y'| * Real.exp (δ * B.weightedDistance y y') ≤
      B.expWeightedMatrixNorm δ M := by
  simp only [SeparatedChain.expWeightedMatrixNorm, finsum_eq_sum_of_fintype]
  exact le_max_of_le_right (le_ciSup (f := fun y' : ↥B.allSites => ∑ y : ↥B.allSites,
    |M y y'| * Real.exp (δ * B.weightedDistance y y')) (Set.finite_range _).bddAbove y')
theorem matNorm_nonneg (δ : ℝ) (M : B.LayerMat) : 0 ≤ B.expWeightedMatrixNorm δ M := by
  refine le_max_of_le_left (Real.iSup_nonneg fun y => ?_)
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_nonneg fun y' _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
theorem matNorm_le (δ C : ℝ) (M : B.LayerMat) (hC : 0 ≤ C)
    (hr : ∀ y : ↥B.allSites,
      ∑ y' : ↥B.allSites, |M y y'| * Real.exp (δ * B.weightedDistance y y') ≤ C)
    (hc : ∀ y' : ↥B.allSites,
      ∑ y : ↥B.allSites, |M y y'| * Real.exp (δ * B.weightedDistance y y') ≤ C) :
    B.expWeightedMatrixNorm δ M ≤ C := by
  simp only [SeparatedChain.expWeightedMatrixNorm, finsum_eq_sum_of_fintype]
  exact max_le (Real.iSup_le hr hC) (Real.iSup_le hc hC)
theorem matNorm_mono (M : B.LayerMat) {δ δ' : ℝ} (h : δ' ≤ δ) :
    B.expWeightedMatrixNorm δ' M ≤ B.expWeightedMatrixNorm δ M := by
  have hterm : ∀ y y' : ↥B.allSites, |M y y'| * Real.exp (δ' * B.weightedDistance y y') ≤
      |M y y'| * Real.exp (δ * B.weightedDistance y y') := fun y y' =>
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h
      (weightedDist_nonneg B _ _))) (abs_nonneg _)
  refine matNorm_le B _ _ M (matNorm_nonneg B _ _) ?_ ?_
  · exact fun y => (Finset.sum_le_sum fun y' _ => hterm y y').trans (row_sum_le B δ M y)
  · exact fun y' => (Finset.sum_le_sum fun y _ => hterm y y').trans (col_sum_le B δ M y')
theorem matNorm_le_of_abs_le (δ : ℝ) (M M' : B.LayerMat)
    (h : ∀ y y' : ↥B.allSites, |M y y'| ≤ M' y y') :
    B.expWeightedMatrixNorm δ M ≤ B.expWeightedMatrixNorm δ M' := by
  have hterm : ∀ y y' : ↥B.allSites, |M y y'| * Real.exp (δ * B.weightedDistance y y') ≤
      |M' y y'| * Real.exp (δ * B.weightedDistance y y') := fun y y' =>
    mul_le_mul_of_nonneg_right ((h y y').trans (le_abs_self _)) (Real.exp_pos _).le
  refine matNorm_le B _ _ M (matNorm_nonneg B _ _) ?_ ?_
  · exact fun y => (Finset.sum_le_sum fun y' _ => hterm y y').trans (row_sum_le B δ M' y)
  · exact fun y' => (Finset.sum_le_sum fun y _ => hterm y y').trans (col_sum_le B δ M' y')
theorem bilinear_le_matNorm (M : B.LayerMat) (c c' : ↥B.allSites → ℝ) :
    |∑ y : ↥B.allSites, ∑ y' : ↥B.allSites, c y * M y y' * c' y'| ≤
      B.expWeightedMatrixNorm 0 M * Real.sqrt (∑ y : ↥B.allSites, c y ^ 2) *
        Real.sqrt (∑ y : ↥B.allSites, c' y ^ 2) := by
  set N := B.expWeightedMatrixNorm 0 M with hN
  have hN0 : 0 ≤ N := matNorm_nonneg B 0 M
  have hrow : ∀ y : ↥B.allSites, ∑ y' : ↥B.allSites, |M y y'| ≤ N := by
    intro y
    simpa using row_sum_le B 0 M y
  have hcol : ∀ y' : ↥B.allSites, ∑ y : ↥B.allSites, |M y y'| ≤ N := by
    intro y'
    simpa using col_sum_le B 0 M y'
  set F : ↥B.allSites × ↥B.allSites → ℝ := fun p => |M p.1 p.2| * c p.1 ^ 2 with hF
  set G : ↥B.allSites × ↥B.allSites → ℝ := fun p => |M p.1 p.2| * c' p.2 ^ 2 with hG
  have hF0 : ∀ p, 0 ≤ F p := fun p => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hG0 : ∀ p, 0 ≤ G p := fun p => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hFs : ∑ p, F p ≤ N * ∑ y : ↥B.allSites, c y ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    simp only [hF]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow y) (sq_nonneg _)
  have hGs : ∑ p, G p ≤ N * ∑ y : ↥B.allSites, c' y ^ 2 := by
    rw [Fintype.sum_prod_type_right, Finset.mul_sum]
    refine Finset.sum_le_sum fun y' _ => ?_
    simp only [hG]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hcol y') (sq_nonneg _)
  have hterm : ∀ p : ↥B.allSites × ↥B.allSites,
      |c p.1 * M p.1 p.2 * c' p.2| = Real.sqrt (F p) * Real.sqrt (G p) := by
    intro p
    simp only [hF, hG]
    rw [Real.sqrt_mul (abs_nonneg _), Real.sqrt_mul (abs_nonneg _), Real.sqrt_sq_eq_abs,
      Real.sqrt_sq_eq_abs, abs_mul, abs_mul]
    have := Real.mul_self_sqrt (abs_nonneg (M p.1 p.2))
    calc |c p.1| * |M p.1 p.2| * |c' p.2|
        = |c p.1| * (Real.sqrt |M p.1 p.2| * Real.sqrt |M p.1 p.2|) * |c' p.2| := by rw [this]
      _ = _ := by ring
  calc |∑ y : ↥B.allSites, ∑ y' : ↥B.allSites, c y * M y y' * c' y'|
      = |∑ p : ↥B.allSites × ↥B.allSites, c p.1 * M p.1 p.2 * c' p.2| := by
        rw [Fintype.sum_prod_type]
    _ ≤ ∑ p : ↥B.allSites × ↥B.allSites, |c p.1 * M p.1 p.2 * c' p.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p, Real.sqrt (F p) * Real.sqrt (G p) := Finset.sum_congr rfl fun p _ => hterm p
    _ ≤ Real.sqrt (∑ p, F p) * Real.sqrt (∑ p, G p) :=
        Real.sum_sqrt_mul_sqrt_le _ hF0 hG0
    _ ≤ Real.sqrt (N * ∑ y : ↥B.allSites, c y ^ 2) * Real.sqrt (N * ∑ y : ↥B.allSites, c' y ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hFs) (Real.sqrt_le_sqrt hGs) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = N * Real.sqrt (∑ y : ↥B.allSites, c y ^ 2) * Real.sqrt (∑ y : ↥B.allSites, c' y ^ 2) := by
        rw [Real.sqrt_mul hN0, Real.sqrt_mul hN0]
        have := Real.mul_self_sqrt hN0
        calc Real.sqrt N * Real.sqrt (∑ y : ↥B.allSites, c y ^ 2) *
              (Real.sqrt N * Real.sqrt (∑ y : ↥B.allSites, c' y ^ 2))
            = (Real.sqrt N * Real.sqrt N) * Real.sqrt (∑ y : ↥B.allSites, c y ^ 2) *
                Real.sqrt (∑ y : ↥B.allSites, c' y ^ 2) := by ring
          _ = _ := by rw [this]
omit [Fintype ↥B.allSites] in
theorem layerSpaceNorm_nonneg (w : B.LayerFn) : 0 ≤ B.layerSpaceNorm w := Real.sqrt_nonneg _
theorem sqrt_sum_coords_sq (w : B.LayerFn) :
    Real.sqrt (∑ y : ↥B.allSites, (B.siteScale y ^ 2 * w y) ^ 2) = B.layerSpaceNorm w := by
  rw [sum_coords_sq, Real.sqrt_sq (layerSpaceNorm_nonneg B w)]
theorem layerSpaceNorm_apply_le (K : B.LayerOp) (w : B.LayerFn) :
    B.layerSpaceNorm (K w) ≤ B.expWeightedOpNorm 0 K * B.layerSpaceNorm w := by
  have hb := bilinear_le_matNorm B (B.matrixOf K) (fun y => B.siteScale y ^ 2 * K w y)
    (fun y => B.siteScale y ^ 2 * w y)
  rw [← layerInner_apply_eq_matrix, sqrt_sum_coords_sq, sqrt_sum_coords_sq] at hb
  have hv : B.layerInner (K w) (K w) = B.layerSpaceNorm (K w) ^ 2 := by
    rw [← sum_coords_sq, layerInner_eq_coords]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hv, abs_of_nonneg (sq_nonneg _)] at hb
  have hN : B.expWeightedOpNorm 0 K = B.expWeightedMatrixNorm 0 (B.matrixOf K) := rfl
  rw [hN]
  rcases (layerSpaceNorm_nonneg B (K w)).eq_or_lt with h0 | h0
  · rw [← h0]
    exact mul_nonneg (matNorm_nonneg B _ _) (layerSpaceNorm_nonneg B w)
  · have : B.layerSpaceNorm (K w) * B.layerSpaceNorm (K w) ≤
        (B.expWeightedMatrixNorm 0 (B.matrixOf K) * B.layerSpaceNorm w) *
          B.layerSpaceNorm (K w) := by
      nlinarith only [hb]
    exact le_of_mul_le_mul_right this h0
theorem matrixNormRules_holds (hM : B.MatNormBounds) : B.MatrixNormRules := by
  refine ⟨?_, layerSpaceNorm_apply_le B⟩
  intro M M' δ δ' h0 hδ
  have hb := hM M M' δ (h0.trans hδ)
  refine ⟨hb.1, matNorm_mono B M hδ, hb.2.1, matNorm_le_of_abs_le B δ M M', ?_⟩
  intro c c'
  simp only [finsum_eq_sum_of_fintype]
  exact bilinear_le_matNorm B M c c'
end Matrices
section Pairs
variable {D : TorusData} (B : SeparatedChain D)
def invScaleOn (W : Set D.Space) : Module.End ℝ ↥(B.layerSpaceOn W) :=
  (B.mulOp fun y => (B.siteScale y)⁻¹).restrict fun w hw y hy => by
    change (B.siteScale y)⁻¹ * w y = 0
    rw [hw y hy, mul_zero]
theorem invScaleOn_coe (W : Set D.Space) (w : ↥(B.layerSpaceOn W)) :
    ((invScaleOn B W w : ↥(B.layerSpaceOn W)) : B.LayerFn) =
      B.mulOp (fun y => (B.siteScale y)⁻¹) w := rfl
theorem inverse_scaleOnLayerOn (W : Set D.Space) :
    Ring.inverse (B.scaleOnLayerOn W) = invScaleOn B W := by
  have h1 : B.scaleOnLayerOn W * invScaleOn B W = 1 := by
    refine LinearMap.ext fun w => Subtype.ext (funext fun y => ?_)
    have := (siteScale_pos B (y : D.Space)).ne'
    change B.siteScale y * ((B.siteScale y)⁻¹ * (w : B.LayerFn) y) = _
    change _ = (w : B.LayerFn) y
    field_simp
  have h2 : invScaleOn B W * B.scaleOnLayerOn W = 1 := by
    refine LinearMap.ext fun w => Subtype.ext (funext fun y => ?_)
    have := (siteScale_pos B (y : D.Space)).ne'
    change (B.siteScale y)⁻¹ * (B.siteScale y * (w : B.LayerFn) y) = _
    change _ = (w : B.LayerFn) y
    field_simp
  exact Ring.inverse_unit (⟨_, _, h1, h2⟩ : (Module.End ℝ ↥(B.layerSpaceOn W))ˣ)
theorem admissibleScaledGreenSq_apply (W : Set D.Space) (𝔟 : Set D.Bond)
    (w : ↥(B.layerSpaceOn W)) :
    B.admissibleScaledGreenSq W 𝔟 w =
      invScaleOn B W (invScaleOn B W (B.admissibleAvgGreenSq W 𝔟
        (invScaleOn B W (invScaleOn B W w)))) := by
  rw [SeparatedChain.admissibleScaledGreenSq, inverse_scaleOnLayerOn]
  rfl
theorem scaledGreenSq_apply (w : B.LayerFn) :
    B.scaledGreenSq w =
      B.mulOp (fun y => (B.siteScale y)⁻¹)
        (B.mulOp (fun y => (B.siteScale y)⁻¹) (B.avgGreenSq
          (B.mulOp (fun y => (B.siteScale y)⁻¹)
            (B.mulOp (fun y => (B.siteScale y)⁻¹) w)))) := by
  rw [SeparatedChain.scaledGreenSq, inverse_scaleOnLayer]
  rfl
theorem layerInner_mulOp (m : ↥B.allSites → ℝ) (w w' : B.LayerFn) :
    B.layerInner (B.mulOp m w) w' = B.layerInner w (B.mulOp m w') := by
  simp only [SeparatedChain.layerInner, mulOp_apply]
  exact finsum_congr fun y => by ring
theorem layerInner_invScaleOn (W : Set D.Space) (w w' : ↥(B.layerSpaceOn W)) :
    B.layerInner (invScaleOn B W w : ↥(B.layerSpaceOn W)) w' =
      B.layerInner w (invScaleOn B W w' : ↥(B.layerSpaceOn W)) :=
  layerInner_mulOp B _ _ _
theorem admissibleScaledGreenSq_symm (W : Set D.Space) (𝔟 : Set D.Bond)
    (hT : ∀ w w' : ↥(B.layerSpaceOn W),
      B.layerInner (B.admissibleAvgGreenSq W 𝔟 w) w' =
        B.layerInner w (B.admissibleAvgGreenSq W 𝔟 w'))
    (w w' : ↥(B.layerSpaceOn W)) :
    B.layerInner (B.admissibleScaledGreenSq W 𝔟 w) w' =
      B.layerInner w (B.admissibleScaledGreenSq W 𝔟 w') := by
  rw [admissibleScaledGreenSq_apply, admissibleScaledGreenSq_apply, layerInner_invScaleOn,
    layerInner_invScaleOn, hT, ← layerInner_invScaleOn, ← layerInner_invScaleOn]
variable (hP : CubesLayersBlocksBallsHold)
include hP
theorem exists_mem_block_eq {y : D.Space} (hy : y ∈ B.allSites) :
    ∃ x ∈ B.block y, (x : D.Space) = y :=
  (block_description B hP hy).2.2.2.2.1
theorem allSites_subset_stage : B.allSites ⊆ B.stage 0 := by
  intro y hy
  rw [← (partition_facts B hP).1.2.1]
  obtain ⟨x, hx, rfl⟩ := exists_mem_block_eq B hP hy
  exact mem_biUnion hy hx
theorem block_subset_of_isBlockUnion {W : Set D.Space} (hW : B.IsBlockUnion W) {y : D.Space}
    (hy : y ∈ B.sitesIn W) : B.block y ⊆ D.bareSites W := by apply _root_.YangMills.Construction.Weighted.BlockUnionIndicator.block_subset_bareSites_of_isBlockUnion <;> assumption
theorem blockIndicator_mem_bareSpaceOn {W : Set D.Space} (hW : B.IsBlockUnion W) {y : D.Space}
    (hy : y ∈ B.sitesIn W) : B.blockIndicator y ∈ B.bareSpaceOn W := by apply _root_.YangMills.Construction.Weighted.BlockUnionIndicator.blockIndicator_mem_bareSpaceOn <;> assumption
theorem blockIndicatorIn_eq {W : Set D.Space} (hW : B.IsBlockUnion W) {y : D.Space}
    (hy : y ∈ B.sitesIn W) :
    B.blockIndicatorIn W y = ⟨B.blockIndicator y, blockIndicator_mem_bareSpaceOn B hP hW hy⟩ := by
  apply Subtype.ext
  funext x
  change (D.bareSites (B.stage 0) ∩ D.bareSites W).indicator (B.blockIndicator y) x =
    B.blockIndicator y x
  by_cases hx : x ∈ B.block y
  · have hm : x ∈ D.bareSites (B.stage 0) ∩ D.bareSites W :=
      ⟨block_subset_base B hP hy.1 hx, block_subset_of_isBlockUnion B hP hW hy hx⟩
    exact indicator_of_mem hm _
  · have h0 : B.blockIndicator y x = 0 := indicator_of_notMem hx _
    rw [h0]
    by_cases hx' : x ∈ D.bareSites (B.stage 0) ∩ D.bareSites W
    · rw [indicator_of_mem hx', h0]
    · exact indicator_of_notMem hx' _
theorem admissiblePairSymm_holds (hne : (B.stage 0).Nonempty)
    (hA : AdmissiblePairOperators) : B.AdmissiblePairSymm := by
  intro W 𝔟 hadm
  obtain ⟨-, hG, -, -, hT, hM⟩ : B.PairOperatorFacts W 𝔟 := (hA ⟨D, B, hne⟩).1 W 𝔟 hadm
  refine ⟨hG, hT, admissibleScaledGreenSq_symm B W 𝔟 hT, ?_⟩
  intro y y' hy hy'
  refine ⟨blockIndicator_mem_bareSpaceOn B hP hadm.1 hy,
    blockIndicator_mem_bareSpaceOn B hP hadm.1 hy', ?_⟩
  have h := hM y y' hy hy'
  rw [blockIndicatorIn_eq B hP hadm.1 hy, blockIndicatorIn_eq B hP hadm.1 hy'] at h
  exact h
theorem basePairFacts_holds (hne : (B.stage 0).Nonempty)
    (hA : AdmissiblePairOperators) : B.BasePairFacts := by
  obtain ⟨h1, h2, h3, -, -, -, h7, h8, h9⟩ : B.InitialPairFacts := (hA ⟨D, B, hne⟩).2
  have hb : B.baseStar = B.initialBonds := rfl
  unfold SeparatedChain.BasePairFacts
  rw [hb]
  refine ⟨h1, inter_eq_left.2 (allSites_subset_stage B hP), h2, h8, ?_, ?_, h9, ?_⟩
  · exact fun f => congrArg Subtype.val (h3 f)
  · exact fun f => congrArg Subtype.val (h7 f)
  · intro w
    rw [admissibleScaledGreenSq_apply, scaledGreenSq_apply]
    simp only [invScaleOn_coe]
    rw [h9]
    simp only [invScaleOn_coe]
end Pairs
theorem distanceAvgPairMatrixNormFacts_holds (hP : CubesLayersBlocksBallsHold)
    (hO : AvgAndMatrixFacts)
    (hA : AdmissiblePairOperators) : DistanceAvgPairMatrixNormFacts := by
  intro D B hne
  have := allSites_finite B hP
  let _ : Fintype ↥B.allSites := Fintype.ofFinite _
  have hG := hO ⟨D, B, hne⟩
  exact ⟨weightedDist_symm_triangle B,
    avgAndAdjoint_holds B hP hne hO,
    weightedAvgForm_holds B hne hO,
    avgWeightClosedForm_holds D.L (L_ge_three D),
    dirichletLapOnBase_holds B,
    basePairFacts_holds B hP hne hA,
    admissiblePairSymm_holds B hP hne hA,
    layerMatrixCalculus_holds B hG.2.2.1,
    matrixNormRules_holds B hG.2.2.2.2.1⟩
end YangMills.Construction.Weighted.DistanceAvgPairMatrixNormProof
