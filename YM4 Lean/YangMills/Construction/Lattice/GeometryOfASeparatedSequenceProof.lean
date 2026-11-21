import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.Lattice.MinimumOverTheWeightsOfConsecutiveLevelsProof
import YangMills.Construction.Lattice.TransposesOfTheCovariantDerivativesOnALatticeProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SequenceGeometryProof
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.TorusMetric YangMills.Construction.SeparatedSequences.BaseParameters
section SupNorms
variable {S : ℝ}
theorem torusSupNorm_eq_sup (x : Torus4 S) :
    torusSupNorm x = Finset.univ.sup' Finset.univ_nonempty fun μ => ‖x μ‖ := by
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  have hcov : torusProj S b = x := funext hb
  apply le_antisymm
  · refine csInf_le ⟨0, ?_⟩ ⟨b, hcov, ?_⟩
    · rintro _ ⟨v, -, rfl⟩
      exact le_trans (abs_nonneg _) (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
    · simp [TorusMetric.supNormVec, hb']
  · refine le_csInf ⟨_, b, hcov, rfl⟩ ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' : torusProj S v = x := hv
    refine Finset.sup'_le _ _ fun μ _ => ?_
    rw [← hv']
    exact (addCircle_norm_coe_le_abs _).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ))
theorem norm_apply_le_torusSupNorm (x : Torus4 S) (μ : Fin 4) : ‖x μ‖ ≤ torusSupNorm x := by
  rw [torusSupNorm_eq_sup]
  exact Finset.le_sup' (fun μ => ‖x μ‖) (Finset.mem_univ μ)
theorem torusSupNorm_le_of_forall {x : Torus4 S} {r : ℝ} (h : ∀ μ, ‖x μ‖ ≤ r) :
    torusSupNorm x ≤ r := by
  rw [torusSupNorm_eq_sup]
  exact Finset.sup'_le _ _ fun μ _ => h μ
theorem torusSupNorm_add_le (x y : Torus4 S) :
    torusSupNorm (x + y) ≤ torusSupNorm x + torusSupNorm y :=
  torusSupNorm_le_of_forall fun μ => (norm_add_le _ _).trans
    (add_le_add (norm_apply_le_torusSupNorm x μ) (norm_apply_le_torusSupNorm y μ))
theorem torusSupNorm_neg (x : Torus4 S) : torusSupNorm (-x) = torusSupNorm x := by
  simp [torusSupNorm_eq_sup]
theorem torusSupNorm_zero : torusSupNorm (0 : Torus4 S) = 0 := by
  simp [torusSupNorm_eq_sup]
end SupNorms
section Steps
variable {L m : ℕ}
theorem meshSize_nonneg' (j : ℤ) : 0 ≤ meshSize L j := zpow_nonneg (Nat.cast_nonneg _) _
theorem torusSupNorm_unitStep_le (j : ℤ) (μ : Fin 4) :
    torusSupNorm ((unitStep L m j μ : Site L m j) : FourTorus L m) ≤ meshSize L j := by
  refine torusSupNorm_le_of_forall fun ν => ?_
  by_cases h : ν = μ
  · subst h
    have h1 := addCircle_norm_coe_le_abs (S := torusSide L m) (meshSize L j)
    rw [abs_of_nonneg (meshSize_nonneg' j)] at h1
    simpa [unitStep, pointOnAxis] using h1
  · simp [unitStep, pointOnAxis, Pi.single_eq_of_ne h, meshSize_nonneg' j]
theorem torusSupNorm_bond_le {j : ℤ} (b : Bond L m j) :
    torusSupNorm ((b.target : FourTorus L m) - (b.source : FourTorus L m)) ≤ meshSize L j := by
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · have h' : (b.target : FourTorus L m) - (b.source : FourTorus L m) =
        ((unitStep L m j μ : Site L m j) : FourTorus L m) := by
      rw [← AddSubgroup.coe_sub, h]
    rw [h']
    exact torusSupNorm_unitStep_le j μ
  · have h' : (b.target : FourTorus L m) - (b.source : FourTorus L m) =
        -((unitStep L m j μ : Site L m j) : FourTorus L m) := by
      rw [← AddSubgroup.coe_sub, h]
      rfl
    rw [h', torusSupNorm_neg]
    exact torusSupNorm_unitStep_le j μ
end Steps
section Units
variable (E : SeparatedSequences.BaseParameters)
theorem cast_L_pos : 0 < (E.L : ℝ) := by apply _root_.YangMills.Construction.SeparatedSequences.LevelWeightMinimum.side_pos <;> assumption
theorem one_le_cast_L : 1 ≤ (E.L : ℝ) := by
  have := E.three_le_L
  exact_mod_cast (by omega : 1 ≤ E.L)
theorem three_le_cast_L : 3 ≤ (E.L : ℝ) := by
  exact_mod_cast E.three_le_L
theorem levelMeshRatio_pos (n : ℕ) : 0 < E.levelMeshRatio n := zpow_pos (cast_L_pos E) _
theorem lengthInUnits_mono {r s : ℝ} (h : r ≤ s) : E.lengthInUnits r ≤ E.lengthInUnits s := by
  simp only [SeparatedSequences.BaseParameters.lengthInUnits,
    SeparatedSequences.ScaleData.toUnits, toLevelUnits]
  exact mul_le_mul_of_nonneg_left h (zpow_nonneg (Nat.cast_nonneg _) _)
end Units
variable (D : SeparatedSequences.SequenceDatum) (H : SeparatedSequences.LatticeCubeStatement)
theorem memberAt_of_le {n : ℕ} (h : n ≤ D.t) : D.memberAt D.region n = D.region n := by apply _root_.YangMills.Construction.AveragesDifference.memberAt_of_le <;> assumption
theorem memberAt_of_lt {n : ℕ} (h : D.t < n) : D.memberAt D.region n = ∅ := by
  simp only [memberAt, SeparatedSequences.truncatedMember]
  exact if_neg (not_le.mpr h)
include H in
theorem far_across_gap {k : ℕ} (hk : k < D.t) {a b : D.Torus} (ha : a ∉ D.region k)
    (hb : b ∈ D.region (k + 1)) :
    (D.L : ℝ) * D.levelMeshRatio k < D.lengthInUnits (torusSupNorm (a - b)) := by
  obtain ⟨hsub, hgap⟩ := D.separated.2 k hk
  rcases D.separated.1 k hk.le with h0 | ⟨hidx, hreg⟩
  · exact absurd (hsub hb) (by simp [h0])
  have hkK : k ≤ D.K := hk.le.trans D.t_le_K
  obtain ⟨-, -, -, hBlk, -⟩ := H D 0 0 le_rfl (Nat.zero_le _)
  obtain ⟨h1, h2, -⟩ := hBlk k hkK
  have hi : k + D.blockExp ≤ D.m + D.K := h1.mp hidx
  have hU : D.IsOrderCubeUnion (k + D.blockExp) (D.region k) := by
    obtain ⟨C, hC, hX⟩ := hreg
    exact ⟨C, (h2 hi) ▸ hC, hX⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hReg, -⟩ := H D _ _ le_rfl hi
  obtain ⟨-, -, -, -, -, hcov, -⟩ := hReg _ hU
  have hidx' : D.scales.blockPartitionIndex k = levelDepth D.K (k + D.blockExp) := by
    simp only [SeparatedSequences.ScaleData.blockPartitionIndex, scaledCubeIndex, levelDepth]
    push_cast
    ring
  have ha' : a ∈ complementRegion (levelDepth D.K (k + D.blockExp)) (D.region k) := by
    have : a ∈ D.region k ∪ complementRegion (levelDepth D.K (k + D.blockExp)) (D.region k) :=
      hcov ▸ mem_univ a
    exact this.resolve_left ha
  rw [hidx'] at hgap
  have hle : supDistInLevelUnits D.K D.scales.unitLevel
      (complementRegion (levelDepth D.K (k + D.blockExp)) (D.region k)) (D.region (k + 1)) ≤
      ENNReal.ofReal ((D.L : ℝ) ^ levelDepth D.K D.scales.unitLevel) *
        ENNReal.ofReal (torusSupNorm (a - b)) := by
    unfold supDistInLevelUnits
    gcongr
    exact iInf₂_le_of_le a ha' (iInf₂_le b hb)
  have hlt := hgap.trans_le hle
  rw [← ENNReal.ofReal_mul (zpow_nonneg (Nat.cast_nonneg _) _)] at hlt
  have hA : 0 ≤ (D.gapSize : ℝ) * (D.L : ℝ) ^ D.scales.blockExp * D.scales.levelMesh D.L k := by
    have := levelMeshRatio_pos D.toBaseParameters k
    have h3 : 0 ≤ D.scales.levelMesh D.L k := this.le
    positivity
  have h4 := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hA).mp hlt
  have hR : (D.L : ℝ) ≤ (D.gapSize : ℝ) := by
    exact_mod_cast D.L_le_pow_gapExp
  have hM : (1 : ℝ) ≤ (D.L : ℝ) ^ D.scales.blockExp := one_le_pow₀ (one_le_cast_L D.toBaseParameters)
  have hx : 0 < D.levelMeshRatio k := levelMeshRatio_pos D.toBaseParameters k
  have h5 : (D.L : ℝ) * D.levelMeshRatio k ≤
      (D.gapSize : ℝ) * (D.L : ℝ) ^ D.scales.blockExp * D.levelMeshRatio k := by
    refine mul_le_mul_of_nonneg_right ?_ hx.le
    calc (D.L : ℝ) = (D.L : ℝ) * 1 := (mul_one _).symm
      _ ≤ (D.gapSize : ℝ) * (D.L : ℝ) ^ D.scales.blockExp :=
        mul_le_mul hR hM zero_le_one (by have := cast_L_pos D.toBaseParameters; linarith)
  exact h5.trans_lt h4
include H in
theorem site_mem_orderCentreSet {k : ℕ} (hk : k ≤ D.t) (x : D.LatticeSite k) :
    (x : D.Torus) ∈ D.orderCentreSet k := by
  obtain ⟨-, -, hLow, -⟩ := H D 0 0 le_rfl (Nat.zero_le _)
  rw [(hLow k hk).2.1]
  exact x.2
include H in
theorem closedOrderCube_eq_cube {n : ℕ} (hn : n ≤ D.t) (y : D.LatticeSite n) :
    D.closedOrderCube n ⟨y, site_mem_orderCentreSet D H hn y⟩ =
      cube (D := D.toBaseParameters) y := by
  obtain ⟨-, -, hLow, -⟩ := H D 0 0 le_rfl (Nat.zero_le _)
  exact (hLow n hn).2.2 _ y rfl
include H in
theorem mem_layerSites_iff {n : ℕ} (hn : n ≤ D.t) (y : D.LatticeSite n) :
    y ∈ D.layerSites D.region n ↔
      (y : D.Torus) ∈ D.memberAt D.region n ∧ (y : D.Torus) ∉ D.memberAt D.region (n + 1) := by apply _root_.YangMills.Construction.AveragesDifference.mem_layerSites_iff <;> assumption
theorem torusSupNorm_le_of_path {L m : ℕ} {j : ℤ} (Γ : List (Bond L m j)) (x₀ x : Site L m j)
    (h : IsBondPathFromTo Γ x₀ x) :
    torusSupNorm ((x : FourTorus L m) - (x₀ : FourTorus L m)) ≤ Γ.length * meshSize L j := by
  induction Γ generalizing x₀ with
  | nil =>
    obtain rfl := h.2.1 rfl
    simp [torusSupNorm_zero]
  | cons b Γ ih =>
    have ht : b.source = x₀ := h.2.2.1 b (by simp)
    cases Γ with
    | nil =>
      have hh : b.target = x := h.2.2.2 b (by simp)
      subst ht hh
      simpa using torusSupNorm_bond_le b
    | cons c Γ' =>
      have hchain : b.target = c.source ∧ IsBondPath (c :: Γ') := by
        simpa [IsBondPath, List.isChain_cons_cons] using h.1
      have hnext : IsBondPathFromTo (c :: Γ') b.target x := by
        refine ⟨hchain.2, by simp, fun e he => ?_, fun e he => ?_⟩
        · simp at he
          rw [← he, hchain.1]
        · exact h.2.2.2 e (by simpa using he)
      have h1 := ih b.target hnext
      have h2 := torusSupNorm_bond_le b
      have h3 : (x : FourTorus L m) - (x₀ : FourTorus L m) =
          ((x : FourTorus L m) - (b.target : FourTorus L m)) +
            ((b.target : FourTorus L m) - (b.source : FourTorus L m)) := by
        rw [ht]
        abel
      rw [h3]
      refine (torusSupNorm_add_le _ _).trans ?_
      have h4 : (((c :: Γ').length + 1 : ℕ) : ℝ) = ((c :: Γ').length : ℝ) + 1 := by
        push_cast; ring
      simp only [List.length_cons] at h1 h4 ⊢
      rw [h4]
      linarith
theorem lengthInUnits_mul_left (E : SeparatedSequences.BaseParameters) (c r : ℝ) :
    E.lengthInUnits (c * r) = c * E.lengthInUnits r := by
  simp only [SeparatedSequences.BaseParameters.lengthInUnits,
    SeparatedSequences.ScaleData.toUnits, toLevelUnits]
  ring
include H in
theorem mem_region_zero_of_near {x₀ w : D.Torus} (h0 : x₀ ∈ D.memberAt D.region 1)
    (hd : torusSupNorm (w - x₀) ≤ 3 * meshSize D.L (levelDepth D.K 0)) : w ∈ D.region 0 := by
  have ht : 0 < D.t := by
    by_contra hle
    rw [memberAt_of_lt D (by omega : D.t < 1)] at h0
    exact h0
  rw [memberAt_of_le D ht] at h0
  by_contra hw
  have h1 := far_across_gap D H ht hw h0
  have h2 := lengthInUnits_mono D.toBaseParameters hd
  rw [lengthInUnits_mul_left, lengthInUnits_meshSize] at h2
  have h3 := three_le_cast_L D.toBaseParameters
  have h4 := levelMeshRatio_pos D.toBaseParameters 0
  nlinarith
theorem exists_near_of_mem_collar {r : ℕ} {x : BareSite D.L D.m D.K}
    (hx : x ∈ D.secondMemberCollar D.region r) :
    ∃ x₀ : BareSite D.L D.m D.K, (x₀ : D.Torus) ∈ D.memberAt D.region 1 ∧
      torusSupNorm ((x : D.Torus) - (x₀ : D.Torus)) ≤ r * meshSize D.L (levelDepth D.K 0) := by
  obtain ⟨x₀, h0, Γ, hl, hΓ⟩ := hx
  refine ⟨x₀, h0, (torusSupNorm_le_of_path Γ x₀ x hΓ).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hl) (meshSize_nonneg' _)
include H in
theorem ends_mem_of_collar {x : BareSite D.L D.m D.K} (hx : x ∈ D.secondMemberCollar D.region 2)
    (b : BareOrientedBond D.L D.m D.K) (hb : b.source = x ∨ b.target = x) :
    b.source ∈ sitesOfRegion D.K (D.region 0) ∧ b.target ∈ sitesOfRegion D.K (D.region 0) := by
  obtain ⟨x₀, h0, hd⟩ := exists_near_of_mem_collar D hx
  have hs := meshSize_nonneg' (L := D.L) (levelDepth D.K 0)
  have hbond := torusSupNorm_bond_le b
  have hbond' : torusSupNorm ((b.source : D.Torus) - (b.target : D.Torus)) ≤
      meshSize D.L (levelDepth D.K 0) := by
    rw [← torusSupNorm_neg, neg_sub]
    exact hbond
  push_cast at hd
  rcases hb with rfl | rfl
  · refine ⟨mem_region_zero_of_near D H h0 (by linarith), mem_region_zero_of_near D H h0 ?_⟩
    have h3 : (b.target : D.Torus) - (x₀ : D.Torus) =
        ((b.target : D.Torus) - (b.source : D.Torus)) + ((b.source : D.Torus) - (x₀ : D.Torus)) := by
      abel
    rw [h3]
    exact (torusSupNorm_add_le _ _).trans (by linarith)
  · refine ⟨mem_region_zero_of_near D H h0 ?_, mem_region_zero_of_near D H h0 (by linarith)⟩
    have h3 : (b.source : D.Torus) - (x₀ : D.Torus) =
        ((b.source : D.Torus) - (b.target : D.Torus)) + ((b.target : D.Torus) - (x₀ : D.Torus)) := by
      abel
    rw [h3]
    exact (torusSupNorm_add_le _ _).trans (by linarith)
include H in
theorem secondMemberCollar : D.SecondMemberCollarProperties D.region := by
  have h2 : D.secondMemberCollar D.region 2 ∩ frontierSites D.K (D.region 0) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro x ⟨hx, -, b, hb, hxb⟩
    have h := ends_mem_of_collar D H hx b.1 (by rcases hxb with h | h <;> simp [h])
    exact hb.2 h
  refine ⟨?_, h2, ?_, ?_⟩
  · intro x hx
    obtain ⟨x₀, h0, hd⟩ := exists_near_of_mem_collar D hx
    push_cast at hd
    exact mem_region_zero_of_near D H h0 hd
  · intro x hx
    have h0 := Nat.zero_le D.t
    refine (mem_layerSites_iff D H h0 x).2 ⟨?_, fun h1 => ?_⟩
    · rw [memberAt_of_le D h0]
      exact hx.1
    · have hc : x ∈ D.secondMemberCollar D.region 2 :=
        ⟨x, h1, [], by simp, by simp [IsBondPathFromTo, IsBondPath]⟩
      have : x ∈ D.secondMemberCollar D.region 2 ∩ frontierSites D.K (D.region 0) := ⟨hc, hx⟩
      rw [h2] at this
      exact this
  · rintro b (h | h)
    · exact ends_mem_of_collar D H h b.1 (Or.inl rfl)
    · exact ends_mem_of_collar D H h b.1 (Or.inr rfl)
section Coordinates
variable {L m : ℕ}
theorem zsmul_addCircle_coe (S : ℝ) (k : ℤ) (c : ℝ) :
    k • (c : AddCircle S) = (((k : ℝ) * c : ℝ) : AddCircle S) := by
  rw [← zsmul_eq_mul]
  rfl
theorem addCircle_coe_ne_zero_of_lt {S c : ℝ} (hS : 0 < S) (h0 : 0 < c) (h1 : c < S) :
    (c : AddCircle S) ≠ 0 := by apply _root_.YangMills.SharedProofs.p5311 <;> assumption
theorem sum_zsmul_unitStep_apply (j : ℤ) (a : Fin 4 → ℤ) (μ : Fin 4) :
    (∑ ν, a ν • ((unitStep L m j ν : Site L m j) : FourTorus L m)) μ =
      (((a μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := by
  rw [Finset.sum_apply, Finset.sum_eq_single μ]
  · show a μ • pointOnAxis L m μ (meshSize L j) μ = _
    rw [← zsmul_addCircle_coe]
    simp [pointOnAxis]
  · intro ν _ hν
    show a ν • pointOnAxis L m ν (meshSize L j) μ = 0
    simp [pointOnAxis, Pi.single_eq_of_ne hν.symm]
  · simp
theorem isLevelLift_unique {K j : ℕ} (hL : 0 < L) {x x' : FourTorus L m} {w : Fin 4 → ℝ}
    (h : IsLevelLift L m K j x w) (h' : IsLevelLift L m K j x' w) : x = x' := by
  obtain ⟨v, hv, hw⟩ := h
  obtain ⟨v', hv', hw'⟩ := h'
  funext μ
  rw [← hv, ← hv']
  have h1 : toLevelUnits L K j (v μ) = toLevelUnits L K j (v' μ) := (hw μ).symm.trans (hw' μ)
  simp only [toLevelUnits] at h1
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [mul_left_cancel₀ (zpow_ne_zero _ hL') h1]
theorem exists_isLevelLift (K j : ℕ) (x : FourTorus L m) : ∃ w, IsLevelLift L m K j x w := by
  choose v hv using fun μ => QuotientAddGroup.mk_surjective (x μ)
  exact ⟨_, v, hv, fun _ => rfl⟩
theorem mem_forwardFlow {j : ℤ} (x : Site L m j) (μ : Fin 4) (k : ℕ) (b : Bond L m j) :
    b ∈ forwardAxisPath x μ k ↔ ∃ i < k, b = Bond.forwardFrom (x + i • unitStep L m j μ) μ := by
  induction k generalizing x with
  | zero => simp [forwardAxisPath]
  | succ k ih =>
    simp only [forwardAxisPath, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · refine ⟨i + 1, by omega, ?_⟩
        rw [succ_nsmul', add_assoc]
    · rintro ⟨i, hi, rfl⟩
      cases i with
      | zero => exact Or.inl (by simp)
      | succ i =>
        refine Or.inr ⟨i, by omega, ?_⟩
        rw [succ_nsmul', add_assoc]
end Coordinates
section Parameters
variable {E : SeparatedSequences.BaseParameters}
theorem meshSize_pos_lt_torusSide (E : SeparatedSequences.BaseParameters) {n : ℕ} (hn : n ≤ E.K) :
    0 < meshSize E.L (levelDepth E.K n) ∧ meshSize E.L (levelDepth E.K n) < torusSide E.L E.m := by
  have hL := cast_L_pos E
  have h1 := one_le_cast_L E
  refine ⟨zpow_pos hL _, ?_⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ, levelDepth E.K n = (e : ℤ) :=
    ⟨E.K - n, by simp only [levelDepth]; omega⟩
  have h2 : meshSize E.L (levelDepth E.K n) ≤ 1 := by
    simp only [meshSize]
    rw [he, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
  have h3 : (1 : ℝ) ≤ (E.L : ℝ) ^ E.m := one_le_pow₀ h1
  simp only [torusSide]
  linarith
theorem torusSide_pos' (E : SeparatedSequences.BaseParameters) : 0 < torusSide E.L E.m := by
  have := cast_L_pos E
  simp only [torusSide]
  positivity
theorem unitStep_ne_zero (E : SeparatedSequences.BaseParameters) {n : ℕ} (hn : n ≤ E.K)
    (μ : Fin 4) : unitStep E.L E.m (levelDepth E.K n) μ ≠ 0 := by
  intro h
  have h1 := congrArg (fun s : Site E.L E.m (levelDepth E.K n) => (s : FourTorus E.L E.m) μ) h
  simp only [unitStep, pointOnAxis, Pi.single_eq_same, ZeroMemClass.coe_zero, Pi.zero_apply] at h1
  exact addCircle_coe_ne_zero_of_lt (torusSide_pos' E) (meshSize_pos_lt_torusSide E hn).1
    (meshSize_pos_lt_torusSide E hn).2 h1
theorem unitStep_injective (E : SeparatedSequences.BaseParameters) {μ ν : Fin 4}
    (h : unitStep E.L E.m (levelDepth E.K 0) μ = unitStep E.L E.m (levelDepth E.K 0) ν) :
    μ = ν := by
  by_contra hne
  have h1 := congrArg (fun s : Site E.L E.m (levelDepth E.K 0) => (s : FourTorus E.L E.m) μ) h
  simp only [unitStep, pointOnAxis, Pi.single_eq_same, Pi.single_eq_of_ne hne] at h1
  have hK : 0 ≤ E.K := Nat.zero_le _
  exact addCircle_coe_ne_zero_of_lt (torusSide_pos' E) (meshSize_pos_lt_torusSide E hK).1
    (meshSize_pos_lt_torusSide E hK).2 h1
def toFineSite {n : ℕ} (y : E.LatticeSite n) : BareSite E.L E.m E.K :=
  ⟨y, sublattice_mono (by have := E.three_le_L; omega) E.m
    (by simp only [levelDepth]; push_cast; omega) y.2⟩
def boxSite {n : ℕ} (y : E.LatticeSite n) (a : Fin 4 → ℤ) : BareSite E.L E.m E.K :=
  toFineSite y + ∑ ν, a ν • unitStep E.L E.m (levelDepth E.K 0) ν
theorem coe_boxSite {n : ℕ} (y : E.LatticeSite n) (a : Fin 4 → ℤ) :
    ((boxSite y a : BareSite E.L E.m E.K) : E.Torus) =
      (y : E.Torus) +
        ∑ ν, a ν • ((unitStep E.L E.m (levelDepth E.K 0) ν : BareSite E.L E.m E.K) : E.Torus) := by
  simp [boxSite, toFineSite]
theorem shiftedPoint_eq (p : E.Torus) (a : Fin 4 → ℤ) :
    E.shiftedPoint 0 p a =
      p + ∑ ν, a ν • ((unitStep E.L E.m (levelDepth E.K 0) ν : BareSite E.L E.m E.K) : E.Torus) := by
  have hLp : 0 < E.L := by have := E.three_le_L; omega
  change torusClassOf E.L E.m E.K E.t (Classical.epsilon (IsLevelLift E.L E.m E.K E.t p) +
    E.orderMesh 0 • ∑ μ, (a μ : ℝ) • coordVec μ) = _
  have h0 : IsLevelLift E.L E.m E.K E.t p (Classical.epsilon (IsLevelLift E.L E.m E.K E.t p)) :=
    Classical.epsilon_spec (exists_isLevelLift E.K E.t p)
  set w0 := Classical.epsilon (IsLevelLift E.L E.m E.K E.t p) with hw0
  set r : Fin 4 → ℝ := E.orderMesh 0 • ∑ μ, (a μ : ℝ) • coordVec μ with hr
  have hθ : toLevelUnits E.L E.K E.t (meshSize E.L (levelDepth E.K 0)) = E.orderMesh 0 := by
    have h1 := E.lengthInUnits_meshSize 0
    simp only [orderMesh, pow_zero, one_mul]
    exact h1
  have hrμ : ∀ μ, r μ = E.orderMesh 0 * (a μ : ℝ) := by
    intro μ
    simp [hr, coordVec, Finset.sum_apply, Pi.single_apply]
  have hl : IsLevelLift E.L E.m E.K E.t
      (p + ∑ ν, a ν • ((unitStep E.L E.m (levelDepth E.K 0) ν : BareSite E.L E.m E.K) : E.Torus))
      (w0 + r) := by
    obtain ⟨v, hv, hw⟩ := h0
    refine ⟨fun μ => v μ + (a μ : ℝ) * meshSize E.L (levelDepth E.K 0), fun μ => ?_, fun μ => ?_⟩
    · rw [Pi.add_apply, sum_zsmul_unitStep_apply, ← hv μ]
      rfl
    · rw [Pi.add_apply, hw μ, hrμ μ, ← hθ]
      simp only [toLevelUnits]
      ring
  exact isLevelLift_unique hLp
    (Classical.epsilon_spec (⟨_, hl⟩ : ∃ x, IsLevelLift E.L E.m E.K E.t x (w0 + r))) hl
def halfSide (E : SeparatedSequences.BaseParameters) (n : ℕ) : ℕ := E.L ^ n / 2
theorem two_mul_halfSide_add_one (E : SeparatedSequences.BaseParameters) (n : ℕ) :
    2 * halfSide E n + 1 = E.L ^ n := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.two_mul_halfWidth_add_one <;> assumption
def IsInBox (E : SeparatedSequences.BaseParameters) (n : ℕ) (a : Fin 4 → ℤ) : Prop :=
  ∀ ν, -(halfSide E n : ℤ) ≤ a ν ∧ a ν ≤ halfSide E n
theorem mem_boundedOffsets_iff {n : ℕ} (a : Fin 4 → ℤ) :
    a ∈ boundedOffsets (E.L ^ n) ↔ IsInBox E n a := by
  have hh : (((E.L ^ n : ℕ) : ℝ) - 1) / 2 = (halfSide E n : ℝ) := by
    have h1 : (((E.L ^ n : ℕ)) : ℝ) = 2 * (halfSide E n : ℝ) + 1 := by
      exact_mod_cast (two_mul_halfSide_add_one E n).symm
    rw [h1]
    ring
  simp only [boundedOffsets, mem_ofPred_eq, hh, IsInBox, abs_le]
  refine forall_congr' fun ν => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
end Parameters
include H in
theorem fineBlock_eq_image {n : ℕ} (hn : n ≤ D.t) (y : D.LatticeSite n) :
    fineBlock (D := D.toBaseParameters) y =
        D.shiftedPoint 0 (y : D.Torus) '' boundedOffsets (D.L ^ n) ∧
      InjOn (D.shiftedPoint 0 (y : D.Torus)) (boundedOffsets (D.L ^ n)) := by
  have hnK : n ≤ D.m + D.K := (hn.trans D.t_le_K).trans (Nat.le_add_left _ _)
  obtain ⟨-, -, hLow, -, -, -, -, hBl2, -⟩ := H D n 0 (Nat.zero_le _) hnK
  obtain ⟨h1, h2, -⟩ := hBl2.1 ⟨y, site_mem_orderCentreSet D H hn y⟩
  rw [closedOrderCube_eq_cube D H hn y, (hLow 0 (Nat.zero_le _)).2.1] at h1
  simp only [orderScaleRatio, Nat.sub_zero] at h1 h2
  refine ⟨?_, h2⟩
  rw [← h1, inter_comm]
  rfl
include H in
theorem mem_fineBlock_iff {n : ℕ} (hn : n ≤ D.t) (y : D.LatticeSite n) (x : BareSite D.L D.m D.K) :
    (x : D.Torus) ∈ fineBlock (D := D.toBaseParameters) y ↔
      ∃ a, IsInBox D.toBaseParameters n a ∧ x = boxSite y a := by
  rw [(fineBlock_eq_image D H hn y).1]
  constructor
  · rintro ⟨a, ha, hx⟩
    refine ⟨a, (mem_boundedOffsets_iff a).1 ha, Subtype.ext ?_⟩
    rw [coe_boxSite, ← hx, shiftedPoint_eq]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (mem_boundedOffsets_iff a).2 ha, by rw [shiftedPoint_eq, coe_boxSite]⟩
end YangMills.Construction.SequenceGeometryProof
end
