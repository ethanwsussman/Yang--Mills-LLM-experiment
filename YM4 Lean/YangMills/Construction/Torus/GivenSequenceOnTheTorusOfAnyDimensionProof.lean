import YangMills.Construction.Dirichlet.NearCentresOfCubeProof
import YangMills.Construction.DirichletOperator.FactsOfTheSettingInLevelUnitsProof
import YangMills.Construction.Torus.BoundsOnTheWeightedDistanceProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.Weighted.GivenChainGeneral.Comparison
theorem supNormVec_eq_norm (v : Fin 4 → ℝ) : TorusMetric.supNormVec v = ‖v‖ := by apply _root_.YangMills.Construction.LevelUnitFacts.supNormVec_eq_norm <;> assumption
theorem torusSupNorm_eq_supNorm {S : ℝ} (p : TorusMetric.Torus4 S) :
    TorusMetric.torusSupNorm p = supNorm (d := 4) p := by
  unfold TorusMetric.torusSupNorm supNorm
  congr 1
  ext r
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, supNormVec_eq_norm v⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, supNormVec_eq_norm v⟩
theorem setSupDist_eq_supSetDist {S : ℝ} (A C : Set (TorusMetric.Torus4 S)) :
    TorusMetric.setSupDist A C = supSetDist (d := 4) A C := by
  unfold TorusMetric.setSupDist supSetDist
  simp only [torusSupNorm_eq_supNorm]
theorem mem_spacingLattice {S σ : ℝ} {x : PeriodicTorus 4 S} :
    x ∈ spacingLattice 4 S σ ↔ ∃ k : Fin 4 → ℤ, x = torusProj 4 S fun μ => (k μ : ℝ) * σ :=
  Iff.rfl
theorem mem_shellSites {S : ℝ} {L : ℕ} {ξ : ℝ} {Ω : ℕ → Set (PeriodicTorus 4 S)} {n : ℕ}
    {y : PeriodicTorus 4 S} :
    y ∈ shellSites L ξ Ω n ↔
      n ≤ lastNonemptyIndex Ω ∧ y ∈ spacingLattice 4 S (scaleSpacing L ξ n) ∧ y ∈ shell Ω n :=
  Iff.rfl
theorem mem_unionShellSites {S : ℝ} {L : ℕ} {ξ : ℝ} {t : ℕ} {Ω : ℕ → Set (PeriodicTorus 4 S)}
    {y : PeriodicTorus 4 S} : y ∈ unionShellSites L ξ t Ω ↔ ∃ n ≤ t, y ∈ shellSites L ξ Ω n :=
  Iff.rfl
section Data
variable (D : TorusData)
theorem cubeAround_eq_cubeAt (σ : ℝ) (y : D.Space) :
    D.cubeAround σ y = Torus.cubeAt (d := 4) (S := D.side) y σ := by
  ext x
  simp only [TorusData.cubeAround, Torus.cubeAt, mem_ofPred_eq, torusSupNorm_eq_supNorm]
theorem latticeAt_eq_spacingLattice (σ : ℝ) :
    D.latticeAt σ = (spacingLattice 4 D.side σ : Set (PeriodicTorus 4 D.side)) := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine mem_spacingLattice.2 ⟨k, ?_⟩
    funext μ
    simp [TorusMetric.torusProj, Torus.torusProj, mul_comm]
  · intro hx
    obtain ⟨k, rfl⟩ := mem_spacingLattice.1 hx
    refine ⟨k, ?_⟩
    funext μ
    simp [TorusMetric.torusProj, Torus.torusProj, mul_comm]
theorem partitionAt_eq_cubePartition (σ : ℝ) :
    D.partitionAt σ = Torus.cubePartition 4 D.side σ := by
  ext Q
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [latticeAt_eq_spacingLattice] at hc
    exact ⟨c, hc, cubeAround_eq_cubeAt D σ c⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, by rw [latticeAt_eq_spacingLattice]; exact hc, cubeAround_eq_cubeAt D σ c⟩
theorem isCubeUnionAt_iff (σ : ℝ) (X : Set D.Space) :
    D.IsCubeUnionAt σ X ↔ Torus.IsCubeUnion (d := 4) (S := D.side) σ X := by
  unfold TorusData.IsCubeUnionAt Torus.IsCubeUnion
  rw [partitionAt_eq_cubePartition]
theorem scaleSpacing_natCast (n : ℕ) : scaleSpacing D.L D.bareSpacing (n : ℤ) = D.scale n := by
  simp [Torus.scaleSpacing, TorusData.scale]
theorem scale_zero : D.scale 0 = D.bareSpacing := by simp [TorusData.scale]
theorem three_le_L : 3 ≤ D.L := D.blocking.three_le_factor
theorem one_lt_L : (1 : ℝ) < D.L := by
  have := three_le_L D
  exact_mod_cast (by omega : 1 < D.L)
theorem scale_pos (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
theorem blockNumber_mul_scale {μ : ℕ} (hμ : D.blockNumber = D.L ^ μ) (n : ℕ) :
    (D.blockNumber : ℝ) * D.scale n = D.scale (n + μ) := by
  simp only [TorusData.scale, hμ, pow_add]
  push_cast
  ring
theorem le_of_scale_le {μ i : ℕ} (hμ : D.blockNumber = D.L ^ μ)
    (h : D.scale i ≤ (D.blockNumber : ℝ) * D.scale D.top) : i ≤ D.top + μ := by
  rw [blockNumber_mul_scale D hμ] at h
  have h' : (D.L : ℝ) ^ i ≤ (D.L : ℝ) ^ (D.top + μ) :=
    le_of_mul_le_mul_right h D.bareSpacing_pos
  exact (pow_le_pow_iff_right₀ (one_lt_L D)).1 h'
theorem side_div_scale {μ i : ℕ} (hμ : D.blockNumber = D.L ^ μ) (hi : i ≤ D.top + μ) :
    IsPosEvenNat (D.side / D.scale i) := by
  obtain ⟨k, hk, hS⟩ := D.side_multiple
  have hL : 0 < D.L := by have := three_le_L D; omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi
  refine ⟨k * D.L ^ j, Nat.mul_pos hk (pow_pos hL j), ?_⟩
  have e : (D.L : ℝ) ^ μ * (D.L : ℝ) ^ D.top = (D.L : ℝ) ^ j * (D.L : ℝ) ^ i := by
    rw [← pow_add, ← pow_add, show μ + D.top = j + i by omega]
  rw [div_eq_iff (scale_pos D i).ne', hS, TorusData.scale, hμ]
  push_cast
  linear_combination (2 * (k : ℝ) * D.bareSpacing) * e
theorem side_pos : 0 < D.side := by apply _root_.YangMills.Construction.Weighted.TorusData.side_pos <;> assumption
theorem two_mul_scale_le_side (n : ℕ) (hn : n ≤ D.top) :
    2 * (D.blockNumber : ℝ) * D.scale n ≤ D.side ∧
      2 * (D.L : ℝ) * D.scale n ≤ 2 * (D.blockNumber : ℝ) * D.scale n := by
  obtain ⟨k, hk, hS⟩ := D.side_multiple
  have hM : (D.L : ℝ) ≤ D.blockNumber := by exact_mod_cast D.le_blockNumber
  have hsp := scale_pos D n
  have hL := one_lt_L D
  constructor
  · have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have h2 : D.scale n ≤ (D.L : ℝ) ^ D.top * D.bareSpacing :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL.le hn) D.bareSpacing_pos.le
    have hM0 : (0 : ℝ) ≤ D.blockNumber := by positivity
    have h3 : (D.blockNumber : ℝ) * D.scale n ≤
        (D.blockNumber : ℝ) * ((D.L : ℝ) ^ D.top * D.bareSpacing) :=
      mul_le_mul_of_nonneg_left h2 hM0
    have h4 : 0 ≤ (D.blockNumber : ℝ) * ((D.L : ℝ) ^ D.top * D.bareSpacing) := by
      have := D.bareSpacing_pos
      positivity
    rw [hS]
    nlinarith
  · have : 0 ≤ D.scale n := hsp.le
    nlinarith
theorem two_mul_bareSpacing_lt_side : 2 * D.bareSpacing < D.side := by
  have h := (two_mul_scale_le_side D 0 (Nat.zero_le _)).1
  rw [scale_zero] at h
  have hM : (3 : ℝ) ≤ D.blockNumber := by
    have := D.le_blockNumber
    have := three_le_L D
    exact_mod_cast (by omega : 3 ≤ D.blockNumber)
  nlinarith [D.bareSpacing_pos]
theorem parameters : Dirichlet.Parameters 4 D.L 1 1 :=
  ⟨by norm_num, three_le_L D, D.blocking.factor_odd, one_pos, le_rfl⟩
theorem isNatAtLeastTwo_of_isPosEvenNat {r : ℝ} (h : IsPosEvenNat r) : IsNatAtLeastTwo r := by apply _root_.YangMills.Construction.Dirichlet.NearCentres.isNatAtLeastTwo_of_isPosEvenNat <;> assumption
theorem nestedPartitionFacts (hT : PartitionsHold) {μ : ℕ}
    (hμ : D.blockNumber = D.L ^ μ) {i' i : ℕ} (h : i' ≤ i) (hi : i ≤ D.top + μ) :
    NestedPartitionFacts 4 D.L D.bareSpacing D.side (scaleSpacing D.L D.bareSpacing (i : ℤ))
      (scaleSpacing D.L D.bareSpacing (i' : ℤ)) := by
  refine (hT 4 D.L 1 1 (parameters D) D.bareSpacing D.side D.bareSpacing_pos (side_pos D)).2.1
    (i' : ℤ) (i : ℤ) (by exact_mod_cast h) ?_
  rw [scaleSpacing_natCast]
  exact isNatAtLeastTwo_of_isPosEvenNat (side_div_scale D hμ hi)
theorem nestedPartitionFacts_bare (hT : PartitionsHold) {μ : ℕ}
    (hμ : D.blockNumber = D.L ^ μ) {i : ℕ} (hi : i ≤ D.top + μ) :
    NestedPartitionFacts 4 D.L D.bareSpacing D.side (scaleSpacing D.L D.bareSpacing (i : ℤ))
      D.bareSpacing := by
  have h := nestedPartitionFacts D hT hμ (Nat.zero_le i) hi
  rwa [scaleSpacing_natCast D 0, scale_zero] at h
theorem cubeComplement_eq_closure (hT : PartitionsHold) {μ i : ℕ}
    (hμ : D.blockNumber = D.L ^ μ) (hi : i ≤ D.top + μ) {Y : Set D.Space}
    (hY : Torus.IsCubeUnion (d := 4) (S := D.side) (scaleSpacing D.L D.bareSpacing (i : ℤ)) Y) :
    cubeComplement (scaleSpacing D.L D.bareSpacing (i : ℤ)) Y = closure Yᶜ := by
  refine (nestedPartitionFacts D hT hμ le_rfl hi).cubeComplement_eq_closure Y hY _
    ⟨(i : ℤ), rfl, ?_⟩ hY
  rw [scaleSpacing_natCast]
  exact isNatAtLeastTwo_of_isPosEvenNat (side_div_scale D hμ hi)
end Data
section Sequence
variable {D : TorusData} (B : SeparatedChain D)
theorem bddAbove_stage_nonempty : BddAbove {n | (B.stage n).Nonempty} := by
  refine ⟨D.top, fun n hn => ?_⟩
  by_contra h
  have h' := B.empty_above n (not_le.1 h)
  obtain ⟨x, hx⟩ := hn
  rw [h'] at hx
  simp at hx
theorem stage_eq_empty_of_lt {n : ℕ} (h : lastNonemptyIndex B.stage < n) : B.stage n = ∅ := by
  by_contra hne
  have := le_csSup (bddAbove_stage_nonempty B) (show n ∈ {n | (B.stage n).Nonempty} from
    Set.nonempty_iff_ne_empty.2 hne)
  exact absurd h (not_lt.2 this)
theorem lastNonemptyIndex_le_top (hne : (B.stage 0).Nonempty) :
    lastNonemptyIndex B.stage ≤ D.top :=
  csSup_le ⟨0, hne⟩ fun n hn => by
    by_contra h
    obtain ⟨x, hx⟩ := hn
    rw [B.empty_above n (not_le.1 h)] at hx
    simp at hx
theorem shell_eq_empty_of_lt {n : ℕ} (h : lastNonemptyIndex B.stage < n) :
    shell (d := 4) (S := D.side) B.stage n = ∅ := by
  simp [shell, stage_eq_empty_of_lt B h]
theorem isCubeUnion_stage {n : ℕ} (hn : n ≤ D.top) {μ : ℕ} (hμ : D.blockNumber = D.L ^ μ) :
    Torus.IsCubeUnion (d := 4) (S := D.side)
      (scaleSpacing D.L D.bareSpacing ((n + μ : ℕ) : ℤ)) (B.stage n) := by
  rw [scaleSpacing_natCast, ← blockNumber_mul_scale D hμ]
  exact (isCubeUnionAt_iff D _ _).1 (B.cubeUnion n hn)
theorem blockNumber_mul_scaleSpacing {μ : ℕ} (hμ : D.blockNumber = D.L ^ μ) (n : ℕ) :
    (D.blockNumber : ℝ) * scaleSpacing D.L D.bareSpacing (n : ℤ) =
      scaleSpacing D.L D.bareSpacing ((n + μ : ℕ) : ℤ) := by
  rw [scaleSpacing_natCast, scaleSpacing_natCast, blockNumber_mul_scale D hμ]
theorem isSeparatedChain (hT : PartitionsHold) (hne : (B.stage 0).Nonempty) :
    IsSeparatedChain (d := 4) (S := D.side) D.L D.bareSpacing D.blockNumber D.gapNumber D.top
      B.stage := by
  obtain ⟨μ, hμ⟩ := D.blockNumber_power
  obtain ⟨ν, hν⟩ := D.gapNumber_power
  refine ⟨D.bareSpacing_pos, side_pos D, ⟨D.le_blockNumber, μ, hμ⟩, ⟨D.le_gapNumber, ν, hν⟩, hne,
    B.decreasing, fun n hn => B.empty_above n hn, ?_, ?_, ?_⟩
  · obtain ⟨k, hk, hS⟩ := D.side_multiple
    have ht := lastNonemptyIndex_le_top B hne
    have hL : 0 < D.L := by have := three_le_L D; omega
    refine ⟨k * D.L ^ (D.top - lastNonemptyIndex B.stage), Nat.mul_pos hk (pow_pos hL _), ?_⟩
    refine hS.trans ?_
    rw [scaleSpacing_natCast, TorusData.scale]
    push_cast
    have e : (D.L : ℝ) ^ D.top =
        (D.L : ℝ) ^ (D.top - lastNonemptyIndex B.stage) * (D.L : ℝ) ^ lastNonemptyIndex B.stage := by
      rw [← pow_add]
      congr 1
      omega
    linear_combination (2 * (k : ℝ) * (D.blockNumber : ℝ) * D.bareSpacing) * e
  · intro n hn
    rw [blockNumber_mul_scaleSpacing hμ]
    exact isCubeUnion_stage B (hn.trans (lastNonemptyIndex_le_top B hne)) hμ
  · intro n hn
    rw [blockNumber_mul_scaleSpacing hμ,
      cubeComplement_eq_closure D hT hμ (by omega) (isCubeUnion_stage B hn.le hμ),
      ← setSupDist_eq_supSetDist, scaleSpacing_natCast]
    exact B.separated n hn
variable {B}
theorem layer_eq_shell
    (hMem : ChainMemberFacts (d := 4) (S := D.side) D.L D.bareSpacing D.blockNumber D.top B.stage)
    (n : ℕ) : B.layer n = shell (d := 4) (S := D.side) B.stage n := by
  unfold SeparatedChain.layer
  split_ifs with h1 h2
  · rfl
  · subst h2
    have h0 : B.stage (D.top + 1) = ∅ := B.empty_above _ (Nat.lt_succ_self _)
    by_cases hn : D.top ≤ lastNonemptyIndex B.stage
    · apply Set.Subset.antisymm
      · unfold shell
        rw [h0, sdiff_empty]
        exact subset_closure
      · exact fun x hx => (hMem.shell_subset _ hn hx).1
    · rw [shell_eq_empty_of_lt B (not_le.1 hn), stage_eq_empty_of_lt B (not_le.1 hn)]
  · have h3 : D.top < n := by omega
    simp [shell, B.empty_above n h3]
theorem layerSites_eq_shellSites
    (hMem : ChainMemberFacts (d := 4) (S := D.side) D.L D.bareSpacing D.blockNumber D.top B.stage)
    (n : ℕ) :
    B.layerSites n = shellSites (d := 4) (S := D.side) D.L D.bareSpacing B.stage n := by
  ext y
  unfold SeparatedChain.layerSites
  rw [mem_shellSites, layer_eq_shell hMem, latticeAt_eq_spacingLattice, scaleSpacing_natCast]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    by_contra h
    rw [shell_eq_empty_of_lt B (not_le.1 h)] at h2
    simp at h2
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩
theorem siteScale_eq_shellSpacing
    (hMem : ChainMemberFacts (d := 4) (S := D.side) D.L D.bareSpacing D.blockNumber D.top B.stage)
    (y : D.Space) :
    B.siteScale y = shellSpacing (d := 4) (S := D.side) D.L D.bareSpacing B.stage y := by
  unfold SeparatedChain.siteScale shellSpacing shellIndex
  rw [scaleSpacing_natCast]
  simp only [layerSites_eq_shellSites hMem]
theorem siteCube_eq
    (hMem : ChainMemberFacts (d := 4) (S := D.side) D.L D.bareSpacing D.blockNumber D.top B.stage)
    (y : D.Space) :
    B.siteCube y = Torus.siteCube (d := 4) (S := D.side) D.L D.bareSpacing B.stage y := by
  unfold SeparatedChain.siteCube Torus.siteCube
  rw [siteScale_eq_shellSpacing hMem, cubeAround_eq_cubeAt]
theorem allSites_eq_unionShellSites
    (hMem : ChainMemberFacts (d := 4) (S := D.side) D.L D.bareSpacing D.blockNumber D.top B.stage) :
    B.allSites = unionShellSites (d := 4) (S := D.side) D.L D.bareSpacing D.top B.stage := by
  ext y
  unfold SeparatedChain.allSites
  rw [mem_unionShellSites]
  simp only [mem_iUnion, Finset.mem_range, layerSites_eq_shellSites hMem, exists_prop,
    Nat.lt_succ_iff]
end Sequence
section Sites
variable {D : TorusData}
theorem latticeAt_scale_zero : D.latticeAt (D.scale 0) =
    (spacingLattice 4 D.side D.bareSpacing : Set (PeriodicTorus 4 D.side)) := by
  rw [latticeAt_eq_spacingLattice, scale_zero]
theorem bareSite_mem (x : D.BareSite) : (x : D.Space) ∈ spacingLattice 4 D.side D.bareSpacing :=
  latticeAt_scale_zero.subset x.2
def toLatticeSite (x : D.BareSite) : Dirichlet.LatticeSite 4 D.side D.bareSpacing :=
  ⟨x.1, bareSite_mem x⟩
def ofLatticeSite (x : Dirichlet.LatticeSite 4 D.side D.bareSpacing) : D.BareSite :=
  ⟨x.1, latticeAt_scale_zero.symm.subset x.2⟩
theorem toLatticeSite_ofLatticeSite (x : Dirichlet.LatticeSite 4 D.side D.bareSpacing) :
    toLatticeSite (ofLatticeSite x) = x := rfl
theorem toLatticeSite_injective : Function.Injective (toLatticeSite (D := D)) := by
  intro a b h
  have h' : (toLatticeSite a).1 = (toLatticeSite b).1 := congrArg Subtype.val h
  exact Subtype.ext h'
theorem unitStep_eq (μ : Fin 4) :
    D.unitStep μ = (Dirichlet.unitStep 4 D.side D.bareSpacing μ).1 := by
  unfold TorusData.unitStep
  rw [scale_zero]
  rfl
theorem adjacent_iff_isNeighbor (x x' : D.BareSite) :
    TorusData.Adjacent x x' ↔ Dirichlet.IsNeighbor (toLatticeSite x) (toLatticeSite x') := by
  constructor
  · rintro ⟨b, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · obtain ⟨μ, hμ⟩ := b.isPositive
      refine ⟨μ, Or.inl (Subtype.ext ?_)⟩
      rw [unitStep_eq] at hμ
      exact sub_eq_iff_eq_add'.1 hμ
    · obtain ⟨μ, hμ⟩ := b.isPositive
      refine ⟨μ, Or.inr (Subtype.ext ?_)⟩
      rw [unitStep_eq] at hμ
      exact eq_sub_of_add_eq (sub_eq_iff_eq_add'.1 hμ).symm
  · rintro ⟨μ, h | h⟩
    · have h' : (x' : D.Space) = (x : D.Space) +
          (Dirichlet.unitStep 4 D.side D.bareSpacing μ).1 := congrArg Subtype.val h
      refine ⟨⟨x, x', μ, ?_⟩, Or.inl ⟨rfl, rfl⟩⟩
      rw [unitStep_eq, h']
      abel
    · have h' : (x' : D.Space) = (x : D.Space) -
          (Dirichlet.unitStep 4 D.side D.bareSpacing μ).1 := congrArg Subtype.val h
      refine ⟨⟨x', x, μ, ?_⟩, Or.inr ⟨rfl, rfl⟩⟩
      rw [unitStep_eq, h']
      abel
theorem addCircle_coe_ne_zero {c : ℝ} (h0 : 0 < c) (h1 : c < D.side) :
    (c : AddCircle D.side) ≠ 0 := by
  rw [Ne, AddCircle.coe_eq_zero_iff]
  rintro ⟨n, hn⟩
  rw [zsmul_eq_mul] at hn
  have hs := side_pos D
  obtain hn0 | hn0 := le_or_gt n 0
  · have : (n : ℝ) * D.side ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hn0) hs.le
    linarith
  · have : D.side ≤ (n : ℝ) * D.side := le_mul_of_one_le_left hs.le (by exact_mod_cast hn0)
    linarith
theorem unitStep_add_unitStep_ne_zero (μ ν : Fin 4) : D.unitStep μ + D.unitStep ν ≠ 0 := by
  intro h
  have h2 := congrFun h μ
  have hξ := D.bareSpacing_pos
  have hS := two_mul_bareSpacing_lt_side D
  simp only [unitStep_eq, Dirichlet.unitStep, Pi.add_apply, Pi.zero_apply, torusProj] at h2
  by_cases e : ν = μ
  · subst e
    rw [Pi.single_eq_same, ← AddCircle.coe_add] at h2
    exact addCircle_coe_ne_zero (D := D) (by linarith) (by linarith) h2
  · rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm e), AddCircle.coe_zero, add_zero] at h2
    exact addCircle_coe_ne_zero (D := D) hξ (by linarith) h2
theorem ncard_bondsAtSite
    (hN : ∀ x : Dirichlet.LatticeSite 4 D.side D.bareSpacing,
      {x' | Dirichlet.IsNeighbor x x'}.ncard = 2 * 4) (x : D.BareSite) :
    (TorusData.bondsAtSite x).ncard = 2 * 4 := by
  classical
  rw [← hN (toLatticeSite x)]
  have back : ∀ a b : D.Bond, a.source = x → b.target = x → a.target = b.source → False := by
    intro a b ha hb hab
    obtain ⟨μ, hμ⟩ := a.isPositive
    obtain ⟨ν, hν⟩ := b.isPositive
    apply unitStep_add_unitStep_ne_zero (D := D) μ ν
    rw [← hμ, ← hν, ha, hb, hab]
    abel
  refine Set.ncard_congr
    (fun b _ => toLatticeSite (if b.source = x then b.target else b.source)) ?_ ?_ ?_
  · intro b hb
    show Dirichlet.IsNeighbor _ _
    rw [← adjacent_iff_isNeighbor]
    by_cases h : b.source = x
    · rw [if_pos h]
      exact ⟨b, Or.inl ⟨h, rfl⟩⟩
    · rw [if_neg h]
      exact ⟨b, Or.inr ⟨rfl, hb.resolve_left h⟩⟩
  · intro a b ha hb hab
    have hab' := toLatticeSite_injective hab
    by_cases h1 : a.source = x <;> by_cases h2 : b.source = x
    · rw [if_pos h1, if_pos h2] at hab'
      exact TorusData.Bond.ext (h1.trans h2.symm) hab'
    · rw [if_pos h1, if_neg h2] at hab'
      exact (back a b h1 (hb.resolve_left h2) hab').elim
    · rw [if_neg h1, if_pos h2] at hab'
      exact (back b a h2 (ha.resolve_left h1) hab'.symm).elim
    · rw [if_neg h1, if_neg h2] at hab'
      exact TorusData.Bond.ext hab' ((ha.resolve_left h1).trans (hb.resolve_left h2).symm)
  · intro x' hx'
    have hj : TorusData.Adjacent x (ofLatticeSite x') :=
      (adjacent_iff_isNeighbor x (ofLatticeSite x')).2 hx'
    obtain ⟨b, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hj
    · refine ⟨b, Or.inl h1, ?_⟩
      simp only [if_pos h1, h2, toLatticeSite_ofLatticeSite]
    · refine ⟨b, Or.inr h2, ?_⟩
      by_cases h : b.source = x
      · simp only [if_pos h]
        rw [h2, ← h, h1, toLatticeSite_ofLatticeSite]
      · show toLatticeSite (if b.source = x then b.target else b.source) = x'
        rw [if_neg h, h1, toLatticeSite_ofLatticeSite]
end Sites
section Known
variable {D : TorusData}
theorem self_mem_cubeAt {S σ : ℝ} (hσ : 0 ≤ σ) (y : PeriodicTorus 4 S) :
    y ∈ Torus.cubeAt y σ := by
  have h0 : supNorm (0 : PeriodicTorus 4 S) ≤ 0 := by
    refine csInf_le ⟨0, ?_⟩ ⟨0, ?_, by simp⟩
    · rintro r ⟨v, -, rfl⟩
      exact norm_nonneg _
    · funext μ
      simp [torusProj]
  show supNorm (y - y) ≤ σ / 2
  rw [sub_self]
  linarith
theorem scaleSpacing_natCast_pos (D : TorusData) (n : ℕ) :
    0 < scaleSpacing D.L D.bareSpacing (n : ℤ) := by
  rw [scaleSpacing_natCast]
  exact scale_pos D n
structure ChainFacts (B : SeparatedChain D) : Prop where
  isSep : IsSeparatedChain (d := 4) (S := D.side) D.L D.bareSpacing D.blockNumber D.gapNumber
    D.top B.stage
  stageFacts : ChainMemberFacts (d := 4) (S := D.side) D.L D.bareSpacing D.blockNumber D.top
    B.stage
  cubeFacts : ∀ n ≤ lastNonemptyIndex B.stage,
    ShellCubeFacts (d := 4) (S := D.side) D.L D.bareSpacing D.blockNumber D.top B.stage n
  location : SiteLocationFacts (d := 4) (S := D.side) D.L D.bareSpacing D.top B.stage
  siteFacts : ∀ n ≤ lastNonemptyIndex B.stage,
    ∀ y ∈ shellSites (d := 4) (S := D.side) D.L D.bareSpacing B.stage n, ∀ z : Fin 4 → ℝ,
      torusProj 4 D.side z = y →
        CubeSiteFacts (d := 4) (S := D.side) D.L D.bareSpacing B.stage y z
  neighbors : ∀ x : Dirichlet.LatticeSite 4 D.side D.bareSpacing,
    {x' | Dirichlet.IsNeighbor x x'}.ncard = 2 * 4
  lastNonemptyIndex_le : lastNonemptyIndex B.stage ≤ D.top
  nested : ∀ n ≤ D.top, NestedPartitionFacts 4 D.L D.bareSpacing D.side
    (scaleSpacing D.L D.bareSpacing (n : ℤ)) (scaleSpacing D.L D.bareSpacing (n : ℤ))
  nestedBare : ∀ n ≤ D.top, NestedPartitionFacts 4 D.L D.bareSpacing D.side
    (scaleSpacing D.L D.bareSpacing (n : ℤ)) D.bareSpacing
theorem chainFacts (hT : PartitionsHold) (B : SeparatedChain D)
    (hne : (B.stage 0).Nonempty) : ChainFacts B := by
  obtain ⟨μ, hμ⟩ := D.blockNumber_power
  have hsep := isSeparatedChain B hT hne
  obtain ⟨-, hMem, hBlock, hPlace, hSite, hNbr⟩ :=
    (hT 4 D.L 1 1 (parameters D) D.bareSpacing D.side D.bareSpacing_pos (side_pos D)).2.2
      D.blockNumber D.gapNumber D.top B.stage hsep
  exact ⟨hsep, hMem, hBlock, hPlace, hSite, hNbr, lastNonemptyIndex_le_top B hne,
    fun n hn => nestedPartitionFacts D hT hμ le_rfl (by omega),
    fun n hn => nestedPartitionFacts_bare D hT hμ (by omega)⟩
variable {B : SeparatedChain D}
theorem mem_interior_cubeAt (K : ChainFacts B) {k : ℕ} {y : D.Space}
    (hy : y ∈ shellSites (d := 4) (S := D.side) D.L D.bareSpacing B.stage k) :
    y ∈ interior (Torus.cubeAt (d := 4) (S := D.side) y
      (scaleSpacing D.L D.bareSpacing (k : ℤ))) := by
  obtain ⟨hk, hl, -⟩ := mem_shellSites.1 hy
  exact (K.nested k (hk.trans K.lastNonemptyIndex_le)).grid_subset_interior y hl
    ⟨hl, self_mem_cubeAt (scaleSpacing_natCast_pos D k).le y⟩
theorem shellIndex_eq (K : ChainFacts B) {n : ℕ} {y : D.Space}
    (hy : y ∈ shellSites (d := 4) (S := D.side) D.L D.bareSpacing B.stage n) :
    shellIndex (d := 4) (S := D.side) D.L D.bareSpacing B.stage y = n := by
  have hk : y ∈ shellSites (d := 4) (S := D.side) D.L D.bareSpacing B.stage
      (shellIndex (d := 4) (S := D.side) D.L D.bareSpacing B.stage y) :=
    Nat.sInf_mem (s := {n | y ∈ shellSites (d := 4) (S := D.side) D.L D.bareSpacing B.stage n})
      ⟨n, hy⟩
  by_contra hne
  obtain ⟨hkt, -, -⟩ := mem_shellSites.1 hk
  obtain ⟨hnt, -, hln⟩ := mem_shellSites.1 hy
  have hd := (K.cubeFacts _ hkt).disjoint_shell y hk n (hnt.trans K.lastNonemptyIndex_le)
    (Ne.symm hne)
  exact Set.disjoint_left.1 hd (mem_interior_cubeAt K hk) hln
theorem siteCube_eq_cubeAt (K : ChainFacts B) {n : ℕ} {y : D.Space}
    (hy : y ∈ shellSites (d := 4) (S := D.side) D.L D.bareSpacing B.stage n) :
    Torus.siteCube (d := 4) (S := D.side) D.L D.bareSpacing B.stage y =
      Torus.cubeAt y (scaleSpacing D.L D.bareSpacing (n : ℤ)) := by
  unfold Torus.siteCube shellSpacing
  rw [shellIndex_eq K hy]
theorem mem_interior_siteCube (K : ChainFacts B) {n : ℕ} {y : D.Space}
    (hy : y ∈ shellSites (d := 4) (S := D.side) D.L D.bareSpacing B.stage n) :
    y ∈ interior (Torus.siteCube (d := 4) (S := D.side) D.L D.bareSpacing B.stage y) := by
  rw [siteCube_eq_cubeAt K hy]
  exact mem_interior_cubeAt K hy
theorem self_mem_siteCube (K : ChainFacts B) {n : ℕ} {y : D.Space}
    (hy : y ∈ shellSites (d := 4) (S := D.side) D.L D.bareSpacing B.stage n) :
    y ∈ Torus.siteCube (d := 4) (S := D.side) D.L D.bareSpacing B.stage y :=
  interior_subset (mem_interior_siteCube K hy)
theorem image_val_block (K : ChainFacts B) (y : D.Space) :
    Subtype.val '' B.block y =
      (spacingLattice 4 D.side D.bareSpacing : Set (PeriodicTorus 4 D.side)) ∩
        Torus.siteCube (d := 4) (S := D.side) D.L D.bareSpacing B.stage y := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨bareSite_mem x, ?_⟩
    have hx' : (x : D.Space) ∈ B.siteCube y := hx
    rwa [siteCube_eq K.stageFacts] at hx'
  · rintro ⟨hp, hc⟩
    refine ⟨ofLatticeSite ⟨p, hp⟩, ?_, rfl⟩
    show p ∈ B.siteCube y
    rwa [siteCube_eq K.stageFacts]
theorem mem_interior_siteCube_of_mem (K : ChainFacts B) {n : ℕ} {y : D.Space}
    (hy : y ∈ shellSites (d := 4) (S := D.side) D.L D.bareSpacing B.stage n)
    {p : D.Space} (hp : p ∈ spacingLattice 4 D.side D.bareSpacing)
    (hc : p ∈ Torus.siteCube (d := 4) (S := D.side) D.L D.bareSpacing B.stage y) :
    p ∈ interior (Torus.siteCube (d := 4) (S := D.side) D.L D.bareSpacing B.stage y) := by
  obtain ⟨hnt, hl, -⟩ := mem_shellSites.1 hy
  rw [siteCube_eq_cubeAt K hy] at hc ⊢
  exact (K.nestedBare n (hnt.trans K.lastNonemptyIndex_le)).grid_subset_interior y hl ⟨hp, hc⟩
end Known
section Segments
theorem displacement_segmentToLifted (s : TorusSegment 4) :
    (segmentToLifted s).displacement = s.direction := by
  simp [TorusMetric.LiftedSegment.displacement, segmentToLifted]
theorem pointAt_segmentToLifted (S : ℝ) (s : TorusSegment 4) (u : ℝ) :
    (segmentToLifted s).pointAt S u = s.pointAt S u := by
  unfold TorusMetric.LiftedSegment.pointAt TorusSegment.pointAt
  rw [displacement_segmentToLifted]
  rfl
theorem pathLengthIn_map (S : ℝ) (Γ : List (TorusSegment 4)) (X : Set (PeriodicTorus 4 S)) :
    TorusMetric.pathLengthIn S (Γ.map segmentToLifted) X = lengthWithin Γ X := by
  unfold TorusMetric.pathLengthIn lengthWithin
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun s _ => ?_)
  have e : Icc (0 : ℝ) 1 ∩ (segmentToLifted s).pointAt S ⁻¹' X =
      {τ ∈ Icc (0 : ℝ) 1 | s.pointAt S τ ∈ X} := by
    ext τ
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [mem_preimage, pointAt_segmentToLifted] at h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [mem_preimage, pointAt_segmentToLifted]⟩
  show TorusMetric.l1NormVec (segmentToLifted s).displacement * _ = _
  rw [displacement_segmentToLifted, e]
  rfl
theorem exists_eq_map_segmentToLifted (Γ : List TorusMetric.LiftedSegment) :
    ∃ Γ' : List (TorusSegment 4), Γ = Γ'.map segmentToLifted := by
  refine ⟨Γ.map fun s => ⟨s.tail, s.head - s.tail⟩, ?_⟩
  rw [List.map_map]
  conv_lhs => rw [← List.map_id Γ]
  refine List.map_congr_left fun s _ => ?_
  cases s
  simp [segmentToLifted]
theorem segmentsSupport_map (S : ℝ) (Γ : List (TorusSegment 4)) :
    TorusMetric.segmentsSupport S (Γ.map segmentToLifted) = segmentUnion S Γ := by
  ext p
  constructor
  · intro hp
    obtain ⟨s', hs', hp'⟩ := mem_iUnion₂.1 hp
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs'
    obtain ⟨u, hu, rfl⟩ := hp'
    exact ⟨s, hs, u, hu, pointAt_segmentToLifted S s u⟩
  · rintro ⟨s, hs, u, hu, rfl⟩
    exact mem_iUnion₂.2
      ⟨segmentToLifted s, List.mem_map.2 ⟨s, hs, rfl⟩, u, hu, pointAt_segmentToLifted S s u⟩
variable {D : TorusData} {B : SeparatedChain D}
theorem weightedLength_map_eq
    (hMem : ChainMemberFacts (d := 4) (S := D.side) D.L D.bareSpacing D.blockNumber D.top B.stage)
    (Γ : List (TorusSegment 4)) : B.weightedLength (Γ.map segmentToLifted) =
      chainWeightedLength (d := 4) (S := D.side) D.L D.bareSpacing D.top B.stage Γ := by
  have h0 : scaleSpacing D.L D.bareSpacing 0 = D.scale 0 := by
    simp [Torus.scaleSpacing, TorusData.scale]
  unfold SeparatedChain.weightedLength Torus.chainWeightedLength
  simp only [pathLengthIn_map, layer_eq_shell hMem, scaleSpacing_natCast, h0]
theorem weightedDistance_eq
    (hMem : ChainMemberFacts (d := 4) (S := D.side) D.L D.bareSpacing D.blockNumber D.top B.stage)
    (x x' : D.Space) : B.weightedDistance x x' =
      chainWeightedDist (d := 4) (S := D.side) D.L D.bareSpacing D.top B.stage x x' := by
  unfold SeparatedChain.weightedDistance chainWeightedDist
  congr 1
  ext r
  constructor
  · rintro ⟨Γ, hc, hx, hx', rfl⟩
    obtain ⟨Γ', rfl⟩ := exists_eq_map_segmentToLifted Γ
    unfold TorusMetric.IsTreeGraph at hc
    rw [segmentsSupport_map] at hc hx hx'
    exact ⟨Γ', hc, hx, hx', weightedLength_map_eq hMem Γ'⟩
  · rintro ⟨Γ, hc, hx, hx', rfl⟩
    refine ⟨Γ.map segmentToLifted, ?_, ?_, ?_, (weightedLength_map_eq hMem Γ).symm⟩
    · unfold TorusMetric.IsTreeGraph
      rwa [segmentsSupport_map]
    · rwa [segmentsSupport_map]
    · rwa [segmentsSupport_map]
end Segments
section Claims
theorem spaceIsPeriodicTorus (hT : PartitionsHold) (D : TorusData) :
    SpaceIsPeriodicTorus D := by
  obtain ⟨μ, hμ⟩ := D.blockNumber_power
  refine ⟨rfl, fun i hi => ?_, ?_, fun i' i h hi => ?_, fun n hn => two_mul_scale_le_side D n hn⟩
  · refine ⟨side_div_scale D hμ (le_of_scale_le D hμ hi), ?_, ?_⟩
    · rw [latticeAt_eq_spacingLattice, scaleSpacing_natCast]
    · rw [partitionAt_eq_cubePartition, scaleSpacing_natCast]
  · exact (hT 4 D.L 1 1 (parameters D) _ _ D.bareSpacing_pos (side_pos D)).1
  · exact nestedPartitionFacts D hT hμ h (le_of_scale_le D hμ hi)
variable {D : TorusData} {B : SeparatedChain D}
theorem agreesWithGeneral (K : ChainFacts B) : AgreesWithGeneral B :=
  ⟨K.isSep, fun n _ => layer_eq_shell K.stageFacts n,
    fun n _ => layerSites_eq_shellSites K.stageFacts n,
    allSites_eq_unionShellSites K.stageFacts, fun y _ => siteScale_eq_shellSpacing K.stageFacts y,
    fun y _ => siteCube_eq K.stageFacts y, weightedLength_map_eq K.stageFacts,
    weightedDistance_eq K.stageFacts⟩
theorem stage_antitone {m m' : ℕ} (h : m ≤ m') : B.stage m' ⊆ B.stage m := by apply _root_.YangMills.Construction.Weighted.DistBounds.stage_anti <;> assumption
theorem shellSites_eq_empty_of_lt {n : ℕ} (h : lastNonemptyIndex B.stage < n) :
    shellSites (d := 4) (S := D.side) D.L D.bareSpacing B.stage n = ∅ := by
  ext y
  simp only [mem_shellSites, mem_empty_iff_false, iff_false]
  exact fun h' => absurd h'.1 (not_le.2 h)
theorem iUnion_siteCube_allSites (K : ChainFacts B) :
    ⋃ y ∈ B.allSites, B.siteCube y = B.stage 0 := by
  apply Subset.antisymm
  · intro p hp
    obtain ⟨y, hy, hc⟩ := mem_iUnion₂.1 hp
    rw [allSites_eq_unionShellSites K.stageFacts] at hy
    obtain ⟨n, -, hyn⟩ := mem_unionShellSites.1 hy
    obtain ⟨hnt, -, -⟩ := mem_shellSites.1 hyn
    rw [K.stageFacts.zero_eq_iUnion]
    refine mem_iUnion₂.2 ⟨n, hnt, ?_⟩
    rw [(K.cubeFacts n hnt).shell_eq_iUnion]
    rw [siteCube_eq K.stageFacts] at hc
    exact mem_iUnion₂.2 ⟨y, hyn, hc⟩
  · intro p hp
    rw [K.stageFacts.zero_eq_iUnion] at hp
    obtain ⟨m, hm, hl⟩ := mem_iUnion₂.1 hp
    have hm' : m ≤ lastNonemptyIndex B.stage := hm
    rw [(K.cubeFacts m hm').shell_eq_iUnion] at hl
    obtain ⟨y, hy, hc⟩ := mem_iUnion₂.1 hl
    refine mem_iUnion₂.2 ⟨y, ?_, ?_⟩
    · rw [allSites_eq_unionShellSites K.stageFacts]
      exact mem_unionShellSites.2 ⟨m, hm'.trans K.lastNonemptyIndex_le, hy⟩
    · rwa [siteCube_eq K.stageFacts]
theorem shellsAndCubes (hT : PartitionsHold) (K : ChainFacts B) : ShellsAndCubes B := by
  obtain ⟨μ, hμ⟩ := D.blockNumber_power
  refine ⟨?_, ?_, ?_, ?_, iUnion_siteCube_allSites K, ?_, ?_, ?_⟩
  · intro n hn
    rw [layer_eq_shell K.stageFacts, isCubeUnionAt_iff, ← scaleSpacing_natCast]
    by_cases h : n ≤ lastNonemptyIndex B.stage
    · rw [K.stageFacts.shell_eq n h]
      exact ⟨_, sep_subset _ _, rfl⟩
    · rw [shell_eq_empty_of_lt B (not_le.1 h)]
      exact ⟨∅, empty_subset _, sUnion_empty.symm⟩
  · intro n hn
    simp only [layer_eq_shell K.stageFacts, layerSites_eq_shellSites K.stageFacts,
      siteCube_eq K.stageFacts]
    by_cases h : n ≤ lastNonemptyIndex B.stage
    · exact (K.cubeFacts n h).shell_eq_iUnion
    · rw [shell_eq_empty_of_lt B (not_le.1 h), shellSites_eq_empty_of_lt (not_le.1 h)]
      simp
  · intro n hn
    rw [layer_eq_shell K.stageFacts]
    by_cases h : n ≤ lastNonemptyIndex B.stage
    · have hr := K.stageFacts.isCubeUnion_succ n h
      have hs := K.stageFacts.shell_subset n h
      rw [blockNumber_mul_scaleSpacing hμ] at hr hs
      rw [cubeComplement_eq_closure D hT hμ (by omega) hr] at hs
      exact hs
    · rw [shell_eq_empty_of_lt B (not_le.1 h)]
      exact empty_subset _
  · intro m m' h
    exact closure_mono (compl_subset_compl.2 (stage_antitone h))
  · intro n y hy
    rw [layerSites_eq_shellSites K.stageFacts] at hy
    rw [siteCube_eq K.stageFacts]
    exact (K.cubeFacts n (mem_shellSites.1 hy).1).disjoint_succ y hy
  · intro n y hy m hm
    rw [layerSites_eq_shellSites K.stageFacts] at hy
    rw [siteCube_eq K.stageFacts, layer_eq_shell K.stageFacts]
    by_cases hmt : m ≤ D.top
    · exact (K.cubeFacts n (mem_shellSites.1 hy).1).disjoint_shell y hy m hmt hm
    · rw [shell_eq_empty_of_lt B (by have := K.lastNonemptyIndex_le; omega)]
      exact disjoint_empty _
  · intro n y hy y' hy' hne
    rw [layerSites_eq_shellSites K.stageFacts] at hy
    rw [allSites_eq_unionShellSites K.stageFacts] at hy'
    rw [siteCube_eq K.stageFacts, siteCube_eq K.stageFacts]
    exact (K.cubeFacts n (mem_shellSites.1 hy).1).disjoint_siteCube y hy y' hy' hne
theorem siteBlockGrid (K : ChainFacts B) {n : ℕ} {y : D.Space} {z : Fin 4 → ℝ}
    (hy : y ∈ B.layerSites n) (hz : torusProj 4 D.side z = y) : SiteBlockGrid B n y z := by
  rw [layerSites_eq_shellSites K.stageFacts] at hy
  obtain ⟨hnt, -, -⟩ := mem_shellSites.1 hy
  have hsf := K.siteFacts n hnt y hy z hz
  have hss : shellSpacing (d := 4) (S := D.side) D.L D.bareSpacing B.stage y =
      scaleSpacing D.L D.bareSpacing (n : ℤ) := by
    unfold shellSpacing
    rw [shellIndex_eq K hy]
  have hN : shellSpacing (d := 4) (S := D.side) D.L D.bareSpacing B.stage y / D.bareSpacing =
      (D.L : ℝ) ^ n := by
    rw [hss, scaleSpacing_natCast, TorusData.scale]
    exact mul_div_cancel_right₀ _ D.bareSpacing_pos.ne'
  have hg := hsf.isCenteredGrid
  have hadj := hsf.isNeighbor_iff
  rw [hN] at hg hadj
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [image_val_block K, scale_zero]
    exact hg
  · rw [siteScale_eq_shellSpacing K.stageFacts, scale_zero, hN, pow_mul]
  · intro x hx
    have hx' : (x : D.Space) ∈ B.siteCube y := hx
    rw [siteCube_eq K.stageFacts] at hx' ⊢
    exact mem_interior_siteCube_of_mem K hy (bareSite_mem x) hx'
  · intro k hk k' hk' x x' hx hx'
    have e : ∀ j : Fin 4 → ℤ, gridImage D.side (D.scale 0) z j =
        gridImage D.side D.bareSpacing z j := fun j => by rw [scale_zero]
    exact (adjacent_iff_isNeighbor x x').trans
      (hadj k hk k' hk' (toLatticeSite x) (toLatticeSite x') (hx.trans (e k)) (hx'.trans (e k')))
theorem cubeAround_scale_zero (p : D.Space) :
    D.cubeAround (D.scale 0) p = Torus.cubeAt (d := 4) (S := D.side) p D.bareSpacing := by
  rw [cubeAround_eq_cubeAt, scale_zero]
theorem blockPartition (K : ChainFacts B) : BlockPartition B := by
  have hall := allSites_eq_unionShellSites K.stageFacts
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ncard_bondsAtSite K.neighbors⟩
  · intro y hy
    rw [hall] at hy
    obtain ⟨n, hn, hyn⟩ := mem_unionShellSites.1 hy
    obtain ⟨hnt, hl, -⟩ := mem_shellSites.1 hyn
    refine ⟨ofLatticeSite ⟨y, (K.nestedBare n hn).spacingLattice_le hl⟩, ?_⟩
    show y ∈ B.siteCube y
    rw [siteCube_eq K.stageFacts]
    exact self_mem_siteCube K hyn
  · intro y hy y' hy' hne
    rw [hall] at hy hy'
    obtain ⟨n, hn, hyn⟩ := mem_unionShellSites.1 hy
    obtain ⟨hnt, -, -⟩ := mem_shellSites.1 hyn
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    have h1 : (x : D.Space) ∈ B.siteCube y := hx
    have h2 : (x : D.Space) ∈ B.siteCube y' := hx'
    rw [siteCube_eq K.stageFacts] at h1 h2
    exact Set.disjoint_left.1 ((K.cubeFacts n hnt).disjoint_siteCube y hyn y' hy' (Ne.symm hne))
      (mem_interior_siteCube_of_mem K hyn (bareSite_mem x) h1) h2
  · ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
      show (x : D.Space) ∈ B.stage 0
      rw [← iUnion_siteCube_allSites K]
      exact mem_iUnion₂.2 ⟨y, hy, hxy⟩
    · intro hx
      obtain ⟨y, hy, hint, -⟩ := K.location.exists_of_mem x.1 (bareSite_mem x) hx
      refine mem_iUnion₂.2 ⟨y, by rw [hall]; exact hy, ?_⟩
      show (x : D.Space) ∈ B.siteCube y
      rw [siteCube_eq K.stageFacts]
      exact interior_subset hint
  · intro x hx
    obtain ⟨y, hy, hint, hother, hcube, -⟩ := K.location.exists_of_mem x.1 (bareSite_mem x) hx
    have hex : ∃ y, y ∈ B.allSites ∧ x ∈ B.block y := by
      refine ⟨y, by rw [hall]; exact hy, ?_⟩
      show (x : D.Space) ∈ B.siteCube y
      rw [siteCube_eq K.stageFacts]
      exact interior_subset hint
    have hs := Classical.epsilon_spec hex
    have hc : B.blockCenter x = y := by
      by_contra h
      have h1 : B.blockCenter x ∈ B.allSites := hs.1
      have h2 : (x : D.Space) ∈ B.siteCube (B.blockCenter x) := hs.2
      rw [hall] at h1
      rw [siteCube_eq K.stageFacts] at h2
      exact hother _ h1 h h2
    rw [hc, cubeAround_scale_zero, siteCube_eq K.stageFacts]
    exact hcube
  · intro Y hY
    ext y'
    constructor
    · intro h
      refine ⟨hY h, mem_iUnion₂.2 ⟨y', h, ?_⟩⟩
      have h1 := hY h
      rw [hall] at h1
      obtain ⟨n, -, hyn⟩ := mem_unionShellSites.1 h1
      rw [siteCube_eq K.stageFacts]
      exact self_mem_siteCube K hyn
    · rintro ⟨h1, h2⟩
      obtain ⟨y, hyY, hc⟩ := mem_iUnion₂.1 h2
      by_contra hnot
      have hne : y ≠ y' := fun e => hnot (e ▸ hyY)
      have h3 := hY hyY
      rw [hall] at h1 h3
      obtain ⟨n, -, hyn⟩ := mem_unionShellSites.1 h1
      obtain ⟨hnt, -, -⟩ := mem_shellSites.1 hyn
      rw [siteCube_eq K.stageFacts] at hc
      exact Set.disjoint_left.1 ((K.cubeFacts n hnt).disjoint_siteCube y' hyn y h3 hne)
        (mem_interior_siteCube K hyn) hc
  · intro Y _
    ext x
    constructor
    · intro h
      obtain ⟨y, hy, hc⟩ := mem_iUnion₂.1 h
      exact mem_iUnion₂.2 ⟨y, hy, hc⟩
    · intro h
      obtain ⟨y, hy, hc⟩ := mem_iUnion₂.1 h
      exact mem_iUnion₂.2 ⟨y, hy, hc⟩
end Claims
theorem givenChainGeneralFacts (hT : PartitionsHold) (hW : WeightedLength.HoldsForAll) :
    GivenChainGeneralFacts := by
  intro G
  have K := chainFacts hT G.chain G.stage_zero_nonempty
  refine ⟨spaceIsPeriodicTorus hT G.data, agreesWithGeneral K, shellsAndCubes hT K,
    fun n y hy z hz => siteBlockGrid K hy hz, blockPartition K, fun x x' x'' => ?_⟩
  simp only [weightedDistance_eq K.stageFacts]
  let 𝒮 : Dirichlet.BlockSetting 4 G.data.L 1 1 G.data.side :=
    ⟨G.data.bareSpacing, G.data.blockNumber, G.data.gapNumber, G.data.top, G.chain.stage,
      fun _ => 1, K.isSep, fun _ _ => ⟨le_rfl, le_rfl⟩⟩
  exact (hW 4 G.data.L 1 1 (parameters G.data) G.data.side 𝒮).dist_triangle x x' x''
end YangMills.Construction.Weighted.GivenChainGeneral.Comparison
end
