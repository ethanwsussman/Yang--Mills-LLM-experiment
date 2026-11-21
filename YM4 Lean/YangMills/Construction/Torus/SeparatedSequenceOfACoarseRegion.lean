import YangMills.Construction.Lattice.PeriodicTorus
import YangMills.Construction.Torus.FormsAveragesAndOperatorsOnAGeneralTorus
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.GeneralTorus
def gridCubes (S s : ℝ) : Set (Set (TorusMetric.Torus4 S)) :=
  {Q | ∃ y ∈ spacingLattice S s, Q = supCube s y}
theorem exists_mem_supCube {S s : ℝ} (hs : 0 < s) [Fact (0 < S)] (x : TorusMetric.Torus4 S) :
    ∃ y ∈ spacingLattice S s, x ∈ supCube s y := by
  have hlift : ∀ μ, ∃ t : ℝ, (t : AddCircle S) = x μ := fun μ =>
    QuotientAddGroup.mk_surjective (x μ)
  choose t ht using hlift
  refine ⟨TorusMetric.torusProj S fun μ => s * ((round (t μ / s) : ℤ) : ℝ),
    ⟨fun μ => round (t μ / s), rfl⟩, ?_⟩
  have hx : x = TorusMetric.torusProj S t := funext fun μ => (ht μ).symm
  have hsub : x - TorusMetric.torusProj S (fun μ => s * ((round (t μ / s) : ℤ) : ℝ)) =
      TorusMetric.torusProj S (fun μ => t μ - s * ((round (t μ / s) : ℤ) : ℝ)) := by
    rw [hx]
    funext μ
    simp [TorusMetric.torusProj]
  have hle : ∀ μ, |t μ - s * ((round (t μ / s) : ℤ) : ℝ)| ≤ s / 2 := by
    intro μ
    have hr := abs_sub_round (t μ / s)
    have ht' : t μ - s * ((round (t μ / s) : ℤ) : ℝ) = s * (t μ / s - (round (t μ / s) : ℝ)) := by
      field_simp
    rw [ht', abs_mul, abs_of_pos hs]
    nlinarith
  change TorusMetric.torusSupNorm _ ≤ s / 2
  rw [hsub]
  refine le_trans (csInf_le ⟨0, ?_⟩ ⟨_, rfl, rfl⟩) ?_
  · rintro _ ⟨w, -, rfl⟩
    exact le_trans (abs_nonneg (w 0))
      (Finset.le_sup' (fun μ => |w μ|) (Finset.mem_univ (0 : Fin 4)))
  · exact Finset.sup'_le _ _ fun μ _ => hle μ
theorem mem_spacingLattice_of_mem_sublattice {N : ℕ} (m : PeriodicLattice.Mesh N)
    {x : PeriodicLattice.Torus 4 N}
    (hx : x ∈ PeriodicLattice.gridSubgroup 4 m) : x ∈ spacingLattice (N : ℝ) m.h := by
  have hz : ∀ μ, ∃ k : ℤ, k • ((m.h : ℝ) : AddCircle (N : ℝ)) = x μ := fun μ =>
    AddSubgroup.mem_zmultiples_iff.mp (hx μ (mem_univ μ))
  choose k hk using hz
  refine ⟨k, funext fun μ => ?_⟩
  rw [← hk μ]
  simp only [TorusMetric.torusProj]
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul, mul_comm]
structure CoarseCubeRegion where
  L : ℕ
  blocking : Blocking.DimFourOddBlockingFactorGeThirteen 4 L
  depth : ℕ
  blockCount : ℕ
  blockCount_pow : ∃ k : ℕ, blockCount = L ^ k
  period : ℕ
  period_eq : period = 8 * (blockCount * L)
  scales : PeriodicLattice.Scales 4 L depth period
  sites : Set (PeriodicLattice.GridPoint 4 scales.coarseMesh)
  isUnion : IsUnionOfCubes (gridCubes (period : ℝ) ((blockCount : ℝ) * (L : ℝ)))
    (⋃ y ∈ sites, supCube (S := (period : ℝ)) (L : ℝ) (y : PeriodicLattice.Torus 4 period))
namespace CoarseCubeRegion
variable (W : CoarseCubeRegion)
theorem L_pos : 0 < W.L := W.scales.factor_pos
theorem blockCount_pos : 0 < W.blockCount := by
  obtain ⟨k, hk⟩ := W.blockCount_pow
  rw [hk]
  exact pow_pos W.L_pos k
def scaleData : ScaleData where
  L := W.L
  blocking := W.blocking
  baseSpacing := PeriodicLattice.fineScale W.L W.depth
  baseSpacing_pos := W.scales.fineMesh.h_pos
  lastLevel := W.depth + 1
  blockCount := W.blockCount
  blockCount_pow := W.blockCount_pow
  gapCount := W.L
  gapCount_pow := ⟨1, (pow_one _).symm⟩
  torusSide := (W.period : ℝ)
  torusSide_evenMultiple := by
    have hL : (W.L : ℝ) ≠ 0 := by exact_mod_cast W.L_pos.ne'
    refine ⟨4 * W.blockCount, by have := W.blockCount_pos; omega, ?_⟩
    rw [W.period_eq, PeriodicLattice.fineScale, pow_succ]
    push_cast
    field_simp
    ring
theorem levelSpacing_eq (n : ℕ) :
    W.scaleData.levelSpacing n = (W.L : ℝ) ^ n * PeriodicLattice.fineScale W.L W.depth := rfl
theorem levelSpacing_zero : W.scaleData.levelSpacing 0 = PeriodicLattice.fineScale W.L W.depth := by
  rw [levelSpacing_eq, pow_zero, one_mul]
theorem levelSpacing_depth_succ : W.scaleData.levelSpacing (W.depth + 1) = (W.L : ℝ) := by
  have hL : (W.L : ℝ) ≠ 0 := by exact_mod_cast W.L_pos.ne'
  rw [levelSpacing_eq, PeriodicLattice.fineScale, pow_succ]
  field_simp
def cubeHull : Set W.scaleData.Space :=
  ⋃ y ∈ W.sites, supCube (S := (W.period : ℝ)) (W.L : ℝ) (y : PeriodicLattice.Torus 4 W.period)
open Classical in
def chainSet (n : ℕ) : Set W.scaleData.Space :=
  if n ≤ W.depth then univ else if n = W.depth + 1 then W.cubeHull else ∅
theorem chainSet_of_le {n : ℕ} (h : n ≤ W.depth) : W.chainSet n = univ := by
  simp [chainSet, h]
theorem chainSet_depth_succ : W.chainSet (W.depth + 1) = W.cubeHull := by
  simp [chainSet]
theorem admitsPartition_blockLength {n : ℕ} (h : n ≤ W.depth + 1) :
    W.scaleData.AdmitsPartition (W.scaleData.blockLength n) := by
  have hL : (W.L : ℝ) ≠ 0 := by exact_mod_cast W.L_pos.ne'
  have hLp : (0 : ℝ) < W.L := by exact_mod_cast W.L_pos
  have hM : (0 : ℝ) < W.blockCount := by exact_mod_cast W.blockCount_pos
  refine ⟨?_, 4 * W.L ^ (W.depth + 1 - n), ?_, ?_⟩
  · have hξ : 0 < W.scaleData.levelSpacing n := by
      rw [levelSpacing_eq]
      exact mul_pos (pow_pos hLp n) W.scales.fineMesh.h_pos
    exact mul_pos hM hξ
  · have := pow_pos W.L_pos (W.depth + 1 - n)
    omega
  · obtain ⟨r, hr⟩ : ∃ r, W.depth + 1 = n + r := ⟨W.depth + 1 - n, by omega⟩
    have hr' : W.depth + 1 - n = r := by omega
    have hp : (W.L : ℝ) ^ W.depth * W.L = (W.L : ℝ) ^ n * (W.L : ℝ) ^ r := by
      rw [← pow_succ, hr, pow_add]
    have hj : ((W.L : ℝ) ^ W.depth) ≠ 0 := pow_ne_zero _ hL
    have hM' : (W.blockCount : ℝ) ≠ 0 := hM.ne'
    rw [hr']
    change (W.period : ℝ) = 2 * ((4 * W.L ^ r : ℕ) : ℝ) *
      ((W.blockCount : ℝ) * ((W.L : ℝ) ^ n * ((W.L : ℝ) ^ W.depth)⁻¹))
    rw [W.period_eq]
    push_cast
    field_simp
    linear_combination (8 : ℝ) * hp
def chain : SeparatedChain W.scaleData where
  set := W.chainSet
  mono := by
    intro n hn
    have hn' : n ≤ W.depth := Nat.lt_succ_iff.mp hn
    rw [W.chainSet_of_le hn']
    exact subset_univ _
  cubeUnion := by
    intro n hn _
    by_cases h : n ≤ W.depth
    · rw [W.chainSet_of_le h]
      have : Fact (0 < W.scaleData.torusSide) := ⟨by
        have := W.scales.period_pos
        change (0 : ℝ) < (W.period : ℝ)
        exact_mod_cast this⟩
      refine ⟨ScaleData.blockPartition W.scaleData n, subset_rfl, ?_⟩
      refine (eq_univ_of_forall fun x => ?_).symm
      have hf := W.admitsPartition_blockLength (n := n) (by omega)
      obtain ⟨y, hy, hx⟩ := exists_mem_supCube hf.1 x
      exact ⟨_, ⟨hf, y, hy, rfl⟩, hx⟩
    · have hn' : n = W.depth + 1 := by
        change n ≤ W.depth + 1 at hn
        omega
      subst hn'
      rw [W.chainSet_depth_succ]
      obtain ⟨C, hC, hU⟩ := W.isUnion
      refine ⟨C, fun Q hQ => ?_, hU⟩
      obtain ⟨y, hy, rfl⟩ := hC hQ
      refine ⟨W.admitsPartition_blockLength le_rfl, y, ?_, ?_⟩
      · have hb : W.scaleData.blockLength (W.depth + 1) = (W.blockCount : ℝ) * (W.L : ℝ) := by
          rw [ScaleData.blockLength, W.levelSpacing_depth_succ]
          rfl
        rw [hb]
        exact hy
      · have hb : W.scaleData.blockLength (W.depth + 1) = (W.blockCount : ℝ) * (W.L : ℝ) := by
          rw [ScaleData.blockLength, W.levelSpacing_depth_succ]
          rfl
        rw [hb]
        rfl
  separation := by
    intro n hn
    have hn' : n ≤ W.depth := Nat.lt_succ_iff.mp hn
    rw [W.chainSet_of_le hn']
    have hc : closedComplement (univ : Set W.scaleData.Space) = ∅ := by
      simp [closedComplement]
    have ht : TorusMetric.setSupDist (∅ : Set W.scaleData.Space) (W.chainSet (n + 1)) = ⊤ := by
      simp [TorusMetric.setSupDist]
    rw [hc, ht]
    exact ENNReal.ofReal_lt_top
  eq_empty_of_gt := by
    intro n hn
    have h1 : ¬n ≤ W.depth := by
      change W.depth + 1 < n at hn
      omega
    have h2 : n ≠ W.depth + 1 := by
      change W.depth + 1 < n at hn
      omega
    simp [chainSet, h1, h2]
def gaugeSetting : GaugeSetting where
  data := W.scaleData
  chain := W.chain
  L_le_gapCount := le_rfl
  choice := .meeting
  mass := 1
  mass_pos := one_pos
def baseSite (x : PeriodicLattice.GridPoint 4 W.scales.fineMesh) : W.scaleData.BaseSite :=
  ⟨x.1, by
    have h := mem_spacingLattice_of_mem_sublattice W.scales.fineMesh x.2
    rw [W.levelSpacing_zero]
    exact h⟩
def fieldRestriction :
    W.scaleData.BondField →ₗ[ℝ] PeriodicLattice.OneForm 4 W.scales.fineMesh where
  toFun A := PeriodicLattice.ScaledFun.ofMap fun b =>
    A (ScaleData.bondFrom (W.baseSite b.2) b.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end CoarseCubeRegion
end YangMills.Construction.GeneralTorus
end
