import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.ReflectionPositivity.NestedLatticesAdicPointsAndMirrors
import YangMills.Construction.ReflectionPositivity.UnitNormalReflectionAndLatticeMirrors
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AdicLattices
open YangMills.Construction.InfiniteLattice (AmbientSpace latticeSubgroup)
open YangMills.Construction.Mirrors (ReflectingHyperplane)
open YangMills.Construction.PeriodicLattice (adicGridPoints meshSize mem_adicGridPoints_iff)
open YangMills.Construction.SeparatedTuples (IsAdicPlaced latticeSpacing halfAdicGridPoints
  scaleLattice posAdicGridPoints)
theorem one_lt_base {L : ℕ} (hL : 13 ≤ L) : (1 : ℝ) < (L : ℝ) := by apply _root_.YangMills.SharedProofs.p15248 <;> assumption
theorem meshSize_natCast (L k : ℕ) : meshSize L (k : ℤ) = ((L : ℝ) ^ k)⁻¹ := by
  simp [meshSize, zpow_neg]
theorem meshSize_pos {L : ℕ} (hL : 13 ≤ L) (k : ℕ) : 0 < meshSize L (k : ℤ) := by
  have h1 := one_lt_base hL
  rw [meshSize_natCast]
  exact inv_pos.mpr (pow_pos (by linarith) k)
theorem meshSize_eq_pow_mul {L : ℕ} (hL : 13 ≤ L) {k k' : ℕ} (h : k ≤ k') :
    meshSize L (k : ℤ) = (L : ℝ) ^ (k' - k) * meshSize L (k' : ℤ) := by
  have h1 := one_lt_base hL
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [meshSize_natCast, meshSize_natCast, Nat.add_sub_cancel_left, pow_add]
  field_simp
theorem exists_int_mul_meshSize_of_le {L : ℕ} (hL : 13 ≤ L) {k k' : ℕ} (h : k ≤ k') {x : ℝ}
    (hx : ∃ n : ℤ, x = (n : ℝ) * meshSize L (k : ℤ)) :
    ∃ n : ℤ, x = (n : ℝ) * meshSize L (k' : ℤ) := by
  obtain ⟨n, rfl⟩ := hx
  refine ⟨n * (L : ℤ) ^ (k' - k), ?_⟩
  rw [meshSize_eq_pow_mul hL h]
  push_cast
  ring
theorem exists_int_mul_half_meshSize_of_le {L : ℕ} (hL : 13 ≤ L) {k k' : ℕ} (h : k ≤ k')
    {x : ℝ} (hx : ∃ n : ℤ, x = (n : ℝ) * (meshSize L (k : ℤ) / 2)) :
    ∃ n : ℤ, x = (n : ℝ) * (meshSize L (k' : ℤ) / 2) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := exists_int_mul_meshSize_of_le hL h (x := 2 * x) ⟨n, by rw [hn]; ring⟩
  exact ⟨m, by linarith⟩
theorem mem_latticeSubgroup_iff (a : ℝ) (x : AmbientSpace) :
    x ∈ latticeSubgroup a ↔ ∃ n : Fin 4 → ℤ, ∀ μ, x μ = (n μ : ℝ) * a :=
  Iff.rfl
theorem latticeSubgroup_mono {L : ℕ} (hL : 13 ≤ L) {k k' : ℕ} (h : k ≤ k') :
    latticeSubgroup (meshSize L (k : ℤ)) ≤ latticeSubgroup (meshSize L (k' : ℤ)) := by
  intro x hx
  obtain ⟨n, hn⟩ := (mem_latticeSubgroup_iff _ x).mp hx
  have hex : ∀ μ, ∃ m : ℤ, x μ = (m : ℝ) * meshSize L (k' : ℤ) :=
    fun μ => exists_int_mul_meshSize_of_le hL h ⟨n μ, hn μ⟩
  choose m hm using hex
  exact (mem_latticeSubgroup_iff _ x).mpr ⟨m, hm⟩
theorem le_coe_of_strictMono {K : ℕ+ → ℕ+} (hK : StrictMono K) (j : ℕ+) :
    (j : ℕ) ≤ (K j : ℕ) := by
  induction j using PNat.recOn with
  | one => exact (K 1).pos
  | succ j ih =>
    have hlt : (K j : ℕ) < (K (j + 1) : ℕ) := hK (PNat.lt_add_right j 1)
    rw [PNat.add_coe, PNat.one_coe]
    omega
theorem exists_forall_le_coe {K : ℕ+ → ℕ+} (hK : StrictMono K) (k : ℕ) :
    ∃ j₀ : ℕ+, ∀ j, j₀ ≤ j → k ≤ (K j : ℕ) := by
  refine ⟨Nat.succPNat k, fun j hj => ?_⟩
  have h1 : (Nat.succPNat k : ℕ) ≤ (j : ℕ) := hj
  have h2 := le_coe_of_strictMono hK j
  rw [Nat.succPNat_coe] at h1
  omega
theorem tendsto_meshSize {L : ℕ} (hL : 13 ≤ L) :
    Tendsto (fun k : ℕ => meshSize L (k : ℤ)) atTop (𝓝 0) := by
  have h1 := one_lt_base hL
  have h2 : Tendsto (fun k : ℕ => ((L : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (by linarith)) (inv_lt_one_of_one_lt₀ h1)
  refine h2.congr fun k => ?_
  rw [meshSize_natCast, inv_pow]
def floorApprox (L : ℕ) (x : ℝ) (k : ℕ) : ℝ := (⌊(L : ℝ) ^ k * x⌋ : ℝ) * meshSize L (k : ℤ)
theorem floorApprox_mem (L : ℕ) (x : ℝ) (k : ℕ) : floorApprox L x k ∈ adicGridPoints L :=
  (mem_adicGridPoints_iff L _).mpr ⟨k, ⌊(L : ℝ) ^ k * x⌋, rfl⟩
theorem pow_mul_mul_meshSize {L : ℕ} (hL : 13 ≤ L) (x : ℝ) (k : ℕ) :
    (L : ℝ) ^ k * x * meshSize L (k : ℤ) = x := by
  have h1 := one_lt_base hL
  have hp : (L : ℝ) ^ k ≠ 0 := (pow_pos (by linarith) k).ne'
  rw [meshSize_natCast]
  field_simp
theorem floorApprox_le {L : ℕ} (hL : 13 ≤ L) (x : ℝ) (k : ℕ) : floorApprox L x k ≤ x := by
  have h := mul_le_mul_of_nonneg_right (Int.floor_le ((L : ℝ) ^ k * x)) (meshSize_pos hL k).le
  rw [pow_mul_mul_meshSize hL] at h
  exact h
theorem sub_meshSize_lt_floorApprox {L : ℕ} (hL : 13 ≤ L) (x : ℝ) (k : ℕ) :
    x - meshSize L (k : ℤ) < floorApprox L x k := by
  have h := mul_lt_mul_of_pos_right (Int.lt_floor_add_one ((L : ℝ) ^ k * x)) (meshSize_pos hL k)
  rw [pow_mul_mul_meshSize hL, add_mul, one_mul] at h
  unfold floorApprox
  linarith
theorem tendsto_floorApprox {L : ℕ} (hL : 13 ≤ L) (x : ℝ) :
    Tendsto (floorApprox L x) atTop (𝓝 x) := by
  have hlow : Tendsto (fun k : ℕ => x - meshSize L (k : ℤ)) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.sub (tendsto_meshSize hL)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun k => (sub_meshSize_lt_floorApprox hL x k).le) (fun k => floorApprox_le hL x k)
theorem add_mem_adicGridPoints {L : ℕ} (hL : 13 ≤ L) {x y : ℝ} (hx : x ∈ adicGridPoints L)
    (hy : y ∈ adicGridPoints L) : x + y ∈ adicGridPoints L := by
  obtain ⟨k, n, hn⟩ := (mem_adicGridPoints_iff L x).mp hx
  obtain ⟨k', n', hn'⟩ := (mem_adicGridPoints_iff L y).mp hy
  obtain ⟨m, hm⟩ := exists_int_mul_meshSize_of_le hL (le_max_left k k') ⟨n, hn⟩
  obtain ⟨m', hm'⟩ := exists_int_mul_meshSize_of_le hL (le_max_right k k') ⟨n', hn'⟩
  refine (mem_adicGridPoints_iff L _).mpr ⟨max k k', m + m', ?_⟩
  rw [hm, hm']
  push_cast
  ring
theorem neg_mem_adicGridPoints {L : ℕ} {x : ℝ} (hx : x ∈ adicGridPoints L) :
    -x ∈ adicGridPoints L := by
  obtain ⟨k, n, hn⟩ := (mem_adicGridPoints_iff L x).mp hx
  refine (mem_adicGridPoints_iff L _).mpr ⟨k, -n, ?_⟩
  rw [hn]
  push_cast
  ring
theorem zero_mem_adicGridPoints (L : ℕ) : (0 : ℝ) ∈ adicGridPoints L :=
  (mem_adicGridPoints_iff L _).mpr ⟨0, 0, by simp⟩
theorem mem_halfAdicGridPoints_of_mem {L : ℕ} (hL : 13 ≤ L) {x : ℝ} (hx : x ∈ adicGridPoints L) :
    x ∈ halfAdicGridPoints L :=
  ⟨x + x, add_mem_adicGridPoints hL hx hx, by ring⟩
theorem exists_pos_nat_div_eq {t a : ℝ} (ht : 0 < t) (ha : 0 < a) {n : ℤ}
    (hn : t = (n : ℝ) * a) : ∃ m : ℕ, 0 < m ∧ t / a = (m : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    by_contra h
    have h' : (n : ℝ) ≤ 0 := not_lt.mp h
    have := mul_nonpos_of_nonpos_of_nonneg h' ha.le
    linarith
  have hnpos' : 0 < n := by exact_mod_cast hnpos
  refine ⟨n.toNat, by omega, ?_⟩
  have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    have h1 : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hnpos'.le
    exact_mod_cast h1
  rw [hcast, hn]
  field_simp
section Hyperplanes
variable (hF : YangMills.Construction.Mirrors.UnitNormalAndLattice.Statement)
include hF
theorem isLatticeSymmetric_iff_of_axial {L : ℕ} (hL : 13 ≤ L) (M : ReflectingHyperplane) (k : ℕ)
    (μ : Fin 4) (hμ : M.normalVec = YangMills.Construction.PeriodicLattice.coordVec μ) :
    M.IsLatticeSymmetric (meshSize L (k : ℤ)) ↔
      ∃ q : ℤ, M.offset = (q : ℝ) * (meshSize L (k : ℤ) / 2) := by
  have ha := meshSize_pos hL k
  obtain ⟨-, hB, -⟩ := hF M (meshSize L (k : ℤ)) ha
  exact ⟨fun h => (hB μ hμ).mp h.2, fun h => ⟨ha, (hB μ hμ).mpr h⟩⟩
theorem isLatticeSymmetric_iff_of_diagonal {L : ℕ} (hL : 13 ≤ L) (M : ReflectingHyperplane)
    (k : ℕ) (μ ν : Fin 4) (hlt : μ < ν)
    (hn : M.normalVec = YangMills.Construction.PeriodicLattice.coordVec μ +
        YangMills.Construction.PeriodicLattice.coordVec ν ∨
      M.normalVec = YangMills.Construction.PeriodicLattice.coordVec μ -
        YangMills.Construction.PeriodicLattice.coordVec ν) :
    M.IsLatticeSymmetric (meshSize L (k : ℤ)) ↔
      ∃ q : ℤ, M.offset = (q : ℝ) * meshSize L (k : ℤ) := by
  have ha := meshSize_pos hL k
  obtain ⟨-, -, hC, -⟩ := hF M (meshSize L (k : ℤ)) ha
  have hC' := (hC μ ν hlt hn).1
  exact ⟨fun h => hC'.mp h.2, fun h => ⟨ha, hC'.mpr h⟩⟩
theorem isLatticeSymmetric_mono {L : ℕ} (hL : 13 ≤ L) (M : ReflectingHyperplane) {k k' : ℕ}
    (h : k ≤ k') (hM : M.IsLatticeSymmetric (meshSize L (k : ℤ))) :
    M.IsLatticeSymmetric (meshSize L (k' : ℤ)) := by
  rcases M.normalVec_mem with ⟨μ, hμ⟩ | ⟨μ, ν, hlt, hn⟩
  · exact (isLatticeSymmetric_iff_of_axial hF hL M k' μ hμ).mpr
      (exists_int_mul_half_meshSize_of_le hL h
        ((isLatticeSymmetric_iff_of_axial hF hL M k μ hμ).mp hM))
  · exact (isLatticeSymmetric_iff_of_diagonal hF hL M k' μ ν hlt hn).mpr
      (exists_int_mul_meshSize_of_le hL h
        ((isLatticeSymmetric_iff_of_diagonal hF hL M k μ ν hlt hn).mp hM))
theorem isAdicPlaced_iff_exists {L : ℕ} (hL : 13 ≤ L) (M : ReflectingHyperplane) :
    IsAdicPlaced L M ↔ ∃ k : ℕ, M.IsLatticeSymmetric (meshSize L (k : ℤ)) := by
  constructor
  · rintro (⟨⟨d, hd, hc⟩, μ, hμ⟩ | ⟨hc, μ, ν, hlt, hn⟩)
    · obtain ⟨k, n, hn⟩ := (mem_adicGridPoints_iff L d).mp hd
      refine ⟨k, (isLatticeSymmetric_iff_of_axial hF hL M k μ hμ).mpr ⟨n, ?_⟩⟩
      rw [hc, hn]
      ring
    · obtain ⟨k, q, hq⟩ := (mem_adicGridPoints_iff L _).mp hc
      exact ⟨k, (isLatticeSymmetric_iff_of_diagonal hF hL M k μ ν hlt hn).mpr ⟨q, hq⟩⟩
  · rintro ⟨k, hk⟩
    rcases hnorm : M.normalVec_mem with ⟨μ, hμ⟩ | ⟨μ, ν, hlt, hn⟩
    · obtain ⟨q, hq⟩ := (isLatticeSymmetric_iff_of_axial hF hL M k μ hμ).mp hk
      refine Or.inl ⟨⟨(q : ℝ) * meshSize L (k : ℤ),
        (mem_adicGridPoints_iff L _).mpr ⟨k, q, rfl⟩, ?_⟩, μ, hμ⟩
      rw [hq]
      ring
    · obtain ⟨q, hq⟩ := (isLatticeSymmetric_iff_of_diagonal hF hL M k μ ν hlt hn).mp hk
      exact Or.inr ⟨(mem_adicGridPoints_iff L _).mpr ⟨k, q, hq⟩, μ, ν, hlt, hn⟩
end Hyperplanes
theorem nestedScales_holds {L : ℕ} (hL : 13 ≤ L) {K : ℕ+ → ℕ+} (hK : StrictMono K) :
    NestedScales L K := by
  intro j
  have hlt : (K j : ℕ) < (K (j + 1) : ℕ) := hK (PNat.lt_add_right j 1)
  refine ⟨?_, by omega, latticeSubgroup_mono hL hlt.le⟩
  have hpos := meshSize_pos hL (K (j + 1) : ℕ)
  rw [latticeSpacing, meshSize_eq_pow_mul hL hlt.le]
  exact mul_div_cancel_right₀ _ hpos.ne'
theorem multiplesUnionAgree_holds {L : ℕ} (hL : 13 ≤ L) {K : ℕ+ → ℕ+} (hK : StrictMono K) :
    MultiplesUnionAgree L K := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨j₀, hj₀⟩ := exists_forall_le_coe hK k
    exact ⟨j₀, exists_int_mul_meshSize_of_le hL (hj₀ j₀ le_rfl) hk⟩
  · rintro ⟨j, hj⟩
    exact ⟨(K j : ℕ), hj⟩
theorem adicDenseSubgroup_holds {L : ℕ} (hL : 13 ≤ L) : AdicDenseSubgroup L := by
  refine ⟨⟨{ carrier := adicGridPoints L
             add_mem' := fun ha hb => add_mem_adicGridPoints hL ha hb
             zero_mem' := zero_mem_adicGridPoints L
             neg_mem' := fun h => neg_mem_adicGridPoints h }, rfl⟩, ?_, ?_, ?_⟩
  · intro x
    exact mem_closure_of_tendsto (tendsto_floorApprox hL x)
      (Eventually.of_forall fun k => floorApprox_mem L x k)
  · intro x hx
    have hx' : (0 : ℝ) < x := hx
    have hev : ∀ᶠ k in atTop, 0 < floorApprox L x k :=
      (tendsto_floorApprox hL x).eventually (lt_mem_nhds hx')
    exact mem_closure_of_tendsto (tendsto_floorApprox hL x)
      (hev.mono fun k hk => ⟨floorApprox_mem L x k, hk⟩)
  · rw [accPt_iff_frequently]
    refine (tendsto_meshSize hL).frequently (Frequently.of_forall fun k => ?_)
    exact ⟨(meshSize_pos hL k).ne', (mem_adicGridPoints_iff L _).mpr ⟨k, 1, by simp⟩,
      meshSize_pos hL k⟩
theorem adicPointsEventuallyOnLattice_holds {L : ℕ} (hL : 13 ≤ L) {K : ℕ+ → ℕ+}
    (hK : StrictMono K) : AdicPointsEventuallyOnLattice L K := by
  intro x hx
  have hex : ∀ μ, ∃ k : ℕ, ∃ n : ℤ, x μ = (n : ℝ) * meshSize L (k : ℤ) :=
    fun μ => (mem_adicGridPoints_iff L _).mp (hx μ)
  choose k hk using hex
  obtain ⟨j₀, hj₀⟩ := exists_forall_le_coe hK (Finset.univ.sup k)
  refine ⟨j₀, fun j hj => ?_⟩
  have hex' : ∀ μ, ∃ m : ℤ, x μ = (m : ℝ) * meshSize L ((K j : ℕ) : ℤ) := fun μ =>
    exists_int_mul_meshSize_of_le hL ((Finset.le_sup (Finset.mem_univ μ)).trans (hj₀ j hj)) (hk μ)
  choose m hm using hex'
  exact (mem_latticeSubgroup_iff _ x).mpr ⟨m, hm⟩
theorem adicTimesEventuallyMultiples_holds {L : ℕ} (hL : 13 ≤ L) {K : ℕ+ → ℕ+}
    (hK : StrictMono K) : AdicTimesEventuallyMultiples L K := by
  rintro t ⟨ht, htpos⟩
  obtain ⟨k, hk⟩ := (mem_adicGridPoints_iff L t).mp ht
  obtain ⟨j₀, hj₀⟩ := exists_forall_le_coe hK k
  refine ⟨j₀, fun j hj => ?_⟩
  obtain ⟨n, hn⟩ := exists_int_mul_meshSize_of_le hL (hj₀ j hj) hk
  exact exists_pos_nat_div_eq htpos (meshSize_pos hL (K j : ℕ)) hn
theorem adicHyperplanesLatticeSymmetric_holds
    (hF : YangMills.Construction.Mirrors.UnitNormalAndLattice.Statement)
    {L : ℕ} (hL : 13 ≤ L) {K : ℕ+ → ℕ+} (hK : StrictMono K) :
    AdicHyperplanesLatticeSymmetric L K := by
  intro M
  have hiff := isAdicPlaced_iff_exists hF hL M
  refine ⟨⟨fun h => ?_, fun ⟨k₀, h⟩ => hiff.mpr ⟨k₀, h k₀ le_rfl⟩⟩, hiff, fun h => ?_⟩
  · obtain ⟨k, hk⟩ := hiff.mp h
    exact ⟨k, fun k' hk' => isLatticeSymmetric_mono hF hL M hk' hk⟩
  · obtain ⟨k, hk⟩ := hiff.mp h
    obtain ⟨j₀, hj₀⟩ := exists_forall_le_coe hK k
    exact ⟨j₀, fun j hj => isLatticeSymmetric_mono hF hL M (hj₀ j hj) hk⟩
theorem tendsto_pnat_coe_atTop : Tendsto (fun r : ℕ+ => (r : ℕ)) atTop atTop :=
  tendsto_atTop.mpr fun n =>
    (eventually_ge_atTop (Nat.succPNat n)).mono fun r hr => by
      have h1 : (Nat.succPNat n : ℕ) ≤ (r : ℕ) := hr
      rw [Nat.succPNat_coe] at h1
      omega
theorem isAdicPlaced_of_offset_mem {L : ℕ} (hL : 13 ≤ L) (M : ReflectingHyperplane)
    (hc : M.offset ∈ adicGridPoints L) : IsAdicPlaced L M := by
  rcases M.normalVec_mem with hn | hn
  · exact Or.inl ⟨mem_halfAdicGridPoints_of_mem hL hc, hn⟩
  · exact Or.inr ⟨hc, hn⟩
theorem adicApproxFromBelow_holds {L : ℕ} (hL : 13 ≤ L) : AdicApproxFromBelow L := by
  intro c
  refine ⟨fun r => floorApprox L c r, fun r => ⟨floorApprox_mem L c r, floorApprox_le hL c r⟩,
    (tendsto_floorApprox hL c).comp tendsto_pnat_coe_atTop, fun n hn r => ?_⟩
  exact isAdicPlaced_of_offset_mem hL ⟨n, hn, _⟩ (floorApprox_mem L c r)
theorem hyperplanesApproxFromBelow_holds {L : ℕ} (hL : 13 ≤ L) : HyperplanesApproxFromBelow L := by
  intro M
  refine ⟨fun r => ⟨M.normalVec, M.normalVec_mem, floorApprox L M.offset r⟩,
    fun r => ⟨rfl, ?_, ?_⟩, ?_⟩
  · exact isAdicPlaced_of_offset_mem hL _ (floorApprox_mem L M.offset r)
  · exact floorApprox_le hL M.offset r
  · exact (tendsto_floorApprox hL M.offset).comp tendsto_pnat_coe_atTop
theorem assertion_holds (hF : YangMills.Construction.Mirrors.UnitNormalAndLattice.Statement) :
    Assertion :=
  fun _ hL _ hK =>
    ⟨nestedScales_holds hL hK, multiplesUnionAgree_holds hL hK, adicDenseSubgroup_holds hL,
      adicPointsEventuallyOnLattice_holds hL hK, adicTimesEventuallyMultiples_holds hL hK,
      adicHyperplanesLatticeSymmetric_holds hF hL hK, adicApproxFromBelow_holds hL,
      hyperplanesApproxFromBelow_holds hL⟩
end YangMills.Construction.ReflectionPositivity.AdicLattices
