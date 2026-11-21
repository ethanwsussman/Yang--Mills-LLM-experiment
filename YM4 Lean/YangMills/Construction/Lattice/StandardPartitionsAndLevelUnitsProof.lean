import YangMills.Construction.Lattice.StandardPartitionCubeGeometryArgument
import YangMills.Construction.Lattice.StandardPartitionsAndLevelUnits
import YangMills.Construction.Torus.BoundsOnTheWeightedDistanceProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace PartitionFacts
variable {L m : ℕ} {i i' : ℤ}
def cubeAbout (a : ℝ) (y : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  pi univ fun ν => Icc (y ν - 1 / 2 * a) (y ν + 1 / 2 * a)
def OnGrid (a : ℝ) (y : Fin 4 → ℝ) : Prop := ∀ ν, ∃ n : ℤ, y ν = a * (n : ℝ)
theorem mem_cubeAbout {a : ℝ} {y w : Fin 4 → ℝ} :
    w ∈ cubeAbout a y ↔ ∀ ν, |w ν - y ν| ≤ a / 2 := by
  simp only [cubeAbout, mem_pi, mem_univ, forall_true_left, mem_Icc, abs_le]
  refine forall_congr' fun ν => ?_
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
theorem meshSize_pos (hL : 0 < L) (i : ℤ) : 0 < meshSize L i := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : _root_.YangMills.Construction.TorusMetric.torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem torusProj_add {S : ℝ} (u v : Fin 4 → ℝ) :
    torusProj S (u + v) = torusProj S u + torusProj S v := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
theorem torusProj_sub {S : ℝ} (u v : Fin 4 → ℝ) :
    torusProj S (u - v) = torusProj S u - torusProj S v := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem torusProj_surjective (S : ℝ) (x : Torus4 S) : ∃ w, torusProj S w = x := by apply _root_.YangMills.Construction.Weighted.DistBounds.torusProj_surjective <;> assumption
theorem exists_int_eq_add_mul_of_coe_eq {S a b : ℝ} (h : (a : AddCircle S) = b) :
    ∃ k : ℤ, a = b + k * S := by apply _root_.YangMills.Construction.PeriodicLattice.StandardCubes.exists_int_eq_add_mul_of_coe_eq <;> assumption
theorem coe_add_int_mul (S v : ℝ) (k : ℤ) : ((v + k * S : ℝ) : AddCircle S) = v := by apply _root_.YangMills.Construction.PeriodicLattice.StandardCubes.coe_add_int_mul_period <;> assumption
theorem exists_int_shift_of_torusProj_eq {S : ℝ} {w w' : Fin 4 → ℝ}
    (h : torusProj S w = torusProj S w') :
    ∃ q : Fin 4 → ℤ, ∀ ν, w ν = w' ν + q ν * S := by
  choose q hq using fun ν => exists_int_eq_add_mul_of_coe_eq (congrFun h ν)
  exact ⟨q, hq⟩
theorem torusProj_add_int_mul (S : ℝ) (y : Fin 4 → ℝ) (q : Fin 4 → ℤ) :
    torusProj S (fun ν => y ν + q ν * S) = torusProj S y := by
  funext ν
  exact coe_add_int_mul S (y ν) (q ν)
theorem torusSide_eq_meshSize_mul (hL : 0 < L) (hi : -(m : ℤ) ≤ i) :
    ∃ N : ℤ, torusSide L m = meshSize L i * (N : ℝ) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hd : (((m : ℤ) + i).toNat : ℤ) = m + i := Int.toNat_of_nonneg (by omega)
  refine ⟨2 * (L : ℤ) ^ ((m : ℤ) + i).toNat, ?_⟩
  unfold torusSide meshSize
  push_cast
  rw [mul_left_comm]
  congr 1
  rw [← zpow_natCast (L : ℝ) ((m : ℤ) + i).toNat, ← zpow_add₀ hL', ← zpow_natCast (L : ℝ) m]
  congr 1
  omega
theorem meshSize_eq_odd_mul (hL : Odd L) (h : i ≤ i') :
    ∃ M : ℕ, meshSize L i = (2 * (M : ℝ) + 1) * meshSize L i' := by
  have hL0 : 0 < L := hL.pos
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL0.ne'
  obtain ⟨M, hM⟩ := hL.pow (n := (i' - i).toNat)
  have hd : (((i' - i).toNat : ℕ) : ℤ) = i' - i := Int.toNat_of_nonneg (by omega)
  refine ⟨M, ?_⟩
  have hM' : (2 * (M : ℝ) + 1) = (L : ℝ) ^ (i' - i) := by
    rw [← hd, zpow_natCast]
    exact_mod_cast hM.symm
  rw [hM']
  unfold meshSize
  rw [← zpow_add₀ hL']
  congr 1
  omega
theorem onGrid_add_int_mul {a S : ℝ} {y : Fin 4 → ℝ} (hy : OnGrid a y) {N : ℤ}
    (hS : S = a * (N : ℝ)) (q : Fin 4 → ℤ) : OnGrid a fun ν => y ν + q ν * S := by
  intro ν
  obtain ⟨n, hn⟩ := hy ν
  refine ⟨n + q ν * N, ?_⟩
  simp only [hn, hS]
  push_cast
  ring
theorem torusProj_mem_sublattice {y : Fin 4 → ℝ} (hy : OnGrid (meshSize L i) y) :
    torusProj (torusSide L m) y ∈ sublattice L m i := by
  choose n hn using hy
  exact ⟨n, fun μ => by simp only [torusProj, hn μ, mul_comm]⟩
theorem cubeAround_eq_image (hL : 0 < L) (z : Site L m i) {y : Fin 4 → ℝ}
    (hz : (z : FourTorus L m) = torusProj (torusSide L m) y) :
    cubeAround z = torusProj (torusSide L m) '' cubeAbout (meshSize L i) y := by
  have ha := meshSize_pos hL i
  ext x
  constructor
  · intro hx
    have hx' : ‖x - torusProj (torusSide L m) y‖ ≤ meshSize L i / 2 := by
      have : _root_.YangMills.Construction.TorusMetric.torusSupNorm (x - (z : FourTorus L m)) ≤ meshSize L i / 2 := hx
      rwa [_root_.YangMills.Construction.PeriodicLattice.PartitionFacts.torusSupNorm_eq_norm, hz] at this
    choose v hv hv' using fun μ => exists_coe_eq_abs_eq_norm ((x - torusProj (torusSide L m) y) μ)
    have hproj : torusProj (torusSide L m) v = x - torusProj (torusSide L m) y := funext hv
    refine ⟨y + v, mem_cubeAbout.2 fun ν => ?_, ?_⟩
    · simp only [Pi.add_apply, add_sub_cancel_left]
      rw [hv' ν]
      exact (norm_le_pi_norm _ ν).trans hx'
    · rw [torusProj_add, hproj]
      abel
  · rintro ⟨w, hw, rfl⟩
    have hw' := mem_cubeAbout.1 hw
    change _root_.YangMills.Construction.TorusMetric.torusSupNorm (torusProj (torusSide L m) w - (z : FourTorus L m)) ≤ meshSize L i / 2
    rw [_root_.YangMills.Construction.PeriodicLattice.PartitionFacts.torusSupNorm_eq_norm, hz, ← torusProj_sub]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun μ => ?_
    exact (addCircle_norm_coe_le_abs _).trans (hw' μ)
theorem exists_onGrid_lift (z : Site L m i) :
    ∃ y, OnGrid (meshSize L i) y ∧ (z : FourTorus L m) = torusProj (torusSide L m) y := by
  obtain ⟨n, hn⟩ := z.2
  refine ⟨fun μ => meshSize L i * (n μ : ℝ), fun μ => ⟨n μ, rfl⟩, ?_⟩
  funext μ
  simp only [torusProj, hn μ, mul_comm]
theorem mem_standardCubePartition_iff (hL : 0 < L) {Q : Set (FourTorus L m)} :
    Q ∈ standardCubePartition L m i ↔
      ∃ y, OnGrid (meshSize L i) y ∧
        Q = torusProj (torusSide L m) '' cubeAbout (meshSize L i) y := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨y, hy, hz⟩ := exists_onGrid_lift z
    exact ⟨y, hy, cubeAround_eq_image hL z hz⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨_, torusProj_mem_sublattice hy⟩, cubeAround_eq_image hL _ rfl⟩
theorem image_cubeAbout_eq_of_torusProj_eq {S a : ℝ} {y y' : Fin 4 → ℝ}
    (h : torusProj S y = torusProj S y') :
    torusProj S '' cubeAbout a y = torusProj S '' cubeAbout a y' := by
  obtain ⟨q, hq⟩ := exists_int_shift_of_torusProj_eq h
  have key : ∀ {y y' : Fin 4 → ℝ} {q : Fin 4 → ℤ}, (∀ ν, y ν = y' ν + q ν * S) →
      torusProj S '' cubeAbout a y ⊆ torusProj S '' cubeAbout a y' := by
    rintro y y' q hq _ ⟨w, hw, rfl⟩
    refine ⟨fun ν => w ν + ((-q ν : ℤ) : ℝ) * S, mem_cubeAbout.2 fun ν => ?_,
      torusProj_add_int_mul _ _ _⟩
    have := mem_cubeAbout.1 hw ν
    rw [hq ν] at this
    have e : w ν + ((-q ν : ℤ) : ℝ) * S - y' ν = w ν - (y' ν + q ν * S) := by
      push_cast
      ring
    rwa [e]
  refine Subset.antisymm (key hq) (key (q := -q) fun ν => ?_)
  rw [hq ν]
  simp
theorem exists_onGrid_mem_cubeAbout {a : ℝ} (ha : 0 < a) (w : Fin 4 → ℝ) :
    ∃ y, OnGrid a y ∧ w ∈ cubeAbout a y := by
  refine ⟨fun ν => a * (round (w ν / a) : ℝ), fun ν => ⟨_, rfl⟩, mem_cubeAbout.2 fun ν => ?_⟩
  have h := abs_sub_round (w ν / a)
  have e : w ν - a * (round (w ν / a) : ℝ) = a * (w ν / a - (round (w ν / a) : ℝ)) := by
    field_simp
  rw [e, abs_mul, abs_of_pos ha]
  nlinarith
theorem exists_int_near_in_window {a b : ℤ} (hab : a ≤ b) {W t : ℝ} (hW : 0 < W)
    (h1 : (a : ℝ) * W - W / 2 ≤ t) (h2 : t ≤ (b : ℝ) * W + W / 2) :
    ∃ p : ℤ, a ≤ p ∧ p ≤ b ∧ |t - (p : ℝ) * W| ≤ W / 2 := by apply _root_.YangMills.Construction.PeriodicLattice.StandardCubes.exists_int_mul_near <;> assumption
theorem exists_finer_cubeAbout {a a' : ℝ} {M : ℕ} (ha' : 0 < a')
    (ha : a = (2 * (M : ℝ) + 1) * a') {y w : Fin 4 → ℝ} (hy : OnGrid a y)
    (hw : w ∈ cubeAbout a y) :
    ∃ w', OnGrid a' w' ∧ w ∈ cubeAbout a' w' ∧ ∀ ν, |w' ν - y ν| + a' / 2 ≤ a / 2 := by
  have key : ∀ ν, ∃ c : ℝ, (∃ k : ℤ, c = a' * (k : ℝ)) ∧ |w ν - c| ≤ a' / 2 ∧
      |c - y ν| + a' / 2 ≤ a / 2 := by
    intro ν
    have hb := abs_le.1 (mem_cubeAbout.1 hw ν)
    obtain ⟨j, hj1, hj2, hj⟩ := exists_int_near_in_window (a := -(M : ℤ)) (b := (M : ℤ))
      (t := w ν - y ν) (by omega) ha' (by push_cast; nlinarith [hb.1])
      (by push_cast; nlinarith [hb.2])
    obtain ⟨n, hn⟩ := hy ν
    refine ⟨y ν + (j : ℝ) * a', ⟨(2 * (M : ℤ) + 1) * n + j, ?_⟩, ?_, ?_⟩
    · rw [hn, ha]
      push_cast
      ring
    · have e : w ν - (y ν + (j : ℝ) * a') = w ν - y ν - (j : ℝ) * a' := by ring
      rwa [e]
    · have e : y ν + (j : ℝ) * a' - y ν = (j : ℝ) * a' := by ring
      rw [e, abs_mul, abs_of_pos ha']
      have hj' : |(j : ℝ)| ≤ (M : ℝ) := by
        rw [abs_le]
        constructor
        · have : ((-(M : ℤ) : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
          simpa using this
        · exact_mod_cast hj2
      rw [ha]
      nlinarith
  choose c hc h1 h2 using key
  exact ⟨c, hc, mem_cubeAbout.2 h1, h2⟩
theorem exists_coarser_cubeAbout {a a' : ℝ} {M : ℕ} (ha' : 0 < a')
    (ha : a = (2 * (M : ℝ) + 1) * a') {z : Fin 4 → ℝ} (hz : OnGrid a' z) :
    ∃ y, OnGrid a y ∧ ∀ ν, |z ν - y ν| + a' / 2 ≤ a / 2 := by
  have key : ∀ ν, ∃ c : ℝ, (∃ n : ℤ, c = a * (n : ℝ)) ∧ |z ν - c| + a' / 2 ≤ a / 2 := by
    intro ν
    obtain ⟨k, hk⟩ := hz ν
    set N : ℤ := 2 * (M : ℤ) + 1 with hN
    have hNpos : 0 < N := by omega
    have hdiv := Int.emod_add_mul_ediv (k + M) N
    have hr0 := Int.emod_nonneg (k + M) hNpos.ne'
    have hr1 := Int.emod_lt_of_pos (k + M) hNpos
    set r := (k + M) % N
    set n := (k + M) / N
    have hj : k - N * n = r - M := by omega
    refine ⟨a * (n : ℝ), ⟨n, rfl⟩, ?_⟩
    have e : z ν - a * (n : ℝ) = ((r - M : ℤ) : ℝ) * a' := by
      rw [← hj, hk, ha, hN]
      push_cast
      ring
    rw [e, abs_mul, abs_of_pos ha']
    have hj' : |((r - M : ℤ) : ℝ)| ≤ (M : ℝ) := by
      have : |r - (M : ℤ)| ≤ (M : ℤ) := by
        rw [abs_le]
        constructor <;> omega
      exact_mod_cast this
    rw [ha]
    nlinarith
  choose c hc h using key
  exact ⟨c, hc, h⟩
theorem cubeAbout_subset {a a' : ℝ} {y z : Fin 4 → ℝ}
    (h : ∀ ν, |z ν - y ν| + a' / 2 ≤ a / 2) : cubeAbout a' z ⊆ cubeAbout a y := by
  intro w hw
  refine mem_cubeAbout.2 fun ν => ?_
  have h1 := mem_cubeAbout.1 hw ν
  have h2 := abs_sub_le (w ν) (z ν) (y ν)
  linarith [h ν]
theorem self_mem_cubeAbout {a : ℝ} (ha : 0 < a) (y : Fin 4 → ℝ) : y ∈ cubeAbout a y :=
  mem_cubeAbout.2 fun ν => by simp; positivity
theorem eq_of_onGrid_of_abs_sub_lt {a : ℝ} (ha : 0 < a) {y y' : Fin 4 → ℝ} (hy : OnGrid a y)
    (hy' : OnGrid a y') (h : ∀ ν, |y ν - y' ν| < a) : y = y' := by
  funext ν
  obtain ⟨n, hn⟩ := hy ν
  obtain ⟨n', hn'⟩ := hy' ν
  have h1 := h ν
  rw [hn, hn', ← mul_sub, abs_mul, abs_of_pos ha] at h1
  have h2 : |(n : ℝ) - (n' : ℝ)| < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have h3 : |n - n'| < 1 := by exact_mod_cast h2
  have h4 : n = n' := by
    have := Int.abs_lt_one_iff.1 h3
    omega
  rw [hn, hn', h4]
theorem torusProj_eq_of_centre_mem {S a a' : ℝ} {N : ℤ} (ha' : 0 < a') (ha : 0 < a)
    (hS : S = a * (N : ℝ)) {y y' z : Fin 4 → ℝ} (hy : OnGrid a y) (hy' : OnGrid a y')
    (hz : ∀ ν, |z ν - y ν| + a' / 2 ≤ a / 2)
    (hm : torusProj S z ∈ torusProj S '' cubeAbout a y') :
    torusProj S y' = torusProj S y := by
  obtain ⟨w, hw, hwz⟩ := hm
  obtain ⟨q, hq⟩ := exists_int_shift_of_torusProj_eq hwz
  have hy'' : OnGrid a fun ν => y' ν + ((-q ν : ℤ) : ℝ) * S :=
    onGrid_add_int_mul hy' hS (fun ν => -q ν)
  have hc : y = fun ν => y' ν + ((-q ν : ℤ) : ℝ) * S := by
    refine eq_of_onGrid_of_abs_sub_lt ha hy hy'' fun ν => ?_
    have h1 := mem_cubeAbout.1 hw ν
    have e : w ν - y' ν = z ν - (y' ν + ((-q ν : ℤ) : ℝ) * S) := by
      rw [hq ν]
      push_cast
      ring
    rw [e] at h1
    have h2 := abs_sub_le (y ν) (z ν) (y' ν + ((-q ν : ℤ) : ℝ) * S)
    have h3 := hz ν
    rw [abs_sub_comm (y ν) (z ν)] at h2
    linarith
  rw [hc]
  exact (torusProj_add_int_mul S y' fun ν => -q ν).symm
theorem exists_finer_partition_cube (hL : Odd L) (h : i ≤ i') {Q : Set (FourTorus L m)}
    (hQ : Q ∈ standardCubePartition L m i) {x : FourTorus L m} (hx : x ∈ Q) :
    ∃ Q' ∈ standardCubePartition L m i', x ∈ Q' ∧ Q' ⊆ Q := by
  have hL0 := hL.pos
  obtain ⟨y, hy, rfl⟩ := (mem_standardCubePartition_iff hL0).1 hQ
  obtain ⟨M, hM⟩ := meshSize_eq_odd_mul hL h
  obtain ⟨w, hw, rfl⟩ := hx
  obtain ⟨w', hw', h1, h2⟩ := exists_finer_cubeAbout (meshSize_pos hL0 i') hM hy hw
  exact ⟨_, (mem_standardCubePartition_iff hL0).2 ⟨w', hw', rfl⟩, ⟨w, h1, rfl⟩,
    image_mono (cubeAbout_subset h2)⟩
theorem isPartitionRegion_of_le (hL : Odd L) (h : i ≤ i') {X : Set (FourTorus L m)}
    (hX : IsPartitionRegion i X) : IsPartitionRegion i' X := by
  obtain ⟨C, hC, rfl⟩ := hX
  refine ⟨{Q' | Q' ∈ standardCubePartition L m i' ∧ Q' ⊆ ⋃₀ C}, fun Q' hQ' => hQ'.1, ?_⟩
  refine Subset.antisymm ?_ (sUnion_subset fun Q' hQ' => hQ'.2)
  rintro x ⟨Q, hQ, hx⟩
  obtain ⟨Q', hQ', hxQ', hsub⟩ := exists_finer_partition_cube hL h (hC hQ) hx
  exact ⟨Q', ⟨hQ', hsub.trans (subset_sUnion_of_mem hQ)⟩, hxQ'⟩
theorem sUnion_not_subset_eq (hL : Odd L) (hi : -(m : ℤ) ≤ i) (h : i ≤ i')
    {X : Set (FourTorus L m)} (hX : IsPartitionRegion i X) :
    ⋃₀ {Q | Q ∈ standardCubePartition L m i ∧ ¬Q ⊆ X} =
      ⋃₀ {Q | Q ∈ standardCubePartition L m i' ∧ ¬Q ⊆ X} := by
  have hL0 := hL.pos
  have ha' := meshSize_pos hL0 i'
  have ha := meshSize_pos hL0 i
  obtain ⟨M, hM⟩ := meshSize_eq_odd_mul hL h
  obtain ⟨N, hN⟩ := torusSide_eq_meshSize_mul (m := m) hL0 hi
  apply Subset.antisymm
  · rintro x ⟨Q, ⟨hQ, hnot⟩, hx⟩
    obtain ⟨y, hy, rfl⟩ := (mem_standardCubePartition_iff hL0).1 hQ
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨w', hw', h1, h2⟩ := exists_finer_cubeAbout ha' hM hy hw
    refine ⟨torusProj (torusSide L m) '' cubeAbout (meshSize L i') w',
      ⟨(mem_standardCubePartition_iff hL0).2 ⟨w', hw', rfl⟩, fun hsub => hnot ?_⟩,
      ⟨w, h1, rfl⟩⟩
    have hc : torusProj (torusSide L m) w' ∈ X := hsub ⟨w', self_mem_cubeAbout ha' w', rfl⟩
    obtain ⟨C, hC, rfl⟩ := hX
    obtain ⟨Q'', hQ'', hcQ⟩ := hc
    obtain ⟨y'', hy'', rfl⟩ := (mem_standardCubePartition_iff hL0).1 (hC hQ'')
    have heq := torusProj_eq_of_centre_mem ha' ha hN hy hy'' h2 hcQ
    rw [← image_cubeAbout_eq_of_torusProj_eq heq]
    exact subset_sUnion_of_mem hQ''
  · rintro x ⟨Q', ⟨hQ', hnot⟩, hx⟩
    obtain ⟨z, hz, rfl⟩ := (mem_standardCubePartition_iff hL0).1 hQ'
    obtain ⟨y, hy, h2⟩ := exists_coarser_cubeAbout ha' hM hz
    have hsub : torusProj (torusSide L m) '' cubeAbout (meshSize L i') z ⊆
        torusProj (torusSide L m) '' cubeAbout (meshSize L i) y :=
      image_mono (cubeAbout_subset h2)
    exact ⟨_, ⟨(mem_standardCubePartition_iff hL0).2 ⟨y, hy, rfl⟩,
      fun hh => hnot (hsub.trans hh)⟩, hsub hx⟩
theorem complementRegion_eq_sUnion (i : ℤ) (X : Set (FourTorus L m)) :
    complementRegion i X = ⋃₀ {Q | Q ∈ standardCubePartition L m i ∧ ¬Q ⊆ X} := by
  unfold complementRegion partitionCubesIn
  congr 1
  ext Q
  simp only [mem_sdiff, mem_ofPred_eq, not_and]
  tauto
theorem partitionRefinement (s : Conventions.StandingParameters) (hi : -((s.m : ℕ) : ℤ) ≤ i)
    (h : i ≤ i') : PartitionRefinement s i i' := by
  have hL : Odd s.L := s.isAdmissible.1
  have hL0 := hL.pos
  refine ⟨?_, ?_, fun X hX => isPartitionRegion_of_le hL h hX, fun X hX => ?_⟩
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨w, rfl⟩ := torusProj_surjective _ x
    obtain ⟨y, hy, hw⟩ := exists_onGrid_mem_cubeAbout (meshSize_pos hL0 i) w
    exact ⟨_, (mem_standardCubePartition_iff hL0).2 ⟨y, hy, rfl⟩, ⟨w, hw, rfl⟩⟩
  · intro Q hQ
    exact isPartitionRegion_of_le hL h
      ⟨{Q}, singleton_subset_iff.2 hQ, sUnion_singleton Q |>.symm⟩
  · have he := sUnion_not_subset_eq hL hi h hX
    refine ⟨he, ?_⟩
    rw [complementRegion_eq_sUnion, complementRegion_eq_sUnion, he]
theorem halfIntegerFaces_subset {a a' : ℝ} {M : ℕ} (ha : a = (2 * (M : ℝ) + 1) * a') :
    halfIntegerFaces a ⊆ halfIntegerFaces a' := by
  rintro x ⟨n, rfl⟩
  refine ⟨(2 * (M : ℤ) + 1) * n + M, ?_⟩
  rw [ha]
  push_cast
  ring
theorem no_int_mul_strictly_between {S : ℝ} (hS : 0 < S) {k : ℤ} (h0 : 0 < (k : ℝ) * S)
    (h1 : (k : ℝ) * S < S) : False := by
  have hk0 : (0 : ℝ) < k := by
    by_contra hc
    push Not at hc
    nlinarith
  have hk1 : (k : ℝ) < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have h2 : 0 < k := by exact_mod_cast hk0
  have h3 : k < 1 := by exact_mod_cast hk1
  omega
theorem le_of_translates_lower {S t f lo hi : ℝ} (ht : 0 < t) (htS : t < S) (hf : f ∈ Icc lo hi)
    (h : ∀ c ∈ Icc lo hi, ∃ k : ℤ, f ≤ c + k * S ∧ c + k * S ≤ f + t) : f ≤ lo := by
  by_contra hc
  push Not at hc
  have hS : 0 < S := ht.trans htS
  obtain ⟨e, he0, he1, he2⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ f - lo ∧ e ≤ (S - t) / 2 :=
    ⟨min (f - lo) ((S - t) / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨k, h1, h2⟩ := h (f - e) ⟨by linarith, by linarith [hf.2]⟩
  exact no_int_mul_strictly_between hS (k := k) (by linarith) (by linarith)
theorem ge_of_translates_upper {S t f lo hi : ℝ} (ht : 0 < t) (htS : t < S)
    (hf : f + t ∈ Icc lo hi)
    (h : ∀ c ∈ Icc lo hi, ∃ k : ℤ, f ≤ c + k * S ∧ c + k * S ≤ f + t) : hi ≤ f + t := by
  by_contra hc
  push Not at hc
  have hS : 0 < S := ht.trans htS
  obtain ⟨e, he0, he1, he2⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ hi - (f + t) ∧ e ≤ (S - t) / 2 :=
    ⟨min (hi - (f + t)) ((S - t) / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨k, h1, h2⟩ := h (f + t + e) ⟨by linarith [hf.1], by linarith⟩
  refine no_int_mul_strictly_between hS (k := -k) ?_ ?_
  · push_cast
    linarith
  · push_cast
    linarith
theorem exists_cubeAbout_in_region (hL : 0 < L) (hi : -(m : ℤ) ≤ i) {f g : Fin 4 → ℝ} {t : ℝ}
    (hX : IsPartitionRegion i (torusProj (torusSide L m) '' TorusCubes.realCube f t))
    (hg : g ∈ TorusCubes.realCube f t) :
    ∃ y, OnGrid (meshSize L i) y ∧ g ∈ cubeAbout (meshSize L i) y ∧
      ∀ ν, ∀ c ∈ Icc (y ν - 1 / 2 * meshSize L i) (y ν + 1 / 2 * meshSize L i),
        ∃ k : ℤ, f ν ≤ c + k * torusSide L m ∧ c + k * torusSide L m ≤ f ν + t := by
  obtain ⟨C, hC, hXe⟩ := hX
  obtain ⟨N, hN⟩ := torusSide_eq_meshSize_mul (m := m) hL hi
  have hmem : torusProj (torusSide L m) g ∈ ⋃₀ C := hXe ▸ ⟨g, hg, rfl⟩
  obtain ⟨Q, hQ, hgQ⟩ := hmem
  obtain ⟨y₀, hy₀, rfl⟩ := (mem_standardCubePartition_iff hL).1 (hC hQ)
  obtain ⟨w, hw, hwg⟩ := hgQ
  obtain ⟨q, hq⟩ := exists_int_shift_of_torusProj_eq hwg.symm
  have hsub : torusProj (torusSide L m) ''
        cubeAbout (meshSize L i) (fun ν => y₀ ν + q ν * torusSide L m) ⊆
      torusProj (torusSide L m) '' TorusCubes.realCube f t := by
    rw [image_cubeAbout_eq_of_torusProj_eq (torusProj_add_int_mul _ y₀ q), hXe]
    exact subset_sUnion_of_mem hQ
  have hgc : g ∈ cubeAbout (meshSize L i) (fun ν => y₀ ν + q ν * torusSide L m) := by
    refine mem_cubeAbout.2 fun ν => ?_
    have h1 := mem_cubeAbout.1 hw ν
    rw [hq ν]
    have e : w ν + (q ν : ℝ) * torusSide L m - (y₀ ν + (q ν : ℝ) * torusSide L m) =
        w ν - y₀ ν := by ring
    rwa [e]
  refine ⟨_, onGrid_add_int_mul hy₀ hN q, hgc, fun ν c hc => ?_⟩
  have hup : Function.update g ν c ∈
      cubeAbout (meshSize L i) (fun ν => y₀ ν + q ν * torusSide L m) := by
    intro μ _
    by_cases hμ : μ = ν
    · subst hμ
      simpa using hc
    · simpa [Function.update_of_ne hμ] using hgc μ (mem_univ μ)
  obtain ⟨x', hx', hxe⟩ := hsub ⟨_, hup, rfl⟩
  have hcoord : ((x' ν : ℝ) : AddCircle (torusSide L m)) = (c : ℝ) := by
    have := congrFun hxe ν
    simpa [torusProj] using this
  obtain ⟨k, hk⟩ := exists_int_eq_add_mul_of_coe_eq hcoord
  have hb := hx' ν (mem_univ ν)
  rw [hk] at hb
  exact ⟨k, hb.1, hb.2⟩
theorem faces_of_region_cube (hL : 0 < L) (hi : -(m : ℤ) ≤ i) {f : Fin 4 → ℝ} {t : ℝ}
    (ht : 0 < t) (htS : t < torusSide L m)
    (hX : IsPartitionRegion i (torusProj (torusSide L m) '' TorusCubes.realCube f t)) :
    (∀ ν, f ν ∈ halfIntegerFaces (meshSize L i) ∧ f ν + t ∈ halfIntegerFaces (meshSize L i)) ∧
      ∃ n : ℕ, 0 < n ∧ t = (n : ℝ) * meshSize L i := by
  have ha := meshSize_pos hL i
  have hlow : ∀ ν, ∃ n : ℤ, f ν = meshSize L i * ((n : ℝ) - 1 / 2) := by
    intro ν
    obtain ⟨y, hy, hg, hc⟩ := exists_cubeAbout_in_region hL hi hX
      (g := f) fun μ _ => ⟨le_rfl, by linarith⟩
    have hmem := hg ν (mem_univ ν)
    have := le_of_translates_lower ht htS hmem (hc ν)
    obtain ⟨n, hn⟩ := hy ν
    refine ⟨n, ?_⟩
    have h1 := hmem.1
    rw [hn] at this h1
    linarith
  have hup : ∀ ν, ∃ n : ℤ, f ν + t = meshSize L i * ((n : ℝ) + 1 / 2) := by
    intro ν
    obtain ⟨y, hy, hg, hc⟩ := exists_cubeAbout_in_region hL hi hX
      (g := fun μ => f μ + t) fun μ _ => ⟨by linarith, le_rfl⟩
    have hmem := hg ν (mem_univ ν)
    have := ge_of_translates_upper ht htS hmem (hc ν)
    obtain ⟨n, hn⟩ := hy ν
    refine ⟨n, ?_⟩
    have h1 := hmem.2
    rw [hn] at this h1
    linarith
  refine ⟨fun ν => ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨n, hn⟩ := hlow ν
    refine ⟨n - 1, ?_⟩
    rw [hn]
    push_cast
    ring
  · exact hup ν
  · obtain ⟨n₁, h₁⟩ := hlow 0
    obtain ⟨n₂, h₂⟩ := hup 0
    have hteq : t = ((n₂ - n₁ + 1 : ℤ) : ℝ) * meshSize L i := by
      push_cast
      linarith
    have hpos : 0 < n₂ - n₁ + 1 := by
      have : (0 : ℝ) < ((n₂ - n₁ + 1 : ℤ) : ℝ) := by
        by_contra hc
        push Not at hc
        nlinarith
      exact_mod_cast this
    refine ⟨(n₂ - n₁ + 1).toNat, by omega, ?_⟩
    have hcast : (((n₂ - n₁ + 1).toNat : ℕ) : ℤ) = n₂ - n₁ + 1 := Int.toNat_of_nonneg hpos.le
    have hcastR : (((n₂ - n₁ + 1).toNat : ℕ) : ℝ) = ((n₂ - n₁ + 1 : ℤ) : ℝ) := by
      exact_mod_cast hcast
    rw [hcastR]
    exact hteq
theorem cubeFacts_id (s : Conventions.StandingParameters) (hi : -((s.m : ℕ) : ℤ) ≤ i)
    (h : i ≤ i') : CubeFactsInUnit s id (torusProj (torusSide s.L s.m)) i i' := by
  have hL : Odd s.L := s.isAdmissible.1
  have hL0 := hL.pos
  refine ⟨fun y hy => ?_, ?_, fun t f ht htS hX => faces_of_region_cube hL0 hi ht htS hX⟩
  · exact ⟨⟨_, torusProj_mem_sublattice hy⟩, rfl, cubeAround_eq_image hL0 _ rfl⟩
  · obtain ⟨M, hM⟩ := meshSize_eq_odd_mul hL h
    exact halfIntegerFaces_subset hM
theorem image_pi_Icc_of_scaled {S c : ℝ} (hc : 0 < c) {p : (Fin 4 → ℝ) → Torus4 S}
    (hp : ∀ v, p v = torusProj S (c⁻¹ • v)) (α β : Fin 4 → ℝ) :
    p '' (pi univ fun ν => Icc (α ν) (β ν)) =
      torusProj S '' (pi univ fun ν => Icc (c⁻¹ * α ν) (c⁻¹ * β ν)) := by
  have hc' : 0 < c⁻¹ := inv_pos.2 hc
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨c⁻¹ • v, fun ν _ => ?_, (hp v).symm⟩
    have := hv ν (mem_univ ν)
    exact ⟨mul_le_mul_of_nonneg_left this.1 hc'.le, mul_le_mul_of_nonneg_left this.2 hc'.le⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨c • v, fun ν _ => ?_, ?_⟩
    · have := hv ν (mem_univ ν)
      have e : ∀ r : ℝ, c * (c⁻¹ * r) = r := fun r => mul_inv_cancel_left₀ hc.ne' r
      refine ⟨?_, ?_⟩
      · have h1 := mul_le_mul_of_nonneg_left this.1 hc.le
        rw [e] at h1
        exact h1
      · have h1 := mul_le_mul_of_nonneg_left this.2 hc.le
        rw [e] at h1
        exact h1
    · rw [hp, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
theorem cubeFacts_of_scale (s : Conventions.StandingParameters) {c : ℝ} (hc : 0 < c)
    {u : ℝ → ℝ} {p : (Fin 4 → ℝ) → FourTorus s.L s.m} (hu : ∀ r, u r = c * r)
    (hp : ∀ v, p v = torusProj (torusSide s.L s.m) (c⁻¹ • v))
    (h : CubeFactsInUnit s id (torusProj (torusSide s.L s.m)) i i') :
    CubeFactsInUnit s u p i i' := by
  have hc0 : c ≠ 0 := hc.ne'
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun y hy => ?_, ?_, fun t f ht htS hX => ?_⟩
  · have hy' : ∀ ν, ∃ n : ℤ, (c⁻¹ • y) ν = id (meshSize s.L i) * (n : ℝ) := by
      intro ν
      obtain ⟨n, hn⟩ := hy ν
      refine ⟨n, ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, hn, hu, id]
      field_simp
    obtain ⟨z, hz1, hz2⟩ := h1 (c⁻¹ • y) hy'
    refine ⟨z, by rw [hz1, hp], ?_⟩
    rw [hz2, image_pi_Icc_of_scaled hc hp]
    congr 2
    funext ν
    simp only [hu, id, Pi.smul_apply, smul_eq_mul]
    congr 1 <;> field_simp
  · rintro x ⟨n, rfl⟩
    have hx : c⁻¹ * (u (meshSize s.L i) * ((n : ℝ) + 1 / 2)) ∈
        halfIntegerFaces (id (meshSize s.L i)) := by
      refine ⟨n, ?_⟩
      simp only [hu, id]
      field_simp
    obtain ⟨k, hk⟩ := h2 hx
    refine ⟨k, ?_⟩
    simp only [id] at hk
    rw [hu (meshSize s.L i')]
    have := congrArg (fun r => c * r) hk
    simp only [mul_inv_cancel_left₀ hc0] at this
    rw [this]
    ring
  · have himage : p '' TorusCubes.realCube f t =
        torusProj (torusSide s.L s.m) '' TorusCubes.realCube (c⁻¹ • f) (c⁻¹ * t) := by
      unfold TorusCubes.realCube
      rw [image_pi_Icc_of_scaled hc hp]
      congr 2
      funext ν
      simp only [Pi.smul_apply, smul_eq_mul, mul_add]
    have hlt : c⁻¹ * t < id (torusSide s.L s.m) := by
      rw [hu] at htS
      simp only [id]
      rw [inv_mul_lt_iff₀ hc]
      exact htS
    obtain ⟨h4, n, hn, hnt⟩ := h3 (c⁻¹ * t) (c⁻¹ • f) (mul_pos (inv_pos.2 hc) ht) hlt
      (himage ▸ hX)
    have hscale : ∀ r : ℝ, r ∈ halfIntegerFaces (id (meshSize s.L i)) →
        c * r ∈ halfIntegerFaces (u (meshSize s.L i)) := by
      rintro r ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      simp only [hu, id]
      ring
    refine ⟨fun ν => ?_, n, hn, ?_⟩
    · have h5 := h4 ν
      have h6 := hscale _ h5.1
      have h7 := hscale _ h5.2
      simp only [Pi.smul_apply, smul_eq_mul, mul_add, mul_inv_cancel_left₀ hc0] at h6 h7
      exact ⟨h6, h7⟩
    · have := congrArg (fun r => c * r) hnt
      simp only [mul_inv_cancel_left₀ hc0, id] at this
      rw [this, hu]
      ring
theorem levelUnitLengths (s : Conventions.StandingParameters) (k k' : ℕ) :
    LevelUnitLengths s k k' := by
  have hL : (s.L : ℝ) ≠ 0 := LevelUnits.blockingFactor_cast_ne_zero s
  refine ⟨fun r t ht => ?_, fun j => ?_, ?_, ?_, ?_⟩
  · rw [← ht]
    simp only [toLevelUnits, levelDepth]
    rw [mul_right_comm, ← zpow_add₀ hL]
    congr 2
    ring
  · simp only [toLevelUnits, levelDepth, meshSize]
    rw [← zpow_add₀ hL]
    congr 1
  · simp only [toLevelUnits, meshSize]
    rw [← zpow_add₀ hL]
    simp
  · simp only [toLevelUnits, levelDepth, meshSize, finestMeshInLevelUnits]
    rw [← zpow_add₀ hL]
    congr 1
    ring
  · simp only [toLevelUnits, levelDepth, torusSide]
    rw [mul_left_comm, ← zpow_natCast (s.L : ℝ) (s.m : ℕ), ← zpow_add₀ hL]
    congr 2
    ring
theorem coverMap_eq_torusProj (s : Conventions.StandingParameters) (k : ℕ) (v : Fin 4 → ℝ) :
    LevelUnits.coverMap s k v =
      torusProj (torusSide s.L s.m) (((s.L : ℝ) ^ levelDepth s.K k)⁻¹ • v) := by
  funext μ
  change ((meshSize s.L (levelDepth s.K k) * v μ : ℝ) : AddCircle (torusSide s.L s.m)) =
    ((((s.L : ℝ) ^ levelDepth s.K k)⁻¹ * v μ : ℝ) : AddCircle (torusSide s.L s.m))
  rw [meshSize, zpow_neg]
end PartitionFacts
open PartitionFacts in
theorem standardPartitionsInUnits_holds : StandardPartitionsInUnits := by
  intro s
  refine ⟨fun i i' hi h => ?_, fun k k' _ _ => levelUnitLengths s k k'⟩
  have hphys := cubeFacts_id s hi h
  refine ⟨partitionRefinement s hi h, hphys, fun k _ => ?_⟩
  have hL0 : (0 : ℝ) < s.L := by exact_mod_cast s.isAdmissible.1.pos
  exact cubeFacts_of_scale s (zpow_pos hL0 _) (fun r => rfl) (coverMap_eq_torusProj s k) hphys
end YangMills.Construction.PeriodicLattice
