import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.SiteCoordinatesProof
import YangMills.Construction.Lattice.WeightedDistanceOfASeparatedSequence
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.BlockPartition
variable {L m : ℕ}
def gridPoint (L m : ℕ) (i : ℤ) (N : Fin 4 → ℤ) : FourTorus L m :=
  fun μ => (((N μ : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m))
theorem gridPoint_add (i : ℤ) (N N' : Fin 4 → ℤ) :
    gridPoint L m i (N + N') = gridPoint L m i N + gridPoint L m i N' := by
  funext μ
  simp only [gridPoint, Pi.add_apply, Int.cast_add, add_mul, AddCircle.coe_add]
theorem gridPoint_zero (i : ℤ) : gridPoint L m i 0 = 0 := by
  funext μ
  simp [gridPoint]
theorem mem_sublattice_iff_gridPoint {i : ℤ} {x : FourTorus L m} :
    x ∈ sublattice L m i ↔ ∃ N, x = gridPoint L m i N :=
  ⟨fun ⟨n, hn⟩ => ⟨n, funext hn⟩, fun ⟨n, hn⟩ => ⟨n, fun μ => by rw [hn]; rfl⟩⟩
theorem gridPoint_mem_sublattice (i : ℤ) (N : Fin 4 → ℤ) : gridPoint L m i N ∈ sublattice L m i :=
  mem_sublattice_iff_gridPoint.2 ⟨N, rfl⟩
theorem meshSize_pos (hL : 0 < L) (i : ℤ) : 0 < meshSize L i := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem torusSide_eq_mul_meshSize (hL : 0 < L) {i : ℤ} {k : ℕ} (hk : (m : ℤ) + i = k) :
    torusSide L m = 2 * (L : ℝ) ^ k * meshSize L i := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have h : (m : ℤ) = k + -i := by omega
  unfold torusSide meshSize
  rw [← zpow_natCast (L : ℝ) m, h, zpow_add₀ hL', zpow_natCast]
  ring
theorem meshSize_eq_pow_mul (hL : 0 < L) (j : ℤ) (n : ℕ) :
    meshSize L j = (L : ℝ) ^ n * meshSize L (j + n) := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.meshSize_eq_pow_mul <;> assumption
theorem coe_mul_meshSize_eq_iff (hL : 0 < L) {i : ℤ} {k : ℕ} (hk : (m : ℤ) + i = k) (s t : ℤ) :
    ((((s : ℝ) * meshSize L i : ℝ)) : AddCircle (torusSide L m)) =
        ((((t : ℝ) * meshSize L i : ℝ)) : AddCircle (torusSide L m)) ↔
      2 * (L : ℤ) ^ k ∣ s - t := by
  have ha := meshSize_pos hL i
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [zsmul_eq_mul, torusSide_eq_mul_meshSize hL hk] at hc
    have h : ((s - t : ℤ) : ℝ) * meshSize L i =
        ((2 * (L : ℤ) ^ k * c : ℤ) : ℝ) * meshSize L i := by
      push_cast
      linarith
    exact_mod_cast mul_right_cancel₀ ha.ne' h
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h : (s : ℝ) - t = 2 * (L : ℝ) ^ k * c := by exact_mod_cast hc
    rw [zsmul_eq_mul, torusSide_eq_mul_meshSize hL hk, ← sub_mul, h]
    ring
theorem gridPoint_eq_iff (hL : 0 < L) {i : ℤ} {k : ℕ} (hk : (m : ℤ) + i = k) (N N' : Fin 4 → ℤ) :
    gridPoint L m i N = gridPoint L m i N' ↔ ∀ μ, 2 * (L : ℤ) ^ k ∣ N μ - N' μ := by
  rw [funext_iff]
  exact forall_congr' fun μ => coe_mul_meshSize_eq_iff hL hk _ _
theorem gridPoint_refine (hL : 0 < L) (j : ℤ) (n : ℕ) (N : Fin 4 → ℤ) :
    gridPoint L m j N = gridPoint L m (j + n) (fun μ => (L : ℤ) ^ n * N μ) := by
  funext μ
  have h : (N μ : ℝ) * meshSize L j =
      (((L : ℤ) ^ n * N μ : ℤ) : ℝ) * meshSize L (j + n) := by
    rw [meshSize_eq_pow_mul hL j n]
    push_cast
    ring
  simp only [gridPoint]
  rw [h]
theorem coe_unitStep (i : ℤ) (μ : Fin 4) :
    ((unitStep L m i μ : Site L m i) : FourTorus L m) = gridPoint L m i (Pi.single μ 1) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [unitStep, pointOnAxis, gridPoint]
  · simp [unitStep, pointOnAxis, gridPoint, Pi.single_eq_of_ne h]
theorem coe_offsetSite {i : ℤ} (y : Site L m i) (p : Fin 4 → ℤ) :
    ((offsetSite y p : Site L m i) : FourTorus L m) = y + gridPoint L m i p := by apply _root_.YangMills.DeltaSharedProofs.p500716 <;> assumption
theorem coe_toSublattice {j i : ℤ} (y : Site L m j) (h : (y : FourTorus L m) ∈ sublattice L m i) :
    ((y.toSublattice i : Site L m i) : FourTorus L m) = y := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.coe_toSublattice <;> assumption
theorem coe_refinedOffsetSite (hL : 0 < L) {j : ℤ} (n : ℕ) (y : Site L m j) (p : Fin 4 → ℤ) :
    ((refinedOffsetSite n y p : Site L m (j + n)) : FourTorus L m) = y + gridPoint L m (j + n) p := by
  unfold refinedOffsetSite
  rw [coe_offsetSite,
    coe_toSublattice y (sublattice_mono hL m (by omega : j ≤ j + n) y.2)]
theorem torusSupNorm_le_iff {S : ℝ} (x : TorusMetric.Torus4 S) (r : ℝ) :
    TorusMetric.torusSupNorm x ≤ r ↔ ∀ μ, ‖x μ‖ ≤ r := by apply _root_.YangMills.Construction.SeparatedSequence.torusSupNorm_le_iff <;> assumption
theorem odd_intCast_pow (hL : Odd L) (n : ℕ) : Odd ((L : ℤ) ^ n) :=
  Odd.pow (by exact_mod_cast hL)
theorem intCast_pow_pos (hL : 0 < L) (n : ℕ) : 0 < (L : ℤ) ^ n :=
  pow_pos (by exact_mod_cast hL) n
theorem exists_eq_mul_add_centered {D : ℤ} (hD : Odd D) (hpos : 0 < D) (N : ℤ) :
    ∃ q r : ℤ, N = D * q + r ∧ 2 * |r| ≤ D - 1 := by
  obtain ⟨h, rfl⟩ := hD
  refine ⟨(N + h) / (2 * h + 1), (N + h) % (2 * h + 1) - h, ?_, ?_⟩
  · have := Int.mul_ediv_add_emod (N + h) (2 * h + 1)
    linarith
  · have h1 := Int.emod_nonneg (N + h) (ne_of_gt hpos)
    have h2 := Int.emod_lt_of_pos (N + h) hpos
    have : |(N + h) % (2 * h + 1) - h| ≤ h := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
theorem ncard_blockOffsets (hL : Odd L) (n : ℕ) :
    (blockOffsets L n).ncard = L ^ (4 * n) := by apply _root_.YangMills.SharedProofs.p29861 <;> assumption
variable {j : ℤ} {n : ℕ}
theorem mem_refinedBlock_iff (hodd : Odd L) (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {i : ℤ}
    (hi : i = j + n) (y : Site L m j) (x : FourTorus L m) :
    x ∈ refinedBlock n y ↔ ∃ p ∈ blockOffsets L n, x = y + gridPoint L m i p := by
  subst hi
  have hy : (y : FourTorus L m) ∈ sublattice L m (j + n) := sublattice_mono hL m (by omega) y.2
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ (m : ℤ) + (j + n))
  have ha := meshSize_pos hL (j + n)
  have hsp := meshSize_eq_pow_mul hL j n
  constructor
  · rintro ⟨hc, hx⟩
    have hc' := (torusSupNorm_le_iff _ _).1 hc
    obtain ⟨N, hN⟩ := mem_sublattice_iff_gridPoint.1 (sub_mem hx hy)
    have hcoord : ∀ μ, ∃ t : ℤ,
        (x - (y : FourTorus L m)) μ =
            ((((t : ℝ) * meshSize L (j + n) : ℝ)) : AddCircle (torusSide L m)) ∧
          2 * |t| ≤ (L : ℤ) ^ n - 1 := by
      intro μ
      obtain ⟨v, hv, hv'⟩ := TorusMetric.exists_coe_eq_abs_eq_norm ((x - (y : FourTorus L m)) μ)
      have hNμ : (x - (y : FourTorus L m)) μ =
          ((((N μ : ℝ) * meshSize L (j + n) : ℝ)) : AddCircle (torusSide L m)) := by
        rw [hN]; rfl
      have h0 : ((v - (N μ : ℝ) * meshSize L (j + n) : ℝ) : AddCircle (torusSide L m)) = 0 := by
        rw [AddCircle.coe_sub, hv, hNμ, sub_self]
      obtain ⟨c, hc2⟩ := (AddCircle.coe_eq_zero_iff _).1 h0
      rw [zsmul_eq_mul, torusSide_eq_mul_meshSize hL hk] at hc2
      refine ⟨N μ + c * (2 * (L : ℤ) ^ k), ?_, ?_⟩
      · rw [← hv]
        congr 1
        push_cast
        linarith
      · have hv2 : v = ((N μ + c * (2 * (L : ℤ) ^ k) : ℤ) : ℝ) * meshSize L (j + n) := by
          push_cast
          linarith
        have hb : |v| ≤ meshSize L j / 2 := hv' ▸ hc' μ
        rw [hv2, abs_mul, abs_of_pos ha, hsp] at hb
        have hb2 : 2 * |((N μ + c * (2 * (L : ℤ) ^ k) : ℤ) : ℝ)| ≤ (L : ℝ) ^ n := by
          have : (2 * |((N μ + c * (2 * (L : ℤ) ^ k) : ℤ) : ℝ)|) * meshSize L (j + n) ≤
              (L : ℝ) ^ n * meshSize L (j + n) := by linarith
          exact le_of_mul_le_mul_right this ha
        have hb3 : 2 * |N μ + c * (2 * (L : ℤ) ^ k)| ≤ (L : ℤ) ^ n := by
          exact_mod_cast hb2
        obtain ⟨h, hh⟩ := odd_intCast_pow hodd n
        rw [hh] at hb3 ⊢
        generalize |N μ + c * (2 * (L : ℤ) ^ k)| = w at hb3 ⊢
        omega
    choose p hp hp' using hcoord
    refine ⟨p, hp', ?_⟩
    have : x - (y : FourTorus L m) = gridPoint L m (j + n) p := funext hp
    rw [← this]
    abel
  · rintro ⟨p, hp, rfl⟩
    refine ⟨?_, add_mem hy (gridPoint_mem_sublattice _ _)⟩
    refine (torusSupNorm_le_iff _ _).2 fun μ => ?_
    rw [add_sub_cancel_left]
    refine (TorusMetric.addCircle_norm_coe_le_abs _).trans ?_
    rw [abs_mul, abs_of_pos ha, hsp]
    have h1 : 2 * |p μ| ≤ (L : ℤ) ^ n := by
      have := hp μ
      linarith
    have h2 : 2 * |(p μ : ℝ)| ≤ (L : ℝ) ^ n := by exact_mod_cast h1
    nlinarith
theorem eq_of_mem_refinedBlock_of_mem (hodd : Odd L) (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    {y y' : Site L m j} {x : FourTorus L m} (h : x ∈ refinedBlock n y)
    (h' : x ∈ refinedBlock n y') : y = y' := by
  obtain ⟨p, hp, hx⟩ := (mem_refinedBlock_iff hodd hL hj rfl y x).1 h
  obtain ⟨p', hp', hx'⟩ := (mem_refinedBlock_iff hodd hL hj rfl y' x).1 h'
  obtain ⟨Y, hY⟩ := mem_sublattice_iff_gridPoint.1 y.2
  obtain ⟨Y', hY'⟩ := mem_sublattice_iff_gridPoint.1 y'.2
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ (m : ℤ) + j)
  have hk' : (m : ℤ) + (j + n) = ((k + n : ℕ) : ℤ) := by push_cast; omega
  have hpts : gridPoint L m (j + n) ((fun μ => (L : ℤ) ^ n * Y μ) + p) =
      gridPoint L m (j + n) ((fun μ => (L : ℤ) ^ n * Y' μ) + p') := by
    rw [gridPoint_add, gridPoint_add, ← gridPoint_refine hL, ← gridPoint_refine hL, ← hY, ← hY',
      ← hx, ← hx']
  have hd := (gridPoint_eq_iff hL hk' _ _).1 hpts
  have hD := intCast_pow_pos hL n
  have hpe : ∀ μ, p μ = p' μ := by
    intro μ
    have h1 : (L : ℤ) ^ n ∣ p μ - p' μ := by
      have h2 : (L : ℤ) ^ n ∣ 2 * (L : ℤ) ^ (k + n) :=
        ⟨2 * (L : ℤ) ^ k, by rw [pow_add]; ring⟩
      have h3 := h2.trans (hd μ)
      have h4 : (L : ℤ) ^ n * Y μ + p μ - ((L : ℤ) ^ n * Y' μ + p' μ) =
          (L : ℤ) ^ n * (Y μ - Y' μ) + (p μ - p' μ) := by ring
      simp only [Pi.add_apply] at h3
      rw [h4] at h3
      exact (Int.dvd_add_right (dvd_mul_right _ _)).1 h3
    have h5 : |p μ - p' μ| < (L : ℤ) ^ n := by
      have a1 := abs_le.1 (by have := hp μ; omega : |p μ| ≤ ((L : ℤ) ^ n - 1) / 2)
      have a2 := abs_le.1 (by have := hp' μ; omega : |p' μ| ≤ ((L : ℤ) ^ n - 1) / 2)
      rw [abs_lt]
      omega
    have := Int.eq_zero_of_abs_lt_dvd h1 h5
    linarith
  have hYe : gridPoint L m j Y = gridPoint L m j Y' := by
    refine (gridPoint_eq_iff hL hk _ _).2 fun μ => ?_
    have h6 := hd μ
    simp only [Pi.add_apply, hpe μ] at h6
    have h7 : (L : ℤ) ^ n * Y μ + p' μ - ((L : ℤ) ^ n * Y' μ + p' μ) =
        (L : ℤ) ^ n * (Y μ - Y' μ) := by ring
    have h8 : 2 * (L : ℤ) ^ (k + n) = (L : ℤ) ^ n * (2 * (L : ℤ) ^ k) := by
      rw [pow_add]; ring
    rw [h7, h8] at h6
    exact (mul_dvd_mul_iff_left hD.ne').1 h6
  exact Subtype.ext (by rw [hY, hY', hYe])
theorem refinedBlock_eq_offsetImage (hodd : Odd L) (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (y : Site L m j) : RefinedBlockEqOffsetImage L m j n y := by
  have himg : refinedBlock n y =
      (fun p => (refinedOffsetSite n y p : FourTorus L m)) '' blockOffsets L n := by
    ext x
    rw [mem_refinedBlock_iff hodd hL hj rfl y x]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, coe_refinedOffsetSite hL n y p⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, coe_refinedOffsetSite hL n y p⟩
  have hinj : InjOn (fun p => (refinedOffsetSite n y p : FourTorus L m)) (blockOffsets L n) := by
    intro p hp p' hp' h
    simp only [coe_refinedOffsetSite hL] at h
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ (m : ℤ) + j)
    have hk' : (m : ℤ) + (j + n) = ((k + n : ℕ) : ℤ) := by push_cast; omega
    have hd := (gridPoint_eq_iff hL hk' _ _).1 (add_left_cancel h)
    funext μ
    have hD : (L : ℤ) ^ n ≤ (L : ℤ) ^ (k + n) := by
      rw [pow_add]
      exact le_mul_of_one_le_left (intCast_pow_pos hL n).le (intCast_pow_pos hL k)
    have a1 := abs_le.1 (by have := hp μ; omega : |p μ| ≤ ((L : ℤ) ^ n - 1) / 2)
    have a2 := abs_le.1 (by have := hp' μ; omega : |p' μ| ≤ ((L : ℤ) ^ n - 1) / 2)
    have h5 : |p μ - p' μ| < 2 * (L : ℤ) ^ (k + n) := by
      have := intCast_pow_pos hL n
      rw [abs_lt]
      omega
    have := Int.eq_zero_of_abs_lt_dvd (hd μ) h5
    linarith
  refine ⟨himg, hinj, ?_⟩
  rw [himg, hinj.ncard_image, ncard_blockOffsets hodd]
theorem exists_mem_refinedBlock (hodd : Odd L) (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    {x : FourTorus L m} (hx : x ∈ sublattice L m (j + n)) :
    ∃ y : Site L m j, x ∈ refinedBlock n y := by
  obtain ⟨N, rfl⟩ := mem_sublattice_iff_gridPoint.1 hx
  choose q r hqr hr using fun μ =>
    exists_eq_mul_add_centered (odd_intCast_pow hodd n) (intCast_pow_pos hL n) (N μ)
  refine ⟨⟨gridPoint L m j q, gridPoint_mem_sublattice _ _⟩,
    (mem_refinedBlock_iff hodd hL hj rfl _ _).2 ⟨r, hr, ?_⟩⟩
  show gridPoint L m (j + n) N = gridPoint L m j q + gridPoint L m (j + n) r
  rw [gridPoint_refine hL j n, ← gridPoint_add]
  congr 1
  funext μ
  exact hqr μ
theorem mem_refinedBlock_self (hodd : Odd L) (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (y : Site L m j) :
    (y : FourTorus L m) ∈ refinedBlock n y := by
  refine (mem_refinedBlock_iff hodd hL hj rfl y _).2
    ⟨0, fun μ => ?_, by rw [gridPoint_zero, add_zero]⟩
  have := intCast_pow_pos hL n
  simp only [Pi.zero_apply, abs_zero, mul_zero]
  omega
theorem refinedBlocks_partition (hodd : Odd L) (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    RefinedBlocksPartition L m j n := by
  refine ⟨mem_refinedBlock_self hodd hL hj, sublattice_mono hL m (by omega), ?_, ?_⟩
  · intro y y' hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    exact eq_of_mem_refinedBlock_of_mem hodd hL hj hx hx'
  · ext x
    simp only [mem_iUnion, SetLike.mem_coe]
    constructor
    · rintro ⟨y, hy⟩
      exact hy.2
    · exact exists_mem_refinedBlock hodd hL hj
theorem combine_mem_blockOffsets (hL : 0 < L) {n' : ℕ} {p p' : Fin 4 → ℤ}
    (hp : p ∈ blockOffsets L n) (hp' : p' ∈ blockOffsets L n') :
    (fun μ => (L : ℤ) ^ n' * p μ + p' μ) ∈ blockOffsets L (n + n') := by
  intro μ
  have hA := intCast_pow_pos hL n'
  have h1 : |(L : ℤ) ^ n' * p μ + p' μ| ≤ (L : ℤ) ^ n' * |p μ| + |p' μ| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hA]
  have h2 := hp μ
  have h3 := hp' μ
  have h4 : (L : ℤ) ^ (n + n') = (L : ℤ) ^ n' * (L : ℤ) ^ n := by rw [pow_add]; ring
  rw [h4]
  nlinarith
theorem quotient_mem_blockOffsets (hodd : Odd L) (hL : 0 < L) {n' : ℕ} {P q r : Fin 4 → ℤ}
    (hP : P ∈ blockOffsets L (n + n')) (hqr : ∀ μ, P μ = (L : ℤ) ^ n' * q μ + r μ)
    (hr : r ∈ blockOffsets L n') : q ∈ blockOffsets L n := by
  intro μ
  have hA := intCast_pow_pos hL n'
  have h1 : (L : ℤ) ^ n' * |q μ| ≤ |P μ| + |r μ| := by
    have : (L : ℤ) ^ n' * q μ = P μ - r μ := by rw [hqr μ]; ring
    calc (L : ℤ) ^ n' * |q μ| = |(L : ℤ) ^ n' * q μ| := by rw [abs_mul, abs_of_pos hA]
      _ = |P μ - r μ| := by rw [this]
      _ ≤ |P μ| + |r μ| := abs_sub _ _
  have h2 := hP μ
  have h3 := hr μ
  have h4 : (L : ℤ) ^ (n + n') = (L : ℤ) ^ n' * (L : ℤ) ^ n := by rw [pow_add]; ring
  rw [h4] at h2
  have h5 : (L : ℤ) ^ n' * (2 * |q μ|) < (L : ℤ) ^ n' * ((L : ℤ) ^ n + 1) := by nlinarith
  have h6 := lt_of_mul_lt_mul_left h5 hA.le
  obtain ⟨h, hh⟩ := odd_intCast_pow hodd n
  rw [hh] at h6 ⊢
  generalize |q μ| = w at h6 ⊢
  omega
theorem refinedBlock_of_sum_order (hodd : Odd L) (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (n' : ℕ)
    (y : Site L m j) : RefinedBlockOfSumOrder L m j n n' y := by
  have hj' : -(m : ℤ) ≤ j + n := by omega
  have hi : j + n + n' = j + ((n + n' : ℕ) : ℤ) := by push_cast; ring
  ext z
  simp only [mem_iUnion, exists_prop]
  rw [mem_refinedBlock_iff hodd hL hj hi y z]
  constructor
  · rintro ⟨P, hP, rfl⟩
    choose q r hqr hr using fun μ =>
      exists_eq_mul_add_centered (odd_intCast_pow hodd n') (intCast_pow_pos hL n') (P μ)
    have hq := quotient_mem_blockOffsets hodd hL hP hqr hr
    have hx : ((y : FourTorus L m) + gridPoint L m (j + n) q) ∈ sublattice L m (j + n) :=
      add_mem (sublattice_mono hL m (by omega) y.2) (gridPoint_mem_sublattice _ _)
    refine ⟨⟨_, hx⟩, (mem_refinedBlock_iff hodd hL hj rfl y _).2 ⟨q, hq, rfl⟩,
      (mem_refinedBlock_iff hodd hL hj' rfl _ _).2 ⟨r, hr, ?_⟩⟩
    have : P = (fun μ => (L : ℤ) ^ n' * q μ) + r := funext hqr
    rw [this, gridPoint_add, ← gridPoint_refine hL]
    exact (add_assoc _ _ _).symm
  · rintro ⟨x, hx, hz⟩
    obtain ⟨p, hp, hxp⟩ := (mem_refinedBlock_iff hodd hL hj rfl y _).1 hx
    obtain ⟨p', hp', rfl⟩ := (mem_refinedBlock_iff hodd hL hj' rfl x z).1 hz
    refine ⟨_, combine_mem_blockOffsets hL hp hp', ?_⟩
    have : (fun μ => (L : ℤ) ^ n' * p μ + p' μ) = (fun μ => (L : ℤ) ^ n' * p μ) + p' := rfl
    rw [this, gridPoint_add, ← gridPoint_refine hL, hxp, add_assoc]
theorem step_from_refinedBlock (hodd : Odd L) (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (y : Site L m j) :
    StepFromRefinedBlockSite L m j n y := by
  intro p hp μ
  have hcoe : (((refinedOffsetSite n y p + unitStep L m (j + n) μ : Site L m (j + n))) :
      FourTorus L m) = y + gridPoint L m (j + n) (p + Pi.single μ 1) := by
    rw [AddSubgroup.coe_add, coe_refinedOffsetSite hL, coe_unitStep, gridPoint_add, add_assoc]
  obtain ⟨h, hh⟩ := odd_intCast_pow hodd n
  constructor
  · intro hlt
    rw [hcoe]
    refine (mem_refinedBlock_iff hodd hL hj rfl y _).2 ⟨_, fun ν => ?_, rfl⟩
    by_cases hν : ν = μ
    · subst hν
      have a1 := abs_le.1 (by have := hp ν; omega : |p ν| ≤ ((L : ℤ) ^ n - 1) / 2)
      simp only [Pi.add_apply, Pi.single_eq_same]
      have : |p ν + 1| ≤ h := abs_le.2 (by omega)
      omega
    · simpa [Pi.single_eq_of_ne hν] using hp ν
  · intro heq
    rw [hcoe]
    refine (mem_refinedBlock_iff hodd hL hj rfl _ _).2
      ⟨p + Pi.single μ 1 - Pi.single μ ((L : ℤ) ^ n), fun ν => ?_, ?_⟩
    · by_cases hν : ν = μ
      · subst hν
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
        have hpos := intCast_pow_pos hL n
        have : |p ν + 1 - (L : ℤ) ^ n| ≤ h := abs_le.2 (by omega)
        omega
      · simpa [Pi.single_eq_of_ne hν] using hp ν
    · have hs : p + Pi.single μ 1 =
          (p + Pi.single μ 1 - Pi.single μ ((L : ℤ) ^ n)) + Pi.single μ ((L : ℤ) ^ n) := by
        abel
      have hst : gridPoint L m (j + n) (Pi.single μ ((L : ℤ) ^ n)) =
          gridPoint L m j (Pi.single μ 1) := by
        rw [gridPoint_refine hL j n]
        congr 1
        funext ν
        by_cases hν : ν = μ
        · subst hν
          simp
        · simp [Pi.single_eq_of_ne hν]
      conv_lhs => rw [hs, gridPoint_add, hst]
      rw [AddSubgroup.coe_add, coe_unitStep]
      abel
theorem unitStep_injective (hL : 0 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i) {μ ν : Fin 4}
    (h : unitStep L m i μ = unitStep L m i ν) : μ = ν := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ (m : ℤ) + i)
  by_contra hne
  have h1 : gridPoint L m i (Pi.single μ 1) = gridPoint L m i (Pi.single ν 1) := by
    rw [← coe_unitStep, ← coe_unitStep, h]
  have h2 := (gridPoint_eq_iff hL hk _ _).1 h1 μ
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne, sub_zero] at h2
  have h3 := Int.le_of_dvd one_pos h2
  have := intCast_pow_pos hL k
  omega
theorem eq_of_unitStep_eq_neg (hL : 1 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i) {μ ν : Fin 4}
    (h : unitStep L m i μ = -unitStep L m i ν) : μ = ν ∧ (m : ℤ) + i = 0 := by
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ (m : ℤ) + i)
  have hL0 : 0 < L := by omega
  have h1 : gridPoint L m i (Pi.single μ 1) + gridPoint L m i (Pi.single ν 1) =
      gridPoint L m i 0 := by
    rw [← coe_unitStep, ← coe_unitStep, gridPoint_zero, h, AddSubgroup.coe_neg, neg_add_cancel]
  rw [← gridPoint_add] at h1
  have h2 := (gridPoint_eq_iff hL0 hk _ _).1 h1 μ
  have hpos := intCast_pow_pos hL0 k
  by_cases hne : μ = ν
  · subst hne
    refine ⟨rfl, ?_⟩
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply, sub_zero] at h2
    have h3 : 2 * (L : ℤ) ^ k ≤ 2 := Int.le_of_dvd (by norm_num) h2
    rcases Nat.eq_zero_or_pos k with rfl | hkp
    · simpa using hk
    · exfalso
      have h4 : 1 < (L : ℤ) ^ k := one_lt_pow₀ (by exact_mod_cast hL) hkp.ne'
      omega
  · exfalso
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, Pi.zero_apply, sub_zero,
      add_zero] at h2
    have h3 := Int.le_of_dvd one_pos h2
    omega
theorem unitStep_eq_neg_self (hL : 0 < L) {i : ℤ} (hi : (m : ℤ) + i = 0) (μ : Fin 4) :
    unitStep L m i μ = -unitStep L m i μ := by
  refine Subtype.ext ?_
  rw [AddSubgroup.coe_neg, eq_neg_iff_add_eq_zero, coe_unitStep, ← gridPoint_add,
    ← gridPoint_zero i]
  refine (gridPoint_eq_iff (k := 0) hL (by simpa using hi) _ _).2 fun ν => ?_
  simp only [Pi.add_apply, Pi.zero_apply, sub_zero, pow_zero, mul_one]
  exact ⟨(Pi.single μ 1 : Fin 4 → ℤ) ν, by ring⟩
theorem unitStep_between_refinedBlocks (hodd : Odd L) (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (t h : Site L m (j + n)) (μ : Fin 4) (hμ : h - t = unitStep L m (j + n) μ) :
    (∃ y : Site L m j, (t : FourTorus L m) ∈ refinedBlock n y ∧
        (h : FourTorus L m) ∈ refinedBlock n y) ∨
      ∃ y : Site L m j, (t : FourTorus L m) ∈ refinedBlock n y ∧
        (h : FourTorus L m) ∈ refinedBlock n (y + unitStep L m j μ) := by
  obtain ⟨y, hy⟩ := exists_mem_refinedBlock hodd hL hj t.2
  obtain ⟨p, hp, hx⟩ := (mem_refinedBlock_iff hodd hL hj rfl y _).1 hy
  have ht : t = refinedOffsetSite n y p := Subtype.ext (by rw [coe_refinedOffsetSite hL]; exact hx)
  have hh : h = refinedOffsetSite n y p + unitStep L m (j + n) μ := by
    rw [← ht, ← hμ]
    abel
  have hs := step_from_refinedBlock hodd hL hj y p hp μ
  have hle : 2 * p μ ≤ (L : ℤ) ^ n - 1 :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)).trans (hp μ)
  rw [← hh] at hs
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inl ⟨y, hy, hs.1 hlt⟩
  · exact Or.inr ⟨y, hy, hs.2 heq⟩
theorem bondEndpoints_in_refinedBlocks (hodd : Odd L) (hL : 1 < L) (hj : -(m : ℤ) ≤ j) :
    BondEndpointsInBlocks L m j n := by
  have hL0 : 0 < L := by omega
  have hj' : -(m : ℤ) ≤ j + n := by omega
  have hneg : (m : ℤ) + (j + n) = 0 → ∀ μ, unitStep L m j μ = -unitStep L m j μ := fun h μ =>
    unitStep_eq_neg_self hL0 (by omega) μ
  intro b
  obtain ⟨μ, hμ | hμ⟩ := b.isNeighbour
  · rcases unitStep_between_refinedBlocks hodd hL0 hj b.source b.target μ hμ with
      ⟨y, h1, h2⟩ | ⟨y, h1, h2⟩
    · exact Or.inl ⟨y, h1, h2⟩
    · have hc : (Bond.forwardFrom y μ).target - (Bond.forwardFrom y μ).source =
          unitStep L m j μ := by
        simp [Bond.forwardFrom]
      refine Or.inr ⟨Bond.forwardFrom y μ, ⟨h1, h2⟩, fun ν => ⟨fun h => ?_, fun h => ?_⟩,
        fun c' hc' => ?_⟩
      · rw [unitStep_injective hL0 hj' (hμ.symm.trans h) |>.symm]
        exact hc
      · obtain ⟨rfl, hz⟩ := eq_of_unitStep_eq_neg hL hj' (hμ.symm.trans h)
        rw [hc]
        exact hneg hz _
      · exact Bond.ext (eq_of_mem_refinedBlock_of_mem hodd hL0 hj hc'.1 h1)
          (eq_of_mem_refinedBlock_of_mem hodd hL0 hj hc'.2 h2)
  · have hμ' : b.source - b.target = unitStep L m (j + n) μ := by rw [← neg_sub, hμ, neg_neg]
    rcases unitStep_between_refinedBlocks hodd hL0 hj b.target b.source μ hμ' with
      ⟨y, h1, h2⟩ | ⟨y, h1, h2⟩
    · exact Or.inl ⟨y, h2, h1⟩
    · have hc : (Bond.forwardFrom y μ).opposite.target - (Bond.forwardFrom y μ).opposite.source =
          -unitStep L m j μ := by
        simp [Bond.forwardFrom, Bond.opposite]
      refine Or.inr ⟨(Bond.forwardFrom y μ).opposite, ⟨h2, h1⟩,
        fun ν => ⟨fun h => ?_, fun h => ?_⟩, fun c' hc' => ?_⟩
      · obtain ⟨rfl, hz⟩ := eq_of_unitStep_eq_neg hL hj' (h.symm.trans hμ)
        rw [hc]
        exact (hneg hz _).symm
      · rw [unitStep_injective hL0 hj' (neg_injective (hμ.symm.trans h)) |>.symm]
        exact hc
      · exact Bond.ext (eq_of_mem_refinedBlock_of_mem hodd hL0 hj hc'.1 h2)
          (eq_of_mem_refinedBlock_of_mem hodd hL0 hj hc'.2 h1)
theorem properties_hold : BlockPartition.Properties := by
  intro L m hL _ j n n' hj
  obtain ⟨hodd, h13⟩ := hL
  have hL0 : 0 < L := by omega
  exact ⟨refinedBlock_eq_offsetImage hodd hL0 hj, refinedBlocks_partition hodd hL0 hj,
    refinedBlock_of_sum_order hodd hL0 hj n', step_from_refinedBlock hodd hL0 hj,
    bondEndpoints_in_refinedBlocks hodd (by omega) hj⟩
end YangMills.Construction.PeriodicLattice.BlockPartition
