import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.CubesBlocksDistancesAndTraces
import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.Lattice.LatticeAsAProbabilitySpaceProof
import YangMills.Construction.Lattice.StandardPartitionsAndLevelUnits
import YangMills.Construction.Lattice.WeightsAsFunctionsOfTheConfigurationAndSourcedIntegrals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubeGeometry
open Set YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : _root_.YangMills.Construction.TorusMetric.torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem le_norm_coe_intMul_of_ne_zero {S a : ℝ} {N : ℕ} (hS : S = (N : ℝ) * a) (ha : 0 < a)
    (n : ℤ) (h : (((n : ℝ) * a : ℝ) : AddCircle S) ≠ 0) :
    a ≤ ‖(((n : ℝ) * a : ℝ) : AddCircle S)‖ := by
  subst hS
  rw [AddCircle.norm_eq]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = round (((N : ℝ) * a)⁻¹ * ((n : ℝ) * a)) := ⟨_, rfl⟩
  rw [← hk]
  have e : (n : ℝ) * a - (k : ℝ) * ((N : ℝ) * a) = ((n - k * N : ℤ) : ℝ) * a := by
    push_cast
    ring
  rw [e, abs_mul, abs_of_pos ha]
  have hne : n - k * N ≠ 0 := by
    intro h0
    apply h
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨k, ?_⟩
    have hn : n = k * N := by linarith
    rw [hn, zsmul_eq_mul]
    push_cast
    ring
  have h1 : (1 : ℝ) ≤ |((n - k * N : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hne
  nlinarith
theorem eq_of_addCircle_coe_eq_of_abs_sub_le {S a u v : ℝ} (hS : 0 < S) (ha : a ≤ S / 2)
    (h : (u : AddCircle S) = v) (hb : |u - v| ≤ a) : u = v := by
  have h3 : ((u - v : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 h3
  have hk0 : k = 0 := by
    by_contra hk0
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hk0
    rw [← hk, zsmul_eq_mul, abs_mul, abs_of_pos hS] at hb
    nlinarith
  rw [hk0, zero_smul] at hk
  linarith
theorem exists_outward_step {a ε w : ℝ} (ha : 0 < a) (hε : 0 < ε) (hw : |w| = a / 2) :
    ∃ t δ : ℝ, 0 < δ ∧ δ ≤ a / 4 ∧ δ < ε ∧ |t| = δ ∧ |w + t| = a / 2 + δ := by
  obtain ⟨δ, hδ, hδa, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ a / 4 ∧ δ < ε :=
    ⟨min (ε / 2) (a / 4), lt_min (by linarith) (by linarith), min_le_right _ _,
      (min_le_left _ _).trans_lt (by linarith)⟩
  rcases le_total 0 w with h | h
  · refine ⟨δ, δ, hδ, hδa, hδε, abs_of_pos hδ, ?_⟩
    rw [abs_of_nonneg h] at hw
    rw [abs_of_pos (by linarith), hw]
  · refine ⟨-δ, δ, hδ, hδa, hδε, by rw [abs_neg, abs_of_pos hδ], ?_⟩
    rw [abs_of_nonpos h] at hw
    rw [abs_of_neg (by linarith)]
    linarith
theorem exists_near_point_shifted_coord {S : ℝ} (x c : Torus4 S) (w t ε : ℝ) (μ : Fin 4)
    (hε : 0 < ε) (ht : |t| < ε) (hw : (w : AddCircle S) = x μ - c μ) :
    ∃ z : Torus4 S, z ∈ Metric.ball x ε ∧ z μ - c μ = ((w + t : ℝ) : AddCircle S) := by
  refine ⟨Function.update x μ (x μ + (t : AddCircle S)), ?_, ?_⟩
  · rw [mem_ball_iff_norm, pi_norm_lt_iff hε]
    intro ν
    by_cases h : ν = μ
    · subst h
      rw [Pi.sub_apply, Function.update_self, add_sub_cancel_left]
      exact (addCircle_norm_coe_le_abs t).trans_lt ht
    · rw [Pi.sub_apply, Function.update_of_ne h, sub_self, norm_zero]
      exact hε
  · rw [Function.update_self, AddCircle.coe_add, hw]
    abel
theorem norm_coord_sub_lt_of_mem_interior {S a : ℝ} (hS : 0 < S) (ha : 0 < a)
    (hhalf : a ≤ S / 2) (c x : Torus4 S) (Q : Set (Torus4 S)) (hQ : ∀ z ∈ Q, ‖z - c‖ ≤ a / 2)
    (hx : x ∈ interior Q) (μ : Fin 4) : ‖x μ - c μ‖ < a / 2 := by
  by_contra hnot
  have h1 : ‖x μ - c μ‖ ≤ a / 2 :=
    (norm_le_pi_norm (x - c) μ).trans (hQ x (interior_subset hx))
  have h4 : ‖x μ - c μ‖ = a / 2 := le_antisymm h1 (not_lt.1 hnot)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  obtain ⟨w, hw, hw'⟩ := exists_coe_eq_abs_eq_norm (x μ - c μ)
  rw [h4] at hw'
  obtain ⟨t, δ, hδ, hδa, hδε, ht, ht'⟩ := exists_outward_step ha hε hw'
  obtain ⟨z, hz, hzc⟩ :=
    exists_near_point_shifted_coord x c w t ε μ hε (by rw [ht]; exact hδε) hw
  have hz2 : ‖z μ - c μ‖ ≤ a / 2 := (norm_le_pi_norm (z - c) μ).trans (hQ z (hball hz))
  rw [hzc] at hz2
  have hs : |w + t| ≤ |S| / 2 := by
    rw [ht', abs_of_pos hS]
    linarith only [hhalf, hδa, ha]
  rw [(AddCircle.norm_coe_eq_abs_iff S hS.ne').2 hs, ht'] at hz2
  linarith only [hz2, hδ]
theorem center_eq_of_mem_interior {S a : ℝ} {N : ℕ} (hN : S = (N : ℝ) * a) (hS : 0 < S)
    (ha : 0 < a) (hhalf : a ≤ S / 2) (c c' x : Torus4 S) (n n' : Fin 4 → ℤ)
    (hn : ∀ μ, c μ = (((n μ : ℝ) * a : ℝ) : AddCircle S))
    (hn' : ∀ μ, c' μ = (((n' μ : ℝ) * a : ℝ) : AddCircle S))
    (Q : Set (Torus4 S)) (hQ : ∀ z ∈ Q, ‖z - c‖ ≤ a / 2) (hx : x ∈ interior Q)
    (hx' : ‖x - c'‖ ≤ a / 2) : c' = c := by
  funext μ
  by_contra hμ
  have hd : c μ - c' μ = ((((n μ - n' μ : ℤ) : ℝ) * a : ℝ) : AddCircle S) := by
    rw [hn μ, hn' μ, ← AddCircle.coe_sub]
    congr 1
    push_cast
    ring
  have hlow : a ≤ ‖c μ - c' μ‖ := by
    rw [hd]
    exact le_norm_coe_intMul_of_ne_zero hN ha _ (by rw [← hd]; exact sub_ne_zero.2 (Ne.symm hμ))
  have h1 := norm_coord_sub_lt_of_mem_interior hS ha hhalf c x Q hQ hx μ
  have h2 : ‖x μ - c' μ‖ ≤ a / 2 := (norm_le_pi_norm (x - c') μ).trans hx'
  have h3 : ‖c μ - c' μ‖ ≤ ‖x μ - c' μ‖ + ‖x μ - c μ‖ := by
    have e : c μ - c' μ = (x μ - c' μ) - (x μ - c μ) := by abel
    rw [e]
    exact norm_sub_le _ _
  linarith only [hlow, h1, h2, h3]
theorem exists_setSupDist_eq {S : ℝ} (A B : Set (Torus4 S)) (hA : A.Nonempty) (hB : B.Nonempty)
    (hcA : IsCompact A) (hcB : IsCompact B) :
    ∃ a ∈ A, ∃ b ∈ B, setSupDist A B = ENNReal.ofReal (_root_.YangMills.Construction.TorusMetric.torusSupNorm (a - b)) := by
  have hc : IsCompact (A ×ˢ B) := hcA.prod hcB
  have hcont : Continuous (fun q : Torus4 S × Torus4 S => ‖q.1 - q.2‖) :=
    continuous_norm.comp (continuous_fst.sub continuous_snd)
  obtain ⟨⟨a, b⟩, hab, hmin⟩ := hc.exists_isMinOn (hA.prod hB) hcont.continuousOn
  refine ⟨a, hab.1, b, hab.2, le_antisymm ?_ ?_⟩
  · unfold setSupDist
    refine iInf₂_le_of_le a hab.1 (iInf₂_le_of_le b hab.2 ?_)
    rw [_root_.YangMills.Construction.PeriodicLattice.CubeGeometry.torusSupNorm_eq_norm]
  · unfold setSupDist
    refine le_iInf₂ fun a' ha' => le_iInf₂ fun b' hb' => ?_
    simp only [_root_.YangMills.Construction.PeriodicLattice.CubeGeometry.torusSupNorm_eq_norm]
    have hle : ‖a - b‖ ≤ ‖a' - b'‖ := isMinOn_iff.1 hmin (a', b') (mk_mem_prod ha' hb')
    exact ENNReal.ofReal_le_ofReal hle
theorem mem_cubeAround_iff {j : ℤ} (y : Site L m j) (x : FourTorus L m) :
    x ∈ cubeAround y ↔ ‖x - (y : FourTorus L m)‖ ≤ meshSize L j / 2 := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.mem_cubeAround <;> assumption
theorem mem_sublattice_iff (j : ℤ) (x : FourTorus L m) :
    x ∈ sublattice L m j ↔ ∃ n : Fin 4 → ℤ, ∀ μ,
      x μ = (((n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := Iff.rfl
theorem zero_lt_meshSize (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem torusSide_pos (hL : 0 < L) (m : ℕ) : 0 < torusSide L m := by apply _root_.YangMills.SharedProofs.p34445 <;> assumption
theorem meshSize_eq_pow_mul (hL : 0 < L) (i : ℤ) (n : ℕ) :
    meshSize L i = (L : ℝ) ^ n * meshSize L (i + n) := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.meshSize_eq_pow_mul <;> assumption
theorem meshSize_le_half_torusSide (hL : 0 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i) :
    meshSize L i ≤ torusSide L m / 2 := by
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h2 := zpow_le_zpow_right₀ h1 (show -i ≤ (m : ℤ) by omega)
  rw [zpow_natCast] at h2
  simp only [meshSize, torusSide]
  linarith
theorem site_eq_of_mem_interior_cubeAround (hL : 0 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i) {N : ℕ}
    (hN : torusSide L m = (N : ℝ) * meshSize L i) (y y' : Site L m i) (x : FourTorus L m)
    (hx : x ∈ interior (cubeAround y)) (hx' : x ∈ cubeAround y') : y' = y := by
  obtain ⟨n, hn⟩ := (mem_sublattice_iff i _).1 y.2
  obtain ⟨n', hn'⟩ := (mem_sublattice_iff i _).1 y'.2
  exact Subtype.ext (center_eq_of_mem_interior hN (torusSide_pos hL m) (zero_lt_meshSize hL i)
    (meshSize_le_half_torusSide hL hi) _ _ x n n' hn hn' (cubeAround y)
    (fun z hz => (mem_cubeAround_iff y z).1 hz) hx ((mem_cubeAround_iff y' x).1 hx'))
theorem refinedOffsetSite_apply (hL : 0 < L) {i : ℤ} (n : ℕ) (y : Site L m i) (p : Fin 4 → ℤ)
    (μ : Fin 4) :
    (refinedOffsetSite n y p : FourTorus L m) μ =
      (y : FourTorus L m) μ + (((p μ : ℝ) * meshSize L (i + n) : ℝ) : AddCircle (torusSide L m)) := by
  have hmem : (y : FourTorus L m) ∈ sublattice L m (i + n) := sublattice_mono hL m (by omega) y.2
  have hy : ((y.toSublattice (i + n) : Site L m (i + n)) : FourTorus L m) = y :=
    Classical.epsilon_spec (p := fun x : Site L m (i + n) => (x : FourTorus L m) = y)
      ⟨⟨y, hmem⟩, rfl⟩
  have key : ∀ ν : Fin 4,
      (((p ν • unitStep L m (i + n) ν : Site L m (i + n)) : FourTorus L m) μ) =
        if ν = μ then (((p μ : ℝ) * meshSize L (i + n) : ℝ) : AddCircle (torusSide L m)) else 0 := by
    intro ν
    by_cases h : ν = μ
    · subst h
      rw [if_pos rfl, AddSubgroup.coe_zsmul, Pi.smul_apply]
      show p ν • (pointOnAxis L m ν (meshSize L (i + n)) ν) = _
      rw [pointOnAxis, Pi.single_eq_same, ← AddCircle.coe_zsmul, zsmul_eq_mul]
    · rw [if_neg h, AddSubgroup.coe_zsmul, Pi.smul_apply]
      show p ν • (pointOnAxis L m ν (meshSize L (i + n)) μ) = _
      rw [pointOnAxis, Pi.single_eq_of_ne (Ne.symm h), smul_zero]
  simp only [refinedOffsetSite, offsetSite, AddSubgroup.coe_add, Pi.add_apply, hy]
  congr 1
  rw [AddSubgroup.val_finsetSum, Finset.sum_apply]
  simp only [key]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ μ)]
theorem cubeAround_subset_of_mem_refinedBlock (hL : 0 < L) {i : ℤ} (n : ℕ) (y : Site L m i)
    (p : Fin 4 → ℤ) (hp : p ∈ blockOffsets L n) (y' : Site L m (i + n))
    (hy' : (y' : FourTorus L m) = refinedOffsetSite n y p) : cubeAround y' ⊆ cubeAround y := by
  intro u hu
  rw [mem_cubeAround_iff] at hu ⊢
  have ha' := zero_lt_meshSize hL (i + n)
  have hr := meshSize_eq_pow_mul hL i n
  refine (pi_norm_le_iff_of_nonneg (half_pos (zero_lt_meshSize hL i)).le).2 fun μ => ?_
  have h1 : ‖u μ - (y' : FourTorus L m) μ‖ ≤ meshSize L (i + n) / 2 :=
    (norm_le_pi_norm (u - (y' : FourTorus L m)) μ).trans hu
  have h2 : (u - (y : FourTorus L m)) μ = (u μ - (y' : FourTorus L m) μ) +
      (((p μ : ℝ) * meshSize L (i + n) : ℝ) : AddCircle (torusSide L m)) := by
    rw [hy', refinedOffsetSite_apply hL, Pi.sub_apply]
    abel
  rw [h2]
  refine (norm_add_le _ _).trans ?_
  have h3 : ‖(((p μ : ℝ) * meshSize L (i + n) : ℝ) : AddCircle (torusSide L m))‖ ≤
      |(p μ : ℝ)| * meshSize L (i + n) := by
    refine (addCircle_norm_coe_le_abs _).trans ?_
    rw [abs_mul, abs_of_pos ha']
  have h4 : 2 * |(p μ : ℝ)| ≤ (L : ℝ) ^ n - 1 := by
    have := hp μ
    rw [← Int.cast_abs]
    exact_mod_cast this
  have h5 : |(p μ : ℝ)| * meshSize L (i + n) ≤ ((L : ℝ) ^ n - 1) / 2 * meshSize L (i + n) :=
    mul_le_mul_of_nonneg_right (by linarith only [h4]) ha'.le
  rw [hr]
  linarith only [h1, h3, h5]
theorem abs_offset_le_half {a a' d q h : ℝ} (ha' : 0 < a') (e : d = (q - h) * a')
    (e2 : a = (2 * h + 1) * a') (hq0 : 0 ≤ q) (hq : q ≤ 2 * h) : -(a / 2) ≤ d ∧ d ≤ a / 2 := by
  have h1 : 0 ≤ q * a' := mul_nonneg hq0 ha'.le
  have h2 : q * a' ≤ 2 * h * a' := mul_le_mul_of_nonneg_right hq ha'.le
  subst e e2
  constructor <;> nlinarith
theorem refinedBlock_in_chart (hL : 0 < L) (hodd : Odd L) {i : ℤ} (hi : -(m : ℤ) ≤ i) (n : ℕ)
    {N : ℕ} (hN : torusSide L m = (N : ℝ) * meshSize L i)
    (hdisp : ∀ y : Site L m i,
      refinedBlock n y = (fun p => (refinedOffsetSite n y p : FourTorus L m)) '' blockOffsets L n)
    (y : Site L m i) (v : Fin 4 → ℝ) (hv : torusProj (torusSide L m) v = (y : FourTorus L m)) :
    InjOn (torusProj (torusSide L m)) (centeredBox v (meshSize L i)) ∧
    ∃ T : Fin 4 → Set ℝ,
      (∀ μ, IsProgressionOfMultiples (meshSize L (i + n)) (L ^ n) (T μ)) ∧
      pi univ T ⊆ centeredBox v (meshSize L i) ∧
      torusProj (torusSide L m) '' pi univ T = refinedBlock n y := by
  have ha := zero_lt_meshSize hL i
  have ha' := zero_lt_meshSize hL (i + n)
  have hr := meshSize_eq_pow_mul hL i n
  have hSp := torusSide_pos hL m
  have hhalf := meshSize_le_half_torusSide (m := m) hL hi
  obtain ⟨h, hh⟩ : ∃ h : ℕ, L ^ n = 2 * h + 1 := hodd.pow
  have hrR : (L : ℝ) ^ n = 2 * (h : ℝ) + 1 := by exact_mod_cast hh
  have hrZ : (L : ℤ) ^ n = 2 * (h : ℤ) + 1 := by exact_mod_cast hh
  have ht : ∀ μ, ∃ t : ℤ, v μ = (t : ℝ) * meshSize L i := by
    intro μ
    obtain ⟨n₀, hn₀⟩ := y.2
    have h1 : ((v μ : ℝ) : AddCircle (torusSide L m)) =
        (((n₀ μ : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m)) := by
      rw [← hn₀ μ, ← hv]
      rfl
    have h2 : ((v μ - (n₀ μ : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m)) = 0 := by
      rw [AddCircle.coe_sub, h1, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 h2
    refine ⟨n₀ μ + k * N, ?_⟩
    rw [zsmul_eq_mul, hN] at hk
    push_cast
    linear_combination -hk
  choose t ht using ht
  have hvc : ∀ μ, v μ = (((L : ℤ) ^ n * t μ - h : ℤ) + (h : ℝ)) * meshSize L (i + n) := by
    intro μ
    rw [ht μ, hr]
    push_cast
    ring
  have hoff : ∀ w : Fin 4 → ℝ, w ∈ pi univ (fun μ => {s : ℝ | ∃ q : ℕ, q < L ^ n ∧
      s = ((((L : ℤ) ^ n * t μ - h : ℤ) : ℝ) + (q : ℝ)) * meshSize L (i + n)}) → ∀ μ,
      -(meshSize L i / 2) ≤ w μ - v μ ∧ w μ - v μ ≤ meshSize L i / 2 := by
    intro w hw μ
    obtain ⟨q, hq, hqw⟩ := hw μ (mem_univ μ)
    have hq' : (q : ℝ) ≤ 2 * (h : ℝ) := by
      have : q ≤ 2 * h := by omega
      exact_mod_cast this
    refine abs_offset_le_half (q := q) (h := h) ha' ?_ (by rw [hr, hrR]) (Nat.cast_nonneg q) hq'
    rw [hqw, hvc μ]
    ring
  refine ⟨?_, fun μ => {s | ∃ q : ℕ, q < L ^ n ∧
    s = ((((L : ℤ) ^ n * t μ - h : ℤ) : ℝ) + (q : ℝ)) * meshSize L (i + n)},
    fun μ => ⟨_, rfl⟩, ?_, ?_⟩
  · intro w₁ h₁ w₂ h₂ he
    funext μ
    have b₁ : v μ - meshSize L i / 2 ≤ w₁ μ ∧ w₁ μ ≤ v μ + meshSize L i / 2 := h₁ μ (mem_univ μ)
    have b₂ : v μ - meshSize L i / 2 ≤ w₂ μ ∧ w₂ μ ≤ v μ + meshSize L i / 2 := h₂ μ (mem_univ μ)
    exact eq_of_addCircle_coe_eq_of_abs_sub_le hSp hhalf (congrFun he μ)
      (abs_le.2 ⟨by linarith only [b₁.1, b₂.2], by linarith only [b₁.2, b₂.1]⟩)
  · intro w hw μ _
    obtain ⟨hb₁, hb₂⟩ := hoff w hw μ
    exact ⟨by linarith only [hb₁], by linarith only [hb₂]⟩
  · apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      show _ ∈ cubeAround y ∩ (sublattice L m (i + n) : Set (FourTorus L m))
      refine Set.mem_inter ((mem_cubeAround_iff y _).2 ?_) ?_
      · rw [← hv]
        refine (pi_norm_le_iff_of_nonneg (half_pos ha).le).2 fun μ => ?_
        have e3 : (torusProj (torusSide L m) w - torusProj (torusSide L m) v) μ =
            ((w μ - v μ : ℝ) : AddCircle (torusSide L m)) := by
          rw [AddCircle.coe_sub]
          rfl
        rw [e3]
        exact (addCircle_norm_coe_le_abs _).trans (abs_le.2 (hoff w hw μ))
      · have hq : ∀ μ, ∃ q : ℕ, q < L ^ n ∧
            w μ = ((((L : ℤ) ^ n * t μ - h : ℤ) : ℝ) + (q : ℝ)) * meshSize L (i + n) :=
          fun μ => hw μ (mem_univ μ)
        choose q _ hqw using hq
        refine SetLike.mem_coe.2 ((mem_sublattice_iff _ _).2
          ⟨fun μ => ((L : ℤ) ^ n * t μ - h) + (q μ : ℤ), fun μ => ?_⟩)
        show ((w μ : ℝ) : AddCircle (torusSide L m)) = _
        rw [hqw μ]
        congr 1
        push_cast
        ring
    · intro x hx
      rw [hdisp y] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      have hpb : ∀ μ, -(h : ℤ) ≤ p μ ∧ p μ ≤ h := by
        intro μ
        have := hp μ
        rw [hrZ] at this
        have h1 := abs_le.1 (show |p μ| ≤ h by omega)
        exact h1
      refine ⟨fun μ => v μ + (p μ : ℝ) * meshSize L (i + n), fun μ _ => ?_, ?_⟩
      · refine ⟨(p μ + h).toNat, ?_, ?_⟩
        · have := (hpb μ).2
          have h0 := (hpb μ).1
          rw [hh]
          omega
        · have h0 := (hpb μ).1
          have e : (((p μ + h).toNat : ℕ) : ℝ) = (p μ : ℝ) + h := by
            have : (((p μ + h).toNat : ℕ) : ℤ) = p μ + h := Int.toNat_of_nonneg (by omega)
            exact_mod_cast this
          rw [e]
          show v μ + (p μ : ℝ) * meshSize L (i + n) = _
          rw [hvc μ]
          ring
      · funext μ
        show (((v μ + (p μ : ℝ) * meshSize L (i + n) : ℝ)) : AddCircle (torusSide L m)) =
          (refinedOffsetSite n y p : FourTorus L m) μ
        rw [refinedOffsetSite_apply hL, AddCircle.coe_add, ← hv]
        rfl
theorem fullTrace_im_eq_zero (hLog : Matrices.ComplexMatrix2.UnitaryLogarithmProperties)
    (V : Matrices.ComplexMatrix2) (hV : V ∈ Matrices.ComplexMatrix2.specialUnitary) :
    (Matrices.ComplexMatrix2.fullTrace V).im = 0 := by apply _root_.YangMills.Construction.LatticeProbability.ProbabilitySpaceProof.fullTrace_im_eq_zero <;> assumption
theorem plaquetteHolonomy_mem {j : ℤ} {U : Bond L m j → Matrices.ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j) (p : Plaquette L m j) :
    plaquetteHolonomy U p ∈ Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.PeriodicLattice.plaquetteHolonomy_mem_specialUnitary <;> assumption
theorem traceRealityAndPlaquettes_holds
    (hLog : Matrices.ComplexMatrix2.UnitaryLogarithmProperties) (L m K : ℕ) :
    TraceRealityAndPlaquettes L m K := by
  refine ⟨fullTrace_im_eq_zero hLog, fun U hU => ?_⟩
  have hp : ∀ p : Plaquette L m (K : ℤ),
      ((plaquetteCost U p : ℝ) : ℂ) = plaquetteEnergy U p := by
    intro p
    have him := fullTrace_im_eq_zero hLog _ (plaquetteHolonomy_mem hU p)
    apply Complex.ext
    · simp [plaquetteCost, plaquetteEnergy]
    · simp [plaquetteCost, plaquetteEnergy, him]
  refine ⟨hp, rfl, ?_⟩
  have h := AddMonoidHom.map_finsum_of_injective (Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom
    Complex.ofReal_injective (fun p : Plaquette L m (K : ℤ) => plaquetteCost U p)
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Complex.ofRealHom_eq_coe] at h
  simp only [wilsonAction]
  rw [h]
  exact finsum_congr hp
theorem elementaryLatticeFacts_holds (hPart : BlockPartition.Properties)
    (hStd : StandardPartitionsInUnits)
    (hLat : CoordinateDescription)
    (hLog : Matrices.ComplexMatrix2.UnitaryLogarithmProperties) : ElementaryLatticeFacts := by
  intro s
  have hfac := s.isAdmissible
  have hodd : Odd s.L := hfac.1
  have hL : 0 < s.L := by have := hfac.2; omega
  refine ⟨fun i i' hi hii' => ?_, traceRealityAndPlaquettes_holds hLog _ _ _⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i' = i + n := ⟨(i' - i).toNat, by omega⟩
  have hn : (i + (n : ℤ) - i).toNat = n := by omega
  obtain ⟨hdisp, ⟨hself, -, hdisj, hunion⟩, -⟩ := hPart s.L s.m hfac s.m.pos i n n hi
  obtain ⟨hcov, hreg, -⟩ := ((hStd s).1 i (i + n) hi hii').1
  have hlat := ((hLat s.L s.m hodd hfac.2 s.m.pos).1 i hi).1
  have hN : torusSide s.L s.m = ((2 * halfPeriod s.L s.m i : ℕ) : ℝ) * meshSize s.L i :=
    (div_eq_iff (zero_lt_meshSize hL i).ne').1 hlat
  have hcover : ∀ u : FourTorus s.L s.m, ∃ Q ∈ standardCubePartition s.L s.m i, u ∈ Q :=
    fun u => by
      have : u ∈ ⋃₀ standardCubePartition s.L s.m i := by
        rw [hcov]
        exact mem_univ u
      exact mem_sUnion.1 this
  refine ⟨⟨?_, ?_, ?_⟩, ⟨hcov, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x y
    simp only [_root_.YangMills.Construction.PeriodicLattice.CubeGeometry.torusSupNorm_eq_norm]
    exact norm_add_le x y
  · rintro _ ⟨y, rfl⟩ p hp p' hp'
    rw [_root_.YangMills.Construction.PeriodicLattice.CubeGeometry.torusSupNorm_eq_norm]
    have h1 := (mem_cubeAround_iff y p).1 hp
    have h2 := (mem_cubeAround_iff y p').1 hp'
    have e : p - p' = (p - (y : FourTorus s.L s.m)) - (p' - (y : FourTorus s.L s.m)) := by abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    linarith only [h1, h2]
  · exact fun A B hA hB hcA hcB => exists_setSupDist_eq A B hA hB hcA hcB
  · rintro _ ⟨y, rfl⟩ x hx _ ⟨y', rfl⟩ hx'
    rw [site_eq_of_mem_interior_cubeAround hL hi hN y y' x hx hx']
  · intro X _
    refine eq_univ_of_forall fun u => ?_
    obtain ⟨Q, hQ, huQ⟩ := hcover u
    by_cases hQX : Q ⊆ X
    · exact Or.inl (hQX huQ)
    · exact Or.inr ⟨Q, ⟨hQ, fun h => hQX h.2⟩, huQ⟩
  · intro Q hQ
    obtain ⟨C, hC, hQC⟩ := hreg Q hQ
    apply Subset.antisymm
    · intro u hu
      rw [hQC] at hu
      obtain ⟨Q', hQ', huQ'⟩ := hu
      exact ⟨Q', ⟨hC hQ', by rw [hQC]; exact subset_sUnion_of_mem hQ'⟩, huQ'⟩
    · exact sUnion_subset fun Q' h => h.2
  · rintro _ ⟨y', rfl⟩
    have hy' : (y' : FourTorus s.L s.m) ∈ ⋃ y : Site s.L s.m i, refinedBlock n y := by
      rw [hunion]
      exact y'.2
    obtain ⟨y, hy⟩ := mem_iUnion.1 hy'
    have hy2 := hy
    rw [(hdisp y).1] at hy2
    obtain ⟨p, hp, hpy⟩ := hy2
    have hself' : (y' : FourTorus s.L s.m) ∈ cubeAround y' := by
      rw [mem_cubeAround_iff, sub_self, norm_zero]
      exact (half_pos (zero_lt_meshSize hL (i + n))).le
    refine ⟨cubeAround y, ⟨⟨y, rfl⟩,
      cubeAround_subset_of_mem_refinedBlock hL n y p hp y' hpy.symm⟩, ?_⟩
    rintro _ ⟨⟨y₂, rfl⟩, hsub⟩
    by_contra hne
    have hyy : y₂ ≠ y := fun h => hne (by rw [h])
    have hd : Disjoint (refinedBlock n y₂) (refinedBlock n y) := hdisj hyy
    exact Set.disjoint_left.1 hd (Set.mem_inter (hsub hself') (SetLike.mem_coe.2 y'.2)) hy
  · simp only [BlocksPartitionSublattice, hn]
    exact ⟨fun y => rfl, fun y => ⟨_, hself y⟩, hunion, fun y y' h => hdisj h⟩
  · simp only [BlocksInChart, hn]
    exact fun y v hv => refinedBlock_in_chart hL hodd hi n hN (fun y => (hdisp y).1) y v hv
end YangMills.Construction.PeriodicLattice.CubeGeometry
end
