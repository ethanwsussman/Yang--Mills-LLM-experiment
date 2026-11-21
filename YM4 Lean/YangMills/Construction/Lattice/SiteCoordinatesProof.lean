import YangMills.Construction.Lattice.BlocksInTheCoordinatesOfAFinerLatticeProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
private def gridPoint (L m : ℕ) (j : ℤ) (n : Fin 4 → ℤ) : FourTorus L m :=
  fun μ => (((n μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))
private theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
private theorem meshSize_eq_pow_mul (hL : 0 < L) (j : ℤ) (n : ℕ) :
    meshSize L j = (L : ℝ) ^ n * meshSize L (j + n) := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.meshSize_eq_pow_mul <;> assumption
private theorem halfPeriod_cast (hj : -(m : ℤ) ≤ j) :
    ((halfPeriod L m j : ℕ) : ℝ) = (L : ℝ) ^ ((m : ℤ) + j) := by
  have h : ((((m : ℤ) + j).toNat : ℕ) : ℤ) = (m : ℤ) + j := Int.toNat_of_nonneg (by omega)
  unfold halfPeriod
  push_cast
  rw [← zpow_natCast, h]
private theorem torusSide_eq (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    torusSide L m = ((2 * halfPeriod L m j : ℕ) : ℝ) * meshSize L j := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  push_cast
  rw [halfPeriod_cast hj]
  unfold torusSide meshSize
  rw [mul_assoc, ← zpow_add₀ hL']
  have e : (m : ℤ) + j + -j = m := by ring
  rw [e, zpow_natCast]
abbrev _root_.YangMills.DeltaSharedProofs.p501486 := @torusSide_eq
private theorem halfPeriod_pos (hL : 0 < L) : 0 < halfPeriod L m j := by
  unfold halfPeriod
  exact pow_pos hL _
private theorem gridCoe_eq_zero_iff (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (t : ℤ) :
    (((t : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 ↔
      ((2 * halfPeriod L m j : ℕ) : ℤ) ∣ t := by
  have hs := (meshSize_pos hL j).ne'
  rw [AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [torusSide_eq hL hj, zsmul_eq_mul, ← mul_assoc] at hk
    have h2 : (k : ℝ) * ((2 * halfPeriod L m j : ℕ) : ℝ) = t := mul_right_cancel₀ hs hk
    refine ⟨k, ?_⟩
    have h3 : (t : ℝ) = ((((2 * halfPeriod L m j : ℕ) : ℤ) * k : ℤ) : ℝ) := by
      push_cast at h2 ⊢
      linarith
    exact_mod_cast h3
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    rw [torusSide_eq hL hj, zsmul_eq_mul]
    push_cast
    ring
abbrev _root_.YangMills.DeltaSharedProofs.p501788 := @gridCoe_eq_zero_iff
private theorem gridCoe_eq_iff (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (t t' : ℤ) :
    (((t : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = (((t' : ℝ) * meshSize L j : ℝ) : _) ↔
      t ≡ t' [ZMOD ((2 * halfPeriod L m j : ℕ) : ℤ)] := by
  rw [Int.modEq_iff_dvd, ← gridCoe_eq_zero_iff hL hj]
  push_cast
  rw [sub_mul, AddCircle.coe_sub, sub_eq_zero]
  exact eq_comm
private theorem exists_lift_eq (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (t : ℤ) (v : ℝ)
    (hv : (v : AddCircle (torusSide L m)) = (((t : ℝ) * meshSize L j : ℝ) : _)) :
    ∃ t' : ℤ, t' ≡ t [ZMOD ((2 * halfPeriod L m j : ℕ) : ℤ)] ∧ v = (t' : ℝ) * meshSize L j := by
  have h0 : ((v - (t : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
    rw [AddCircle.coe_sub, hv, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 h0
  refine ⟨t + k * ((2 * halfPeriod L m j : ℕ) : ℤ), ?_, ?_⟩
  · rw [Int.modEq_iff_dvd]
    exact ⟨-k, by ring⟩
  · rw [torusSide_eq hL hj, zsmul_eq_mul] at hk
    push_cast at hk ⊢
    linarith
private theorem coe_sum_unitStep (n : Fin 4 → ℤ) :
    ((∑ μ, n μ • unitStep L m j μ : Site L m j) : FourTorus L m) = gridPoint L m j n := by
  funext ν
  rw [AddSubgroup.val_finsetSum]
  rw [Finset.sum_apply, Finset.sum_eq_single ν]
  · simp [unitStep, pointOnAxis, gridPoint]
  · intro μ _ h
    simp [unitStep, pointOnAxis, Pi.single_eq_of_ne h.symm]
  · simp
private theorem coe_offsetSite (y : Site L m j) (n : Fin 4 → ℤ) :
    ((offsetSite y n : Site L m j) : FourTorus L m) = (y : FourTorus L m) + gridPoint L m j n := by
  unfold offsetSite
  rw [AddSubgroup.coe_add, coe_sum_unitStep]
abbrev _root_.YangMills.DeltaSharedProofs.p500716 := @coe_offsetSite
private theorem offsetSite_eq_iff (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (y : Site L m j)
    (n n' : Fin 4 → ℤ) :
    offsetSite y n = offsetSite y n' ↔
      ∀ μ, n μ ≡ n' μ [ZMOD ((2 * halfPeriod L m j : ℕ) : ℤ)] := by
  rw [← Subtype.coe_inj, coe_offsetSite, coe_offsetSite, add_right_inj,
    funext_iff]
  exact forall_congr' fun μ => gridCoe_eq_iff hL hj _ _
private theorem exists_offsetSite_eq (y x : Site L m j) :
    ∃ n : Fin 4 → ℤ, x = offsetSite y n := by
  obtain ⟨n, hn⟩ := (x - y).2
  refine ⟨n, Subtype.ext ?_⟩
  rw [coe_offsetSite]
  have h : ((x - y : Site L m j) : FourTorus L m) = gridPoint L m j n := funext hn
  rw [← h, AddSubgroup.coe_sub]
  abel
private theorem add_zsmul_unitStep_eq (y : Site L m j) (μ : Fin 4) (t : ℤ) :
    y + t • unitStep L m j μ = offsetSite y (Pi.single μ t) := by
  unfold offsetSite
  congr 1
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ h
    simp [Pi.single_eq_of_ne h]
  · simp
abbrev _root_.YangMills.SharedProofs.p86227 := @add_zsmul_unitStep_eq
private theorem add_zsmul_unitStep_eq_iff (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (y : Site L m j)
    (μ : Fin 4) (t t' : ℤ) :
    y + t • unitStep L m j μ = y + t' • unitStep L m j μ ↔
      t ≡ t' [ZMOD ((2 * halfPeriod L m j : ℕ) : ℤ)] := by
  rw [add_zsmul_unitStep_eq, add_zsmul_unitStep_eq, offsetSite_eq_iff hL hj]
  constructor
  · intro h
    simpa using h μ
  · intro h ν
    by_cases e : ν = μ
    · subst e
      simpa using h
    · simp [Pi.single_eq_of_ne e]
private theorem axisLine_ncard (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (y : Site L m j) (μ : Fin 4) :
    (axisLine y μ).ncard = 2 * halfPeriod L m j := by
  have hM : (0 : ℤ) < ((2 * halfPeriod L m j : ℕ) : ℤ) := by
    have := halfPeriod_pos (m := m) (j := j) hL
    exact_mod_cast (by omega : 0 < 2 * halfPeriod L m j)
  have hset : axisLine y μ = (fun t : ℕ => y + (t : ℤ) • unitStep L m j μ) ''
      (Finset.range (2 * halfPeriod L m j) : Set ℕ) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨(t % ((2 * halfPeriod L m j : ℕ) : ℤ)).toNat, ?_, ?_⟩
      · have h1 := Int.emod_nonneg t hM.ne'
        have h2 := Int.emod_lt_of_pos t hM
        simp only [Finset.coe_range, mem_Iio]
        omega
      · have h1 := Int.emod_nonneg t hM.ne'
        show y + (((t % _).toNat : ℕ) : ℤ) • unitStep L m j μ = _
        rw [Int.toNat_of_nonneg h1, add_zsmul_unitStep_eq_iff hL hj]
        exact Int.mod_modEq _ _
    · rintro ⟨t, -, rfl⟩
      exact ⟨t, rfl⟩
  rw [hset, Set.InjOn.ncard_image, Set.ncard_coe_finset, Finset.card_range]
  intro a ha' b hb' hab
  have h := (add_zsmul_unitStep_eq_iff hL hj y μ _ _).1 hab
  have ha : a < 2 * halfPeriod L m j := Finset.mem_range.1 (Finset.mem_coe.1 ha')
  have hb : b < 2 * halfPeriod L m j := Finset.mem_range.1 (Finset.mem_coe.1 hb')
  have h' : a ≡ b [MOD 2 * halfPeriod L m j] := (Int.natCast_modEq_iff).1 h
  exact Nat.ModEq.eq_of_lt_of_lt h' ha hb
private theorem isMinimalResidue_of_abs_lt {H t : ℤ} (ht : |t| < H) :
    IsMinimalResidue (2 * H) t ∧
      ∀ s : ℤ, s ≡ t [ZMOD 2 * H] → IsMinimalResidue (2 * H) s → s = t := by
  have key : ∀ s : ℤ, s ≡ t [ZMOD 2 * H] → |s| < H → s = t := by
    intro s hs hsH
    have hd : 2 * H ∣ t - s := hs.dvd
    have hlt : |t - s| < 2 * H := by
      have := abs_sub t s
      linarith
    have h0 := Int.eq_zero_of_abs_lt_dvd hd hlt
    omega
  constructor
  · intro s hs
    by_contra hlt'
    have hlt := not_le.1 hlt'
    have hst := key s hs (hlt.trans ht)
    rw [hst] at hlt
    exact lt_irrefl _ hlt
  · intro s hs hl
    exact key s hs (lt_of_le_of_lt (hl t hs.symm) ht)
private theorem exists_isMinimalResidue (M t : ℤ) :
    ∃ s : ℤ, s ≡ t [ZMOD M] ∧ IsMinimalResidue M s := by
  classical
  have hex : ∃ k : ℕ, ∃ s : ℤ, s ≡ t [ZMOD M] ∧ s.natAbs = k :=
    ⟨t.natAbs, t, Int.ModEq.refl t, rfl⟩
  obtain ⟨s, hs, hk⟩ := Nat.find_spec hex
  refine ⟨s, hs, fun u hu => ?_⟩
  have h := Nat.find_min' hex ⟨u, hu.trans hs, rfl⟩
  rw [← hk] at h
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  exact_mod_cast h
private theorem supNormVec_mono {v w : Fin 4 → ℝ} (h : ∀ μ, |w μ| ≤ |v μ|) :
    TorusMetric.supNormVec w ≤ TorusMetric.supNormVec v :=
  Finset.sup'_le _ _ fun μ _ => (h μ).trans (Finset.le_sup' (fun ν => |v ν|) (Finset.mem_univ μ))
private theorem abs_le_supNormVec (v : Fin 4 → ℝ) (μ : Fin 4) :
    |v μ| ≤ TorusMetric.supNormVec v := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.abs_le_supNormVec <;> assumption
private theorem supNormVec_mul_const (a : Fin 4 → ℝ) {s : ℝ} (hs : 0 < s) :
    TorusMetric.supNormVec (fun μ => a μ * s) = s * TorusMetric.supNormVec a := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun μ _ => ?_
    rw [abs_mul, abs_of_pos hs, mul_comm]
    exact mul_le_mul_of_nonneg_left (abs_le_supNormVec a μ) hs.le
  · obtain ⟨μ, -, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun ν => |a ν|)
    have h' : TorusMetric.supNormVec a = |a μ| := h
    rw [h']
    have := abs_le_supNormVec (fun ν => a ν * s) μ
    simp only [abs_mul, abs_of_pos hs] at this
    linarith
private theorem norms_gridPoint_of_minimal (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (n : Fin 4 → ℤ)
    (hn : ∀ μ, IsMinimalResidue ((2 * halfPeriod L m j : ℕ) : ℤ) (n μ)) :
    TorusMetric.torusSupNorm (gridPoint L m j n) =
        meshSize L j * TorusMetric.supNormVec (fun μ => (n μ : ℝ)) ∧
      TorusMetric.torusL1Norm (gridPoint L m j n) =
        meshSize L j * TorusMetric.l1NormVec (fun μ => (n μ : ℝ)) := by
  have hs := meshSize_pos hL j
  set w : Fin 4 → ℝ := fun μ => (n μ : ℝ) * meshSize L j with hw
  have hcov : TorusMetric.torusProj (torusSide L m) w = gridPoint L m j n := rfl
  have hlow : ∀ v : Fin 4 → ℝ, TorusMetric.torusProj (torusSide L m) v = gridPoint L m j n →
      ∀ μ, |w μ| ≤ |v μ| := by
    intro v hv μ
    obtain ⟨t', ht, hvt⟩ := exists_lift_eq hL hj (n μ) (v μ) (congrFun hv μ)
    have h1 : ((|n μ| : ℤ) : ℝ) ≤ ((|t'| : ℤ) : ℝ) := by exact_mod_cast hn μ t' ht
    rw [Int.cast_abs, Int.cast_abs] at h1
    rw [hvt, hw]
    simp only [abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_right h1 hs.le
  constructor
  · rw [← supNormVec_mul_const _ hs]
    apply le_antisymm
    · refine csInf_le ⟨0, ?_⟩ ⟨w, hcov, ?_⟩
      · rintro _ ⟨v, -, rfl⟩
        exact (abs_nonneg _).trans (abs_le_supNormVec v 0)
      · rfl
    · refine le_csInf ⟨_, w, hcov, rfl⟩ ?_
      rintro _ ⟨v, hv, rfl⟩
      exact supNormVec_mono (hlow v hv)
  · have hsum : TorusMetric.l1NormVec w =
        meshSize L j * TorusMetric.l1NormVec (fun μ => (n μ : ℝ)) := by
      simp only [TorusMetric.l1NormVec, hw, abs_mul, abs_of_pos hs, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [← hsum]
    apply le_antisymm
    · refine csInf_le ⟨0, ?_⟩ ⟨w, hcov, rfl⟩
      rintro _ ⟨v, -, rfl⟩
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    · refine le_csInf ⟨_, w, hcov, rfl⟩ ?_
      rintro _ ⟨v, hv, rfl⟩
      exact Finset.sum_le_sum fun μ _ => hlow v hv μ
private theorem sublatticeCoordinates_holds (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    SublatticeCoordinates L m j := by
  have hH := halfPeriod_pos (m := m) (j := j) hL
  refine ⟨?_, by omega, fun j' h => sublattice_mono hL m h, fun y x => exists_offsetSite_eq y x,
    fun y n n' => offsetSite_eq_iff hL hj y n n', fun y μ => axisLine_ncard hL hj y μ,
    ?_, ?_⟩
  · rw [torusSide_eq hL hj]
    exact mul_div_cancel_right₀ _ (meshSize_pos hL j).ne'
  · intro t ht
    have := isMinimalResidue_of_abs_lt ht
    push_cast
    exact this
  · intro y n hn
    rw [coe_offsetSite, add_sub_cancel_left]
    exact norms_gridPoint_of_minimal hL hj n hn
private theorem coe_toSublattice {j' : ℤ} (y : Site L m j) (h : (y : FourTorus L m) ∈ sublattice L m j') :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.coe_toSublattice <;> assumption
private theorem zsmul_pointOnAxis (a : ℤ) (μ : Fin 4) (t : ℝ) :
    a • pointOnAxis L m μ t = pointOnAxis L m μ ((a : ℝ) * t) := by
  funext ν
  by_cases e : ν = μ
  · subst e
    simp [pointOnAxis]
  · simp [pointOnAxis, Pi.single_eq_of_ne e]
abbrev _root_.YangMills.SharedProofs.p34729 := @zsmul_pointOnAxis
private theorem abs_orientedLength (hL : 0 < L) (b : Bond L m j) :
    |b.orientedLength| = meshSize L j := by
  unfold Bond.orientedLength
  split_ifs
  · exact abs_of_pos (meshSize_pos hL j)
  · rw [abs_neg]
    exact abs_of_pos (meshSize_pos hL j)
private theorem levelUnitCoordinates_holds (hL : 0 < L) {K k : ℕ} (hk : k ≤ K) :
    LevelUnitCoordinates L m K k := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hj : -(m : ℤ) ≤ levelDepth K k := by
    simp only [levelDepth]
    omega
  have hhalf : halfPeriod L m (levelDepth K k) = L ^ (m + K - k) := by
    unfold halfPeriod
    congr 1
    simp only [levelDepth]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold toLevelUnits torusSide
    have e : ((m + K - k : ℕ) : ℤ) = levelDepth K k + m := by
      simp only [levelDepth]
      omega
    rw [← zpow_natCast (L : ℝ) (m + K - k), e, zpow_add₀ hL', zpow_natCast]
    ring
  · intro y μ
    rw [axisLine_ncard hL hj y μ, hhalf]
  · intro i _ b
    rw [abs_orientedLength hL]
    unfold toLevelUnits meshSize
    rw [← zpow_add₀ hL']
    congr 1
    simp only [levelDepth]
    ring
  · intro i hki _
    exact sublattice_mono hL m (by simp only [levelDepth]; omega)
  · intro _ c μ h
    have hle : levelDepth K (k + 1) ≤ levelDepth K k := by
      simp only [levelDepth]
      omega
    apply Subtype.ext
    rw [AddSubgroup.coe_add, coe_toSublattice _ (sublattice_mono hL m hle c.target.2),
      coe_toSublattice _ (sublattice_mono hL m hle c.source.2)]
    have h1 : (c.target : FourTorus L m) - c.source =
        pointOnAxis L m μ (meshSize L (levelDepth K (k + 1))) := by
      rw [← AddSubgroup.coe_sub, h]
      rfl
    have h3 : ((L : ℤ) : ℝ) * meshSize L (levelDepth K k) = meshSize L (levelDepth K (k + 1)) := by
      have e := meshSize_eq_pow_mul hL (levelDepth K (k + 1)) 1
      have e2 : levelDepth K (k + 1) + ((1 : ℕ) : ℤ) = levelDepth K k := by
        simp only [levelDepth]
        push_cast
        ring
      rw [e2, pow_one] at e
      rw [e]
      simp
    have h2 : (((L : ℤ) • unitStep L m (levelDepth K k) μ : Site L m (levelDepth K k)) : FourTorus L m) =
        pointOnAxis L m μ (meshSize L (levelDepth K (k + 1))) := by
      rw [AddSubgroup.coe_zsmul]
      show (L : ℤ) • pointOnAxis L m μ (meshSize L (levelDepth K k)) = _
      rw [zsmul_pointOnAxis, h3]
    rw [h2, ← h1]
    abel
private theorem coe_mem_finer_sublattice (hL : 0 < L) (n : ℕ) (y : Site L m j) :
    (y : FourTorus L m) ∈ sublattice L m (j + n) :=
  sublattice_mono hL m (by omega) y.2
private theorem coe_refinedOffsetSite (hL : 0 < L) (n : ℕ) (y : Site L m j) (p : Fin 4 → ℤ) :
    ((refinedOffsetSite n y p : Site L m (j + n)) : FourTorus L m) =
      (y : FourTorus L m) + gridPoint L m (j + n) p := by
  unfold refinedOffsetSite
  rw [coe_offsetSite, coe_toSublattice _ (coe_mem_finer_sublattice hL n y)]
private theorem odd_natCast_pow (hodd : Odd L) (n : ℕ) : Odd ((L : ℤ) ^ n) :=
  (hodd.natCast).pow
private theorem pow_le_halfPeriod (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (n : ℕ) :
    L ^ n ≤ halfPeriod L m (j + n) := by
  unfold halfPeriod
  exact Nat.pow_le_pow_right hL (by omega)
private theorem mem_refinedBlock_iff (hodd : Odd L) (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (n : ℕ)
    (y : Site L m j) (z : FourTorus L m) :
    z ∈ refinedBlock n y ↔
      ∃ p ∈ blockOffsets L n, z = (y : FourTorus L m) + gridPoint L m (j + n) p := by
  have hs := meshSize_pos hL (j + n)
  have hJ : -(m : ℤ) ≤ j + n := by omega
  have hsj := meshSize_eq_pow_mul hL j n
  constructor
  · rintro ⟨hcube, hz⟩
    obtain ⟨n0, hn0⟩ := exists_offsetSite_eq (y.toSublattice (j + n)) (⟨z, hz⟩ : Site L m (j + n))
    choose p hp hleast using
      fun μ => exists_isMinimalResidue ((2 * halfPeriod L m (j + n) : ℕ) : ℤ) (n0 μ)
    have hsame : offsetSite (y.toSublattice (j + n)) p =
        offsetSite (y.toSublattice (j + n)) n0 :=
      (offsetSite_eq_iff hL hJ _ _ _).2 hp
    have hzp : z = (y : FourTorus L m) + gridPoint L m (j + n) p := by
      have h1 := congrArg Subtype.val (hn0.trans hsame.symm)
      rw [coe_offsetSite, coe_toSublattice _ (coe_mem_finer_sublattice hL n y)] at h1
      exact h1
    refine ⟨p, ?_, hzp⟩
    have hsup : TorusMetric.torusSupNorm (z - (y : FourTorus L m)) ≤ meshSize L j / 2 := hcube
    rw [hzp, add_sub_cancel_left, (norms_gridPoint_of_minimal hL hJ p hleast).1] at hsup
    intro μ
    show 2 * |p μ| ≤ (L : ℤ) ^ n - 1
    have h1 : |(p μ : ℝ)| ≤ TorusMetric.supNormVec (fun ν => (p ν : ℝ)) :=
      abs_le_supNormVec (fun ν => (p ν : ℝ)) μ
    have h2 : meshSize L (j + n) * |(p μ : ℝ)| ≤ (L : ℝ) ^ n * meshSize L (j + n) / 2 := by
      rw [← hsj]
      exact (mul_le_mul_of_nonneg_left h1 hs.le).trans hsup
    have h3 : 2 * |(p μ : ℝ)| ≤ (L : ℝ) ^ n := by
      have h5 : meshSize L (j + n) * (2 * |(p μ : ℝ)|) ≤ meshSize L (j + n) * (L : ℝ) ^ n := by
        linarith
      exact le_of_mul_le_mul_left h5 hs
    have h4 : 2 * |p μ| ≤ (L : ℤ) ^ n := by exact_mod_cast h3
    obtain ⟨c, hc⟩ := odd_natCast_pow hodd n
    omega
  · rintro ⟨p, hp, rfl⟩
    refine ⟨?_, ?_⟩
    · show TorusMetric.torusSupNorm _ ≤ meshSize L j / 2
      rw [add_sub_cancel_left]
      have hle : TorusMetric.supNormVec (fun μ => (p μ : ℝ) * meshSize L (j + n)) ≤
          meshSize L j / 2 := by
        refine Finset.sup'_le _ _ fun μ _ => ?_
        rw [abs_mul, abs_of_pos hs, hsj]
        have h1 : 2 * |p μ| ≤ (L : ℤ) ^ n - 1 := hp μ
        have h2 : 2 * |(p μ : ℝ)| ≤ (L : ℝ) ^ n - 1 := by exact_mod_cast h1
        have h3 : |(p μ : ℝ)| ≤ (L : ℝ) ^ n / 2 := by linarith
        calc |(p μ : ℝ)| * meshSize L (j + n) ≤ (L : ℝ) ^ n / 2 * meshSize L (j + n) :=
              mul_le_mul_of_nonneg_right h3 hs.le
          _ = (L : ℝ) ^ n * meshSize L (j + n) / 2 := by ring
      refine le_trans (csInf_le ⟨0, ?_⟩
        ⟨fun μ => (p μ : ℝ) * meshSize L (j + n), rfl, rfl⟩) hle
      rintro _ ⟨v, -, rfl⟩
      exact (abs_nonneg _).trans (abs_le_supNormVec v 0)
    · show _ ∈ sublattice L m (j + n)
      rw [← coe_refinedOffsetSite hL n y p]
      exact (refinedOffsetSite n y p).2
private theorem gridPoint_injOn (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (n : ℕ) {p p' : Fin 4 → ℤ}
    (hp : p ∈ blockOffsets L n) (hp' : p' ∈ blockOffsets L n)
    (h : gridPoint L m (j + n) p = gridPoint L m (j + n) p') : p = p' := by
  have hJ : -(m : ℤ) ≤ j + n := by omega
  funext μ
  have h1 := (gridCoe_eq_iff hL hJ (p μ) (p' μ)).1 (congrFun h μ)
  have hd : ((2 * halfPeriod L m (j + n) : ℕ) : ℤ) ∣ p' μ - p μ := h1.dvd
  have hb : |p' μ - p μ| < ((2 * halfPeriod L m (j + n) : ℕ) : ℤ) := by
    have h2 : (L : ℤ) ^ n ≤ (halfPeriod L m (j + n) : ℤ) := by
      exact_mod_cast pow_le_halfPeriod hL hj n
    have h3 : 2 * |p μ| ≤ (L : ℤ) ^ n - 1 := hp μ
    have h4 : 2 * |p' μ| ≤ (L : ℤ) ^ n - 1 := hp' μ
    have h5 := abs_sub (p' μ) (p μ)
    have h6 := abs_nonneg (p μ)
    push_cast
    linarith
  have h0 := Int.eq_zero_of_abs_lt_dvd hd hb
  omega
private theorem ncard_blockOffsets (hodd : Odd L) (n : ℕ) :
    (blockOffsets L n).ncard = L ^ (4 * n) := by
  obtain ⟨h, hh⟩ := hodd.pow (n := n)
  have hh' : (L : ℤ) ^ n = 2 * (h : ℤ) + 1 := by exact_mod_cast hh
  have hset : blockOffsets L n = ((Fintype.piFinset fun _ : Fin 4 =>
      Finset.Icc (-(h : ℤ)) h : Finset (Fin 4 → ℤ)) : Set (Fin 4 → ℤ)) := by
    ext p
    simp only [blockOffsets, Set.mem_ofPred_eq, Finset.mem_coe, Fintype.mem_piFinset,
      Finset.mem_Icc, hh']
    refine forall_congr' fun μ => ?_
    rw [← abs_le]
    omega
  rw [hset, Set.ncard_coe_finset, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have e : ((h : ℤ) + 1 - -(h : ℤ)).toNat = L ^ n := by
    rw [hh]
    omega
  rw [e, ← pow_mul, mul_comm]
abbrev _root_.YangMills.SharedProofs.p29861 := @ncard_blockOffsets
private theorem refinedBlockCoordinates_holds (hodd : Odd L) (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (n : ℕ) : RefinedBlockCoordinates L m j n := by
  intro y
  have himg : ∀ n : ℕ, refinedBlock n y =
      (fun p => (y : FourTorus L m) + gridPoint L m (j + n) p) '' blockOffsets L n := by
    intro n
    ext z
    rw [mem_refinedBlock_iff hodd hL hj]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
  refine ⟨coe_mem_finer_sublattice hL n y, ?_, ?_, ?_, ?_⟩
  · rw [himg n]
    exact image_congr fun p _ => (coe_refinedOffsetSite hL n y p).symm
  · intro p hp p' hp' h
    apply gridPoint_injOn hL hj n hp hp'
    have h1 := congrArg Subtype.val h
    have h2 : (y : FourTorus L m) + gridPoint L m (j + n) p =
        (y : FourTorus L m) + gridPoint L m (j + n) p' := by
      rw [← coe_refinedOffsetSite hL n y p, ← coe_refinedOffsetSite hL n y p']
      exact h1
    exact add_left_cancel h2
  · rw [himg n, Set.InjOn.ncard_image, ncard_blockOffsets hodd]
    intro p hp p' hp' h
    exact gridPoint_injOn hL hj n hp hp' (add_left_cancel h)
  · have h0 : blockOffsets L 0 = {0} := by
      ext p
      constructor
      · intro hp
        funext μ
        have h1 : 2 * |p μ| ≤ (L : ℤ) ^ 0 - 1 := hp μ
        have h2 := abs_nonneg (p μ)
        have h3 : |p μ| = 0 := by
          rw [pow_zero] at h1
          omega
        simpa using h3
      · rintro rfl μ
        simp
    have hz : gridPoint L m (j + ((0 : ℕ) : ℤ)) 0 = 0 := by
      funext μ
      simp [gridPoint]
    rw [himg 0, h0, image_singleton, hz, add_zero]
private theorem exists_split_of_odd {A B p : ℤ} (hA : Odd A) (hB : Odd B) (hB0 : 0 < B)
    (hp : 2 * |p| ≤ A * B - 1) :
    ∃ q r : ℤ, p = B * q + r ∧ 2 * |q| ≤ A - 1 ∧ 2 * |r| ≤ B - 1 := by
  obtain ⟨g, hg⟩ := hA
  obtain ⟨h, hh⟩ := hB
  have e0 := Int.emod_add_mul_ediv (p + h) B
  have e1 := Int.emod_nonneg (p + h) hB0.ne'
  have e2 := Int.emod_lt_of_pos (p + h) hB0
  generalize (p + h) % B = ρ at e0 e1 e2
  generalize (p + h) / B = q at e0
  have hr : |ρ - h| ≤ h := abs_le.2 ⟨by omega, by omega⟩
  refine ⟨q, ρ - h, by linarith, ?_, by omega⟩
  by_contra hq
  have hq' : g + 1 ≤ |q| := by omega
  have e3 : B * |q| = |p - (ρ - h)| := by
    rw [show p - (ρ - h) = B * q by linarith, abs_mul, abs_of_pos hB0]
  have e4 := abs_sub p (ρ - h)
  have e5 : B * (g + 1) ≤ B * |q| := mul_le_mul_of_nonneg_left hq' hB0.le
  subst hg
  nlinarith
private theorem combine_split {A B q r : ℤ} (hB0 : 0 < B) (hq : 2 * |q| ≤ A - 1)
    (hr : 2 * |r| ≤ B - 1) : 2 * |B * q + r| ≤ A * B - 1 := by
  have e1 := abs_add_le (B * q) r
  rw [abs_mul, abs_of_pos hB0] at e1
  have e2 : B * (2 * |q|) ≤ B * (A - 1) := mul_le_mul_of_nonneg_left hq hB0.le
  nlinarith
private theorem cancel_split {B q q' r r' : ℤ} (hB0 : 0 < B) (hr : 2 * |r| ≤ B - 1)
    (hr' : 2 * |r'| ≤ B - 1) (h : B * q + r = B * q' + r') : q = q' := by
  have hd : B ∣ r' - r := ⟨q - q', by linear_combination -h⟩
  have hb : |r' - r| < B := by
    have e1 := abs_sub r' r
    linarith
  have h0 := Int.eq_zero_of_abs_lt_dvd hd hb
  have h1 : B * (q - q') = 0 := by linear_combination h + h0
  have h2 := (mul_eq_zero.1 h1).resolve_left hB0.ne'
  omega
private theorem gridPoint_add (hL : 0 < L) (J : ℤ) (a b : ℕ) (q r : Fin 4 → ℤ) :
    gridPoint L m (J + a) q + gridPoint L m (J + a + b) r =
      gridPoint L m (J + a + b) (fun μ => (L : ℤ) ^ b * q μ + r μ) := by
  funext μ
  show (((q μ : ℝ) * meshSize L (J + a) : ℝ) : AddCircle (torusSide L m)) +
      (((r μ : ℝ) * meshSize L (J + a + b) : ℝ) : AddCircle (torusSide L m)) = _
  have e : (q μ : ℝ) * meshSize L (J + a) + (r μ : ℝ) * meshSize L (J + a + b) =
      (((L : ℤ) ^ b * q μ + r μ : ℤ) : ℝ) * meshSize L (J + a + b) := by
    rw [meshSize_eq_pow_mul hL (J + a) b]
    push_cast
    ring
  rw [← AddCircle.coe_add, e]
  rfl
private theorem refinedBlock_add (hodd : Odd L) (hL : 0 < L) {J : ℤ} (hJ : -(m : ℤ) ≤ J)
    (a b : ℕ) (y : Site L m J) :
    refinedBlock (a + b) y =
        ⋃ x ∈ (sitesIn (refinedBlock a y) : Set (Site L m (J + (a : ℤ)))), refinedBlock b x ∧
      (sitesIn (refinedBlock a y) : Set (Site L m (J + (a : ℤ)))).PairwiseDisjoint
        (refinedBlock b) := by
  have hJa : -(m : ℤ) ≤ J + a := by omega
  have idx : J + ((a + b : ℕ) : ℤ) = J + a + b := by
    push_cast
    ring
  have hB0 : (0 : ℤ) < (L : ℤ) ^ b := pow_pos (by exact_mod_cast hL) b
  have memAB : ∀ z : FourTorus L m, z ∈ refinedBlock (a + b) y ↔
      ∃ p ∈ blockOffsets L (a + b), z = (y : FourTorus L m) + gridPoint L m (J + a + b) p := by
    intro z
    rw [mem_refinedBlock_iff hodd hL hJ, idx]
  have hcomb : ∀ {q r : Fin 4 → ℤ}, q ∈ blockOffsets L a → r ∈ blockOffsets L b →
      (fun μ => (L : ℤ) ^ b * q μ + r μ) ∈ blockOffsets L (a + b) := by
    intro q r hq hr μ
    show 2 * |(L : ℤ) ^ b * q μ + r μ| ≤ (L : ℤ) ^ (a + b) - 1
    rw [pow_add]
    exact combine_split hB0 (hq μ) (hr μ)
  constructor
  · ext z
    simp only [mem_iUnion, exists_prop]
    constructor
    · intro hz
      obtain ⟨p, hp, rfl⟩ := (memAB _).1 hz
      have hsplit : ∀ μ, ∃ q r : ℤ, p μ = (L : ℤ) ^ b * q + r ∧ 2 * |q| ≤ (L : ℤ) ^ a - 1 ∧
          2 * |r| ≤ (L : ℤ) ^ b - 1 := fun μ =>
        exists_split_of_odd (odd_natCast_pow hodd a) (odd_natCast_pow hodd b) hB0
          (by have h1 : 2 * |p μ| ≤ (L : ℤ) ^ (a + b) - 1 := hp μ
              rwa [pow_add] at h1)
      choose q r hqr hq hr using hsplit
      have hpq : p = fun μ => (L : ℤ) ^ b * q μ + r μ := funext hqr
      refine ⟨refinedOffsetSite a y q, ?_, ?_⟩
      · show ((refinedOffsetSite a y q : Site L m (J + a)) : FourTorus L m) ∈ refinedBlock a y
        rw [mem_refinedBlock_iff hodd hL hJ]
        exact ⟨q, hq, coe_refinedOffsetSite hL a y q⟩
      · rw [mem_refinedBlock_iff hodd hL hJa]
        refine ⟨r, hr, ?_⟩
        rw [coe_refinedOffsetSite hL, add_assoc (y : FourTorus L m), gridPoint_add hL, hpq]
    · rintro ⟨x, hx, hz⟩
      obtain ⟨q, hq, hxq⟩ := (mem_refinedBlock_iff hodd hL hJ a y _).1 hx
      obtain ⟨r, hr, rfl⟩ := (mem_refinedBlock_iff hodd hL hJa b x _).1 hz
      refine (memAB _).2 ⟨_, hcomb hq hr, ?_⟩
      rw [hxq, add_assoc (y : FourTorus L m), gridPoint_add hL]
  · intro x hx x' hx' hne
    refine Set.disjoint_left.2 fun z hz hz' => hne ?_
    obtain ⟨q, hq, hxq⟩ := (mem_refinedBlock_iff hodd hL hJ a y _).1 hx
    obtain ⟨q', hq', hxq'⟩ := (mem_refinedBlock_iff hodd hL hJ a y _).1 hx'
    obtain ⟨r, hr, hzr⟩ := (mem_refinedBlock_iff hodd hL hJa b x _).1 hz
    obtain ⟨r', hr', hzr'⟩ := (mem_refinedBlock_iff hodd hL hJa b x' _).1 hz'
    have e : (y : FourTorus L m) + gridPoint L m (J + a + b) (fun μ => (L : ℤ) ^ b * q μ + r μ) =
        (y : FourTorus L m) + gridPoint L m (J + a + b) (fun μ => (L : ℤ) ^ b * q' μ + r' μ) := by
      rw [← gridPoint_add hL J a b q r, ← gridPoint_add hL J a b q' r', ← add_assoc, ← add_assoc,
        ← hxq, ← hxq', ← hzr, ← hzr']
    have hu := gridPoint_injOn (n := a + b) hL hJ (hcomb hq hr) (hcomb hq' hr')
      (by rw [idx]; exact add_left_cancel e)
    have hqq : q = q' := funext fun μ =>
      cancel_split hB0 (hr μ) (hr' μ) (congrFun hu μ)
    apply Subtype.ext
    rw [hxq, hxq', hqq]
theorem coordinateDescription_holds : CoordinateDescription := by
  intro L m hodd hL13 _
  have hL : 0 < L := by omega
  refine ⟨fun j hj => sublatticeCoordinates_holds hL hj,
    fun K k _ hk => levelUnitCoordinates_holds hL hk,
    fun j n hj => refinedBlockCoordinates_holds hodd hL hj n, ?_⟩
  intro K k i j _ hji _ hkK y
  have hJ : -(m : ℤ) ≤ levelDepth K k := by
    simp only [levelDepth]
    omega
  generalize hA : i - j = a
  obtain rfl : i = a + j := by omega
  exact refinedBlock_add hodd hL hJ a j y
end YangMills.Construction.PeriodicLattice
