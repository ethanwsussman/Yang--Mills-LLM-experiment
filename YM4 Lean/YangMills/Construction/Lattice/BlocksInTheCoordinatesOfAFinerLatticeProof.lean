import YangMills.Construction.Averaging.LayerwiseAveragingStandingData
import YangMills.Construction.Lattice.LevelCubesAndBlocks
import YangMills.Construction.Lattice.SiteCoordinates
import Mathlib
import YangMills.Construction.LawInAState.TheLeastTorusLawUnderLatticeIsometriesProof
set_option autoImplicit false

section
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.TorusMetric
def coordinatePoint {L m : ℕ} (s : ℤ) (y : FourTorus L m) (p : Fin 4 → ℤ) : FourTorus L m :=
  y + ∑ μ, pointOnAxis L m μ ((p μ : ℝ) * meshSize L s)
def axisSiteCount (L m : ℕ) (s : ℤ) : ℕ := 2 * halfPeriod L m s
def FinerLatticeAroundSite (L m : ℕ) (t s : ℤ) (n : ℕ) : Prop :=
  meshSize L t = (L : ℝ) ^ n * meshSize L s ∧
  torusSide L m = (axisSiteCount L m s : ℝ) * meshSize L s ∧
  torusSide L m = 2 * (L : ℝ) ^ ((m : ℤ) + t) * meshSize L t ∧
  sublattice L m t ≤ sublattice L m s ∧
  (∀ y : Site L m t, ∀ x ∈ sublattice L m s,
    (∃ p : Fin 4 → ℤ, x = coordinatePoint s (y : FourTorus L m) p ∧
      ∀ μ, 2 * |p μ| ≤ (axisSiteCount L m s : ℤ)) ∧
    (∀ p p' : Fin 4 → ℤ, x = coordinatePoint s (y : FourTorus L m) p →
      x = coordinatePoint s (y : FourTorus L m) p' →
        ∀ μ, p μ ≡ p' μ [ZMOD (axisSiteCount L m s : ℤ)]) ∧
    (∀ p : Fin 4 → ℤ, x = coordinatePoint s (y : FourTorus L m) p →
      (∀ μ, 2 * |p μ| ≤ (axisSiteCount L m s : ℤ)) →
        TorusMetric.torusSupNorm (x - (y : FourTorus L m)) = meshSize L s * TorusMetric.supNormVec fun μ => (p μ : ℝ))) ∧
  ∀ y y' : Site L m t, y ≠ y' →
    meshSize L t ≤ TorusMetric.torusSupNorm ((y : FourTorus L m) - (y' : FourTorus L m))
def RefinedBlockAroundCentre (L m : ℕ) (t s : ℤ) (n : ℕ) : Prop :=
  ∀ y : Site L m t,
    refinedBlock n y = coordinatePoint s (y : FourTorus L m) '' blockOffsets L n ∧
    InjOn (coordinatePoint s (y : FourTorus L m)) (blockOffsets L n) ∧
    (refinedBlock n y).ncard = L ^ (4 * n) ∧
    (∀ x ∈ refinedBlock n y, TorusMetric.torusSupNorm (x - (y : FourTorus L m)) < meshSize L t / 2) ∧
    (y : FourTorus L m) ∈ refinedBlock n y ∧
    refinedBlock 0 y = {(y : FourTorus L m)} ∧
    refinedBlock n y ∩ (sublattice L m t : Set (FourTorus L m)) = {(y : FourTorus L m)}
def RefinedBlocksCover (L m : ℕ) (t s : ℤ) (n : ℕ) : Prop :=
  (∀ x ∈ sublattice L m s,
    (∃! y' : Site L m t, x ∈ cubeAround y') ∧ ∃! y' : Site L m t, x ∈ refinedBlock n y') ∧
  ∀ (x : FourTorus L m) (y' y'' : Site L m t) (ε : ℤ) (μ : Fin 4), (ε = 1 ∨ ε = -1) →
    x ∈ refinedBlock n y' →
    x + pointOnAxis L m μ ((ε : ℝ) * meshSize L s) ∈ refinedBlock n y'' → y'' ≠ y' →
      (y'' : FourTorus L m) = (y' : FourTorus L m) + pointOnAxis L m μ ((ε : ℝ) * meshSize L t)
def RefinedBlocksInCoordinates (L m : ℕ) (t s : ℤ) (n : ℕ) : Prop :=
  s = t + n ∧ FinerLatticeAroundSite L m t s n ∧ RefinedBlockAroundCentre L m t s n ∧
    RefinedBlocksCover L m t s n
def LevelSublatticesInCoordinates (L m K i j : ℕ) : Prop :=
  RefinedBlocksInCoordinates L m (levelDepth K j) (levelDepth K i) (j - i) ∧
  (∀ y : SiteAtLevel L m K j, cubeAtLevel y = cubeAround y ∧
    blockAtLevel i y = refinedBlock (j - i) y) ∧
  axisSiteCount L m (levelDepth K i) = 2 * L ^ (m + K - i) ∧
  2 * L ≤ 2 * L ^ (m + K - i) ∧
  (∀ (y : SiteAtLevel L m K i) (μ : Fin 4),
    (axisLine y μ).ncard = axisSiteCount L m (levelDepth K i)) ∧
  sublattice L m (levelDepth K j) ≤ sublattice L m (levelDepth K i)
def MeshesAndSideInLevelUnits (L m K k : ℕ) : Prop :=
  (∀ i : ℕ, i ≤ K →
    toLevelUnits L K k (meshSize L (levelDepth K i)) = (L : ℝ) ^ ((i : ℤ) - (k : ℤ))) ∧
  toLevelUnits L K k (meshSize L (levelDepth K 0)) = finestMeshInLevelUnits L k ∧
  toLevelUnits L K k (torusSide L m) = 2 * (L : ℝ) ^ (m + K - k)
def RefinedBlockCoordinatesHold : Prop :=
  ∀ L K m : ℕ, Averaging.LayerwiseParameters 4 2 L K m Matrices.ComplexMatrix2.specialUnitary
      (torusSide L m) →
    (∀ (t : ℤ) (n : ℕ), -(m : ℤ) ≤ t → RefinedBlocksInCoordinates L m t (t + n) n) ∧
    (∀ i j : ℕ, i ≤ j → j ≤ K → LevelSublatticesInCoordinates L m K i j) ∧
    ∀ k : ℕ, k ≤ K → MeshesAndSideInLevelUnits L m K k
end YangMills.Construction.PeriodicLattice
end
end

open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof
variable {L m : ℕ}
theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem meshSize_eq_pow_mul (hL : 0 < L) (t : ℤ) (n : ℕ) :
    meshSize L t = (L : ℝ) ^ n * meshSize L (t + n) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold meshSize
  rw [← zpow_natCast, ← zpow_add₀ hL']
  congr 1
  ring
theorem coordinatePoint_apply (s : ℤ) (y : FourTorus L m) (p : Fin 4 → ℤ) (ν : Fin 4) :
    coordinatePoint s y p ν =
      y ν + (((p ν : ℝ) * meshSize L s : ℝ) : AddCircle (torusSide L m)) := by
  unfold coordinatePoint
  rw [Pi.add_apply, Finset.sum_apply, Finset.sum_eq_single ν]
  · simp [pointOnAxis]
  · intro μ _ h
    simp [pointOnAxis, Pi.single_eq_of_ne h.symm]
  · simp
theorem coe_offsetSite {s : ℤ} (y : Site L m s) (p : Fin 4 → ℤ) :
    ((offsetSite y p : Site L m s) : FourTorus L m) =
      coordinatePoint s (y : FourTorus L m) p := by
  funext ν
  rw [coordinatePoint_apply]
  unfold offsetSite
  rw [AddSubgroup.coe_add, Pi.add_apply, AddSubgroup.val_finsetSum, Finset.sum_apply,
    Finset.sum_eq_single ν]
  · simp [unitStep, pointOnAxis]
  · intro μ _ h
    simp [unitStep, pointOnAxis, Pi.single_eq_of_ne h.symm]
  · simp
theorem coe_toSublattice {j i : ℤ} (y : Site L m j) (h : (y : FourTorus L m) ∈ sublattice L m i) :
    ((y.toSublattice i : Site L m i) : FourTorus L m) = y :=
  Classical.epsilon_spec (p := fun x : Site L m i => (x : FourTorus L m) = y) ⟨⟨y, h⟩, rfl⟩
theorem coe_refinedOffsetSite (hL : 0 < L) {t : ℤ} (n : ℕ) (y : Site L m t) (p : Fin 4 → ℤ) :
    ((refinedOffsetSite n y p : Site L m (t + n)) : FourTorus L m) =
      coordinatePoint (t + n) (y : FourTorus L m) p := by
  unfold refinedOffsetSite
  rw [coe_offsetSite, coe_toSublattice y (sublattice_mono hL m (by omega : t ≤ t + n) y.2)]
theorem coordinatePoint_zero (s : ℤ) (y : FourTorus L m) : coordinatePoint s y 0 = y := by
  funext ν
  rw [coordinatePoint_apply]
  simp
theorem coordinatePoint_add_pointOnAxis (s : ℤ) (y : FourTorus L m) (p : Fin 4 → ℤ) (μ : Fin 4)
    (e : ℤ) :
    coordinatePoint s y p + pointOnAxis L m μ ((e : ℝ) * meshSize L s) =
      coordinatePoint s y (p + Pi.single μ e) := by
  funext ν
  rw [Pi.add_apply, coordinatePoint_apply, coordinatePoint_apply, add_assoc]
  congr 1
  by_cases h : ν = μ
  · subst h
    simp [pointOnAxis, add_mul]
  · simp [pointOnAxis, Pi.single_eq_of_ne h]
theorem coordinatePoint_coordinatePoint (hL : 0 < L) (t : ℤ) (n : ℕ) (y : FourTorus L m)
    (q r : Fin 4 → ℤ) :
    coordinatePoint (t + n) (coordinatePoint t y q) r =
      coordinatePoint (t + n) y (fun ν => (L : ℤ) ^ n * q ν + r ν) := by
  funext ν
  simp only [coordinatePoint_apply, add_assoc, ← AddCircle.coe_add]
  rw [meshSize_eq_pow_mul hL t n]
  congr 2
  push_cast
  ring
theorem exists_balanced_division_odd {D : ℕ} (hD : Odd D) (a : ℤ) :
    ∃ q r : ℤ, a = (D : ℤ) * q + r ∧ 2 * |r| ≤ (D : ℤ) - 1 := by
  obtain ⟨c, rfl⟩ := hD
  have lo := Int.le_bmod (x := a) (m := 2 * c + 1) (by omega)
  have hi := Int.bmod_lt (x := a) (m := 2 * c + 1) (by omega)
  have split := Int.bmod_add_bdiv a (2 * c + 1)
  refine ⟨Int.bdiv a (2 * c + 1), Int.bmod a (2 * c + 1), by linear_combination split.symm, ?_⟩
  rcases abs_cases (Int.bmod a (2 * c + 1)) with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> push_cast at lo hi ⊢ <;>
    omega
theorem int_abs_sub_le_abs_add_abs (a b : ℤ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg] using abs_add_le a (-b)
theorem dvd_quotient_of_unit_step {M N a s s' u : ℤ} (hM : 0 < M) (hs : 2 * |s| ≤ M - 1)
    (hs' : 2 * |s'| ≤ M - 1) (hu : u = 0 ∨ u = 1 ∨ u = -1)
    (hc : M * a + s' ≡ s + u [ZMOD M * N]) :
    N ∣ a ∨ (u ≠ 0 ∧ N ∣ a - u) := by
  rcases Int.ModEq.dvd hc with ⟨j, hj⟩
  have gap : s + u - s' = M * (a + N * j) := by linear_combination hj
  have g1 := le_abs_self s
  have g2 := neg_abs_le s
  have g3 := le_abs_self s'
  have g4 := neg_abs_le s'
  have top : M * (a + N * j) ≤ M * 1 := by
    rw [← gap]
    omega
  have bot : M * (-1) ≤ M * (a + N * j) := by
    rw [← gap]
    omega
  have w1 := le_of_mul_le_mul_left top hM
  have w2 := le_of_mul_le_mul_left bot hM
  obtain z | o | n : a + N * j = 0 ∨ a + N * j = 1 ∨ a + N * j = -1 := by omega
  · exact Or.inl ⟨-j, by linear_combination z⟩
  · rw [o, mul_one] at gap
    obtain rfl : u = 1 := by omega
    exact Or.inr ⟨one_ne_zero, -j, by linear_combination o⟩
  · rw [n] at gap
    obtain rfl : u = -1 := by omega
    exact Or.inr ⟨by norm_num, -j, by linear_combination n⟩
theorem isMinimalResidue_of_two_mul_abs_le {M p : ℤ} (h : 2 * |p| ≤ M) :
    IsMinimalResidue M p := by
  intro s hs
  obtain ⟨k, hk⟩ := hs.dvd
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [mul_zero, sub_eq_zero] at hk
    exact (congrArg abs hk).le
  · have hM : 0 ≤ M := (mul_nonneg zero_le_two (abs_nonneg p)).trans h
    have far : M ≤ |p - s| := by
      rw [hk, abs_mul, abs_of_nonneg hM]
      exact le_mul_of_one_le_right hM (Int.one_le_abs hk0)
    linarith [int_abs_sub_le_abs_add_abs p s]
theorem exists_modEq_two_mul_abs_le (h : ℕ) (hh : 0 < h) (a : ℤ) :
    ∃ r : ℤ, r ≡ a [ZMOD ((2 * h : ℕ) : ℤ)] ∧ 2 * |r| ≤ ((2 * h : ℕ) : ℤ) := by
  have lo := Int.le_bmod (x := a) (m := 2 * h) (by omega)
  have hi := Int.bmod_lt (x := a) (m := 2 * h) (by omega)
  refine ⟨Int.bmod a (2 * h), Int.bmod_emod, ?_⟩
  rcases abs_cases (Int.bmod a (2 * h)) with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> push_cast at lo hi ⊢ <;>
    omega
theorem abs_le_supNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ _root_.YangMills.Construction.TorusMetric.supNormVec v :=
  Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ)
theorem torusSupNorm_eq_supNormVec_norm {S : ℝ} (x : Torus4 S) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm x = _root_.YangMills.Construction.TorusMetric.supNormVec fun μ => ‖x μ‖ := by
  choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm (x μ)
  have hcov : _root_.YangMills.Construction.TorusMetric.torusProj S b = x := funext hb
  apply le_antisymm
  · refine csInf_le ⟨0, ?_⟩ ⟨b, hcov, ?_⟩
    · rintro _ ⟨v, -, rfl⟩
      exact (abs_nonneg (v 0)).trans (abs_le_supNormVec v 0)
    · simp [_root_.YangMills.Construction.TorusMetric.supNormVec, hb']
  · refine le_csInf ⟨_, b, hcov, rfl⟩ ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' : _root_.YangMills.Construction.TorusMetric.torusProj S v = x := hv
    refine Finset.sup'_le _ _ fun μ _ => ?_
    rw [abs_norm, ← hv']
    exact (addCircle_norm_coe_le_abs _).trans (abs_le_supNormVec v μ)
theorem torusSupNorm_sub_le {S : ℝ} (x z : Torus4 S) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm (x - z) ≤ _root_.YangMills.Construction.TorusMetric.torusSupNorm x + _root_.YangMills.Construction.TorusMetric.torusSupNorm z := by
  rw [torusSupNorm_eq_supNormVec_norm, torusSupNorm_eq_supNormVec_norm,
    torusSupNorm_eq_supNormVec_norm]
  refine Finset.sup'_le _ _ fun μ _ => ?_
  have h1 := abs_le_supNormVec (fun μ => ‖x μ‖) μ
  have h2 := abs_le_supNormVec (fun μ => ‖z μ‖) μ
  simp only [abs_norm] at h1 h2
  rw [abs_norm, Pi.sub_apply]
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)
theorem exists_coordinates {s : ℤ} (Hs : SublatticeCoordinates L m s) {y x : FourTorus L m}
    (hy : y ∈ sublattice L m s) (hx : x ∈ sublattice L m s) :
    ∃ p, x = coordinatePoint s y p := by
  obtain ⟨p, hp⟩ := Hs.2.2.2.1 ⟨y, hy⟩ ⟨x, hx⟩
  refine ⟨p, ?_⟩
  have h := congrArg Subtype.val hp
  rw [coe_offsetSite] at h
  exact h
theorem coordinates_modEq {s : ℤ} (Hs : SublatticeCoordinates L m s) {y : FourTorus L m}
    (hy : y ∈ sublattice L m s) (p p' : Fin 4 → ℤ)
    (h : coordinatePoint s y p = coordinatePoint s y p') :
    ∀ μ, p μ ≡ p' μ [ZMOD (axisSiteCount L m s : ℤ)] :=
  (Hs.2.2.2.2.1 ⟨y, hy⟩ p p').mp (Subtype.ext (by
    rw [coe_offsetSite, coe_offsetSite]
    exact h))
theorem torusSupNorm_coordinatePoint_sub {s : ℤ} (Hs : SublatticeCoordinates L m s)
    {y : FourTorus L m} (hy : y ∈ sublattice L m s) (p : Fin 4 → ℤ)
    (h : ∀ μ, 2 * |p μ| ≤ (axisSiteCount L m s : ℤ)) :
    _root_.YangMills.Construction.TorusMetric.torusSupNorm (coordinatePoint s y p - y) =
      meshSize L s * _root_.YangMills.Construction.TorusMetric.supNormVec fun μ => (p μ : ℝ) := by
  have h1 := (Hs.2.2.2.2.2.2.2 ⟨y, hy⟩ p
    (fun μ => isMinimalResidue_of_two_mul_abs_le (h μ))).1
  rw [coe_offsetSite] at h1
  exact h1
theorem exists_small_coordinates {s : ℤ} (Hs : SublatticeCoordinates L m s)
    {y x : FourTorus L m} (hy : y ∈ sublattice L m s) (hx : x ∈ sublattice L m s) :
    ∃ p, x = coordinatePoint s y p ∧
      ∀ μ, 2 * |p μ| ≤ (axisSiteCount L m s : ℤ) := by
  obtain ⟨p0, hp0⟩ := exists_coordinates Hs hy hx
  have hpos : 0 < halfPeriod L m s := by
    have := Hs.2.1
    omega
  choose r hr hr' using fun μ => exists_modEq_two_mul_abs_le (halfPeriod L m s) hpos (p0 μ)
  have e : offsetSite (⟨y, hy⟩ : Site L m s) r = offsetSite ⟨y, hy⟩ p0 :=
    (Hs.2.2.2.2.1 ⟨y, hy⟩ r p0).mpr hr
  have e' := congrArg Subtype.val e
  rw [coe_offsetSite, coe_offsetSite] at e'
  refine ⟨r, ?_, hr'⟩
  rw [hp0]
  exact e'.symm
theorem meshSize_le_torusSupNorm_sub (hL : 0 < L) {t : ℤ} (Ht : SublatticeCoordinates L m t)
    (y y' : Site L m t) (h : y ≠ y') :
    meshSize L t ≤ _root_.YangMills.Construction.TorusMetric.torusSupNorm ((y : FourTorus L m) - (y' : FourTorus L m)) := by
  obtain ⟨p, hp, hs⟩ := exists_small_coordinates Ht y'.2 y.2
  have hne : ∃ μ, p μ ≠ 0 := by
    by_contra hc
    apply h
    apply Subtype.ext
    have h0 : p = 0 := funext fun μ => by_contra fun hμ => hc ⟨μ, hμ⟩
    rw [hp, h0, coordinatePoint_zero]
  obtain ⟨μ, hμ⟩ := hne
  rw [hp, torusSupNorm_coordinatePoint_sub Ht y'.2 p hs]
  have h1 : (1 : ℝ) ≤ _root_.YangMills.Construction.TorusMetric.supNormVec fun μ => (p μ : ℝ) := by
    refine le_trans ?_ (abs_le_supNormVec (fun μ => (p μ : ℝ)) μ)
    exact_mod_cast Int.one_le_abs hμ
  have h2 := meshSize_pos hL t
  nlinarith
theorem axisSiteCount_add {t : ℤ} (ht : -(m : ℤ) ≤ t) (n : ℕ) :
    (axisSiteCount L m (t + n) : ℤ) = (L : ℤ) ^ n * (axisSiteCount L m t : ℤ) := by
  have h : ((m : ℤ) + (t + n)).toNat = ((m : ℤ) + t).toNat + n := by omega
  unfold axisSiteCount halfPeriod
  rw [h]
  push_cast
  ring
theorem finerLatticeAroundSite (hL : 0 < L) {t : ℤ} (ht : -(m : ℤ) ≤ t)
    (H : ∀ j : ℤ, -(m : ℤ) ≤ j → SublatticeCoordinates L m j) (n : ℕ) :
    FinerLatticeAroundSite L m t (t + n) n := by
  have Hs := H (t + n) (by omega)
  have Ht := H t ht
  refine ⟨meshSize_eq_pow_mul hL t n, ?_, ?_, sublattice_mono hL m (by omega), ?_, ?_⟩
  · have h := Hs.1
    rw [div_eq_iff (meshSize_pos hL _).ne'] at h
    exact h
  · have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    unfold torusSide meshSize
    rw [mul_assoc, ← zpow_add₀ hL']
    have e : (m : ℤ) + t + -t = m := by ring
    rw [e, zpow_natCast]
  · intro y x hx
    have hy : (y : FourTorus L m) ∈ sublattice L m (t + n) := sublattice_mono hL m (by omega) y.2
    refine ⟨exists_small_coordinates Hs hy hx, ?_, ?_⟩
    · intro p p' h h'
      exact coordinates_modEq Hs hy p p' (h.symm.trans h')
    · intro p h h'
      rw [h]
      exact torusSupNorm_coordinatePoint_sub Hs hy p h'
  · intro y y' h
    exact meshSize_le_torusSupNorm_sub hL Ht y y' h
theorem refinedBlock_eq_image (hL : 0 < L) {t : ℤ} {n : ℕ} (hB : RefinedBlockCoordinates L m t n)
    (y : Site L m t) :
    refinedBlock n y = coordinatePoint (t + n) (y : FourTorus L m) '' blockOffsets L n := by
  rw [(hB y).2.1]
  exact Set.image_congr fun p _ => coe_refinedOffsetSite hL n y p
theorem refinedBlockAroundCentre (hL : 0 < L) {t : ℤ} (ht : -(m : ℤ) ≤ t)
    (H : ∀ j : ℤ, -(m : ℤ) ≤ j → SublatticeCoordinates L m j) (n : ℕ)
    (hB : RefinedBlockCoordinates L m t n) : RefinedBlockAroundCentre L m t (t + n) n := by
  intro y
  have Hs := H (t + n) (by omega)
  have Ht := H t ht
  have hy : (y : FourTorus L m) ∈ sublattice L m (t + n) := sublattice_mono hL m (by omega) y.2
  have himg := refinedBlock_eq_image hL hB y
  have hPpos : (1 : ℤ) ≤ (L : ℤ) ^ n := by
    have : (0 : ℤ) < (L : ℤ) ^ n := pow_pos (by exact_mod_cast hL) n
    omega
  have hNt : (1 : ℤ) ≤ (axisSiteCount L m t : ℤ) := by
    have := Ht.2.1
    unfold axisSiteCount
    omega
  have hsmall : ∀ p ∈ blockOffsets L n, ∀ μ,
      2 * |p μ| ≤ (axisSiteCount L m (t + n) : ℤ) := by
    intro p hp μ
    have h1 := hp μ
    rw [axisSiteCount_add ht n]
    nlinarith
  have hsup : ∀ x ∈ refinedBlock n y,
      _root_.YangMills.Construction.TorusMetric.torusSupNorm (x - (y : FourTorus L m)) < meshSize L t / 2 := by
    intro x hx
    rw [himg] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [torusSupNorm_coordinatePoint_sub Hs hy p (hsmall p hp), meshSize_eq_pow_mul hL t n]
    have hv : _root_.YangMills.Construction.TorusMetric.supNormVec (fun μ => (p μ : ℝ)) ≤ ((L : ℝ) ^ n - 1) / 2 := by
      refine Finset.sup'_le _ _ fun μ _ => ?_
      have h1 := hp μ
      have h2 : 2 * |(p μ : ℝ)| ≤ (L : ℝ) ^ n - 1 := by exact_mod_cast h1
      linarith
    have h3 := meshSize_pos hL (t + n)
    nlinarith
  have hmem : (y : FourTorus L m) ∈ refinedBlock n y := by
    rw [himg]
    refine ⟨0, ?_, coordinatePoint_zero _ _⟩
    intro μ
    simp only [Pi.zero_apply, abs_zero, mul_zero]
    omega
  refine ⟨himg, ?_, (hB y).2.2.2.1, hsup, hmem, (hB y).2.2.2.2, ?_⟩
  · intro p hp p' hp' e
    apply (hB y).2.2.1 hp hp'
    apply Subtype.ext
    rw [coe_refinedOffsetSite hL, coe_refinedOffsetSite hL]
    exact e
  · ext x
    constructor
    · rintro ⟨hxb, hxt⟩
      by_contra hne
      have h1 := meshSize_le_torusSupNorm_sub hL Ht ⟨x, hxt⟩ y
        (fun e => hne (mem_singleton_iff.mpr (congrArg Subtype.val e)))
      have h2 := hsup x hxb
      have h3 := meshSize_pos hL t
      linarith
    · intro hx
      rw [mem_singleton_iff] at hx
      subst hx
      exact ⟨hmem, y.2⟩
theorem mem_refinedBlock_iff {t : ℤ} {n : ℕ} {y : Site L m t} {x : FourTorus L m} :
    x ∈ refinedBlock n y ↔ x ∈ cubeAround y ∧ x ∈ sublattice L m (t + n) := Iff.rfl
theorem refinedBlocksCover (hL : 0 < L) (hodd : Odd L) {t : ℤ} (ht : -(m : ℤ) ≤ t)
    (H : ∀ j : ℤ, -(m : ℤ) ≤ j → SublatticeCoordinates L m j) (n : ℕ)
    (hB : RefinedBlockCoordinates L m t n) : RefinedBlocksCover L m t (t + n) n := by
  have Hs := H (t + n) (by omega)
  have Ht := H t ht
  have hcentre := refinedBlockAroundCentre hL ht H n hB
  have uniq : ∀ (x : FourTorus L m) (y' y'' : Site L m t), x ∈ refinedBlock n y' →
      x ∈ refinedBlock n y'' → y'' = y' := by
    intro x y' y'' h' h''
    by_contra hne
    have h1 := meshSize_le_torusSupNorm_sub hL Ht y' y'' (fun e => hne e.symm)
    have h2 := (hcentre y').2.2.2.1 x h'
    have h3 := (hcentre y'').2.2.2.1 x h''
    have h4 := torusSupNorm_sub_le (x - (y'' : FourTorus L m)) (x - (y' : FourTorus L m))
    rw [sub_sub_sub_cancel_left] at h4
    linarith
  have ex : ∀ x ∈ sublattice L m (t + n), ∃ y' : Site L m t, x ∈ refinedBlock n y' := by
    rintro x ⟨N, hN⟩
    choose q r hq hr using fun μ => exists_balanced_division_odd (D := L ^ n) hodd.pow (N μ)
    let y' : Site L m t :=
      ⟨fun μ => (((q μ : ℝ) * meshSize L t : ℝ) : AddCircle (torusSide L m)), q, fun _ => rfl⟩
    refine ⟨y', ?_⟩
    rw [(hcentre y').1]
    refine ⟨r, fun μ => by exact_mod_cast hr μ, ?_⟩
    funext ν
    rw [coordinatePoint_apply, hN ν, hq ν]
    show (((q ν : ℝ) * meshSize L t : ℝ) : AddCircle (torusSide L m)) + _ = _
    rw [← AddCircle.coe_add, meshSize_eq_pow_mul hL t n]
    congr 1
    push_cast
    ring
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y', h⟩ := ex x hx
    refine ⟨⟨y', (mem_refinedBlock_iff.mp h).1, fun y'' h'' => ?_⟩, y', h,
      fun y'' h'' => uniq x y' y'' h h''⟩
    exact uniq x y' y'' h (mem_refinedBlock_iff.mpr ⟨h'', hx⟩)
  · intro x y' y'' ε μ hε hx hx' hne
    rw [(hcentre y').1] at hx
    rw [(hcentre y'').1] at hx'
    have hPpos : (0 : ℤ) < (L : ℤ) ^ n := pow_pos (by exact_mod_cast hL) n
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨r', hr', e⟩ := hx'
    obtain ⟨q, hq⟩ := Ht.2.2.2.1 y' y''
    have hq' : (y'' : FourTorus L m) = coordinatePoint t (y' : FourTorus L m) q := by
      rw [hq, coe_offsetSite]
    have hy' : (y' : FourTorus L m) ∈ sublattice L m (t + n) :=
      sublattice_mono hL m (by omega) y'.2
    rw [hq', coordinatePoint_coordinatePoint hL, coordinatePoint_add_pointOnAxis] at e
    have hm := coordinates_modEq Hs hy' _ _ e
    rw [axisSiteCount_add ht n] at hm
    have he : ∀ ν, (Pi.single μ ε : Fin 4 → ℤ) ν = 0 ∨ (Pi.single μ ε : Fin 4 → ℤ) ν = 1 ∨
        (Pi.single μ ε : Fin 4 → ℤ) ν = -1 := by
      intro ν
      by_cases h : ν = μ
      · subst h
        rw [Pi.single_eq_same]
        tauto
      · left
        exact Pi.single_eq_of_ne h _
    have key : ∀ ν, (axisSiteCount L m t : ℤ) ∣ q ν ∨
        ((Pi.single μ ε : Fin 4 → ℤ) ν ≠ 0 ∧
          (axisSiteCount L m t : ℤ) ∣ q ν - (Pi.single μ ε : Fin 4 → ℤ) ν) :=
      fun ν => dvd_quotient_of_unit_step hPpos (hr ν) (hr' ν) (he ν) (hm ν)
    have hother : ∀ ν, ν ≠ μ → (axisSiteCount L m t : ℤ) ∣ q ν := by
      intro ν h
      rcases key ν with h1 | ⟨h1, -⟩
      · exact h1
      · exact absurd (Pi.single_eq_of_ne h _) h1
    by_cases hz : (axisSiteCount L m t : ℤ) ∣ q μ
    · exfalso
      apply hne
      have h0 : offsetSite y' q = offsetSite y' 0 := by
        refine (Ht.2.2.2.2.1 y' q 0).mpr fun ν => ?_
        have hν : (axisSiteCount L m t : ℤ) ∣ q ν := by
          by_cases h : ν = μ
          · rw [h]
            exact hz
          · exact hother ν h
        exact (Int.modEq_zero_iff_dvd).mpr hν
      rw [hq, h0]
      apply Subtype.ext
      rw [coe_offsetSite, coordinatePoint_zero]
    · have hμ : (axisSiteCount L m t : ℤ) ∣ q μ - ε := by
        rcases key μ with h1 | ⟨-, h1⟩
        · exact absurd h1 hz
        · rwa [Pi.single_eq_same] at h1
      have h0 : offsetSite y' q = offsetSite y' (Pi.single μ ε) := by
        refine (Ht.2.2.2.2.1 y' q (Pi.single μ ε)).mpr fun ν => ?_
        by_cases h : ν = μ
        · subst h
          rw [Pi.single_eq_same]
          exact (Int.modEq_iff_dvd.mpr hμ).symm
        · rw [Pi.single_eq_of_ne h]
          exact (Int.modEq_zero_iff_dvd).mpr (hother ν h)
      have e2 := congrArg Subtype.val h0
      rw [coe_offsetSite, coe_offsetSite] at e2
      rw [hq', e2]
      have e3 := coordinatePoint_add_pointOnAxis t (y' : FourTorus L m) 0 μ ε
      rw [coordinatePoint_zero, zero_add] at e3
      exact e3.symm
theorem levelSublatticesInCoordinates (hL : 0 < L) (hodd : Odd L) {K : ℕ} (hm : 0 < m)
    (H : ∀ j : ℤ, -(m : ℤ) ≤ j → SublatticeCoordinates L m j)
    (HB : ∀ (t : ℤ) (n : ℕ), -(m : ℤ) ≤ t → RefinedBlockCoordinates L m t n) (i j : ℕ)
    (hij : i ≤ j) (hjK : j ≤ K) : LevelSublatticesInCoordinates L m K i j := by
  have e : levelDepth K i = levelDepth K j + ((j - i : ℕ) : ℤ) := by
    simp only [levelDepth]
    omega
  have hd : -(m : ℤ) ≤ levelDepth K j := by
    simp only [levelDepth]
    omega
  have hdi : -(m : ℤ) ≤ levelDepth K i := by
    simp only [levelDepth]
    omega
  refine ⟨?_, fun y => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [e]
    exact ⟨rfl, finerLatticeAroundSite hL hd H _, refinedBlockAroundCentre hL hd H _ (HB _ _ hd),
      refinedBlocksCover hL hodd hd H _ (HB _ _ hd)⟩
  · have h : ((m : ℤ) + levelDepth K i).toNat = m + K - i := by
      simp only [levelDepth]
      omega
    unfold axisSiteCount halfPeriod
    rw [h]
  · have h : 1 ≤ m + K - i := by omega
    exact Nat.mul_le_mul_left 2 (Nat.le_self_pow (by omega) L)
  · intro y μ
    exact (H _ hdi).2.2.2.2.2.1 y μ
  · exact sublattice_mono hL m (by simp only [levelDepth]; omega)
theorem meshesAndSideInLevelUnits (hL : 0 < L) {K k : ℕ} (hk : k ≤ K) :
    MeshesAndSideInLevelUnits L m K k := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  refine ⟨fun i _ => ?_, ?_, ?_⟩
  · unfold toLevelUnits meshSize
    rw [← zpow_add₀ hL']
    congr 1
    simp only [levelDepth]
    ring
  · unfold toLevelUnits meshSize finestMeshInLevelUnits
    rw [← zpow_add₀ hL']
    congr 1
    simp only [levelDepth]
    push_cast
    ring
  · unfold toLevelUnits torusSide
    have h : (L : ℝ) ^ (m + K - k) = (L : ℝ) ^ levelDepth K k * (L : ℝ) ^ m := by
      rw [← zpow_natCast, ← zpow_natCast (L : ℝ) m, ← zpow_add₀ hL']
      congr 1
      simp only [levelDepth]
      omega
    rw [h]
    ring
theorem refinedBlockCoordinatesHold_of_coordinateDescription (h : CoordinateDescription) :
    RefinedBlockCoordinatesHold := by
  intro L K m D
  have hodd := D.odd_factor
  have h13 := D.thirteen_le_factor
  have hm := D.exponent_pos
  have hL : 0 < L := by omega
  obtain ⟨H, -, HB, -⟩ := h L m hodd h13 hm
  refine ⟨fun t n ht => ?_,
    fun i j hij hjK => levelSublatticesInCoordinates hL hodd hm H HB i j hij hjK,
    fun k hk => meshesAndSideInLevelUnits hL hk⟩
  exact ⟨rfl, finerLatticeAroundSite hL ht H n, refinedBlockAroundCentre hL ht H n (HB t n ht),
    refinedBlocksCover hL hodd ht H n (HB t n ht)⟩
end YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof
