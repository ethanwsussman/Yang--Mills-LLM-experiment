import YangMills.Construction.Towers.BlocksCorridorsPivotBondsAndPaths
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.CubeCorridorProof
open InfiniteLattice
variable {a a' : ℝ}
theorem two_mul_abs_le_iff {z M : ℤ} : 2 * |z| ≤ M ↔ -M ≤ 2 * z ∧ 2 * z ≤ M := by
  rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
theorem exists_two_mul_abs_sub_le {M : ℤ} (hM : Odd M) (h0 : 0 < M) (N : ℤ) :
    ∃ q, 2 * |N - M * q| ≤ M - 1 := by
  obtain ⟨m, rfl⟩ := hM
  refine ⟨(N + m) / (2 * m + 1), ?_⟩
  have h1 := Int.emod_add_mul_ediv (N + m) (2 * m + 1)
  have h2 := Int.emod_nonneg (N + m) (ne_of_gt h0)
  have h3 := Int.emod_lt_of_pos (N + m) h0
  have e : N - (2 * m + 1) * ((N + m) / (2 * m + 1)) = (N + m) % (2 * m + 1) - m := by linarith
  rw [e, two_mul_abs_le_iff]
  omega
theorem eq_of_two_mul_abs_sub_le {M N q q' : ℤ} (h0 : 0 < M) (h : 2 * |N - M * q| ≤ M - 1)
    (h' : 2 * |N - M * q'| ≤ M - 1) : q = q' := by
  rw [two_mul_abs_le_iff] at h h'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hl
  · have h1 : M * (q + 1) ≤ M * q' := mul_le_mul_of_nonneg_left (by omega) h0.le
    rw [mul_add] at h1
    linarith [h.2, h'.1]
  · have h1 : M * (q' + 1) ≤ M * q := mul_le_mul_of_nonneg_left (by omega) h0.le
    rw [mul_add] at h1
    linarith [h.1, h'.2]
theorem two_mul_abs_digit_le {P L d A B : ℤ} (hP : 0 < P) (hL : Odd L) (hA : 2 * |A| ≤ P * L - 1)
    (hB : 2 * |B| ≤ P - 1) (e : P * d = A - B) : 2 * |d| ≤ L - 1 := by
  rw [two_mul_abs_le_iff] at hA hB ⊢
  obtain ⟨m, rfl⟩ := hL
  constructor
  · by_contra hc
    have h1 : d + m + 1 ≤ 0 := by omega
    have h2 : P * (d + m + 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hP.le h1
    nlinarith [hA.1, hB.2]
  · by_contra hc
    have h1 : 0 ≤ d - m - 1 := by omega
    have h2 : 0 ≤ P * (d - m - 1) := mul_nonneg hP.le h1
    nlinarith [hA.2, hB.1]
theorem two_mul_abs_add_mul_le {P L d B : ℤ} (hP : 0 < P) (hd : 2 * |d| ≤ L - 1)
    (hB : 2 * |B| ≤ P - 1) : 2 * |B + P * d| ≤ P * L - 1 := by
  rw [two_mul_abs_le_iff] at hd hB ⊢
  have h1 : P * (2 * d) ≤ P * (L - 1) := mul_le_mul_of_nonneg_left hd.2 hP.le
  have h2 : P * (-(L - 1)) ≤ P * (2 * d) := mul_le_mul_of_nonneg_left hd.1 hP.le
  constructor <;> nlinarith [hB.1, hB.2]
def coordVec (a' : ℝ) (ν : Fin 4 → ℤ) : AmbientSpace := ∑ μ, Pi.single μ ((ν μ : ℝ) * a')
theorem coordVec_apply (a' : ℝ) (ν : Fin 4 → ℤ) (μ : Fin 4) : coordVec a' ν μ = (ν μ : ℝ) * a' := by
  simp [coordVec, Finset.sum_apply, Pi.single_apply]
theorem coordVec_injective (ha : a' ≠ 0) {ν ν' : Fin 4 → ℤ} (h : coordVec a' ν = coordVec a' ν') :
    ν = ν' := by
  funext μ
  have h' := congrFun h μ
  rw [coordVec_apply, coordVec_apply] at h'
  exact_mod_cast mul_right_cancel₀ ha h'
theorem coordVec_add (a' : ℝ) (ν ν' : Fin 4 → ℤ) :
    coordVec a' (ν + ν') = coordVec a' ν + coordVec a' ν' := by
  funext μ
  simp [coordVec_apply, add_mul]
theorem coordVec_neg (a' : ℝ) (ν : Fin 4 → ℤ) : coordVec a' (-ν) = -coordVec a' ν := by
  funext μ
  simp [coordVec_apply]
theorem coordVec_mem (a' : ℝ) (ν : Fin 4 → ℤ) : coordVec a' ν ∈ latticeSubgroup a' :=
  ⟨ν, coordVec_apply a' ν⟩
theorem exists_coordVec_of_mem {x : AmbientSpace} (hx : x ∈ latticeSubgroup a') :
    ∃ N, x = coordVec a' N := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, funext fun μ => by rw [hn, coordVec_apply]⟩
theorem exists_coordVec (x : InfiniteLattice.LatticePoint a') :
    ∃ N, (x : AmbientSpace) = coordVec a' N := exists_coordVec_of_mem x.2
theorem coordVec_of_eq_mul {M : ℤ} (h : a = (M : ℝ) * a') (q : Fin 4 → ℤ) :
    coordVec a q = coordVec a' fun μ => M * q μ := by
  funext μ
  rw [coordVec_apply, coordVec_apply, h]
  push_cast
  ring
theorem coe_mem_of_eq_mul {M : ℤ} (h : a = (M : ℝ) * a') (y : InfiniteLattice.LatticePoint a) :
    (y : AmbientSpace) ∈ latticeSubgroup a' := by
  obtain ⟨q, hq⟩ := exists_coordVec y
  rw [hq, coordVec_of_eq_mul h]
  exact coordVec_mem _ _
theorem exists_coordVec_of_eq_mul {M : ℤ} (h : a = (M : ℝ) * a') (y : InfiniteLattice.LatticePoint a) :
    ∃ Y, (y : AmbientSpace) = coordVec a' Y := exists_coordVec_of_mem (coe_mem_of_eq_mul h y)
theorem coe_toFiner {y : InfiniteLattice.LatticePoint a} (hy : (y : AmbientSpace) ∈ latticeSubgroup a') :
    (toFiner a' y : AmbientSpace) = y :=
  Classical.epsilon_spec (p := fun x : InfiniteLattice.LatticePoint a' => (x : AmbientSpace) = y)
    ⟨⟨y, hy⟩, rfl⟩
def addAt (N : Fin 4 → ℤ) (μ : Fin 4) (t : ℤ) : Fin 4 → ℤ :=
  fun ρ => N ρ + if ρ = μ then t else 0
theorem addAt_zero (N : Fin 4 → ℤ) (μ : Fin 4) : addAt N μ 0 = N := by
  funext ρ
  simp [addAt]
theorem coe_zsmul_axisStep (a : ℝ) (μ ρ : Fin 4) (t : ℤ) :
    ((t • axisStep a μ : InfiniteLattice.LatticePoint a) : AmbientSpace) ρ =
      if ρ = μ then (t : ℝ) * a else 0 := by
  by_cases h : ρ = μ
  · subst h
    simp [axisStep]
  · simp [axisStep, h]
theorem coe_add_zsmul_axisStep_of_eq_mul {M : ℤ} (h : a = (M : ℝ) * a')
    {y : InfiniteLattice.LatticePoint a} {Y : Fin 4 → ℤ}
    (hy : (y : AmbientSpace) = coordVec a' Y) (μ : Fin 4) (t : ℤ) :
    ((y + t • axisStep a μ : InfiniteLattice.LatticePoint a) : AmbientSpace) =
      coordVec a' (addAt Y μ (M * t)) := by
  funext ρ
  have hρ := congrFun hy ρ
  rw [coordVec_apply] at hρ
  rw [AddSubgroup.coe_add, Pi.add_apply, coe_zsmul_axisStep, hρ, coordVec_apply, h]
  by_cases e : ρ = μ
  · simp only [addAt, e, if_true]
    push_cast
    ring
  · simp [addAt, e]
theorem coe_add_zsmul_axisStep {x : InfiniteLattice.LatticePoint a'} {N : Fin 4 → ℤ}
    (hx : (x : AmbientSpace) = coordVec a' N) (μ : Fin 4) (t : ℤ) :
    ((x + t • axisStep a' μ : InfiniteLattice.LatticePoint a') : AmbientSpace) =
      coordVec a' (addAt N μ t) := by
  have h := coe_add_zsmul_axisStep_of_eq_mul (M := 1) (a' := a') (by simp) hx μ t
  rwa [one_mul] at h
theorem coe_add_axisStep {x : InfiniteLattice.LatticePoint a'} {N : Fin 4 → ℤ}
    (hx : (x : AmbientSpace) = coordVec a' N) (μ : Fin 4) :
    ((x + axisStep a' μ : InfiniteLattice.LatticePoint a') : AmbientSpace) =
      coordVec a' (addAt N μ 1) := by
  have h := coe_add_zsmul_axisStep hx μ 1
  rwa [one_smul] at h
theorem addAt_bound {A : ℤ} {N Y : Fin 4 → ℤ} {μ : Fin 4} {t u : ℤ}
    (hB : ∀ ρ, 2 * |N ρ - Y ρ| ≤ A) (h : 2 * |N μ + t - (Y μ + u)| ≤ A) :
    ∀ ρ, 2 * |addAt N μ t ρ - addAt Y μ u ρ| ≤ A := by
  intro ρ
  by_cases e : ρ = μ
  · subst e
    simpa [addAt] using h
  · simpa [addAt, e] using hB ρ
theorem addAt_bound_left {A : ℤ} {N Y : Fin 4 → ℤ} {μ : Fin 4} {t : ℤ}
    (hB : ∀ ρ, 2 * |N ρ - Y ρ| ≤ A) (h : 2 * |N μ + t - Y μ| ≤ A) :
    ∀ ρ, 2 * |addAt N μ t ρ - Y ρ| ≤ A := by
  have := addAt_bound (u := 0) hB (by simpa using h)
  rwa [addAt_zero] at this
theorem exists_link_signed (b : InfiniteLattice.Link a') :
    ∃ (μ : Fin 4) (s : ℤ), (s = 1 ∨ s = -1) ∧ b.terminal = b.initial + s • axisStep a' μ := by
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · exact ⟨μ, 1, Or.inl rfl, by rw [one_smul]; exact eq_add_of_sub_eq' h⟩
  · exact ⟨μ, -1, Or.inr rfl, by rw [neg_smul, one_smul]; exact eq_add_of_sub_eq' h⟩
section Order
variable (L n : ℕ)
theorem mem_cubeOfOrder_iff (ha : a' ≠ 0) {y : InfiniteLattice.LatticePoint a} {Y N : Fin 4 → ℤ}
    (hy : (y : AmbientSpace) = coordVec a' Y) :
    coordVec a' N ∈ cubeOfOrder L a' n y ↔ ∀ μ, 2 * |N μ - Y μ| ≤ (L : ℤ) ^ n - 1 := by
  constructor
  · rintro ⟨ν, hν, e⟩
    have e' : coordVec a' N = coordVec a' (Y + ν) := by
      rw [coordVec_add, ← hy]
      exact e
    have hN := coordVec_injective ha e'
    intro μ
    rw [hN]
    simpa using hν μ
  · intro h
    refine ⟨N - Y, fun μ => by simpa using h μ, ?_⟩
    show coordVec a' N = (y : AmbientSpace) + coordVec a' (N - Y)
    rw [hy, ← coordVec_add]
    congr 1
    abel
theorem mem_latticeSubgroup_of_mem_cubeOfOrder {y : InfiniteLattice.LatticePoint a}
    (hy : (y : AmbientSpace) ∈ latticeSubgroup a') {x : AmbientSpace}
    (hx : x ∈ cubeOfOrder L a' n y) : x ∈ latticeSubgroup a' := by
  obtain ⟨ν, -, rfl⟩ := hx
  exact add_mem hy (coordVec_mem a' ν)
theorem disjoint_cubeOfOrder (h0 : 0 < (L : ℤ) ^ n)
    (h : a = (((L : ℤ) ^ n : ℤ) : ℝ) * a') (ha : a' ≠ 0) {y y' : InfiniteLattice.LatticePoint a}
    (hne : y ≠ y') : Disjoint (cubeOfOrder L a' n y) (cubeOfOrder L a' n y') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨q, hq⟩ := exists_coordVec y
  obtain ⟨q', hq'⟩ := exists_coordVec y'
  rw [coordVec_of_eq_mul h] at hq hq'
  obtain ⟨N, rfl⟩ :=
    exists_coordVec_of_mem (mem_latticeSubgroup_of_mem_cubeOfOrder L n (coe_mem_of_eq_mul h y) hx)
  rw [mem_cubeOfOrder_iff L n ha hq] at hx
  rw [mem_cubeOfOrder_iff L n ha hq'] at hx'
  have e : q = q' := funext fun μ => eq_of_two_mul_abs_sub_le h0 (hx μ) (hx' μ)
  exact hne (Subtype.ext (by rw [hq, hq', e]))
theorem exists_mem_cubeOfOrder (hodd : Odd ((L : ℤ) ^ n)) (h0 : 0 < (L : ℤ) ^ n)
    (h : a = (((L : ℤ) ^ n : ℤ) : ℝ) * a') (ha : a' ≠ 0) {x : AmbientSpace}
    (hx : x ∈ latticeSubgroup a') :
    ∃ y : InfiniteLattice.LatticePoint a, x ∈ cubeOfOrder L a' n y := by
  obtain ⟨N, rfl⟩ := exists_coordVec_of_mem hx
  choose q hq using fun μ => exists_two_mul_abs_sub_le hodd h0 (N μ)
  exact ⟨⟨coordVec a q, coordVec_mem a q⟩, (mem_cubeOfOrder_iff L n ha (coordVec_of_eq_mul h q)).2 hq⟩
theorem offsetBox_ncard_eq (hodd : Odd ((L : ℤ) ^ n)) : (offsetBox L n).ncard = L ^ (4 * n) := by
  obtain ⟨m, hm⟩ := hodd
  have e : offsetBox L n =
      ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-m) m : Finset (Fin 4 → ℤ)) :
        Set (Fin 4 → ℤ)) := by
    ext ν
    rw [mem_offsetBox_iff]
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    refine forall_congr' fun μ => ?_
    rw [two_mul_abs_le_iff, hm]
    omega
  rw [e, Set.ncard_coe_finset, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : (m + 1 - -m).toNat = L ^ n := by
    have h2 : ((L ^ n : ℕ) : ℤ) = 2 * m + 1 := by
      push_cast
      exact hm
    omega
  rw [h1, ← pow_mul, mul_comm]
theorem cubeOfOrder_eq_image (y : InfiniteLattice.LatticePoint a) :
    cubeOfOrder L a' n y = cubeOffsetPoint a' y '' offsetBox L n := by
  ext x
  constructor
  · rintro ⟨ν, hν, rfl⟩
    exact ⟨ν, mem_offsetBox_iff.2 hν, rfl⟩
  · rintro ⟨ν, hν, rfl⟩
    exact ⟨ν, mem_offsetBox_iff.1 hν, rfl⟩
end Order
theorem meshAt_ne_zero {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k i : ℕ) :
    meshAt L k i ≠ 0 := by
  have h : (L : ℝ) ≠ 0 := by
    have := hL.2
    exact_mod_cast (by omega : L ≠ 0)
  exact zpow_ne_zero _ h
theorem meshAt_eq_pow_mul {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j n : ℕ)
    (hn : n ≤ j) : meshAt L k j = (((L : ℤ) ^ n : ℤ) : ℝ) * meshAt L k (j - n) := by
  have h : (L : ℝ) ≠ 0 := by
    have := hL.2
    exact_mod_cast (by omega : L ≠ 0)
  unfold meshAt
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ h]
  congr 1
  omega
theorem odd_pow_factor {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (n : ℕ) :
    Odd ((L : ℤ) ^ n) :=
  Odd.pow (by exact_mod_cast hL.1)
theorem pow_factor_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (n : ℕ) :
    0 < (L : ℤ) ^ n := by
  have := hL.2
  exact pow_pos (by omega) n
theorem cubesOfOrderPartition {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j n : ℕ)
    (hn : n ≤ j) : CubesOfOrderPartition L k j n := by
  have ha := meshAt_ne_zero hL k (j - n)
  have h := meshAt_eq_pow_mul hL k j n hn
  have hodd := odd_pow_factor hL n
  have h0 := pow_factor_pos hL n
  have hinj : ∀ y : Vertex L k j,
      Set.InjOn (cubeOffsetPoint (meshAt L k (j - n)) y) (offsetBox L n) :=
    fun y ν _ ν' _ e => coordVec_injective ha (add_left_cancel e)
  exact
    { offsetPoint_mem := fun y ν _ => add_mem (coe_mem_of_eq_mul h y) (coordVec_mem _ ν)
      offsetPoint_injOn := hinj
      offsetBox_ncard := offsetBox_ncard_eq L n hodd
      cube_ncard := fun y => by
        rw [cubeOfOrder_eq_image, Set.InjOn.ncard_image (hinj y), offsetBox_ncard_eq L n hodd]
      center_mem := fun y => by
        refine ⟨0, fun μ => ?_, ?_⟩
        · have : (1 : ℤ) ≤ (L : ℤ) ^ n := h0
          simpa using this
        · simp
      pointReflection_image := fun y => by
        ext x
        constructor
        · rintro ⟨_, ⟨ν, hν, rfl⟩, rfl⟩
          refine ⟨-ν, fun μ => by simpa using hν μ, ?_⟩
          show _ = (y : AmbientSpace) + coordVec _ (-ν)
          rw [coordVec_neg]
          show (y : AmbientSpace) - ((y : AmbientSpace) + coordVec _ ν - (y : AmbientSpace)) = _
          abel_nf
        · rintro ⟨ν, hν, rfl⟩
          refine ⟨(y : AmbientSpace) + coordVec _ (-ν), ⟨-ν, fun μ => by simpa using hν μ, rfl⟩, ?_⟩
          rw [coordVec_neg]
          show _ = (y : AmbientSpace) + coordVec _ ν
          abel_nf
      cube_add := fun y w => by
        ext x
        constructor
        · rintro ⟨ν, hν, rfl⟩
          refine ⟨(y : AmbientSpace) + coordVec _ ν, ⟨ν, hν, rfl⟩, ?_⟩
          show _ = ((y + w : Vertex L k j) : AmbientSpace) + coordVec _ ν
          rw [AddSubgroup.coe_add]
          abel_nf
        · rintro ⟨_, ⟨ν, hν, rfl⟩, rfl⟩
          refine ⟨ν, hν, ?_⟩
          show _ = ((y + w : Vertex L k j) : AmbientSpace) + coordVec _ ν
          rw [AddSubgroup.coe_add]
          show (y : AmbientSpace) + coordVec _ ν + (w : AmbientSpace) = _
          abel_nf
      iUnion_cube := by
        ext x
        rw [Set.mem_iUnion]
        constructor
        · rintro ⟨y, hy⟩
          exact mem_latticeSubgroup_of_mem_cubeOfOrder L n (coe_mem_of_eq_mul h y) hy
        · intro hx
          exact exists_mem_cubeOfOrder L n hodd h0 h ha hx
      pairwise_disjoint_cube := fun y y' hne => disjoint_cubeOfOrder L n h0 h ha hne }
theorem cubeOfOrder_eq_biUnion {a a₁ a' : ℝ} {L n : ℕ} (hodd : Odd (L : ℤ)) (hn : 1 ≤ n)
    (hP0 : 0 < (L : ℤ) ^ (n - 1)) (hPodd : Odd ((L : ℤ) ^ (n - 1)))
    (h₁ : a = ((L : ℤ) : ℝ) * a₁) (hP : a₁ = (((L : ℤ) ^ (n - 1) : ℤ) : ℝ) * a')
    (ha₁ : a₁ ≠ 0) (ha' : a' ≠ 0) (y : InfiniteLattice.LatticePoint a) :
    cubeOfOrder L a' n y =
      ⋃ x ∈ cubeVertices L a₁ y, cubeOfOrder L a' (n - 1) x := by
  have hpow : (L : ℤ) ^ n = (L : ℤ) ^ (n - 1) * L := by
    rw [← pow_succ]
    congr 1
    omega
  obtain ⟨q, hq⟩ := exists_coordVec y
  have hY₁ : (y : AmbientSpace) = coordVec a₁ fun μ => (L : ℤ) * q μ :=
    hq.trans (coordVec_of_eq_mul h₁ q)
  have hY : (y : AmbientSpace) = coordVec a' fun μ => (L : ℤ) ^ (n - 1) * ((L : ℤ) * q μ) :=
    hY₁.trans (coordVec_of_eq_mul hP _)
  have hysites : (y : AmbientSpace) ∈ latticeSubgroup a' := by
    rw [hY]
    exact coordVec_mem _ _
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro hx
    obtain ⟨N, rfl⟩ := exists_coordVec_of_mem (mem_latticeSubgroup_of_mem_cubeOfOrder L n hysites hx)
    rw [mem_cubeOfOrder_iff L n ha' hY] at hx
    choose r hr using fun μ => exists_two_mul_abs_sub_le hPodd hP0 (N μ)
    refine ⟨⟨coordVec a₁ r, coordVec_mem a₁ r⟩, ?_, ?_⟩
    · show coordVec a₁ r ∈ cubeOfOrder L a₁ 1 y
      rw [mem_cubeOfOrder_iff L 1 ha₁ hY₁]
      intro μ
      rw [pow_one]
      have hxμ : 2 * |N μ - (L : ℤ) ^ (n - 1) * ((L : ℤ) * q μ)| ≤
          (L : ℤ) ^ (n - 1) * L - 1 := by
        have := hx μ
        rw [hpow] at this
        exact this
      exact two_mul_abs_digit_le hP0 hodd hxμ (hr μ) (by ring)
    · exact (mem_cubeOfOrder_iff L (n - 1) ha' (coordVec_of_eq_mul hP r)).2 hr
  · rintro ⟨x₁, hx₁, hx⟩
    obtain ⟨R, hR⟩ := exists_coordVec x₁
    have hx₁sites : (x₁ : AmbientSpace) ∈ latticeSubgroup a' := by
      rw [hR, coordVec_of_eq_mul hP]
      exact coordVec_mem _ _
    obtain ⟨N, rfl⟩ :=
      exists_coordVec_of_mem (mem_latticeSubgroup_of_mem_cubeOfOrder L (n - 1) hx₁sites hx)
    rw [mem_cubeOfOrder_iff L (n - 1) ha' (hR.trans (coordVec_of_eq_mul hP R))] at hx
    have hx₁' : coordVec a₁ R ∈ cubeOfOrder L a₁ 1 y := by
      rw [← hR]
      exact hx₁
    rw [mem_cubeOfOrder_iff L 1 ha₁ hY₁] at hx₁'
    rw [mem_cubeOfOrder_iff L n ha' hY, hpow]
    intro μ
    have hd : 2 * |R μ - (L : ℤ) * q μ| ≤ (L : ℤ) - 1 := by
      have := hx₁' μ
      rwa [pow_one] at this
    have := two_mul_abs_add_mul_le hP0 hd (hx μ)
    have e : N μ - (L : ℤ) ^ (n - 1) * R μ + (L : ℤ) ^ (n - 1) * (R μ - (L : ℤ) * q μ) =
        N μ - (L : ℤ) ^ (n - 1) * ((L : ℤ) * q μ) := by ring
    rw [e] at this
    exact this
theorem cubeIsDisjointUnionOfSubcubes {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (k j n : ℕ) (h2 : 2 ≤ n) (hnj : n ≤ j) (y : Vertex L k j) :
    CubeIsDisjointUnionOfSubcubes L k j n y := by
  have ha₁ := meshAt_ne_zero hL k (j - 1)
  have ha' := meshAt_ne_zero hL k (j - n)
  have h₁ : meshAt L k j = ((L : ℤ) : ℝ) * meshAt L k (j - 1) := by
    have := meshAt_eq_pow_mul hL k j 1 (by omega)
    rwa [pow_one] at this
  have hP : meshAt L k (j - 1) =
      (((L : ℤ) ^ (n - 1) : ℤ) : ℝ) * meshAt L k (j - n) := by
    have := meshAt_eq_pow_mul hL k (j - 1) (n - 1) (by omega)
    rwa [show j - 1 - (n - 1) = j - n by omega] at this
  have hodd : Odd (L : ℤ) := by
    have := odd_pow_factor hL 1
    rwa [pow_one] at this
  exact
    { cube_eq_biUnion :=
        cubeOfOrder_eq_biUnion hodd (by omega) (pow_factor_pos hL _) (odd_pow_factor hL _) h₁ hP
          ha₁ ha' y
      pairwiseDisjoint_subcube := fun x _ x' _ hne =>
        disjoint_cubeOfOrder L (n - 1) (pow_factor_pos hL _) hP ha' hne }
section Steps
variable {L : ℕ}
theorem mem_cube_iff (ha : a' ≠ 0) {y : InfiniteLattice.LatticePoint a} {Y N : Fin 4 → ℤ}
    (hy : (y : AmbientSpace) = coordVec a' Y) :
    coordVec a' N ∈ cube L a' y ↔ ∀ μ, 2 * |N μ - Y μ| ≤ (L : ℤ) - 1 := by
  have := mem_cubeOfOrder_iff L 1 ha hy (N := N)
  rwa [pow_one] at this
theorem disjoint_cube (hL : 0 < (L : ℤ)) (h : a = ((L : ℤ) : ℝ) * a') (ha : a' ≠ 0)
    {y y' : InfiniteLattice.LatticePoint a} (hne : y ≠ y') : Disjoint (cube L a' y) (cube L a' y') :=
  disjoint_cubeOfOrder L 1 (by rwa [pow_one]) (by rwa [pow_one]) ha hne
theorem coe_eq_coordVec_of_isCubeOffset {y : InfiniteLattice.LatticePoint a}
    {x : InfiniteLattice.LatticePoint a'} {ν Y : Fin 4 → ℤ} (hd : IsCubeOffset L y x ν)
    (hy : (y : AmbientSpace) = coordVec a' Y) : (x : AmbientSpace) = coordVec a' (Y + ν) := by
  rw [coordVec_add, ← hy]
  exact eq_add_of_sub_eq' hd.1
theorem add_axisStep_mem_cube (ha : a' ≠ 0) (h : a = ((L : ℤ) : ℝ) * a') (hodd : Odd (L : ℤ))
    {y : InfiniteLattice.LatticePoint a} {x : InfiniteLattice.LatticePoint a'} {ν : Fin 4 → ℤ}
    (hd : IsCubeOffset L y x ν) {μ : Fin 4} (hlt : 2 * ν μ < (L : ℤ) - 1) :
    ((x + axisStep a' μ : InfiniteLattice.LatticePoint a') : AmbientSpace) ∈ cube L a' y := by
  obtain ⟨Y, hY⟩ := exists_coordVec_of_eq_mul h y
  rw [coe_add_axisStep (coe_eq_coordVec_of_isCubeOffset hd hY), mem_cube_iff ha hY]
  refine addAt_bound_left (fun ρ => by simpa using hd.2 ρ) ?_
  have hb := hd.2 μ
  rw [two_mul_abs_le_iff] at hb ⊢
  obtain ⟨m, hm⟩ := hodd
  simp only [Pi.add_apply]
  omega
theorem add_axisStep_mem_cube_add (ha : a' ≠ 0) (h : a = ((L : ℤ) : ℝ) * a')
    {y : InfiniteLattice.LatticePoint a} {x : InfiniteLattice.LatticePoint a'} {ν : Fin 4 → ℤ}
    (hd : IsCubeOffset L y x ν) {μ : Fin 4} (heq : 2 * ν μ = (L : ℤ) - 1) :
    ((x + axisStep a' μ : InfiniteLattice.LatticePoint a') : AmbientSpace) ∈
      cube L a' (y + axisStep a μ) := by
  obtain ⟨Y, hY⟩ := exists_coordVec_of_eq_mul h y
  have hc := coe_add_zsmul_axisStep_of_eq_mul h hY μ 1
  rw [one_smul, mul_one] at hc
  rw [coe_add_axisStep (coe_eq_coordVec_of_isCubeOffset hd hY), mem_cube_iff ha hc]
  refine addAt_bound (fun ρ => by simpa using hd.2 ρ) ?_
  rw [two_mul_abs_le_iff]
  simp only [Pi.add_apply]
  omega
theorem endpoints_of_link (ha : a' ≠ 0) (h : a = ((L : ℤ) : ℝ) * a') (hodd : Odd (L : ℤ))
    (hL : 0 < (L : ℤ)) (b : InfiniteLattice.Link a') :
    (∃ y : InfiniteLattice.LatticePoint a, (b.initial : AmbientSpace) ∈ cube L a' y ∧
        (b.terminal : AmbientSpace) ∈ cube L a' y) ∨
      ∃ c : InfiniteLattice.Link a,
        ((b.initial : AmbientSpace) ∈ cube L a' c.initial ∧
          (b.terminal : AmbientSpace) ∈ cube L a' c.terminal) ∧
        SameAxisAndSense c b ∧
        ∀ c' : InfiniteLattice.Link a,
          ((b.initial : AmbientSpace) ∈ cube L a' c'.initial ∧
            (b.terminal : AmbientSpace) ∈ cube L a' c'.terminal) →
            c' = c := by
  obtain ⟨μ, s, hs, hb⟩ := exists_link_signed b
  obtain ⟨T, hT⟩ := exists_coordVec b.initial
  have h' : a = (((L : ℤ) ^ 1 : ℤ) : ℝ) * a' := by rwa [pow_one]
  obtain ⟨y, hy⟩ : ∃ y : InfiniteLattice.LatticePoint a,
      (b.initial : AmbientSpace) ∈ cubeOfOrder L a' 1 y :=
    exists_mem_cubeOfOrder L 1 (by rwa [pow_one]) (by rwa [pow_one]) h' ha
      (SetLike.coe_mem b.initial)
  obtain ⟨Y, hY⟩ := exists_coordVec_of_eq_mul h y
  have hy' : coordVec a' T ∈ cube L a' y := by
    rw [← hT]
    exact hy
  have hbt := (mem_cube_iff ha hY).1 hy'
  have hhead : (b.terminal : AmbientSpace) = coordVec a' (addAt T μ s) := by
    rw [hb]
    exact coe_add_zsmul_axisStep hT μ s
  by_cases hin : 2 * |T μ + s - Y μ| ≤ (L : ℤ) - 1
  · left
    refine ⟨y, hy, ?_⟩
    rw [hhead, mem_cube_iff ha hY]
    exact addAt_bound_left hbt hin
  · right
    have hadj : ∃ ρ : Fin 4, (y + s • axisStep a μ) - y = axisStep a ρ ∨
        (y + s • axisStep a μ) - y = -axisStep a ρ := by
      refine ⟨μ, ?_⟩
      rcases hs with rfl | rfl
      · left
        simp
      · right
        simp
    have hcoe := coe_add_zsmul_axisStep_of_eq_mul h hY μ s
    refine ⟨⟨y, y + s • axisStep a μ, hadj⟩, ⟨hy, ?_⟩, ?_, ?_⟩
    · show (b.terminal : AmbientSpace) ∈ cube L a' (y + s • axisStep a μ)
      rw [hhead, mem_cube_iff ha hcoe]
      refine addAt_bound hbt ?_
      have hbμ := hbt μ
      rw [two_mul_abs_le_iff] at hbμ hin ⊢
      obtain ⟨m, hm⟩ := hodd
      rcases hs with rfl | rfl <;> omega
    · refine ⟨μ, ?_⟩
      rcases hs with rfl | rfl
      · left
        exact ⟨by simp, by rw [hb]; simp⟩
      · right
        exact ⟨by simp, by rw [hb]; simp⟩
    · rintro c' ⟨h₁, h₂⟩
      have e₁ : c'.initial = y := by
        by_contra hne
        exact Set.disjoint_left.1 (disjoint_cube hL h ha hne) h₁ hy
      have hhy : (b.terminal : AmbientSpace) ∈ cube L a' (y + s • axisStep a μ) := by
        rw [hhead, mem_cube_iff ha hcoe]
        refine addAt_bound hbt ?_
        have hbμ := hbt μ
        rw [two_mul_abs_le_iff] at hbμ hin ⊢
        obtain ⟨m, hm⟩ := hodd
        rcases hs with rfl | rfl <;> omega
      have e₂ : c'.terminal = y + s • axisStep a μ := by
        by_contra hne
        exact Set.disjoint_left.1 (disjoint_cube hL h ha hne) h₂ hhy
      exact Link.ext e₁ e₂
end Steps
section Paths
variable {L : ℕ}
theorem zsmul_axisStep_inj (ha : a ≠ 0) {ν μ : Fin 4} {t n : ℤ} (hn : n ≠ 0)
    (e : t • axisStep a ν = n • axisStep a μ) : ν = μ ∧ t = n := by
  have hc : ∀ ρ, ((t • axisStep a ν : InfiniteLattice.LatticePoint a) : AmbientSpace) ρ =
      ((n • axisStep a μ : InfiniteLattice.LatticePoint a) : AmbientSpace) ρ := fun ρ => by rw [e]
  have hμ := hc μ
  rw [coe_zsmul_axisStep, coe_zsmul_axisStep, if_pos rfl] at hμ
  have hνμ : ν = μ := by
    by_contra hne
    rw [if_neg (Ne.symm hne)] at hμ
    have h0 : (n : ℝ) * a ≠ 0 := mul_ne_zero (by exact_mod_cast hn) ha
    exact h0 hμ.symm
  subst hνμ
  rw [if_pos rfl] at hμ
  exact ⟨rfl, by exact_mod_cast mul_right_cancel₀ ha hμ⟩
theorem axisPath_eq (ha : a ≠ 0) {x x' : InfiniteLattice.LatticePoint a} {μ : Fin 4} {n : ℤ}
    (hn : n ≠ 0) (h : IsAxisDisplacement x x' μ n) : axisPath x x' = signedSteps x μ n := by
  have hex : ∃ q : Fin 4 × ℤ, IsAxisDisplacement x x' q.1 q.2 := ⟨(μ, n), h⟩
  have hq : x' - x = hex.choose.2 • axisStep a hex.choose.1 := hex.choose_spec
  have hn' : x' - x = n • axisStep a μ := h
  obtain ⟨h1, h2⟩ := zsmul_axisStep_inj ha hn (hq.symm.trans hn')
  unfold axisPath
  rw [dif_pos hex, h1, h2]
theorem mem_forwardSteps {x : InfiniteLattice.LatticePoint a'} {μ : Fin 4} {n : ℕ}
    {b : InfiniteLattice.Link a'} :
    b ∈ forwardSteps x μ n ↔
      ∃ t : ℕ, t < n ∧ b = Link.forwardFrom (x + (t : ℤ) • axisStep a' μ) μ := by
  induction n generalizing x with
  | zero => simp [forwardSteps]
  | succ n ih =>
    simp only [forwardSteps, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨t, ht, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · refine ⟨t + 1, by omega, ?_⟩
        congr 1
        push_cast
        rw [add_smul, one_smul]
        abel
    · rintro ⟨t, ht, rfl⟩
      cases t with
      | zero =>
        left
        simp
      | succ t =>
        right
        refine ⟨t, by omega, ?_⟩
        congr 1
        push_cast
        rw [add_smul, one_smul]
        abel
theorem mem_backwardSteps {x : InfiniteLattice.LatticePoint a'} {μ : Fin 4} {n : ℕ}
    {b : InfiniteLattice.Link a'} (hb : b ∈ backwardSteps x μ n) :
    ∃ t : ℕ, t < n ∧ b = backwardLink (x + (-(t : ℤ)) • axisStep a' μ) μ := by
  induction n generalizing x with
  | zero => simp [backwardSteps] at hb
  | succ n ih =>
    simp only [backwardSteps, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨t, ht, rfl⟩ := ih hb
      refine ⟨t + 1, by omega, ?_⟩
      congr 1
      push_cast
      rw [neg_add, add_smul, neg_smul, neg_smul, one_smul]
      abel
theorem mem_signedSteps {x : InfiniteLattice.LatticePoint a'} {μ : Fin 4} {n : ℤ}
    {b : InfiniteLattice.Link a'} (hb : b ∈ signedSteps x μ n) :
    ∃ t t' : ℤ, b.initial = x + t • axisStep a' μ ∧ b.terminal = x + t' • axisStep a' μ ∧
      min 0 n ≤ t ∧ t ≤ max 0 n ∧ min 0 n ≤ t' ∧ t' ≤ max 0 n := by
  unfold signedSteps at hb
  split_ifs at hb with h
  · obtain ⟨t, ht, rfl⟩ := mem_forwardSteps.1 hb
    refine ⟨t, t + 1, rfl, ?_, by omega, by omega, by omega, by omega⟩
    show x + (t : ℤ) • axisStep a' μ + axisStep a' μ = _
    rw [add_smul, one_smul, add_assoc]
  · obtain ⟨t, ht, rfl⟩ := mem_backwardSteps hb
    refine ⟨-(t : ℤ), -(t : ℤ) - 1, rfl, ?_, by omega, by omega, by omega, by omega⟩
    show x + (-(t : ℤ)) • axisStep a' μ - axisStep a' μ = _
    rw [sub_smul, one_smul, add_sub_assoc]
theorem forwardFrom_mem_linkCorridor_iff (ha : a' ≠ 0) {c : InfiniteLattice.Link a}
    {Y : Fin 4 → ℤ} {μ : Fin 4} (hY : (c.initial : AmbientSpace) = coordVec a' Y)
    (hH : (c.terminal : AmbientSpace) = coordVec a' (addAt Y μ (L : ℤ))) (hL : 0 ≤ (L : ℤ) - 1)
    {x : InfiniteLattice.LatticePoint a'} (hx : (x : AmbientSpace) = coordVec a' Y) {t : ℕ}
    (ht : t < L) :
    Link.forwardFrom (x + (t : ℤ) • axisStep a' μ) μ ∈ linkCorridor L a' c ↔
      2 * (t : ℤ) = (L : ℤ) - 1 := by
  have h₁ := coe_add_zsmul_axisStep hx μ (t : ℤ)
  have h₂ := coe_add_axisStep h₁ μ
  have hz : ∀ ρ, 2 * |Y ρ - Y ρ| ≤ (L : ℤ) - 1 := fun ρ => by simpa using hL
  constructor
  · rintro ⟨ht₁, ht₂⟩
    have ht₁' : coordVec a' (addAt Y μ (t : ℤ)) ∈ cube L a' c.initial := by
      rw [← h₁]
      exact ht₁
    have ht₂' : coordVec a' (addAt (addAt Y μ (t : ℤ)) μ 1) ∈ cube L a' c.terminal := by
      rw [← h₂]
      exact ht₂
    have e₁ := (mem_cube_iff ha hY).1 ht₁' μ
    have e₂ := (mem_cube_iff ha hH).1 ht₂' μ
    simp only [addAt, if_true] at e₁ e₂
    rw [two_mul_abs_le_iff] at e₁ e₂
    omega
  · intro h
    refine ⟨?_, ?_⟩
    · show ((x + (t : ℤ) • axisStep a' μ : InfiniteLattice.LatticePoint a') : AmbientSpace) ∈
        cube L a' c.initial
      rw [h₁, mem_cube_iff ha hY]
      refine addAt_bound_left hz ?_
      rw [two_mul_abs_le_iff]
      omega
    · show ((x + (t : ℤ) • axisStep a' μ + axisStep a' μ : InfiniteLattice.LatticePoint a') :
          AmbientSpace) ∈ cube L a' c.terminal
      rw [h₂, mem_cube_iff ha hH]
      refine addAt_bound (fun ρ => ?_) ?_
      · exact addAt_bound_left hz (by rw [two_mul_abs_le_iff]; omega) ρ
      · simp only [addAt, if_true]
        rw [two_mul_abs_le_iff]
        omega
theorem linkCorridor_of_sub_eq (ha : a' ≠ 0) (h : a = ((L : ℤ) : ℝ) * a')
    (hL₁ : Odd L) (hLpos : 0 < L) {c : InfiniteLattice.Link a} {μ : Fin 4}
    (hc : c.terminal - c.initial = axisStep a μ) :
    (∃! b : InfiniteLattice.Link a',
      b ∈ axisPath (toFiner a' c.initial) (toFiner a' c.terminal) ∧ b ∈ linkCorridor L a' c) ∧
    ∀ b : InfiniteLattice.Link a',
      b ∈ axisPath (toFiner a' c.initial) (toFiner a' c.terminal) ∧ b ∈ linkCorridor L a' c →
        (b.initial : AmbientSpace) =
          (c.initial : AmbientSpace) + Pi.single μ ((((L : ℝ) - 1) / 2) * a') := by
  obtain ⟨Y, hY⟩ := exists_coordVec_of_eq_mul h c.initial
  have hhead : c.terminal = c.initial + (1 : ℤ) • axisStep a μ := by
    rw [one_smul]
    exact eq_add_of_sub_eq' hc
  have hH : (c.terminal : AmbientSpace) = coordVec a' (addAt Y μ (L : ℤ)) := by
    have := coe_add_zsmul_axisStep_of_eq_mul h hY μ 1
    rw [mul_one] at this
    rw [hhead]
    exact this
  have hx₀ : (toFiner a' c.initial : AmbientSpace) = coordVec a' Y := by
    rw [coe_toFiner (coe_mem_of_eq_mul h c.initial)]
    exact hY
  have hx₁ : (toFiner a' c.terminal : AmbientSpace) = coordVec a' (addAt Y μ (L : ℤ)) := by
    rw [coe_toFiner (coe_mem_of_eq_mul h c.terminal)]
    exact hH
  have hdisp : IsAxisDisplacement (toFiner a' c.initial) (toFiner a' c.terminal) μ (L : ℤ) := by
    refine sub_eq_of_eq_add' (Subtype.ext ?_)
    rw [coe_add_zsmul_axisStep hx₀]
    exact hx₁
  have hpath : axisPath (toFiner a' c.initial) (toFiner a' c.terminal) =
      forwardSteps (toFiner a' c.initial) μ L := by
    rw [axisPath_eq ha (by omega) hdisp]
    simp [signedSteps]
  have hnn : 0 ≤ (L : ℤ) - 1 := by omega
  obtain ⟨m, hm⟩ := hL₁
  have hm' : 2 * (m : ℤ) = (L : ℤ) - 1 := by omega
  have hiff := fun (t : ℕ) (ht : t < L) =>
    forwardFrom_mem_linkCorridor_iff (L := L) ha hY hH hnn hx₀ ht
  rw [hpath]
  constructor
  · refine ⟨Link.forwardFrom (toFiner a' c.initial + (m : ℤ) • axisStep a' μ) μ,
      ⟨mem_forwardSteps.2 ⟨m, by omega, rfl⟩, (hiff m (by omega)).2 hm'⟩, ?_⟩
    rintro b ⟨hb₁, hb₂⟩
    obtain ⟨t, ht, rfl⟩ := mem_forwardSteps.1 hb₁
    have e := (hiff t ht).1 hb₂
    have : t = m := by omega
    rw [this]
  · rintro b ⟨hb₁, hb₂⟩
    obtain ⟨t, ht, rfl⟩ := mem_forwardSteps.1 hb₁
    have e := (hiff t ht).1 hb₂
    have e' : ((L : ℝ) - 1) / 2 = (t : ℝ) := by
      have : (L : ℝ) = 2 * t + 1 := by
        have : (L : ℤ) = 2 * t + 1 := by omega
        exact_mod_cast this
      rw [this]
      ring
    show ((toFiner a' c.initial + (t : ℤ) • axisStep a' μ : InfiniteLattice.LatticePoint a') :
      AmbientSpace) = _
    rw [coe_add_zsmul_axisStep hx₀, hY, e']
    funext ρ
    by_cases hρ : ρ = μ
    · subst hρ
      simp [addAt, coordVec_apply, add_mul]
    · simp [addAt, coordVec_apply, hρ]
end Paths
section Contours
variable {L : ℕ}
theorem stepsInOrder_endpoints_mem (ha : a' ≠ 0) {y : InfiniteLattice.LatticePoint a}
    {Y ν : Fin 4 → ℤ} (hY : (y : AmbientSpace) = coordVec a' Y)
    (hν : ∀ μ, 2 * |ν μ| ≤ (L : ℤ) - 1) (l : List (Fin 4)) :
    l.Nodup → ∀ (x₀ : InfiniteLattice.LatticePoint a') (X : Fin 4 → ℤ),
      (x₀ : AmbientSpace) = coordVec a' X →
      (∀ ρ, 2 * |X ρ - Y ρ| ≤ (L : ℤ) - 1) → (∀ ρ ∈ l, X ρ = Y ρ) →
      ∀ b ∈ stepsInOrder ν x₀ l,
        (b.initial : AmbientSpace) ∈ cube L a' y ∧ (b.terminal : AmbientSpace) ∈ cube L a' y := by
  induction l with
  | nil =>
    intro _ x₀ X _ _ _ b hb
    simp [stepsInOrder] at hb
  | cons μ l ih =>
    intro hl x₀ X hx hB hl' b hb
    rw [List.nodup_cons] at hl
    have hXμ : X μ = Y μ := hl' μ List.mem_cons_self
    have hμ := hν μ
    simp only [stepsInOrder, List.mem_append] at hb
    rcases hb with hb | hb
    · obtain ⟨t, t', e₁, e₂, h₁, h₂, h₃, h₄⟩ := mem_signedSteps hb
      have key : ∀ s : ℤ, min 0 (ν μ) ≤ s → s ≤ max 0 (ν μ) →
          ((x₀ + s • axisStep a' μ : InfiniteLattice.LatticePoint a') : AmbientSpace) ∈
            cube L a' y := by
        intro s hs₁ hs₂
        rw [coe_add_zsmul_axisStep hx, mem_cube_iff ha hY]
        refine addAt_bound_left hB ?_
        rw [two_mul_abs_le_iff] at hμ ⊢
        omega
      rw [e₁, e₂]
      exact ⟨key t h₁ h₂, key t' h₃ h₄⟩
    · refine ih hl.2 _ (addAt X μ (ν μ)) (coe_add_zsmul_axisStep hx μ _) ?_ ?_ b hb
      · refine addAt_bound_left hB ?_
        rw [two_mul_abs_le_iff] at hμ ⊢
        omega
      · intro ρ hρ
        have hne : ρ ≠ μ := fun e => hl.1 (e ▸ hρ)
        simp [addAt, hne, hl' ρ (List.mem_cons_of_mem _ hρ)]
theorem contour_vertex_mem_cube (ha : a' ≠ 0) (h : a = ((L : ℤ) : ℝ) * a') (hL : 0 ≤ (L : ℤ) - 1)
    {y : InfiniteLattice.LatticePoint a} {x : InfiniteLattice.LatticePoint a'}
    (hx : (x : AmbientSpace) ∈ cube L a' y)
    {Γ : List (InfiniteLattice.Link a')} (hΓ : Γ ∈ contourSet L y x)
    {z : InfiniteLattice.LatticePoint a'}
    (hz : z = toFiner a' y ∨ z = x ∨ ∃ b ∈ Γ, z = b.initial ∨ z = b.terminal) :
    (z : AmbientSpace) ∈ cube L a' y := by
  obtain ⟨Y, hY⟩ := exists_coordVec_of_eq_mul h y
  have hz₀ : ∀ ρ, 2 * |Y ρ - Y ρ| ≤ (L : ℤ) - 1 := fun ρ => by simpa using hL
  have hy₀ : (toFiner a' y : AmbientSpace) = coordVec a' Y := by
    rw [coe_toFiner (coe_mem_of_eq_mul h y)]
    exact hY
  rcases hz with rfl | rfl | ⟨b, hb, hz⟩
  · rw [hy₀]
    exact (mem_cube_iff ha hY).2 hz₀
  · exact hx
  · obtain ⟨ν₀, hν₀, e⟩ := hx
    have hd₀ : IsCubeOffset L y x ν₀ :=
      ⟨sub_eq_of_eq_add' e, fun μ => by simpa using hν₀ μ⟩
    have hd : IsCubeOffset L y x (cubeOffset L y x) :=
      Classical.epsilon_spec (p := IsCubeOffset L y x) ⟨ν₀, hd₀⟩
    obtain ⟨σ, rfl⟩ := hΓ
    have hnd : ((List.finRange (offsetSupport L y x).card).map
        fun i => ((σ i : offsetSupport L y x) : Fin 4)).Nodup :=
      List.Nodup.map (fun i i' e => σ.injective (Subtype.ext e)) (List.nodup_finRange _)
    have hends := stepsInOrder_endpoints_mem ha hY hd.2 _ hnd (toFiner a' y) Y hy₀ hz₀
      (fun _ _ => rfl) b hb
    rcases hz with rfl | rfl
    · exact hends.1
    · exact hends.2
theorem crossing_vertex_mem_doubleCube (ha : a' ≠ 0) (h : a = ((L : ℤ) : ℝ) * a')
    (hodd : Odd (L : ℤ)) (hpos : 0 < (L : ℤ)) (c : InfiniteLattice.Link a)
    (x : InfiniteLattice.LatticePoint a') (hx : (x : AmbientSpace) ∈ cube L a' c.initial)
    {z : InfiniteLattice.LatticePoint a'}
    (hz : z = x ∨ z = shifted c x ∨ ∃ b ∈ crossingPath c x, z = b.initial ∨ z = b.terminal) :
    (z : AmbientSpace) ∈ doubleCube L a' c := by
  obtain ⟨μ, s, hs, hc⟩ := exists_link_signed c
  obtain ⟨Y, hY⟩ := exists_coordVec_of_eq_mul h c.initial
  obtain ⟨X, hX⟩ := exists_coordVec x
  have hH : (c.terminal : AmbientSpace) = coordVec a' (addAt Y μ ((L : ℤ) * s)) := by
    rw [hc]
    exact coe_add_zsmul_axisStep_of_eq_mul h hY μ s
  have hx' : coordVec a' X ∈ cube L a' c.initial := by
    rw [← hX]
    exact hx
  have hB := (mem_cube_iff ha hY).1 hx'
  have htr : shifted c x = x + ((L : ℤ) * s) • axisStep a' μ := by
    apply Subtype.ext
    rw [coe_add_zsmul_axisStep hX]
    show ((x + toFiner a' (c.terminal - c.initial) : InfiniteLattice.LatticePoint a') :
      AmbientSpace) = _
    rw [AddSubgroup.coe_add, coe_toFiner (coe_mem_of_eq_mul h (c.terminal - c.initial)),
      AddSubgroup.coe_sub, hH, hY, hX]
    funext ρ
    simp only [Pi.add_apply, Pi.sub_apply, coordVec_apply, addAt]
    by_cases e : ρ = μ
    · simp only [e, if_true]
      push_cast
      ring
    · simp [e]
  have hn : (L : ℤ) * s ≠ 0 := by
    rcases hs with rfl | rfl <;> omega
  have hcross : crossingPath c x = signedSteps x μ ((L : ℤ) * s) :=
    axisPath_eq ha hn (sub_eq_of_eq_add' htr)
  have key : ∀ t : ℤ, min 0 ((L : ℤ) * s) ≤ t → t ≤ max 0 ((L : ℤ) * s) →
      ((x + t • axisStep a' μ : InfiniteLattice.LatticePoint a') : AmbientSpace) ∈
        doubleCube L a' c := by
    intro t h₁ h₂
    show _ ∈ cube L a' c.initial ∪ cube L a' c.terminal
    rw [coe_add_zsmul_axisStep hX]
    by_cases hin : 2 * |X μ + t - Y μ| ≤ (L : ℤ) - 1
    · exact Set.mem_union_left _ ((mem_cube_iff ha hY).2 (addAt_bound_left hB hin))
    · refine Set.mem_union_right _ ((mem_cube_iff ha hH).2 (addAt_bound hB ?_))
      have hbμ := hB μ
      rw [two_mul_abs_le_iff] at hbμ hin ⊢
      obtain ⟨m, hm⟩ := hodd
      rcases hs with rfl | rfl <;> omega
  rcases hz with rfl | rfl | ⟨b, hb, hz⟩
  · exact Set.mem_union_left _ hx
  · rw [htr]
    exact key _ (min_le_right _ _) (le_max_right _ _)
  · rw [hcross] at hb
    obtain ⟨t, t', e₁, e₂, h₁, h₂, h₃, h₄⟩ := mem_signedSteps hb
    rcases hz with rfl | rfl
    · rw [e₁]
      exact key t h₁ h₂
    · rw [e₂]
      exact key t' h₃ h₄
end Contours
theorem meshAt_eq_mul {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ)
    (hj : 1 ≤ j) : meshAt L k j = ((L : ℤ) : ℝ) * meshAt L k (j - 1) := by
  have := meshAt_eq_pow_mul hL k j 1 hj
  rwa [pow_one] at this
theorem odd_factor {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) : Odd (L : ℤ) := by
  have := odd_pow_factor hL 1
  rwa [pow_one] at this
theorem stepsEdgesAndCorridors {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ)
    (hj : 1 ≤ j) : StepsEdgesAndCorridors L k j := by
  have ha := meshAt_ne_zero hL k (j - 1)
  have h := meshAt_eq_mul hL k j hj
  have hodd := odd_factor hL
  have hpos : 0 < L := by
    have := hL.2
    omega
  have hposZ : 0 < (L : ℤ) := by omega
  exact
    { step_mem_cube := fun y x ν hd μ hlt => add_axisStep_mem_cube ha h hodd hd hlt
      step_mem_adjacent_cube := fun y x ν hd μ heq => add_axisStep_mem_cube_add ha h hd heq
      endpoints := fun b => endpoints_of_link ha h hodd hposZ b
      existsUnique_corridorEdge := fun c μ hc => (linkCorridor_of_sub_eq ha h hL.1 hpos hc).1
      corridorEdge_initial := fun c μ hc b hb => (linkCorridor_of_sub_eq ha h hL.1 hpos hc).2 b hb }
theorem pathsStayInCubes {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ)
    (hj : 1 ≤ j) : PathsStayInCubes L k j := by
  have ha := meshAt_ne_zero hL k (j - 1)
  have h := meshAt_eq_mul hL k j hj
  have hodd := odd_factor hL
  have hposZ : 0 < (L : ℤ) := by
    have := hL.2
    omega
  exact
    { contour_vertex_mem := fun y x hx Γ hΓ z hz =>
        contour_vertex_mem_cube ha h (by omega) hx hΓ hz
      crossing_vertex_mem := fun c x hx z hz =>
        crossing_vertex_mem_doubleCube ha h hodd hposZ c x hx hz }
theorem cubesCorridorsPivotEdgesAndPaths : CubesCorridorsPivotEdgesAndPaths := by
  intro L hL k j n _ hj _ _ hnj
  exact ⟨cubesOfOrderPartition hL k j n hnj,
    fun h2 y => cubeIsDisjointUnionOfSubcubes hL k j n h2 hnj y, stepsEdgesAndCorridors hL k j hj,
    pathsStayInCubes hL k j hj⟩
end YangMills.Construction.Tower.FullSpace.CubeCorridorProof
end
