import YangMills.Construction.Lattice.LiftsOfCubesVerticesAndEdges
import YangMills.Construction.Lattice.StandardPartitionsAndLevelUnits
import YangMills.Construction.Lattice.TorusAsAQuotientInLevelUnits
import YangMills.Construction.SeparatedSequences.SitesBondsCubesAndCellsAreFinite
import Mathlib
set_option autoImplicit false
open Set
namespace YangMills.Construction.PeriodicLattice.CubeLifts
theorem int_le_of_scaled_le {M : ℝ} (hM : 0 < M) {a b : ℤ} (h : M * a ≤ M * b) : a ≤ b := by
  exact_mod_cast le_of_mul_le_mul_left h hM
theorem half_shift_eq_or {M : ℝ} (hM : 0 < M) {a b : ℤ}
    (hl : M * b - M / 2 ≤ M * ((a : ℝ) + 1 / 2)) (hu : M * ((a : ℝ) + 1 / 2) ≤ M * b + M / 2) :
    M * ((a : ℝ) + 1 / 2) = M * b + M / 2 ∨ M * ((a : ℝ) + 1 / 2) = M * b - M / 2 := by
  have h1 : a ≤ b := int_le_of_scaled_le hM (by linarith)
  have h2 : b - 1 ≤ a := int_le_of_scaled_le hM (by push_cast; linarith)
  obtain h | h : a = b ∨ a = b - 1 := by omega
  · left; subst h; ring
  · right; subst h; push_cast; ring
theorem edge_coord_cases {M t : ℝ} (hM : 0 < M) {a b : ℤ} (ht0 : 0 ≤ t) (ht1 : t ≤ M)
    (hl : M * b - M / 2 ≤ M * ((a : ℝ) + 1 / 2) + t)
    (hu : M * ((a : ℝ) + 1 / 2) + t ≤ M * b + M / 2) :
    ((M * b - M / 2 ≤ M * ((a : ℝ) + 1 / 2) ∧ M * ((a : ℝ) + 1 / 2) ≤ M * b + M / 2) ∨
      (M * b - M / 2 ≤ M * ((a : ℝ) + 1 / 2) + M ∧ M * ((a : ℝ) + 1 / 2) + M ≤ M * b + M / 2)) ∧
    (0 < t → t < M → M * ((a : ℝ) + 1 / 2) = M * b - M / 2) := by
  have h1 : a ≤ b := int_le_of_scaled_le hM (by linarith)
  have h2 : b - 2 ≤ a := int_le_of_scaled_le hM (by push_cast; linarith)
  obtain h | h | h : a = b ∨ a = b - 1 ∨ a = b - 2 := by omega
  · subst h
    refine ⟨Or.inl ⟨by linarith, by linarith⟩, fun h0 _ => ?_⟩
    linarith
  · subst h
    push_cast at hl hu ⊢
    refine ⟨Or.inl ⟨by linarith, by linarith⟩, fun _ _ => ?_⟩
    ring
  · subst h
    push_cast at hl hu ⊢
    refine ⟨Or.inr ⟨by linarith, by linarith⟩, fun _ h1 => ?_⟩
    linarith
theorem le_abs_mul_int {M : ℝ} (hM : 0 < M) {k n : ℕ} (hk : k ≤ n) {a : ℤ} (ha : a ≠ 0) :
    (k : ℝ) * M ≤ |(n : ℝ) * M * (a : ℝ)| := by
  have h1 : (1 : ℝ) ≤ |(a : ℝ)| := by
    have : (1 : ℤ) ≤ |a| := Int.one_le_abs ha
    exact_mod_cast this
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  rw [abs_mul, abs_mul, abs_of_pos hM, Nat.abs_cast]
  calc (k : ℝ) * M ≤ (n : ℝ) * M := by gcongr
    _ ≤ (n : ℝ) * M * |(a : ℝ)| := le_mul_of_one_le_right (by positivity) h1
theorem add_smul_coordVec_of_ne (w : Fin 4 → ℝ) {μ ν : Fin 4} (t : ℝ) (h : μ ≠ ν) :
    (w + t • coordVec ν) μ = w μ := by
  simp [coordVec, Pi.single_eq_of_ne h]
theorem add_smul_coordVec_self (w : Fin 4 → ℝ) (ν : Fin 4) (t : ℝ) :
    (w + t • coordVec ν) ν = w ν + t := by
  simp [coordVec]
theorem exists_sign_vector {M : ℝ} (hM : 0 < M) (c x : Fin 4 → ℝ)
    (h : ∀ μ, x μ = c μ + M / 2 ∨ x μ = c μ - M / 2) :
    ∃ ε, LevelUnitPartition.IsSigns ε ∧ x = c + (M / 2) • ε ∧
      ∀ μ, x μ = c μ - M / 2 → ε μ = -1 := by
  classical
  refine ⟨fun μ => if x μ = c μ + M / 2 then 1 else -1, fun μ => ?_, ?_, fun μ hμ => ?_⟩
  · by_cases hx : x μ = c μ + M / 2 <;> simp [hx]
  · funext μ
    by_cases hx : x μ = c μ + M / 2
    · simp [hx]
    · have := (h μ).resolve_left hx
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_neg hx]
      linarith
  · have hne : x μ ≠ c μ + M / 2 := by
      rw [hμ]; intro h'; linarith
    simp [hne]
variable (S : LevelUnitPartition)
theorem thirteen_le_L : 13 ≤ S.params.L := S.params.isAdmissible.2
theorem L_ne_zero : S.params.L ≠ 0 := by
  have := thirteen_le_L S
  omega
theorem L_cast_ne_zero : (S.params.L : ℝ) ≠ 0 := by
  exact_mod_cast L_ne_zero S
theorem side_pos : 0 < S.side :=
  Nat.pow_pos (Nat.pos_of_ne_zero (L_ne_zero S))
theorem side_cast_pos : (0 : ℝ) < (S.side : ℝ) := by
  exact_mod_cast side_pos S
def countExp : ℕ := ((S.params.m : ℤ) + S.index).toNat
theorem countExp_cast :
    ((countExp S : ℕ) : ℤ) =
      ((S.params.m : ℕ) : ℤ) + ((S.params.K : ℕ) : ℤ) - S.level - S.sideExponent := by
  have h := S.inRange.2
  simp only [countExp, LevelUnitPartition.index, coarseCubeIndex, scaledCubeIndex, levelDepth]
  omega
theorem cubeCount_eq : S.cubeCount = 2 * S.params.L ^ countExp S := rfl
theorem cubeCount_cases :
    (countExp S = 0 ∧ S.cubeCount = 2) ∨ (1 ≤ countExp S ∧ 2 * S.params.L ≤ S.cubeCount) := by
  rcases Nat.eq_zero_or_pos (countExp S) with h | h
  · left
    exact ⟨h, by rw [cubeCount_eq, h]; simp⟩
  · right
    refine ⟨h, ?_⟩
    rw [cubeCount_eq]
    have h1 : S.params.L ^ 1 ≤ S.params.L ^ countExp S :=
      Nat.pow_le_pow_right (Nat.pos_of_ne_zero (L_ne_zero S)) h
    rw [pow_one] at h1
    omega
theorem two_le_cubeCount : 2 ≤ S.cubeCount := by
  have := thirteen_le_L S
  rcases cubeCount_cases S with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
theorem three_le_cubeCount_iff : 3 ≤ S.cubeCount ↔ 1 ≤ countExp S := by
  have := thirteen_le_L S
  rcases cubeCount_cases S with ⟨h1, h⟩ | ⟨h1, h⟩ <;> omega
theorem cubeCount_eq_two_iff : S.cubeCount = 2 ↔ countExp S = 0 := by
  have := thirteen_le_L S
  rcases cubeCount_cases S with ⟨h1, h⟩ | ⟨h1, h⟩ <;> omega
theorem scaledTorusSide_eq :
    scaledTorusSide S = (S.cubeCount : ℝ) * (S.side : ℝ) := by
  have hL := L_cast_ne_zero S
  have he := countExp_cast S
  simp only [scaledTorusSide, Conventions.StandingParameters.side, torusSide, cubeCount_eq,
    LevelUnitPartition.side, levelDepth]
  push_cast
  rw [← zpow_natCast (S.params.L : ℝ) (S.params.m : ℕ),
    ← zpow_natCast (S.params.L : ℝ) (countExp S),
    ← zpow_natCast (S.params.L : ℝ) S.sideExponent, mul_assoc, mul_assoc,
    ← zpow_add₀ hL, ← zpow_add₀ hL]
  congr 2
  rw [he]
  ring
theorem toLevelUnits_meshSize_index :
    toLevelUnits S.params.L S.params.K S.level (meshSize S.params.L S.index) =
      (S.side : ℝ) := by
  have hL := L_cast_ne_zero S
  simp only [toLevelUnits, meshSize, LevelUnitPartition.index, coarseCubeIndex, scaledCubeIndex,
    LevelUnitPartition.side, levelDepth]
  push_cast
  rw [← zpow_add₀ hL, ← zpow_natCast (S.params.L : ℝ) S.sideExponent]
  congr 1
  ring
theorem side_mul_meshSize :
    (S.side : ℝ) * meshSize S.params.L (levelDepth S.params.K S.level) =
      meshSize S.params.L S.index := by
  have hL := L_cast_ne_zero S
  simp only [meshSize, LevelUnitPartition.index, coarseCubeIndex, scaledCubeIndex,
    LevelUnitPartition.side, levelDepth]
  push_cast
  rw [← zpow_natCast (S.params.L : ℝ) S.sideExponent, ← zpow_add₀ hL]
  congr 1
  ring
theorem proj_eq_coverMap (w : Fin 4 → ℝ) :
    S.proj w = LevelUnits.coverMap S.params S.level w := rfl
theorem proj_add (a b : Fin 4 → ℝ) : S.proj (a + b) = S.proj a + S.proj b := by
  simp only [proj_eq_coverMap, map_add]
theorem isPointLift_iff (x : S.Points) (w : Fin 4 → ℝ) : S.IsPointLift x w ↔ S.proj w = x :=
  (levelProj_eq_iff_isLevelLift (L_ne_zero S) _ _ _ x w).symm
theorem proj_eq_proj_iff (hQ : TorusQuotientInLevelUnits) (w w' : Fin 4 → ℝ) :
    S.proj w = S.proj w' ↔ IsPeriodVector S (w - w') := by
  have h := hQ S.params S.level S.inRange.1
  dsimp only at h
  obtain ⟨h1, _, _, _, h5⟩ := h
  have hN : sideInLevelUnits S.params.L S.params.m S.params.K S.level =
      (S.cubeCount : ℝ) * (S.side : ℝ) := by
    rw [← h1, ← scaledTorusSide_eq, scaledTorusSide, mul_comm]
  refine (h5 w w').trans ?_
  simp only [IsPeriodVector, Pi.sub_apply, hN]
theorem proj_surjective (hQ : TorusQuotientInLevelUnits) :
    Function.Surjective S.proj := by
  have h := hQ S.params S.level S.inRange.1
  dsimp only at h
  exact h.2.2.1
theorem edgeAt_congr {w w' : Fin 4 → ℝ} (h : S.proj w = S.proj w') (ν : Fin 4) :
    S.edgeAt w ν = S.edgeAt w' ν := by
  ext p
  simp only [LevelUnitPartition.edgeAt, mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨t, h0, h1, rfl⟩, rfl⟩
    exact ⟨w' + t • coordVec ν, ⟨t, h0, h1, rfl⟩, by rw [proj_add, proj_add, h]⟩
  · rintro ⟨x, ⟨t, h0, h1, rfl⟩, rfl⟩
    exact ⟨w + t • coordVec ν, ⟨t, h0, h1, rfl⟩, by rw [proj_add, proj_add, h]⟩
theorem exists_site_of_centre (hS : StandardPartitionsInUnits) {c : Fin 4 → ℝ}
    (hc : IsCubeCentre S c) :
    ∃ y : Site S.params.L S.params.m S.index, (y : S.Points) = S.proj c ∧
      cubeAround y = S.proj '' S.closedBox c := by
  have hi : -((S.params.m : ℕ) : ℤ) ≤ S.index := by
    have h := S.inRange.2
    simp only [LevelUnitPartition.index, coarseCubeIndex, scaledCubeIndex, levelDepth]
    omega
  have hu := toLevelUnits_meshSize_index S
  obtain ⟨z, hz, hcube⟩ := ((((hS S.params).1 S.index S.index hi le_rfl).2.2 S.level
    S.inRange.1).1) c (fun ν => by
      obtain ⟨a, ha⟩ := hc ν
      exact ⟨a, by rw [hu]; exact ha⟩)
  refine ⟨z, hz, ?_⟩
  rw [hcube, hu]
  have hset : (Set.pi univ fun ν => Icc (c ν - 1 / 2 * (S.side : ℝ))
      (c ν + 1 / 2 * (S.side : ℝ))) = S.closedBox c := by
    ext x
    constructor
    · intro h μ
      have := h μ (mem_univ μ)
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    · intro h μ _
      have := h μ
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
  rw [hset]
  rfl
theorem isCubeCentre_of_lift (hQ : TorusQuotientInLevelUnits)
    (y : Site S.params.L S.params.m S.index) {c : Fin 4 → ℝ}
    (h : S.IsPointLift (y : S.Points) c) : IsCubeCentre S c := by
  obtain ⟨n, hn⟩ : ∃ n : Fin 4 → ℤ, ∀ μ, (y : S.Points) μ =
      (((n μ : ℝ) * meshSize S.params.L S.index : ℝ) : AddCircle (torusSide S.params.L S.params.m)) :=
    y.2
  have hcov : S.proj (fun μ => (S.side : ℝ) * (n μ : ℝ)) = (y : S.Points) := by
    funext μ
    rw [hn μ, ← side_mul_meshSize]
    change (((meshSize S.params.L (levelDepth S.params.K S.level) *
      ((S.side : ℝ) * (n μ : ℝ)) : ℝ)) : AddCircle (torusSide S.params.L S.params.m)) = _
    congr 1
    ring
  have h1 : S.proj c = S.proj (fun μ => (S.side : ℝ) * (n μ : ℝ)) := by
    rw [hcov]; exact (isPointLift_iff S _ _).1 h
  obtain ⟨a, ha⟩ := (proj_eq_proj_iff S hQ _ _).1 h1
  intro μ
  refine ⟨n μ + (S.cubeCount : ℤ) * a μ, ?_⟩
  have := ha μ
  simp only [Pi.sub_apply] at this
  push_cast
  linarith
theorem mem_closedBox_self (c : Fin 4 → ℝ) : c ∈ S.closedBox c := by
  have hM := side_cast_pos S
  intro μ
  exact ⟨by linarith, by linarith⟩
theorem eq_of_mem_closedBox {c c' : Fin 4 → ℝ} (hc : IsCubeCentre S c)
    (hc' : IsCubeCentre S c') (h : c' ∈ S.closedBox c) : c' = c := by
  have hM := side_cast_pos S
  funext μ
  obtain ⟨a, ha⟩ := hc μ
  obtain ⟨b, hb⟩ := hc' μ
  obtain ⟨h1, h2⟩ := h μ
  rw [ha, hb] at h1 h2
  have h3 : b ≤ a := int_le_of_scaled_le hM (by
    have : (S.side : ℝ) * (b : ℝ) < (S.side : ℝ) * ((a : ℝ) + 1) := by linarith
    have h4 : b < a + 1 := by
      have h5 := lt_of_mul_lt_mul_left this hM.le
      exact_mod_cast h5
    have h6 : (b : ℝ) ≤ a := by exact_mod_cast (by omega : b ≤ a)
    exact mul_le_mul_of_nonneg_left h6 hM.le)
  have h3' : a ≤ b := int_le_of_scaled_le hM (by
    have : (S.side : ℝ) * (a : ℝ) < (S.side : ℝ) * ((b : ℝ) + 1) := by linarith
    have h4 : a < b + 1 := by
      have h5 := lt_of_mul_lt_mul_left this hM.le
      exact_mod_cast h5
    have h6 : (a : ℝ) ≤ b := by exact_mod_cast (by omega : a ≤ b)
    exact mul_le_mul_of_nonneg_left h6 hM.le)
  have : a = b := le_antisymm h3' h3
  rw [ha, hb, this]
theorem siteAndCubeLifts (hS : StandardPartitionsInUnits)
    (hQ : TorusQuotientInLevelUnits)
    (hF : SeparatedSequences.CellSetting.Finiteness.Statement) :
    SiteAndCubeLifts S := by
  have hcube : ∀ (y : Site S.params.L S.params.m S.index) (c : Fin 4 → ℝ),
      S.IsPointLift (y : S.Points) c → cubeAround y = S.proj '' S.closedBox c := by
    intro y c h
    obtain ⟨z, hz, hzc⟩ := exists_site_of_centre S hS (isCubeCentre_of_lift S hQ y h)
    have : z = y := Subtype.ext (hz.trans ((isPointLift_iff S _ _).1 h))
    rw [← this, hzc]
  refine ⟨fun c => ⟨?_, ?_⟩, hcube, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    exact isCubeCentre_of_lift S hQ y hy
  · intro hc
    obtain ⟨y, hy, _⟩ := exists_site_of_centre S hS hc
    exact ⟨y, (isPointLift_iff S _ _).2 hy.symm⟩
  · intro y y' hne heq
    apply hne
    obtain ⟨c, hc⟩ := proj_surjective S hQ (y : S.Points)
    obtain ⟨c', hc'⟩ := proj_surjective S hQ (y' : S.Points)
    have hl := (isPointLift_iff S _ _).2 hc
    have hl' := (isPointLift_iff S _ _).2 hc'
    have hmem : (y' : S.Points) ∈ S.proj '' S.closedBox c := by
      rw [← hcube y c hl, heq, hcube y' c' hl']
      exact ⟨c', mem_closedBox_self S c', hc'⟩
    obtain ⟨x, hx, hxy⟩ := hmem
    have hxl : IsCubeCentre S x := isCubeCentre_of_lift S hQ y' ((isPointLift_iff S _ _).2 hxy)
    have := eq_of_mem_closedBox S (isCubeCentre_of_lift S hQ y hl) hxl hx
    apply Subtype.ext
    rw [← hc, ← hxy, this]
  · have hi : -((S.params.m : ℕ) : ℤ) ≤ S.index := by
      have h := S.inRange.2
      simp only [LevelUnitPartition.index, coarseCubeIndex, scaledCubeIndex, levelDepth]
      omega
    exact ((hF.1 S.params.L S.params.m S.params.K S.params.isAdmissible.1
      S.params.isAdmissible.2 S.params.m.pos S.params.K.pos).2.2 S.index hi)
theorem centre_add_smul_mem {c ε : Fin 4 → ℝ} (hc : IsCubeCentre S c)
    (hε : LevelUnitPartition.IsSigns ε) :
    c + ((S.side : ℝ) / 2) • ε ∈ S.vertexSet := by
  intro μ
  obtain ⟨a, ha⟩ := hc μ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha]
  rcases hε μ with h | h
  · exact ⟨a, by rw [h]; ring⟩
  · exact ⟨a - 1, by rw [h]; push_cast; ring⟩
noncomputable def upperCentre (w : Fin 4 → ℝ) : Fin 4 → ℝ := fun μ => w μ + (S.side : ℝ) / 2
theorem upperCentre_isCubeCentre {w : Fin 4 → ℝ} (hw : w ∈ S.vertexSet) :
    IsCubeCentre S (upperCentre S w) := by
  intro μ
  obtain ⟨a, ha⟩ := hw μ
  exact ⟨a + 1, by simp only [upperCentre, ha]; push_cast; ring⟩
theorem eq_upperCentre_add (w : Fin 4 → ℝ) :
    w = upperCentre S w + ((S.side : ℝ) / 2) • (fun _ => (-1 : ℝ)) := by
  funext μ
  simp [upperCentre]
theorem isSigns_neg_one : LevelUnitPartition.IsSigns (fun _ => (-1 : ℝ)) :=
  fun _ => Or.inr rfl
theorem isVertex_and_isEdge (hS : StandardPartitionsInUnits)
    {w : Fin 4 → ℝ} (hw : w ∈ S.vertexSet) :
    S.IsVertex (S.proj w) ∧ ∀ ν, S.IsEdge (S.edgeAt w ν) := by
  obtain ⟨y, hy, _⟩ := exists_site_of_centre S hS (upperCentre_isCubeCentre S hw)
  have hlift : S.IsPointLift (y : S.Points) (upperCentre S w) := (isPointLift_iff S _ _).2 hy.symm
  have hpart : cubeAround y ∈ S.cubes := ⟨y, rfl⟩
  refine ⟨⟨cubeAround y, hpart, y, rfl, upperCentre S w, hlift, fun _ => -1, isSigns_neg_one,
    by rw [← eq_upperCentre_add]⟩, fun ν => ⟨cubeAround y, hpart, y, rfl, upperCentre S w, hlift,
    fun _ => -1, ν, isSigns_neg_one, rfl, by rw [← eq_upperCentre_add]⟩⟩
theorem mem_vertexSet_of_proj_eq (hQ : TorusQuotientInLevelUnits)
    {w w' : Fin 4 → ℝ} (hw : w ∈ S.vertexSet) (h : S.proj w' = S.proj w) :
    w' ∈ S.vertexSet := by
  obtain ⟨a, ha⟩ := (proj_eq_proj_iff S hQ _ _).1 h
  intro μ
  obtain ⟨b, hb⟩ := hw μ
  refine ⟨b + (S.cubeCount : ℤ) * a μ, ?_⟩
  have := ha μ
  simp only [Pi.sub_apply] at this
  push_cast
  rw [hb] at this
  linarith
noncomputable def gridVertex (z : Fin 4 → Fin S.cubeCount) : Fin 4 → ℝ :=
  fun μ => (S.side : ℝ) * (((z μ : ℕ) : ℝ) + 1 / 2)
theorem exists_gridVertex (hQ : TorusQuotientInLevelUnits) {w : Fin 4 → ℝ}
    (hw : w ∈ S.vertexSet) : ∃ z, S.proj w = S.proj (gridVertex S z) := by
  choose a ha using hw
  have hn : (0 : ℤ) < (S.cubeCount : ℤ) := by
    have := two_le_cubeCount S
    omega
  have hlt : ∀ μ, (a μ % (S.cubeCount : ℤ)).toNat < S.cubeCount := fun μ => by
    have h1 := Int.emod_nonneg (a μ) hn.ne'
    have h2 := Int.emod_lt_of_pos (a μ) hn
    omega
  refine ⟨fun μ => ⟨_, hlt μ⟩, (proj_eq_proj_iff S hQ _ _).2
    ⟨fun μ => a μ / (S.cubeCount : ℤ), fun μ => ?_⟩⟩
  have h1 := Int.emod_nonneg (a μ) hn.ne'
  have h2 : (((a μ % (S.cubeCount : ℤ)).toNat : ℤ)) = a μ % (S.cubeCount : ℤ) :=
    Int.toNat_of_nonneg h1
  have h3 : a μ = (((a μ % (S.cubeCount : ℤ)).toNat : ℤ)) +
      (S.cubeCount : ℤ) * (a μ / (S.cubeCount : ℤ)) := by
    rw [h2]; exact (Int.emod_add_mul_ediv _ _).symm
  have h4 : (a μ : ℝ) = (((a μ % (S.cubeCount : ℤ)).toNat : ℕ) : ℝ) +
      (S.cubeCount : ℝ) * ((a μ / (S.cubeCount : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast h3
  simp only [Pi.sub_apply, gridVertex, ha μ]
  rw [h4]
  ring
theorem vertexAndEdgeLifts (hS : StandardPartitionsInUnits)
    (hQ : TorusQuotientInLevelUnits) : VertexAndEdgeLifts S := by
  have hM := side_cast_pos S
  have hV : ∀ v : S.Points, S.IsVertex v ↔ ∃ w ∈ S.vertexSet, v = S.proj w := by
    intro v
    constructor
    · rintro ⟨Δ, _, y, _, c, hc, ε, hε, hv⟩
      exact ⟨_, centre_add_smul_mem S (isCubeCentre_of_lift S hQ y hc) hε, hv⟩
    · rintro ⟨w, hw, rfl⟩
      exact (isVertex_and_isEdge S hS hw).1
  have hE : ∀ e : Set S.Points, S.IsEdge e ↔
      ∃ w ∈ S.vertexSet, ∃ ν, e = S.edgeAt w ν := by
    intro e
    constructor
    · rintro ⟨Δ, _, y, _, c, hc, ε, ν, hε, _, he⟩
      exact ⟨_, centre_add_smul_mem S (isCubeCentre_of_lift S hQ y hc) hε, ν, he⟩
    · rintro ⟨w, hw, ν, rfl⟩
      exact (isVertex_and_isEdge S hS hw).2 ν
  refine ⟨hV, ?_, hE, ?_, ?_, ?_⟩
  · intro v w hv hl
    obtain ⟨w₀, hw₀, rfl⟩ := (hV v).1 hv
    exact mem_vertexSet_of_proj_eq S hQ hw₀ ((isPointLift_iff S _ _).1 hl)
  · refine (Set.finite_range fun z => S.proj (gridVertex S z)).subset ?_
    intro v hv
    obtain ⟨w, hw, rfl⟩ := (hV v).1 hv
    obtain ⟨z, hz⟩ := exists_gridVertex S hQ hw
    exact ⟨z, hz.symm⟩
  · refine (Set.finite_range fun q : (Fin 4 → Fin S.cubeCount) × Fin 4 =>
      S.edgeAt (gridVertex S q.1) q.2).subset ?_
    intro e he
    obtain ⟨w, hw, ν, rfl⟩ := (hE e).1 he
    obtain ⟨z, hz⟩ := exists_gridVertex S hQ hw
    exact ⟨(z, ν), (edgeAt_congr S hz ν).symm⟩
  · intro c hc
    ext x
    constructor
    · rintro ⟨hx, hxV⟩
      obtain ⟨ε, hε, hxε, _⟩ := exists_sign_vector hM c x (fun μ => by
        obtain ⟨b, hb⟩ := hc μ
        obtain ⟨a, ha⟩ := hxV μ
        obtain ⟨h1, h2⟩ := hx μ
        rw [ha, hb] at h1 h2
        rw [ha, hb]
        exact half_shift_eq_or hM h1 h2)
      exact ⟨ε, hε, hxε⟩
    · rintro ⟨ε, hε, rfl⟩
      refine ⟨fun μ => ?_, centre_add_smul_mem S hc hε⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases hε μ with h | h <;> rw [h] <;> exact ⟨by linarith, by linarith⟩
theorem edgePointsInCube (hS : StandardPartitionsInUnits) :
    EdgePointsInCube S := by
  intro c w ν t hc hw ht0 ht1 hmem
  have hM := side_cast_pos S
  have hother : ∀ μ, μ ≠ ν → w μ ∈ Icc (c μ - (S.side : ℝ) / 2) (c μ + (S.side : ℝ) / 2) :=
    fun μ h => by
      have := hmem μ
      rwa [add_smul_coordVec_of_ne w t h] at this
  have hν := hmem ν
  rw [add_smul_coordVec_self] at hν
  obtain ⟨b, hb⟩ := hc ν
  obtain ⟨a, ha⟩ := hw ν
  rw [ha, hb] at hν
  obtain ⟨hA, hB⟩ := edge_coord_cases hM ht0 ht1 hν.1 hν.2
  refine ⟨?_, fun h0 h1 => ?_⟩
  · rcases hA with hA | hA
    · left
      intro μ
      by_cases h : μ = ν
      · subst h; rw [ha, hb]; exact hA
      · exact hother μ h
    · right
      intro μ
      by_cases h : μ = ν
      · subst h; rw [add_smul_coordVec_self, ha, hb]; exact hA
      · rw [add_smul_coordVec_of_ne w _ h]; exact hother μ h
  · have hwν := hB h0 h1
    obtain ⟨ε, hε, hwε, hneg⟩ := exists_sign_vector hM c w (fun μ => by
      by_cases h : μ = ν
      · subst h
        right
        rw [ha, hb]
        exact hwν
      · obtain ⟨b', hb'⟩ := hc μ
        obtain ⟨a', ha'⟩ := hw μ
        obtain ⟨h1, h2⟩ := hother μ h
        rw [ha', hb'] at h1 h2
        rw [ha', hb']
        exact half_shift_eq_or hM h1 h2)
    have hεν : ε ν = -1 := hneg ν (by rw [ha, hb]; exact hwν)
    refine ⟨⟨ε, hε, hεν, hwε⟩, ?_⟩
    obtain ⟨y, hy, hcube⟩ := exists_site_of_centre S hS (c := c) (by
      intro μ
      exact hc μ)
    refine ⟨y, hcube.symm, c, (isPointLift_iff S _ _).2 hy.symm, ε, ν, hε, hεν, ?_⟩
    rw [← hwε]
theorem shortVectorsNotPeriods (_hQ : TorusQuotientInLevelUnits) :
    ShortVectorsNotPeriods S := by
  have hM := side_cast_pos S
  have hnz : ∀ r : Fin 4 → ℝ, r ≠ 0 → ∃ μ, r μ ≠ 0 := fun r hr => by
    by_contra h
    exact hr (funext fun μ => by_contra fun h' => h ⟨μ, h'⟩)
  constructor
  · rintro r hr hcomp ⟨a, ha⟩
    obtain ⟨μ, hμ⟩ := hnz r hr
    have ha0 : a μ ≠ 0 := fun h => hμ (by rw [ha μ, h]; simp)
    have h1 := le_abs_mul_int hM (two_le_cubeCount S) ha0
    rw [← ha μ] at h1
    push_cast at h1
    rcases hcomp μ with h | h | h
    · exact hμ h
    · rw [h, abs_of_pos hM] at h1; linarith
    · rw [h, abs_neg, abs_of_pos hM] at h1; linarith
  · rintro h3 r hr hcomp ⟨a, ha⟩
    obtain ⟨μ, hμ⟩ := hnz r hr
    have ha0 : a μ ≠ 0 := fun h => hμ (by rw [ha μ, h]; simp)
    have h1 := le_abs_mul_int hM h3 ha0
    rw [← ha μ] at h1
    push_cast at h1
    have h2 : (0 : ℝ) < 2 * (S.side : ℝ) := by linarith
    rcases hcomp μ with h | h | h | h | h
    · exact hμ h
    · rw [h, abs_of_pos hM] at h1; linarith
    · rw [h, abs_neg, abs_of_pos hM] at h1; linarith
    · rw [h, abs_of_pos h2] at h1; linarith
    · rw [h, abs_neg, abs_of_pos h2] at h1; linarith
theorem torusInCubeUnits (hQ : TorusQuotientInLevelUnits) :
    TorusInCubeUnits S := by
  have hsurj := proj_surjective S hQ
  refine ⟨?_, side_mul_meshSize S, rfl, toLevelUnits_meshSize_index S, ?_, scaledTorusSide_eq S,
    ?_, ?_, ?_, two_le_cubeCount S, side_pos S⟩
  · have h := S.inRange.2
    simp only [LevelUnitPartition.index, coarseCubeIndex, scaledCubeIndex, levelDepth]
    omega
  · simp only [toLevelUnits, scaledTorusSide, Conventions.StandingParameters.side, mul_comm]
  · intro x
    obtain ⟨w, hw⟩ := hsurj x
    exact ⟨w, (isPointLift_iff S _ _).2 hw⟩
  · intro w w'
    rw [← proj_eq_proj_iff S hQ]
    constructor
    · rintro ⟨x, h, h'⟩
      rw [(isPointLift_iff S _ _).1 h, (isPointLift_iff S _ _).1 h']
    · intro h
      exact ⟨_, (isPointLift_iff S _ _).2 rfl, (isPointLift_iff S _ _).2 h.symm⟩
  · exact ⟨S.params.L ^ countExp S, by rw [cubeCount_eq]; ring⟩
theorem cubeCountDichotomy : CubeCountDichotomy S := by
  have hM := side_cast_pos S
  have he := countExp_cast S
  have h3 := three_le_cubeCount_iff S
  have h2 := cubeCount_eq_two_iff S
  have hside := scaledTorusSide_eq S
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hside, mul_le_mul_iff_left₀ hM]
    exact_mod_cast Iff.rfl
  · omega
  · intro h
    rcases cubeCount_cases S with ⟨_, h'⟩ | ⟨_, h'⟩ <;> omega
  · rw [Xor]
    omega
  · rw [hside]
    constructor
    · intro h; rw [h]; norm_num
    · intro h
      have := mul_right_cancel₀ hM.ne' h
      exact_mod_cast this
  · omega
  · omega
  · omega
theorem dataOrdering : DataOrdering := by
  refine ⟨fun m' k m K _ _ => ⟨?_, ?_, ?_, ?_⟩, fun m' k => ?_⟩
  · simp only [RegionCells.LevelInRange]
    omega
  · omega
  · omega
  · omega
  · omega
theorem three_le_cubeCount_iff_add : 3 ≤ S.cubeCount ↔
    S.sideExponent + S.level + 1 ≤ (S.params.m : ℕ) + (S.params.K : ℕ) := by
  have he := countExp_cast S
  have h3 := three_le_cubeCount_iff S
  omega
theorem admissibleData : AdmissibleData := by
  refine ⟨fun S => ?_, fun L m' k hL => ?_, fun s m' k hm hk => ?_⟩
  · have he := countExp_cast S
    have h2 := cubeCount_eq_two_iff S
    have hform := S.inRange
    simp only [RegionCells.LevelInRange] at hform
    refine ⟨hform.1, ?_, three_le_cubeCount_iff_add S, ?_⟩ <;> omega
  · let s : Conventions.StandingParameters := ⟨L, hL, ⟨k + 1, Nat.succ_pos k⟩, ⟨m' + 1, Nat.succ_pos m'⟩⟩
    have hform : RegionCells.LevelInRange s.m s.K m' k := by
      simp only [RegionCells.LevelInRange, s, PNat.mk_coe]
      push_cast
      omega
    refine ⟨⟨s, m', k, hform⟩, rfl, rfl, rfl, ?_⟩
    refine (three_le_cubeCount_iff_add _).2 ?_
    simp only [s, PNat.mk_coe]
    omega
  · have hform : RegionCells.LevelInRange s.m s.K m' k := by
      simp only [RegionCells.LevelInRange]
      omega
    refine ⟨⟨s, m', k, hform⟩, rfl, rfl, rfl, ?_⟩
    refine (three_le_cubeCount_iff_add _).2 ?_
    show m' + k + 1 ≤ (s.m : ℕ) + (s.K : ℕ)
    omega
theorem statement_holds (hS : StandardPartitionsInUnits)
    (hQ : TorusQuotientInLevelUnits)
    (hF : SeparatedSequences.CellSetting.Finiteness.Statement) : Statement :=
  ⟨dataOrdering, admissibleData, fun S =>
    ⟨torusInCubeUnits S hQ, cubeCountDichotomy S, siteAndCubeLifts S hS hQ hF,
      vertexAndEdgeLifts S hS hQ, edgePointsInCube S hS, shortVectorsNotPeriods S hQ⟩⟩
end YangMills.Construction.PeriodicLattice.CubeLifts
