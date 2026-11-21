import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlockProof
import YangMills.Construction.Lattice.OneStepObjectsReadInTheChartProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.AxialPathCorridorProof
open YangMills.Construction.TorusMetric
variable {L m : ℕ} {j : ℤ}
structure SitesPerAxis (L m : ℕ) (j : ℤ) (H : ℕ) : Prop where
  meshSize_pos : 0 < meshSize L j
  torusSide_eq : torusSide L m = 2 * (H : ℝ) * meshSize L j
def latticeVector (v : Fin 4 → ℤ) : Site L m j := ∑ μ, v μ • unitStep L m j μ
theorem coe_zsmul_unitStep (n : ℤ) (μ : Fin 4) :
    ((n • unitStep L m j μ : Site L m j) : FourTorus L m) =
      pointOnAxis L m μ ((n : ℝ) * meshSize L j) := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.coe_zsmul_unitStep <;> assumption
theorem coe_latticeVector_apply (v : Fin 4 → ℤ) (ν : Fin 4) :
    ((latticeVector v : Site L m j) : FourTorus L m) ν =
      (((v ν : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := by
  unfold latticeVector
  rw [AddSubgroup.val_finsetSum, Finset.sum_apply, Finset.sum_eq_single ν]
  · rw [coe_zsmul_unitStep]; simp [pointOnAxis]
  · intro μ _ h
    rw [coe_zsmul_unitStep]; simp [pointOnAxis, Pi.single_eq_of_ne h.symm]
  · simp
theorem latticeVector_add (v w : Fin 4 → ℤ) :
    (latticeVector (v + w) : Site L m j) = latticeVector v + latticeVector w := by
  simp [latticeVector, add_zsmul, Finset.sum_add_distrib]
theorem latticeVector_single (μ : Fin 4) (n : ℤ) :
    (latticeVector (Pi.single μ n) : Site L m j) = n • unitStep L m j μ := by
  unfold latticeVector
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ h
    simp [Pi.single_eq_of_ne h]
  · simp
theorem dvd_sub_of_latticeVector_eq {H : ℕ} (R : SitesPerAxis L m j H) {v w : Fin 4 → ℤ}
    (h : (latticeVector v : Site L m j) = latticeVector w) (ν : Fin 4) :
    (2 * (H : ℤ)) ∣ v ν - w ν := by
  have h1 := congrFun (congrArg (fun x : Site L m j => (x : FourTorus L m)) h) ν
  simp only [coe_latticeVector_apply] at h1
  have h2 : ((((v ν : ℝ) - (w ν : ℝ)) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
    rw [sub_mul, AddCircle.coe_sub, h1, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at h2
  obtain ⟨q, hq⟩ := h2
  refine ⟨q, ?_⟩
  have ha := R.meshSize_pos.ne'
  rw [R.torusSide_eq, zsmul_eq_mul] at hq
  have h3 : (q : ℝ) * (2 * (H : ℝ)) = (v ν : ℝ) - (w ν : ℝ) := by
    apply mul_right_cancel₀ ha
    linarith
  have h4 : ((q * (2 * (H : ℤ)) : ℤ) : ℝ) = ((v ν - w ν : ℤ) : ℝ) := by
    push_cast
    exact h3
  have h5 : q * (2 * (H : ℤ)) = v ν - w ν := by exact_mod_cast h4
  linarith
theorem eq_of_latticeVector_eq {H : ℕ} (R : SitesPerAxis L m j H) {v w : Fin 4 → ℤ}
    (h : (latticeVector v : Site L m j) = latticeVector w) (ν : Fin 4)
    (hb : |v ν - w ν| < 2 * (H : ℤ)) : v ν = w ν :=
  sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd (dvd_sub_of_latticeVector_eq R h ν) hb)
theorem exists_signed_step (b : Bond L m j) : ∃ (ν : Fin 4) (δ : ℤ), (δ = 1 ∨ δ = -1) ∧
    b.target = b.source + δ • unitStep L m j ν := by
  obtain ⟨ν, h | h⟩ := b.isNeighbour
  · exact ⟨ν, 1, Or.inl rfl, by rw [one_zsmul, ← h]; abel⟩
  · exact ⟨ν, -1, Or.inr rfl, by rw [neg_one_zsmul, ← neg_eq_iff_eq_neg.mpr h]; abel⟩
theorem bondPath_cons_iff {b : Bond L m j} {Γ : List (Bond L m j)} {x x' : Site L m j} :
    IsBondPathFromTo (b :: Γ) x x' ↔ b.source = x ∧ IsBondPathFromTo Γ b.target x' := by
  cases Γ with
  | nil => simp [IsBondPathFromTo, IsBondPath]
  | cons b' Γ =>
    simp only [IsBondPathFromTo, IsBondPath, List.isChain_cons_cons]
    simp
    tauto
theorem bondPath_nil_iff {x x' : Site L m j} :
    IsBondPathFromTo ([] : List (Bond L m j)) x x' ↔ x = x' := by
  simp [IsBondPathFromTo, IsBondPath]
theorem exists_displacement_of_bondPath (Γ : List (Bond L m j)) : ∀ x x' : Site L m j,
    IsBondPathFromTo Γ x x' →
      ∃ v : Fin 4 → ℤ, x' = x + latticeVector v ∧ ∑ ν, |v ν| ≤ (Γ.length : ℤ) := by
  induction Γ with
  | nil =>
    intro x x' h
    refine ⟨0, ?_, by simp⟩
    rw [bondPath_nil_iff.mp h]
    simp [latticeVector]
  | cons b Γ ih =>
    intro x x' h
    obtain ⟨rfl, h'⟩ := bondPath_cons_iff.mp h
    obtain ⟨v, hv, hn⟩ := ih _ _ h'
    obtain ⟨ν, δ, hδ, hb⟩ := exists_signed_step b
    refine ⟨Pi.single ν δ + v, ?_, ?_⟩
    · rw [latticeVector_add, latticeVector_single, hv, hb]; abel
    · have h1 : ∀ ρ, |(Pi.single ν δ + v : Fin 4 → ℤ) ρ| ≤
          |(Pi.single ν δ : Fin 4 → ℤ) ρ| + |v ρ| :=
        fun ρ => abs_add_le _ _
      have h2 : ∑ ρ, |(Pi.single ν δ : Fin 4 → ℤ) ρ| = 1 := by
        rw [Finset.sum_eq_single ν]
        · rcases hδ with rfl | rfl <;> simp
        · intro ρ _ h; simp [Pi.single_eq_of_ne h]
        · simp
      have h3 := Finset.sum_le_sum (s := Finset.univ) fun ρ _ => h1 ρ
      rw [Finset.sum_add_distrib, h2] at h3
      simp only [List.length_cons]
      push_cast
      linarith
theorem first_bond_of_axial {H : ℕ} (R : SitesPerAxis L m j H) {b : Bond L m j}
    {Γ : List (Bond L m j)} {x : Site L m j} {μ : Fin 4} {ε n : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hn : n = (Γ.length : ℤ) + 1) (hroom : n < H)
    (h : IsBondPathFromTo (b :: Γ) x (x + (ε * n) • unitStep L m j μ)) :
    b.source = x ∧ b.target = x + ε • unitStep L m j μ := by
  obtain ⟨rfl, h'⟩ := bondPath_cons_iff.mp h
  refine ⟨rfl, ?_⟩
  obtain ⟨v, hv, hvn⟩ := exists_displacement_of_bondPath _ _ _ h'
  obtain ⟨ν, δ, hδ, hb⟩ := exists_signed_step b
  have hE : (latticeVector (Pi.single μ (ε * n)) : Site L m j) =
      latticeVector (Pi.single ν δ + v) := by
    rw [latticeVector_add, latticeVector_single, latticeVector_single]
    rw [hb] at hv
    have := hv
    rw [add_assoc] at this
    exact add_left_cancel this
  have hvμ : |v μ| ≤ (Γ.length : ℤ) :=
    (Finset.single_le_sum (f := fun ρ => |v ρ|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ μ)).trans hvn
  have hεabs : |ε| = 1 := by rcases hε with rfl | rfl <;> simp
  have hnpos : 0 < n := by omega
  by_cases hνμ : ν = μ
  · subst hνμ
    have hc : ε * n = δ + v ν := by
      have := eq_of_latticeVector_eq R hE ν ?_
      · simpa using this
      · simp only [Pi.single_eq_same, Pi.add_apply]
        have h1 : |δ| = 1 := by rcases hδ with rfl | rfl <;> simp
        have h2 : |ε * n| = n := by rw [abs_mul, hεabs, one_mul, abs_of_pos hnpos]
        have h3 := abs_sub (ε * n) (δ + v ν)
        have h4 := abs_add_le δ (v ν)
        omega
    have : δ = ε := by
      rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
      · rfl
      · exfalso; rw [abs_le] at hvμ; omega
      · exfalso; rw [abs_le] at hvμ; omega
      · rfl
    rw [hb, this]
  · exfalso
    have hc : ε * n = v μ := by
      have := eq_of_latticeVector_eq R hE μ ?_
      · simpa [Pi.single_eq_of_ne (Ne.symm hνμ)] using this
      · simp only [Pi.single_eq_same, Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hνμ), zero_add]
        have h2 : |ε * n| = n := by rw [abs_mul, hεabs, one_mul, abs_of_pos hnpos]
        have h3 := abs_sub (ε * n) (v μ)
        omega
    have h2 : |ε * n| = n := by rw [abs_mul, hεabs, one_mul, abs_of_pos hnpos]
    rw [hc] at h2
    omega
theorem axial_bondPath_unique {H : ℕ} (R : SitesPerAxis L m j H) {μ : Fin 4} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (Γ : List (Bond L m j)) :
    ∀ (Γ' : List (Bond L m j)) (x : Site L m j), Γ'.length = Γ.length → (Γ.length : ℤ) < H →
      IsBondPathFromTo Γ x (x + (ε * (Γ.length : ℤ)) • unitStep L m j μ) →
      IsBondPathFromTo Γ' x (x + (ε * (Γ.length : ℤ)) • unitStep L m j μ) → Γ' = Γ := by
  induction Γ with
  | nil =>
    intro Γ' x hl _ _ _
    simpa using hl
  | cons b Γ ih =>
    intro Γ' x hl hroom h h'
    cases Γ' with
    | nil => simp at hl
    | cons b' Γ' =>
      have hl' : Γ'.length = Γ.length := by simpa using hl
      have e1 := first_bond_of_axial R hε (Γ := Γ) (n := ((b :: Γ).length : ℤ)) (by simp) hroom h
      have e2 := first_bond_of_axial R hε (Γ := Γ') (n := ((b :: Γ).length : ℤ))
        (by simp [hl']) hroom h'
      have hb : b' = b := Bond.ext (e2.1.trans e1.1.symm) (e2.2.trans e1.2.symm)
      subst hb
      have hend : x + (ε * ((b' :: Γ).length : ℤ)) • unitStep L m j μ =
          b'.target + (ε * (Γ.length : ℤ)) • unitStep L m j μ := by
        rw [e1.2, add_assoc, ← add_zsmul]
        congr 2
        simp
        ring
      rw [hend] at h h'
      have t1 := (bondPath_cons_iff.mp h).2
      have t2 := (bondPath_cons_iff.mp h').2
      rw [ih Γ' b'.target hl' (by simp at hroom; omega) t1 t2]
theorem bondPath_of_range (n : ℕ) : ∀ (f : ℕ → Bond L m j) (x : ℕ → Site L m j),
    (∀ s, (f s).source = x s) → (∀ s, (f s).target = x (s + 1)) →
      IsBondPathFromTo ((List.range n).map f) (x 0) (x n) := by
  induction n with
  | zero =>
    intro f x _ _
    simp [bondPath_nil_iff]
  | succ n ih =>
    intro f x ht hh
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine bondPath_cons_iff.mpr ⟨ht 0, ?_⟩
    rw [hh 0]
    exact ih (f ∘ Nat.succ) (x ∘ Nat.succ) (fun s => ht _) (fun s => hh _)
theorem forwardFlow_isBondPathFromTo (μ : Fin 4) (n : ℕ) : ∀ x : Site L m j,
    IsBondPathFromTo (forwardAxisPath x μ n) x (x + (n : ℤ) • unitStep L m j μ) := by apply _root_.YangMills.SharedProofs.p4940 <;> assumption
theorem backwardFlow_isBondPathFromTo (μ : Fin 4) (n : ℕ) : ∀ x : Site L m j,
    IsBondPathFromTo (backwardAxisPath x μ n) x (x + (-(n : ℤ)) • unitStep L m j μ) := by
  induction n with
  | zero => intro x; simp [backwardAxisPath, bondPath_nil_iff]
  | succ n ih =>
    intro x
    refine bondPath_cons_iff.mpr ⟨rfl, ?_⟩
    have := ih (x - unitStep L m j μ)
    have e : x - unitStep L m j μ + (-(n : ℤ)) • unitStep L m j μ =
        x + (-((n + 1 : ℕ) : ℤ)) • unitStep L m j μ := by
      push_cast
      rw [neg_add, add_zsmul, neg_one_zsmul]
      abel
    rw [e] at this
    exact this
theorem forwardFlow_length (x : Site L m j) (μ : Fin 4) (n : ℕ) :
    (forwardAxisPath x μ n).length = n := by apply _root_.YangMills.SharedProofs.p1058 <;> assumption
theorem backwardFlow_length (x : Site L m j) (μ : Fin 4) (n : ℕ) :
    (backwardAxisPath x μ n).length = n := by apply _root_.YangMills.SharedProofs.p8383 <;> assumption
theorem flowAlong_spec (x : Site L m j) (μ : Fin 4) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {n : ℕ}
    (hn : 0 < n) :
    IsBondPathFromTo (flowAlong x μ (ε * n)) x (x + (ε * n) • unitStep L m j μ) ∧
      (flowAlong x μ (ε * n)).length = n := by
  rcases hε with rfl | rfl
  · have h0 : (0 : ℤ) ≤ 1 * (n : ℤ) := by omega
    have h1 : (1 * (n : ℤ)).toNat = n := by omega
    simp only [flowAlong, if_pos h0, h1]
    refine ⟨?_, forwardFlow_length x μ n⟩
    have := forwardFlow_isBondPathFromTo (L := L) (m := m) (j := j) μ n x
    rwa [← one_mul (n : ℤ)] at this
  · have h0 : ¬ (0 : ℤ) ≤ -1 * (n : ℤ) := by omega
    have h1 : (-(-1 * (n : ℤ))).toNat = n := by omega
    simp only [flowAlong, if_neg h0, h1]
    refine ⟨?_, backwardFlow_length x μ n⟩
    have := backwardFlow_isBondPathFromTo (L := L) (m := m) (j := j) μ n x
    rwa [← neg_one_mul (n : ℤ)] at this
theorem bondWithEnds_spec {x y : Site L m j} (h : IsBondEndpointPair x y) :
    (bondWithEnds x y).source = x ∧ (bondWithEnds x y).target = y :=
  Classical.epsilon_spec (p := fun b : Bond L m j => b.source = x ∧ b.target = y) h
theorem isBondEndpointPair_of_step {x : Site L m j} {μ : Fin 4} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {y : Site L m j} (h : y = x + ε • unitStep L m j μ) : IsBondEndpointPair x y := by
  refine ⟨⟨x, y, μ, ?_⟩, rfl, rfl⟩
  rcases hε with rfl | rfl
  · left; rw [h, one_zsmul]; abel
  · right; rw [h, neg_one_zsmul]; abel
structure TwoLevelSetting (L m K k H : ℕ) : Prop where
  fine : SitesPerAxis L m (levelDepth K k) H
  odd : Odd L
  thirteen_le : 13 ≤ L
  room : L < H
  dvd : L ∣ H
  half : (L : ℝ) ^ ((m : ℤ) + levelDepth K k) = (H : ℝ)
  coarse_meshSize : meshSize L (levelDepth K (k + 1)) = (L : ℝ) * meshSize L (levelDepth K k)
  le : sublattice L m (levelDepth K (k + 1)) ≤ sublattice L m (levelDepth K k)
  unitBlock_eq : ∀ y : SiteAtLevel L m K (k + 1),
    unitBlock y = coordinatePoint (levelDepth K k) (y : FourTorus L m) '' blockOffsets L 1
  cover : ∀ x ∈ sublattice L m (levelDepth K k), ∃! y : SiteAtLevel L m K (k + 1), x ∈ unitBlock y
variable {K k H : ℕ}
theorem coe_toSublattice (S : TwoLevelSetting L m K k H) (y : SiteAtLevel L m K (k + 1)) :
    ((y.toSublattice (levelDepth K k) : SiteAtLevel L m K k) : FourTorus L m) = y :=
  Classical.epsilon_spec (p := fun x : SiteAtLevel L m K k => (x : FourTorus L m) = y)
    ⟨⟨y, S.le y.2⟩, rfl⟩
abbrev fineSite (K k : ℕ) (y : SiteAtLevel L m K (k + 1)) : SiteAtLevel L m K k :=
  y.toSublattice (levelDepth K k)
def HasAxisAndSign (c : BondAtLevel L m K (k + 1)) (μ : Fin 4) (ε : ℤ) : Prop :=
  (ε = 1 ∨ ε = -1) ∧
    fineSite K k c.target = fineSite K k c.source + (ε * (L : ℤ)) • unitStep L m (levelDepth K k) μ
theorem coe_coarse_unitStep (S : TwoLevelSetting L m K k H) (μ : Fin 4) :
    ((unitStep L m (levelDepth K (k + 1)) μ : Site L m (levelDepth K (k + 1))) : FourTorus L m) =
      (((L : ℤ) • unitStep L m (levelDepth K k) μ : SiteAtLevel L m K k) : FourTorus L m) := by
  rw [coe_zsmul_unitStep]
  change pointOnAxis L m μ (meshSize L (levelDepth K (k + 1))) = _
  rw [S.coarse_meshSize]
  simp
theorem fineSite_eq_add_of_sub (S : TwoLevelSetting L m K k H) (x y : SiteAtLevel L m K (k + 1))
    {w : SiteAtLevel L m K k}
    (h : ((y - x : SiteAtLevel L m K (k + 1)) : FourTorus L m) = (w : FourTorus L m)) :
    fineSite K k y = fineSite K k x + w := by
  apply Subtype.ext
  rw [AddSubgroup.coe_add, coe_toSublattice S, coe_toSublattice S, ← h, AddSubgroup.coe_sub]
  abel
theorem exists_axis_and_sign (S : TwoLevelSetting L m K k H) (c : BondAtLevel L m K (k + 1)) :
    ∃ (μ : Fin 4) (ε : ℤ), HasAxisAndSign c μ ε := by
  obtain ⟨μ, h | h⟩ := c.isNeighbour
  · refine ⟨μ, 1, Or.inl rfl, ?_⟩
    rw [one_mul]
    apply fineSite_eq_add_of_sub S
    rw [h, coe_coarse_unitStep S]
  · refine ⟨μ, -1, Or.inr rfl, ?_⟩
    rw [neg_one_mul, neg_zsmul]
    apply fineSite_eq_add_of_sub S
    rw [h, AddSubgroup.coe_neg, coe_coarse_unitStep S, AddSubgroup.coe_neg]
theorem abs_lt_of_isAxialDisplacement (S : TwoLevelSetting L m K k H) {x y : SiteAtLevel L m K k}
    {μ : Fin 4} {n : ℤ} (h : IsAxialDisplacement x y μ n) : |n| < (H : ℤ) := by
  have := h.2
  rw [S.half] at this
  exact_mod_cast this
theorem zsmul_unitStep_inj (S : TwoLevelSetting L m K k H) {μ μ' : Fin 4} {n n' : ℤ} (hn : n ≠ 0)
    (hb : |n| + |n'| < 2 * (H : ℤ)) (hb' : |n| < 2 * (H : ℤ))
    (h : n • unitStep L m (levelDepth K k) μ = n' • unitStep L m (levelDepth K k) μ') :
    μ' = μ ∧ n' = n := by
  have hv : (latticeVector (Pi.single μ n) : SiteAtLevel L m K k) =
      latticeVector (Pi.single μ' n') := by
    rw [latticeVector_single, latticeVector_single, h]
  by_cases hμ : μ' = μ
  · subst hμ
    refine ⟨rfl, ?_⟩
    have := eq_of_latticeVector_eq S.fine hv μ' (by
      simp only [Pi.single_eq_same]
      exact (abs_sub _ _).trans_lt hb)
    simpa using this.symm
  · exfalso
    have := eq_of_latticeVector_eq S.fine hv μ (by
      simpa [Pi.single_eq_of_ne (Ne.symm hμ)] using hb')
    apply hn
    simpa [Pi.single_eq_of_ne (Ne.symm hμ)] using this
section Bond
variable {c : BondAtLevel L m K (k + 1)} {μ : Fin 4} {ε : ℤ}
theorem factor_pos (S : TwoLevelSetting L m K k H) : 0 < L := by
  have := S.thirteen_le
  omega
theorem abs_sign (D : HasAxisAndSign c μ ε) : |ε| = 1 := by
  rcases D.1 with h | h <;> simp [h]
theorem abs_sign_mul (D : HasAxisAndSign c μ ε) (n : ℤ) : |ε * n| = |n| := by
  rw [abs_mul, abs_sign D, one_mul]
theorem sign_ne_zero (D : HasAxisAndSign c μ ε) : ε ≠ 0 := by
  rcases D.1 with h | h <;> simp [h]
theorem isAxialDisplacement (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    IsAxialDisplacement (fineSite K k c.source) (fineSite K k c.target) μ (ε * (L : ℤ)) := by
  refine ⟨by rw [D.2]; abel, ?_⟩
  rw [S.half, abs_sign_mul D]
  have := S.room
  simp only [Nat.abs_cast, Int.cast_natCast]
  exact_mod_cast this
theorem axialDisplacement_unique (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε)
    {μ' : Fin 4} {n : ℤ}
    (h : IsAxialDisplacement (fineSite K k c.source) (fineSite K k c.target) μ' n) :
    μ' = μ ∧ n = ε * (L : ℤ) := by
  have h1 := abs_lt_of_isAxialDisplacement S h
  have h2 := S.room
  have h3 : |ε * (L : ℤ)| = L := by rw [abs_sign_mul D]; simp
  have h4 := factor_pos S
  refine zsmul_unitStep_inj S (mul_ne_zero (sign_ne_zero D) (by omega)) (by omega) (by omega) ?_
  have := h.1
  rw [D.2] at this
  rw [← this]
  abel
theorem isPositivelyOriented_iff (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    c.IsPositivelyOriented ↔ ε = 1 := by
  constructor
  · rintro ⟨μ', h⟩
    have h1 : HasAxisAndSign c μ' 1 := ⟨Or.inl rfl, by
      rw [one_mul]
      apply fineSite_eq_add_of_sub S
      rw [h, coe_coarse_unitStep S]⟩
    have h2 := axialDisplacement_unique S D (isAxialDisplacement S h1)
    have h3 := factor_pos S
    have h4 : (1 - ε) * (L : ℤ) = 0 := by linarith [h2.2]
    rcases mul_eq_zero.mp h4 with h5 | h5 <;> omega
  · rintro rfl
    refine ⟨μ, Subtype.ext ?_⟩
    have h : c.target.toSublattice (levelDepth K k) =
        c.source.toSublattice (levelDepth K k) + (L : ℤ) • unitStep L m (levelDepth K k) μ := by
      have h' := D.2
      rwa [one_mul] at h'
    rw [coe_coarse_unitStep S, AddSubgroup.coe_sub, ← coe_toSublattice S c.target,
      ← coe_toSublattice S c.source, h, AddSubgroup.coe_add]
    abel
theorem site_succ (μ : Fin 4) (ε : ℤ) (c : BondAtLevel L m K (k + 1)) (s : ℕ) :
    axialPathSite c μ ε (s + 1) =
      axialPathSite c μ ε s + ε • unitStep L m (levelDepth K k) μ := by
  unfold axialPathSite
  rw [add_assoc, ← add_zsmul]
  congr 2
  push_cast
  ring
theorem site_pair_isBond (D : HasAxisAndSign c μ ε) (s : ℕ) :
    IsBondEndpointPair (axialPathSite c μ ε s) (axialPathSite c μ ε (s + 1)) :=
  isBondEndpointPair_of_step D.1 (site_succ μ ε c s)
theorem bond_source (D : HasAxisAndSign c μ ε) (s : ℕ) :
    (axialPathStepBond c μ ε s).source = axialPathSite c μ ε s :=
  (bondWithEnds_spec (site_pair_isBond D s)).1
theorem bond_target (D : HasAxisAndSign c μ ε) (s : ℕ) :
    (axialPathStepBond c μ ε s).target = axialPathSite c μ ε (s + 1) :=
  (bondWithEnds_spec (site_pair_isBond D s)).2
theorem site_zero (μ : Fin 4) (ε : ℤ) (c : BondAtLevel L m K (k + 1)) :
    axialPathSite c μ ε 0 = fineSite K k c.source := by
  simp [axialPathSite]
theorem site_last (D : HasAxisAndSign c μ ε) :
    axialPathSite c μ ε L = fineSite K k c.target := by
  unfold axialPathSite
  rw [D.2, mul_comm]
theorem site_eq_latticeVector (μ : Fin 4) (ε : ℤ) (c : BondAtLevel L m K (k + 1)) (s : ℕ) :
    axialPathSite c μ ε s =
      fineSite K k c.source + latticeVector (Pi.single μ ((s : ℤ) * ε)) := by
  rw [latticeVector_single]
  rfl
theorem sites_injective (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) {s s' : ℕ}
    (hs : s ≤ L) (hs' : s' ≤ L)
    (h : axialPathSite c μ ε s = axialPathSite c μ ε s') : s = s' := by
  rw [site_eq_latticeVector, site_eq_latticeVector] at h
  have h1 := eq_of_latticeVector_eq S.fine (add_left_cancel h) μ (by
    simp only [Pi.single_eq_same]
    rw [← sub_mul, mul_comm, abs_sign_mul D]
    have := S.room
    have : |(s : ℤ) - s'| ≤ L := by rw [abs_le]; omega
    omega)
  simp only [Pi.single_eq_same] at h1
  have h2 := mul_right_cancel₀ (sign_ne_zero D) h1
  exact_mod_cast h2
theorem bonds_isBondPathFromTo (D : HasAxisAndSign c μ ε) :
    IsBondPathFromTo (axialPathBonds c μ ε) (fineSite K k c.source)
      (fineSite K k c.target) := by
  have := bondPath_of_range L (axialPathStepBond c μ ε) (axialPathSite c μ ε)
    (bond_source D) (bond_target D)
  rwa [site_zero, site_last D] at this
theorem bonds_length : (axialPathBonds c μ ε).length = L := by
  simp [axialPathBonds]
theorem eq_axialPathBonds_of_length (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε)
    {Γ : List (BondAtLevel L m K k)} (hl : Γ.length = L)
    (hp : IsBondPathFromTo Γ (fineSite K k c.source) (fineSite K k c.target)) :
    Γ = axialPathBonds c μ ε := by
  have h1 := S.room
  refine axial_bondPath_unique S.fine (μ := μ) D.1 _ Γ (fineSite K k c.source)
    (by rw [hl, bonds_length]) (by rw [bonds_length]; exact_mod_cast h1) ?_ ?_
  · rw [bonds_length, ← D.2]; exact bonds_isBondPathFromTo D
  · rw [bonds_length, ← D.2]; exact hp
theorem axialPath_eq (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    axialPath (fineSite K k c.source) (fineSite K k c.target) = axialPathBonds c μ ε := by
  have hex : ∃ q : Fin 4 × ℤ, IsAxialDisplacement (fineSite K k c.source)
      (fineSite K k c.target) q.1 q.2 := ⟨(μ, ε * (L : ℤ)), isAxialDisplacement S D⟩
  unfold axialPath
  rw [dif_pos hex]
  have hq := axialDisplacement_unique S D hex.choose_spec
  rw [hq.1, hq.2]
  have hp := flowAlong_spec (fineSite K k c.source) μ D.1 (factor_pos S)
  refine eq_axialPathBonds_of_length S D hp.2 ?_
  rw [D.2]
  exact hp.1
theorem two_abs_single_le (S : TwoLevelSetting L m K k H) {a : ℤ} (h : 2 * |a| ≤ (L : ℤ) - 1)
    (ρ : Fin 4) : 2 * |(Pi.single μ a : Fin 4 → ℤ) ρ| ≤ (L : ℤ) - 1 := by
  have := S.thirteen_le
  by_cases hρ : ρ = μ
  · subst hρ; simpa using h
  · simp only [Pi.single_eq_of_ne hρ, abs_zero]; omega
theorem two_abs_single_add_single_le (S : TwoLevelSetting L m K k H) {ν : Fin 4} (hν : ν ≠ μ)
    {a : ℤ} (h : 2 * |a| ≤ (L : ℤ) - 1) (ρ : Fin 4) :
    2 * |(Pi.single μ a + Pi.single ν 1 : Fin 4 → ℤ) ρ| ≤ (L : ℤ) - 1 := by
  have := S.thirteen_le
  by_cases hρ : ρ = μ
  · subst hρ
    simpa [Pi.single_eq_of_ne hν.symm] using h
  · by_cases hρ' : ρ = ν
    · subst hρ'
      simp only [Pi.add_apply, Pi.single_eq_of_ne hρ, Pi.single_eq_same, zero_add, abs_one]
      omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hρ, Pi.single_eq_of_ne hρ', add_zero, abs_zero]
      omega
theorem mem_unitBlock (S : TwoLevelSetting L m K k H) (y : SiteAtLevel L m K (k + 1))
    {p : Fin 4 → ℤ} (hp : ∀ ρ, 2 * |p ρ| ≤ (L : ℤ) - 1) :
    ((fineSite K k y + latticeVector p : SiteAtLevel L m K k) : FourTorus L m) ∈ unitBlock y := by
  rw [S.unitBlock_eq]
  refine ⟨p, fun ρ => by simpa using hp ρ, ?_⟩
  funext ν
  rw [AddSubgroup.coe_add, coe_toSublattice S, Pi.add_apply, coe_latticeVector_apply]
  unfold coordinatePoint
  rw [Pi.add_apply, Finset.sum_apply, Finset.sum_eq_single ν]
  · simp [pointOnAxis]
  · intro ρ _ h
    simp [pointOnAxis, Pi.single_eq_of_ne h.symm]
  · simp
theorem unitBlock_unique (S : TwoLevelSetting L m K k H) {x : SiteAtLevel L m K k}
    {y y' : SiteAtLevel L m K (k + 1)} (h : (x : FourTorus L m) ∈ unitBlock y)
    (h' : (x : FourTorus L m) ∈ unitBlock y') : y = y' :=
  (S.cover x x.2).unique h h'
theorem site_eq_latticeVector_target (D : HasAxisAndSign c μ ε) (s : ℕ) :
    axialPathSite c μ ε s =
      fineSite K k c.target + latticeVector (Pi.single μ (((s : ℤ) - (L : ℤ)) * ε)) := by
  rw [latticeVector_single, D.2, add_assoc, ← add_zsmul]
  unfold axialPathSite
  congr 2
  ring
theorem site_mem_source_block (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) {s : ℕ}
    (hs : s ≤ (L - 1) / 2) :
    (axialPathSite c μ ε s : FourTorus L m) ∈ unitBlock c.source := by
  have hodd : L % 2 = 1 := Nat.odd_iff.mp S.odd
  rw [site_eq_latticeVector]
  apply mem_unitBlock S
  apply two_abs_single_le S
  rw [mul_comm _ ε, abs_sign_mul D, Nat.abs_cast]
  omega
theorem site_mem_target_block (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) {s : ℕ}
    (hs : (L + 1) / 2 ≤ s) (hs' : s ≤ L) :
    (axialPathSite c μ ε s : FourTorus L m) ∈ unitBlock c.target := by
  have hodd : L % 2 = 1 := Nat.odd_iff.mp S.odd
  rw [site_eq_latticeVector_target D]
  apply mem_unitBlock S
  apply two_abs_single_le S
  rw [mul_comm _ ε, abs_sign_mul D, abs_of_nonpos (by omega)]
  omega
theorem source_ne_target (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    c.source ≠ c.target := by
  intro h
  have h1 := sites_injective S D (Nat.zero_le L) le_rfl (by rw [site_zero, site_last D, h])
  have := factor_pos S
  omega
theorem not_mem_both_blocks (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε)
    {x : SiteAtLevel L m K k} (h : (x : FourTorus L m) ∈ unitBlock c.source)
    (h' : (x : FourTorus L m) ∈ unitBlock c.target) : False :=
  source_ne_target S D (unitBlock_unique S h h')
theorem blocks_disjoint (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    unitBlock c.source ∩ unitBlock c.target = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr ?_
  rintro x ⟨h1, h2⟩
  have e : levelDepth K (k + 1) + ((1 : ℕ) : ℤ) = levelDepth K k := by
    simp only [levelDepth]
    push_cast
    ring
  have hx : x ∈ sublattice L m (levelDepth K k) := by
    have := h1.2
    rw [e] at this
    exact this
  exact source_ne_target S D ((S.cover x hx).unique h1 h2)
theorem bond_mem_corridor_iff (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) (s : ℕ) :
    (s < L ∧ axialPathStepBond c μ ε s ∈ (bondCorridor c : Set (BondAtLevel L m K k))) ↔
      s = (L - 1) / 2 := by
  have hodd : L % 2 = 1 := Nat.odd_iff.mp S.odd
  constructor
  · rintro ⟨hs, ht, hh⟩
    rw [bond_source D] at ht
    rw [bond_target D] at hh
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact not_mem_both_blocks S D (site_mem_source_block S D (by omega)) hh
    · exact not_mem_both_blocks S D ht (site_mem_target_block S D (by omega) (by omega))
  · rintro rfl
    refine ⟨by omega, ?_, ?_⟩
    · rw [bond_source D]
      exact site_mem_source_block S D le_rfl
    · rw [bond_target D]
      exact site_mem_target_block S D (by omega) (by omega)
theorem joinsEndBlocks_iff (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) (s : ℕ) :
    (s < L ∧ JoinsEndBlocks c (axialPathStepBond c μ ε s)) ↔ s = (L - 1) / 2 := by
  have hodd : L % 2 = 1 := Nat.odd_iff.mp S.odd
  constructor
  · rintro ⟨hs, h⟩
    unfold JoinsEndBlocks at h
    rw [bond_source D, bond_target D] at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact not_mem_both_blocks S D (site_mem_source_block S D (by omega)) h2
      · exact not_mem_both_blocks S D (site_mem_source_block S D (by omega)) h1
    · rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact not_mem_both_blocks S D h1 (site_mem_target_block S D (by omega) (by omega))
      · exact not_mem_both_blocks S D h2 (site_mem_target_block S D (by omega) (by omega))
  · intro h
    have h1 := (bond_mem_corridor_iff S D s).mpr h
    exact ⟨h1.1, Or.inl h1.2⟩
theorem pivot_eq (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    (pivot c : BondAtLevel L m K k) = axialPathStepBond c μ ε ((L - 1) / 2) := by
  have hmem := (bond_mem_corridor_iff S D ((L - 1) / 2)).mpr rfl
  have hb : IsPivot (j' := levelDepth K k) c (axialPathStepBond c μ ε ((L - 1) / 2)) := by
    refine ⟨hmem.2, ?_⟩
    have : axialPath (c.source.toSublattice (levelDepth K k))
        (c.target.toSublattice (levelDepth K k)) = axialPathBonds c μ ε := axialPath_eq S D
    rw [this]
    exact List.mem_map.mpr ⟨_, List.mem_range.mpr hmem.1, rfl⟩
  have spec : IsPivot (j' := levelDepth K k) c (pivot c : BondAtLevel L m K k) :=
    Classical.epsilon_spec (p := IsPivot (j' := levelDepth K k) c) ⟨_, hb⟩
  obtain ⟨h1, h2⟩ := spec
  have h3 : (pivot c : BondAtLevel L m K k) ∈ axialPathBonds c μ ε := by
    have : axialPath (c.source.toSublattice (levelDepth K k))
        (c.target.toSublattice (levelDepth K k)) = axialPathBonds c μ ε := axialPath_eq S D
    rwa [this] at h2
  obtain ⟨s, hs, e⟩ := List.mem_map.mp h3
  have h4 := (bond_mem_corridor_iff S D s).mp ⟨List.mem_range.mp hs, by rw [e]; exact h1⟩
  rw [← e, h4]
theorem pivot_source (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    (pivot c : BondAtLevel L m K k).source = axialPathSite c μ ε ((L - 1) / 2) := by
  rw [pivot_eq S D, bond_source D]
theorem pivot_target (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    (pivot c : BondAtLevel L m K k).target = axialPathSite c μ ε ((L - 1) / 2 + 1) := by
  rw [pivot_eq S D, bond_target D]
theorem pivot_source_mem (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    ((pivot c : BondAtLevel L m K k).source : FourTorus L m) ∈ unitBlock c.source := by
  rw [pivot_source S D]
  exact site_mem_source_block S D le_rfl
theorem pivot_target_mem (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    ((pivot c : BondAtLevel L m K k).target : FourTorus L m) ∈ unitBlock c.target := by
  have hodd : L % 2 = 1 := Nat.odd_iff.mp S.odd
  rw [pivot_target S D]
  exact site_mem_target_block S D (by omega) (by omega)
theorem hasAxisAndSign_opposite (D : HasAxisAndSign c μ ε) : HasAxisAndSign c.opposite μ (-ε) := by
  refine ⟨D.1.symm.imp (fun h => by simp [h]) (fun h => by simp [h]), ?_⟩
  change fineSite K k c.source =
    fineSite K k c.target + (-ε * (L : ℤ)) • unitStep L m (levelDepth K k) μ
  rw [D.2, add_assoc, ← add_zsmul]
  simp
theorem pivot_opposite (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    (pivot c.opposite : BondAtLevel L m K k) = (pivot c : BondAtLevel L m K k).opposite := by
  obtain ⟨h, hh⟩ := S.odd
  have e : (L - 1) / 2 = h := by omega
  have hz : (L : ℤ) = 2 * (h : ℤ) + 1 := by omega
  have D' := hasAxisAndSign_opposite D
  apply Bond.ext
  · rw [pivot_source S D']
    change _ = (pivot c : BondAtLevel L m K k).target
    rw [pivot_target S D, e]
    change fineSite K k c.target + ((h : ℤ) * -ε) • unitStep L m (levelDepth K k) μ =
      fineSite K k c.source + (((h + 1 : ℕ) : ℤ) * ε) • unitStep L m (levelDepth K k) μ
    rw [D.2, add_assoc, ← add_zsmul]
    congr 2
    push_cast
    rw [hz]
    ring
  · rw [pivot_target S D']
    change _ = (pivot c : BondAtLevel L m K k).source
    rw [pivot_source S D, e]
    change fineSite K k c.target + (((h + 1 : ℕ) : ℤ) * -ε) • unitStep L m (levelDepth K k) μ =
      fineSite K k c.source + ((h : ℤ) * ε) • unitStep L m (levelDepth K k) μ
    rw [D.2, add_assoc, ← add_zsmul]
    congr 2
    push_cast
    rw [hz]
    ring
theorem pivot_step (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    (pivot c : BondAtLevel L m K k).target =
      (pivot c : BondAtLevel L m K k).source + ε • unitStep L m (levelDepth K k) μ := by
  rw [pivot_source S D, pivot_target S D, site_succ]
theorem pivot_isPositivelyOriented_iff (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    (pivot c : BondAtLevel L m K k).IsPositivelyOriented ↔ c.IsPositivelyOriented := by
  rw [isPositivelyOriented_iff S D]
  constructor
  · rintro ⟨μ', h⟩
    rw [pivot_step S D] at h
    have hr := S.room
    have hL := factor_pos S
    have h1 : ε • unitStep L m (levelDepth K k) μ = (1 : ℤ) • unitStep L m (levelDepth K k) μ' := by
      rw [one_zsmul, ← h]
      abel
    have h2 := zsmul_unitStep_inj S (sign_ne_zero D) (by rw [abs_sign D]; simp; omega)
      (by rw [abs_sign D]; omega) h1
    exact h2.2.symm
  · rintro rfl
    refine ⟨μ, ?_⟩
    rw [pivot_step S D, one_zsmul]
    abel
theorem pivot_source_mem_union_iff (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε)
    (Θ : Set (SiteAtLevel L m K (k + 1))) :
    ((pivot c : BondAtLevel L m K k).source : FourTorus L m) ∈ refinedBlockUnion 1 Θ ↔
      c.source ∈ Θ := by
  constructor
  · intro h
    obtain ⟨y, hy, h⟩ := mem_iUnion₂.mp h
    rwa [← unitBlock_unique S h (pivot_source_mem S D)]
  · intro h
    exact mem_iUnion₂.mpr ⟨_, h, pivot_source_mem S D⟩
theorem pivot_target_mem_union_iff (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε)
    (Θ : Set (SiteAtLevel L m K (k + 1))) :
    ((pivot c : BondAtLevel L m K k).target : FourTorus L m) ∈ refinedBlockUnion 1 Θ ↔
      c.target ∈ Θ := by
  constructor
  · intro h
    obtain ⟨y, hy, h⟩ := mem_iUnion₂.mp h
    rwa [← unitBlock_unique S h (pivot_target_mem S D)]
  · intro h
    exact mem_iUnion₂.mpr ⟨_, h, pivot_target_mem S D⟩
theorem pivot_injective (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε)
    (c' : BondAtLevel L m K (k + 1))
    (h : (pivot c' : BondAtLevel L m K k) = pivot c) : c' = c := by
  obtain ⟨μ', ε', D'⟩ := exists_axis_and_sign S c'
  apply Bond.ext
  · have h1 := pivot_source_mem S D'
    rw [h] at h1
    exact unitBlock_unique S h1 (pivot_source_mem S D)
  · have h1 := pivot_target_mem S D'
    rw [h] at h1
    exact unitBlock_unique S h1 (pivot_target_mem S D)
theorem coe_target (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    (c.target : FourTorus L m) =
      (c.source : FourTorus L m) +
        pointOnAxis L m μ ((L : ℝ) * ε * meshSize L (levelDepth K k)) := by
  have h := congrArg (fun x : SiteAtLevel L m K k => (x : FourTorus L m)) D.2
  simp only [AddSubgroup.coe_add] at h
  rw [coe_toSublattice S, coe_toSublattice S, coe_zsmul_unitStep] at h
  rw [h]
  congr 2
  push_cast
  ring
theorem bondSegment_inter_sublattice (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    bondSegment c μ ε ∩ (sublattice L m (levelDepth K (k + 1)) : Set (FourTorus L m)) =
      {(c.source : FourTorus L m), (c.target : FourTorus L m)} := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast factor_pos S
  have hε2 : (ε : ℝ) * ε = 1 := by rcases D.1 with h | h <;> simp [h]
  ext p
  constructor
  · rintro ⟨⟨t, ht0, ht1, rfl⟩, hp⟩
    have hax : pointOnAxis L m μ (t * ε * meshSize L (levelDepth K k)) ∈
        sublattice L m (levelDepth K (k + 1)) := by
      have h1 := (sublattice L m (levelDepth K (k + 1))).sub_mem hp c.source.2
      simpa using h1
    obtain ⟨n, hn⟩ := hax
    have h1 := hn μ
    simp only [pointOnAxis, Pi.single_eq_same] at h1
    rw [S.coarse_meshSize] at h1
    have h2 : (((t * ε - n μ * L) * meshSize L (levelDepth K k) : ℝ) :
        AddCircle (torusSide L m)) = 0 := by
      rw [sub_mul, AddCircle.coe_sub, h1, ← mul_assoc, sub_eq_zero]
    rw [AddCircle.coe_eq_zero_iff] at h2
    obtain ⟨q, hq⟩ := h2
    obtain ⟨H', hH'⟩ := S.dvd
    have ha := S.fine.meshSize_pos.ne'
    rw [S.fine.torusSide_eq, zsmul_eq_mul] at hq
    have h3 : (t * ε - n μ * L) = q * (2 * (H : ℝ)) := by
      apply mul_right_cancel₀ ha
      linarith
    have hHr : (H : ℝ) = L * H' := by exact_mod_cast hH'
    set u : ℤ := ε * (n μ + q * (2 * (H' : ℤ))) with hu
    have h4 : t = L * (u : ℝ) := by
      have h5 : t * ε = L * ((n μ : ℝ) + q * (2 * (H' : ℝ))) := by
        rw [hHr] at h3
        linarith
      calc t = t * ε * ε := by rw [mul_assoc, hε2, mul_one]
        _ = L * (u : ℝ) := by
          rw [h5, hu]
          push_cast
          ring
    have h6 : (0 : ℝ) ≤ u := by
      by_contra hneg
      have : (L : ℝ) * u < 0 := mul_neg_of_pos_of_neg hLpos (not_le.mp hneg)
      linarith
    have h7 : (u : ℝ) ≤ 1 := by
      by_contra hbig
      have : (L : ℝ) * 1 < L * u := mul_lt_mul_of_pos_left (not_le.mp hbig) hLpos
      linarith
    have h6' : 0 ≤ u := by exact_mod_cast h6
    have h7' : u ≤ 1 := by exact_mod_cast h7
    have h8 : u = 0 ∨ u = 1 := by omega
    rcases h8 with h8 | h8
    · left
      have : t = 0 := by rw [h4, h8]; simp
      simp [this, pointOnAxis]
    · right
      have : t = L := by rw [h4, h8]; simp
      rw [mem_singleton_iff, coe_target S D, this]
  · intro hp
    rcases hp with rfl | hp
    · exact ⟨⟨0, le_rfl, by positivity, by simp [pointOnAxis]⟩, c.source.2⟩
    · rw [mem_singleton_iff] at hp
      subst hp
      exact ⟨⟨L, hLpos.le, le_rfl, coe_target S D⟩, c.target.2⟩
theorem shifted_step (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) (ν : Fin 4) :
    (pivot c : BondAtLevel L m K k).target + unitStep L m (levelDepth K k) ν =
      ((pivot c : BondAtLevel L m K k).source + unitStep L m (levelDepth K k) ν) +
        ε • unitStep L m (levelDepth K k) μ := by
  rw [pivot_step S D]
  abel
theorem shifted_isBond (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) (ν : Fin 4) :
    IsBondEndpointPair ((pivot c : BondAtLevel L m K k).source + unitStep L m (levelDepth K k) ν)
      ((pivot c : BondAtLevel L m K k).target + unitStep L m (levelDepth K k) ν) :=
  isBondEndpointPair_of_step D.1 (shifted_step S D ν)
theorem shifted_source_eq (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) (ν : Fin 4) :
    (pivot c : BondAtLevel L m K k).source + unitStep L m (levelDepth K k) ν =
      fineSite K k c.source +
        latticeVector (Pi.single μ ((((L - 1) / 2 : ℕ) : ℤ) * ε) + Pi.single ν 1) := by
  rw [pivot_source S D, site_eq_latticeVector, latticeVector_add, latticeVector_single ν,
    one_zsmul, add_assoc]
theorem shifted_target_eq (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) (ν : Fin 4) :
    (pivot c : BondAtLevel L m K k).target + unitStep L m (levelDepth K k) ν =
      fineSite K k c.target +
        latticeVector (Pi.single μ (((((L - 1) / 2 + 1 : ℕ) : ℤ) - (L : ℤ)) * ε) +
          Pi.single ν 1) := by
  rw [pivot_target S D, site_eq_latticeVector_target D, latticeVector_add,
    latticeVector_single ν, one_zsmul, add_assoc]
theorem shifted_mem_corridor (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε)
    {ν : Fin 4} (hν : ν ≠ μ) :
    bondWithEnds ((pivot c : BondAtLevel L m K k).source + unitStep L m (levelDepth K k) ν)
      ((pivot c : BondAtLevel L m K k).target + unitStep L m (levelDepth K k) ν) ∈
        (bondCorridor c : Set (BondAtLevel L m K k)) := by
  have hodd : L % 2 = 1 := Nat.odd_iff.mp S.odd
  have hL := S.thirteen_le
  have hs := bondWithEnds_spec (shifted_isBond S D ν)
  refine ⟨?_, ?_⟩
  · rw [hs.1, shifted_source_eq S D]
    apply mem_unitBlock S
    apply two_abs_single_add_single_le S hν
    rw [mul_comm _ ε, abs_sign_mul D, Nat.abs_cast]
    omega
  · rw [hs.2, shifted_target_eq S D]
    apply mem_unitBlock S
    apply two_abs_single_add_single_le S hν
    rw [mul_comm _ ε, abs_sign_mul D, abs_of_nonpos (by omega)]
    omega
theorem shifted_ne (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) {ν : Fin 4}
    (hν : ν ≠ μ) (s : ℕ) :
    bondWithEnds ((pivot c : BondAtLevel L m K k).source + unitStep L m (levelDepth K k) ν)
      ((pivot c : BondAtLevel L m K k).target + unitStep L m (levelDepth K k) ν) ≠
        axialPathStepBond c μ ε s := by
  intro h
  have h1 := congrArg Bond.source h
  rw [(bondWithEnds_spec (shifted_isBond S D ν)).1, bond_source D, shifted_source_eq S D,
    site_eq_latticeVector] at h1
  have hr := S.room
  have hL := factor_pos S
  have h2 := eq_of_latticeVector_eq S.fine (add_left_cancel h1) ν (by
    simp [Pi.single_eq_of_ne hν]
    omega)
  simp [Pi.single_eq_of_ne hν] at h2
theorem axialPathAndPivot_of_bond (S : TwoLevelSetting L m K k H) (D : HasAxisAndSign c μ ε) :
    AxialPathAndPivot c μ ε where
  isPositivelyOriented_iff := isPositivelyOriented_iff S D
  site_zero := site_zero μ ε c
  site_last := site_last D
  site_injOn := fun _ hs _ hs' h => sites_injective S D hs hs' h
  consecutive_isBond := fun s _ => site_pair_isBond D s
  stepBond_injOn := fun s hs s' hs' h => by
    have h1 := congrArg Bond.source h
    rw [bond_source D, bond_source D] at h1
    exact sites_injective S D (le_of_lt hs) (le_of_lt hs') h1
  isBondPath := bonds_isBondPathFromTo D
  eq_of_length_eq := fun _ hl hp => eq_axialPathBonds_of_length S D hl hp
  axialPath_eq := axialPath_eq S D
  unitBlock_inter_eq_empty := blocks_disjoint S D
  site_mem_source_block := fun _ hs => site_mem_source_block S D hs
  site_mem_target_block := fun _ hs hs' => site_mem_target_block S D hs hs'
  stepBond_within_source_block := fun s hs => by
    have hodd : L % 2 = 1 := Nat.odd_iff.mp S.odd
    rw [bond_source D, bond_target D]
    exact ⟨site_mem_source_block S D (by omega), site_mem_source_block S D (by omega)⟩
  stepBond_within_target_block := fun s hs hs' => by
    have hodd : L % 2 = 1 := Nat.odd_iff.mp S.odd
    rw [bond_source D, bond_target D]
    exact ⟨site_mem_target_block S D (by omega) (by omega),
      site_mem_target_block S D (by omega) (by omega)⟩
  middle_stepBond_mem := by
    have h1 := (bond_mem_corridor_iff S D ((L - 1) / 2)).mpr rfl
    exact h1.2
  stepBond_mem_bondCorridor_iff := bond_mem_corridor_iff S D
  joinsEndBlocks_iff := joinsEndBlocks_iff S D
  pivot_eq := pivot_eq S D
  pivot_source := pivot_source S D
  pivot_target := by
    have hodd : L % 2 = 1 := Nat.odd_iff.mp S.odd
    have e : (L + 1) / 2 = (L - 1) / 2 + 1 := by omega
    rw [e]
    exact pivot_target S D
  pivot_source_mem := pivot_source_mem S D
  pivot_target_mem := pivot_target_mem S D
  pivot_opposite := pivot_opposite S D
  pivot_isPositivelyOriented_iff := pivot_isPositivelyOriented_iff S D
  pivot_source_mem_iff := pivot_source_mem_union_iff S D
  pivot_target_mem_iff := pivot_target_mem_union_iff S D
  pivot_endpoint_mem_iff := fun Θ => by
    rw [pivot_source_mem_union_iff S D, pivot_target_mem_union_iff S D]
  eq_of_pivot_eq := pivot_injective S D
  source_ne_target := source_ne_target S D
  bondSegment_inter_sublattice := bondSegment_inter_sublattice S D
  translated_pivot_isBond := fun ν _ => shifted_isBond S D ν
  translated_pivot_mem_bondCorridor := fun _ hν => shifted_mem_corridor S D hν
  translated_pivot_ne_stepBond := fun _ hν s _ => shifted_ne S D hν s
end Bond
theorem meshSizesInLevelUnits (S : TwoLevelSetting L m K k H) (hH : H = L ^ (m + K - k)) :
    MeshSizesInLevelUnits L m K k := by
  have hL : (L : ℝ) ≠ 0 := by
    have := S.thirteen_le
    exact_mod_cast (by omega : L ≠ 0)
  refine ⟨?_, ?_, ?_⟩
  · unfold toLevelUnits meshSize
    rw [← zpow_add₀ hL]
    simp
  · unfold toLevelUnits meshSize
    rw [← zpow_add₀ hL]
    have e : levelDepth K k + -levelDepth K (k + 1) = 1 := by
      simp only [levelDepth]
      push_cast
      ring
    rw [e, zpow_one]
  · unfold toLevelUnits torusSide
    have h1 := S.half
    rw [zpow_add₀ hL, zpow_natCast, hH] at h1
    push_cast at h1
    rw [← h1]
    ring
theorem twoLevelSetting (h : RefinedBlockCoordinatesHold) {L m K k : ℕ} (hodd : Odd L)
    (h13 : 13 ≤ L) (hK : 0 < K) (hm : 0 < m) (hk : k < K) :
    TwoLevelSetting L m K k (L ^ (m + K - k)) := by
  have hstd : Averaging.LayerwiseParameters 4 2 L K m Matrices.ComplexMatrix2.specialUnitary
      (torusSide L m) :=
    ⟨rfl, rfl, rfl, hodd, h13, hK, hm, rfl⟩
  have hlev := (h L K m hstd).2.1 k (k + 1) (Nat.le_succ k) hk
  unfold LevelSublatticesInCoordinates at hlev
  rw [show k + 1 - k = 1 by omega] at hlev
  obtain ⟨⟨-, hfin, hblk, hcov⟩, -, hsites, -, -, hle⟩ := hlev
  have hLpos : 0 < L := by omega
  have hsp : 0 < meshSize L (levelDepth K k) := by
    unfold meshSize
    exact zpow_pos (by exact_mod_cast hLpos) _
  refine ⟨⟨hsp, ?_⟩, hodd, h13, ?_, ?_, ?_, ?_, hle, fun y => (hblk y).1,
    fun x hx => (hcov.1 x hx).2⟩
  · rw [hfin.2.1, hsites]
    push_cast
    ring
  · calc L = L ^ 1 := (pow_one L).symm
      _ < L ^ (m + K - k) := Nat.pow_lt_pow_right (by omega) (by omega)
  · exact dvd_pow_self L (by omega)
  · have e : (m : ℤ) + levelDepth K k = ((m + K - k : ℕ) : ℤ) := by
      simp only [levelDepth]
      omega
    rw [e, zpow_natCast]
    push_cast
    rfl
  · have := hfin.1
    simpa using this
theorem axialPathCorridorAndPivot (h : RefinedBlockCoordinatesHold) :
    AxialPathCorridorAndPivotStatement := by
  intro s k hk
  have S := twoLevelSetting h s.isAdmissible.1 s.isAdmissible.2 s.K.pos s.m.pos hk
  refine ⟨meshSizesInLevelUnits S rfl, fun c => ?_⟩
  obtain ⟨μ, ε, D⟩ := exists_axis_and_sign S c
  refine ⟨⟨(μ, ε * (s.L : ℤ)), isAxialDisplacement S D, ?_⟩, μ, ε, D.1,
    isAxialDisplacement S D, axialPathAndPivot_of_bond S D⟩
  rintro ⟨μ', n⟩ hq
  have := axialDisplacement_unique S D hq
  exact Prod.ext this.1 this.2
end YangMills.Construction.PeriodicLattice.AxialPathCorridorProof
