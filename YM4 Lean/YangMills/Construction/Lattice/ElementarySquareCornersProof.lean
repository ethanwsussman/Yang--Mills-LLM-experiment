import YangMills.Construction.Lattice.ElementarySquareCorners
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ElementarySquare
section Coordinates
variable {C : Type} [AddCommGroup C]
private def axisPoint (φ : ℝ → C) (μ : Fin 4) (t : ℝ) : Fin 4 → C := Pi.single μ (φ t)
private theorem vertex_coord_cases (φ : ℝ → C) (a : ℝ) {x c : Fin 4 → C} {μ ν : Fin 4} (hμν : μ ≠ ν)
    (hc : c ∈ vertexList (axisPoint φ) a x μ ν) (ρ : Fin 4) :
    c ρ = x ρ ∨ (c ρ = x ρ + φ a ∧ (ρ = μ ∨ ρ = ν)) := by
  simp only [vertexList, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · by_cases h : ρ = μ
    · subst h
      right
      simp [axisPoint]
    · left
      simp [axisPoint, Pi.single_eq_of_ne h]
  · by_cases h : ρ = μ
    · subst h
      right
      simp [axisPoint, Pi.single_eq_of_ne hμν]
    · by_cases h' : ρ = ν
      · subst h'
        right
        simp [axisPoint, Pi.single_eq_of_ne h]
      · left
        simp [axisPoint, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
  · by_cases h : ρ = ν
    · subst h
      right
      simp [axisPoint]
    · left
      simp [axisPoint, Pi.single_eq_of_ne h]
private theorem axis_of_coord_ne (φ : ℝ → C) (a : ℝ) {x c c' : Fin 4 → C} {μ ν ρ : Fin 4}
    (hμν : μ ≠ ν) (hc : c ∈ vertexList (axisPoint φ) a x μ ν)
    (hc' : c' ∈ vertexList (axisPoint φ) a x μ ν) (h : c ρ ≠ c' ρ) : ρ = μ ∨ ρ = ν := by
  rcases vertex_coord_cases φ a hμν hc ρ with h1 | ⟨-, h1⟩
  · rcases vertex_coord_cases φ a hμν hc' ρ with h2 | ⟨-, h2⟩
    · exact absurd (h1.trans h2.symm) h
    · exact h2
  · exact h1
private theorem self_mem_vertexList (φ : ℝ → C) (a : ℝ) (x : Fin 4 → C) (μ ν : Fin 4) :
    x ∈ vertexList (axisPoint φ) a x μ ν := by
  simp [vertexList]
private theorem add_low_mem_vertexList (φ : ℝ → C) (a : ℝ) (x : Fin 4 → C) (μ ν : Fin 4) :
    x + axisPoint φ μ a ∈ vertexList (axisPoint φ) a x μ ν := by
  simp [vertexList]
private theorem add_high_mem_vertexList (φ : ℝ → C) (a : ℝ) (x : Fin 4 → C) (μ ν : Fin 4) :
    x + axisPoint φ ν a ∈ vertexList (axisPoint φ) a x μ ν := by
  simp [vertexList]
private theorem vertexList_nodup (φ : ℝ → C) (a : ℝ) (hb : φ a ≠ 0) (x : Fin 4 → C) {μ ν : Fin 4}
    (hμν : μ ≠ ν) : (vertexList (axisPoint φ) a x μ ν).Nodup := by
  have hμ : ∀ y z : Fin 4 → C, y = z → y μ = z μ := fun _ _ h => congrFun h μ
  have hν : ∀ y z : Fin 4 → C, y = z → y ν = z ν := fun _ _ h => congrFun h ν
  simp only [vertexList, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> intro h
  · have := hμ _ _ h
    simp [axisPoint, hb] at this
  · have := hμ _ _ h
    simp [axisPoint, hb, Pi.single_eq_of_ne hμν] at this
  · have := hν _ _ h
    simp [axisPoint, hb] at this
  · have := hν _ _ h
    simp [axisPoint, hb, Pi.single_eq_of_ne hμν.symm] at this
  · have := hμ _ _ h
    simp [axisPoint, hb, Pi.single_eq_of_ne hμν] at this
  · have := hμ _ _ h
    simp [axisPoint, hb, Pi.single_eq_of_ne hμν] at this
private theorem eq_of_add_mem_pair {p q b : C} (hb : b ≠ 0) (hb2 : b + b ≠ 0)
    (h1 : p = q ∨ p = q + b) (h2 : p + b = q ∨ p + b = q + b) : p = q := by
  rcases h1 with h1 | h1
  · exact h1
  · exfalso
    subst h1
    rcases h2 with h2 | h2
    · apply hb2
      have : q + (b + b) = q + 0 := by rw [add_zero, ← add_assoc]; exact h2
      exact add_left_cancel this
    · apply hb
      have : q + b + b = q + b + 0 := by rw [add_zero]; exact h2
      exact add_left_cancel this
private theorem eq_of_vertexList_eq (φ : ℝ → C) (a : ℝ) (hb : φ a ≠ 0) (hb2 : φ a + φ a ≠ 0)
    {x x' : Fin 4 → C} {μ ν μ' ν' : Fin 4} (hμν : μ < ν) (hμν' : μ' < ν')
    (hS : {c | c ∈ vertexList (axisPoint φ) a x μ ν} = {c | c ∈ vertexList (axisPoint φ) a x' μ' ν'}) :
    x = x' ∧ μ = μ' ∧ ν = ν' := by
  have hne : μ ≠ ν := hμν.ne
  have hne' : μ' ≠ ν' := hμν'.ne
  have toRight : ∀ c, c ∈ vertexList (axisPoint φ) a x μ ν → c ∈ vertexList (axisPoint φ) a x' μ' ν' :=
    fun c hc => by
      have : c ∈ {c | c ∈ vertexList (axisPoint φ) a x' μ' ν'} := hS ▸ hc
      exact this
  have toLeft : ∀ c, c ∈ vertexList (axisPoint φ) a x' μ' ν' → c ∈ vertexList (axisPoint φ) a x μ ν :=
    fun c hc => by
      have : c ∈ {c | c ∈ vertexList (axisPoint φ) a x μ ν} := hS ▸ hc
      exact this
  have differs : ∀ (y : Fin 4 → C) (ρ : Fin 4), y ρ ≠ (y + axisPoint φ ρ a) ρ := by
    intro y ρ h
    simp [axisPoint, hb] at h
  have h1 : μ = μ' ∨ μ = ν' :=
    axis_of_coord_ne φ a hne' (toRight _ (self_mem_vertexList φ a x μ ν))
      (toRight _ (add_low_mem_vertexList φ a x μ ν)) (differs x μ)
  have h2 : ν = μ' ∨ ν = ν' :=
    axis_of_coord_ne φ a hne' (toRight _ (self_mem_vertexList φ a x μ ν))
      (toRight _ (add_high_mem_vertexList φ a x μ ν)) (differs x ν)
  have h3 : μ' = μ ∨ μ' = ν :=
    axis_of_coord_ne φ a hne (toLeft _ (self_mem_vertexList φ a x' μ' ν'))
      (toLeft _ (add_low_mem_vertexList φ a x' μ' ν')) (differs x' μ')
  have h4 : ν' = μ ∨ ν' = ν :=
    axis_of_coord_ne φ a hne (toLeft _ (self_mem_vertexList φ a x' μ' ν'))
      (toLeft _ (add_high_mem_vertexList φ a x' μ' ν')) (differs x' ν')
  have hdir : μ = μ' ∧ ν = ν' := by
    simp only [Fin.ext_iff, Fin.lt_def] at *
    omega
  obtain ⟨rfl, rfl⟩ := hdir
  refine ⟨?_, rfl, rfl⟩
  have hbase := toRight _ (self_mem_vertexList φ a x μ ν)
  have hlow := toRight _ (add_low_mem_vertexList φ a x μ ν)
  have hhigh := toRight _ (add_high_mem_vertexList φ a x μ ν)
  funext ρ
  by_cases hρμ : ρ = μ
  · subst hρμ
    have e1 := vertex_coord_cases φ a hne hbase ρ
    have e2 := vertex_coord_cases φ a hne hlow ρ
    have hv : (x + axisPoint φ ρ a) ρ = x ρ + φ a := by simp [axisPoint]
    rw [hv] at e2
    exact eq_of_add_mem_pair hb hb2 (e1.imp_right And.left) (e2.imp_right And.left)
  · by_cases hρν : ρ = ν
    · subst hρν
      have e1 := vertex_coord_cases φ a hne hbase ρ
      have e2 := vertex_coord_cases φ a hne hhigh ρ
      have hv : (x + axisPoint φ ρ a) ρ = x ρ + φ a := by simp [axisPoint]
      rw [hv] at e2
      exact eq_of_add_mem_pair hb hb2 (e1.imp_right And.left) (e2.imp_right And.left)
    · rcases vertex_coord_cases φ a hne hbase ρ with h | ⟨-, h⟩
      · exact h
      · exact absurd h (by simp [hρμ, hρν])
private theorem planePoint_apply (φ : ℝ → C) (a : ℝ) (x : Fin 4 → C) {μ ν : Fin 4} (hμν : μ ≠ ν)
    (s t : ℝ) :
    planePoint (axisPoint φ) a x μ ν s t μ = x μ + φ (s * a) ∧
      planePoint (axisPoint φ) a x μ ν s t ν = x ν + φ (t * a) ∧
      ∀ ρ, ρ ≠ μ → ρ ≠ ν → planePoint (axisPoint φ) a x μ ν s t ρ = x ρ := by
  refine ⟨?_, ?_, fun ρ h1 h2 => ?_⟩
  · simp [planePoint, axisPoint, Pi.single_eq_of_ne hμν]
  · simp [planePoint, axisPoint, Pi.single_eq_of_ne hμν.symm]
  · simp [planePoint, axisPoint, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
private theorem squareFacts_of_coord (φ : ℝ → C) (a : ℝ) (Z : AddSubgroup C)
    (Λ : AddSubgroup (Fin 4 → C)) (hΛ : ∀ x, x ∈ Λ ↔ ∀ μ, x μ ∈ Z) (h0 : φ 0 = 0)
    (hZ : ∀ r : ℝ, φ (r * a) ∈ Z ↔ ∃ n : ℤ, r = n) (hb : φ a ≠ 0) (hb2 : φ a + φ a ≠ 0) :
    SquareFacts Λ (axisPoint φ) a := by
  have hbZ : φ a ∈ Z := by
    have := (hZ 1).2 ⟨1, by simp⟩
    rwa [one_mul] at this
  have vertexMem : ∀ x ∈ Λ, ∀ μ ν : Fin 4, μ ≠ ν → ∀ c ∈ vertexList (axisPoint φ) a x μ ν, c ∈ Λ := by
    intro x hx μ ν hne c hc
    rw [hΛ] at hx ⊢
    intro ρ
    rcases vertex_coord_cases φ a hne hc ρ with h | ⟨h, -⟩
    · rw [h]
      exact hx ρ
    · rw [h]
      exact Z.add_mem (hx ρ) hbZ
  have vertexFace : ∀ (x : Fin 4 → C) (μ ν : Fin 4), ∀ c ∈ vertexList (axisPoint φ) a x μ ν,
      c ∈ filledSquare (axisPoint φ) a x μ ν := by
    intro x μ ν c hc
    have e0 : axisPoint φ μ 0 = 0 := by simp [axisPoint, h0]
    have e0' : axisPoint φ ν 0 = 0 := by simp [axisPoint, h0]
    simp only [vertexList, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨0, 0, le_rfl, zero_le_one, le_rfl, zero_le_one, by simp [planePoint, e0, e0']⟩
    · exact ⟨1, 0, zero_le_one, le_rfl, le_rfl, zero_le_one, by simp [planePoint, e0']⟩
    · exact ⟨1, 1, zero_le_one, le_rfl, zero_le_one, le_rfl, by simp [planePoint]⟩
    · exact ⟨0, 1, le_rfl, zero_le_one, zero_le_one, le_rfl, by simp [planePoint, e0]⟩
  have memLattice : ∀ x ∈ Λ, ∀ μ ν : Fin 4, μ ≠ ν → ∀ s t : ℝ,
      (planePoint (axisPoint φ) a x μ ν s t ∈ Λ ↔ (∃ n : ℤ, s = n) ∧ ∃ n : ℤ, t = n) := by
    intro x hx μ ν hne s t
    obtain ⟨p1, p2, p3⟩ := planePoint_apply φ a x hne s t
    have hx' := (hΛ x).1 hx
    rw [hΛ]
    constructor
    · intro h
      have h1 := h μ
      have h2 := h ν
      rw [p1] at h1
      rw [p2] at h2
      exact ⟨(hZ s).1 ((Z.add_mem_cancel_left (hx' μ)).1 h1),
        (hZ t).1 ((Z.add_mem_cancel_left (hx' ν)).1 h2)⟩
    · rintro ⟨hs, ht⟩ ρ
      by_cases h1 : ρ = μ
      · subst h1
        rw [p1]
        exact Z.add_mem (hx' _) ((hZ s).2 hs)
      · by_cases h2 : ρ = ν
        · subst h2
          rw [p2]
          exact Z.add_mem (hx' _) ((hZ t).2 ht)
        · rw [p3 ρ h1 h2]
          exact hx' ρ
  have meet : ∀ x ∈ Λ, ∀ μ ν : Fin 4, μ ≠ ν →
      (Λ : Set (Fin 4 → C)) ∩ filledSquare (axisPoint φ) a x μ ν =
        {c | c ∈ vertexList (axisPoint φ) a x μ ν} := by
    intro x hx μ ν hne
    ext p
    constructor
    · rintro ⟨hp, s, t, hs0, hs1, ht0, ht1, rfl⟩
      obtain ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩ := (memLattice x hx μ ν hne s t).1 hp
      have hm0 : 0 ≤ m := by exact_mod_cast hs0
      have hm1 : m ≤ 1 := by exact_mod_cast hs1
      have hn0 : 0 ≤ n := by exact_mod_cast ht0
      have hn1 : n ≤ 1 := by exact_mod_cast ht1
      have e0 : axisPoint φ μ 0 = 0 := by simp [axisPoint, h0]
      have e0' : axisPoint φ ν 0 = 0 := by simp [axisPoint, h0]
      have hm : m = 0 ∨ m = 1 := by omega
      have hn : n = 0 ∨ n = 1 := by omega
      rcases hm with rfl | rfl <;> rcases hn with rfl | rfl
      · simp [planePoint, vertexList, e0, e0']
      · simp [planePoint, vertexList, e0]
      · simp [planePoint, vertexList, e0']
      · simp [planePoint, vertexList]
    · intro hp
      exact ⟨vertexMem x hx μ ν hne p hp, vertexFace x μ ν p hp⟩
  intro x hx x' hx' μ ν μ' ν' hμν hμν'
  refine ⟨⟨vertexMem x hx μ ν hμν.ne, vertexList_nodup φ a hb x hμν.ne⟩,
    eq_of_vertexList_eq φ a hb hb2 hμν hμν', memLattice x hx μ ν hμν.ne, meet x hx μ ν hμν.ne, ?_⟩
  intro hsq
  refine eq_of_vertexList_eq φ a hb hb2 hμν hμν' ?_
  rw [← meet x hx μ ν hμν.ne, ← meet x' hx' μ' ν' hμν'.ne, hsq]
end Coordinates
private theorem addCircle_intMul_ne_zero {S a : ℝ} {N : ℕ} (ha : a ≠ 0) (hS : S = (N : ℝ) * a)
    (hN : 3 ≤ N) {c : ℤ} (hc0 : 0 < c) (hc3 : c < 3) : (((c : ℝ) * a : ℝ) : AddCircle S) ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff S).1 h
  rw [zsmul_eq_mul, hS, ← mul_assoc] at hm
  have hr : (m : ℝ) * (N : ℝ) = (c : ℝ) := mul_right_cancel₀ ha hm
  have hi : m * (N : ℤ) = c := by exact_mod_cast hr
  rcases le_or_gt m 0 with h1 | h1
  · nlinarith
  · nlinarith
private theorem addCircle_mem_zmultiples_iff {S a : ℝ} {N : ℕ} (ha : a ≠ 0) (hS : S = (N : ℝ) * a)
    (r : ℝ) :
    ((r * a : ℝ) : AddCircle S) ∈ AddSubgroup.zmultiples ((a : ℝ) : AddCircle S) ↔
      ∃ n : ℤ, r = n := by
  constructor
  · intro hmem
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hmem
    have h0 : (((r - k) * a : ℝ) : AddCircle S) = 0 := by
      rw [sub_mul, AddCircle.coe_sub, ← hk, ← AddCircle.coe_zsmul, zsmul_eq_mul, sub_self]
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff S).1 h0
    rw [zsmul_eq_mul, hS, ← mul_assoc] at hm
    have hr : (m : ℝ) * (N : ℝ) = r - k := mul_right_cancel₀ ha hm
    refine ⟨m * N + k, ?_⟩
    push_cast
    linarith
  · rintro ⟨n, rfl⟩
    exact AddSubgroup.mem_zmultiples_iff.2 ⟨n, by rw [← AddCircle.coe_zsmul, zsmul_eq_mul]⟩
theorem elementarySquareStatement_holds : ElementarySquareStatement := by
  rintro L ⟨-, hL⟩ n₀ j k hn hjk
  obtain ⟨e, he⟩ : ∃ e : ℕ, (k : ℤ) - (j : ℤ) = e := ⟨k - j, by omega⟩
  have hdepth : PeriodicLattice.levelDepth k j = (e : ℤ) := he
  rw [hdepth]
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := by omega
    exact_mod_cast this
  have ha : 0 < PeriodicLattice.meshSize L (e : ℤ) := zpow_pos hLpos _
  have hane := ha.ne'
  have hS : PeriodicLattice.torusSide L n₀ =
      ((2 * L ^ (n₀ + e) : ℕ) : ℝ) * PeriodicLattice.meshSize L (e : ℤ) := by
    simp only [PeriodicLattice.torusSide, PeriodicLattice.meshSize]
    push_cast
    rw [pow_add, zpow_neg, zpow_natCast]
    field_simp
  have hN : 3 ≤ 2 * L ^ (n₀ + e) := by
    have : L ≤ L ^ (n₀ + e) := Nat.le_self_pow (by omega) L
    omega
  constructor
  · refine squareFacts_of_coord (fun t : ℝ => (t : AddCircle (PeriodicLattice.torusSide L n₀)))
      (PeriodicLattice.meshSize L (e : ℤ))
      (AddSubgroup.zmultiples
        ((PeriodicLattice.meshSize L (e : ℤ) : ℝ) : AddCircle (PeriodicLattice.torusSide L n₀)))
      (PeriodicLattice.sublattice L n₀ (e : ℤ)) ?_ (by simp)
      (addCircle_mem_zmultiples_iff hane hS) ?_ ?_
    · intro x
      constructor
      · rintro ⟨n, hn⟩ μ
        exact AddSubgroup.mem_zmultiples_iff.2
          ⟨n μ, by rw [hn μ, ← AddCircle.coe_zsmul, zsmul_eq_mul]⟩
      · intro h
        choose n hn using fun μ => AddSubgroup.mem_zmultiples_iff.1 (h μ)
        exact ⟨n, fun μ => by rw [← hn μ, ← AddCircle.coe_zsmul, zsmul_eq_mul]⟩
    · have := addCircle_intMul_ne_zero (c := 1) hane hS hN (by norm_num) (by norm_num)
      simpa using this
    · have := addCircle_intMul_ne_zero (c := 2) hane hS hN (by norm_num) (by norm_num)
      intro h
      apply this
      rw [← AddCircle.coe_add] at h
      rw [← h]
      congr 1
      push_cast
      ring
  · refine squareFacts_of_coord (fun t : ℝ => t) (PeriodicLattice.meshSize L (e : ℤ))
      (AddSubgroup.zmultiples (PeriodicLattice.meshSize L (e : ℤ)))
      (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L (e : ℤ))) ?_ rfl ?_ hane ?_
    · intro x
      constructor
      · rintro ⟨n, hn⟩ μ
        exact AddSubgroup.mem_zmultiples_iff.2 ⟨n μ, by rw [hn μ, zsmul_eq_mul]⟩
      · intro h
        choose n hn using fun μ => AddSubgroup.mem_zmultiples_iff.1 (h μ)
        exact ⟨n, fun μ => by rw [← hn μ, zsmul_eq_mul]⟩
    · intro r
      constructor
      · intro hmem
        obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hmem
        rw [zsmul_eq_mul] at hn
        exact ⟨n, (mul_right_cancel₀ hane hn).symm⟩
      · rintro ⟨n, rfl⟩
        exact AddSubgroup.mem_zmultiples_iff.2 ⟨n, by rw [zsmul_eq_mul]⟩
    · intro h
      have : 0 < PeriodicLattice.meshSize L (e : ℤ) + PeriodicLattice.meshSize L (e : ℤ) := by
        positivity
      exact this.ne' h
end YangMills.Construction.ElementarySquare
end
