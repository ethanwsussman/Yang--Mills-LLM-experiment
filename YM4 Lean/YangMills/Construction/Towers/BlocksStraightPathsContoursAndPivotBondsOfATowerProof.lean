import YangMills.Construction.Lattice.GeometryOfASeparatedSequenceProof
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocksProof
import YangMills.Construction.Towers.AtMostOneStraightPath
import YangMills.Construction.Towers.BlocksOfATowerProof
import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATower
import YangMills.Construction.Towers.ReverseOfAStraightPathOfATowerProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.BlockPathContourPivotProof
theorem two_mul_abs_le_iff {z M : ℤ} : 2 * |z| ≤ M ↔ -M ≤ 2 * z ∧ 2 * z ≤ M := by
  rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
theorem exists_centered_remainder {M : ℤ} (hM : Odd M) (h0 : 0 < M) (N : ℤ) :
    ∃ q, 2 * |N - M * q| ≤ M - 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.exists_two_mul_abs_sub_le <;> assumption
theorem centered_quotient_unique {M N q q' : ℤ} (h0 : 0 < M) (h : 2 * |N - M * q| ≤ M - 1)
    (h' : 2 * |N - M * q'| ≤ M - 1) : q = q' := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.eq_of_two_mul_abs_sub_le <;> assumption
theorem two_mul_abs_quotient_le {P L d A B : ℤ} (hP : 0 < P) (hL : Odd L)
    (hA : 2 * |A| ≤ P * L - 1) (hB : 2 * |B| ≤ P - 1) (e : P * d = A - B) :
    2 * |d| ≤ L - 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.two_mul_abs_digit_le <;> assumption
theorem two_mul_abs_add_mul_le {P L d B : ℤ} (hP : 0 < P) (hd : 2 * |d| ≤ L - 1)
    (hB : 2 * |B| ≤ P - 1) : 2 * |B + P * d| ≤ P * L - 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.two_mul_abs_add_mul_le <;> assumption
def centeredBox (M : ℤ) : Set (Fin 4 → ℤ) := {ν | ∀ μ, 2 * |ν μ| ≤ M - 1}
theorem offsetBox_eq_centeredBox (L n : ℕ) : offsetBox L n = centeredBox ((L : ℤ) ^ n) :=
  Set.ext fun _ => mem_offsetBox_iff
theorem centeredBox_ncard {M : ℤ} (hodd : Odd M) (h0 : 0 < M) :
    (centeredBox M).ncard = M.toNat ^ 4 := by
  obtain ⟨m, hm⟩ := hodd
  have e : centeredBox M =
      ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-m) m : Finset (Fin 4 → ℤ)) :
        Set (Fin 4 → ℤ)) := by
    ext ν
    simp only [centeredBox, Set.mem_ofPred_eq, Finset.mem_coe, Fintype.mem_piFinset,
      Finset.mem_Icc]
    refine forall_congr' fun μ => ?_
    rw [two_mul_abs_le_iff, hm]
    omega
  rw [e, Set.ncard_coe_finset, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : (m + 1 - -m).toNat = M.toNat := by omega
  rw [h1]
theorem offsetBox_ncard {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (n : ℕ) :
    (offsetBox L n).ncard = L ^ (4 * n) := by
  have hodd : Odd ((L : ℤ) ^ n) := Odd.pow (by exact_mod_cast hL.1)
  have h0 : 0 < (L : ℤ) ^ n := pow_pos (by have := hL.2; omega) n
  rw [offsetBox_eq_centeredBox, centeredBox_ncard hodd h0]
  have : ((L : ℤ) ^ n).toNat = L ^ n := by
    have : (L : ℤ) ^ n = ((L ^ n : ℕ) : ℤ) := by push_cast; rfl
    rw [this, Int.toNat_natCast]
  rw [this, ← pow_mul, mul_comm]
theorem add_single_mem_centeredBox {M : ℤ} {ν : Fin 4 → ℤ} (h : ν ∈ centeredBox M) {μ : Fin 4}
    {t : ℤ} (ht : 2 * |ν μ + t| ≤ M - 1) : ν + Pi.single μ t ∈ centeredBox M := by
  intro ρ
  by_cases e : ρ = μ
  · subst e
    simpa using ht
  · simpa [Pi.single_eq_of_ne e] using h ρ
theorem zero_mem_centeredBox {M : ℤ} (h0 : 0 < M) : (0 : Fin 4 → ℤ) ∈ centeredBox M := fun μ => by
  simp only [Pi.zero_apply, abs_zero, mul_zero]
  omega
section Points
variable {P : Type*} [AddCommGroup P]
def gridPoint (e : Fin 4 → P) (y : P) (ν : Fin 4 → ℤ) : P := y + ∑ μ, ν μ • e μ
theorem gridPoint_zero (e : Fin 4 → P) (y : P) : gridPoint e y 0 = y := by
  simp [gridPoint]
theorem gridPoint_add_base (e : Fin 4 → P) (y v : P) (ν : Fin 4 → ℤ) :
    gridPoint e (y + v) ν = gridPoint e y ν + v := by
  unfold gridPoint
  abel
theorem gridPoint_add (e : Fin 4 → P) (y : P) (ν ν' : Fin 4 → ℤ) :
    gridPoint e y (ν + ν') = gridPoint e (gridPoint e y ν) ν' := by
  simp only [gridPoint, Pi.add_apply, add_smul, Finset.sum_add_distrib, add_assoc]
theorem gridPoint_single (e : Fin 4 → P) (y : P) (μ : Fin 4) (t : ℤ) :
    gridPoint e y (Pi.single μ t) = y + t • e μ := by
  unfold gridPoint
  congr 1
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ρ _ h
    simp [Pi.single_eq_of_ne h]
  · simp
theorem gridPoint_add_single (e : Fin 4 → P) (y : P) (ν : Fin 4 → ℤ) (μ : Fin 4) (t : ℤ) :
    gridPoint e y (ν + Pi.single μ t) = gridPoint e y ν + t • e μ := by
  rw [gridPoint_add, gridPoint_single]
theorem gridPoint_base_add_smul (e : Fin 4 → P) (y : P) (ν : Fin 4 → ℤ) (μ : Fin 4) (t : ℤ) :
    gridPoint e (y + t • e μ) ν = gridPoint e y (ν + Pi.single μ t) := by
  rw [gridPoint_add_base, gridPoint_add_single]
theorem image_gridPoint_add_base (e : Fin 4 → P) (y v : P) (A : Set (Fin 4 → ℤ)) :
    gridPoint e (y + v) '' A = (fun p => p + v) '' (gridPoint e y '' A) := by
  rw [image_image]
  exact image_congr fun ν _ => gridPoint_add_base e y v ν
theorem gridPoint_add_mem_image {M : ℤ} (hM : Odd M) (e : Fin 4 → P) (y : P) {ν : Fin 4 → ℤ}
    (hν : ν ∈ centeredBox M) {μ : Fin 4} (h : 2 * ν μ < M - 1) :
    gridPoint e y ν + e μ ∈ gridPoint e y '' centeredBox M := by
  refine ⟨ν + Pi.single μ 1, add_single_mem_centeredBox hν ?_,
    by rw [gridPoint_add_single, one_smul]⟩
  have := hν μ
  obtain ⟨r, rfl⟩ := hM
  rw [two_mul_abs_le_iff] at this ⊢
  omega
theorem gridPoint_add_mem_next {M : ℤ} (e : Fin 4 → P) (y : P) {ν : Fin 4 → ℤ}
    (hν : ν ∈ centeredBox M) {μ : Fin 4} (h : 2 * ν μ = M - 1) :
    gridPoint e y ν + e μ ∈ gridPoint e (y + M • e μ) '' centeredBox M := by
  refine ⟨ν + Pi.single μ (1 - M), add_single_mem_centeredBox hν ?_, ?_⟩
  · have hb := hν μ
    rw [two_mul_abs_le_iff] at hb ⊢
    omega
  · rw [gridPoint_base_add_smul, add_assoc, ← Pi.single_add, gridPoint_add_single]
    simp
theorem gridPoint_add_smul_mem_union {M : ℤ} (e : Fin 4 → P) (y : P) {ν : Fin 4 → ℤ}
    (hν : ν ∈ centeredBox M) (hM : Odd M) {μ : Fin 4} {t : ℤ} (h₀ : 0 ≤ t) (h₁ : t ≤ M) :
    gridPoint e y ν + t • e μ ∈
      gridPoint e y '' centeredBox M ∪ gridPoint e (y + M • e μ) '' centeredBox M := by
  by_cases hin : 2 * |ν μ + t| ≤ M - 1
  · left
    exact ⟨ν + Pi.single μ t, add_single_mem_centeredBox hν hin, by rw [gridPoint_add_single]⟩
  · right
    refine ⟨ν + Pi.single μ (t - M), add_single_mem_centeredBox hν ?_, ?_⟩
    · have hb := hν μ
      obtain ⟨r, rfl⟩ := hM
      rw [two_mul_abs_le_iff] at hb hin ⊢
      omega
    · rw [gridPoint_base_add_smul, add_assoc, ← Pi.single_add, gridPoint_add_single]
      simp
theorem mem_image_centeredBox_mul_iff {M N : ℤ} (hM : Odd M) (h0 : 0 < M) (hN : Odd N)
    (e : Fin 4 → P) (y z : P) : z ∈ gridPoint e y '' centeredBox (M * N) ↔
      ∃ ν₁ ∈ centeredBox N,
        z ∈ gridPoint e (gridPoint (fun μ => M • e μ) y ν₁) '' centeredBox M := by
  have key : ∀ ν₁ ν₂ : Fin 4 → ℤ,
      gridPoint e (gridPoint (fun μ => M • e μ) y ν₁) ν₂ =
        gridPoint e y (ν₂ + fun μ => M * ν₁ μ) := by
    intro ν₁ ν₂
    have h : ∀ μ, (ν₂ μ + M * ν₁ μ) • e μ = ν₂ μ • e μ + ν₁ μ • M • e μ := by
      intro μ
      rw [add_smul, mul_comm, mul_smul]
    simp only [gridPoint, Pi.add_apply]
    rw [Finset.sum_congr rfl fun μ _ => h μ, Finset.sum_add_distrib]
    abel
  constructor
  · rintro ⟨ν, hν, rfl⟩
    choose q hq using fun μ => exists_centered_remainder hM h0 (ν μ)
    refine ⟨q, fun μ => two_mul_abs_quotient_le h0 hN (hν μ) (hq μ) (by ring),
      ν - fun μ => M * q μ, hq, ?_⟩
    rw [key]
    congr 1
    abel
  · rintro ⟨ν₁, h₁, ν₂, h₂, rfl⟩
    refine ⟨ν₂ + fun μ => M * ν₁ μ, fun μ => two_mul_abs_add_mul_le h0 (h₁ μ) (h₂ μ),
      (key ν₁ ν₂).symm⟩
end Points
theorem abs_intCast_mul_lt {N M r : ℤ} {a : ℝ} (ha : 0 < a) (h : 2 * |N| ≤ r * M - 1) :
    |(N : ℝ) * a| < (r : ℝ) / 2 * ((M : ℝ) * a) := by
  have h' : 2 * |(N : ℝ)| ≤ (r : ℝ) * M - 1 := by exact_mod_cast h
  rw [abs_mul, abs_of_pos ha]
  nlinarith
theorem encard_le_four_mul_of_injOn {β P : Type*} {T : Set β} {U : Set P} (hU : U.Finite) {N : ℕ}
    (hN : U.ncard ≤ N) (tail : β → P) (dir : β → Fin 4) (hmaps : ∀ b ∈ T, tail b ∈ U)
    (hinj : InjOn (fun b => (tail b, dir b)) T) : T.encard ≤ ((4 * N : ℕ) : ℕ∞) := by
  have h1 : T.encard ≤ (U ×ˢ (Set.univ : Set (Fin 4))).encard :=
    Set.encard_le_encard_of_injOn (fun b hb => ⟨hmaps b hb, Set.mem_univ _⟩) hinj
  refine h1.trans ?_
  have hfin : (U ×ˢ (Set.univ : Set (Fin 4))).Finite := hU.prod Set.finite_univ
  rw [← hfin.cast_ncard_eq, Set.ncard_prod]
  have : (Set.univ : Set (Fin 4)).ncard = 4 := by simp [Set.ncard_univ]
  rw [this]
  exact_mod_cast (by omega : U.ncard * 4 ≤ 4 * N)
theorem encard_le_eight_of_subset_range {β : Type*} {T : Set β} (G : Fin 4 × Bool → β)
    (h : T ⊆ Set.range G) : T.encard ≤ 8 := by
  refine (Set.encard_le_encard h).trans ?_
  rw [← Set.image_univ]
  refine Set.encard_image_le _ _ |>.trans ?_
  simp [Set.encard_univ]
theorem nodup_and_mem_of_equiv {S : Finset (Fin 4)} (σ : Fin S.card ≃ S) :
    ((List.finRange S.card).map fun i => ((σ i : S) : Fin 4)).Nodup ∧
      ∀ μ, μ ∈ ((List.finRange S.card).map fun i => ((σ i : S) : Fin 4)) ↔ μ ∈ S := by
  refine ⟨List.Nodup.map (fun i i' e => σ.injective (Subtype.ext e)) (List.nodup_finRange _),
    fun μ => ?_⟩
  simp only [List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (σ i).2
  · intro h
    exact ⟨σ.symm ⟨μ, h⟩, by simp⟩
theorem list_map_sum_eq_univ_sum {A : Type*} [AddCommMonoid A] {l : List (Fin 4)} (hl : l.Nodup)
    {ν : Fin 4 → ℤ} (hmem : ∀ μ, μ ∈ l ↔ ν μ ≠ 0) (f : Fin 4 → A)
    (hf : ∀ μ, ν μ = 0 → f μ = 0) : (l.map f).sum = ∑ μ, f μ := by
  rw [← List.sum_toFinset f hl]
  refine Finset.sum_subset (Finset.subset_univ _) fun μ _ h => hf μ ?_
  by_contra h0
  exact h (List.mem_toFinset.2 ((hmem μ).2 h0))
def orderingsOf (S : Finset (Fin 4)) : Set (List (Fin 4)) :=
  {l | ∃ σ : Fin S.card ≃ S, l = (List.finRange S.card).map fun i => ((σ i : S) : Fin 4)}
namespace Periodic
section Walks
variable {L m : ℕ} {d : ℤ}
theorem forwardFlow_eq (x : PeriodicLattice.Site L m d) (μ : Fin 4) (n : ℕ) :
    PeriodicLattice.forwardAxisPath x μ n = (List.range n).map fun i =>
      PeriodicLattice.Bond.forwardFrom (x + i • (PeriodicLattice.unitStep L m d) μ) μ := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [PeriodicLattice.forwardAxisPath, ih, List.range_succ_eq_map, List.map_cons, List.map_map,
      zero_smul, add_zero]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    congr 1
    rw [succ_nsmul]
    abel
theorem backwardFlow_eq (x : PeriodicLattice.Site L m d) (μ : Fin 4) (n : ℕ) :
    PeriodicLattice.backwardAxisPath x μ n = (List.range n).map fun i =>
      PeriodicLattice.Bond.backwardFrom (x - i • (PeriodicLattice.unitStep L m d) μ) μ := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [PeriodicLattice.backwardAxisPath, ih, List.range_succ_eq_map, List.map_cons, List.map_map,
      zero_smul, sub_zero]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    congr 1
    rw [succ_nsmul]
    abel
theorem mem_forwardFlow {x : PeriodicLattice.Site L m d} {μ : Fin 4} {n : ℕ}
    {b : PeriodicLattice.Bond L m d} :
    b ∈ PeriodicLattice.forwardAxisPath x μ n ↔ ∃ i : ℕ, i < n ∧
      b = PeriodicLattice.Bond.forwardFrom (x + i • (PeriodicLattice.unitStep L m d) μ) μ := by apply _root_.YangMills.Construction.SequenceGeometryProof.mem_forwardFlow <;> assumption
theorem length_flowAlong (x : PeriodicLattice.Site L m d) (μ : Fin 4) (t : ℤ) :
    (PeriodicLattice.flowAlong x μ t).length = t.natAbs := by apply _root_.YangMills.Construction.PeriodicLattice.BlockPaths.length_flowAlong <;> assumption
theorem mem_flowAlong {x : PeriodicLattice.Site L m d} {μ : Fin 4} {t : ℤ}
    {b : PeriodicLattice.Bond L m d} (hb : b ∈ PeriodicLattice.flowAlong x μ t) :
    ∃ s s' : ℤ, b.source = x + s • (PeriodicLattice.unitStep L m d) μ ∧
      b.target = x + s' • (PeriodicLattice.unitStep L m d) μ ∧
      b.target - b.source = t.sign • (PeriodicLattice.unitStep L m d) μ ∧ |s| ≤ |t| ∧
      |s'| ≤ |t| := by
  unfold PeriodicLattice.flowAlong at hb
  split_ifs at hb with h
  · obtain ⟨i, hi, rfl⟩ := mem_forwardFlow.1 hb
    have ht : 0 < t := by omega
    refine ⟨i, i + 1, ?_, ?_, ?_, ?_, ?_⟩
    · show x + i • (PeriodicLattice.unitStep L m d) μ = _
      rw [natCast_zsmul]
    · show x + i • (PeriodicLattice.unitStep L m d) μ + (PeriodicLattice.unitStep L m d) μ = _
      rw [add_zsmul, one_zsmul, natCast_zsmul, add_assoc]
    · rw [Int.sign_eq_one_of_pos ht, one_zsmul]
      show x + i • (PeriodicLattice.unitStep L m d) μ + (PeriodicLattice.unitStep L m d) μ -
        (x + i • (PeriodicLattice.unitStep L m d) μ) = _
      abel
    · rw [abs_of_nonneg ht.le, abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_nonneg ht.le, abs_of_nonneg (by omega)]
      omega
  · rw [backwardFlow_eq] at hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    have hi' := List.mem_range.1 hi
    have ht : t < 0 := by omega
    refine ⟨-i, -i - 1, ?_, ?_, ?_, ?_, ?_⟩
    · show x - i • (PeriodicLattice.unitStep L m d) μ = _
      rw [neg_zsmul, natCast_zsmul]
      abel
    · show x - i • (PeriodicLattice.unitStep L m d) μ - (PeriodicLattice.unitStep L m d) μ = _
      rw [sub_zsmul, neg_zsmul, natCast_zsmul, one_zsmul]
      abel
    · rw [Int.sign_eq_neg_one_of_neg ht, neg_zsmul, one_zsmul]
      show x - i • (PeriodicLattice.unitStep L m d) μ - (PeriodicLattice.unitStep L m d) μ -
        (x - i • (PeriodicLattice.unitStep L m d) μ) = _
      abel
    · rw [abs_of_neg ht, abs_neg, abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_neg ht, abs_of_nonpos (by omega)]
      omega
def Joins : PeriodicLattice.Site L m d → PeriodicLattice.Site L m d →
    List (PeriodicLattice.Bond L m d) → Prop
  | x, x', [] => x = x'
  | x, x', b :: Γ => b.source = x ∧ Joins b.target x' Γ
theorem Joins.append {Γ Γ' : List (PeriodicLattice.Bond L m d)} {x y z : PeriodicLattice.Site L m d}
    (h : Joins x y Γ) (h' : Joins y z Γ') : Joins x z (Γ ++ Γ') := by
  induction Γ generalizing x with
  | nil =>
    obtain rfl : x = y := h
    exact h'
  | cons b Γ ih => exact ⟨h.1, ih h.2⟩
theorem Joins.isChain {Γ : List (PeriodicLattice.Bond L m d)} {x y : PeriodicLattice.Site L m d}
    (h : Joins x y Γ) : Γ.IsChain fun b b' => b.target = b'.source := by
  induction Γ generalizing x with
  | nil => exact List.isChain_nil
  | cons b Γ ih =>
    cases Γ with
    | nil => exact List.isChain_singleton _
    | cons b' Γ =>
      exact List.isChain_cons_cons.2 ⟨h.2.1.symm ▸ rfl, ih h.2⟩
theorem joins_forwardFlow (x : PeriodicLattice.Site L m d) (μ : Fin 4) (n : ℕ) :
    Joins x (x + n • (PeriodicLattice.unitStep L m d) μ) (PeriodicLattice.forwardAxisPath x μ n) := by
  induction n generalizing x with
  | zero => simp [PeriodicLattice.forwardAxisPath, Joins]
  | succ n ih =>
    refine ⟨rfl, ?_⟩
    have := ih (x + (PeriodicLattice.unitStep L m d) μ)
    rw [show x + (n + 1) • (PeriodicLattice.unitStep L m d) μ = x + (PeriodicLattice.unitStep L m d) μ +
      n • (PeriodicLattice.unitStep L m d) μ by rw [succ_nsmul]; abel]
    exact this
theorem joins_backwardFlow (x : PeriodicLattice.Site L m d) (μ : Fin 4) (n : ℕ) :
    Joins x (x - n • (PeriodicLattice.unitStep L m d) μ) (PeriodicLattice.backwardAxisPath x μ n) := by
  induction n generalizing x with
  | zero => simp [PeriodicLattice.backwardAxisPath, Joins]
  | succ n ih =>
    refine ⟨rfl, ?_⟩
    have := ih (x - (PeriodicLattice.unitStep L m d) μ)
    rw [show x - (n + 1) • (PeriodicLattice.unitStep L m d) μ = x - (PeriodicLattice.unitStep L m d) μ -
      n • (PeriodicLattice.unitStep L m d) μ by rw [succ_nsmul]; abel]
    exact this
theorem joins_flowAlong (x : PeriodicLattice.Site L m d) (μ : Fin 4) (t : ℤ) :
    Joins x (x + t • (PeriodicLattice.unitStep L m d) μ) (PeriodicLattice.flowAlong x μ t) := by
  unfold PeriodicLattice.flowAlong
  split_ifs with h
  · have := joins_forwardFlow x μ t.toNat
    rwa [← natCast_zsmul, Int.toNat_of_nonneg h] at this
  · have := joins_backwardFlow x μ (-t).toNat
    rw [← natCast_zsmul, Int.toNat_of_nonneg (by omega), neg_zsmul, sub_neg_eq_add] at this
    exact this
theorem joins_stepsThroughAxes (ν : Fin 4 → ℤ) (x : PeriodicLattice.Site L m d) (l : List (Fin 4)) :
    Joins x (x + (l.map fun μ => ν μ • (PeriodicLattice.unitStep L m d) μ).sum)
      (PeriodicLattice.stepsThroughAxes ν x l) := by
  induction l generalizing x with
  | nil => simp [PeriodicLattice.stepsThroughAxes, Joins]
  | cons μ l ih =>
    have := (joins_flowAlong x μ (ν μ)).append (ih (x + ν μ • (PeriodicLattice.unitStep L m d) μ))
    simpa only [PeriodicLattice.stepsThroughAxes, List.map_cons, List.sum_cons, add_assoc] using this
theorem length_stepsThroughAxes (ν : Fin 4 → ℤ) (x : PeriodicLattice.Site L m d) (l : List (Fin 4)) :
    (PeriodicLattice.stepsThroughAxes ν x l).length = (l.map fun μ => (ν μ).natAbs).sum := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    simp only [PeriodicLattice.stepsThroughAxes, List.length_append, length_flowAlong, ih,
      List.map_cons, List.sum_cons]
theorem mem_stepsThroughAxes {ν : Fin 4 → ℤ} {x : PeriodicLattice.Site L m d} {l : List (Fin 4)}
    {b : PeriodicLattice.Bond L m d} (hb : b ∈ PeriodicLattice.stepsThroughAxes ν x l) :
    ∃ μ ∈ l, b.target - b.source = (ν μ).sign • (PeriodicLattice.unitStep L m d) μ ∧ ν μ ≠ 0 := by
  induction l generalizing x with
  | nil => simp [PeriodicLattice.stepsThroughAxes] at hb
  | cons μ l ih =>
    simp only [PeriodicLattice.stepsThroughAxes, List.mem_append] at hb
    rcases hb with hb | hb
    · obtain ⟨s, s', -, -, e, -, -⟩ := mem_flowAlong hb
      refine ⟨μ, List.mem_cons_self, e, ?_⟩
      intro h0
      have := length_flowAlong x μ (ν μ)
      rw [h0] at this hb
      simp only [Int.natAbs_zero, List.length_eq_zero_iff] at this
      rw [this] at hb
      simp at hb
    · obtain ⟨ρ, hρ, e⟩ := ih hb
      exact ⟨ρ, List.mem_cons_of_mem _ hρ, e⟩
theorem filter_length_stepsThroughAxes {ν : Fin 4 → ℤ}
    (hsep : ∀ (ρ σ : Fin 4) (q q' : ℤ), |q| ≤ 1 → |q'| ≤ 1 →
      q • (PeriodicLattice.unitStep L m d) ρ = q' • (PeriodicLattice.unitStep L m d) σ →
      (q = 0 ∧ q' = 0) ∨ (ρ = σ ∧ q = q'))
    (p : PeriodicLattice.Bond L m d → Bool) {μ : Fin 4} (hμ : ν μ ≠ 0)
    (hp : ∀ b, p b = true ↔ b.target - b.source = (ν μ).sign • (PeriodicLattice.unitStep L m d) μ)
    (x : PeriodicLattice.Site L m d) (l : List (Fin 4)) (hl : l.Nodup) :
    ((PeriodicLattice.stepsThroughAxes ν x l).filter p).length =
      if μ ∈ l then (ν μ).natAbs else 0 := by
  have hsign : ∀ t : ℤ, |t.sign| ≤ 1 := fun t => by
    rcases lt_trichotomy t 0 with h | h | h
    · simp [Int.sign_eq_neg_one_of_neg h]
    · simp [h]
    · simp [Int.sign_eq_one_of_pos h]
  have hsign0 : (ν μ).sign ≠ 0 := by
    rcases lt_or_gt_of_ne hμ with h | h
    · rw [Int.sign_eq_neg_one_of_neg h]
      omega
    · rw [Int.sign_eq_one_of_pos h]
      omega
  induction l generalizing x with
  | nil => simp [PeriodicLattice.stepsThroughAxes]
  | cons ρ l ih =>
    rw [List.nodup_cons] at hl
    simp only [PeriodicLattice.stepsThroughAxes, List.filter_append, List.length_append, ih _ hl.2]
    by_cases e : ρ = μ
    · subst e
      have h1 : (PeriodicLattice.flowAlong x ρ (ν ρ)).filter p = PeriodicLattice.flowAlong x ρ (ν ρ) := by
        refine List.filter_eq_self.2 fun b hb => ?_
        obtain ⟨s, s', -, -, e', -, -⟩ := mem_flowAlong hb
        exact (hp b).2 e'
      rw [h1, length_flowAlong, if_neg hl.1, if_pos List.mem_cons_self]
      rfl
    · have h1 : (PeriodicLattice.flowAlong x ρ (ν ρ)).filter p = [] := by
        refine List.filter_eq_nil_iff.2 fun b hb hpb => ?_
        obtain ⟨s, s', -, -, e', -, -⟩ := mem_flowAlong hb
        have := (hp b).1 hpb
        rcases hsep ρ μ _ _ (hsign _) (hsign _) (e'.symm.trans this) with ⟨-, h⟩ | ⟨h, -⟩
        · exact hsign0 h
        · exact e h
      rw [h1]
      simp [List.mem_cons, Ne.symm e]
def translateBond (v : PeriodicLattice.Site L m d) (b : PeriodicLattice.Bond L m d) :
    PeriodicLattice.Bond L m d :=
  ⟨b.source + v, b.target + v, by
    obtain ⟨μ, h⟩ := b.isNeighbour
    exact ⟨μ, by simpa only [add_sub_add_right_eq_sub] using h⟩⟩
theorem translateBond_forwardFrom (v x : PeriodicLattice.Site L m d) (μ : Fin 4) :
    translateBond v (PeriodicLattice.Bond.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (x + v) μ := by
  refine PeriodicLattice.Bond.ext rfl ?_
  show x + (PeriodicLattice.unitStep L m d) μ + v = x + v + (PeriodicLattice.unitStep L m d) μ
  abel
theorem translateBond_backwardFrom (v x : PeriodicLattice.Site L m d) (μ : Fin 4) :
    translateBond v (PeriodicLattice.Bond.backwardFrom x μ) =
      PeriodicLattice.Bond.backwardFrom (x + v) μ := by
  refine PeriodicLattice.Bond.ext rfl ?_
  show x - (PeriodicLattice.unitStep L m d) μ + v = x + v - (PeriodicLattice.unitStep L m d) μ
  abel
theorem map_translateBond_forwardFlow (v x : PeriodicLattice.Site L m d) (μ : Fin 4) (n : ℕ) :
    (PeriodicLattice.forwardAxisPath x μ n).map (translateBond v) =
      PeriodicLattice.forwardAxisPath (x + v) μ n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [PeriodicLattice.forwardAxisPath, List.map_cons, translateBond_forwardFrom, ih]
    rw [add_right_comm]
theorem map_translateBond_backwardFlow (v x : PeriodicLattice.Site L m d) (μ : Fin 4) (n : ℕ) :
    (PeriodicLattice.backwardAxisPath x μ n).map (translateBond v) =
      PeriodicLattice.backwardAxisPath (x + v) μ n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [PeriodicLattice.backwardAxisPath, List.map_cons, translateBond_backwardFrom, ih]
    rw [sub_add_eq_add_sub]
theorem map_translateBond_flowAlong (v x : PeriodicLattice.Site L m d) (μ : Fin 4) (t : ℤ) :
    (PeriodicLattice.flowAlong x μ t).map (translateBond v) = PeriodicLattice.flowAlong (x + v) μ t := by
  unfold PeriodicLattice.flowAlong
  split_ifs
  · exact map_translateBond_forwardFlow v x μ _
  · exact map_translateBond_backwardFlow v x μ _
theorem map_translateBond_stepsThroughAxes (v : PeriodicLattice.Site L m d) (ν : Fin 4 → ℤ)
    (x : PeriodicLattice.Site L m d) (l : List (Fin 4)) :
    (PeriodicLattice.stepsThroughAxes ν x l).map (translateBond v) =
      PeriodicLattice.stepsThroughAxes ν (x + v) l := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    simp only [PeriodicLattice.stepsThroughAxes, List.map_append, map_translateBond_flowAlong, ih]
    rw [add_right_comm]
theorem ends_stepsThroughAxes {ν : Fin 4 → ℤ} {y : PeriodicLattice.Site L m d} (l : List (Fin 4))
    (hl : l.Nodup) (X : Fin 4 → ℤ) (hX : ∀ ρ, |X ρ| ≤ |ν ρ|) (h0 : ∀ ρ ∈ l, X ρ = 0)
    {b : PeriodicLattice.Bond L m d}
    (hb : b ∈ PeriodicLattice.stepsThroughAxes ν (gridPoint (PeriodicLattice.unitStep L m d) y X) l) :
    (∃ N : Fin 4 → ℤ, b.source = gridPoint (PeriodicLattice.unitStep L m d) y N ∧
        ∀ ρ, |N ρ| ≤ |ν ρ|) ∧
      ∃ N : Fin 4 → ℤ, b.target = gridPoint (PeriodicLattice.unitStep L m d) y N ∧
        ∀ ρ, |N ρ| ≤ |ν ρ| := by
  induction l generalizing X with
  | nil => simp [PeriodicLattice.stepsThroughAxes] at hb
  | cons μ l ih =>
    rw [List.nodup_cons] at hl
    have hXμ : X μ = 0 := h0 μ List.mem_cons_self
    have key : ∀ s : ℤ, |s| ≤ |ν μ| → ∀ ρ, |(X + Pi.single μ s : Fin 4 → ℤ) ρ| ≤ |ν ρ| := by
      intro s hs ρ
      by_cases e : ρ = μ
      · subst e
        simpa [hXμ] using hs
      · simpa [Pi.single_eq_of_ne e] using hX ρ
    simp only [PeriodicLattice.stepsThroughAxes, List.mem_append] at hb
    rcases hb with hb | hb
    · obtain ⟨s, s', e₁, e₂, -, h₁, h₂⟩ := mem_flowAlong hb
      refine ⟨⟨X + (Pi.single μ s : Fin 4 → ℤ), ?_, key s h₁⟩,
        ⟨X + (Pi.single μ s' : Fin 4 → ℤ), ?_, key s' h₂⟩⟩
      · rw [e₁, gridPoint_add_single]
      · rw [e₂, gridPoint_add_single]
    · rw [← gridPoint_add_single] at hb
      refine ih hl.2 _ (key _ le_rfl) (fun ρ hρ => ?_) hb
      have hne : ρ ≠ μ := fun e => hl.1 (e ▸ hρ)
      simp [Pi.single_eq_of_ne hne, h0 ρ (List.mem_cons_of_mem _ hρ)]
end Walks
section Points
open PeriodicLattice (FourTorus pointOnAxis levelDepth sublattice)
variable {L m k : ℕ}
theorem zsmul_pointOnAxis (μ : Fin 4) (t : ℤ) (c : ℝ) :
    t • pointOnAxis L m μ c = pointOnAxis L m μ ((t : ℝ) * c) := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.zsmul_pointOnAxis <;> assumption
def axisVectors (L m : ℕ) (a : ℝ) : Fin 4 → FourTorus L m := fun μ => pointOnAxis L m μ a
theorem offsetPoint_eq_gridPoint (a : ℝ) (y : FourTorus L m) (ν : Fin 4 → ℤ) :
    offsetPoint a y ν = gridPoint (axisVectors L m a) y ν := by
  unfold offsetPoint gridPoint
  congr 1
  exact Finset.sum_congr rfl fun μ _ => (zsmul_pointOnAxis μ (ν μ) a).symm
theorem offsetPoint_eq_gridPoint_fun (a : ℝ) (y : FourTorus L m) :
    offsetPoint a y = gridPoint (axisVectors L m a) y := funext (offsetPoint_eq_gridPoint a y)
theorem coe_unitStep {d : ℤ} (μ : Fin 4) :
    ((PeriodicLattice.unitStep L m d μ : PeriodicLattice.Site L m d) : FourTorus L m) =
      axisVectors L m (PeriodicLattice.meshSize L d) μ := rfl
theorem coe_zsmul_unitStep {d : ℤ} (t : ℤ) (μ : Fin 4) :
    ((t • PeriodicLattice.unitStep L m d μ : PeriodicLattice.Site L m d) : FourTorus L m) =
      t • axisVectors L m (PeriodicLattice.meshSize L d) μ := rfl
theorem coe_gridPoint {d : ℤ} (x : PeriodicLattice.Site L m d) (ν : Fin 4 → ℤ) :
    ((gridPoint (PeriodicLattice.unitStep L m d) x ν : PeriodicLattice.Site L m d) : FourTorus L m) =
      gridPoint (axisVectors L m (PeriodicLattice.meshSize L d)) (x : FourTorus L m) ν := by
  unfold gridPoint
  rw [AddSubgroup.coe_add]
  congr 1
theorem coe_toSublattice (hL : 0 < L) {d d' : ℤ} (h : d ≤ d') (y : PeriodicLattice.Site L m d) :
    ((y.toSublattice d' : PeriodicLattice.Site L m d') : FourTorus L m) = y := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
theorem levelDepth_add {n j : ℕ} (hn : n ≤ j) : levelDepth k j + (n : ℤ) = levelDepth k (j - n) := by
  simp only [levelDepth]
  omega
theorem levelDepth_anti {n j : ℕ} (hn : n ≤ j) : levelDepth k j ≤ levelDepth k (j - n) := by
  simp only [levelDepth]
  omega
theorem blockingFactor_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < L := by apply _root_.YangMills.Construction.Tower.AxisPathReversal.blockingFactor_pos <;> assumption
theorem meshAt_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j :=
  zpow_pos (by exact_mod_cast blockingFactor_pos hL) _
theorem meshAt_eq_pow_mul {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j n : ℕ)
    (hn : n ≤ j) : meshAt L k j = (((L : ℤ) ^ n : ℤ) : ℝ) * meshAt L k (j - n) := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.meshAt_eq_pow_mul <;> assumption
theorem odd_blockingFactor_pow {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (n : ℕ) :
    Odd ((L : ℤ) ^ n) := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.odd_pow_factor <;> assumption
theorem blockingFactor_pow_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (n : ℕ) :
    0 < (L : ℤ) ^ n := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.pow_factor_pos <;> assumption
theorem axisVectors_coarse (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j) :
    axisVectors L m (meshAt L k j) =
      fun μ => ((L : ℤ) ^ n) • axisVectors L m (meshAt L k (j - n)) μ := by
  funext μ
  show _ = _ • pointOnAxis L m μ _
  rw [zsmul_pointOnAxis, ← meshAt_eq_pow_mul hL k j n hn]
  rfl
theorem coe_unitStep_level (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j)
    (μ : Fin 4) :
    ((PeriodicLattice.unitStep L m (levelDepth k j) μ : PeriodicLattice.SiteAtLevel L m k j) :
        FourTorus L m) =
      ((L : ℤ) ^ n) • axisVectors L m (meshAt L k (j - n)) μ := by
  rw [coe_unitStep, meshSize_levelDepth, axisVectors_coarse hL hn]
theorem coe_refinedOffsetSite (hL : 0 < L) {d : ℤ} (n : ℕ) (y : PeriodicLattice.Site L m d)
    (p : Fin 4 → ℤ) :
    ((PeriodicLattice.refinedOffsetSite n y p : PeriodicLattice.Site L m (d + (n : ℤ))) :
        FourTorus L m) =
      gridPoint (axisVectors L m (PeriodicLattice.meshSize L (d + (n : ℤ)))) (y : FourTorus L m) p := by
  unfold PeriodicLattice.refinedOffsetSite PeriodicLattice.offsetSite
  have h := coe_gridPoint (y.toSublattice (d + (n : ℤ))) p
  rw [coe_toSublattice hL (by omega) y] at h
  exact h
structure BlockData (L m k n j : ℕ) : Prop where
  eq_image : ∀ y : Vertex L m k j, PeriodicLattice.refinedBlock n y =
    gridPoint (axisVectors L m (meshAt L k (j - n))) (y : FourTorus L m) '' centeredBox ((L : ℤ) ^ n)
  injOn : ∀ y : Vertex L m k j,
    InjOn (gridPoint (axisVectors L m (meshAt L k (j - n))) (y : FourTorus L m))
      (centeredBox ((L : ℤ) ^ n))
  ncard : ∀ y : Vertex L m k j, (PeriodicLattice.refinedBlock n y).ncard = L ^ (4 * n)
  subset_sublattice : ∀ y : Vertex L m k j, PeriodicLattice.refinedBlock n y ⊆
    (sublattice L m (levelDepth k (j - n)) : Set (FourTorus L m))
  existsUnique_mem : ∀ x : Vertex L m k (j - n),
    ∃! y : Vertex L m k j, (x : FourTorus L m) ∈ PeriodicLattice.refinedBlock n y
theorem blockData (h₁ : PeriodicLattice.BlockPartition.Properties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {n j : ℕ} (hn : n ≤ j)
    (hj : j ≤ k) : BlockData L m k n j := by
  have hneg : -(m : ℤ) ≤ levelDepth k j := by
    simp only [levelDepth]
    omega
  obtain ⟨hd, hp, -, -, -⟩ := h₁ L m hL hm (levelDepth k j) n 0 hneg
  have hsp : PeriodicLattice.meshSize L (levelDepth k j + (n : ℤ)) = meshAt L k (j - n) := by
    rw [levelDepth_add hn, meshSize_levelDepth]
  have hf : ∀ y : Vertex L m k j, (fun p => ((PeriodicLattice.refinedOffsetSite n y p :
      PeriodicLattice.Site L m (levelDepth k j + (n : ℤ))) : FourTorus L m)) =
      gridPoint (axisVectors L m (meshAt L k (j - n))) (y : FourTorus L m) := by
    intro y
    funext p
    rw [coe_refinedOffsetSite (blockingFactor_pos hL), hsp]
  obtain ⟨-, -, hdisj, hcover⟩ := hp
  refine ⟨fun y => ?_, fun y => ?_, fun y => (hd y).2.2, fun y x hx => ?_, fun x => ?_⟩
  · have := (hd y).1
    rwa [hf y] at this
  · have := (hd y).2.1
    rwa [hf y] at this
  · have h : x ∈ (sublattice L m (levelDepth k j + (n : ℤ)) : Set (FourTorus L m)) := hx.2
    rwa [levelDepth_add hn] at h
  · have hx : (x : FourTorus L m) ∈ ⋃ y : Vertex L m k j, PeriodicLattice.refinedBlock n y := by
      rw [hcover, levelDepth_add hn]
      exact x.2
    obtain ⟨y, hy⟩ := mem_iUnion.mp hx
    refine ⟨y, hy, fun y' hy' => ?_⟩
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) hy' hy
theorem BlockData.disjoint {n j : ℕ} (C : BlockData L m k n j) {y y' : Vertex L m k j}
    (hne : y ≠ y') :
    Disjoint (PeriodicLattice.refinedBlock n y) (PeriodicLattice.refinedBlock n y') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨y₀, -, hu⟩ := C.existsUnique_mem ⟨x, C.subset_sublattice y hx⟩
  exact hne ((hu y hx).trans (hu y' hx').symm)
theorem BlockData.mem {n j : ℕ} (C : BlockData L m k n j) (y : Vertex L m k j) (ν : Fin 4 → ℤ)
    (hν : ν ∈ centeredBox ((L : ℤ) ^ n)) :
    gridPoint (axisVectors L m (meshAt L k (j - n))) (y : FourTorus L m) ν ∈
      PeriodicLattice.refinedBlock n y := by
  rw [C.eq_image]
  exact ⟨ν, hν, rfl⟩
end Points
section Requirements
open PeriodicLattice (FourTorus pointOnAxis unitBlock refinedBlock contourSet bondCorridor
  crossingPath levelDepth sublattice pivot sitesIn axialPath shiftAcross)
variable {L m k : ℕ}
theorem Joins.isBondPathFromTo {d : ℤ} {Γ : List (PeriodicLattice.Bond L m d)}
    {x x' : PeriodicLattice.Site L m d} (h : Joins x x' Γ) :
    PeriodicLattice.IsBondPathFromTo Γ x x' := by
  refine ⟨h.isChain, ?_, ?_, ?_⟩
  · rintro rfl
    exact h
  · cases Γ with
    | nil => simp
    | cons b Γ =>
      intro b' hb'
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb'
      exact hb' ▸ h.1
  · induction Γ generalizing x with
    | nil => simp
    | cons b Γ ih =>
      cases Γ with
      | nil =>
        intro b' hb'
        simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hb'
        exact hb' ▸ h.2
      | cons b₂ Γ =>
        intro b' hb'
        rw [List.getLast?_cons_cons] at hb'
        exact ih h.2 b' hb'
theorem toNat_natCast_pow (L n : ℕ) : ((L : ℤ) ^ n).toNat = L ^ n := by
  have : (L : ℤ) ^ n = ((L ^ n : ℕ) : ℤ) := by push_cast; rfl
  rw [this, Int.toNat_natCast]
theorem abs_mul_meshAt_lt_half_side (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    {n j : ℕ} (hn : n ≤ j) (hj : j ≤ k) {q : ℤ} (hq : |q| ≤ (L : ℤ) ^ n) :
    ((|q| : ℤ) : ℝ) * meshAt L k (j - n) < PeriodicLattice.torusSide L m / 2 := by
  have h1 : (1 : ℝ) < L := by exact_mod_cast (by have := hL.2; omega : 1 < L)
  have hq' : ((|q| : ℤ) : ℝ) ≤ (((L : ℤ) ^ n : ℤ) : ℝ) := by exact_mod_cast hq
  have h2 : ((|q| : ℤ) : ℝ) * meshAt L k (j - n) ≤ meshAt L k j := by
    rw [meshAt_eq_pow_mul hL k j n hn]
    exact mul_le_mul_of_nonneg_right hq' (meshAt_pos hL k _).le
  have h3 : meshAt L k j ≤ 1 := by
    unfold meshAt
    have := zpow_le_zpow_right₀ h1.le (show (j : ℤ) - (k : ℤ) ≤ 0 by omega)
    simpa using this
  have h4 : (1 : ℝ) < (L : ℝ) ^ m := one_lt_pow₀ h1 hm.ne'
  have h5 : PeriodicLattice.torusSide L m / 2 = (L : ℝ) ^ m := by
    unfold PeriodicLattice.torusSide
    ring
  linarith
theorem unitStep_separation (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℕ} (hi : i ≤ k)
    (ρ σ : Fin 4) (q q' : ℤ) (h : |q| ≤ 1) (h' : |q'| ≤ 1)
    (e : q • PeriodicLattice.unitStep L m (levelDepth k i) ρ =
      q' • PeriodicLattice.unitStep L m (levelDepth k i) σ) :
    (q = 0 ∧ q' = 0) ∨ (ρ = σ ∧ q = q') :=
  ((hE L hL k i hi).1 m hm).1 ρ σ q q'
    (abs_mul_meshAt_lt_half_side hL hm (Nat.zero_le i) hi (by simpa using h))
    (abs_mul_meshAt_lt_half_side hL hm (Nat.zero_le i) hi (by simpa using h')) e
theorem unitStep_ne_zero (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℕ} (hi : i ≤ k) (μ : Fin 4) :
    PeriodicLattice.unitStep L m (levelDepth k i) μ ≠ 0 := by
  intro h
  have := unitStep_separation hE hL hm hi μ μ 1 0 (by simp) (by simp) (by simp [h])
  omega
theorem eq_forwardFrom {d : ℤ} {c : PeriodicLattice.Bond L m d} {μ : Fin 4}
    (hc : c.target - c.source = PeriodicLattice.unitStep L m d μ) :
    c = PeriodicLattice.Bond.forwardFrom c.source μ :=
  PeriodicLattice.Bond.ext rfl (eq_add_of_sub_eq' hc)
theorem coe_target (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j)
    {c : Edge L m k j} {μ : Fin 4}
    (hc : c.target - c.source = PeriodicLattice.unitStep L m (levelDepth k j) μ) :
    (c.target : FourTorus L m) =
      (c.source : FourTorus L m) + ((L : ℤ) ^ n) • axisVectors L m (meshAt L k (j - n)) μ := by
  have h : c.target = c.source + PeriodicLattice.unitStep L m (levelDepth k j) μ :=
    eq_add_of_sub_eq' hc
  rw [h, AddSubgroup.coe_add, coe_unitStep_level hL hn]
theorem coe_shiftAcross_eq (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j)
    (c : Edge L m k j) (x : Vertex L m k (j - n)) :
    ((shiftAcross c x : Vertex L m k (j - n)) : FourTorus L m) =
      (x : FourTorus L m) + ((c.target : FourTorus L m) - (c.source : FourTorus L m)) := by
  unfold shiftAcross
  rw [AddSubgroup.coe_add, coe_toSublattice (blockingFactor_pos hL) (levelDepth_anti hn)]
  rfl
theorem shiftAcross_eq (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j)
    {c : Edge L m k j} {μ : Fin 4}
    (hc : c.target - c.source = PeriodicLattice.unitStep L m (levelDepth k j) μ)
    (x : Vertex L m k (j - n)) :
    shiftAcross c x = x + ((L : ℤ) ^ n) • PeriodicLattice.unitStep L m (levelDepth k (j - n)) μ := by
  apply Subtype.ext
  rw [coe_shiftAcross_eq hL hn, coe_target hL hn hc, AddSubgroup.coe_add, coe_zsmul_unitStep,
    meshSize_levelDepth]
  abel
theorem crossingPath_eq_axialPath (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {n j : ℕ} (hn : n ≤ j)
    (hj : j ≤ k) {c : Edge L m k j} {μ : Fin 4}
    (hc : c.target - c.source = PeriodicLattice.unitStep L m (levelDepth k j) μ)
    (x : Vertex L m k (j - n)) :
    crossingPath c x = PeriodicLattice.flowAlong x μ ((L : ℤ) ^ n) := by
  have e : shiftAcross c x - x =
      ((L : ℤ) ^ n) • PeriodicLattice.unitStep L m (levelDepth k (j - n)) μ := by
    rw [shiftAcross_eq hL hn hc]
    abel
  have hq := abs_mul_meshAt_lt_half_side (k := k) (m := m) hL hm hn hj (q := (L : ℤ) ^ n)
    (by rw [abs_of_pos (blockingFactor_pow_pos hL n)])
  exact (((hE L hL k (j - n) (by omega)).1 m hm).2 x _ μ μ _ _ e hq e hq).2
theorem crossingPath_eq_map (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {n j : ℕ} (hn : n ≤ j)
    (hj : j ≤ k) {c : Edge L m k j} {μ : Fin 4}
    (hc : c.target - c.source = PeriodicLattice.unitStep L m (levelDepth k j) μ)
    (x : Vertex L m k (j - n)) :
    crossingPath c x = (List.range (L ^ n)).map fun i =>
      PeriodicLattice.Bond.forwardFrom
        (x + i • PeriodicLattice.unitStep L m (levelDepth k (j - n)) μ) μ := by
  rw [crossingPath_eq_axialPath hE hL hm hn hj hc]
  unfold PeriodicLattice.flowAlong
  rw [if_pos (blockingFactor_pow_pos hL n).le, forwardFlow_eq, toNat_natCast_pow]
theorem refinedBlocksPartition (h₁ : PeriodicLattice.BlockPartition.Properties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {n j : ℕ} (hn : n ≤ j)
    (hj : j ≤ k) : RefinedBlocksPartition L m k n j := by
  have C := blockData (k := k) h₁ hL hm hn hj
  have hbox := offsetBox_eq_centeredBox L n
  refine ⟨fun y => ?_, fun y => ?_, offsetBox_ncard hL n, C.ncard, C.subset_sublattice,
    C.existsUnique_mem, fun y v => ?_, fun h1 y => ?_, fun h1 y => ?_⟩
  · rw [C.eq_image, offsetPoint_eq_gridPoint_fun, hbox]
  · rw [offsetPoint_eq_gridPoint_fun, hbox]
    exact C.injOn y
  · rw [C.eq_image, C.eq_image, AddSubgroup.coe_add]
    exact image_gridPoint_add_base _ _ _ _
  · have C₁ := blockData (k := k) (m := m) (n := 1) (j := j) h₁ hL hm (by omega) hj
    have C₂ := blockData (k := k) (m := m) (n := n - 1) (j := j - 1) h₁ hL hm (by omega) (by omega)
    have e : j - 1 - (n - 1) = j - n := by omega
    have hax := axisVectors_coarse (k := k) (m := m) hL (n := n - 1) (j := j - 1) (by omega)
    rw [e] at hax
    have hpow : (L : ℤ) ^ n = (L : ℤ) ^ (n - 1) * (L : ℤ) := by
      rw [← pow_succ]
      congr 1
      omega
    have hodd : Odd (L : ℤ) := by exact_mod_cast hL.1
    ext z
    simp only [mem_iUnion, exists_prop]
    rw [C.eq_image, hpow, mem_image_centeredBox_mul_iff (odd_blockingFactor_pow hL _)
      (blockingFactor_pow_pos hL _) hodd, ← hax]
    constructor
    · rintro ⟨ν₁, hν₁, hz⟩
      have hmem : gridPoint (axisVectors L m (meshAt L k (j - 1))) (y : FourTorus L m) ν₁ ∈
          unitBlock y :=
        C₁.mem y ν₁ (by rwa [pow_one])
      refine ⟨⟨_, C₁.subset_sublattice y hmem⟩, hmem, ?_⟩
      rw [C₂.eq_image, e]
      exact hz
    · rintro ⟨x, hx, hz⟩
      have hx' : (x : FourTorus L m) ∈ refinedBlock 1 y := hx
      rw [C₁.eq_image] at hx'
      obtain ⟨ν₁, hν₁, e₁⟩ := hx'
      refine ⟨ν₁, by rwa [pow_one] at hν₁, ?_⟩
      rw [C₂.eq_image, e] at hz
      rw [e₁]
      exact hz
  · have C₂ := blockData (k := k) (m := m) (n := n - 1) (j := j - 1) h₁ hL hm (by omega) (by omega)
    exact fun x _ x' _ hne => C₂.disjoint hne
theorem faceSteps (hE : AxisPathUniqueness.AxisPathsUnique)
    (h₁ : PeriodicLattice.BlockPartition.Properties) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) {n j : ℕ} (hn : n ≤ j) (hj : j ≤ k) : FaceSteps L m k n j := by
  have C := blockData (k := k) h₁ hL hm hn hj
  refine ⟨fun y ν hν μ h => ?_, fun y ν hν μ h => ?_, fun y μ => ?_⟩
  · rw [C.eq_image, offsetPoint_eq_gridPoint]
    rw [offsetBox_eq_centeredBox] at hν
    exact gridPoint_add_mem_image (odd_blockingFactor_pow hL n) _ _ hν h
  · rw [C.eq_image, offsetPoint_eq_gridPoint, AddSubgroup.coe_add, coe_unitStep_level hL hn]
    rw [offsetBox_eq_centeredBox] at hν
    exact gridPoint_add_mem_next _ _ hν h
  · refine C.disjoint fun h => unitStep_ne_zero hE hL hm hj μ ?_
    exact add_eq_left.mp h
theorem add_smul_mem_adjacent_blocks {n j : ℕ} (C : BlockData L m k n j)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : n ≤ j) {c : Edge L m k j} {μ : Fin 4}
    (hc : c.target - c.source = PeriodicLattice.unitStep L m (levelDepth k j) μ)
    {x : Vertex L m k (j - n)} (hx : (x : FourTorus L m) ∈ refinedBlock n c.source) {t : ℤ}
    (h0 : 0 ≤ t) (h1 : t ≤ (L : ℤ) ^ n) :
    ((x + t • PeriodicLattice.unitStep L m (levelDepth k (j - n)) μ : Vertex L m k (j - n)) :
        FourTorus L m) ∈
      refinedBlock n c.source ∪ refinedBlock n c.target := by
  rw [C.eq_image] at hx
  obtain ⟨ν, hν, e⟩ := hx
  rw [AddSubgroup.coe_add, coe_zsmul_unitStep, meshSize_levelDepth, ← e, C.eq_image, C.eq_image,
    coe_target hL hn hc]
  exact gridPoint_add_smul_mem_union _ _ hν (odd_blockingFactor_pow hL n) h0 h1
theorem blockTranslateAlongBond (hE : AxisPathUniqueness.AxisPathsUnique)
    (h₁ : PeriodicLattice.BlockPartition.Properties) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) {n j : ℕ} (hn : n ≤ j) (hj : j ≤ k) : BlockTranslateAlongBond L m k n j := by
  have C := blockData (k := k) h₁ hL hm hn hj
  refine ⟨fun c => ?_, fun c x _ => coe_shiftAcross_eq hL hn c x, fun c μ hc x _ => ⟨?_, ?_⟩,
    fun c μ hc x _ => crossingPath_eq_map hE hL hm hn hj hc x, ?_⟩
  · have h : refinedBlock n c.target = torusTranslation
        ((c.target : FourTorus L m) - (c.source : FourTorus L m)) '' refinedBlock n c.source := by
      rw [C.eq_image, C.eq_image]
      have := image_gridPoint_add_base (axisVectors L m (meshAt L k (j - n)))
        (c.source : FourTorus L m) ((c.target : FourTorus L m) - (c.source : FourTorus L m))
        (centeredBox ((L : ℤ) ^ n))
      rwa [add_sub_cancel] at this
    rw [h]
    exact (add_left_injective _).injOn.bijOn_image
  · rw [shiftAcross_eq hL hn hc]
    abel
  · have h1 : (1 : ℝ) < L := by exact_mod_cast (by have := hL.2; omega : 1 < L)
    have h2 := zpow_lt_zpow_right₀ h1
      (show (n : ℤ) < (m : ℤ) + levelDepth k (j - n) by
        simp only [levelDepth]
        omega)
    rw [abs_of_pos (blockingFactor_pow_pos hL n)]
    simpa using h2
  · rintro c ⟨μ, hc⟩ x hx z hz
    have key : ∀ t : ℤ, 0 ≤ t → t ≤ (L : ℤ) ^ n →
        ((x + t • PeriodicLattice.unitStep L m (levelDepth k (j - n)) μ : Vertex L m k (j - n)) :
            FourTorus L m) ∈
          refinedBlock n c.source ∪ refinedBlock n c.target :=
      fun t h0 h1 => add_smul_mem_adjacent_blocks C hL hn hc hx h0 h1
    rcases hz with rfl | rfl | ⟨b, hb, hz⟩
    · exact Or.inl hx
    · rw [shiftAcross_eq hL hn hc]
      exact key _ (blockingFactor_pow_pos hL n).le le_rfl
    · rw [crossingPath_eq_map hE hL hm hn hj hc] at hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
      have hi' : ((i : ℕ) : ℤ) < (L : ℤ) ^ n := by
        have := List.mem_range.1 hi
        exact_mod_cast this
      rcases hz with rfl | rfl
      · have := key i (by omega) hi'.le
        rwa [natCast_zsmul] at this
      · have := key (i + 1) (by omega) (by omega)
        rw [add_zsmul, one_zsmul, natCast_zsmul, ← add_assoc] at this
        exact this
theorem axialPathMultiplicity (hE : AxisPathUniqueness.AxisPathsUnique)
    (h₁ : PeriodicLattice.BlockPartition.Properties) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) {n j : ℕ} (hn : n ≤ j) (hj : j ≤ k) : AxialPathMultiplicity L m k n j := by
  rintro b' ⟨μ, hb⟩
  have C := blockData (k := k) h₁ hL hm hn hj
  have hb' := eq_forwardFrom hb
  let xs : ℕ → Vertex L m k (j - n) := fun i =>
    b'.source - (i : ℤ) • PeriodicLattice.unitStep L m (levelDepth k (j - n)) μ
  have hex := fun i => (C.existsUnique_mem (xs i)).exists
  choose ys hys using hex
  let F : ℕ → Edge L m k j × Vertex L m k (j - n) := fun i =>
    (PeriodicLattice.Bond.forwardFrom (ys i) μ, xs i)
  have hF : ∀ i, (F i).1.target - (F i).1.source =
      PeriodicLattice.unitStep L m (levelDepth k j) μ := fun i => by
    show ys i + PeriodicLattice.unitStep L m (levelDepth k j) μ - ys i = _
    abel
  have hset : {p : Edge L m k j × Vertex L m k (j - n) | p.1.IsPositivelyOriented ∧
      (p.2 : FourTorus L m) ∈ refinedBlock n p.1.source ∧ b' ∈ crossingPath p.1 p.2} =
      F '' (↑(Finset.range (L ^ n)) : Set ℕ) := by
    ext ⟨c, x⟩
    constructor
    · rintro ⟨⟨ρ, hc⟩, hx, hmem⟩
      simp only at hc hx hmem
      rw [crossingPath_eq_map hE hL hm hn hj hc] at hmem
      obtain ⟨i, hi, e⟩ := List.mem_map.1 hmem
      have e₁ : b'.source = x + i • PeriodicLattice.unitStep L m (levelDepth k (j - n)) ρ :=
        (congrArg PeriodicLattice.Bond.source e).symm
      have e₂ : b'.target = x + i • PeriodicLattice.unitStep L m (levelDepth k (j - n)) ρ +
          PeriodicLattice.unitStep L m (levelDepth k (j - n)) ρ :=
        (congrArg PeriodicLattice.Bond.target e).symm
      have hρ : ρ = μ := by
        have h3 : PeriodicLattice.unitStep L m (levelDepth k (j - n)) ρ =
            PeriodicLattice.unitStep L m (levelDepth k (j - n)) μ := by
          rw [← hb, e₁, e₂]
          abel
        rcases unitStep_separation (k := k) hE hL hm (i := j - n) (by omega) ρ μ 1 1 (by simp)
          (by simp) (by simpa using h3) with ⟨h, -⟩ | ⟨h, -⟩
        · omega
        · exact h
      subst hρ
      have hxi : x = xs i := by
        show x = b'.source - (i : ℤ) • _
        rw [e₁, natCast_zsmul]
        abel
      refine ⟨i, by simpa using List.mem_range.1 hi, ?_⟩
      have hy : c.source = ys i :=
        (C.existsUnique_mem (xs i)).unique (hxi ▸ hx) (hys i)
      refine Prod.ext ?_ hxi.symm
      show PeriodicLattice.Bond.forwardFrom (ys i) ρ = c
      rw [← hy]
      exact (eq_forwardFrom hc).symm
    · rintro ⟨i, hi, e⟩
      have hi' : i < L ^ n := by simpa using hi
      rw [← e]
      refine ⟨⟨μ, hF i⟩, hys i, ?_⟩
      rw [crossingPath_eq_map hE hL hm hn hj (hF i)]
      refine List.mem_map.2 ⟨i, List.mem_range.2 hi', ?_⟩
      rw [hb']
      show PeriodicLattice.Bond.forwardFrom (xs i + i • _) μ = _
      congr 1
      show b'.source - (i : ℤ) • _ + i • _ = _
      rw [natCast_zsmul]
      abel
  have hinj : Set.InjOn F (↑(Finset.range (L ^ n)) : Set ℕ) := by
    intro i hi i' hi' e
    have hi₁ : i < L ^ n := by simpa using hi
    have hi₂ : i' < L ^ n := by simpa using hi'
    have e₂ : xs i = xs i' := congrArg Prod.snd e
    have e₃ : (i : ℤ) • PeriodicLattice.unitStep L m (levelDepth k (j - n)) μ =
        (i' : ℤ) • PeriodicLattice.unitStep L m (levelDepth k (j - n)) μ := sub_right_injective e₂
    have hb₁ : ∀ i : ℕ, i < L ^ n → |(i : ℤ)| ≤ (L : ℤ) ^ n := fun i hi => by
      rw [abs_of_nonneg (by omega)]
      exact_mod_cast hi.le
    rcases ((hE L hL k (j - n) (by omega)).1 m hm).1 μ μ i i'
      (abs_mul_meshAt_lt_half_side hL hm hn hj (hb₁ i hi₁))
      (abs_mul_meshAt_lt_half_side hL hm hn hj (hb₁ i' hi₂)) e₃ with ⟨h, h'⟩ | ⟨-, h⟩ <;> omega
  rw [hset, hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]
theorem adjacentBlocksBounds (h₁ : PeriodicLattice.BlockPartition.Properties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {n j : ℕ} (hn : n ≤ j)
    (hj : j ≤ k) : AdjacentBlocksBounds L m k n j := by
  have C := blockData (k := k) h₁ hL hm hn hj
  have ha := meshAt_pos hL k (j - n)
  have hsp := meshAt_eq_pow_mul hL k j n hn
  have hnear : ∀ (r : ℤ) (N : ℤ), 2 * |N| ≤ r * (L : ℤ) ^ n - 1 →
      |(N : ℝ) * meshAt L k (j - n)| < (r : ℝ) / 2 * meshAt L k j := by
    intro r N h
    rw [hsp]
    exact abs_intCast_mul_lt ha h
  have hin : ∀ (c : Edge L m k j), ∀ x ∈ refinedBlock n c.source, ∃ ν : Fin 4 → ℤ,
      x = offsetPoint (meshAt L k (j - n)) (c.source : FourTorus L m) ν ∧
        ∀ ρ, 2 * |ν ρ| ≤ 1 * (L : ℤ) ^ n - 1 := by
    intro c x hx
    rw [C.eq_image] at hx
    obtain ⟨ν, hν, rfl⟩ := hx
    exact ⟨ν, (offsetPoint_eq_gridPoint _ _ _).symm, fun ρ => by simpa using hν ρ⟩
  have hfin : ∀ y : Vertex L m k j, (refinedBlock n y).Finite := fun y =>
    Set.finite_of_ncard_pos (by rw [C.ncard]; exact pow_pos (blockingFactor_pos hL) _)
  refine ⟨?_, fun c _ x hx => ?_, ?_, fun b => ?_⟩
  · rintro c ⟨μ, hc⟩ x hx
    rcases hx with hx | hx
    · obtain ⟨ν, e, h⟩ := hin c x hx
      refine ⟨ν, e, fun ρ => ?_⟩
      have := hnear 3 (ν ρ) (by have := h ρ; have h0 := blockingFactor_pow_pos hL n; omega)
      simpa using this
    · rw [C.eq_image, coe_target hL hn hc] at hx
      obtain ⟨ν, hν, rfl⟩ := hx
      refine ⟨ν + (Pi.single μ ((L : ℤ) ^ n) : Fin 4 → ℤ), ?_, fun ρ => ?_⟩
      · rw [offsetPoint_eq_gridPoint, gridPoint_base_add_smul]
      · have hb : 2 * |(ν + (Pi.single μ ((L : ℤ) ^ n) : Fin 4 → ℤ)) ρ| ≤
            3 * (L : ℤ) ^ n - 1 := by
          have h0 := blockingFactor_pow_pos hL n
          have h1 := hν ρ
          by_cases e : ρ = μ
          · subst e
            simp only [Pi.add_apply, Pi.single_eq_same]
            rw [two_mul_abs_le_iff] at h1 ⊢
            omega
          · simp only [Pi.add_apply, Pi.single_eq_of_ne e, add_zero]
            omega
        simpa using hnear 3 _ hb
  · obtain ⟨ν, e, h⟩ := hin c x hx
    refine ⟨ν, e, fun ρ => ?_⟩
    simpa using hnear 1 (ν ρ) (h ρ)
  · rintro c -
    classical
    let dir : Edge L m k (j - n) → Fin 4 := fun b =>
      if h : b.IsPositivelyOriented then h.choose else 0
    have hdir : ∀ b : Edge L m k (j - n), b.IsPositivelyOriented →
        b = PeriodicLattice.Bond.forwardFrom b.source (dir b) := by
      intro b hb
      have : dir b = hb.choose := dif_pos hb
      rw [this]
      exact eq_forwardFrom hb.choose_spec
    have hN : (refinedBlock n c.source ∪ refinedBlock n c.target).ncard ≤ 2 * L ^ (4 * n) :=
      (Set.ncard_union_le _ _).trans (by rw [C.ncard, C.ncard]; omega)
    have h := encard_le_four_mul_of_injOn (T := {b : Edge L m k (j - n) | b.IsPositivelyOriented ∧
      (b.source : FourTorus L m) ∈ refinedBlock n c.source ∪ refinedBlock n c.target ∧
      (b.target : FourTorus L m) ∈ refinedBlock n c.source ∪ refinedBlock n c.target})
      ((hfin _).union (hfin _)) hN (fun b => (b.source : FourTorus L m)) dir
      (fun b hb => hb.2.1) (by
        intro b hb b' hb' e
        have e₁ : b.source = b'.source := Subtype.ext (congrArg Prod.fst e)
        have e₂ : dir b = dir b' := congrArg Prod.snd e
        rw [hdir b hb.1, hdir b' hb'.1, e₁, e₂])
    refine h.trans (le_of_eq ?_)
    congr 1
    ring
  · obtain ⟨y, hy, hu⟩ := C.existsUnique_mem b.source
    refine encard_le_eight_of_subset_range (fun p => if p.2 then PeriodicLattice.Bond.forwardFrom y p.1
      else PeriodicLattice.Bond.forwardFrom (y - PeriodicLattice.unitStep L m (levelDepth k j) p.1) p.1) ?_
    rintro c ⟨⟨ρ, hc⟩, ht, -⟩
    have hcf := eq_forwardFrom hc
    rcases ht with ht | ht
    · have h1 : c.source = y := hu _ ht
      refine ⟨(ρ, true), ?_⟩
      simp only [if_true]
      rw [← h1]
      exact hcf.symm
    · have h1 : c.target = y := hu _ ht
      refine ⟨(ρ, false), ?_⟩
      simp only [Bool.false_eq_true, if_false]
      have h2 : y - PeriodicLattice.unitStep L m (levelDepth k j) ρ = c.source := by
        rw [← h1, ← hc]
        abel
      rw [h2]
      exact hcf.symm
theorem isBlockOffset_iff {j : ℕ} {y : Vertex L m k j} {x : Vertex L m k (j - 1)}
    {ν : Fin 4 → ℤ} : PeriodicLattice.IsBlockOffset y x ν ↔
      (x : FourTorus L m) = gridPoint (axisVectors L m (meshAt L k (j - 1))) (y : FourTorus L m) ν ∧
        ν ∈ centeredBox ((L : ℤ) ^ 1) := by
  have hsum : ∑ μ, pointOnAxis L m μ ((ν μ : ℝ) * PeriodicLattice.meshSize L (levelDepth k (j - 1))) =
      ∑ μ, ν μ • axisVectors L m (meshAt L k (j - 1)) μ :=
    Finset.sum_congr rfl fun μ _ => by
      rw [meshSize_levelDepth]
      exact (zsmul_pointOnAxis μ (ν μ) _).symm
  unfold PeriodicLattice.IsBlockOffset
  rw [hsum, sub_eq_iff_eq_add']
  refine and_congr Iff.rfl (forall_congr' fun μ => ?_)
  rw [pow_one]
theorem blockOffset_eq {j : ℕ} (C : BlockData L m k 1 j) {y : Vertex L m k j}
    {x : Vertex L m k (j - 1)} {ν : Fin 4 → ℤ} (hν : ν ∈ centeredBox ((L : ℤ) ^ 1))
    (hx : (x : FourTorus L m) =
      gridPoint (axisVectors L m (meshAt L k (j - 1))) (y : FourTorus L m) ν) :
    PeriodicLattice.blockOffset y x = ν := by
  have hs := Classical.epsilon_spec (p := PeriodicLattice.IsBlockOffset y x)
    ⟨ν, isBlockOffset_iff.2 ⟨hx, hν⟩⟩
  obtain ⟨h1, h2⟩ := isBlockOffset_iff.1 hs
  exact C.injOn y h2 hν (h1.symm.trans hx)
theorem contourSet_eq_image {d d' : ℤ} (y : PeriodicLattice.Site L m d)
    (x : PeriodicLattice.Site L m d') :
    contourSet y x = (fun l => PeriodicLattice.stepsThroughAxes (PeriodicLattice.blockOffset y x)
      (y.toSublattice d') l) '' orderingsOf (PeriodicLattice.offsetAxes y x) := by
  ext Γ
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨_, ⟨σ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
    exact ⟨σ, rfl⟩
theorem stepsThroughAxes_properties (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ k)
    (C : BlockData L m k 1 j) {y : Vertex L m k j} {ν : Fin 4 → ℤ}
    (hν : ν ∈ centeredBox ((L : ℤ) ^ 1)) {x : Vertex L m k (j - 1)}
    (hx : (x : FourTorus L m) =
      gridPoint (axisVectors L m (meshAt L k (j - 1))) (y : FourTorus L m) ν)
    {l : List (Fin 4)} (hl : l.Nodup) (hmem : ∀ μ, μ ∈ l ↔ ν μ ≠ 0) :
    PeriodicLattice.IsBondPathFromTo
        (PeriodicLattice.stepsThroughAxes ν (y.toSublattice (levelDepth k (j - 1))) l)
        (y.toSublattice (levelDepth k (j - 1))) x ∧
      HasStepsOf ν
        (PeriodicLattice.stepsThroughAxes ν (y.toSublattice (levelDepth k (j - 1))) l) ∧
      (PeriodicLattice.stepsThroughAxes ν (y.toSublattice (levelDepth k (j - 1))) l).length =
        ∑ μ, (ν μ).natAbs ∧
      ∑ μ, (ν μ).natAbs ≤ 2 * (L - 1) ∧
      ∀ z : Vertex L m k (j - 1),
        (z = y.toSublattice (levelDepth k (j - 1)) ∨ z = x ∨
            ∃ b ∈ PeriodicLattice.stepsThroughAxes ν (y.toSublattice (levelDepth k (j - 1))) l,
              z = b.source ∨ z = b.target) →
          (z : FourTorus L m) ∈ unitBlock y := by
  have hi : j - 1 ≤ k := by omega
  have h₀ : ((y.toSublattice (levelDepth k (j - 1)) : Vertex L m k (j - 1)) : FourTorus L m) = y :=
    coe_toSublattice (blockingFactor_pos hL) (levelDepth_anti (n := 1) hj1) y
  have hcoe : ∀ N : Fin 4 → ℤ,
      ((gridPoint (PeriodicLattice.unitStep L m (levelDepth k (j - 1)))
          (y.toSublattice (levelDepth k (j - 1))) N : Vertex L m k (j - 1)) : FourTorus L m) =
        gridPoint (axisVectors L m (meshAt L k (j - 1))) (y : FourTorus L m) N := by
    intro N
    rw [coe_gridPoint, h₀, meshSize_levelDepth]
  have hxs : x = gridPoint (PeriodicLattice.unitStep L m (levelDepth k (j - 1)))
      (y.toSublattice (levelDepth k (j - 1))) ν := Subtype.ext (by rw [hcoe, hx])
  have hsum := list_map_sum_eq_univ_sum hl hmem
    (fun μ => ν μ • PeriodicLattice.unitStep L m (levelDepth k (j - 1)) μ) (fun μ h => by simp [h])
  have hruns := joins_stepsThroughAxes ν (y.toSublattice (levelDepth k (j - 1))) l
  rw [hsum] at hruns
  have hlen := length_stepsThroughAxes (d := levelDepth k (j - 1)) (L := L) (m := m) ν
    (y.toSublattice (levelDepth k (j - 1))) l
  rw [list_map_sum_eq_univ_sum hl hmem (fun μ => (ν μ).natAbs) (fun μ h => by simp [h])] at hlen
  have hsepl := unitStep_separation (k := k) hE hL hm hi
  refine ⟨?_, ?_, hlen, ?_, ?_⟩
  · rw [hxs]
    exact hruns.isBondPathFromTo
  · constructor
    · intro μ
      by_cases h0 : ν μ = 0
      · rw [h0]
        simp only [Int.sign_zero, Int.natAbs_zero, List.length_eq_zero_iff]
        refine List.filter_eq_nil_iff.2 fun b hb hp => ?_
        obtain ⟨ρ, -, e, hρ⟩ := mem_stepsThroughAxes hb
        have hp' : IsSignedAxisStep b 0 μ := by
          classical
          exact of_decide_eq_true hp
        have e' : (ν ρ).sign • PeriodicLattice.unitStep L m (levelDepth k (j - 1)) ρ =
            0 • PeriodicLattice.unitStep L m (levelDepth k (j - 1)) μ := e.symm.trans hp'
        have hs : (ν ρ).sign ≠ 0 := by
          rcases lt_or_gt_of_ne hρ with h | h
          · rw [Int.sign_eq_neg_one_of_neg h]
            omega
          · rw [Int.sign_eq_one_of_pos h]
            omega
        have h1 : |(ν ρ).sign| ≤ 1 := by
          rcases lt_or_gt_of_ne hρ with h | h
          · simp [Int.sign_eq_neg_one_of_neg h]
          · simp [Int.sign_eq_one_of_pos h]
        rcases hsepl ρ μ _ 0 h1 (by simp) e' with ⟨h, -⟩ | ⟨-, h⟩
        · exact hs h
        · exact hs h
      · have hf := filter_length_stepsThroughAxes hsepl
          (fun b => @decide (IsSignedAxisStep b (ν μ).sign μ) (Classical.propDecidable _)) h0
          (fun b => @decide_eq_true_iff _ (Classical.propDecidable _))
          (y.toSublattice (levelDepth k (j - 1))) l hl
        rw [if_pos ((hmem μ).2 h0)] at hf
        exact hf
    · intro b hb
      obtain ⟨ρ, -, e, hρ⟩ := mem_stepsThroughAxes hb
      exact ⟨ρ, hρ, e⟩
  · have h : ∀ μ, 2 * (ν μ).natAbs + 1 ≤ L := by
      intro μ
      have h1 := hν μ
      rw [pow_one, Int.abs_eq_natAbs] at h1
      omega
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    rw [Fin.sum_univ_four]
    omega
  · have hN : ∀ N : Fin 4 → ℤ, (∀ ρ, |N ρ| ≤ |ν ρ|) →
        ((gridPoint (PeriodicLattice.unitStep L m (levelDepth k (j - 1)))
            (y.toSublattice (levelDepth k (j - 1))) N : Vertex L m k (j - 1)) : FourTorus L m) ∈
          unitBlock y := by
      intro N h
      rw [hcoe]
      refine C.mem y N fun ρ => ?_
      have h1 := hν ρ
      have h2 := h ρ
      omega
    have hzero : ∀ ρ, |(0 : Fin 4 → ℤ) ρ| ≤ |ν ρ| := fun ρ => by simp
    intro z hz
    rcases hz with rfl | rfl | ⟨b, hb, hz⟩
    · have := hN 0 hzero
      rwa [gridPoint_zero] at this
    · rw [hxs]
      exact hN ν fun ρ => le_rfl
    · rw [show y.toSublattice (levelDepth k (j - 1)) =
        gridPoint (PeriodicLattice.unitStep L m (levelDepth k (j - 1)))
          (y.toSublattice (levelDepth k (j - 1))) 0 from (gridPoint_zero _ _).symm] at hb
      obtain ⟨⟨N₁, e₁, h₁⟩, ⟨N₂, e₂, h₂⟩⟩ :=
        ends_stepsThroughAxes l hl 0 hzero (fun _ _ => rfl) hb
      rcases hz with rfl | rfl
      · rw [e₁]
        exact hN N₁ h₁
      · rw [e₂]
        exact hN N₂ h₂
theorem vertexImage_torusTranslation {i : ℕ} {w : FourTorus L m} {v : Vertex L m k i}
    (hv : (v : FourTorus L m) = w) (x : Vertex L m k i) :
    vertexImage (torusTranslation w) x = x + v := by
  subst hv
  exact Subtype.ext (Classical.epsilon_spec
    (p := fun x' : Vertex L m k i => (x' : FourTorus L m) = torusTranslation (v : FourTorus L m) x)
    ⟨x + v, rfl⟩)
theorem edgeImage_torusTranslation {i : ℕ} {w : FourTorus L m} {v : Vertex L m k i}
    (hv : (v : FourTorus L m) = w) (b : Edge L m k i) :
    edgeImage (torusTranslation w) b = translateBond v b := by
  have h := Classical.epsilon_spec
    (p := fun b' : Edge L m k i => b'.source = vertexImage (torusTranslation w) b.source ∧
      b'.target = vertexImage (torusTranslation w) b.target)
    ⟨translateBond v b, by rw [vertexImage_torusTranslation hv]; rfl,
      by rw [vertexImage_torusTranslation hv]; rfl⟩
  refine PeriodicLattice.Bond.ext ?_ ?_
  · exact h.1.trans (vertexImage_torusTranslation hv _)
  · exact h.2.trans (vertexImage_torusTranslation hv _)
theorem pathImage_torusTranslation {i : ℕ} {w : FourTorus L m} {v : Vertex L m k i}
    (hv : (v : FourTorus L m) = w) (Γ : List (Edge L m k i)) :
    pathImage (k := k) (j := i) (torusTranslation w) Γ = Γ.map (translateBond v) :=
  List.map_congr_left fun b _ => edgeImage_torusTranslation hv b
theorem contourTranslation (hE : AxisPathUniqueness.AxisPathsUnique)
    (h₁ : PeriodicLattice.BlockPartition.Properties) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) {n j : ℕ} (hn : n ≤ j) (hj1 : 1 ≤ j) (hj : j ≤ k) :
    ContourTranslation L m k n j := by
  have C := blockData (k := k) (m := m) (n := 1) (j := j) h₁ hL hm hj1 hj
  have hle : ∀ i ≤ j, levelDepth k j ≤ levelDepth k i := fun i hi => by
    simp only [levelDepth]
    omega
  have hin : ∀ (i : ℕ), i ≤ j → ∀ v : Vertex L m k j,
      ((v.toSublattice (levelDepth k i) : Vertex L m k i) : FourTorus L m) = v :=
    fun i hi v => coe_toSublattice (blockingFactor_pos hL) (hle i hi) v
  refine ⟨fun y ν hν x hx => ?_, fun v a b => ?_, fun v i hi => ⟨?_, ?_, ?_⟩,
    fun v y ν hν x hx => ?_, ?_⟩
  · rw [offsetBox_eq_centeredBox] at hν
    rw [offsetPoint_eq_gridPoint] at hx
    refine ⟨hx ▸ C.mem y ν hν, fun Γ hΓ => ?_⟩
    have hbd := blockOffset_eq C hν hx
    rw [contourSet_eq_image] at hΓ
    obtain ⟨l, ⟨σ, rfl⟩, rfl⟩ := hΓ
    obtain ⟨hnd, hmem⟩ := nodup_and_mem_of_equiv σ
    generalize (List.finRange (PeriodicLattice.offsetAxes y x).card).map
      (fun i => ((σ i : PeriodicLattice.offsetAxes y x) : Fin 4)) = l at hnd hmem ⊢
    have hmem' : ∀ μ, μ ∈ l ↔ ν μ ≠ 0 := fun μ => by
      rw [hmem]
      simp [PeriodicLattice.offsetAxes, hbd]
    simp only [hbd]
    exact stepsThroughAxes_properties hE hL hm hj1 hj C hν hx hnd hmem'
  · show TorusMetric.torusEuclidNorm (a + (v : FourTorus L m) - (b + (v : FourTorus L m))) = _
    rw [add_sub_add_right_eq_sub]
  · ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine add_mem hq ?_
      rw [← hin i hi v]
      exact SetLike.coe_mem _
    · intro hp
      refine ⟨p - (v : FourTorus L m), sub_mem hp ?_, ?_⟩
      · rw [← hin i hi v]
        exact SetLike.coe_mem _
      · show p - (v : FourTorus L m) + (v : FourTorus L m) = p
        abel
  · intro b
    refine ⟨translateBond (v.toSublattice (levelDepth k i)) b, ?_, ?_⟩
    · show ((b.source + v.toSublattice (levelDepth k i) : Vertex L m k i) : FourTorus L m) = _
      rw [AddSubgroup.coe_add, hin i hi v]
      rfl
    · show ((b.target + v.toSublattice (levelDepth k i) : Vertex L m k i) : FourTorus L m) = _
      rw [AddSubgroup.coe_add, hin i hi v]
      rfl
  · intro b'
    refine ⟨translateBond (-v.toSublattice (levelDepth k i)) b', ?_, ?_⟩
    · show _ = ((b'.source + -v.toSublattice (levelDepth k i) : Vertex L m k i) : FourTorus L m) +
        (v : FourTorus L m)
      rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, hin i hi v]
      abel
    · show _ = ((b'.target + -v.toSublattice (levelDepth k i) : Vertex L m k i) : FourTorus L m) +
        (v : FourTorus L m)
      rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, hin i hi v]
      abel
  · rw [offsetBox_eq_centeredBox] at hν
    rw [offsetPoint_eq_gridPoint] at hx
    have hv := hin (j - 1) (by omega) v
    have hbd₁ := blockOffset_eq C hν hx
    have hbd₂ : PeriodicLattice.blockOffset (y + v) (x + v.toSublattice (levelDepth k (j - 1))) = ν :=
      blockOffset_eq C hν (by
        rw [AddSubgroup.coe_add, AddSubgroup.coe_add, hv, hx, gridPoint_add_base])
    have hS : PeriodicLattice.offsetAxes (y + v) (x + v.toSublattice (levelDepth k (j - 1))) =
        PeriodicLattice.offsetAxes y x := by
      unfold PeriodicLattice.offsetAxes
      rw [hbd₁, hbd₂]
    rw [contourSet_eq_image, contourSet_eq_image, hS, hbd₁, hbd₂, image_image]
    refine image_congr fun l _ => ?_
    rw [pathImage_torusTranslation hv, map_translateBond_stepsThroughAxes]
    congr 1
    apply Subtype.ext
    rw [AddSubgroup.coe_add, hv,
      coe_toSublattice (blockingFactor_pos hL) (by simp only [levelDepth]; omega) y,
      coe_toSublattice (blockingFactor_pos hL) (by simp only [levelDepth]; omega) (y + v),
      AddSubgroup.coe_add]
  · rintro v c ⟨μ, hc⟩ z -
    have hv := hin (j - n) (by omega) v
    rw [pathImage_torusTranslation hv, crossingPath_eq_axialPath hE hL hm hn hj hc,
      map_translateBond_flowAlong]
    have e : (shiftAcross c z + v.toSublattice (levelDepth k (j - n))) -
        (z + v.toSublattice (levelDepth k (j - n))) =
        ((L : ℤ) ^ n) • PeriodicLattice.unitStep L m (levelDepth k (j - n)) μ := by
      rw [shiftAcross_eq hL hn hc]
      abel
    have hq := abs_mul_meshAt_lt_half_side (k := k) (m := m) hL hm hn hj (q := (L : ℤ) ^ n)
      (by rw [abs_of_pos (blockingFactor_pow_pos hL n)])
    exact (((hE L hL k (j - n) (by omega)).1 m hm).2 _ _ μ μ _ _ e hq e hq).2.symm
theorem pivotOnAxialPath (hE : AxisPathUniqueness.AxisPathsUnique)
    (h₁ : PeriodicLattice.BlockPartition.Properties) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ k) : PivotOnAxialPath L m k j := by
  have C := blockData (k := k) (m := m) (n := 1) (j := j) h₁ hL hm hj1 hj
  obtain ⟨h, hLh⟩ := hL.1
  have hpath : ∀ (c : Edge L m k j) (μ : Fin 4),
      c.target - c.source = PeriodicLattice.unitStep L m (levelDepth k j) μ →
      axialPath (c.source.toSublattice (levelDepth k (j - 1)))
          (c.target.toSublattice (levelDepth k (j - 1))) =
        (List.range L).map fun i => PeriodicLattice.Bond.forwardFrom
          (c.source.toSublattice (levelDepth k (j - 1)) +
            i • PeriodicLattice.unitStep L m (levelDepth k (j - 1)) μ) μ := by
    intro c μ hc
    have e : shiftAcross c (c.source.toSublattice (levelDepth k (j - 1))) =
        c.target.toSublattice (levelDepth k (j - 1)) := by
      apply Subtype.ext
      rw [coe_shiftAcross_eq hL hj1,
        coe_toSublattice (blockingFactor_pos hL) (levelDepth_anti (n := 1) hj1),
        coe_toSublattice (blockingFactor_pos hL) (levelDepth_anti (n := 1) hj1)]
      abel
    have := crossingPath_eq_map (n := 1) hE hL hm hj1 hj hc
      (c.source.toSublattice (levelDepth k (j - 1)))
    rw [pow_one] at this
    rw [← e]
    exact this
  have hiff : ∀ (c : Edge L m k j) (μ : Fin 4),
      c.target - c.source = PeriodicLattice.unitStep L m (levelDepth k j) μ →
      ∀ b : Edge L m k (j - 1), PeriodicLattice.IsPivot c b ↔
        b = PeriodicLattice.Bond.forwardFrom (c.source.toSublattice (levelDepth k (j - 1)) +
          h • PeriodicLattice.unitStep L m (levelDepth k (j - 1)) μ) μ := by
    intro c μ hc b
    have hne : c.source ≠ c.target := by
      intro e
      apply unitStep_ne_zero hE hL hm hj μ
      rw [← hc, e, sub_self]
    have hdis := C.disjoint hne
    have hLZ : (L : ℤ) = 2 * (h : ℤ) + 1 := by exact_mod_cast hLh
    have hbox : ∀ t : ℤ, 2 * |t| ≤ (L : ℤ) - 1 →
        (Pi.single μ t : Fin 4 → ℤ) ∈ centeredBox ((L : ℤ) ^ 1) := by
      intro t ht
      have := add_single_mem_centeredBox
        (zero_mem_centeredBox (M := (L : ℤ) ^ 1) (by rw [pow_one]; omega)) (μ := μ)
        (t := t) (by simpa using ht)
      simpa using this
    have hz : ∀ t : ℤ, ((c.source.toSublattice (levelDepth k (j - 1)) +
        t • PeriodicLattice.unitStep L m (levelDepth k (j - 1)) μ : Vertex L m k (j - 1)) :
          FourTorus L m) =
        gridPoint (axisVectors L m (meshAt L k (j - 1))) (c.source : FourTorus L m)
          (Pi.single μ t) := by
      intro t
      rw [gridPoint_single, AddSubgroup.coe_add, coe_zsmul_unitStep, meshSize_levelDepth,
        coe_toSublattice (blockingFactor_pos hL) (levelDepth_anti (n := 1) hj1)]
    have hz₂ : ∀ t : ℤ, ((c.source.toSublattice (levelDepth k (j - 1)) +
        t • PeriodicLattice.unitStep L m (levelDepth k (j - 1)) μ : Vertex L m k (j - 1)) :
          FourTorus L m) =
        gridPoint (axisVectors L m (meshAt L k (j - 1))) (c.target : FourTorus L m)
          (Pi.single μ (t - L)) := by
      intro t
      have e : (Pi.single μ t : Fin 4 → ℤ) =
          (Pi.single μ (t - L) : Fin 4 → ℤ) + (Pi.single μ (L : ℤ) : Fin 4 → ℤ) := by
        rw [← Pi.single_add]
        simp
      rw [hz, coe_target hL hj1 hc, pow_one, gridPoint_base_add_smul, e]
    have hin₁ : ∀ t : ℤ, 2 * |t| ≤ (L : ℤ) - 1 →
        ((c.source.toSublattice (levelDepth k (j - 1)) +
          t • PeriodicLattice.unitStep L m (levelDepth k (j - 1)) μ : Vertex L m k (j - 1)) :
            FourTorus L m) ∈ unitBlock c.source := fun t ht => by
      rw [hz]
      exact C.mem _ _ (hbox t ht)
    have hin₂ : ∀ t : ℤ, 2 * |t - L| ≤ (L : ℤ) - 1 →
        ((c.source.toSublattice (levelDepth k (j - 1)) +
          t • PeriodicLattice.unitStep L m (levelDepth k (j - 1)) μ : Vertex L m k (j - 1)) :
            FourTorus L m) ∈ unitBlock c.target := fun t ht => by
      rw [hz₂]
      exact C.mem _ _ (hbox _ ht)
    constructor
    · rintro ⟨⟨h₂, h₃⟩, hb⟩
      rw [hpath c μ hc] at hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
      have hi' := List.mem_range.1 hi
      have hbi : ((i : ℕ) : ℤ) ≤ h := by
        by_contra hlt
        have h4 := hin₂ i (by rw [two_mul_abs_le_iff]; omega)
        rw [natCast_zsmul] at h4
        exact Set.disjoint_left.mp hdis h₂ h4
      have hbi' : (h : ℤ) ≤ i := by
        by_contra hlt
        have h4 := hin₁ (i + 1) (by rw [two_mul_abs_le_iff]; omega)
        rw [add_zsmul, one_zsmul, natCast_zsmul, ← add_assoc] at h4
        exact Set.disjoint_left.mp hdis h4 h₃
      have hih : i = h := by omega
      rw [hih]
    · rintro rfl
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have h4 := hin₁ h (by rw [two_mul_abs_le_iff]; omega)
        rwa [natCast_zsmul] at h4
      · have h4 := hin₂ (h + 1) (by rw [two_mul_abs_le_iff]; omega)
        rwa [add_zsmul, one_zsmul, natCast_zsmul, ← add_assoc] at h4
      · rw [hpath c μ hc]
        exact List.mem_map.2 ⟨h, List.mem_range.2 (by omega), rfl⟩
  refine ⟨fun c μ hc => ?_, fun c μ hc => ?_, fun c μ hc b hb => ?_, fun c μ hc b hb => ?_⟩
  · rw [hpath c μ hc]
    simp
  · exact ⟨_, (hiff c μ hc _).2 rfl, fun b hb => (hiff c μ hc b).1 hb⟩
  · rw [(hiff c μ hc b).1 hb]
    show ((c.source.toSublattice (levelDepth k (j - 1)) +
      h • PeriodicLattice.unitStep L m (levelDepth k (j - 1)) μ : Vertex L m k (j - 1)) :
        FourTorus L m) = _
    rw [AddSubgroup.coe_add, coe_toSublattice (blockingFactor_pos hL) (levelDepth_anti (n := 1) hj1),
      ← natCast_zsmul, coe_zsmul_unitStep, meshSize_levelDepth]
    congr 1
    show ((h : ℤ)) • pointOnAxis L m μ _ = _
    rw [zsmul_pointOnAxis]
    congr 1
    rw [hLh]
    push_cast
    ring
  · have hs := Classical.epsilon_spec
      (p := PeriodicLattice.IsPivot (j' := levelDepth k (j - 1)) c) ⟨b, hb⟩
    exact ((hiff c μ hc b).1 hb).trans ((hiff c μ hc _).1 hs).symm
theorem atFiniteSide (hE : AxisPathUniqueness.AxisPathsUnique)
    (h₁ : PeriodicLattice.BlockPartition.Properties) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) {n j : ℕ} (hn : n ≤ j) (hj : j ≤ k) :
    RefinedBlocksPartition L m k n j ∧ FaceSteps L m k n j ∧
      BlockTranslateAlongBond L m k n j ∧ AxialPathMultiplicity L m k n j ∧
      AdjacentBlocksBounds L m k n j ∧
      (1 ≤ j → ContourTranslation L m k n j ∧ PivotOnAxialPath L m k j) :=
  ⟨refinedBlocksPartition h₁ hL hm hn hj, faceSteps hE h₁ hL hm hn hj,
    blockTranslateAlongBond hE h₁ hL hm hn hj, axialPathMultiplicity hE h₁ hL hm hn hj,
    adjacentBlocksBounds h₁ hL hm hn hj,
    fun hj1 => ⟨contourTranslation hE h₁ hL hm hn hj1 hj, pivotOnAxialPath hE h₁ hL hm hj1 hj⟩⟩
end Requirements
end Periodic
end YangMills.Construction.Tower.BlockPathContourPivotProof
namespace YangMills.Construction.Tower.FullSpace.CubesAndPaths
open YangMills.Construction.Tower.BlockPathContourPivotProof
section Walks
variable {a : ℝ}
theorem forwardSteps_eq (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ) :
    FullSpace.forwardSteps x μ n = (List.range n).map fun i =>
      InfiniteLattice.Link.forwardFrom (x + i • (InfiniteLattice.axisStep a) μ) μ := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [FullSpace.forwardSteps, ih, List.range_succ_eq_map, List.map_cons, List.map_map,
      zero_smul, add_zero]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    congr 1
    rw [succ_nsmul]
    abel
theorem backwardSteps_eq (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ) :
    FullSpace.backwardSteps x μ n = (List.range n).map fun i =>
      FullSpace.backwardLink (x - i • (InfiniteLattice.axisStep a) μ) μ := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [FullSpace.backwardSteps, ih, List.range_succ_eq_map, List.map_cons, List.map_map,
      zero_smul, sub_zero]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    congr 1
    rw [succ_nsmul]
    abel
theorem mem_forwardSteps {x : InfiniteLattice.LatticePoint a} {μ : Fin 4} {n : ℕ}
    {b : InfiniteLattice.Link a} :
    b ∈ FullSpace.forwardSteps x μ n ↔ ∃ i : ℕ, i < n ∧
      b = InfiniteLattice.Link.forwardFrom (x + i • (InfiniteLattice.axisStep a) μ) μ := by
  rw [forwardSteps_eq]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
theorem length_signedSteps (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (t : ℤ) :
    (FullSpace.signedSteps x μ t).length = t.natAbs := by
  unfold FullSpace.signedSteps
  split_ifs with h
  · rw [forwardSteps_eq]
    simp only [List.length_map, List.length_range]
    omega
  · rw [backwardSteps_eq]
    simp only [List.length_map, List.length_range]
    omega
theorem mem_signedSteps {x : InfiniteLattice.LatticePoint a} {μ : Fin 4} {t : ℤ}
    {b : InfiniteLattice.Link a} (hb : b ∈ FullSpace.signedSteps x μ t) :
    ∃ s s' : ℤ, b.initial = x + s • (InfiniteLattice.axisStep a) μ ∧
      b.terminal = x + s' • (InfiniteLattice.axisStep a) μ ∧
      b.terminal - b.initial = t.sign • (InfiniteLattice.axisStep a) μ ∧ |s| ≤ |t| ∧
      |s'| ≤ |t| := by
  unfold FullSpace.signedSteps at hb
  split_ifs at hb with h
  · obtain ⟨i, hi, rfl⟩ := mem_forwardSteps.1 hb
    have ht : 0 < t := by omega
    refine ⟨i, i + 1, ?_, ?_, ?_, ?_, ?_⟩
    · show x + i • (InfiniteLattice.axisStep a) μ = _
      rw [natCast_zsmul]
    · show x + i • (InfiniteLattice.axisStep a) μ + (InfiniteLattice.axisStep a) μ = _
      rw [add_zsmul, one_zsmul, natCast_zsmul, add_assoc]
    · rw [Int.sign_eq_one_of_pos ht, one_zsmul]
      show x + i • (InfiniteLattice.axisStep a) μ + (InfiniteLattice.axisStep a) μ -
        (x + i • (InfiniteLattice.axisStep a) μ) = _
      abel
    · rw [abs_of_nonneg ht.le, abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_nonneg ht.le, abs_of_nonneg (by omega)]
      omega
  · rw [backwardSteps_eq] at hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    have hi' := List.mem_range.1 hi
    have ht : t < 0 := by omega
    refine ⟨-i, -i - 1, ?_, ?_, ?_, ?_, ?_⟩
    · show x - i • (InfiniteLattice.axisStep a) μ = _
      rw [neg_zsmul, natCast_zsmul]
      abel
    · show x - i • (InfiniteLattice.axisStep a) μ - (InfiniteLattice.axisStep a) μ = _
      rw [sub_zsmul, neg_zsmul, natCast_zsmul, one_zsmul]
      abel
    · rw [Int.sign_eq_neg_one_of_neg ht, neg_zsmul, one_zsmul]
      show x - i • (InfiniteLattice.axisStep a) μ - (InfiniteLattice.axisStep a) μ -
        (x - i • (InfiniteLattice.axisStep a) μ) = _
      abel
    · rw [abs_of_neg ht, abs_neg, abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_neg ht, abs_of_nonpos (by omega)]
      omega
def Joins : InfiniteLattice.LatticePoint a → InfiniteLattice.LatticePoint a →
    List (InfiniteLattice.Link a) → Prop
  | x, x', [] => x = x'
  | x, x', b :: Γ => b.initial = x ∧ Joins b.terminal x' Γ
theorem Joins.append {Γ Γ' : List (InfiniteLattice.Link a)} {x y z : InfiniteLattice.LatticePoint a}
    (h : Joins x y Γ) (h' : Joins y z Γ') : Joins x z (Γ ++ Γ') := by
  induction Γ generalizing x with
  | nil =>
    obtain rfl : x = y := h
    exact h'
  | cons b Γ ih => exact ⟨h.1, ih h.2⟩
theorem Joins.isChain {Γ : List (InfiniteLattice.Link a)} {x y : InfiniteLattice.LatticePoint a}
    (h : Joins x y Γ) : Γ.IsChain fun b b' => b.terminal = b'.initial := by
  induction Γ generalizing x with
  | nil => exact List.isChain_nil
  | cons b Γ ih =>
    cases Γ with
    | nil => exact List.isChain_singleton _
    | cons b' Γ =>
      exact List.isChain_cons_cons.2 ⟨h.2.1.symm ▸ rfl, ih h.2⟩
theorem joins_forwardSteps (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ) :
    Joins x (x + n • (InfiniteLattice.axisStep a) μ) (FullSpace.forwardSteps x μ n) := by
  induction n generalizing x with
  | zero => simp [FullSpace.forwardSteps, Joins]
  | succ n ih =>
    refine ⟨rfl, ?_⟩
    have := ih (x + (InfiniteLattice.axisStep a) μ)
    rw [show x + (n + 1) • (InfiniteLattice.axisStep a) μ = x + (InfiniteLattice.axisStep a) μ +
      n • (InfiniteLattice.axisStep a) μ by rw [succ_nsmul]; abel]
    exact this
theorem joins_backwardSteps (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ) :
    Joins x (x - n • (InfiniteLattice.axisStep a) μ) (FullSpace.backwardSteps x μ n) := by
  induction n generalizing x with
  | zero => simp [FullSpace.backwardSteps, Joins]
  | succ n ih =>
    refine ⟨rfl, ?_⟩
    have := ih (x - (InfiniteLattice.axisStep a) μ)
    rw [show x - (n + 1) • (InfiniteLattice.axisStep a) μ = x - (InfiniteLattice.axisStep a) μ -
      n • (InfiniteLattice.axisStep a) μ by rw [succ_nsmul]; abel]
    exact this
theorem joins_signedSteps (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (t : ℤ) :
    Joins x (x + t • (InfiniteLattice.axisStep a) μ) (FullSpace.signedSteps x μ t) := by
  unfold FullSpace.signedSteps
  split_ifs with h
  · have := joins_forwardSteps x μ t.toNat
    rwa [← natCast_zsmul, Int.toNat_of_nonneg h] at this
  · have := joins_backwardSteps x μ (-t).toNat
    rw [← natCast_zsmul, Int.toNat_of_nonneg (by omega), neg_zsmul, sub_neg_eq_add] at this
    exact this
theorem joins_stepsInOrder (ν : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint a) (l : List (Fin 4)) :
    Joins x (x + (l.map fun μ => ν μ • (InfiniteLattice.axisStep a) μ).sum)
      (FullSpace.stepsInOrder ν x l) := by
  induction l generalizing x with
  | nil => simp [FullSpace.stepsInOrder, Joins]
  | cons μ l ih =>
    have := (joins_signedSteps x μ (ν μ)).append (ih (x + ν μ • (InfiniteLattice.axisStep a) μ))
    simpa only [FullSpace.stepsInOrder, List.map_cons, List.sum_cons, add_assoc] using this
theorem length_stepsInOrder (ν : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint a) (l : List (Fin 4)) :
    (FullSpace.stepsInOrder ν x l).length = (l.map fun μ => (ν μ).natAbs).sum := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    simp only [FullSpace.stepsInOrder, List.length_append, length_signedSteps, ih, List.map_cons,
      List.sum_cons]
theorem mem_stepsInOrder {ν : Fin 4 → ℤ} {x : InfiniteLattice.LatticePoint a} {l : List (Fin 4)}
    {b : InfiniteLattice.Link a} (hb : b ∈ FullSpace.stepsInOrder ν x l) :
    ∃ μ ∈ l, b.terminal - b.initial = (ν μ).sign • (InfiniteLattice.axisStep a) μ ∧ ν μ ≠ 0 := by
  induction l generalizing x with
  | nil => simp [FullSpace.stepsInOrder] at hb
  | cons μ l ih =>
    simp only [FullSpace.stepsInOrder, List.mem_append] at hb
    rcases hb with hb | hb
    · obtain ⟨s, s', -, -, e, -, -⟩ := mem_signedSteps hb
      refine ⟨μ, List.mem_cons_self, e, ?_⟩
      intro h0
      have := length_signedSteps x μ (ν μ)
      rw [h0] at this hb
      simp only [Int.natAbs_zero, List.length_eq_zero_iff] at this
      rw [this] at hb
      simp at hb
    · obtain ⟨ρ, hρ, e⟩ := ih hb
      exact ⟨ρ, List.mem_cons_of_mem _ hρ, e⟩
theorem filter_length_stepsInOrder {ν : Fin 4 → ℤ}
    (hsep : ∀ (ρ σ : Fin 4) (q q' : ℤ), |q| ≤ 1 → |q'| ≤ 1 →
      q • (InfiniteLattice.axisStep a) ρ = q' • (InfiniteLattice.axisStep a) σ →
      (q = 0 ∧ q' = 0) ∨ (ρ = σ ∧ q = q'))
    (p : InfiniteLattice.Link a → Bool) {μ : Fin 4} (hμ : ν μ ≠ 0)
    (hp : ∀ b, p b = true ↔ b.terminal - b.initial = (ν μ).sign • (InfiniteLattice.axisStep a) μ)
    (x : InfiniteLattice.LatticePoint a) (l : List (Fin 4)) (hl : l.Nodup) :
    ((FullSpace.stepsInOrder ν x l).filter p).length = if μ ∈ l then (ν μ).natAbs else 0 := by
  have hsign : ∀ t : ℤ, |t.sign| ≤ 1 := fun t => by
    rcases lt_trichotomy t 0 with h | h | h
    · simp [Int.sign_eq_neg_one_of_neg h]
    · simp [h]
    · simp [Int.sign_eq_one_of_pos h]
  have hsign0 : (ν μ).sign ≠ 0 := by
    rcases lt_or_gt_of_ne hμ with h | h
    · rw [Int.sign_eq_neg_one_of_neg h]
      omega
    · rw [Int.sign_eq_one_of_pos h]
      omega
  induction l generalizing x with
  | nil => simp [FullSpace.stepsInOrder]
  | cons ρ l ih =>
    rw [List.nodup_cons] at hl
    simp only [FullSpace.stepsInOrder, List.filter_append, List.length_append, ih _ hl.2]
    by_cases e : ρ = μ
    · subst e
      have h1 : (FullSpace.signedSteps x ρ (ν ρ)).filter p = FullSpace.signedSteps x ρ (ν ρ) := by
        refine List.filter_eq_self.2 fun b hb => ?_
        obtain ⟨s, s', -, -, e', -, -⟩ := mem_signedSteps hb
        exact (hp b).2 e'
      rw [h1, length_signedSteps, if_neg hl.1, if_pos List.mem_cons_self]
      rfl
    · have h1 : (FullSpace.signedSteps x ρ (ν ρ)).filter p = [] := by
        refine List.filter_eq_nil_iff.2 fun b hb hpb => ?_
        obtain ⟨s, s', -, -, e', -, -⟩ := mem_signedSteps hb
        have := (hp b).1 hpb
        rcases hsep ρ μ _ _ (hsign _) (hsign _) (e'.symm.trans this) with ⟨-, h⟩ | ⟨h, -⟩
        · exact hsign0 h
        · exact e h
      rw [h1]
      simp [List.mem_cons, Ne.symm e]
def translateLink (v : InfiniteLattice.LatticePoint a) (b : InfiniteLattice.Link a) :
    InfiniteLattice.Link a :=
  ⟨b.initial + v, b.terminal + v, by
    obtain ⟨μ, h⟩ := b.isAdjacent
    exact ⟨μ, by simpa only [add_sub_add_right_eq_sub] using h⟩⟩
theorem translateLink_forwardFrom (v x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    translateLink v (InfiniteLattice.Link.forwardFrom x μ) =
      InfiniteLattice.Link.forwardFrom (x + v) μ := by
  refine InfiniteLattice.Link.ext rfl ?_
  show x + (InfiniteLattice.axisStep a) μ + v = x + v + (InfiniteLattice.axisStep a) μ
  abel
theorem translateLink_backwardLink (v x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    translateLink v (FullSpace.backwardLink x μ) = FullSpace.backwardLink (x + v) μ := by
  refine InfiniteLattice.Link.ext rfl ?_
  show x - (InfiniteLattice.axisStep a) μ + v = x + v - (InfiniteLattice.axisStep a) μ
  abel
theorem map_translateLink_forwardSteps (v x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ) :
    (FullSpace.forwardSteps x μ n).map (translateLink v) = FullSpace.forwardSteps (x + v) μ n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [FullSpace.forwardSteps, List.map_cons, translateLink_forwardFrom, ih]
    rw [add_right_comm]
theorem map_translateLink_backwardSteps (v x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (n : ℕ) :
    (FullSpace.backwardSteps x μ n).map (translateLink v) = FullSpace.backwardSteps (x + v) μ n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [FullSpace.backwardSteps, List.map_cons, translateLink_backwardLink, ih]
    rw [sub_add_eq_add_sub]
theorem map_translateLink_signedSteps (v x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (t : ℤ) :
    (FullSpace.signedSteps x μ t).map (translateLink v) = FullSpace.signedSteps (x + v) μ t := by
  unfold FullSpace.signedSteps
  split_ifs
  · exact map_translateLink_forwardSteps v x μ _
  · exact map_translateLink_backwardSteps v x μ _
theorem map_translateLink_stepsInOrder (v : InfiniteLattice.LatticePoint a) (ν : Fin 4 → ℤ)
    (x : InfiniteLattice.LatticePoint a) (l : List (Fin 4)) :
    (FullSpace.stepsInOrder ν x l).map (translateLink v) = FullSpace.stepsInOrder ν (x + v) l := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    simp only [FullSpace.stepsInOrder, List.map_append, map_translateLink_signedSteps, ih]
    rw [add_right_comm]
theorem ends_stepsInOrder {ν : Fin 4 → ℤ} {y : InfiniteLattice.LatticePoint a} (l : List (Fin 4))
    (hl : l.Nodup) (X : Fin 4 → ℤ) (hX : ∀ ρ, |X ρ| ≤ |ν ρ|) (h0 : ∀ ρ ∈ l, X ρ = 0)
    {b : InfiniteLattice.Link a}
    (hb : b ∈ FullSpace.stepsInOrder ν (gridPoint (InfiniteLattice.axisStep a) y X) l) :
    (∃ N : Fin 4 → ℤ, b.initial = gridPoint (InfiniteLattice.axisStep a) y N ∧
        ∀ ρ, |N ρ| ≤ |ν ρ|) ∧
      ∃ N : Fin 4 → ℤ, b.terminal = gridPoint (InfiniteLattice.axisStep a) y N ∧
        ∀ ρ, |N ρ| ≤ |ν ρ| := by
  induction l generalizing X with
  | nil => simp [FullSpace.stepsInOrder] at hb
  | cons μ l ih =>
    rw [List.nodup_cons] at hl
    have hXμ : X μ = 0 := h0 μ List.mem_cons_self
    have key : ∀ s : ℤ, |s| ≤ |ν μ| → ∀ ρ, |(X + Pi.single μ s : Fin 4 → ℤ) ρ| ≤ |ν ρ| := by
      intro s hs ρ
      by_cases e : ρ = μ
      · subst e
        simpa [hXμ] using hs
      · simpa [Pi.single_eq_of_ne e] using hX ρ
    simp only [FullSpace.stepsInOrder, List.mem_append] at hb
    rcases hb with hb | hb
    · obtain ⟨s, s', e₁, e₂, -, h₁, h₂⟩ := mem_signedSteps hb
      refine ⟨⟨X + (Pi.single μ s : Fin 4 → ℤ), ?_, key s h₁⟩,
        ⟨X + (Pi.single μ s' : Fin 4 → ℤ), ?_, key s' h₂⟩⟩
      · rw [e₁, gridPoint_add_single]
      · rw [e₂, gridPoint_add_single]
    · rw [← gridPoint_add_single] at hb
      refine ih hl.2 _ (key _ le_rfl) (fun ρ hρ => ?_) hb
      have hne : ρ ≠ μ := fun e => hl.1 (e ▸ hρ)
      simp [Pi.single_eq_of_ne hne, h0 ρ (List.mem_cons_of_mem _ hρ)]
end Walks
section Points
open InfiniteLattice (AmbientSpace)
variable {L k : ℕ}
theorem zsmul_piSingle (μ : Fin 4) (t : ℤ) (c : ℝ) :
    t • (Pi.single μ c : AmbientSpace) = Pi.single μ ((t : ℝ) * c) := by
  funext ρ
  by_cases h : ρ = μ
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]
def axisVectors (a : ℝ) : Fin 4 → AmbientSpace := fun μ => Pi.single μ a
theorem offsetPoint_eq_gridPoint (a : ℝ) (y : AmbientSpace) (ν : Fin 4 → ℤ) :
    offsetPoint a y ν = gridPoint (axisVectors a) y ν := by
  unfold offsetPoint gridPoint
  congr 1
  exact Finset.sum_congr rfl fun μ _ => (zsmul_piSingle μ (ν μ) a).symm
theorem offsetPoint_eq_gridPoint_fun (a : ℝ) (y : AmbientSpace) :
    offsetPoint a y = gridPoint (axisVectors a) y := funext (offsetPoint_eq_gridPoint a y)
theorem gridPoint_apply (a : ℝ) (y : AmbientSpace) (ν : Fin 4 → ℤ) (ρ : Fin 4) :
    gridPoint (axisVectors a) y ν ρ = y ρ + (ν ρ : ℝ) * a := by
  rw [← offsetPoint_eq_gridPoint]
  simp [offsetPoint, Finset.sum_apply, Pi.single_apply]
theorem coe_axisStep {a : ℝ} (μ : Fin 4) :
    ((InfiniteLattice.axisStep a μ : InfiniteLattice.LatticePoint a) : AmbientSpace) =
      axisVectors a μ := rfl
theorem coe_zsmul_axisStep {a : ℝ} (t : ℤ) (μ : Fin 4) :
    ((t • InfiniteLattice.axisStep a μ : InfiniteLattice.LatticePoint a) : AmbientSpace) =
      t • axisVectors a μ := rfl
theorem coe_gridPoint {a : ℝ} (x : InfiniteLattice.LatticePoint a) (ν : Fin 4 → ℤ) :
    ((gridPoint (InfiniteLattice.axisStep a) x ν : InfiniteLattice.LatticePoint a) : AmbientSpace) =
      gridPoint (axisVectors a) (x : AmbientSpace) ν := by
  unfold gridPoint
  rw [AddSubgroup.coe_add]
  congr 1
theorem blockingFactor_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < L := by apply _root_.YangMills.Construction.Tower.AxisPathReversal.blockingFactor_pos <;> assumption
theorem meshAt_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem meshAt_eq_pow_mul_of_pos {L : ℕ} (hL : 0 < L) (k j n : ℕ) (hn : n ≤ j) :
    meshAt L k j = (((L : ℤ) ^ n : ℤ) : ℝ) * meshAt L k (j - n) := by
  have h : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold meshAt
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ h]
  congr 1
  omega
theorem meshAt_eq_pow_mul {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j n : ℕ)
    (hn : n ≤ j) : meshAt L k j = (((L : ℤ) ^ n : ℤ) : ℝ) * meshAt L k (j - n) := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.meshAt_eq_pow_mul <;> assumption
theorem odd_blockingFactor_pow {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (n : ℕ) :
    Odd ((L : ℤ) ^ n) := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.odd_pow_factor <;> assumption
theorem blockingFactor_pow_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (n : ℕ) :
    0 < (L : ℤ) ^ n := by apply _root_.YangMills.Construction.Tower.FullSpace.CubeCorridorProof.pow_factor_pos <;> assumption
theorem axisVectors_coarse (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j) :
    axisVectors (meshAt L k j) = fun μ => ((L : ℤ) ^ n) • axisVectors (meshAt L k (j - n)) μ := by
  funext μ
  show _ = _ • (Pi.single μ _ : AmbientSpace)
  rw [zsmul_piSingle, ← meshAt_eq_pow_mul hL k j n hn]
  rfl
theorem coe_axisStep_level (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j)
    (μ : Fin 4) :
    ((InfiniteLattice.axisStep (meshAt L k j) μ : Vertex L k j) : AmbientSpace) =
      ((L : ℤ) ^ n) • axisVectors (meshAt L k (j - n)) μ := by
  rw [coe_axisStep, axisVectors_coarse hL hn]
theorem coe_mem_latticeSubgroup {L : ℕ} (hL : 0 < L) {n j : ℕ} (hn : n ≤ j) (y : Vertex L k j) :
    (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (meshAt L k (j - n)) := by
  obtain ⟨q, hq⟩ := y.2
  refine ⟨fun μ => (L : ℤ) ^ n * q μ, fun μ => ?_⟩
  rw [hq μ, meshAt_eq_pow_mul_of_pos hL k j n hn]
  push_cast
  ring
theorem sub_sub_sub_self {n j : ℕ} (hn : n ≤ j) : j - (j - (j - n)) = j - n := by omega
theorem coe_toFiner (hL : 0 < L) {i j : ℕ} (h : j - (j - i) = i) (y : Vertex L k j) :
    ((toFiner (meshAt L k i) y : Vertex L k i) : AmbientSpace) = y := by
  have hm : (y : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (meshAt L k i) := by
    have := coe_mem_latticeSubgroup hL (Nat.sub_le j i) y
    rwa [h] at this
  exact Classical.epsilon_spec
    (p := fun x : InfiniteLattice.LatticePoint (meshAt L k i) => (x : AmbientSpace) = y)
    ⟨⟨y, hm⟩, rfl⟩
structure CubeData (L k n j : ℕ) : Prop where
  eq_image : ∀ y : Vertex L k j, cubeOfOrder L (meshAt L k (j - n)) n y =
    gridPoint (axisVectors (meshAt L k (j - n))) (y : AmbientSpace) '' centeredBox ((L : ℤ) ^ n)
  injOn : ∀ y : Vertex L k j,
    InjOn (gridPoint (axisVectors (meshAt L k (j - n))) (y : AmbientSpace))
      (centeredBox ((L : ℤ) ^ n))
  ncard : ∀ y : Vertex L k j,
    (cubeOfOrder L (meshAt L k (j - n)) n y).ncard = L ^ (4 * n)
  subset_sublattice : ∀ y : Vertex L k j, cubeOfOrder L (meshAt L k (j - n)) n y ⊆
    (InfiniteLattice.latticeSubgroup (meshAt L k (j - n)) : Set AmbientSpace)
  existsUnique_mem : ∀ x : Vertex L k (j - n),
    ∃! y : Vertex L k j, (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n y
theorem cubeData (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j)
    (_hj : j ≤ k) : CubeData L k n j := by
  have ha := meshAt_pos hL k (j - n)
  have h0 := blockingFactor_pow_pos hL n
  have hsp := meshAt_eq_pow_mul hL k j n hn
  have hbe : ∀ y : Vertex L k j, cubeOfOrder L (meshAt L k (j - n)) n y =
      gridPoint (axisVectors (meshAt L k (j - n))) (y : AmbientSpace) '' centeredBox ((L : ℤ) ^ n) := by
    intro y
    ext x
    constructor
    · rintro ⟨ν, hν, rfl⟩
      exact ⟨ν, hν, (offsetPoint_eq_gridPoint _ _ _).symm⟩
    · rintro ⟨ν, hν, rfl⟩
      exact ⟨ν, hν, offsetPoint_eq_gridPoint _ _ _ |>.symm⟩
  have hinj : ∀ y : Vertex L k j,
      InjOn (gridPoint (axisVectors (meshAt L k (j - n))) (y : AmbientSpace))
        (centeredBox ((L : ℤ) ^ n)) := by
    intro y ν _ ν' _ e
    funext ρ
    have h := congrFun e ρ
    rw [gridPoint_apply, gridPoint_apply] at h
    exact_mod_cast mul_right_cancel₀ ha.ne' (add_left_cancel h)
  refine ⟨hbe, hinj, fun y => ?_, fun y x hx => ?_, fun x => ?_⟩
  · rw [hbe, (hinj y).ncard_image, ← offsetBox_eq_centeredBox, offsetBox_ncard hL]
  · rw [hbe] at hx
    obtain ⟨ν, -, rfl⟩ := hx
    obtain ⟨q, hq⟩ := coe_mem_latticeSubgroup (blockingFactor_pos hL) hn y
    refine ⟨q + ν, fun μ => ?_⟩
    rw [gridPoint_apply, hq μ]
    simp only [Pi.add_apply]
    push_cast
    ring
  · obtain ⟨N, hN⟩ := x.2
    choose q hq using fun μ => exists_centered_remainder (odd_blockingFactor_pow hL n) h0 (N μ)
    have hmem : ∀ (y : Vertex L k j) (Y : Fin 4 → ℤ),
        (∀ μ, (y : AmbientSpace) μ = (Y μ : ℝ) * meshAt L k j) →
        ((x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n y ↔
          ∀ μ, 2 * |N μ - (L : ℤ) ^ n * Y μ| ≤ (L : ℤ) ^ n - 1) := by
      intro y Y hY
      have hdiff : ∀ ν : Fin 4 → ℤ,
          (x : AmbientSpace) = gridPoint (axisVectors (meshAt L k (j - n))) y ν ↔
            ∀ μ, ν μ = N μ - (L : ℤ) ^ n * Y μ := by
        intro ν
        constructor
        · intro e μ
          have h := congrFun e μ
          rw [gridPoint_apply, hN μ, hY μ, hsp] at h
          have h' : ((N μ : ℝ)) = (((L : ℤ) ^ n * Y μ + ν μ : ℤ) : ℝ) := by
            apply mul_right_cancel₀ ha.ne'
            rw [h]
            push_cast
            ring
          have h'' : N μ = (L : ℤ) ^ n * Y μ + ν μ := by exact_mod_cast h'
          omega
        · intro e
          funext μ
          rw [gridPoint_apply, hN μ, hY μ, hsp, e μ]
          push_cast
          ring
      rw [hbe]
      constructor
      · rintro ⟨ν, hν, e⟩ μ
        rw [← (hdiff ν).1 e.symm μ]
        exact hν μ
      · intro h
        exact ⟨fun μ => N μ - (L : ℤ) ^ n * Y μ, h, ((hdiff _).2 fun μ => rfl).symm⟩
    let y₀ : Vertex L k j := ⟨fun μ => (q μ : ℝ) * meshAt L k j, q, fun μ => rfl⟩
    refine ⟨y₀, (hmem y₀ q fun μ => rfl).2 hq, fun y hy => ?_⟩
    obtain ⟨Y, hY⟩ := y.2
    have h1 := (hmem y Y hY).1 hy
    have : Y = q := funext fun μ => centered_quotient_unique h0 (h1 μ) (hq μ)
    apply Subtype.ext
    funext μ
    rw [hY μ, this]
theorem CubeData.disjoint {n j : ℕ} (C : CubeData L k n j) {y y' : Vertex L k j} (hne : y ≠ y') :
    Disjoint (cubeOfOrder L (meshAt L k (j - n)) n y) (cubeOfOrder L (meshAt L k (j - n)) n y') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨y₀, -, hu⟩ := C.existsUnique_mem ⟨x, C.subset_sublattice y hx⟩
  exact hne ((hu y hx).trans (hu y' hx').symm)
theorem CubeData.mem {n j : ℕ} (C : CubeData L k n j) (y : Vertex L k j) (ν : Fin 4 → ℤ)
    (hν : ν ∈ centeredBox ((L : ℤ) ^ n)) :
    gridPoint (axisVectors (meshAt L k (j - n))) (y : AmbientSpace) ν ∈
      cubeOfOrder L (meshAt L k (j - n)) n y := by
  rw [C.eq_image]
  exact ⟨ν, hν, rfl⟩
end Points
section Requirements
open InfiniteLattice (AmbientSpace)
variable {L k : ℕ}
theorem Joins.isLinkPath_and_linksJoin {a : ℝ} {Γ : List (InfiniteLattice.Link a)}
    {x x' : InfiniteLattice.LatticePoint a} (h : Joins x x' Γ) :
    IsLinkPath Γ ∧ LinksJoin (x : AmbientSpace) (x' : AmbientSpace) Γ := by
  refine ⟨h.isChain, ?_⟩
  induction Γ generalizing x with
  | nil => exact congrArg _ h
  | cons b Γ ih => exact ⟨congrArg _ h.1, ih h.2⟩
theorem toNat_natCast_pow (L n : ℕ) : ((L : ℤ) ^ n).toNat = L ^ n := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.toNat_natCast_pow <;> assumption
theorem axisStep_separation (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i ≤ k) (ρ σ : Fin 4) (q q' : ℤ)
    (_h : |q| ≤ 1) (_h' : |q'| ≤ 1)
    (e : q • InfiniteLattice.axisStep (meshAt L k i) ρ =
      q' • InfiniteLattice.axisStep (meshAt L k i) σ) :
    (q = 0 ∧ q' = 0) ∨ (ρ = σ ∧ q = q') :=
  (hE L hL k i hi).2.1 ρ σ q q' e
theorem axisStep_ne_zero (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i ≤ k) (μ : Fin 4) :
    InfiniteLattice.axisStep (meshAt L k i) μ ≠ 0 := by
  intro h
  have := axisStep_separation hE hL hi μ μ 1 0 (by simp) (by simp) (by simp [h])
  omega
theorem eq_forwardFrom {a : ℝ} {c : InfiniteLattice.Link a} {μ : Fin 4}
    (hc : c.terminal - c.initial = InfiniteLattice.axisStep a μ) :
    c = InfiniteLattice.Link.forwardFrom c.initial μ :=
  InfiniteLattice.Link.ext rfl (eq_add_of_sub_eq' hc)
theorem coe_terminal (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j)
    {c : Edge L k j} {μ : Fin 4}
    (hc : c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ) :
    (c.terminal : AmbientSpace) =
      (c.initial : AmbientSpace) + ((L : ℤ) ^ n) • axisVectors (meshAt L k (j - n)) μ := by
  have h : c.terminal = c.initial + InfiniteLattice.axisStep (meshAt L k j) μ :=
    eq_add_of_sub_eq' hc
  rw [h, AddSubgroup.coe_add, coe_axisStep_level hL hn]
theorem coe_shifted_eq (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j)
    (c : Edge L k j) (x : Vertex L k (j - n)) :
    ((shifted c x : Vertex L k (j - n)) : AmbientSpace) =
      (x : AmbientSpace) + ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)) := by
  unfold shifted
  rw [AddSubgroup.coe_add, coe_toFiner (blockingFactor_pos hL) (sub_sub_sub_self hn)]
  rfl
theorem shifted_eq (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j)
    {c : Edge L k j} {μ : Fin 4}
    (hc : c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ)
    (x : Vertex L k (j - n)) :
    shifted c x = x + ((L : ℤ) ^ n) • InfiniteLattice.axisStep (meshAt L k (j - n)) μ := by
  apply Subtype.ext
  rw [coe_shifted_eq hL hn, coe_terminal hL hn hc, AddSubgroup.coe_add, coe_zsmul_axisStep]
  abel
theorem crossingPath_eq_signedSteps (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j) (hj : j ≤ k)
    {c : Edge L k j} {μ : Fin 4}
    (hc : c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ)
    (x : Vertex L k (j - n)) :
    crossingPath c x = signedSteps x μ ((L : ℤ) ^ n) := by
  have e : shifted c x - x = ((L : ℤ) ^ n) • InfiniteLattice.axisStep (meshAt L k (j - n)) μ := by
    rw [shifted_eq hL hn hc]
    abel
  exact ((hE L hL k (j - n) (by omega)).2.2 x _ μ μ _ _ e e).2
theorem crossingPath_eq_map (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j) (hj : j ≤ k)
    {c : Edge L k j} {μ : Fin 4}
    (hc : c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ)
    (x : Vertex L k (j - n)) :
    crossingPath c x = (List.range (L ^ n)).map fun i =>
      InfiniteLattice.Link.forwardFrom (x + i • InfiniteLattice.axisStep (meshAt L k (j - n)) μ) μ := by
  rw [crossingPath_eq_signedSteps hE hL hn hj hc]
  unfold signedSteps
  rw [if_pos (blockingFactor_pow_pos hL n).le, forwardSteps_eq, toNat_natCast_pow]
theorem refinedCubesPartition (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ}
    (hn : n ≤ j) (hj : j ≤ k) : RefinedCubesPartition L k n j := by
  have C := cubeData (k := k) hL hn hj
  have hbox := offsetBox_eq_centeredBox L n
  refine ⟨fun y => ?_, fun y => ?_, offsetBox_ncard hL n, C.ncard, C.subset_sublattice,
    C.existsUnique_mem, fun y v => ?_, fun h1 y => ?_, fun h1 y => ?_⟩
  · rw [C.eq_image, offsetPoint_eq_gridPoint_fun, hbox]
  · rw [offsetPoint_eq_gridPoint_fun, hbox]
    exact C.injOn y
  · rw [C.eq_image, C.eq_image, AddSubgroup.coe_add]
    exact image_gridPoint_add_base _ _ _ _
  · have C₁ := cubeData (k := k) (n := 1) (j := j) hL (by omega) hj
    have C₂ := cubeData (k := k) (n := n - 1) (j := j - 1) hL (by omega) (by omega)
    have e : j - 1 - (n - 1) = j - n := by omega
    have hax := axisVectors_coarse (k := k) hL (n := n - 1) (j := j - 1) (by omega)
    rw [e] at hax
    have hpow : (L : ℤ) ^ n = (L : ℤ) ^ (n - 1) * (L : ℤ) := by
      rw [← pow_succ]
      congr 1
      omega
    have hodd : Odd (L : ℤ) := by exact_mod_cast hL.1
    ext z
    simp only [mem_iUnion, exists_prop]
    rw [C.eq_image, hpow, mem_image_centeredBox_mul_iff (odd_blockingFactor_pow hL _)
      (blockingFactor_pow_pos hL _) hodd, ← hax]
    constructor
    · rintro ⟨ν₁, hν₁, hz⟩
      have hmem : gridPoint (axisVectors (meshAt L k (j - 1))) (y : AmbientSpace) ν₁ ∈
          cube L (meshAt L k (j - 1)) y :=
        C₁.mem y ν₁ (by rwa [pow_one])
      refine ⟨⟨_, C₁.subset_sublattice y hmem⟩, hmem, ?_⟩
      have hb₂ := C₂.eq_image ⟨_, C₁.subset_sublattice y hmem⟩
      rw [e] at hb₂
      rw [hb₂]
      exact hz
    · rintro ⟨x, hx, hz⟩
      have hx' : (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - 1)) 1 y := hx
      rw [C₁.eq_image] at hx'
      obtain ⟨ν₁, hν₁, e₁⟩ := hx'
      refine ⟨ν₁, by rwa [pow_one] at hν₁, ?_⟩
      have hb₂ := C₂.eq_image x
      rw [e] at hb₂
      rw [hb₂] at hz
      rw [e₁]
      exact hz
  · have C₂ := cubeData (k := k) (n := n - 1) (j := j - 1) hL (by omega) (by omega)
    have e : j - 1 - (n - 1) = j - n := by omega
    intro x _ x' _ hne
    have := C₂.disjoint hne
    rwa [e] at this
theorem faceSteps (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j) (hj : j ≤ k) :
    FaceSteps L k n j := by
  have C := cubeData (k := k) hL hn hj
  refine ⟨fun y ν hν μ h => ?_, fun y ν hν μ h => ?_, fun y μ => ?_⟩
  · rw [C.eq_image, offsetPoint_eq_gridPoint]
    rw [offsetBox_eq_centeredBox] at hν
    exact gridPoint_add_mem_image (odd_blockingFactor_pow hL n) _ _ hν h
  · rw [C.eq_image, offsetPoint_eq_gridPoint, AddSubgroup.coe_add, coe_axisStep_level hL hn]
    rw [offsetBox_eq_centeredBox] at hν
    exact gridPoint_add_mem_next _ _ hν h
  · refine C.disjoint fun h => axisStep_ne_zero hE hL hj μ ?_
    exact add_eq_left.mp h
theorem add_smul_mem_adjacent_cubes {n j : ℕ} (C : CubeData L k n j)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : n ≤ j) {c : Edge L k j} {μ : Fin 4}
    (hc : c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ)
    {x : Vertex L k (j - n)} (hx : (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial)
    {t : ℤ} (h0 : 0 ≤ t) (h1 : t ≤ (L : ℤ) ^ n) :
    ((x + t • InfiniteLattice.axisStep (meshAt L k (j - n)) μ : Vertex L k (j - n)) : AmbientSpace) ∈
      cubeOfOrder L (meshAt L k (j - n)) n c.initial ∪
        cubeOfOrder L (meshAt L k (j - n)) n c.terminal := by
  rw [C.eq_image] at hx
  obtain ⟨ν, hν, e⟩ := hx
  rw [AddSubgroup.coe_add, coe_zsmul_axisStep, ← e, C.eq_image, C.eq_image, coe_terminal hL hn hc]
  exact gridPoint_add_smul_mem_union _ _ hν (odd_blockingFactor_pow hL n) h0 h1
theorem cubeTranslateAlongLink (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j) (hj : j ≤ k) :
    CubeTranslateAlongLink L k n j := by
  have C := cubeData (k := k) hL hn hj
  refine ⟨fun c => ?_, fun c x _ => coe_shifted_eq hL hn c x, fun c μ hc x _ => ?_,
    fun c μ hc x _ => crossingPath_eq_map hE hL hn hj hc x, ?_⟩
  · have h : cubeOfOrder L (meshAt L k (j - n)) n c.terminal = spaceTranslation
        ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)) ''
          cubeOfOrder L (meshAt L k (j - n)) n c.initial := by
      rw [C.eq_image, C.eq_image]
      have := image_gridPoint_add_base (axisVectors (meshAt L k (j - n))) (c.initial : AmbientSpace)
        ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)) (centeredBox ((L : ℤ) ^ n))
      rwa [add_sub_cancel] at this
    rw [h]
    exact (add_left_injective _).injOn.bijOn_image
  · show shifted c x - x = _
    rw [shifted_eq hL hn hc]
    abel
  · rintro c ⟨μ, hc⟩ x hx z hz
    have key : ∀ t : ℤ, 0 ≤ t → t ≤ (L : ℤ) ^ n →
        ((x + t • InfiniteLattice.axisStep (meshAt L k (j - n)) μ : Vertex L k (j - n)) :
            AmbientSpace) ∈
          cubeOfOrder L (meshAt L k (j - n)) n c.initial ∪
            cubeOfOrder L (meshAt L k (j - n)) n c.terminal :=
      fun t h0 h1 => add_smul_mem_adjacent_cubes C hL hn hc hx h0 h1
    rcases hz with rfl | rfl | ⟨b, hb, hz⟩
    · exact Or.inl hx
    · rw [shifted_eq hL hn hc]
      exact key _ (blockingFactor_pow_pos hL n).le le_rfl
    · rw [crossingPath_eq_map hE hL hn hj hc] at hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
      have hi' : ((i : ℕ) : ℤ) < (L : ℤ) ^ n := by
        have := List.mem_range.1 hi
        exact_mod_cast this
      rcases hz with rfl | rfl
      · have := key i (by omega) hi'.le
        rwa [natCast_zsmul] at this
      · have := key (i + 1) (by omega) (by omega)
        rw [add_zsmul, one_zsmul, natCast_zsmul, ← add_assoc] at this
        exact this
theorem axisPathMultiplicity (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j) (hj : j ≤ k) :
    AxisPathMultiplicity L k n j := by
  rintro b' ⟨μ, hb⟩
  have C := cubeData (k := k) hL hn hj
  have hb' := eq_forwardFrom hb
  let xs : ℕ → Vertex L k (j - n) := fun i =>
    b'.initial - (i : ℤ) • InfiniteLattice.axisStep (meshAt L k (j - n)) μ
  have hex := fun i => (C.existsUnique_mem (xs i)).exists
  choose ys hys using hex
  let F : ℕ → Edge L k j × Vertex L k (j - n) := fun i =>
    (InfiniteLattice.Link.forwardFrom (ys i) μ, xs i)
  have hF : ∀ i, (F i).1.terminal - (F i).1.initial =
      InfiniteLattice.axisStep (meshAt L k j) μ := fun i => by
    show ys i + InfiniteLattice.axisStep (meshAt L k j) μ - ys i = _
    abel
  have hset : {p : Edge L k j × Vertex L k (j - n) | p.1.IsPositivelyOriented ∧
      (p.2 : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n p.1.initial ∧
        b' ∈ crossingPath p.1 p.2} =
      F '' (↑(Finset.range (L ^ n)) : Set ℕ) := by
    ext ⟨c, x⟩
    constructor
    · rintro ⟨⟨ρ, hc⟩, hx, hmem⟩
      simp only at hc hx hmem
      rw [crossingPath_eq_map hE hL hn hj hc] at hmem
      obtain ⟨i, hi, e⟩ := List.mem_map.1 hmem
      have e₁ : b'.initial = x + i • InfiniteLattice.axisStep (meshAt L k (j - n)) ρ :=
        (congrArg InfiniteLattice.Link.initial e).symm
      have e₂ : b'.terminal = x + i • InfiniteLattice.axisStep (meshAt L k (j - n)) ρ +
          InfiniteLattice.axisStep (meshAt L k (j - n)) ρ :=
        (congrArg InfiniteLattice.Link.terminal e).symm
      have hρ : ρ = μ := by
        have h3 : InfiniteLattice.axisStep (meshAt L k (j - n)) ρ =
            InfiniteLattice.axisStep (meshAt L k (j - n)) μ := by
          rw [← hb, e₁, e₂]
          abel
        rcases axisStep_separation (k := k) hE hL (i := j - n) (by omega) ρ μ 1 1 (by simp)
          (by simp) (by simpa using h3) with ⟨h, -⟩ | ⟨h, -⟩
        · omega
        · exact h
      subst hρ
      have hxi : x = xs i := by
        show x = b'.initial - (i : ℤ) • _
        rw [e₁, natCast_zsmul]
        abel
      refine ⟨i, by simpa using List.mem_range.1 hi, ?_⟩
      have hy : c.initial = ys i :=
        (C.existsUnique_mem (xs i)).unique (hxi ▸ hx) (hys i)
      refine Prod.ext ?_ hxi.symm
      show InfiniteLattice.Link.forwardFrom (ys i) ρ = c
      rw [← hy]
      exact (eq_forwardFrom hc).symm
    · rintro ⟨i, hi, e⟩
      have hi' : i < L ^ n := by simpa using hi
      rw [← e]
      refine ⟨⟨μ, hF i⟩, hys i, ?_⟩
      rw [crossingPath_eq_map hE hL hn hj (hF i)]
      refine List.mem_map.2 ⟨i, List.mem_range.2 hi', ?_⟩
      rw [hb']
      show InfiniteLattice.Link.forwardFrom (xs i + i • _) μ = _
      congr 1
      show b'.initial - (i : ℤ) • _ + i • _ = _
      rw [natCast_zsmul]
      abel
  have hinj : Set.InjOn F (↑(Finset.range (L ^ n)) : Set ℕ) := by
    intro i hi i' hi' e
    have e₂ : xs i = xs i' := congrArg Prod.snd e
    have e₃ : (i : ℤ) • InfiniteLattice.axisStep (meshAt L k (j - n)) μ =
        (i' : ℤ) • InfiniteLattice.axisStep (meshAt L k (j - n)) μ := sub_right_injective e₂
    rcases (hE L hL k (j - n) (by omega)).2.1 μ μ i i' e₃ with ⟨h, h'⟩ | ⟨-, h⟩ <;> omega
  rw [hset, hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]
theorem adjacentCubesBounds (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j)
    (hj : j ≤ k) : AdjacentCubesBounds L k n j := by
  have C := cubeData (k := k) hL hn hj
  have ha := meshAt_pos hL k (j - n)
  have hsp := meshAt_eq_pow_mul hL k j n hn
  have hnear : ∀ (r : ℤ) (N : ℤ), 2 * |N| ≤ r * (L : ℤ) ^ n - 1 →
      |(N : ℝ) * meshAt L k (j - n)| < (r : ℝ) / 2 * meshAt L k j := by
    intro r N h
    rw [hsp]
    exact abs_intCast_mul_lt ha h
  have hin : ∀ (c : Edge L k j), ∀ x ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial,
      ∃ ν : Fin 4 → ℤ, x = offsetPoint (meshAt L k (j - n)) (c.initial : AmbientSpace) ν ∧
        ∀ ρ, 2 * |ν ρ| ≤ 1 * (L : ℤ) ^ n - 1 := by
    intro c x hx
    rw [C.eq_image] at hx
    obtain ⟨ν, hν, rfl⟩ := hx
    exact ⟨ν, (offsetPoint_eq_gridPoint _ _ _).symm, fun ρ => by simpa using hν ρ⟩
  have hfin : ∀ y : Vertex L k j, (cubeOfOrder L (meshAt L k (j - n)) n y).Finite := fun y =>
    Set.finite_of_ncard_pos (by rw [C.ncard]; exact pow_pos (blockingFactor_pos hL) _)
  refine ⟨?_, fun c _ x hx => ?_, ?_, fun b => ?_⟩
  · rintro c ⟨μ, hc⟩ x hx
    rcases hx with hx | hx
    · obtain ⟨ν, e, h⟩ := hin c x hx
      refine ⟨ν, e, fun ρ => ?_⟩
      have := hnear 3 (ν ρ) (by have := h ρ; have h0 := blockingFactor_pow_pos hL n; omega)
      simpa using this
    · rw [C.eq_image, coe_terminal hL hn hc] at hx
      obtain ⟨ν, hν, rfl⟩ := hx
      refine ⟨ν + (Pi.single μ ((L : ℤ) ^ n) : Fin 4 → ℤ), ?_, fun ρ => ?_⟩
      · rw [offsetPoint_eq_gridPoint, gridPoint_base_add_smul]
      · have hb : 2 * |(ν + (Pi.single μ ((L : ℤ) ^ n) : Fin 4 → ℤ)) ρ| ≤
            3 * (L : ℤ) ^ n - 1 := by
          have h0 := blockingFactor_pow_pos hL n
          have h1 := hν ρ
          by_cases e : ρ = μ
          · subst e
            simp only [Pi.add_apply, Pi.single_eq_same]
            rw [two_mul_abs_le_iff] at h1 ⊢
            omega
          · simp only [Pi.add_apply, Pi.single_eq_of_ne e, add_zero]
            omega
        simpa using hnear 3 _ hb
  · obtain ⟨ν, e, h⟩ := hin c x hx
    refine ⟨ν, e, fun ρ => ?_⟩
    simpa using hnear 1 (ν ρ) (h ρ)
  · rintro c -
    classical
    let dir : Edge L k (j - n) → Fin 4 := fun b =>
      if h : b.IsPositivelyOriented then h.choose else 0
    have hdir : ∀ b : Edge L k (j - n), b.IsPositivelyOriented →
        b = InfiniteLattice.Link.forwardFrom b.initial (dir b) := by
      intro b hb
      have : dir b = hb.choose := dif_pos hb
      rw [this]
      exact eq_forwardFrom hb.choose_spec
    have hN : (cubeOfOrder L (meshAt L k (j - n)) n c.initial ∪
        cubeOfOrder L (meshAt L k (j - n)) n c.terminal).ncard ≤ 2 * L ^ (4 * n) :=
      (Set.ncard_union_le _ _).trans (by rw [C.ncard, C.ncard]; omega)
    have h := encard_le_four_mul_of_injOn (T := {b : Edge L k (j - n) | b.IsPositivelyOriented ∧
      (b.initial : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial ∪
        cubeOfOrder L (meshAt L k (j - n)) n c.terminal ∧
      (b.terminal : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial ∪
        cubeOfOrder L (meshAt L k (j - n)) n c.terminal})
      ((hfin _).union (hfin _)) hN (fun b => (b.initial : AmbientSpace)) dir
      (fun b hb => hb.2.1) (by
        intro b hb b' hb' e
        have e₁ : b.initial = b'.initial := Subtype.ext (congrArg Prod.fst e)
        have e₂ : dir b = dir b' := congrArg Prod.snd e
        rw [hdir b hb.1, hdir b' hb'.1, e₁, e₂])
    refine h.trans (le_of_eq ?_)
    congr 1
    ring
  · obtain ⟨y, hy, hu⟩ := C.existsUnique_mem b.initial
    refine encard_le_eight_of_subset_range (fun p => if p.2 then InfiniteLattice.Link.forwardFrom y p.1
      else InfiniteLattice.Link.forwardFrom (y - InfiniteLattice.axisStep (meshAt L k j) p.1) p.1) ?_
    rintro c ⟨⟨ρ, hc⟩, ht, -⟩
    have hcf := eq_forwardFrom hc
    rcases ht with ht | ht
    · have h1 : c.initial = y := hu _ ht
      refine ⟨(ρ, true), ?_⟩
      simp only [if_true]
      rw [← h1]
      exact hcf.symm
    · have h1 : c.terminal = y := hu _ ht
      refine ⟨(ρ, false), ?_⟩
      simp only [Bool.false_eq_true, if_false]
      have h2 : y - InfiniteLattice.axisStep (meshAt L k j) ρ = c.initial := by
        rw [← h1, ← hc]
        abel
      rw [h2]
      exact hcf.symm
theorem isCubeOffset_iff {j : ℕ} {y : Vertex L k j} {x : Vertex L k (j - 1)}
    {ν : Fin 4 → ℤ} : IsCubeOffset L y x ν ↔
      (x : AmbientSpace) = gridPoint (axisVectors (meshAt L k (j - 1))) (y : AmbientSpace) ν ∧
        ν ∈ centeredBox ((L : ℤ) ^ 1) := by
  have hsum : ∑ μ, (Pi.single μ ((ν μ : ℝ) * meshAt L k (j - 1)) : AmbientSpace) =
      ∑ μ, ν μ • axisVectors (meshAt L k (j - 1)) μ :=
    Finset.sum_congr rfl fun μ _ => (zsmul_piSingle μ (ν μ) _).symm
  unfold IsCubeOffset
  rw [hsum, sub_eq_iff_eq_add']
  refine and_congr Iff.rfl (forall_congr' fun μ => ?_)
  rw [pow_one]
theorem cubeOffset_eq {j : ℕ} (C : CubeData L k 1 j) {y : Vertex L k j}
    {x : Vertex L k (j - 1)} {ν : Fin 4 → ℤ} (hν : ν ∈ centeredBox ((L : ℤ) ^ 1))
    (hx : (x : AmbientSpace) =
      gridPoint (axisVectors (meshAt L k (j - 1))) (y : AmbientSpace) ν) :
    cubeOffset L y x = ν := by
  have hs := Classical.epsilon_spec (p := IsCubeOffset L y x)
    ⟨ν, isCubeOffset_iff.2 ⟨hx, hν⟩⟩
  obtain ⟨h1, h2⟩ := isCubeOffset_iff.1 hs
  exact C.injOn y h2 hν (h1.symm.trans hx)
theorem contourSet_eq_image {a a' : ℝ} (y : InfiniteLattice.LatticePoint a)
    (x : InfiniteLattice.LatticePoint a') :
    contourSet L y x = (fun l => stepsInOrder (cubeOffset L y x)
      (toFiner a' y) l) '' orderingsOf (offsetSupport L y x) := by
  ext Γ
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨_, ⟨σ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
    exact ⟨σ, rfl⟩
theorem stepsInOrder_properties (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ k)
    (C : CubeData L k 1 j) {y : Vertex L k j} {ν : Fin 4 → ℤ}
    (hν : ν ∈ centeredBox ((L : ℤ) ^ 1)) {x : Vertex L k (j - 1)}
    (hx : (x : AmbientSpace) =
      gridPoint (axisVectors (meshAt L k (j - 1))) (y : AmbientSpace) ν)
    {l : List (Fin 4)} (hl : l.Nodup) (hmem : ∀ μ, μ ∈ l ↔ ν μ ≠ 0) :
    (IsLinkPath (stepsInOrder ν (toFiner (meshAt L k (j - 1)) y) l) ∧
        LinksJoin (y : AmbientSpace) (x : AmbientSpace)
          (stepsInOrder ν (toFiner (meshAt L k (j - 1)) y) l)) ∧
      HasStepsOf ν (stepsInOrder ν (toFiner (meshAt L k (j - 1)) y) l) ∧
      (stepsInOrder ν (toFiner (meshAt L k (j - 1)) y) l).length = ∑ μ, (ν μ).natAbs ∧
      ∑ μ, (ν μ).natAbs ≤ 2 * (L - 1) ∧
      ∀ z : Vertex L k (j - 1),
        (z = toFiner (meshAt L k (j - 1)) y ∨ z = x ∨
            ∃ b ∈ stepsInOrder ν (toFiner (meshAt L k (j - 1)) y) l,
              z = b.initial ∨ z = b.terminal) →
          (z : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) y := by
  have hi : j - 1 ≤ k := by omega
  have h₀ : ((toFiner (meshAt L k (j - 1)) y : Vertex L k (j - 1)) : AmbientSpace) = y :=
    coe_toFiner (blockingFactor_pos hL) (sub_sub_sub_self (n := 1) hj1) y
  have hcoe : ∀ N : Fin 4 → ℤ,
      ((gridPoint (InfiniteLattice.axisStep (meshAt L k (j - 1))) (toFiner (meshAt L k (j - 1)) y) N :
        Vertex L k (j - 1)) : AmbientSpace) =
        gridPoint (axisVectors (meshAt L k (j - 1))) (y : AmbientSpace) N := by
    intro N
    rw [coe_gridPoint, h₀]
  have hxs : x = gridPoint (InfiniteLattice.axisStep (meshAt L k (j - 1)))
      (toFiner (meshAt L k (j - 1)) y) ν := Subtype.ext (by rw [hcoe, hx])
  have hsum := list_map_sum_eq_univ_sum hl hmem
    (fun μ => ν μ • InfiniteLattice.axisStep (meshAt L k (j - 1)) μ) (fun μ h => by simp [h])
  have hruns := joins_stepsInOrder ν (toFiner (meshAt L k (j - 1)) y) l
  rw [hsum] at hruns
  have hlen := length_stepsInOrder (a := meshAt L k (j - 1)) ν
    (toFiner (meshAt L k (j - 1)) y) l
  rw [list_map_sum_eq_univ_sum hl hmem (fun μ => (ν μ).natAbs) (fun μ h => by simp [h])] at hlen
  have hsepl := axisStep_separation (k := k) hE hL hi
  refine ⟨?_, ?_, hlen, ?_, ?_⟩
  · have hr : Joins (toFiner (meshAt L k (j - 1)) y) x
        (stepsInOrder ν (toFiner (meshAt L k (j - 1)) y) l) := by
      rw [hxs]
      exact hruns
    have h2 := hr.isLinkPath_and_linksJoin
    rw [h₀] at h2
    exact h2
  · constructor
    · intro μ
      by_cases h0 : ν μ = 0
      · rw [h0]
        simp only [Int.sign_zero, Int.natAbs_zero, List.length_eq_zero_iff]
        refine List.filter_eq_nil_iff.2 fun b hb hp => ?_
        obtain ⟨ρ, -, e, hρ⟩ := mem_stepsInOrder hb
        have hp' : IsSignedAxisStep b 0 μ := by
          classical
          exact of_decide_eq_true hp
        have e' : (ν ρ).sign • InfiniteLattice.axisStep (meshAt L k (j - 1)) ρ =
            0 • InfiniteLattice.axisStep (meshAt L k (j - 1)) μ := e.symm.trans hp'
        have hs : (ν ρ).sign ≠ 0 := by
          rcases lt_or_gt_of_ne hρ with h | h
          · rw [Int.sign_eq_neg_one_of_neg h]
            omega
          · rw [Int.sign_eq_one_of_pos h]
            omega
        have h1 : |(ν ρ).sign| ≤ 1 := by
          rcases lt_or_gt_of_ne hρ with h | h
          · simp [Int.sign_eq_neg_one_of_neg h]
          · simp [Int.sign_eq_one_of_pos h]
        rcases hsepl ρ μ _ 0 h1 (by simp) e' with ⟨h, -⟩ | ⟨-, h⟩
        · exact hs h
        · exact hs h
      · have hf := filter_length_stepsInOrder hsepl
          (fun b => @decide (IsSignedAxisStep b (ν μ).sign μ) (Classical.propDecidable _)) h0
          (fun b => @decide_eq_true_iff _ (Classical.propDecidable _))
          (toFiner (meshAt L k (j - 1)) y) l hl
        rw [if_pos ((hmem μ).2 h0)] at hf
        exact hf
    · intro b hb
      obtain ⟨ρ, -, e, hρ⟩ := mem_stepsInOrder hb
      exact ⟨ρ, hρ, e⟩
  · have h : ∀ μ, 2 * (ν μ).natAbs + 1 ≤ L := by
      intro μ
      have h1 := hν μ
      rw [pow_one, Int.abs_eq_natAbs] at h1
      omega
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    rw [Fin.sum_univ_four]
    omega
  · have hN : ∀ N : Fin 4 → ℤ, (∀ ρ, |N ρ| ≤ |ν ρ|) →
        ((gridPoint (InfiniteLattice.axisStep (meshAt L k (j - 1)))
            (toFiner (meshAt L k (j - 1)) y) N : Vertex L k (j - 1)) : AmbientSpace) ∈
          cube L (meshAt L k (j - 1)) y := by
      intro N h
      rw [hcoe]
      refine C.mem y N fun ρ => ?_
      have h1 := hν ρ
      have h2 := h ρ
      omega
    have hzero : ∀ ρ, |(0 : Fin 4 → ℤ) ρ| ≤ |ν ρ| := fun ρ => by simp
    intro z hz
    rcases hz with rfl | rfl | ⟨b, hb, hz⟩
    · have := hN 0 hzero
      rwa [gridPoint_zero] at this
    · rw [hxs]
      exact hN ν fun ρ => le_rfl
    · rw [show toFiner (meshAt L k (j - 1)) y =
        gridPoint (InfiniteLattice.axisStep (meshAt L k (j - 1)))
          (toFiner (meshAt L k (j - 1)) y) 0 from (gridPoint_zero _ _).symm] at hb
      obtain ⟨⟨N₁, e₁, h₁⟩, ⟨N₂, e₂, h₂⟩⟩ := ends_stepsInOrder l hl 0 hzero (fun _ _ => rfl) hb
      rcases hz with rfl | rfl
      · rw [e₁]
        exact hN N₁ h₁
      · rw [e₂]
        exact hN N₂ h₂
theorem vertexImage_spaceTranslation {i : ℕ} {w : AmbientSpace} {v : Vertex L k i}
    (hv : (v : AmbientSpace) = w) (x : Vertex L k i) :
    vertexImage (spaceTranslation w) x = x + v := by
  subst hv
  exact Subtype.ext (Classical.epsilon_spec
    (p := fun x' : Vertex L k i => (x' : AmbientSpace) = spaceTranslation (v : AmbientSpace) x)
    ⟨x + v, rfl⟩)
theorem edgeImage_spaceTranslation {i : ℕ} {w : AmbientSpace} {v : Vertex L k i}
    (hv : (v : AmbientSpace) = w) (b : Edge L k i) :
    edgeImage (spaceTranslation w) b = translateLink v b := by
  have h := Classical.epsilon_spec
    (p := fun b' : Edge L k i => b'.initial = vertexImage (spaceTranslation w) b.initial ∧
      b'.terminal = vertexImage (spaceTranslation w) b.terminal)
    ⟨translateLink v b, by rw [vertexImage_spaceTranslation hv]; rfl,
      by rw [vertexImage_spaceTranslation hv]; rfl⟩
  refine InfiniteLattice.Link.ext ?_ ?_
  · exact h.1.trans (vertexImage_spaceTranslation hv _)
  · exact h.2.trans (vertexImage_spaceTranslation hv _)
theorem pathImage_spaceTranslation {i : ℕ} {w : AmbientSpace} {v : Vertex L k i}
    (hv : (v : AmbientSpace) = w) (Γ : List (Edge L k i)) :
    pathImage (a := meshAt L k i) (spaceTranslation w) Γ = Γ.map (translateLink v) :=
  List.map_congr_left fun b _ => edgeImage_spaceTranslation hv b
theorem contourTranslation (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j) (hj1 : 1 ≤ j)
    (hj : j ≤ k) : ContourTranslation L k n j := by
  have C := cubeData (k := k) (n := 1) (j := j) hL hj1 hj
  have hle : ∀ i ≤ j, j - (j - i) = i := fun i hi => by omega
  have hin : ∀ (i : ℕ), i ≤ j → ∀ v : Vertex L k j,
      ((toFiner (meshAt L k i) v : Vertex L k i) : AmbientSpace) = v :=
    fun i hi v => coe_toFiner (blockingFactor_pos hL) (hle i hi) v
  refine ⟨fun y ν hν x hx => ?_, fun v a b => ?_, fun v i hi => ⟨?_, ?_, ?_⟩,
    fun v y ν hν x hx => ?_, ?_⟩
  · rw [offsetBox_eq_centeredBox] at hν
    rw [offsetPoint_eq_gridPoint] at hx
    refine ⟨hx ▸ C.mem y ν hν, fun Γ hΓ => ?_⟩
    have hbd := cubeOffset_eq C hν hx
    rw [contourSet_eq_image] at hΓ
    obtain ⟨l, ⟨σ, rfl⟩, rfl⟩ := hΓ
    obtain ⟨hnd, hmem⟩ := nodup_and_mem_of_equiv σ
    generalize (List.finRange (offsetSupport L y x).card).map
      (fun i => ((σ i : offsetSupport L y x) : Fin 4)) = l at hnd hmem ⊢
    have hmem' : ∀ μ, μ ∈ l ↔ ν μ ≠ 0 := fun μ => by
      rw [hmem]
      simp [offsetSupport, hbd]
    simp only [hbd]
    exact stepsInOrder_properties hE hL hj1 hj C hν hx hnd hmem'
  · show TorusMetric.euclidNormVec (a + (v : AmbientSpace) - (b + (v : AmbientSpace))) = _
    rw [add_sub_add_right_eq_sub]
  · ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine add_mem hq ?_
      rw [← hin i hi v]
      exact SetLike.coe_mem _
    · intro hp
      refine ⟨p - (v : AmbientSpace), sub_mem hp ?_, ?_⟩
      · rw [← hin i hi v]
        exact SetLike.coe_mem _
      · show p - (v : AmbientSpace) + (v : AmbientSpace) = p
        abel
  · intro b
    refine ⟨translateLink (toFiner (meshAt L k i) v) b, ?_, ?_⟩
    · show ((b.initial + toFiner (meshAt L k i) v : Vertex L k i) : AmbientSpace) = _
      rw [AddSubgroup.coe_add, hin i hi v]
      rfl
    · show ((b.terminal + toFiner (meshAt L k i) v : Vertex L k i) : AmbientSpace) = _
      rw [AddSubgroup.coe_add, hin i hi v]
      rfl
  · intro b'
    refine ⟨translateLink (-toFiner (meshAt L k i) v) b', ?_, ?_⟩
    · show _ = ((b'.initial + -toFiner (meshAt L k i) v : Vertex L k i) : AmbientSpace) +
        (v : AmbientSpace)
      rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, hin i hi v]
      abel
    · show _ = ((b'.terminal + -toFiner (meshAt L k i) v : Vertex L k i) : AmbientSpace) +
        (v : AmbientSpace)
      rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, hin i hi v]
      abel
  · rw [offsetBox_eq_centeredBox] at hν
    rw [offsetPoint_eq_gridPoint] at hx
    have hv := hin (j - 1) (by omega) v
    have hbd₁ := cubeOffset_eq C hν hx
    have hbd₂ : cubeOffset L (y + v) (x + toFiner (meshAt L k (j - 1)) v) = ν :=
      cubeOffset_eq C hν (by
        rw [AddSubgroup.coe_add, AddSubgroup.coe_add, hv, hx, gridPoint_add_base])
    have hS : offsetSupport L (y + v) (x + toFiner (meshAt L k (j - 1)) v) =
        offsetSupport L y x := by
      unfold offsetSupport
      rw [hbd₁, hbd₂]
    rw [contourSet_eq_image, contourSet_eq_image, hS, hbd₁, hbd₂, image_image]
    refine image_congr fun l _ => ?_
    rw [pathImage_spaceTranslation hv, map_translateLink_stepsInOrder]
    congr 1
    apply Subtype.ext
    rw [AddSubgroup.coe_add, hv, coe_toFiner (blockingFactor_pos hL) (by omega) y,
      coe_toFiner (blockingFactor_pos hL) (by omega) (y + v), AddSubgroup.coe_add]
  · rintro v c ⟨μ, hc⟩ z -
    have hv := hin (j - n) (by omega) v
    rw [pathImage_spaceTranslation hv, crossingPath_eq_signedSteps hE hL hn hj hc,
      map_translateLink_signedSteps]
    have e : (shifted c z + toFiner (meshAt L k (j - n)) v) -
        (z + toFiner (meshAt L k (j - n)) v) =
        ((L : ℤ) ^ n) • InfiniteLattice.axisStep (meshAt L k (j - n)) μ := by
      rw [shifted_eq hL hn hc]
      abel
    exact ((hE L hL k (j - n) (by omega)).2.2 _ _ μ μ _ _ e e).2.symm
theorem pivotOnAxisPath (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ k) :
    PivotOnAxisPath L k j := by
  have C := cubeData (k := k) (n := 1) (j := j) hL hj1 hj
  obtain ⟨h, hLh⟩ := hL.1
  have hpath : ∀ (c : Edge L k j) (μ : Fin 4),
      c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ →
      axisPath (toFiner (meshAt L k (j - 1)) c.initial) (toFiner (meshAt L k (j - 1)) c.terminal) =
        (List.range L).map fun i => InfiniteLattice.Link.forwardFrom
          (toFiner (meshAt L k (j - 1)) c.initial +
            i • InfiniteLattice.axisStep (meshAt L k (j - 1)) μ) μ := by
    intro c μ hc
    have e : shifted c (toFiner (meshAt L k (j - 1)) c.initial) =
        toFiner (meshAt L k (j - 1)) c.terminal := by
      apply Subtype.ext
      rw [coe_shifted_eq hL hj1, coe_toFiner (blockingFactor_pos hL) (sub_sub_sub_self (n := 1) hj1),
        coe_toFiner (blockingFactor_pos hL) (sub_sub_sub_self (n := 1) hj1)]
      abel
    have := crossingPath_eq_map (n := 1) hE hL hj1 hj hc (toFiner (meshAt L k (j - 1)) c.initial)
    rw [pow_one] at this
    rw [← e]
    exact this
  have hiff : ∀ (c : Edge L k j) (μ : Fin 4),
      c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ →
      ∀ b : Edge L k (j - 1), IsPivotLink L (meshAt L k (j - 1)) c b ↔
        b = InfiniteLattice.Link.forwardFrom (toFiner (meshAt L k (j - 1)) c.initial +
          h • InfiniteLattice.axisStep (meshAt L k (j - 1)) μ) μ := by
    intro c μ hc b
    have hne : c.initial ≠ c.terminal := by
      intro e
      apply axisStep_ne_zero hE hL hj μ
      rw [← hc, e, sub_self]
    have hdis := C.disjoint hne
    have hLZ : (L : ℤ) = 2 * (h : ℤ) + 1 := by exact_mod_cast hLh
    have hbox : ∀ t : ℤ, 2 * |t| ≤ (L : ℤ) - 1 →
        (Pi.single μ t : Fin 4 → ℤ) ∈ centeredBox ((L : ℤ) ^ 1) := by
      intro t ht
      have := add_single_mem_centeredBox
        (zero_mem_centeredBox (M := (L : ℤ) ^ 1) (by rw [pow_one]; omega)) (μ := μ)
        (t := t) (by simpa using ht)
      simpa using this
    have hz : ∀ t : ℤ, ((toFiner (meshAt L k (j - 1)) c.initial +
        t • InfiniteLattice.axisStep (meshAt L k (j - 1)) μ : Vertex L k (j - 1)) : AmbientSpace) =
        gridPoint (axisVectors (meshAt L k (j - 1))) (c.initial : AmbientSpace) (Pi.single μ t) := by
      intro t
      rw [gridPoint_single, AddSubgroup.coe_add, coe_zsmul_axisStep,
        coe_toFiner (blockingFactor_pos hL) (sub_sub_sub_self (n := 1) hj1)]
    have hz₂ : ∀ t : ℤ, ((toFiner (meshAt L k (j - 1)) c.initial +
        t • InfiniteLattice.axisStep (meshAt L k (j - 1)) μ : Vertex L k (j - 1)) : AmbientSpace) =
        gridPoint (axisVectors (meshAt L k (j - 1))) (c.terminal : AmbientSpace)
          (Pi.single μ (t - L)) := by
      intro t
      have e : (Pi.single μ t : Fin 4 → ℤ) =
          (Pi.single μ (t - L) : Fin 4 → ℤ) + (Pi.single μ (L : ℤ) : Fin 4 → ℤ) := by
        rw [← Pi.single_add]
        simp
      rw [hz, coe_terminal hL hj1 hc, pow_one, gridPoint_base_add_smul, e]
    have hin₁ : ∀ t : ℤ, 2 * |t| ≤ (L : ℤ) - 1 →
        ((toFiner (meshAt L k (j - 1)) c.initial +
          t • InfiniteLattice.axisStep (meshAt L k (j - 1)) μ : Vertex L k (j - 1)) : AmbientSpace) ∈
          cube L (meshAt L k (j - 1)) c.initial := fun t ht => by
      rw [hz]
      exact C.mem _ _ (hbox t ht)
    have hin₂ : ∀ t : ℤ, 2 * |t - L| ≤ (L : ℤ) - 1 →
        ((toFiner (meshAt L k (j - 1)) c.initial +
          t • InfiniteLattice.axisStep (meshAt L k (j - 1)) μ : Vertex L k (j - 1)) : AmbientSpace) ∈
          cube L (meshAt L k (j - 1)) c.terminal := fun t ht => by
      rw [hz₂]
      exact C.mem _ _ (hbox _ ht)
    constructor
    · rintro ⟨⟨h₂, h₃⟩, hb⟩
      rw [hpath c μ hc] at hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
      have hi' := List.mem_range.1 hi
      have hbi : ((i : ℕ) : ℤ) ≤ h := by
        by_contra hlt
        have h4 := hin₂ i (by rw [two_mul_abs_le_iff]; omega)
        rw [natCast_zsmul] at h4
        exact Set.disjoint_left.mp hdis h₂ h4
      have hbi' : (h : ℤ) ≤ i := by
        by_contra hlt
        have h4 := hin₁ (i + 1) (by rw [two_mul_abs_le_iff]; omega)
        rw [add_zsmul, one_zsmul, natCast_zsmul, ← add_assoc] at h4
        exact Set.disjoint_left.mp hdis h4 h₃
      have hih : i = h := by omega
      rw [hih]
    · rintro rfl
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have h4 := hin₁ h (by rw [two_mul_abs_le_iff]; omega)
        rwa [natCast_zsmul] at h4
      · have h4 := hin₂ (h + 1) (by rw [two_mul_abs_le_iff]; omega)
        rwa [add_zsmul, one_zsmul, natCast_zsmul, ← add_assoc] at h4
      · rw [hpath c μ hc]
        exact List.mem_map.2 ⟨h, List.mem_range.2 (by omega), rfl⟩
  refine ⟨fun c μ hc => ?_, fun c μ hc => ?_, fun c μ hc b hb => ?_, fun c μ hc b hb => ?_⟩
  · rw [hpath c μ hc]
    simp
  · exact ⟨_, (hiff c μ hc _).2 rfl, fun b hb => (hiff c μ hc b).1 hb⟩
  · rw [(hiff c μ hc b).1 hb]
    show ((toFiner (meshAt L k (j - 1)) c.initial +
      h • InfiniteLattice.axisStep (meshAt L k (j - 1)) μ : Vertex L k (j - 1)) : AmbientSpace) = _
    rw [AddSubgroup.coe_add, coe_toFiner (blockingFactor_pos hL) (sub_sub_sub_self (n := 1) hj1),
      ← natCast_zsmul, coe_zsmul_axisStep]
    congr 1
    show ((h : ℤ)) • (Pi.single μ _ : AmbientSpace) = _
    rw [zsmul_piSingle]
    congr 1
    rw [hLh]
    push_cast
    ring
  · have hs := Classical.epsilon_spec (p := IsPivotLink L (meshAt L k (j - 1)) c) ⟨b, hb⟩
    exact ((hiff c μ hc b).1 hb).trans ((hiff c μ hc _).1 hs).symm
theorem atInfiniteSide (hE : AxisPathUniqueness.AxisPathsUnique)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {n j : ℕ} (hn : n ≤ j) (hj : j ≤ k) :
    RefinedCubesPartition L k n j ∧ FaceSteps L k n j ∧
      CubeTranslateAlongLink L k n j ∧ AxisPathMultiplicity L k n j ∧
      AdjacentCubesBounds L k n j ∧
      (1 ≤ j → ContourTranslation L k n j ∧ PivotOnAxisPath L k j) :=
  ⟨refinedCubesPartition hL hn hj, faceSteps hE hL hn hj, cubeTranslateAlongLink hE hL hn hj,
    axisPathMultiplicity hE hL hn hj, adjacentCubesBounds hL hn hj,
    fun hj1 => ⟨contourTranslation hE hL hn hj1 hj, pivotOnAxisPath hE hL hj1 hj⟩⟩
end Requirements
end YangMills.Construction.Tower.FullSpace.CubesAndPaths
namespace YangMills.Construction.Tower.BlockPathContourPivotProof
theorem blockPathContourPivot (h₁ : PeriodicLattice.BlockPartition.Properties)
    (hE : AxisPathUniqueness.AxisPathsUnique) : BlockPathContourPivotStatement := by
  intro L hL k n j _ hn hj
  obtain ⟨w₁, w₂, w₃, w₄, w₅, w₆⟩ :=
    FullSpace.CubesAndPaths.atInfiniteSide (k := k) hE hL hn hj
  exact ⟨fun m hm => Periodic.atFiniteSide hE h₁ hL hm hn hj, w₁, w₂, w₃, w₄, w₅, w₆⟩
end YangMills.Construction.Tower.BlockPathContourPivotProof
end
