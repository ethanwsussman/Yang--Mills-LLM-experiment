import YangMills.Construction.HoleBesideASecondHole.DistancesBlocksAndLumpsProof
import YangMills.Construction.HullsInEveryVolume.SixteenOffsetsSeparatePlaces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardGrids
open HullTrees TorusFields TorusLumps WeightedResponses
variable {n : ℕ} [NeZero n]
private theorem val_add_mod_of_dvd {l : ℕ} (hl : l ∣ n) (a b : ZMod n) :
    (a + b).val % l = (a.val + b.val) % l := by
  rw [ZMod.val_add, Nat.mod_mod_of_dvd _ hl]
private theorem natAbs_valMinAbs_natCast_le (k : ℕ) : (((k : ZMod n)).valMinAbs).natAbs ≤ k := by apply _root_.YangMills.Construction.LumpContours.natAbs_valMinAbs_natCast_le <;> assumption
private theorem val_add_div_of_mod_add_lt {l s : ℕ} (hl : l ∣ n) (y : ZMod n) (h : y.val % l + s < l) :
    (y + (s : ZMod n)).val / l = y.val / l := by
  obtain ⟨k, hk⟩ := hl
  have hl0 : 0 < l := by omega
  have hy : y.val < n := ZMod.val_lt y
  have hq : y.val / l < k := Nat.div_lt_of_lt_mul (by rw [← hk]; exact hy)
  have e := Nat.div_add_mod y.val l
  have hm : l * (y.val / l + 1) ≤ l * k := Nat.mul_le_mul_left l hq
  have hlt : y.val + s < n := by
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  have hval : (y + (s : ZMod n)).val = y.val + s := by
    rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, Nat.mod_eq_of_lt hlt]
  rw [hval]
  have e2 : y.val + s = (y.val % l + s) + l * (y.val / l) := by omega
  rw [e2, Nat.add_mul_div_left _ _ hl0, Nat.div_eq_of_lt h, Nat.zero_add]
private theorem block_index_eq_of_near {l r o : ℕ} (hl : l ∣ n) (a x : ZMod n)
    (good : (a - ((10 * r : ℕ) : ZMod n) - ((o + 1 : ℕ) : ZMod n)).val % l + 20 * r < l)
    (near : ((x - a).valMinAbs).natAbs ≤ 10 * r) :
    (x - ((o + 1 : ℕ) : ZMod n)).val / l = (a - ((o + 1 : ℕ) : ZMod n)).val / l := by
  set y : ZMod n := a - ((10 * r : ℕ) : ZMod n) - ((o + 1 : ℕ) : ZMod n) with hy
  set e : ℤ := (x - a).valMinAbs with he
  have h1 : 0 ≤ e + 10 * (r : ℤ) := by omega
  have hs : ((e + 10 * (r : ℤ)).toNat : ℤ) = e + 10 * (r : ℤ) := Int.toNat_of_nonneg h1
  have hs20 : (e + 10 * (r : ℤ)).toNat ≤ 20 * r := by omega
  have hcast : (((e + 10 * (r : ℤ)).toNat : ℕ) : ZMod n) = (x - a) + ((10 * r : ℕ) : ZMod n) := by
    have := congrArg (Int.cast : ℤ → ZMod n) hs
    rw [Int.cast_natCast] at this
    rw [this]
    push_cast
    rw [he, ZMod.coe_valMinAbs]
  have hx : x - ((o + 1 : ℕ) : ZMod n) = y + (((e + 10 * (r : ℤ)).toNat : ℕ) : ZMod n) := by
    rw [hcast, hy]; ring
  have ha : a - ((o + 1 : ℕ) : ZMod n) = y + ((10 * r : ℕ) : ZMod n) := by
    rw [hy]; ring
  rw [hx, ha, val_add_div_of_mod_add_lt hl y (by omega), val_add_div_of_mod_add_lt hl y (by omega)]
private def axisOffset (l : ℕ) (b : Bool) : ℕ := if b then (l - 1) / 2 else 0
private theorem exists_clear_axisOffset {l r : ℕ} (hl : l ∣ n) (hodd : Odd l) (hr : 40 * r ≤ l) (a : ZMod n) :
    ∃ b : Bool, (a - ((10 * r : ℕ) : ZMod n) - ((axisOffset l b + 1 : ℕ) : ZMod n)).val % l + 20 * r < l := by
  obtain ⟨h, hh⟩ := hodd
  have hlh : (l - 1) / 2 = h := by omega
  by_cases h0 : (a - ((10 * r : ℕ) : ZMod n) - ((axisOffset l false + 1 : ℕ) : ZMod n)).val % l + 20 * r < l
  · exact ⟨false, h0⟩
  · refine ⟨true, ?_⟩
    have e1 : axisOffset l true = h := by simp [axisOffset, hlh]
    rw [e1]
    set y : ZMod n := a - ((10 * r : ℕ) : ZMod n) - ((h + 1 : ℕ) : ZMod n) with hy
    have hy0 : a - ((10 * r : ℕ) : ZMod n) - ((axisOffset l false + 1 : ℕ) : ZMod n) = y + ((h : ℕ) : ZMod n) := by
      have e0 : axisOffset l false = 0 := by simp [axisOffset]
      rw [e0, hy]; push_cast; ring
    rw [hy0] at h0
    have hl0 : 0 < l := by omega
    have hhl : h < l := by omega
    have key : (y + ((h : ℕ) : ZMod n)).val % l = (y.val % l + h) % l := by
      rw [val_add_mod_of_dvd hl, ZMod.val_natCast, Nat.add_mod, Nat.mod_mod_of_dvd _ hl, Nat.mod_eq_of_lt hhl]
    rw [key] at h0
    have ht : y.val % l < l := Nat.mod_lt _ hl0
    by_cases hc : y.val % l + h < l
    · rw [Nat.mod_eq_of_lt hc] at h0
      omega
    · have e2 : (y.val % l + h) % l = y.val % l + h - l := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e2] at h0
      omega
private theorem natAbs_valMinAbs_sub_le_of_same_block {l w : ℕ} (u v c : ZMod n) (h1 : (u - c).val / l = (v - c).val / l)
    (h2 : ((u - c).val % l) / (w + 1) = ((v - c).val % l) / (w + 1)) :
    ((u - v).valMinAbs).natAbs ≤ w := by
  have eU : (((u - c).val : ℕ) : ZMod n) = u - c := ZMod.natCast_zmod_val _
  have eV : (((v - c).val : ℕ) : ZMod n) = v - c := ZMod.natCast_zmod_val _
  generalize (u - c).val = A at *
  generalize (v - c).val = B at *
  have eA := Nat.div_add_mod A l
  have eB := Nat.div_add_mod B l
  rw [← h1] at eB
  have fA := Nat.div_add_mod (A % l) (w + 1)
  have fB := Nat.div_add_mod (B % l) (w + 1)
  rw [← h2] at fB
  have mA : A % l % (w + 1) < w + 1 := Nat.mod_lt _ (Nat.succ_pos w)
  have mB : B % l % (w + 1) < w + 1 := Nat.mod_lt _ (Nat.succ_pos w)
  rcases le_total B A with hBA | hAB
  · have hd : u - v = ((A - B : ℕ) : ZMod n) := by
      rw [Nat.cast_sub hBA, eU, eV]; ring
    rw [hd]
    refine (natAbs_valMinAbs_natCast_le _).trans ?_
    omega
  · have hd : u - v = -((B - A : ℕ) : ZMod n) := by
      rw [Nat.cast_sub hAB, eU, eV]; ring
    rw [hd, ZMod.natAbs_valMinAbs_neg]
    refine (natAbs_valMinAbs_natCast_le _).trans ?_
    omega
private theorem leastPowerAbove_properties {L r N : ℕ} (hL : 3 ≤ L) (hodd : Odd L)
    (hside : 2 * leastPowerAbove L (40 * r) ≤ 2 * L ^ N) :
    leastPowerAbove L (40 * r) ∣ 2 * L ^ N ∧ Odd (leastPowerAbove L (40 * r)) ∧ 40 * r ≤ leastPowerAbove L (40 * r) ∧
      leastPowerAbove L (40 * r) ≤ (20 * r + 1) * (2 * L) := by
  have h1 : 1 < L := by omega
  have hp : Nat.clog L (40 * r) ≤ N := by
    have h2 : L ^ Nat.clog L (40 * r) ≤ L ^ N := by
      have : leastPowerAbove L (40 * r) ≤ L ^ N := by omega
      exact this
    exact (Nat.pow_le_pow_iff_right h1).mp h2
  refine ⟨Dvd.dvd.mul_left (pow_dvd_pow L hp) 2, hodd.pow, Nat.le_pow_clog h1 _, ?_⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [leastPowerAbove]
    omega
  · have h40 : 1 < 40 * r := by omega
    have hlt := Nat.pow_pred_clog_lt_self h1 h40
    have hc : 0 < Nat.clog L (40 * r) := Nat.clog_pos h1 (by omega)
    obtain ⟨k, hk⟩ : ∃ k, Nat.clog L (40 * r) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc).symm⟩
    rw [hk] at hlt
    simp only [Nat.pred_succ] at hlt
    have e : (20 * r + 1) * (2 * L) = 40 * r * L + 2 * L := by ring
    have h3 : L ^ k * L ≤ 40 * r * L := Nat.mul_le_mul_right _ hlt.le
    rw [leastPowerAbove, hk, pow_succ, e]
    omega
private theorem exists_grid_of_separated {l L r : ℕ} (hl : l ∣ n) (hodd : Odd l) (hr : 40 * r ≤ l)
    (hroom : l ≤ (20 * r + 1) * (2 * L)) (S : Finset (TorusSite n)) (hS : Separated (30 * r) S) :
    ∃ (g : MirrorGrid) (I : Finset (TorusSite n)), g.side = l ∧ I ⊆ S ∧
      (S.card : ℝ) ≤ 16 * (2 * (L : ℝ)) ^ 4 * (I.card : ℝ) ∧
      ∃ c : TorusSite n → Fin 4 → ℕ, (∀ z ∈ I, c z ∈ g.cellIndices n ∧ box z (10 * r) ⊆ g.cellSites n (c z)) ∧
        ∀ z ∈ I, ∀ z' ∈ I, z ≠ z' → c z ≠ c z' := by
  classical
  have hl0 : 0 < l := hodd.pos
  have pick : ∀ z : TorusSite n, ∃ τ : Fin 4 → Bool, ∀ i,
      (z i - ((10 * r : ℕ) : ZMod n) - ((axisOffset l (τ i) + 1 : ℕ) : ZMod n)).val % l + 20 * r < l := fun z => by
    choose τ hτ using fun i => exists_clear_axisOffset hl hodd hr (z i)
    exact ⟨τ, hτ⟩
  choose τ hτ using pick
  obtain ⟨τ₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 4 → Bool))
    (fun t => (S.filter fun z => τ z = t).card) ⟨fun _ => false, Finset.mem_univ _⟩
  set S' : Finset (TorusSite n) := S.filter fun z => τ z = τ₀ with hS'
  have h16 : S.card ≤ S'.card * 16 := by
    have h1 := Finset.card_le_mul_card_image (f := τ) S S'.card (fun t _ => hmax t (Finset.mem_univ t))
    have h2 : (S.image τ).card ≤ 16 := by
      refine (Finset.card_le_card (Finset.subset_univ _)).trans ?_
      simp [Finset.card_univ, Fintype.card_pi]
    exact h1.trans (Nat.mul_le_mul_left _ h2)
  let cc : Fin 4 → ZMod n := fun i => ((axisOffset l (τ₀ i) + 1 : ℕ) : ZMod n)
  let g : MirrorGrid := ⟨l, fun i => ((axisOffset l (τ₀ i) : ℕ) : ℤ)⟩
  have hcell : ∀ (x : TorusSite n) i, g.cellIndex x i = (x i - cc i).val / l := by
    intro x i
    have e : (((g.offset i + 1 : ℤ)) : ZMod n) = cc i := by
      simp [g, cc]
    show (x i - (((g.offset i + 1 : ℤ)) : ZMod n)).val / l = _
    rw [e]
  have hfib : ∀ c, (S'.filter fun z => g.cellIndex z = c).card ≤ (2 * L) ^ 4 := by
    intro c
    let b : TorusSite n → Fin 4 → ℕ := fun x i => ((x i - cc i).val % l) / (20 * r + 1)
    have hmaps : ∀ x ∈ (S'.filter fun z => g.cellIndex z = c),
        b x ∈ Fintype.piFinset fun _ : Fin 4 => Finset.range (2 * L) := by
      intro x _
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range]
      exact Nat.div_lt_of_lt_mul ((Nat.mod_lt _ hl0).trans_le hroom)
    have hinj : Set.InjOn b ((S'.filter fun z => g.cellIndex z = c : Finset _) : Set (TorusSite n)) := by
      intro x hx y hy hxy
      by_contra hne
      have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
      have hy' := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
      have hd := hS x (Finset.mem_filter.mp hx'.1).1 y (Finset.mem_filter.mp hy'.1).1 hne
      have hc : ∀ i, ((x i - y i).valMinAbs).natAbs ≤ 20 * r := by
        intro i
        refine natAbs_valMinAbs_sub_le_of_same_block (l := l) (x i) (y i) (cc i) ?_ (congrFun hxy i)
        rw [← hcell, ← hcell, hx'.2, hy'.2]
      have hle : supDist x y ≤ 20 * r := Finset.sup_le fun i _ => hc i
      have hr0 : r = 0 := by omega
      apply hne
      funext i
      have h3 := hc i
      rw [hr0] at h3
      have h0 : (x i - y i).valMinAbs = 0 := by omega
      exact sub_eq_zero.mp ((ZMod.valMinAbs_eq_zero _).mp h0)
    have h4 := Finset.card_le_card_of_injOn b hmaps hinj
    simpa using h4
  have h2 : S'.card ≤ (2 * L) ^ 4 * (S'.image g.cellIndex).card :=
    Finset.card_le_mul_card_image S' _ (fun c _ => hfib c)
  let rep : (Fin 4 → ℕ) → TorusSite n := Function.invFunOn g.cellIndex (S' : Set (TorusSite n))
  have rep_mem : ∀ c ∈ S'.image g.cellIndex, rep c ∈ S' ∧ g.cellIndex (rep c) = c := by
    intro c hc
    obtain ⟨a, ha, hac⟩ := Finset.mem_image.mp hc
    have hc' : c ∈ g.cellIndex '' (S' : Set (TorusSite n)) := ⟨a, Finset.mem_coe.mpr ha, hac⟩
    exact ⟨Finset.mem_coe.mp (Function.invFunOn_mem hc'), Function.invFunOn_eq hc'⟩
  let I : Finset (TorusSite n) := (S'.image g.cellIndex).image rep
  have hIS' : I ⊆ S' := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    exact (rep_mem c hc).1
  have hIcard : I.card = (S'.image g.cellIndex).card := by
    refine Finset.card_image_of_injOn ?_
    intro c hc c' hc' h
    have h5 := congrArg g.cellIndex h
    rwa [(rep_mem c (Finset.mem_coe.mp hc)).2, (rep_mem c' (Finset.mem_coe.mp hc')).2] at h5
  refine ⟨g, I, rfl, fun z hz => (Finset.mem_filter.mp (hIS' hz)).1, ?_, g.cellIndex, ?_, ?_⟩
  · have h6 : S.card ≤ 16 * (2 * L) ^ 4 * I.card := by
      rw [hIcard]
      calc S.card ≤ S'.card * 16 := h16
        _ ≤ ((2 * L) ^ 4 * (S'.image g.cellIndex).card) * 16 := Nat.mul_le_mul_right _ h2
        _ = 16 * (2 * L) ^ 4 * (S'.image g.cellIndex).card := by ring
    exact_mod_cast h6
  · intro z hz
    refine ⟨?_, ?_⟩
    · rw [MirrorGrid.cellIndices, Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range, hcell]
      exact Nat.div_lt_div_of_lt_of_dvd hl (ZMod.val_lt _)
    · intro x hx
      have hzS' := Finset.mem_filter.mp (hIS' hz)
      have hxz : supDist x z ≤ 10 * r := by simpa [box, thickening] using hx
      simp only [MirrorGrid.cellSites, Finset.mem_filter, Finset.mem_univ, true_and]
      funext i
      rw [hcell, hcell]
      refine block_index_eq_of_near (r := r) (o := axisOffset l (τ₀ i)) hl (z i) (x i) ?_ ?_
      · have h7 := hτ z i
        rw [hzS'.2] at h7
        exact h7
      · exact (Finset.le_sup (f := fun i => ((x i - z i).valMinAbs).natAbs) (Finset.mem_univ i)).trans hxz
  · intro z hz z' hz' hne hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hz'
    apply hne
    rw [(rep_mem a ha).2, (rep_mem a' ha').2] at hc
    rw [hc]
theorem offsetSeparationStatement_holds : offsetSeparationStatement := by
  unfold offsetSeparationStatement EventuallyInParameters
  intro a _
  refine ⟨3, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L hLodd hL3 Tb _ hTL _ _ _ _ _
  subst hTL
  refine ⟨0, fun Kr _ _ _ _ _ => ⟨0, fun y _ _ _ => ?_⟩⟩
  intro g β K m T u n _ hA hside S hS
  have hn : n = 2 * Tb.side ^ (m + (K - u)) := by
    rw [hA.side_eq, torusSideAtLevel, fineSide_eq, pow_add]
    ring
  obtain ⟨f1, f2, f3, f4⟩ := leastPowerAbove_properties (r := stageRange T u) (N := m + (K - u)) hL3 hLodd (by
    rw [← hn]
    exact hside)
  have f1' : leastPowerAbove Tb.side (40 * stageRange T u) ∣ n := by
    rw [hn]
    exact f1
  exact exists_grid_of_separated (L := Tb.side) (r := stageRange T u) f1' f2 f3 f4 S hS
end YangMills.Construction.ChessboardGrids
end
