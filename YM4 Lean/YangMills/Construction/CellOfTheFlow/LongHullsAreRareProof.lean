import YangMills.Construction.CellOfTheFlow.LongHullsAreRare
import YangMills.Construction.CellOfTheFlow.SixteenGridsCoverTheTorus
import YangMills.Construction.ClusterExpansionOfAStep.CountsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps WeightedResponses RenormalizationStepParameters BlockAverages LumpContours TorusCounting
namespace LongHullsRare
section Lists
variable {V : Type*}
private def ChainsTo (Rl : V → V → Prop) : List V → V → V → Prop
  | [], a, b => a = b
  | c :: l, a, b => Rl a c ∧ ChainsTo Rl l c b
private theorem chainsTo_of_append {Rl : V → V → Prop} {x b : V} {t : List V} :
    ∀ (s : List V) (a : V), ChainsTo Rl (s ++ x :: t) a b → ChainsTo Rl t x b
  | [], _, h => h.2
  | _ :: s, _, h => chainsTo_of_append s _ h.2
private theorem exists_nodup_chainsTo {Rl : V → V → Prop} {a b : V} (h : Relation.ReflTransGen Rl a b) :
    ∃ l : List V, (a :: l).Nodup ∧ ChainsTo Rl l a b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], by simp, rfl⟩
  | @head a c hac _ ih =>
    obtain ⟨l, hnd, hl⟩ := ih
    by_cases hmem : a ∈ c :: l
    · rcases List.mem_cons.mp hmem with rfl | hal
      · exact ⟨l, hnd, hl⟩
      · obtain ⟨s, t, rfl⟩ := List.append_of_mem hal
        refine ⟨t, ?_, chainsTo_of_append s c hl⟩
        have : (s ++ a :: t).Nodup := (List.nodup_cons.mp hnd).2
        exact (List.sublist_append_right s (a :: t)).nodup this
    · exact ⟨c :: l, List.nodup_cons.mpr ⟨hmem, hnd⟩, hac, hl⟩
private theorem forall_mem_of_chainsTo {Rl : V → V → Prop} {P : V → Prop} (hP : ∀ x y, Rl x y → P y) {b : V} :
    ∀ (l : List V) (a : V), P a → ChainsTo Rl l a b → ∀ c ∈ a :: l, P c
  | [], _, ha, _ => by simpa using ha
  | d :: l, a, ha, h => by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ha
      · exact forall_mem_of_chainsTo hP l d (hP _ _ h.1) h.2 c hc
private def walks [DecidableEq V] (nb : V → Finset V) : ℕ → V → Finset (List V)
  | 0, _ => {[]}
  | t + 1, a => (nb a).biUnion fun c => (walks nb t c).image (c :: ·)
private theorem card_walks_le [DecidableEq V] {nb : V → Finset V} {D : ℕ} (hD : ∀ a, (nb a).card ≤ D) :
    ∀ (t : ℕ) (a : V), (walks nb t a).card ≤ D ^ t
  | 0, a => by simp [walks]
  | t + 1, a => by
      rw [walks, pow_succ']
      refine (Finset.card_biUnion_le_card_mul _ _ (D ^ t) fun c _ => ?_).trans ?_
      · exact Finset.card_image_le.trans (card_walks_le hD t c)
      · exact Nat.mul_le_mul_right _ (hD a)
private theorem take_mem_walks [DecidableEq V] {nb : V → Finset V} {Rl : V → V → Prop}
    (hnb : ∀ x y, Rl x y → y ∈ nb x) {b : V} :
    ∀ (t : ℕ) (l : List V) (a : V), ChainsTo Rl l a b → t ≤ l.length → l.take t ∈ walks nb t a
  | 0, l, a, _, _ => by simp [walks]
  | t + 1, [], a, _, h => by simp at h
  | t + 1, c :: l, a, h, hl => by
      simp only [List.take_succ_cons, walks, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨c, hnb _ _ h.1, l.take t, take_mem_walks hnb t l c h.2 (by simpa using hl), rfl⟩
end Lists
private abbrev ShiftedCell : Type := Finset (Fin 4) × (Fin 4 → ℤ)
private theorem exists_grid_sixteenth {p : List ShiftedCell} (hnd : p.Nodup) :
    ∃ (A : Finset (Fin 4)) (S : Finset (Fin 4 → ℤ)), p.length ≤ 16 * S.card ∧ ∀ κ ∈ S, (A, κ) ∈ p := by
  have hcard : p.toFinset.card = p.length := List.toFinset_card_of_nodup hnd
  have hsum : p.toFinset.card = ∑ A : Finset (Fin 4), (p.toFinset.filter fun c => c.1 = A).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  obtain ⟨A, hA⟩ : ∃ A : Finset (Fin 4), p.length ≤ 16 * (p.toFinset.filter fun c => c.1 = A).card := by
    by_contra hc
    push Not at hc
    have hlt : ∑ A : Finset (Fin 4), 16 * (p.toFinset.filter fun c => c.1 = A).card <
        ∑ _A : Finset (Fin 4), p.length :=
      Finset.sum_lt_sum_of_nonempty ⟨∅, Finset.mem_univ _⟩ fun A _ => hc A
    rw [← Finset.mul_sum, ← hsum, hcard, Finset.sum_const] at hlt
    simp at hlt
  refine ⟨A, (p.toFinset.filter fun c => c.1 = A).image Prod.snd, ?_, ?_⟩
  · rwa [Finset.card_image_of_injOn]
    intro c hc d hd hcd
    have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hd)).2
    exact Prod.ext (h1.trans h2.symm) hcd
  · intro κ hκ
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hκ
    obtain ⟨hcF, rfl⟩ := Finset.mem_filter.mp hc
    exact List.mem_toFinset.mp hcF
section Cells
variable {n : ℕ} [NeZero n]
private theorem supDist_le_side_of_mem_cell (G : CellGrid) {κ : Fin 4 → ℤ} {x y : TorusSite n}
    (hx : x ∈ G.cell n κ) (hy : y ∈ G.cell n κ) : _root_.YangMills.Construction.TorusFields.supDist x y ≤ G.side := by
  simp only [CellGrid.cell, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  obtain ⟨h, hh, rfl⟩ := hx
  obtain ⟨h', hh', rfl⟩ := hy
  rw [_root_.YangMills.Construction.TorusFields.supDist_le_iff]
  intro i
  have e : ((siteOfInt fun i => G.offset i + (G.side : ℤ) * κ i + h i : TorusSite n) i
      - (siteOfInt fun i => G.offset i + (G.side : ℤ) * κ i + h' i : TorusSite n) i)
      = ((h i - h' i : ℤ) : ZMod n) := by
    simp only [siteOfInt]
    push_cast
    ring
  rw [e]
  refine (_root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le _).trans ?_
  have := hh i
  have := hh' i
  omega
private def adjacentCells (Nc : ℕ) (c : ShiftedCell) : Finset ShiftedCell :=
  (Finset.univ : Finset (Finset (Fin 4))).biUnion fun A =>
    (Fintype.piFinset fun _ : Fin 4 => ({-1, 0, 1} : Finset ℤ)).image fun δ =>
      (A, fun i => (c.2 i + δ i) % (Nc : ℤ))
private theorem card_adjacentCells_le (Nc : ℕ) (c : ShiftedCell) : (adjacentCells Nc c).card ≤ 1296 := by
  refine (Finset.card_biUnion_le_card_mul _ _ 81 fun A _ => ?_).trans ?_
  · refine Finset.card_image_le.trans ?_
    simp [Fintype.card_piFinset]
  · simp
private theorem exists_adjacent_index {s N w κ κ' t : ℤ} (hs : 0 < s) (hκ0 : 0 ≤ κ') (hκ1 : κ' < N)
    (ht1 : -(2 * s) < t) (ht2 : t < 2 * s) (h : s * (κ' - κ - N * w) = t) :
    ∃ δ ∈ ({-1, 0, 1} : Finset ℤ), κ' = (κ + δ) % N := by
  have h1 : κ' - κ - N * w ≤ 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have h2 : -1 ≤ κ' - κ - N * w := by
    by_contra hc
    push Not at hc
    nlinarith
  refine ⟨κ' - κ - N * w, ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · have e : κ + (κ' - κ - N * w) = κ' + N * (-w) := by ring
    rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hκ0 hκ1]
private theorem shift_offset_eq (G : CellGrid) (hs : 0 < G.side) (A : Finset (Fin 4)) (i : Fin 4) :
    ∃ e : ℤ, (G.shift A).offset i = G.offset i + e ∧ 0 ≤ e ∧ 2 * e ≤ (G.side : ℤ) := by
  by_cases h : i ∈ A
  · exact ⟨((G.side : ℤ) - 1) / 2, by simp [CellGrid.shift, h], by omega, by omega⟩
  · exact ⟨0, by simp [CellGrid.shift, h], le_rfl, by omega⟩
private theorem mem_adjacentCells_of_common_site (G : CellGrid) {Nc : ℕ} (hs : 0 < G.side) (hn : n = G.side * Nc)
    {c c' : ShiftedCell} (hc' : c'.2 ∈ (G.shift c'.1).indices n) {x : TorusSite n}
    (hx : x ∈ (G.shift c.1).cell n c.2) (hx' : x ∈ (G.shift c'.1).cell n c'.2) :
    c' ∈ adjacentCells Nc c := by
  have hdiv : n / G.side = Nc := by
    rw [hn]
    exact Nat.mul_div_cancel_left _ hs
  have hnz : (n : ℤ) = (G.side : ℤ) * (Nc : ℤ) := by exact_mod_cast hn
  have key : ∀ i, ∃ δ ∈ ({-1, 0, 1} : Finset ℤ), c'.2 i = (c.2 i + δ) % (Nc : ℤ) := by
    intro i
    simp only [CellGrid.cell, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    obtain ⟨h, hh, e⟩ := hx
    obtain ⟨h', hh', e'⟩ := hx'
    have eq : (((G.shift c.1).offset i + ((G.shift c.1).side : ℤ) * c.2 i + h i : ℤ) : ZMod n) =
        (((G.shift c'.1).offset i + ((G.shift c'.1).side : ℤ) * c'.2 i + h' i : ℤ) : ZMod n) :=
      congrFun (e.symm.trans e') i
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at eq
    obtain ⟨w, hw⟩ := eq
    obtain ⟨a, ha, ha0, ha1⟩ := shift_offset_eq G hs c.1 i
    obtain ⟨a', ha', ha0', ha1'⟩ := shift_offset_eq G hs c'.1 i
    have hside : ∀ A, (G.shift A).side = G.side := fun _ => rfl
    rw [ha, ha', hside, hside] at hw
    have hκ := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hc' i)
    rw [hside, hdiv] at hκ
    have hb := hh i
    have hb' := hh' i
    rw [hside] at hb hb'
    refine exists_adjacent_index (s := (G.side : ℤ)) (w := w) (t := (a - a') + (h i - h' i))
      (by exact_mod_cast hs) hκ.1 hκ.2 (by omega) (by omega) ?_
    linear_combination hw + w * hnz
  choose δ hδ hδe using key
  refine Finset.mem_biUnion.mpr ⟨c'.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨δ, ?_, ?_⟩⟩
  · exact Fintype.mem_piFinset.mpr hδ
  · exact Prod.ext rfl (funext fun i => (hδe i).symm)
private def IsOccupied (G : CellGrid) (r : ℕ) (Y : Finset (TorusSite n)) (c : ShiftedCell) : Prop :=
  c.2 ∈ (G.shift c.1).indices n ∧ (Y ∩ interiorAtDepth (8 * r) ((G.shift c.1).cell n c.2)).Nonempty
private def IsCellAssignment (G : CellGrid) (r : ℕ) (f : TorusSite n → ShiftedCell) : Prop :=
  ∀ x, (f x).2 ∈ (G.shift (f x).1).indices n ∧ x ∈ interiorAtDepth (8 * r) ((G.shift (f x).1).cell n (f x).2)
private def AdjacentOccupied (G : CellGrid) (r : ℕ) (Y : Finset (TorusSite n)) (c c' : ShiftedCell) : Prop :=
  IsOccupied G r Y c ∧ IsOccupied G r Y c' ∧ ∃ w, w ∈ (G.shift c.1).cell n c.2 ∧ w ∈ (G.shift c'.1).cell n c'.2
private theorem supDist_le_of_chainsTo (G : CellGrid) {r : ℕ} {Y : Finset (TorusSite n)} {b : ShiftedCell} {y : TorusSite n}
    (hy : y ∈ (G.shift b.1).cell n b.2) :
    ∀ (l : List ShiftedCell) (a : ShiftedCell) (x : TorusSite n), x ∈ (G.shift a.1).cell n a.2 →
      ChainsTo (AdjacentOccupied G r Y) l a b → _root_.YangMills.Construction.TorusFields.supDist x y ≤ (l.length + 1) * G.side
  | [], a, x, hx, h => by
      subst h
      have h0 : _root_.YangMills.Construction.TorusFields.supDist x y ≤ G.side := supDist_le_side_of_mem_cell (G.shift a.1) hx hy
      simpa using h0
  | d :: l, a, x, hx, h => by
      obtain ⟨w, hw, hw'⟩ := h.1.2.2
      have h1 : _root_.YangMills.Construction.TorusFields.supDist x w ≤ G.side := supDist_le_side_of_mem_cell (G.shift a.1) hx hw
      have h2 := supDist_le_of_chainsTo G hy l d w hw' h.2
      have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle x w y
      simp only [List.length_cons]
      nlinarith
private theorem exists_occupied_walk (G : CellGrid) {Nc r : ℕ} (hs : 0 < G.side) (hn : n = G.side * Nc) (hr : 0 < r)
    {f : TorusSite n → ShiftedCell} (hf : IsCellAssignment G r f) {Y : Finset (TorusSite n)} {X : Finset (TorusSite n)}
    (hX : X ∈ chainComponents r Y) {z : TorusSite n} (hz : z ∈ X) {m : ℕ} (hm : m < siteDiameter X) :
    ∃ l ∈ walks (adjacentCells Nc) (m / (2 * G.side)) (f z), (f z :: l).Nodup ∧
      ∀ c ∈ f z :: l, IsOccupied G r Y c := by
  obtain ⟨v, hv, hmv⟩ : ∃ v ∈ X, m < 2 * _root_.YangMills.Construction.TorusFields.supDist z v := by
    unfold siteDiameter at hm
    obtain ⟨a, ha, hm⟩ := Finset.lt_sup_iff.mp hm
    obtain ⟨b, hb, hm⟩ := Finset.lt_sup_iff.mp hm
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle a z b
    rw [_root_.YangMills.Construction.TorusFields.supDist_comm a z] at h3
    by_cases h : m < 2 * _root_.YangMills.Construction.TorusFields.supDist z a
    · exact ⟨a, ha, h⟩
    · exact ⟨b, hb, by omega⟩
  have hzY : z ∈ Y := subset_of_mem_chainComponents hX hz
  have occOf : ∀ q, q ∈ Y → IsOccupied G r Y (f q) := fun q hq =>
    ⟨(hf q).1, q, Finset.mem_inter.mpr ⟨hq, (hf q).2⟩⟩
  have lift : ∀ q, ChainConnected r Y z q → Relation.ReflTransGen (AdjacentOccupied G r Y) (f z) (f q) := by
    intro q hq
    induction hq with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      refine ih.tail ⟨occOf b hbc.1, occOf c hbc.2.1, c, ?_, ?_⟩
      · have hb := Finset.mem_filter.mp (hf b).2
        by_contra hc
        have := hb.2 c hc
        have := hbc.2.2
        omega
      · exact (Finset.mem_filter.mp (hf c).2).1
  obtain ⟨l, hnd, hl⟩ := exists_nodup_chainsTo (lift v (chainConnected_of_mem_chainComponents hX hz hv))
  have hocc : ∀ c ∈ f z :: l, IsOccupied G r Y c :=
    forall_mem_of_chainsTo (fun _ _ h => h.2.1) l (f z) (occOf z hzY) hl
  have hw : _root_.YangMills.Construction.TorusFields.supDist z v ≤ (l.length + 1) * G.side :=
    supDist_le_of_chainsTo G (Finset.mem_filter.mp (hf v).2).1 l (f z) z (Finset.mem_filter.mp (hf z).2).1 hl
  have hlen : m / (2 * G.side) ≤ l.length := by
    have : m / (2 * G.side) < l.length + 1 := by
      apply Nat.div_lt_of_lt_mul
      nlinarith
    omega
  refine ⟨l.take (m / (2 * G.side)), ?_, ?_, ?_⟩
  · refine take_mem_walks (Rl := AdjacentOccupied G r Y) (fun x y h => ?_) _ l _ hl hlen
    obtain ⟨w, hw, hw'⟩ := h.2.2
    exact mem_adjacentCells_of_common_site G hs hn h.2.1.1 hw hw'
  · exact ((List.take_sublist _ l).cons_cons _).nodup hnd
  · intro c hc
    exact hocc c (((List.take_sublist _ l).cons_cons _).subset hc)
private theorem length_of_mem_walks {V : Type*} [DecidableEq V] {nb : V → Finset V} :
    ∀ (t : ℕ) (a : V) (l : List V), l ∈ walks nb t a → l.length = t
  | 0, a, l, h => by simpa [walks] using h
  | t + 1, a, l, h => by
      simp only [walks, Finset.mem_biUnion, Finset.mem_image] at h
      obtain ⟨c, _, l', hl', rfl⟩ := h
      simpa using length_of_mem_walks t c l' hl'
private theorem measure_large_component_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (G : CellGrid) {Nc r : ℕ}
    (hs : 0 < G.side) (hn : n = G.side * Nc) (hr : 0 < r) {f : TorusSite n → ShiftedCell} (hf : IsCellAssignment G r f)
    (Y : Ω → Finset (TorusSite n)) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hcell : ∀ (A : Finset (Fin 4)) (S : Finset (Fin 4 → ℤ)), S ⊆ (G.shift A).indices n →
      μ {u | ∀ κ ∈ S, (Y u ∩ interiorAtDepth (8 * r) ((G.shift A).cell n κ)).Nonempty} ≤
        ENNReal.ofReal (ε ^ S.card))
    (B : Finset (TorusSite n)) (m : ℕ) :
    μ {u | ∃ X ∈ chainComponents r (Y u), (∃ z ∈ X, z ∈ B) ∧ m < siteDiameter X} ≤
      ((B.card * 1296 ^ (m / (2 * G.side)) : ℕ) : ENNReal) *
        ENNReal.ofReal (ε ^ ((m / (2 * G.side) + 16) / 16)) := by
  classical
  set t := m / (2 * G.side) with ht
  set q := (t + 16) / 16 with hq
  let Pat : TorusSite n → Finset (List ShiftedCell) := fun a =>
    (walks (adjacentCells Nc) t (f a)).filter fun l =>
      (f a :: l).Nodup ∧ ∀ c ∈ f a :: l, c.2 ∈ (G.shift c.1).indices n
  let E : TorusSite n → List ShiftedCell → Set Ω := fun a l => {u | ∀ c ∈ f a :: l, IsOccupied G r (Y u) c}
  have sub : {u | ∃ X ∈ chainComponents r (Y u), (∃ z ∈ X, z ∈ B) ∧ m < siteDiameter X} ⊆
      ⋃ a ∈ B, ⋃ l ∈ Pat a, E a l := by
    rintro u ⟨X, hX, ⟨z, hz, hzB⟩, hm⟩
    obtain ⟨l, hl, hnd, hocc⟩ := exists_occupied_walk G hs hn hr hf hX hz hm
    simp only [Set.mem_iUnion]
    exact ⟨z, hzB, l, Finset.mem_filter.mpr ⟨hl, hnd, fun c hc => (hocc c hc).1⟩, hocc⟩
  have each : ∀ a, ∀ l ∈ Pat a, μ (E a l) ≤ ENNReal.ofReal (ε ^ q) := by
    intro a l hl
    obtain ⟨hw, hnd, hidx⟩ := Finset.mem_filter.mp hl
    obtain ⟨A, S, hS, hmem⟩ := exists_grid_sixteenth hnd
    have hlen : (f a :: l).length = t + 1 := by
      simp [length_of_mem_walks t _ l hw]
    have hqS : q ≤ S.card := by omega
    have hsub : S ⊆ (G.shift A).indices n := fun κ hκ => hidx _ (hmem κ hκ)
    have hmono : E a l ⊆ {u | ∀ κ ∈ S, (Y u ∩ interiorAtDepth (8 * r) ((G.shift A).cell n κ)).Nonempty} :=
      fun u hu κ hκ => (hu _ (hmem κ hκ)).2
    exact (measure_mono hmono).trans ((hcell A S hsub).trans
      (ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one h0 h1 hqS)))
  calc μ {u | ∃ X ∈ chainComponents r (Y u), (∃ z ∈ X, z ∈ B) ∧ m < siteDiameter X}
      ≤ μ (⋃ a ∈ B, ⋃ l ∈ Pat a, E a l) := measure_mono sub
    _ ≤ ∑ a ∈ B, μ (⋃ l ∈ Pat a, E a l) := measure_biUnion_finset_le _ _
    _ ≤ ∑ a ∈ B, ∑ l ∈ Pat a, μ (E a l) :=
        Finset.sum_le_sum fun a _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ B, ((1296 ^ t : ℕ) : ENNReal) * ENNReal.ofReal (ε ^ q) := by
        refine Finset.sum_le_sum fun a _ => ?_
        refine (Finset.sum_le_card_nsmul _ _ _ (each a)).trans ?_
        rw [nsmul_eq_mul]
        gcongr
        exact (Finset.card_filter_le _ _).trans (card_walks_le (card_adjacentCells_le Nc) t _)
    _ = ((B.card * 1296 ^ t : ℕ) : ENNReal) * ENNReal.ofReal (ε ^ q) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
end Cells
private theorem entropy_le_energy {a : ℝ} (ha : 2 ^ 15 ≤ a) (m : ℕ) {s : ℕ} (hs : 0 < s) :
    (1296 : ℝ) ^ (m / (2 * s)) * Real.exp (-a) ^ ((m / (2 * s) + 16) / 16) ≤
      Real.exp (-a) ^ ((m : ℝ) / (320 * s)) := by
  set t := m / (2 * s) with ht
  set q := (t + 16) / 16 with hq
  have hmt : m < 2 * s * (t + 1) := Nat.lt_mul_div_succ m (by omega)
  have htq : t + 1 ≤ 16 * q := by omega
  have hmt' : (m : ℝ) ≤ 2 * s * (t + 1) := by exact_mod_cast hmt.le
  have htq' : (t : ℝ) + 1 ≤ 16 * q := by exact_mod_cast htq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : (1296 : ℝ) ≤ Real.exp 1296 := by
    have := Real.add_one_le_exp (1296 : ℝ)
    linarith
  have h2 : (1296 : ℝ) ^ t ≤ Real.exp (t * 1296) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) h1 t
  rw [← Real.exp_nat_mul, ← Real.exp_mul]
  calc (1296 : ℝ) ^ t * Real.exp (q * -a)
      ≤ Real.exp (t * 1296) * Real.exp (q * -a) := by gcongr
    _ = Real.exp (t * 1296 + q * -a) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr ?_
  have hy : (m : ℝ) / (320 * s) ≤ q / 10 := by
    rw [div_le_iff₀ (by positivity)]
    have : 2 * (s : ℝ) * (t + 1) ≤ 2 * s * (16 * q) :=
      mul_le_mul_of_nonneg_left htq' (by positivity)
    linarith
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have h3 : a * ((m : ℝ) / (320 * s)) ≤ a * (q / 10) := mul_le_mul_of_nonneg_left hy ha0.le
  have h4 : (2 : ℝ) ^ 15 * q ≤ a * q := mul_le_mul_of_nonneg_right ha hq0
  norm_num at h4
  nlinarith
theorem longHullsRare_of_cellEventsRare (h₁ : cellEventsRareStatement) (h₂ : shiftedGridsCoverTorusStatement) :
    longHullsRareStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, hrt, H⟩ := h₁ a ha
  refine ⟨L₀, rt₀, hrt, fun L hL hL₀ Tb hTa hTL hD hle => ?_⟩
  obtain ⟨y₀, hy₀⟩ := H L hL hL₀ Tb hTa hTL hD hle
  have hσ := hD.σ_pos
  have hκ₁ : 0 < Tb.κ₁ :=
    lt_min (div_pos hD.κ_pos (by norm_num)) (div_pos hD.cE_pos (by positivity))
  have hκσ : 0 < Tb.κ₁ * Tb.threshold ^ 2 := by positivity
  refine ⟨max y₀ (max 1 (2 ^ 20 / (Tb.κ₁ * Tb.threshold ^ 2))), fun y hy hExp hWil => ?_⟩
  have cell := hy₀ y ((le_max_left _ _).trans hy) hExp hWil
  have hy1 : (1 : ℝ) ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy2 : 2 ^ 20 / (Tb.κ₁ * Tb.threshold ^ 2) ≤ y :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  intro R hR
  refine ⟨(((2 * ⌈R + 1⌉₊ + 1) ^ 4 : ℕ) : ℝ), fun T β k hOn e hside y₁ m hm => ?_⟩
  have hL1 : 1 < (Tb.stepParameters y).side := by
    have : 2 ^ 40 ≤ (Tb.stepParameters y).side := hD.L_ge
    omega
  have hLodd : Odd (Tb.stepParameters y).side := hD.L_odd
  have hx : y ≤ (T.stage k).coupling := (hOn.onFamily.onFamily k le_rfl).le_coupling
  have hx0 : 0 < (T.stage k).coupling := by linarith
  have hr : 0 < stageRange T k := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hx0 _)
  obtain ⟨G, hG⟩ : ∃ G : CellGrid, G.side = baseCellSide (Tb.stepParameters y).side (stageRange T k) := ⟨⟨_, 0⟩, rfl⟩
  have hsd : G.side = (Tb.stepParameters y).side ^ Nat.clog (Tb.stepParameters y).side (2 ^ 7 * stageRange T k) := hG
  have hs : 0 < G.side := by
    rw [hsd]
    exact pow_pos (by omega) _
  have hce : Nat.clog (Tb.stepParameters y).side (2 ^ 7 * stageRange T k) ≤ e := by
    rw [← Nat.pow_le_pow_iff_right hL1, ← hsd, hG]
    omega
  have hn : 2 * (Tb.stepParameters y).side ^ e =
      G.side * (2 * (Tb.stepParameters y).side ^ (e - Nat.clog (Tb.stepParameters y).side (2 ^ 7 * stageRange T k))) := by
    rw [hsd, mul_left_comm, ← pow_add, Nat.add_sub_cancel' hce]
  have hfits : G.Compatible (2 * (Tb.stepParameters y).side ^ e) :=
    ⟨hs, by rw [hsd]; exact Nat.mul_dvd_mul_left 2 (pow_dvd_pow _ hce)⟩
  have hodd : Odd G.side := by
    rw [hsd]
    exact hLodd.pow
  have hr7 : 2 ^ 7 * stageRange T k ≤ G.side := by
    rw [hsd]
    exact Nat.le_pow_clog hL1 _
  have hex := fun x => h₂ (2 * (Tb.stepParameters y).side ^ e) (stageRange T k) G hfits hodd hr7 x
  choose fA fκ hfκ hfx using hex
  have hf : IsCellAssignment G (stageRange T k) fun x => (fA x, fκ x) := fun x => ⟨hfκ x, hfx x⟩
  have hcell : ∀ (A : Finset (Fin 4)) (S : Finset (Fin 4 → ℤ)),
      S ⊆ (G.shift A).indices (2 * (Tb.stepParameters y).side ^ e) →
      markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ e) {u | ∀ κ ∈ S,
        (stageHull T k _ u ∩ interiorAtDepth (8 * stageRange T k)
          ((G.shift A).cell (2 * (Tb.stepParameters y).side ^ e) κ)).Nonempty} ≤
        ENNReal.ofReal (cellEventBound Tb (T.stage k).coupling ^ S.card) := fun A S hS =>
    (cell T β k hOn e (G.shift A) S hG (by show 2 * G.side ≤ _; rw [hG]; exact hside) hS).2.2.1
  have ha15 : (2 : ℝ) ^ 15 ≤ (T.stage k).coupling * Tb.κ₁ * Tb.threshold ^ 2 / 2 ^ 5 := by
    have h20 : (2 : ℝ) ^ 20 ≤ (T.stage k).coupling * (Tb.κ₁ * Tb.threshold ^ 2) :=
      (div_le_iff₀ hκσ).mp (hy2.trans hx)
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hε : cellEventBound Tb (T.stage k).coupling =
      Real.exp (-((T.stage k).coupling * Tb.κ₁ * Tb.threshold ^ 2 / 2 ^ 5)) := rfl
  have hε0 : 0 ≤ cellEventBound Tb (T.stage k).coupling := (Real.exp_pos _).le
  have hε1 : cellEventBound Tb (T.stage k).coupling ≤ 1 := by
    rw [hε, Real.exp_le_one_iff]
    have : (0 : ℝ) < 2 ^ 15 := by norm_num
    linarith
  have sub : {u | m < maxDiameterNearBox T k _ u y₁ R} ⊆
      {u | ∃ X ∈ chainComponents (stageRange T k) (stageHull T k (2 * (Tb.stepParameters y).side ^ e) u),
        (∃ z ∈ X, z ∈ thickening ⌈R + 1⌉₊ {y₁}) ∧ m < siteDiameter X} := by
    intro u hu
    have hu' : m < (componentsNearBox T k _ u y₁ R).sup siteDiameter := hu
    obtain ⟨X, hX, hmX⟩ := Finset.lt_sup_iff.mp hu'
    obtain ⟨hXc, z, hz, w, hw, hzw⟩ := Finset.mem_filter.mp hX
    refine ⟨X, hXc, ⟨z, hz, ?_⟩, hmX⟩
    simp only [thickening, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨y₁, rfl, ?_⟩
    have h3 := _root_.YangMills.Construction.TorusFields.supDist_triangle z w y₁
    have h4 : (_root_.YangMills.Construction.TorusFields.supDist z y₁ : ℝ) ≤ ⌈R + 1⌉₊ := by
      have h5 : (_root_.YangMills.Construction.TorusFields.supDist z y₁ : ℝ) ≤ _root_.YangMills.Construction.TorusFields.supDist z w + _root_.YangMills.Construction.TorusFields.supDist w y₁ := by exact_mod_cast h3
      have h6 : (_root_.YangMills.Construction.TorusFields.supDist z w : ℝ) ≤ 1 := by exact_mod_cast hzw
      exact (by linarith : (supDist z y₁ : ℝ) ≤ R + 1).trans (Nat.le_ceil _)
    exact_mod_cast h4
  refine (measure_mono sub).trans ((measure_large_component_le _ G hs hn hr hf _ hε0 hε1 hcell _ m).trans ?_)
  have hcard : (thickening ⌈R + 1⌉₊ {y₁}).card ≤ (2 * ⌈R + 1⌉₊ + 1) ^ 4 := card_thickening_singleton_le _ _
  have hcard' : ((thickening ⌈R + 1⌉₊ {y₁}).card : ℝ) ≤ (((2 * ⌈R + 1⌉₊ + 1) ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hpay := entropy_le_energy ha15 m hs
  rw [← hε, hG] at hpay
  rw [hG, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]
  have hpos : 0 ≤ (1296 : ℝ) ^ (m / (2 * baseCellSide (Tb.stepParameters y).side (stageRange T k))) *
      cellEventBound Tb (T.stage k).coupling ^ ((m / (2 * baseCellSide (Tb.stepParameters y).side (stageRange T k)) + 16) / 16) := by
    positivity
  exact (mul_le_mul_of_nonneg_right hcard' hpos).trans (mul_le_mul_of_nonneg_left hpay (Nat.cast_nonneg _))
end LongHullsRare
end YangMills.Construction.CellWindows
end
