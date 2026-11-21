import YangMills.Construction.HoleBesideASecondHole.ComponentsOfLumps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Holes
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
namespace LinkComponentFacts
variable {F : BlockFrame} {h : Finset (Finset (F.Site F.depth))}
theorem supDist_comm {j : ℕ} (x y : F.Site j) : supDist x y = supDist y x := by
  unfold supDist
  congr 1
  funext i
  rw [← neg_sub, ZMod.natAbs_valMinAbs_neg]
theorem areWithin_symm {j r : ℕ} {X Y : Finset (F.Site j)} (w : AreWithin r X Y) : AreWithin r Y X := by
  obtain ⟨x, hx, y, hy, d⟩ := w
  exact ⟨y, hy, x, hx, by rwa [supDist_comm]⟩
theorem areWithin_mono {j r r' : ℕ} {X Y : Finset (F.Site j)} (hr : r ≤ r') (w : AreWithin r X Y) :
    AreWithin r' X Y := by
  obtain ⟨x, hx, y, hy, d⟩ := w
  exact ⟨x, hx, y, hy, d.trans hr⟩
theorem lumpsLinked_symm {r : ℕ} : Symmetric (LumpsLinked r h) :=
  fun _ _ w => ⟨w.2.1, w.1, areWithin_symm w.2.2⟩
theorem mem_linkComponent {r : ℕ} {l l' : Finset (F.Site F.depth)} :
    l' ∈ linkComponent r h l ↔ l' ∈ h ∧ Relation.ReflTransGen (LumpsLinked r h) l l' := by
  classical
  simp [linkComponent]
theorem self_mem_linkComponent (r : ℕ) {l : Finset (F.Site F.depth)} (hl : l ∈ h) :
    l ∈ linkComponent r h l :=
  mem_linkComponent.2 ⟨hl, Relation.ReflTransGen.refl⟩
theorem reflTransGen_lumpsLinked_symm {r : ℕ} {a b : Finset (F.Site F.depth)}
    (hab : Relation.ReflTransGen (LumpsLinked r h) a b) :
    Relation.ReflTransGen (LumpsLinked r h) b a := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (lumpsLinked_symm hbc) ih
theorem linkComponent_eq_of_mem {r : ℕ} {l l' : Finset (F.Site F.depth)}
    (hm : l' ∈ linkComponent r h l) : linkComponent r h l' = linkComponent r h l := by
  obtain ⟨_, hr⟩ := mem_linkComponent.1 hm
  ext x
  simp only [mem_linkComponent]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨a, hr.trans b⟩
  · rintro ⟨a, b⟩
    exact ⟨a, (reflTransGen_lumpsLinked_symm hr).trans b⟩
theorem reflTransGen_lumpsLinked_mono {r r' : ℕ} (hr : r ≤ r') {a b : Finset (F.Site F.depth)}
    (hab : Relation.ReflTransGen (LumpsLinked r h) a b) :
    Relation.ReflTransGen (LumpsLinked r' h) a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hbc.1, hbc.2.1, areWithin_mono hr hbc.2.2⟩
theorem linkComponent_mono {r r' : ℕ} (hr : r ≤ r') (l : Finset (F.Site F.depth)) :
    linkComponent r h l ⊆ linkComponent r' h l := by
  intro x hx
  obtain ⟨a, b⟩ := mem_linkComponent.1 hx
  exact mem_linkComponent.2 ⟨a, reflTransGen_lumpsLinked_mono hr b⟩
theorem linkComponent_subset (r : ℕ) (l : Finset (F.Site F.depth)) : linkComponent r h l ⊆ h :=
  fun _ hx => (mem_linkComponent.1 hx).1
theorem exists_eq_linkComponent_of_mem {r : ℕ} {k : Finset (Finset (F.Site F.depth))}
    (hk : k ∈ linkComponents r h) : ∃ l ∈ h, k = linkComponent r h l := by
  classical
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hk
  exact ⟨l, hl, rfl⟩
theorem componentsWithin_eq_image {r r' : ℕ} {k : Finset (Finset (F.Site F.depth))} (hr : r ≤ r')
    (hk : k ∈ linkComponents r' h) : componentsWithin r h k = k.image (linkComponent r h) := by
  classical
  obtain ⟨l₀, hl₀, rfl⟩ := exists_eq_linkComponent_of_mem hk
  ext x
  simp only [componentsWithin, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hx, hs⟩
    obtain ⟨l, hl, rfl⟩ := exists_eq_linkComponent_of_mem hx
    exact ⟨l, hs (self_mem_linkComponent r hl), rfl⟩
  · rintro ⟨l, hl, rfl⟩
    have hlh := linkComponent_subset r' l₀ hl
    refine ⟨Finset.mem_image_of_mem _ hlh, ?_⟩
    rw [← linkComponent_eq_of_mem hl]
    exact linkComponent_mono hr l
theorem holeScale_mono (J₀ : ℕ) (hJ : 1 ≤ J₀) {i j : ℕ} (hij : i ≤ j) :
    holeScale J₀ i ≤ holeScale J₀ j := by
  unfold holeScale
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hij)
def coarsen (r' : ℕ) (h : Finset (Finset (F.Site F.depth))) (A : Finset (Finset (F.Site F.depth))) :
    Finset (Finset (F.Site F.depth)) := by
  classical exact A.biUnion (linkComponent r' h)
theorem coarsen_linkComponent {r r' : ℕ} (hr : r ≤ r') {l : Finset (F.Site F.depth)} (hl : l ∈ h) :
    coarsen r' h (linkComponent r h l) = linkComponent r' h l := by
  classical
  ext x
  simp only [coarsen, Finset.mem_biUnion]
  constructor
  · rintro ⟨l', hl', hx⟩
    have := linkComponent_eq_of_mem (linkComponent_mono hr l hl')
    rwa [this] at hx
  · intro hx
    exact ⟨l, self_mem_linkComponent r hl, hx⟩
theorem card_componentsWithin_step {r r' R : ℕ} (hr : r ≤ r') (hR : r' ≤ R)
    {k : Finset (Finset (F.Site F.depth))} (hk : k ∈ linkComponents R h) :
    (componentsWithin r' h k).card ≤ (componentsWithin r h k).card ∧
      (componentsWithin r h k ≠ componentsWithin r' h k →
        (componentsWithin r' h k).card + 1 ≤ (componentsWithin r h k).card) := by
  classical
  have hkh : k ⊆ h := by
    obtain ⟨l₀, _, rfl⟩ := exists_eq_linkComponent_of_mem hk
    exact linkComponent_subset R l₀
  have e1 := componentsWithin_eq_image (r := r) (hr.trans hR) hk
  have e2 := componentsWithin_eq_image (r := r') hR hk
  have e3 : componentsWithin r' h k = (componentsWithin r h k).image (coarsen r' h) := by
    rw [e1, e2, Finset.image_image]
    refine Finset.image_congr fun l hl => ?_
    exact (coarsen_linkComponent hr (hkh hl)).symm
  refine ⟨by rw [e3]; exact Finset.card_image_le, fun hne => ?_⟩
  by_contra hcon
  have hle : (componentsWithin r' h k).card ≤ (componentsWithin r h k).card := by
    rw [e3]
    exact Finset.card_image_le
  have heq : ((componentsWithin r h k).image (coarsen r' h)).card = (componentsWithin r h k).card := by
    rw [← e3]
    omega
  have hinj := Finset.card_image_iff.1 heq
  apply hne
  rw [e1, e2]
  refine Finset.image_congr fun l hl => ?_
  have hlh := hkh hl
  refine Finset.Subset.antisymm (linkComponent_mono hr l) fun x hx => ?_
  have hxk : x ∈ k := by
    obtain ⟨l₀, _, rfl⟩ := exists_eq_linkComponent_of_mem hk
    have a : linkComponent R h l = linkComponent R h l₀ := linkComponent_eq_of_mem hl
    rw [← a]
    exact linkComponent_mono hR l hx
  have hxh := hkh hxk
  have m1 : linkComponent r h l ∈ (componentsWithin r h k : Set _) := by
    rw [e1]
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hl)
  have m2 : linkComponent r h x ∈ (componentsWithin r h k : Set _) := by
    rw [e1]
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hxk)
  have e4 : coarsen r' h (linkComponent r h x) = coarsen r' h (linkComponent r h l) := by
    rw [coarsen_linkComponent hr hxh, coarsen_linkComponent hr hlh, linkComponent_eq_of_mem hx]
  have e5 := hinj m2 m1 e4
  rw [← e5]
  exact self_mem_linkComponent r hxh
open Classical in
theorem succ_le_card_stable_add_card (J₀ I : ℕ) (hJ : 1 ≤ J₀) (k : Finset (Finset (F.Site F.depth)))
    (hk : k ∈ linkComponents (holeScale J₀ I) h) :
    I + 1 ≤ ((Finset.range I).filter (IsStableIndex J₀ h k)).card + k.card := by
  classical
  have hkh : k ⊆ h := by
    obtain ⟨l₀, _, rfl⟩ := exists_eq_linkComponent_of_mem hk
    exact linkComponent_subset _ l₀
  have hne : k.Nonempty := by
    obtain ⟨l₀, hl₀, rfl⟩ := exists_eq_linkComponent_of_mem hk
    exact ⟨l₀, self_mem_linkComponent _ hl₀⟩
  have ind : ∀ n ≤ I, (componentsWithin (holeScale J₀ n) h k).card +
      ((Finset.range n).filter fun i => ¬ IsStableIndex J₀ h k i).card ≤
        (componentsWithin (holeScale J₀ 0) h k).card := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have hs := card_componentsWithin_step (holeScale_mono J₀ hJ (show n ≤ n + 1 by omega))
        (holeScale_mono J₀ hJ hn) hk
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hf : IsStableIndex J₀ h k n
      · rw [if_neg (by simpa using hf)]
        have := hs.1
        omega
      · rw [if_pos hf, Finset.card_insert_of_notMem (by simp)]
        have := hs.2 hf
        omega
  have h0 := ind I le_rfl
  have hc0 : (componentsWithin (holeScale J₀ 0) h k).card ≤ k.card := by
    rw [componentsWithin_eq_image (holeScale_mono J₀ hJ (Nat.zero_le I)) hk]
    exact Finset.card_image_le
  have hcI : 1 ≤ (componentsWithin (holeScale J₀ I) h k).card := by
    rw [componentsWithin_eq_image le_rfl hk]
    exact Finset.card_pos.2 (hne.image _)
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range I) (IsStableIndex J₀ h k)
  rw [Finset.card_range] at hsplit
  omega
end LinkComponentFacts
open LinkComponentFacts in
theorem linkComponentProperties_holds : LinkComponentProperties := by
  intro F h
  exact ⟨fun r l hl => self_mem_linkComponent r hl, fun r l l' hm => linkComponent_eq_of_mem hm,
    fun r r' l hr => linkComponent_mono hr l, fun r r' k hr hk => componentsWithin_eq_image hr hk,
    fun J₀ I k hJ hk => succ_le_card_stable_add_card J₀ I hJ k hk⟩
end YangMills.Construction.Holes
end
