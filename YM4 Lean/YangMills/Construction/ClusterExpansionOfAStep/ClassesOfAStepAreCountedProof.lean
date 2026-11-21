import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfAStepAreCounted
import YangMills.Construction.ClusterExpansionOfAStep.ClassesOfTheGas
import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClassProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterCounting
open TorusFields TorusLumps
section Walks
variable {V : Type} [DecidableEq V] (nb : V → Finset V)
def IsWalk : V → List V → Prop
  | _, [] => True
  | x, v :: l => v ∈ nb x ∧ IsWalk v l
def walks : ℕ → V → Finset (List V)
  | 0, _ => {[]}
  | k + 1, x => (nb x).biUnion fun v => (walks k v).image (v :: ·)
theorem card_walks_le (Δ : ℕ) (h : ∀ v, (nb v).card ≤ Δ) (k : ℕ) (x : V) :
    (walks nb k x).card ≤ Δ ^ k := by
  induction k generalizing x with
  | zero => simp [walks]
  | succ k ih =>
    simp only [walks]
    calc _ ≤ ∑ v ∈ nb x, ((walks nb k v).image (v :: ·)).card := Finset.card_biUnion_le
      _ ≤ ∑ v ∈ nb x, Δ ^ k := Finset.sum_le_sum fun v _ => Finset.card_image_le.trans (ih v)
      _ = (nb x).card * Δ ^ k := by simp
      _ ≤ Δ * Δ ^ k := Nat.mul_le_mul_right _ (h x)
      _ = Δ ^ (k + 1) := by ring
theorem mem_walks {k : ℕ} {x : V} {l : List V} (h : IsWalk nb x l) (hl : l.length = k) :
    l ∈ walks nb k x := by
  induction l generalizing k x with
  | nil =>
    subst hl
    simp [walks]
  | cons v l ih =>
    obtain ⟨hv, hw⟩ := h
    cases k with
    | zero => simp at hl
    | succ k =>
      simp only [walks, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨v, hv, l, ih hw (by simpa using hl), rfl⟩
theorem length_of_mem_walks {k : ℕ} {x : V} {l : List V} (h : l ∈ walks nb k x) :
    l.length = k := by
  induction k generalizing x l with
  | zero =>
    simp only [walks, Finset.mem_singleton] at h
    simp [h]
  | succ k ih =>
    simp only [walks, Finset.mem_biUnion, Finset.mem_image] at h
    obtain ⟨v, _, l', hl', rfl⟩ := h
    simp [ih hl']
variable {nb}
theorem exists_walk_extend (hsym : ∀ a b, b ∈ nb a → a ∈ nb b) {u v : V} (hv : v ∈ nb u) (l : List V) (x : V)
    (hw : IsWalk nb x l) (hu : u ∈ x :: l) :
    ∃ l', IsWalk nb x l' ∧ l'.length = l.length + 2 ∧ ∀ z, z ∈ x :: l' ↔ z = v ∨ z ∈ x :: l := by
  induction l generalizing x with
  | nil =>
    have : u = x := by simpa using hu
    subst this
    refine ⟨[v, u], ⟨hv, hsym _ _ hv, trivial⟩, rfl, fun z => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto
  | cons w l ih =>
    by_cases hux : u = x
    · subst hux
      refine ⟨v :: u :: w :: l, ⟨hv, hsym _ _ hv, hw⟩, by simp, fun z => ?_⟩
      simp only [List.mem_cons]
      tauto
    · have hu' : u ∈ w :: l := by
        rcases List.mem_cons.mp hu with h | h
        · exact absurd h hux
        · exact h
      obtain ⟨l', hl', hlen, hz⟩ := ih w hw.2 hu'
      refine ⟨w :: l', ⟨hw.1, hl'⟩, by simp [hlen], fun z => ?_⟩
      have := hz z
      simp only [List.mem_cons] at this ⊢
      tauto
def StepWithin (nb : V → Finset V) (S : Finset V) (a b : V) : Prop := a ∈ S ∧ b ∈ S ∧ b ∈ nb a
theorem exists_step_out_of {S A : Finset V} {a y : V} (ha : a ∈ A) (hy : y ∉ A)
    (h : Relation.ReflTransGen (StepWithin nb S) a y) : ∃ u ∈ A, ∃ v, v ∉ A ∧ StepWithin nb S u v := by
  induction h with
  | refl => exact absurd ha hy
  | @tail b c _ hbc ih =>
    by_cases hb : b ∈ A
    · exact ⟨b, hb, c, hy, hbc⟩
    · exact ih hb
theorem exists_walk_pad (hrefl : ∀ a, a ∈ nb a) (x : V) (l : List V) (hw : IsWalk nb x l) (j : ℕ) :
    ∃ l', IsWalk nb x l' ∧ l'.length = l.length + j ∧ ∀ z, z ∈ x :: l' ↔ z ∈ x :: l := by
  induction j with
  | zero => exact ⟨l, hw, rfl, fun _ => Iff.rfl⟩
  | succ j ih =>
    obtain ⟨l', hl', hlen, hz⟩ := ih
    refine ⟨x :: l', ⟨hrefl x, hl'⟩, by simp [hlen]; omega, fun z => ?_⟩
    have := hz z
    simp only [List.mem_cons] at this ⊢
    tauto
theorem exists_walk_covering (hrefl : ∀ a, a ∈ nb a) (hsym : ∀ a b, b ∈ nb a → a ∈ nb b) {x : V} {S : Finset V}
    (hx : x ∈ S) (hc : ∀ y ∈ S, Relation.ReflTransGen (StepWithin nb S) x y) {m : ℕ} (hm : S.card ≤ m + 1) :
    ∃ l, IsWalk nb x l ∧ l.length = 2 * m ∧ ∀ z, z ∈ x :: l ↔ z ∈ S := by
  have key : ∀ k, k + 1 ≤ S.card → ∃ (A : Finset V) (l : List V), A ⊆ S ∧ A.card = k + 1 ∧
      IsWalk nb x l ∧ l.length = 2 * k ∧ ∀ z, z ∈ x :: l ↔ z ∈ A := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨{x}, [], by simpa using hx, by simp, trivial, rfl, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨A, l, hAS, hAc, hw, hlen, hz⟩ := ih (by omega)
      obtain ⟨y, hyS, hyA⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := A) (t := S) (by omega)
      have hxA : x ∈ A := (hz x).1 (by simp)
      obtain ⟨u, huA, v, hvA, _, hvS, hv⟩ := exists_step_out_of hxA hyA (hc y hyS)
      obtain ⟨l', hl', hlen', hz'⟩ := exists_walk_extend hsym hv l x hw ((hz u).2 huA)
      refine ⟨insert v A, l', ?_, ?_, hl', by omega, fun z => ?_⟩
      · intro z hz2
        rcases Finset.mem_insert.mp hz2 with rfl | h
        · exact hvS
        · exact hAS h
      · rw [Finset.card_insert_of_notMem hvA, hAc]
      · rw [hz' z, Finset.mem_insert, hz z]
  have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨x, hx⟩
  obtain ⟨A, l, hAS, hAc, hw, hlen, hz⟩ := key (S.card - 1) (by omega)
  have hAeq : A = S := Finset.eq_of_subset_of_card_le hAS (by omega)
  subst hAeq
  obtain ⟨l', hl', hlen', hz'⟩ := exists_walk_pad hrefl x l hw (2 * m - 2 * (A.card - 1))
  exact ⟨l', hl', by omega, fun z => (hz' z).trans (hz z)⟩
end Walks
section Balls
variable {N : ℕ} [NeZero N]
theorem card_thickening_singleton_le (m : ℕ) (x : TorusSite N) : (thickening m {x}).card ≤ (2 * m + 1) ^ 4 := by apply _root_.YangMills.Construction.TorusBalls.card_thickening_singleton_le <;> assumption
theorem card_thickening_le (m : ℕ) (C : Finset (TorusSite N)) :
    (thickening m C).card ≤ C.card * (2 * m + 1) ^ 4 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ClassNeighbourhood.card_thickening_le <;> assumption
theorem supDist_le_of_mem_walk {D : ℕ} {x : TorusSite N} {l : List (TorusSite N)}
    (hw : IsWalk (fun v => thickening D {v}) x l)
    {z : TorusSite N} (hz : z ∈ x :: l) : _root_.YangMills.Construction.TorusFields.supDist x z ≤ l.length * D := by
  induction l generalizing x with
  | nil =>
    have : z = x := by simpa using hz
    subst this
    simp [_root_.YangMills.Construction.TorusFields.supDist_self]
  | cons v l ih =>
    rcases List.mem_cons.mp hz with rfl | h
    · simp [_root_.YangMills.Construction.TorusFields.supDist_self]
    · obtain ⟨hv, hw'⟩ := hw
      have h1 := ih hw' h
      obtain ⟨c, hc, hd⟩ := (mem_thickening D {x} v).1 hv
      obtain rfl : c = x := by simpa using hc
      have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle c v z
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm c v] at h2
      simp only [List.length_cons]
      nlinarith
end Balls
section Blocks
variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]
theorem supDist_le_of_parentBlock_eq {x y : TorusSite (n * L)} (h : parentBlock L x = parentBlock L y) :
    _root_.YangMills.Construction.TorusFields.supDist x y ≤ L := by apply _root_.YangMills.Construction.TorusLumps.supDist_le_of_parentBlock_eq <;> assumption
theorem supDist_parentBlock_le (x y : TorusSite (n * L)) :
    _root_.YangMills.Construction.TorusFields.supDist (parentBlock L x) (parentBlock L y) ≤ _root_.YangMills.Construction.TorusFields.supDist x y / L + 1 := by apply _root_.YangMills.Construction.TorusBalls.supDist_parentBlock_le_div_add_one <;> assumption
end Blocks
section Clusters
variable {n : ℕ} [NeZero n] {L : ℕ} [NeZero L]
theorem exists_cover_centres (r : ℕ) (hL : L ≤ 4 * r) (θ : ClusterSupport L n) :
    ∃ C : Finset (TorusSite (n * L)), C.card ≤ supportUnitCount L r θ ∧
      clusterSupportSites L θ ⊆ thickening (4 * r) C ∧
      ∀ c ∈ C, ∃ s ∈ clusterSupportSites L θ, _root_.YangMills.Construction.TorusFields.supDist c s ≤ 4 * r := by
  classical
  have hne : {k | ∃ C : Finset (TorusSite (n * L)), C.card = k ∧ θ.2 ⊆ thickening (4 * r) C}.Nonempty :=
    ⟨_, θ.2, rfl, fun z hz => (mem_thickening _ _ _).2 ⟨z, hz, by simp [_root_.YangMills.Construction.TorusFields.supDist_self]⟩⟩
  obtain ⟨C₁, hC₁, hcov⟩ := Nat.sInf_mem hne
  let rep : TorusSite n → TorusSite (n * L) := fun β =>
    if h : ∃ b ∈ θ.1, parentBlock L b.1 = β then h.choose.1 else 0
  have hrep : ∀ b ∈ θ.1, parentBlock L (rep (parentBlock L b.1)) = parentBlock L b.1 := by
    intro b hb
    have h : ∃ b' ∈ θ.1, parentBlock L b'.1 = parentBlock L b.1 := ⟨b, hb, rfl⟩
    simp only [rep, dif_pos h]
    exact h.choose_spec.2
  let C₂ : Finset (TorusSite (n * L)) := (θ.1.image fun b => parentBlock L b.1).image rep
  refine ⟨(C₁ ∪ C₂).filter fun c => ∃ s ∈ clusterSupportSites L θ, _root_.YangMills.Construction.TorusFields.supDist c s ≤ 4 * r, ?_, ?_, ?_⟩
  · calc _ ≤ (C₁ ∪ C₂).card := Finset.card_filter_le _ _
      _ ≤ C₁.card + C₂.card := Finset.card_union_le _ _
      _ ≤ ballCoverNumber (4 * r) θ.2 + badBlockCount L θ := by
          refine Nat.add_le_add (le_of_eq hC₁) Finset.card_image_le
      _ = supportUnitCount L r θ := by simp [supportUnitCount, add_comm]
  · intro z hz
    have key : ∃ c ∈ C₁ ∪ C₂, _root_.YangMills.Construction.TorusFields.supDist z c ≤ 4 * r := by
      rcases Finset.mem_union.mp hz with h | h
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
        refine ⟨rep (parentBlock L b.1), Finset.mem_union_right _ ?_, ?_⟩
        · exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hb)
        · exact (_root_.YangMills.Construction.ClusterCounting.supDist_le_of_parentBlock_eq (hrep b hb).symm).trans hL
      · obtain ⟨c, hc, hd⟩ := (mem_thickening _ _ _).1 (hcov h)
        exact ⟨c, Finset.mem_union_left _ hc, hd⟩
    obtain ⟨c, hc, hd⟩ := key
    refine (mem_thickening _ _ _).2 ⟨c, Finset.mem_filter.mpr ⟨hc, z, hz, ?_⟩, hd⟩
    rwa [_root_.YangMills.Construction.TorusFields.supDist_comm]
  · intro c hc
    exact (Finset.mem_filter.mp hc).2
def supBall {N : ℕ} [NeZero N] (D : ℕ) (v : TorusSite N) : Finset (TorusSite N) := thickening D {v}
theorem mem_supBall {N : ℕ} [NeZero N] {D : ℕ} {v z : TorusSite N} : z ∈ supBall D v ↔ _root_.YangMills.Construction.TorusFields.supDist z v ≤ D := by
  simp [supBall, mem_thickening]
theorem exists_site_of_mem_supportCore {r : ℕ} {θ : ClusterSupport L n} {y : TorusSite n}
    (hy : y ∈ supportCore L r θ) :
    ∃ x, parentBlock L x = y ∧ x ∈ thickening (4 * r) (clusterSupportSites L θ) := by
  classical
  have h1 := (Finset.mem_filter.mp hy).2
  obtain ⟨x, hx⟩ := h1
  obtain ⟨hb, hw⟩ := Finset.mem_inter.mp hx
  have := (Finset.mem_filter.mp hb).2
  exact ⟨x, by simpa using this, hw⟩
theorem cluster_walk_data {r : ℕ} (hL : L ≤ r) (hL' : 88 ≤ L) {θ : ClusterSupport L n} {Y : TorusSite n}
    {x₀ : TorusSite (n * L)} (hx₀ : parentBlock L x₀ = Y) (hθ : IsClusterSupport L r θ)
    (hY : Y ∈ supportCore L r θ) :
    1 ≤ supportUnitCount L r θ ∧
    (∃ l, IsWalk (supBall (18 * r)) x₀ l ∧ l.length = 2 * supportUnitCount L r θ ∧
      clusterSupportSites L θ ⊆ thickening (4 * r) (insert x₀ l.toFinset)) ∧
    (supportCore L r θ).card ≤ supportUnitCount L r θ * (16 * r + 1) ^ 4 ∧
    siteDiameter (supportCore L r θ) ≤ r * supportUnitCount L r θ + 1 := by
  classical
  obtain ⟨C, hCc, hcov, hC⟩ := exists_cover_centres r (by omega) θ
  set u := supportUnitCount L r θ with hu
  have hu1 : 1 ≤ u := by
    obtain ⟨s, hs⟩ := hθ.1
    obtain ⟨c, hc, _⟩ := (mem_thickening _ _ _).1 (hcov hs)
    exact (Finset.card_pos.mpr ⟨c, hc⟩).trans_le hCc
  obtain ⟨x, hxY, hxw⟩ := exists_site_of_mem_supportCore hY
  obtain ⟨s₀, hs₀, hxs⟩ := (mem_thickening _ _ _).1 hxw
  have hx₀x : _root_.YangMills.Construction.TorusFields.supDist x₀ x ≤ r := (_root_.YangMills.Construction.ClusterCounting.supDist_le_of_parentBlock_eq (hx₀.trans hxY.symm)).trans hL
  set S := insert x₀ C with hS
  have hxS : x₀ ∈ S := Finset.mem_insert_self _ _
  have hCS : ∀ c ∈ C, c ∈ S := fun c hc => Finset.mem_insert_of_mem hc
  have hstep : ∀ s ∈ clusterSupportSites L θ, ChainConnected (10 * r) (clusterSupportSites L θ) s₀ s →
      ∀ c ∈ C, _root_.YangMills.Construction.TorusFields.supDist s c ≤ 4 * r → Relation.ReflTransGen (StepWithin (supBall (18 * r)) S) x₀ c := by
    intro s hs hj
    induction hj with
    | refl =>
      intro c hc hd
      refine Relation.ReflTransGen.single ⟨hxS, hCS c hc, mem_supBall.2 ?_⟩
      have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle c s₀ x₀
      have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle s₀ x x₀
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm c s₀] at h1
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm s₀ x, _root_.YangMills.Construction.TorusFields.supDist_comm x x₀] at h2
      omega
    | @tail b z hb hbz ih =>
      intro c hc hd
      obtain ⟨hbs, hzs, hbzd⟩ := hbz
      obtain ⟨c', hc', hd'⟩ := (mem_thickening _ _ _).1 (hcov hbs)
      refine (ih hbs c' hc' hd').tail ⟨hCS c' hc', hCS c hc, mem_supBall.2 ?_⟩
      have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle c z c'
      have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle z b c'
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm c z] at h1
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm z b] at h2
      omega
  have hconn : ∀ y ∈ S, Relation.ReflTransGen (StepWithin (supBall (18 * r)) S) x₀ y := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Relation.ReflTransGen.refl
    · obtain ⟨s, hs, hd⟩ := hC y hy
      exact hstep s hs (hθ.2 _ hs₀ _ hs) y hy (by rwa [_root_.YangMills.Construction.TorusFields.supDist_comm])
  have hSc : S.card ≤ u + 1 := (Finset.card_insert_le _ _).trans (by omega)
  obtain ⟨l, hw, hlen, hz⟩ := exists_walk_covering (nb := supBall (18 * r))
    (fun a => mem_supBall.2 (by simp [_root_.YangMills.Construction.TorusFields.supDist_self]))
    (fun a b h => mem_supBall.2 (by rw [_root_.YangMills.Construction.TorusFields.supDist_comm]; exact mem_supBall.1 h)) hxS hconn hSc
  have hdist : ∀ c ∈ C, _root_.YangMills.Construction.TorusFields.supDist x₀ c ≤ 2 * u * (18 * r) := by
    intro c hc
    have := _root_.YangMills.Construction.ClusterCounting.supDist_le_of_mem_walk (D := 18 * r) (x := x₀) (l := l) hw ((hz c).2 (hCS c hc))
    rwa [hlen] at this
  refine ⟨hu1, ⟨l, hw, hlen, ?_⟩, ?_, ?_⟩
  · intro z' hz'
    obtain ⟨c, hc, hd⟩ := (mem_thickening _ _ _).1 (hcov hz')
    refine (mem_thickening _ _ _).2 ⟨c, ?_, hd⟩
    have := (hz c).2 (hCS c hc)
    simpa using this
  · have hsub : supportCore L r θ ⊆ (thickening (8 * r) C).image (parentBlock L) := by
      intro y hy
      obtain ⟨x', hx', hw'⟩ := exists_site_of_mem_supportCore hy
      obtain ⟨s, hs, hd⟩ := (mem_thickening _ _ _).1 hw'
      obtain ⟨c, hc, hd'⟩ := (mem_thickening _ _ _).1 (hcov hs)
      refine Finset.mem_image.mpr ⟨x', (mem_thickening _ _ _).2 ⟨c, hc, ?_⟩, hx'⟩
      have := _root_.YangMills.Construction.TorusFields.supDist_triangle x' s c
      omega
    calc _ ≤ ((thickening (8 * r) C).image (parentBlock L)).card := Finset.card_le_card hsub
      _ ≤ (thickening (8 * r) C).card := Finset.card_image_le
      _ ≤ C.card * (2 * (8 * r) + 1) ^ 4 := card_thickening_le _ _
      _ ≤ u * (16 * r + 1) ^ 4 := by
          have : 2 * (8 * r) + 1 = 16 * r + 1 := by ring
          rw [this]
          exact Nat.mul_le_mul_right _ hCc
  · have hfar : ∀ y ∈ supportCore L r θ, ∃ x', parentBlock L x' = y ∧
        _root_.YangMills.Construction.TorusFields.supDist x₀ x' ≤ 2 * u * (18 * r) + 8 * r := by
      intro y hy
      obtain ⟨x', hx', hw'⟩ := exists_site_of_mem_supportCore hy
      obtain ⟨s, hs, hd⟩ := (mem_thickening _ _ _).1 hw'
      obtain ⟨c, hc, hd'⟩ := (mem_thickening _ _ _).1 (hcov hs)
      refine ⟨x', hx', ?_⟩
      have h1 := _root_.YangMills.Construction.TorusFields.supDist_triangle x₀ c x'
      have h2 := _root_.YangMills.Construction.TorusFields.supDist_triangle x' s c
      have h3 := hdist c hc
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm c x'] at h1
      omega
    refine Finset.sup_le fun y hy => Finset.sup_le fun y' hy' => ?_
    obtain ⟨x₁, rfl, h₁⟩ := hfar y hy
    obtain ⟨x₂, rfl, h₂⟩ := hfar y' hy'
    refine (_root_.YangMills.Construction.ClusterCounting.supDist_parentBlock_le x₁ x₂).trans ?_
    have h3 : _root_.YangMills.Construction.TorusFields.supDist x₁ x₂ ≤ 88 * (r * u) := by
      have h4 := _root_.YangMills.Construction.TorusFields.supDist_triangle x₁ x₀ x₂
      rw [_root_.YangMills.Construction.TorusFields.supDist_comm x₁ x₀] at h4
      have h5 : r ≤ r * u := Nat.le_mul_of_pos_right _ hu1
      nlinarith
    have h6 : _root_.YangMills.Construction.TorusFields.supDist x₁ x₂ / L ≤ r * u := by
      apply Nat.div_le_of_le_mul
      exact h3.trans (Nat.mul_le_mul_right _ hL')
    omega
open Classical in
def supportPairs (Nn : Finset (TorusSite (n * L))) : Finset (ClusterSupport L n) :=
  (Nn ×ˢ (Finset.univ : Finset (Fin 4))).powerset ×ˢ Nn.powerset
omit [NeZero n] [NeZero L] in
theorem card_supportPairs (Nn : Finset (TorusSite (n * L))) :
    (supportPairs (n := n) (L := L) Nn).card = 2 ^ (5 * Nn.card) := by
  classical
  simp only [supportPairs, Finset.card_product, Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  rw [← pow_add]
  congr 1
  ring
open Classical in
def walkFamily (x₀ : TorusSite (n * L)) (r u : ℕ) : Finset (ClusterSupport L n) :=
  (walks (supBall (18 * r)) (2 * u) x₀).biUnion fun l =>
    supportPairs (thickening (4 * r) (insert x₀ l.toFinset))
theorem card_walkFamily_le (x₀ : TorusSite (n * L)) (r u : ℕ) :
    (walkFamily x₀ r u).card ≤ ((2 * (18 * r) + 1) ^ 4) ^ (2 * u) *
      2 ^ (5 * ((2 * u + 1) * (2 * (4 * r) + 1) ^ 4)) := by
  classical
  refine (Finset.card_biUnion_le_card_mul _ _ _ fun l hl => ?_).trans
    (Nat.mul_le_mul_right _ (card_walks_le _ _ (fun v => card_thickening_singleton_le _ v) _ _))
  rw [card_supportPairs]
  refine Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ ?_)
  refine (card_thickening_le _ _).trans (Nat.mul_le_mul_right _ ?_)
  have h1 := length_of_mem_walks _ hl
  calc _ ≤ l.toFinset.card + 1 := Finset.card_insert_le _ _
    _ ≤ l.length + 1 := Nat.add_le_add_right (List.toFinset_card_le _) _
    _ = 2 * u + 1 := by rw [h1]
theorem mem_walkFamily {r : ℕ} (hL : L ≤ r) (hL' : 88 ≤ L) {θ : ClusterSupport L n} {Y : TorusSite n}
    {x₀ : TorusSite (n * L)} (hx₀ : parentBlock L x₀ = Y) (hθ : IsClusterSupport L r θ)
    (hY : Y ∈ supportCore L r θ) : θ ∈ walkFamily x₀ r (supportUnitCount L r θ) := by
  classical
  obtain ⟨_, ⟨l, hw, hlen, hsub⟩, _, _⟩ := cluster_walk_data hL hL' hx₀ hθ hY
  refine Finset.mem_biUnion.mpr ⟨l, mem_walks _ hw hlen, ?_⟩
  refine Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.mem_powerset.mpr ?_⟩
  · intro b hb
    refine Finset.mem_product.mpr ⟨hsub ?_, Finset.mem_univ _⟩
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb)
  · intro z hz
    exact hsub (Finset.mem_union_right _ hz)
end Clusters
section Numbers
theorem walk_count_mul_weight_le (c x rt : ℝ) (r u : ℕ) (hr : 1 ≤ r) (hrt : 0 < rt) (hu : 1 ≤ u)
    (hfl : (2 ^ 16 + 2 ^ 7 * rt) * (r : ℝ) ^ 4 ≤ c * x) :
    ((((2 * (18 * r) + 1) ^ 4) ^ (2 * u) * 2 ^ (5 * ((2 * u + 1) * (2 * (4 * r) + 1) ^ 4)) : ℕ) : ℝ) *
        (Real.exp (-(16 * c * x * (u : ℝ))) * ((u * (16 * r + 1) ^ 4 : ℕ) : ℝ) ^ 4 *
          Real.exp (2 * rt * ((r * u + 1 : ℕ) : ℝ))) ≤ Real.exp (-(14 * c * x * (u : ℝ))) := by
  have hR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hT : (1 : ℝ) ≤ u := by exact_mod_cast hu
  set R : ℝ := (r : ℝ) with hRdef
  set T : ℝ := (u : ℝ) with hTdef
  have a1 : ((2 * (18 * R) + 1) ^ 4) ^ (2 * u) ≤ Real.exp (288 * R * T) := by
    have h1 : 2 * (18 * R) + 1 ≤ Real.exp (36 * R) := by
      have := Real.add_one_le_exp (36 * R)
      linarith
    calc ((2 * (18 * R) + 1) ^ 4) ^ (2 * u) = (2 * (18 * R) + 1) ^ (4 * (2 * u)) := (pow_mul _ _ _).symm
      _ ≤ Real.exp (36 * R) ^ (4 * (2 * u)) := pow_le_pow_left₀ (by positivity) h1 _
      _ = Real.exp (((4 * (2 * u) : ℕ) : ℝ) * (36 * R)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (288 * R * T) := by
          congr 1
          push_cast
          ring
  have a2 : (2 : ℝ) ^ (5 * ((2 * u + 1) * (2 * (4 * r) + 1) ^ 4)) ≤
      Real.exp (5 * ((2 * T + 1) * (2 * (4 * R) + 1) ^ 4)) := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    calc (2 : ℝ) ^ (5 * ((2 * u + 1) * (2 * (4 * r) + 1) ^ 4))
        ≤ Real.exp 1 ^ (5 * ((2 * u + 1) * (2 * (4 * r) + 1) ^ 4)) := pow_le_pow_left₀ (by norm_num) h1 _
      _ = Real.exp (((5 * ((2 * u + 1) * (2 * (4 * r) + 1) ^ 4) : ℕ) : ℝ) * 1) := (Real.exp_nat_mul _ _).symm
      _ = _ := by
          congr 1
          push_cast
          ring
  have a3 : (T * (16 * R + 1) ^ 4) ^ 4 ≤ Real.exp (4 * T + 256 * R) := by
    have h1 : 16 * R + 1 ≤ Real.exp (16 * R) := by
      have := Real.add_one_le_exp (16 * R)
      linarith
    have h2 : T ≤ Real.exp T := by
      have := Real.add_one_le_exp T
      linarith
    have h3 : (16 * R + 1) ^ 4 ≤ Real.exp (64 * R) := by
      calc (16 * R + 1) ^ 4 ≤ Real.exp (16 * R) ^ 4 := pow_le_pow_left₀ (by positivity) h1 _
        _ = Real.exp (((4 : ℕ) : ℝ) * (16 * R)) := (Real.exp_nat_mul _ _).symm
        _ = _ := by
            congr 1
            push_cast
            ring
    calc (T * (16 * R + 1) ^ 4) ^ 4 ≤ (Real.exp T * Real.exp (64 * R)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul h2 h3 (by positivity) (Real.exp_pos _).le) _
      _ = Real.exp (((4 : ℕ) : ℝ) * (T + 64 * R)) := by
          rw [← Real.exp_add, Real.exp_nat_mul]
      _ = _ := by
          congr 1
          push_cast
          ring
  have hcast1 : ((((2 * (18 * r) + 1) ^ 4) ^ (2 * u) * 2 ^ (5 * ((2 * u + 1) * (2 * (4 * r) + 1) ^ 4)) : ℕ) : ℝ) =
      ((2 * (18 * R) + 1) ^ 4) ^ (2 * u) * (2 : ℝ) ^ (5 * ((2 * u + 1) * (2 * (4 * r) + 1) ^ 4)) := by
    push_cast
    rfl
  have hcast2 : ((u * (16 * r + 1) ^ 4 : ℕ) : ℝ) = T * (16 * R + 1) ^ 4 := by
    push_cast
    rfl
  have hcast3 : ((r * u + 1 : ℕ) : ℝ) = R * T + 1 := by
    push_cast
    rfl
  rw [hcast1, hcast2, hcast3]
  have hprod : ((2 * (18 * R) + 1) ^ 4) ^ (2 * u) * (2 : ℝ) ^ (5 * ((2 * u + 1) * (2 * (4 * r) + 1) ^ 4)) *
        (Real.exp (-(16 * c * x * T)) * (T * (16 * R + 1) ^ 4) ^ 4 * Real.exp (2 * rt * (R * T + 1))) ≤
      Real.exp (288 * R * T) * Real.exp (5 * ((2 * T + 1) * (2 * (4 * R) + 1) ^ 4)) *
        (Real.exp (-(16 * c * x * T)) * Real.exp (4 * T + 256 * R) * Real.exp (2 * rt * (R * T + 1))) := by
    gcongr
  refine hprod.trans ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hR4 : R ≤ R ^ 4 := by
    calc R = R ^ 1 := (pow_one R).symm
      _ ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  have hB : (2 * (4 * R) + 1) ^ 4 ≤ 6561 * R ^ 4 := by
    calc (2 * (4 * R) + 1) ^ 4 ≤ (9 * R) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = 6561 * R ^ 4 := by ring
  have hTR : T * R ≤ T * R ^ 4 := mul_le_mul_of_nonneg_left hR4 (by linarith)
  have hT4 : T ≤ T * R ^ 4 := by nlinarith
  have hR4T : R ≤ T * R ^ 4 := by nlinarith
  have e1 : 5 * ((2 * T + 1) * (2 * (4 * R) + 1) ^ 4) ≤ 15 * T * (6561 * R ^ 4) := by
    have h1 : 5 * (2 * T + 1) ≤ 15 * T := by linarith
    calc 5 * ((2 * T + 1) * (2 * (4 * R) + 1) ^ 4) = 5 * (2 * T + 1) * (2 * (4 * R) + 1) ^ 4 := by ring
      _ ≤ 15 * T * (6561 * R ^ 4) := mul_le_mul h1 hB (by positivity) (by positivity)
  have e2 : 2 * rt * (R * T + 1) ≤ 4 * rt * (T * R ^ 4) := by
    have h1 : R * T + 1 ≤ 2 * (T * R ^ 4) := by nlinarith
    nlinarith
  have e3 : T * ((2 ^ 16 + 2 ^ 7 * rt) * R ^ 4) ≤ T * (c * x) :=
    mul_le_mul_of_nonneg_left hfl (by linarith)
  have hTR' : 0 ≤ rt * (T * R ^ 4) := by positivity
  nlinarith
theorem sum_geometric_succ_le (q : ℝ) (h0 : 0 ≤ q) (h1 : 2 * q ≤ 1) (U : ℕ) :
    ∑ v ∈ Finset.range U, q ^ (v + 1) ≤ 2 * q := by
  have key : ∑ v ∈ Finset.range U, q ^ (v + 1) ≤ 2 * q - 2 * q ^ (U + 1) := by
    induction U with
    | zero => simp
    | succ U ih =>
      rw [Finset.sum_range_succ]
      have h2 : 2 * q ^ (U + 1 + 1) ≤ q ^ (U + 1) := by
        rw [pow_succ q (U + 1)]
        have : 0 ≤ q ^ (U + 1) := by positivity
        nlinarith
      linarith
  have : 0 ≤ q ^ (U + 1) := by positivity
  linarith
end Numbers
theorem clusterSumBound_holds : ClusterSumBound := by
  intro ℓ c hfit hc hfl x hx n _ Y
  classical
  obtain ⟨hLr, hnum⟩ := hfl x hx
  set r := clusterRange x with hrdef
  have hL16 : 2 ^ 16 ≤ ℓ.side := hfit.L_ge
  have hL' : 88 ≤ ℓ.side := by
    norm_num at hL16
    omega
  have hr1 : 1 ≤ r := by omega
  have hR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrt := hfit.rt_pos
  have hcx : 1 ≤ c * x := by
    have h1 : (1 : ℝ) ≤ (r : ℝ) ^ 4 := one_le_pow₀ hR
    have h2 : 0 ≤ 2 ^ 7 * ℓ.rt := by positivity
    nlinarith
  rcases (supportsAtBlock ℓ.side r Y).eq_empty_or_nonempty with hemp | ⟨θ₀, hθ₀⟩
  · rw [hemp]
    simp only [Finset.sum_empty]
    exact (Real.exp_pos _).le
  have hmem : ∀ θ ∈ supportsAtBlock ℓ.side r Y, IsClusterSupport ℓ.side r θ ∧ Y ∈ supportCore ℓ.side r θ :=
    fun θ hθ => (Finset.mem_filter.mp hθ).2
  obtain ⟨x₀, hx₀, _⟩ := exists_site_of_mem_supportCore (hmem θ₀ hθ₀).2
  set q := Real.exp (-(14 * c * x)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hbig : ∀ a : ℝ, 1 ≤ a → 2 * Real.exp (-a) ≤ 1 := by
    intro a ha
    have h1 := Real.add_one_le_exp a
    have h2 : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos (-a)
    nlinarith
  have hq1 : 2 * q ≤ 1 := by
    have := hbig (14 * (c * x)) (by linarith)
    have he : -(14 * c * x) = -(14 * (c * x)) := by ring
    rw [hq, he]
    exact this
  have hmaps : ∀ θ ∈ supportsAtBlock ℓ.side r Y, supportUnitCount ℓ.side r θ - 1 ∈
      Finset.range ((supportsAtBlock ℓ.side r Y).sup (fun θ => supportUnitCount ℓ.side r θ - 1) + 1) := by
    intro θ hθ
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Finset.le_sup (f := fun θ => supportUnitCount ℓ.side r θ - 1) hθ))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have inner : ∀ v : ℕ, ∑ θ ∈ (supportsAtBlock ℓ.side r Y).filter (fun θ => supportUnitCount ℓ.side r θ - 1 = v),
      clusterWeight ℓ.side c x r θ * ((supportCore ℓ.side r θ).card : ℝ) ^ 4 *
        Real.exp (2 * ℓ.rt * (siteDiameter (supportCore ℓ.side r θ) : ℝ)) ≤ q ^ (v + 1) := by
    intro v
    set b : ℝ := Real.exp (-(16 * c * x * ((v + 1 : ℕ) : ℝ))) *
      (((v + 1) * (16 * r + 1) ^ 4 : ℕ) : ℝ) ^ 4 *
      Real.exp (2 * ℓ.rt * ((r * (v + 1) + 1 : ℕ) : ℝ)) with hb
    have hb0 : 0 ≤ b := by positivity
    have hone : ∀ θ ∈ (supportsAtBlock ℓ.side r Y).filter (fun θ => supportUnitCount ℓ.side r θ - 1 = v),
        supportUnitCount ℓ.side r θ = v + 1 ∧ θ ∈ walkFamily x₀ r (v + 1) ∧
        clusterWeight ℓ.side c x r θ * ((supportCore ℓ.side r θ).card : ℝ) ^ 4 *
          Real.exp (2 * ℓ.rt * (siteDiameter (supportCore ℓ.side r θ) : ℝ)) ≤ b := by
      intro θ hθ
      obtain ⟨hθX, hv⟩ := Finset.mem_filter.mp hθ
      obtain ⟨hcl, hY⟩ := hmem θ hθX
      obtain ⟨h1, _, hcard, hdiam⟩ := cluster_walk_data hLr hL' hx₀ hcl hY
      have hu : supportUnitCount ℓ.side r θ = v + 1 := by omega
      have hfam := mem_walkFamily hLr hL' hx₀ hcl hY
      rw [hu] at hcard hdiam hfam
      refine ⟨hu, hfam, ?_⟩
      have hw : clusterWeight ℓ.side c x r θ = Real.exp (-(16 * c * x * ((v + 1 : ℕ) : ℝ))) := by
        simp only [clusterWeight, hu]
      rw [hw, hb]
      have c1 : ((supportCore ℓ.side r θ).card : ℝ) ≤ (((v + 1) * (16 * r + 1) ^ 4 : ℕ) : ℝ) := by
        exact_mod_cast hcard
      have c2 : (siteDiameter (supportCore ℓ.side r θ) : ℝ) ≤ ((r * (v + 1) + 1 : ℕ) : ℝ) := by
        exact_mod_cast hdiam
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) c1 4) (Real.exp_pos _).le)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left c2 (by linarith))) (Real.exp_pos _).le
        (mul_nonneg (Real.exp_pos _).le (pow_nonneg (Nat.cast_nonneg _) 4))
    have hcard : (((supportsAtBlock ℓ.side r Y).filter (fun θ => supportUnitCount ℓ.side r θ - 1 = v)).card : ℝ) ≤
        ((((2 * (18 * r) + 1) ^ 4) ^ (2 * (v + 1)) *
          2 ^ (5 * ((2 * (v + 1) + 1) * (2 * (4 * r) + 1) ^ 4)) : ℕ) : ℝ) := by
      have hsub : (supportsAtBlock ℓ.side r Y).filter (fun θ => supportUnitCount ℓ.side r θ - 1 = v) ⊆
          walkFamily x₀ r (v + 1) := fun θ hθ => (hone θ hθ).2.1
      exact_mod_cast (Finset.card_le_card hsub).trans (card_walkFamily_le x₀ r (v + 1))
    calc _ ≤ ((supportsAtBlock ℓ.side r Y).filter (fun θ => supportUnitCount ℓ.side r θ - 1 = v)).card • b :=
          Finset.sum_le_card_nsmul _ _ _ fun θ hθ => (hone θ hθ).2.2
      _ = (((supportsAtBlock ℓ.side r Y).filter (fun θ => supportUnitCount ℓ.side r θ - 1 = v)).card : ℝ) * b :=
          nsmul_eq_mul _ _
      _ ≤ _ * b := mul_le_mul_of_nonneg_right hcard hb0
      _ ≤ Real.exp (-(14 * c * x * ((v + 1 : ℕ) : ℝ))) :=
          walk_count_mul_weight_le c x ℓ.rt r (v + 1) hr1 hrt (by omega) hnum
      _ = q ^ (v + 1) := by
          rw [hq, ← Real.exp_nat_mul]
          congr 1
          ring
  refine (Finset.sum_le_sum fun v _ => inner v).trans ((sum_geometric_succ_le q hq0 hq1 _).trans ?_)
  have h6 := hbig (6 * (c * x)) (by linarith)
  have hsplit : q = Real.exp (-(8 * c * x)) * Real.exp (-(6 * (c * x))) := by
    rw [hq, ← Real.exp_add]
    congr 1
    ring
  have hpos := Real.exp_pos (-(8 * c * x))
  rw [hsplit]
  nlinarith
end YangMills.Construction.ClusterCounting
end
