import YangMills.Construction.Lattice.MatrixValuedFormOperators
import YangMills.Construction.Towers.PlaquettesOfABond
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
namespace FacesContainingEdge
section General
variable {V E F : Type*} [AddGroup V] {shift : Fin 4 → V} {edgeFrom : V → Fin 4 → E}
  {edgesOf : F → List E} {corner : F → V} {lowDir highDir : F → Fin 4}
theorem exists_axis_and_corner_of_mem
    (hinj : ∀ (u v : V) (α β : Fin 4), edgeFrom u α = edgeFrom v β → u = v ∧ α = β)
    (hedges : ∀ f, edgesOf f = [edgeFrom (corner f) (lowDir f),
      edgeFrom (corner f + shift (lowDir f)) (highDir f),
      edgeFrom (corner f + shift (highDir f)) (lowDir f), edgeFrom (corner f) (highDir f)])
    (hord : ∀ f, lowDir f < highDir f) (v : V) (α : Fin 4) (f : F) (hmem : edgeFrom v α ∈ edgesOf f) :
    ∃ β : Fin 4, β ≠ α ∧ ({lowDir f, highDir f} : Set (Fin 4)) = {α, β} ∧
      (corner f = v ∨ corner f = v - shift β) := by
  have hne := (hord f).ne
  rw [hedges f] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hmem | hmem | hmem | hmem
  · obtain ⟨hv, hα⟩ := hinj _ _ _ _ hmem
    subst hα
    exact ⟨highDir f, fun e => hne e.symm, rfl, Or.inl hv.symm⟩
  · obtain ⟨hv, hα⟩ := hinj _ _ _ _ hmem
    subst hα
    exact ⟨lowDir f, hne, pair_comm _ _, Or.inr (eq_sub_of_add_eq hv.symm)⟩
  · obtain ⟨hv, hα⟩ := hinj _ _ _ _ hmem
    subst hα
    exact ⟨highDir f, fun e => hne e.symm, rfl, Or.inr (eq_sub_of_add_eq hv.symm)⟩
  · obtain ⟨hv, hα⟩ := hinj _ _ _ _ hmem
    subst hα
    exact ⟨lowDir f, hne, pair_comm _ _, Or.inl hv.symm⟩
theorem encard_le_six_of_subset_range {α : Fin 4} {A : Set F}
    (g : {β : Fin 4 // β ≠ α} × Bool → F) (hA : A ⊆ range g) : A.encard ≤ 6 := by
  classical
  have hcard : ∀ α : Fin 4, Fintype.card ({β : Fin 4 // β ≠ α} × Bool) = 6 := by decide
  calc A.encard ≤ (g '' univ).encard := encard_le_encard (by rwa [image_univ])
    _ ≤ (univ : Set ({β : Fin 4 // β ≠ α} × Bool)).encard := encard_image_le _ _
    _ = 6 := by
      rw [encard_eq_coe_toFinset_card, toFinset_univ, Finset.card_univ, hcard]
      rfl
theorem encard_setOf_mem_edges_le_six
    (hinj : ∀ (u v : V) (α β : Fin 4), edgeFrom u α = edgeFrom v β → u = v ∧ α = β)
    (hedges : ∀ f, edgesOf f = [edgeFrom (corner f) (lowDir f),
      edgeFrom (corner f + shift (lowDir f)) (highDir f),
      edgeFrom (corner f + shift (highDir f)) (lowDir f), edgeFrom (corner f) (highDir f)])
    (hord : ∀ f, lowDir f < highDir f) (build : (u : V) → (a b : Fin 4) → a < b → F)
    (hbuild : ∀ (f : F) (u : V) (a b : Fin 4) (hab : a < b),
      corner f = u → lowDir f = a → highDir f = b → build u a b hab = f)
    (v : V) (α : Fin 4) : {f : F | edgeFrom v α ∈ edgesOf f}.encard ≤ 6 := by
  classical
  let start : {β : Fin 4 // β ≠ α} × Bool → V := fun q => if q.2 then v else v - shift q.1.1
  let g : {β : Fin 4 // β ≠ α} × Bool → F := fun q =>
    if hq : α < q.1.1 then build (start q) α q.1.1 hq
    else build (start q) q.1.1 α (lt_of_le_of_ne (not_lt.mp hq) q.1.2)
  refine encard_le_six_of_subset_range g ?_
  intro f hf
  obtain ⟨β, hβ, hpair, hcorner⟩ := exists_axis_and_corner_of_mem hinj hedges hord v α f hf
  obtain ⟨s, hs⟩ : ∃ s : Bool, corner f = start (⟨β, hβ⟩, s) := by
    rcases hcorner with e | e
    · exact ⟨true, by simpa [start] using e⟩
    · exact ⟨false, by simpa [start] using e⟩
  refine ⟨(⟨β, hβ⟩, s), ?_⟩
  have hlh := hord f
  rcases pair_eq_pair_iff.mp hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hαβ : α < β := by rwa [h1, h2] at hlh
    simp only [g, dif_pos hαβ]
    exact hbuild f _ _ _ _ hs h1 h2
  · have hαβ : ¬ α < β := by
      rw [h1, h2] at hlh
      exact not_lt.mpr hlh.le
    simp only [g, dif_neg hαβ]
    exact hbuild f _ _ _ _ hs h1 h2
theorem finite_of_forall_encard_le_six {C : Type*} {S : Set C} (hS : S.Finite) (A : C → Set F)
    (hA : ∀ c, (A c).encard ≤ 6) : {f : F | ∃ c ∈ S, f ∈ A c}.Finite := by
  refine (hS.biUnion fun c _ => finite_of_encard_le_coe (k := 6) (by exact_mod_cast hA c)).subset ?_
  rintro f ⟨c, hc, hf⟩
  exact mem_biUnion hc hf
end General
theorem eq_and_eq_of_forwardFrom_eq {L n k j : ℕ} (hL : 2 ≤ L) (hn : 0 < n) (hj : j ≤ k)
    (u v : Vertex L n k j) (α β : Fin 4)
    (h : PeriodicLattice.Bond.forwardFrom u α = PeriodicLattice.Bond.forwardFrom v β) :
    u = v ∧ α = β := by
  have huv : u = v := congrArg PeriodicLattice.Bond.source h
  subst huv
  refine ⟨rfl, ?_⟩
  have htarget := congrArg PeriodicLattice.Bond.target h
  have hshift : PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) α =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) β :=
    add_left_cancel (a := u) htarget
  by_contra hne
  have hdepth : -(n : ℤ) < PeriodicLattice.levelDepth k j := by
    simp only [PeriodicLattice.levelDepth]
    omega
  exact PeriodicLattice.MatrixValued.unitStep_ne_unitStep hL hdepth hne hshift
theorem axisStep_injective {a : ℝ} (ha : a ≠ 0) {α β : Fin 4}
    (h : InfiniteLattice.axisStep a α = InfiniteLattice.axisStep a β) : α = β := by
  by_contra hne
  have hv := congrArg (fun s : InfiniteLattice.LatticePoint a =>
    (s : InfiniteLattice.AmbientSpace) α) h
  simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne hne] at hv
  exact ha hv
theorem eq_and_eq_of_link_forwardFrom_eq {a : ℝ} (ha : a ≠ 0)
    (u v : InfiniteLattice.LatticePoint a) (α β : Fin 4)
    (h : InfiniteLattice.Link.forwardFrom u α = InfiniteLattice.Link.forwardFrom v β) :
    u = v ∧ α = β := by
  have huv : u = v := congrArg InfiniteLattice.Link.initial h
  subst huv
  have hterminal := congrArg InfiniteLattice.Link.terminal h
  exact ⟨rfl, axisStep_injective ha (add_left_cancel (a := u) hterminal)⟩
theorem periodic_holds {L n k j : ℕ} (hL : 2 ≤ L) (hn : 0 < n) (hj : j ≤ k) :
    Periodic L n k j := by
  have hinj := eq_and_eq_of_forwardFrom_eq (L := L) (n := n) (k := k) (j := j) hL hn hj
  have hedges : ∀ f : Face L n k j, faceEdges f = _ := fun _ => rfl
  have hord : ∀ f : Face L n k j, f.firstAxis < f.secondAxis := fun f => f.firstAxis_lt_secondAxis
  have hsix : ∀ e : PositiveEdge L n k j,
      {f : Face L n k j | (e : Edge L n k j) ∈ faceEdges f}.encard ≤ 6 := by
    rintro ⟨e, α, he⟩
    have hef : e = PeriodicLattice.Bond.forwardFrom e.source α :=
      PeriodicLattice.Bond.ext rfl (sub_eq_iff_eq_add'.mp he)
    simp only []
    rw [hef]
    exact encard_setOf_mem_edges_le_six hinj hedges hord
      (fun u a c hac => (⟨u, a, c, hac⟩ : Face L n k j))
      (fun f u a c hac h1 h2 h3 => by subst h1 h2 h3; rfl) e.source α
  exact ⟨fun v α f hf => exists_axis_and_corner_of_mem hinj hedges hord v α f hf, hsix,
    fun S hS => finite_of_forall_encard_le_six hS _ hsix⟩
theorem onFullSpace_holds {L k j : ℕ} (hL : 2 ≤ L) : OnFullSpace L k j := by
  have ha : meshAt L k j ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast (by omega : L ≠ 0))
  have hinj := eq_and_eq_of_link_forwardFrom_eq ha
  have hedges : ∀ f : FullSpace.Face L k j, FullSpace.faceEdges f = _ := fun _ => rfl
  have hord : ∀ f : FullSpace.Face L k j, f.lowAxis < f.highAxis := fun f => f.lowAxis_lt_highAxis
  have hsix : ∀ e : FullSpace.PositiveEdge (meshAt L k j),
      {f : FullSpace.Face L k j |
        (e : InfiniteLattice.Link (meshAt L k j)) ∈ FullSpace.faceEdges f}.encard ≤ 6 := by
    rintro ⟨e, α, he⟩
    have hef : e = InfiniteLattice.Link.forwardFrom e.initial α :=
      InfiniteLattice.Link.ext rfl (sub_eq_iff_eq_add'.mp he)
    simp only []
    rw [hef]
    exact encard_setOf_mem_edges_le_six hinj hedges hord
      (fun u a c hac => (⟨u, a, c, hac⟩ : FullSpace.Face L k j))
      (fun f u a c hac h1 h2 h3 => by subst h1 h2 h3; rfl) e.initial α
  exact ⟨fun v α f hf => exists_axis_and_corner_of_mem hinj hedges hord v α f hf, hsix,
    fun S hS => finite_of_forall_encard_le_six hS _ hsix⟩
theorem holds : Holds := by
  intro L hL k j hj
  have h2 : 2 ≤ L := by
    have := hL.2
    omega
  exact ⟨fun n hn => periodic_holds h2 hn hj, onFullSpace_holds h2⟩
end FacesContainingEdge
end Tower
end YangMills.Construction
end
