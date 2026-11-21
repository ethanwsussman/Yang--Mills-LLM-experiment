import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATower
import YangMills.Construction.Towers.CountsOfCrossingsOnASide
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.PeriodicLattice (FourTorus refinedBlock crossingPath)
noncomputable section
namespace YangMills.Construction.Tower.CrossingCounting
theorem finsum_ncard_slices {C X : Type*} (p : C → Prop) (S : Set (C × X)) (hS : S.Finite)
    (hp : ∀ q ∈ S, p q.1) :
    ∑ᶠ c : {c // p c}, (({x | (c.1, x) ∈ S}).ncard : ℝ) = (S.ncard : ℝ) := by
  classical
  have hsupp : Function.support (fun c : {c // p c} => (({x | (c.1, x) ∈ S}).ncard : ℝ)) ⊆
      (((hS.toFinset.image Prod.fst).subtype p : Finset {c // p c}) : Set {c // p c}) := by
    intro c hc
    have hne : ({x | (c.1, x) ∈ S}).ncard ≠ 0 := by
      simpa [Function.mem_support] using hc
    obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero hne
    rw [Finset.mem_coe, Finset.mem_subtype]
    exact Finset.mem_image.2 ⟨(c.1, x), hS.mem_toFinset.2 hx, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_subtype_of_mem (fun c => (({x | (c, x) ∈ S}).ncard : ℝ))
      (by
        intro c hc
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hc
        exact hp q (hS.mem_toFinset.1 hq)),
    Set.ncard_eq_toFinset_card S hS,
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := hS.toFinset.image Prod.fst)
      (fun q hq => Finset.mem_image_of_mem _ hq)]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [← Set.ncard_image_of_injective _ (Prod.mk_right_injective c), ← Set.ncard_coe_finset]
  congr 1
  ext q
  simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hq, rfl⟩
    exact ⟨q.2, hq, rfl⟩
theorem nsmul_unitStep_injOn {L m : ℕ} (hL : 0 < L) {J : ℤ} {N : ℕ} (μ : Fin 4)
    (hN : (N : ℝ) < (L : ℝ) ^ ((m : ℤ) + J)) {a b : ℕ} (ha : a < N) (hb : b < N)
    (h : a • PeriodicLattice.unitStep L m J μ = b • PeriodicLattice.unitStep L m J μ) :
    a = b := by
  wlog hab : a ≤ b generalizing a b
  · exact (this hb ha h.symm (by omega)).symm
  by_contra hne
  have hlt : a < b := lt_of_le_of_ne hab hne
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hco : a • ((PeriodicLattice.meshSize L J : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) =
      b • ((PeriodicLattice.meshSize L J : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) := by
    have := congrArg (fun s : PeriodicLattice.Site L m J => (s : FourTorus L m) μ) h
    simpa [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis] using this
  have hzero : ((((b : ℝ) - a) * PeriodicLattice.meshSize L J : ℝ) :
      AddCircle (PeriodicLattice.torusSide L m)) = 0 := by
    rw [sub_mul, AddCircle.coe_sub, ← nsmul_eq_mul, ← nsmul_eq_mul, AddCircle.coe_nsmul,
      AddCircle.coe_nsmul, hco, sub_self]
  obtain ⟨t, ht⟩ := (AddCircle.coe_eq_zero_iff _).1 hzero
  have hs : 0 < PeriodicLattice.meshSize L J := zpow_pos hLr _
  have hLm : (0 : ℝ) < (L : ℝ) ^ m := pow_pos hLr m
  have hdiff : (0 : ℝ) < (b : ℝ) - a := by
    have : (a : ℝ) < b := by exact_mod_cast hlt
    linarith
  have hdiffN : (b : ℝ) - a < N := by
    have h1 : (b : ℝ) < N := by exact_mod_cast hb
    linarith
  have hprod : (L : ℝ) ^ ((m : ℤ) + J) * PeriodicLattice.meshSize L J = (L : ℝ) ^ m := by
    rw [PeriodicLattice.meshSize, ← zpow_add₀ hLr.ne']
    simp
  have hval : (t : ℝ) * (2 * (L : ℝ) ^ m) = ((b : ℝ) - a) * PeriodicLattice.meshSize L J := by
    simpa [PeriodicLattice.torusSide, zsmul_eq_mul] using ht
  have hpos : (0 : ℝ) < (t : ℝ) * (2 * (L : ℝ) ^ m) := by
    rw [hval]
    exact mul_pos hdiff hs
  have ht0 : (0 : ℝ) < t := by
    by_contra hc
    have : (t : ℝ) * (2 * (L : ℝ) ^ m) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) (by positivity)
    linarith
  have ht1 : (1 : ℝ) ≤ t := by
    have : (0 : ℤ) < t := by exact_mod_cast ht0
    exact_mod_cast this
  nlinarith
variable {L m k n j : ℕ}
theorem crossingPath_nodup_positive_length (hL : 0 < L)
    (hT : BlockTranslateAlongBond L m k n j)
    (c : Edge L m k j) (hc : c.IsPositivelyOriented) (x : Vertex L m k (j - n))
    (hx : (x : FourTorus L m) ∈ refinedBlock n c.source) :
    (crossingPath c x).Nodup ∧ (∀ e ∈ crossingPath c x, e.IsPositivelyOriented) ∧
      (crossingPath c x).length = L ^ n := by
  obtain ⟨μ, hμ⟩ := hc
  have hbound := (hT.isAxialDisplacement c μ hμ x hx).2
  have hN : ((L ^ n : ℕ) : ℝ) <
      (L : ℝ) ^ ((m : ℤ) + PeriodicLattice.levelDepth k (j - n)) := by
    have habs : |(L : ℤ) ^ n| = (L : ℤ) ^ n := abs_of_nonneg (by positivity)
    rw [habs] at hbound
    simpa using hbound
  rw [hT.crossingPath_eq c μ hμ x hx]
  refine ⟨?_, ?_, by simp⟩
  · refine List.Nodup.map_on ?_ List.nodup_range
    intro a ha b hb hab
    have hsrc := congrArg PeriodicLattice.Bond.source hab
    simp only [PeriodicLattice.Bond.forwardFrom, add_right_inj] at hsrc
    exact nsmul_unitStep_injOn hL μ hN (List.mem_range.1 ha) (List.mem_range.1 hb) hsrc
  · intro e he
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    exact ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
theorem ncard_vertices_in_refinedBlock (hB : RefinedBlocksPartition L m k n j)
    (y : Vertex L m k j) :
    {x : Vertex L m k (j - n) | (x : FourTorus L m) ∈ refinedBlock n y}.ncard = L ^ (4 * n) := by
  rw [← hB.ncard_eq y, ← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hp
    exact ⟨⟨p, hB.subset_sublattice y hp⟩, hp, rfl⟩
theorem finsum_fineEdges_ncard (hL : 0 < L) (hB : RefinedBlocksPartition L m k n j)
    (hT : BlockTranslateAlongBond L m k n j) (c : Edge L m k j) (hc : c.IsPositivelyOriented) :
    ∑ᶠ e : PositiveEdge L m k (j - n),
        (({x : Vertex L m k (j - n) | (x : FourTorus L m) ∈ refinedBlock n c.source ∧
          e.1 ∈ crossingPath c x}).ncard : ℝ) = (L : ℝ) ^ (5 * n) := by
  classical
  set X : Set (Vertex L m k (j - n)) := {x | (x : FourTorus L m) ∈ refinedBlock n c.source}
    with hXdef
  have hXcard : X.ncard = L ^ (4 * n) := ncard_vertices_in_refinedBlock hB c.source
  have hXfin : X.Finite := Set.finite_of_ncard_ne_zero (by rw [hXcard]; positivity)
  set Q : Set (Vertex L m k (j - n) × Edge L m k (j - n)) :=
    {q | q.1 ∈ X ∧ q.2 ∈ crossingPath c q.1} with hQdef
  have hQfin : Q.Finite := by
    refine (hXfin.biUnion fun x _ =>
      (List.finite_toSet (crossingPath c x)).image (fun e => (x, e))).subset ?_
    rintro ⟨x, e⟩ ⟨hx, he⟩
    exact Set.mem_biUnion hx ⟨e, he, rfl⟩
  have hcount : (Q.ncard : ℝ) = (L : ℝ) ^ (5 * n) := by
    rw [← finsum_ncard_slices (fun x => x ∈ X) Q hQfin fun q hq => hq.1]
    have hslice : ∀ x : {x // x ∈ X},
        (({e | (x.1, e) ∈ Q}).ncard : ℝ) = (L : ℝ) ^ n := by
      intro x
      obtain ⟨hnd, -, hlen⟩ := crossingPath_nodup_positive_length hL hT c hc x.1 x.2
      have : {e | (x.1, e) ∈ Q} = ((crossingPath c x.1).toFinset : Set _) := by
        ext e
        simp [hQdef, x.2]
      rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen]
      simp
    have : Finite {x // x ∈ X} := hXfin.to_subtype
    have : Fintype {x // x ∈ X} := Fintype.ofFinite _
    rw [finsum_congr hslice, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    have : Nat.card {x // x ∈ X} = X.ncard := Nat.card_coe_set_eq X
    rw [this, hXcard, nsmul_eq_mul]
    push_cast
    rw [← pow_add]
    congr 1
    ring
  set S : Set (Edge L m k (j - n) × Vertex L m k (j - n)) :=
    {q | q.1.IsPositivelyOriented ∧ q.2 ∈ X ∧ q.1 ∈ crossingPath c q.2} with hSdef
  have hswap : Prod.swap '' Q = S := by
    ext ⟨e, x⟩
    constructor
    · rintro ⟨⟨x', e'⟩, ⟨hx, he⟩, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨(crossingPath_nodup_positive_length hL hT c hc _ hx).2.1 _ he, hx, he⟩
    · rintro ⟨-, hx, he⟩
      exact ⟨(x, e), ⟨hx, he⟩, rfl⟩
  have hSfin : S.Finite := hswap ▸ hQfin.image _
  have hScard : S.ncard = Q.ncard := by
    rw [← hswap, Set.ncard_image_of_injective _ Prod.swap_injective]
  have hsum := finsum_ncard_slices (fun e : Edge L m k (j - n) => e.IsPositivelyOriented) S hSfin
    fun q hq => hq.1
  rw [hScard, hcount] at hsum
  rw [← hsum]
  refine finsum_congr fun e => ?_
  congr 2
  ext x
  simp [hSdef, hXdef, e.2]
theorem finsum_coarseEdges_ncard (hL : 0 < L) (hA : AxialPathMultiplicity L m k n j)
    (e : Edge L m k (j - n)) (he : e.IsPositivelyOriented) :
    ∑ᶠ c : PositiveEdge L m k j,
        (({x : Vertex L m k (j - n) | (x : FourTorus L m) ∈ refinedBlock n c.1.source ∧
          e ∈ crossingPath c.1 x}).ncard : ℝ) = (L : ℝ) ^ n := by
  set S : Set (Edge L m k j × Vertex L m k (j - n)) :=
    {p | p.1.IsPositivelyOriented ∧ (p.2 : FourTorus L m) ∈ refinedBlock n p.1.source ∧
      e ∈ crossingPath p.1 p.2}
    with hSdef
  have hcard : S.ncard = L ^ n := hA e he
  have hSfin : S.Finite := Set.finite_of_ncard_ne_zero (by rw [hcard]; positivity)
  have hsum := finsum_ncard_slices (fun c : Edge L m k j => c.IsPositivelyOriented) S hSfin
    fun q hq => hq.1
  rw [hcard] at hsum
  push_cast at hsum
  rw [← hsum]
  refine finsum_congr fun c => ?_
  congr 2
  ext x
  simp [hSdef, c.2]
theorem crossingCountsOnTorus_holds (h : BlockPathContourPivotStatement) :
    CrossingCountsOnTorus := by
  intro L hL m k i j hm hk hij hjk
  obtain ⟨n, hn, rfl⟩ : ∃ n, n ≤ j ∧ i = j - n := ⟨j - i, by omega, by omega⟩
  have hnn : j - (j - n) = n := by omega
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨hB, -, hT, hA, -, -⟩ := (h L hL k n j hk hn hjk).1 m hm
  simp only [crossingSites, hnn]
  refine ⟨fun c => finsum_fineEdges_ncard hL0 hB hT c.1 c.2,
    fun e => finsum_coarseEdges_ncard hL0 hA e.1 e.2, fun c x hx => ?_⟩
  obtain ⟨hnd, hpos, -⟩ := crossingPath_nodup_positive_length hL0 hT c.1 c.2 x hx
  exact ⟨hnd, hpos⟩
end YangMills.Construction.Tower.CrossingCounting
end
