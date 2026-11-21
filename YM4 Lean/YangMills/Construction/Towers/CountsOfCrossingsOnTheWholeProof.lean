import YangMills.Construction.Towers.CountsOfCrossingsOnASideProof
import YangMills.Construction.Towers.CountsOfCrossingsOnTheWhole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open InfiniteLattice (AmbientSpace)
namespace Tower.FullSpace.CrossingCounting
theorem finsum_ncard_fiber_eq_ncard {C X : Type*} (p : C → Prop) (S : Set (C × X)) (hS : S.Finite)
    (hp : ∀ q ∈ S, p q.1) :
    ∑ᶠ c : {c // p c}, (({x | (c.1, x) ∈ S}).ncard : ℝ) = (S.ncard : ℝ) := by apply _root_.YangMills.Construction.Tower.CrossingCounting.finsum_ncard_slices <;> assumption
theorem finite_support_of_finsum_ne_zero {α : Type*} {f : α → ℝ} (h : ∑ᶠ a, f a ≠ 0) :
    (Function.support f).Finite := by
  by_contra hinf
  exact h (finsum_of_infinite_support hinf)
theorem nsmul_axisStep_inj {s : ℝ} (hs : 0 < s) (μ : Fin 4) {a b : ℕ}
    (h : a • InfiniteLattice.axisStep s μ = b • InfiniteLattice.axisStep s μ) : a = b := by
  have h1 := congrArg (fun p : InfiniteLattice.LatticePoint s => (p : AmbientSpace) μ) h
  have h2 : (a : ℝ) * s = b * s := by
    simpa [InfiniteLattice.axisStep] using h1
  exact_mod_cast mul_right_cancel₀ hs.ne' h2
variable {L k n j : ℕ}
theorem meshAt_pos (hL : 0 < L) (i : ℕ) : 0 < meshAt L k i :=
  zpow_pos (by exact_mod_cast hL) _
theorem crossingPath_nodup_positive_length (hL : 0 < L) (hT : CubeTranslateAlongLink L k n j)
    (c : Edge L k j) (hc : c.IsPositivelyOriented) (x : Vertex L k (j - n))
    (hx : (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial) :
    (crossingPath c x).Nodup ∧ (∀ e ∈ crossingPath c x, e.IsPositivelyOriented) ∧
      (crossingPath c x).length = L ^ n := by
  obtain ⟨μ, hμ⟩ := hc
  rw [hT.crossingPath_eq c μ hμ x hx]
  refine ⟨?_, ?_, by simp⟩
  · refine List.Nodup.map_on ?_ List.nodup_range
    intro a _ b _ hab
    have hinit := congrArg InfiniteLattice.Link.initial hab
    simp only [InfiniteLattice.Link.forwardFrom, add_right_inj] at hinit
    exact nsmul_axisStep_inj (meshAt_pos hL _) μ hinit
  · intro e he
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    exact ⟨μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem ncard_vertices_in_cube (hB : RefinedCubesPartition L k n j) (y : Vertex L k j) :
    {x : Vertex L k (j - n) |
      (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n y}.ncard = L ^ (4 * n) := by
  rw [← hB.ncard_eq y, ← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hp
    exact ⟨⟨p, hB.subset_sublattice y hp⟩, hp, rfl⟩
theorem finsum_over_fine_edges (hL : 0 < L) (hB : RefinedCubesPartition L k n j)
    (hT : CubeTranslateAlongLink L k n j) (c : Edge L k j) (hc : c.IsPositivelyOriented) :
    ∑ᶠ b : PositiveEdge (meshAt L k (j - n)),
        (({x : Vertex L k (j - n) |
          (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial ∧
            b.1 ∈ crossingPath c x}).ncard : ℝ) = (L : ℝ) ^ (5 * n) := by
  classical
  set X : Set (Vertex L k (j - n)) :=
    {x | (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial} with hXdef
  have hXcard : X.ncard = L ^ (4 * n) := ncard_vertices_in_cube hB c.initial
  have hXfin : X.Finite := Set.finite_of_ncard_ne_zero (by rw [hXcard]; positivity)
  set Q : Set (Vertex L k (j - n) × Edge L k (j - n)) :=
    {q | q.1 ∈ X ∧ q.2 ∈ crossingPath c q.1} with hQdef
  have hQfin : Q.Finite := by
    refine (hXfin.biUnion fun x _ =>
      (List.finite_toSet (crossingPath c x)).image (fun b => (x, b))).subset ?_
    rintro ⟨x, b⟩ ⟨hx, hb⟩
    exact Set.mem_biUnion hx ⟨b, hb, rfl⟩
  have hcount : (Q.ncard : ℝ) = (L : ℝ) ^ (5 * n) := by
    rw [← finsum_ncard_fiber_eq_ncard (fun x => x ∈ X) Q hQfin fun q hq => hq.1]
    have hfibre : ∀ x : {x // x ∈ X},
        (({b | (x.1, b) ∈ Q}).ncard : ℝ) = (L : ℝ) ^ n := by
      intro x
      obtain ⟨hnd, -, hlen⟩ := crossingPath_nodup_positive_length hL hT c hc x.1 x.2
      have : {b | (x.1, b) ∈ Q} = ((crossingPath c x.1).toFinset : Set _) := by
        ext b
        simp [hQdef, x.2]
      rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hlen]
      simp
    have : Finite {x // x ∈ X} := hXfin.to_subtype
    have : Fintype {x // x ∈ X} := Fintype.ofFinite _
    rw [finsum_congr hfibre, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    have : Nat.card {x // x ∈ X} = X.ncard := Nat.card_coe_set_eq X
    rw [this, hXcard, nsmul_eq_mul]
    push_cast
    rw [← pow_add]
    congr 1
    ring
  set P : Set (Edge L k (j - n) × Vertex L k (j - n)) :=
    {q | q.1.IsPositivelyOriented ∧ q.2 ∈ X ∧ q.1 ∈ crossingPath c q.2} with hPdef
  have hswap : Prod.swap '' Q = P := by
    ext ⟨b, x⟩
    constructor
    · rintro ⟨⟨x', b'⟩, ⟨hx, hb⟩, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨(crossingPath_nodup_positive_length hL hT c hc _ hx).2.1 _ hb, hx, hb⟩
    · rintro ⟨-, hx, hb⟩
      exact ⟨(x, b), ⟨hx, hb⟩, rfl⟩
  have hPfin : P.Finite := hswap ▸ hQfin.image _
  have hPcard : P.ncard = Q.ncard := by
    rw [← hswap, Set.ncard_image_of_injective _ Prod.swap_injective]
  have hsum := finsum_ncard_fiber_eq_ncard
    (fun b : Edge L k (j - n) => b.IsPositivelyOriented) P hPfin fun q hq => hq.1
  rw [hPcard, hcount] at hsum
  rw [← hsum]
  refine finsum_congr fun b => ?_
  congr 2
  ext x
  simp [hPdef, hXdef, b.2]
theorem finsum_over_coarse_edges (hL : 0 < L) (hM : AxisPathMultiplicity L k n j)
    (b : Edge L k (j - n)) (hb : b.IsPositivelyOriented) :
    ∑ᶠ c : PositiveEdge (meshAt L k j),
        (({x : Vertex L k (j - n) |
          (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.1.initial ∧
            b ∈ crossingPath c.1 x}).ncard : ℝ) = (L : ℝ) ^ n := by
  set P : Set (Edge L k j × Vertex L k (j - n)) :=
    {p | p.1.IsPositivelyOriented ∧
      (p.2 : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n p.1.initial ∧
      b ∈ crossingPath p.1 p.2}
    with hPdef
  have hcard : P.ncard = L ^ n := hM b hb
  have hPfin : P.Finite := Set.finite_of_ncard_ne_zero (by rw [hcard]; positivity)
  have hsum := finsum_ncard_fiber_eq_ncard
    (fun c : Edge L k j => c.IsPositivelyOriented) P hPfin fun q hq => hq.1
  rw [hcard] at hsum
  push_cast at hsum
  rw [← hsum]
  refine finsum_congr fun c => ?_
  congr 2
  ext x
  simp [hPdef, c.2]
theorem crossingCounts_holds (h : BlockPathContourPivotStatement) :
    CrossingCounts := by
  intro L hL k i j hk hij hjk
  obtain ⟨n, hn, rfl⟩ : ∃ n, n ≤ j ∧ i = j - n := ⟨j - i, by omega, by omega⟩
  have hnn : j - (j - n) = n := by omega
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨-, hB, -, hT, hM, hS, -⟩ := h L hL k n j hk hn hjk
  simp only [crossingSites, hnn]
  refine ⟨fun c => ?_, fun b => ?_, fun c x hx => ?_, ?_⟩
  · have hsum := finsum_over_fine_edges hL0 hB hT c.1 c.2
    exact ⟨finite_support_of_finsum_ne_zero (by rw [hsum]; positivity), hsum⟩
  · have hsum := finsum_over_coarse_edges hL0 hM b.1 b.2
    exact ⟨finite_support_of_finsum_ne_zero (by rw [hsum]; positivity), hsum⟩
  · obtain ⟨hnd, hpos, -⟩ := crossingPath_nodup_positive_length hL0 hT c.1 c.2 x hx
    exact ⟨hnd, hpos⟩
  · rintro c b ⟨x, hx, hb⟩ ρ
    have hz := hT.crossingPath_vertex_mem c.1 c.2 x hx b.1.initial
      (Or.inr (Or.inr ⟨b.1, hb, Or.inl rfl⟩))
    obtain ⟨ν, hν, hlt⟩ := hS.sites_near c.1 c.2 _ hz
    have hdiff : (b.1.initial : AmbientSpace) ρ - (c.1.initial : AmbientSpace) ρ =
        (ν ρ : ℝ) * meshAt L k (j - n) := by
      rw [hν]
      simp [offsetPoint, Finset.sum_apply, Pi.single_apply]
    rw [hdiff]
    exact (hlt ρ).le
end Tower.FullSpace.CrossingCounting
end YangMills.Construction
end
