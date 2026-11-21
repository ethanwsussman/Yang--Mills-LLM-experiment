import YangMills.Construction.TorusForms.BlocksCorridorsAveragesTrees
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.IntegerLattice
def scaledLattice (d s : ℕ) : AddSubgroup (Fin d → ℤ) :=
  AddSubgroup.pi Set.univ fun _ => AddSubgroup.zmultiples (s : ℤ)
abbrev ScaledSite (d s : ℕ) : Type := scaledLattice d s
theorem mem_scaledLattice_one {d : ℕ} (v : Fin d → ℤ) : v ∈ scaledLattice d 1 :=
  (AddSubgroup.mem_pi _).mpr fun i _ => AddSubgroup.mem_zmultiples_iff.mpr ⟨v i, by simp⟩
def toUnitSite {d s : ℕ} (y : ScaledSite d s) : ScaledSite d 1 := ⟨y, mem_scaledLattice_one _⟩
def basisStep (d s : ℕ) (i : Fin d) : ScaledSite d s :=
  ⟨Pi.single i (s : ℤ), (AddSubgroup.mem_pi _).mpr fun j _ =>
    AddSubgroup.mem_zmultiples_iff.mpr ⟨if j = i then 1 else 0, by
      by_cases h : j = i <;> simp [h]⟩⟩
abbrev Edge (d s : ℕ) : Type := ScaledSite d s × Fin d
def Edge.head {d s : ℕ} (e : Edge d s) : ScaledSite d s := e.1 + basisStep d s e.2
@[ext]
structure Face (d s : ℕ) where
  base : ScaledSite d s
  first : Fin d
  second : Fin d
  lt : first < second
def Face.corners {d s : ℕ} (p : Face d s) : Set (ScaledSite d s) :=
  {p.base, p.base + basisStep d s p.first, p.base + basisStep d s p.first + basisStep d s p.second,
    p.base + basisStep d s p.second}
def Face.edges {d s : ℕ} (p : Face d s) : Set (Edge d s) :=
  {(p.base, p.first), (p.base + basisStep d s p.first, p.second),
    (p.base + basisStep d s p.second, p.first), (p.base, p.second)}
def edgesMeeting {d s : ℕ} (X : Set (ScaledSite d s)) : Set (Edge d s) :=
  {e | e.1 ∈ X ∨ e.head ∈ X}
abbrev EdgeForm (d s : ℕ) : Type := Edge d s →₀ ℝ
def edgeNormSq {d s : ℕ} (B : EdgeForm d s) : ℝ := ∑ e ∈ B.support, |B e| ^ 2
def discreteCurl (d : ℕ) : EdgeForm d 1 →ₗ[ℝ] (Face d 1 → ℝ) where
  toFun A p := A (p.base, p.first) + A (p.base + basisStep d 1 p.first, p.second)
    - A (p.base + basisStep d 1 p.second, p.first) - A (p.base, p.second)
  map_add' A B := by
    funext p
    simp only [Finsupp.add_apply, Pi.add_apply]
    ring
  map_smul' c A := by
    funext p
    simp only [Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
structure Passage (d s : ℕ) where
  edge : Edge d s
  forward : Bool
def Passage.source {d s : ℕ} (t : Passage d s) : ScaledSite d s :=
  if t.forward then t.edge.1 else t.edge.head
def Passage.target {d s : ℕ} (t : Passage d s) : ScaledSite d s :=
  if t.forward then t.edge.head else t.edge.1
def IsPassageChain {d s : ℕ} : ScaledSite d s → List (Passage d s) → Prop
  | _, [] => True
  | x, t :: ts => t.source = x ∧ IsPassageChain t.target ts
structure EdgePath (d s : ℕ) where
  origin : ScaledSite d s
  passages : List (Passage d s)
  chain : IsPassageChain origin passages
def unitPassage {d s : ℕ} (x : ScaledSite d s) (i : Fin d) (forward : Bool) : Passage d s :=
  ⟨if forward then (x, i) else (x - basisStep d s i, i), forward⟩
theorem unitPassage_source {d s : ℕ} (x : ScaledSite d s) (i : Fin d) (forward : Bool) :
    (unitPassage x i forward).source = x := by
  cases forward <;> simp [unitPassage, Passage.source, Edge.head]
def passagesOfMoves {d s : ℕ} : ScaledSite d s → List (Fin d × Bool) → List (Passage d s)
  | _, [] => []
  | x, m :: ms => unitPassage x m.1 m.2 :: passagesOfMoves (unitPassage x m.1 m.2).target ms
theorem isPassageChain_passagesOfMoves {d s : ℕ} (x : ScaledSite d s) (ms : List (Fin d × Bool)) :
    IsPassageChain x (passagesOfMoves x ms) := by
  induction ms generalizing x with
  | nil => trivial
  | cons m ms ih => exact ⟨unitPassage_source x m.1 m.2, ih _⟩
def coordinatePath {d s : ℕ} (x : ScaledSite d s) (σ : Fin d → ℤ) : EdgePath d s :=
  ⟨x, passagesOfMoves x (BlockSpin.axisMoves σ), isPassageChain_passagesOfMoves x _⟩
section Cubes
variable (S : Lattice.LatticeParameters)
def cube (y : ScaledSite S.d S.L) : Set (ScaledSite S.d 1) :=
  {x | ∃ σ, BlockSpin.InBlockIndexRange S 1 σ ∧ (x : Fin S.d → ℤ) = (y : Fin S.d → ℤ) + σ}
def cubeUnion (Y : Set (ScaledSite S.d S.L)) : Set (ScaledSite S.d 1) := ⋃ y ∈ Y, cube S y
theorem finite_setOf_inBlockIndexRange :
    {σ : Fin S.d → ℤ | BlockSpin.InBlockIndexRange S 1 σ}.Finite := by
  refine (Set.Finite.pi' fun _ => Set.finite_Icc (-(BlockSpin.blockOffset S 1 : ℤ))
    ((S.L : ℤ) ^ 1 - 1 - BlockSpin.blockOffset S 1)).subset ?_
  intro σ hσ i
  exact Set.mem_Icc.mpr (hσ i)
theorem cube_finite (y : ScaledSite S.d S.L) : (cube S y).Finite := by
  refine (((finite_setOf_inBlockIndexRange S).image fun σ => (y : Fin S.d → ℤ) + σ).preimage
    Subtype.val_injective.injOn).subset ?_
  rintro x ⟨σ, hσ, hx⟩
  exact ⟨σ, hσ, hx.symm⟩
def edgeCorridor (c : Edge S.d S.L) : Set (Edge S.d 1) :=
  {e | e.2 = c.2 ∧ e.1 ∈ cube S c.1 ∧ e.head ∈ cube S c.head}
def FaceInEdgeCorridor (p : Face S.d 1) (c : Edge S.d S.L) : Prop :=
  ∃ e ∈ p.edges, ∃ e' ∈ p.edges, e ≠ e' ∧ e ∈ edgeCorridor S c ∧ e' ∈ edgeCorridor S c
def edgeDomain (c : Edge S.d S.L) : Set (Edge S.d 1) :=
  {a | ∃ x ∈ cube S c.1, ∃ k : ℕ, k < S.L ∧ a = (x + k • basisStep S.d 1 c.2, c.2)}
theorem finite_setOf_mem_edgeDomain (a : Edge S.d 1) :
    {c : Edge S.d S.L | a ∈ edgeDomain S c}.Finite := by
  have hF := ((Set.finite_Iio S.L).prod (finite_setOf_inBlockIndexRange S)).image
    fun p : ℕ × (Fin S.d → ℤ) =>
      (a.1 : Fin S.d → ℤ) - p.1 • (basisStep S.d 1 a.2 : Fin S.d → ℤ) - p.2
  have hinj : Function.Injective fun c : Edge S.d S.L => ((c.1 : Fin S.d → ℤ), c.2) :=
    fun c c' h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) h.2
  refine ((hF.prod (Set.finite_singleton a.2)).preimage hinj.injOn).subset ?_
  rintro ⟨y, i⟩ ⟨x, ⟨σ, hσ, hx⟩, k, hk, rfl⟩
  refine ⟨⟨(k, σ), ⟨hk, hσ⟩, ?_⟩, rfl⟩
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_nsmul, hx]
  abel
def blockAverageValue (A : EdgeForm S.d 1) (c : Edge S.d S.L) : ℝ :=
  ((S.L : ℝ) ^ (S.d + 1))⁻¹ *
    ∑ x ∈ (cube_finite S c.1).toFinset, ∑ k ∈ Finset.range S.L, A (x + k • basisStep S.d 1 c.2, c.2)
theorem blockAverageValue_support_finite (A : EdgeForm S.d 1) :
    (Function.support (blockAverageValue S A)).Finite := by
  refine (A.support.finite_toSet.biUnion fun a _ => finite_setOf_mem_edgeDomain S a).subset ?_
  intro c hc
  by_contra hno
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_coe, Finsupp.mem_support_iff,
    exists_prop, not_exists, not_and] at hno
  apply hc
  have hz : ∀ x ∈ (cube_finite S c.1).toFinset, ∀ k ∈ Finset.range S.L,
      A (x + k • basisStep S.d 1 c.2, c.2) = 0 := fun x hx k hk => by
    by_contra h
    exact hno _ h ⟨x, (Set.Finite.mem_toFinset _).mp hx, k, Finset.mem_range.mp hk, rfl⟩
  simp only [blockAverageValue]
  rw [Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun k hk => hz x hx k hk, mul_zero]
def blockAverage : EdgeForm S.d 1 →ₗ[ℝ] EdgeForm S.d S.L where
  toFun A := Finsupp.ofSupportFinite (blockAverageValue S A) (blockAverageValue_support_finite S A)
  map_add' A B := by
    ext c
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.add_apply, blockAverageValue, mul_add,
      Finset.sum_add_distrib]
  map_smul' r A := by
    ext c
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.smul_apply, blockAverageValue, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
def coordinateContour (y : ScaledSite S.d S.L) (x : ScaledSite S.d 1) : EdgePath S.d 1 :=
  coordinatePath (toUnitSite y) ((x : Fin S.d → ℤ) - y)
end Cubes
end YangMills.Construction.IntegerLattice
