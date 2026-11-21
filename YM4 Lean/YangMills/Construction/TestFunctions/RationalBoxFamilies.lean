import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.TestFunctions
def IsRatBox (B : Set (Fin 4 → ℝ)) : Prop :=
  ∃ s t : Fin 4 → ℚ, (∀ κ, s κ < t κ) ∧ B = univ.pi fun κ => Icc (s κ : ℝ) (t κ)
def ratBoxUnions : Set (Set (Fin 4 → ℝ)) :=
  {Q | ∃ 𝓑 : Set (Set (Fin 4 → ℝ)), 𝓑.Finite ∧ (∀ B ∈ 𝓑, IsRatBox B) ∧ Q = ⋃₀ 𝓑}
def c1ZeroOff (Q : Set (Fin 4 → ℝ)) : Set ((Fin 4 → ℝ) → ℝ) :=
  {f | IsC1R4 f ∧ ∀ x, x ∉ Q → f x = 0}
def IsDenseInC1ZeroOff (Q : Set (Fin 4 → ℝ)) (D : Set ((Fin 4 → ℝ) → ℝ)) : Prop :=
  ∀ f ∈ c1ZeroOff Q, ∀ ε : ℝ, 0 < ε → ∃ g ∈ D, c1NormR4 (g - f) < ε
structure IsDenseFamily (D : ratBoxUnions → Set ((Fin 4 → ℝ) → ℝ)) : Prop where
  subset : ∀ Q : ratBoxUnions, D Q ⊆ c1ZeroOff Q
  countable : ∀ Q : ratBoxUnions, (D Q).Countable
  dense : ∀ Q : ratBoxUnions, IsDenseInC1ZeroOff Q (D Q)
def disjointTupleFamily (D : ratBoxUnions → Set ((Fin 4 → ℝ) → ℝ)) :
    Set (List ((Fin 4 → ℝ) → ℝ)) :=
  {X | X ≠ [] ∧ ∃ Q : Fin X.length → ratBoxUnions,
    (Pairwise fun i k => Disjoint (Q i : Set (Fin 4 → ℝ)) (Q k)) ∧ ∀ i, X.get i ∈ D (Q i)}
theorem IsRatBox.isCompact {B : Set (Fin 4 → ℝ)} (h : IsRatBox B) : IsCompact B := by
  obtain ⟨s, t, -, rfl⟩ := h
  exact isCompact_univ_pi fun κ => isCompact_Icc
theorem isCompact_of_mem_ratBoxUnions {Q : Set (Fin 4 → ℝ)} (h : Q ∈ ratBoxUnions) :
    IsCompact Q := by
  obtain ⟨𝓑, hf, hB, rfl⟩ := h
  exact hf.isCompact_sUnion fun B hB' => (hB B hB').isCompact
theorem tsupport_subset_of_mem_c1ZeroOff {Q : Set (Fin 4 → ℝ)} (hQ : IsClosed Q)
    {f : (Fin 4 → ℝ) → ℝ} (hf : f ∈ c1ZeroOff Q) : tsupport f ⊆ Q :=
  closure_minimal (fun x hx => by_contra fun h => hx (hf.2 x h)) hQ
theorem mem_c1ZeroOff_iff {Q : Set (Fin 4 → ℝ)} (hQ : Q ∈ ratBoxUnions)
    {f : (Fin 4 → ℝ) → ℝ} :
    f ∈ c1ZeroOff Q ↔ IsC1R4 f ∧ HasCompactSupport f ∧ tsupport f ⊆ Q := by
  have hc := isCompact_of_mem_ratBoxUnions hQ
  constructor
  · intro hf
    have hs := tsupport_subset_of_mem_c1ZeroOff hc.isClosed hf
    exact ⟨hf.1, hc.of_isClosed_subset (isClosed_tsupport f) hs, hs⟩
  · rintro ⟨h1, -, hs⟩
    refine ⟨h1, fun x hx => ?_⟩
    by_contra h
    exact hx (hs (subset_tsupport f h))
theorem pairwise_disjoint_tsupport_of_mem_disjointTupleFamily
    {D : ratBoxUnions → Set ((Fin 4 → ℝ) → ℝ)} (hD : IsDenseFamily D)
    {X : List ((Fin 4 → ℝ) → ℝ)} (hX : X ∈ disjointTupleFamily D) :
    X.Pairwise fun f g => Disjoint (tsupport f) (tsupport g) := by
  obtain ⟨-, Q, hdis, hQ⟩ := hX
  refine List.pairwise_iff_get.2 fun i k hik => ?_
  have hi := (mem_c1ZeroOff_iff (Q i).2).1 (hD.subset (Q i) (hQ i))
  have hk := (mem_c1ZeroOff_iff (Q k).2).1 (hD.subset (Q k) (hQ k))
  exact (hdis hik.ne).mono hi.2.2 hk.2.2
end YangMills.Construction.TestFunctions
