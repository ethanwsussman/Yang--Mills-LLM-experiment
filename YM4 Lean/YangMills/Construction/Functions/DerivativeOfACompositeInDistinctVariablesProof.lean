import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionFacts
import YangMills.Construction.Functions.DerivativeOfACompositeInDistinctVariables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CompositeDerivative
open Filter Topology
open YangMills.Construction.ComplexVariables YangMills.Construction.SetPartition
open YangMills.Construction.Coordinates
section Blocks
variable {α : Type*} [DecidableEq α]
theorem mem_iff_exists_part {A : Finset α} (P : Partitions A) (x : α) :
    x ∈ A ↔ ∃ B ∈ P.parts, x ∈ B := by
  constructor
  · intro hx
    rw [← P.sup_parts, Finset.mem_sup] at hx
    exact hx
  · rintro ⟨B, hB, hx⟩
    exact P.le hB hx
theorem part_eq_of_mem_of_mem {A : Finset α} (P : Partitions A) {B B' : Finset α}
    (hB : B ∈ P.parts) (hB' : B' ∈ P.parts) {x : α} (hx : x ∈ B) (hx' : x ∈ B') : B = B' := by
  by_contra hne
  exact Finset.disjoint_left.1 (P.disjoint hB hB' hne) hx hx'
def ofDisjointParts (A : Finset α) (Q : Finset (Finset α))
    (hd : ∀ B ∈ Q, ∀ B' ∈ Q, ∀ x, x ∈ B → x ∈ B' → B = B')
    (hu : ∀ x, x ∈ A ↔ ∃ B ∈ Q, x ∈ B) (hne : ∅ ∉ Q) : Partitions A where
  parts := Q
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.2 fun B hB B' hB' h =>
    Finset.disjoint_left.2 fun x hx hx' => h (hd B hB B' hB' x hx hx')
  sup_parts := by
    ext x
    rw [Finset.mem_sup, hu x]
    rfl
  bot_notMem := hne
variable {A : Finset α} {s : α}
theorem notMem_part_of_notMem (hs : s ∉ A) (P : Partitions A) {B : Finset α}
    (hB : B ∈ P.parts) : s ∉ B := fun h => hs (P.le hB h)
theorem part_nonempty (P : Partitions A) {B : Finset α} (hB : B ∈ P.parts) : B.Nonempty :=
  Finset.nonempty_iff_ne_empty.2 (by rintro rfl; exact P.bot_notMem hB)
def addSingletonPart (hs : s ∉ A) (P : Partitions A) : Partitions (insert s A) :=
  ofDisjointParts (insert s A) (insert {s} P.parts)
    (by
      intro B hB B' hB' x hx hx'
      rcases Finset.mem_insert.1 hB with rfl | hB <;> rcases Finset.mem_insert.1 hB' with rfl | hB'
      · rfl
      · rw [Finset.mem_singleton] at hx
        exact absurd (hx ▸ hx') (notMem_part_of_notMem hs P hB')
      · rw [Finset.mem_singleton] at hx'
        exact absurd (hx' ▸ hx) (notMem_part_of_notMem hs P hB)
      · exact part_eq_of_mem_of_mem P hB hB' hx hx')
    (by
      intro x
      rw [Finset.mem_insert, mem_iff_exists_part P x]
      constructor
      · rintro (rfl | ⟨B, hB, hx⟩)
        · exact ⟨{x}, Finset.mem_insert_self _ _, Finset.mem_singleton_self x⟩
        · exact ⟨B, Finset.mem_insert_of_mem hB, hx⟩
      · rintro ⟨B, hB, hx⟩
        rcases Finset.mem_insert.1 hB with rfl | hB
        · exact Or.inl (Finset.mem_singleton.1 hx)
        · exact Or.inr ⟨B, hB, hx⟩)
    (by
      intro h
      rcases Finset.mem_insert.1 h with h | h
      · exact Finset.singleton_ne_empty s h.symm
      · exact P.bot_notMem h)
def insertIntoPart (hs : s ∉ A) (P : Partitions A) (B₀ : Finset α) (hB₀ : B₀ ∈ P.parts) :
    Partitions (insert s A) :=
  ofDisjointParts (insert s A) (insert (insert s B₀) (P.parts.erase B₀))
    (by
      have key : ∀ B ∈ P.parts.erase B₀, ∀ x, x ∈ insert s B₀ → x ∈ B → False := by
        intro B hB x hx hx'
        obtain ⟨hne, hB⟩ := Finset.mem_erase.1 hB
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact notMem_part_of_notMem hs P hB hx'
        · exact hne (part_eq_of_mem_of_mem P hB hB₀ hx' hx)
      intro B hB B' hB' x hx hx'
      rcases Finset.mem_insert.1 hB with rfl | hB <;> rcases Finset.mem_insert.1 hB' with rfl | hB'
      · rfl
      · exact (key B' hB' x hx hx').elim
      · exact (key B hB x hx' hx).elim
      · exact part_eq_of_mem_of_mem P (Finset.mem_of_mem_erase hB) (Finset.mem_of_mem_erase hB')
          hx hx')
    (by
      intro x
      rw [Finset.mem_insert, mem_iff_exists_part P x]
      constructor
      · rintro (rfl | ⟨B, hB, hx⟩)
        · exact ⟨_, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
        · by_cases hBB : B = B₀
          · subst hBB
            exact ⟨_, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hx⟩
          · exact ⟨B, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hBB, hB⟩), hx⟩
      · rintro ⟨B, hB, hx⟩
        rcases Finset.mem_insert.1 hB with rfl | hB
        · rcases Finset.mem_insert.1 hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr ⟨B₀, hB₀, hx⟩
        · exact Or.inr ⟨B, Finset.mem_of_mem_erase hB, hx⟩)
    (by
      intro h
      rcases Finset.mem_insert.1 h with h | h
      · exact Finset.insert_ne_empty s B₀ h.symm
      · exact P.bot_notMem (Finset.mem_of_mem_erase h))
def extendPartition (hs : s ∉ A) (P : Partitions A) :
    Option {B // B ∈ P.parts} → Partitions (insert s A)
  | none => addSingletonPart hs P
  | some B => insertIntoPart hs P B.1 B.2
theorem parts_erase_of_extendPartition (hs : s ∉ A) (P : Partitions A)
    (o : Option {B // B ∈ P.parts}) :
    ((extendPartition hs P o).parts.image fun B => B.erase s).erase ∅ = P.parts := by
  have hout : ∀ B ∈ P.parts, B.erase s = B := fun B hB =>
    Finset.erase_eq_of_notMem (notMem_part_of_notMem hs P hB)
  ext I
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hI, B, hB, rfl⟩
    cases o with
    | none =>
      rcases Finset.mem_insert.1 hB with rfl | hB
      · simp at hI
      · rwa [hout B hB]
    | some B₀ =>
      rcases Finset.mem_insert.1 hB with rfl | hB
      · rw [Finset.erase_insert (notMem_part_of_notMem hs P B₀.2)]
        exact B₀.2
      · rw [hout B (Finset.mem_of_mem_erase hB)]
        exact Finset.mem_of_mem_erase hB
  · intro hI
    refine ⟨(part_nonempty P hI).ne_empty, ?_⟩
    cases o with
    | none => exact ⟨I, Finset.mem_insert_of_mem hI, hout I hI⟩
    | some B₀ =>
      by_cases hIB : I = B₀.1
      · refine ⟨insert s I, ?_, ?_⟩
        · rw [hIB]
          exact Finset.mem_insert_self _ _
        · exact Finset.erase_insert (notMem_part_of_notMem hs P hI)
      · exact ⟨I, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hIB, hI⟩), hout I hI⟩
theorem extendPartition_bijective (hs : s ∉ A) :
    Function.Bijective fun p : (Σ P : Partitions A, Option {B // B ∈ P.parts}) =>
      extendPartition hs p.1 p.2 := by
  constructor
  · rintro ⟨P, o⟩ ⟨P₂, o₂⟩ h
    have h' : extendPartition hs P o = extendPartition hs P₂ o₂ := h
    have hP : P = P₂ := by
      apply Finpartition.ext
      rw [← parts_erase_of_extendPartition hs P o, ← parts_erase_of_extendPartition hs P₂ o₂, h']
    subst hP
    have hparts := congrArg Finpartition.parts h'
    have hnone : ∀ B₀ : {B // B ∈ P.parts}, {s} ∉ (insertIntoPart hs P B₀.1 B₀.2).parts := by
      intro B₀ hmem
      rcases Finset.mem_insert.1 hmem with h1 | h1
      · obtain ⟨x, hx⟩ := part_nonempty P B₀.2
        have hx' : x ∈ ({s} : Finset α) := h1 ▸ Finset.mem_insert_of_mem hx
        rw [Finset.mem_singleton] at hx'
        exact notMem_part_of_notMem hs P B₀.2 (hx' ▸ hx)
      · exact notMem_part_of_notMem hs P (Finset.mem_of_mem_erase h1) (Finset.mem_singleton_self s)
    cases o with
    | none =>
      cases o₂ with
      | none => rfl
      | some B₂ =>
        refine absurd ?_ (hnone B₂)
        have : {s} ∈ (addSingletonPart hs P).parts := Finset.mem_insert_self _ _
        exact hparts ▸ this
    | some B₁ =>
      cases o₂ with
      | none =>
        refine absurd ?_ (hnone B₁)
        have : {s} ∈ (addSingletonPart hs P).parts := Finset.mem_insert_self _ _
        exact hparts.symm ▸ this
      | some B₂ =>
        have hmem : insert s B₁.1 ∈ (insertIntoPart hs P B₂.1 B₂.2).parts := by
          have : insert s B₁.1 ∈ (insertIntoPart hs P B₁.1 B₁.2).parts :=
            Finset.mem_insert_self _ _
          exact hparts ▸ this
        rcases Finset.mem_insert.1 hmem with h1 | h1
        · have h2 := congrArg (fun I => I.erase s) h1
          simp only [Finset.erase_insert (notMem_part_of_notMem hs P B₁.2),
            Finset.erase_insert (notMem_part_of_notMem hs P B₂.2)] at h2
          rw [Subtype.ext h2]
        · exact absurd (Finset.mem_insert_self s B₁.1)
            (notMem_part_of_notMem hs P (Finset.mem_of_mem_erase h1))
  · intro P'
    have hsA : s ∈ insert s A := Finset.mem_insert_self _ _
    obtain ⟨B', hB', hsB'⟩ := (mem_iff_exists_part P' s).1 hsA
    by_cases hone : B' = {s}
    · subst hone
      let P : Partitions A := ofDisjointParts A (P'.parts.erase {s})
        (fun B hB I hI x hx hx' =>
          part_eq_of_mem_of_mem P' (Finset.mem_of_mem_erase hB) (Finset.mem_of_mem_erase hI)
            hx hx')
        (by
          intro x
          constructor
          · intro hx
            obtain ⟨B, hB, hxB⟩ := (mem_iff_exists_part P' x).1 (Finset.mem_insert_of_mem hx)
            refine ⟨B, Finset.mem_erase.2 ⟨?_, hB⟩, hxB⟩
            rintro rfl
            rw [Finset.mem_singleton] at hxB
            exact hs (hxB ▸ hx)
          · rintro ⟨B, hB, hxB⟩
            obtain ⟨hne, hB⟩ := Finset.mem_erase.1 hB
            rcases Finset.mem_insert.1 (P'.le hB hxB) with rfl | hx
            · exact absurd (part_eq_of_mem_of_mem P' hB hB' hxB (Finset.mem_singleton_self x)) hne
            · exact hx)
        (fun h => P'.bot_notMem (Finset.mem_of_mem_erase h))
      refine ⟨⟨P, none⟩, ?_⟩
      apply Finpartition.ext
      exact Finset.insert_erase hB'
    · have hB₀ : (B'.erase s).Nonempty := by
        obtain ⟨x, hx, hxs⟩ : ∃ x ∈ B', x ≠ s := by
          by_contra hc
          push Not at hc
          exact hone (Finset.eq_singleton_iff_unique_mem.2 ⟨hsB', hc⟩)
        exact ⟨x, Finset.mem_erase.2 ⟨hxs, hx⟩⟩
      have hnot : B'.erase s ∉ P'.parts.erase B' := by
        intro h
        obtain ⟨x, hx⟩ := hB₀
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 h
        exact hne (part_eq_of_mem_of_mem P' hmem hB' hx (Finset.mem_of_mem_erase hx))
      let P : Partitions A := ofDisjointParts A (insert (B'.erase s) (P'.parts.erase B'))
        (by
          have key : ∀ B ∈ P'.parts.erase B', ∀ x, x ∈ B'.erase s → x ∈ B → False := by
            intro B hB x hx hx'
            obtain ⟨hne, hB⟩ := Finset.mem_erase.1 hB
            exact hne (part_eq_of_mem_of_mem P' hB hB' hx' (Finset.mem_of_mem_erase hx))
          intro B hB I hI x hx hx'
          rcases Finset.mem_insert.1 hB with rfl | hB <;>
            rcases Finset.mem_insert.1 hI with rfl | hI
          · rfl
          · exact (key I hI x hx hx').elim
          · exact (key B hB x hx' hx).elim
          · exact part_eq_of_mem_of_mem P' (Finset.mem_of_mem_erase hB)
              (Finset.mem_of_mem_erase hI) hx hx')
        (by
          intro x
          constructor
          · intro hx
            have hxs : x ≠ s := fun h => hs (h ▸ hx)
            obtain ⟨B, hB, hxB⟩ := (mem_iff_exists_part P' x).1 (Finset.mem_insert_of_mem hx)
            by_cases hBB : B = B'
            · subst hBB
              exact ⟨_, Finset.mem_insert_self _ _, Finset.mem_erase.2 ⟨hxs, hxB⟩⟩
            · exact ⟨B, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hBB, hB⟩), hxB⟩
          · rintro ⟨B, hB, hxB⟩
            rcases Finset.mem_insert.1 hB with rfl | hB
            · obtain ⟨hxs, hx⟩ := Finset.mem_erase.1 hxB
              rcases Finset.mem_insert.1 (P'.le hB' hx) with h | h
              · exact absurd h hxs
              · exact h
            · obtain ⟨hne, hB⟩ := Finset.mem_erase.1 hB
              rcases Finset.mem_insert.1 (P'.le hB hxB) with rfl | h
              · exact absurd (part_eq_of_mem_of_mem P' hB hB' hxB hsB') hne
              · exact h)
        (by
          intro h
          rcases Finset.mem_insert.1 h with h | h
          · exact hB₀.ne_empty h.symm
          · exact P'.bot_notMem (Finset.mem_of_mem_erase h))
      have hmem : B'.erase s ∈ P.parts := Finset.mem_insert_self _ _
      refine ⟨⟨P, some ⟨B'.erase s, hmem⟩⟩, ?_⟩
      apply Finpartition.ext
      change insert (insert s (B'.erase s))
        ((insert (B'.erase s) (P'.parts.erase B')).erase (B'.erase s)) = P'.parts
      rw [Finset.insert_erase hsB', Finset.erase_insert hnot, Finset.insert_erase hB']
theorem sum_partitions_insert {M : Type*} [AddCommMonoid M] (hs : s ∉ A)
    (f : Partitions (insert s A) → M) :
    ∑ P', f P' = ∑ P : Partitions A,
      (f (addSingletonPart hs P) + ∑ B ∈ P.parts.attach, f (insertIntoPart hs P B.1 B.2)) := by
  rw [← (extendPartition_bijective hs).sum_comp f, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Fintype.sum_option]
  rfl
end Blocks
section Analysis
variable {n : ℕ}
abbrev coordLine (z : ComplexCoordinates n) (j : Fin n) (ζ : ℂ) : ComplexCoordinates n :=
  z + ζ • ComplexCoordinates.stdBasisVector j
theorem coordLine_zero (z : ComplexCoordinates n) (j : Fin n) : coordLine z j 0 = z := by
  simp [coordLine]
theorem hasDerivAt_coordLine {U : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ}
    {j : Fin n} (h : HasPartialDeriv U F j) {z : ComplexCoordinates n} (hz : z ∈ U) :
    HasDerivAt (fun ζ => F (coordLine z j ζ)) (partialDeriv j F z) 0 := by
  obtain ⟨l, hl⟩ := h.2 z hz
  have hv : partialDeriv j F z = l := hl.limUnder_eq
  rw [hv, hasDerivAt_iff_tendsto_slope_zero]
  refine hl.congr fun ζ => ?_
  simp [diffQuot, coordLine]
theorem partialDeriv_eq_of_hasDerivAt {F : ComplexCoordinates n → ℂ} {j : Fin n}
    {z : ComplexCoordinates n} {l : ℂ} (h : HasDerivAt (fun ζ => F (coordLine z j ζ)) l 0) :
    partialDeriv j F z = l := by
  refine Tendsto.limUnder_eq (h.tendsto_slope_zero.congr fun ζ => ?_)
  simp [diffQuot, coordLine]
theorem differentiableOn_of_isHolomorphicVia {W : Set ℂ} {η : ℂ → ℂ}
    (h : ComplexCoordinates.IsHolomorphicVia (Equiv.funUnique (Fin 1) ℂ).symm
      (Equiv.funUnique (Fin 1) ℂ).symm W η) : DifferentiableOn ℂ η W := by
  intro w hw
  obtain ⟨-, -, hd⟩ := h
  have h0 := (hd ((Equiv.funUnique (Fin 1) ℂ).symm w) ⟨w, hw, rfl⟩ 0).self_of_nhds
  have h1 : DifferentiableAt ℂ (fun ζ : ℂ => η (w + ζ)) 0 := by
    have h2 := differentiableAt_pi.1 h0 0
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun ζ => ?_)
    simp [ComplexCoordinates.stdBasisVector]
  have h3 : DifferentiableAt ℂ (fun ζ : ℂ => η (w + ζ)) ((fun x : ℂ => x - w) w) := by
    simpa using h1
  have h4 : DifferentiableAt ℂ (fun x : ℂ => x - w) w := by fun_prop
  have h5 := DifferentiableAt.comp (g := fun ζ : ℂ => η (w + ζ)) (f := fun x : ℂ => x - w) w h3 h4
  have h6 : ((fun ζ : ℂ => η (w + ζ)) ∘ fun x : ℂ => x - w) = η := by
    funext x
    simp
  rw [h6] at h5
  exact h5.differentiableWithinAt
theorem differentiableOn_iteratedDeriv_of_isOpen {W : Set ℂ} {η : ℂ → ℂ} (hW : IsOpen W)
    (h : DifferentiableOn ℂ η W) (k : ℕ) : DifferentiableOn ℂ (iteratedDeriv k η) W := by
  induction k with
  | zero => simpa [iteratedDeriv_zero] using h
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv hW
theorem partialOverFinset_singleton_eq (s : Fin n) (F : ComplexCoordinates n → ℂ) :
    partialOverFinset {s} F = partialDeriv s F := by
  simp [partialOverFinset, iteratedPartials]
def partitionTerm {A : Finset (Fin n)} (η : ℂ → ℂ) (V : ComplexCoordinates n → ℂ)
    (P : Partitions A) (z : ComplexCoordinates n) : ℂ :=
  iteratedDeriv (blockCount P) η (V z) * ∏ B ∈ P.parts, partialOverFinset B V z
theorem hasDerivAt_partitionTerm {U : Set (ComplexCoordinates n)} {W : Set ℂ}
    {V : ComplexCoordinates n → ℂ} {η : ℂ → ℂ} (hW : IsOpen W) (hmaps : Set.MapsTo V U W)
    (hη : DifferentiableOn ℂ η W)
    (hVs : ∀ j, HasPartialDeriv U V j)
    (hVB : ∀ (B : Finset (Fin n)) (j : Fin n), HasPartialDeriv U (partialOverFinset B V) j)
    (hVins : ∀ (B : Finset (Fin n)) (s : Fin n), s ∉ B →
      Set.EqOn (partialDeriv s (partialOverFinset B V)) (partialOverFinset (insert s B) V) U)
    {A : Finset (Fin n)} {s : Fin n} (hs : s ∉ A) (P : Partitions A)
    {z : ComplexCoordinates n} (hz : z ∈ U) :
    HasDerivAt (fun ζ => partitionTerm η V P (coordLine z s ζ))
      (iteratedDeriv (blockCount P + 1) η (V z) * partialDeriv s V z *
          ∏ B ∈ P.parts, partialOverFinset B V z +
        iteratedDeriv (blockCount P) η (V z) *
          ∑ B ∈ P.parts, (∏ B' ∈ P.parts.erase B, partialOverFinset B' V z) *
            partialOverFinset (insert s B) V z) 0 := by
  have hd : HasDerivAt (iteratedDeriv (blockCount P) η)
      (iteratedDeriv (blockCount P + 1) η (V z)) (V z) := by
    rw [iteratedDeriv_succ]
    exact ((differentiableOn_iteratedDeriv_of_isOpen hW hη _).differentiableAt
      (hW.mem_nhds (hmaps hz))).hasDerivAt
  have h1 : HasDerivAt (fun ζ => iteratedDeriv (blockCount P) η (V (coordLine z s ζ)))
      (iteratedDeriv (blockCount P + 1) η (V z) * partialDeriv s V z) 0 := by
    have hd' : HasDerivAt (iteratedDeriv (blockCount P) η)
        (iteratedDeriv (blockCount P + 1) η (V z)) ((fun ζ => V (coordLine z s ζ)) 0) := by
      simp only [coordLine_zero]
      exact hd
    exact HasDerivAt.comp (h₂ := iteratedDeriv (blockCount P) η)
      (h := fun ζ => V (coordLine z s ζ)) 0 hd' (hasDerivAt_coordLine (hVs s) hz)
  have h2 : HasDerivAt (fun ζ => ∏ B ∈ P.parts, partialOverFinset B V (coordLine z s ζ))
      (∑ B ∈ P.parts, (∏ B' ∈ P.parts.erase B, partialOverFinset B' V z) *
        partialOverFinset (insert s B) V z) 0 := by
    have h3 := HasDerivAt.fun_finsetProd (u := P.parts)
      (f := fun B ζ => partialOverFinset B V (coordLine z s ζ))
      (f' := fun B => partialOverFinset (insert s B) V z) (x := 0) (fun B hB => by
        have h4 := hasDerivAt_coordLine (hVB B s) hz
        rwa [hVins B s (notMem_part_of_notMem hs P hB) hz] at h4)
    simpa only [coordLine_zero, smul_eq_mul] using h3
  have h5 := h1.mul h2
  simp only [coordLine_zero] at h5
  exact h5
theorem partialOverFinset_comp_eq_sum {U : Set (ComplexCoordinates n)} {W : Set ℂ}
    {V : ComplexCoordinates n → ℂ} {η : ℂ → ℂ} (hU : IsOpen U) (hW : IsOpen W)
    (hmaps : Set.MapsTo V U W) (hη : DifferentiableOn ℂ η W)
    (hVs : ∀ j, HasPartialDeriv U V j)
    (hVB : ∀ (B : Finset (Fin n)) (j : Fin n), HasPartialDeriv U (partialOverFinset B V) j)
    (hVins : ∀ (B : Finset (Fin n)) (s : Fin n), s ∉ B →
      Set.EqOn (partialDeriv s (partialOverFinset B V)) (partialOverFinset (insert s B) V) U)
    (hcins : ∀ (B : Finset (Fin n)) (s : Fin n), s ∉ B →
      Set.EqOn (partialDeriv s (partialOverFinset B (η ∘ V)))
        (partialOverFinset (insert s B) (η ∘ V)) U)
    (A : Finset (Fin n)) :
    ∀ z ∈ U, partialOverFinset A (η ∘ V) z = ∑ P : Partitions A, partitionTerm η V P z := by
  induction A using Finset.induction_on with
  | empty =>
    intro z _
    have : Unique (Partitions (∅ : Finset (Fin n))) :=
      inferInstanceAs (Unique (Finpartition (⊥ : Finset (Fin n))))
    have hempty : ∀ P : Partitions (∅ : Finset (Fin n)), P.parts = ∅ := fun P =>
      Finpartition.parts_eq_empty_iff.2 rfl
    rw [Fintype.sum_unique]
    simp [partitionTerm, blockCount, hempty, partialOverFinset, iteratedPartials]
  | insert s A hs ih =>
    intro z hz
    rw [← hcins A s hs hz]
    have hderiv := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Partitions A)))
      (fun P _ => hasDerivAt_partitionTerm hW hmaps hη hVs hVB hVins hs P hz)
    have hev : (fun ζ => partialOverFinset A (η ∘ V) (coordLine z s ζ)) =ᶠ[𝓝 0]
        fun ζ => ∑ P : Partitions A, partitionTerm η V P (coordLine z s ζ) := by
      have hc : ContinuousAt (fun ζ : ℂ => coordLine z s ζ) 0 := by
        unfold coordLine
        fun_prop
      have hmem : U ∈ 𝓝 (coordLine z s 0) := by
        rw [coordLine_zero]
        exact hU.mem_nhds hz
      filter_upwards [hc hmem] with ζ hζ using ih _ hζ
    rw [partialDeriv_eq_of_hasDerivAt (hderiv.congr_of_eventuallyEq hev),
      sum_partitions_insert hs (fun P' => partitionTerm η V P' z)]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hown : partitionTerm η V (addSingletonPart hs P) z =
        iteratedDeriv (blockCount P + 1) η (V z) * partialDeriv s V z *
          ∏ B ∈ P.parts, partialOverFinset B V z := by
      have hnot : ({s} : Finset (Fin n)) ∉ P.parts := fun h =>
        notMem_part_of_notMem hs P h (Finset.mem_singleton_self s)
      have hparts : (addSingletonPart hs P).parts = insert {s} P.parts := rfl
      have hcard : blockCount (addSingletonPart hs P) = blockCount P + 1 := by
        rw [blockCount, hparts, Finset.card_insert_of_notMem hnot]
        rfl
      rw [partitionTerm, hcard, hparts, Finset.prod_insert hnot, partialOverFinset_singleton_eq,
        mul_assoc]
    have hjoin : ∀ B : {B // B ∈ P.parts}, partitionTerm η V (insertIntoPart hs P B.1 B.2) z =
        iteratedDeriv (blockCount P) η (V z) *
          ((∏ B' ∈ P.parts.erase B.1, partialOverFinset B' V z) *
            partialOverFinset (insert s B.1) V z) := by
      intro B
      have hnot : insert s B.1 ∉ P.parts.erase B.1 := fun h =>
        notMem_part_of_notMem hs P (Finset.mem_of_mem_erase h) (Finset.mem_insert_self _ _)
      have hparts : (insertIntoPart hs P B.1 B.2).parts =
          insert (insert s B.1) (P.parts.erase B.1) := rfl
      have hcard : blockCount (insertIntoPart hs P B.1 B.2) = blockCount P := by
        rw [blockCount, hparts, Finset.card_insert_of_notMem hnot,
          Finset.card_erase_add_one B.2]
        rfl
      rw [partitionTerm, hcard, hparts, Finset.prod_insert hnot,
        mul_comm (partialOverFinset (insert s B.1) V z)]
    rw [hown, Finset.sum_congr rfl fun B _ => hjoin B,
      Finset.sum_attach P.parts fun B => iteratedDeriv (blockCount P) η (V z) *
        ((∏ B' ∈ P.parts.erase B, partialOverFinset B' V z) * partialOverFinset (insert s B) V z),
      Finset.mul_sum]
end Analysis
theorem partitionChainRule_of_standardFacts
    (h : ComplexVariables.HolomorphicFacts.StandardFacts) : PartitionChainRule := by
  intro q hq U W V η hU hW hmaps hV hηh A _
  have hη := differentiableOn_of_isHolomorphicVia hηh
  obtain ⟨hPD, -, hChain, -⟩ := h q hq U hU
  have hcomp : IsHolomorphicScalar U (η ∘ V) := (hChain W V η hW hV hmaps hη).1
  obtain ⟨hV1, -, hV3, -, -, -, hV7, -⟩ := hPD V hV
  obtain ⟨-, -, hc3, -, -, -, hc7, -⟩ := hPD _ hcomp
  refine ⟨(hc3 A).1, fun P B _ => (hV3 B).1, fun z hz => ?_⟩
  exact partialOverFinset_comp_eq_sum hU hW hmaps hη (fun j => (hV1 j).1)
    (fun B j => ((hPD _ (hV3 B).2).1 j).1) hV7 hc7 A z hz
end YangMills.Construction.CompositeDerivative
