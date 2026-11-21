import YangMills.Construction.ClusterExpansionOfAStep.LocalityOfTheKernelProof
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ClusterExpansionOfAStep.BlocksReadTheirBoxesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ContourOffsets
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.TorusLumps YangMills.Construction.TorusContours
section Paths
def intStep (st : PathStep) : Fin 4 → ℤ := if st.2 then Pi.single st.1 1 else -Pi.single st.1 1
def offsetPath : (Fin 4 → ℤ) → List PathStep → List (Fin 4 → ℤ)
  | u, [] => [u]
  | u, st :: r => u :: offsetPath (u + intStep st) r
def offsetEnd : (Fin 4 → ℤ) → List PathStep → (Fin 4 → ℤ)
  | u, [] => u
  | u, st :: r => offsetEnd (u + intStep st) r
theorem offsetEnd_append (u : Fin 4 → ℤ) (l l' : List PathStep) :
    offsetEnd u (l ++ l') = offsetEnd (offsetEnd u l) l' := by
  induction l generalizing u with
  | nil => rfl
  | cons st r ih => exact ih _
theorem mem_offsetPath_self (u : Fin 4 → ℤ) (l : List PathStep) : u ∈ offsetPath u l := by
  cases l <;> simp [offsetPath]
theorem mem_offsetPath_append {u p : Fin 4 → ℤ} {l l' : List PathStep} (h : p ∈ offsetPath u (l ++ l')) :
    p ∈ offsetPath u l ∨ p ∈ offsetPath (offsetEnd u l) l' := by
  induction l generalizing u with
  | nil => exact Or.inr h
  | cons st r ih =>
    simp only [List.cons_append, offsetPath, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inl (by simp [offsetPath])
    · rcases ih h with h | h
      · exact Or.inl (by simp [offsetPath, h])
      · exact Or.inr h
theorem intStep_flip (st : PathStep) : intStep (st.1, !st.2) = - intStep st := by
  rcases st with ⟨i, b⟩
  cases b <;> simp [intStep]
theorem offsetEnd_reversePath (u : Fin 4 → ℤ) (l : List PathStep) :
    offsetEnd (offsetEnd u l) (reversePath l) = u := by
  induction l generalizing u with
  | nil => rfl
  | cons st r ih =>
    have : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    rw [this, offsetEnd_append]
    simp only [offsetEnd]
    rw [ih, intStep_flip]
    simp
theorem mem_offsetPath_of_reversePath {v p : Fin 4 → ℤ} {l : List PathStep}
    (h : p ∈ offsetPath (offsetEnd v l) (reversePath l)) : p ∈ offsetPath v l := by
  induction l generalizing v with
  | nil => exact h
  | cons st r ih =>
    have hr : reversePath (st :: r) = reversePath r ++ [(st.1, !st.2)] := by
      simp [reversePath]
    rw [hr] at h
    simp only [offsetEnd] at h
    rcases mem_offsetPath_append h with h | h
    · exact List.mem_cons_of_mem _ (ih h)
    · rw [offsetEnd_reversePath] at h
      simp only [offsetPath, intStep_flip, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · simp [offsetPath, mem_offsetPath_self]
      · simp [offsetPath]
def InBox (lo hi u : Fin 4 → ℤ) : Prop := ∀ k, lo k ≤ u k ∧ u k ≤ hi k
def partialShift (u h : Fin 4 → ℤ) (S : Finset (Fin 4)) : Fin 4 → ℤ := fun k => u k + if k ∈ S then h k else 0
theorem replicate_inBox {lo hi : Fin 4 → ℤ} (a : Fin 4) (b : Bool) :
    ∀ (m : ℕ) (u : Fin 4 → ℤ), InBox lo hi u →
      InBox lo hi (u + (m : ℤ) • intStep (a, b)) →
      (∀ p ∈ offsetPath u (List.replicate m (a, b)), InBox lo hi p) ∧
        offsetEnd u (List.replicate m (a, b)) = u + (m : ℤ) • intStep (a, b) := by
  intro m
  induction m with
  | zero =>
    intro u hu _
    simp [offsetPath, offsetEnd, hu]
  | succ m ih =>
    intro u hu hv
    have hs : InBox lo hi (u + intStep (a, b)) := by
      intro k
      have h1 := hu k
      have h2 := hv k
      by_cases hk : k = a
      · subst hk
        cases b <;> simp [intStep] at h2 ⊢ <;> omega
      · cases b <;> simp [intStep, hk] at h2 ⊢ <;> omega
    have he : u + intStep (a, b) + (m : ℤ) • intStep (a, b) = u + ((m + 1 : ℕ) : ℤ) • intStep (a, b) := by
      push_cast
      rw [add_smul, one_smul]
      abel
    obtain ⟨h1, h2⟩ := ih (u + intStep (a, b)) hs (he ▸ hv)
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [List.replicate_succ, offsetPath, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hu
      · exact h1 p hp
    · simp only [List.replicate_succ, offsetEnd]
      rw [h2, he]
theorem natAbs_smul_intStep (a : Fin 4) (c : ℤ) :
    ((c.natAbs : ℤ)) • intStep (a, decide (0 ≤ c)) = Pi.single a c := by apply _root_.YangMills.Construction.BlockLocality.natAbs_smul_stepOffset <;> assumption
theorem flatMap_legs_inBox {lo hi u h : Fin 4 → ℤ} (hu : InBox lo hi u) (hv : InBox lo hi (u + h))
    (π : Equiv.Perm (Fin 4)) :
    ∀ (ks : List (Fin 4)) (S : Finset (Fin 4)), ks.Nodup → (∀ k ∈ ks, π k ∉ S) →
      (∀ p ∈ offsetPath (partialShift u h S)
          (ks.flatMap fun k => List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))), InBox lo hi p) ∧
        offsetEnd (partialShift u h S)
            (ks.flatMap fun k => List.replicate (h (π k)).natAbs (π k, decide (0 ≤ h (π k)))) =
          partialShift u h (S ∪ (ks.map π).toFinset) := by
  have hpart : ∀ S, InBox lo hi (partialShift u h S) := by
    intro S k
    have h1 := hu k
    have h2 := hv k
    simp only [Pi.add_apply] at h2
    simp only [partialShift]
    split_ifs <;> omega
  intro ks
  induction ks with
  | nil =>
    intro S _ _
    simp only [List.flatMap_nil, offsetEnd, offsetPath, List.mem_singleton, List.map_nil, List.toFinset_nil,
      Finset.union_empty]
    exact ⟨fun p hp => hp ▸ hpart S, trivial⟩
  | cons a r ih =>
    intro S hnd hS
    obtain ⟨hna, hnr⟩ := List.nodup_cons.mp hnd
    have haS : π a ∉ S := hS a (List.mem_cons_self)
    have hend : partialShift u h S + ((h (π a)).natAbs : ℤ) • intStep (π a, decide (0 ≤ h (π a))) =
        partialShift u h (insert (π a) S) := by
      rw [natAbs_smul_intStep]
      funext k
      by_cases hk : k = π a
      · subst hk
        simp [partialShift, haS]
      · simp [partialShift, hk]
    obtain ⟨h1, h2⟩ := replicate_inBox (lo := lo) (hi := hi) (π a) (decide (0 ≤ h (π a))) (h (π a)).natAbs
      (partialShift u h S) (hpart S) (hend ▸ hpart _)
    have hS' : ∀ k ∈ r, π k ∉ insert (π a) S := by
      intro k hk hmem
      rcases Finset.mem_insert.mp hmem with he | he
      · exact hna (π.injective he ▸ hk)
      · exact hS k (List.mem_cons_of_mem _ hk) he
    obtain ⟨h3, h4⟩ := ih (insert (π a) S) hnr hS'
    simp only [List.flatMap_cons]
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases mem_offsetPath_append hp with hp | hp
      · exact h1 p hp
      · rw [h2, hend] at hp
        exact h3 p hp
    · rw [offsetEnd_append, h2, hend, h4]
      congr 1
      ext k
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_map, List.map_cons,
        List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
theorem axisPath_inBox {lo hi u h : Fin 4 → ℤ} (hu : InBox lo hi u) (hv : InBox lo hi (u + h))
    (π : Equiv.Perm (Fin 4)) :
    (∀ p ∈ offsetPath u (axisPath h π), InBox lo hi p) ∧ offsetEnd u (axisPath h π) = u + h := by
  have h0 : partialShift u h ∅ = u := by
    funext k
    simp [partialShift]
  have := flatMap_legs_inBox hu hv π (List.finRange 4) ∅ (List.nodup_finRange 4) (by simp)
  rw [h0] at this
  refine ⟨this.1, this.2.trans ?_⟩
  funext k
  have : k ∈ ((List.finRange 4).map π).toFinset := by
    simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and]
    exact ⟨π.symm k, by simp⟩
  simp [partialShift, this]
def contourSteps (L : ℕ) (z₀ z₁ ξ : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)) (i : Fin 4) : List PathStep :=
  axisPath (ξ - z₀) π ++ List.replicate L (i, true) ++ reversePath (axisPath (ξ - z₁) π)
def slabLower (L : ℕ) : Fin 4 → ℤ := fun _ => -(((L : ℤ) - 1) / 2)
def slabUpper (L : ℕ) (i : Fin 4) : Fin 4 → ℤ :=
  fun k => ((L : ℤ) - 1) / 2 + (Pi.single i (L : ℤ) : Fin 4 → ℤ) k
abbrev InSlab (L : ℕ) (i : Fin 4) (u : Fin 4 → ℤ) : Prop := InBox (slabLower L) (slabUpper L i) u
theorem contourSteps_inSlab {L : ℕ} {z₀ z₁ ξ : Fin 4 → ℤ} (h₀ : z₀ ∈ centredCube L) (h₁ : z₁ ∈ centredCube L)
    (hξ : ξ ∈ centredCube L) (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    ∀ p ∈ offsetPath z₀ (contourSteps L z₀ z₁ ξ π i), InSlab L i p := by
  have hc : ∀ {z : Fin 4 → ℤ}, z ∈ centredCube L → ∀ k, -(((L : ℤ) - 1) / 2) ≤ z k ∧ z k ≤ ((L : ℤ) - 1) / 2 :=
    fun h => mem_centredCube_iff.mp h
  have hLn : (0 : ℤ) ≤ L := by positivity
  have hsi : ∀ k, (0 : ℤ) ≤ (Pi.single i (L : ℤ) : Fin 4 → ℤ) k := by
    intro k
    by_cases hk : k = i
    · subst hk
      simpa using hLn
    · simp [hk]
  have hbox : ∀ {z : Fin 4 → ℤ}, z ∈ centredCube L → InSlab L i z := by
    intro z hz k
    have h1 := hc hz k
    have h2 := hsi k
    simp only [slabLower, slabUpper]
    constructor <;> omega
  have hshift : ∀ {z : Fin 4 → ℤ}, z ∈ centredCube L → InSlab L i (z + Pi.single i (L : ℤ)) := by
    intro z hz k
    have h1 := hc hz k
    have h2 := hsi k
    simp only [Pi.add_apply, slabLower, slabUpper]
    constructor <;> omega
  obtain ⟨a₁, a₂⟩ := axisPath_inBox (hbox h₀) (by simpa using hbox hξ) π (h := ξ - z₀)
  have hend₀ : z₀ + (ξ - z₀) = ξ := by abel
  rw [hend₀] at a₂
  have hrep : (L : ℤ) • intStep (i, true) = Pi.single i (L : ℤ) := by
    have := natAbs_smul_intStep i (L : ℤ)
    simpa using this
  obtain ⟨b₁, b₂⟩ := replicate_inBox (lo := slabLower L) (hi := slabUpper L i) i true L ξ (hbox hξ)
    (by rw [hrep]; exact hshift hξ)
  rw [hrep] at b₂
  have hend₁ : z₁ + Pi.single i (L : ℤ) + (ξ - z₁) = ξ + Pi.single i (L : ℤ) := by abel
  obtain ⟨c₁, c₂⟩ := axisPath_inBox (u := z₁ + Pi.single i (L : ℤ)) (h := ξ - z₁) (hshift h₁)
    (by rw [hend₁]; exact hshift hξ) π
  rw [hend₁] at c₂
  intro p hp
  unfold contourSteps at hp
  rcases mem_offsetPath_append hp with hp | hp
  · rcases mem_offsetPath_append hp with hp | hp
    · exact a₁ p hp
    · rw [a₂] at hp
      exact b₁ p hp
  · rw [offsetEnd_append, a₂, b₂, ← c₂] at hp
    exact c₁ p (mem_offsetPath_of_reversePath hp)
end Paths
section Contours
variable {F F' : BlockFrame} [∀ j i, NeZero (F.period j i)] [∀ j i, NeZero (F'.period j i)]
theorem siteAtOffset_add_stepDisplacement (y : F.Cell) (u : Fin 4 → ℤ) (st : PathStep) :
    (siteAtOffset y u : F.Site F.depth) + stepDisplacement F.depth st = siteAtOffset y (u + intStep st) := by apply _root_.YangMills.Construction.BlockLocality.siteAtOffset_add_stepDisplacement <;> assumption
theorem pathHolonomy_eq_of_agree (P : (Fin 4 → ℤ) → Prop) (X : F.GaugeField F.depth)
    (X' : F'.GaugeField F'.depth) (y : F.Cell) (y' : F'.Cell)
    (hag : ∀ (u : Fin 4 → ℤ) (i : Fin 4), P u → P (u + Pi.single i 1) →
      X (siteAtOffset y u) i = X' (siteAtOffset y' u) i) (l : List PathStep) (u : Fin 4 → ℤ)
    (hp : ∀ p ∈ offsetPath u l, P p) :
    pathHolonomy X (siteAtOffset y u) l = pathHolonomy X' (siteAtOffset y' u) l := by
  induction l generalizing u with
  | nil => rfl
  | cons st r ih =>
    simp only [pathHolonomy]
    rw [siteAtOffset_add_stepDisplacement, siteAtOffset_add_stepDisplacement]
    have h1 : P u := hp u (by simp [offsetPath])
    have h2 : P (u + intStep st) := hp _ (by simp [offsetPath, mem_offsetPath_self])
    rw [ih _ fun p hq => hp p (by simp [offsetPath, hq])]
    congr 1
    rcases st with ⟨i, b⟩
    cases b
    · have h3 : P (u - Pi.single i 1) := by simpa [intStep, sub_eq_add_neg] using h2
      have h4 := hag (u - Pi.single i 1) i h3 (by simpa using h1)
      have e1 : (siteAtOffset y u : F.Site F.depth) - unitStep F.depth i = siteAtOffset y (u - Pi.single i 1) := by
        simp [siteAtOffset, unitStep, sub_eq_add_neg, _root_.YangMills.Construction.TorusContours.siteOfCoords_add, _root_.YangMills.Construction.TorusContours.siteOfCoords_neg, add_assoc]
      have e2 : (siteAtOffset y' u : F'.Site F'.depth) - unitStep F'.depth i =
          siteAtOffset y' (u - Pi.single i 1) := by
        simp [siteAtOffset, unitStep, sub_eq_add_neg, _root_.YangMills.Construction.TorusContours.siteOfCoords_add, _root_.YangMills.Construction.TorusContours.siteOfCoords_neg, add_assoc]
      simp only [linkValue, Bool.false_eq_true, if_false, e1, e2, h4]
    · have h4 := hag u i h1 (by simpa [intStep] using h2)
      simp only [linkValue, if_true, h4]
theorem siteAtOffset_shift (y : F.Cell) (i : Fin 4) (v : Fin 4 → ℤ) :
    (siteAtOffset (y + unitStep F.top i) v : F.Site F.depth) = siteAtOffset y (v + Pi.single i (F.blockSide : ℤ)) := by apply _root_.YangMills.Construction.BlockLocality.siteAtOffset_add_unitStep <;> assumption
theorem valMinAbs_intCast_of_small {p : ℕ} [NeZero p] {z : ℤ} (h : 2 * |z| < (p : ℤ)) :
    ((z : ZMod p)).valMinAbs = z := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
theorem siteAtOffset_sub_apply (y : F.Cell) (u v : Fin 4 → ℤ) (i : Fin 4) :
    (siteAtOffset y u : F.Site F.depth) i - (siteAtOffset y v : F.Site F.depth) i =
      ((u i - v i : ℤ) : ZMod (F.period F.depth i)) := by
  rw [siteAtOffset_eq, siteAtOffset_eq]
  simp only [siteOfCoords]
  push_cast
  ring
theorem contourPath_eq_contourSteps (hbig : ∀ i, 2 * (F.blockSide : ℤ) ≤ (F.period F.depth i : ℤ))
    {b : F.Cell → F.Site F.depth} {y : F.Cell} {i : Fin 4} {z₀ z₁ ξ : Fin 4 → ℤ}
    (h₀ : z₀ ∈ centredCube F.blockSide) (h₁ : z₁ ∈ centredCube F.blockSide) (hξ : ξ ∈ centredCube F.blockSide)
    (hb₀ : b y = siteAtOffset y z₀) (hb₁ : b (y + unitStep F.top i) = siteAtOffset (y + unitStep F.top i) z₁)
    (π : Equiv.Perm (Fin 4)) : contourPath b (y, i) ξ π = contourSteps F.blockSide z₀ z₁ ξ π i := by
  have hoff : ∀ (y₁ : F.Cell) {z : Fin 4 → ℤ}, z ∈ centredCube F.blockSide →
      minimalOffset (siteAtOffset y₁ z : F.Site F.depth) (cellCentre F.depth y₁ + siteOfCoords F.depth ξ) =
        ξ - z := by
    intro y₁ z hz
    funext k
    have h1 := mem_centredCube_iff.mp hz k
    have h2 := mem_centredCube_iff.mp hξ k
    have h3 := hbig k
    show (((siteAtOffset y₁ ξ : F.Site F.depth) k - (siteAtOffset y₁ z : F.Site F.depth) k)).valMinAbs =
      ξ k - z k
    rw [siteAtOffset_sub_apply]
    refine valMinAbs_intCast_of_small ?_
    have h4 : |ξ k - z k| ≤ 2 * (((F.blockSide : ℤ) - 1) / 2) := by
      rw [abs_le]
      omega
    omega
  simp only [contourPath, contourSteps, hb₀, hb₁, hoff _ h₀, hoff _ h₁]
end Contours
end YangMills.Construction.ContourOffsets
end
