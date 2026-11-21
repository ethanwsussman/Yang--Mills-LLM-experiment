import YangMills.Construction.InfiniteLattice.BoxRepresentsTheTorusAndItsThinBoundaryLayerProof
import YangMills.Construction.InfiniteLattice.DataOfADiagonalPictureProof
import YangMills.Construction.InfiniteLattice.BondsAndCutPlaquettesAtAMirror
import YangMills.Construction.InfiniteLattice.ContinuousLocalFunctionsAreDenseAndTestMeasuresProof
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.PropertiesOfTheSixteenFamilies
import YangMills.Construction.TransferOperators.PeriodicGibbsStatesAreInvariantUnderLinkMirrors
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies.LevelCuts
open Matrices
open InfiniteLattice
open PeriodicLattice (coordVec)
theorem coe_axisStep (ρ : Fin 4) :
    ((axisStep 1 ρ : LatticePoint 1) : AmbientSpace) = coordVec ρ := rfl
theorem dotProduct_coordVec (v : AmbientSpace) (ρ : Fin 4) : v ⬝ᵥ coordVec ρ = v ρ := by
  simp [coordVec]
theorem coordVec_self (μ : Fin 4) : coordVec μ μ = 1 := by apply _root_.YangMills.Construction.LatticeConventions.DiagonalPictureExpansion.basisVector_apply_self <;> assumption
theorem coordVec_of_ne {μ ρ : Fin 4} (h : ρ ≠ μ) : coordVec μ ρ = 0 := by
  simp [coordVec, Pi.single_eq_of_ne h]
theorem linearHeight_coordVec (μ : Fin 4) (x : AmbientSpace) :
    linearHeight (coordVec μ) x = x μ := by apply _root_.YangMills.Construction.InfiniteLattice.BoxQuotient.coordVec_dotProduct <;> assumption
theorem linearHeight_add_axisStep (v : AmbientSpace) (x : LatticePoint 1) (ρ : Fin 4) :
    linearHeight v (x + axisStep 1 ρ : LatticePoint 1) = linearHeight v (x : LatticePoint 1) + v ρ := by
  simp only [linearHeight, AddSubgroup.coe_add, dotProduct_add, coe_axisStep, dotProduct_coordVec]
theorem normSq_coordVec (μ : Fin 4) : normSq (coordVec μ) = 1 := by apply _root_.YangMills.Construction.TransferOperators.normSq_coordVec <;> assumption
theorem normSq_coordVec_add {μ ν : Fin 4} (h : μ ≠ ν) :
    normSq (coordVec μ + coordVec ν) = 2 := by
  rw [normSq_eq_dotProduct]
  simp only [dotProduct_add, dotProduct_coordVec, Pi.add_apply, coordVec_self, coordVec_of_ne h,
    coordVec_of_ne h.symm]
  norm_num
theorem normSq_coordVec_sub {μ ν : Fin 4} (h : μ ≠ ν) :
    normSq (coordVec μ - coordVec ν) = 2 := by
  rw [normSq_eq_dotProduct]
  simp only [dotProduct_sub, dotProduct_coordVec, Pi.sub_apply, coordVec_self, coordVec_of_ne h,
    coordVec_of_ne h.symm]
  norm_num
theorem exists_eq_coordVec_of_normSq_ne_two {v : AmbientSpace} (hv : v ∈ normalSet)
    (hq : normSq v ≠ 2) : ∃ μ, v = coordVec μ := by
  rcases hv with h | ⟨μ, ν, hlt, rfl | rfl⟩
  · exact h
  · exact absurd (normSq_coordVec_add hlt.ne) hq
  · exact absurd (normSq_coordVec_sub hlt.ne) hq
theorem intCast_ne_add_half (k m : ℤ) : (m : ℝ) ≠ (k : ℝ) + 1 / 2 := by
  intro h
  have h₂ : (2 * m : ℝ) = 2 * k + 1 := by linarith
  have h₃ : 2 * m = 2 * k + 1 := by exact_mod_cast h₂
  omega
theorem mem_closedHalfSpace_pos {v : AmbientSpace} {c : ℝ} {x : AmbientSpace} :
    x ∈ closedHalfSpace v c 1 ↔ c ≤ linearHeight v x := by
  simp [closedHalfSpace, linearHeight]
theorem mem_closedHalfSpace_neg {v : AmbientSpace} {c : ℝ} {x : AmbientSpace} :
    x ∈ closedHalfSpace v c (-1) ↔ linearHeight v x ≤ c := by
  simp [closedHalfSpace, linearHeight]
theorem mem_halfSpaceLinks {v : AmbientSpace} {c : ℝ} {ε : ℤˣ} {b : Link 1} :
    b ∈ halfSpaceLinks 1 v c ε ↔
      b ∈ positiveLinks 1 ∧ (b.initial : AmbientSpace) ∈ closedHalfSpace v c ε ∧
        (b.terminal : AmbientSpace) ∈ closedHalfSpace v c ε := by
  simp only [halfSpaceLinks, LinksLieIn, mem_singleton_iff, forall_eq]
  exact Iff.rfl
theorem forwardFrom_mem_positiveLinks (x : LatticePoint 1) (ρ : Fin 4) :
    Link.forwardFrom x ρ ∈ positiveLinks 1 :=
  ⟨ρ, add_sub_cancel_left _ _⟩
theorem exists_eq_forwardFrom {b : Link 1} (hb : b ∈ positiveLinks 1) :
    ∃ ρ, b = Link.forwardFrom b.initial ρ := by
  obtain ⟨ρ, h⟩ := hb
  exact ⟨ρ, InfiniteLattice.Link.ext rfl (sub_eq_iff_eq_add'.mp h)⟩
theorem linkSet_subset_halfSpaceLinks_iff (p : ElementaryPlaquette 1) (v : AmbientSpace) (c : ℝ)
    (ε : ℤˣ) :
    p.linkSet ⊆ halfSpaceLinks 1 v c ε ↔
      ((p.corner : LatticePoint 1) : AmbientSpace) ∈ closedHalfSpace v c ε ∧
        ((p.corner + axisStep 1 p.lowAxis : LatticePoint 1) : AmbientSpace) ∈ closedHalfSpace v c ε ∧
        ((p.corner + axisStep 1 p.lowAxis + axisStep 1 p.highAxis : LatticePoint 1) : AmbientSpace) ∈
          closedHalfSpace v c ε ∧
        ((p.corner + axisStep 1 p.highAxis : LatticePoint 1) : AmbientSpace) ∈ closedHalfSpace v c ε := by
  have hcomm : p.corner + axisStep 1 p.highAxis + axisStep 1 p.lowAxis =
      p.corner + axisStep 1 p.lowAxis + axisStep 1 p.highAxis := add_right_comm _ _ _
  constructor
  · intro h
    have h₁ := mem_halfSpaceLinks.mp (h (show Link.forwardFrom p.corner p.lowAxis ∈ p.linkSet by
      simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges]))
    have h₂ := mem_halfSpaceLinks.mp (h (show Link.forwardFrom (p.corner + axisStep 1 p.lowAxis)
        p.highAxis ∈ p.linkSet by
      simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges]))
    have h₃ := mem_halfSpaceLinks.mp (h (show Link.forwardFrom p.corner p.highAxis ∈ p.linkSet by
      simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges]))
    exact ⟨h₁.2.1, h₁.2.2, h₂.2.2, h₃.2.2⟩
  · rintro ⟨h₀, h₁, h₂, h₃⟩ b hb
    change b ∈ p.edges at hb
    simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact mem_halfSpaceLinks.mpr ⟨forwardFrom_mem_positiveLinks _ _, h₀, h₁⟩
    · exact mem_halfSpaceLinks.mpr ⟨forwardFrom_mem_positiveLinks _ _, h₁, h₂⟩
    · refine mem_halfSpaceLinks.mpr ⟨forwardFrom_mem_positiveLinks _ _, h₃, ?_⟩
      change ((p.corner + axisStep 1 p.highAxis + axisStep 1 p.lowAxis : LatticePoint 1) :
        AmbientSpace) ∈ _
      rw [hcomm]
      exact h₂
    · exact mem_halfSpaceLinks.mpr ⟨forwardFrom_mem_positiveLinks _ _, h₀, h₃⟩
theorem isCutBy_iff_heights (p : ElementaryPlaquette 1) (v : AmbientSpace) (c : ℝ) :
    IsCutBy p v c ↔
      ¬ (c ≤ linearHeight v (p.corner : LatticePoint 1) ∧
          c ≤ linearHeight v (p.corner : LatticePoint 1) + v p.lowAxis ∧
          c ≤ linearHeight v (p.corner : LatticePoint 1) + v p.lowAxis + v p.highAxis ∧
          c ≤ linearHeight v (p.corner : LatticePoint 1) + v p.highAxis) ∧
        ¬ (linearHeight v (p.corner : LatticePoint 1) ≤ c ∧
          linearHeight v (p.corner : LatticePoint 1) + v p.lowAxis ≤ c ∧
          linearHeight v (p.corner : LatticePoint 1) + v p.lowAxis + v p.highAxis ≤ c ∧
          linearHeight v (p.corner : LatticePoint 1) + v p.highAxis ≤ c) := by
  rw [IsCutBy, linkSet_subset_halfSpaceLinks_iff, linkSet_subset_halfSpaceLinks_iff]
  simp only [mem_closedHalfSpace_pos, mem_closedHalfSpace_neg, linearHeight_add_axisStep]
theorem intCast_trichotomy (i k : ℤ) : (i : ℝ) + 1 ≤ k ∨ (i : ℝ) = k ∨ (k : ℝ) + 1 ≤ i := by
  rcases lt_trichotomy i k with h | h | h
  · left
    exact_mod_cast h
  · right
    left
    exact_mod_cast h
  · right
    right
    exact_mod_cast h
theorem not_straddle_of_axis_zero {t c a₁ a₂ : ℝ} (ht : ∃ i : ℤ, t = i) (hc : ∃ k : ℤ, c = k)
    (h₁ : a₁ = 0 ∨ a₁ = 1 ∨ a₁ = -1) (h₂ : a₂ = 0 ∨ a₂ = 1 ∨ a₂ = -1) (h₀ : a₁ = 0 ∨ a₂ = 0) :
    ¬ (¬ (c ≤ t ∧ c ≤ t + a₁ ∧ c ≤ t + a₁ + a₂ ∧ c ≤ t + a₂) ∧
      ¬ (t ≤ c ∧ t + a₁ ≤ c ∧ t + a₁ + a₂ ≤ c ∧ t + a₂ ≤ c)) := by
  obtain ⟨i, rfl⟩ := ht
  obtain ⟨k, rfl⟩ := hc
  rintro ⟨hA, hB⟩
  have hi := intCast_trichotomy i k
  rcases h₀ with rfl | rfl
  · rcases h₂ with rfl | rfl | rfl <;> rcases hi with hi | hi | hi <;>
      first
      | exact hA ⟨by linarith, by linarith, by linarith, by linarith⟩
      | exact hB ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rcases h₁ with rfl | rfl | rfl <;> rcases hi with hi | hi | hi <;>
      first
      | exact hA ⟨by linarith, by linarith, by linarith, by linarith⟩
      | exact hB ⟨by linarith, by linarith, by linarith, by linarith⟩
theorem straddle_iff_axis {t c a₁ a₂ : ℝ} (ht : ∃ i : ℤ, t = i) (hc : ∃ k : ℤ, c = (k : ℝ) + 1 / 2)
    (ha : (a₁ = 1 ∧ a₂ = 0) ∨ (a₁ = 0 ∧ a₂ = 1)) :
    (¬ (c ≤ t ∧ c ≤ t + a₁ ∧ c ≤ t + a₁ + a₂ ∧ c ≤ t + a₂) ∧
      ¬ (t ≤ c ∧ t + a₁ ≤ c ∧ t + a₁ + a₂ ≤ c ∧ t + a₂ ≤ c)) ↔ t = c - 1 / 2 := by
  obtain ⟨i, rfl⟩ := ht
  obtain ⟨k, rfl⟩ := hc
  have hi := intCast_trichotomy i k
  constructor
  · rintro ⟨hA, hB⟩
    rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hi with hi | hi | hi <;>
      first
      | linarith
      | exact (hA ⟨by linarith, by linarith, by linarith, by linarith⟩).elim
      | exact (hB ⟨by linarith, by linarith, by linarith, by linarith⟩).elim
  · intro e
    rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> constructor <;> rintro ⟨a₁, a₂, a₃, a₄⟩ <;> linarith
theorem straddle_iff_of_sub {t c : ℝ} (ht : ∃ i : ℤ, t = i) (hc : ∃ k : ℤ, c = k) :
    (¬ (c ≤ t ∧ c ≤ t + 1 ∧ c ≤ t + 1 + -1 ∧ c ≤ t + -1) ∧
      ¬ (t ≤ c ∧ t + 1 ≤ c ∧ t + 1 + -1 ≤ c ∧ t + -1 ≤ c)) ↔ t = c := by
  obtain ⟨i, rfl⟩ := ht
  obtain ⟨k, rfl⟩ := hc
  have hi := intCast_trichotomy i k
  constructor
  · rintro ⟨hA, hB⟩
    rcases hi with hi | hi | hi
    · exact (hB ⟨by linarith, by linarith, by linarith, by linarith⟩).elim
    · exact hi
    · exact (hA ⟨by linarith, by linarith, by linarith, by linarith⟩).elim
  · intro e
    constructor <;> rintro ⟨a₁, a₂, a₃, a₄⟩ <;> linarith
theorem straddle_iff_of_add {t c : ℝ} (ht : ∃ i : ℤ, t = i) (hc : ∃ k : ℤ, c = k) :
    (¬ (c ≤ t ∧ c ≤ t + 1 ∧ c ≤ t + 1 + 1 ∧ c ≤ t + 1) ∧
      ¬ (t ≤ c ∧ t + 1 ≤ c ∧ t + 1 + 1 ≤ c ∧ t + 1 ≤ c)) ↔ t = c - 1 := by
  obtain ⟨i, rfl⟩ := ht
  obtain ⟨k, rfl⟩ := hc
  have hi := intCast_trichotomy (i + 1) k
  push_cast at hi
  constructor
  · rintro ⟨hA, hB⟩
    rcases hi with hi | hi | hi
    · exact (hB ⟨by linarith, by linarith, by linarith, by linarith⟩).elim
    · linarith
    · exact (hA ⟨by linarith, by linarith, by linarith, by linarith⟩).elim
  · intro e
    constructor <;> rintro ⟨a₁, a₂, a₃, a₄⟩ <;> linarith
theorem reflectAcross_of_linearHeight_eq {v : AmbientSpace} {c : ℝ} {x : AmbientSpace}
    (h : linearHeight v x = c) : reflectAcross v c x = x := by
  have h₀ : v ⬝ᵥ x - c = 0 := sub_eq_zero.mpr h
  simp [reflectAcross, h₀]
theorem reflectAcross_of_half_below {v : AmbientSpace} {c : ℝ} {μ : Fin 4} (hμ : v = coordVec μ)
    {x : AmbientSpace} (h : linearHeight v x = c - 1 / 2) :
    reflectAcross v c x = x + coordVec μ := by
  have h₀ : 2 * (v ⬝ᵥ x - c) = -1 := by
    have h₁ : v ⬝ᵥ x = c - 1 / 2 := h
    rw [h₁]
    ring
  have hs : dualVector v = coordVec μ := by
    rw [dualVector, hμ, normSq_coordVec, inv_one, one_smul]
  rw [reflectAcross, h₀, hs, neg_smul, one_smul, sub_neg_eq_add]
theorem reflectAcross_of_one_above {v : AmbientSpace} {c : ℝ} (hq : normSq v = 2) {x : AmbientSpace}
    (h : linearHeight v x = c + 1) : reflectAcross v c x = x - v := by
  have h₀ : 2 * (v ⬝ᵥ x - c) = 2 := by
    have h₁ : v ⬝ᵥ x = c + 1 := h
    rw [h₁]
    ring
  rw [reflectAcross, h₀, dualVector, hq, smul_smul]
  norm_num
theorem linearHeight_terminal {v : AmbientSpace} {b : Link 1} (hb : b ∈ positiveLinks 1) :
    ∃ ρ, b = Link.forwardFrom b.initial ρ ∧
      linearHeight v (b.terminal : LatticePoint 1) = linearHeight v (b.initial : LatticePoint 1) + v ρ := by
  obtain ⟨ρ, hρ⟩ := exists_eq_forwardFrom hb
  refine ⟨ρ, hρ, ?_⟩
  have h : b.terminal = b.initial + axisStep 1 ρ := congrArg Link.terminal hρ
  rw [h, linearHeight_add_axisStep]
theorem mem_halfSpaceLinks_pos_iff {v : AmbientSpace} {c : ℝ} {b : Link 1} (hb : b ∈ positiveLinks 1) :
    b ∈ halfSpaceLinks 1 v c 1 ↔
      c ≤ linearHeight v (b.initial : LatticePoint 1) ∧ c ≤ linearHeight v (b.terminal : LatticePoint 1) := by
  rw [mem_halfSpaceLinks, mem_closedHalfSpace_pos, mem_closedHalfSpace_pos]
  exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩
theorem mem_halfSpaceLinks_neg_iff {v : AmbientSpace} {c : ℝ} {b : Link 1} (hb : b ∈ positiveLinks 1) :
    b ∈ halfSpaceLinks 1 v c (-1) ↔
      linearHeight v (b.initial : LatticePoint 1) ≤ c ∧ linearHeight v (b.terminal : LatticePoint 1) ≤ c := by
  rw [mem_halfSpaceLinks, mem_closedHalfSpace_neg, mem_closedHalfSpace_neg]
  exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩
theorem linksAtIntegerLevel_of (P : NormalLevelPair 1)
    (hint : ∀ x : LatticePoint 1, ∃ i : ℤ, linearHeight P.normal (x : AmbientSpace) = i)
    (hent : ∀ ρ, P.normal ρ = 0 ∨ P.normal ρ = 1 ∨ P.normal ρ = -1)
    (hk : ∃ k : ℤ, P.level = (k : ℝ)) : LinksAtIntegerLevel P := by
  obtain ⟨k, hk⟩ := hk
  refine ⟨subset_empty_iff.mp fun b hb => ?_, fun b hb => ?_⟩
  · exfalso
    obtain ⟨hpos, hnot⟩ := hb
    obtain ⟨ρ, -, hterm⟩ := linearHeight_terminal (v := P.normal) hpos
    obtain ⟨i, hi⟩ := hint b.initial
    have hcases := intCast_trichotomy i k
    have hside : (P.level ≤ linearHeight P.normal (b.initial : LatticePoint 1) ∧
          P.level ≤ linearHeight P.normal (b.terminal : LatticePoint 1)) ∨
        (linearHeight P.normal (b.initial : LatticePoint 1) ≤ P.level ∧
          linearHeight P.normal (b.terminal : LatticePoint 1) ≤ P.level) := by
      rw [hterm, hi, hk]
      rcases hent ρ with h | h | h <;> rw [h] <;> rcases hcases with hc | hc | hc <;>
        first
        | exact Or.inl ⟨by linarith, by linarith⟩
        | exact Or.inr ⟨by linarith, by linarith⟩
    rcases hside with h | h
    · exact hnot (Or.inl ((mem_halfSpaceLinks_pos_iff hpos).mpr h))
    · exact hnot (Or.inr ((mem_halfSpaceLinks_neg_iff hpos).mpr h))
  · have hpos := (mem_halfSpaceLinks.mp hb.1).1
    have h₁ := (mem_halfSpaceLinks_pos_iff hpos).mp hb.1
    have h₂ := (mem_halfSpaceLinks_neg_iff hpos).mp hb.2
    have ht := reflectAcross_of_linearHeight_eq (le_antisymm h₂.1 h₁.1)
    have hh := reflectAcross_of_linearHeight_eq (le_antisymm h₂.2 h₁.2)
    exact ⟨ht, hh, InfiniteLattice.Link.ext (Subtype.ext ht) (Subtype.ext hh)⟩
theorem linksAtHalfIntegerLevel_of (P : NormalLevelPair 1)
    (hint : ∀ x : LatticePoint 1, ∃ i : ℤ, linearHeight P.normal (x : AmbientSpace) = i)
    (hinv : reflectAcross P.normal P.level ∘ reflectAcross P.normal P.level = id)
    (hk : ∃ k : ℤ, P.level = (k : ℝ) + 1 / 2) : LinksAtHalfIntegerLevel P := by
  obtain ⟨k, hk⟩ := hk
  have hq : normSq P.normal ≠ 2 := by
    intro hq
    obtain ⟨m, hm⟩ := P.allowed.2 hq
    exact intCast_ne_add_half k m (by rw [← hk, hm, mul_one])
  obtain ⟨μ, hμ⟩ := exists_eq_coordVec_of_normSq_ne_two P.normal_mem hq
  have hμ₁ : P.normal μ = 1 := by rw [hμ, coordVec_self]
  have hval : ∀ ρ, ρ ≠ μ → P.normal ρ = 0 := fun ρ h => by rw [hμ, coordVec_of_ne h]
  have hcoord : ∀ x : AmbientSpace, linearHeight P.normal x = x μ := fun x => by
    rw [hμ, linearHeight_coordVec]
  refine ⟨μ, hμ, subset_empty_iff.mp fun b hb => ?_, ?_, fun x hx => ?_⟩
  · exfalso
    have hpos := (mem_halfSpaceLinks.mp hb.1).1
    have h₁ := (mem_halfSpaceLinks_pos_iff hpos).mp hb.1
    have h₂ := (mem_halfSpaceLinks_neg_iff hpos).mp hb.2
    obtain ⟨i, hi⟩ := hint b.initial
    exact intCast_ne_add_half k i (by rw [← hi, ← hk]; exact le_antisymm h₂.1 h₁.1)
  · ext b
    constructor
    · rintro ⟨hpos, hnot⟩
      obtain ⟨ρ, hρ, hterm⟩ := linearHeight_terminal (v := P.normal) hpos
      obtain ⟨i, hi⟩ := hint b.initial
      have hn₁ : ¬ (P.level ≤ linearHeight P.normal (b.initial : LatticePoint 1) ∧
          P.level ≤ linearHeight P.normal (b.terminal : LatticePoint 1)) :=
        fun h => hnot (Or.inl ((mem_halfSpaceLinks_pos_iff hpos).mpr h))
      have hn₂ : ¬ (linearHeight P.normal (b.initial : LatticePoint 1) ≤ P.level ∧
          linearHeight P.normal (b.terminal : LatticePoint 1) ≤ P.level) :=
        fun h => hnot (Or.inr ((mem_halfSpaceLinks_neg_iff hpos).mpr h))
      have hρμ : ρ = μ := by
        by_contra hne
        rw [hterm, hval ρ hne, add_zero] at hn₁ hn₂
        rcases le_total P.level (linearHeight P.normal (b.initial : LatticePoint 1)) with h | h
        · exact hn₁ ⟨h, h⟩
        · exact hn₂ ⟨h, h⟩
      subst hρμ
      rw [hterm, hμ₁] at hn₁ hn₂
      refine ⟨b.initial, ?_, hρ⟩
      rw [← hcoord (b.initial : AmbientSpace), hi, hk]
      rw [hi, hk] at hn₁ hn₂
      rcases intCast_trichotomy i k with hc | hc | hc
      · exact (hn₂ ⟨by linarith, by linarith⟩).elim
      · linarith
      · exact (hn₁ ⟨by linarith, by linarith⟩).elim
    · rintro ⟨x, hx, rfl⟩
      have hpos := forwardFrom_mem_positiveLinks x μ
      have ht : linearHeight P.normal (x : AmbientSpace) = P.level - 1 / 2 := by rw [hcoord, hx]
      have hh : linearHeight P.normal (x + axisStep 1 μ : LatticePoint 1) = P.level + 1 / 2 := by
        rw [linearHeight_add_axisStep, ht, hμ₁]
        ring
      refine ⟨hpos, ?_⟩
      rintro (h | h)
      · have := ((mem_halfSpaceLinks_pos_iff hpos).mp h).1
        change _ ≤ linearHeight P.normal (x : AmbientSpace) at this
        linarith
      · have := ((mem_halfSpaceLinks_neg_iff hpos).mp h).2
        change linearHeight P.normal (x + axisStep 1 μ : LatticePoint 1) ≤ _ at this
        linarith
  · have ht : linearHeight P.normal (x : AmbientSpace) = P.level - 1 / 2 := by rw [hcoord, hx]
    have h₁ : reflectAcross P.normal P.level (x : LatticePoint 1) = (x + axisStep 1 μ : LatticePoint 1) :=
      reflectAcross_of_half_below hμ ht
    have h₂ : reflectAcross P.normal P.level (x + axisStep 1 μ : LatticePoint 1) = (x : LatticePoint 1) := by
      rw [← h₁]
      exact congrFun hinv _
    exact ⟨h₁, h₂, InfiniteLattice.Link.ext (Subtype.ext h₁) (Subtype.ext h₂)⟩
theorem orientedRepresentative_mem (b : Link 1) : b.orientedRepresentative ∈ positiveLinks 1 := by
  by_cases h : b.IsPositivelyOriented
  · simp only [Link.orientedRepresentative, if_pos h]
    exact h
  · simp only [Link.orientedRepresentative, if_neg h]
    obtain ⟨μ, e | e⟩ := b.isAdjacent
    · exact (h ⟨μ, e⟩).elim
    · refine ⟨μ, ?_⟩
      change b.initial - b.terminal = axisStep 1 μ
      rw [← neg_sub, e, neg_neg]
theorem ends_orientedRepresentative (b : Link 1) (Q : LatticePoint 1 → Prop) (ht : Q b.initial)
    (hh : Q b.terminal) : Q b.orientedRepresentative.initial ∧ Q b.orientedRepresentative.terminal := by
  by_cases h : b.IsPositivelyOriented
  · simp only [Link.orientedRepresentative, if_pos h]
    exact ⟨ht, hh⟩
  · simp only [Link.orientedRepresentative, if_neg h]
    exact ⟨hh, ht⟩
theorem halfSpaceLinksCorrespond_of (P : NormalLevelPair 1) (hI : LatticeSymmetryProperties 1)
    (hdot : ∀ x, P.normal ⬝ᵥ reflectAcross P.normal P.level x = 2 * P.level - P.normal ⬝ᵥ x)
    (hinv : reflectAcross P.normal P.level ∘ reflectAcross P.normal P.level = id) :
    HalfSpaceLinksCorrespond P := by
  obtain ⟨hbij, hcomp, -⟩ := hI P.reflectSymmetry P.reflectSymmetry
  have hheight : ∀ x : LatticePoint 1,
      linearHeight P.normal (P.reflectSymmetry.pointMap x : LatticePoint 1) =
        2 * P.level - linearHeight P.normal (x : AmbientSpace) := fun x => hdot x
  have hself : ∀ b ∈ positiveLinks 1, P.reflectedLink (P.reflectedLink b) = b := by
    intro b hb
    have h₁ := hcomp b hb
    have h₂ : (P.reflectSymmetry.comp P.reflectSymmetry).linkMap b = b :=
      InfiniteLattice.Link.ext (Subtype.ext (congrFun hinv _)) (Subtype.ext (congrFun hinv _))
    rw [h₂] at h₁
    have h₃ : b.orientedRepresentative = b := if_pos hb
    rw [h₃] at h₁
    exact h₁
  have hup : ∀ b ∈ halfSpaceLinks 1 P.normal P.level 1,
      P.reflectedLink b ∈ halfSpaceLinks 1 P.normal P.level (-1) := by
    intro b hb
    have hpos := (mem_halfSpaceLinks.mp hb).1
    have h₁ := (mem_halfSpaceLinks_pos_iff hpos).mp hb
    refine (mem_halfSpaceLinks_neg_iff (orientedRepresentative_mem _)).mpr
      (ends_orientedRepresentative (P.reflectSymmetry.linkMap b)
        (fun x => linearHeight P.normal (x : AmbientSpace) ≤ P.level) ?_ ?_)
    · change linearHeight P.normal (P.reflectSymmetry.pointMap b.initial : LatticePoint 1) ≤ _
      rw [hheight]
      linarith [h₁.1]
    · change linearHeight P.normal (P.reflectSymmetry.pointMap b.terminal : LatticePoint 1) ≤ _
      rw [hheight]
      linarith [h₁.2]
  have hdown : ∀ b ∈ halfSpaceLinks 1 P.normal P.level (-1),
      P.reflectedLink b ∈ halfSpaceLinks 1 P.normal P.level 1 := by
    intro b hb
    have hpos := (mem_halfSpaceLinks.mp hb).1
    have h₁ := (mem_halfSpaceLinks_neg_iff hpos).mp hb
    refine (mem_halfSpaceLinks_pos_iff (orientedRepresentative_mem _)).mpr
      (ends_orientedRepresentative (P.reflectSymmetry.linkMap b)
        (fun x => P.level ≤ linearHeight P.normal (x : AmbientSpace)) ?_ ?_)
    · change _ ≤ linearHeight P.normal (P.reflectSymmetry.pointMap b.initial : LatticePoint 1)
      rw [hheight]
      linarith [h₁.1]
    · change _ ≤ linearHeight P.normal (P.reflectSymmetry.pointMap b.terminal : LatticePoint 1)
      rw [hheight]
      linarith [h₁.2]
  refine Set.BijOn.mk hup (fun b hb b' hb' h => ?_) fun b hb => ?_
  · exact hbij.injOn (mem_halfSpaceLinks.mp hb).1 (mem_halfSpaceLinks.mp hb').1 h
  · exact ⟨P.reflectedLink b, hdown b hb, hself b (mem_halfSpaceLinks.mp hb).1⟩
theorem apply_eq_of_orientedRepresentative {U U' : GaugeField 1} {b : Link 1}
    (h : U b.orientedRepresentative = U' b.orientedRepresentative) : U b = U' b := by
  by_cases hb : b.IsPositivelyOriented
  · simpa only [Link.orientedRepresentative, if_pos hb] using h
  · simp only [Link.orientedRepresentative, if_neg hb] at h
    have h₁ : U b = (U b.opposite)⁻¹ := U.2 b.opposite
    have h₂ : U' b = (U' b.opposite)⁻¹ := U'.2 b.opposite
    rw [h₁, h₂, h]
theorem continuous_apply_link (b : Link 1) : Continuous fun U : GaugeField 1 => U b := by apply _root_.YangMills.Construction.InfiniteLattice.ContinuousLocalDensity.continuous_eval_link <;> assumption
theorem orientedRepresentative_mem_linksInside {S : Set AmbientSpace} {b : Link 1}
    (h : (b.initial : AmbientSpace) ∈ S ∧ (b.terminal : AmbientSpace) ∈ S) :
    b.orientedRepresentative ∈ linksInside 1 S := by
  refine ⟨orientedRepresentative_mem b, fun b' hb' => ?_⟩
  rw [mem_singleton_iff.mp hb']
  exact ends_orientedRepresentative b (fun x => (x : AmbientSpace) ∈ S) h.1 h.2
theorem entry_mem_regionObservables (hM : MeasurableIffDependsOnly 1) {S : Set AmbientSpace}
    {b₀ b₁ : Link 1}
    (h₀ : (b₀.initial : AmbientSpace) ∈ S ∧ (b₀.terminal : AmbientSpace) ∈ S)
    (h₁ : (b₁.initial : AmbientSpace) ∈ S ∧ (b₁.terminal : AmbientSpace) ∈ S) (i j : Fin 2) :
    (fun U : GaugeField 1 => ((U b₀ * U b₁ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) i j) ∈
      regionObservables 1 S ∩ continuousLocalFunctions 1 := by
  have hcont : Continuous fun U : GaugeField 1 =>
      ((U b₀ * U b₁ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) i j :=
    (continuous_subtype_val.comp
      ((continuous_apply_link b₀).mul (continuous_apply_link b₁))).matrix_elem i j
  have hobs : IsBoundedObservable fun U : GaugeField 1 =>
      ((U b₀ * U b₁ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) i j :=
    ⟨hcont.measurable, 1, fun U =>
      entry_norm_bound_of_unitary (Matrix.mem_specialUnitaryGroup_iff.mp (U b₀ * U b₁).2).1 i j⟩
  obtain ⟨-, -, hS, hL⟩ := hM
  refine ⟨?_, hobs, ?_, hcont⟩
  · rw [hS]
    refine ⟨hobs, fun U U' h => ?_⟩
    have e₀ : U b₀ = U' b₀ :=
      apply_eq_of_orientedRepresentative (h _ (orientedRepresentative_mem_linksInside h₀))
    have e₁ : U b₁ = U' b₁ :=
      apply_eq_of_orientedRepresentative (h _ (orientedRepresentative_mem_linksInside h₁))
    simp only [e₀, e₁]
  · refine (hL _ hobs).mpr
      ⟨{b₀.orientedRepresentative, b₁.orientedRepresentative}, ?_, ?_, fun U U' h => ?_⟩
    · rintro b (rfl | rfl)
      · exact orientedRepresentative_mem _
      · exact orientedRepresentative_mem _
    · exact (finite_singleton _).insert _
    · have e₀ : U b₀ = U' b₀ := apply_eq_of_orientedRepresentative (h _ (mem_insert _ _))
      have e₁ : U b₁ = U' b₁ := apply_eq_of_orientedRepresentative (h _ (mem_insert_of_mem _ rfl))
      simp only [e₀, e₁]
theorem corners_of_highAxis_ne_one {v : AmbientSpace} {p : ElementaryPlaquette 1}
    (h : v p.highAxis ≠ 1) :
    levelCornerOne v p = p.corner ∧
      levelCornerTwo v p = p.corner + axisStep 1 p.lowAxis + axisStep 1 p.highAxis ∧
      raisedCorner v p = p.corner + axisStep 1 p.lowAxis ∧
      loweredCorner v p = p.corner + axisStep 1 p.highAxis :=
  ⟨if_neg h, if_neg h, if_neg h, if_neg h⟩
theorem corners_of_highAxis_eq_one {v : AmbientSpace} {p : ElementaryPlaquette 1}
    (h : v p.highAxis = 1) :
    levelCornerOne v p = p.corner + axisStep 1 p.lowAxis ∧
      levelCornerTwo v p = p.corner + axisStep 1 p.highAxis ∧
      raisedCorner v p = p.corner + axisStep 1 p.lowAxis + axisStep 1 p.highAxis ∧
      loweredCorner v p = p.corner :=
  ⟨if_pos h, if_pos h, if_pos h, if_pos h⟩
theorem diagonal_cut_formulas (hF : PlaquetteProperties 1) (hM : MeasurableIffDependsOnly 1)
    (P : NormalLevelPair 1) (p : ElementaryPlaquette 1)
    (hy : linearHeight P.normal (levelCornerOne P.normal p : LatticePoint 1) = P.level)
    (hy' : linearHeight P.normal (levelCornerTwo P.normal p : LatticePoint 1) = P.level)
    (hz : linearHeight P.normal (raisedCorner P.normal p : LatticePoint 1) = P.level + 1)
    (hθ : reflectAcross P.normal P.level (raisedCorner P.normal p : LatticePoint 1) =
      (loweredCorner P.normal p : LatticePoint 1))
    (hc : ({levelCornerOne P.normal p, raisedCorner P.normal p, levelCornerTwo P.normal p,
      loweredCorner P.normal p} : Set (LatticePoint 1)) = p.cornerSet) :
    (∀ i j : Fin 2,
      (fun U : GaugeField 1 =>
        ((raisedPathHolonomy P.normal p U : ComplexMatrix2.specialUnitary) : ComplexMatrix2) i j) ∈
        halfSpaceContinuousLocal 1 P.normal P.level 1) ∧
    ∀ U : GaugeField 1,
      (ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re =
          (ComplexMatrix2.fullTrace ((raisedPathHolonomy P.normal p U *
            (raisedPathHolonomy P.normal p (P.reflectSymmetry.pullbackField U))⁻¹ :
              ComplexMatrix2.specialUnitary) : ComplexMatrix2)).re ∧
        raisedPathHolonomy P.normal p (P.reflectSymmetry.pullbackField U) =
          U (linkToLowered P.normal p) * U (linkFromLowered P.normal p) := by
  obtain ⟨-, hloop, -⟩ := hF
  have hm₀ : P.reflectSymmetry.linkMap (linkToRaised P.normal p) = linkToLowered P.normal p :=
    InfiniteLattice.Link.ext (Subtype.ext (reflectAcross_of_linearHeight_eq hy)) (Subtype.ext hθ)
  have hm₁ : P.reflectSymmetry.linkMap (linkFromRaised P.normal p) = linkFromLowered P.normal p :=
    InfiniteLattice.Link.ext (Subtype.ext hθ) (Subtype.ext (reflectAcross_of_linearHeight_eq hy'))
  have hv : ∀ U : GaugeField 1,
      raisedPathHolonomy P.normal p (P.reflectSymmetry.pullbackField U) =
        U (linkToLowered P.normal p) * U (linkFromLowered P.normal p) := fun U => by
    change U (P.reflectSymmetry.linkMap (linkToRaised P.normal p)) *
      U (P.reflectSymmetry.linkMap (linkFromRaised P.normal p)) = _
    rw [hm₀, hm₁]
  refine ⟨fun i j => ?_, fun U => ⟨?_, hv U⟩⟩
  · exact entry_mem_regionObservables hM (b₀ := linkToRaised P.normal p)
      (b₁ := linkFromRaised P.normal p)
      ⟨mem_closedHalfSpace_pos.mpr hy.ge, mem_closedHalfSpace_pos.mpr (by
        change _ ≤ linearHeight P.normal (raisedCorner P.normal p : LatticePoint 1)
        linarith)⟩
      ⟨mem_closedHalfSpace_pos.mpr (by
        change _ ≤ linearHeight P.normal (raisedCorner P.normal p : LatticePoint 1)
        linarith), mem_closedHalfSpace_pos.mpr hy'.ge⟩ i j
  · have h := hloop p U (linkToRaised P.normal p) (linkFromRaised P.normal p)
      (linkFromLowered P.normal p).opposite (linkToLowered P.normal p).opposite hc rfl rfl
      rfl rfl
    have e : raisedPathHolonomy P.normal p U *
        (U (linkToLowered P.normal p) * U (linkFromLowered P.normal p))⁻¹ =
        U (linkToRaised P.normal p) * U (linkFromRaised P.normal p) *
          U (linkFromLowered P.normal p).opposite * U (linkToLowered P.normal p).opposite := by
      rw [U.2, U.2, mul_inv_rev, raisedPathHolonomy]
      simp only [mul_assoc]
    rw [hv U, e]
    linarith
theorem coordVec_sub_apply {μ ν : Fin 4} (h : μ ≠ ν) :
    (coordVec μ - coordVec ν) μ = 1 ∧
      (coordVec μ - coordVec ν) ν = -1 ∧
      ∀ ρ, ρ ≠ μ → ρ ≠ ν → (coordVec μ - coordVec ν) ρ = 0 := by
  refine ⟨?_, ?_, fun ρ h₁ h₂ => ?_⟩
  · simp only [Pi.sub_apply, coordVec_self, coordVec_of_ne h, sub_zero]
  · simp only [Pi.sub_apply, coordVec_self, coordVec_of_ne h.symm, zero_sub]
  · simp only [Pi.sub_apply, coordVec_of_ne h₁, coordVec_of_ne h₂, sub_zero]
theorem coordVec_add_apply {μ ν : Fin 4} (h : μ ≠ ν) :
    (coordVec μ + coordVec ν) μ = 1 ∧
      (coordVec μ + coordVec ν) ν = 1 ∧
      ∀ ρ, ρ ≠ μ → ρ ≠ ν → (coordVec μ + coordVec ν) ρ = 0 := by
  refine ⟨?_, ?_, fun ρ h₁ h₂ => ?_⟩
  · simp only [Pi.add_apply, coordVec_self, coordVec_of_ne h, add_zero]
  · simp only [Pi.add_apply, coordVec_self, coordVec_of_ne h.symm, zero_add]
  · simp only [Pi.add_apply, coordVec_of_ne h₁, coordVec_of_ne h₂, add_zero]
theorem insert_swap_four {x₁ x₂ x₃ x₄ : LatticePoint 1} :
    ({x₁, x₂, x₃, x₄} : Set (LatticePoint 1)) = {x₁, x₃, x₂, x₄} := by
  ext z
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto
theorem diagonalCutProperties_of_sub (hF : PlaquetteProperties 1) (hM : MeasurableIffDependsOnly 1)
    (P : NormalLevelPair 1) (p : ElementaryPlaquette 1)
    (hn : P.normal = coordVec p.lowAxis - coordVec p.highAxis)
    (hbase : linearHeight P.normal (p.corner : LatticePoint 1) = P.level) :
    DiagonalCutProperties P p.lowAxis p.highAxis p := by
  have hne := p.lowAxis_lt_highAxis.ne
  obtain ⟨v₁, v₂, -⟩ := coordVec_sub_apply hne
  have hn₁ : P.normal p.lowAxis = 1 := by rw [hn]; exact v₁
  have hn₂ : P.normal p.highAxis = -1 := by rw [hn]; exact v₂
  have hn₃ : P.normal p.highAxis ≠ 1 := by rw [hn₂]; norm_num
  obtain ⟨e₁, e₂, e₃, e₄⟩ := corners_of_highAxis_ne_one hn₃
  have hq : normSq P.normal = 2 := by rw [hn]; exact normSq_coordVec_sub hne
  have hy : linearHeight P.normal (levelCornerOne P.normal p : LatticePoint 1) = P.level := by
    rw [e₁, hbase]
  have hy' : linearHeight P.normal (levelCornerTwo P.normal p : LatticePoint 1) = P.level := by
    rw [e₂, linearHeight_add_axisStep, linearHeight_add_axisStep, hbase, hn₁, hn₂]
    ring
  have hz : linearHeight P.normal (raisedCorner P.normal p : LatticePoint 1) = P.level + 1 := by
    rw [e₃, linearHeight_add_axisStep, hbase, hn₁]
  have hz' : linearHeight P.normal (loweredCorner P.normal p : LatticePoint 1) = P.level - 1 := by
    rw [e₄, linearHeight_add_axisStep, hbase, hn₂]
    ring
  have hθ : reflectAcross P.normal P.level (raisedCorner P.normal p : LatticePoint 1) =
      (loweredCorner P.normal p : LatticePoint 1) := by
    rw [reflectAcross_of_one_above hq hz, e₃, e₄, hn]
    simp only [AddSubgroup.coe_add, coe_axisStep]
    abel
  have hc : ({levelCornerOne P.normal p, raisedCorner P.normal p, levelCornerTwo P.normal p,
      loweredCorner P.normal p} : Set (LatticePoint 1)) = p.cornerSet := by
    rw [e₁, e₂, e₃, e₄]
    rfl
  obtain ⟨hE, hT⟩ := diagonal_cut_formulas hF hM P p hy hy' hz hθ hc
  refine ⟨fun _ => ⟨e₁, e₂, e₃, e₄⟩, fun h => ?_, ?_, hy, hy', hz, hz', hθ, hE, hT⟩
  · have h₁ : (coordVec p.lowAxis + coordVec p.highAxis) p.highAxis = 1 :=
      (coordVec_add_apply hne).2.1
    rw [← h] at h₁
    exact (hn₃ h₁).elim
  · rw [insert_swap_four, hc]
    rfl
theorem diagonalCutProperties_of_add (hF : PlaquetteProperties 1) (hM : MeasurableIffDependsOnly 1)
    (P : NormalLevelPair 1) (p : ElementaryPlaquette 1)
    (hn : P.normal = coordVec p.lowAxis + coordVec p.highAxis)
    (hbase : linearHeight P.normal (p.corner : LatticePoint 1) = P.level - 1) :
    DiagonalCutProperties P p.lowAxis p.highAxis p := by
  have hne := p.lowAxis_lt_highAxis.ne
  obtain ⟨v₁, v₂, -⟩ := coordVec_add_apply hne
  have hn₁ : P.normal p.lowAxis = 1 := by rw [hn]; exact v₁
  have hn₂ : P.normal p.highAxis = 1 := by rw [hn]; exact v₂
  obtain ⟨e₁, e₂, e₃, e₄⟩ := corners_of_highAxis_eq_one hn₂
  have hq : normSq P.normal = 2 := by rw [hn]; exact normSq_coordVec_add hne
  have hy : linearHeight P.normal (levelCornerOne P.normal p : LatticePoint 1) = P.level := by
    rw [e₁, linearHeight_add_axisStep, hbase, hn₁]
    ring
  have hy' : linearHeight P.normal (levelCornerTwo P.normal p : LatticePoint 1) = P.level := by
    rw [e₂, linearHeight_add_axisStep, hbase, hn₂]
    ring
  have hz : linearHeight P.normal (raisedCorner P.normal p : LatticePoint 1) = P.level + 1 := by
    rw [e₃, linearHeight_add_axisStep, linearHeight_add_axisStep, hbase, hn₁, hn₂]
    ring
  have hz' : linearHeight P.normal (loweredCorner P.normal p : LatticePoint 1) = P.level - 1 := by
    rw [e₄, hbase]
  have hθ : reflectAcross P.normal P.level (raisedCorner P.normal p : LatticePoint 1) =
      (loweredCorner P.normal p : LatticePoint 1) := by
    rw [reflectAcross_of_one_above hq hz, e₃, e₄, hn]
    simp only [AddSubgroup.coe_add, coe_axisStep]
    abel
  have hc : ({levelCornerOne P.normal p, raisedCorner P.normal p, levelCornerTwo P.normal p,
      loweredCorner P.normal p} : Set (LatticePoint 1)) = p.cornerSet := by
    rw [e₁, e₂, e₃, e₄]
    ext z
    simp only [ElementaryPlaquette.cornerSet, mem_insert_iff, mem_singleton_iff]
    tauto
  obtain ⟨hE, hT⟩ := diagonal_cut_formulas hF hM P p hy hy' hz hθ hc
  refine ⟨fun h => ?_, fun _ => ⟨e₁, e₂, e₃, e₄⟩, ?_, hy, hy', hz, hz', hθ, hE, hT⟩
  · have h₁ : (coordVec p.lowAxis - coordVec p.highAxis) p.highAxis = -1 :=
      (coordVec_sub_apply hne).2.1
    rw [← h, hn₂] at h₁
    norm_num at h₁
  · rw [insert_swap_four, hc]
    rfl
theorem diagonalCutCharacterization_of (hF : PlaquetteProperties 1)
    (hM : MeasurableIffDependsOnly 1) (P : NormalLevelPair 1)
    (hint : ∀ x : LatticePoint 1, ∃ i : ℤ, linearHeight P.normal (x : AmbientSpace) = i)
    (hent : ∀ ρ, P.normal ρ = 0 ∨ P.normal ρ = 1 ∨ P.normal ρ = -1) :
    DiagonalCutCharacterization P := by
  intro μ ν hlt hn p
  have hq : normSq P.normal = 2 := by
    rcases hn with h | h
    · rw [h]
      exact normSq_coordVec_sub hlt.ne
    · rw [h]
      exact normSq_coordVec_add hlt.ne
  obtain ⟨k, hk⟩ := P.allowed.2 hq
  have hc : ∃ k : ℤ, P.level = (k : ℝ) := ⟨k, by rw [hk, mul_one]⟩
  have hh := hint p.corner
  by_cases hpl : p.lowAxis = μ ∧ p.highAxis = ν
  · obtain ⟨rfl, rfl⟩ := hpl
    have hOf : p.LiesInPlane p.lowAxis p.highAxis := Or.inl ⟨rfl, rfl⟩
    rcases hn with hn | hn
    · obtain ⟨v₁, v₂, -⟩ := coordVec_sub_apply hlt.ne
      have hn₁ : P.normal p.lowAxis = 1 := by rw [hn]; exact v₁
      have hn₂ : P.normal p.highAxis = -1 := by rw [hn]; exact v₂
      have hcut : IsCutBy p P.normal P.level ↔
          linearHeight P.normal (p.corner : LatticePoint 1) = P.level := by
        rw [isCutBy_iff_heights, hn₁, hn₂]
        exact straddle_iff_of_sub hh hc
      have hopp : HasDiagonalCornersAtLevel P.normal P.level p ↔
          linearHeight P.normal (p.corner : LatticePoint 1) = P.level := by
        simp only [HasDiagonalCornersAtLevel, linearHeight_add_axisStep, hn₁, hn₂]
        constructor
        · rintro (⟨a, -⟩ | ⟨a, b⟩)
          · exact a
          · linarith
        · intro e
          exact Or.inl ⟨e, by linarith⟩
      refine ⟨?_, fun _ => ?_, fun h => ?_, fun h => ?_⟩
      · rw [hcut, hopp]
        exact ⟨fun e => ⟨hOf, e⟩, fun e => e.2⟩
      · rw [hcut]
        exact ⟨fun e => ⟨hOf, e⟩, fun e => e.2⟩
      · have h₁ : (coordVec p.lowAxis + coordVec p.highAxis) p.highAxis = 1 :=
          (coordVec_add_apply hlt.ne).2.1
        rw [← h, hn₂] at h₁
        norm_num at h₁
      · exact diagonalCutProperties_of_sub hF hM P p hn (hcut.mp h)
    · obtain ⟨v₁, v₂, -⟩ := coordVec_add_apply hlt.ne
      have hn₁ : P.normal p.lowAxis = 1 := by rw [hn]; exact v₁
      have hn₂ : P.normal p.highAxis = 1 := by rw [hn]; exact v₂
      have hcut : IsCutBy p P.normal P.level ↔
          linearHeight P.normal (p.corner : LatticePoint 1) = P.level - 1 := by
        rw [isCutBy_iff_heights, hn₁, hn₂]
        exact straddle_iff_of_add hh hc
      have hopp : HasDiagonalCornersAtLevel P.normal P.level p ↔
          linearHeight P.normal (p.corner : LatticePoint 1) = P.level - 1 := by
        simp only [HasDiagonalCornersAtLevel, linearHeight_add_axisStep, hn₁, hn₂]
        constructor
        · rintro (⟨a, b⟩ | ⟨a, -⟩) <;> linarith
        · intro e
          exact Or.inr ⟨by linarith, by linarith⟩
      refine ⟨?_, fun h => ?_, fun _ => ?_, fun h => ?_⟩
      · rw [hcut, hopp]
        exact ⟨fun e => ⟨hOf, e⟩, fun e => e.2⟩
      · have h₁ : (coordVec p.lowAxis - coordVec p.highAxis) p.highAxis = -1 :=
          (coordVec_sub_apply hlt.ne).2.1
        rw [← h, hn₂] at h₁
        norm_num at h₁
      · rw [hcut]
        exact ⟨fun e => ⟨hOf, e⟩, fun e => e.2⟩
      · exact diagonalCutProperties_of_add hF hM P p hn (hcut.mp h)
  · have hz : ∀ ρ, ρ ≠ μ → ρ ≠ ν → P.normal ρ = 0 := by
      intro ρ h₁ h₂
      rcases hn with h | h
      · rw [h]
        exact (coordVec_sub_apply hlt.ne).2.2 ρ h₁ h₂
      · rw [h]
        exact (coordVec_add_apply hlt.ne).2.2 ρ h₁ h₂
    have h₀ : P.normal p.lowAxis = 0 ∨ P.normal p.highAxis = 0 := by
      by_cases a : p.lowAxis = μ
      · right
        have b : p.highAxis ≠ ν := fun b => hpl ⟨a, b⟩
        have c : p.highAxis ≠ μ := fun c => p.lowAxis_lt_highAxis.ne (a.trans c.symm)
        exact hz _ c b
      · by_cases b : p.lowAxis = ν
        · right
          have h₁ : ν < p.highAxis := b ▸ p.lowAxis_lt_highAxis
          exact hz _ (hlt.trans h₁).ne' h₁.ne'
        · left
          exact hz _ a b
    have hnc : ¬ IsCutBy p P.normal P.level := fun h =>
      not_straddle_of_axis_zero hh hc (hent _) (hent _) h₀ ((isCutBy_iff_heights _ _ _).mp h)
    have hnp : ¬ p.LiesInPlane μ ν := by
      rintro (⟨a, b⟩ | ⟨a, b⟩)
      · exact hpl ⟨a, b⟩
      · have h₁ := p.lowAxis_lt_highAxis
        rw [a, b] at h₁
        exact absurd h₁ (not_lt.mpr hlt.le)
    exact ⟨iff_of_false hnc fun h => hnp h.1, fun _ => iff_of_false hnc fun h => hnp h.1,
      fun _ => iff_of_false hnc fun h => hnp h.1, fun h => absurd h hnc⟩
theorem cornerSet_of_liesInPlane {p : ElementaryPlaquette 1} {μ ν : Fin 4} (h : p.LiesInPlane μ ν) :
    p.cornerSet = {p.corner, p.corner + axisStep 1 μ, p.corner + axisStep 1 μ + axisStep 1 ν,
      p.corner + axisStep 1 ν} := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · have hcomm : p.corner + axisStep 1 p.highAxis + axisStep 1 p.lowAxis =
        p.corner + axisStep 1 p.lowAxis + axisStep 1 p.highAxis := add_right_comm _ _ _
    rw [hcomm]
    ext z
    simp only [ElementaryPlaquette.cornerSet, mem_insert_iff, mem_singleton_iff]
    tauto
theorem axisCutProperties_of (hF : PlaquetteProperties 1) (P : NormalLevelPair 1) {μ ν : Fin 4}
    (hμ : P.normal = coordVec μ) (hν : ν ≠ μ) {p : ElementaryPlaquette 1}
    (hpl : p.LiesInPlane μ ν) (hlow : HasBaseEdgeAtLevel P.normal P.level ν p) :
    AxisCutProperties P μ ν p := by
  obtain ⟨-, hloop, -⟩ := hF
  obtain ⟨h₀, h₁⟩ := hlow
  have hμ₁ : P.normal μ = 1 := by rw [hμ, coordVec_self]
  have hν₀ : P.normal ν = 0 := by rw [hμ, coordVec_of_ne hν]
  have hcomm : p.corner + axisStep 1 ν + axisStep 1 μ = p.corner + axisStep 1 μ + axisStep 1 ν :=
    add_right_comm _ _ _
  have hcorn := cornerSet_of_liesInPlane hpl
  refine ⟨hcorn, ?_, ?_, ?_, fun U => ?_⟩
  · refine (mem_halfSpaceLinks_neg_iff (forwardFrom_mem_positiveLinks _ _)).mpr ⟨?_, ?_⟩
    · change linearHeight P.normal (p.corner : LatticePoint 1) ≤ _
      linarith
    · change linearHeight P.normal (p.corner + axisStep 1 ν : LatticePoint 1) ≤ _
      linarith
  · refine (mem_halfSpaceLinks_pos_iff (forwardFrom_mem_positiveLinks _ _)).mpr ⟨?_, ?_⟩
    · change _ ≤ linearHeight P.normal (p.corner + axisStep 1 μ : LatticePoint 1)
      rw [linearHeight_add_axisStep, h₀, hμ₁]
      linarith
    · change _ ≤ linearHeight P.normal (p.corner + axisStep 1 μ + axisStep 1 ν : LatticePoint 1)
      rw [linearHeight_add_axisStep, linearHeight_add_axisStep, h₀, hμ₁, hν₀]
      linarith
  · refine InfiniteLattice.Link.ext (Subtype.ext (reflectAcross_of_half_below hμ h₀)) (Subtype.ext ?_)
    refine (reflectAcross_of_half_below hμ h₁).trans ?_
    change _ = ((p.corner + axisStep 1 μ + axisStep 1 ν : LatticePoint 1) : AmbientSpace)
    rw [← hcomm]
    rfl
  · have h := hloop p U (Link.forwardFrom p.corner μ) (Link.forwardFrom (p.corner + axisStep 1 μ) ν)
      (Link.forwardFrom (p.corner + axisStep 1 ν) μ).opposite (Link.forwardFrom p.corner ν).opposite ?_
      rfl hcomm.symm rfl rfl
    · rw [U.2, U.2] at h
      simp only [crossingHolonomy, upperCutLink, lowerCutLink]
      linarith
    · rw [hcorn]
      change ({p.corner, p.corner + axisStep 1 μ, p.corner + axisStep 1 ν + axisStep 1 μ,
        p.corner + axisStep 1 ν} : Set (LatticePoint 1)) = _
      rw [hcomm]
theorem axisCutCharacterization_of (hF : PlaquetteProperties 1) (P : NormalLevelPair 1)
    (hint : ∀ x : LatticePoint 1, ∃ i : ℤ, linearHeight P.normal (x : AmbientSpace) = i) :
    AxisCutCharacterization P := by
  intro μ hμ hpos p
  have hh := hint p.corner
  have hμ₁ : P.normal μ = 1 := by rw [hμ, coordVec_self]
  have hval : ∀ ρ, ρ ≠ μ → P.normal ρ = 0 := fun ρ h => by rw [hμ, coordVec_of_ne h]
  refine ⟨?_, fun ν hν hpl hlow => axisCutProperties_of hF P hμ hν hpl hlow⟩
  by_cases a : p.lowAxis = μ
  · have b : p.highAxis ≠ μ := fun b => p.lowAxis_lt_highAxis.ne (a.trans b.symm)
    have hn₁ : P.normal p.lowAxis = 1 := by rw [a, hμ₁]
    have hn₂ : P.normal p.highAxis = 0 := hval _ b
    have hiff : IsCutBy p P.normal P.level ↔
        linearHeight P.normal (p.corner : LatticePoint 1) = P.level - 1 / 2 :=
      (isCutBy_iff_heights _ _ _).trans (straddle_iff_axis hh hpos (Or.inl ⟨hn₁, hn₂⟩))
    rw [hiff]
    constructor
    · intro e
      exact ⟨p.highAxis, b, Or.inl ⟨a, rfl⟩, e,
        by rw [linearHeight_add_axisStep, hn₂, add_zero]; exact e⟩
    · rintro ⟨ν, -, -, e, -⟩
      exact e
  · by_cases b : p.highAxis = μ
    · have hn₁ : P.normal p.lowAxis = 0 := hval _ a
      have hn₂ : P.normal p.highAxis = 1 := by rw [b, hμ₁]
      have hiff : IsCutBy p P.normal P.level ↔
          linearHeight P.normal (p.corner : LatticePoint 1) = P.level - 1 / 2 :=
        (isCutBy_iff_heights _ _ _).trans (straddle_iff_axis hh hpos (Or.inr ⟨hn₁, hn₂⟩))
      rw [hiff]
      constructor
      · intro e
        exact ⟨p.lowAxis, a, Or.inr ⟨rfl, b⟩, e,
          by rw [linearHeight_add_axisStep, hn₁, add_zero]; exact e⟩
      · rintro ⟨ν, -, -, e, -⟩
        exact e
    · have hn₁ : P.normal p.lowAxis = 0 := hval _ a
      have hn₂ : P.normal p.highAxis = 0 := hval _ b
      refine iff_of_false (fun hcut => ?_) ?_
      · have h := (isCutBy_iff_heights _ _ _).mp hcut
        rw [hn₁, hn₂] at h
        obtain ⟨hA, hB⟩ := h
        rcases le_total P.level (linearHeight P.normal (p.corner : LatticePoint 1)) with h | h
        · exact hA ⟨h, by linarith, by linarith, by linarith⟩
        · exact hB ⟨h, by linarith, by linarith, by linarith⟩
      · rintro ⟨ν, -, (⟨x, -⟩ | ⟨-, y⟩), -⟩
        · exact a x
        · exact b y
theorem linksAndCutPlaquettesAtLevel (hPos : NormalFamilies.Properties.Statement)
    (hEl : InfiniteLattice.ElementaryLatticeFacts) :
    NormalFamilies.LinksAndCutPlaquettesAtLevel := by
  obtain ⟨-, hF, -, -, -, -, hM, hI, -⟩ := hEl 1 1 one_pos one_pos
  obtain ⟨⟨-, -, -, hfam⟩, hrefl, -⟩ := hPos
  intro P
  have hint : ∀ x : LatticePoint 1, ∃ i : ℤ, linearHeight P.normal (x : AmbientSpace) = i := fun x =>
    (hfam P.normal P.normal_mem).2.2.2 x x.2
  have hent : ∀ ρ, P.normal ρ = 0 ∨ P.normal ρ = 1 ∨ P.normal ρ = -1 :=
    (hfam P.normal P.normal_mem).2.2.1
  obtain ⟨-, -, hdot, hinv, -⟩ := hrefl P.normal P.normal_mem P.level
  refine ⟨fun x ρ => ⟨?_, dotProduct_coordVec _ _, hent ρ⟩, linksAtIntegerLevel_of P hint hent,
    linksAtHalfIntegerLevel_of P hint hinv, halfSpaceLinksCorrespond_of P hI hdot hinv, ?_,
    diagonalCutCharacterization_of hF hM P hint hent, axisCutCharacterization_of hF P hint⟩
  · rw [linearHeight_add_axisStep, dotProduct_coordVec]
    ring
  · rintro ⟨hq, k, hk⟩ p hcut
    obtain ⟨μ, hμ⟩ := exists_eq_coordVec_of_normSq_ne_two P.normal_mem (by rw [hq]; norm_num)
    have h₀ : P.normal p.lowAxis = 0 ∨ P.normal p.highAxis = 0 := by
      by_cases a : p.lowAxis = μ
      · right
        have b : p.highAxis ≠ μ := fun b => p.lowAxis_lt_highAxis.ne (a.trans b.symm)
        rw [hμ, coordVec_of_ne b]
      · left
        rw [hμ, coordVec_of_ne a]
    exact not_straddle_of_axis_zero (hint p.corner) ⟨k, by rw [hk, mul_one]⟩ (hent _) (hent _) h₀
      ((isCutBy_iff_heights _ _ _).mp hcut)
end YangMills.Construction.NormalFamilies.LevelCuts
