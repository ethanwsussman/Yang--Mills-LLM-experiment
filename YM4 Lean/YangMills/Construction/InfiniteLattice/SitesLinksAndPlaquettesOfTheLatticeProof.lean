import YangMills.Construction.InfiniteLattice.BondsAndTheirVariablesProof
import YangMills.Construction.InfiniteLattice.MeasurabilityIsDependenceOnVariablesAtEverySpacingProof
import YangMills.Construction.InfiniteLattice.SitesLinksAndPlaquettesOfTheLattice
import YangMills.Construction.LawInAState.CovarianceBelowTheAveragesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.LatticeGeometry
variable {a : ℝ}
theorem axisStep_apply (μ ν : Fin 4) :
    ((axisStep a μ : LatticePoint a) : AmbientSpace) ν = if ν = μ then a else 0 := by apply _root_.YangMills.SharedProofs.p59492 <;> assumption
theorem smul_single_eq (ε : ℝ) (μ : Fin 4) :
    ε • (Pi.single μ a : AmbientSpace) = Pi.single μ (ε * a) := by
  funext ν
  by_cases hνμ : ν = μ
  · subst hνμ
    simp
  · simp [Pi.single_eq_of_ne hνμ]
theorem coe_sub_eq_of_axisStep {x y : LatticePoint a} {μ : Fin 4} (h : y - x = axisStep a μ) :
    (y : AmbientSpace) - x = (1 : ℝ) • (Pi.single μ a : AmbientSpace) := by
  rw [one_smul]
  exact congrArg Subtype.val h
theorem coe_sub_eq_of_neg_axisStep {x y : LatticePoint a} {μ : Fin 4}
    (h : y - x = -axisStep a μ) :
    (y : AmbientSpace) - x = (-1 : ℝ) • (Pi.single μ a : AmbientSpace) := by
  rw [neg_one_smul]
  exact congrArg Subtype.val h
theorem euclidNormVec_sign_smul_single (ha : 0 < a) {ε : ℝ} (hε : ε ∈ ({1, -1} : Set ℝ))
    (μ : Fin 4) :
    TorusMetric.euclidNormVec (ε • (Pi.single μ a : AmbientSpace)) = a := by
  rw [smul_single_eq, euclidNormVec_single]
  simp only [mem_insert_iff, mem_singleton_iff] at hε
  rcases hε with rfl | rfl
  · simp [abs_of_pos ha]
  · simp [abs_of_pos ha]
theorem euclidNormVec_sub_eq_iff (ha : 0 < a) (x y : LatticePoint a) :
    TorusMetric.euclidNormVec ((y : AmbientSpace) - x) = a ↔
      ∃ ε ∈ ({1, -1} : Set ℝ), ∃ μ : Fin 4,
        (y : AmbientSpace) - x = ε • (Pi.single μ a : AmbientSpace) := by
  constructor
  · intro h
    obtain ⟨μ, hμ | hμ⟩ := isAdjacent_of_euclidNormVec x y (by rw [h, abs_of_pos ha])
    · exact ⟨1, by simp, μ, coe_sub_eq_of_axisStep hμ⟩
    · exact ⟨-1, by simp, μ, coe_sub_eq_of_neg_axisStep hμ⟩
  · rintro ⟨ε, hε, μ, h⟩
    rw [h]
    exact euclidNormVec_sign_smul_single ha hε μ
theorem sign_eq_and_axis_eq_of_smul_single_eq (ha : 0 < a) {ε ε' : ℝ}
    (hε : ε ∈ ({1, -1} : Set ℝ)) {μ μ' : Fin 4}
    (h : ε • (Pi.single μ a : AmbientSpace) = ε' • (Pi.single μ' a : AmbientSpace)) :
    ε = ε' ∧ μ = μ' := by
  have hε0 : ε ≠ 0 := by
    simp only [mem_insert_iff, mem_singleton_iff] at hε
    rcases hε with rfl | rfl <;> norm_num
  have hμ : μ = μ' := by
    by_contra hc
    have hz : ε * a = 0 := by
      have hcoord := congrFun h μ
      simpa [Pi.single_eq_of_ne hc] using hcoord
    exact mul_ne_zero hε0 ha.ne' hz
  subst hμ
  have hmul : ε * a = ε' * a := by
    have hcoord := congrFun h μ
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul] at hcoord
    exact hcoord
  exact ⟨mul_right_cancel₀ ha.ne' hmul, rfl⟩
theorem linksAreNeighborPairs_holds (ha : 0 < a) : LinksAreNeighborPairs a := by
  refine ⟨euclidNormVec_sub_eq_iff ha, ?_, ?_, ?_, xor_mem_positiveLinks ha, ?_⟩
  · intro x y ε hε ε' _ μ μ' h h'
    exact sign_eq_and_axis_eq_of_smul_single_eq ha hε (h.symm.trans h')
  · intro x y
    constructor
    · rintro ⟨ℓ, rfl, rfl⟩
      obtain ⟨μ, hμ | hμ⟩ := ℓ.isAdjacent
      · exact (euclidNormVec_sub_eq_iff ha _ _).mpr ⟨1, by simp, μ, coe_sub_eq_of_axisStep hμ⟩
      · exact (euclidNormVec_sub_eq_iff ha _ _).mpr
          ⟨-1, by simp, μ, coe_sub_eq_of_neg_axisStep hμ⟩
    · intro h
      obtain ⟨μ, hμ⟩ := isAdjacent_of_euclidNormVec x y (by rw [h, abs_of_pos ha])
      exact ⟨⟨x, y, μ, hμ⟩, rfl, rfl⟩
  · intro ℓ
    exact ⟨rfl, rfl, rfl⟩
  · intro L _ hsub ℓ hℓ hr
    exact opposite_notMem_positiveLinks ha (hsub hℓ) (hsub hr)
theorem finite_points_of_isBounded (ha : 0 < a) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) :
    {x : LatticePoint a | (x : AmbientSpace) ∈ S}.Finite := by apply _root_.YangMills.Construction.InfiniteLattice.MeasurableIffDependsOnlyProof.finite_latticePoints_of_isBounded <;> assumption
theorem finite_positiveLinksWithin (ha : 0 < a) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) :
    (positiveLinksWithin a S).Finite := by
  have hT := finite_points_of_isBounded ha hS
  refine Set.Finite.of_finite_image (f := fun ℓ : Link a => (ℓ.initial, ℓ.terminal))
    ((hT.prod hT).subset ?_) ?_
  · rintro _ ⟨ℓ, hℓ, rfl⟩
    have hℓ' : ℓ ∈ positiveLinkSet a ∩ linksWithin S := hℓ
    have hends : (ℓ.initial : AmbientSpace) ∈ S ∧ (ℓ.terminal : AmbientSpace) ∈ S := hℓ'.2
    exact ⟨hends.1, hends.2⟩
  · intro ℓ _ ℓ' _ h
    exact Link.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
theorem countable_positiveLinks : (positiveLinkSet a).Countable := by apply _root_.YangMills.Construction.CutoffLinks.LinksAndTheirVariables.countable_positiveLinks <;> assumption
theorem axisStep_ne_zero (ha : 0 < a) (μ : Fin 4) : axisStep a μ ≠ 0 := by apply _root_.YangMills.Construction.InfiniteLattice.OneSpacing.axisStep_ne_zero <;> assumption
theorem add_axisStep_ne_self (ha : 0 < a) (x : LatticePoint a) (μ : Fin 4) :
    x + axisStep a μ ≠ x := fun h =>
  axisStep_ne_zero ha μ (add_eq_left.mp h)
theorem forwardFrom_injective_pair (ha : 0 < a) {x y : LatticePoint a} {μ ν : Fin 4}
    (h : Link.forwardFrom x μ = Link.forwardFrom y ν) : x = y ∧ μ = ν := by apply _root_.YangMills.Construction.InfiniteLattice.OneSpacing.forwardFrom_inj <;> assumption
theorem list_nodup_of_four {α : Type} {w x y z : α} (h₁ : w ≠ x) (h₂ : w ≠ y) (h₃ : w ≠ z)
    (h₄ : x ≠ y) (h₅ : x ≠ z) (h₆ : y ≠ z) : [w, x, y, z].Nodup := by
  simp [h₁, h₂, h₃, h₄, h₅, h₆]
theorem cornerList_nodup (ha : 0 < a) (p : ElementaryPlaquette a) :
    [p.corner, p.corner + axisStep a p.lowAxis, p.corner + axisStep a p.lowAxis + axisStep a p.highAxis,
      p.corner + axisStep a p.highAxis].Nodup := by
  have hne : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  apply list_nodup_of_four
  all_goals
    intro h
    have hlow := congrArg (fun z : LatticePoint a => (z : AmbientSpace) p.lowAxis) h
    have hhigh := congrArg (fun z : LatticePoint a => (z : AmbientSpace) p.highAxis) h
    simp only [AddSubgroup.coe_add, Pi.add_apply, axisStep_apply, if_true, if_neg hne,
      if_neg hne.symm] at hlow hhigh
    linarith
theorem mem_closedSquare_of_mem_cornerSet (p : ElementaryPlaquette a) {c : LatticePoint a}
    (hc : c ∈ p.cornerSet) : (c : AmbientSpace) ∈ p.closedSquare := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  simp only [ElementaryPlaquette.cornerSet, mem_insert_iff, mem_singleton_iff] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact ⟨0, h0, 0, h0, by simp⟩
  · refine ⟨1, h1, 0, h0, ?_⟩
    funext ν
    simp [axisStep, Pi.single_apply]
  · refine ⟨1, h1, 1, h1, ?_⟩
    funext ν
    simp [axisStep, Pi.single_apply, add_assoc]
  · refine ⟨0, h0, 1, h1, ?_⟩
    funext ν
    simp [axisStep, Pi.single_apply]
theorem corner_le_of_mem_closedSquare (ha : 0 < a) {p : ElementaryPlaquette a} {y : AmbientSpace}
    (hy : y ∈ p.closedSquare) (κ : Fin 4) : (p.corner : AmbientSpace) κ ≤ y κ := by
  obtain ⟨s, hs, t, ht, rfl⟩ := hy
  have hlow : 0 ≤ (Pi.single p.lowAxis (1 : ℝ) : AmbientSpace) κ := by
    rw [Pi.single_apply]
    split_ifs <;> norm_num
  have hhigh : 0 ≤ (Pi.single p.highAxis (1 : ℝ) : AmbientSpace) κ := by
    rw [Pi.single_apply]
    split_ifs <;> norm_num
  have hsum := mul_nonneg ha.le (add_nonneg (mul_nonneg hs.1 hlow) (mul_nonneg ht.1 hhigh))
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith
theorem axis_of_mem_closedSquare (ha : 0 < a) {q : ElementaryPlaquette a} {μ : Fin 4}
    (h : ((q.corner + axisStep a μ : LatticePoint a) : AmbientSpace) ∈ q.closedSquare) :
    μ = q.lowAxis ∨ μ = q.highAxis := by
  by_contra hc
  push Not at hc
  obtain ⟨s, _, t, _, e⟩ := h
  have hcoord := congrFun e μ
  simp only [AddSubgroup.coe_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, axisStep_apply,
    if_true, Pi.single_eq_of_ne hc.1, Pi.single_eq_of_ne hc.2] at hcoord
  have : a = 0 := by linarith
  exact ha.ne' this
theorem eq_of_cornerSet_subset_closedSquare (ha : 0 < a) (p q : ElementaryPlaquette a)
    (h : ∀ c ∈ p.cornerSet, (c : AmbientSpace) ∈ q.closedSquare)
    (h' : ∀ c ∈ q.cornerSet, (c : AmbientSpace) ∈ p.closedSquare) : p = q := by
  have hp0 : p.corner ∈ p.cornerSet := by simp [ElementaryPlaquette.cornerSet]
  have hq0 : q.corner ∈ q.cornerSet := by simp [ElementaryPlaquette.cornerSet]
  have hp1 : p.corner + axisStep a p.lowAxis ∈ p.cornerSet := by
    simp [ElementaryPlaquette.cornerSet]
  have hp2 : p.corner + axisStep a p.highAxis ∈ p.cornerSet := by
    simp [ElementaryPlaquette.cornerSet]
  have hc : p.corner = q.corner := Subtype.ext (funext fun κ =>
    le_antisymm (corner_le_of_mem_closedSquare ha (h' _ hq0) κ)
      (corner_le_of_mem_closedSquare ha (h _ hp0) κ))
  have h₁ : p.lowAxis = q.lowAxis ∨ p.lowAxis = q.highAxis :=
    axis_of_mem_closedSquare ha (by rw [← hc]; exact h _ hp1)
  have h₂ : p.highAxis = q.lowAxis ∨ p.highAxis = q.highAxis :=
    axis_of_mem_closedSquare ha (by rw [← hc]; exact h _ hp2)
  have lt := p.lowAxis_lt_highAxis
  have lt' := q.lowAxis_lt_highAxis
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · rw [h₁, h₂] at lt
    exact absurd lt (lt_irrefl _)
  · exact ElementaryPlaquette.ext hc h₁ h₂
  · rw [h₁, h₂] at lt
    exact absurd lt lt'.asymm
  · rw [h₁, h₂] at lt
    exact absurd lt (lt_irrefl _)
theorem edges_nodup (ha : 0 < a) (p : ElementaryPlaquette a) : p.edges.Nodup := by
  have hne : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  refine list_nodup_of_four ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun h => hne (forwardFrom_injective_pair ha h).2
  · exact fun h => add_axisStep_ne_self ha _ _ (forwardFrom_injective_pair ha h).1.symm
  · exact fun h => hne (forwardFrom_injective_pair ha h).2
  · exact fun h => hne.symm (forwardFrom_injective_pair ha h).2
  · exact fun h => add_axisStep_ne_self ha _ _ (forwardFrom_injective_pair ha h).1
  · exact fun h => hne (forwardFrom_injective_pair ha h).2
theorem endpoints_mem_cornerSet (p : ElementaryPlaquette a) :
    ∀ ℓ ∈ p.edges, ℓ.initial ∈ p.cornerSet ∧ ℓ.terminal ∈ p.cornerSet := by
  intro ℓ hℓ
  simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl <;>
    simp [ElementaryPlaquette.cornerSet, Link.forwardFrom, add_right_comm]
theorem forwardFrom_mem_edges_iff (ha : 0 < a) (p : ElementaryPlaquette a) (y : LatticePoint a)
    (κ : Fin 4) :
    Link.forwardFrom y κ ∈ p.edges ↔
      (κ = p.lowAxis ∧ (p.corner = y ∨ p.corner = y - axisStep a p.highAxis)) ∨
        (κ = p.highAxis ∧ (p.corner = y ∨ p.corner = y - axisStep a p.lowAxis)) := by
  have fwd : ∀ {x : LatticePoint a} {ν : Fin 4},
      Link.forwardFrom y κ = Link.forwardFrom x ν ↔ y = x ∧ κ = ν := by
    intro x ν
    refine ⟨forwardFrom_injective_pair ha, ?_⟩
    rintro ⟨rfl, rfl⟩
    rfl
  simp only [ElementaryPlaquette.edges, List.mem_cons, List.not_mem_nil, or_false, fwd]
  constructor
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩)
    · exact Or.inl ⟨h', Or.inl h.symm⟩
    · exact Or.inr ⟨h', Or.inr (by rw [h, add_sub_cancel_right])⟩
    · exact Or.inl ⟨h', Or.inr (by rw [h, add_sub_cancel_right])⟩
    · exact Or.inr ⟨h', Or.inl h.symm⟩
  · rintro (⟨h', h | h⟩ | ⟨h', h | h⟩)
    · exact Or.inl ⟨h.symm, h'⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by rw [h, sub_add_cancel], h'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
    · exact Or.inr (Or.inl ⟨by rw [h, sub_add_cancel], h'⟩)
def plaquetteThroughLink (y : LatticePoint a) (κ : Fin 4) (z : {ν : Fin 4 // ν ≠ κ} × Bool) :
    ElementaryPlaquette a where
  corner := if z.2 then y - axisStep a z.1.1 else y
  lowAxis := min κ z.1.1
  highAxis := max κ z.1.1
  lowAxis_lt_highAxis := min_lt_max.mpr z.1.2.symm
theorem eq_of_min_eq_of_max_eq : ∀ κ ν ν' : Fin 4, ν ≠ κ → ν' ≠ κ → min κ ν = min κ ν' →
    max κ ν = max κ ν' → ν = ν' := by
  decide
theorem plaquetteThroughLink_injective (ha : 0 < a) (y : LatticePoint a) (κ : Fin 4) :
    Function.Injective (plaquetteThroughLink y κ) := by
  rintro ⟨⟨ν, hν⟩, e⟩ ⟨⟨ν', hν'⟩, e'⟩ h
  have h₁ : min κ ν = min κ ν' := congrArg ElementaryPlaquette.lowAxis h
  have h₂ : max κ ν = max κ ν' := congrArg ElementaryPlaquette.highAxis h
  have h₃ : (if e then y - axisStep a ν else y) = (if e' then y - axisStep a ν' else y) :=
    congrArg ElementaryPlaquette.corner h
  obtain rfl : ν = ν' := eq_of_min_eq_of_max_eq κ ν ν' hν hν' h₁ h₂
  have hs : y - axisStep a ν ≠ y := fun h₄ => axisStep_ne_zero ha ν (by simpa using h₄)
  cases e <;> cases e'
  · rfl
  · exact absurd h₃.symm (by simpa using hs)
  · exact absurd h₃ (by simpa using hs)
  · rfl
theorem setOf_plaquettes_containing_eq_range (ha : 0 < a) (y : LatticePoint a) (κ : Fin 4) :
    {p : ElementaryPlaquette a | Link.forwardFrom y κ ∈ p.edges} =
      range (plaquetteThroughLink y κ) := by
  ext p
  simp only [mem_ofPred_eq, mem_range]
  rw [forwardFrom_mem_edges_iff ha]
  constructor
  · rintro (⟨h, hc⟩ | ⟨h, hc⟩)
    · have hν : p.highAxis ≠ κ := by
        rw [h]
        exact p.lowAxis_lt_highAxis.ne'
      have hmin : min κ p.highAxis = p.lowAxis := by
        rw [h]
        exact min_eq_left p.lowAxis_lt_highAxis.le
      have hmax : max κ p.highAxis = p.highAxis := by
        rw [h]
        exact max_eq_right p.lowAxis_lt_highAxis.le
      rcases hc with hc | hc
      · exact ⟨(⟨p.highAxis, hν⟩, false),
          ElementaryPlaquette.ext (by simp [plaquetteThroughLink, hc]) hmin hmax⟩
      · exact ⟨(⟨p.highAxis, hν⟩, true),
          ElementaryPlaquette.ext (by simp [plaquetteThroughLink, hc]) hmin hmax⟩
    · have hν : p.lowAxis ≠ κ := by
        rw [h]
        exact p.lowAxis_lt_highAxis.ne
      have hmin : min κ p.lowAxis = p.lowAxis := by
        rw [h]
        exact min_eq_right p.lowAxis_lt_highAxis.le
      have hmax : max κ p.lowAxis = p.highAxis := by
        rw [h]
        exact max_eq_left p.lowAxis_lt_highAxis.le
      rcases hc with hc | hc
      · exact ⟨(⟨p.lowAxis, hν⟩, false),
          ElementaryPlaquette.ext (by simp [plaquetteThroughLink, hc]) hmin hmax⟩
      · exact ⟨(⟨p.lowAxis, hν⟩, true),
          ElementaryPlaquette.ext (by simp [plaquetteThroughLink, hc]) hmin hmax⟩
  · rintro ⟨⟨⟨ν, hν⟩, e⟩, rfl⟩
    rcases lt_or_gt_of_ne hν with h | h
    · have hmin : min κ ν = ν := min_eq_right h.le
      have hmax : max κ ν = κ := max_eq_left h.le
      right
      simp only [plaquetteThroughLink, hmin, hmax]
      cases e <;> simp
    · have hmin : min κ ν = κ := min_eq_left h.le
      have hmax : max κ ν = ν := max_eq_right h.le
      left
      simp only [plaquetteThroughLink, hmin, hmax]
      cases e <;> simp
theorem ncard_plaquettes_containing_link (ha : 0 < a) (y : LatticePoint a) (κ : Fin 4) :
    {p : ElementaryPlaquette a | Link.forwardFrom y κ ∈ p.edges}.ncard = 6 := by
  have hcard : ∀ κ : Fin 4, Fintype.card {ν : Fin 4 // ν ≠ κ} = 3 := by decide
  rw [setOf_plaquettes_containing_eq_range ha, ← Set.image_univ,
    Set.ncard_image_of_injective _ (plaquetteThroughLink_injective ha y κ), Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool, hcard κ]
theorem plaquetteCornersAndEdges_holds (ha : 0 < a) : PlaquetteCornersAndEdges a := by
  refine ⟨cornerList_nodup ha, ?_, ?_, edges_nodup ha, endpoints_mem_cornerSet,
    forwardFrom_mem_edges_iff ha, ?_⟩
  · intro p q h
    exact eq_of_cornerSet_subset_closedSquare ha p q
      (fun c hc => mem_closedSquare_of_mem_cornerSet q (by rw [← h]; exact hc))
      (fun c hc => mem_closedSquare_of_mem_cornerSet p (by rw [h]; exact hc))
  · intro p q h
    exact eq_of_cornerSet_subset_closedSquare ha p q
      (fun c hc => by rw [← h]; exact mem_closedSquare_of_mem_cornerSet p hc)
      (fun c hc => by rw [h]; exact mem_closedSquare_of_mem_cornerSet q hc)
  · rintro ℓ ⟨y, κ, rfl⟩
    exact ncard_plaquettes_containing_link ha y κ
theorem latticeGeometryStatement_holds : LatticeGeometryStatement := fun _ ha =>
  ⟨linksAreNeighborPairs_holds ha,
    ⟨fun _ hS => ⟨finite_points_of_isBounded ha hS, finite_positiveLinksWithin ha hS⟩,
      countable_positiveLinks⟩,
    plaquetteCornersAndEdges_holds ha, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
end YangMills.Construction.InfiniteLattice.LatticeGeometry
