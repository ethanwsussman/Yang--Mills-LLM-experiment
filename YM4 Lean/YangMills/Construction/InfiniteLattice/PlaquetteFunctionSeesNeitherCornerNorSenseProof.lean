import YangMills.Construction.InfiniteLattice.FactsOfThePlaquettesAtEverySpacingProof
import YangMills.Construction.InfiniteLattice.FactsOfTheBondsConfigurationsAndMotionsAtOneSpacingProof
import YangMills.Construction.InfiniteLattice.FactsOfThePlaquettesAtEverySpacing
import YangMills.Construction.InfiniteLattice.PlaquetteFunctionSeesNeitherCornerNorSense
import YangMills.Construction.LawInAState.CovarianceBelowTheAveragesProof
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.InfiniteLattice YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing.FaceEnergyInvariance
variable {a : ℝ}
def lowOffset : Fin 4 → ℤ := ![0, 1, 1, 0]
def highOffset : Fin 4 → ℤ := ![0, 0, 1, 1]
def vertex (p : ElementaryPlaquette a) : Fin 4 → LatticePoint a :=
  ![p.corner, p.corner + axisStep a p.lowAxis, p.corner + axisStep a p.lowAxis + axisStep a p.highAxis,
    p.corner + axisStep a p.highAxis]
theorem axisStep_apply (μ ν : Fin 4) :
    ((axisStep a μ : LatticePoint a) : AmbientSpace) ν = if ν = μ then a else 0 := by apply _root_.YangMills.SharedProofs.p59492 <;> assumption
theorem axisStep_ne_zero (ha : 0 < a) (μ : Fin 4) : axisStep a μ ≠ 0 := by apply _root_.YangMills.Construction.InfiniteLattice.OneSpacing.axisStep_ne_zero <;> assumption
theorem vertex_apply (p : ElementaryPlaquette a) (i : Fin 4) (ν : Fin 4) :
    ((vertex p i : LatticePoint a) : AmbientSpace) ν = (p.corner : AmbientSpace) ν +
      (lowOffset i : ℝ) * (if ν = p.lowAxis then a else 0) +
      (highOffset i : ℝ) * (if ν = p.highAxis then a else 0) := by
  fin_cases i <;> simp [vertex, lowOffset, highOffset, axisStep_apply]
theorem vertex_apply_lowAxis (p : ElementaryPlaquette a) (i : Fin 4) :
    ((vertex p i : LatticePoint a) : AmbientSpace) p.lowAxis =
      (p.corner : AmbientSpace) p.lowAxis + (lowOffset i : ℝ) * a := by
  rw [vertex_apply, if_pos rfl, if_neg p.lowAxis_lt_highAxis.ne]
  ring
theorem vertex_apply_highAxis (p : ElementaryPlaquette a) (i : Fin 4) :
    ((vertex p i : LatticePoint a) : AmbientSpace) p.highAxis =
      (p.corner : AmbientSpace) p.highAxis + (highOffset i : ℝ) * a := by
  rw [vertex_apply, if_pos rfl, if_neg p.lowAxis_lt_highAxis.ne']
  ring
theorem lowOffset_eq_of_apply (ha : 0 < a) (p : ElementaryPlaquette a) {i j : Fin 4}
    (h : ((vertex p i : LatticePoint a) : AmbientSpace) p.lowAxis =
      ((vertex p j : LatticePoint a) : AmbientSpace) p.lowAxis) :
    lowOffset i = lowOffset j := by
  rw [vertex_apply_lowAxis, vertex_apply_lowAxis] at h
  exact_mod_cast mul_right_cancel₀ ha.ne' (add_left_cancel h)
theorem highOffset_eq_of_apply (ha : 0 < a) (p : ElementaryPlaquette a) {i j : Fin 4}
    (h : ((vertex p i : LatticePoint a) : AmbientSpace) p.highAxis =
      ((vertex p j : LatticePoint a) : AmbientSpace) p.highAxis) :
    highOffset i = highOffset j := by
  rw [vertex_apply_highAxis, vertex_apply_highAxis] at h
  exact_mod_cast mul_right_cancel₀ ha.ne' (add_left_cancel h)
theorem vertex_injective (ha : 0 < a) (p : ElementaryPlaquette a) :
    Function.Injective (vertex p) := by apply _root_.YangMills.Construction.InfiniteLattice.PlaquetteProperties.cyclicCorner_injective <;> assumption
theorem mem_cornerSet_iff (p : ElementaryPlaquette a) (x : LatticePoint a) :
    x ∈ p.cornerSet ↔ ∃ i, x = vertex p i := by apply _root_.YangMills.Construction.InfiniteLattice.PlaquetteProperties.mem_cornerSet_iff <;> assumption
abbrev CyclicNeighbors (i j : Fin 4) : Prop := j = i + 1 ∨ i = j + 1
theorem cyclicNeighbors_of_offset_eq : ∀ i j : Fin 4, i ≠ j →
    (lowOffset i = lowOffset j ∨ highOffset i = highOffset j) → CyclicNeighbors i j := by
  decide
theorem cyclicNeighbors_of_step (ha : 0 < a) (p : ElementaryPlaquette a) {i j : Fin 4}
    (h : ∃ μ : Fin 4, vertex p j - vertex p i = axisStep a μ ∨
      vertex p j - vertex p i = -axisStep a μ) : CyclicNeighbors i j := by
  obtain ⟨μ, h⟩ := h
  have hne : i ≠ j := by
    rintro rfl
    rw [sub_self] at h
    rcases h with h | h
    · exact axisStep_ne_zero ha μ h.symm
    · exact axisStep_ne_zero ha μ (neg_eq_zero.mp h.symm)
  have hoff : ∀ ν, ν ≠ μ →
      ((vertex p i : LatticePoint a) : AmbientSpace) ν =
        ((vertex p j : LatticePoint a) : AmbientSpace) ν := by
    intro ν hν
    have hz : ((vertex p j - vertex p i : LatticePoint a) : AmbientSpace) ν = 0 := by
      rcases h with h | h <;> rw [h]
      · rw [axisStep_apply, if_neg hν]
      · have : ((-axisStep a μ : LatticePoint a) : AmbientSpace) ν =
            -((axisStep a μ : LatticePoint a) : AmbientSpace) ν := rfl
        rw [this, axisStep_apply, if_neg hν, neg_zero]
    have hz' : ((vertex p j : LatticePoint a) : AmbientSpace) ν -
        ((vertex p i : LatticePoint a) : AmbientSpace) ν = 0 := hz
    linarith
  refine cyclicNeighbors_of_offset_eq i j hne ?_
  by_cases hμ : p.lowAxis = μ
  · right
    exact highOffset_eq_of_apply ha p (hoff _ fun e => p.lowAxis_lt_highAxis.ne (hμ.trans e.symm))
  · left
    exact lowOffset_eq_of_apply ha p (hoff _ hμ)
theorem step_succ (p : ElementaryPlaquette a) (i : Fin 4) :
    ∃ μ : Fin 4, vertex p (i + 1) - vertex p i = axisStep a μ ∨
      vertex p (i + 1) - vertex p i = -axisStep a μ := by
  fin_cases i
  · exact ⟨p.lowAxis, Or.inl (show p.corner + axisStep a p.lowAxis - p.corner = _ by abel)⟩
  · exact ⟨p.highAxis, Or.inl
      (show p.corner + axisStep a p.lowAxis + axisStep a p.highAxis -
        (p.corner + axisStep a p.lowAxis) = _ by abel)⟩
  · exact ⟨p.lowAxis, Or.inr (show p.corner + axisStep a p.highAxis -
      (p.corner + axisStep a p.lowAxis + axisStep a p.highAxis) = _ by abel)⟩
  · exact ⟨p.highAxis, Or.inr (show p.corner - (p.corner + axisStep a p.highAxis) = _ by abel)⟩
theorem step_of_cyclicNeighbors (p : ElementaryPlaquette a) {i j : Fin 4}
    (h : CyclicNeighbors i j) :
    ∃ μ : Fin 4, vertex p j - vertex p i = axisStep a μ ∨
      vertex p j - vertex p i = -axisStep a μ := by
  rcases h with rfl | rfl
  · exact step_succ p i
  · obtain ⟨μ, h | h⟩ := step_succ p j
    · exact ⟨μ, Or.inr (by rw [← neg_sub, h])⟩
    · exact ⟨μ, Or.inl (by rw [← neg_sub, h, neg_neg])⟩
abbrev IsCyclicTour (t : Fin 4 × Fin 4 × Fin 4 × Fin 4) : Prop :=
  (∀ k : Fin 4, k = t.1 ∨ k = t.2.1 ∨ k = t.2.2.1 ∨ k = t.2.2.2) ∧
    CyclicNeighbors t.1 t.2.1 ∧ CyclicNeighbors t.2.1 t.2.2.1 ∧
      CyclicNeighbors t.2.2.1 t.2.2.2 ∧ CyclicNeighbors t.2.2.2 t.1
theorem card_isCyclicTour : Fintype.card {t // IsCyclicTour t} = 8 := by
  decide +kernel
def cycleOfTour (p : ElementaryPlaquette a) (t : {t // IsCyclicTour t}) : BoundaryCycle p where
  v₁ := vertex p t.1.1
  v₂ := vertex p t.1.2.1
  v₃ := vertex p t.1.2.2.1
  v₄ := vertex p t.1.2.2.2
  corners_eq := by
    ext x
    rw [mem_cornerSet_iff]
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩]
    · rintro ⟨k, rfl⟩
      rcases t.2.1 k with h | h | h | h <;> rw [h] <;> simp
  adj₁₂ := step_of_cyclicNeighbors p t.2.2.1
  adj₂₃ := step_of_cyclicNeighbors p t.2.2.2.1
  adj₃₄ := step_of_cyclicNeighbors p t.2.2.2.2.1
  adj₄₁ := step_of_cyclicNeighbors p t.2.2.2.2.2
theorem cycleOfTour_injective (ha : 0 < a) (p : ElementaryPlaquette a) :
    Function.Injective (cycleOfTour p) := by
  rintro ⟨⟨i, j, k, l⟩, ht⟩ ⟨⟨i', j', k', l'⟩, ht'⟩ h
  have h₁ : i = i' := vertex_injective ha p (congrArg BoundaryCycle.v₁ h)
  have h₂ : j = j' := vertex_injective ha p (congrArg BoundaryCycle.v₂ h)
  have h₃ : k = k' := vertex_injective ha p (congrArg BoundaryCycle.v₃ h)
  have h₄ : l = l' := vertex_injective ha p (congrArg BoundaryCycle.v₄ h)
  subst h₁ h₂ h₃ h₄
  rfl
theorem cycleOfTour_surjective (ha : 0 < a) (p : ElementaryPlaquette a) :
    Function.Surjective (cycleOfTour p) := by
  rintro ⟨x₁, x₂, x₃, x₄, hl, h₁₂, h₂₃, h₃₄, h₄₁⟩
  have hmem : ∀ x ∈ ({x₁, x₂, x₃, x₄} : Set (LatticePoint a)), ∃ i, x = vertex p i :=
    fun x hx => (mem_cornerSet_iff p x).mp (hl ▸ hx)
  obtain ⟨i, rfl⟩ := hmem x₁ (by simp)
  obtain ⟨j, rfl⟩ := hmem x₂ (by simp)
  obtain ⟨k, rfl⟩ := hmem x₃ (by simp)
  obtain ⟨l, rfl⟩ := hmem x₄ (by simp)
  have hround : ∀ m : Fin 4, m = i ∨ m = j ∨ m = k ∨ m = l := by
    intro m
    have hm : vertex p m ∈ p.cornerSet := (mem_cornerSet_iff p _).mpr ⟨m, rfl⟩
    rw [← hl] at hm
    simp only [mem_insert_iff, mem_singleton_iff] at hm
    rcases hm with h | h | h | h
    · exact Or.inl (vertex_injective ha p h)
    · exact Or.inr (Or.inl (vertex_injective ha p h))
    · exact Or.inr (Or.inr (Or.inl (vertex_injective ha p h)))
    · exact Or.inr (Or.inr (Or.inr (vertex_injective ha p h)))
  exact ⟨⟨(i, j, k, l), hround, cyclicNeighbors_of_step ha p h₁₂, cyclicNeighbors_of_step ha p h₂₃,
    cyclicNeighbors_of_step ha p h₃₄, cyclicNeighbors_of_step ha p h₄₁⟩, rfl⟩
theorem card_boundaryCycle (ha : 0 < a) (p : ElementaryPlaquette a) :
    Nat.card (BoundaryCycle p) = 8 := by
  rw [← Nat.card_congr
      (Equiv.ofBijective _ ⟨cycleOfTour_injective ha p, cycleOfTour_surjective ha p⟩),
    Nat.card_eq_fintype_card]
  exact card_isCyclicTour
theorem exists_boundaryCycle_holonomy_eq (p : ElementaryPlaquette a) (U : GaugeField a) :
    ∃ c : BoundaryCycle p, c.holonomy U = faceHolonomy U p := by
  refine ⟨cycleOfTour p ⟨(0, 1, 2, 3), by decide⟩, ?_⟩
  rw [faceHolonomy, ← U.2 (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis),
    ← U.2 (Link.forwardFrom p.corner p.highAxis)]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_) ?_
  · exact congrArg U (Link.ext rfl rfl)
  · exact congrArg U (Link.ext rfl rfl)
  · exact congrArg U (Link.ext (add_right_comm _ _ _) rfl)
  · exact congrArg U (Link.ext rfl rfl)
theorem corner_le_of_mem_cornerSet (ha : 0 < a) (p : ElementaryPlaquette a) {x : LatticePoint a}
    (hx : x ∈ p.cornerSet) (ν : Fin 4) :
    (p.corner : AmbientSpace) ν ≤ (x : AmbientSpace) ν := by
  obtain ⟨i, rfl⟩ := (mem_cornerSet_iff p x).mp hx
  rw [vertex_apply]
  have h₁ : (0 : ℝ) ≤ (lowOffset i : ℝ) * (if ν = p.lowAxis then a else 0) := by
    refine mul_nonneg ?_ (by split_ifs <;> simp [ha.le])
    fin_cases i <;> simp [lowOffset]
  have h₂ : (0 : ℝ) ≤ (highOffset i : ℝ) * (if ν = p.highAxis then a else 0) := by
    refine mul_nonneg ?_ (by split_ifs <;> simp [ha.le])
    fin_cases i <;> simp [highOffset]
  linarith
theorem corner_mem_cornerSet (p : ElementaryPlaquette a) : p.corner ∈ p.cornerSet :=
  (mem_cornerSet_iff p _).mpr ⟨0, rfl⟩
theorem axis_of_step_mem (ha : 0 < a) (p : ElementaryPlaquette a) {μ : Fin 4}
    (h : p.corner + axisStep a μ ∈ p.cornerSet) : μ = p.lowAxis ∨ μ = p.highAxis := by
  by_contra hc
  obtain ⟨i, hi⟩ := (mem_cornerSet_iff p _).mp h
  have h' := congrFun (congrArg Subtype.val hi) μ
  rw [vertex_apply] at h'
  have h₁ : μ ≠ p.lowAxis := fun e => hc (Or.inl e)
  have h₂ : μ ≠ p.highAxis := fun e => hc (Or.inr e)
  have h₃ : ((p.corner + axisStep a μ : LatticePoint a) : AmbientSpace) μ =
      (p.corner : AmbientSpace) μ + ((axisStep a μ : LatticePoint a) : AmbientSpace) μ := rfl
  rw [h₃, axisStep_apply, if_pos rfl, if_neg h₁, if_neg h₂] at h'
  simp only [mul_zero, add_zero] at h'
  linarith
theorem eq_of_cornerSet_eq (ha : 0 < a) (p p' : ElementaryPlaquette a)
    (h : p.cornerSet = p'.cornerSet) : p = p' := by
  have hbase : p.corner = p'.corner := by
    refine Subtype.ext (funext fun ν => le_antisymm ?_ ?_)
    · exact corner_le_of_mem_cornerSet ha p (h ▸ corner_mem_cornerSet p') ν
    · exact corner_le_of_mem_cornerSet ha p' (h ▸ corner_mem_cornerSet p) ν
  have hmem₁ : p.corner + axisStep a p.lowAxis ∈ p.cornerSet :=
    (mem_cornerSet_iff p _).mpr ⟨1, rfl⟩
  have hmem₂ : p.corner + axisStep a p.highAxis ∈ p.cornerSet :=
    (mem_cornerSet_iff p _).mpr ⟨3, rfl⟩
  rw [h, hbase] at hmem₁ hmem₂
  have h₁ := axis_of_step_mem ha p' hmem₁
  have h₂ := axis_of_step_mem ha p' hmem₂
  have hlt := p.lowAxis_lt_highAxis
  have hlt' := p'.lowAxis_lt_highAxis
  refine ElementaryPlaquette.ext hbase ?_ ?_
  · rcases h₁ with e₁ | e₁
    · exact e₁
    · rcases h₂ with e₂ | e₂
      · rw [e₁, e₂] at hlt
        exact absurd hlt (not_lt.mpr hlt'.le)
      · rw [e₁, e₂] at hlt
        exact absurd hlt (lt_irrefl _)
  · rcases h₂ with e₂ | e₂
    · rcases h₁ with e₁ | e₁
      · rw [e₁, e₂] at hlt
        exact absurd hlt (lt_irrefl _)
      · rw [e₁, e₂] at hlt
        exact absurd hlt (not_lt.mpr hlt'.le)
    · exact e₂
theorem forwardFrom_inj (ha : 0 < a) {x x' : LatticePoint a} {μ μ' : Fin 4}
    (h : Link.forwardFrom x μ = Link.forwardFrom x' μ') : x = x' ∧ μ = μ' := by apply _root_.YangMills.Construction.InfiniteLattice.OneSpacing.forwardFrom_inj <;> assumption
def edgeAt (p : ElementaryPlaquette a) : Fin 4 → Link a :=
  ![Link.forwardFrom p.corner p.lowAxis,
    Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis,
    Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis,
    Link.forwardFrom p.corner p.highAxis]
theorem mem_linkSet_iff (p : ElementaryPlaquette a) (b : Link a) :
    b ∈ p.linkSet ↔ ∃ i, edgeAt p i = b := by
  simp only [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges, mem_ofPred_eq, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
theorem edgeAt_injective (ha : 0 < a) (p : ElementaryPlaquette a) :
    Function.Injective (edgeAt p) := by
  have hd : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  have h₁ : ∀ x : LatticePoint a, x + axisStep a p.lowAxis ≠ x := fun x e =>
    axisStep_ne_zero ha _ (add_eq_left.mp e)
  have h₂ : ∀ x : LatticePoint a, x + axisStep a p.highAxis ≠ x := fun x e =>
    axisStep_ne_zero ha _ (add_eq_left.mp e)
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd (forwardFrom_inj ha h).2 hd
  · exact absurd (forwardFrom_inj ha h).1.symm (h₂ _)
  · exact absurd (forwardFrom_inj ha h).2 hd
  · exact absurd (forwardFrom_inj ha h).2 hd.symm
  · rfl
  · exact absurd (forwardFrom_inj ha h).2 hd.symm
  · exact absurd (forwardFrom_inj ha h).1 (h₁ _)
  · exact absurd (forwardFrom_inj ha h).1 (h₂ _)
  · exact absurd (forwardFrom_inj ha h).2 hd
  · rfl
  · exact absurd (forwardFrom_inj ha h).2 hd
  · exact absurd (forwardFrom_inj ha h).2 hd.symm
  · exact absurd (forwardFrom_inj ha h).1.symm (h₁ _)
  · exact absurd (forwardFrom_inj ha h).2 hd.symm
  · rfl
def faceAlong (x : LatticePoint a) (κ : Fin 4) (t : {l : Fin 4 // l ≠ κ} × Bool) :
    ElementaryPlaquette a where
  corner := if t.2 then x else x - axisStep a t.1.1
  lowAxis := min κ t.1.1
  highAxis := max κ t.1.1
  lowAxis_lt_highAxis := min_lt_max.mpr t.1.2.symm
theorem eq_of_min_max_eq : ∀ κ l l' : Fin 4, l ≠ κ → l' ≠ κ → min κ l = min κ l' →
    max κ l = max κ l' → l = l' := by decide
theorem faceAlong_injective (ha : 0 < a) (x : LatticePoint a) (κ : Fin 4) :
    Function.Injective (faceAlong x κ) := by
  rintro ⟨⟨l, hl⟩, s⟩ ⟨⟨l', hl'⟩, s'⟩ h
  have hll : l = l' := eq_of_min_max_eq κ l l' hl hl'
    (congrArg ElementaryPlaquette.lowAxis h) (congrArg ElementaryPlaquette.highAxis h)
  subst hll
  have hb : (if s then x else x - axisStep a l) = if s' then x else x - axisStep a l :=
    congrArg ElementaryPlaquette.corner h
  have hne : x ≠ x - axisStep a l := fun e => axisStep_ne_zero ha l (sub_eq_self.mp e.symm)
  cases s <;> cases s' <;> simp_all
theorem forwardFrom_mem_faceAlong (x : LatticePoint a) (κ : Fin 4)
    (t : {l : Fin 4 // l ≠ κ} × Bool) :
    Link.forwardFrom x κ ∈ (faceAlong x κ t).linkSet := by
  obtain ⟨⟨l, hl⟩, s⟩ := t
  rw [mem_linkSet_iff]
  rcases lt_or_gt_of_ne hl with h | h
  · have hf : (faceAlong x κ (⟨l, hl⟩, s)).lowAxis = l := min_eq_right h.le
    have hs : (faceAlong x κ (⟨l, hl⟩, s)).highAxis = κ := max_eq_left h.le
    cases s
    · have hb : (faceAlong x κ (⟨l, hl⟩, false)).corner = x - axisStep a l := by
        simp [faceAlong]
      refine ⟨1, ?_⟩
      change Link.forwardFrom ((faceAlong x κ (⟨l, hl⟩, false)).corner +
        axisStep a (faceAlong x κ (⟨l, hl⟩, false)).lowAxis)
        (faceAlong x κ (⟨l, hl⟩, false)).highAxis = _
      rw [hb, hf, hs, sub_add_cancel]
    · have hb : (faceAlong x κ (⟨l, hl⟩, true)).corner = x := by simp [faceAlong]
      refine ⟨3, ?_⟩
      change Link.forwardFrom (faceAlong x κ (⟨l, hl⟩, true)).corner
        (faceAlong x κ (⟨l, hl⟩, true)).highAxis = _
      rw [hb, hs]
  · have hf : (faceAlong x κ (⟨l, hl⟩, s)).lowAxis = κ := min_eq_left h.le
    have hs : (faceAlong x κ (⟨l, hl⟩, s)).highAxis = l := max_eq_right h.le
    cases s
    · have hb : (faceAlong x κ (⟨l, hl⟩, false)).corner = x - axisStep a l := by
        simp [faceAlong]
      refine ⟨2, ?_⟩
      change Link.forwardFrom ((faceAlong x κ (⟨l, hl⟩, false)).corner +
        axisStep a (faceAlong x κ (⟨l, hl⟩, false)).highAxis)
        (faceAlong x κ (⟨l, hl⟩, false)).lowAxis = _
      rw [hb, hf, hs, sub_add_cancel]
    · have hb : (faceAlong x κ (⟨l, hl⟩, true)).corner = x := by simp [faceAlong]
      refine ⟨0, ?_⟩
      change Link.forwardFrom (faceAlong x κ (⟨l, hl⟩, true)).corner
        (faceAlong x κ (⟨l, hl⟩, true)).lowAxis = _
      rw [hb, hf]
theorem exists_faceAlong_eq (ha : 0 < a) (x : LatticePoint a) (κ : Fin 4)
    (p : ElementaryPlaquette a) (h : Link.forwardFrom x κ ∈ p.linkSet) :
    ∃ t, faceAlong x κ t = p := by
  have hlt := p.lowAxis_lt_highAxis
  obtain ⟨i, hi⟩ := (mem_linkSet_iff p _).mp h
  fin_cases i
  · obtain ⟨rfl, rfl⟩ := forwardFrom_inj ha hi
    exact ⟨(⟨p.highAxis, hlt.ne'⟩, true),
      ElementaryPlaquette.ext rfl (min_eq_left hlt.le) (max_eq_right hlt.le)⟩
  · obtain ⟨rfl, rfl⟩ := forwardFrom_inj ha hi
    exact ⟨(⟨p.lowAxis, hlt.ne⟩, false),
      ElementaryPlaquette.ext (add_sub_cancel_right _ _) (min_eq_right hlt.le) (max_eq_left hlt.le)⟩
  · obtain ⟨rfl, rfl⟩ := forwardFrom_inj ha hi
    exact ⟨(⟨p.highAxis, hlt.ne'⟩, false),
      ElementaryPlaquette.ext (add_sub_cancel_right _ _) (min_eq_left hlt.le) (max_eq_right hlt.le)⟩
  · obtain ⟨rfl, rfl⟩ := forwardFrom_inj ha hi
    exact ⟨(⟨p.lowAxis, hlt.ne⟩, true),
      ElementaryPlaquette.ext rfl (min_eq_right hlt.le) (max_eq_left hlt.le)⟩
theorem card_otherAxes : ∀ κ : Fin 4,
    Fintype.card ({l : Fin 4 // l ≠ κ} × Bool) = 6 := by decide
theorem realTrace_conj_inv : RealTraceConjInvInvariant := by
  intro g V
  constructor
  · have h₁ : ((g * V * g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
        ((g * V : ComplexMatrix2.specialUnitary) : ComplexMatrix2) *
          ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := rfl
    have h₂ : ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) *
        ((g * V : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
        ((g⁻¹ * (g * V) : ComplexMatrix2.specialUnitary) : ComplexMatrix2) := rfl
    rw [h₁, ComplexMatrix2.fullTrace, Matrix.trace_mul_comm, h₂, inv_mul_cancel_left]
  · have h₁ : ((V⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) =
        star (V : ComplexMatrix2) := rfl
    rw [h₁, ComplexMatrix2.fullTrace, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
    simp
theorem faceEnergyIndependent_of_plaquetteProperties (hF : PlaquettePropertiesAllMeshes.Statement) :
    FaceEnergyIndependentOfBasepointAndOrientation := by
  refine ⟨realTrace_conj_inv, fun a ha => ?_⟩
  obtain ⟨hbound, hloop, hsides, -, hlocal, -⟩ := hF a ha
  have hsides' : ∀ p : ElementaryPlaquette a, edgesOf p = p.linkSet := by
    intro p
    ext b
    rw [hsides p b]
    simp only [edgesOf, mem_ofPred_eq, mem_positiveLinks_iff]
  have hcircuit : ∀ (p : ElementaryPlaquette a) (U : GaugeField a) (c : BoundaryCycle p),
      (ComplexMatrix2.fullTrace (c.holonomy U : ComplexMatrix2)).re =
        (ComplexMatrix2.fullTrace (faceHolonomy U p : ComplexMatrix2)).re := by
    intro p U c
    have h := hloop p U ⟨c.v₁, c.v₂, c.adj₁₂⟩ ⟨c.v₂, c.v₃, c.adj₂₃⟩
      ⟨c.v₃, c.v₄, c.adj₃₄⟩ ⟨c.v₄, c.v₁, c.adj₄₁⟩ c.corners_eq rfl rfl rfl rfl
    exact mul_left_cancel₀ (by norm_num) h
  refine ⟨fun p U => ⟨fun c c' => ?_, card_boundaryCycle ha p, exists_boundaryCycle_holonomy_eq p U, ?_⟩,
    fun p => ⟨?_, ?_, ?_, fun U => ?_⟩, eq_of_cornerSet_eq ha, ?_⟩
  · rw [hcircuit p U c, hcircuit p U c']
  · intro p' hc
    rw [eq_of_cornerSet_eq ha p' p hc]
  · rw [hsides' p]
    have : p.linkSet = edgeAt p '' univ := by
      ext b
      simp [mem_linkSet_iff]
    rw [this, ncard_image_of_injective _ (edgeAt_injective ha p), ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  · obtain ⟨⟨hobs, hloc, hcont⟩, -⟩ := hlocal p
    exact ⟨hcont, hobs, hloc⟩
  · intro U U' hU
    have hdep := (hlocal p).2 U U' fun b hb =>
      congrFun hU ⟨b, (hsides' p).symm ▸ hb⟩
    exact Complex.ofReal_injective hdep
  · exact hbound p U
  · intro b hb
    obtain ⟨x, κ, rfl⟩ := hb
    have hset : {p : ElementaryPlaquette a | Link.forwardFrom x κ ∈ edgesOf p} =
        faceAlong x κ '' univ := by
      ext p
      simp only [mem_ofPred_eq, hsides' p, image_univ, mem_range]
      exact ⟨exists_faceAlong_eq ha x κ p, fun ⟨t, ht⟩ => ht ▸ forwardFrom_mem_faceAlong x κ t⟩
    rw [hset, ncard_image_of_injective _ (faceAlong_injective ha x κ), ncard_univ,
      Nat.card_eq_fintype_card]
    exact card_otherAxes κ
end YangMills.Construction.GibbsAtFixedSpacing.FaceEnergyInvariance
