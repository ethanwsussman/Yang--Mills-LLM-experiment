import YangMills.Construction.InfiniteLattice.FactsOfTheBondsConfigurationsAndMotionsAtOneSpacingProof
import YangMills.Construction.InfiniteLattice.FactsOfThePlaquettesAtEverySpacing
import YangMills.Construction.InfiniteLattice.MeasurabilityIsDependenceOnVariablesAtEverySpacing
import YangMills.Construction.LawInAState.CovarianceBelowTheAveragesProof
import YangMills.Construction.SourcesAndGluing.CumulantsOfBoundedVariablesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PlaquetteProperties
variable {a : ℝ}
def cyclicCorner (p : ElementaryPlaquette a) : Fin 4 → LatticePoint a :=
  ![p.corner, p.corner + axisStep a p.lowAxis, p.corner + axisStep a p.lowAxis + axisStep a p.highAxis,
    p.corner + axisStep a p.highAxis]
def cyclicEdge (p : ElementaryPlaquette a) : Fin 4 → Link a :=
  ![Link.forwardFrom p.corner p.lowAxis, Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis,
    (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis).opposite,
    (Link.forwardFrom p.corner p.highAxis).opposite]
def halfReTrace (g : Matrices.ComplexMatrix2.specialUnitary) : ℝ :=
  (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (g : Matrices.ComplexMatrix2)).re
theorem cyclicEdge_ends (p : ElementaryPlaquette a) (i : Fin 4) :
    (cyclicEdge p i).initial = cyclicCorner p i ∧ (cyclicEdge p i).terminal = cyclicCorner p (i + 1) := by
  fin_cases i
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨add_right_comm _ _ _, rfl⟩
  · exact ⟨rfl, rfl⟩
theorem mem_cornerSet_iff (p : ElementaryPlaquette a) (x : LatticePoint a) :
    x ∈ p.cornerSet ↔ ∃ i, x = cyclicCorner p i := by
  simp only [ElementaryPlaquette.cornerSet, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
theorem axisStep_apply (μ ν : Fin 4) :
    ((axisStep a μ : LatticePoint a) : AmbientSpace) ν = if ν = μ then a else 0 := by apply _root_.YangMills.SharedProofs.p59492 <;> assumption
theorem coord_eq_zero_or_of_axis {d : LatticePoint a} {ν : Fin 4}
    (h : d = axisStep a ν ∨ d = -axisStep a ν)
    {μ κ : Fin 4} (hμκ : μ ≠ κ) : (d : AmbientSpace) μ = 0 ∨ (d : AmbientSpace) κ = 0 := by
  by_cases hμ : μ = ν
  · right
    have hκ : κ ≠ ν := fun e => hμκ (hμ.trans e.symm)
    rcases h with rfl | rfl
    · simp [axisStep_apply, hκ]
    · simp [axisStep_apply, hκ]
  · left
    rcases h with rfl | rfl
    · simp [axisStep_apply, hμ]
    · simp [axisStep_apply, hμ]
theorem axisStep_ne_zero (ha : 0 < a) (μ : Fin 4) : axisStep a μ ≠ 0 := by apply _root_.YangMills.Construction.InfiniteLattice.OneSpacing.axisStep_ne_zero <;> assumption
theorem cyclicCorner_injective (ha : 0 < a) (p : ElementaryPlaquette a) :
    Function.Injective (cyclicCorner p) := by
  have hne : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  have ha0 : a ≠ 0 := ha.ne'
  intro i j h
  have h₁ : ((cyclicCorner p i : LatticePoint a) : AmbientSpace) p.lowAxis =
      ((cyclicCorner p j : LatticePoint a) : AmbientSpace) p.lowAxis := by rw [h]
  have h₂ : ((cyclicCorner p i : LatticePoint a) : AmbientSpace) p.highAxis =
      ((cyclicCorner p j : LatticePoint a) : AmbientSpace) p.highAxis := by rw [h]
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exfalso
       simp [cyclicCorner, axisStep_apply, hne, hne.symm, ha0] at h₁ h₂)
theorem consecutive_of_link_ends (ha : 0 < a) (p : ElementaryPlaquette a) (b : Link a) (i j : Fin 4)
    (ht : b.initial = cyclicCorner p i) (hh : b.terminal = cyclicCorner p j) :
    j = i + 1 ∨ i = j + 1 := by
  have hne : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  have ha0 : a ≠ 0 := ha.ne'
  obtain ⟨ν, hν⟩ := b.isAdjacent
  have hd := coord_eq_zero_or_of_axis hν hne
  have hne0 : b.terminal - b.initial ≠ 0 := by
    rcases hν with h | h <;> rw [h]
    · exact axisStep_ne_zero ha ν
    · exact neg_ne_zero.mpr (axisStep_ne_zero ha ν)
  rw [ht, hh] at hd hne0
  fin_cases i <;> fin_cases j <;> first
    | (left; rfl)
    | (right; rfl)
    | (exfalso; exact hne0 (sub_self _))
    | (exfalso
       simp [cyclicCorner, axisStep_apply, hne, hne.symm, ha0] at hd)
theorem eq_cyclicEdge {p : ElementaryPlaquette a} {b : Link a} {i : Fin 4}
    (ht : b.initial = cyclicCorner p i) (hh : b.terminal = cyclicCorner p (i + 1)) :
    b = cyclicEdge p i :=
  Link.ext (ht.trans (cyclicEdge_ends p i).1.symm) (hh.trans (cyclicEdge_ends p i).2.symm)
theorem eq_opposite_cyclicEdge {p : ElementaryPlaquette a} {b : Link a} {j : Fin 4}
    (ht : b.initial = cyclicCorner p (j + 1)) (hh : b.terminal = cyclicCorner p j) :
    b = (cyclicEdge p j).opposite :=
  Link.ext (ht.trans (cyclicEdge_ends p j).2.symm) (hh.trans (cyclicEdge_ends p j).1.symm)
theorem halfReTrace_mul_comm (g h : Matrices.ComplexMatrix2.specialUnitary) :
    halfReTrace (g * h) = halfReTrace (h * g) := by
  unfold halfReTrace
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Matrices.ComplexMatrix2.fullTrace,
    Matrices.ComplexMatrix2.fullTrace, Matrix.trace_mul_comm]
theorem halfReTrace_inv (g : Matrices.ComplexMatrix2.specialUnitary) :
    halfReTrace g⁻¹ = halfReTrace g := by
  have h : ((g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      Matrix.conjTranspose (g : Matrices.ComplexMatrix2) := rfl
  unfold halfReTrace
  rw [h, Matrices.ComplexMatrix2.fullTrace, Matrices.ComplexMatrix2.fullTrace,
    Matrix.trace_conjTranspose]
  simp
theorem halfReTrace_rotate (g : Fin 4 → Matrices.ComplexMatrix2.specialUnitary) (i : Fin 4) :
    halfReTrace (g i * g (i + 1) * g (i + 2) * g (i + 3)) =
      halfReTrace (g 0 * g 1 * g 2 * g 3) := by
  fin_cases i
  · rfl
  · change halfReTrace (g 1 * g 2 * g 3 * g 0) = _
    rw [halfReTrace_mul_comm]
    simp only [mul_assoc]
  · change halfReTrace (g 2 * g 3 * g 0 * g 1) = _
    rw [halfReTrace_mul_comm, ← mul_assoc, halfReTrace_mul_comm]
    simp only [mul_assoc]
  · change halfReTrace (g 3 * g 0 * g 1 * g 2) = _
    rw [mul_assoc (g 3), mul_assoc (g 3), halfReTrace_mul_comm]
theorem prod_cyclicEdge_eq_faceHolonomy (U : GaugeField a) (p : ElementaryPlaquette a) :
    U (cyclicEdge p 0) * U (cyclicEdge p 1) * U (cyclicEdge p 2) * U (cyclicEdge p 3) =
      faceHolonomy U p := by
  have hrev : ∀ b : Link a, U b.opposite = (U b)⁻¹ := U.2
  change U (Link.forwardFrom p.corner p.lowAxis) *
      U (Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis) *
      U (Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis).opposite *
      U (Link.forwardFrom p.corner p.highAxis).opposite = _
  rw [hrev, hrev]
  rfl
theorem cyclic_order_of_consecutive : ∀ i₀ i₁ i₂ i₃ : Fin 4,
    (∀ j : Fin 4, j = i₀ ∨ j = i₁ ∨ j = i₂ ∨ j = i₃) →
    (i₁ = i₀ + 1 ∨ i₀ = i₁ + 1) → (i₂ = i₁ + 1 ∨ i₁ = i₂ + 1) → (i₃ = i₂ + 1 ∨ i₂ = i₃ + 1) →
    (i₁ = i₀ + 1 ∧ i₂ = i₀ + 2 ∧ i₃ = i₀ + 3) ∨ (i₁ = i₀ + 3 ∧ i₂ = i₀ + 2 ∧ i₃ = i₀ + 1) := by
  decide
theorem fin_four_add_one_add_one : ∀ i : Fin 4, i + 1 + 1 = i + 2 := by decide
theorem fin_four_add_two_add_one : ∀ i : Fin 4, i + 2 + 1 = i + 3 := by decide
theorem fin_four_add_three_add_one : ∀ i : Fin 4, i + 3 + 1 = i := by decide
theorem halfReTrace_closed_loop (ha : 0 < a) (p : ElementaryPlaquette a) (U : GaugeField a)
    (b₀ b₁ b₂ b₃ : Link a)
    (hc : ({b₀.initial, b₁.initial, b₂.initial, b₃.initial} : Set (LatticePoint a)) = p.cornerSet)
    (h₀ : b₀.terminal = b₁.initial) (h₁ : b₁.terminal = b₂.initial) (h₂ : b₂.terminal = b₃.initial)
    (h₃ : b₃.terminal = b₀.initial) :
    halfReTrace (U b₀ * U b₁ * U b₂ * U b₃) = halfReTrace (faceHolonomy U p) := by
  obtain ⟨i₀, t₀⟩ := (mem_cornerSet_iff p b₀.initial).1 (hc ▸ by simp)
  obtain ⟨i₁, t₁⟩ := (mem_cornerSet_iff p b₁.initial).1 (hc ▸ by simp)
  obtain ⟨i₂, t₂⟩ := (mem_cornerSet_iff p b₂.initial).1 (hc ▸ by simp)
  obtain ⟨i₃, t₃⟩ := (mem_cornerSet_iff p b₃.initial).1 (hc ▸ by simp)
  have hcover : ∀ j : Fin 4, j = i₀ ∨ j = i₁ ∨ j = i₂ ∨ j = i₃ := by
    intro j
    have hj : cyclicCorner p j ∈ p.cornerSet := (mem_cornerSet_iff p _).2 ⟨j, rfl⟩
    rw [← hc] at hj
    simp only [mem_insert_iff, mem_singleton_iff, t₀, t₁, t₂, t₃] at hj
    have hinj := cyclicCorner_injective ha p
    rcases hj with h | h | h | h
    · exact Or.inl (hinj h)
    · exact Or.inr (Or.inl (hinj h))
    · exact Or.inr (Or.inr (Or.inl (hinj h)))
    · exact Or.inr (Or.inr (Or.inr (hinj h)))
  have a₀ := consecutive_of_link_ends ha p b₀ i₀ i₁ t₀ (h₀.trans t₁)
  have a₁ := consecutive_of_link_ends ha p b₁ i₁ i₂ t₁ (h₁.trans t₂)
  have a₂ := consecutive_of_link_ends ha p b₂ i₂ i₃ t₂ (h₂.trans t₃)
  have hround : halfReTrace (U (cyclicEdge p 0) * U (cyclicEdge p 1) * U (cyclicEdge p 2) *
      U (cyclicEdge p 3)) = halfReTrace (faceHolonomy U p) := by
    rw [prod_cyclicEdge_eq_faceHolonomy]
  have hcyc : halfReTrace (U (cyclicEdge p i₀) * U (cyclicEdge p (i₀ + 1)) *
      U (cyclicEdge p (i₀ + 2)) * U (cyclicEdge p (i₀ + 3))) =
      halfReTrace (U (cyclicEdge p 0) * U (cyclicEdge p 1) * U (cyclicEdge p 2) *
        U (cyclicEdge p 3)) :=
    halfReTrace_rotate (fun j => U (cyclicEdge p j)) i₀
  rcases cyclic_order_of_consecutive i₀ i₁ i₂ i₃ hcover a₀ a₁ a₂ with ⟨e₁, e₂, e₃⟩ | ⟨e₁, e₂, e₃⟩
  · subst e₁ e₂ e₃
    have f₀ : b₀ = cyclicEdge p i₀ := eq_cyclicEdge t₀ (h₀.trans t₁)
    have f₁ : b₁ = cyclicEdge p (i₀ + 1) :=
      eq_cyclicEdge t₁ (by rw [fin_four_add_one_add_one]; exact h₁.trans t₂)
    have f₂ : b₂ = cyclicEdge p (i₀ + 2) :=
      eq_cyclicEdge t₂ (by rw [fin_four_add_two_add_one]; exact h₂.trans t₃)
    have f₃ : b₃ = cyclicEdge p (i₀ + 3) :=
      eq_cyclicEdge t₃ (by rw [fin_four_add_three_add_one]; exact h₃.trans t₀)
    rw [f₀, f₁, f₂, f₃, hcyc, hround]
  · subst e₁ e₂ e₃
    have f₀ : b₀ = (cyclicEdge p (i₀ + 3)).opposite :=
      eq_opposite_cyclicEdge (by rw [fin_four_add_three_add_one]; exact t₀) (h₀.trans t₁)
    have f₁ : b₁ = (cyclicEdge p (i₀ + 2)).opposite :=
      eq_opposite_cyclicEdge (by rw [fin_four_add_two_add_one]; exact t₁) (h₁.trans t₂)
    have f₂ : b₂ = (cyclicEdge p (i₀ + 1)).opposite :=
      eq_opposite_cyclicEdge (by rw [fin_four_add_one_add_one]; exact t₂) (h₂.trans t₃)
    have f₃ : b₃ = (cyclicEdge p i₀).opposite := eq_opposite_cyclicEdge t₃ (h₃.trans t₀)
    have hrev : ∀ b : Link a, U b.opposite = (U b)⁻¹ := U.2
    have hprod : U b₀ * U b₁ * U b₂ * U b₃ =
        (U (cyclicEdge p i₀) * U (cyclicEdge p (i₀ + 1)) * U (cyclicEdge p (i₀ + 2)) *
          U (cyclicEdge p (i₀ + 3)))⁻¹ := by
      rw [f₀, f₁, f₂, f₃, hrev, hrev, hrev, hrev]
      simp only [mul_inv_rev, mul_assoc]
    rw [hprod, halfReTrace_inv, hcyc, hround]
theorem forwardFrom_isPositivelyOriented (x : LatticePoint a) (μ : Fin 4) :
    (Link.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, add_sub_cancel_left _ _⟩
theorem forwardFrom_corner_lowAxis_mem_linkSet (p : ElementaryPlaquette a) :
    Link.forwardFrom p.corner p.lowAxis ∈ p.linkSet := by
  simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges]
theorem forwardFrom_lowNeighbour_highAxis_mem_linkSet (p : ElementaryPlaquette a) :
    Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis ∈ p.linkSet := by
  simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges]
theorem forwardFrom_highNeighbour_lowAxis_mem_linkSet (p : ElementaryPlaquette a) :
    Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis ∈ p.linkSet := by
  simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges]
theorem forwardFrom_corner_highAxis_mem_linkSet (p : ElementaryPlaquette a) :
    Link.forwardFrom p.corner p.highAxis ∈ p.linkSet := by
  simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges]
theorem mem_linkSet_iff (p : ElementaryPlaquette a) (b : Link a) :
    b ∈ p.linkSet ↔ b = Link.forwardFrom p.corner p.lowAxis ∨
      b = Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis ∨
      b = Link.forwardFrom (p.corner + axisStep a p.highAxis) p.lowAxis ∨
      b = Link.forwardFrom p.corner p.highAxis := by
  simp [ElementaryPlaquette.linkSet, ElementaryPlaquette.edges]
theorem cyclicEdge_mem_linkSet (ha : 0 < a) (p : ElementaryPlaquette a) (i : Fin 4)
    (h : (cyclicEdge p i).IsPositivelyOriented) : cyclicEdge p i ∈ p.linkSet := by
  fin_cases i
  · exact forwardFrom_corner_lowAxis_mem_linkSet p
  · exact forwardFrom_lowNeighbour_highAxis_mem_linkSet p
  · exact absurd h (Link.opposite_not_isPositivelyOriented ha (forwardFrom_isPositivelyOriented _ _))
  · exact absurd h (Link.opposite_not_isPositivelyOriented ha (forwardFrom_isPositivelyOriented _ _))
theorem opposite_cyclicEdge_mem_linkSet (ha : 0 < a) (p : ElementaryPlaquette a) (i : Fin 4)
    (h : (cyclicEdge p i).opposite.IsPositivelyOriented) :
    (cyclicEdge p i).opposite ∈ p.linkSet := by
  fin_cases i
  · exact absurd h (Link.opposite_not_isPositivelyOriented ha (forwardFrom_isPositivelyOriented _ _))
  · exact absurd h (Link.opposite_not_isPositivelyOriented ha (forwardFrom_isPositivelyOriented _ _))
  · exact forwardFrom_highNeighbour_lowAxis_mem_linkSet p
  · exact forwardFrom_corner_highAxis_mem_linkSet p
theorem opposite_corner_comm (p : ElementaryPlaquette a) :
    p.corner + axisStep a p.highAxis + axisStep a p.lowAxis = cyclicCorner p 2 :=
  add_right_comm _ _ _
theorem mem_linkSet_iff_ends (ha : 0 < a) (p : ElementaryPlaquette a) (b : Link a) :
    b ∈ p.linkSet ↔ b.IsPositivelyOriented ∧ b.initial ∈ p.cornerSet ∧ b.terminal ∈ p.cornerSet := by
  constructor
  · intro hb
    have hc : ∀ i, cyclicCorner p i ∈ p.cornerSet := fun i => (mem_cornerSet_iff p _).2 ⟨i, rfl⟩
    rcases (mem_linkSet_iff p b).1 hb with rfl | rfl | rfl | rfl
    · exact ⟨forwardFrom_isPositivelyOriented _ _, hc 0, hc 1⟩
    · exact ⟨forwardFrom_isPositivelyOriented _ _, hc 1, hc 2⟩
    · refine ⟨forwardFrom_isPositivelyOriented _ _, hc 3, ?_⟩
      change p.corner + axisStep a p.highAxis + axisStep a p.lowAxis ∈ p.cornerSet
      rw [opposite_corner_comm]
      exact hc 2
    · exact ⟨forwardFrom_isPositivelyOriented _ _, hc 0, hc 3⟩
  · rintro ⟨hpos, ht, hh⟩
    obtain ⟨i, hi⟩ := (mem_cornerSet_iff p _).1 ht
    obtain ⟨j, hj⟩ := (mem_cornerSet_iff p _).1 hh
    rcases consecutive_of_link_ends ha p b i j hi hj with e | e
    · subst e
      have hb := eq_cyclicEdge hi hj
      rw [hb] at hpos ⊢
      exact cyclicEdge_mem_linkSet ha p i hpos
    · subst e
      have hb := eq_opposite_cyclicEdge hi hj
      rw [hb] at hpos ⊢
      exact opposite_cyclicEdge_mem_linkSet ha p j hpos
theorem exists_link_of_mem_cornerSet (p : ElementaryPlaquette a) (x : LatticePoint a)
    (hx : x ∈ p.cornerSet) : ∃ b ∈ p.linkSet, x = b.initial ∨ x = b.terminal := by
  obtain ⟨i, rfl⟩ := (mem_cornerSet_iff p x).1 hx
  fin_cases i
  · exact ⟨_, forwardFrom_corner_lowAxis_mem_linkSet p, Or.inl rfl⟩
  · exact ⟨_, forwardFrom_corner_lowAxis_mem_linkSet p, Or.inr rfl⟩
  · exact ⟨_, forwardFrom_lowNeighbour_highAxis_mem_linkSet p, Or.inr rfl⟩
  · exact ⟨_, forwardFrom_corner_highAxis_mem_linkSet p, Or.inr rfl⟩
theorem abs_re_fullTrace_le_two (g : Matrices.ComplexMatrix2.specialUnitary) :
    |(Matrices.ComplexMatrix2.fullTrace (g : Matrices.ComplexMatrix2)).re| ≤ 2 := by apply _root_.YangMills.Construction.SourcesAndGluing.BoundedCumulants.abs_re_fullTrace_le <;> assumption
theorem faceEnergy_mem_Icc (p : ElementaryPlaquette a) (U : GaugeField a) :
    faceEnergy U p ∈ Icc (0 : ℝ) 2 := by
  have h := abs_le.1 (abs_re_fullTrace_le_two (faceHolonomy U p))
  unfold faceEnergy
  constructor <;> linarith [h.1, h.2]
theorem continuous_eval_link (b : Link a) : Continuous fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem continuous_faceEnergy (p : ElementaryPlaquette a) :
    Continuous fun U : GaugeField a => (faceEnergy U p : ℂ) := by
  have hv : Continuous fun U : GaugeField a => faceHolonomy U p := by
    unfold faceHolonomy
    exact (((continuous_eval_link _).mul (continuous_eval_link _)).mul
      (continuous_eval_link _).inv).mul (continuous_eval_link _).inv
  refine Complex.continuous_ofReal.comp ?_
  unfold faceEnergy
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp
    (Continuous.matrix_trace (continuous_subtype_val.comp hv))))
theorem faceEnergy_dependsOnlyOn (p : ElementaryPlaquette a) :
    DependsOnlyOn p.linkSet fun U : GaugeField a => (faceEnergy U p : ℂ) := by
  intro U U' h
  have e₁ := h _ (forwardFrom_corner_lowAxis_mem_linkSet p)
  have e₂ := h _ (forwardFrom_lowNeighbour_highAxis_mem_linkSet p)
  have e₃ := h _ (forwardFrom_highNeighbour_lowAxis_mem_linkSet p)
  have e₄ := h _ (forwardFrom_corner_highAxis_mem_linkSet p)
  change ((faceEnergy U p : ℝ) : ℂ) = (faceEnergy U' p : ℝ)
  simp only [faceEnergy, faceHolonomy, e₁, e₂, e₃, e₄]
theorem linkSet_isLinkSet (p : ElementaryPlaquette a) : IsLinkSet p.linkSet := by
  intro b hb
  rcases (mem_linkSet_iff p b).1 hb with rfl | rfl | rfl | rfl <;>
    exact forwardFrom_isPositivelyOriented _ _
theorem linkSet_finite (p : ElementaryPlaquette a) : p.linkSet.Finite := List.finite_toSet p.edges
theorem faceEnergy_isBoundedObservable (p : ElementaryPlaquette a) :
    IsBoundedObservable fun U : GaugeField a => (faceEnergy U p : ℂ) := by apply _root_.YangMills.Construction.LatticeConventions.SymmetryGeneration.isBoundedObservable_faceEnergy <;> assumption
theorem finite_setOf_mem_linkSet (b : Link a) :
    {p : ElementaryPlaquette a | b ∈ p.linkSet}.Finite := by
  have hbase : (({b.initial} : Set (LatticePoint a)) ∪
      range fun κ : Fin 4 => b.initial - axisStep a κ).Finite :=
    (finite_singleton _).union (finite_range _)
  have hfin := (hbase.prod (finite_univ (α := Fin 4))).prod (finite_univ (α := Fin 4))
  refine Set.Finite.of_finite_image
    (f := fun p : ElementaryPlaquette a => ((p.corner, p.lowAxis), p.highAxis)) (hfin.subset ?_) ?_
  · rintro _ ⟨p, hp, rfl⟩
    have hb : p.corner ∈ ({b.initial} : Set (LatticePoint a)) ∪
        range fun κ : Fin 4 => b.initial - axisStep a κ := by
      rcases (mem_linkSet_iff p b).1 hp with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨p.lowAxis, add_sub_cancel_right _ _⟩
      · exact Or.inr ⟨p.highAxis, add_sub_cancel_right _ _⟩
      · exact Or.inl rfl
    exact ⟨⟨hb, mem_univ _⟩, mem_univ _⟩
  · intro p _ q _ h
    have h₁ := congrArg (fun t => t.1.1) h
    have h₂ := congrArg (fun t => t.1.2) h
    have h₃ := congrArg Prod.snd h
    exact ElementaryPlaquette.ext h₁ h₂ h₃
theorem facesMeeting_links_finite (W : LinkWindow a) :
    (facesMeeting (W.links : Set (Link a))).Finite := by
  refine (W.links.finite_toSet.biUnion fun b _ => finite_setOf_mem_linkSet b).subset ?_
  rintro p ⟨b, hbp, hbW⟩
  exact mem_biUnion hbW hbp
theorem statement_of_measurableIffDependsOnly (hM : MeasurableIffDependsOnlyAllSpacings) :
    PlaquettePropertiesAllMeshes.Statement := by
  intro a ha
  refine ⟨faceEnergy_mem_Icc, ?_, mem_linkSet_iff_ends ha, exists_link_of_mem_cornerSet, ?_,
    facesMeeting_links_finite⟩
  · intro p U b₀ b₁ b₂ b₃ hc h₀ h₁ h₂ h₃
    exact halfReTrace_closed_loop ha p U b₀ b₁ b₂ b₃ hc h₀ h₁ h₂ h₃
  · intro p
    have hobs := faceEnergy_isBoundedObservable p
    refine ⟨⟨hobs, ?_, continuous_faceEnergy p⟩, faceEnergy_dependsOnlyOn p⟩
    exact ((hM a ha).2.2.2 _ hobs).2
      ⟨p.linkSet, linkSet_isLinkSet p, linkSet_finite p, faceEnergy_dependsOnlyOn p⟩
end YangMills.Construction.InfiniteLattice.PlaquetteProperties
