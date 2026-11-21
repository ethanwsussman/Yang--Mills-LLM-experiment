import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.IsometriesOnExponentialsAndPlaquettesAtTheSideInfinityProof
import YangMills.Construction.Towers.IsometriesOnExponentialsAndPlaquettesOfASide
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.PeriodicSymmetryAction
theorem fin_four_adjacent_of_ne : ∀ a b : Fin 4, b ≠ a → b ≠ a + 2 → b = a + 1 ∨ a = b + 1 := by
  decide
theorem fullTrace_cyclic_product_perm (v : Fin 4 → Fin 4 → Matrices.ComplexMatrix2)
    (hdet : ∀ a, (v a (a + 1)).det = 1)
    (hrev : ∀ a, v (a + 1) a = (v a (a + 1))⁻¹) (σ : Fin 4 → Fin 4)
    (hσ : Function.Injective σ) (hn : ∀ i, σ (i + 1) = σ i + 1 ∨ σ i = σ (i + 1) + 1) :
    Matrices.ComplexMatrix2.fullTrace (v (σ 0) (σ 1) * v (σ 1) (σ 2) * v (σ 2) (σ 3) * v (σ 3) (σ 0)) =
      Matrices.ComplexMatrix2.fullTrace (v 0 1 * v 1 2 * v 2 3 * v 3 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.SymmetryFacts.fullTrace_prod_along_cycle <;> assumption
theorem matExp_conj_inv (hEl : Matrices.ComplexMatrix2.NormExpLogBasics)
    {g X : Matrices.ComplexMatrix2} (hg : g.det = 1) :
    Matrices.ComplexMatrix2.matExp (Complex.I • -Matrices.ComplexMatrix2.conjugateBy g⁻¹ X) * g⁻¹ =
      (Matrices.ComplexMatrix2.matExp (Complex.I • X) * g)⁻¹ := by apply _root_.YangMills.Construction.Tower.FullSpace.SymmetryFacts.matExp_neg_conj_mul_inv <;> assumption
variable {L n k j : ℕ}
def linkValue (W : Edge L n k j → Matrices.ComplexMatrix2) (x y : Vertex L n k j) :
    Matrices.ComplexMatrix2 :=
  W (Classical.epsilon fun b : Edge L n k j => b.source = x ∧ b.target = y)
theorem linkValue_bond (W : Edge L n k j → Matrices.ComplexMatrix2) (b : Edge L n k j) :
    linkValue W b.source b.target = W b := by
  have h := Classical.epsilon_spec
    (p := fun c : Edge L n k j => c.source = b.source ∧ c.target = b.target) ⟨b, rfl, rfl⟩
  exact congrArg W (PeriodicLattice.Bond.ext h.1 h.2)
theorem opposite_opposite (b : Edge L n k j) : b.opposite.opposite = b := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_opposite_opposite <;> assumption
def vertexAt (p : Face L n k j) : Fin 4 → Vertex L n k j :=
  ![p.origin, p.origin + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.firstAxis,
    p.origin + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.firstAxis +
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.secondAxis,
    p.origin + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.secondAxis]
theorem mem_vertices_iff {p : Face L n k j} {x : Vertex L n k j} :
    x ∈ p.vertices ↔ ∃ a, vertexAt p a = x := by
  simp only [PeriodicLattice.Plaquette.vertices, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  · rintro ⟨a, rfl⟩
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
theorem vertexAt_two_eq (p : Face L n k j) :
    p.origin + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.secondAxis +
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.firstAxis = vertexAt p 2 :=
  add_right_comm _ _ _
theorem exists_bond_vertexAt (p : Face L n k j) (a : Fin 4) :
    ∃ d : Edge L n k j, d.source = vertexAt p a ∧ d.target = vertexAt p (a + 1) := by
  fin_cases a
  · exact ⟨PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis, rfl, rfl⟩
  · exact ⟨PeriodicLattice.Bond.forwardFrom
      (p.origin + PeriodicLattice.unitStep L n _ p.firstAxis) p.secondAxis, rfl, rfl⟩
  · exact ⟨(PeriodicLattice.Bond.forwardFrom
      (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis) p.firstAxis).opposite,
      vertexAt_two_eq p, rfl⟩
  · exact ⟨(PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis).opposite, rfl, rfl⟩
theorem plaquetteHolonomy_eq_linkValue (W : Edge L n k j → Matrices.ComplexMatrix2)
    (p : Face L n k j) :
    PeriodicLattice.plaquetteHolonomy W p =
      linkValue W (vertexAt p 0) (vertexAt p 1) * linkValue W (vertexAt p 1) (vertexAt p 2) *
        linkValue W (vertexAt p 2) (vertexAt p 3) * linkValue W (vertexAt p 3) (vertexAt p 0) := by
  have h : ∀ (d : Edge L n k j) (x y : Vertex L n k j), d.source = x → d.target = y →
      W d = linkValue W x y := by
    rintro d x y rfl rfl
    exact (linkValue_bond W d).symm
  have e0 : W (PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis) =
      linkValue W (vertexAt p 0) (vertexAt p 1) :=
    h _ _ _ rfl rfl
  have e1 : W (PeriodicLattice.Bond.forwardFrom
      (p.origin + PeriodicLattice.unitStep L n _ p.firstAxis) p.secondAxis) =
      linkValue W (vertexAt p 1) (vertexAt p 2) := h _ _ _ rfl rfl
  have e2 : W (PeriodicLattice.Bond.forwardFrom
      (p.origin + PeriodicLattice.unitStep L n _ p.secondAxis) p.firstAxis).opposite =
      linkValue W (vertexAt p 2) (vertexAt p 3) := h _ _ _ (vertexAt_two_eq p) rfl
  have e3 : W (PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis).opposite =
      linkValue W (vertexAt p 3) (vertexAt p 0) := h _ _ _ rfl rfl
  simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [e0, e1, e2, e3]
  simp only [mul_assoc]
def Adjacent (x y : Vertex L n k j) : Prop :=
  ∃ μ : Fin 4, y - x = PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ ∨
    y - x = -PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ
theorem Adjacent.symm {x y : Vertex L n k j} (h : Adjacent x y) : Adjacent y x := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inr (by rw [← neg_sub, h])⟩
  · exact ⟨μ, Or.inl (by rw [← neg_sub, h, neg_neg])⟩
theorem pi_single_sum_sub_ne {A : Type*} [AddCommGroup A] {T : A} (hT : T ≠ 0) {μ ν : Fin 4}
    (h : μ ≠ ν) (c : Fin 4) :
    (Pi.single μ T + Pi.single ν T : Fin 4 → A) ≠ Pi.single c T ∧
    (Pi.single μ T + Pi.single ν T : Fin 4 → A) ≠ -Pi.single c T ∧
    (Pi.single ν T - Pi.single μ T : Fin 4 → A) ≠ Pi.single c T ∧
    (Pi.single ν T - Pi.single μ T : Fin 4 → A) ≠ -Pi.single c T := by
  by_cases hc : c = μ
  · subst hc
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    · have := congrFun e ν
      simp [Pi.single_apply, h, h.symm, hT] at this
  · have hc' : μ ≠ c := fun e => hc e.symm
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    · have := congrFun e μ
      simp [Pi.single_apply, h, h.symm, hc, hc', hT] at this
theorem vertexAt_injective (hc : FaceSums.FaceVerticesPeriodic L n k j)
    (p : Face L n k j) : Function.Injective (vertexAt p) := by
  have h := (hc p.origin p.origin p.firstAxis p.secondAxis p.firstAxis p.secondAxis
    p.firstAxis_lt_secondAxis p.firstAxis_lt_secondAxis).1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := h
  intro a b hab
  by_contra hne
  fin_cases a <;> fin_cases b <;>
    first
    | exact hne rfl
    | exact h1 hab | exact h2 hab | exact h3 hab | exact h4 hab | exact h5 hab | exact h6 hab
    | exact h1 hab.symm | exact h2 hab.symm | exact h3 hab.symm | exact h4 hab.symm
    | exact h5 hab.symm | exact h6 hab.symm
theorem not_adjacent_vertexAt_add_two (hc : FaceSums.FaceVerticesPeriodic L n k j)
    (p : Face L n k j) (a : Fin 4) : ¬ Adjacent (vertexAt p a) (vertexAt p (a + 2)) := by
  have hT : ((PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j) : ℝ) :
      AddCircle (PeriodicLattice.torusSide L n)) ≠ 0 := by
    intro h0
    have h01 : vertexAt p 0 ≠ vertexAt p 1 :=
      fun e => absurd (vertexAt_injective hc p e) (by decide)
    apply h01
    have hs : PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.firstAxis = 0 := by
      apply Subtype.ext
      change Pi.single p.firstAxis _ = 0
      rw [h0]
      simp
    change p.origin = p.origin + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.firstAxis
    rw [hs, add_zero]
  have hμν : p.firstAxis ≠ p.secondAxis := p.firstAxis_lt_secondAxis.ne
  have h02 : ¬ Adjacent (vertexAt p 0) (vertexAt p 2) := by
    rintro ⟨c, h | h⟩
    · have e : PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.firstAxis +
          PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.secondAxis =
          PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) c := by
        rw [← h]
        change _ = p.origin + _ + _ - p.origin
        abel
      exact (pi_single_sum_sub_ne hT hμν c).1 (congrArg Subtype.val e)
    · have e : PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.firstAxis +
          PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.secondAxis =
          -PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) c := by
        rw [← h]
        change _ = p.origin + _ + _ - p.origin
        abel
      exact (pi_single_sum_sub_ne hT hμν c).2.1 (congrArg Subtype.val e)
  have h13 : ¬ Adjacent (vertexAt p 1) (vertexAt p 3) := by
    rintro ⟨c, h | h⟩
    · have e : PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.secondAxis -
          PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.firstAxis =
          PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) c := by
        rw [← h]
        change _ = p.origin + _ - (p.origin + _)
        abel
      exact (pi_single_sum_sub_ne hT hμν c).2.2.1 (congrArg Subtype.val e)
    · have e : PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.secondAxis -
          PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) p.firstAxis =
          -PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) c := by
        rw [← h]
        change _ = p.origin + _ - (p.origin + _)
        abel
      exact (pi_single_sum_sub_ne hT hμν c).2.2.2 (congrArg Subtype.val e)
  fin_cases a
  · exact h02
  · exact h13
  · exact fun h => h02 h.symm
  · exact fun h => h13 h.symm
theorem vertex_injective_of_mapsOnto [Finite (Vertex L n k j)]
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hm : MapsSublatticeOnto k j f) :
    ∀ a b : Vertex L n k j, f a = f b → a = b := by
  unfold MapsSublatticeOnto at hm
  have hin : ∀ x : Vertex L n k j,
      f x ∈ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) := by
    intro x
    have h : f x ∈ f '' (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) :
        Set (PeriodicLattice.FourTorus L n)) := mem_image_of_mem f x.2
    rw [hm] at h
    exact h
  let φ : Vertex L n k j → Vertex L n k j := fun x => ⟨f x, hin x⟩
  have hs : Function.Surjective φ := by
    intro y
    have h : (y : PeriodicLattice.FourTorus L n) ∈ f '' (PeriodicLattice.sublattice L n
        (PeriodicLattice.levelDepth k j) : Set (PeriodicLattice.FourTorus L n)) := by
      rw [hm]
      exact y.2
    obtain ⟨x, hx, e⟩ := h
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  have hi : Function.Injective φ := Finite.injective_iff_surjective.mpr hs
  intro a b h
  exact hi (Subtype.ext h)
theorem vertexPreimage_eq {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hinj : ∀ a b : Vertex L n k j, f a = f b → a = b) {x x' : Vertex L n k j} (h : f x' = x) :
    vertexPreimage (k := k) (j := j) f x = x' := by
  have hs : f (vertexPreimage (k := k) (j := j) f x) = x :=
    Classical.epsilon_spec (p := fun y : Vertex L n k j => f y = x) ⟨x', h⟩
  exact hinj _ _ (hs.trans h.symm)
theorem edgePreimage_eq {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hinj : ∀ a b : Vertex L n k j, f a = f b → a = b) {c c' : Edge L n k j}
    (ht : (c'.source : PeriodicLattice.FourTorus L n) = f c.source)
    (hh : (c'.target : PeriodicLattice.FourTorus L n) = f c.target) :
    edgePreimage (k := k) (j := j) f c' = c := by
  have e1 := vertexPreimage_eq hinj ht.symm
  have e2 := vertexPreimage_eq hinj hh.symm
  have hs := Classical.epsilon_spec (p := fun b : Edge L n k j =>
      b.source = vertexPreimage (k := k) (j := j) f c'.source ∧
        b.target = vertexPreimage (k := k) (j := j) f c'.target) ⟨c, e1.symm, e2.symm⟩
  exact PeriodicLattice.Bond.ext (hs.1.trans e1) (hs.2.trans e2)
theorem edgePreimage_opposite {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hinj : ∀ a b : Vertex L n k j, f a = f b → a = b) (hb : MapsEdgesOnto k j f)
    (b : Edge L n k j) :
    edgePreimage (k := k) (j := j) f b.opposite =
      (edgePreimage (k := k) (j := j) f b).opposite := by
  obtain ⟨c, ht, hh⟩ := hb.2 b
  rw [edgePreimage_eq hinj ht hh]
  exact edgePreimage_eq (c := c.opposite) (c' := b.opposite) hinj hh ht
theorem expTwist_eq_inv_opposite (hEl : Matrices.ComplexMatrix2.NormExpLogBasics) (hL : 1 < L)
    (hj : -(n : ℤ) < PeriodicLattice.levelDepth k j) {U B : Edge L n k j → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) (c : Edge L n k j) :
    PeriodicLattice.expTwist B U c = (PeriodicLattice.expTwist B U c.opposite)⁻¹ := by
  by_cases h : c.IsPositivelyOriented
  · have h' : ¬ c.opposite.IsPositivelyOriented :=
      PeriodicLattice.Bond.opposite_not_isPositivelyOriented hL hj h
    have hd : IsUnit (Matrices.ComplexMatrix2.matExp (Complex.I • B c) * U c).det := by
      rw [Matrix.det_mul, show (U c).det = 1 from hU.1 c (mem_univ c), mul_one]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (hEl.2.1 _).2.2.2.1
    simp only [PeriodicLattice.expTwist, if_pos h, if_neg h', opposite_opposite]
    exact (Matrix.nonsing_inv_nonsing_inv _ hd).symm
  · have h' : c.opposite.IsPositivelyOriented :=
      PeriodicLattice.Bond.opposite_isPositivelyOriented h
    simp only [PeriodicLattice.expTwist, if_neg h, if_pos h']
theorem expTwist_pushField_of_positive (hEl : Matrices.ComplexMatrix2.NormExpLogBasics)
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    {U B : Edge L n k j → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist (isometryOnTangent f U B) (pushField (k := k) (j := j) f U) b =
      PeriodicLattice.expTwist B U (edgePreimage (k := k) (j := j) f b) := by
  have hA : isometryOnTangent f U B b =
      tangentEdgeValue U B (edgePreimage (k := k) (j := j) f b) := by
    simp only [isometryOnTangent, extendOddly, if_pos hb]
  have hl : PeriodicLattice.expTwist (isometryOnTangent f U B)
      (pushField (k := k) (j := j) f U) b =
      Matrices.ComplexMatrix2.matExp
          (Complex.I • tangentEdgeValue U B (edgePreimage (k := k) (j := j) f b)) *
        U (edgePreimage (k := k) (j := j) f b) := by
    rw [← hA]
    simp only [PeriodicLattice.expTwist, if_pos hb, pushField]
  rw [hl]
  generalize edgePreimage (k := k) (j := j) f b = c
  by_cases hc : c.IsPositivelyOriented
  · simp only [tangentEdgeValue, PeriodicLattice.expTwist, if_pos hc]
  · have hr : U c = (U c.opposite)⁻¹ := by
      have := hU.2 c.opposite (mem_univ _)
      rwa [opposite_opposite] at this
    simp only [tangentEdgeValue, PeriodicLattice.expTwist, if_neg hc]
    rw [hr]
    exact matExp_conj_inv hEl (hU.1 c.opposite (mem_univ _))
theorem fullTrace_plaquetteHolonomy_image
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hinj : ∀ a b : Vertex L n k j, f a = f b → a = b) (hb : MapsEdgesOnto k j f)
    (hc : FaceSums.FaceVerticesPeriodic L n k j) {U : Edge L n k j → Matrices.ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) {p p' : Face L n k j}
    (h : IsImageFace f p p') :
    Matrices.ComplexMatrix2.fullTrace
        (PeriodicLattice.plaquetteHolonomy (pushField (k := k) (j := j) f U) p') =
      Matrices.ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy U p) := by
  have hz : ∀ i, ∃ a, (vertexAt p' i : PeriodicLattice.FourTorus L n) = f (vertexAt p a) := by
    intro i
    have hm : (vertexAt p' i : PeriodicLattice.FourTorus L n) ∈ Subtype.val '' p'.vertices :=
      mem_image_of_mem _ (mem_vertices_iff.mpr ⟨i, rfl⟩)
    rw [h] at hm
    obtain ⟨_, ⟨y, hy, rfl⟩, e⟩ := hm
    obtain ⟨a, rfl⟩ := mem_vertices_iff.mp hy
    exact ⟨a, e.symm⟩
  choose σ hσ using hz
  have hσi : Function.Injective σ := by
    intro a b e
    apply vertexAt_injective hc p'
    apply Subtype.ext
    rw [hσ a, hσ b, e]
  have hstep : ∀ i, linkValue (pushField (k := k) (j := j) f U) (vertexAt p' i)
        (vertexAt p' (i + 1)) = linkValue U (vertexAt p (σ i)) (vertexAt p (σ (i + 1))) ∧
      Adjacent (vertexAt p (σ i)) (vertexAt p (σ (i + 1))) := by
    intro i
    obtain ⟨d, hd1, hd2⟩ := exists_bond_vertexAt p' i
    obtain ⟨c, ht, hh⟩ := hb.2 d
    have e1 : c.source = vertexAt p (σ i) := hinj _ _ (by rw [← ht, hd1, hσ i])
    have e2 : c.target = vertexAt p (σ (i + 1)) := hinj _ _ (by rw [← hh, hd2, hσ (i + 1)])
    refine ⟨?_, ?_⟩
    · rw [← hd1, ← hd2, ← e1, ← e2, linkValue_bond, linkValue_bond]
      exact congrArg U (edgePreimage_eq hinj ht hh)
    · rw [← e1, ← e2]
      exact c.isNeighbour
  have hne : ∀ i : Fin 4, i + 1 ≠ i := by decide
  have hn : ∀ i, σ (i + 1) = σ i + 1 ∨ σ i = σ (i + 1) + 1 := by
    intro i
    refine fin_four_adjacent_of_ne _ _ (fun e => ?_) (fun e => ?_)
    · exact absurd (hσi e) (hne i)
    · have := (hstep i).2
      rw [e] at this
      exact not_adjacent_vertexAt_add_two hc p _ this
  have hdet : ∀ a, (linkValue U (vertexAt p a) (vertexAt p (a + 1))).det = 1 := by
    intro a
    obtain ⟨d, hd1, hd2⟩ := exists_bond_vertexAt p a
    rw [← hd1, ← hd2, linkValue_bond]
    exact hU.1 d (mem_univ d)
  have hrev : ∀ a, linkValue U (vertexAt p (a + 1)) (vertexAt p a) =
      (linkValue U (vertexAt p a) (vertexAt p (a + 1)))⁻¹ := by
    intro a
    obtain ⟨d, hd1, hd2⟩ := exists_bond_vertexAt p a
    rw [← hd1, ← hd2, linkValue_bond]
    exact (linkValue_bond U d.opposite).trans (hU.2 d (mem_univ d))
  have s0 := (hstep 0).1
  have s1 := (hstep 1).1
  have s2 := (hstep 2).1
  have s3 := (hstep 3).1
  change linkValue _ _ (vertexAt p' 1) = linkValue U _ (vertexAt p (σ 1)) at s0
  change linkValue _ _ (vertexAt p' 2) = linkValue U _ (vertexAt p (σ 2)) at s1
  change linkValue _ _ (vertexAt p' 3) = linkValue U _ (vertexAt p (σ 3)) at s2
  change linkValue _ _ (vertexAt p' 0) = linkValue U _ (vertexAt p (σ 0)) at s3
  rw [plaquetteHolonomy_eq_linkValue, plaquetteHolonomy_eq_linkValue, s0, s1, s2, s3]
  exact fullTrace_cyclic_product_perm (fun a b => linkValue U (vertexAt p a) (vertexAt p b))
    hdet hrev σ hσi hn
end YangMills.Construction.Tower.PeriodicSymmetryAction
namespace YangMills.Construction.Tower
open PeriodicSymmetryAction in
theorem periodicSymmetriesActOnExpAndFaces_holds
    (hEl : Matrices.ComplexMatrix2.NormExpLogBasics)
    (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hE : FaceSums.FacesAndPairings) :
    PeriodicSymmetriesActOnExpAndFaces := by
  intro L n k j hL hn hjk f U hf hm hU
  have hL0 : 0 < L := by have := hL.2; omega
  have hL1 : 1 < L := by have := hL.2; omega
  have hdepth : -(n : ℤ) < PeriodicLattice.levelDepth k j := by
    simp only [PeriodicLattice.levelDepth]
    omega
  obtain ⟨hc, hsites, -, -⟩ := (hE L hL k j hjk).1 n hn
  have hfin : Finite (Vertex L n k j) :=
    Set.finite_univ_iff.mp (hsites univ).2.1
  have hinj := vertex_injective_of_mapsOnto hm
  obtain ⟨-, hrest⟩ := (hT L hL0 hL k).2.2.2.1 n hn j hjk f hf hm
  obtain ⟨-, hbonds, hplaq⟩ := hrest j le_rfl
  refine ⟨fun B _ => ?_, fun p => ⟨?_, fun p' h => ?_⟩⟩
  · funext b
    change _ = PeriodicLattice.expTwist B U _
    by_cases hb : b.IsPositivelyOriented
    · exact expTwist_pushField_of_positive hEl hU hb
    · have hb' : b.opposite.IsPositivelyOriented :=
        PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      have h1 := expTwist_pushField_of_positive (B := B) (f := f) hEl hU hb'
      rw [edgePreimage_opposite hinj hbonds] at h1
      rw [expTwist_eq_inv_opposite hEl hL1 hdepth hU (edgePreimage f b), ← h1]
      simp only [PeriodicLattice.expTwist, if_neg hb, if_pos hb']
  · obtain ⟨p', h⟩ := hplaq.1 p
    refine ⟨p', h, fun q hq => ?_⟩
    have e : q.vertices = p'.vertices :=
      Subtype.val_injective.image_injective (hq.trans h.symm)
    have := (hc q.origin p'.origin q.firstAxis q.secondAxis p'.firstAxis p'.secondAxis
      q.firstAxis_lt_secondAxis p'.firstAxis_lt_secondAxis).2 e
    simp only [Prod.mk.injEq] at this
    obtain ⟨e1, e2, e3⟩ := this
    exact PeriodicLattice.Plaquette.ext e1 e2 e3
  · have ht := fullTrace_plaquetteHolonomy_image hinj hbonds hc hU h
    simp only [complexFaceTerm, PeriodicLattice.plaquetteEnergy, ht]
end YangMills.Construction.Tower
end
