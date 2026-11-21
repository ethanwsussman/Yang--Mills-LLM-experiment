import YangMills.Construction.InfiniteLattice.PlaquetteFunctionAndActionOfTheIsometriesProof
import YangMills.Construction.Lattice.CovarianceOfComplexPlaquetteVariablesProof
import YangMills.Construction.Towers.IsometriesKeepThePairingsAndTheSecondDerivativeAtTheSideInfinityProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower.FullSpace.SymmetryFacts
theorem fullTrace_mul_rotate (a b c d : Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.fullTrace (b * c * d * a) =
      Matrices.ComplexMatrix2.fullTrace (a * b * c * d) := by
  have h : a * b * c * d = a * (b * c * d) := by simp only [mul_assoc]
  rw [h]
  exact Matrix.trace_mul_comm _ _
theorem fullTrace_inv_of_det_eq_one {g : Matrices.ComplexMatrix2} (hg : g.det = 1) :
    Matrices.ComplexMatrix2.fullTrace g⁻¹ = Matrices.ComplexMatrix2.fullTrace g := by apply _root_.YangMills.Construction.PeriodicLattice.PlaquetteCovariance.fullTrace_inv <;> assumption
theorem fullTrace_inv_reverse_prod {a b c d : Matrices.ComplexMatrix2} (ha : a.det = 1)
    (hb : b.det = 1) (hc : c.det = 1) (hd : d.det = 1) :
    Matrices.ComplexMatrix2.fullTrace (d⁻¹ * c⁻¹ * b⁻¹ * a⁻¹) =
      Matrices.ComplexMatrix2.fullTrace (a * b * c * d) := by
  have h : d⁻¹ * c⁻¹ * b⁻¹ * a⁻¹ = (a * b * c * d)⁻¹ := by
    simp only [Matrix.mul_inv_rev, mul_assoc]
  rw [h]
  exact fullTrace_inv_of_det_eq_one (by simp only [Matrix.det_mul, ha, hb, hc, hd, one_mul])
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
theorem fin_four_cyclic_orders : ∀ a b c d : Fin 4, (b = a + 1 ∨ a = b + 1) →
    (c = b + 1 ∨ b = c + 1) → (d = c + 1 ∨ c = d + 1) → (a = d + 1 ∨ d = a + 1) →
    a ≠ c → b ≠ d →
    (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3) ∨ (a = 1 ∧ b = 2 ∧ c = 3 ∧ d = 0) ∨
    (a = 2 ∧ b = 3 ∧ c = 0 ∧ d = 1) ∨ (a = 3 ∧ b = 0 ∧ c = 1 ∧ d = 2) ∨
    (a = 0 ∧ b = 3 ∧ c = 2 ∧ d = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 3 ∧ d = 2) ∨
    (a = 2 ∧ b = 1 ∧ c = 0 ∧ d = 3) ∨ (a = 3 ∧ b = 2 ∧ c = 1 ∧ d = 0) := by
  decide
theorem fin_four_adjacent_of_ne : ∀ a b : Fin 4, b ≠ a → b ≠ a + 2 →
    b = a + 1 ∨ a = b + 1 := by
  decide
theorem fullTrace_prod_along_cycle (v : Fin 4 → Fin 4 → Matrices.ComplexMatrix2)
    (hdet : ∀ i, (v i (i + 1)).det = 1) (hrev : ∀ i, v (i + 1) i = (v i (i + 1))⁻¹)
    (σ : Fin 4 → Fin 4) (hσ : Function.Injective σ)
    (hadj : ∀ i, σ (i + 1) = σ i + 1 ∨ σ i = σ (i + 1) + 1) :
    Matrices.ComplexMatrix2.fullTrace
        (v (σ 0) (σ 1) * v (σ 1) (σ 2) * v (σ 2) (σ 3) * v (σ 3) (σ 0)) =
      Matrices.ComplexMatrix2.fullTrace (v 0 1 * v 1 2 * v 2 3 * v 3 0) := by
  have d0 : (v 0 1).det = 1 := hdet 0
  have d1 : (v 1 2).det = 1 := hdet 1
  have d2 : (v 2 3).det = 1 := hdet 2
  have d3 : (v 3 0).det = 1 := hdet 3
  have r0 : v 1 0 = (v 0 1)⁻¹ := hrev 0
  have r1 : v 2 1 = (v 1 2)⁻¹ := hrev 1
  have r2 : v 3 2 = (v 2 3)⁻¹ := hrev 2
  have r3 : v 0 3 = (v 3 0)⁻¹ := hrev 3
  have q0 : σ 1 = σ 0 + 1 ∨ σ 0 = σ 1 + 1 := hadj 0
  have q1 : σ 2 = σ 1 + 1 ∨ σ 1 = σ 2 + 1 := hadj 1
  have q2 : σ 3 = σ 2 + 1 ∨ σ 2 = σ 3 + 1 := hadj 2
  have q3 : σ 0 = σ 3 + 1 ∨ σ 3 = σ 0 + 1 := hadj 3
  have e02 : σ 0 ≠ σ 2 := fun h => absurd (hσ h) (by decide)
  have e13 : σ 1 ≠ σ 3 := fun h => absurd (hσ h) (by decide)
  have t1 := fullTrace_mul_rotate (v 0 1) (v 1 2) (v 2 3) (v 3 0)
  have t2 := fullTrace_mul_rotate (v 1 2) (v 2 3) (v 3 0) (v 0 1)
  have t3 := fullTrace_mul_rotate (v 2 3) (v 3 0) (v 0 1) (v 1 2)
  rcases fin_four_cyclic_orders _ _ _ _ q0 q1 q2 q3 e02 e13 with
    ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ |
    ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ <;> simp only [a, b, c, d]
  · exact t1
  · exact t2.trans t1
  · exact t3.trans (t2.trans t1)
  · simp only [r0, r1, r2, r3]
    exact fullTrace_inv_reverse_prod d0 d1 d2 d3
  · simp only [r0, r1, r2, r3]
    exact (fullTrace_inv_reverse_prod d1 d2 d3 d0).trans t1
  · simp only [r0, r1, r2, r3]
    exact (fullTrace_inv_reverse_prod d2 d3 d0 d1).trans (t2.trans t1)
  · simp only [r0, r1, r2, r3]
    exact (fullTrace_inv_reverse_prod d3 d0 d1 d2).trans (t3.trans (t2.trans t1))
theorem matExp_neg_conj_mul_inv (hEl : Matrices.ComplexMatrix2.NormExpLogBasics)
    {g X : Matrices.ComplexMatrix2} (hg : g.det = 1) :
    Matrices.ComplexMatrix2.matExp
        (Complex.I • -Matrices.ComplexMatrix2.conjugateBy g⁻¹ X) * g⁻¹ =
      (Matrices.ComplexMatrix2.matExp (Complex.I • X) * g)⁻¹ := by
  have hdet : IsUnit g⁻¹.det := by
    rw [Matrix.det_nonsing_inv, hg]
    simp
  have hu : IsUnit g⁻¹ := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hconj := (hEl.2.1 (-(Complex.I • X))).2.2.2.2.2.2 g⁻¹ hu
  have e : Complex.I • -Matrices.ComplexMatrix2.conjugateBy g⁻¹ X =
      g⁻¹ * (-(Complex.I • X)) * g⁻¹⁻¹ := by
    simp only [Matrices.ComplexMatrix2.conjugateBy, smul_neg, mul_neg, neg_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  have hinv : (Matrices.ComplexMatrix2.matExp (Complex.I • X))⁻¹ =
      Matrices.ComplexMatrix2.matExp (-(Complex.I • X)) :=
    (hEl.2.1 (Complex.I • X)).2.2.2.2.1
  rw [e, ← hconj, Matrix.mul_inv_rev, hinv, mul_assoc, Matrix.nonsing_inv_mul _ hdet, mul_one]
variable {a : ℝ}
def FaceCornersDistinct (a : ℝ) : Prop :=
  ∀ (x x' : InfiniteLattice.LatticePoint a) (μ ν μ' ν' : Fin 4) (h : μ < ν) (h' : μ' < ν'),
    [x, x + InfiniteLattice.axisStep a μ,
      x + InfiniteLattice.axisStep a μ + InfiniteLattice.axisStep a ν,
      x + InfiniteLattice.axisStep a ν].Nodup ∧
    (FullSpace.faceCorners (⟨x, μ, ν, h⟩ : InfiniteLattice.ElementaryPlaquette a) =
        FullSpace.faceCorners (⟨x', μ', ν', h'⟩ : InfiniteLattice.ElementaryPlaquette a) →
      (x, μ, ν) = (x', μ', ν'))
def linkValue (W : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (x y : InfiniteLattice.LatticePoint a) : Matrices.ComplexMatrix2 :=
  W (Classical.epsilon fun l : InfiniteLattice.Link a => l.initial = x ∧ l.terminal = y)
theorem linkValue_link (W : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (l : InfiniteLattice.Link a) : linkValue W l.initial l.terminal = W l := by
  have h := Classical.epsilon_spec
    (p := fun m : InfiniteLattice.Link a => m.initial = l.initial ∧ m.terminal = l.terminal)
    ⟨l, rfl, rfl⟩
  exact congrArg W (InfiniteLattice.Link.ext h.1 h.2)
theorem opposite_opposite (l : InfiniteLattice.Link a) : l.opposite.opposite = l := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_opposite <;> assumption
theorem opposite_isPositivelyOriented_of_not {l : InfiniteLattice.Link a}
    (h : ¬ l.IsPositivelyOriented) : l.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem not_opposite_isPositivelyOriented (ha : a ≠ 0) {l : InfiniteLattice.Link a}
    (h : l.IsPositivelyOriented) : ¬ l.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.FullSpace.PolydiscSmoothing.not_opposite_isPositivelyOriented <;> assumption
def vertexAt (p : InfiniteLattice.ElementaryPlaquette a) :
    Fin 4 → InfiniteLattice.LatticePoint a :=
  ![p.corner, p.corner + InfiniteLattice.axisStep a p.lowAxis,
    p.corner + InfiniteLattice.axisStep a p.lowAxis + InfiniteLattice.axisStep a p.highAxis,
    p.corner + InfiniteLattice.axisStep a p.highAxis]
theorem mem_faceCorners {p : InfiniteLattice.ElementaryPlaquette a}
    {x : InfiniteLattice.LatticePoint a} :
    x ∈ FullSpace.faceCorners p ↔ ∃ i, vertexAt p i = x := by
  simp only [FullSpace.faceCorners, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
theorem vertexAt_two_eq (p : InfiniteLattice.ElementaryPlaquette a) :
    p.corner + InfiniteLattice.axisStep a p.highAxis + InfiniteLattice.axisStep a p.lowAxis =
      vertexAt p 2 :=
  add_right_comm _ _ _
theorem exists_link_vertexAt (p : InfiniteLattice.ElementaryPlaquette a) (i : Fin 4) :
    ∃ l : InfiniteLattice.Link a, l.initial = vertexAt p i ∧ l.terminal = vertexAt p (i + 1) := by
  fin_cases i
  · exact ⟨InfiniteLattice.Link.forwardFrom p.corner p.lowAxis, rfl, rfl⟩
  · exact ⟨InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.lowAxis)
      p.highAxis, rfl, rfl⟩
  · exact ⟨(InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.highAxis)
      p.lowAxis).opposite, vertexAt_two_eq p, rfl⟩
  · exact ⟨(InfiniteLattice.Link.forwardFrom p.corner p.highAxis).opposite, rfl, rfl⟩
theorem faceVariable_eq_prod (W : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    FullSpace.faceVariable W p =
      linkValue W (vertexAt p 0) (vertexAt p 1) * linkValue W (vertexAt p 1) (vertexAt p 2) *
        linkValue W (vertexAt p 2) (vertexAt p 3) *
          linkValue W (vertexAt p 3) (vertexAt p 0) := by
  have h : ∀ (l : InfiniteLattice.Link a) (x y : InfiniteLattice.LatticePoint a),
      l.initial = x → l.terminal = y → W l = linkValue W x y := by
    rintro l x y rfl rfl
    exact (linkValue_link W l).symm
  have e0 : W (InfiniteLattice.Link.forwardFrom p.corner p.lowAxis) =
      linkValue W (vertexAt p 0) (vertexAt p 1) := h _ _ _ rfl rfl
  have e1 : W (InfiniteLattice.Link.forwardFrom
      (p.corner + InfiniteLattice.axisStep a p.lowAxis) p.highAxis) =
      linkValue W (vertexAt p 1) (vertexAt p 2) := h _ _ _ rfl rfl
  have e2 : W (InfiniteLattice.Link.forwardFrom
      (p.corner + InfiniteLattice.axisStep a p.highAxis) p.lowAxis).opposite =
      linkValue W (vertexAt p 2) (vertexAt p 3) := h _ _ _ (vertexAt_two_eq p) rfl
  have e3 : W (InfiniteLattice.Link.forwardFrom p.corner p.highAxis).opposite =
      linkValue W (vertexAt p 3) (vertexAt p 0) := h _ _ _ rfl rfl
  simp only [FullSpace.faceVariable, FullSpace.linkHolonomy, FullSpace.faceBoundary,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [e0, e1, e2, e3]
  simp only [mul_assoc]
def Adjacent (x y : InfiniteLattice.LatticePoint a) : Prop :=
  ∃ μ : Fin 4, y - x = InfiniteLattice.axisStep a μ ∨ y - x = -InfiniteLattice.axisStep a μ
theorem Adjacent.symm {x y : InfiniteLattice.LatticePoint a} (h : Adjacent x y) :
    Adjacent y x := by apply _root_.YangMills.Construction.InfiniteLattice.FaceEnergyAndMotions.Neighbours.symm <;> assumption
theorem single_add_single_ne {T : ℝ} (hT : T ≠ 0) {μ ν : Fin 4} (h : μ ≠ ν) (c : Fin 4) :
    (Pi.single μ T + Pi.single ν T : Fin 4 → ℝ) ≠ Pi.single c T ∧
    (Pi.single μ T + Pi.single ν T : Fin 4 → ℝ) ≠ -Pi.single c T ∧
    (Pi.single ν T - Pi.single μ T : Fin 4 → ℝ) ≠ Pi.single c T ∧
    (Pi.single ν T - Pi.single μ T : Fin 4 → ℝ) ≠ -Pi.single c T := by
  by_cases hc : c = μ
  · subst hc
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    · have := congrFun e ν
      simp [h.symm, hT] at this
  · have hc' : μ ≠ c := fun e => hc e.symm
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    · have := congrFun e μ
      simp [h, hc', hT] at this
theorem vertexAt_injective (hc : FaceCornersDistinct a)
    (p : InfiniteLattice.ElementaryPlaquette a) : Function.Injective (vertexAt p) := by
  have h := (hc p.corner p.corner p.lowAxis p.highAxis p.lowAxis p.highAxis
    p.lowAxis_lt_highAxis p.lowAxis_lt_highAxis).1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := h
  intro s t hst
  by_contra hne
  fin_cases s <;> fin_cases t <;>
    first
    | exact hne rfl
    | exact h1 hst | exact h2 hst | exact h3 hst | exact h4 hst | exact h5 hst | exact h6 hst
    | exact h1 hst.symm | exact h2 hst.symm | exact h3 hst.symm | exact h4 hst.symm
    | exact h5 hst.symm | exact h6 hst.symm
theorem not_adjacent_opposite_vertices (ha : a ≠ 0) (p : InfiniteLattice.ElementaryPlaquette a)
    (i : Fin 4) : ¬ Adjacent (vertexAt p i) (vertexAt p (i + 2)) := by
  have hμν : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  have h02 : ¬ Adjacent (vertexAt p 0) (vertexAt p 2) := by
    rintro ⟨c, h | h⟩
    · have e : InfiniteLattice.axisStep a p.lowAxis + InfiniteLattice.axisStep a p.highAxis =
          InfiniteLattice.axisStep a c := by
        rw [← h]
        change _ = p.corner + _ + _ - p.corner
        abel
      exact (single_add_single_ne ha hμν c).1 (congrArg Subtype.val e)
    · have e : InfiniteLattice.axisStep a p.lowAxis + InfiniteLattice.axisStep a p.highAxis =
          -InfiniteLattice.axisStep a c := by
        rw [← h]
        change _ = p.corner + _ + _ - p.corner
        abel
      exact (single_add_single_ne ha hμν c).2.1 (congrArg Subtype.val e)
  have h13 : ¬ Adjacent (vertexAt p 1) (vertexAt p 3) := by
    rintro ⟨c, h | h⟩
    · have e : InfiniteLattice.axisStep a p.highAxis - InfiniteLattice.axisStep a p.lowAxis =
          InfiniteLattice.axisStep a c := by
        rw [← h]
        change _ = p.corner + _ - (p.corner + _)
        abel
      exact (single_add_single_ne ha hμν c).2.2.1 (congrArg Subtype.val e)
    · have e : InfiniteLattice.axisStep a p.highAxis - InfiniteLattice.axisStep a p.lowAxis =
          -InfiniteLattice.axisStep a c := by
        rw [← h]
        change _ = p.corner + _ - (p.corner + _)
        abel
      exact (single_add_single_ne ha hμν c).2.2.2 (congrArg Subtype.val e)
  fin_cases i
  · exact h02
  · exact h13
  · exact fun h => h02 h.symm
  · exact fun h => h13 h.symm
theorem edgePreimage_eq {f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace}
    (hinj : ∀ x y : InfiniteLattice.LatticePoint a, f x = f y → x = y)
    {l l' : InfiniteLattice.Link a}
    (hi : (l'.initial : InfiniteLattice.AmbientSpace) = f l.initial)
    (ht : (l'.terminal : InfiniteLattice.AmbientSpace) = f l.terminal) :
    FullSpace.edgePreimage f l' = l := by apply _root_.YangMills.Construction.Tower.FullSpace.LeftChartAlgebra.SymmetriesPreservePairingsAndHessian.edgePreimage_eq <;> assumption
theorem edgePreimage_opposite {f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace}
    (hinj : ∀ x y : InfiniteLattice.LatticePoint a, f x = f y → x = y)
    (hl : FullSpace.MapsLinksOnto a f) (l : InfiniteLattice.Link a) :
    FullSpace.edgePreimage f l.opposite = (FullSpace.edgePreimage f l).opposite := by apply _root_.YangMills.Construction.Tower.FullSpace.LeftChartAlgebra.SymmetriesPreservePairingsAndHessian.edgePreimage_opposite <;> assumption
theorem expTwist_eq_inv_opposite (hEl : Matrices.ComplexMatrix2.NormExpLogBasics) (ha : a ≠ 0)
    {U B : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hU : FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup U) (l : InfiniteLattice.Link a) :
    FullSpace.expTwist B U l = (FullSpace.expTwist B U l.opposite)⁻¹ := by
  by_cases h : l.IsPositivelyOriented
  · have h' : ¬ l.opposite.IsPositivelyOriented := not_opposite_isPositivelyOriented ha h
    have hd : IsUnit (Matrices.ComplexMatrix2.matExp (Complex.I • B l) * U l).det := by
      rw [Matrix.det_mul, show (U l).det = 1 from hU.1 l, mul_one]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (hEl.2.1 _).2.2.2.1
    simp only [FullSpace.expTwist, if_pos h, if_neg h', opposite_opposite]
    exact (Matrix.nonsing_inv_nonsing_inv _ hd).symm
  · have h' : l.opposite.IsPositivelyOriented := opposite_isPositivelyOriented_of_not h
    simp only [FullSpace.expTwist, if_neg h, if_pos h']
theorem expTwist_push_of_positive (hEl : Matrices.ComplexMatrix2.NormExpLogBasics)
    {f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace}
    {U B : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hU : FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup U) {l : InfiniteLattice.Link a}
    (hl : l.IsPositivelyOriented) :
    FullSpace.expTwist (FullSpace.isometryOnTangent f U B) (FullSpace.pushField f U) l =
      FullSpace.expTwist B U (FullSpace.edgePreimage f l) := by
  have hA : FullSpace.isometryOnTangent f U B l =
      FullSpace.tangentEdgeValue U B (FullSpace.edgePreimage f l) := by
    simp only [FullSpace.isometryOnTangent, FullSpace.extendOddly, if_pos hl]
  have hlhs : FullSpace.expTwist (FullSpace.isometryOnTangent f U B) (FullSpace.pushField f U) l =
      Matrices.ComplexMatrix2.matExp
          (Complex.I • FullSpace.tangentEdgeValue U B (FullSpace.edgePreimage f l)) *
        U (FullSpace.edgePreimage f l) := by
    rw [← hA]
    simp only [FullSpace.expTwist, if_pos hl, FullSpace.pushField]
  rw [hlhs]
  generalize FullSpace.edgePreimage f l = m
  by_cases hm : m.IsPositivelyOriented
  · simp only [FullSpace.tangentEdgeValue, FullSpace.expTwist, if_pos hm]
  · have hr : U m = (U m.opposite)⁻¹ := by
      have := hU.2 m.opposite
      rwa [opposite_opposite] at this
    simp only [FullSpace.tangentEdgeValue, FullSpace.expTwist, if_neg hm]
    rw [hr]
    exact matExp_neg_conj_mul_inv hEl (hU.1 m.opposite)
theorem fullTrace_faceVariable_image
    {f : InfiniteLattice.AmbientSpace → InfiniteLattice.AmbientSpace} (ha : a ≠ 0)
    (hinj : ∀ x y : InfiniteLattice.LatticePoint a, f x = f y → x = y)
    (hl : FullSpace.MapsLinksOnto a f) (hc : FaceCornersDistinct a)
    {U : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hU : FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup U)
    {p p' : InfiniteLattice.ElementaryPlaquette a} (h : FullSpace.IsImageFace f p p') :
    Matrices.ComplexMatrix2.fullTrace (FullSpace.faceVariable (FullSpace.pushField f U) p') =
      Matrices.ComplexMatrix2.fullTrace (FullSpace.faceVariable U p) := by
  have hz : ∀ i, ∃ s, (vertexAt p' i : InfiniteLattice.AmbientSpace) = f (vertexAt p s) := by
    intro i
    have hm : (vertexAt p' i : InfiniteLattice.AmbientSpace) ∈
        Subtype.val '' FullSpace.faceCorners p' :=
      mem_image_of_mem _ (mem_faceCorners.mpr ⟨i, rfl⟩)
    rw [h] at hm
    obtain ⟨_, ⟨y, hy, rfl⟩, e⟩ := hm
    obtain ⟨s, rfl⟩ := mem_faceCorners.mp hy
    exact ⟨s, e.symm⟩
  choose σ hσ using hz
  have hσi : Function.Injective σ := by
    intro s t e
    apply vertexAt_injective hc p'
    apply Subtype.ext
    rw [hσ s, hσ t, e]
  have hstep : ∀ i, linkValue (FullSpace.pushField f U) (vertexAt p' i) (vertexAt p' (i + 1)) =
        linkValue U (vertexAt p (σ i)) (vertexAt p (σ (i + 1))) ∧
      Adjacent (vertexAt p (σ i)) (vertexAt p (σ (i + 1))) := by
    intro i
    obtain ⟨d, hd1, hd2⟩ := exists_link_vertexAt p' i
    obtain ⟨m, hi, ht⟩ := hl.2 d
    have e1 : m.initial = vertexAt p (σ i) := hinj _ _ (by rw [← hi, hd1, hσ i])
    have e2 : m.terminal = vertexAt p (σ (i + 1)) := hinj _ _ (by rw [← ht, hd2, hσ (i + 1)])
    refine ⟨?_, ?_⟩
    · rw [← hd1, ← hd2, ← e1, ← e2, linkValue_link, linkValue_link]
      exact congrArg U (edgePreimage_eq hinj hi ht)
    · rw [← e1, ← e2]
      exact m.isAdjacent
  have hne : ∀ i : Fin 4, i + 1 ≠ i := by decide
  have hadj : ∀ i, σ (i + 1) = σ i + 1 ∨ σ i = σ (i + 1) + 1 := by
    intro i
    refine fin_four_adjacent_of_ne _ _ (fun e => ?_) (fun e => ?_)
    · exact absurd (hσi e) (hne i)
    · have := (hstep i).2
      rw [e] at this
      exact not_adjacent_opposite_vertices ha p _ this
  have hdet : ∀ s, (linkValue U (vertexAt p s) (vertexAt p (s + 1))).det = 1 := by
    intro s
    obtain ⟨d, hd1, hd2⟩ := exists_link_vertexAt p s
    rw [← hd1, ← hd2, linkValue_link]
    exact hU.1 d
  have hrev : ∀ s, linkValue U (vertexAt p (s + 1)) (vertexAt p s) =
      (linkValue U (vertexAt p s) (vertexAt p (s + 1)))⁻¹ := by
    intro s
    obtain ⟨d, hd1, hd2⟩ := exists_link_vertexAt p s
    rw [← hd1, ← hd2, linkValue_link]
    exact (linkValue_link U d.opposite).trans (hU.2 d)
  have s0 := (hstep 0).1
  have s1 := (hstep 1).1
  have s2 := (hstep 2).1
  have s3 := (hstep 3).1
  change linkValue _ _ (vertexAt p' 1) = linkValue U _ (vertexAt p (σ 1)) at s0
  change linkValue _ _ (vertexAt p' 2) = linkValue U _ (vertexAt p (σ 2)) at s1
  change linkValue _ _ (vertexAt p' 3) = linkValue U _ (vertexAt p (σ 3)) at s2
  change linkValue _ _ (vertexAt p' 0) = linkValue U _ (vertexAt p (σ 0)) at s3
  rw [faceVariable_eq_prod, faceVariable_eq_prod, s0, s1, s2, s3]
  exact fullTrace_prod_along_cycle (fun s t => linkValue U (vertexAt p s) (vertexAt p t))
    hdet hrev σ hσi hadj
end Tower.FullSpace.SymmetryFacts
open Tower.FullSpace.SymmetryFacts in
theorem Tower.FullSpace.symmetriesActOnExpAndFaces_holds
    (hEl : Matrices.ComplexMatrix2.NormExpLogBasics)
    (hT : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hE : Tower.FaceSums.FacesAndPairings) :
    Tower.FullSpace.SymmetriesActOnExpAndFaces := by
  intro L k j hL hjk f U hf hm hU
  have hL0 : 0 < L := by have := hL.2; omega
  have ha : Tower.meshAt L k j ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.mpr hL0.ne')
  have hc : FaceCornersDistinct (Tower.meshAt L k j) := (hE L hL k j hjk).2.1
  obtain ⟨⟨w, -, v, -, hw⟩, hrest, -⟩ := (hT L hL0 hL k).2.2.2.2.1 j hjk f hf hm
  obtain ⟨-, hlinks, hfaces⟩ := hrest j le_rfl
  have hinj : ∀ x y : InfiniteLattice.LatticePoint (Tower.meshAt L k j),
      f x = f y → x = y := by
    intro x y e
    rw [hw, hw] at e
    exact Subtype.ext (w.injective (add_right_cancel e))
  refine ⟨fun B _ => ?_, fun p => ⟨?_, fun p' h => ?_⟩⟩
  · funext l
    change _ = Tower.FullSpace.expTwist B U _
    by_cases hl : l.IsPositivelyOriented
    · exact expTwist_push_of_positive hEl hU hl
    · have hl' : l.opposite.IsPositivelyOriented := opposite_isPositivelyOriented_of_not hl
      have h1 := expTwist_push_of_positive (B := B) (f := f) hEl hU hl'
      rw [edgePreimage_opposite hinj hlinks] at h1
      rw [expTwist_eq_inv_opposite hEl ha hU (Tower.FullSpace.edgePreimage f l), ← h1]
      simp only [Tower.FullSpace.expTwist, if_neg hl, if_pos hl']
  · obtain ⟨p', h⟩ := hfaces.1 p
    refine ⟨p', h, fun q hq => ?_⟩
    have e : Tower.FullSpace.faceCorners q = Tower.FullSpace.faceCorners p' :=
      Subtype.val_injective.image_injective (hq.trans h.symm)
    have := (hc q.corner p'.corner q.lowAxis q.highAxis p'.lowAxis p'.highAxis
      q.lowAxis_lt_highAxis p'.lowAxis_lt_highAxis).2 e
    simp only [Prod.mk.injEq] at this
    obtain ⟨e1, e2, e3⟩ := this
    exact InfiniteLattice.ElementaryPlaquette.ext e1 e2 e3
  · have ht := fullTrace_faceVariable_image ha hinj hlinks hc hU h
    simp only [Tower.FullSpace.complexFaceTerm, ht]
end YangMills.Construction
end
