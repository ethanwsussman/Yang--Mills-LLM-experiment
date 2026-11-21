import YangMills.Construction.Towers.GaugeConditionsOfTheAlgebraOfTheLeftChartOnASide
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Towers.TranslationsAndIsometriesOfATowerProof
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Tower.LeftChartAlgebra.GaugeRequirements
theorem isUnit_det_of_det_eq_one {V : ComplexMatrix2} (h : V.det = 1) : IsUnit V.det := by apply _root_.YangMills.SharedProofs.p11557 <;> assumption
theorem inv_mul_self_of_det_eq_one {V : ComplexMatrix2} (h : V.det = 1) : V⁻¹ * V = 1 :=
  Matrix.nonsing_inv_mul V (isUnit_det_of_det_eq_one h)
theorem conjugateBy_sub (V X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (X - Y) =
      ComplexMatrix2.conjugateBy V X - ComplexMatrix2.conjugateBy V Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_sub, sub_mul]
theorem conjugateBy_add (V X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (X + Y) =
      ComplexMatrix2.conjugateBy V X + ComplexMatrix2.conjugateBy V Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (V X : ComplexMatrix2) (c : ℂ) :
    ComplexMatrix2.conjugateBy V (c • X) = c • ComplexMatrix2.conjugateBy V X := by
  simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
theorem conjugateBy_gauged (t g h x : ComplexMatrix2) (hh : h.det = 1) :
    ComplexMatrix2.conjugateBy (t * g * h⁻¹) (ComplexMatrix2.conjugateBy h x) =
      ComplexMatrix2.conjugateBy t (ComplexMatrix2.conjugateBy g x) := by
  have hi := inv_mul_self_of_det_eq_one hh
  simp only [ComplexMatrix2.conjugateBy, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv h (isUnit_det_of_det_eq_one hh)]
  calc t * g * h⁻¹ * (h * x * h⁻¹) * (h * (g⁻¹ * t⁻¹))
      = t * g * (h⁻¹ * h) * x * (h⁻¹ * h) * (g⁻¹ * t⁻¹) := by simp only [mul_assoc]
    _ = t * (g * x * g⁻¹) * t⁻¹ := by
        rw [hi, mul_one, mul_one]
        simp only [mul_assoc]
theorem conjugateBy_inv_conjugateBy (V X : ComplexMatrix2) (hV : V.det = 1) :
    ComplexMatrix2.conjugateBy V⁻¹ (ComplexMatrix2.conjugateBy V X) = X := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.conjugateBy_inv_conjugateBy <;> assumption
theorem conjugateBy_conjugateBy_inv (V X : ComplexMatrix2) (hV : V.det = 1) :
    ComplexMatrix2.conjugateBy V (ComplexMatrix2.conjugateBy V⁻¹ X) = X := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.conjugateBy_conjugateBy_inv <;> assumption
theorem trace_conj_eq (V X : ComplexMatrix2) (hV : V.det = 1) :
    Matrix.trace (V * X * V⁻¹) = Matrix.trace X := by
  rw [Matrix.trace_mul_comm, ← mul_assoc, inv_mul_self_of_det_eq_one hV, one_mul]
theorem det_eq_one_of_mem {V : ComplexMatrix2} (hV : V ∈ ComplexMatrix2.specialUnitary) :
    V.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hV).2
theorem inv_eq_conjTranspose_of_mem {V : ComplexMatrix2}
    (hV : V ∈ ComplexMatrix2.specialUnitary) : V⁻¹ = V.conjTranspose := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_eq_conjTranspose_of_mem_specialUnitary <;> assumption
theorem inv_mem_specialUnitary {V : ComplexMatrix2} (hV : V ∈ ComplexMatrix2.specialUnitary) :
    V⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
theorem conjugateBy_preserves_hermitianTraceless {V X : ComplexMatrix2}
    (hV : V ∈ ComplexMatrix2.specialUnitary) (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.conjugateBy_mem_hermitianTraceless <;> assumption
theorem conjugateBy_preserves_traceless {V X : ComplexMatrix2} (hV : V.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
theorem halfTraceProduct_conjugateBy {V : ComplexMatrix2}
    (hV : V ∈ ComplexMatrix2.specialUnitary) (X Y : ComplexMatrix2) :
    halfTraceProduct (ComplexMatrix2.conjugateBy V X) (ComplexMatrix2.conjugateBy V Y) =
      halfTraceProduct X Y := by
  have hd := det_eq_one_of_mem hV
  have ha : ComplexMatrix2.adjointMatrix (ComplexMatrix2.conjugateBy V X) =
      ComplexMatrix2.conjugateBy V (ComplexMatrix2.adjointMatrix X) := by
    simp only [ComplexMatrix2.conjugateBy, ComplexMatrix2.adjointMatrix,
      inv_eq_conjTranspose_of_mem hV, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, mul_assoc]
  have hp : ComplexMatrix2.conjugateBy V (ComplexMatrix2.adjointMatrix X) *
      ComplexMatrix2.conjugateBy V Y = V * (ComplexMatrix2.adjointMatrix X * Y) * V⁻¹ := by
    calc ComplexMatrix2.conjugateBy V (ComplexMatrix2.adjointMatrix X) *
          ComplexMatrix2.conjugateBy V Y
        = V * ComplexMatrix2.adjointMatrix X * (V⁻¹ * V) * Y * V⁻¹ := by
          simp only [ComplexMatrix2.conjugateBy, mul_assoc]
      _ = V * (ComplexMatrix2.adjointMatrix X * Y) * V⁻¹ := by
          rw [inv_mul_self_of_det_eq_one hd, mul_one]
          simp only [mul_assoc]
  unfold halfTraceProduct
  rw [ha, hp, ComplexMatrix2.halfTrace, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    ComplexMatrix2.fullTrace, trace_conj_eq _ _ hd]
theorem halfTraceProduct_eq_entries (X Y : ComplexMatrix2) :
    halfTraceProduct X Y = (1 / 2 : ℂ) * (star (X 0 0) * Y 0 0 + star (X 1 0) * Y 1 0 +
      (star (X 0 1) * Y 0 1 + star (X 1 1) * Y 1 1)) := by
  simp only [halfTraceProduct, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    ComplexMatrix2.adjointMatrix, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply]
theorem re_halfTraceProduct_self (X : ComplexMatrix2) :
    (halfTraceProduct X X).re =
      (‖X 0 0‖ ^ 2 + ‖X 1 0‖ ^ 2 + (‖X 0 1‖ ^ 2 + ‖X 1 1‖ ^ 2)) / 2 := by
  have h : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [halfTraceProduct_eq_entries, h, h, h, h]
  simp only [← Complex.ofReal_add]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring
theorem norm_star_mul_le_half_sq (x y : ℂ) : ‖star x * y‖ ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  rw [norm_mul, norm_star]
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
theorem norm_halfTraceProduct_le (X Y : ComplexMatrix2) :
    ‖halfTraceProduct X Y‖ ≤ (halfTraceProduct X X).re + (halfTraceProduct Y Y).re := by
  rw [re_halfTraceProduct_self, re_halfTraceProduct_self, halfTraceProduct_eq_entries, norm_mul]
  have h1 := norm_star_mul_le_half_sq (X 0 0) (Y 0 0)
  have h2 := norm_star_mul_le_half_sq (X 1 0) (Y 1 0)
  have h3 := norm_star_mul_le_half_sq (X 0 1) (Y 0 1)
  have h4 := norm_star_mul_le_half_sq (X 1 1) (Y 1 1)
  have hs : ‖star (X 0 0) * Y 0 0 + star (X 1 0) * Y 1 0 +
      (star (X 0 1) * Y 0 1 + star (X 1 1) * Y 1 1)‖ ≤
      ‖star (X 0 0) * Y 0 0‖ + ‖star (X 1 0) * Y 1 0‖ +
        (‖star (X 0 1) * Y 0 1‖ + ‖star (X 1 1) * Y 1 1‖) :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
  have hh : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hh]
  nlinarith
theorem hermitianSeriesAbsConv_all (ι : Type*) : HermitianSeriesAbsConv ι := by
  intro f f' hf hf'
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => norm_halfTraceProduct_le (f i) (f' i)) (hf.2.add hf'.2)
theorem hermitianInner_conjugateBy {ι : Type*} {f f' g g' : ι → ComplexMatrix2}
    {v : ι → ComplexMatrix2} (hv : ∀ i, v i ∈ ComplexMatrix2.specialUnitary)
    (hg : ∀ i, g i = ComplexMatrix2.conjugateBy (v i) (f i))
    (hg' : ∀ i, g' i = ComplexMatrix2.conjugateBy (v i) (f' i)) :
    hermitianInner g g' = hermitianInner f f' := by
  unfold hermitianInner
  refine tsum_congr fun i => ?_
  rw [hg, hg', halfTraceProduct_conjugateBy (hv i)]
theorem isL2Traceless_conjugateBy {ι : Type*} {f g : ι → ComplexMatrix2}
    {v : ι → ComplexMatrix2} (hv : ∀ i, v i ∈ ComplexMatrix2.specialUnitary)
    (hg : ∀ i, g i = ComplexMatrix2.conjugateBy (v i) (f i)) (hf : IsL2Traceless f) :
    IsL2Traceless g := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [hg]
    exact conjugateBy_preserves_traceless (det_eq_one_of_mem (hv i)) (hf.1 i)
  · have : (fun i => (halfTraceProduct (g i) (g i)).re) =
        fun i => (halfTraceProduct (f i) (f i)).re := by
      funext i
      rw [hg, halfTraceProduct_conjugateBy (hv i)]
    rw [this]
    exact hf.2
section Faces
variable {L m : ℕ} {j : ℤ}
theorem gauged_loop_product (a b c d g₁ g₂ g₃ g₄ : ComplexMatrix2) (hb : b.det = 1)
    (hc : c.det = 1) (hd : d.det = 1) :
    a * g₁ * b⁻¹ * (b * g₂ * c⁻¹ * (c * g₃ * d⁻¹ * (d * g₄ * a⁻¹))) =
      a * (g₁ * (g₂ * (g₃ * g₄))) * a⁻¹ := by
  calc a * g₁ * b⁻¹ * (b * g₂ * c⁻¹ * (c * g₃ * d⁻¹ * (d * g₄ * a⁻¹)))
      = a * g₁ * (b⁻¹ * b) * g₂ * (c⁻¹ * c) * g₃ * (d⁻¹ * d) * g₄ * a⁻¹ := by
        simp only [mul_assoc]
    _ = a * (g₁ * (g₂ * (g₃ * g₄))) * a⁻¹ := by
        rw [inv_mul_self_of_det_eq_one hb, inv_mul_self_of_det_eq_one hc,
          inv_mul_self_of_det_eq_one hd]
        simp only [mul_one, mul_assoc]
theorem plaquetteHolonomy_gaugeTransform (U : PeriodicLattice.Bond L m j → ComplexMatrix2)
    (u : PeriodicLattice.Site L m j → ComplexMatrix2) (hu : ∀ x, (u x).det = 1)
    (p : PeriodicLattice.Plaquette L m j) :
    PeriodicLattice.plaquetteHolonomy (PeriodicLattice.gaugeTransform u U) p =
      u p.origin * PeriodicLattice.plaquetteHolonomy U p * (u p.origin)⁻¹ := by
  have hc : p.origin + PeriodicLattice.unitStep L m j p.secondAxis +
      PeriodicLattice.unitStep L m j p.firstAxis =
      p.origin + PeriodicLattice.unitStep L m j p.firstAxis +
        PeriodicLattice.unitStep L m j p.secondAxis :=
    add_right_comm _ _ _
  simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, PeriodicLattice.gaugeTransform, PeriodicLattice.Bond.forwardFrom,
    PeriodicLattice.Bond.opposite, hc]
  exact gauged_loop_product _ _ _ _ _ _ _ _ (hu _) (hu _) (hu _)
end Faces
section FiniteSide
variable {L m k j : ℕ}
theorem positive_or_opposite_positive (b : Edge L m k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem not_opposite_positive (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k) (b : Edge L m k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
theorem extendOddly_of_positive (f : Edge L m k j → ComplexMatrix2) {b : Edge L m k j}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_pos <;> assumption
theorem extendOddly_of_not_positive (f : Edge L m k j → ComplexMatrix2) {b : Edge L m k j}
    (hb : ¬ b.IsPositivelyOriented) : extendOddly f b = -f b.opposite := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_not_pos <;> assumption
theorem extendOddly_congr {f g : Edge L m k j → ComplexMatrix2}
    (h : ∀ b : Edge L m k j, b.IsPositivelyOriented → f b = g b) :
    extendOddly f = extendOddly g := by apply _root_.YangMills.Construction.Tower.CovDiffStep.extendOddly_congr <;> assumption
theorem adjointForm_of_positive (u : Vertex L m k j → ComplexMatrix2)
    (B : Edge L m k j → ComplexMatrix2) {b : Edge L m k j} (hb : b.IsPositivelyOriented) :
    adjointForm u B b = ComplexMatrix2.conjugateBy (u b.source) (B b) :=
  extendOddly_of_positive _ hb
theorem adjointForm_of_not_positive (u : Vertex L m k j → ComplexMatrix2)
    (B : Edge L m k j → ComplexMatrix2) {b : Edge L m k j} (hb : ¬ b.IsPositivelyOriented) :
    adjointForm u B b = -ComplexMatrix2.conjugateBy (u b.opposite.source) (B b.opposite) :=
  extendOddly_of_not_positive _ hb
theorem covDiff_of_positive (U : Edge L m k j → ComplexMatrix2)
    (l : Vertex L m k j → ComplexMatrix2) {b : Edge L m k j} (hb : b.IsPositivelyOriented) :
    covDiff U l b = ComplexMatrix2.conjugateBy (U b) (l b.target) - l b.source := by apply _root_.YangMills.Construction.Tower.Translations.covDiff_of_pos <;> assumption
theorem covDiff_gaugeTransform (U : Edge L m k j → ComplexMatrix2)
    (u l : Vertex L m k j → ComplexMatrix2) (hu : ∀ x, (u x).det = 1) :
    covDiff (PeriodicLattice.gaugeTransform u U) (adjointVertexFn u l) =
      adjointForm u (covDiff U l) := by
  refine extendOddly_congr fun b hb => ?_
  rw [covDiff_of_positive U l hb, conjugateBy_sub]
  change ComplexMatrix2.conjugateBy (u b.source * U b * (u b.target)⁻¹)
      (ComplexMatrix2.conjugateBy (u b.target) (l b.target)) -
    ComplexMatrix2.conjugateBy (u b.source) (l b.source) = _
  rw [conjugateBy_gauged _ _ _ _ (hu _)]
theorem gaugeCovariance_holds (L m k j : ℕ) : GaugeCovariance L m k j := by
  intro U u _ hu
  have hd : ∀ x, (u x).det = 1 := hu
  refine ⟨fun l _ => covDiff_gaugeTransform U u l hd, fun p => ?_⟩
  have hp := plaquetteHolonomy_gaugeTransform U u hd p
  refine ⟨hp, ?_⟩
  unfold complexFaceTerm PeriodicLattice.plaquetteEnergy
  rw [hp, ComplexMatrix2.fullTrace, ComplexMatrix2.fullTrace, trace_conj_eq _ _ (hd _)]
theorem adjointForm_add (u : Vertex L m k j → ComplexMatrix2)
    (B B' : Edge L m k j → ComplexMatrix2) :
    adjointForm u (B + B') = adjointForm u B + adjointForm u B' := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.adjointForm_add <;> assumption
theorem adjointForm_smul (u : Vertex L m k j → ComplexMatrix2) (c : ℂ)
    (B : Edge L m k j → ComplexMatrix2) :
    adjointForm u (c • B) = c • adjointForm u B := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [Pi.smul_apply, adjointForm_of_positive _ _ hb, conjugateBy_smul]
  · simp only [Pi.smul_apply, adjointForm_of_not_positive _ _ hb, conjugateBy_smul, smul_neg]
theorem adjointForm_opposite
    (hnb : ∀ b : Edge L m k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (u : Vertex L m k j → ComplexMatrix2) (B : Edge L m k j → ComplexMatrix2)
    (b : Edge L m k j) : adjointForm u B b.opposite = -adjointForm u B b := by
  by_cases hb : b.IsPositivelyOriented
  · rw [adjointForm_of_not_positive _ _ (hnb b hb), adjointForm_of_positive _ _ hb]
    rfl
  · have hr := (positive_or_opposite_positive b).resolve_left hb
    rw [adjointForm_of_positive _ _ hr, adjointForm_of_not_positive _ _ hb, neg_neg]
theorem adjointForm_mem_edgeFormSpace
    (hnb : ∀ b : Edge L m k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (u : Vertex L m k j → ComplexMatrix2) (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary)
    {B : Edge L m k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L m k j) :
    adjointForm u B ∈ edgeFormSpace L m k j := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.adjointForm_mem <;> assumption
theorem adjointForm_mem_l2Forms
    (hnb : ∀ b : Edge L m k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (u : Vertex L m k j → ComplexMatrix2) (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary)
    {B : Edge L m k j → ComplexMatrix2} (hB : B ∈ l2Forms L m k j) :
    adjointForm u B ∈ l2Forms L m k j := by
  obtain ⟨⟨hv, -⟩, hs⟩ := hB
  refine ⟨⟨fun b hb => ?_, adjointForm_opposite hnb u B⟩, ?_⟩
  · rw [adjointForm_of_positive _ _ hb]
    exact conjugateBy_preserves_traceless (det_eq_one_of_mem (hu _)) (hv b hb)
  · exact isL2Traceless_conjugateBy (v := fun b : PositiveEdge L m k j => u b.1.source)
      (fun _ => hu _) (fun b => adjointForm_of_positive u B b.2) hs
theorem adjointForm_adjointForm (u w : Vertex L m k j → ComplexMatrix2)
    (h : ∀ x X, ComplexMatrix2.conjugateBy (w x) (ComplexMatrix2.conjugateBy (u x) X) = X)
    {B : Edge L m k j → ComplexMatrix2} (hB : ∀ b : Edge L m k j, B b.opposite = -B b) :
    adjointForm w (adjointForm u B) = B := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [adjointForm_of_positive _ _ hb, adjointForm_of_positive _ _ hb, h]
  · have hp := (positive_or_opposite_positive b).resolve_left hb
    rw [adjointForm_of_not_positive _ _ hb, adjointForm_of_positive _ _ hp, h, hB, neg_neg]
theorem adjointVertexFn_add (u l l' : Vertex L m k j → ComplexMatrix2) :
    adjointVertexFn u (l + l') = adjointVertexFn u l + adjointVertexFn u l' :=
  funext fun _ => conjugateBy_add _ _ _
theorem adjointVertexFn_smul (u : Vertex L m k j → ComplexMatrix2) (c : ℂ)
    (l : Vertex L m k j → ComplexMatrix2) :
    adjointVertexFn u (c • l) = c • adjointVertexFn u l :=
  funext fun _ => conjugateBy_smul _ _ _
theorem adjointVertexFn_mem (u : Vertex L m k j → ComplexMatrix2)
    (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary) {l : Vertex L m k j → ComplexMatrix2}
    (hl : l ∈ vertexFunctionSpace L m k j) : adjointVertexFn u l ∈ vertexFunctionSpace L m k j :=
  fun x _ => conjugateBy_preserves_hermitianTraceless (hu x) (hl x (mem_univ x))
theorem bijOn_of_twoSided_inverse {α : Type*} {S : Set α} {T T' : α → α} (hT : MapsTo T S S)
    (hT' : MapsTo T' S S) (hl : ∀ x ∈ S, T' (T x) = x) (hr : ∀ x ∈ S, T (T' x) = x) :
    BijOn T S S :=
  (InvOn.bijOn ⟨hl, hr⟩ hT hT')
theorem adjointForm_isUnitaryOnSet
    (hnb : ∀ b : Edge L m k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (u : Vertex L m k j → ComplexMatrix2) (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary) :
    IsUnitaryOnSet (l2Forms L m k j) restrictToPositiveEdges (adjointForm u) := by
  have hd : ∀ x, (u x).det = 1 := fun x => det_eq_one_of_mem (hu x)
  have hi : ∀ x, (fun y => (u y)⁻¹) x ∈ ComplexMatrix2.specialUnitary :=
    fun x => inv_mem_specialUnitary (hu x)
  refine ⟨bijOn_of_twoSided_inverse (T' := adjointForm fun y => (u y)⁻¹)
      (fun B hB => adjointForm_mem_l2Forms hnb u hu hB)
      (fun B hB => adjointForm_mem_l2Forms hnb _ hi hB)
      (fun B hB => adjointForm_adjointForm _ _
        (fun x X => conjugateBy_inv_conjugateBy _ X (hd x)) hB.1.2)
      (fun B hB => adjointForm_adjointForm _ _
        (fun x X => conjugateBy_conjugateBy_inv _ X (hd x)) hB.1.2),
    fun B _ B' _ => adjointForm_add u B B', fun c B _ => adjointForm_smul u c B,
    fun B _ B' _ => ?_⟩
  exact hermitianInner_conjugateBy (v := fun b : PositiveEdge L m k j => u b.1.source)
    (fun _ => hu _) (fun b => adjointForm_of_positive u B b.2)
    (fun b => adjointForm_of_positive u B' b.2)
theorem adjointVertexFn_isUnitaryOnSet (u : Vertex L m k j → ComplexMatrix2)
    (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary) :
    IsUnitaryOnSet {l : Vertex L m k j → ComplexMatrix2 | IsL2Traceless l} id
      (adjointVertexFn u) := by
  have hd : ∀ x, (u x).det = 1 := fun x => det_eq_one_of_mem (hu x)
  have hi : ∀ x, (fun y => (u y)⁻¹) x ∈ ComplexMatrix2.specialUnitary :=
    fun x => inv_mem_specialUnitary (hu x)
  refine ⟨bijOn_of_twoSided_inverse (T' := adjointVertexFn fun y => (u y)⁻¹)
      (fun l hl => isL2Traceless_conjugateBy hu (fun _ => rfl) hl)
      (fun l hl => isL2Traceless_conjugateBy hi (fun _ => rfl) hl)
      (fun l _ => funext fun x => conjugateBy_inv_conjugateBy _ _ (hd x))
      (fun l _ => funext fun x => conjugateBy_conjugateBy_inv _ _ (hd x)),
    fun l _ l' _ => adjointVertexFn_add u l l', fun c l _ => adjointVertexFn_smul u c l,
    fun l _ l' _ => ?_⟩
  exact hermitianInner_conjugateBy hu (fun _ => rfl) (fun _ => rfl)
theorem gaugeUnitarity_holds
    (hnb : ∀ b : Edge L m k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented) :
    GaugeUnitarity L m k j := by
  refine ⟨hermitianSeriesAbsConv_all _, hermitianSeriesAbsConv_all _, fun u hu => ?_⟩
  have hg : ∀ x, u x ∈ ComplexMatrix2.specialUnitary := hu
  exact ⟨fun B hB => adjointForm_mem_edgeFormSpace hnb u hg hB,
    fun l hl => adjointVertexFn_mem u hg hl,
    adjointForm_isUnitaryOnSet hnb u hg, adjointVertexFn_isUnitaryOnSet u hg⟩
end FiniteSide
theorem gaugeIdentitiesFiniteSide_holds (hA : QuotientLattices.TorusAndSpaceLatticeProperties) :
    GaugeConditionsFiniteSide :=
  fun L m k j hL hm hj =>
    ⟨gaugeCovariance_holds L m k j,
      gaugeUnitarity_holds fun b hb => not_opposite_positive hA hL hm hj b hb⟩
end YangMills.Construction.Tower.LeftChartAlgebra.GaugeRequirements
end
