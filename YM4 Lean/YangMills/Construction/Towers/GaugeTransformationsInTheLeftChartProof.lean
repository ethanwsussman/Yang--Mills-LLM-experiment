import YangMills.Construction.Matrices.UnitaryLogConjugationProof
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import YangMills.Construction.Lattice.TransposesOfTheCovariantDerivativesOnALatticeProof
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChart
import YangMills.Construction.Towers.WilsonActionIsRealAnalyticOnTheConfigurationsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.LeftChartGauge
open YangMills.Construction.Matrices
theorem isUnit_det_of_det_eq_one {V : ComplexMatrix2} (h : V.det = 1) : IsUnit V.det := by apply _root_.YangMills.SharedProofs.p11557 <;> assumption
theorem matExp_conjugateBy_mul (V W X M : ComplexMatrix2) (hV : V.det = 1) :
    ComplexMatrix2.matExp (Complex.I • ComplexMatrix2.conjugateBy V X) * (V * M * W) =
      V * (ComplexMatrix2.matExp (Complex.I • X) * M) * W := by
  have hconj : Complex.I • ComplexMatrix2.conjugateBy V X = V * (Complex.I • X) * V⁻¹ := by
    simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
  have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V (isUnit_det_of_det_eq_one hV)
  have hexp : ComplexMatrix2.matExp (V * (Complex.I • X) * V⁻¹) =
      V * ComplexMatrix2.matExp (Complex.I • X) * V⁻¹ :=
    Matrix.exp_conj V _ ((Matrix.isUnit_iff_isUnit_det V).2 (isUnit_det_of_det_eq_one hV))
  rw [hconj, hexp]
  calc V * ComplexMatrix2.matExp (Complex.I • X) * V⁻¹ * (V * M * W)
      = V * ComplexMatrix2.matExp (Complex.I • X) * (V⁻¹ * V) * M * W := by
        simp only [mul_assoc]
    _ = V * (ComplexMatrix2.matExp (Complex.I • X) * M) * W := by
        rw [hinv, mul_one]
        simp only [mul_assoc]
theorem inv_matExp_conjugateBy_mul (V W X M : ComplexMatrix2) (hV : V.det = 1) (hW : W.det = 1) :
    (ComplexMatrix2.matExp (Complex.I • ComplexMatrix2.conjugateBy V X) * (V * M * W⁻¹))⁻¹ =
      W * (ComplexMatrix2.matExp (Complex.I • X) * M)⁻¹ * V⁻¹ := by
  rw [matExp_conjugateBy_mul V W⁻¹ X M hV, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv W (isUnit_det_of_det_eq_one hW), mul_assoc]
theorem halfTrace_conjugateBy_mul (V X Y : ComplexMatrix2) (hV : V.det = 1) :
    ComplexMatrix2.halfTrace (ComplexMatrix2.conjugateBy V X * ComplexMatrix2.conjugateBy V Y) =
      ComplexMatrix2.halfTrace (X * Y) := by
  have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V (isUnit_det_of_det_eq_one hV)
  have hprod : ComplexMatrix2.conjugateBy V X * ComplexMatrix2.conjugateBy V Y =
      V * (X * Y * V⁻¹) := by
    calc ComplexMatrix2.conjugateBy V X * ComplexMatrix2.conjugateBy V Y
        = V * X * (V⁻¹ * V) * Y * V⁻¹ := by
          simp only [ComplexMatrix2.conjugateBy, mul_assoc]
      _ = V * (X * Y * V⁻¹) := by
          rw [hinv, mul_one]
          simp only [mul_assoc]
  rw [hprod, ComplexMatrix2.halfTrace, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    ComplexMatrix2.fullTrace, Matrix.trace_mul_comm, mul_assoc, hinv, mul_one]
theorem conjugateBy_add (V X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy V (X + Y) =
      ComplexMatrix2.conjugateBy V X + ComplexMatrix2.conjugateBy V Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (V X : ComplexMatrix2) (c : ℝ) :
    ComplexMatrix2.conjugateBy V (c • X) = c • ComplexMatrix2.conjugateBy V X := by
  simp only [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
theorem conjugateBy_inv_conjugateBy (V X : ComplexMatrix2) (hV : V.det = 1) :
    ComplexMatrix2.conjugateBy V⁻¹ (ComplexMatrix2.conjugateBy V X) = X := by
  have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V (isUnit_det_of_det_eq_one hV)
  simp only [ComplexMatrix2.conjugateBy,
    Matrix.nonsing_inv_nonsing_inv V (isUnit_det_of_det_eq_one hV)]
  calc V⁻¹ * (V * X * V⁻¹) * V = (V⁻¹ * V) * X * (V⁻¹ * V) := by simp only [mul_assoc]
    _ = X := by rw [hinv, one_mul, mul_one]
theorem conjugateBy_conjugateBy_inv (V X : ComplexMatrix2) (hV : V.det = 1) :
    ComplexMatrix2.conjugateBy V (ComplexMatrix2.conjugateBy V⁻¹ X) = X := by
  have hinv : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V (isUnit_det_of_det_eq_one hV)
  simp only [ComplexMatrix2.conjugateBy,
    Matrix.nonsing_inv_nonsing_inv V (isUnit_det_of_det_eq_one hV)]
  calc V * (V⁻¹ * X * V) * V⁻¹ = (V * V⁻¹) * X * (V * V⁻¹) := by simp only [mul_assoc]
    _ = X := by rw [hinv, one_mul, mul_one]
theorem det_eq_one_of_mem_specialUnitary {V : ComplexMatrix2}
    (hV : V ∈ ComplexMatrix2.specialUnitary) : V.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hV).2
theorem inv_eq_conjTranspose_of_mem {V : ComplexMatrix2}
    (hV : V ∈ ComplexMatrix2.specialUnitary) : V⁻¹ = V.conjTranspose := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_eq_conjTranspose_of_mem_specialUnitary <;> assumption
theorem inv_mem_specialUnitary {V : ComplexMatrix2} (hV : V ∈ ComplexMatrix2.specialUnitary) :
    V⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
theorem conjugateBy_mem_hermitianTraceless {V X : ComplexMatrix2}
    (hV : V ∈ ComplexMatrix2.specialUnitary) (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy V X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.DeltaSharedProofs.p501638 <;> assumption
theorem traceFinsumPairing_conjugateBy {ι : Type*} {f f' g g' v : ι → ComplexMatrix2}
    (hv : ∀ i, (v i).det = 1) (hg : ∀ i, g i = ComplexMatrix2.conjugateBy (v i) (f i))
    (hg' : ∀ i, g' i = ComplexMatrix2.conjugateBy (v i) (f' i)) :
    traceFinsumPairing g g' = traceFinsumPairing f f' := by
  unfold traceFinsumPairing
  refine finsum_congr fun i => ?_
  rw [hg, hg', halfTrace_conjugateBy_mul _ _ _ (hv i)]
theorem isOrthogonalOn_of_inverse {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Submodule ℝ E) (p : E → E → ℂ) (T T' : E → E)
    (hadd : ∀ x y, x ∈ S → y ∈ S → T (x + y) = T x + T y)
    (hsmul : ∀ (c : ℝ) (x : E), x ∈ S → T (c • x) = c • T x)
    (hT : ∀ x ∈ S, T x ∈ S) (hT' : ∀ x ∈ S, T' x ∈ S)
    (hleft : ∀ x ∈ S, T' (T x) = x) (hright : ∀ x ∈ S, T (T' x) = x)
    (hp : ∀ x ∈ S, ∀ y ∈ S, p (T x) (T y) = p x y) :
    YangMills.Construction.Tower.LeftChartFacts.IsOrthogonalOn S p T := by
  refine ⟨{ toFun := fun x => ⟨T x, hT x x.2⟩
            map_add' := fun x y => Subtype.ext (hadd x y x.2 y.2)
            map_smul' := fun c x => Subtype.ext (hsmul c x x.2)
            invFun := fun x => ⟨T' x, hT' x x.2⟩
            left_inv := fun x => Subtype.ext (hleft x x.2)
            right_inv := fun x => Subtype.ext (hright x x.2) }, fun x => rfl,
    fun x y => hp x x.2 y y.2⟩
section Periodic
variable {L m k j : ℕ}
theorem edge_positive_or_opposite (b : Edge L m k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem edge_not_both_positive (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k) (b : Edge L m k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_not_both_positive <;> assumption
theorem adjointForm_of_positive (u : Vertex L m k j → ComplexMatrix2)
    (B : Edge L m k j → ComplexMatrix2) {b : Edge L m k j} (hb : b.IsPositivelyOriented) :
    adjointForm u B b = ComplexMatrix2.conjugateBy (u b.source) (B b) := by
  unfold adjointForm extendOddly
  exact if_pos hb
theorem adjointForm_of_not_positive (u : Vertex L m k j → ComplexMatrix2)
    (B : Edge L m k j → ComplexMatrix2) {b : Edge L m k j} (hb : ¬ b.IsPositivelyOriented) :
    adjointForm u B b = -ComplexMatrix2.conjugateBy (u b.opposite.source) (B b.opposite) := by
  unfold adjointForm extendOddly
  exact if_neg hb
theorem expTwist_of_positive (A U : Edge L m k j → ComplexMatrix2) {b : Edge L m k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by
  unfold PeriodicLattice.expTwist
  exact if_pos hb
theorem expTwist_of_not_positive (A U : Edge L m k j → ComplexMatrix2) {b : Edge L m k j}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by
  unfold PeriodicLattice.expTwist
  exact if_neg hb
theorem expTwist_adjointForm_gaugeTransform (u : Vertex L m k j → ComplexMatrix2)
    (hu : ∀ x, (u x).det = 1) (U B : Edge L m k j → ComplexMatrix2) :
    PeriodicLattice.expTwist (adjointForm u B) (PeriodicLattice.gaugeTransform u U) =
      PeriodicLattice.gaugeTransform u (PeriodicLattice.expTwist B U) := by
  funext b
  change _ = u b.source * PeriodicLattice.expTwist B U b * (u b.target)⁻¹
  by_cases hb : b.IsPositivelyOriented
  · rw [expTwist_of_positive _ _ hb, expTwist_of_positive _ _ hb, adjointForm_of_positive _ _ hb]
    exact matExp_conjugateBy_mul (u b.source) (u b.target)⁻¹ (B b) (U b) (hu _)
  · have hopp := (edge_positive_or_opposite b).resolve_left hb
    rw [expTwist_of_not_positive _ _ hb, expTwist_of_not_positive _ _ hb,
      adjointForm_of_positive _ _ hopp]
    exact inv_matExp_conjugateBy_mul (u b.opposite.source) (u b.opposite.target) (B b.opposite)
      (U b.opposite) (hu _) (hu _)
theorem edgeFormPairing_adjointForm (u : Vertex L m k j → ComplexMatrix2)
    (hu : ∀ x, (u x).det = 1) (B B' : Edge L m k j → ComplexMatrix2) :
    edgeFormPairing (adjointForm u B) (adjointForm u B') = edgeFormPairing B B' :=
  traceFinsumPairing_conjugateBy (v := fun b : PositiveEdge L m k j => u b.1.source)
    (fun _ => hu _) (fun b => adjointForm_of_positive u B b.2)
    (fun b => adjointForm_of_positive u B' b.2)
theorem adjointForm_add (u : Vertex L m k j → ComplexMatrix2)
    (B B' : Edge L m k j → ComplexMatrix2) :
    adjointForm u (B + B') = adjointForm u B + adjointForm u B' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [Pi.add_apply, adjointForm_of_positive _ _ hb, conjugateBy_add]
  · simp only [Pi.add_apply, adjointForm_of_not_positive _ _ hb, conjugateBy_add, neg_add]
theorem adjointForm_smul (u : Vertex L m k j → ComplexMatrix2) (c : ℝ)
    (B : Edge L m k j → ComplexMatrix2) :
    adjointForm u (c • B) = c • adjointForm u B := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [Pi.smul_apply, adjointForm_of_positive _ _ hb, conjugateBy_smul]
  · simp only [Pi.smul_apply, adjointForm_of_not_positive _ _ hb, conjugateBy_smul, smul_neg]
theorem adjointForm_mem
    (hnb : ∀ b : Edge L m k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (u : Vertex L m k j → ComplexMatrix2) (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary)
    {B : Edge L m k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L m k j) :
    adjointForm u B ∈ edgeFormSpace L m k j := by
  obtain ⟨hval, -⟩ := hB
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [adjointForm_of_positive _ _ hb]
    exact conjugateBy_mem_hermitianTraceless (hu _) (hval b hb)
  · by_cases hb : b.IsPositivelyOriented
    · rw [adjointForm_of_not_positive _ _ (hnb b hb), adjointForm_of_positive _ _ hb]
      rfl
    · have hopp := (edge_positive_or_opposite b).resolve_left hb
      rw [adjointForm_of_positive _ _ hopp, adjointForm_of_not_positive _ _ hb, neg_neg]
theorem adjointForm_adjointForm (u w : Vertex L m k j → ComplexMatrix2)
    (h : ∀ x X, ComplexMatrix2.conjugateBy (w x) (ComplexMatrix2.conjugateBy (u x) X) = X)
    {B : Edge L m k j → ComplexMatrix2} (hB : B ∈ edgeFormSpace L m k j) :
    adjointForm w (adjointForm u B) = B := by
  obtain ⟨-, hodd⟩ := hB
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [adjointForm_of_positive _ _ hb, adjointForm_of_positive _ _ hb, h]
  · have hpos := (edge_positive_or_opposite b).resolve_left hb
    rw [adjointForm_of_not_positive _ _ hb, adjointForm_of_positive _ _ hpos, h, hodd, neg_neg]
theorem adjointVertexFn_add (u l l' : Vertex L m k j → ComplexMatrix2) :
    adjointVertexFn u (l + l') = adjointVertexFn u l + adjointVertexFn u l' :=
  funext fun _ => conjugateBy_add _ _ _
theorem adjointVertexFn_smul (u : Vertex L m k j → ComplexMatrix2) (c : ℝ)
    (l : Vertex L m k j → ComplexMatrix2) :
    adjointVertexFn u (c • l) = c • adjointVertexFn u l :=
  funext fun _ => conjugateBy_smul _ _ _
theorem adjointVertexFn_mem (u : Vertex L m k j → ComplexMatrix2)
    (hu : ∀ x, u x ∈ ComplexMatrix2.specialUnitary)
    {l : Vertex L m k j → ComplexMatrix2} (hl : l ∈ vertexFunctionSpace L m k j) :
    adjointVertexFn u l ∈ vertexFunctionSpace L m k j :=
  fun x _ => conjugateBy_mem_hermitianTraceless (hu x) (hl x (mem_univ x))
theorem gaugeEquivarianceForms_of_not_both
    (hnb : ∀ b : Edge L m k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented) :
    YangMills.Construction.Tower.LeftChartFacts.GaugeEquivarianceForms L m k j := by
  intro u hu
  have hdet : ∀ x, (u x).det = 1 := hu
  refine ⟨fun U _ B _ => expTwist_adjointForm_gaugeTransform u hdet U B,
    fun B _ B' _ => edgeFormPairing_adjointForm u hdet B B',
    fun l l' _ _ => traceFinsumPairing_conjugateBy hdet (fun _ => rfl) (fun _ => rfl),
    fun hg => ?_⟩
  have hg' : ∀ x, u x ∈ ComplexMatrix2.specialUnitary := hg
  have hinv : ∀ x, (fun y => (u y)⁻¹) x ∈ ComplexMatrix2.specialUnitary :=
    fun x => inv_mem_specialUnitary (hg' x)
  refine ⟨isOrthogonalOn_of_inverse _ _ _ (adjointForm fun x => (u x)⁻¹)
      (fun B B' _ _ => adjointForm_add u B B') (fun c B _ => adjointForm_smul u c B)
      (fun B hB => adjointForm_mem hnb u hg' hB) (fun B hB => adjointForm_mem hnb _ hinv hB)
      (fun B hB => adjointForm_adjointForm _ _
        (fun x X => conjugateBy_inv_conjugateBy _ X (hdet x)) hB)
      (fun B hB => adjointForm_adjointForm _ _
        (fun x X => conjugateBy_conjugateBy_inv _ X (hdet x)) hB)
      (fun B _ B' _ => edgeFormPairing_adjointForm u hdet B B'),
    isOrthogonalOn_of_inverse _ _ _ (adjointVertexFn fun x => (u x)⁻¹)
      (fun l l' _ _ => adjointVertexFn_add u l l') (fun c l _ => adjointVertexFn_smul u c l)
      (fun l hl => adjointVertexFn_mem u hg' hl) (fun l hl => adjointVertexFn_mem _ hinv hl)
      (fun l _ => funext fun x => conjugateBy_inv_conjugateBy _ _ (hdet x))
      (fun l _ => funext fun x => conjugateBy_conjugateBy_inv _ _ (hdet x))
      (fun l _ l' _ => traceFinsumPairing_conjugateBy hdet (fun _ => rfl) (fun _ => rfl))⟩
end Periodic
section Infinite
variable {a : ℝ}
theorem link_positive_or_opposite (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem fullSpace_adjointForm_of_positive (u : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B : InfiniteLattice.Link a → ComplexMatrix2) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) :
    FullSpace.adjointForm u B b = ComplexMatrix2.conjugateBy (u b.initial) (B b) := by
  unfold FullSpace.adjointForm FullSpace.extendOddly
  exact if_pos hb
theorem fullSpace_expTwist_of_positive (A U : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    FullSpace.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by
  unfold FullSpace.expTwist
  exact if_pos hb
theorem fullSpace_expTwist_of_not_positive (A U : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : ¬ b.IsPositivelyOriented) :
    FullSpace.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by
  unfold FullSpace.expTwist
  exact if_neg hb
theorem fullSpace_expTwist_adjointForm_gaugeAct
    (u : InfiniteLattice.LatticePoint a → ComplexMatrix2) (hu : ∀ x, (u x).det = 1)
    (U B : InfiniteLattice.Link a → ComplexMatrix2) :
    FullSpace.expTwist (FullSpace.adjointForm u B) (FullSpace.gaugeAct u U) =
      FullSpace.gaugeAct u (FullSpace.expTwist B U) := by
  funext b
  change _ = u b.initial * FullSpace.expTwist B U b * (u b.terminal)⁻¹
  by_cases hb : b.IsPositivelyOriented
  · rw [fullSpace_expTwist_of_positive _ _ hb, fullSpace_expTwist_of_positive _ _ hb,
      fullSpace_adjointForm_of_positive _ _ hb]
    exact matExp_conjugateBy_mul (u b.initial) (u b.terminal)⁻¹ (B b) (U b) (hu _)
  · have hopp := (link_positive_or_opposite b).resolve_left hb
    rw [fullSpace_expTwist_of_not_positive _ _ hb, fullSpace_expTwist_of_not_positive _ _ hb,
      fullSpace_adjointForm_of_positive _ _ hopp]
    exact inv_matExp_conjugateBy_mul (u b.opposite.initial) (u b.opposite.terminal)
      (B b.opposite) (U b.opposite) (hu _) (hu _)
theorem fullSpace_edgeFormPairing_adjointForm
    (u : InfiniteLattice.LatticePoint a → ComplexMatrix2) (hu : ∀ x, (u x).det = 1)
    (B B' : InfiniteLattice.Link a → ComplexMatrix2) :
    FullSpace.finiteEdgePairing (FullSpace.adjointForm u B) (FullSpace.adjointForm u B') =
      FullSpace.finiteEdgePairing B B' :=
  traceFinsumPairing_conjugateBy (v := fun b : FullSpace.PositiveEdge a => u b.1.initial)
    (fun _ => hu _) (fun b => fullSpace_adjointForm_of_positive u B b.2)
    (fun b => fullSpace_adjointForm_of_positive u B' b.2)
end Infinite
theorem fullSpace_gaugeEquivarianceForms (L k j : ℕ) :
    FullSpace.LeftChartFacts.GaugeEquivarianceForms L k j := by
  intro u hu
  have hdet : ∀ x, (u x).det = 1 := hu
  exact ⟨fun U _ B _ => fullSpace_expTwist_adjointForm_gaugeAct u hdet U B,
    fun B _ B' _ _ => fullSpace_edgeFormPairing_adjointForm u hdet B B',
    fun l l' _ _ _ => traceFinsumPairing_conjugateBy hdet (fun _ => rfl) (fun _ => rfl)⟩
theorem gaugeEquivarianceFormsAllSides_holds
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties) : GaugeEquivarianceFormsAllSides :=
  fun L k j hL hj =>
    ⟨fun _ hm => gaugeEquivarianceForms_of_not_both fun b hb => edge_not_both_positive hA hL hm hj b hb,
      fullSpace_gaugeEquivarianceForms L k j⟩
end YangMills.Construction.Tower.LeftChartGauge
end
