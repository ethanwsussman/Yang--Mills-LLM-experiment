import YangMills.Construction.ClusterExpansion.PolymerSystemOfARegion
import YangMills.Construction.Lattice.OppositeBondsAndPositiveValues
import YangMills.Construction.Matrices.ConjugationDeterminantProof
import YangMills.Construction.Towers.AlgebraOfTheLeftChart
import YangMills.Construction.Towers.IsometryCovarianceOfTheCovariantAveragesOnTheWholeLatticeProof
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAndTheTwoDeterminants
import YangMills.Construction.Towers.TheBackgroundKernelAtZeroProof
import YangMills.Construction.Towers.TheMassiveFunctionalIsGaugeInvariant
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.Tower.MassiveFunctionals.GaugeInvariance
open YangMills.Construction.Matrices
open Massive (shiftedDetOn restrictToSubmodule)
open PairedFunctionSpace (linearOfValues transposeOfValues)
section Determinants
variable {E : Type} [AddCommGroup E] [Module ℝ E] {W : Submodule ℝ E}
theorem restrictToSubmodule_eq {T : E → E} (X : W →ₗ[ℝ] W) (hX : ∀ f : W, (X f : E) = T f) :
    restrictToSubmodule W T = X := by
  have h : ∀ f : W, (restrictToSubmodule W T f : E) = T f :=
    Classical.epsilon_spec (p := fun T' : W →ₗ[ℝ] W => ∀ f : W, (T' f : E) = T f) ⟨X, hX⟩
  exact LinearMap.ext fun f => Subtype.ext ((h f).trans (hX f).symm)
theorem shiftedDetOn_conj {T T' : E → E} (z : ℝ) (e : W ≃ₗ[ℝ] W) (A : W →ₗ[ℝ] W)
    (hA : ∀ f : W, (A f : E) = T f) (hT : ∀ f : W, T' (e f : E) = (e (A f) : E)) :
    shiftedDetOn W T' z = shiftedDetOn W T z := by
  set C : W →ₗ[ℝ] W := A + z • LinearMap.id with hC
  have h₁ : restrictToSubmodule W (fun f => T f + z • f) = C :=
    restrictToSubmodule_eq C fun f => by simp [hC, hA]
  have h₂ : restrictToSubmodule W (fun f => T' f + z • f) =
      (e : W →ₗ[ℝ] W) ∘ₗ C ∘ₗ (e.symm : W →ₗ[ℝ] W) := by
    refine restrictToSubmodule_eq _ fun f => ?_
    have h := hT (e.symm f)
    rw [LinearEquiv.apply_symm_apply] at h
    simp [hC, h]
  unfold shiftedDetOn
  rw [h₁, h₂, LinearMap.det_conj]
end Determinants
section Pairing
variable {ι : Type}
theorem traceFinsumPairing_sub_right [Finite ι] (c f g : ι → ComplexMatrix2) :
    traceFinsumPairing c (f - g) = traceFinsumPairing c f - traceFinsumPairing c g := by
  unfold traceFinsumPairing
  rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
  refine finsum_congr fun i => ?_
  simp only [Pi.sub_apply, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, mul_sub,
    Matrix.trace_sub]
theorem traceFinsumPairing_comm (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = traceFinsumPairing g f := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelAtZeroSources.traceFinsumPairing_comm <;> assumption
theorem eq_zero_of_traceFinsumPairing_conjTranspose_self [Finite ι] (X : ι → ComplexMatrix2)
    (h : traceFinsumPairing (fun i => (X i).conjTranspose) X = 0) : X = 0 := by
  have := Fintype.ofFinite ι
  unfold traceFinsumPairing at h
  rw [finsum_eq_sum_of_fintype] at h
  have hnn : ∀ i ∈ Finset.univ,
      0 ≤ ComplexMatrix2.halfTrace ((X i).conjTranspose * X i) := fun i _ => by
    have h₀ : 0 ≤ Matrix.trace ((X i).conjTranspose * X i) :=
      (Matrix.posSemidef_conjTranspose_mul_self (X i)).trace_nonneg
    simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
    refine mul_nonneg ?_ h₀
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.zero_le_real.2 (by norm_num)
  funext i
  have h₁ := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h i (Finset.mem_univ i)
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, mul_eq_zero] at h₁
  rcases h₁ with h₁ | h₁
  · norm_num at h₁
  · exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h₁
end Pairing
theorem conjTranspose_mem_traceless {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    X.conjTranspose ∈ ComplexMatrix2.traceless := by
  have h₀ : Matrix.trace X = 0 := h
  change Matrix.trace X.conjTranspose = 0
  rw [Matrix.trace_conjTranspose, h₀, star_zero]
theorem conjugateBy_traceless {g X : ComplexMatrix2} (hg : IsUnit g.det)
    (h : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy g X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.FullSpace.IsometryEquivariance.conjugateBy_mem_traceless_of_isUnit <;> assumption
theorem conjugateBy_conjugateBy_inv {g : ComplexMatrix2} (hg : IsUnit g.det) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (ComplexMatrix2.conjugateBy g⁻¹ X) = X := by apply _root_.YangMills.SharedProofs.p1183 <;> assumption
theorem conjugateBy_add (g X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (X + Y) =
      ComplexMatrix2.conjugateBy g X + ComplexMatrix2.conjugateBy g Y := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
section Forms
variable {L n : ℕ}
theorem mem_complexEdgeForms_iff {B : Edge L n 0 0 → ComplexMatrix2} :
    B ∈ complexEdgeForms L n 0 0 ↔
      PeriodicLattice.IsBondForm PeriodicLattice.complexLieAlgebra B := Iff.rfl
theorem extendOddly_of_pos (f : Edge L n 0 0 → ComplexMatrix2) {b : Edge L n 0 0}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by
  simp only [extendOddly, if_pos hb]
theorem extendOddly_of_not_pos (f : Edge L n 0 0 → ComplexMatrix2) {b : Edge L n 0 0}
    (hb : ¬ b.IsPositivelyOriented) : extendOddly f b = -f b.opposite := by
  simp only [extendOddly, if_neg hb]
def UniqueOrientation (L n : ℕ) : Prop :=
  ∀ b : Edge L n 0 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
theorem UniqueOrientation.opposite_pos (h : UniqueOrientation L n)
    {b : Edge L n 0 0} (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  rcases h b with h₁ | h₁
  · exact absurd h₁.1 hb
  · exact h₁.1
theorem UniqueOrientation.not_opposite_pos (h : UniqueOrientation L n)
    {b : Edge L n 0 0} (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  rcases h b with h₁ | h₁
  · exact h₁.2
  · exact absurd hb h₁.2
theorem extendOddly_opposite (h : UniqueOrientation L n) (f : Edge L n 0 0 → ComplexMatrix2)
    (b : Edge L n 0 0) : extendOddly f b.opposite = -extendOddly f b := by
  by_cases hb : b.IsPositivelyOriented
  · rw [extendOddly_of_not_pos f (h.not_opposite_pos hb), extendOddly_of_pos f hb]
    rfl
  · rw [extendOddly_of_pos f (h.opposite_pos hb), extendOddly_of_not_pos f hb, neg_neg]
theorem adjointForm_mem (h : UniqueOrientation L n) {v : Vertex L n 0 0 → ComplexMatrix2}
    (hv : ∀ x, IsUnit (v x).det) {B : Edge L n 0 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) :
    adjointForm v B ∈ complexEdgeForms L n 0 0 := by
  refine mem_complexEdgeForms_iff.2 ⟨fun b hb => ?_, extendOddly_opposite h _⟩
  change adjointForm v B b ∈ ComplexMatrix2.traceless
  rw [adjointForm, extendOddly_of_pos _ hb]
  exact conjugateBy_traceless (hv _) ((mem_complexEdgeForms_iff.1 hB).1 b hb)
theorem adjointForm_adjointForm_inv (h : UniqueOrientation L n)
    {v : Vertex L n 0 0 → ComplexMatrix2} (hv : ∀ x, IsUnit (v x).det)
    {B : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n 0 0) :
    adjointForm v (adjointForm (fun x => (v x)⁻¹) B) = B := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [adjointForm, extendOddly_of_pos _ hb, adjointForm,
      extendOddly_of_pos _ hb, conjugateBy_conjugateBy_inv (hv _)]
  · have hr := h.opposite_pos hb
    rw [adjointForm, extendOddly_of_not_pos _ hb, adjointForm,
      extendOddly_of_pos _ hr, conjugateBy_conjugateBy_inv (hv _),
      (mem_complexEdgeForms_iff.1 hB).2 b, neg_neg]
theorem adjointForm_add (v : Vertex L n 0 0 → ComplexMatrix2) (B B' : Edge L n 0 0 → ComplexMatrix2) :
    adjointForm v (B + B') = adjointForm v B + adjointForm v B' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [adjointForm, Pi.add_apply, extendOddly_of_pos _ hb, conjugateBy_add]
  · simp only [adjointForm, Pi.add_apply, extendOddly_of_not_pos _ hb, conjugateBy_add, neg_add]
theorem eq_of_restrictToPositiveEdges_eq (h : UniqueOrientation L n)
    {X Y : Edge L n 0 0 → ComplexMatrix2}
    (hX : X ∈ complexEdgeForms L n 0 0) (hY : Y ∈ complexEdgeForms L n 0 0)
    (hXY : restrictToPositiveEdges X = restrictToPositiveEdges Y) : X = Y := by
  have hp : ∀ b : Edge L n 0 0, b.IsPositivelyOriented → X b = Y b := fun b hb =>
    congrFun hXY ⟨b, hb⟩
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact hp b hb
  · have hr := hp _ (h.opposite_pos hb)
    rw [(mem_complexEdgeForms_iff.1 hX).2 b, (mem_complexEdgeForms_iff.1 hY).2 b] at hr
    exact neg_injective hr
theorem eq_of_edgeFormPairing_eq [Finite (PositiveEdge L n 0 0)] (h : UniqueOrientation L n)
    {X Y : Edge L n 0 0 → ComplexMatrix2} (hX : X ∈ complexEdgeForms L n 0 0)
    (hY : Y ∈ complexEdgeForms L n 0 0)
    (hXY : ∀ C ∈ complexEdgeForms L n 0 0, edgeFormPairing C X = edgeFormPairing C Y) :
    X = Y := by
  have hD : X - Y ∈ complexEdgeForms L n 0 0 := Submodule.sub_mem _ hX hY
  have hC : (fun b => (X b - Y b).conjTranspose) ∈ complexEdgeForms L n 0 0 := by
    refine mem_complexEdgeForms_iff.2 ⟨fun b hb => ?_, fun b => ?_⟩
    · exact conjTranspose_mem_traceless ((mem_complexEdgeForms_iff.1 hD).1 b hb)
    · have hr := (mem_complexEdgeForms_iff.1 hD).2 b
      simp only [Pi.sub_apply] at hr
      simp only [hr, Matrix.conjTranspose_neg]
  refine eq_of_restrictToPositiveEdges_eq h hX hY (sub_eq_zero.1 ?_)
  refine eq_zero_of_traceFinsumPairing_conjTranspose_self _ ?_
  have h₀ := hXY _ hC
  unfold edgeFormPairing at h₀
  have h₁ := traceFinsumPairing_sub_right
    (restrictToPositiveEdges fun b => (X b - Y b).conjTranspose)
    (restrictToPositiveEdges X) (restrictToPositiveEdges Y)
  rw [h₀, sub_self] at h₁
  exact h₁
theorem eq_of_traceFinsumPairing_eq [Finite (Vertex L n 0 0)]
    {X Y : Vertex L n 0 0 → ComplexMatrix2}
    (hX : ∀ x, X x ∈ ComplexMatrix2.traceless) (hY : ∀ x, Y x ∈ ComplexMatrix2.traceless)
    (hXY : ∀ c : Vertex L n 0 0 → ComplexMatrix2, (∀ x, c x ∈ ComplexMatrix2.traceless) →
      traceFinsumPairing c X = traceFinsumPairing c Y) :
    X = Y := by
  refine sub_eq_zero.1 (eq_zero_of_traceFinsumPairing_conjTranspose_self _ ?_)
  have h₀ := hXY (fun x => (X x - Y x).conjTranspose) fun x =>
    conjTranspose_mem_traceless (ComplexMatrix2.traceless.sub_mem (hX x) (hY x))
  have h₁ := traceFinsumPairing_sub_right (fun x => (X x - Y x).conjTranspose) X Y
  rw [h₀, sub_self] at h₁
  exact h₁
end Forms
section Operators
structure ConjugationData (L n : ℕ) (U : Edge L n 0 0 → ComplexMatrix2)
    (v : Vertex L n 0 0 → ComplexMatrix2) : Prop where
  finite_vertices : Finite (Vertex L n 0 0)
  finite_edges : Finite (PositiveEdge L n 0 0)
  orientation : UniqueOrientation L n
  transposes : CovDiffTransposes.OnTorus L n 0 0
  kernel : HessianKernel.HoldsOnTorus L n 0 0
  field_mem : U ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup
  gauge_field_mem : PeriodicLattice.gaugeTransform v U ∈
    fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup
  det_isUnit : ∀ x, IsUnit (v x).det
  covDiff_conj : ∀ l : Vertex L n 0 0 → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
    covDiff (PeriodicLattice.gaugeTransform v U) (adjointVertexFn v l) =
      adjointForm v (covDiff U l)
  edgePairing_conj : ∀ B ∈ complexEdgeForms L n 0 0, ∀ B' ∈ complexEdgeForms L n 0 0,
    edgeFormPairing (adjointForm v B) (adjointForm v B') = edgeFormPairing B B'
  vertexPairing_conj : ∀ l l' : Vertex L n 0 0 → ComplexMatrix2,
    (∀ x, l x ∈ ComplexMatrix2.traceless) → (∀ x, l' x ∈ ComplexMatrix2.traceless) →
    traceFinsumPairing (adjointVertexFn v l) (adjointVertexFn v l') = traceFinsumPairing l l'
  hessian_conj : ∀ B ∈ complexEdgeForms L n 0 0, ∀ B' ∈ complexEdgeForms L n 0 0,
    complexActionHessian (PeriodicLattice.gaugeTransform v U) (adjointForm v B)
      (adjointForm v B') = complexActionHessian U B B'
variable {L n : ℕ}
theorem transposeOfValues_spec (hT : CovDiffTransposes.OnTorus L n 0 0)
    [Finite (Vertex L n 0 0)] {U : Edge L n 0 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup)
    {g : Edge L n 0 0 → ComplexMatrix2} (hg : g ∈ complexEdgeForms L n 0 0) :
    (∀ x, transposeOfValues (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0)
        (covDiff U) g x ∈ ComplexMatrix2.traceless) ∧
      ∀ l : Vertex L n 0 0 → ComplexMatrix2, (∀ x, l x ∈ ComplexMatrix2.traceless) →
        traceFinsumPairing (transposeOfValues (pairedFunctions (Vertex L n 0 0))
          (edgePairedSpace L n 0 0) (covDiff U) g) l = edgeFormPairing g (covDiff U l) := by
  have c := (hT U hU).covDiff
  have hgc : g ∈ (edgePairedSpace L n 0 0).complexSubmodule := hg
  have hval : transposeOfValues (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0)
      (covDiff U) g =
      (PairedFunctionSpace.transposeMap (linearOfValues (pairedFunctions (Vertex L n 0 0))
        (edgePairedSpace L n 0 0) (covDiff U)) ⟨g, hgc⟩ :
          (pairedFunctions (Vertex L n 0 0)).complexSubmodule).1 := dif_pos hgc
  rw [hval]
  refine ⟨fun x => ?_, fun l hl => ?_⟩
  · exact (PairedFunctionSpace.transposeMap (linearOfValues (pairedFunctions (Vertex L n 0 0))
      (edgePairedSpace L n 0 0) (covDiff U)) ⟨g, hgc⟩).2 x (Set.mem_univ x)
  · have hlc : l ∈ (pairedFunctions (Vertex L n 0 0)).complexSubmodule := fun x _ => hl x
    have h₁ := c.isTranspose ⟨g, hgc⟩ ⟨l, hlc⟩ (Set.toFinite _)
    have h₂ : (linearOfValues (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0)
        (covDiff U) ⟨l, hlc⟩).1 = covDiff U l := c.coe_linear ⟨l, hlc⟩
    exact h₁.trans (congrArg (edgeFormPairing g) h₂)
theorem covDiff_mem (hT : CovDiffTransposes.OnTorus L n 0 0)
    {U : Edge L n 0 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup)
    {l : Vertex L n 0 0 → ComplexMatrix2} (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) :
    covDiff U l ∈ complexEdgeForms L n 0 0 := by
  have hlc : l ∈ (pairedFunctions (Vertex L n 0 0)).complexSubmodule := fun x _ => hl x
  have h₂ : (linearOfValues (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0)
      (covDiff U) ⟨l, hlc⟩).1 = covDiff U l :=
    (hT U hU).covDiff.coe_linear ⟨l, hlc⟩
  exact h₂ ▸ (linearOfValues (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0)
    (covDiff U) ⟨l, hlc⟩).2
variable {U : Edge L n 0 0 → ComplexMatrix2} {v : Vertex L n 0 0 → ComplexMatrix2}
theorem adjointVertexFn_mem (h : ConjugationData L n U v) {l : Vertex L n 0 0 → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (x : Vertex L n 0 0) :
    adjointVertexFn v l x ∈ ComplexMatrix2.traceless :=
  conjugateBy_traceless (h.det_isUnit x) (hl x)
theorem inv_det_isUnit (h : ConjugationData L n U v) (x : Vertex L n 0 0) :
    IsUnit ((v x)⁻¹).det :=
  Matrix.isUnit_nonsing_inv_det _ (h.det_isUnit x)
theorem transpose_conj (h : ConjugationData L n U v) {g : Edge L n 0 0 → ComplexMatrix2}
    (hg : g ∈ complexEdgeForms L n 0 0) :
    transposeOfValues (pairedFunctions (Vertex L n 0 0)) (edgePairedSpace L n 0 0)
        (covDiff (PeriodicLattice.gaugeTransform v U)) (adjointForm v g) =
      adjointVertexFn v (transposeOfValues (pairedFunctions (Vertex L n 0 0))
        (edgePairedSpace L n 0 0) (covDiff U) g) := by
  have := h.finite_vertices
  have hg' := adjointForm_mem h.orientation h.det_isUnit hg
  obtain ⟨hW₁, hW₂⟩ := transposeOfValues_spec h.transposes h.gauge_field_mem hg'
  obtain ⟨hU₁, hU₂⟩ := transposeOfValues_spec h.transposes h.field_mem hg
  refine eq_of_traceFinsumPairing_eq hW₁ (adjointVertexFn_mem h hU₁) fun c hc => ?_
  have hc' : ∀ x, adjointVertexFn (fun x => (v x)⁻¹) c x ∈ ComplexMatrix2.traceless := fun x =>
    conjugateBy_traceless (inv_det_isUnit h x) (hc x)
  have hcc : adjointVertexFn v (adjointVertexFn (fun x => (v x)⁻¹) c) = c := by
    funext x
    exact conjugateBy_conjugateBy_inv (h.det_isUnit x) (c x)
  generalize adjointVertexFn (fun x => (v x)⁻¹) c = c' at hc' hcc
  subst hcc
  refine (traceFinsumPairing_comm _ _).trans ((hW₂ _ (adjointVertexFn_mem h hc')).trans ?_)
  rw [h.covDiff_conj c' hc',
    h.edgePairing_conj _ hg _ (covDiff_mem h.transposes h.field_mem hc')]
  exact (hU₂ c' hc').symm.trans
    ((h.vertexPairing_conj _ _ hU₁ hc').symm.trans (traceFinsumPairing_comm _ _))
theorem gaugeLaplacian_conj (h : ConjugationData L n U v) {f : Vertex L n 0 0 → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) :
    gaugeLaplacian (PeriodicLattice.gaugeTransform v U) (adjointVertexFn v f) =
      adjointVertexFn v (gaugeLaplacian U f) := by
  unfold gaugeLaplacian
  rw [h.covDiff_conj f hf]
  exact transpose_conj h (covDiff_mem h.transposes h.field_mem hf)
theorem complexHessianOperator_conj (h : ConjugationData L n U v)
    {B : Edge L n 0 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n 0 0) :
    complexHessianOperator (PeriodicLattice.gaugeTransform v U) (adjointForm v B) =
      adjointForm v (complexHessianOperator U B) := by
  have := h.finite_edges
  have hB' := adjointForm_mem h.orientation h.det_isUnit hB
  have hOW : complexHessianOperator (PeriodicLattice.gaugeTransform v U) (adjointForm v B) ∈
      complexEdgeForms L n 0 0 := ((h.transposes _ h.gauge_field_mem).operator_mem _ hB').2.1
  have hOU : complexHessianOperator U B ∈ complexEdgeForms L n 0 0 :=
    ((h.transposes _ h.field_mem).operator_mem _ hB).2.1
  obtain ⟨-, -, -, -, hW, -⟩ := h.kernel _ h.gauge_field_mem
  obtain ⟨-, -, -, -, hU, -⟩ := h.kernel _ h.field_mem
  refine eq_of_edgeFormPairing_eq h.orientation hOW
    (adjointForm_mem h.orientation h.det_isUnit hOU) fun C hC => ?_
  have hC' := adjointForm_mem h.orientation (inv_det_isUnit h) hC
  have hCC := adjointForm_adjointForm_inv h.orientation h.det_isUnit hC
  generalize adjointForm (fun x => (v x)⁻¹) C = C' at hC' hCC
  subst hCC
  rw [hW _ hC _ hB', h.hessian_conj _ hC' _ hB, ← hU _ hC' _ hB,
    h.edgePairing_conj _ hC' _ hOU]
theorem massiveHessian_conj (h : ConjugationData L n U v) {B : Edge L n 0 0 → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) :
    massiveHessian (PeriodicLattice.gaugeTransform v U) (adjointForm v B) =
      adjointForm v (massiveHessian U B) := by
  have := h.finite_vertices
  unfold massiveHessian
  rw [adjointForm_add, complexHessianOperator_conj h hB, transpose_conj h hB,
    h.covDiff_conj _ (transposeOfValues_spec h.transposes h.field_mem hB).1]
end Operators
theorem mem_complexGaugeGroup_of_mem_compact {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : g ∈ PeriodicLattice.complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.1 hg).2
theorem claim_holds (hAlgebra : LeftChartAlgebra.AllConditionsHold)
    (hGauge : GaugeEquivarianceFormsAllSides)
    (hImage : GaugeAndSymmetryImages.statement)
    (hDeterminants : HessianDeterminants.HessianSymmAndDetsPositive)
    (hKernel : HessianKernel.KernelProperties)
    (hTransposes : CovDiffTransposes.Claim)
    (hOrientation : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction) :
    Claim := by
  intro L hL z hz n hn U hU v hv
  have hL₀ : 0 < L := by
    have := hL.2
    omega
  have hUc : U ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup :=
    ⟨fun b hb => mem_complexGaugeGroup_of_mem_compact (hU.1 b hb), hU.2⟩
  have hvc : PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup v := fun x =>
    mem_complexGaugeGroup_of_mem_compact (hv x)
  have hSites : Finite (Vertex L n 0 0) :=
    (ClusterExpansion.RegionPolymers.sublattice_finite hL₀ n
      (PeriodicLattice.levelDepth 0 0)).to_subtype
  have hBonds : Finite (PositiveEdge L n 0 0) :=
    Finite.of_injective (fun b : PositiveEdge L n 0 0 => (b.1.source, b.1.target)) fun _ _ h =>
      Subtype.ext (PeriodicLattice.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  have hOne : UniqueOrientation L n := fun b =>
    ((hOrientation ⟨L, hL, 1, ⟨n, hn⟩⟩ (PeriodicLattice.levelDepth 0 0)
      (by simpa [PeriodicLattice.levelDepth] using hn)).1 b).2.2.2.2.2
  obtain ⟨-, hPB, hPS, hOrth⟩ := (hGauge L 0 0 hL le_rfl).1 n hn v hvc
  obtain ⟨-, hGA, -, -, hDer, -⟩ := ((hAlgebra.2.2 L 0 0 hL le_rfl).1 n hn).1
  have hSetting : ConjugationData L n U v :=
    { finite_vertices := hSites
      finite_edges := hBonds
      orientation := hOne
      transposes := ((hTransposes L hL 0 0 le_rfl).1 n hn)
      kernel := ((hKernel L hL 0 0 le_rfl).1 n hn)
      field_mem := hUc
      gauge_field_mem := ((hImage L 0 0 hL le_rfl).1 n hn U v id hUc hvc (fun _ _ => rfl)
        (Set.image_id _)).1
      det_isUnit := fun x => by
        have hx : (v x).det = 1 := hvc x
        rw [hx]
        exact isUnit_one
      covDiff_conj := fun l hl => (hGA U v hUc hvc).1 l hl
      edgePairing_conj := hPB
      vertexPairing_conj := hPS
      hessian_conj := fun B hB B' hB' =>
        (hDer U v 0 B B' hUc hvc (fun _ => ComplexMatrix2.traceless.zero_mem) hB hB').2.1 }
  obtain ⟨hLap, hMas, -⟩ := ((hDeterminants L hL).2 z hz n hn).1 U hU
  obtain ⟨A₁, hA₁⟩ := hLap.1
  obtain ⟨A₂, hA₂⟩ := hMas.1
  obtain ⟨⟨eb, heb, -⟩, es, hes, -⟩ := hOrth hv
  have hSite : ∀ (f : vertexFunctionSpace L n 0 0) (x : Vertex L n 0 0),
      (f : Vertex L n 0 0 → ComplexMatrix2) x ∈ ComplexMatrix2.traceless :=
    fun f x => (f.2 x (Set.mem_univ x)).2
  have hForm : ∀ B : edgeFormSpace L n 0 0,
      (B : Edge L n 0 0 → ComplexMatrix2) ∈ complexEdgeForms L n 0 0 := fun B => by
    have hB : PeriodicLattice.IsBondForm PeriodicLattice.compactLieAlgebra
      (B : Edge L n 0 0 → ComplexMatrix2) := B.2
    exact mem_complexEdgeForms_iff.2 ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
  have h₁ : shiftedDetOn (vertexFunctionSpace L n 0 0)
      (gaugeLaplacian (PeriodicLattice.gaugeTransform v U)) z =
      shiftedDetOn (vertexFunctionSpace L n 0 0) (gaugeLaplacian U) z :=
    shiftedDetOn_conj z es A₁ hA₁ fun f => by
      rw [hes f, hes (A₁ f), hA₁ f]
      exact gaugeLaplacian_conj hSetting (hSite f)
  have h₂ : shiftedDetOn (edgeFormSpace L n 0 0)
      (massiveHessian (PeriodicLattice.gaugeTransform v U)) z =
      shiftedDetOn (edgeFormSpace L n 0 0) (massiveHessian U) z :=
    shiftedDetOn_conj z eb A₂ hA₂ fun B => by
      rw [heb B, heb (A₂ B), hA₂ B]
      exact massiveHessian_conj hSetting (hForm B)
  unfold massiveLogDetFunctional massiveLogDet
  rw [h₁, h₂]
end YangMills.Construction.Tower.MassiveFunctionals.GaugeInvariance
end
