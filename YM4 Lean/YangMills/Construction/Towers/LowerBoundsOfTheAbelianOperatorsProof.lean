import YangMills.Construction.LawInAState.ReflectionKernelAtADistanceProof
import YangMills.Construction.Towers.CommutatorTermAtAPeriodicExtensionDescendsProof
import YangMills.Construction.InfiniteLattice.FactsOfTheBondsConfigurationsAndMotionsAtOneSpacingProof
import YangMills.Construction.Towers.AbelianOperatorsAreLocalAndSelfAdjointProof
import YangMills.Construction.Towers.KernelsOfTheTwoOperatorsAreProductsProof
import YangMills.Construction.Towers.LogarithmsOfTheAbelianOperatorsProof
import YangMills.Construction.Towers.LowerBoundsOfTheAbelianOperators
import YangMills.Construction.Towers.QuadraticFormOfTheAbelianMassiveOperator
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.AbelianOperatorBounds
open Matrices AbelianFieldFacts UnitLatticeL2 AbelianFieldDensity
section RealVectors
variable {J : Type}
theorem inner_im_eq_zero_of_real (x y : lp (fun _ : J => ℂ) 2) (hx : ∀ ι, (x ι).im = 0)
    (hy : ∀ ι, (y ι).im = 0) : (inner ℂ x y : ℂ).im = 0 := by
  have h := Complex.imCLM.hasSum (lp.hasSum_inner x y)
  have h0 : (fun i => Complex.imCLM (inner ℂ (x i) (y i) : ℂ)) = fun _ => (0 : ℝ) := by
    funext i
    have h1 := hx i
    have h2 := hy i
    simp [RCLike.inner_apply, Complex.mul_im, h1, h2]
  rw [h0] at h
  simpa using h.unique hasSum_zero
theorem re_inner_add_I_smul_of_real (T : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2)
    (hT : IsSelfAdjointOp T)
    (hreal : ∀ v : lp (fun _ : J => ℂ) 2, (∀ ι, (v ι).im = 0) → ∀ ι, (T v ι).im = 0)
    (a b : lp (fun _ : J => ℂ) 2) (ha : ∀ ι, (a ι).im = 0) (hb : ∀ ι, (b ι).im = 0) :
    (inner ℂ (a + Complex.I • b) (T (a + Complex.I • b)) : ℂ).re =
      (inner ℂ a (T a) : ℂ).re + (inner ℂ b (T b) : ℂ).re := by
  have hsym : (inner ℂ a (T b) : ℂ) = conj (inner ℂ b (T a) : ℂ) := by
    have h1 : (inner ℂ a (T b) : ℂ) = inner ℂ (opAdjoint T a) b :=
      (ContinuousLinearMap.adjoint_inner_left T b a).symm
    rw [h1, hT, inner_conj_symm]
  have him : (inner ℂ b (T a) : ℂ).im = 0 := inner_im_eq_zero_of_real b (T a) hb (hreal a ha)
  have hzz : (inner ℂ a (T b) : ℂ) = inner ℂ b (T a) := by
    rw [hsym]; exact Complex.conj_eq_iff_im.mpr him
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hzz, Complex.conj_I]
  simp [Complex.add_re, Complex.mul_re]
  ring
theorem isBoundedBelowBy_of_real (T : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2)
    (hT : IsSelfAdjointOp T)
    (hreal : ∀ v : lp (fun _ : J => ℂ) 2, (∀ ι, (v ι).im = 0) → ∀ ι, (T v ι).im = 0) (c : ℝ)
    (hfin : ∀ v : lp (fun _ : J => ℂ) 2, (∀ ι, (v ι).im = 0) →
      (Function.support fun ι => v ι).Finite →
      c * (inner ℂ v v : ℂ).re ≤ (inner ℂ v (T v) : ℂ).re) : IsBoundedBelowBy T c := by
  classical
  have hid : IsSelfAdjointOp
      (ContinuousLinearMap.id ℂ (lp (fun _ : J => ℂ) 2)) := ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun _ _ => rfl).symm
  have hfin' : ∀ v : lp (fun _ : J => ℂ) 2, (Function.support fun ι => v ι).Finite →
      c * (inner ℂ v v : ℂ).re ≤ (inner ℂ v (T v) : ℂ).re := by
    intro v hv
    set a : lp (fun _ : J => ℂ) 2 := (1 / 2 : ℂ) • (v + star v) with ha_def
    set b : lp (fun _ : J => ℂ) 2 := (-(Complex.I / 2)) • (v - star v) with hb_def
    have hav : ∀ ι, a ι = ((v ι).re : ℂ) := by
      intro ι
      have h1 : a ι = (1 / 2 : ℂ) * (v ι + conj (v ι)) := rfl
      rw [h1, Complex.add_conj]
      push_cast
      ring
    have hbv : ∀ ι, b ι = ((v ι).im : ℂ) := by
      intro ι
      have h1 : b ι = (-(Complex.I / 2)) * (v ι - conj (v ι)) := rfl
      rw [h1, Complex.sub_conj]
      push_cast
      linear_combination (-((v ι).im : ℂ)) * Complex.I_sq
    have ha : ∀ ι, (a ι).im = 0 := fun ι => by rw [hav]; simp
    have hb : ∀ ι, (b ι).im = 0 := fun ι => by rw [hbv]; simp
    have hvab : v = a + Complex.I • b := by
      ext ι
      change v ι = a ι + Complex.I * b ι
      rw [hav, hbv, mul_comm]
      exact (Complex.re_add_im _).symm
    have hsa : (Function.support fun ι => a ι).Finite := by
      refine hv.subset fun ι hι h0 => hι ?_
      have h0' : v ι = 0 := h0
      simp [hav, h0']
    have hsb : (Function.support fun ι => b ι).Finite := by
      refine hv.subset fun ι hι h0 => hι ?_
      have h0' : v ι = 0 := h0
      simp [hbv, h0']
    have h1 := re_inner_add_I_smul_of_real T hT hreal a b ha hb
    have h2 := re_inner_add_I_smul_of_real _ hid (fun w hw => hw) a b ha hb
    simp only [ContinuousLinearMap.id_apply] at h2
    rw [hvab, h1, h2, mul_add]
    exact add_le_add (hfin a ha hsa) (hfin b hb hsb)
  have hall : ∀ ψ : lp (fun _ : J => ℂ) 2, 0 ≤ (inner ℂ ψ (T ψ) : ℂ).re - c * (inner ℂ ψ ψ : ℂ).re := by
    intro ψ
    have hsum := lp.hasSum_single (p := 2) (by norm_num) ψ
    have hcont : Continuous fun x : lp (fun _ : J => ℂ) 2 =>
        (inner ℂ x (T x) : ℂ).re - c * (inner ℂ x x : ℂ).re := by fun_prop
    refine ge_of_tendsto' ((hcont.tendsto ψ).comp hsum) fun s => ?_
    have hs := hfin' (∑ i ∈ s, lp.single 2 i (ψ i)) (by
      refine s.finite_toSet.subset fun ι hι => ?_
      by_contra hn
      apply hι
      rw [lp.coeFn_sum]
      change (∑ i ∈ s, ((lp.single 2 i (ψ i) : lp (fun _ : J => ℂ) 2) : J → ℂ)) ι = 0
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hne : ι ≠ i := fun h => hn (h ▸ hi)
      simp [lp.single_apply, Pi.single_eq_of_ne hne])
    exact sub_nonneg.mpr hs
  intro ψ
  have hsym : (inner ℂ ψ (T ψ) : ℂ).im = 0 := by
    have h1 : (inner ℂ ψ (T ψ) : ℂ) = inner ℂ (opAdjoint T ψ) ψ :=
      (ContinuousLinearMap.adjoint_inner_left T ψ ψ).symm
    rw [hT] at h1
    have h2 : (inner ℂ ψ (T ψ) : ℂ) = conj (inner ℂ ψ (T ψ) : ℂ) := by
      conv_rhs => rw [inner_conj_symm]
      exact h1
    exact Complex.conj_eq_iff_im.mp h2.symm
  have hself : (inner ℂ ψ ψ : ℂ).im = 0 := Complex.conj_eq_iff_im.mp (inner_conj_symm ψ ψ)
  refine ⟨?_, ?_⟩
  · rw [Complex.sub_im, Complex.mul_im, hsym, hself]
    simp
  · have := hall ψ
    simpa [Complex.sub_re, Complex.mul_re, hself] using this
end RealVectors
section Coordinates
variable {σ : Type}
theorem sum_norm_sq_le_re_inner {J : Type} (s : Finset J) (v : lp (fun _ : J => ℂ) 2) :
    ∑ ι ∈ s, ‖v ι‖ ^ 2 ≤ (inner ℂ v v : ℂ).re := by
  have h := Complex.reCLM.hasSum (lp.hasSum_inner v v)
  have h0 : (fun i => Complex.reCLM (inner ℂ (v i) (v i) : ℂ)) = fun i => ‖v i‖ ^ 2 := by
    funext i
    simp [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h0] at h
  exact sum_le_hasSum s (fun _ _ => by positivity) h
theorem fieldStar_ofCoords (v : Fin 3 × σ → ℂ) :
    fieldStar (ofCoords v) = ofCoords fun ι => conj (v ι) := by
  funext s
  simp only [fieldStar, ofCoords, ComplexMatrix2.sum_smul_pauliFamily]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring
theorem adjointMatrix_ofCoords (v : Fin 3 × σ → ℂ) (hv : ∀ ι, (v ι).im = 0) (s : σ) :
    ComplexMatrix2.adjointMatrix (ofCoords v s) = ofCoords v s := by
  have h := congrFun (fieldStar_ofCoords v) s
  have h' : (fun ι => conj (v ι)) = v := by
    funext ι
    exact Complex.conj_eq_iff_im.mpr (hv ι)
  rw [h'] at h
  exact h
theorem coords_im_eq_zero_of_fieldStar (hco : CoordsIsometry σ) (w : L2Field σ)
    (hw : fieldStar (ofCoords w) = ofCoords w) (ι : Fin 3 × σ) :
    (w ι).im = 0 := by
  have h1 := (hco.2.2.1 w).2 ι
  have h2 := (hco.2.2.1 (star w)).2 ι
  have h3 : ofCoords ((star w : L2Field σ) : Fin 3 × σ → ℂ) =
      ofCoords w := by
    rw [← hw, fieldStar_ofCoords]
    rfl
  rw [h3, h1] at h2
  have h4 : w ι = conj (w ι) := h2
  exact Complex.conj_eq_iff_im.mp h4.symm
theorem hermitianInner_eq_traceFinsumPairing (f g : σ → ComplexMatrix2)
    (hf : ∀ s, ComplexMatrix2.adjointMatrix (f s) = f s)
    (hs : (Function.support f).Finite) : hermitianInner f g = traceFinsumPairing f g := by
  have h : (fun s => halfTraceProduct (f s) (g s)) = fun s => ComplexMatrix2.halfTrace (f s * g s) := by
    funext s
    simp only [halfTraceProduct, hf]
  have hsup : (Function.support fun s => ComplexMatrix2.halfTrace (f s * g s)).Finite := by
    refine hs.subset fun s hs' h0 => hs' ?_
    have h0' : f s = 0 := h0
    simp [h0']
  simp only [hermitianInner, traceFinsumPairing, h]
  exact tsum_eq_finsum hsup
theorem ofCoords_support_finite (v : Fin 3 × σ → ℂ)
    (hv : (Function.support v).Finite) :
    (Function.support (ofCoords v)).Finite := by apply _root_.YangMills.DeltaSharedProofs.p502039 <;> assumption
end Coordinates
theorem halfTrace_mul_self_re_nonneg (X : ComplexMatrix2) (hX : ComplexMatrix2.adjointMatrix X = X) :
    0 ≤ (ComplexMatrix2.halfTrace (X * X)).re := by
  have h : X * X = X * ComplexMatrix2.adjointMatrix X := by rw [hX]
  rw [h]
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, ComplexMatrix2.adjointMatrix,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  simp [Complex.mul_re]
  nlinarith [mul_self_nonneg (X 0 0).re, mul_self_nonneg (X 0 0).im, mul_self_nonneg (X 0 1).re,
    mul_self_nonneg (X 0 1).im, mul_self_nonneg (X 1 0).re, mul_self_nonneg (X 1 0).im,
    mul_self_nonneg (X 1 1).re, mul_self_nonneg (X 1 1).im]
theorem two_halfTrace_sum_mul_loweringPauli (x : Fin 3 → ℂ) :
    2 * ComplexMatrix2.halfTrace ((∑ a, x a • ComplexMatrix2.pauliFamily a) * loweringPauli) =
      x 0 - Complex.I * x 1 := by
  rw [ComplexMatrix2.sum_smul_pauliFamily]
  simp only [loweringPauli, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, ComplexMatrix2.pauliFamily_apply.1,
    ComplexMatrix2.pauliFamily_apply.2.1]
  simp
  ring_nf
section Lattice
theorem axisStep_ne_zero {a : ℝ} (ha : 0 < a) (μ : Fin 4) : InfiniteLattice.axisStep a μ ≠ 0 := by apply _root_.YangMills.Construction.InfiniteLattice.OneSpacing.axisStep_ne_zero <;> assumption
theorem not_isPositivelyOriented_opposite {a : ℝ} (ha : 0 < a) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
theorem isPositivelyOriented_opposite_of_not {a : ℝ} {b : InfiniteLattice.Link a}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem opposite_opposite {a : ℝ} (b : InfiniteLattice.Link a) : b.opposite.opposite = b := rfl
theorem forwardFrom_injective {a : ℝ} (ha : 0 < a) {x y : InfiniteLattice.LatticePoint a} {μ ν : Fin 4}
    (h : InfiniteLattice.Link.forwardFrom x μ = InfiniteLattice.Link.forwardFrom y ν) :
    x = y ∧ μ = ν := by apply _root_.YangMills.Construction.InfiniteLattice.OneSpacing.forwardFrom_inj <;> assumption
theorem facePositiveEdge_injective {a : ℝ} (ha : 0 < a) (p : InfiniteLattice.ElementaryPlaquette a) :
    Function.Injective (facePositiveEdge p) := by
  have hne : p.lowAxis ≠ p.highAxis := p.lowAxis_lt_highAxis.ne
  have key : ∀ {x y : InfiniteLattice.LatticePoint a} {μ ν : Fin 4},
      FullSpace.forwardEdge x μ = FullSpace.forwardEdge y ν → x = y ∧ μ = ν := fun h =>
    forwardFrom_injective ha (congrArg Subtype.val h)
  have hs1 : p.corner + InfiniteLattice.axisStep a p.lowAxis ≠ p.corner := fun h =>
    axisStep_ne_zero ha _ (by simpa using h)
  have hs2 : p.corner + InfiniteLattice.axisStep a p.highAxis ≠ p.corner := fun h =>
    axisStep_ne_zero ha _ (by simpa using h)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exfalso
       simp only [facePositiveEdge, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
         at hij
       have h := key hij
       first
         | exact hne h.2
         | exact hne h.2.symm
         | exact hs1 h.1
         | exact hs1 h.1.symm
         | exact hs2 h.1
         | exact hs2 h.1.symm)
theorem norm_faceNumbers {a : ℝ} (θ : FullSpace.PositiveEdge a → ℝ)
    (w : FullSpace.PositiveEdge a → ℂ) (p : InfiniteLattice.ElementaryPlaquette a) (i : Fin 4) :
    ‖FullSpace.faceNumbers θ w p i‖ = ‖w (facePositiveEdge p i)‖ := by
  have hE : ∀ r : ℝ, ‖Complex.exp (2 * Complex.I * (r : ℂ))‖ = 1 := fun r => by
    rw [Complex.norm_exp]
    simp
  fin_cases i <;>
    simp [FullSpace.faceNumbers, facePositiveEdge, FullSpace.chargedShift, FullSpace.edgeComponent,
      hE]
end Lattice
section Forms
variable {L : ℕ}
theorem meshAt_zero_pos (L : ℕ) : 0 < meshAt L 0 0 := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.meshAt_zero_pos <;> assumption
theorem formOfPositiveValues_of_pos (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (b : PeriodicOperators.PosEdge L 0 0) : formOfPositiveValues g b.1 = g b := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.formOfPositiveValues_apply <;> assumption
theorem formOfPositiveValues_opposite (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (b : FullSpace.Edge L 0 0) : formOfPositiveValues g b.opposite = -formOfPositiveValues g b := by
  classical
  by_cases hb : b.IsPositivelyOriented
  · have h := not_isPositivelyOriented_opposite (meshAt_zero_pos L) hb
    simp [formOfPositiveValues, FullSpace.extendOddly, hb, h, opposite_opposite]
  · have h := isPositivelyOriented_opposite_of_not hb
    simp [formOfPositiveValues, FullSpace.extendOddly, hb, h, opposite_opposite]
theorem fieldStar_formOfPositiveValues (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (hg : ∀ b, ComplexMatrix2.adjointMatrix (g b) = g b) :
    fieldStar (formOfPositiveValues g) = formOfPositiveValues g := by apply _root_.YangMills.Construction.Tower.AbelianOperatorsLocalSelfAdjointProof.fieldStar_formOfPositiveValues <;> assumption
theorem restrict_formOfPositiveValues (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2) :
    FullSpace.restrictToPositiveEdges (formOfPositiveValues g) = g :=
  funext (formOfPositiveValues_of_pos g)
theorem formOfPositiveValues_mem_l2Forms (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (hg : IsL2Traceless g) :
    formOfPositiveValues g ∈ FullSpace.l2Forms (meshAt L 0 0) := by
  refine ⟨⟨fun b hb => ?_, formOfPositiveValues_opposite g⟩, ?_⟩
  · have h : formOfPositiveValues g b = g ⟨b, hb⟩ := formOfPositiveValues_of_pos g ⟨b, hb⟩
    rw [h]
    exact hg.1 _
  · rw [restrict_formOfPositiveValues]
    exact hg
theorem formOfPositiveValues_mem_edgeFormSpace (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (hg : IsL2Traceless g) (hh : ∀ b, ComplexMatrix2.adjointMatrix (g b) = g b) :
    formOfPositiveValues g ∈ FullSpace.edgeFormSpace (meshAt L 0 0) := by
  refine ⟨fun b hb => ?_, formOfPositiveValues_opposite g⟩
  have h : formOfPositiveValues g b = g ⟨b, hb⟩ := formOfPositiveValues_of_pos g ⟨b, hb⟩
  rw [h]
  exact ⟨(hh _).symm, hg.1 _⟩
theorem formOfPositiveValues_hasFiniteEdgeSupport (g : PeriodicOperators.PosEdge L 0 0 → ComplexMatrix2)
    (hs : (Function.support g).Finite) :
    FullSpace.HasFiniteEdgeSupport (formOfPositiveValues g) := by
  refine (hs.image Subtype.val).subset fun b hb => ⟨⟨b, hb.1⟩, ?_, rfl⟩
  have h : formOfPositiveValues g b = g ⟨b, hb.1⟩ := formOfPositiveValues_of_pos g ⟨b, hb.1⟩
  have h2 := hb.2
  rw [h] at h2
  exact h2
end Forms
section Keeps
variable {L : ℕ} {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
theorem massiveOp_im_eq_zero (hops : AbelianOperators θ) (hsym : ChargeSymmetries θ)
    (hco : CoordsIsometry (PeriodicOperators.PosEdge L 0 0))
    (v : L2Field (PeriodicOperators.PosEdge L 0 0))
    (hv : ∀ ι, (v ι).im = 0) (ι : EdgeIndex L) :
    (AbelianFieldDensity.massiveOp θ v ι).im = 0 := by
  have hc := hco.2.2.1 v
  have hg := adjointMatrix_ofCoords v hv
  have hB := formOfPositiveValues_mem_l2Forms _ hc.1
  have h1 := hsym.hessian_star _ hB
  rw [fieldStar_formOfPositiveValues _ hg] at h1
  refine coords_im_eq_zero_of_fieldStar hco _ ?_ ι
  rw [hops.hessian_apply v]
  funext b
  exact (congrFun h1 b.1).symm
theorem laplacianOp_im_eq_zero (hops : AbelianOperators θ) (hsym : ChargeSymmetries θ)
    (hco : CoordsIsometry (FullSpace.Vertex L 0 0))
    (v : L2Field (FullSpace.Vertex L 0 0))
    (hv : ∀ ι, (v ι).im = 0) (ι : VertexIndex L) :
    (laplacianOp θ v ι).im = 0 := by
  have hc := hco.2.2.1 v
  have hg := adjointMatrix_ofCoords v hv
  have h0 : fieldStar (ofCoords v) = ofCoords v := funext hg
  have h1 := hsym.laplacian_star _ hc.1
  rw [h0] at h1
  refine coords_im_eq_zero_of_fieldStar hco _ ?_ ι
  rw [hops.laplacian_apply v]
  exact h1.symm
end Keeps
section Plaquettes
theorem sum_faces_le_six_mul {a : ℝ} (ha : 0 < a) (g : FullSpace.PositiveEdge a → ℝ) (hg : ∀ b, 0 ≤ g b)
    (hsix : ∀ b : FullSpace.PositiveEdge a,
      {p : InfiniteLattice.ElementaryPlaquette a |
        (b : InfiniteLattice.Link a) ∈ FullSpace.faceEdges p}.encard ≤ 6)
    (F : Finset (InfiniteLattice.ElementaryPlaquette a)) :
    ∃ I : Finset (FullSpace.PositiveEdge a),
      ∑ p ∈ F, ∑ i, g (facePositiveEdge p i) ≤ 6 * ∑ b ∈ I, g b := by
  classical
  refine ⟨(F ×ˢ (Finset.univ : Finset (Fin 4))).image fun q => facePositiveEdge q.1 q.2, ?_⟩
  rw [← Finset.sum_product' (f := fun p i => g (facePositiveEdge p i)),
    Finset.sum_comp g (fun q : InfiniteLattice.ElementaryPlaquette a × Fin 4 =>
      facePositiveEdge q.1 q.2), Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hg b)
  set T := (F ×ˢ (Finset.univ : Finset (Fin 4))).filter
    fun q => facePositiveEdge q.1 q.2 = b with hT
  have hinj : Set.InjOn Prod.fst (T : Set (InfiniteLattice.ElementaryPlaquette a × Fin 4)) := by
    rintro ⟨p, i⟩ hq ⟨p', j⟩ hq' hpp
    have hpp' : p = p' := hpp
    subst hpp'
    have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hq')).2
    have hij : i = j := facePositiveEdge_injective ha p (h1.trans h2.symm)
    rw [hij]
  have hsub : ((T.image Prod.fst : Finset (InfiniteLattice.ElementaryPlaquette a)) :
      Set (InfiniteLattice.ElementaryPlaquette a)) ⊆
      {p : InfiniteLattice.ElementaryPlaquette a |
        (b : InfiniteLattice.Link a) ∈ FullSpace.faceEdges p} := by
    intro p hp
    obtain ⟨⟨p', i⟩, hq, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
    have h1 := (Finset.mem_filter.mp hq).2
    change (b : InfiniteLattice.Link a) ∈ FullSpace.faceEdges p'
    rw [← h1, facePositiveEdge_val]
    exact List.getElem_mem _
  have hcard := (Set.encard_le_encard hsub).trans (hsix b)
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injOn hinj] at hcard
  exact_mod_cast hcard
theorem sum_lt_pairs_fin_four (F : Fin 4 × Fin 4 → ℝ) :
    ∑ c ∈ Finset.univ.filter (fun c : Fin 4 × Fin 4 => c.1 < c.2), F c =
      F (0, 1) + F (0, 2) + F (0, 3) + F (1, 2) + F (1, 3) + F (2, 3) := by apply _root_.YangMills.DeltaSharedProofs.p501473 <;> assumption
variable {L : ℕ}
theorem faceTerm_ge (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (B : FullSpace.Edge L 0 0 → ComplexMatrix2) (p : FullSpace.Face L 0 0)
    (hcos : 0 ≤ Real.cos (FullSpace.faceAngle θ p)) {s : ℝ}
    (hs : |Real.sin (FullSpace.faceAngle θ p)| ≤ s) :
    -(3 * s) * ∑ i, ‖FullSpace.offDiagonalComponent B (facePositiveEdge p i)‖ ^ 2 ≤
      faceTerm θ B p := by
  have hny := norm_faceNumbers θ (FullSpace.offDiagonalComponent B) p
  have hs0 : 0 ≤ s := (abs_nonneg _).trans hs
  unfold faceTerm
  rw [sum_lt_pairs_fin_four]
  set y := FullSpace.faceNumbers θ (FullSpace.offDiagonalComponent B) p with hy
  have hI : ∀ i j, |(y i * conj (y j)).im| ≤ ‖y i‖ * ‖y j‖ := fun i j => by
    refine (Complex.abs_im_le_norm _).trans ?_
    simp
  simp only [← hny]
  rw [Fin.sum_univ_four]
  set n0 := ‖y 0‖
  set n1 := ‖y 1‖
  set n2 := ‖y 2‖
  set n3 := ‖y 3‖
  set T := (y 0 * conj (y 1)).im + (y 0 * conj (y 2)).im + (y 0 * conj (y 3)).im +
    (y 1 * conj (y 2)).im + (y 1 * conj (y 3)).im + (y 2 * conj (y 3)).im with hT
  have hTabs : |T| ≤ 3 / 2 * (n0 ^ 2 + n1 ^ 2 + n2 ^ 2 + n3 ^ 2) := by
    have h01 := hI 0 1
    have h02 := hI 0 2
    have h03 := hI 0 3
    have h12 := hI 1 2
    have h13 := hI 1 3
    have h23 := hI 2 3
    have e1 := abs_add_le ((y 0 * conj (y 1)).im) ((y 0 * conj (y 2)).im)
    have e2 := abs_add_le ((y 0 * conj (y 1)).im + (y 0 * conj (y 2)).im) ((y 0 * conj (y 3)).im)
    have e3 := abs_add_le ((y 0 * conj (y 1)).im + (y 0 * conj (y 2)).im + (y 0 * conj (y 3)).im)
      ((y 1 * conj (y 2)).im)
    have e4 := abs_add_le ((y 0 * conj (y 1)).im + (y 0 * conj (y 2)).im + (y 0 * conj (y 3)).im +
      (y 1 * conj (y 2)).im) ((y 1 * conj (y 3)).im)
    have e5 := abs_add_le ((y 0 * conj (y 1)).im + (y 0 * conj (y 2)).im + (y 0 * conj (y 3)).im +
      (y 1 * conj (y 2)).im + (y 1 * conj (y 3)).im) ((y 2 * conj (y 3)).im)
    nlinarith [sq_nonneg (n0 - n1), sq_nonneg (n0 - n2), sq_nonneg (n0 - n3), sq_nonneg (n1 - n2),
      sq_nonneg (n1 - n3), sq_nonneg (n2 - n3)]
  have hST : Real.sin (FullSpace.faceAngle θ p) * T ≤
      s * (3 / 2 * (n0 ^ 2 + n1 ^ 2 + n2 ^ 2 + n3 ^ 2)) := by
    calc Real.sin (FullSpace.faceAngle θ p) * T
        ≤ |Real.sin (FullSpace.faceAngle θ p) * T| := le_abs_self _
      _ = |Real.sin (FullSpace.faceAngle θ p)| * |T| := abs_mul _ _
      _ ≤ s * (3 / 2 * (n0 ^ 2 + n1 ^ 2 + n2 ^ 2 + n3 ^ 2)) :=
        mul_le_mul hs hTabs (abs_nonneg _) hs0
  have hC : 0 ≤ Real.cos (FullSpace.faceAngle θ p) *
      (FullSpace.edgeDifference (FullSpace.diagonalComponent B) p ^ 2 + ‖∑ i, y i‖ ^ 2) :=
    mul_nonneg hcos (by positivity)
  nlinarith
end Plaquettes
theorem adjointMatrix_conjugateBy (V X : ComplexMatrix2) (hV : V ∈ ComplexMatrix2.specialUnitary)
    (hX : ComplexMatrix2.adjointMatrix X = X) :
    ComplexMatrix2.adjointMatrix (ComplexMatrix2.conjugateBy V X) = ComplexMatrix2.conjugateBy V X := by
  have h1 : V⁻¹ = star V :=
    Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp hV).1)
  have hX' : X.conjTranspose = X := hX
  simp [ComplexMatrix2.conjugateBy, ComplexMatrix2.adjointMatrix, h1, Matrix.conjTranspose_mul,
    Matrix.star_eq_conjTranspose, hX', mul_assoc]
section Bounds
variable {L : ℕ} {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
theorem norm_offDiagonal_sq_le
    (v : L2Field (PeriodicOperators.PosEdge L 0 0))
    (hv : ∀ ι, (v ι).im = 0) (b : PeriodicOperators.PosEdge L 0 0) :
    ‖FullSpace.offDiagonalComponent (formOfPositiveValues (ofCoords v)) b‖ ^ 2 ≤
      ∑ a : Fin 3, ‖v (a, b)‖ ^ 2 := by
  have h1 : FullSpace.offDiagonalComponent (formOfPositiveValues (ofCoords v)) b =
      v (0, b) - Complex.I * v (1, b) := by
    simp only [FullSpace.offDiagonalComponent, formOfPositiveValues_of_pos]
    exact two_halfTrace_sum_mul_loweringPauli fun a => v (a, b)
  have h0 : (v (0, b)) = ((v (0, b)).re : ℂ) := Complex.ext rfl (by simp [hv])
  have h1' : (v (1, b)) = ((v (1, b)).re : ℂ) := Complex.ext rfl (by simp [hv])
  rw [h1, Fin.sum_univ_three, h0, h1']
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp
  nlinarith [mul_self_nonneg (v (2, b)).re, mul_self_nonneg (v (2, b)).im]
theorem massiveOp_lower_bound (hquad : HessianQuadraticForm θ) (hops : AbelianOperators θ)
    (hco : CoordsIsometry (PeriodicOperators.PosEdge L 0 0))
    (hsix : ∀ b : FullSpace.PositiveEdge (meshAt L 0 0),
      {p : InfiniteLattice.ElementaryPlaquette (meshAt L 0 0) |
        (b : InfiniteLattice.Link (meshAt L 0 0)) ∈ FullSpace.faceEdges p}.encard ≤ 6)
    (hf : ∀ p : FullSpace.Face L 0 0, |FullSpace.faceAngle θ p| ≤ Real.pi / 2)
    (v : L2Field (PeriodicOperators.PosEdge L 0 0))
    (hv : ∀ ι, (v ι).im = 0) (hs : (Function.support fun ι => v ι).Finite) :
    (-24 * ⨆ p : FullSpace.Face L 0 0, |Real.sin (FullSpace.faceAngle θ p)|) *
        (inner ℂ v v : ℂ).re ≤ (inner ℂ v (AbelianFieldDensity.massiveOp θ v) : ℂ).re := by
  classical
  set s := ⨆ p : FullSpace.Face L 0 0, |Real.sin (FullSpace.faceAngle θ p)| with hsdef
  have hs0 : 0 ≤ s := Real.iSup_nonneg fun _ => abs_nonneg _
  have hbdd : BddAbove (Set.range fun p : FullSpace.Face L 0 0 =>
      |Real.sin (FullSpace.faceAngle θ p)|) :=
    ⟨1, by rintro _ ⟨p, rfl⟩; exact Real.abs_sin_le_one _⟩
  have hc := hco.2.2.1 v
  have hh := adjointMatrix_ofCoords v hv
  have hgs := ofCoords_support_finite v hs
  set g := ofCoords (v : Fin 3 × PeriodicOperators.PosEdge L 0 0 → ℂ) with hgdef
  set B := formOfPositiveValues g with hBdef
  have hBf : B ∈ FullSpace.edgeFormSpace (meshAt L 0 0) :=
    formOfPositiveValues_mem_edgeFormSpace g hc.1 hh
  have hBs : FullSpace.HasFiniteEdgeSupport B := formOfPositiveValues_hasFiniteEdgeSupport g hgs
  obtain ⟨-, hp, -, hpair⟩ := hquad B hBf hBs
  have hinner : (inner ℂ v (AbelianFieldDensity.massiveOp θ v) : ℂ) =
      FullSpace.finiteEdgePairing B (FullSpace.abelianMassiveHessian θ B) := by
    rw [← hco.2.2.2.2.2 v (AbelianFieldDensity.massiveOp θ v), hops.hessian_apply v,
      hermitianInner_eq_traceFinsumPairing _ _ hh hgs]
    simp only [FullSpace.finiteEdgePairing, hBdef, restrict_formOfPositiveValues]
    rfl
  rw [hinner, hpair, Complex.ofReal_re]
  have hsite : 0 ≤ ∑ᶠ x, vertexTerm θ B x := finsum_nonneg fun x => by
    unfold vertexTerm
    positivity
  have hN : 0 ≤ (inner ℂ v v : ℂ).re := by simpa using sum_norm_sq_le_re_inner ∅ v
  set w := FullSpace.offDiagonalComponent B with hw
  obtain ⟨I, hI⟩ := sum_faces_le_six_mul (meshAt_zero_pos L) (fun b => ‖w b‖ ^ 2)
    (fun _ => by positivity) hsix hp.toFinset
  have hterm : ∑ b ∈ I, ‖w b‖ ^ 2 ≤ (inner ℂ v v : ℂ).re := by
    calc ∑ b ∈ I, ‖w b‖ ^ 2 ≤ ∑ b ∈ I, ∑ a : Fin 3, ‖v (a, b)‖ ^ 2 :=
          Finset.sum_le_sum fun b _ => norm_offDiagonal_sq_le v hv b
      _ = ∑ ι ∈ (Finset.univ : Finset (Fin 3)) ×ˢ I, ‖v ι‖ ^ 2 := by
          rw [Finset.sum_comm, Finset.sum_product]
      _ ≤ (inner ℂ v v : ℂ).re := sum_norm_sq_le_re_inner _ v
  have hplaq : -(3 * s) * ∑ p ∈ hp.toFinset, ∑ i, ‖w (facePositiveEdge p i)‖ ^ 2 ≤
      ∑ᶠ p, faceTerm θ B p := by
    rw [finsum_eq_sum_of_support_subset _ (s := hp.toFinset) (by simp), Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => faceTerm_ge θ B p ?_ (le_ciSup hbdd p)
    have h := abs_le.mp (hf p)
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [h.1]) h.2
  have hsN : 0 ≤ s * (inner ℂ v v : ℂ).re := mul_nonneg hs0 hN
  have hchain : -(3 * s) * (6 * (inner ℂ v v : ℂ).re) ≤
      -(3 * s) * ∑ p ∈ hp.toFinset, ∑ i, ‖w (facePositiveEdge p i)‖ ^ 2 := by
    refine mul_le_mul_of_nonpos_left (hI.trans ?_) (by linarith)
    linarith
  nlinarith
theorem laplacianOp_nonneg (hops : AbelianOperators θ)
    (hco : CoordsIsometry (FullSpace.Vertex L 0 0))
    (hconf : FullSpace.abelianLinkField θ ∈ FullSpace.fieldSpace L 0 0)
    (hD : UnitGaugeDirections.CovDiffAndAdjoint (FullSpace.abelianLinkField θ))
    (v : L2Field (FullSpace.Vertex L 0 0))
    (hv : ∀ ι, (v ι).im = 0) (hs : (Function.support fun ι => v ι).Finite) :
    (0 : ℝ) * (inner ℂ v v : ℂ).re ≤ (inner ℂ v (laplacianOp θ v) : ℂ).re := by
  classical
  rw [zero_mul]
  obtain ⟨-, hmap, hfs, htr, hval⟩ := hD
  have hc := hco.2.2.1 v
  have hh := adjointMatrix_ofCoords v hv
  have hgs := ofCoords_support_finite v hs
  set g := ofCoords (v : Fin 3 × FullSpace.Vertex L 0 0 → ℂ) with hgdef
  have hgmem : g ∈ (UnitGaugeDirections.unitVertexSpace L).complexSubmodule :=
    fun x _ => hc.1.1 x
  set l : (UnitGaugeDirections.unitVertexSpace L).complexSubmodule := ⟨g, hgmem⟩ with hl
  set Dm := UnitGaugeDirections.covDiffLinear (FullSpace.abelianLinkField θ) with hDm
  have hDl : (Dm l).1 = FullSpace.covDiff (FullSpace.abelianLinkField θ) g := hmap l
  have hDf : HasFiniteSupp (FullSpace.restrictToPositiveEdges (Dm l).1) := hfs l hgs
  have htrans : traceFinsumPairing (PairedFunctionSpace.transposeMap Dm (Dm l)).1 g =
      FullSpace.finiteEdgePairing (Dm l).1 (Dm l).1 := htr (Dm l) l hgs
  have hlap : FullSpace.abelianGaugeLaplacian θ g = (PairedFunctionSpace.transposeMap Dm (Dm l)).1 := by
    change FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ)
      (FullSpace.covDiff (FullSpace.abelianLinkField θ) g) = _
    rw [← hDl]
    exact hval (Dm l)
  have hinner : (inner ℂ v (laplacianOp θ v) : ℂ) =
      FullSpace.finiteEdgePairing (Dm l).1 (Dm l).1 := by
    rw [← hco.2.2.2.2.2 v (laplacianOp θ v), hops.laplacian_apply v,
      hermitianInner_eq_traceFinsumPairing _ _ hh hgs, hlap, ← htrans]
    simp only [traceFinsumPairing, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
    exact finsum_congr fun x => by rw [Matrix.trace_mul_comm]
  rw [hinner]
  have hherm : ∀ b : FullSpace.PositiveEdge (meshAt L 0 0),
      ComplexMatrix2.adjointMatrix (FullSpace.restrictToPositiveEdges (Dm l).1 b) =
        FullSpace.restrictToPositiveEdges (Dm l).1 b := by
    intro b
    have h1 : FullSpace.restrictToPositiveEdges (Dm l).1 b =
        ComplexMatrix2.conjugateBy (FullSpace.abelianLinkField θ b.1) (g b.1.terminal) - g b.1.initial := by
      simp only [FullSpace.restrictToPositiveEdges, hDl, FullSpace.covDiff, FullSpace.extendOddly, b.2,
        if_true]
    rw [h1]
    simp only [ComplexMatrix2.adjointMatrix, Matrix.conjTranspose_sub]
    rw [show (ComplexMatrix2.conjugateBy (FullSpace.abelianLinkField θ b.1) (g b.1.terminal)).conjTranspose = _ from
      adjointMatrix_conjugateBy _ _ (hconf.1 b.1) (hh _), show (g b.1.initial).conjTranspose = _ from hh _]
  simp only [FullSpace.finiteEdgePairing, traceFinsumPairing]
  have hsup : (Function.support fun b => ComplexMatrix2.halfTrace
      (FullSpace.restrictToPositiveEdges (Dm l).1 b * FullSpace.restrictToPositiveEdges (Dm l).1 b)).Finite := by
    refine hDf.subset fun b hb h0 => hb ?_
    have h0' : FullSpace.restrictToPositiveEdges (Dm l).1 b = 0 := h0
    simp [h0']
  rw [finsum_eq_sum_of_support_subset _ (s := hsup.toFinset) (by simp), Complex.re_sum]
  exact Finset.sum_nonneg fun b _ => halfTrace_mul_self_re_nonneg _ (hherm b)
end Bounds
theorem lowerBoundsHold_of_facts (hOperators : AbelianOperatorsLocalSelfAdjoint)
    (hForm : MassiveOperatorQuadraticForm)
    (hSymmetries : AbelianOperatorSymmetries)
    (hPlaquettes : AbelianFieldPlaquettes.Claim)
    (hSix : FacesContainingEdge.Holds)
    (hSpaces : UnitLatticeL2Statement)
    (hGauge : UnitGaugeDirections.Claim) : LowerBoundsHold := by
  intro L hL θ
  have hops := hOperators L hL θ
  have hsym := hSymmetries L hL θ
  have hconf := (hPlaquettes L hL θ).abelianLinkField_mem
  have hsix := ((hSix L hL 0 0 le_rfl).2).2.1
  have hcoS := ((hSpaces.2 L).2.1).1
  have hcoB := ((hSpaces.2 L).2.2).1
  refine ⟨fun hf => ?_, ?_⟩
  · exact isBoundedBelowBy_of_real _ hops.hessian_isSelfAdjoint (massiveOp_im_eq_zero hops hsym hcoB) _
      (massiveOp_lower_bound (hForm L hL θ) hops hcoB hsix hf)
  · have hconfc : FullSpace.abelianLinkField θ ∈
        FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup :=
      ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.mp (hconf.1 b)).2, hconf.2⟩
    have hD := ((hGauge L hL).2 _ hconfc).1
    exact isBoundedBelowBy_of_real _ hops.laplacian_isSelfAdjoint (laplacianOp_im_eq_zero hops hsym hcoS) _
      (laplacianOp_nonneg hops hcoS hconf hD)
end YangMills.Construction.Tower.AbelianOperatorBounds
end
