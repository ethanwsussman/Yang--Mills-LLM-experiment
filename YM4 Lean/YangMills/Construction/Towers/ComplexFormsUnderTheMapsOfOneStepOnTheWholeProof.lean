import YangMills.Construction.Towers.ComplexFormsUnderTheMapsOfOneStepOnTheWhole
import YangMills.Construction.Towers.LinearMapsOfTheWholeLatticeAreOnto
import YangMills.Construction.Towers.LinearMapsOnConstantFormsOfTheWholeLattice
import YangMills.Construction.Towers.RelationAndBoundsOfTheIteratesOnTheWholeLatticeProof
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.OneStepComplexForms
def hermitianComponent (X : ComplexMatrix2) : ComplexMatrix2 := (2⁻¹ : ℂ) • (X + X.conjTranspose)
def imaginaryComponent (X : ComplexMatrix2) : ComplexMatrix2 :=
  (-(Complex.I / 2)) • (X - X.conjTranspose)
theorem hermitianComponent_add_I_smul_imaginaryComponent (X : ComplexMatrix2) :
    hermitianComponent X + Complex.I • imaginaryComponent X = X := by
  unfold hermitianComponent imaginaryComponent
  rw [smul_smul]
  have e : Complex.I * -(Complex.I / 2) = (2⁻¹ : ℂ) := by
    have := Complex.I_mul_I
    linear_combination (-(1 : ℂ) / 2) * this
  rw [e, ← smul_add]
  have e2 : X + X.conjTranspose + (X - X.conjTranspose) = (2 : ℂ) • X := by
    rw [two_smul]; abel
  rw [e2, smul_smul]
  norm_num
theorem hermitianComponent_mem_hermitianTraceless {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.traceless) :
    hermitianComponent X ∈ ComplexMatrix2.hermitianTraceless := by
  have ht : Matrix.trace X = 0 := h
  refine ⟨?_, ?_⟩
  · unfold hermitianComponent
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      add_comm X]
    simp
  · show Matrix.trace (hermitianComponent X) = 0
    unfold hermitianComponent
    rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_conjTranspose, ht]
    simp
theorem imaginaryComponent_mem_hermitianTraceless {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.traceless) :
    imaginaryComponent X ∈ ComplexMatrix2.hermitianTraceless := by
  have ht : Matrix.trace X = 0 := h
  refine ⟨?_, ?_⟩
  · unfold imaginaryComponent
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    have e : X.conjTranspose - X = -(X - X.conjTranspose) := by abel
    rw [e, smul_neg, ← neg_smul]
    congr 1
    simp
    ring
  · show Matrix.trace (imaginaryComponent X) = 0
    unfold imaginaryComponent
    rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose, ht]
    simp
theorem hermitianComponent_neg (X : ComplexMatrix2) :
    hermitianComponent (-X) = -hermitianComponent X := by
  unfold hermitianComponent
  rw [Matrix.conjTranspose_neg, ← neg_add, smul_neg]
theorem imaginaryComponent_neg (X : ComplexMatrix2) :
    imaginaryComponent (-X) = -imaginaryComponent X := by
  unfold imaginaryComponent
  rw [Matrix.conjTranspose_neg]
  have e : -X - -X.conjTranspose = -(X - X.conjTranspose) := by abel
  rw [e, smul_neg]
def realPartFn {ι : Type*} (f : ι → ComplexMatrix2) : ι → ComplexMatrix2 :=
  fun i => hermitianComponent (f i)
def imagPartFn {ι : Type*} (f : ι → ComplexMatrix2) : ι → ComplexMatrix2 :=
  fun i => imaginaryComponent (f i)
theorem realPartFn_add_I_smul_imagPartFn {ι : Type*} (f : ι → ComplexMatrix2) :
    realPartFn f + Complex.I • imagPartFn f = f := by
  funext i
  exact hermitianComponent_add_I_smul_imaginaryComponent (f i)
theorem realPartFn_mem_edgeFormSpace {a : ℝ} {B : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms a) : realPartFn B ∈ edgeFormSpace a := by
  obtain ⟨h, r⟩ := hB
  refine ⟨fun b hb => hermitianComponent_mem_hermitianTraceless (h b hb), fun b => ?_⟩
  show hermitianComponent (B b.opposite) = -hermitianComponent (B b)
  rw [r, hermitianComponent_neg]
theorem imagPartFn_mem_edgeFormSpace {a : ℝ} {B : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms a) : imagPartFn B ∈ edgeFormSpace a := by
  obtain ⟨h, r⟩ := hB
  refine ⟨fun b hb => imaginaryComponent_mem_hermitianTraceless (h b hb), fun b => ?_⟩
  show imaginaryComponent (B b.opposite) = -imaginaryComponent (B b)
  rw [r, imaginaryComponent_neg]
theorem mem_complexEdgeForms_of_mem_edgeFormSpace {a : ℝ}
    {B : InfiniteLattice.Link a → ComplexMatrix2} (hB : B ∈ edgeFormSpace a) :
    B ∈ complexEdgeForms a :=
  ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
theorem add_I_smul_mem_complexEdgeForms {a : ℝ} {B₁ B₂ : InfiniteLattice.Link a → ComplexMatrix2}
    (h₁ : B₁ ∈ edgeFormSpace a) (h₂ : B₂ ∈ edgeFormSpace a) :
    B₁ + Complex.I • B₂ ∈ complexEdgeForms a :=
  (complexEdgeForms a).add_mem (mem_complexEdgeForms_of_mem_edgeFormSpace h₁)
    ((complexEdgeForms a).smul_mem _ (mem_complexEdgeForms_of_mem_edgeFormSpace h₂))
theorem exists_edgeForm_decomposition {a : ℝ} {B : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms a) :
    ∃ B₁ ∈ edgeFormSpace a, ∃ B₂ ∈ edgeFormSpace a, B = B₁ + Complex.I • B₂ :=
  ⟨_, realPartFn_mem_edgeFormSpace hB, _, imagPartFn_mem_edgeFormSpace hB,
    (realPartFn_add_I_smul_imagPartFn B).symm⟩
theorem exists_vertexFunction_decomposition {a : ℝ}
    {f : InfiniteLattice.LatticePoint a → ComplexMatrix2}
    (hf : f ∈ GroupLieProduct.tracelessFunctions (InfiniteLattice.LatticePoint a)) :
    ∃ f₁ ∈ vertexFunctionSpace a, ∃ f₂ ∈ vertexFunctionSpace a, f = f₁ + Complex.I • f₂ :=
  ⟨realPartFn f, fun x _ => hermitianComponent_mem_hermitianTraceless (hf x (mem_univ x)),
    imagPartFn f, fun x _ => imaginaryComponent_mem_hermitianTraceless (hf x (mem_univ x)),
    (realPartFn_add_I_smul_imagPartFn f).symm⟩
theorem mem_tracelessFunctions_of_mem_vertexFunctionSpace {a : ℝ}
    {f : InfiniteLattice.LatticePoint a → ComplexMatrix2} (hf : f ∈ vertexFunctionSpace a) :
    f ∈ GroupLieProduct.tracelessFunctions (InfiniteLattice.LatticePoint a) :=
  fun x _ => (hf x (mem_univ x)).2
theorem cubeVertices_finite_and_ncard (hZ : BlockStructure) {L k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (y : Vertex L k (j + 1)) :
    (cubeVertices L (meshAt L k j) y).Finite ∧
      (cubeVertices L (meshAt L k j) y).ncard = L ^ 4 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.cubeVertices_finite_ncard <;> assumption
theorem sumAlong_add_I_smul {a : ℝ} (F G : InfiniteLattice.Link a → ComplexMatrix2)
    (Γ : List (InfiniteLattice.Link a)) :
    sumAlong (F + Complex.I • G) Γ = sumAlong F Γ + Complex.I • sumAlong G Γ := by
  induction Γ with
  | nil => simp [sumAlong]
  | cons b Γ ih =>
    simp only [sumAlong, List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply] at ih ⊢
    rw [ih, smul_add]
    abel
theorem contourAverage_add_I_smul (L : ℕ) {a a' : ℝ}
    (F G : InfiniteLattice.Link a' → ComplexMatrix2)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    contourAverage L (F + Complex.I • G) y x =
      contourAverage L F y x + Complex.I • contourAverage L G y x := by
  simp only [contourAverage, sumAlong_add_I_smul, Finset.sum_add_distrib, ← Finset.smul_sum,
    smul_add]
  rw [smul_comm Complex.I]
theorem smul_finsum_add_I_smul {ι : Type*} {S : Set ι} (hS : S.Finite) (w : ℂ)
    (f g h : ι → ComplexMatrix2) (e : ∀ x, f x = g x + Complex.I • h x) :
    w • ∑ᶠ x ∈ S, f x = w • ∑ᶠ x ∈ S, g x + Complex.I • (w • ∑ᶠ x ∈ S, h x) := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS,
    finsum_mem_eq_finite_toFinset_sum _ hS]
  have key : ∑ x ∈ hS.toFinset, f x =
      ∑ x ∈ hS.toFinset, g x + Complex.I • ∑ x ∈ hS.toFinset, h x := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => e x
  rw [key, smul_add, smul_comm w Complex.I]
theorem linearSmoothing_apply_add_I_smul (L : ℕ) {a a' : ℝ}
    (F G : InfiniteLattice.Link a' → ComplexMatrix2) (c : InfiniteLattice.Link a)
    (hf : (cubeVertices L a' c.initial).Finite) :
    linearSmoothing L (F + Complex.I • G) c =
      linearSmoothing L F c + Complex.I • linearSmoothing L G c := by
  refine smul_finsum_add_I_smul hf _ _ _ _ fun _ => ?_
  simp only [contourAverage_add_I_smul, sumAlong_add_I_smul, smul_add, smul_sub]
  abel
theorem crossingSmoothing_apply_add_I_smul (L : ℕ) {a a' : ℝ}
    (F G : InfiniteLattice.Link a' → ComplexMatrix2) (c : InfiniteLattice.Link a)
    (hf : (cubeVertices L a' c.initial).Finite) :
    crossingSmoothing L (F + Complex.I • G) c =
      crossingSmoothing L F c + Complex.I • crossingSmoothing L G c :=
  smul_finsum_add_I_smul hf _ _ _ _ fun _ => sumAlong_add_I_smul F G _
theorem cubeContourAverage_apply_add_I_smul (L : ℕ) {a a' : ℝ}
    (F G : InfiniteLattice.Link a' → ComplexMatrix2) (y : InfiniteLattice.LatticePoint a)
    (hf : (cubeVertices L a' y).Finite) :
    cubeContourAverage L (F + Complex.I • G) y =
      cubeContourAverage L F y + Complex.I • cubeContourAverage L G y :=
  smul_finsum_add_I_smul hf _ _ _ _ fun x => contourAverage_add_I_smul L F G y x
theorem vertexSmoothing_apply_add_I_smul (L : ℕ) {a a' : ℝ}
    (f g : InfiniteLattice.LatticePoint a' → ComplexMatrix2) (y : InfiniteLattice.LatticePoint a)
    (hf : (cubeVertices L a' y).Finite) :
    vertexSmoothing L (f + Complex.I • g) y =
      vertexSmoothing L f y + Complex.I • vertexSmoothing L g y :=
  smul_finsum_add_I_smul hf _ _ _ _ fun _ => rfl
theorem linearSmoothing_apply_sub (L : ℕ) {a a' : ℝ}
    (F G : InfiniteLattice.Link a' → ComplexMatrix2) (c : InfiniteLattice.Link a)
    (hf : (cubeVertices L a' c.initial).Finite) :
    linearSmoothing L (F - G) c = linearSmoothing L F c - linearSmoothing L G c := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.linearSmoothing_sub <;> assumption
theorem vertexCoboundary_add_I_smul {a : ℝ} (f g : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    vertexCoboundary (f + Complex.I • g) =
      vertexCoboundary f + Complex.I • vertexCoboundary g := by
  funext b
  simp only [vertexCoboundary, Pi.add_apply, Pi.smul_apply, smul_sub]
  abel
theorem restrictVertexFunction_add_I_smul {a : ℝ} (a' : ℝ)
    (f g : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    restrictVertexFunction a' (f + Complex.I • g) =
      restrictVertexFunction a' f + Complex.I • restrictVertexFunction a' g :=
  rfl
theorem crossingSmoothing_mem_edgeFormSpace (hF : AxisPathReversal.MainStatement) {L k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace (meshAt L k j)) :
    crossingSmoothing (a := meshAt L k (j + 1)) L B ∈ edgeFormSpace (meshAt L k (j + 1)) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.crossingSmoothing_mem <;> assumption
theorem cubeContourAverage_mem_vertexFunctionSpace {L k j : ℕ} {B : Edge L k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace (meshAt L k j)) :
    cubeContourAverage (a := meshAt L k (j + 1)) L B ∈ vertexFunctionSpace (meshAt L k (j + 1)) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.cubeContourAverage_mem <;> assumption
theorem vertexCoboundary_mem_edgeFormSpace {a : ℝ}
    {l : InfiniteLattice.LatticePoint a → ComplexMatrix2} (hl : l ∈ vertexFunctionSpace a) :
    vertexCoboundary l ∈ edgeFormSpace a :=
  ⟨fun _ _ => ComplexMatrix2.hermitianTraceless.sub_mem (hl _ (mem_univ _)) (hl _ (mem_univ _)),
    fun _ => (neg_sub _ _).symm⟩
theorem maxOperatorNorm_cubeContourAverage_le_natCast (hZ : BlockStructure) {L k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (B : Edge L k j → ComplexMatrix2) :
    maxOperatorNorm (cubeContourAverage (a := meshAt L k (j + 1)) L B) ≤
      ((2 * (L - 1) : ℕ) : ℝ≥0∞) * maxOperatorNorm B := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.maxOperatorNorm_cubeContourAverage_le <;> assumption
theorem natCast_two_mul_sub_one {L : ℕ} (hL : 1 ≤ L) :
    ((2 * (L - 1) : ℕ) : ℝ≥0∞) = 2 * ((L : ℝ≥0∞) - 1) := by apply _root_.YangMills.Construction.Tower.FullSpace.IterateBounds.natCast_two_mul_sub_one <;> assumption
section OneStep
variable (hZ : BlockStructure) {L k i : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hi : i < k)
include hZ hL hi
theorem linearSmoothing_add_I_smul (F G : Edge L k i → ComplexMatrix2) :
    linearSmoothing (a := meshAt L k (i + 1)) L (F + Complex.I • G) =
      linearSmoothing (a := meshAt L k (i + 1)) L F +
        Complex.I • linearSmoothing (a := meshAt L k (i + 1)) L G :=
  funext fun c => linearSmoothing_apply_add_I_smul L F G c
    (cubeVertices_finite_and_ncard hZ hL hi c.initial).1
theorem crossingSmoothing_add_I_smul (F G : Edge L k i → ComplexMatrix2) :
    crossingSmoothing (a := meshAt L k (i + 1)) L (F + Complex.I • G) =
      crossingSmoothing (a := meshAt L k (i + 1)) L F +
        Complex.I • crossingSmoothing (a := meshAt L k (i + 1)) L G :=
  funext fun c => crossingSmoothing_apply_add_I_smul L F G c
    (cubeVertices_finite_and_ncard hZ hL hi c.initial).1
theorem cubeContourAverage_add_I_smul (F G : Edge L k i → ComplexMatrix2) :
    cubeContourAverage (a := meshAt L k (i + 1)) L (F + Complex.I • G) =
      cubeContourAverage (a := meshAt L k (i + 1)) L F +
        Complex.I • cubeContourAverage (a := meshAt L k (i + 1)) L G :=
  funext fun y => cubeContourAverage_apply_add_I_smul L F G y
    (cubeVertices_finite_and_ncard hZ hL hi y).1
theorem vertexSmoothing_add_I_smul (f g : Vertex L k i → ComplexMatrix2) :
    vertexSmoothing (a := meshAt L k (i + 1)) L (f + Complex.I • g) =
      vertexSmoothing (a := meshAt L k (i + 1)) L f +
        Complex.I • vertexSmoothing (a := meshAt L k (i + 1)) L g :=
  funext fun y => vertexSmoothing_apply_add_I_smul L f g y
    (cubeVertices_finite_and_ncard hZ hL hi y).1
end OneStep
theorem oneStepProperties (hRel : TrivialLinearization.OneStepIdentitiesHold)
    (hConst : LinearizationFacts.constantFormsStatement)
    (hOnto : LinearizationFacts.surjectivityStatement) (hZ : BlockStructure)
    (hF : AxisPathReversal.MainStatement) {L k i : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hi : i + 1 ≤ k) : OneStepProperties L k i := by
  have hj : i < k := hi
  have hs := hRel L hL k i hj
  have hQ := linearSmoothing_add_I_smul hZ hL hj
  have hR := crossingSmoothing_add_I_smul hZ hL hj
  have hN := cubeContourAverage_add_I_smul hZ hL hj
  have hA := vertexSmoothing_add_I_smul hZ hL hj
  have hOn := hOnto L hL k i 0 hj (Nat.zero_le k)
  have memR : ∀ {B : Edge L k i → ComplexMatrix2}, B ∈ edgeFormSpace (meshAt L k i) →
      crossingSmoothing (a := meshAt L k (i + 1)) L B ∈ edgeFormSpace (meshAt L k (i + 1)) :=
    fun hB => crossingSmoothing_mem_edgeFormSpace hF hL hj hB
  have memQ : ∀ {B : Edge L k i → ComplexMatrix2}, B ∈ edgeFormSpace (meshAt L k i) →
      linearSmoothing (a := meshAt L k (i + 1)) L B ∈ edgeFormSpace (meshAt L k (i + 1)) := by
    intro B hB
    rw [hs.1 B hB]
    exact (edgeFormSpace _).sub_mem (memR hB)
      (vertexCoboundary_mem_edgeFormSpace (cubeContourAverage_mem_vertexFunctionSpace hB))
  refine
    { linearSmoothing_sub := ?_
      linearSmoothing_mapsTo := ?_
      crossingSmoothing_mapsTo := ?_
      linearSmoothing_mapsTo_real := fun B hB => memQ hB
      crossingSmoothing_mapsTo_real := fun B hB => memR hB
      cubeContourAverage_mapsTo := ?_
      vertexSmoothing_mapsTo := ?_
      linearSmoothing_eq := ?_
      linearSmoothing_coboundary := ?_
      crossingSmoothing_coboundary := ?_
      cubeContourAverage_coboundary := ?_
      of_constant := ?_
      linearSmoothing_surjOn := ?_
      crossingSmoothing_surjOn := ?_
      linearSmoothing_surjOn_real := ?_
      crossingSmoothing_surjOn_real := ?_
      maxOperatorNorm_cubeContourAverage_le := ?_ }
  · intro B _ B' _
    exact funext fun c => linearSmoothing_apply_sub L B B' c
      (cubeVertices_finite_and_ncard hZ hL hj c.initial).1
  · intro B hB
    obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := exists_edgeForm_decomposition hB
    rw [SetLike.mem_coe, hQ]
    exact add_I_smul_mem_complexEdgeForms (memQ h₁) (memQ h₂)
  · intro B hB
    obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := exists_edgeForm_decomposition hB
    rw [SetLike.mem_coe, hR]
    exact add_I_smul_mem_complexEdgeForms (memR h₁) (memR h₂)
  · intro B hB
    obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := exists_edgeForm_decomposition hB
    rw [SetLike.mem_coe, hN]
    exact Submodule.add_mem _
      (mem_tracelessFunctions_of_mem_vertexFunctionSpace
        (cubeContourAverage_mem_vertexFunctionSpace h₁))
      (Submodule.smul_mem _ _ (mem_tracelessFunctions_of_mem_vertexFunctionSpace
        (cubeContourAverage_mem_vertexFunctionSpace h₂)))
  · intro f hf y _
    have hy := (cubeVertices_finite_and_ncard hZ hL hj y).1
    have key : ∑ᶠ x ∈ cubeVertices L (meshAt L k i) y, f x ∈ ComplexMatrix2.traceless :=
      finsum_mem_induction (· ∈ ComplexMatrix2.traceless) ComplexMatrix2.traceless.zero_mem
        (fun _ _ => ComplexMatrix2.traceless.add_mem) fun x _ => hf x (mem_univ x)
    exact ComplexMatrix2.traceless.smul_mem _ key
  · intro B hB
    obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := exists_edgeForm_decomposition hB
    rw [hQ, hR, hN, hs.1 B₁ h₁, hs.1 B₂ h₂, vertexCoboundary_add_I_smul, smul_sub]
    abel
  · intro f hf
    obtain ⟨f₁, h₁, f₂, h₂, rfl⟩ := exists_vertexFunction_decomposition hf
    rw [vertexCoboundary_add_I_smul, hQ, (hs.2 f₁ h₁).1, (hs.2 f₂ h₂).1,
      restrictVertexFunction_add_I_smul, vertexCoboundary_add_I_smul]
  · intro f hf
    obtain ⟨f₁, h₁, f₂, h₂, rfl⟩ := exists_vertexFunction_decomposition hf
    rw [vertexCoboundary_add_I_smul, hR, (hs.2 f₁ h₁).2.1, (hs.2 f₂ h₂).2.1, hA,
      vertexCoboundary_add_I_smul]
  · intro f hf
    obtain ⟨f₁, h₁, f₂, h₂, rfl⟩ := exists_vertexFunction_decomposition hf
    rw [vertexCoboundary_add_I_smul, hN, (hs.2 f₁ h₁).2.2.1, (hs.2 f₂ h₂).2.2.1, hA,
      restrictVertexFunction_add_I_smul, smul_sub]
    abel
  · intro B hB a ha
    have c₁ := hConst L hL k i hj (realPartFn B) (realPartFn_mem_edgeFormSpace hB)
      (fun μ => hermitianComponent (a μ)) (fun x μ => congrArg hermitianComponent (ha x μ))
    have c₂ := hConst L hL k i hj (imagPartFn B) (imagPartFn_mem_edgeFormSpace hB)
      (fun μ => imaginaryComponent (a μ)) (fun x μ => congrArg imaginaryComponent (ha x μ))
    have e := realPartFn_add_I_smul_imagPartFn B
    refine ⟨?_, ?_, fun x μ => ?_⟩
    · rw [← e, hN, c₁.2.1, c₂.2.1]
      simp
    · rw [← e, hQ, hR, c₁.2.2.1, c₂.2.2.1]
    · rw [← e, hR]
      show crossingSmoothing L (realPartFn B) (InfiniteLattice.Link.forwardFrom x μ) +
        Complex.I • crossingSmoothing L (imagPartFn B) (InfiniteLattice.Link.forwardFrom x μ) = _
      rw [c₁.2.2.2.2 x μ, c₂.2.2.2.2 x μ, smul_comm Complex.I, ← smul_add,
        hermitianComponent_add_I_smul_imaginaryComponent]
  · intro C hC
    obtain ⟨C₁, h₁, C₂, h₂, rfl⟩ := exists_edgeForm_decomposition hC
    obtain ⟨B₁, m₁, rfl⟩ := hOn.1 C₁ h₁
    obtain ⟨B₂, m₂, rfl⟩ := hOn.1 C₂ h₂
    exact ⟨B₁ + Complex.I • B₂, add_I_smul_mem_complexEdgeForms m₁ m₂, hQ B₁ B₂⟩
  · intro C hC
    obtain ⟨C₁, h₁, C₂, h₂, rfl⟩ := exists_edgeForm_decomposition hC
    obtain ⟨B₁, m₁, rfl⟩ := hOn.2.1 C₁ h₁
    obtain ⟨B₂, m₂, rfl⟩ := hOn.2.1 C₂ h₂
    exact ⟨B₁ + Complex.I • B₂, add_I_smul_mem_complexEdgeForms m₁ m₂, hR B₁ B₂⟩
  · intro C hC
    obtain ⟨B, m, rfl⟩ := hOn.1 C hC
    exact ⟨B, m, rfl⟩
  · intro C hC
    obtain ⟨B, m, rfl⟩ := hOn.2.1 C hC
    exact ⟨B, m, rfl⟩
  · intro B _
    have hL1 : 1 ≤ L := by have := hL.2; omega
    rw [← natCast_two_mul_sub_one hL1]
    exact maxOperatorNorm_cubeContourAverage_le_natCast hZ hL hj B
theorem oneStepClaim_holds (hRel : TrivialLinearization.OneStepIdentitiesHold)
    (hConst : LinearizationFacts.constantFormsStatement)
    (hOnto : LinearizationFacts.surjectivityStatement) (hZ : BlockStructure)
    (hF : AxisPathReversal.MainStatement) : OneStepClaim :=
  fun _ hL _ _ hi => oneStepProperties hRel hConst hOnto hZ hF hL hi
end YangMills.Construction.Tower.FullSpace.OneStepComplexForms
end
