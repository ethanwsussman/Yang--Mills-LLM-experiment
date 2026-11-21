import YangMills.Construction.FormOnAFibre.SiteFormsAtAFiniteSideAreEuclidean
import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreUnderAGaugeFunctionProof
import YangMills.Construction.RunningCouplingSlope.ChainNumberReadsNoPoint
import YangMills.Construction.RunningCouplingSlope.ChangeOfGaugeInAGaussianNumber
import YangMills.Construction.RunningCouplingSlope.FibreFormAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.LeastPointsOverAFieldAreOneOrbit
import YangMills.Construction.RunningCouplingSlope.MapsOfTheChainAtALeastPoint
import YangMills.Construction.RunningCouplingSlope.TheChainNearARealPoint
import YangMills.Construction.RunningCouplingSlope.TheKernelOfTheHessianOfTheWholeChainDecaysProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open Filter MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Tower LinearConstraint GaussianConstraint Matrices
namespace RunningCouplingSlope.LogWeightIndependence
section
variable {E F : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
private theorem constrainedGaussian_isometry (c : InnerProductSpace.Core ℝ E)
    (c' : InnerProductSpace.Core ℝ F)
    (M M' : E →ₗ[ℝ] F) (A : E →ₗ[ℝ] E) (hA : ∀ x y, c.inner (A x) (A y) = c.inner x y)
    (hM : ∀ x, M' (A x) = M x) (T : QuadraticForm ℝ (LinearMap.ker M))
    (T' : QuadraticForm ℝ (LinearMap.ker M'))
    (hT : ∀ (ξ : LinearMap.ker M) (h : A ξ ∈ LinearMap.ker M'), T' ⟨A ξ, h⟩ = T ξ) :
    constrainedGaussianNumberOfCores c c' M' T' = constrainedGaussianNumberOfCores c c' M T := by
  let := c.toNormedAddCommGroup
  let := InnerProductSpace.ofCore c.toCore
  let := c'.toNormedAddCommGroup
  let := InnerProductSpace.ofCore c'.toCore
  let Ai : E →ₗᵢ[ℝ] E := A.isometryOfInner hA
  let Ae : E ≃ₗᵢ[ℝ] E := Ai.toLinearIsometryEquiv rfl
  have hsym : ∀ x, A (Ae.symm x) = x := fun x => Ae.apply_symm_apply x
  have hadj : LinearMap.adjoint A = (Ae.symm.toLinearEquiv : E →ₗ[ℝ] E) := by
    refine ((LinearMap.eq_adjoint_iff (Ae.symm.toLinearEquiv : E →ₗ[ℝ] E) A).mpr fun x y => ?_).symm
    have h := Ae.inner_map_map (Ae.symm x) y
    rw [Ae.apply_symm_apply] at h
    exact h.symm
  have hMM : M' ∘ₗ LinearMap.adjoint M' = M ∘ₗ LinearMap.adjoint M := by
    have e : M = M' ∘ₗ A := LinearMap.ext fun x => (hM x).symm
    rw [e, LinearMap.adjoint_comp, hadj]
    refine LinearMap.ext fun x => ?_
    change M' _ = M' (A (Ae.symm _))
    rw [hsym]
  have mem : ∀ ξ : LinearMap.ker M, A ξ ∈ LinearMap.ker M' := fun ξ =>
    LinearMap.mem_ker.2 ((hM _).trans (LinearMap.mem_ker.1 ξ.2))
  have mem' : ∀ η : LinearMap.ker M', Ae.symm η ∈ LinearMap.ker M := fun η =>
    LinearMap.mem_ker.2 (by rw [← hM, hsym]; exact LinearMap.mem_ker.1 η.2)
  let e : LinearMap.ker M ≃ₗᵢ[ℝ] LinearMap.ker M' :=
    { toFun := fun ξ => ⟨A ξ, mem ξ⟩
      invFun := fun η => ⟨Ae.symm η, mem' η⟩
      left_inv := fun ξ => Subtype.ext (Ae.symm_apply_apply ξ)
      right_inv := fun η => Subtype.ext (hsym η)
      map_add' := fun ξ ξ' => Subtype.ext (map_add A _ _)
      map_smul' := fun r ξ => Subtype.ext (map_smul A r _)
      norm_map' := fun ξ => Ae.norm_map ξ }
  have hI : kernelGaussianIntegral M' T' = kernelGaussianIntegral M T := by
    unfold kernelGaussianIntegral
    letI : MeasurableSpace (LinearMap.ker M) := borel _
    haveI : BorelSpace (LinearMap.ker M) := ⟨rfl⟩
    letI : MeasurableSpace (LinearMap.ker M') := borel _
    haveI : BorelSpace (LinearMap.ker M') := ⟨rfl⟩
    exact show (∫ B : LinearMap.ker M', Real.exp (-(1 / 2) * T' B)) =
        ∫ B : LinearMap.ker M, Real.exp (-(1 / 2) * T B) from by
      have hmp := e.measurePreserving
      have hem : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
      rw [← hmp.integral_comp hem]
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      change Real.exp (-(1 / 2) * T' ⟨A ξ, mem ξ⟩) = _
      rw [hT ξ (mem ξ)]
  change constrainedGaussianNumber M' T' = constrainedGaussianNumber M T
  unfold constrainedGaussianNumber
  rw [hMM, hI]
private theorem absDet_isometry {G Y : Type} [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (cG : InnerProductSpace.Core ℝ G) (K : Submodule ℝ G) (g : G →ₗ[ℝ] G)
    (hg : ∀ x y, cG.inner (g x) (g y) = cG.inner x y) (hK : ∀ x ∈ K, g x ∈ K)
    (B B' : G →ₗ[ℝ] Y) (hB : ∀ x, B' (g x) = B x)
    (h' : Function.Bijective (B' ∘ₗ K.subtype)) :
    Function.Bijective (B ∘ₗ K.subtype) ∧
      (letI := cG.toNormedAddCommGroup
       letI := InnerProductSpace.ofCore cG.toCore
       absDetOfMap (B' ∘ₗ K.subtype) = absDetOfMap (B ∘ₗ K.subtype)) := by
  let := cG.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cG.toCore
  let gi : K →ₗᵢ[ℝ] K := (g.restrict hK).isometryOfInner fun x y => hg x y
  let ι : K ≃ₗᵢ[ℝ] K := gi.toLinearIsometryEquiv rfl
  have hc : B ∘ₗ K.subtype = (B' ∘ₗ K.subtype) ∘ₗ (ι.toLinearEquiv : K →ₗ[ℝ] K) :=
    LinearMap.ext fun x => (hB x).symm
  refine ⟨?_, ?_⟩
  · rw [hc]
    exact h'.comp ι.bijective
  · rw [hc]
    set P := B' ∘ₗ K.subtype with hP
    have hadj : LinearMap.adjoint (ι.toLinearEquiv : K →ₗ[ℝ] K) =
        (ι.symm.toLinearEquiv : K →ₗ[ℝ] K) := by
      refine ((LinearMap.eq_adjoint_iff (ι.symm.toLinearEquiv : K →ₗ[ℝ] K)
        (ι.toLinearEquiv : K →ₗ[ℝ] K)).mpr fun x y => ?_).symm
      have h := ι.inner_map_map (ι.symm x) y
      rw [ι.apply_symm_apply] at h
      exact h.symm
    have e2 : LinearMap.adjoint (P ∘ₗ (ι.toLinearEquiv : K →ₗ[ℝ] K)) ∘ₗ
        (P ∘ₗ (ι.toLinearEquiv : K →ₗ[ℝ] K)) =
        (ι.symm.toLinearEquiv : K →ₗ[ℝ] K) ∘ₗ (LinearMap.adjoint P ∘ₗ P) ∘ₗ
          (ι.symm.toLinearEquiv.symm : K →ₗ[ℝ] K) := by
      rw [LinearMap.adjoint_comp, hadj]
      rfl
    unfold absDetOfMap
    rw [e2, LinearMap.det_conj]
private theorem gaussian_slice_indep (hG : LinearConstraint.GaugeChangeGaussianIdentity)
    {A C G Gc Y Y' : Type} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]
    [AddCommGroup C] [Module ℝ C] [FiniteDimensional ℝ C]
    [AddCommGroup G] [Module ℝ G] [FiniteDimensional ℝ G]
    [AddCommGroup Gc] [Module ℝ Gc] [FiniteDimensional ℝ Gc]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] [FiniteDimensional ℝ Y']
    (cA : InnerProductSpace.Core ℝ A) (cC : InnerProductSpace.Core ℝ C)
    (cG : InnerProductSpace.Core ℝ G) (cGc : InnerProductSpace.Core ℝ Gc)
    (D : G →ₗ[ℝ] A) (Dc : Gc →ₗ[ℝ] C) (Q : A →ₗ[ℝ] C) (r : G →ₗ[ℝ] Gc) (rt : Gc →ₗ[ℝ] G)
    (T : QuadraticForm ℝ (LinearMap.ker Q)) (K : Submodule ℝ G) (hK : K = LinearMap.ker r)
    (hQ : Function.Surjective Q)
    (hrt : ∀ g x, cG.inner (rt g) x = cGc.inner g (r x))
    (hrrt : ∀ g, r (rt g) = g)
    (hQD : ∀ x, Q (D x) = Dc (r x))
    (hDinj : Function.Injective (D ∘ₗ K.subtype))
    (hT0 : ∀ ξ, 0 ≤ T ξ)
    (hTnull : ∀ ξ : LinearMap.ker Q, T ξ = 0 ↔ (ξ : A) ∈ K.map D)
    (l : A →ₗ[ℝ] Y) (l' : A →ₗ[ℝ] Y')
    (hl : Function.Bijective (l ∘ₗ D ∘ₗ K.subtype))
    (hl' : Function.Bijective (l' ∘ₗ D ∘ₗ K.subtype)) :
    constrainedGaussianNumberOfCores cA cC Q (T + (normSqForm l).comp (LinearMap.ker Q).subtype) *
        (letI := cG.toNormedAddCommGroup
         letI := InnerProductSpace.ofCore cG.toCore
         absDetOfMap (l ∘ₗ D ∘ₗ K.subtype)) =
      constrainedGaussianNumberOfCores cA cC Q (T + (normSqForm l').comp (LinearMap.ker Q).subtype) *
        (letI := cG.toNormedAddCommGroup
         letI := InnerProductSpace.ofCore cG.toCore
         absDetOfMap (l' ∘ₗ D ∘ₗ K.subtype)) := by
  subst hK
  let := cA.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cA.toCore
  let := cC.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cC.toCore
  let := cG.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cG.toCore
  let := cGc.toNormedAddCommGroup
  let := InnerProductSpace.ofCore cGc.toCore
  have adjr : LinearMap.adjoint r = rt := ((LinearMap.eq_adjoint_iff rt r).mpr hrt).symm
  have hrr : r ∘ₗ LinearMap.adjoint r = LinearMap.id := by
    rw [adjr]
    exact LinearMap.ext hrrt
  have hn0 : r + (0 : A →ₗ[ℝ] Gc) ∘ₗ D = r := by simp
  obtain ⟨-, -, h, key⟩ := hG G A Gc C D Dc Q r 0 T hQ hrr (LinearMap.ext hQD)
    (by rw [hn0, hrr]; exact Function.bijective_id) hDinj hT0 hTnull
  have e1 := key Y Y' l l' hl (by rw [hn0]; exact hl')
  have e2 := key Y' Y' l' l' hl' (by rw [hn0]; exact hl')
  exact e1.trans e2.symm
end
section
private theorem det_of_compact {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
private theorem isUnit_det_of_compact {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : IsUnit g.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem fullTrace_conj {g M : ComplexMatrix2} (hg : IsUnit g.det) :
    ComplexMatrix2.fullTrace (g * M * g⁻¹) = ComplexMatrix2.fullTrace M := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.fullTrace_conj <;> assumption
private theorem conjugateBy_mem {g A : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy g A ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p2904 <;> assumption
private theorem conjugateBy_add (g A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (A + B) =
      ComplexMatrix2.conjugateBy g A + ComplexMatrix2.conjugateBy g B := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
private theorem conjugateBy_sub (g A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (A - B) =
      ComplexMatrix2.conjugateBy g A - ComplexMatrix2.conjugateBy g B := by
  simp [ComplexMatrix2.conjugateBy, mul_sub, sub_mul]
private theorem conjugateBy_smul (g : ComplexMatrix2) (r : ℝ) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (r • A) = r • ComplexMatrix2.conjugateBy g A := by apply _root_.YangMills.Construction.Tower.RealLinearMaps.conjugateBy_real_smul <;> assumption
private theorem conjugateBy_gauge {g h : ComplexMatrix2} (U : ComplexMatrix2) (hh : IsUnit h.det)
    (x : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy (g * U * h⁻¹) (ComplexMatrix2.conjugateBy h x) =
      ComplexMatrix2.conjugateBy g (ComplexMatrix2.conjugateBy U x) := by
  simp only [ComplexMatrix2.conjugateBy, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hh,
    mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hh]
private theorem halfTrace_conjugateBy {g : ComplexMatrix2} (hg : IsUnit g.det) (A B : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (ComplexMatrix2.conjugateBy g A * ComplexMatrix2.conjugateBy g B) =
      ComplexMatrix2.halfTrace (A * B) := by
  have e : ComplexMatrix2.conjugateBy g A * ComplexMatrix2.conjugateBy g B = g * (A * B) * g⁻¹ := by
    simp only [ComplexMatrix2.conjugateBy, mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hg]
  rw [e]
  simp only [ComplexMatrix2.halfTrace]
  rw [fullTrace_conj hg]
private theorem matExp_conjugateBy {g : ComplexMatrix2} (hg : IsUnit g.det) (B : ComplexMatrix2) :
    ComplexMatrix2.matExp (Complex.I • ComplexMatrix2.conjugateBy g B) =
      g * ComplexMatrix2.matExp (Complex.I • B) * g⁻¹ := by
  have e : Complex.I • ComplexMatrix2.conjugateBy g B = g * (Complex.I • B) * g⁻¹ := by
    simp [ComplexMatrix2.conjugateBy, Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  exact Matrix.exp_conj g _ ((Matrix.isUnit_iff_isUnit_det _).2 hg)
private theorem conj_mul_gauge {g h : ComplexMatrix2} (E U : ComplexMatrix2) (hg : IsUnit g.det) :
    (g * E * g⁻¹) * (g * U * h⁻¹) = g * (E * U) * h⁻¹ := by
  simp only [mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hg]
private theorem gauge_inv {g h : ComplexMatrix2} (M : ComplexMatrix2) (hh : IsUnit h.det) :
    (g * M * h⁻¹)⁻¹ = h * M⁻¹ * g⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hh]
  simp only [mul_assoc]
private theorem cancel_I_smul_mul {W M N : ComplexMatrix2} (hW : IsUnit W.det)
    (h : (Complex.I • M) * W = (Complex.I • N) * W) : M = N := by
  have h1 : Complex.I • M = Complex.I • N := by
    have := congrArg (· * W⁻¹) h
    simpa [mul_assoc, Matrix.mul_nonsing_inv _ hW] using this
  exact smul_right_injective _ Complex.I_ne_zero h1
abbrev _root_.YangMills.SharedProofs.p6717 := @cancel_I_smul_mul
end
section
variable {L n k j : ℕ}
private theorem edgeForm_ext {A B : edgeFormSpace L n k j}
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented →
      (A : Edge L n k j → ComplexMatrix2) b = (B : Edge L n k j → ComplexMatrix2) b) : A = B := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.edgeForm_ext <;> assumption
private theorem extendOddly_pos (f : Edge L n k j → ComplexMatrix2) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.IdentityChartCurves.extendOddly_of_pos <;> assumption
private theorem extendOddly_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Edge L n k j → ComplexMatrix2)
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.hermitianTraceless) :
    extendOddly f ∈ edgeFormSpace L n k j := by apply _root_.YangMills.SharedProofs.p1442 <;> assumption
private def adjointFormMap
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (u : Vertex L n k j → ComplexMatrix2) (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup) :
    edgeFormSpace L n k j →ₗ[ℝ] edgeFormSpace L n k j where
  toFun B := ⟨adjointForm u B, extendOddly_mem hx _ fun b hb => conjugateBy_mem (hu _) (B.2.1 b hb)⟩
  map_add' B B' := edgeForm_ext fun b hb => by
    change adjointForm u ((B + B' : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) b =
      adjointForm u B b + adjointForm u B' b
    simp only [adjointForm, extendOddly_pos _ hb]
    exact conjugateBy_add _ _ _
  map_smul' c B := edgeForm_ext fun b hb => by
    change adjointForm u ((c • B : edgeFormSpace L n k j) : Edge L n k j → ComplexMatrix2) b =
      c • adjointForm u B b
    simp only [adjointForm, extendOddly_pos _ hb]
    exact conjugateBy_smul _ _ _
private theorem adjointFormMap_pos
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (u : Vertex L n k j → ComplexMatrix2) (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup)
    (B : edgeFormSpace L n k j) {b : Edge L n k j} (hb : b.IsPositivelyOriented) :
    (adjointFormMap hx u hu B : Edge L n k j → ComplexMatrix2) b =
      ComplexMatrix2.conjugateBy (u b.source) ((B : Edge L n k j → ComplexMatrix2) b) := by
  change extendOddly (fun b => ComplexMatrix2.conjugateBy (u b.source)
    ((B : Edge L n k j → ComplexMatrix2) b)) b = _
  exact extendOddly_pos _ hb
private theorem pairing_adjointFormMap
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (u : Vertex L n k j → ComplexMatrix2) (hu : ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup)
    (B B' : edgeFormSpace L n k j) :
    edgeFormPairing (adjointFormMap hx u hu B : Edge L n k j → ComplexMatrix2)
        (adjointFormMap hx u hu B' : Edge L n k j → ComplexMatrix2) =
      edgeFormPairing (B : Edge L n k j → ComplexMatrix2) (B' : Edge L n k j → ComplexMatrix2) := by
  unfold edgeFormPairing traceFinsumPairing
  refine finsum_congr fun b => ?_
  simp only [restrictToPositiveEdges]
  rw [adjointFormMap_pos hx u hu B b.2, adjointFormMap_pos hx u hu B' b.2,
    halfTrace_conjugateBy (isUnit_det_of_compact (hu _))]
end
section
variable {L n k : ℕ} [NeZero L]
private theorem chainPoint_ext {X Y : ChainPoint L n k} (h1 : X.fine = Y.fine)
    (h2 : X.noise = Y.noise) : X = Y := by
  cases X
  cases Y
  cases h1
  cases h2
  rfl
private theorem fieldOfPositiveValues_pos {j : ℕ} (w : PositiveEdge L n k j → ComplexMatrix2)
    {b : Edge L n k j} (h : b.IsPositivelyOriented) : fieldOfPositiveValues w b = w ⟨b, h⟩ := by
  simp [fieldOfPositiveValues, h]
private theorem fieldOfPositiveValues_neg {j : ℕ} (w : PositiveEdge L n k j → ComplexMatrix2)
    {b : Edge L n k j} (h : ¬b.IsPositivelyOriented) :
    fieldOfPositiveValues w b =
      (w ⟨b.opposite, PeriodicLattice.Bond.opposite_isPositivelyOriented h⟩)⁻¹ := by
  simp [fieldOfPositiveValues, h, PeriodicLattice.Bond.opposite_isPositivelyOriented h]
private theorem levelField_succ (X : ChainPoint L n k) {j : ℕ} (h : j < k) :
    levelField X (j + 1) =
      fieldOfPositiveValues fun c => X.noise ⟨j, h⟩ c * normalizedMean (levelField X j) c.1 := by
  simp [levelField, h]
private theorem levelField_succ_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : b.IsPositivelyOriented) :
    levelField X (j + 1) b = X.noise ⟨j, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X j) b := by
  rw [levelField_succ X h, fieldOfPositiveValues_pos _ hb]
private theorem levelField_succ_neg (X : ChainPoint L n k) {j : ℕ} (h : j < k)
    {b : Edge L n k (j + 1)} (hb : ¬b.IsPositivelyOriented) :
    levelField X (j + 1) b = (levelField X (j + 1) b.opposite)⁻¹ := by
  rw [levelField_succ_pos X h (PeriodicLattice.Bond.opposite_isPositivelyOriented hb),
    levelField_succ X h, fieldOfPositiveValues_neg _ hb]
private theorem restrict_zero (v : Vertex L n k 0 → ComplexMatrix2) :
    restrictVertexFunction 0 v = v := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.restrictVertexFunction_zero <;> assumption
private theorem restrict_toSublattice (v : Vertex L n k 0 → ComplexMatrix2) {j : ℕ} (hj : j ≤ k)
    (y : Vertex L n k (j + 1)) :
    restrictVertexFunction j v (y.toSublattice (PeriodicLattice.levelDepth k j)) =
      restrictVertexFunction (j + 1) v y := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.restrictVertexFunction_toSublattice <;> assumption
private theorem fieldsIn_complex_of_compact {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) :
    V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
  ⟨fun b hb => det_of_compact (hV.1 b hb), hV.2⟩
variable (hC : ContourMeanGaugeCovariant) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hn : 0 < n)
include hC hL hn in
private theorem levelField_gauge {Y : ChainPoint L n k}
    (hY : ∀ j, j < k → levelField Y j ∈ fieldSpace L n k j) {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    ∀ j, j ≤ k → levelField (gaugeTransformPoint v Y) j =
      PeriodicLattice.gaugeTransform (restrictVertexFunction j v) (levelField Y j) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [restrict_zero]
    rfl
  | succ j ih =>
    intro hj
    have h : j < k := hj
    have hW := hY j h
    have hvj : ∀ i (x : Vertex L n k i), restrictVertexFunction i v x ∈
        PeriodicLattice.compactGaugeGroup :=
      fun i x => hv _
    have hpos : ∀ b : Edge L n k (j + 1), b.IsPositivelyOriented →
        levelField (gaugeTransformPoint v Y) (j + 1) b =
        PeriodicLattice.gaugeTransform (restrictVertexFunction (j + 1) v) (levelField Y (j + 1)) b := by
      intro b hb
      have hcov := (hC L hL n k j hn h _ (fieldsIn_complex_of_compact hW) (restrictVertexFunction j v)
        (fun x => det_of_compact (hvj j x)) b hb).2.2
      rw [restrict_toSublattice v h.le, restrict_toSublattice v h.le] at hcov
      rw [levelField_succ_pos _ h hb, ih h.le, hcov]
      simp only [PeriodicLattice.gaugeTransform]
      rw [levelField_succ_pos Y h hb]
      have e : (gaugeTransformPoint v Y).noise ⟨j, h⟩ ⟨b, hb⟩ =
          restrictVertexFunction (j + 1) v b.source * Y.noise ⟨j, h⟩ ⟨b, hb⟩ *
            (restrictVertexFunction (j + 1) v b.source)⁻¹ := rfl
      rw [e]
      have hg : (restrictVertexFunction (j + 1) v b.source)⁻¹ *
          restrictVertexFunction (j + 1) v b.source = 1 :=
        Matrix.nonsing_inv_mul _ (isUnit_det_of_compact (hvj _ _))
      calc _ = restrictVertexFunction (j + 1) v b.source * Y.noise ⟨j, h⟩ ⟨b, hb⟩ *
              ((restrictVertexFunction (j + 1) v b.source)⁻¹ *
                restrictVertexFunction (j + 1) v b.source) *
              normalizedMean (levelField Y j) b * (restrictVertexFunction (j + 1) v b.target)⁻¹ := by
            simp only [mul_assoc]
        _ = _ := by rw [hg]; simp only [mul_one, mul_assoc]
    funext b
    by_cases hb : b.IsPositivelyOriented
    · exact hpos b hb
    · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      rw [levelField_succ_neg _ h hb, hpos _ hp]
      simp only [PeriodicLattice.gaugeTransform]
      have e1 : levelField Y (j + 1) b = (levelField Y (j + 1) b.opposite)⁻¹ :=
        levelField_succ_neg _ h hb
      have e2 : b.opposite.source = b.target := rfl
      have e3 : b.opposite.target = b.source := rfl
      rw [e1, e2, e3, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_compact (hvj _ _))]
      simp only [mul_assoc]
abbrev _root_.YangMills.SharedProofs.p78689 := @levelField_gauge
include hC hL hn in
private theorem meanRadius_gauge {Y : ChainPoint L n k}
    (hY : ∀ j, j < k → levelField Y j ∈ fieldSpace L n k j) {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    meanRadius (levelField (gaugeTransformPoint v Y) i) c.1 = meanRadius (levelField Y i) c.1 := by
  have hW := hY i i.2
  have hl := (hC L hL n k i hn i.2 _ (fieldsIn_complex_of_compact hW) (restrictVertexFunction i v)
      (fun x => det_of_compact (hv _)) c.1 c.2).2.1
  rw [levelField_gauge hC hL hn hY hv i i.2.le, hl]
abbrev _root_.YangMills.SharedProofs.p13056 := @meanRadius_gauge
include hC hL hn in
private theorem chainAction_gauge
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (a : ℝ) (hk : 0 < k) {Y : ChainPoint L n k}
    (hY : ∀ j, j < k → levelField Y j ∈ fieldSpace L n k j) {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    chainAction a (gaugeTransformPoint v Y) = chainAction a Y := by
  have hU : Y.fine ∈ fieldSpace L n k 0 := hY 0 hk
  have hjm : -(n : ℤ) ≤ PeriodicLattice.levelDepth k 0 := by
    simp only [PeriodicLattice.levelDepth]; omega
  have h1 : plaquetteAction L n k (gaugeTransformPoint v Y).fine = plaquetteAction L n k Y.fine := by
    have e : (gaugeTransformPoint v Y).fine = PeriodicLattice.gaugeTransform v Y.fine := rfl
    rw [e]
    simp only [plaquetteAction, PeriodicLattice.wilsonAction]
    refine finsum_congr fun p => ?_
    have := (hg L n hL.1 hL.2 hn (PeriodicLattice.levelDepth k 0) hjm Set.univ Y.fine v v
      (fun b _ => trivial) (fieldsIn_complex_of_compact hU) (fun x => det_of_compact (hv x))
      (fun x => det_of_compact (hv x))).2.2 p (fun _ _ => trivial)
    simp only [PeriodicLattice.plaquetteCost]
    rw [this, fullTrace_conj (isUnit_det_of_compact (hv _))]
  have h2 : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (meanRadius (levelField (gaugeTransformPoint v Y) i) c.1).re *
          traceDefect ((gaugeTransformPoint v Y).noise i c) =
        (meanRadius (levelField Y i) c.1).re * traceDefect (Y.noise i c) := by
    intro i c
    rw [meanRadius_gauge hC hL hn hY hv i c]
    congr 1
    have e : (gaugeTransformPoint v Y).noise i c = restrictVertexFunction (i + 1) v c.1.source *
        Y.noise i c * (restrictVertexFunction (i + 1) v c.1.source)⁻¹ := rfl
    rw [e]
    simp only [traceDefect, ComplexMatrix2.halfTrace]
    rw [fullTrace_conj (g := restrictVertexFunction (i + 1) v c.1.source)
      (isUnit_det_of_compact (hv _))]
  have h3 : ∑ i : Fin k, ∑ᶠ c : PositiveEdge L n k (i + 1),
      (meanRadius (levelField (gaugeTransformPoint v Y) i) c.1).re *
        traceDefect ((gaugeTransformPoint v Y).noise i c) =
      ∑ i : Fin k, ∑ᶠ c : PositiveEdge L n k (i + 1),
        (meanRadius (levelField Y i) c.1).re * traceDefect (Y.noise i c) :=
    Finset.sum_congr rfl fun i _ => finsum_congr fun c => h2 i c
  unfold chainAction
  rw [h1, h3]
abbrev _root_.YangMills.SharedProofs.p8575 := @chainAction_gauge
include hC hL hn in
private theorem logRadiusSum_gauge {Y : ChainPoint L n k}
    (hY : ∀ j, j < k → levelField Y j ∈ fieldSpace L n k j) {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    logRadiusSum (gaugeTransformPoint v Y) = logRadiusSum Y := by
  unfold logRadiusSum
  refine Finset.sum_congr rfl fun i _ => finsum_congr fun c => ?_
  rw [meanRadius_gauge hC hL hn hY hv i c]
end
section
variable {L n k : ℕ} [NeZero L]
private theorem restrict_compact {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    (i : ℕ) (x : Vertex L n k i) :
    restrictVertexFunction i v x ∈ PeriodicLattice.compactGaugeGroup :=
  hv _
private def adjointLevelMap
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (v : Vertex L n k 0 → ComplexMatrix2) (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    LevelForms L n k →ₗ[ℝ] LevelForms L n k where
  toFun ξ := (adjointFormMap (hxor 0 (Nat.zero_le _)) v hv ξ.1, fun i =>
    adjointFormMap (hxor (i + 1) i.2) (restrictVertexFunction (i + 1) v) (restrict_compact hv _)
      (ξ.2 i))
  map_add' ξ ξ' := Prod.ext (map_add _ _ _) (funext fun i => map_add _ _ _)
  map_smul' c ξ := by
    refine Prod.ext (map_smul _ _ _) (funext fun i => ?_)
    exact map_smul (adjointFormMap (hxor (i + 1) i.2) (restrictVertexFunction (i + 1) v)
      (restrict_compact hv _)) c (ξ.2 i)
private theorem pairing_adjointLevelMap
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (v : Vertex L n k 0 → ComplexMatrix2) (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    (ξ ξ' : LevelForms L n k) :
    levelPairing (formValues (adjointLevelMap hxor v hv ξ))
        (formValues (adjointLevelMap hxor v hv ξ')) =
      levelPairing (formValues ξ) (formValues ξ') := by
  have h0 := pairing_adjointFormMap (hxor 0 (Nat.zero_le _)) v hv ξ.1 ξ'.1
  have hi := fun i : Fin k => pairing_adjointFormMap (hxor (i + 1) i.2)
    (restrictVertexFunction (i + 1) v) (restrict_compact hv _) (ξ.2 i) (ξ'.2 i)
  unfold levelPairing
  exact congrArg₂ (· + ·) (congrArg Complex.re h0)
    (Finset.sum_congr rfl fun i _ => congrArg Complex.re (hi i))
private theorem expMove_adjoint
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    (Z : ChainPoint L n k) (ξ : LevelForms L n k) :
    expMove (adjointLevelMap hxor v hv ξ) (gaugeTransformPoint v Z) =
      gaugeTransformPoint v (expMove ξ Z) := by
  refine chainPoint_ext ?_ (funext fun i => funext fun c => ?_)
  · funext b
    change PeriodicLattice.expTwist
        (adjointFormMap (hxor 0 (Nat.zero_le _)) v hv ξ.1 : Edge L n k 0 → ComplexMatrix2)
        (fun b => v b.source * Z.fine b * (v b.target)⁻¹) b =
      v b.source * PeriodicLattice.expTwist (ξ.1 : Edge L n k 0 → ComplexMatrix2) Z.fine b *
        (v b.target)⁻¹
    by_cases hb : b.IsPositivelyOriented
    · simp only [PeriodicLattice.expTwist, if_pos hb]
      rw [adjointFormMap_pos _ v hv _ hb, matExp_conjugateBy (isUnit_det_of_compact (hv _)),
        conj_mul_gauge _ _ (isUnit_det_of_compact (hv _))]
    · have hp := PeriodicLattice.Bond.opposite_isPositivelyOriented hb
      simp only [PeriodicLattice.expTwist, if_neg hb]
      rw [adjointFormMap_pos _ v hv _ hp, matExp_conjugateBy (isUnit_det_of_compact (hv _))]
      have e2 : b.opposite.source = b.target := rfl
      have e3 : b.opposite.target = b.source := rfl
      rw [e2, e3, conj_mul_gauge _ _ (isUnit_det_of_compact (hv _)),
        gauge_inv _ (isUnit_det_of_compact (hv _))]
  · change ComplexMatrix2.matExp (Complex.I • (adjointFormMap (hxor (i + 1) i.2)
        (restrictVertexFunction (i + 1) v) (restrict_compact hv _)
        (ξ.2 i) : Edge L n k (i + 1) → ComplexMatrix2) c.1) *
        (restrictVertexFunction (i + 1) v c.1.source * Z.noise i c *
          (restrictVertexFunction (i + 1) v c.1.source)⁻¹) =
      restrictVertexFunction (i + 1) v c.1.source *
        (ComplexMatrix2.matExp (Complex.I • (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1) *
          Z.noise i c) *
        (restrictVertexFunction (i + 1) v c.1.source)⁻¹
    rw [adjointFormMap_pos _ _ _ _ c.2,
      matExp_conjugateBy (isUnit_det_of_compact (restrict_compact hv _ _)),
      conj_mul_gauge _ _ (isUnit_det_of_compact (restrict_compact hv _ _))]
private def adjointVertexMap (v : Vertex L n k 0 → ComplexMatrix2)
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0 where
  toFun l := ⟨adjointVertexFn v l, fun x _ => conjugateBy_mem (hv x) (l.2 x (Set.mem_univ x))⟩
  map_add' l l' := Subtype.ext (funext fun x => conjugateBy_add _ _ _)
  map_smul' c l := Subtype.ext (funext fun x => conjugateBy_smul _ _ _)
private theorem pairing_adjointVertexMap (v : Vertex L n k 0 → ComplexMatrix2)
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) (l l' : vertexFunctionSpace L n k 0) :
    traceFinsumPairing (adjointVertexMap v hv l : Vertex L n k 0 → ComplexMatrix2)
        (adjointVertexMap v hv l' : Vertex L n k 0 → ComplexMatrix2) =
      traceFinsumPairing (l : Vertex L n k 0 → ComplexMatrix2)
        (l' : Vertex L n k 0 → ComplexMatrix2) := by
  unfold traceFinsumPairing
  exact finsum_congr fun x => halfTrace_conjugateBy (isUnit_det_of_compact (hv x)) _ _
private theorem adjointVertexMap_mem_top (v : Vertex L n k 0 → ComplexMatrix2)
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    (l : vertexFunctionSpace L n k 0) (hl : l ∈ topVanishingGauges L n k) :
    adjointVertexMap v hv l ∈ topVanishingGauges L n k := by
  intro y
  have h := hl y
  change ComplexMatrix2.conjugateBy (restrictVertexFunction k v y)
    (restrictVertexFunction k (l : Vertex L n k 0 → ComplexMatrix2) y) = 0
  rw [h]
  simp [ComplexMatrix2.conjugateBy]
private theorem gaugeOrbitMap_adjoint
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    {X : ChainPoint L n k}
    (hD : IsGaugeOrbitMap X (gaugeOrbitMap X))
    (hD' : IsGaugeOrbitMap (gaugeTransformPoint v X) (gaugeOrbitMap (gaugeTransformPoint v X)))
    (l : vertexFunctionSpace L n k 0) :
    gaugeOrbitMap (gaugeTransformPoint v X) (adjointVertexMap v hv l) =
      adjointLevelMap hxor v hv (gaugeOrbitMap X l) := by
  refine Prod.ext (edgeForm_ext fun b hb => ?_) (funext fun i => edgeForm_ext fun b hb => ?_)
  · have e1 : ((gaugeOrbitMap (gaugeTransformPoint v X) (adjointVertexMap v hv l)).1 :
        Edge L n k 0 → ComplexMatrix2) =
        covDiff (gaugeTransformPoint v X).fine (adjointVertexFn v l) :=
      congrArg Prod.fst (hD' (adjointVertexMap v hv l))
    have e2 : ((gaugeOrbitMap X l).1 : Edge L n k 0 → ComplexMatrix2) = covDiff X.fine l :=
      congrArg Prod.fst (hD l)
    change ((gaugeOrbitMap (gaugeTransformPoint v X) (adjointVertexMap v hv l)).1 :
        Edge L n k 0 → ComplexMatrix2) b =
      (adjointFormMap (hxor 0 (Nat.zero_le _)) v hv (gaugeOrbitMap X l).1 :
        Edge L n k 0 → ComplexMatrix2) b
    rw [adjointFormMap_pos _ v hv _ hb, e1, e2]
    simp only [covDiff, extendOddly_pos _ hb]
    change ComplexMatrix2.conjugateBy (v b.source * X.fine b * (v b.target)⁻¹)
        (ComplexMatrix2.conjugateBy (v b.target) ((l : Vertex L n k 0 → ComplexMatrix2) b.target)) -
        ComplexMatrix2.conjugateBy (v b.source) ((l : Vertex L n k 0 → ComplexMatrix2) b.source) = _
    rw [conjugateBy_gauge _ (isUnit_det_of_compact (hv _)), conjugateBy_sub]
  · have e1 : ((gaugeOrbitMap (gaugeTransformPoint v X) (adjointVertexMap v hv l)).2 i :
        Edge L n k (i + 1) → ComplexMatrix2) =
        (gaugeOrbitValues (gaugeTransformPoint v X) (adjointVertexMap v hv l)).2 i :=
      congrFun (congrArg Prod.snd (hD' (adjointVertexMap v hv l))) i
    have e2 : ((gaugeOrbitMap X l).2 i : Edge L n k (i + 1) → ComplexMatrix2) =
        (gaugeOrbitValues X l).2 i :=
      congrFun (congrArg Prod.snd (hD l)) i
    change ((gaugeOrbitMap (gaugeTransformPoint v X) (adjointVertexMap v hv l)).2 i :
        Edge L n k (i + 1) → ComplexMatrix2) b =
      (adjointFormMap (hxor (i + 1) i.2) (restrictVertexFunction (i + 1) v) (restrict_compact hv _)
        ((gaugeOrbitMap X l).2 i) : Edge L n k (i + 1) → ComplexMatrix2) b
    rw [adjointFormMap_pos _ _ _ _ hb, e1, e2]
    simp only [gaugeOrbitValues, extendOddly_pos _ hb, dif_pos hb]
    change ComplexMatrix2.conjugateBy (restrictVertexFunction (i + 1) v b.source * X.noise i ⟨b, hb⟩ *
          (restrictVertexFunction (i + 1) v b.source)⁻¹)
        (ComplexMatrix2.conjugateBy (restrictVertexFunction (i + 1) v b.source)
          (restrictVertexFunction (i + 1) (l : Vertex L n k 0 → ComplexMatrix2) b.source)) -
        ComplexMatrix2.conjugateBy (restrictVertexFunction (i + 1) v b.source)
          (restrictVertexFunction (i + 1) (l : Vertex L n k 0 → ComplexMatrix2) b.source) = _
    rw [conjugateBy_gauge _ (isUnit_det_of_compact (restrict_compact hv _ _)), conjugateBy_sub]
private theorem gaugeTransform_top {v : Vertex L n k 0 → ComplexMatrix2}
    (hv1 : ∀ y : Vertex L n k k, restrictVertexFunction k v y = 1)
    (F : Edge L n k k → ComplexMatrix2) :
    PeriodicLattice.gaugeTransform (restrictVertexFunction k v) F = F := by
  funext b
  simp [PeriodicLattice.gaugeTransform, hv1]
variable (hC : ContourMeanGaugeCovariant) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hn : 0 < n)
include hC hL hn in
private theorem topDeriv_adjoint
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    (hv1 : ∀ y : Vertex L n k k, restrictVertexFunction k v y = 1) {X : ChainPoint L n k}
    (hX : IsCompactValued X)
    (near : ∀ ξ : LevelForms L n k, ∀ᶠ r in 𝓝 (0 : ℝ), IsCompactValued (expMove (r • ξ) X))
    (dX : ∀ (ξ : LevelForms L n k) (b : Edge L n k k), b.IsPositivelyOriented →
      HasDerivAt (fun r : ℝ => levelField (expMove (r • ξ) X) k b)
        ((Complex.I • tangentTransport X ξ k b) * levelField X k b) 0)
    (dX' : ∀ (ξ : LevelForms L n k) (b : Edge L n k k), b.IsPositivelyOriented →
      HasDerivAt (fun r : ℝ => levelField (expMove (r • ξ) (gaugeTransformPoint v X)) k b)
        ((Complex.I • tangentTransport (gaugeTransformPoint v X) ξ k b) *
          levelField (gaugeTransformPoint v X) k b) 0)
    (hQ : IsTopDeriv X (topDeriv X))
    (hQ' : IsTopDeriv (gaugeTransformPoint v X) (topDeriv (gaugeTransformPoint v X)))
    (ξ : LevelForms L n k) :
    topDeriv (gaugeTransformPoint v X) (adjointLevelMap hxor v hv ξ) = topDeriv X ξ := by
  refine edgeForm_ext fun b hb => ?_
  rw [hQ', hQ]
  have ev : (fun r : ℝ => levelField (expMove (r • adjointLevelMap hxor v hv ξ)
      (gaugeTransformPoint v X)) k b) =ᶠ[𝓝 0]
      fun r : ℝ => levelField (expMove (r • ξ) X) k b := by
    filter_upwards [near ξ] with r hr
    rw [← map_smul, expMove_adjoint hxor hv,
      levelField_gauge hC hL hn (fun j h => hr.2 j h.le) hv k le_rfl, gaugeTransform_top hv1]
  have h3 := (dX' (adjointLevelMap hxor v hv ξ) b hb).congr_of_eventuallyEq ev.symm
  have h4 := (dX ξ b hb).unique h3
  have hW : levelField (gaugeTransformPoint v X) k = levelField X k := by
    rw [levelField_gauge hC hL hn (fun j h => hX.2 j h.le) hv k le_rfl, gaugeTransform_top hv1]
  rw [hW] at h4
  have hu : IsUnit (levelField X k b).det :=
    isUnit_det_of_compact ((hX.2 k le_rfl).1 b (Set.mem_univ _))
  exact (cancel_I_smul_mul hu h4).symm
private theorem fibreMove_noise_last (X : ChainPoint L n k) (η : LevelForms L n k) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) (hi : i.val + 1 = k) :
    (fibreMove X η).noise i c =
      levelField X (i + 1) c.1 * (normalizedMean (levelField (expMove η X) i) c.1)⁻¹ := by
  unfold fibreMove
  exact if_pos hi
private theorem fibreMove_noise_other (X : ChainPoint L n k) (η : LevelForms L n k) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) (hi : ¬i.val + 1 = k) :
    (fibreMove X η).noise i c = (expMove η X).noise i c := by
  unfold fibreMove
  exact if_neg hi
private theorem levelField_fibreMove (X : ChainPoint L n k) (η : LevelForms L n k) :
    ∀ j, j < k → levelField (fibreMove X η) j = levelField (expMove η X) j := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.levelField_fibreMove_of_lt <;> assumption
include hC hL hn in
private theorem fibreMove_gauge
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    (hv1 : ∀ y : Vertex L n k k, restrictVertexFunction k v y = 1) {X : ChainPoint L n k}
    (hX : IsCompactValued X) (η : LevelForms L n k) (hZ : IsCompactValued (expMove η X)) :
    fibreMove (gaugeTransformPoint v X) (adjointLevelMap hxor v hv η) =
      gaugeTransformPoint v (fibreMove X η) := by
  have hm := expMove_adjoint hxor hv X η
  refine chainPoint_ext ?_ (funext fun i => funext fun c => ?_)
  · change (expMove (adjointLevelMap hxor v hv η) (gaugeTransformPoint v X)).fine = _
    rw [hm]
    rfl
  · change _ = restrictVertexFunction (i + 1) v c.1.source * (fibreMove X η).noise i c *
      (restrictVertexFunction (i + 1) v c.1.source)⁻¹
    by_cases hi : i.val + 1 = k
    · have hone : ∀ (j : ℕ), j = k → ∀ y : Vertex L n k j, restrictVertexFunction j v y = 1 := by
        rintro j rfl y
        exact hv1 y
      have hg1 : restrictVertexFunction (i + 1) v c.1.source = 1 := hone _ hi _
      have hh1 : restrictVertexFunction (i + 1) v c.1.target = 1 := hone _ hi _
      have hav : normalizedMean (levelField (expMove (adjointLevelMap hxor v hv η)
            (gaugeTransformPoint v X)) i) c.1 =
          normalizedMean (levelField (expMove η X) i) c.1 := by
        rw [hm, levelField_gauge hC hL hn (fun j h => hZ.2 j h.le) hv i i.2.le]
        have hcov := (hC L hL n k i hn i.2 _ (fieldsIn_complex_of_compact (hZ.2 i i.2.le))
          (restrictVertexFunction i v) (fun x => det_of_compact (hv _)) c.1 c.2).2.2
        rw [restrict_toSublattice v i.2.le, restrict_toSublattice v i.2.le, hg1, hh1] at hcov
        rw [hcov]
        simp
      have htop : levelField (gaugeTransformPoint v X) (i + 1) c.1 = levelField X (i + 1) c.1 := by
        rw [levelField_gauge hC hL hn (fun j h => hX.2 j h.le) hv (i + 1) i.2]
        simp [PeriodicLattice.gaugeTransform, hg1, hh1]
      rw [fibreMove_noise_last _ _ i c hi, fibreMove_noise_last X η i c hi, hav, htop, hg1]
      simp
    · rw [fibreMove_noise_other _ _ i c hi, fibreMove_noise_other X η i c hi, hm]
      rfl
private theorem fibreSecondDeriv_diag (a : ℝ) (X : ChainPoint L n k) (ξ : LevelForms L n k) :
    fibreSecondDeriv a X ξ ξ =
      deriv (deriv fun u : ℝ => chainAction a (fibreMove X (u • ξ))) 0 := by
  have e₀ : (fun s : ℝ => deriv (fun t : ℝ => chainAction a (fibreMove X (s • ξ + t • ξ))) 0) =
      deriv fun u : ℝ => chainAction a (fibreMove X (u • ξ)) := by
    funext s
    have e : (fun t : ℝ => chainAction a (fibreMove X (s • ξ + t • ξ))) =
        fun t : ℝ => (fun u : ℝ => chainAction a (fibreMove X (u • ξ))) (s + t) := by
      funext t
      simp only [add_smul]
    rw [e]
    have h := deriv_comp_const_add (fun u : ℝ => chainAction a (fibreMove X (u • ξ))) s 0
    rw [add_zero] at h
    exact h
  rw [fibreSecondDeriv, e₀]
include hC hL hn in
private theorem fibreHessian_adjoint
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hk : 1 ≤ k) (a : ℝ)
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    (hv1 : ∀ y : Vertex L n k k, restrictVertexFunction k v y = 1) {X : ChainPoint L n k}
    (hX : IsCompactValued X)
    (near : ∀ ξ : LevelForms L n k, ∀ᶠ r in 𝓝 (0 : ℝ), IsCompactValued (expMove (r • ξ) X))
    (hs : IsFibreHessian a X (fibreHessian a X))
    (hs' : IsFibreHessian a (gaugeTransformPoint v X) (fibreHessian a (gaugeTransformPoint v X)))
    (ξ : LinearMap.ker (topDeriv X))
    (h : adjointLevelMap hxor v hv ξ ∈ LinearMap.ker (topDeriv (gaugeTransformPoint v X))) :
    fibreHessian a (gaugeTransformPoint v X) ⟨adjointLevelMap hxor v hv ξ, h⟩ =
      fibreHessian a X ξ := by
  rw [hs' ⟨_, h⟩, hs ξ, fibreSecondDeriv_diag, fibreSecondDeriv_diag]
  have ev : (fun u : ℝ => chainAction a
        (fibreMove (gaugeTransformPoint v X)
          (u • adjointLevelMap hxor v hv (ξ : LevelForms L n k)))) =ᶠ[𝓝 0]
      fun u : ℝ => chainAction a (fibreMove X (u • (ξ : LevelForms L n k))) := by
    filter_upwards [near ξ] with r hr
    rw [← map_smul, fibreMove_gauge hC hL hn hxor hv hv1 hX _ hr]
    refine chainAction_gauge hC hL hn hg a hk (fun j hj => ?_) hv
    rw [levelField_fibreMove X _ j hj]
    exact hr.2 j hj.le
  exact ev.deriv.deriv_eq
end
section
variable {L n k : ℕ}
private theorem levelFormsEuclidean_of (hF : FiniteSideFormSpaces)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) : LevelFormsEuclidean L n k := by apply _root_.YangMills.SharedProofs.p14283 <;> assumption
private theorem levelGaussianNumber_eq (hA : LevelFormsEuclidean L n k)
    (hC : EdgeFormsEuclidean L n k k) (M : LevelForms L n k →ₗ[ℝ] edgeFormSpace L n k k)
    (T : QuadraticForm ℝ (LinearMap.ker M)) :
    levelGaussianNumber M T =
      (haveI := hA.1
       haveI := hC.1
       constrainedGaussianNumberOfCores hA.2.choose hC.2.choose M T) := by
  unfold levelGaussianNumber
  exact dif_pos ⟨hA, hC⟩
private theorem sliceOrbitVolume_eq (h₀ : VertexFunctionsEuclidean L n k 0) {Y : Type}
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (X : ChainPoint L n k) (l : LevelForms L n k →ₗ[ℝ] Y) :
    sliceOrbitVolume X l =
      (haveI := h₀.1
       letI := h₀.2.choose.toNormedAddCommGroup
       letI := InnerProductSpace.ofCore h₀.2.choose.toCore
       absDetOfMap (l ∘ₗ gaugeOrbitMap X ∘ₗ (topVanishingGauges L n k).subtype)) := by
  unfold sliceOrbitVolume
  exact dif_pos h₀
variable [NeZero L]
private theorem chainLogWeight_gauge (hG : LinearConstraint.GaugeChangeGaussianIdentity)
    (hC : ContourMeanGaugeCovariant)
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (hc : ExpMoveNearCompactPoint) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hk : 1 ≤ k)
    (hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hA : LevelFormsEuclidean L n k) (hCk : EdgeFormsEuclidean L n k k)
    (h₀ : VertexFunctionsEuclidean L n k 0) (hkS : VertexFunctionsEuclidean L n k k) (a : ℝ)
    {X : ChainPoint L n k} {v : Vertex L n k 0 → ComplexMatrix2} (hX : IsCompactValued X)
    (hX' : IsCompactValued (gaugeTransformPoint v X))
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    (hv1 : ∀ y : Vertex L n k k, restrictVertexFunction k v y = 1) (mX : ChainLinearMapsAt X)
    (mX' : ChainLinearMapsAt (gaugeTransformPoint v X)) (hT0 : ∀ ξ, 0 ≤ fibreHessian a X ξ)
    (hTnull : ∀ ξ : LinearMap.ker (topDeriv X), fibreHessian a X ξ = 0 ↔
      (ξ : LevelForms L n k) ∈ (topVanishingGauges L n k).map (gaugeOrbitMap X))
    {Y Y' : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] [FiniteDimensional ℝ Y']
    (l : LevelForms L n k →ₗ[ℝ] Y) (l' : LevelForms L n k →ₗ[ℝ] Y')
    (hl : IsTransversalSlice X l) (hl' : IsTransversalSlice (gaugeTransformPoint v X) l') :
    chainLogWeight a X l = chainLogWeight a (gaugeTransformPoint v X) l' := by
  classical
  haveI := hA.1
  haveI := hCk.1
  haveI := h₀.1
  haveI := hkS.1
  have iA : IsLevelCore hA.2.choose := hA.2.choose_spec
  have iG : IsVertexPairingCore h₀.2.choose := h₀.2.choose_spec
  have iGc : IsVertexPairingCore hkS.2.choose := hkS.2.choose_spec
  have cX := hc a L hL k n hk hn X hX
  have cX' := hc a L hL k n hk hn _ hX'
  have hQA := topDeriv_adjoint hC hL hn hxor hv hv1 hX (fun ξ => (cX.2 ξ).1)
    (fun ξ b hb => (cX.2 ξ).2 k le_rfl b hb) (fun ξ b hb => (cX'.2 ξ).2 k le_rfl b hb)
    mX.topDeriv_spec mX'.topDeriv_spec
  have hDA := gaugeOrbitMap_adjoint hxor hv mX.orbit_spec mX'.orbit_spec
  have hAin : ∀ x y, hA.2.choose.inner (adjointLevelMap hxor v hv x) (adjointLevelMap hxor v hv y) =
      hA.2.choose.inner x y := fun x y => by
    rw [iA, iA]
    exact pairing_adjointLevelMap hxor v hv x y
  have hgin : ∀ x y, h₀.2.choose.inner (adjointVertexMap v hv x) (adjointVertexMap v hv y) =
      h₀.2.choose.inner x y := fun x y => by
    rw [iG, iG]
    exact congrArg Complex.re (pairing_adjointVertexMap v hv x y)
  let l₂ : LevelForms L n k →ₗ[ℝ] Y' := l' ∘ₗ adjointLevelMap hxor v hv
  obtain ⟨hbij, hvol⟩ := absDet_isometry h₀.2.choose (topVanishingGauges L n k)
    (adjointVertexMap v hv) hgin
    (adjointVertexMap_mem_top v hv) (l₂ ∘ₗ gaugeOrbitMap X)
    (l' ∘ₗ gaugeOrbitMap (gaugeTransformPoint v X))
    (fun x => by
      change l' (gaugeOrbitMap (gaugeTransformPoint v X) (adjointVertexMap v hv x)) =
        l' (adjointLevelMap hxor v hv (gaugeOrbitMap X x))
      rw [hDA]) hl'
  have hsl : IsTransversalSlice X l₂ := hbij
  have hK : topVanishingGauges L n k = LinearMap.ker (restrictToTopLinear L n k) := by
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      exact Subtype.ext ((mX.restrict_apply x).trans (funext h))
    · intro h y
      have h1 := mX.restrict_apply x
      rw [h] at h1
      exact (congrFun h1 y).symm
  have e1 := gaussian_slice_indep hG hA.2.choose hCk.2.choose h₀.2.choose hkS.2.choose
    (gaugeOrbitMap X)
    (topCovDiffLinear (levelField X k)) (topDeriv X) (restrictToTopLinear L n k)
    (extendFromTopLinear L n k) (fibreHessian a X) (topVanishingGauges L n k) hK
    mX.topDeriv_surjective
    (fun g x => by rw [iG, iGc, mX.extend_pairing]) mX.restrict_extend mX.topDeriv_orbit
    mX.orbit_injective hT0 hTnull l l₂ hl hsl
  have e2 := constrainedGaussian_isometry hA.2.choose hCk.2.choose (topDeriv X)
    (topDeriv (gaugeTransformPoint v X)) (adjointLevelMap hxor v hv) hAin hQA
    (fibreHessian a X + (normSqForm l₂).comp (LinearMap.ker (topDeriv X)).subtype)
    (fibreHessian a (gaugeTransformPoint v X) +
      (normSqForm l').comp (LinearMap.ker (topDeriv (gaugeTransformPoint v X))).subtype)
    (fun ξ h => by
      have hf := fibreHessian_adjoint hC hL hn hg hxor hk a hv hv1 hX (fun ξ => (cX.2 ξ).1)
        cX.1 cX'.1 ξ h
      simp only [add_apply, QuadraticMap.comp_apply]
      rw [hf]
      rfl)
  have key : levelGaussianNumber (topDeriv X)
        (fibreHessian a X + (normSqForm l).comp (LinearMap.ker (topDeriv X)).subtype) *
        sliceOrbitVolume X l =
      levelGaussianNumber (topDeriv (gaugeTransformPoint v X))
        (fibreHessian a (gaugeTransformPoint v X) +
          (normSqForm l').comp (LinearMap.ker (topDeriv (gaugeTransformPoint v X))).subtype) *
        sliceOrbitVolume (gaugeTransformPoint v X) l' := by
    rw [levelGaussianNumber_eq hA hCk, levelGaussianNumber_eq hA hCk, sliceOrbitVolume_eq h₀,
      sliceOrbitVolume_eq h₀]
    refine e1.trans ?_
    refine congrArg₂ (· * ·) e2.symm hvol.symm
  unfold chainLogWeight
  rw [key, logRadiusSum_gauge hC hL hn (fun j h => hX.2 j h.le) hv]
end
private theorem xor_opposite_of (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.xor_isPositivelyOriented_opposite <;> assumption
theorem chainLogWeightIndependent (hm : ChainMapsAtMinimizers) (hf : FibreHessianAtMinimizer)
    (ho : MinimizersFormOneGaugeOrbit) (hc : ExpMoveNearCompactPoint)
    (hG : LinearConstraint.GaugeChangeGaussianIdentity) (hC : ContourMeanGaugeCovariant)
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (hSp : FiniteSideFormSpaces)
    (hSite : FormOnAFibre.VertexFunctionsAreEuclidean.Statement) :
    ChainLogWeightIndependent := by
  intro a ha L hL k n hk hn
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  have hxor : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    xor_opposite_of hb hL hn
  have hA : LevelFormsEuclidean L n k := levelFormsEuclidean_of hSp hL hn
  have hCk : EdgeFormsEuclidean L n k k := by
    obtain ⟨-, f, -, c, h⟩ := hSp L n k k hL hn le_rfl
    exact ⟨f, c, fun B B' => by rw [h B B', Complex.ofReal_re]⟩
  have h₀ : VertexFunctionsEuclidean L n k 0 := hSite L n k 0 hL hn (Nat.zero_le k)
  have hkS : VertexFunctionsEuclidean L n k k := hSite L n k k hL hn le_rfl
  filter_upwards [hm a ha L hL k n hk hn, hf a ha L hL k n hk hn, ho a ha L hL k n hk hn]
    with V h1 h2 h3 W hW X X' hX hX' Y Y' _ _ _ _ _ _ l l' hl hl'
  obtain ⟨v, hv, hv1, rfl⟩ := h3 W hW X X' hX hX'
  have f := h2 W hW X hX
  exact chainLogWeight_gauge hG hC hg hc hL hn hk hxor hA hCk h₀ hkS a hX.compact hX'.compact hv hv1
    (h1 W hW X hX) (h1 W hW _ hX') f.1 f.2 l l' hl hl'
end RunningCouplingSlope.LogWeightIndependence
end YangMills.Construction
end
