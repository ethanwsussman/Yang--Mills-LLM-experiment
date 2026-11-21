import YangMills.Construction.Towers.CovariantDifferenceOfAFieldIsLocalWithEntireKernels
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.CovDiffKernelProof
open PeriodicOperators Matrices
section MatrixExponential
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
def lieMatrix (w : Fin 3 → ℂ) : ComplexMatrix2 :=
  Complex.I • ∑ a, w a • ComplexMatrix2.pauliFamily a
theorem differentiable_lieMatrix : Differentiable ℂ lieMatrix := by
  have hsum : Differentiable ℂ fun w : Fin 3 → ℂ => ∑ a, w a • ComplexMatrix2.pauliFamily a :=
    Differentiable.fun_sum fun a _ => (differentiable_apply a).smul_const _
  exact (differentiable_const Complex.I).smul hsum
theorem differentiable_exp_lieMatrix :
    Differentiable ℂ fun w => (NormedSpace.exp (lieMatrix w) : ComplexMatrix2) := fun w =>
  ((NormedSpace.exp_analytic (𝕂 := ℂ) (lieMatrix w)).differentiableAt).comp w
    (differentiable_lieMatrix w)
theorem differentiable_exp_neg_lieMatrix :
    Differentiable ℂ fun w => (NormedSpace.exp (-lieMatrix w) : ComplexMatrix2) := fun w =>
  ((NormedSpace.exp_analytic (𝕂 := ℂ) (-lieMatrix w)).differentiableAt).comp w
    (differentiable_lieMatrix w).neg
def pauliForm (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
  map_add' X Y := by fin_cases a <;> simp <;> ring
  map_smul' c X := by fin_cases a <;> simp <;> ring
theorem pauliCoeff_eq_pauliForm {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a X = pauliForm a X := by
  unfold pauliCoeff
  rw [dif_pos hX]
  rfl
def conjDiff (P Q : ComplexMatrix2) (w : Fin 3 → ℂ) : ComplexMatrix2 :=
  ComplexMatrix2.conjugateBy (ComplexMatrix2.matExp (lieMatrix w)) P - Q
theorem conjDiff_eq (P Q : ComplexMatrix2) (w : Fin 3 → ℂ) :
    conjDiff P Q w =
      NormedSpace.exp (lieMatrix w) * P * NormedSpace.exp (-lieMatrix w) - Q := by
  unfold conjDiff ComplexMatrix2.conjugateBy ComplexMatrix2.matExp
  rw [Matrix.exp_neg]
theorem differentiable_conjDiff (P Q : ComplexMatrix2) :
    Differentiable ℂ (conjDiff P Q) := by
  have hfun : conjDiff P Q = fun w =>
      NormedSpace.exp (lieMatrix w) * P * NormedSpace.exp (-lieMatrix w) - Q :=
    funext (conjDiff_eq P Q)
  rw [hfun]
  exact ((differentiable_exp_lieMatrix.mul_const P).mul
    differentiable_exp_neg_lieMatrix).sub_const Q
theorem differentiable_pauliForm_conjDiff (a : Fin 3) (P Q : ComplexMatrix2) :
    Differentiable ℂ fun w => pauliForm a (conjDiff P Q w) :=
  (LinearMap.toContinuousLinearMap (pauliForm a)).differentiable.comp
    (differentiable_conjDiff P Q)
end MatrixExponential
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by
  change Matrix.trace _ = 0
  fin_cases a <;>
    simp [ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
      OneLoop.pauliZ, Matrix.trace_fin_two]
theorem conjDiff_mem_traceless {P Q : ComplexMatrix2} (hP : P ∈ ComplexMatrix2.traceless)
    (hQ : Q ∈ ComplexMatrix2.traceless) (w : Fin 3 → ℂ) :
    conjDiff P Q w ∈ ComplexMatrix2.traceless := by
  refine ComplexMatrix2.traceless.sub_mem ?_ hQ
  have hunit : IsUnit (ComplexMatrix2.matExp (lieMatrix w)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)
  change Matrix.trace _ = 0
  have htr : Matrix.trace P = 0 := hP
  unfold ComplexMatrix2.conjugateBy
  rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ hunit, one_mul, htr]
theorem ofPauliCoeffs_indicator {σ : Type} (ι : Fin 3 × σ)
    (dec : ∀ κ : Fin 3 × σ, Decidable (κ = ι)) (y : σ) (dec' : Decidable (y = ι.2)) :
    ofPauliCoeffs (fun κ : Fin 3 × σ => @ite _ (κ = ι) (dec κ) (1 : ℂ) 0) y =
      @ite _ (y = ι.2) dec' (ComplexMatrix2.pauliFamily ι.1) 0 := by
  unfold ofPauliCoeffs
  by_cases hy : y = ι.2
  · rw [if_pos hy, Finset.sum_eq_single ι.1]
    · beta_reduce
      rw [if_pos (show (ι.1, y) = ι from Prod.ext rfl hy), one_smul]
    · intro a _ ha
      beta_reduce
      rw [if_neg (fun he : (a, y) = ι => ha (congrArg Prod.fst he)), zero_smul]
    · simp
  · rw [if_neg hy]
    refine Finset.sum_eq_zero fun a _ => ?_
    beta_reduce
    rw [if_neg (fun he : (a, y) = ι => hy (congrArg Prod.snd he)), zero_smul]
variable {L : ℕ}
def vertexDelta (ι : Fin 3 × FullSpace.Vertex L 0 0) (y : FullSpace.Vertex L 0 0) :
    ComplexMatrix2 :=
  open Classical in if y = ι.2 then ComplexMatrix2.pauliFamily ι.1 else 0
theorem vertexDelta_mem_traceless (ι : Fin 3 × FullSpace.Vertex L 0 0)
    (y : FullSpace.Vertex L 0 0) : vertexDelta ι y ∈ ComplexMatrix2.traceless := by
  unfold vertexDelta
  split_ifs
  · exact pauliFamily_mem_traceless _
  · exact ComplexMatrix2.traceless.zero_mem
theorem expField_positive (ζ : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.expField ζ b.1 = ComplexMatrix2.matExp (lieMatrix fun c => ζ (c, b)) := by
  unfold FullSpace.expField FullSpace.expTwist
  rw [if_pos b.2, mul_one]
  change ComplexMatrix2.matExp (Complex.I • FullSpace.extendOddly _ b.1) = _
  unfold FullSpace.extendOddly
  rw [if_pos b.2]
  beta_reduce
  rw [dif_pos b.2]
  rfl
theorem ofCoeffs_indicator (ι : Fin 3 × FullSpace.Vertex L 0 0)
    (dec : ∀ κ : Fin 3 × FullSpace.Vertex L 0 0, Decidable (κ = ι)) :
    (vertexCoordinate (FullSpace.Vertex L 0 0)).ofCoeffs
      (fun κ => @ite _ (κ = ι) (dec κ) (1 : ℂ) 0) = vertexDelta ι :=
  funext fun y => ofPauliCoeffs_indicator ι dec y _
open CovDiffTransposes (matrixKernel) in
theorem matrixKernel_eq (r r' : PauliComponentsOfSymmetricKernel)
    (M : (r.space.index → ComplexMatrix2) → r'.space.index → ComplexMatrix2) (ι' : r'.Index)
    (ι : r.Index) (f : r.space.index → ComplexMatrix2)
    (hf : ∀ dec : ∀ κ : r.Index, Decidable (κ = ι),
      r.ofCoeffs (fun κ => @ite _ (κ = ι) (dec κ) (1 : ℂ) 0) = f) :
    matrixKernel r r' M ι' ι = r'.coeffs (M f) ι' := by
  unfold matrixKernel
  rw [hf]
theorem kernel_eq_pauliCoeff (ζ : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ)
    (ι' : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0))
    (ι : Fin 3 × FullSpace.Vertex L 0 0) :
    FullSpace.covDiffKernelOfField ζ ι' ι = pauliCoeff ι'.1
      (FullSpace.covDiff (FullSpace.expField ζ) (vertexDelta ι) ι'.2.1) :=
  matrixKernel_eq (vertexCoordinate (FullSpace.Vertex L 0 0)) (FullSpace.edgePauliCoordinates L 0 0)
    (FullSpace.covDiff (FullSpace.expField ζ)) ι' ι (vertexDelta ι)
    (ofCoeffs_indicator ι)
theorem kernel_eq (ζ : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ)
    (ι' : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0))
    (ι : Fin 3 × FullSpace.Vertex L 0 0) :
    FullSpace.covDiffKernelOfField ζ ι' ι =
      pauliForm ι'.1 (conjDiff (vertexDelta ι ι'.2.1.terminal) (vertexDelta ι ι'.2.1.initial)
        fun c => ζ (c, ι'.2)) := by
  rw [kernel_eq_pauliCoeff,
    ← pauliCoeff_eq_pauliForm
      (conjDiff_mem_traceless (vertexDelta_mem_traceless _ _) (vertexDelta_mem_traceless _ _) _)]
  congr 1
  unfold FullSpace.covDiff FullSpace.extendOddly
  rw [if_pos ι'.2.2]
  beta_reduce
  rw [expField_positive ζ ι'.2]
  rfl
theorem kernel_eq_zero (ζ : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ)
    (ι' : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0))
    (ι : Fin 3 × FullSpace.Vertex L 0 0) (h₁ : ι.2 ≠ ι'.2.1.terminal)
    (h₂ : ι.2 ≠ ι'.2.1.initial) :
    FullSpace.covDiffKernelOfField ζ ι' ι = 0 := by
  rw [kernel_eq]
  have e₁ : vertexDelta ι ι'.2.1.terminal = 0 := if_neg fun he => h₁ he.symm
  have e₂ : vertexDelta ι ι'.2.1.initial = 0 := if_neg fun he => h₂ he.symm
  rw [e₁, e₂]
  simp [conjDiff, ComplexMatrix2.conjugateBy]
theorem exists_entire_kernel (ι' : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0))
    (ι : Fin 3 × FullSpace.Vertex L 0 0)
    {S : Set (Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0))}
    {l : ℕ} (e : Fin l ≃ S) (hS : ∀ c, (c, ι'.2) ∈ S) :
    ∃ g : Coordinates.ComplexCoordinates l → ℂ, Differentiable ℂ g ∧
      ∀ ζ : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ,
        FullSpace.covDiffKernelOfField ζ ι' ι = g fun j => ζ (e j) := by
  refine ⟨fun z => pauliForm ι'.1 (conjDiff (vertexDelta ι ι'.2.1.terminal)
    (vertexDelta ι ι'.2.1.initial) fun c => z (e.symm ⟨(c, ι'.2), hS c⟩)), ?_, fun ζ => ?_⟩
  · exact (differentiable_pauliForm_conjDiff _ _ _).comp
      (differentiable_pi.2 fun c => differentiable_apply _)
  · rw [kernel_eq]
    simp
theorem isHolomorphicIn_of_differentiable {l : ℕ} {g : Coordinates.ComplexCoordinates l → ℂ}
    (hg : Differentiable ℂ g) {O : Set (Coordinates.ComplexCoordinates l)} (hO : IsOpen O) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => g z := by
  refine ⟨hO, (continuous_pi fun _ => hg.continuous).continuousOn, fun a _ j => ?_⟩
  refine Filter.Eventually.of_forall fun ζ => differentiableAt_pi.2 fun _ => ?_
  exact (hg _).comp ζ (by fun_prop)
theorem isOpen_openPolydisk {l : ℕ} (ρ : ℝ) : IsOpen
    (Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk
      (0 : Coordinates.ComplexCoordinates l) ρ) := by
  have hset : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk
      (0 : Coordinates.ComplexCoordinates l) ρ =
        ⋂ j, {z : Coordinates.ComplexCoordinates l |
          ‖z j - (0 : Coordinates.ComplexCoordinates l) j‖ < ρ} := by
    ext z
    simp [Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk]
  rw [hset]
  exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
theorem meshAt_zero_zero : meshAt L 0 0 = 1 := by simp [meshAt]
def latticePoint (k : Fin 4 → ℤ) : FullSpace.Vertex L 0 0 :=
  ⟨fun μ => (k μ : ℝ) * meshAt L 0 0, k, fun _ => rfl⟩
theorem exists_vertex_of_intShift (k : Fin 4 → ℤ) (x : FullSpace.Vertex L 0 0) :
    ∃ x' : FullSpace.Vertex L 0 0, (x' : InfiniteLattice.AmbientSpace) = intShift k x := by
  obtain ⟨j, hj⟩ := x.2
  refine ⟨latticePoint (j + k), funext fun μ => ?_⟩
  simp [latticePoint, intShift, castVec, hj μ, meshAt_zero_zero]
theorem coe_vertexImage (k : Fin 4 → ℤ) (x : FullSpace.Vertex L 0 0) :
    ((FullSpace.vertexImage (intShift k) x : FullSpace.Vertex L 0 0) :
      InfiniteLattice.AmbientSpace) = intShift k x :=
  Classical.epsilon_spec (exists_vertex_of_intShift k x)
theorem vertexImage_sub (k : Fin 4 → ℤ) (x y : FullSpace.Vertex L 0 0) :
    FullSpace.vertexImage (intShift k) y - FullSpace.vertexImage (intShift k) x = y - x := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_sub, coe_vertexImage, intShift, add_sub_add_right_eq_sub]
theorem vertexImage_neg_vertexImage (k : Fin 4 → ℤ) (x : FullSpace.Vertex L 0 0) :
    FullSpace.vertexImage (intShift (-k)) (FullSpace.vertexImage (intShift k) x) = x := by
  apply Subtype.ext
  rw [coe_vertexImage]
  rw [coe_vertexImage]
  funext μ
  simp [intShift, castVec]
theorem vertexImage_injective (k : Fin 4 → ℤ) :
    Function.Injective (FullSpace.vertexImage (a := meshAt L 0 0) (intShift k)) :=
  Function.LeftInverse.injective (vertexImage_neg_vertexImage k)
theorem edgeImage_endpoints (k : Fin 4 → ℤ) (b : FullSpace.Edge L 0 0) :
    (FullSpace.edgeImage (intShift k) b).initial =
        FullSpace.vertexImage (intShift k) b.initial ∧
      (FullSpace.edgeImage (intShift k) b).terminal =
        FullSpace.vertexImage (intShift k) b.terminal := by
  refine Classical.epsilon_spec (p := fun b' : FullSpace.Edge L 0 0 =>
    b'.initial = FullSpace.vertexImage (intShift k) b.initial ∧
      b'.terminal = FullSpace.vertexImage (intShift k) b.terminal) ?_
  refine ⟨⟨FullSpace.vertexImage (intShift k) b.initial,
    FullSpace.vertexImage (intShift k) b.terminal, ?_⟩, rfl, rfl⟩
  rw [vertexImage_sub]
  exact b.isAdjacent
theorem shiftEdge_val (k : Fin 4 → ℤ) (b : PeriodicOperators.PosEdge L 0 0) :
    (shiftEdge k b).1 = FullSpace.edgeImage (intShift k) b.1 := by
  refine Classical.epsilon_spec (p := fun b' : PeriodicOperators.PosEdge L 0 0 =>
    b'.1 = FullSpace.edgeImage (intShift k) b.1) ?_
  refine ⟨⟨FullSpace.edgeImage (intShift k) b.1, ?_⟩, rfl⟩
  obtain ⟨μ, hμ⟩ := b.2
  refine ⟨μ, ?_⟩
  rw [(edgeImage_endpoints k b.1).1, (edgeImage_endpoints k b.1).2, vertexImage_sub]
  exact hμ
theorem shiftEdge_terminal (k : Fin 4 → ℤ) (b : PeriodicOperators.PosEdge L 0 0) :
    (shiftEdge k b).1.terminal = FullSpace.vertexImage (intShift k) b.1.terminal := by
  rw [shiftEdge_val, (edgeImage_endpoints k b.1).2]
theorem shiftEdge_initial (k : Fin 4 → ℤ) (b : PeriodicOperators.PosEdge L 0 0) :
    (shiftEdge k b).1.initial = FullSpace.vertexImage (intShift k) b.1.initial := by
  rw [shiftEdge_val, (edgeImage_endpoints k b.1).1]
theorem shiftEdge_neg_shiftEdge (k : Fin 4 → ℤ) (b : PeriodicOperators.PosEdge L 0 0) :
    shiftEdge (-k) (shiftEdge k b) = b := by
  apply Subtype.ext
  apply InfiniteLattice.Link.ext
  · rw [shiftEdge_initial, shiftEdge_initial, vertexImage_neg_vertexImage]
  · rw [shiftEdge_terminal, shiftEdge_terminal, vertexImage_neg_vertexImage]
theorem vertexDelta_vertexImage (k : Fin 4 → ℤ) (c : Fin 3) (x y : FullSpace.Vertex L 0 0) :
    vertexDelta (c, FullSpace.vertexImage (intShift k) x) (FullSpace.vertexImage (intShift k) y) =
      vertexDelta (c, x) y := by
  unfold vertexDelta
  simp only [(vertexImage_injective k).eq_iff]
theorem kernel_shift_covariant (ζ : (colourEdges L 0 0).Carrier → ℂ) (k : Fin 4 → ℤ)
    (ι' : (colourEdges L 0 0).Carrier) (ι : (colourVertices L 0 0).Carrier) :
    FullSpace.covDiffKernelOfField (shiftField (colourEdges L 0 0) k ζ)
        ((colourEdges L 0 0).translate k ι') ((colourVertices L 0 0).translate k ι) =
      FullSpace.covDiffKernelOfField ζ ι' ι := by
  obtain ⟨c', b⟩ := ι'
  obtain ⟨c, x⟩ := ι
  refine (kernel_eq (L := L) (shiftField (colourEdges L 0 0) k ζ)
    (c', shiftEdge k b) (c, FullSpace.vertexImage (intShift k) x)).trans
    (Eq.trans ?_ (kernel_eq (L := L) ζ (c', b) (c, x)).symm)
  change pauliForm c' (conjDiff
      (vertexDelta (c, FullSpace.vertexImage (intShift k) x) (shiftEdge k b).1.terminal)
      (vertexDelta (c, FullSpace.vertexImage (intShift k) x) (shiftEdge k b).1.initial)
      fun a => ζ (a, shiftEdge (-k) (shiftEdge k b))) = _
  rw [shiftEdge_neg_shiftEdge, shiftEdge_terminal, shiftEdge_initial, vertexDelta_vertexImage,
    vertexDelta_vertexImage]
theorem abs_le_euclidNormVec (v : Fin 4 → ℝ) (ν : Fin 4) :
    |v ν| ≤ TorusMetric.euclidNormVec v := by
  refine Real.abs_le_sqrt ?_
  exact Finset.single_le_sum (f := fun μ => v μ ^ 2) (fun μ _ => sq_nonneg _) (Finset.mem_univ ν)
def forwardEdge (k : Fin 4 → ℤ) (μ : Fin 4) : PeriodicOperators.PosEdge L 0 0 :=
  ⟨InfiniteLattice.Link.forwardFrom (latticePoint k) μ, μ,
    by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem finite_nearIndices (y : InfiniteLattice.AmbientSpace) (R : ℝ) :
    (nearIndices (colourEdges L 0 0) y R).Finite := by
  have hbox : (Icc (fun ν => ⌊y ν - R⌋) (fun ν => ⌈y ν + R⌉) : Set (Fin 4 → ℤ)).Finite :=
    Set.finite_Icc _ _
  refine (((finite_univ (α := Fin 3)).prod ((finite_univ (α := Fin 4)).prod hbox)).image
    (fun p : Fin 3 × Fin 4 × (Fin 4 → ℤ) =>
      ((p.1, forwardEdge p.2.2 p.2.1) : (colourEdges L 0 0).Carrier))).subset ?_
  rintro ⟨c, b⟩ hκ
  obtain ⟨μ, hμ⟩ := b.2
  obtain ⟨j, hj⟩ := b.1.initial.2
  have hj' : ∀ ν, ((b.1.initial : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace) ν =
      j ν := fun ν => by
    rw [hj ν, meshAt_zero_zero, mul_one]
  have hdist : ∀ ν, |(j ν : ℝ) - y ν| ≤ R := fun ν => by
    have := abs_le_euclidNormVec
      (((b.1.initial : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace) - y) ν
    simp only [Pi.sub_apply, hj'] at this
    exact this.trans hκ
  refine ⟨(c, μ, j), ⟨mem_univ _, mem_univ _, fun ν => ?_, fun ν => ?_⟩, ?_⟩
  · have h₁ := Int.floor_le (y ν - R)
    have h₂ := (abs_le.1 (hdist ν)).1
    have : ((⌊y ν - R⌋ : ℤ) : ℝ) ≤ j ν := by linarith
    exact_mod_cast this
  · have h₁ := Int.le_ceil (y ν + R)
    have h₂ := (abs_le.1 (hdist ν)).2
    have : (j ν : ℝ) ≤ ((⌈y ν + R⌉ : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  · have hinit : latticePoint (L := L) j = b.1.initial :=
      Subtype.ext (funext fun ν => (hj ν).symm)
    refine Prod.ext rfl (Subtype.ext (InfiniteLattice.Link.ext hinit ?_))
    change latticePoint j + InfiniteLattice.axisStep _ μ = b.1.terminal
    rw [hinit, ← hμ]
    abel
theorem euclidNormVec_axisStep (μ : Fin 4) :
    TorusMetric.euclidNormVec
      ((InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) :
        InfiniteLattice.AmbientSpace) = 1 := by
  have hsq : ∑ ν, ((InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) :
      InfiniteLattice.AmbientSpace) ν ^ 2 = 1 := by
    simp only [InfiniteLattice.axisStep, meshAt_zero_zero]
    fin_cases μ <;> simp [Pi.single_apply]
  unfold TorusMetric.euclidNormVec
  rw [hsq, Real.sqrt_one]
theorem kernel_eq_zero_of_far (ζ : Fin 3 × FullSpace.PositiveEdge (meshAt L 0 0) → ℂ)
    (ι' : (colourEdges L 0 0).Carrier) (ι : (colourVertices L 0 0).Carrier)
    (hfar : ¬ TorusMetric.euclidNormVec
      ((colourVertices L 0 0).pos ι - (colourEdges L 0 0).pos ι') ≤ 2) :
    FullSpace.covDiffKernelOfField ζ ι' ι = 0 := by
  obtain ⟨c', b⟩ := ι'
  obtain ⟨c, x⟩ := ι
  refine kernel_eq_zero ζ (c', b) (c, x) (fun he => hfar ?_) (fun he => hfar ?_)
  · obtain ⟨μ, hμ⟩ := b.2
    change TorusMetric.euclidNormVec ((x : InfiniteLattice.AmbientSpace) - _) ≤ 2
    have hx : x = b.1.terminal := he
    have hdiff : (x : InfiniteLattice.AmbientSpace) -
        ((b.1.initial : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace) =
        ((InfiniteLattice.axisStep (meshAt L 0 0) μ : FullSpace.Vertex L 0 0) :
          InfiniteLattice.AmbientSpace) := by
      rw [hx, ← hμ]
      rfl
    change TorusMetric.euclidNormVec
      ((x : InfiniteLattice.AmbientSpace) -
        ((b.1.initial : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace)) ≤ 2
    rw [hdiff, euclidNormVec_axisStep]
    norm_num
  · have hx : x = b.1.initial := he
    change TorusMetric.euclidNormVec
      ((x : InfiniteLattice.AmbientSpace) -
        ((b.1.initial : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace)) ≤ 2
    rw [hx, sub_self]
    simp [TorusMetric.euclidNormVec]
theorem mem_nearIndices_self (ι' : (colourEdges L 0 0).Carrier) (c : Fin 3) :
    ((c, ι'.2) : (colourEdges L 0 0).Carrier) ∈
      nearIndices (colourEdges L 0 0) ((colourEdges L 0 0).pos ι') 2 := by
  change TorusMetric.euclidNormVec (_ - _) ≤ 2
  change TorusMetric.euclidNormVec
    (((ι'.2.1.initial : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace) -
      ((ι'.2.1.initial : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace)) ≤ 2
  rw [sub_self]
  simp [TorusMetric.euclidNormVec]
theorem covDiffKernelLocalEntire_holds : CovDiffKernelLocalEntire := by
  intro L _
  refine ⟨fun ρ hρ => ⟨hρ, fun ζ _ ι' ι hfar => kernel_eq_zero_of_far ζ ι' ι hfar,
    fun ι' ι => ?_, fun ζ _ k ι' ι => kernel_shift_covariant ζ k ι' ι⟩, fun ι' ι => ?_,
      fun ζ ι' ι h₁ h₂ => kernel_eq_zero ζ ι' ι h₁ h₂⟩
  · have := (finite_nearIndices (L := L) ((colourEdges L 0 0).pos ι') 2).to_subtype
    let e := (Finite.equivFin (nearIndices (colourEdges L 0 0)
      ((colourEdges L 0 0).pos ι') 2)).symm
    obtain ⟨g, hg, hv⟩ := exists_entire_kernel ι' ι e (mem_nearIndices_self ι')
    exact ⟨_, e, g, isHolomorphicIn_of_differentiable hg (isOpen_openPolydisk ρ),
      fun ζ _ => hv ζ⟩
  · have hinj : Function.Injective
        fun c : Fin 3 => ((c, ι'.2) : (colourEdges L 0 0).Carrier) :=
      fun c c' he => congrArg Prod.fst he
    let e := Equiv.ofInjective _ hinj
    obtain ⟨g, hg, hv⟩ := exists_entire_kernel ι' ι e fun c => ⟨c, rfl⟩
    exact ⟨_, 3, e, g, ⟨by norm_num, isHolomorphicIn_of_differentiable hg isOpen_univ⟩, hv⟩
end YangMills.Construction.Tower.CovDiffKernelProof
end
