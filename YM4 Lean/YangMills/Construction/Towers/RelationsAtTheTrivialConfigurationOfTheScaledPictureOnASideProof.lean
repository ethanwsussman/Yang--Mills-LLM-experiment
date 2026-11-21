import YangMills.Construction.RunningCouplingSlope.PlainIteratesAreHolomorphicAtARadiusProof
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSitesProof
import YangMills.Construction.Towers.DerivativesOfAPlaquetteTerm
import YangMills.Construction.Towers.KernelAlgebraOfTheScaledPicture
import YangMills.Construction.Towers.KernelDeterminedByABilinearForm
import YangMills.Construction.Towers.RelationsAtTheTrivialConfigurationOfTheScaledPictureOnASide
import YangMills.Construction.Towers.RelationsOfTheIteratedAveragesOfTheScaledPictureOnASide
import YangMills.Construction.Towers.SecondDifferentialOfTheActionAsAKernel
import YangMills.Construction.Towers.StepsAtTheTrivialConfigurationOfTheScaledPictureOnASide
import YangMills.Construction.Towers.TransposesOfTheIteratedAveragesOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set
noncomputable section
namespace YangMills.Construction.Tower.TrivialFieldRescaledRelations
open PeriodicOperators (KernelMatrix applyKernel compKernel unitKernel kernelOfMap Represents
  RowFinite ApplySummable CompSummable)
open RescaledConditions
open Matrices
section Kernels
variable {N N' N'' : Type}
theorem applySummable_of_finite [Finite N] (T : KernelMatrix N N') (f : N → ℂ) :
    ApplySummable T f := fun i' => by
  have := Fintype.ofFinite N
  exact (hasSum_fintype _).summable
theorem compSummable_of_finite [Finite N'] (T : KernelMatrix N' N'') (S : KernelMatrix N N') :
    CompSummable T S := fun i'' i => by
  have := Fintype.ofFinite N'
  exact (hasSum_fintype _).summable
theorem rowFinite_of_finite [Finite N] (T : KernelMatrix N N') : RowFinite T :=
  fun _ => Set.toFinite _
theorem kernelOfMap_represents [Finite N] (M : (N → ℂ) → N' → ℂ)
    (hM : ∀ (z : ℂ) (f g : N → ℂ), M (z • f + g) = z • M f + M g) :
    Represents (kernelOfMap M) M := by
  classical
  have := Fintype.ofFinite N
  have h0 : M 0 = 0 := by
    have := hM 1 0 0
    simpa using this
  let A : (N → ℂ) →ₗ[ℂ] (N' → ℂ) :=
    { toFun := M
      map_add' := fun f g => by simpa using hM 1 f g
      map_smul' := fun z f => by simpa [h0] using hM z f 0 }
  have hex : ∃ T : KernelMatrix N N', Represents T M := by
    refine ⟨fun i' i => M (fun κ => unitKernel N κ i) i', fun f => ⟨applySummable_of_finite _ f, ?_⟩⟩
    have hf : f = ∑ i, f i • (fun κ => unitKernel N κ i) := by
      funext κ
      simp [Finset.sum_apply, unitKernel]
    funext i'
    have e : M f = ∑ i, f i • M (fun κ => unitKernel N κ i) := by
      conv_lhs => rw [hf]
      exact (map_sum A _ _).trans (Finset.sum_congr rfl fun i _ => map_smul A _ _)
    rw [e]
    simp only [applyKernel, tsum_fintype, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  exact Classical.epsilon_spec (p := fun T => Represents T M) hex
end Kernels
section Quadratic
variable {σ σ' : Type}
theorem meshTranspose_self {a : ℝ} (ha : a ≠ 0) (T : KernelMatrix (Fin 3 × σ) (Fin 3 × σ'))
    (i : Fin 3 × σ) (κ : Fin 3 × σ') : meshTranspose a a T i κ = T κ i := by
  simp only [meshTranspose, PeriodicOperators.wTranspose, meshWeight]
  have : a ^ 4 / a ^ 4 = 1 := div_self (pow_ne_zero 4 ha)
  rw [this]
  simp
theorem wPairing_transpose_comp [Fintype σ] [Fintype σ'] {a : ℝ} (ha : a ≠ 0)
    (d : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')) (c : Fin 3 × σ → ℂ) :
    PeriodicOperators.wPairing (fun _ => a ^ 4) c
        (applyKernel (compKernel (meshTranspose a a d) d) c) =
      ((a ^ 4 : ℝ) : ℂ) * ∑ κ, applyKernel d c κ * applyKernel d c κ := by
  simp only [PeriodicOperators.wPairing, applyKernel, compKernel, tsum_fintype,
    meshTranspose_self ha]
  rw [← Finset.mul_sum]
  congr 1
  calc ∑ i, c i * ∑ i', (∑ κ, d κ i * d κ i') * c i'
      = ∑ i, ∑ κ, (d κ i * c i) * ∑ i', d κ i' * c i' := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun i' _ => ?_
        ring
    _ = ∑ κ, (∑ i, d κ i * c i) * ∑ i', d κ i' * c i' := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun κ _ => (Finset.sum_mul _ _ _).symm
end Quadratic
section Coefficients
variable {σ : Type}
theorem ofPauliCoeffs_mem_traceless (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
theorem ofPauliCoeffs_smul_add (z : ℂ) (c c' : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (z • c + c') = z • ofPauliCoeffs c + ofPauliCoeffs c' := by apply _root_.YangMills.Construction.RunningCouplingSlope.MeanIteratesHolomorphicOfNear.ofPauliCoeffs_smul_add <;> assumption
theorem pauliCoeff_smul_add {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (z : ℂ) (a : Fin 3) :
    pauliCoeff a (z • X + Y) = z * pauliCoeff a X + pauliCoeff a Y := by
  have h : z • X + Y ∈ ComplexMatrix2.traceless :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hX) hY
  unfold pauliCoeff
  rw [dif_pos h, dif_pos hX, dif_pos hY]
  have e : (⟨z • X + Y, h⟩ : ComplexMatrix2.traceless) = z • ⟨X, hX⟩ + ⟨Y, hY⟩ := rfl
  rw [e, map_add, map_smul]
  rfl
theorem toPauliCoeffs_smul_add {f g : σ → ComplexMatrix2} (hf : ∀ x, f x ∈ ComplexMatrix2.traceless)
    (hg : ∀ x, g x ∈ ComplexMatrix2.traceless) (z : ℂ) :
    toPauliCoeffs (z • f + g) = z • toPauliCoeffs f + toPauliCoeffs g := by
  funext i
  exact pauliCoeff_smul_add (hf i.2) (hg i.2) z i.1
theorem halfTrace_mul_self_eq_sum (hP : OneLoop.PauliMatrixRelations) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.halfTrace (X * X) = ∑ a, pauliCoeff a X * pauliCoeff a X := by
  have hc : X = ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a := by
    have hco := OneLoop.pauliCoordinateEquiv.symm_apply_apply ⟨X, hX⟩
    have e : ∀ a, pauliCoeff a X = OneLoop.pauliCoordinateEquiv ⟨X, hX⟩ a :=
      fun a => dif_pos hX
    have e' : _ = X := congrArg Subtype.val hco
    simp only [e]
    rw [Fin.sum_univ_three]
    exact e'.symm
  exact hP.2.2.2.2.1 ⟨X, hX⟩ ⟨X, hX⟩ _ _ hc hc
end Coefficients
section Side
variable {L n k j : ℕ}
theorem admissibleBlockingFactor_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < L := by apply _root_.YangMills.Construction.Tower.AxisPathReversal.blockingFactor_pos <;> assumption
theorem finestMesh_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < finestMesh L k := by
  have h : (0 : ℝ) < L := by exact_mod_cast admissibleBlockingFactor_pos hL
  exact zpow_pos h _
theorem meshAt_self : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
theorem vertex_finite (hL : Conventions.IsAdmissibleBlockingFactor L) (n k j : ℕ) :
    Finite (Vertex L n k j) :=
  SeparatedSequences.BaseParameters.site_finite (admissibleBlockingFactor_pos hL) _ _
theorem positiveEdge_finite (hL : Conventions.IsAdmissibleBlockingFactor L) (n k j : ℕ) :
    Finite (PositiveEdge L n k j) := by
  have := vertex_finite hL n k j
  exact Finite.of_injective (fun b : PositiveEdge L n k j => (b.1.source, b.1.target)) fun b b' h =>
    Subtype.ext (PeriodicLattice.Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
theorem face_finite (hL : Conventions.IsAdmissibleBlockingFactor L) (n k j : ℕ) :
    Finite (Face L n k j) := by
  have := vertex_finite hL n k j
  exact Finite.of_injective (fun p : Face L n k j => (p.origin, p.firstAxis, p.secondAxis))
    fun p q h => by
      simp only [Prod.mk.injEq] at h
      exact PeriodicLattice.Plaquette.ext h.1 h.2.1 h.2.2
theorem opposite_isPositivelyOriented_of_not {b : Edge L n k j} (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.opposite_isPositivelyOriented_of_not <;> assumption
theorem forwardFrom_isPositivelyOriented (y : Vertex L n k j) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom y μ : Edge L n k j).IsPositivelyOriented :=
  ⟨μ, by show y + PeriodicLattice.unitStep L n _ μ - y = _; abel⟩
theorem extendOddly_congr {f g : Edge L n k j → ComplexMatrix2}
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → f b = g b) : extendOddly f = extendOddly g := by apply _root_.YangMills.Construction.Tower.CovDiffStep.extendOddly_congr <;> assumption
theorem extendOddly_opposite
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (f : Edge L n k j → ComplexMatrix2) (b : Edge L n k j) :
    extendOddly f b.opposite = -extendOddly f b := by apply _root_.YangMills.Construction.Tower.ProlongCompositesProof.extendOddly_opposite <;> assumption
def positiveEdgeValues (c : Fin 3 × PositiveEdge L n k j → ℂ) : Edge L n k j → ComplexMatrix2 :=
  open Classical in fun b => if h : b.IsPositivelyOriented then ofPauliCoeffs c ⟨b, h⟩ else 0
def edgeFormOfCoeffs (c : Fin 3 × PositiveEdge L n k j → ℂ) : Edge L n k j → ComplexMatrix2 :=
  extendOddly (positiveEdgeValues c)
theorem edgeFormOfCoeffs_of_pos (c : Fin 3 × PositiveEdge L n k j → ℂ) (b : PositiveEdge L n k j) :
    edgeFormOfCoeffs c b.1 = ofPauliCoeffs c b := by
  have hb := b.2
  unfold edgeFormOfCoeffs extendOddly positiveEdgeValues
  rw [if_pos hb, dif_pos hb]
theorem edgeFormOfCoeffs_of_not_pos (c : Fin 3 × PositiveEdge L n k j → ℂ) {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    edgeFormOfCoeffs c b =
      -ofPauliCoeffs c ⟨b.opposite, opposite_isPositivelyOriented_of_not hb⟩ := by
  unfold edgeFormOfCoeffs extendOddly positiveEdgeValues
  rw [if_neg hb, dif_pos (opposite_isPositivelyOriented_of_not hb)]
theorem edgeFormOfCoeffs_mem
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (c : Fin 3 × PositiveEdge L n k j → ℂ) : edgeFormOfCoeffs c ∈ complexEdgeForms L n k j := by
  refine ⟨fun b hb => ?_, fun b => extendOddly_opposite hx (positiveEdgeValues c) b⟩
  have e := edgeFormOfCoeffs_of_pos c ⟨b, hb⟩
  show edgeFormOfCoeffs c b ∈ ComplexMatrix2.traceless
  rw [show edgeFormOfCoeffs c b = _ from e]
  exact ofPauliCoeffs_mem_traceless c _
theorem edgeFormOfCoeffs_smul_add (z : ℂ) (c c' : Fin 3 × PositiveEdge L n k j → ℂ) :
    edgeFormOfCoeffs (z • c + c') = z • edgeFormOfCoeffs c + edgeFormOfCoeffs c' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · have e₁ := edgeFormOfCoeffs_of_pos (z • c + c') ⟨b, hb⟩
    have e₂ := edgeFormOfCoeffs_of_pos c ⟨b, hb⟩
    have e₃ := edgeFormOfCoeffs_of_pos c' ⟨b, hb⟩
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [show edgeFormOfCoeffs (z • c + c') b = _ from e₁, show edgeFormOfCoeffs c b = _ from e₂,
      show edgeFormOfCoeffs c' b = _ from e₃, ofPauliCoeffs_smul_add]
    rfl
  · simp only [Pi.add_apply, Pi.smul_apply]
    rw [edgeFormOfCoeffs_of_not_pos _ hb, edgeFormOfCoeffs_of_not_pos _ hb,
      edgeFormOfCoeffs_of_not_pos _ hb, ofPauliCoeffs_smul_add]
    simp only [Pi.add_apply, Pi.smul_apply, neg_add, smul_neg]
theorem edgePauliCoordinates_coeffs_smul_add {B B' : Edge L n k j → ComplexMatrix2}
    (hB : ∀ b : PositiveEdge L n k j, B b.1 ∈ ComplexMatrix2.traceless)
    (hB' : ∀ b : PositiveEdge L n k j, B' b.1 ∈ ComplexMatrix2.traceless) (z : ℂ) :
    (edgePauliCoordinates L n k j).coeffs (z • B + B') =
      z • (edgePauliCoordinates L n k j).coeffs B + (edgePauliCoordinates L n k j).coeffs B' :=
  toPauliCoeffs_smul_add (f := restrictToPositiveEdges B) (g := restrictToPositiveEdges B') hB hB' z
theorem vertexCoboundary_smul_add (z : ℂ) (l l' : Vertex L n k j → ComplexMatrix2) :
    vertexCoboundary (z • l + l') = z • vertexCoboundary l + vertexCoboundary l' := by
  funext b
  simp only [vertexCoboundary, Pi.add_apply, Pi.smul_apply, smul_sub]
  abel
theorem edgeCoboundary_smul_add (z : ℂ) (B B' : Edge L n k j → ComplexMatrix2) :
    edgeCoboundary (z • B + B') = z • edgeCoboundary B + edgeCoboundary B' := by
  funext p
  simp only [edgeCoboundary, Pi.add_apply, Pi.smul_apply, smul_sub, smul_add]
  abel
theorem edgeCoboundary_real_smul (a : ℝ) (B : Edge L n k j → ComplexMatrix2) :
    edgeCoboundary (a • B) = a • edgeCoboundary B := by
  funext p
  simp only [edgeCoboundary, Pi.smul_apply, smul_sub, smul_add]
theorem scaledVertexCoboundary_smul_add (z : ℂ) (l l' : Vertex L n k j → ComplexMatrix2) :
    scaledVertexCoboundary (z • l + l') =
      z • scaledVertexCoboundary l + scaledVertexCoboundary l' := by
  unfold scaledVertexCoboundary
  rw [vertexCoboundary_smul_add, smul_add, smul_comm]
theorem scaledEdgeCoboundary_smul_add (z : ℂ) (B B' : Edge L n k j → ComplexMatrix2) :
    scaledEdgeCoboundary (z • B + B') =
      z • scaledEdgeCoboundary B + scaledEdgeCoboundary B' := by
  unfold scaledEdgeCoboundary
  rw [edgeCoboundary_smul_add, smul_add, smul_comm]
theorem scaledVertexCoboundary_mem_traceless {l : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (b : PositiveEdge L n k j) :
    scaledVertexCoboundary l b.1 ∈ ComplexMatrix2.traceless := by
  have e : scaledVertexCoboundary l b.1 = (meshAt L k j)⁻¹ • (l b.1.target - l b.1.source) := rfl
  rw [e]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ (hl _) (hl _))
theorem scaledEdgeCoboundary_mem_traceless {B : Edge L n k j → ComplexMatrix2}
    (hB : ∀ b : Edge L n k j, b.IsPositivelyOriented → B b ∈ ComplexMatrix2.traceless)
    (p : Face L n k j) : scaledEdgeCoboundary B p ∈ ComplexMatrix2.traceless := by
  have e : scaledEdgeCoboundary B p = (meshAt L k j)⁻¹ • edgeCoboundary B p := rfl
  rw [e]
  refine Submodule.smul_of_tower_mem _ _ ?_
  exact Submodule.sub_mem _ (Submodule.sub_mem _
    (Submodule.add_mem _ (hB _ (forwardFrom_isPositivelyOriented _ _))
      (hB _ (forwardFrom_isPositivelyOriented _ _)))
    (hB _ (forwardFrom_isPositivelyOriented _ _))) (hB _ (forwardFrom_isPositivelyOriented _ _))
theorem vertexKernel_represents (hL : Conventions.IsAdmissibleBlockingFactor L) (n k j : ℕ) :
    Represents ((vertexCoordinate (Vertex L n k j)).kernel (edgePauliCoordinates L n k j) scaledVertexCoboundary)
      ((vertexCoordinate (Vertex L n k j)).mapOnCoeffs (edgePauliCoordinates L n k j)
        scaledVertexCoboundary) := by
  have := vertex_finite hL n k j
  have h : ∀ (z : ℂ) (c c' : Fin 3 × Vertex L n k j → ℂ),
      (edgePauliCoordinates L n k j).coeffs (scaledVertexCoboundary (ofPauliCoeffs (z • c + c'))) =
        z • (edgePauliCoordinates L n k j).coeffs (scaledVertexCoboundary (ofPauliCoeffs c)) +
          (edgePauliCoordinates L n k j).coeffs (scaledVertexCoboundary (ofPauliCoeffs c')) := by
    intro z c c'
    rw [ofPauliCoeffs_smul_add, scaledVertexCoboundary_smul_add]
    exact edgePauliCoordinates_coeffs_smul_add
      (scaledVertexCoboundary_mem_traceless (ofPauliCoeffs_mem_traceless c))
      (scaledVertexCoboundary_mem_traceless (ofPauliCoeffs_mem_traceless c')) z
  exact kernelOfMap_represents (N := Fin 3 × Vertex L n k j)
    (fun c => (edgePauliCoordinates L n k j).coeffs (scaledVertexCoboundary (ofPauliCoeffs c))) h
theorem edgeKernel_represents (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hx : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    Represents ((edgePauliCoordinates L n k j).kernel (vertexCoordinate (Face L n k j))
        scaledEdgeCoboundary)
      ((edgePauliCoordinates L n k j).mapOnCoeffs (vertexCoordinate (Face L n k j))
        scaledEdgeCoboundary) := by
  have := positiveEdge_finite hL n k j
  have h : ∀ (z : ℂ) (c c' : Fin 3 × PositiveEdge L n k j → ℂ),
      toPauliCoeffs (scaledEdgeCoboundary (edgeFormOfCoeffs (z • c + c'))) =
        z • toPauliCoeffs (scaledEdgeCoboundary (edgeFormOfCoeffs c)) +
          toPauliCoeffs (scaledEdgeCoboundary (edgeFormOfCoeffs c')) := by
    intro z c c'
    rw [edgeFormOfCoeffs_smul_add, scaledEdgeCoboundary_smul_add]
    exact toPauliCoeffs_smul_add
      (scaledEdgeCoboundary_mem_traceless (edgeFormOfCoeffs_mem hx c).1)
      (scaledEdgeCoboundary_mem_traceless (edgeFormOfCoeffs_mem hx c').1) z
  exact kernelOfMap_represents (N := Fin 3 × PositiveEdge L n k j)
    (fun c => toPauliCoeffs (scaledEdgeCoboundary (edgeFormOfCoeffs c))) h
theorem covDiff_trivialField (l : Vertex L n k j → ComplexMatrix2) :
    covDiff (trivialField L n k j) l = vertexCoboundary l := by
  funext b
  unfold covDiff extendOddly vertexCoboundary
  by_cases hb : b.IsPositivelyOriented
  · simp [hb, ComplexMatrix2.conjugateBy]
  · simp only [if_neg hb]
    simp [ComplexMatrix2.conjugateBy, PeriodicLattice.Bond.opposite]
theorem basisForm_eq_edgeFormOfCoeffs (a : Fin 3) (b : PositiveEdge L n k j) :
    basisForm a b =
      edgeFormOfCoeffs (fun κ => unitKernel (Fin 3 × PositiveEdge L n k j) κ (a, b)) := by
  classical
  refine extendOddly_congr (f := fun b' => if b' = b.1 then ComplexMatrix2.pauliFamily a else 0)
    fun b' hb' => ?_
  show _ = positiveEdgeValues _ b'
  unfold positiveEdgeValues
  rw [dif_pos hb']
  by_cases h : b' = b.1
  · have e : (⟨b', hb'⟩ : PositiveEdge L n k j) = b := Subtype.ext h
    rw [if_pos h, e]
    simp [ofPauliCoeffs, unitKernel]
  · have e : (⟨b', hb'⟩ : PositiveEdge L n k j) ≠ b := fun e => h (congrArg Subtype.val e)
    rw [if_neg h]
    simp [ofPauliCoeffs, unitKernel, e]
theorem halfTrace_real_smul_mul_self (c : ℝ) (X : ComplexMatrix2) :
    ComplexMatrix2.halfTrace ((c • X) * (c • X)) =
      ((c ^ 2 : ℝ) : ℂ) * ComplexMatrix2.halfTrace (X * X) := by
  have e : (c • X) * (c • X) = ((c ^ 2 : ℝ) : ℂ) • (X * X) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two]
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [e]
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_smul, smul_eq_mul]
  ring
theorem traceFinsumPairing_real_smul (hP : OneLoop.PauliMatrixRelations) {P : Type} [Fintype P]
    {s : P → ComplexMatrix2} (hs : ∀ p, s p ∈ ComplexMatrix2.traceless) (c : ℝ) :
    traceFinsumPairing (c • s) (c • s) =
      ((c ^ 2 : ℝ) : ℂ) * ∑ κ : Fin 3 × P, toPauliCoeffs s κ * toPauliCoeffs s κ := by
  unfold traceFinsumPairing
  rw [finsum_eq_sum_of_fintype, Fintype.sum_prod_type_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.smul_apply]
  rw [halfTrace_real_smul_mul_self, halfTrace_mul_self_eq_sum hP (hs p)]
  rfl
theorem hessian_eq_transpose_comp (hP : OneLoop.PauliMatrixRelations)
    (hD : FaceTermDerivatives.Statement)
    (hK : HessianKernel.KernelProperties)
    (hPol : PolarisedKernel.ValueAtUnits) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n)
    (hx : ∀ b : Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hone : trivialField L n k 0 ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup) :
    (rescaledOperators L n k (trivialField L n k 0)).H =
      compKernel (meshTranspose (finestMesh L k) (finestMesh L k)
        ((edgePauliCoordinates L n k 0).kernel (vertexCoordinate (Face L n k 0))
          scaledEdgeCoboundary))
        ((edgePauliCoordinates L n k 0).kernel (vertexCoordinate (Face L n k 0))
          scaledEdgeCoboundary) := by
  classical
  have ha : 0 < finestMesh L k := finestMesh_pos hL
  have := positiveEdge_finite hL n k 0
  have := face_finite hL n k 0
  have := Fintype.ofFinite (PositiveEdge L n k 0)
  have := Fintype.ofFinite (Face L n k 0)
  have hrep := edgeKernel_represents (L := L) (n := n) (k := k) (j := 0) hL hx
  set a := finestMesh L k with hadef
  set d : KernelMatrix (Fin 3 × PositiveEdge L n k 0) (Fin 3 × Face L n k 0) :=
    (edgePauliCoordinates L n k 0).kernel (vertexCoordinate (Face L n k 0)) scaledEdgeCoboundary
    with hddef
  set T : KernelMatrix (Fin 3 × PositiveEdge L n k 0) (Fin 3 × PositiveEdge L n k 0) :=
    compKernel (meshTranspose a a d) d with hTdef
  let Q := complexActionHessian (trivialField L n k 0)
  let β : ((Fin 3 × PositiveEdge L n k 0) → ℂ) → ((Fin 3 × PositiveEdge L n k 0) → ℂ) → ℂ :=
    fun c c' => Q (a • edgeFormOfCoeffs c) (a • edgeFormOfCoeffs c')
  have hmem : ∀ c, a • edgeFormOfCoeffs c ∈ complexEdgeForms L n k 0 := fun c =>
    Submodule.smul_of_tower_mem _ a (edgeFormOfCoeffs_mem hx c)
  have hbil := ((hK L hL k 0 (Nat.zero_le k)).1 n hn _ hone).1
  have hlin : ∀ (z : ℂ) (f g : (Fin 3 × PositiveEdge L n k 0) → ℂ),
      a • edgeFormOfCoeffs (z • f + g) = z • (a • edgeFormOfCoeffs f) + a • edgeFormOfCoeffs g := by
    intro z f g
    rw [edgeFormOfCoeffs_smul_add, smul_add, smul_comm]
  have hβ : PolarisedKernel.IsSymmBilinearOnFinite β :=
    { add_smul_left := fun z f g h _ _ _ => by
        show Q _ _ = _
        rw [hlin]
        exact (hbil z _ (hmem f) _ (hmem g) _ (hmem h)).1
      symm := fun f g _ _ => (hbil 0 _ (hmem f) _ (hmem f) _ (hmem g)).2.2 }
  have hsym : ∀ i i', T i i' = T i' i := by
    intro i i'
    simp only [hTdef, compKernel, meshTranspose_self ha.ne']
    exact tsum_congr fun κ => mul_comm _ _
  have hq : ∀ c : (Fin 3 × PositiveEdge L n k 0) → ℂ, PeriodicOperators.HasFiniteSupport c →
      β c c = PeriodicOperators.wPairing (fun _ => a ^ 4) c (applyKernel T c) := by
    intro c _
    rw [hTdef, wPairing_transpose_comp ha.ne' d c]
    have e₁ : β c c = traceFinsumPairing (edgeCoboundary (a • edgeFormOfCoeffs c))
        (edgeCoboundary (a • edgeFormOfCoeffs c)) :=
      ((hD L hL k 0 (Nat.zero_le k)).1 n hn _ (hmem c)).2
    have e₂ : edgeCoboundary (a • edgeFormOfCoeffs c) =
        (a * a) • scaledEdgeCoboundary (edgeFormOfCoeffs c : Edge L n k 0 → ComplexMatrix2) := by
      rw [edgeCoboundary_real_smul]
      show _ = (a * a) • (a⁻¹ • edgeCoboundary (edgeFormOfCoeffs c))
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ ha.ne', mul_one]
    have e₃ : applyKernel d c =
        toPauliCoeffs (scaledEdgeCoboundary (edgeFormOfCoeffs c : Edge L n k 0 → ComplexMatrix2)) :=
      (hrep c).2
    rw [e₁, e₂, traceFinsumPairing_real_smul hP
      (scaledEdgeCoboundary_mem_traceless (edgeFormOfCoeffs_mem hx c).1), e₃]
    congr 1
    push_cast
    ring
  funext i i'
  have key := hPol _ T (a ^ 4) β (rowFinite_of_finite T) hsym hβ hq i i'
  show (((a ^ 4)⁻¹ : ℝ) : ℂ) * Q (a • basisForm i.1 i.2) (a • basisForm i'.1 i'.2) = T i i'
  rw [basisForm_eq_edgeFormOfCoeffs, basisForm_eq_edgeFormOfCoeffs]
  have e : Q (a • edgeFormOfCoeffs fun κ => unitKernel (Fin 3 × PositiveEdge L n k 0) κ (i.1, i.2))
      (a • edgeFormOfCoeffs fun κ => unitKernel (Fin 3 × PositiveEdge L n k 0) κ (i'.1, i'.2)) =
      ((a ^ 4 : ℝ) : ℂ) * T i i' := key
  rw [e, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 4 ha.ne')]
  simp
theorem iterCovariantDeriv_trivialField (hLin : StepMapsComplexLinear.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hst : ∀ i < k, TrivialStep L n k i)
    (hblock : ∀ j, j ≤ k → PeriodicLattice.complexBlockFieldAtLevel j (trivialField L n k 0) =
      trivialField L n k j)
    (hsmall : ∀ j < k, trivialField L n k j ∈ smallComplexFields L n k j)
    {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n k 0) (j : ℕ) (hj : j ≤ k) :
    iterCovariantDeriv L n k (trivialField L n k 0) j B =
        crossingSmoothingIter L n k j B ∧
      (j < k → iterCovariantDeriv L n k (trivialField L n k 0) j B ∈
        complexEdgeForms L n k j) := by
  induction j with
  | zero => exact ⟨rfl, fun _ => hB⟩
  | succ j ih =>
    obtain ⟨e, hm⟩ := ih (by omega)
    have hm' := hm (by omega)
    have hjk : j < k := by omega
    have hstep := ((hst j hjk).2.2.2.2.1 _ hm').2.2
    have eq : iterCovariantDeriv L n k (trivialField L n k 0) (j + 1) B =
        covariantSmoothingDeriv (trivialField L n k j)
          (iterCovariantDeriv L n k (trivialField L n k 0) j B) := by
      show covariantSmoothingDeriv (PeriodicLattice.complexBlockFieldAtLevel j _) _ = _
      rw [hblock j hjk.le]
    refine ⟨?_, fun hj' => ?_⟩
    · rw [eq, hstep, e]
      rfl
    · rw [eq]
      have l₁ := hLin L hL n k j hn hjk _ (hsmall j hjk)
      have l₂ := hLin L hL n k (j + 1) hn hj' _ (hsmall (j + 1) hj')
      unfold covariantSmoothingDeriv
      rw [(hst j hjk).1]
      exact Submodule.add_mem _ (l₁.1 _ hm').1 (l₂.2.2.1 _ (l₁.1 _ hm').2).1
theorem iterAdjointCubeAverage_trivialField (hLin : StepMapsComplexLinear.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hst : ∀ i < k, TrivialStep L n k i)
    (hblock : ∀ j, j ≤ k → PeriodicLattice.complexBlockFieldAtLevel j (trivialField L n k 0) =
      trivialField L n k j)
    (hsmall : ∀ j < k, trivialField L n k j ∈ smallComplexFields L n k j)
    {l : Vertex L n k 0 → ComplexMatrix2}
    (hl : l ∈ Matrices.GroupLieProduct.tracelessFunctions (Vertex L n k 0))
    (j : ℕ) (hj : j ≤ k) :
    iterAdjointCubeAverage L n k (trivialField L n k 0) j l = vertexSmoothingIter L n k j l ∧
      iterAdjointCubeAverage L n k (trivialField L n k 0) j l ∈
        Matrices.GroupLieProduct.tracelessFunctions (Vertex L n k j) := by
  induction j with
  | zero => exact ⟨rfl, hl⟩
  | succ j ih =>
    obtain ⟨e, hm⟩ := ih (by omega)
    have hjk : j < k := by omega
    have hstep := (hst j hjk).2.2.2.2.2 _ hm
    have eq : iterAdjointCubeAverage L n k (trivialField L n k 0) (j + 1) l =
        adjointCubeAverage (trivialField L n k j)
          (iterAdjointCubeAverage L n k (trivialField L n k 0) j l) := by
      show adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j _) _ = _
      rw [hblock j hjk.le]
    refine ⟨?_, ?_⟩
    · rw [eq, hstep, e]
      rfl
    · rw [eq]
      have l₁ := hLin L hL n k j hn hjk _ (hsmall j hjk)
      exact Submodule.mem_pi.2 fun y _ =>
        (l₁.2.2.1 _ fun x => Submodule.mem_pi.1 hm x (mem_univ x)).2 y
end Side
theorem holds (hRel : RescaledIterRelations)
    (hSteps : RescaledTrivialSteps)
    (hAlg : RescaledKernelAlgebra.Claim)
    (hPol : PolarisedKernel.ValueAtUnits)
    (hD : FaceTermDerivatives.Statement)
    (hK : HessianKernel.KernelProperties)
    (hLin : StepMapsComplexLinear.Claim)
    (hP : OneLoop.PauliMatrixRelations)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement) : Statement := by
  intro L hL k hk n hn
  obtain ⟨hU, hst⟩ := hSteps L hL k hk n hn
  have rel := hRel L hL k hk n hn _ hU
  have hx : ∀ j, j ≤ k → ∀ b : Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun j hj b => ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj).2.2.2 b).2.2.2.2.2
  have hblock : ∀ j, j ≤ k → PeriodicLattice.complexBlockFieldAtLevel j (trivialField L n k 0) =
      trivialField L n k j := by
    intro j
    induction j with
    | zero => exact fun _ => rfl
    | succ j ih =>
      intro hj
      show PeriodicLattice.complexBlockAverageStep j
        (PeriodicLattice.complexBlockFieldAtLevel j _) = _
      rw [ih (by omega)]
      exact (hst j (by omega)).1
  have hsmall : ∀ j < k, trivialField L n k j ∈ smallComplexFields L n k j := by
    intro j hj
    have h := hU.2 j hj
    rwa [hblock j hj.le] at h
  have hη : 0 < finestMesh L k := finestMesh_pos hL
  have f₁ := vertex_finite hL n k 0
  have f₂ := vertex_finite hL n k k
  have f₃ := positiveEdge_finite hL n k 0
  have f₅ : Finite (vertexCoordinate (Vertex L n k 0)).Index :=
    (inferInstance : Finite (Fin 3 × Vertex L n k 0))
  have f₆ : Finite (vertexCoordinate (Vertex L n k k)).Index :=
    (inferInstance : Finite (Fin 3 × Vertex L n k k))
  have f₇ : Finite (edgePauliCoordinates L n k 0).Index :=
    (inferInstance : Finite (Fin 3 × PositiveEdge L n k 0))
  have f₈ := face_finite hL n k 0
  have f₉ : Finite (vertexCoordinate (Face L n k 0)).Index :=
    (inferInstance : Finite (Fin 3 × Face L n k 0))
  set p := rescaledOperators L n k (trivialField L n k 0) with hp
  have hcov : (fun l : Vertex L n k 0 → ComplexMatrix2 =>
      (finestMesh L k)⁻¹ • covDiff (trivialField L n k 0) l) =
      scaledVertexCoboundary := funext fun l => by
    rw [covDiff_trivialField]
    rfl
  have hDeq : p.D = (vertexCoordinate (Vertex L n k 0)).kernel (edgePauliCoordinates L n k 0)
      scaledVertexCoboundary :=
    congrArg (fun m => (vertexCoordinate (Vertex L n k 0)).kernel (edgePauliCoordinates L n k 0) m) hcov
  have hDW : covDiffKernel L n k k
      (PeriodicLattice.complexBlockFieldAtLevel k (trivialField L n k 0)) =
      (vertexCoordinate (Vertex L n k k)).kernel (edgePauliCoordinates L n k k) scaledVertexCoboundary := by
    rw [hblock k le_rfl]
    have hcov' : covDiff (trivialField L n k k) =
        scaledVertexCoboundary := funext fun l => by
      rw [covDiff_trivialField]
      unfold scaledVertexCoboundary
      rw [meshAt_self]
      simp
    exact congrArg (fun m => (vertexCoordinate (Vertex L n k k)).kernel (edgePauliCoordinates L n k k) m) hcov'
  have hH := hessian_eq_transpose_comp hP hD hK hPol hL hn (hx 0 (Nat.zero_le k)) hU.1
  have hH' : p.H = compKernel (meshTranspose p.eta p.eta
      ((edgePauliCoordinates L n k 0).kernel (vertexCoordinate (Face L n k 0))
        scaledEdgeCoboundary))
      ((edgePauliCoordinates L n k 0).kernel (vertexCoordinate (Face L n k 0))
        scaledEdgeCoboundary) := hH
  have hRRt := rel.R_comp_Rt
  have hcons := hAlg _ _ _ _ p hη (by show 0 < meshAt L k k; rw [meshAt_self]; exact one_pos)
    ⟨rowFinite_of_finite _, rowFinite_of_finite _, rowFinite_of_finite _,
      rowFinite_of_finite _, rowFinite_of_finite _⟩ hRRt
  have hDt : p.Dt = meshTranspose p.eta p.eta
      ((vertexCoordinate (Vertex L n k 0)).kernel (edgePauliCoordinates L n k 0) scaledVertexCoboundary) := by
    rw [← hDeq]
    rfl
  refine
    { vertex_represents := vertexKernel_represents hL n k 0
      edge_represents := edgeKernel_represents hL (hx 0 (Nat.zero_le k))
      coarse_represents := vertexKernel_represents hL n k k
      D_eq := hDeq
      Q_represents := ?_
      R_represents := ?_
      comp_summable := ⟨compSummable_of_finite _ _, compSummable_of_finite _ _,
        compSummable_of_finite _ _, compSummable_of_finite _ _,
        compSummable_of_finite _ _⟩
      Q_comp_d := ?_
      H_eq := hH
      K_eq := ?_
      Delta_eq := ?_
      X_eq := ?_ }
  · have e : PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L n k 0) (edgePauliCoordinates L n k k)
        (fun B' => p.eta • crossingSmoothingIter L n k k B') =
        PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L n k 0) (edgePauliCoordinates L n k k)
          (fun B' => p.eta • iterCovariantDeriv L n k
            (trivialField L n k 0) k B') := by
      funext (f : Fin 3 × PositiveEdge L n k 0 → ℂ)
      have e' := (iterCovariantDeriv_trivialField hLin hL hn hst hblock hsmall
        (edgeFormOfCoeffs_mem (hx 0 (Nat.zero_le k)) f) k le_rfl).1
      exact show (edgePauliCoordinates L n k k).coeffs
          (p.eta • crossingSmoothingIter L n k k (edgeFormOfCoeffs f)) =
          (edgePauliCoordinates L n k k).coeffs (p.eta • iterCovariantDeriv L n k
            (trivialField L n k 0) k (edgeFormOfCoeffs f)) from by rw [e']
    have g : Represents p.Q (PauliComponentsOfSymmetricKernel.mapOnCoeffs (edgePauliCoordinates L n k 0) (edgePauliCoordinates L n k k)
        (fun B' => p.eta • iterCovariantDeriv L n k
          (trivialField L n k 0) k B')) := rel.Q_represents
    rw [← e] at g
    exact g
  · have e : PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (Vertex L n k 0))
        (vertexCoordinate (Vertex L n k k)) (vertexSmoothingIter L n k k) =
        PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (Vertex L n k 0)) (vertexCoordinate (Vertex L n k k))
          (iterAdjointCubeAverage L n k (trivialField L n k 0) k) := by
      funext (f : Fin 3 × Vertex L n k 0 → ℂ)
      have e' := (iterAdjointCubeAverage_trivialField hLin hL hn hst hblock hsmall
        (Submodule.mem_pi.2 fun x _ => ofPauliCoeffs_mem_traceless f x) k le_rfl).1
      exact show toPauliCoeffs (vertexSmoothingIter L n k k (ofPauliCoeffs f)) =
          toPauliCoeffs (iterAdjointCubeAverage L n k (trivialField L n k 0) k
            (ofPauliCoeffs f)) from by rw [e']
    have g : Represents p.R (PauliComponentsOfSymmetricKernel.mapOnCoeffs (vertexCoordinate (Vertex L n k 0))
        (vertexCoordinate (Vertex L n k k))
        (iterAdjointCubeAverage L n k (trivialField L n k 0) k)) := rel.R_represents
    rw [← e] at g
    exact g
  · have e : compKernel p.Q ((vertexCoordinate (Vertex L n k 0)).kernel (edgePauliCoordinates L n k 0)
          scaledVertexCoboundary) =
        compKernel ((vertexCoordinate (Vertex L n k k)).kernel (edgePauliCoordinates L n k k)
          scaledVertexCoboundary) p.R := by
      rw [← hDeq, ← hDW]
      exact rel.Q_comp_D
    exact e
  · have e : p.K = p.H + compKernel p.D p.Dt := rfl
    rw [hDt, hDeq, hH'] at e
    exact e
  · have e : p.Delta = compKernel p.Dt p.D := rfl
    rw [hDt, hDeq] at e
    exact e
  · have e : p.X = p.H + compKernel (compKernel p.D (complementProj p)) p.Dt :=
      hcons.X_eq
    rw [hDt, hDeq, hH'] at e
    exact e
end YangMills.Construction.Tower.TrivialFieldRescaledRelations
end
