import YangMills.Construction.RunningCouplingSlope.FinePartsAlongTheBackgroundAreLocal
import YangMills.Construction.RunningCouplingSlope.LocalFamiliesAreClosed
import YangMills.Construction.RunningCouplingSlope.LocalFamiliesOfCells
import Mathlib
import YangMills.Construction.RunningCouplingSlope.TheGhostOfTheWholeChainHasABoundedInverseAtOneProof
set_option autoImplicit false

section
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.CriticalBranchResponse
def ConjugatedFamiliesLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ M θ : ℝ, 0 < M ∧ 0 < θ ∧
    ∀ k : ℕ, 1 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
      ∀ [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × PositiveEdge L n k k)]
        [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
        [DecidableEq (Fin 3 × PositiveEdge L n k 0)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
        [DecidableEq (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k k)],
      ∀ v : Fin 4 → ℤ,
        IsLocalAlongBackground colouredEdgeCell colouredEdgeCell (xiConjugated L n k v) v M θ ∧
        IsLocalAlongBackground colouredVertexCell colouredVertexCell (yConjugated L n k v) v M θ
end YangMills.Construction.RunningCouplingSlope
end
end

open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.ConjugatedFamilies
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.CriticalBranchResponse
variable {L n k : ℕ}
private lemma of_compKernel {a b c : Type} [Fintype b] (T : KernelMatrix b a)
    (S : KernelMatrix c b) : Matrix.of (compKernel T S) = Matrix.of T * Matrix.of S := by apply _root_.YangMills.DeltaSharedProofs.p17742 <;> assumption
private lemma meshTranspose_same_mesh {σ σ' : Type} (hη : finestMesh L k ≠ 0)
    (K : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')) :
    Matrix.of (meshTranspose (finestMesh L k) (finestMesh L k) K) =
      (Matrix.of K).transpose := by
  ext ι ι'
  simp only [meshTranspose, PeriodicOperators.wTranspose, meshWeight, Matrix.of_apply,
    Matrix.transpose_apply]
  have : finestMesh L k ^ 4 / finestMesh L k ^ 4 = 1 := div_self (pow_ne_zero _ hη)
  rw [this]
  simp
private lemma meshTranspose_finest_coarse {σ σ' : Type}
    (K : KernelMatrix (Fin 3 × σ) (Fin 3 × σ')) :
    Matrix.of (meshTranspose (finestMesh L k) (meshAt L k k) K) =
      (unitNormScale L k * unitNormScale L k) • (Matrix.of K).transpose := by apply _root_.YangMills.SharedProofs.p28483 <;> assumption
private lemma edgeForm_mem_complex (h : edgeFormSpace L n k 0) :
    (h : Edge L n k 0 → Matrices.ComplexMatrix2) ∈ complexEdgeForms L n k 0 :=
  ⟨fun b hb => (h.2.1 b hb).2, h.2.2⟩
private lemma exists_remainder_eq_background (z : Fin 4 → ℤ) (s t : ℝ) :
    ∃ a ∈ complexEdgeForms L n k 0, twoSourceBackground L n k z s t = remainderGaugeField a := by
  refine ⟨(s : ℂ) • (periodicResponse L n k (pauliUnitForm L n k 0) :
      Edge L n k 0 → Matrices.ComplexMatrix2) +
    (t : ℂ) • (periodicResponse L n k (pauliUnitForm L n k z) :
      Edge L n k 0 → Matrices.ComplexMatrix2), ?_, ?_⟩
  · exact (complexEdgeForms L n k 0).add_mem
      ((complexEdgeForms L n k 0).smul_mem _ (edgeForm_mem_complex _))
      ((complexEdgeForms L n k 0).smul_mem _ (edgeForm_mem_complex _))
  · unfold twoSourceBackground remainderGaugeField IdentityExpChart.expForm
      scaledRemainderForm
    congr 1
    funext b
    simp only [meshScaledResponse, Pi.add_apply, Pi.smul_apply, Submodule.coe_smul, smul_add]
    rw [smul_comm (s : ℂ), smul_comm (t : ℂ)]
private lemma matrix_xi_expand {B P S T T' : Type} [Fintype B] [Fintype P] [Fintype S]
    [Fintype T] [Fintype T'] (Dif : Matrix P B ℂ) (Zt : Matrix P P ℂ) (f : Matrix B B ℂ)
    (D : Matrix B S ℂ) (Rm : Matrix T S ℂ) (Qm : Matrix T' B ℂ) (g : Matrix B B ℂ) (u : ℂ)
    (hgt : g.transpose = g) :
    g * (Dif.transpose * (Zt * Dif) + f + D * D.transpose -
        (D * ((u * u) • Rm.transpose)) * (Rm * D.transpose) +
        ((u * u) • Qm.transpose) * Qm) * g =
      (Dif * g).transpose * (Zt * (Dif * g)) + g * f * g +
        (D.transpose * g).transpose * (D.transpose * g) +
        (-1 : ℂ) • (((u • Rm) * (D.transpose * g)).transpose * ((u • Rm) * (D.transpose * g))) +
        ((u • Qm) * g).transpose * ((u • Qm) * g) := by
  have t1 : g * (Dif.transpose * (Zt * Dif)) * g = (Dif * g).transpose * (Zt * (Dif * g)) := by
    simp only [Matrix.transpose_mul, hgt, Matrix.mul_assoc]
  have t3 : g * (D * D.transpose) * g = (D.transpose * g).transpose * (D.transpose * g) := by
    simp only [Matrix.transpose_mul, hgt, Matrix.transpose_transpose, Matrix.mul_assoc]
  have t4 : g * ((D * ((u * u) • Rm.transpose)) * (Rm * D.transpose)) * g =
      ((u • Rm) * (D.transpose * g)).transpose * ((u • Rm) * (D.transpose * g)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_smul, hgt, Matrix.transpose_transpose,
      Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  have t5 : g * (((u * u) • Qm.transpose) * Qm) * g =
      ((u • Qm) * g).transpose * ((u • Qm) * g) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_smul, hgt, Matrix.mul_assoc, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul]
  rw [← t1, ← t3, ← t4, ← t5]
  simp only [Matrix.mul_add, Matrix.add_mul, neg_smul, one_smul, sub_eq_add_neg, Matrix.mul_neg,
    Matrix.neg_mul]
private lemma matrix_y_expand {S T : Type} [Fintype S] {B : Type} [Fintype B] [Fintype T]
    (D : Matrix B S ℂ) (Rm : Matrix T S ℂ) (g : Matrix S S ℂ) (u : ℂ) (hgt : g.transpose = g) :
    g * (D.transpose * D + ((u * u) • Rm.transpose) * Rm) * g =
      (D * g).transpose * (D * g) + ((u • Rm) * g).transpose * ((u • Rm) * g) := by
  have t1 : g * (D.transpose * D) * g = (D * g).transpose * (D * g) := by
    simp only [Matrix.transpose_mul, hgt, Matrix.mul_assoc]
  have t2 : g * (((u * u) • Rm.transpose) * Rm) * g =
      ((u • Rm) * g).transpose * ((u • Rm) * g) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_smul, hgt, Matrix.mul_assoc, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul]
  rw [← t1, ← t2]
  simp only [Matrix.mul_add, Matrix.add_mul]
private lemma finite_face [Finite (Vertex L n k 0)] : Finite (Face L n k 0) := by
  refine Finite.of_injective
    (fun p : Face L n k 0 => ((p.origin, p.firstAxis, p.secondAxis) : Vertex L n k 0 × Fin 4 × Fin 4)) ?_
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl
abbrev _root_.YangMills.SharedProofs.p14127 := @finite_face
private lemma localFamily_weaken (hC : LocalFamiliesClosed)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] {c : ι → Vertex L n k k}
    {c' : ι' → Vertex L n k k} {T : ℝ → ℝ → Matrix ι' ι ℂ} {z : Fin 4 → ℤ} {M M' θ θ' : ℝ}
    (hM : 0 ≤ M) (hMM : M ≤ M') (hθ' : 0 < θ') (hθθ : θ' ≤ θ)
    (h : IsLocalAlongBackground c c' T z M θ) :
    IsLocalAlongBackground c c' T z M' θ' := by
  obtain ⟨S, -, hS⟩ := hC θ (hθ'.trans_le hθθ)
  exact (hS L n k hL hn).mono c c' T z M M' θ' hM hMM hθ' hθθ h
private lemma localFamily_const (hC : LocalFamiliesClosed)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] [DecidableEq ι] {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k}
    {A : Matrix ι' ι ℂ} (z : Fin 4 → ℤ) {M θ : ℝ} (hM : 0 ≤ M) (hθ : 0 < θ)
    (h : IsLocalOnCells c c' A M θ fun _ => 1) :
    IsLocalAlongBackground c c' (fun _ _ => A) z M θ := by
  obtain ⟨S, -, hS⟩ := hC θ hθ
  exact (hS L n k hL hn).ofConstant c c' A z M hM h
private lemma xiConjugated_eq (hH : WilsonHessian.DecompositionHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n)
    [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × PositiveEdge L n k k)]
    [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
    [Fintype (Fin 3 × Face L n k 0)] (z : Fin 4 → ℤ) (s t : ℝ)
    (hgt : (periodicEdgeResolventSqrt L n k).transpose = periodicEdgeResolventSqrt L n k) :
    xiConjugated L n k z s t =
      ((Matrix.of (scaledEdgeCoboundaryKernel L n k 0) +
            holonomyDefectAlongBackground L n k z s t) *
          periodicEdgeResolventSqrt L n k).transpose *
        (faceTraceAlongBackground L n k z s t *
          ((Matrix.of (scaledEdgeCoboundaryKernel L n k 0) +
            holonomyDefectAlongBackground L n k z s t) * periodicEdgeResolventSqrt L n k)) +
      periodicEdgeResolventSqrt L n k * curvatureAlongBackground L n k z s t *
        periodicEdgeResolventSqrt L n k +
      ((Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).D).transpose *
          periodicEdgeResolventSqrt L n k).transpose *
        ((Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).D).transpose *
          periodicEdgeResolventSqrt L n k) +
      (-1 : ℂ) • ((rescaledRAlong L n k z s t *
          ((Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).D).transpose *
            periodicEdgeResolventSqrt L n k)).transpose *
        (rescaledRAlong L n k z s t *
          ((Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).D).transpose *
            periodicEdgeResolventSqrt L n k))) +
      (rescaledQAlong L n k z s t * periodicEdgeResolventSqrt L n k).transpose *
        (rescaledQAlong L n k z s t * periodicEdgeResolventSqrt L n k) := by
  have hη : finestMesh L k ≠ 0 := by
    have : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    unfold finestMesh meshAt
    exact (zpow_pos this _).ne'
  obtain ⟨a, ha, hU⟩ := exists_remainder_eq_background (L := L) (n := n) (k := k) z s t
  have hHess := (hH L hL k hk).1 n hn a ha
  rw [← hU] at hHess
  set U := twoSourceBackground L n k z s t with hUdef
  have eXi : Matrix.of (rescaledOperators L n k U).Xi =
      (Matrix.of (coboundaryAddDefectKernel L n k U)).transpose *
          (Matrix.of (halfFaceTraceKernel L n k U) *
            Matrix.of (coboundaryAddDefectKernel L n k U)) +
        Matrix.of (curvatureKernel U) +
        Matrix.of (rescaledOperators L n k U).D *
          (Matrix.of (rescaledOperators L n k U).D).transpose -
        (Matrix.of (rescaledOperators L n k U).D *
          ((unitNormScale L k * unitNormScale L k) •
            (Matrix.of (rescaledOperators L n k U).R).transpose)) *
          (Matrix.of (rescaledOperators L n k U).R *
            (Matrix.of (rescaledOperators L n k U).D).transpose) +
        ((unitNormScale L k * unitNormScale L k) •
            (Matrix.of (rescaledOperators L n k U).Q).transpose) *
          Matrix.of (rescaledOperators L n k U).Q := by
    have a1 : Matrix.of (rescaledOperators L n k U).Dt =
        (Matrix.of (rescaledOperators L n k U).D).transpose :=
      meshTranspose_same_mesh hη _
    have a2 : Matrix.of (rescaledOperators L n k U).Rt =
        (unitNormScale L k * unitNormScale L k) •
          (Matrix.of (rescaledOperators L n k U).R).transpose :=
      meshTranspose_finest_coarse _
    have a3 : Matrix.of (rescaledOperators L n k U).Qt =
        (unitNormScale L k * unitNormScale L k) •
          (Matrix.of (rescaledOperators L n k U).Q).transpose :=
      meshTranspose_finest_coarse _
    have a4 : Matrix.of (meshTranspose (finestMesh L k) (finestMesh L k)
        (coboundaryAddDefectKernel L n k U)) =
        (Matrix.of (coboundaryAddDefectKernel L n k U)).transpose :=
      meshTranspose_same_mesh hη _
    have a5 : Matrix.of (rescaledOperators L n k U).H =
        (Matrix.of (coboundaryAddDefectKernel L n k U)).transpose *
          (Matrix.of (halfFaceTraceKernel L n k U) *
            Matrix.of (coboundaryAddDefectKernel L n k U)) +
        Matrix.of (curvatureKernel U) := by
      rw [hHess]
      show Matrix.of (coboundarySquareKernel L n k U) + Matrix.of (curvatureKernel U) = _
      unfold coboundarySquareKernel
      rw [of_compKernel, of_compKernel, a4]
    show Matrix.of (rescaledOperators L n k U).H +
        Matrix.of (compKernel (rescaledOperators L n k U).D (rescaledOperators L n k U).Dt) -
        Matrix.of (compKernel
          (compKernel (rescaledOperators L n k U).D (rescaledOperators L n k U).Rt)
          (compKernel (rescaledOperators L n k U).R (rescaledOperators L n k U).Dt)) +
        Matrix.of (compKernel (rescaledOperators L n k U).Qt (rescaledOperators L n k U).Q) = _
    rw [of_compKernel, of_compKernel, of_compKernel, of_compKernel, of_compKernel,
      a1, a2, a3, a5]
  have eDif : Matrix.of (coboundaryAddDefectKernel L n k U) =
      Matrix.of (scaledEdgeCoboundaryKernel L n k 0) +
        holonomyDefectAlongBackground L n k z s t := rfl
  unfold xiConjugated
  rw [← hUdef, eXi, matrix_xi_expand _ _ _ _ _ _ _ _ hgt, eDif]
  rfl
private lemma yConjugated_eq (hL : Conventions.IsAdmissibleBlockingFactor L)
    [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × Vertex L n k 0)]
    [Fintype (Fin 3 × Vertex L n k k)] (z : Fin 4 → ℤ) (s t : ℝ)
    (hgt : (periodicVertexResolventSqrt L n k).transpose = periodicVertexResolventSqrt L n k) :
    yConjugated L n k z s t =
      (Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).D *
          periodicVertexResolventSqrt L n k).transpose *
        (Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).D *
          periodicVertexResolventSqrt L n k) +
      (rescaledRAlong L n k z s t * periodicVertexResolventSqrt L n k).transpose *
        (rescaledRAlong L n k z s t * periodicVertexResolventSqrt L n k) := by
  have hη : finestMesh L k ≠ 0 := by
    have : (0 : ℝ) < L := by
      have := hL.2
      exact_mod_cast (by omega : 0 < L)
    unfold finestMesh meshAt
    exact (zpow_pos this _).ne'
  set U := twoSourceBackground L n k z s t with hUdef
  have eY : Matrix.of (rescaledOperators L n k U).Y =
      (Matrix.of (rescaledOperators L n k U).D).transpose *
          Matrix.of (rescaledOperators L n k U).D +
        ((unitNormScale L k * unitNormScale L k) •
            (Matrix.of (rescaledOperators L n k U).R).transpose) *
          Matrix.of (rescaledOperators L n k U).R := by
    have a1 : Matrix.of (rescaledOperators L n k U).Dt =
        (Matrix.of (rescaledOperators L n k U).D).transpose :=
      meshTranspose_same_mesh hη _
    have a2 : Matrix.of (rescaledOperators L n k U).Rt =
        (unitNormScale L k * unitNormScale L k) •
          (Matrix.of (rescaledOperators L n k U).R).transpose :=
      meshTranspose_finest_coarse _
    show Matrix.of (compKernel (rescaledOperators L n k U).Dt (rescaledOperators L n k U).D) +
        Matrix.of (compKernel (rescaledOperators L n k U).Rt (rescaledOperators L n k U).R) = _
    rw [of_compKernel, of_compKernel, a1, a2]
  unfold yConjugated
  rw [← hUdef, eY, matrix_y_expand _ _ _ _ hgt]
  rfl
theorem conjugatedFamiliesLocal_holds (hC : LocalFamiliesClosed)
    (hH : WilsonHessian.DecompositionHolds) (hR : PeriodicResolventSqrtsLocal)
    (hA : BackgroundMeansAreLocal) (hF : FineOperatorPartsAreLocal) :
    ConjugatedFamiliesLocal := by
  intro L hL
  obtain ⟨M₁, θ₁, hM₁, hθ₁, hR'⟩ := hR L hL
  obtain ⟨M₂, θ₂, hM₂, hθ₂, hA'⟩ := hA 1 one_pos L hL
  obtain ⟨M₃, θ₃, hM₃, hθ₃, hF'⟩ := hF L hL
  obtain ⟨θ, hθ, l₁, l₂, l₃⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ θ₁ ∧ θ ≤ θ₂ ∧ θ ≤ θ₃ :=
    ⟨min (min θ₁ θ₂) θ₃, lt_min (lt_min hθ₁ hθ₂) hθ₃, (min_le_left _ _).trans (min_le_left _ _),
      (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _⟩
  obtain ⟨M₀, hM₀, m₁, m₂, m₃⟩ : ∃ M₀ : ℝ, 0 < M₀ ∧ M₁ ≤ M₀ ∧ M₂ ≤ M₀ ∧ M₃ ≤ M₀ :=
    ⟨M₁ + M₂ + M₃, by positivity, by linarith, by linarith, by linarith⟩
  have r1 : 0 < θ / 4 := by positivity
  have r2 : 0 < θ / 4 / 4 := by positivity
  have r3 : 0 < θ / 4 / 4 / 4 := by positivity
  have r4 : 0 < θ / 4 / 4 / 4 / 4 := by positivity
  have r5 : 0 < θ / 4 / 4 / 4 / 4 / 4 := by positivity
  obtain ⟨S₀, hS₀, hc₀⟩ := hC θ hθ
  obtain ⟨S₁, hS₁, hc₁⟩ := hC (θ / 4) r1
  obtain ⟨S₂, hS₂, hc₂⟩ := hC (θ / 4 / 4) r2
  obtain ⟨S₃, hS₃, hc₃⟩ := hC (θ / 4 / 4 / 4) r3
  obtain ⟨S₄, hS₄, hc₄⟩ := hC (θ / 4 / 4 / 4 / 4) r4
  obtain ⟨S₅, hS₅, hc₅⟩ := hC (θ / 4 / 4 / 4 / 4 / 4) r5
  have hS₀0 : 0 ≤ S₀ := by linarith
  have hS₁0 : 0 ≤ S₁ := by linarith
  have hS₂0 : 0 ≤ S₂ := by linarith
  have hS₃0 : 0 ≤ S₃ := by linarith
  have hS₄0 : 0 ≤ S₄ := by linarith
  have hM₀0 := hM₀.le
  obtain ⟨c₁, hc₁0, a₁, a₂⟩ : ∃ c : ℝ, 0 ≤ c ∧ M₀ ≤ c ∧ S₀ * M₀ * M₀ ≤ c :=
    ⟨M₀ + S₀ * M₀ * M₀, by positivity, by nlinarith [mul_nonneg (mul_nonneg hS₀0 hM₀0) hM₀0],
      by linarith⟩
  obtain ⟨c₂, hc₂0, b₁, b₂⟩ : ∃ c : ℝ, 0 ≤ c ∧ c₁ + c₁ ≤ c ∧
      S₁ * (c₁ + c₁) * (c₁ + c₁) ≤ c := by
    have : 0 ≤ S₁ * (c₁ + c₁) * (c₁ + c₁) := by positivity
    exact ⟨c₁ + c₁ + S₁ * (c₁ + c₁) * (c₁ + c₁), by positivity, by linarith, by linarith⟩
  obtain ⟨c₃, hc₃0, d₁, d₂⟩ : ∃ c : ℝ, 0 ≤ c ∧ c₂ + c₂ ≤ c ∧
      S₂ * (c₂ + c₂) * (c₂ + c₂) ≤ c := by
    have : 0 ≤ S₂ * (c₂ + c₂) * (c₂ + c₂) := by positivity
    exact ⟨c₂ + c₂ + S₂ * (c₂ + c₂) * (c₂ + c₂), by positivity, by linarith, by linarith⟩
  obtain ⟨c₄, hc₄0, e₁, e₂⟩ : ∃ c : ℝ, 0 ≤ c ∧ c₃ ≤ c ∧ S₃ * c₃ * c₃ ≤ c := by
    have : 0 ≤ S₃ * c₃ * c₃ := by positivity
    exact ⟨c₃ + S₃ * c₃ * c₃, by positivity, by linarith, by linarith⟩
  obtain ⟨c₅, hc₅0, f₁, f₂⟩ : ∃ c : ℝ, 0 ≤ c ∧ c₄ ≤ c ∧ S₄ * c₄ * c₄ ≤ c := by
    have : 0 ≤ S₄ * c₄ * c₄ := by positivity
    exact ⟨c₄ + S₄ * c₄ * c₄, by positivity, by linarith, by linarith⟩
  have hd₁ : 0 ≤ c₁ + c₁ := by positivity
  have hd₂ : 0 ≤ c₂ + c₂ := by positivity
  have le₁ : c₁ ≤ c₁ + c₁ := by linarith
  have le₂ : c₁ + c₁ ≤ c₂ + c₂ := by linarith
  have le₃ : c₂ ≤ c₂ + c₂ := by linarith
  have le₄ : c₂ + c₂ ≤ c₃ := d₁
  refine ⟨5 * c₅ + 1, θ / 4 / 4 / 4 / 4 / 4, by positivity, r5, fun k hk => ?_⟩
  obtain ⟨n₁, h₁⟩ := hR' k hk
  obtain ⟨n₂, h₂⟩ := hA' k hk
  obtain ⟨n₃, h₃⟩ := hF' k hk
  refine ⟨n₁ + n₂ + n₃, fun n hn hn0 => ?_⟩
  intro _ _ _ _ _ _ _ _ z
  have : Finite (Vertex L n k 0) :=
    Finite.of_injective (fun x : Vertex L n k 0 => ((0 : Fin 3), x))
      fun x y h => (Prod.ext_iff.1 h).2
  have : Finite (Face L n k 0) := finite_face
  haveI : Fintype (Fin 3 × Face L n k 0) := Fintype.ofFinite _
  classical
  obtain ⟨gt, gst, -, -, gl, gsl, dgl, dtgl, dsgl⟩ := h₁ n (by omega) hn0
  obtain ⟨fq, -, fr, -, -⟩ := h₂ n (by omega) hn0 z
  obtain ⟨fe, fE, fzt, ff⟩ := h₃ n (by omega) hn0 z
  have cl₀ := hc₀ L n k hL hn0
  have cl₁ := hc₁ L n k hL hn0
  have cl₂ := hc₂ L n k hL hn0
  have cl₃ := hc₃ L n k hL hn0
  have cl₄ := hc₄ L n k hL hn0
  have cl₅ := hc₅ L n k hL hn0
  have gB := localFamily_weaken hC hL hn0 hM₁.le m₁ hθ l₁
    (localFamily_const hC hL hn0 z hM₁.le hθ₁ gl)
  have gS := localFamily_weaken hC hL hn0 hM₁.le m₁ hθ l₁
    (localFamily_const hC hL hn0 z hM₁.le hθ₁ gsl)
  have dG := localFamily_weaken hC hL hn0 hM₁.le m₁ hθ l₁
    (localFamily_const hC hL hn0 z hM₁.le hθ₁ dgl)
  have dtG := localFamily_weaken hC hL hn0 hM₁.le m₁ hθ l₁
    (localFamily_const hC hL hn0 z hM₁.le hθ₁ dtgl)
  have dS := localFamily_weaken hC hL hn0 hM₁.le m₁ hθ l₁
    (localFamily_const hC hL hn0 z hM₁.le hθ₁ dsgl)
  have wq := localFamily_weaken hC hL hn0 hM₂.le m₂ hθ l₂ fq
  have wr := localFamily_weaken hC hL hn0 hM₂.le m₂ hθ l₂ fr
  have we := localFamily_weaken hC hL hn0 hM₃.le m₃ hθ l₃ fe
  have wE := localFamily_weaken hC hL hn0 hM₃.le m₃ hθ l₃ fE
  have wz := localFamily_weaken hC hL hn0 hM₃.le m₃ hθ l₃ fzt
  have wf := localFamily_weaken hC hL hn0 hM₃.le m₃ hθ l₃ ff
  have p₀ : 0 ≤ S₀ * M₀ * M₀ := by positivity
  have p₁ : 0 ≤ S₁ * (c₁ + c₁) * (c₁ + c₁) := by positivity
  have p₂ : 0 ≤ S₂ * (c₂ + c₂) * (c₂ + c₂) := by positivity
  have p₃ : 0 ≤ S₃ * c₃ * c₃ := by positivity
  have p₄ : 0 ≤ S₄ * c₄ * c₄ := by positivity
  have q₀ : θ / 4 ≤ θ := by linarith
  have q₁ : θ / 4 / 4 ≤ θ := by linarith
  have q₂ : θ / 4 / 4 ≤ θ / 4 := by linarith
  have q₃ : θ / 4 / 4 / 4 ≤ θ / 4 / 4 := by linarith
  have q₄ : θ / 4 / 4 / 4 / 4 ≤ θ / 4 / 4 / 4 := by linarith
  have q₅ : θ / 4 / 4 / 4 / 4 / 4 ≤ θ / 4 / 4 / 4 / 4 := by linarith
  have q₆ : θ / 4 / 4 / 4 / 4 / 4 ≤ θ / 4 / 4 / 4 := by linarith
  have q₇ : θ / 4 / 4 / 4 / 4 / 4 ≤ θ / 4 / 4 := by linarith
  have Eg := cl₀.mul _ _ _ _ _ z M₀ M₀ hM₀0 hM₀0 wE gB
  have P := cl₁.add _ _ _ _ z c₁ c₁ (localFamily_weaken hC hL hn0 hM₀0 a₁ r1 q₀ dG)
    (localFamily_weaken hC hL hn0 p₀ a₂ r1 le_rfl Eg)
  have ZP := cl₁.mul _ _ _ _ _ z _ _ hd₁ hd₁
    (localFamily_weaken hC hL hn0 hM₀0 (a₁.trans le₁) r1 q₀ wz) P
  have Pt := cl₁.transpose _ _ _ z _ hd₁ P
  have T1 := cl₂.mul _ _ _ _ _ z _ _ hd₂ hd₂
    (localFamily_weaken hC hL hn0 hd₁ le₂ r2 le_rfl Pt)
    (localFamily_weaken hC hL hn0 p₁ (b₂.trans le₃) r2 le_rfl ZP)
  have g₁ := localFamily_weaken hC hL hn0 hM₀0 (a₁.trans le₁) r1 q₀ gB
  have gf := cl₀.mul _ _ _ _ _ z M₀ M₀ hM₀0 hM₀0 gB wf
  have T2 := cl₁.mul _ _ _ _ _ z _ _ hd₁ hd₁
    (localFamily_weaken hC hL hn0 p₀ (a₂.trans le₁) r1 le_rfl gf) g₁
  have et := cl₀.transpose _ _ _ z M₀ hM₀0 we
  have etg := cl₁.mul _ _ _ _ _ z _ _ hd₁ hd₁
    (localFamily_weaken hC hL hn0 hM₀0 (a₁.trans le₁) r1 le_rfl et) g₁
  have Dg := cl₂.add _ _ _ _ z c₂ c₂
    (localFamily_weaken hC hL hn0 hM₀0 ((a₁.trans le₁).trans b₁) r2 q₁ dtG)
    (localFamily_weaken hC hL hn0 p₁ b₂ r2 le_rfl etg)
  have Dgt := cl₂.transpose _ _ _ z _ hd₂ Dg
  have Dg₃ := localFamily_weaken hC hL hn0 hd₂ le₄ r3 q₃ Dg
  have T3 := cl₃.mul _ _ _ _ _ z _ _ hc₃0 hc₃0
    (localFamily_weaken hC hL hn0 hd₂ le₄ r3 le_rfl Dgt) Dg₃
  have rDg := cl₂.mul _ _ _ _ _ z _ _ hd₂ hd₂
    (localFamily_weaken hC hL hn0 hM₀0 (((a₁.trans le₁).trans b₁).trans le₃) r2 q₁ wr) Dg
  have rDg₃ := localFamily_weaken hC hL hn0 p₂ d₂ r3 le_rfl rDg
  have rDgt := cl₃.transpose _ _ _ z _ hc₃0 rDg₃
  have T4 := cl₄.mul _ _ _ _ _ z _ _ hc₄0 hc₄0
    (localFamily_weaken hC hL hn0 hc₃0 e₁ r4 le_rfl rDgt)
    (localFamily_weaken hC hL hn0 hc₃0 e₁ r4 q₄ rDg₃)
  have qg := cl₀.mul _ _ _ _ _ z M₀ M₀ hM₀0 hM₀0 wq gB
  have qg₁ := localFamily_weaken hC hL hn0 p₀ (a₂.trans le₁) r1 le_rfl qg
  have qgt := cl₁.transpose _ _ _ z _ hd₁ qg₁
  have T5 := cl₂.mul _ _ _ _ _ z _ _ hd₂ hd₂
    (localFamily_weaken hC hL hn0 hd₁ le₂ r2 le_rfl qgt)
    (localFamily_weaken hC hL hn0 hd₁ le₂ r2 q₂ qg₁)
  have b₃ : c₃ ≤ c₅ := e₁.trans f₁
  have n1 : ‖(-1 : ℂ)‖ = 1 := by simp
  have U1 := localFamily_weaken hC hL hn0 p₂ (d₂.trans b₃) r5 q₆ T1
  have U2 := localFamily_weaken hC hL hn0 p₁ (b₂.trans (le₃.trans (le₄.trans b₃))) r5 q₇ T2
  have U3 := localFamily_weaken hC hL hn0 p₃ (e₂.trans f₁) r5 q₅ T3
  have U4 := localFamily_weaken hC hL hn0 p₄ f₂ r5 le_rfl T4
  have U5 := localFamily_weaken hC hL hn0 p₂ (d₂.trans b₃) r5 q₆ T5
  have Sum := cl₅.add _ _ _ _ z _ _ (cl₅.add _ _ _ _ z _ _ (cl₅.add _ _ _ _ z _ _
    (cl₅.add _ _ _ _ z _ _ U1 U2) U3) (cl₅.smul _ _ _ z _ (-1 : ℂ) U4)) U5
  have eP : ∀ s t, Matrix.of (scaledEdgeCoboundaryKernel L n k 0) *
      periodicEdgeResolventSqrt L n k +
      holonomyDefectAlongBackground L n k z s t * periodicEdgeResolventSqrt L n k =
      (Matrix.of (scaledEdgeCoboundaryKernel L n k 0) +
        holonomyDefectAlongBackground L n k z s t) * periodicEdgeResolventSqrt L n k :=
    fun s t => (Matrix.add_mul _ _ _).symm
  have eD : ∀ s t, (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).D).transpose *
      periodicEdgeResolventSqrt L n k +
      (covariantDifferenceDefect L n k z s t).transpose * periodicEdgeResolventSqrt L n k =
      (Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).D).transpose *
        periodicEdgeResolventSqrt L n k := by
    intro s t
    rw [← Matrix.add_mul, ← Matrix.transpose_add]
    unfold covariantDifferenceDefect
    rw [add_sub_cancel]
  simp only [eP, eD] at Sum
  have hX : IsLocalAlongBackground colouredEdgeCell colouredEdgeCell (xiConjugated L n k z) z
      (5 * c₅ + 1) (θ / 4 / 4 / 4 / 4 / 4) := by
    rw [show xiConjugated L n k z = _ from
      funext₂ fun s t => xiConjugated_eq hH hL hk hn0 z s t gt]
    exact localFamily_weaken hC hL hn0 (by rw [n1]; positivity) (by rw [n1]; linarith) r5
      le_rfl Sum
  have eg := cl₀.mul _ _ _ _ _ z M₀ M₀ hM₀0 hM₀0 we gS
  have Wf := cl₁.add _ _ _ _ z c₁ c₁ (localFamily_weaken hC hL hn0 hM₀0 a₁ r1 q₀ dS)
    (localFamily_weaken hC hL hn0 p₀ a₂ r1 le_rfl eg)
  have Wt := cl₁.transpose _ _ _ z _ hd₁ Wf
  have T6 := cl₂.mul _ _ _ _ _ z _ _ hd₂ hd₂
    (localFamily_weaken hC hL hn0 hd₁ le₂ r2 le_rfl Wt)
    (localFamily_weaken hC hL hn0 hd₁ le₂ r2 q₂ Wf)
  have rg := cl₀.mul _ _ _ _ _ z M₀ M₀ hM₀0 hM₀0 wr gS
  have rg₁ := localFamily_weaken hC hL hn0 p₀ (a₂.trans le₁) r1 le_rfl rg
  have rgt := cl₁.transpose _ _ _ z _ hd₁ rg₁
  have T7 := cl₂.mul _ _ _ _ _ z _ _ hd₂ hd₂
    (localFamily_weaken hC hL hn0 hd₁ le₂ r2 le_rfl rgt)
    (localFamily_weaken hC hL hn0 hd₁ le₂ r2 q₂ rg₁)
  have Sum' := cl₅.add _ _ _ _ z _ _
    (localFamily_weaken hC hL hn0 p₂ (d₂.trans b₃) r5 q₆ T6)
    (localFamily_weaken hC hL hn0 p₂ (d₂.trans b₃) r5 q₆ T7)
  have eW : ∀ s t, Matrix.of (rescaledOperators L n k (trivialField L n k 0)).D *
      periodicVertexResolventSqrt L n k +
      covariantDifferenceDefect L n k z s t * periodicVertexResolventSqrt L n k =
      Matrix.of (rescaledOperators L n k (twoSourceBackground L n k z s t)).D *
        periodicVertexResolventSqrt L n k := by
    intro s t
    rw [← Matrix.add_mul]
    unfold covariantDifferenceDefect
    rw [add_sub_cancel]
  simp only [eW] at Sum'
  have hY : IsLocalAlongBackground colouredVertexCell colouredVertexCell (yConjugated L n k z) z
      (5 * c₅ + 1) (θ / 4 / 4 / 4 / 4 / 4) := by
    rw [show yConjugated L n k z = _ from funext₂ fun s t => yConjugated_eq hL z s t gst]
    exact localFamily_weaken hC hL hn0 (by positivity) (by linarith) r5 le_rfl Sum'
  exact ⟨hX, hY⟩
end YangMills.Construction.RunningCouplingSlope.ConjugatedFamilies
end
