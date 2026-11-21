import YangMills.Construction.LinearAlgebra.BivectorsReflectionsAngles
import YangMills.Construction.Lattice.AxisBivectorBasis
import YangMills.Construction.LinearAlgebra.SignsOfCoordinatePlanesAndEntriesOfTwoVectors
import Mathlib
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotionsProof
set_option autoImplicit false

section
open Matrix YangMills.Construction.Exterior
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def ExteriorSquareTraceHodgeFacts : Prop :=
  (∀ u v : Fin 4 → ℝ, wedgeProd v u = -wedgeProd u v) ∧
  (∀ (μ ν : Fin 4) (h : μ < ν),
      wedgeProd (Pi.single μ 1) (Pi.single ν 1) = axisBivector ⟨μ, ν, h⟩) ∧
  (∀ (ω : Bivector) (μ ν : Fin 4),
      ω.1 μ ν = inner ℝ (wedgeProd (Pi.single μ 1) (Pi.single ν 1)) ω) ∧
  (∀ (S : Bivector →ₗ[ℝ] Bivector) (μ ν ρ σ : Fin 4),
      endEntry S ν μ ρ σ = -endEntry S μ ν ρ σ ∧
      endEntry S μ ν σ ρ = -endEntry S μ ν ρ σ) ∧
  (∀ (S : Bivector →ₗ[ℝ] Bivector) (P Q : AxisPlane),
      endEntry S P.lower P.upper Q.lower Q.upper = bivectorMatrixEntry S P Q) ∧
  (∀ u v u' v' : Fin 4 → ℝ,
      inner ℝ (wedgeProd u v) (wedgeProd u' v') = (u ⬝ᵥ u') * (v ⬝ᵥ v') - (u ⬝ᵥ v') * (v ⬝ᵥ u')) ∧
  (∀ (T : Matrix (Fin 4) (Fin 4) ℝ) (u v : Fin 4 → ℝ),
      exteriorSq T (wedgeProd u v) = wedgeProd (T *ᵥ u) (T *ᵥ v)) ∧
  (∀ (T : Matrix (Fin 4) (Fin 4) ℝ) (μ ν ρ σ : Fin 4),
      endEntry (exteriorSq T) μ ν ρ σ = T μ ρ * T ν σ - T μ σ * T ν ρ) ∧
  Submodule.span ℝ {ω : Bivector | ∃ u v : Fin 4 → ℝ, ω = wedgeProd u v} = ⊤ ∧
  (∀ S T : Matrix (Fin 4) (Fin 4) ℝ,
      exteriorSq (S * T) = exteriorSq S ∘ₗ exteriorSq T) ∧
  exteriorSq 1 = LinearMap.id ∧
  (∀ T : Matrix (Fin 4) (Fin 4) ℝ,
      LinearMap.adjoint (exteriorSq T) = exteriorSq Tᵀ) ∧
  (∀ T : Matrix (Fin 4) (Fin 4) ℝ, T ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
      LinearMap.adjoint (exteriorSq T) ∘ₗ exteriorSq T = LinearMap.id) ∧
  (∀ T : Matrix (Fin 4) (Fin 4) ℝ, Tᵀ = T → IsSelfAdjointMap (exteriorSq T)) ∧
  (∀ T : Matrix (Fin 4) (Fin 4) ℝ,
      bivectorTrace (exteriorSq T) = (1 / 2) * (T.trace ^ 2 - (T ^ 2).trace) ∧
      ∀ lam : Fin 4 → ℂ,
        Finset.univ.val.map lam = (T.charpoly.map (algebraMap ℝ ℂ)).roots →
        (bivectorTrace (exteriorSq T) : ℂ) =
          ∑ p ∈ ascPairs, lam p.1 * lam p.2) ∧
  (∀ ω η : Bivector,
      wedgeVolume ω η =
        ∑ P : AxisPlane, ∑ Q : AxisPlane,
          bivectorComponent ω P * bivectorComponent η Q * (axisPlaneSign P Q : ℝ) ∧
      wedgeVolume η ω = wedgeVolume ω η) ∧
  (∀ P Q : AxisPlane, bivectorMatrixEntry hodge P Q = (axisPlaneSign P Q : ℝ)) ∧
  IsSelfAdjointMap hodge ∧
  LinearMap.adjoint hodge ∘ₗ hodge = LinearMap.id ∧
  hodge ∘ₗ hodge = LinearMap.id ∧
  (∀ Q : AxisPlane,
      hodge (axisBivector Q) =
        (axisPlaneSign Q.opposite Q : ℝ) • axisBivector Q.opposite) ∧
  hodge (axisBivector ⟨0, 1, by decide⟩) = axisBivector ⟨2, 3, by decide⟩ ∧
  hodge (axisBivector ⟨2, 3, by decide⟩) = axisBivector ⟨0, 1, by decide⟩ ∧
  hodge (axisBivector ⟨0, 2, by decide⟩) = -axisBivector ⟨1, 3, by decide⟩ ∧
  hodge (axisBivector ⟨1, 3, by decide⟩) = -axisBivector ⟨0, 2, by decide⟩ ∧
  hodge (axisBivector ⟨0, 3, by decide⟩) = axisBivector ⟨1, 2, by decide⟩ ∧
  hodge (axisBivector ⟨1, 2, by decide⟩) = axisBivector ⟨0, 3, by decide⟩ ∧
  (∀ v₁ v₂ v₃ v₄ : Fin 4 → ℝ,
      wedgeVolume (wedgeProd v₁ v₂) (wedgeProd v₃ v₄) = ((Matrix.of ![v₁, v₂, v₃, v₄])ᵀ).det) ∧
  (∀ (T : Matrix (Fin 4) (Fin 4) ℝ) (ω η : Bivector),
      wedgeVolume (exteriorSq T ω) (exteriorSq T η) = T.det * wedgeVolume ω η) ∧
  (∀ T : Matrix (Fin 4) (Fin 4) ℝ, T ∈ Matrix.orthogonalGroup (Fin 4) ℝ →
      hodge ∘ₗ exteriorSq T = T.det • (exteriorSq T ∘ₗ hodge))
end YangMills.Construction.PeriodicLattice
end
end

noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrix YangMills.Construction.Exterior
private theorem wedgeProd_apply_entry (u v : Fin 4 → ℝ) (i j : Fin 4) :
    (wedgeProd u v).1 i j = u i * v j - v i * u j := by
  simp [wedgeProd, Matrix.sub_apply, vecMulVec_apply]
private theorem bivector_diag_entry (ω : Bivector) (i : Fin 4) : ω.1 i i = 0 := by
  have := ω.apply_swap i i
  linarith
private theorem bivector_entries_explicit (ω : Bivector) :
    ω.1 0 0 = 0 ∧ ω.1 1 1 = 0 ∧ ω.1 2 2 = 0 ∧ ω.1 3 3 = 0 ∧
    ω.1 1 0 = -ω.1 0 1 ∧ ω.1 2 0 = -ω.1 0 2 ∧ ω.1 3 0 = -ω.1 0 3 ∧
    ω.1 2 1 = -ω.1 1 2 ∧ ω.1 3 1 = -ω.1 1 3 ∧ ω.1 3 2 = -ω.1 2 3 :=
  ⟨bivector_diag_entry ω 0, bivector_diag_entry ω 1, bivector_diag_entry ω 2,
    bivector_diag_entry ω 3,
    ω.apply_swap 0 1, ω.apply_swap 0 2, ω.apply_swap 0 3,
    ω.apply_swap 1 2, ω.apply_swap 1 3, ω.apply_swap 2 3⟩
private theorem bivInner_eq_half_trace_transpose_mul (ω η : Bivector) :
    inner ℝ ω η = (1 / 2) * (ω.1ᵀ * η.1).trace := by
  rw [inner_eq_bivInner, bivInner_eq_sum_six]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_four]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := bivector_entries_explicit ω
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := bivector_entries_explicit η
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]
  ring
private theorem inner_wedgeProd_left_eq_dotProduct (u v : Fin 4 → ℝ) (ω : Bivector) :
    inner ℝ (wedgeProd u v) ω = u ⬝ᵥ (ω.1 *ᵥ v) := by
  rw [inner_eq_bivInner, bivInner_eq_sum_six]
  simp only [wedgeProd_apply_entry, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := bivector_entries_explicit ω
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  ring
private theorem bivector_entry_eq_inner_basis_wedge (ω : Bivector) (i j : Fin 4) :
    ω.1 i j = inner ℝ (wedgeProd (Pi.single i 1) (Pi.single j 1)) ω := by
  rw [inner_wedgeProd_left_eq_dotProduct]
  simp
private theorem exteriorSq_matrix (T : Matrix (Fin 4) (Fin 4) ℝ) (ω : Bivector) :
    (exteriorSq T ω).1 = T * ω.1 * Tᵀ := rfl
private theorem exteriorSq_wedgeProd (T : Matrix (Fin 4) (Fin 4) ℝ) (u v : Fin 4 → ℝ) :
    exteriorSq T (wedgeProd u v) = wedgeProd (T *ᵥ u) (T *ᵥ v) := by
  apply Bivector.ext
  change T * (vecMulVec u v - vecMulVec v u) * Tᵀ =
    vecMulVec (T *ᵥ u) (T *ᵥ v) - vecMulVec (T *ᵥ v) (T *ᵥ u)
  rw [Matrix.mul_sub, Matrix.sub_mul, mul_vecMulVec, mul_vecMulVec, vecMulVec_mul, vecMulVec_mul,
    vecMul_transpose, vecMul_transpose]
abbrev _root_.YangMills.SharedProofs.p95030 := @exteriorSq_wedgeProd
private theorem wedgeProd_swap (u v : Fin 4 → ℝ) : wedgeProd v u = -wedgeProd u v := by
  apply Bivector.ext
  ext i j
  change (wedgeProd v u).1 i j = -(wedgeProd u v).1 i j
  rw [wedgeProd_apply_entry, wedgeProd_apply_entry]
  ring
abbrev _root_.YangMills.SharedProofs.p1483 := @wedgeProd_swap
private theorem endEntry_exteriorSq (h : BivectorInnerMinorsReflectionDet)
    (T : Matrix (Fin 4) (Fin 4) ℝ) (i j k l : Fin 4) :
    endEntry (exteriorSq T) i j k l = T i k * T j l - T i l * T j k := by
  rw [endEntry, exteriorSq_wedgeProd, h.1]
  simp
private theorem span_wedgeProds_eq_top :
    Submodule.span ℝ {ω : Bivector | ∃ u v : Fin 4 → ℝ, ω = wedgeProd u v} = ⊤ := by
  rw [eq_top_iff]
  refine top_le_span_axisBivector.trans (Submodule.span_mono ?_)
  rintro _ ⟨P, rfl⟩
  exact ⟨_, _, rfl⟩
private theorem bivector_induction_wedgeProd {p : Bivector → Prop}
    (hadd : ∀ a b, p a → p b → p (a + b)) (hsmul : ∀ (c : ℝ) a, p a → p (c • a))
    (hw : ∀ u v, p (wedgeProd u v)) (ω : Bivector) : p ω := by
  have hω : ω ∈ Submodule.span ℝ {ω : Bivector | ∃ u v : Fin 4 → ℝ, ω = wedgeProd u v} := by
    rw [span_wedgeProds_eq_top]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, v, rfl⟩ := hx
    exact hw u v
  | zero => simpa using hsmul 0 _ (hw 0 0)
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx
private theorem exteriorSq_mul (S T : Matrix (Fin 4) (Fin 4) ℝ) :
    exteriorSq (S * T) = exteriorSq S ∘ₗ exteriorSq T := by
  refine LinearMap.ext fun ω => Bivector.ext ?_
  change S * T * ω.1 * (S * T)ᵀ = S * (T * ω.1 * Tᵀ) * Sᵀ
  simp [Matrix.transpose_mul, Matrix.mul_assoc]
private theorem exteriorSq_one : exteriorSq 1 = LinearMap.id := by
  refine LinearMap.ext fun ω => Bivector.ext ?_
  change 1 * ω.1 * (1 : Matrix (Fin 4) (Fin 4) ℝ)ᵀ = ω.1
  simp
private theorem inner_exteriorSq_eq_inner_transpose (T : Matrix (Fin 4) (Fin 4) ℝ)
    (ω η : Bivector) :
    inner ℝ (exteriorSq T ω) η = inner ℝ ω (exteriorSq Tᵀ η) := by
  rw [bivInner_eq_half_trace_transpose_mul, bivInner_eq_half_trace_transpose_mul,
    exteriorSq_matrix, exteriorSq_matrix]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm T]
  simp only [Matrix.mul_assoc]
private theorem adjoint_exteriorSq (T : Matrix (Fin 4) (Fin 4) ℝ) :
    LinearMap.adjoint (exteriorSq T) = exteriorSq Tᵀ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro ω η
  have := inner_exteriorSq_eq_inner_transpose Tᵀ ω η
  rwa [Matrix.transpose_transpose] at this
private theorem orthogonal_transpose_mul_self {T : Matrix (Fin 4) (Fin 4) ℝ}
    (hT : T ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : Tᵀ * T = 1 := by apply _root_.YangMills.Construction.ConfigSpace.orth_transpose_mul_self <;> assumption
private theorem orthogonal_mul_transpose_self {T : Matrix (Fin 4) (Fin 4) ℝ}
    (hT : T ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : T * Tᵀ = 1 := by apply _root_.YangMills.Construction.Tower.OrthogonalMotions.orth_mul_transpose_self <;> assumption
private theorem sum_axisPlane_six {M : Type*} [AddCommMonoid M] (f : AxisPlane → M) :
    ∑ P, f P = f ⟨0, 1, by decide⟩ + f ⟨0, 2, by decide⟩ + f ⟨0, 3, by decide⟩ +
      f ⟨1, 2, by decide⟩ + f ⟨1, 3, by decide⟩ + f ⟨2, 3, by decide⟩ := by
  classical
  have huniv : (Finset.univ : Finset AxisPlane) =
      {⟨0, 1, by decide⟩, ⟨0, 2, by decide⟩, ⟨0, 3, by decide⟩, ⟨1, 2, by decide⟩,
        ⟨1, 3, by decide⟩, ⟨2, 3, by decide⟩} := by
    ext ⟨a, b, hab⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      AxisPlane.mk.injEq, true_iff]
    revert a b
    decide
  rw [huniv]
  repeat rw [Finset.sum_insert (by simp)]
  rw [Finset.sum_singleton]
  simp only [add_assoc]
private theorem axisPlaneSign_values :
    axisPlaneSign ⟨0, 1, by decide⟩ ⟨0, 1, by decide⟩ = 0 ∧
    axisPlaneSign ⟨0, 1, by decide⟩ ⟨0, 2, by decide⟩ = 0 ∧
    axisPlaneSign ⟨0, 1, by decide⟩ ⟨0, 3, by decide⟩ = 0 ∧
    axisPlaneSign ⟨0, 1, by decide⟩ ⟨1, 2, by decide⟩ = 0 ∧
    axisPlaneSign ⟨0, 1, by decide⟩ ⟨1, 3, by decide⟩ = 0 ∧
    axisPlaneSign ⟨0, 1, by decide⟩ ⟨2, 3, by decide⟩ = 1 ∧
    axisPlaneSign ⟨0, 2, by decide⟩ ⟨0, 1, by decide⟩ = 0 ∧
    axisPlaneSign ⟨0, 2, by decide⟩ ⟨0, 2, by decide⟩ = 0 ∧
    axisPlaneSign ⟨0, 2, by decide⟩ ⟨0, 3, by decide⟩ = 0 ∧
    axisPlaneSign ⟨0, 2, by decide⟩ ⟨1, 2, by decide⟩ = 0 ∧
    axisPlaneSign ⟨0, 2, by decide⟩ ⟨1, 3, by decide⟩ = -1 ∧
    axisPlaneSign ⟨0, 2, by decide⟩ ⟨2, 3, by decide⟩ = 0 ∧
    axisPlaneSign ⟨0, 3, by decide⟩ ⟨0, 1, by decide⟩ = 0 ∧
    axisPlaneSign ⟨0, 3, by decide⟩ ⟨0, 2, by decide⟩ = 0 ∧
    axisPlaneSign ⟨0, 3, by decide⟩ ⟨0, 3, by decide⟩ = 0 ∧
    axisPlaneSign ⟨0, 3, by decide⟩ ⟨1, 2, by decide⟩ = 1 ∧
    axisPlaneSign ⟨0, 3, by decide⟩ ⟨1, 3, by decide⟩ = 0 ∧
    axisPlaneSign ⟨0, 3, by decide⟩ ⟨2, 3, by decide⟩ = 0 ∧
    axisPlaneSign ⟨1, 2, by decide⟩ ⟨0, 1, by decide⟩ = 0 ∧
    axisPlaneSign ⟨1, 2, by decide⟩ ⟨0, 2, by decide⟩ = 0 ∧
    axisPlaneSign ⟨1, 2, by decide⟩ ⟨0, 3, by decide⟩ = 1 ∧
    axisPlaneSign ⟨1, 2, by decide⟩ ⟨1, 2, by decide⟩ = 0 ∧
    axisPlaneSign ⟨1, 2, by decide⟩ ⟨1, 3, by decide⟩ = 0 ∧
    axisPlaneSign ⟨1, 2, by decide⟩ ⟨2, 3, by decide⟩ = 0 ∧
    axisPlaneSign ⟨1, 3, by decide⟩ ⟨0, 1, by decide⟩ = 0 ∧
    axisPlaneSign ⟨1, 3, by decide⟩ ⟨0, 2, by decide⟩ = -1 ∧
    axisPlaneSign ⟨1, 3, by decide⟩ ⟨0, 3, by decide⟩ = 0 ∧
    axisPlaneSign ⟨1, 3, by decide⟩ ⟨1, 2, by decide⟩ = 0 ∧
    axisPlaneSign ⟨1, 3, by decide⟩ ⟨1, 3, by decide⟩ = 0 ∧
    axisPlaneSign ⟨1, 3, by decide⟩ ⟨2, 3, by decide⟩ = 0 ∧
    axisPlaneSign ⟨2, 3, by decide⟩ ⟨0, 1, by decide⟩ = 1 ∧
    axisPlaneSign ⟨2, 3, by decide⟩ ⟨0, 2, by decide⟩ = 0 ∧
    axisPlaneSign ⟨2, 3, by decide⟩ ⟨0, 3, by decide⟩ = 0 ∧
    axisPlaneSign ⟨2, 3, by decide⟩ ⟨1, 2, by decide⟩ = 0 ∧
    axisPlaneSign ⟨2, 3, by decide⟩ ⟨1, 3, by decide⟩ = 0 ∧
    axisPlaneSign ⟨2, 3, by decide⟩ ⟨2, 3, by decide⟩ = 0 := by
  decide +kernel
private theorem wedgeVolume_symm (ω η : Bivector) : wedgeVolume η ω = wedgeVolume ω η := by
  simp only [wedgeVolume]
  ring
private theorem wedgeVolume_eq_double_sum (ω η : Bivector) :
    wedgeVolume ω η = ∑ P : AxisPlane, ∑ Q : AxisPlane,
      bivectorComponent ω P * bivectorComponent η Q * (axisPlaneSign P Q : ℝ) := by
  simp only [sum_axisPlane_six, axisPlaneSign_values, bivectorComponent, wedgeVolume]
  simp
  ring
open Classical in
private theorem bivectorComponent_axisBivector (P P' : AxisPlane) :
    bivectorComponent (axisBivector P) P' = if P' = P then 1 else 0 := by
  rw [bivectorComponent, axisBivector_apply P P'.lower_lt_upper]
  by_cases hP : P' = P
  · simp [hP]
  · have hnot : ¬(P'.lower = P.lower ∧ P'.upper = P.upper) :=
      fun e => hP (AxisPlane.ext e.1 e.2)
    rw [if_neg hnot, if_neg hP]
private theorem bivectorMatrixEntry_hodge (P Q : AxisPlane) :
    bivectorMatrixEntry hodge P Q = (axisPlaneSign P Q : ℝ) := by
  classical
  rw [bivectorMatrixEntry, inner_hodge, wedgeVolume_eq_double_sum]
  simp [bivectorComponent_axisBivector]
private theorem hodge_isSelfAdjointMap : IsSelfAdjointMap hodge := by
  intro ω η
  rw [inner_hodge, real_inner_comm, inner_hodge, wedgeVolume_symm]
private theorem adjoint_hodge_eq : LinearMap.adjoint hodge = hodge := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro ω η
  exact (hodge_isSelfAdjointMap ω η).symm
private theorem hodge_comp_hodge : hodge ∘ₗ hodge = LinearMap.id := by
  refine LinearMap.ext fun η => Bivector.ext ?_
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := bivector_entries_explicit η
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hodge, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
private theorem hodge_axisBivector_eq_sum (Q : AxisPlane) :
    hodge (axisBivector Q) = ∑ P, (axisPlaneSign P Q : ℝ) • axisBivector P := by
  conv_lhs => rw [← axisBivectorBasis.sum_repr' (hodge (axisBivector Q))]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [axisBivectorBasis_apply, ← bivectorMatrixEntry_hodge]
  rfl
private theorem hodge_axisBivector_eq_opposite (Q : AxisPlane) :
    hodge (axisBivector Q) =
      (axisPlaneSign Q.opposite Q : ℝ) • axisBivector Q.opposite := by
  rw [hodge_axisBivector_eq_sum, Finset.sum_eq_single Q.opposite]
  · intro P _ hP
    have hnd : ¬P.IsDisjoint Q := fun hd =>
      hP (AxisPlane.eq_opposite_of_isDisjoint
        ⟨hd.1.symm, hd.2.2.1.symm, hd.2.1.symm, hd.2.2.2.symm⟩)
    rw [axisPlaneSign_eq_zero_of_not_isDisjoint hnd]
    simp
  · intro hQ
    exact absurd (Finset.mem_univ _) hQ
private theorem wedgeVolume_add_fst (a b η : Bivector) :
    wedgeVolume (a + b) η = wedgeVolume a η + wedgeVolume b η := by
  simp only [wedgeVolume, Bivector.add_val, Matrix.add_apply]
  ring
private theorem wedgeVolume_smul_fst (c : ℝ) (a η : Bivector) :
    wedgeVolume (c • a) η = c * wedgeVolume a η := by
  simp only [wedgeVolume, Bivector.smul_val, Matrix.smul_apply, smul_eq_mul]
  ring
private theorem wedgeVolume_add_snd (ω a b : Bivector) :
    wedgeVolume ω (a + b) = wedgeVolume ω a + wedgeVolume ω b := by
  simp only [wedgeVolume, Bivector.add_val, Matrix.add_apply]
  ring
private theorem wedgeVolume_smul_snd (c : ℝ) (ω a : Bivector) :
    wedgeVolume ω (c • a) = c * wedgeVolume ω a := by
  simp only [wedgeVolume, Bivector.smul_val, Matrix.smul_apply, smul_eq_mul]
  ring
private theorem wedgeVolume_exteriorSq (h : BivectorInnerMinorsReflectionDet)
    (T : Matrix (Fin 4) (Fin 4) ℝ) (ω η : Bivector) :
    wedgeVolume (exteriorSq T ω) (exteriorSq T η) = T.det * wedgeVolume ω η := by
  have hdet := h.2.2.2.2
  induction ω using bivector_induction_wedgeProd with
  | hadd a b ha hb => rw [map_add, wedgeVolume_add_fst, wedgeVolume_add_fst, ha, hb]; ring
  | hsmul c a ha => rw [map_smul, wedgeVolume_smul_fst, wedgeVolume_smul_fst, ha]; ring
  | hw u v =>
    induction η using bivector_induction_wedgeProd with
    | hadd a b ha hb => rw [map_add, wedgeVolume_add_snd, wedgeVolume_add_snd, ha, hb]; ring
    | hsmul c a ha => rw [map_smul, wedgeVolume_smul_snd, wedgeVolume_smul_snd, ha]; ring
    | hw u' v' =>
      rw [exteriorSq_wedgeProd, exteriorSq_wedgeProd, hdet, hdet, ← Matrix.det_mul]
      congr 1
      ext i j
      fin_cases j <;> simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
private theorem hodge_comp_exteriorSq (h : BivectorInnerMinorsReflectionDet)
    {T : Matrix (Fin 4) (Fin 4) ℝ} (hT : T ∈ Matrix.orthogonalGroup (Fin 4) ℝ) :
    hodge ∘ₗ exteriorSq T = T.det • (exteriorSq T ∘ₗ hodge) := by
  refine LinearMap.ext fun η => ext_inner_left ℝ fun ω => ?_
  have hω : ω = exteriorSq T (exteriorSq Tᵀ ω) := by
    have h1 := LinearMap.congr_fun (exteriorSq_mul T Tᵀ) ω
    rw [orthogonal_mul_transpose_self hT, exteriorSq_one] at h1
    exact h1
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  rw [inner_hodge, inner_smul_right]
  calc wedgeVolume ω (exteriorSq T η)
      = wedgeVolume (exteriorSq T (exteriorSq Tᵀ ω)) (exteriorSq T η) := by rw [← hω]
    _ = T.det * wedgeVolume (exteriorSq Tᵀ ω) η := wedgeVolume_exteriorSq h T _ _
    _ = T.det * inner ℝ ω (exteriorSq T (hodge η)) := by
      rw [← inner_hodge, inner_exteriorSq_eq_inner_transpose, Matrix.transpose_transpose]
private theorem hodge_axisBivector_values :
    hodge (axisBivector ⟨0, 1, by decide⟩) = axisBivector ⟨2, 3, by decide⟩ ∧
    hodge (axisBivector ⟨2, 3, by decide⟩) = axisBivector ⟨0, 1, by decide⟩ ∧
    hodge (axisBivector ⟨0, 2, by decide⟩) = -axisBivector ⟨1, 3, by decide⟩ ∧
    hodge (axisBivector ⟨1, 3, by decide⟩) = -axisBivector ⟨0, 2, by decide⟩ ∧
    hodge (axisBivector ⟨0, 3, by decide⟩) = axisBivector ⟨1, 2, by decide⟩ ∧
    hodge (axisBivector ⟨1, 2, by decide⟩) = axisBivector ⟨0, 3, by decide⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hodge_axisBivector_eq_sum, sum_axisPlane_six]
     simp only [axisPlaneSign_values]
     simp)
private theorem bivectorTrace_exteriorSq (h : BivectorInnerMinorsReflectionDet)
    (T : Matrix (Fin 4) (Fin 4) ℝ) :
    bivectorTrace (exteriorSq T) = (1 / 2) * (T.trace ^ 2 - (T ^ 2).trace) := by
  have he : ∀ P, bivectorMatrixEntry (exteriorSq T) P P =
      T P.lower P.lower * T P.upper P.upper - T P.lower P.upper * T P.upper P.lower :=
    fun P => endEntry_exteriorSq h T P.lower P.upper P.lower P.upper
  simp only [bivectorTrace, he, sum_axisPlane_six]
  simp only [Matrix.trace, Matrix.diag, sq, Matrix.mul_apply, Fin.sum_univ_four]
  ring
private theorem trace_and_trace_sq_eq_sum_roots (A : Matrix (Fin 4) (Fin 4) ℂ)
    (lam : Fin 4 → ℂ) (hlam : Finset.univ.val.map lam = A.charpoly.roots) :
    A.trace = ∑ i, lam i ∧ (A ^ 2).trace = ∑ i, lam i ^ 2 := by
  have hev : ∀ z : ℂ, A.charpoly.eval z = ∏ i, (z - lam i) := by
    intro z
    have hz := (IsAlgClosed.splits A.charpoly).eval_eq_prod_roots_of_monic A.charpoly_monic z
    rw [hz, ← hlam, Multiset.map_map]
    rfl
  have hs : ∀ c : ℂ, Matrix.scalar (Fin 4) c = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    intro c
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  have hsq : ∀ z : ℂ, (A ^ 2).charpoly.eval (z ^ 2) = ∏ i, (z ^ 2 - lam i ^ 2) := by
    intro z
    have hc : Commute (z • (1 : Matrix (Fin 4) (Fin 4) ℂ)) A := (Commute.one_left A).smul_left z
    have hfac : Matrix.scalar (Fin 4) (z ^ 2) - A ^ 2 =
        -(Matrix.scalar (Fin 4) (-z) - A) * (Matrix.scalar (Fin 4) z - A) := by
      have e1 : Matrix.scalar (Fin 4) (z ^ 2) = (z • (1 : Matrix (Fin 4) (Fin 4) ℂ)) ^ 2 := by
        rw [hs, smul_pow, one_pow]
      have e2 : -(Matrix.scalar (Fin 4) (-z) - A) = z • (1 : Matrix (Fin 4) (Fin 4) ℂ) + A := by
        rw [hs, neg_smul]
        abel
      rw [e1, e2, hs z, hc.sq_sub_sq]
    rw [Matrix.eval_charpoly, hfac, Matrix.det_mul, Matrix.det_neg, ← Matrix.eval_charpoly,
      ← Matrix.eval_charpoly, hev, hev]
    simp only [Fin.prod_univ_four, Fintype.card_fin]
    ring
  have hp : (A ^ 2).charpoly = ∏ i, (Polynomial.X - Polynomial.C (lam i ^ 2)) := by
    apply Polynomial.funext
    intro w
    obtain ⟨z, rfl⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) two_pos
    rw [hsq z, Polynomial.eval_prod]
    simp
  have hm : ∏ i, (Polynomial.X - Polynomial.C (lam i ^ 2)) =
      ((Finset.univ.val.map fun i => lam i ^ 2).map
        fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.map_map]
    rfl
  refine ⟨?_, ?_⟩
  · rw [Matrix.trace_eq_sum_roots_charpoly, ← hlam]
    rfl
  · rw [Matrix.trace_eq_sum_roots_charpoly, hp, hm, Polynomial.roots_multiset_prod_X_sub_C]
    rfl
private theorem bivectorTrace_exteriorSq_eq_sum_eigen (h : BivectorInnerMinorsReflectionDet)
    (T : Matrix (Fin 4) (Fin 4) ℝ) (lam : Fin 4 → ℂ)
    (hl : Finset.univ.val.map lam = (T.charpoly.map (algebraMap ℝ ℂ)).roots) :
    (bivectorTrace (exteriorSq T) : ℂ) = ∑ p ∈ ascPairs, lam p.1 * lam p.2 := by
  have hmap : (T.map (algebraMap ℝ ℂ)).charpoly = T.charpoly.map (algebraMap ℝ ℂ) :=
    T.charpoly_map _
  obtain ⟨h1, h2⟩ :=
    trace_and_trace_sq_eq_sum_roots (T.map (algebraMap ℝ ℂ)) lam (by rw [hmap]; exact hl)
  have t1 : (T.map (algebraMap ℝ ℂ)).trace = (T.trace : ℂ) := by
    simp [Matrix.trace, Fin.sum_univ_four]
  have t2 : ((T.map (algebraMap ℝ ℂ)) ^ 2).trace = ((T ^ 2).trace : ℂ) := by
    simp [Matrix.trace, Fin.sum_univ_four, sq, Matrix.mul_apply]
  have hpairs : ascPairs = {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide
  rw [t1] at h1
  rw [t2] at h2
  rw [bivectorTrace_exteriorSq h, hpairs]
  push_cast
  rw [h1, h2]
  simp [Fin.sum_univ_four]
  ring
theorem exteriorSquareTraceHodgeFacts_of_minors (h : BivectorInnerMinorsReflectionDet) :
    ExteriorSquareTraceHodgeFacts := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hodge_axisBivector_values
  unfold ExteriorSquareTraceHodgeFacts
  refine ⟨fun u v => wedgeProd_swap u v, fun i j hij => rfl, bivector_entry_eq_inner_basis_wedge,
    ?_, fun S P Q => rfl,
    h.1, exteriorSq_wedgeProd, endEntry_exteriorSq h, span_wedgeProds_eq_top, exteriorSq_mul,
    exteriorSq_one, adjoint_exteriorSq, ?_, ?_,
    fun T => ⟨bivectorTrace_exteriorSq h T, bivectorTrace_exteriorSq_eq_sum_eigen h T⟩,
    fun ω η => ⟨wedgeVolume_eq_double_sum ω η, wedgeVolume_symm ω η⟩,
    bivectorMatrixEntry_hodge, hodge_isSelfAdjointMap, ?_, hodge_comp_hodge,
    hodge_axisBivector_eq_opposite,
    s1, s2, s3, s4, s5, s6, h.2.2.2.2, wedgeVolume_exteriorSq h,
    fun T hT => hodge_comp_exteriorSq h hT⟩
  · intro S i j k l
    refine ⟨?_, ?_⟩
    · rw [endEntry, endEntry, wedgeProd_swap (Pi.single i 1) (Pi.single j 1),
        inner_neg_left]
    · rw [endEntry, endEntry, wedgeProd_swap (Pi.single k 1) (Pi.single l 1),
        map_neg, inner_neg_right]
  · intro T hT
    rw [adjoint_exteriorSq, ← exteriorSq_mul, orthogonal_transpose_mul_self hT, exteriorSq_one]
  · intro T hT ω η
    rw [inner_exteriorSq_eq_inner_transpose, hT]
  · rw [adjoint_hodge_eq]
    exact hodge_comp_hodge
end YangMills.Construction.PeriodicLattice
end
