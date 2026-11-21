import YangMills.Construction.Conventions.OneLoopLawDefs
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Topology
open scoped ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction
namespace ComplexHilbert
open YangMills.Construction.OneLoopNotation
section LinearMaps
variable {E F : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
def linearKer (B : E →ₗ[ℂ] F) : Set E := {x | B x = 0}
def linearRange (B : E →ₗ[ℂ] F) : Set F := {y | ∃ x, B x = y}
end LinearMaps
section Spaces
variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
theorem norm_eq_sqrt_innerProd (v : H) : ‖v‖ = Real.sqrt (⟪v, v⟫_ℂ).re :=
  norm_eq_sqrt_re_inner (𝕜 := ℂ) v
def boundSet (B : H →ₗ[ℂ] K) : Set ℝ := {C | ∀ v, ‖B v‖ ≤ C * ‖v‖}
def HasBound (B : H →ₗ[ℂ] K) : Prop := (boundSet B).Nonempty
theorem exists_bddOp_of_hasBound {B : H →ₗ[ℂ] K} (hB : HasBound B) :
    ∃ T : BddOpBetween H K, (T : H →ₗ[ℂ] K) = B := by
  obtain ⟨C, hC⟩ := hB
  exact ⟨B.mkContinuous C hC, by ext v; rfl⟩
variable (H) in
abbrev idOp : BddOp H := ContinuousLinearMap.id ℂ H
def IsSymmetricOp (B : BddOp H) : Prop := ∀ u v, ⟪u, B v⟫_ℂ = ⟪B u, v⟫_ℂ
theorem IsSymmetricOp.inner_self_apply_im_eq_zero {B : BddOp H}
    (hB : IsSymmetricOp B) (v : H) : (⟪v, B v⟫_ℂ).im = 0 := by
  have hconj : ⟪v, B v⟫_ℂ = conj ⟪v, B v⟫_ℂ := by
    rw [inner_conj_symm]
    exact hB v v
  exact Complex.conj_eq_iff_im.mp hconj.symm
theorem isSymmetricOp_iff (B : BddOp H) :
    IsSymmetricOp B ↔ IsSelfAdjoint B := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact ⟨fun hB u v => (hB u v).symm, fun hB u v => (hB u v).symm⟩
structure OpLE (A B : BddOp H) : Prop where
  left : IsSymmetricOp A
  right : IsSymmetricOp B
  le : ∀ v, ⟪v, A v⟫_ℂ ≤ ⟪v, B v⟫_ℂ
abbrev OpGE (B A : BddOp H) : Prop := OpLE A B
structure IsOrthProj (P : BddOp H) : Prop where
  selfAdjoint : IsSymmetricOp P
  idempotent : P ^ 2 = P
def fixedSubspace (P : BddOp H) : Submodule ℂ H where
  carrier := {v | P v = v}
  add_mem' := by
    intro v w hv hw
    change P v = v at hv
    change P w = w at hw
    change P (v + w) = v + w
    rw [map_add, hv, hw]
  zero_mem' := map_zero P
  smul_mem' := by
    intro c v hv
    change P v = v at hv
    change P (c • v) = c • v
    rw [map_smul, hv]
def IsOrthProjOnto (P : BddOp H) (M : Submodule ℂ H) : Prop :=
  IsOrthProj P ∧ M = fixedSubspace P
def IsIsometry (V : H →ₗ[ℂ] K) : Prop := ∀ v, ‖V v‖ = ‖v‖
structure IsUnitaryMap (V : H →ₗ[ℂ] K) : Prop where
  isometric : IsIsometry V
  onto : Function.Surjective V
theorem IsUnitaryMap.bijective {V : H →ₗ[ℂ] K} (hV : IsUnitaryMap V) :
    Function.Bijective V := by
  refine ⟨(injective_iff_map_eq_zero V).mpr fun v hv => ?_, hV.onto⟩
  have hn := hV.isometric v
  rw [hv, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm
def seqClosureOf (D : Set H) : Set H :=
  {x | ∃ u : ℕ → H, (∀ k, u k ∈ D) ∧ Tendsto u atTop (𝓝 x)}
def IsClosedSet (D : Set H) : Prop := seqClosureOf D = D
def IsDenseSet (D : Set H) : Prop := seqClosureOf D = Set.univ
def orthSet (D : Set H) : Set H := {x | ∀ v ∈ D, ⟪x, v⟫_ℂ = 0}
theorem seqClosureOf_eq_closure (D : Set H) : seqClosureOf D = closure D := by
  ext x
  exact mem_closure_iff_seq_limit.symm
theorem isClosedSet_iff (D : Set H) : IsClosedSet D ↔ IsClosed D := by
  rw [IsClosedSet, seqClosureOf_eq_closure]
  exact closure_eq_iff_isClosed
theorem isDenseSet_iff (D : Set H) : IsDenseSet D ↔ Dense D := by
  rw [IsDenseSet, seqClosureOf_eq_closure]
  exact dense_iff_closure_eq.symm
def IsUnitaryMap.toLinearEquiv {W : H →ₗ[ℂ] K} (hW : IsUnitaryMap W) : H ≃ₗ[ℂ] K :=
  LinearEquiv.ofBijective W hW.bijective
end Spaces
end ComplexHilbert
end YangMills.Construction
