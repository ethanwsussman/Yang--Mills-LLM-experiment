import YangMills.Construction.HilbertSpaces.ElementaryFactsOfComplexHilbertSpaces
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.HilbertFacts
open OneLoopNotation ComplexHilbert
theorem eqOfInnerSelfEq_holds : EqOfInnerSelfEq := by
  intro H _ _ _ B B' hBB
  have hlin : (B : H →ₗ[ℂ] H) = (B' : H →ₗ[ℂ] H) := by
    refine (ext_inner_map _ _).1 fun x => ?_
    have hconj := congrArg (starRingEnd ℂ) (hBB x)
    simp only [inner_conj_symm] at hconj
    exact hconj
  exact ContinuousLinearMap.coe_injective hlin
def linearIsometryOfNormEq {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (T : E →ₗ[ℂ] F)
    (hT : ∀ v, ‖T v‖ = ‖v‖) : E →ₗᵢ[ℂ] F := ⟨T, hT⟩
theorem inner_map_map_of_norm_eq {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (T : E →ₗ[ℂ] F)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (u v : E) : ⟪T u, T v⟫_ℂ = ⟪u, v⟫_ℂ :=
  (linearIsometryOfNormEq T hT).inner_map_map u v
theorem isometryInnerAndClosedRange_holds : IsometryInnerAndClosedRange := by
  intro H H' _ _ _ _ _ _ V hV
  refine ⟨inner_map_map_of_norm_eq V hV, ?_⟩
  rw [isClosedSet_iff]
  have hran : linearRange V = Set.range V := by
    ext w
    rfl
  rw [hran]
  exact (linearIsometryOfNormEq V hV).isometry.isClosedEmbedding.isClosed_range
theorem unitaryInverseExists_holds : UnitaryInverseExists := by
  intro H H' _ _ _ _ _ _ V hV
  set e := hV.toLinearEquiv
  have hl : ∀ v, e.symm (V v) = v := fun v => e.symm_apply_apply v
  have hr : ∀ w, V (e.symm w) = w := fun w => e.apply_symm_apply w
  refine ⟨(e.symm : H' →ₗ[ℂ] H), ?_, ?_, ⟨fun w => ?_, e.symm.surjective⟩,
    fun w v => ?_⟩
  · ext v
    exact hl v
  · ext w
    exact hr w
  · have hn := hV.isometric (e.symm w)
    rw [hr] at hn
    exact hn.symm
  · have hi := inner_map_map_of_norm_eq V hV.isometric (e.symm w) v
    rw [hr] at hi
    exact hi
@[reducible] def posOpCore {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : BddOp H) (hs : IsSymmetricOp B) (hp : OpGE B 0) :
    PreInnerProductSpace.Core ℂ H where
  inner u v := ⟪u, B v⟫_ℂ
  conj_inner_symm u v := by
    rw [inner_conj_symm]
    exact (hs u v).symm
  re_inner_nonneg u := by
    have hle := hp.le u
    have hz : ⟪u, (0 : BddOp H) u⟫_ℂ = 0 := by simp
    rw [hz] at hle
    exact (Complex.le_def.mp hle).1
  add_left u u' v := inner_add_left u u' (B v)
  smul_left u v c := inner_smul_left u (B v) c
theorem posOpCauchySchwarz_holds : PosOpCauchySchwarz := by
  intro H _ _ _ B hs hp
  have hcs : ∀ u v : H, ((‖⟪u, B v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) ≤ ⟪u, B u⟫_ℂ * ⟪v, B v⟫_ℂ := by
    intro u v
    have ha : ‖⟪u, B v⟫_ℂ‖ * ‖⟪v, B u⟫_ℂ‖ ≤ (⟪u, B u⟫_ℂ).re * (⟪v, B v⟫_ℂ).re :=
      @InnerProductSpace.Core.inner_mul_inner_self_le ℂ H _ _ _ (posOpCore B hs hp) u v
    have hb : ‖⟪v, B u⟫_ℂ‖ = ‖⟪u, B v⟫_ℂ‖ := by
      rw [hs v u, norm_inner_symm]
    rw [hb] at ha
    have hre : ∀ w : H, ⟪w, B w⟫_ℂ = (((⟪w, B w⟫_ℂ).re : ℝ) : ℂ) := fun w =>
      Complex.ext (by simp) (by simpa using hs.inner_self_apply_im_eq_zero w)
    rw [hre u, hre v, ← Complex.ofReal_mul, Complex.real_le_real, pow_two]
    simpa using ha
  refine ⟨hcs, fun v hv => ?_⟩
  have ha := hcs (B v) v
  rw [hv, mul_zero] at ha
  have hsq : ‖⟪B v, B v⟫_ℂ‖ ^ 2 ≤ 0 := by
    exact_mod_cast ha
  have hzero : ‖⟪B v, B v⟫_ℂ‖ = 0 := by
    nlinarith [norm_nonneg ⟪B v, B v⟫_ℂ]
  exact inner_self_eq_zero.mp (norm_eq_zero.mp hzero)
theorem closedSubmoduleHilbert_holds : ClosedSubmoduleHilbert := by
  intro H _ _ _ M hM
  have hc : IsClosed (M : Set H) := (isClosedSet_iff _).mp hM
  exact ⟨hc.completeSpace_coe, fun _ _ => rfl⟩
theorem orthSetClosed_holds : OrthSetClosed := by
  intro H _ _ _ S
  refine ⟨⟨{ carrier := orthSet S
             add_mem' := ?_
             zero_mem' := ?_
             smul_mem' := ?_ }, rfl⟩, ?_⟩
  · intro w w' hw hw' v hv
    rw [inner_add_left, hw v hv, hw' v hv, add_zero]
  · intro v _
    exact inner_zero_left v
  · intro c w hw v hv
    rw [inner_smul_left, hw v hv, mul_zero]
  · rw [isClosedSet_iff]
    have hinter : orthSet S = ⋂ v ∈ S, {w : H | ⟪w, v⟫_ℂ = 0} := by
      ext w
      simp [orthSet]
    rw [hinter]
    exact isClosed_biInter fun v _ => isClosed_eq (continuous_id.inner continuous_const)
      continuous_const
theorem kerClosed_holds : KerClosed := by
  intro H H' _ _ _ _ _ _ B
  refine ⟨⟨LinearMap.ker (B : H →ₗ[ℂ] H'), rfl⟩, ?_⟩
  rw [isClosedSet_iff]
  exact isClosed_eq B.continuous continuous_const
theorem eqOfEqOnDense_holds : EqOfEqOnDense := by
  intro H H' _ _ _ _ _ _ S hS B B' hBB
  exact DFunLike.coe_injective
    (Continuous.ext_on ((isDenseSet_iff S).mp hS) B.continuous B'.continuous hBB)
theorem closureImageDenseEqClosureRange_holds : ClosureImageDenseEqClosureRange := by
  intro H H' _ _ _ _ _ _ S hS B
  rw [seqClosureOf_eq_closure, seqClosureOf_eq_closure]
  have hran : linearRange (B : H →ₗ[ℂ] H') = Set.range B := by
    ext w
    rfl
  rw [hran]
  apply subset_antisymm
  · exact closure_mono (Set.image_subset_range _ _)
  · refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨v, rfl⟩
    exact image_closure_subset_closure_image B.continuous
      ⟨v, (isDenseSet_iff S).mp hS v, rfl⟩
theorem isSelfAdjoint_list_prod_of_commute {R : Type} [Monoid R] [StarMul R] (l : List R)
    (hs : ∀ x ∈ l, IsSelfAdjoint x) (hc : l.Pairwise Commute) : IsSelfAdjoint l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons]
    have ha := hs a List.mem_cons_self
    have hl := ih (fun x hx => hs x (List.mem_cons_of_mem a hx)) (List.pairwise_cons.mp hc).2
    exact (IsSelfAdjoint.commute_iff ha hl).mp
      (Commute.list_prod_right l a (List.pairwise_cons.mp hc).1)
theorem commutingSymmetricProd_holds : CommutingSymmetricProd := by
  intro H _ _ _ n B _ hs hc
  rw [isSymmetricOp_iff]
  refine isSelfAdjoint_list_prod_of_commute _ ?_ ?_
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (isSymmetricOp_iff _).mp (hs i)
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact hc i j hij.ne
theorem elementaryFacts_holds : ElementaryFacts :=
  ⟨eqOfInnerSelfEq_holds, ⟨isometryInnerAndClosedRange_holds, unitaryInverseExists_holds⟩,
    posOpCauchySchwarz_holds,
    ⟨closedSubmoduleHilbert_holds, orthSetClosed_holds, kerClosed_holds⟩,
    ⟨eqOfEqOnDense_holds, closureImageDenseEqClosureRange_holds⟩, commutingSymmetricProd_holds⟩
end YangMills.Construction.HilbertFacts
