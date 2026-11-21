import YangMills.Construction.HilbertSpace.FormsAndOperators
import YangMills.Construction.ReflectionPositiveLimits.MirrorsAndReflectionPositivityOfAFunctional
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
open EuclidIsometry
def lowerHalfSpace : Set Space := {x | x timeAxis < 0}
theorem timeZeroMirror_negSide : timeZeroMirror.negSide = lowerHalfSpace := by
  ext x
  simp [NormalMirror.negSide, timeZeroMirror, lowerHalfSpace, euclidInner_coordVec]
theorem disjoint_lowerHalfSpace_upperHalfSpace : Disjoint lowerHalfSpace upperHalfSpace := by
  rw [← timeZeroMirror_negSide, ← timeZeroMirror_posSide]
  exact timeZeroMirror.disjoint_negSide_posSide
theorem mem_combsSupportedIn_iff {U : Set Space} {A : TupleComb} :
    A ∈ combsSupportedIn U ↔ (A.support : Set Tuple) ⊆ tuplesSupportedIn U := by
  have hU : combsSupportedIn U = Finsupp.supported ℂ ℂ (tuplesSupportedIn U) := by
    rw [Finsupp.supported_eq_span_single]
    rfl
  rw [hU]
  exact Finsupp.mem_supported ℂ A
theorem conjComb_add (A B : TupleComb) : conjComb (A + B) = conjComb A + conjComb B := by
  ext T
  simp [conjComb]
theorem conjComb_smul (c : ℂ) (A : TupleComb) : conjComb (c • A) = conj c • conjComb A := by
  ext T
  simp [conjComb]
theorem pushComb_conjComb_mem {A : TupleComb} (hA : A ∈ combsSupportedIn upperHalfSpace) :
    pushComb timeZeroMirror.reflectIso (conjComb A) ∈ combsSupportedIn lowerHalfSpace := by
  classical
  rw [mem_combsSupportedIn_iff] at hA ⊢
  intro S hS
  have hS₁ := Finsupp.mapDomain_support (f := push timeZeroMirror.reflectIso) (s := conjComb A)
    (Finset.mem_coe.1 hS)
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hS₁
  have hT₂ : T ∈ A.support := Finsupp.support_mapRange hT
  rw [← timeZeroMirror_negSide]
  exact NormalMirror.push_reflectIso_mem (by rw [timeZeroMirror_posSide]; exact hA hT₂)
def thetaConj (A : combsSupportedIn upperHalfSpace) : combsSupportedIn lowerHalfSpace :=
  ⟨pushComb timeZeroMirror.reflectIso (conjComb A), pushComb_conjComb_mem A.2⟩
theorem thetaConj_add (A B : combsSupportedIn upperHalfSpace) :
    thetaConj (A + B) = thetaConj A + thetaConj B :=
  Subtype.ext (by simp [thetaConj, conjComb_add])
theorem thetaConj_smul (c : ℂ) (A : combsSupportedIn upperHalfSpace) :
    thetaConj (c • A) = conj c • thetaConj A :=
  Subtype.ext (by simp [thetaConj, conjComb_smul])
def reflForm (σ : Tuple → ℝ) (A B : combsSupportedIn upperHalfSpace) : ℂ :=
  linearExt σ (concatOn lowerHalfSpace upperHalfSpace (thetaConj A) B)
theorem isSesquilinear_reflForm (σ : Tuple → ℝ) :
    HilbertSpaceBasics.IsSesquilinear (reflForm σ) where
  add_left A₁ A₂ B := by
    simp only [reflForm, thetaConj_add, map_add, LinearMap.add_apply]
  smul_left c A B := by
    simp only [reflForm, thetaConj_smul, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
  add_right A B₁ B₂ := by
    simp only [reflForm, map_add]
  smul_right c A B := by
    simp only [reflForm, map_smul, smul_eq_mul]
theorem reflForm_self_eq_sum (σ : Tuple → ℝ) {ι : Type} [Fintype ι]
    (T : ι → Tuple) (a : ι → ℂ) (hT : ∀ i, T i ∈ tuplesSupportedIn timeZeroMirror.posSide)
    (A : combsSupportedIn upperHalfSpace) (hA : (A : TupleComb) = ∑ i, a i • basisOf (T i)) :
    reflForm σ A A = ∑ i, ∑ j, conj (a i) * a j *
      (σ (concat (push timeZeroMirror.reflectIso (T i)) (T j)
        (NormalMirror.concatenable_reflectIso (hT i) (hT j))) : ℂ) := by
  change linearExt σ (concatBilin
    (pushComb timeZeroMirror.reflectIso (conjComb (A : TupleComb))) (A : TupleComb)) = _
  rw [hA, conjComb_sum]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp : pushComb timeZeroMirror.reflectIso (basisOf (T i)) =
      basisOf (push timeZeroMirror.reflectIso (T i)) := by
    simp [pushComb, basisOf]
  have hd := NormalMirror.concatenable_reflectIso (hT i) (hT j)
  rw [hp]
  have hc : concatBilin (basisOf (push timeZeroMirror.reflectIso (T i)))
      (basisOf (T j)) = basisOf (concat _ _ hd) := by
    simp [concatBilin, basisOf, concatBasis, hd]
  have hl : ∀ S, linearExt σ (basisOf S) = (σ S : ℂ) := fun S => by
    simp [linearExt, basisOf]
  rw [hc, hl]
  ring
theorem reflForm_self_nonneg {σ : Tuple → ℝ} (hσ : ReflectionPositiveAt timeZeroMirror σ)
    (A : combsSupportedIn upperHalfSpace) : 0 ≤ reflForm σ A A := by
  have hs := mem_combsSupportedIn_iff.1 A.2
  have hT : ∀ i : (A : TupleComb).support, (i : Tuple) ∈ tuplesSupportedIn timeZeroMirror.posSide :=
    fun i => by rw [timeZeroMirror_posSide]; exact hs i.2
  have hA : (A : TupleComb) =
      ∑ i : (A : TupleComb).support, (A : TupleComb) i • basisOf (i : Tuple) := by
    rw [Finset.sum_coe_sort (A : TupleComb).support
      fun T => (A : TupleComb) T • basisOf T]
    conv_lhs => rw [← Finsupp.sum_single (A : TupleComb)]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp [basisOf]
  rw [reflForm_self_eq_sum σ _ _ hT A hA]
  exact hσ _ _ _ hT
theorem isPosSemidef_reflForm {σ : Tuple → ℝ}
    (hσ : ReflectionPositiveAt timeZeroMirror σ) :
    HilbertSpaceBasics.IsPosSemidef (reflForm σ) :=
  { isSesquilinear_reflForm σ with nonneg := reflForm_self_nonneg hσ }
abbrev ReconstructionSpace (σ : Tuple → ℝ)
    (hσ : ReflectionPositiveAt timeZeroMirror σ) : Type :=
  HilbertSpaceBasics.FormCompletion (reflForm σ) (isPosSemidef_reflForm hσ)
def toReconstruction (σ : Tuple → ℝ) (hσ : ReflectionPositiveAt timeZeroMirror σ) :
    combsSupportedIn upperHalfSpace →ₗ[ℂ] ReconstructionSpace σ hσ :=
  HilbertSpaceBasics.completionClass (reflForm σ) (isPosSemidef_reflForm hσ)
theorem inner_toReconstruction (σ : Tuple → ℝ)
    (hσ : ReflectionPositiveAt timeZeroMirror σ) (A B : combsSupportedIn upperHalfSpace) :
    ⟪toReconstruction σ hσ A, toReconstruction σ hσ B⟫_ℂ = reflForm σ A B :=
  UniformSpace.Completion.inner_coe (𝕜 := ℂ)
    (show HilbertSpaceBasics.FormSpace (reflForm σ)
      (isPosSemidef_reflForm hσ) from A)
    (show HilbertSpaceBasics.FormSpace (reflForm σ)
      (isPosSemidef_reflForm hσ) from B)
theorem basisOf_nilTuple_mem : basisOf nilTuple ∈ combsSupportedIn upperHalfSpace :=
  Submodule.subset_span (mem_image_of_mem _ fun _ hf => by simp [nilTuple] at hf)
def vacuum (σ : Tuple → ℝ) (hσ : ReflectionPositiveAt timeZeroMirror σ) :
    ReconstructionSpace σ hσ :=
  toReconstruction σ hσ ⟨basisOf nilTuple, basisOf_nilTuple_mem⟩
end YangMills.Construction.ReflectionPositivity
