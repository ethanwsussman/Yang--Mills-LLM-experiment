import YangMills.Construction.Continuum.SchwartzFunctionsFlatOutsideAnOpenSet
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ContDiff
noncomputable section
namespace YangMills.Construction.ConfigSpace
def timeFlip (u : Fin 4 → ℝ) : Fin 4 → ℝ := ![u 0, u 1, u 2, -u 3]
def euclidMotions : Set ((Fin 4 → ℝ) → Fin 4 → ℝ) :=
  {r | ∃ R ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∃ v : Fin 4 → ℝ, ∀ u, r u = R.mulVec u + v}
abbrev EuclidMotion : Type := {r : (Fin 4 → ℝ) → Fin 4 → ℝ // r ∈ euclidMotions}
def EuclidMotion.invMap (r : EuclidMotion) : (Fin 4 → ℝ) → Fin 4 → ℝ :=
  Function.invFun r.1
section Orthogonal
variable {M : Matrix (Fin 4) (Fin 4) ℝ}
theorem orth_transpose_mul_self (hM : M ∈ Matrix.orthogonalGroup (Fin 4) ℝ) :
    M.transpose * M = 1 :=
  mul_eq_one_comm.1 ((Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).1 hM)
theorem orth_inv_mul_self (hM : M ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : M⁻¹ * M = 1 := by
  rw [Matrix.inv_eq_right_inv ((Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).1 hM)]
  exact orth_transpose_mul_self hM
theorem orth_mul_inv_self (hM : M ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : M * M⁻¹ = 1 :=
  mul_eq_one_comm.1 (orth_inv_mul_self hM)
theorem euclidNormVec_orth_mulVec (hM : M ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (u : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (M.mulVec u) = TorusMetric.euclidNormVec u := by
  have hdot : M.mulVec u ⬝ᵥ M.mulVec u = u ⬝ᵥ u := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
      orth_transpose_mul_self hM, Matrix.one_mulVec]
  unfold TorusMetric.euclidNormVec
  congr 1
  simpa [dotProduct, sq] using hdot
end Orthogonal
theorem bijective_of_mem_euclidMotions {r : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hr : r ∈ euclidMotions) : Function.Bijective r := by
  obtain ⟨M, hM, v, hrv⟩ := hr
  have hleft : Function.LeftInverse (fun u => M⁻¹.mulVec (u - v)) r := fun u => by
    simp [hrv, Matrix.mulVec_mulVec, orth_inv_mul_self hM]
  have hright : Function.RightInverse (fun u => M⁻¹.mulVec (u - v)) r := fun u => by
    simp [hrv, Matrix.mulVec_mulVec, orth_mul_inv_self hM]
  exact ⟨hleft.injective, hright.surjective⟩
namespace EuclidMotion
theorem apply_invMap (r : EuclidMotion) (u : Fin 4 → ℝ) : r.1 (r.invMap u) = u :=
  Function.rightInverse_invFun (bijective_of_mem_euclidMotions r.2).2 u
theorem invMap_eq (r : EuclidMotion) {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : M ∈ Matrix.orthogonalGroup (Fin 4) ℝ) {v : Fin 4 → ℝ}
    (hrv : ∀ u, r.1 u = M.mulVec u + v) (u : Fin 4 → ℝ) : r.invMap u = M⁻¹.mulVec (u - v) := by
  apply (bijective_of_mem_euclidMotions r.2).1
  rw [apply_invMap, hrv]
  simp [Matrix.mulVec_mulVec, orth_mul_inv_self hM]
end EuclidMotion
def timeFlipMotion : EuclidMotion :=
  ⟨timeFlip, Matrix.diagonal ![1, 1, 1, -1], by
    rw [Matrix.mem_orthogonalGroup_iff, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp, 0, fun u => by
    funext i
    fin_cases i <;> simp [timeFlip, Matrix.mulVec_diagonal]⟩
theorem timeFlip_timeFlip (u : Fin 4 → ℝ) : timeFlip (timeFlip u) = u := by
  funext i
  fin_cases i <;> simp [timeFlip]
def shiftMotion (w : Fin 4 → ℝ) : EuclidMotion :=
  ⟨fun u => u + w, 1, one_mem _, w, fun u => by simp⟩
theorem shiftMotion_invMap (w u : Fin 4 → ℝ) :
    (shiftMotion w).invMap u = u - w := by
  rw [EuclidMotion.invMap_eq (shiftMotion w) (M := 1) (v := w) (one_mem _)
    (fun u => by simp [shiftMotion])]
  simp
section Functions
variable {n : ℕ} {F : Type*}
def motionAct (r : EuclidMotion) (φ : Config n → F) : Config n → F :=
  fun x => φ fun i => r.invMap (x i)
def permAct (σ : Equiv.Perm (Fin n)) (φ : Config n → F) : Config n → F :=
  fun x => φ fun i => x (σ i)
def flipConj (φ : Config n → ℂ) : Config n → ℂ :=
  fun x => conj (φ fun i => timeFlip (x i))
def shiftAct (w : Fin 4 → ℝ) (φ : Config n → F) : Config n → F :=
  motionAct (shiftMotion w) φ
theorem shiftAct_apply (w : Fin 4 → ℝ) (φ : Config n → F) (x : Config n) :
    shiftAct w φ x = φ fun i => x i - w := by
  simp only [shiftAct, motionAct, shiftMotion_invMap]
end Functions
def liftOne {F : Type*} (f : (Fin 4 → ℝ) → F) : Config 1 → F := fun x => f (x 0)
def liftOneSet (O : Set (Fin 4 → ℝ)) : Set (Config 1) := {x | x 0 ∈ O}
def realC1CompactIn (O : Set (Fin 4 → ℝ)) : Set ((Fin 4 → ℝ) → ℝ) :=
  {f | liftOne (fun u => (f u : ℂ)) ∈ c1CompactSupportIn (liftOneSet O)}
def realSmoothCompactIn (O : Set (Fin 4 → ℝ)) : Set ((Fin 4 → ℝ) → ℝ) :=
  {f | liftOne (fun u => (f u : ℂ)) ∈ smoothCompactSupportIn (liftOneSet O)}
theorem compactClass_liftOne_iff (k : WithTop ℕ∞) (O : Set (Fin 4 → ℝ))
    (f : (Fin 4 → ℝ) → ℝ) :
    (IsOpen (liftOneSet O) ∧ ContDiff ℝ k (liftOne fun u => (f u : ℂ)) ∧
        IsCompact (tsupport (liftOne fun u => (f u : ℂ))) ∧
        tsupport (liftOne fun u => (f u : ℂ)) ⊆ liftOneSet O) ↔
      IsOpen O ∧ ContDiff ℝ k f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ O := by
  let e : Config 1 ≃L[ℝ] (Fin 4 → ℝ) := ContinuousLinearEquiv.funUnique (Fin 1) ℝ (Fin 4 → ℝ)
  have hset : liftOneSet O = e ⁻¹' O := rfl
  have hfun : (liftOne fun u => (f u : ℂ)) = (fun u => (f u : ℂ)) ∘ e := rfl
  have hsupp : tsupport (fun u => (f u : ℂ)) = tsupport f := by
    unfold tsupport
    congr 1
    ext u
    simp
  have hts : tsupport (liftOne fun u => (f u : ℂ)) = e ⁻¹' tsupport f := by
    rw [hfun, ← hsupp]
    exact tsupport_comp_eq_preimage _ e.toHomeomorph
  have hdiff : ContDiff ℝ k (fun u => (f u : ℂ)) ↔ ContDiff ℝ k f :=
    ⟨fun h => by
      have h' := Complex.reCLM.contDiff.comp h
      convert h' using 1
      funext u
      simp, fun h => Complex.ofRealCLM.contDiff.comp h⟩
  have hopen : IsOpen (e ⁻¹' O) ↔ IsOpen O := e.toHomeomorph.isOpen_preimage
  have hcpt : IsCompact (e ⁻¹' tsupport f) ↔ IsCompact (tsupport f) :=
    e.toHomeomorph.isCompact_preimage
  rw [hts, hfun, hset, e.contDiff_comp_iff, hdiff, hopen, hcpt,
    Set.preimage_subset_preimage_iff (by simp [e.surjective.range_eq])]
theorem mem_realC1CompactIn_iff {O : Set (Fin 4 → ℝ)} {f : (Fin 4 → ℝ) → ℝ} :
    f ∈ realC1CompactIn O ↔
      IsOpen O ∧ ContDiff ℝ 1 f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ O :=
  compactClass_liftOne_iff 1 O f
theorem mem_realSmoothCompactIn_iff {O : Set (Fin 4 → ℝ)} {f : (Fin 4 → ℝ) → ℝ} :
    f ∈ realSmoothCompactIn O ↔
      IsOpen O ∧ ContDiff ℝ ∞ f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ O :=
  compactClass_liftOne_iff ∞ O f
section Tensors
variable {p p' n : ℕ}
def concatConfig (x : Config p) (y : Config p') : Config (p + p') := Fin.append x y
def headArgs (z : Config (p + p')) : Config p := fun i => z (Fin.castAdd p' i)
def tailArgs (z : Config (p + p')) : Config p' := fun j => z (Fin.natAdd p j)
theorem headArgs_concatConfig (x : Config p) (y : Config p') :
    headArgs (concatConfig x y) = x := by
  funext i
  simp [headArgs, concatConfig]
theorem tailArgs_concatConfig (x : Config p) (y : Config p') :
    tailArgs (concatConfig x y) = y := by
  funext j
  simp [tailArgs, concatConfig]
theorem concatConfig_headArgs_tailArgs (z : Config (p + p')) :
    concatConfig (headArgs z) (tailArgs z) = z :=
  Fin.append_castAdd_natAdd
def tensorFn (φ : Config p → ℂ) (ψ : Config p' → ℂ) : Config (p + p') → ℂ :=
  fun z => φ (headArgs z) * ψ (tailArgs z)
theorem tensorFn_concatConfig (φ : Config p → ℂ) (ψ : Config p' → ℂ) (x : Config p)
    (y : Config p') : tensorFn φ ψ (concatConfig x y) = φ x * ψ y := by
  simp [tensorFn, headArgs_concatConfig, tailArgs_concatConfig]
def tensorFamily (f : Fin n → (Fin 4 → ℝ) → ℂ) : Config n → ℂ :=
  fun x => ∏ i, f i (x i)
def tensorRealFamily (f : Fin n → (Fin 4 → ℝ) → ℝ) : Config n → ℂ :=
  tensorFamily fun i u => (f i u : ℂ)
end Tensors
def separatedFamilies (O : Set (Fin 4 → ℝ)) (n : ℕ) : Set (Fin n → (Fin 4 → ℝ) → ℝ) :=
  {f | (∀ i, f i ∈ realC1CompactIn O) ∧
    Pairwise fun i j => Disjoint (tsupport (f i)) (tsupport (f j))}
def nilFamily : Fin 0 → (Fin 4 → ℝ) → ℝ := Fin.elim0
theorem separatedFamilies_zero (O : Set (Fin 4 → ℝ)) : separatedFamilies O 0 = {nilFamily} := by
  ext f
  have hf : f = nilFamily := Subsingleton.elim _ _
  simp only [Set.mem_singleton_iff, hf, iff_true]
  exact ⟨fun i => i.elim0, fun i => i.elim0⟩
abbrev SeparatedFamily : Type :=
  Σ n : ℕ, {f : Fin n → (Fin 4 → ℝ) → ℝ // f ∈ separatedFamilies Set.univ n}
def AllSmoothCompact {n : ℕ} (f : Fin n → (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ i, f i ∈ realSmoothCompactIn Set.univ
theorem allSmoothCompact_nilFamily : AllSmoothCompact nilFamily := fun i => i.elim0
def FnOrScalar : ℕ → Type
  | 0 => ℂ
  | n + 1 => Config (n + 1) → ℂ
def flatOffDiagonalAt : (n : ℕ) → Set (FnOrScalar n)
  | 0 => Set.univ
  | n + 1 => schwartzFlatOffDiagonal (n + 1)
def flatOffPosTimeAt : (n : ℕ) → Set (FnOrScalar n)
  | 0 => Set.univ
  | n + 1 => schwartzFlatOffPosTime (n + 1)
def motionActAt (r : EuclidMotion) : {n : ℕ} → FnOrScalar n → FnOrScalar n
  | 0, c => c
  | _ + 1, φ => motionAct r φ
def shiftActAt (w : Fin 4 → ℝ) : {n : ℕ} → FnOrScalar n → FnOrScalar n
  | 0, c => c
  | _ + 1, φ => shiftAct w φ
def flipConjAt : {n : ℕ} → FnOrScalar n → FnOrScalar n
  | 0, c => (conj (show ℂ from c) : ℂ)
  | _ + 1, φ => flipConj φ
def smulAt (c : ℂ) : {n : ℕ} → FnOrScalar n → FnOrScalar n
  | 0, ψ => (c * (show ℂ from ψ) : ℂ)
  | _ + 1, ψ => fun y => c * ψ y
def tensorAt : {p p' : ℕ} → FnOrScalar p → FnOrScalar p' →
    FnOrScalar (p + p')
  | 0, p', c, ψ => (Nat.zero_add p').symm ▸ smulAt (show ℂ from c) ψ
  | _ + 1, 0, φ, c => smulAt (show ℂ from c) φ
  | p + 1, p' + 1, φ, ψ => tensorFn (p := p + 1) (p' := p' + 1) φ ψ
theorem tensorAt_scalar_left {p' : ℕ} (c : ℂ) (ψ : FnOrScalar p') :
    tensorAt (p := 0) c ψ = (Nat.zero_add p').symm ▸ smulAt c ψ :=
  rfl
theorem tensorAt_scalar_right {p : ℕ} (ψ : FnOrScalar p) (c : ℂ) :
    tensorAt (p' := 0) ψ c = smulAt c ψ := by
  cases p with
  | zero => exact mul_comm (G := ℂ) ψ c
  | succ p => rfl
def ofConfigFn : {n : ℕ} → (Config n → ℂ) → FnOrScalar n
  | 0, f => f fun i => i.elim0
  | _ + 1, f => f
def toConfigFn : {n : ℕ} → FnOrScalar n → Config n → ℂ
  | 0, c => fun _ => c
  | _ + 1, φ => φ
end YangMills.Construction.ConfigSpace
end
