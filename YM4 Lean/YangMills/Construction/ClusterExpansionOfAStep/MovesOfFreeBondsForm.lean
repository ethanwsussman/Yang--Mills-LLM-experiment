import YangMills.Construction.ClusterExpansionOfAStep.BondInCoordinates
import YangMills.Construction.ClusterExpansionOfAStep.LogarithmOfAMove
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.FreeBondMoves
open TorusFields QuaternionLogarithm LineCalculus ColdStepAtMirrorFrames
variable {m : ℕ}
def leftMovesAt (I : Finset (TorusBond m)) (a : I → ImaginaryCoord) (W : TorusField m) : TorusField m := fun x i =>
  if h : (x, i) ∈ I then BlockAverages.expUnit (toImaginary (a ⟨(x, i), h⟩)) * W x i else W x i
def alongMoves (I : Finset (TorusBond m)) (G : TorusField m → ℝ) (W : TorusField m) (a : I → ImaginaryCoord) : ℝ :=
  G (leftMovesAt I a W)
theorem toImaginary_add (v w : ImaginaryCoord) : toImaginary (v + w) = toImaginary v + toImaginary w := by
  apply Subtype.ext
  show imaginaryCLM (v + w) = imaginaryCLM v + imaginaryCLM w
  exact map_add _ _ _
theorem toImaginary_smul (c : ℝ) (v : ImaginaryCoord) : toImaginary (c • v) = c • toImaginary v := by
  apply Subtype.ext
  show imaginaryCLM (c • v) = c • imaginaryCLM v
  exact map_smul _ _ _
theorem toImaginary_zero : toImaginary (0 : ImaginaryCoord) = 0 := by apply _root_.YangMills.Construction.BondCoordinates.toImaginary_zero <;> assumption
def coordUnit (j : Fin 3) : ImaginaryCoord := EuclideanSpace.single j 1
theorem sum_smul_toImaginary_coordUnit (v : ImaginaryCoord) :
    ∑ j, v j • toImaginary (coordUnit j) = toImaginary v := by
  have h : v = ∑ j, v j • coordUnit j := by
    ext i
    simp [coordUnit, Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [h]
  have hmap : ∀ (s : Finset (Fin 3)),
      toImaginary (∑ j ∈ s, v j • coordUnit j) = ∑ j ∈ s, v j • toImaginary (coordUnit j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [toImaginary_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, toImaginary_add, toImaginary_smul, ih]
  exact (hmap _).symm
section Smooth
variable (I : Finset (TorusBond m))
def moveEquiv : Fin (Fintype.card (I × Fin 3)) ≃ I × Fin 3 := (Fintype.equivFin (I × Fin 3)).symm
def moveCoordinates : (I → ImaginaryCoord) →L[ℝ] (Fin (Fintype.card (I × Fin 3)) → ℝ) :=
  ContinuousLinearMap.pi fun l =>
    (EuclideanSpace.proj (moveEquiv I l).2 : ImaginaryCoord →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj (moveEquiv I l).1)
theorem perturb_moveCoordinates (a : I → ImaginaryCoord) (W : TorusField m) :
    perturb (fun l => ((moveEquiv I l).1 : TorusBond m)) (fun l => toImaginary (coordUnit (moveEquiv I l).2))
      (moveCoordinates I a) W = leftMovesAt I a W := by
  classical
  funext x i
  unfold perturb leftMovesAt
  have hs : (∑ l, if (((moveEquiv I l).1 : TorusBond m)) = (x, i) then
      moveCoordinates I a l • toImaginary (coordUnit (moveEquiv I l).2) else 0) =
      ∑ q : I × Fin 3, if ((q.1 : TorusBond m)) = (x, i) then a q.1 q.2 • toImaginary (coordUnit q.2) else 0 :=
    Fintype.sum_equiv (moveEquiv I) _ _ fun l => rfl
  rw [hs, Fintype.sum_prod_type]
  split_ifs with h
  · have h2 : ∀ b : I, (∑ j, if ((b : TorusBond m)) = (x, i) then a b j • toImaginary (coordUnit j) else 0) =
        if b = ⟨(x, i), h⟩ then toImaginary (a b) else 0 := by
      intro b
      by_cases hb : ((b : TorusBond m)) = (x, i)
      · have hbe : b = ⟨(x, i), h⟩ := Subtype.ext hb
        rw [if_pos hbe]
        have h3 : (∑ j, if ((b : TorusBond m)) = (x, i) then a b j • toImaginary (coordUnit j) else 0) =
            ∑ j, a b j • toImaginary (coordUnit j) := Finset.sum_congr rfl fun j _ => if_pos hb
        rw [h3]
        exact sum_smul_toImaginary_coordUnit _
      · have : b ≠ ⟨(x, i), h⟩ := fun he => hb (congrArg Subtype.val he)
        simp [hb, this]
    simp only [h2]
    rw [Finset.sum_ite_eq' Finset.univ]
    simp
  · have h2 : ∀ b : I, (∑ j, if ((b : TorusBond m)) = (x, i) then a b j • toImaginary (coordUnit j) else 0) = 0 := by
      intro b
      have hb : ((b : TorusBond m)) ≠ (x, i) := fun he => h (he ▸ b.2)
      simp [hb]
    simp only [h2, Finset.sum_const_zero]
    rw [expUnit_zero, one_mul]
theorem contDiffAt_alongMoves {G : TorusField m → ℝ} {W : TorusField m} (h : ContDiffThreeAt G W) :
    ContDiffAt ℝ 3 (alongMoves I G W) 0 := by
  have e : alongMoves I G W = (fun σ => G (perturb (fun l => ((moveEquiv I l).1 : TorusBond m))
      (fun l => toImaginary (coordUnit (moveEquiv I l).2)) σ W)) ∘ moveCoordinates I := by
    funext a
    simp only [Function.comp, alongMoves, perturb_moveCoordinates]
  rw [e]
  have h0 := h _ (fun l => ((moveEquiv I l).1 : TorusBond m)) fun l => toImaginary (coordUnit (moveEquiv I l).2)
  have h1 : ContDiffAt ℝ 3 (fun σ => G (perturb (fun l => ((moveEquiv I l).1 : TorusBond m))
      (fun l => toImaginary (coordUnit (moveEquiv I l).2)) σ W)) (moveCoordinates I 0) := by
    rw [map_zero]
    exact h0
  exact h1.comp (0 : I → ImaginaryCoord) (moveCoordinates I).contDiff.contDiffAt
end Smooth
section Mixed
variable {I : Finset (TorusBond m)}
def pairMove (b b' : I) (p p' : ImaginaryCoord) : (Fin 2 → ℝ) →L[ℝ] (I → ImaginaryCoord) :=
  ((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight (Pi.single b p : I → ImaginaryCoord)) +
    ((ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight (Pi.single b' p' : I → ImaginaryCoord))
def singleMove (b : I) (p : ImaginaryCoord) : (Fin 1 → ℝ) →L[ℝ] (I → ImaginaryCoord) :=
  (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ).smulRight (Pi.single b p : I → ImaginaryCoord)
def moveAt (I : Finset (TorusBond m)) (a : I → ImaginaryCoord) (x : TorusSite m) (i : Fin 4) : ImaginaryCoord :=
  open Classical in if h : (x, i) ∈ I then a ⟨(x, i), h⟩ else 0
theorem leftMovesAt_eq (a : I → ImaginaryCoord) (W : TorusField m) (x : TorusSite m) (i : Fin 4) :
    leftMovesAt I a W x i = BlockAverages.expUnit (toImaginary (moveAt I a x i)) * W x i := by
  unfold leftMovesAt moveAt
  split_ifs with h
  · rfl
  · simp [toImaginary_zero, expUnit_zero]
theorem moveAt_single (b : I) (p : ImaginaryCoord) (x : TorusSite m) (i : Fin 4) :
    moveAt I (Pi.single b p) x i = open Classical in if (b : TorusBond m) = (x, i) then p else 0 := by
  classical
  unfold moveAt
  by_cases hb : (b : TorusBond m) = (x, i)
  · have hx : (x, i) ∈ I := hb ▸ b.2
    have hbe : b = ⟨(x, i), hx⟩ := Subtype.ext hb
    rw [dif_pos hx, if_pos hb, ← hbe]
    simp
  · rw [if_neg hb]
    split_ifs with hx
    · have : (⟨(x, i), hx⟩ : I) ≠ b := fun he => hb (congrArg Subtype.val he).symm
      simp [this]
    · rfl
theorem moveAt_add (a a' : I → ImaginaryCoord) (x : TorusSite m) (i : Fin 4) :
    moveAt I (a + a') x i = moveAt I a x i + moveAt I a' x i := by
  unfold moveAt
  split_ifs
  · rfl
  · simp
theorem moveAt_smul (c : ℝ) (a : I → ImaginaryCoord) (x : TorusSite m) (i : Fin 4) :
    moveAt I (c • a) x i = c • moveAt I a x i := by
  unfold moveAt
  split_ifs
  · rfl
  · simp
theorem singleMove_apply (b : I) (p : ImaginaryCoord) (σ : Fin 1 → ℝ) :
    singleMove b p σ = σ 0 • (Pi.single b p : I → ImaginaryCoord) := rfl
theorem pairMove_apply (b b' : I) (p p' : ImaginaryCoord) (σ : Fin 2 → ℝ) :
    pairMove b b' p p' σ =
      σ 0 • (Pi.single b p : I → ImaginaryCoord) + σ 1 • (Pi.single b' p' : I → ImaginaryCoord) := rfl
theorem perturb_single (b : I) (p : ImaginaryCoord) (σ : Fin 1 → ℝ) (W : TorusField m) :
    perturb ![(b : TorusBond m)] ![toImaginary p] σ W = leftMovesAt I (singleMove b p σ) W := by
  classical
  funext x i
  rw [leftMovesAt_eq, singleMove_apply, moveAt_smul, moveAt_single, toImaginary_smul]
  unfold perturb
  congr 2
  by_cases hb : (b : TorusBond m) = (x, i) <;> simp [hb, toImaginary_zero]
theorem perturb_pair (b b' : I) (p p' : ImaginaryCoord) (σ : Fin 2 → ℝ) (W : TorusField m) :
    perturb ![(b : TorusBond m), (b' : TorusBond m)] ![toImaginary p, toImaginary p'] σ W =
      leftMovesAt I (pairMove b b' p p' σ) W := by
  classical
  funext x i
  rw [leftMovesAt_eq, pairMove_apply, moveAt_add, moveAt_smul, moveAt_smul, moveAt_single, moveAt_single,
    toImaginary_add, toImaginary_smul, toImaginary_smul]
  unfold perturb
  congr 2
  rw [Fin.sum_univ_two]
  by_cases hb : (b : TorusBond m) = (x, i) <;> by_cases hb' : (b' : TorusBond m) = (x, i) <;>
    simp [hb, hb', toImaginary_zero]
theorem fderiv_alongMoves {G : TorusField m → ℝ} {W : TorusField m} (h : ContDiffThreeAt G W) (b : I)
    (p : ImaginaryCoord) :
    fderiv ℝ (alongMoves I G W) 0 (Pi.single b p) = mixedDeriv G W ![(b : TorusBond m)] ![toImaginary p] := by
  have hd : DifferentiableAt ℝ (alongMoves I G W) ((singleMove b p) 0) := by
    rw [map_zero]
    exact (contDiffAt_alongMoves I h).differentiableAt (by norm_num)
  have e : (fun σ : Fin 1 → ℝ => G (perturb ![(b : TorusBond m)] ![toImaginary p] σ W)) =
      alongMoves I G W ∘ singleMove b p := by
    funext σ
    simp only [Function.comp, alongMoves, perturb_single]
  unfold mixedDeriv
  rw [e, iteratedFDeriv_one_apply, fderiv_of_eventuallyEq_comp (Filter.EventuallyEq.refl _ _) hd
    (singleMove b p).differentiableAt, ContinuousLinearMap.fderiv]
  simp [singleMove]
theorem second_fderiv_alongMoves {G : TorusField m → ℝ} {W : TorusField m} (h : ContDiffThreeAt G W)
    (b b' : I) (p p' : ImaginaryCoord) :
    fderiv ℝ (fderiv ℝ (alongMoves I G W)) 0 (Pi.single b p) (Pi.single b' p') =
      mixedDeriv G W ![(b : TorusBond m), (b' : TorusBond m)] ![toImaginary p, toImaginary p'] := by
  have hd : ContDiffAt ℝ 2 (alongMoves I G W) ((pairMove b b' p p') 0) := by
    rw [map_zero]
    exact (contDiffAt_alongMoves I h).of_le (by norm_num)
  have hl : ContDiffAt ℝ 2 (pairMove b b' p p') (0 : Fin 2 → ℝ) := (pairMove b b' p p').contDiff.contDiffAt
  have e : (fun σ : Fin 2 → ℝ =>
      G (perturb ![(b : TorusBond m), (b' : TorusBond m)] ![toImaginary p, toImaginary p'] σ W)) =
      alongMoves I G W ∘ pairMove b b' p p' := by
    funext σ
    simp only [Function.comp, alongMoves, perturb_pair]
  unfold mixedDeriv
  rw [e, iteratedFDeriv_two_apply, second_fderiv_of_eventuallyEq_comp (Filter.EventuallyEq.refl _ _) hd hl]
  have h1 : fderiv ℝ (pairMove b b' p p') = fun _ => pairMove b b' p p' := by
    funext q
    exact (pairMove b b' p p').fderiv
  have h2 : fderiv ℝ (fderiv ℝ (pairMove b b' p p')) 0 = 0 := by
    rw [h1]
    simp
  rw [h2, h1]
  simp [pairMove]
end Mixed
end YangMills.Construction.FreeBondMoves
end
