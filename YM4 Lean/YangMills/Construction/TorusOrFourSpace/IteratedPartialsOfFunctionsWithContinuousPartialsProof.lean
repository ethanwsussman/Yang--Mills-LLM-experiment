import YangMills.Construction.TorusOrFourSpace.ContinuousPartialsAreContinuousDifferentiability
import YangMills.Construction.TorusOrFourSpace.IteratedPartialsOfFunctionsWithContinuousPartials
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.IteratedPartials
open Coords
variable {p : ℕ+}
theorem partialAlong_eq_fderiv {F : Coords p → ℂ} (hF : Differentiable ℝ F)
    (k : Fin (4 * (p : ℕ))) (x : Coords p) :
    partialAlong k F x = fderiv ℝ F x (Pi.single k 1) :=
  (hF x).lineDeriv_eq_fderiv
theorem contDiff_partialAlong {n : ℕ} {F : Coords p → ℂ}
    (hF : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F) (k : Fin (4 * (p : ℕ))) :
    ContDiff ℝ (n : WithTop ℕ∞) (partialAlong k F) := by
  have hdiff : Differentiable ℝ F := hF.differentiable (by simp)
  have heq : partialAlong k F = fun x => fderiv ℝ F x (Pi.single k 1) :=
    funext (partialAlong_eq_fderiv hdiff k)
  rw [heq]
  exact (hF.fderiv_right (m := (n : WithTop ℕ∞)) (by norm_cast)).clm_apply contDiff_const
theorem partialAlong_comm {F : Coords p → ℂ}
    (hF : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) F) (a b : Fin (4 * (p : ℕ))) :
    partialAlong a (partialAlong b F) = partialAlong b (partialAlong a F) := by
  have hdiff : Differentiable ℝ F := hF.differentiable (by simp)
  have hD : ContDiff ℝ (1 : WithTop ℕ∞) (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hDd : Differentiable ℝ (fderiv ℝ F) := hD.differentiable (by simp)
  have second : ∀ (u v : Fin (4 * (p : ℕ))) (x : Coords p),
      partialAlong u (partialAlong v F) x =
        fderiv ℝ (fderiv ℝ F) x (Pi.single u 1) (Pi.single v 1) := by
    intro u v x
    have hv : partialAlong v F = fun y => fderiv ℝ F y (Pi.single v 1) :=
      funext (partialAlong_eq_fderiv hdiff v)
    have hdv : DifferentiableAt ℝ (fun y => fderiv ℝ F y (Pi.single v 1)) x :=
      (hDd x).clm_apply (differentiableAt_const _)
    rw [hv]
    change lineDeriv ℝ (fun y => fderiv ℝ F y (Pi.single v 1)) x (Pi.single u 1) = _
    rw [hdv.lineDeriv_eq_fderiv, fderiv_clm_apply (hDd x) (differentiableAt_const _)]
    simp
  funext x
  rw [second, second]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp)) _ _
def partialWord (w : List (Fin (4 * (p : ℕ)))) (F : Coords p → ℂ) : Coords p → ℂ :=
  w.foldr partialAlong F
theorem partialWord_append (u v : List (Fin (4 * (p : ℕ)))) (F : Coords p → ℂ) :
    partialWord (u ++ v) F = partialWord u (partialWord v F) := by
  simp [partialWord, List.foldr_append]
theorem partialWord_replicate (n : ℕ) (k : Fin (4 * (p : ℕ))) (F : Coords p → ℂ) :
    partialWord (List.replicate n k) F = (partialAlong k)^[n] F := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl
theorem contDiff_partialWord (w : List (Fin (4 * (p : ℕ)))) (n : ℕ) {F : Coords p → ℂ}
    (hF : ContDiff ℝ ((n + w.length : ℕ) : WithTop ℕ∞) F) :
    ContDiff ℝ (n : WithTop ℕ∞) (partialWord w F) := by
  induction w generalizing n with
  | nil => simpa [partialWord] using hF
  | cons k w ih =>
    refine contDiff_partialAlong (n := n) (ih (n + 1) ?_) k
    have : n + 1 + w.length = n + (k :: w).length := by simp; omega
    rwa [this]
theorem partialWord_perm {w w' : List (Fin (4 * (p : ℕ)))} (h : w.Perm w') :
    ∀ {F : Coords p → ℂ}, ContDiff ℝ (w.length : WithTop ℕ∞) F →
      partialWord w F = partialWord w' F := by
  induction h with
  | nil => intro F _; rfl
  | cons x _ ih =>
    intro F hF
    have := ih (F := F) (hF.of_le (by norm_cast; simp))
    change partialAlong x (partialWord _ F) = partialAlong x (partialWord _ F)
    rw [this]
  | swap x y w =>
    intro F hF
    have h2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (partialWord w F) :=
      contDiff_partialWord w 2 (by
        have : 2 + w.length = (y :: x :: w).length := by simp; omega
        rwa [this])
    exact partialAlong_comm h2 y x
  | trans h₁ _ ih₁ ih₂ =>
    intro F hF
    rw [ih₁ hF, ih₂ (by rwa [← h₁.length_eq])]
def multiIndexToList (α : CoordIndex p) : List (Fin (4 * (p : ℕ))) :=
  (List.finRange (4 * (p : ℕ))).flatMap fun k => List.replicate (α k) k
theorem iterPartial_eq_partialWord (α : CoordIndex p) (F : Coords p → ℂ) :
    iterPartial α F = partialWord (multiIndexToList α) F := by
  unfold Coords.iterPartial multiIndexToList
  induction List.finRange (4 * (p : ℕ)) with
  | nil => rfl
  | cons k L ih =>
    rw [List.foldr_cons, List.flatMap_cons, partialWord_append, partialWord_replicate, ih]
theorem length_multiIndexToList (α : CoordIndex p) : (multiIndexToList α).length = α.degree := by
  simp [multiIndexToList, CoordIndex.degree, List.length_flatMap, Fin.sum_univ_def]
theorem count_multiIndexList (α : CoordIndex p) (k : Fin (4 * (p : ℕ))) :
    (multiIndexToList α).count k = α k := by
  have h : ∀ L : List (Fin (4 * (p : ℕ))), L.Nodup →
      (L.flatMap fun i => List.replicate (α i) i).count k = if k ∈ L then α k else 0 := by
    intro L
    induction L with
    | nil => simp
    | cons i L ih =>
      intro hL
      rw [List.flatMap_cons, List.count_append, ih (List.nodup_cons.mp hL).2, List.count_replicate]
      have hi := (List.nodup_cons.mp hL).1
      by_cases hik : i = k
      · subst hik
        simp [hi]
      · have hki : k ≠ i := fun e => hik e.symm
        simp [hik, hki]
  simpa [multiIndexToList] using h _ (List.nodup_finRange _)
theorem iteratedPartialsCompose_of_contPartialsIffContDiff (h : ContPartialsIffContDiff) :
    PartialDerivatives.IteratedPartialsCompose := by
  intro p ν F hF α hα
  have hC : ContDiff ℝ (ν : WithTop ℕ∞) F := (h p ν F).mp hF
  refine ⟨(h p _ _).mpr ?_, ?_⟩
  · rw [iterPartial_eq_partialWord]
    refine contDiff_partialWord _ _ ?_
    rw [length_multiIndexToList, Nat.sub_add_cancel hα]
    exact hC
  · intro β hβ
    rw [iterPartial_eq_partialWord α, iterPartial_eq_partialWord β,
      iterPartial_eq_partialWord (α + β), ← partialWord_append]
    refine partialWord_perm (List.perm_iff_count.mpr fun k => ?_) (hC.of_le ?_)
    · simp [List.count_append, count_multiIndexList, add_comm]
    · rw [List.length_append, length_multiIndexToList, length_multiIndexToList]
      norm_cast
      omega
end YangMills.Construction.PeriodicSpace.IteratedPartials
