import YangMills.Construction.TorusOrFourSpace.ContinuousPartialsAreContinuousDifferentiability
import YangMills.Construction.TorusOrFourSpace.ContinuousPartialsUnderTranslationsSumsAndProducts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PartialsAlgebra
open Coords
variable {p : ℕ+}
theorem iterPartial_of_commute (T : (Coords p → ℂ) → Coords p → ℂ)
    (hT : ∀ j F, partialAlong j (T F) = T (partialAlong j F))
    (α : CoordIndex p) (F : Coords p → ℂ) :
    iterPartial α (T F) = T (iterPartial α F) := by
  unfold iterPartial
  induction List.finRange (4 * (p : ℕ)) with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact (Function.Semiconj.iterate_right (f := T) (ga := partialAlong j)
      (gb := partialAlong j) (fun H => (hT j H).symm) (α j) _).symm
theorem partialAlong_comp_add (v : Coords p) (j : Fin (4 * (p : ℕ)))
    (F : Coords p → ℂ) :
    partialAlong j (fun x => F (x + v)) = fun x => partialAlong j F (x + v) := by
  funext x
  have hfun : (fun t : ℝ => F (x + t • (Pi.single j 1 : Coords p) + v)) =
      fun t => F (x + v + t • (Pi.single j 1 : Coords p)) := by
    funext t
    rw [add_right_comm]
  exact congrArg (fun f => deriv f 0) hfun
theorem partialAlong_eq_zero_of_eqOn {U : Set (Coords p)} (hU : IsOpen U)
    {F : Coords p → ℂ} (hF : ∀ x ∈ U, F x = 0) (j : Fin (4 * (p : ℕ))) :
    ∀ x ∈ U, partialAlong j F x = 0 := by
  intro x hx
  have hcont : Continuous fun t : ℝ => x + t • (Pi.single j 1 : Coords p) := by fun_prop
  have hnhds : (fun t : ℝ => x + t • (Pi.single j 1 : Coords p)) ⁻¹' U ∈ nhds (0 : ℝ) :=
    (hU.preimage hcont).mem_nhds (by simpa using hx)
  have hloc : (fun t : ℝ => F (x + t • (Pi.single j 1 : Coords p))) =ᶠ[nhds 0]
      fun _ => (0 : ℂ) := by
    filter_upwards [hnhds] with t ht using hF _ ht
  unfold partialAlong lineDeriv
  rw [hloc.deriv_eq]
  simp
theorem iterate_partialAlong_eq_zero_of_eqOn {U : Set (Coords p)} (hU : IsOpen U)
    (j : Fin (4 * (p : ℕ))) (n : ℕ) {F : Coords p → ℂ} (hF : ∀ x ∈ U, F x = 0) :
    ∀ x ∈ U, (partialAlong j)^[n] F x = 0 := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact partialAlong_eq_zero_of_eqOn hU ih j
theorem iterPartial_eq_zero_of_eqOn {U : Set (Coords p)} (hU : IsOpen U)
    {F : Coords p → ℂ} (hF : ∀ x ∈ U, F x = 0) (α : CoordIndex p) :
    ∀ x ∈ U, iterPartial α F x = 0 := by
  unfold iterPartial
  induction List.finRange (4 * (p : ℕ)) with
  | nil => simpa using hF
  | cons j l ih =>
    simp only [List.foldr_cons]
    exact iterate_partialAlong_eq_zero_of_eqOn hU j (α j) ih
theorem partialAlong_clm_comp (A : ℂ →L[ℝ] ℂ) (j : Fin (4 * (p : ℕ)))
    (F : Coords p → ℂ) (hF : ∀ x, LineDifferentiableAt ℝ F x (Pi.single j 1)) :
    partialAlong j (fun x => A (F x)) = fun x => A (partialAlong j F x) := by
  funext x
  have hd : HasLineDerivAt ℝ F (lineDeriv ℝ F x (Pi.single j 1)) x (Pi.single j 1) :=
    (hF x).hasLineDerivAt
  have hd' : HasLineDerivAt ℝ (fun y => A (F y)) (A (lineDeriv ℝ F x (Pi.single j 1))) x
      (Pi.single j 1) :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) A.hasFDerivAt hd
  exact hd'.lineDeriv
theorem iterate_partialAlong_clm_comp (A : ℂ →L[ℝ] ℂ) (j : Fin (4 * (p : ℕ))) (n m : ℕ) :
    ∀ F : Coords p → ℂ, ContPartialsUpTo (n + m) F →
      ContPartialsUpTo m ((partialAlong j)^[n] F) ∧
        (partialAlong j)^[n] (fun x => A (F x)) =
          fun x => A ((partialAlong j)^[n] F x) := by
  induction n with
  | zero =>
    intro F hF
    exact ⟨by simpa using hF, rfl⟩
  | succ n ih =>
    intro F hF
    have hF' : ContPartialsUpTo ((n + m) + 1) F := by
      rwa [show n + m + 1 = n + 1 + m by omega]
    have hj := hF'.2 j
    simp only [Function.iterate_succ_apply]
    rw [partialAlong_clm_comp A j F hj.1]
    exact ih _ hj.2
theorem foldr_partialAlong_clm_comp (A : ℂ →L[ℝ] ℂ) (α : CoordIndex p)
    (l : List (Fin (4 * (p : ℕ)))) :
    ∀ (m : ℕ) (F : Coords p → ℂ), ContPartialsUpTo ((l.map α).sum + m) F →
      ContPartialsUpTo m (l.foldr (fun j H => (partialAlong j)^[α j] H) F) ∧
        l.foldr (fun j H => (partialAlong j)^[α j] H) (fun x => A (F x)) =
          fun x => A (l.foldr (fun j H => (partialAlong j)^[α j] H) F x) := by
  induction l with
  | nil =>
    intro m F hF
    exact ⟨by simpa using hF, rfl⟩
  | cons j l ih =>
    intro m F hF
    have hF' : ContPartialsUpTo ((l.map α).sum + (α j + m)) F := by
      have hsum : (l.map α).sum + (α j + m) = ((j :: l).map α).sum + m := by
        simp only [List.map_cons, List.sum_cons]
        omega
      rwa [hsum]
    obtain ⟨h₁, h₂⟩ := ih (α j + m) F hF'
    simp only [List.foldr_cons]
    rw [h₂]
    exact iterate_partialAlong_clm_comp A j (α j) m _ h₁
theorem iterPartial_clm_comp (hmono : ∀ (ν μ : ℕ) (F : Coords p → ℂ), μ ≤ ν →
      ContPartialsUpTo ν F → ContPartialsUpTo μ F)
    (A : ℂ →L[ℝ] ℂ) {ν : ℕ} {F : Coords p → ℂ} (hF : ContPartialsUpTo ν F)
    {α : CoordIndex p} (hα : α.degree ≤ ν) :
    iterPartial α (fun x => A (F x)) = fun x => A (iterPartial α F x) := by
  have hdeg : α.degree = ((List.finRange (4 * (p : ℕ))).map α).sum := Fin.sum_univ_def α
  exact (foldr_partialAlong_clm_comp A α (List.finRange (4 * (p : ℕ))) 0 F
    (by simpa [← hdeg] using hmono ν α.degree F hα hF)).2
theorem statement_holds (hiff : ContPartialsIffContDiff) : Statement := by
  intro p
  have hmono : ∀ (ν μ : ℕ) (F : Coords p → ℂ), μ ≤ ν →
      ContPartialsUpTo ν F → ContPartialsUpTo μ F := fun ν μ F hμ hF =>
    (hiff p μ F).2 (((hiff p ν F).1 hF).of_le (by exact_mod_cast hμ))
  refine ⟨fun α F v => ?_, fun α F U hU hF => iterPartial_eq_zero_of_eqOn hU hF α,
    fun ν F H hF hH => ?_⟩
  · exact iterPartial_of_commute (fun K x => K (x + v))
      (fun j K => partialAlong_comp_add v j K) α F
  · have cF := (hiff p ν F).1 hF
    have cH := (hiff p ν H).1 hH
    refine ⟨fun a b => (hiff p ν _).2 ?_, (hiff p ν _).2 (cF.mul cH), (hiff p ν _).2 ?_,
      (hiff p ν _).2 ?_, fun α hα => ⟨?_, ?_⟩⟩
    · exact (contDiff_const.smul cF).add (contDiff_const.smul cH)
    · exact (Complex.ofRealCLM.comp Complex.reCLM).contDiff.comp cF
    · exact (Complex.ofRealCLM.comp Complex.imCLM).contDiff.comp cF
    · exact iterPartial_clm_comp hmono (Complex.ofRealCLM.comp Complex.reCLM) hF hα
    · exact iterPartial_clm_comp hmono (Complex.ofRealCLM.comp Complex.imCLM) hF hα
end YangMills.Construction.PeriodicSpace.PartialsAlgebra
