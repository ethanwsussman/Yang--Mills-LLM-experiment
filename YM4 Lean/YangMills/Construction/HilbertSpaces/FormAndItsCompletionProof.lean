import YangMills.Construction.HilbertSpaces.FormAndItsCompletion
import YangMills.Construction.HilbertSpaces.SemigroupOnTheCompletionProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ComplexOrder InnerProductSpace
open YangMills.Construction.FormsOperators (IsHilbertCompletion IsSesquilinear PosFormQuotient qNorm
  formRadical formOnQuotient norm_eq_sqrt_re_inner_self)
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction.QuotientCompletion
theorem le_of_pow_two_pow_le_mul_pow {a b σ : ℝ} (hb : 0 ≤ b)
    (h : ∀ k : ℕ, ∃ e : ℕ, e + 1 = 2 ^ k ∧ a ^ (2 ^ k) ≤ b ^ e * σ) : a ≤ b := by
  by_contra hab
  rw [not_le] at hab
  rcases hb.eq_or_lt with hzero | hbpos
  · obtain ⟨e, he, hk⟩ := h 1
    have heq : e = 1 := by omega
    subst heq
    have hapos : 0 < a ^ (2 ^ 1) := pow_pos (hzero ▸ hab) _
    rw [← hzero] at hk
    simp only [pow_one, zero_mul] at hk hapos
    linarith
  · have hratio : 1 < a / b := (one_lt_div hbpos).mpr hab
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (σ / b) hratio
    obtain ⟨e, he, hk⟩ := h m
    have hmono : (a / b) ^ m ≤ (a / b) ^ (2 ^ m) :=
      pow_le_pow_right₀ hratio.le Nat.lt_two_pow_self.le
    have hsplit : b ^ (2 ^ m) = b ^ e * b := by rw [← he, pow_succ]
    have hupper : (a / b) ^ (2 ^ m) ≤ σ / b := by
      rw [div_pow, div_le_div_iff₀ (pow_pos hbpos _) hbpos, hsplit]
      calc a ^ (2 ^ m) * b ≤ b ^ e * σ * b := mul_le_mul_of_nonneg_right hk hbpos.le
        _ = σ * (b ^ e * b) := by ring
    linarith
section Contraction
variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : PreHilbertData V}
theorem zero_le_re_form_self (hS : S.IsAdmissible) (x : V) : 0 ≤ (S.form x x).re :=
  (Complex.le_def.mp (hS.posSemidef.nonneg x)).1
theorem im_form_self_eq_zero (hS : S.IsAdmissible) (x : V) : (S.form x x).im = 0 :=
  (Complex.le_def.mp (hS.posSemidef.nonneg x)).2.symm
theorem form_semigroupMap_self (hS : S.IsAdmissible) (t : ℝ≥0) (x : V) :
    S.form (S.semigroupMap t x) (S.semigroupMap t x) = S.form x (S.semigroupMap (t + t) x) := by apply _root_.YangMills.Construction.PositiveFormReconstruction.SemigroupOnCompletion.form_semigroupMap_semigroupMap <;> assumption
theorem norm_form_sq_le (hQ : PosFormQuotient) (hS : S.IsAdmissible) (x y : V) :
    ‖S.form x y‖ ^ 2 ≤ (S.form x x).re * (S.form y y).re := by
  have hcs := (hQ V S.form hS.hermitian hS.posSemidef).1 x y
  unfold qNorm at hcs
  calc ‖S.form x y‖ ^ 2
      ≤ (Real.sqrt (S.form x x).re * Real.sqrt (S.form y y).re) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hcs 2
    _ = (S.form x x).re * (S.form y y).re := by
        rw [mul_pow, Real.sq_sqrt (zero_le_re_form_self hS x),
          Real.sq_sqrt (zero_le_re_form_self hS y)]
theorem re_form_semigroupMap_sq_le (hQ : PosFormQuotient) (hS : S.IsAdmissible) (t : ℝ≥0)
    (x : V) :
    (S.form (S.semigroupMap t x) (S.semigroupMap t x)).re ^ 2 ≤
      (S.form x x).re * (S.form (S.semigroupMap (t + t) x) (S.semigroupMap (t + t) x)).re := by
  have hle : (S.form (S.semigroupMap t x) (S.semigroupMap t x)).re ≤
      ‖S.form x (S.semigroupMap (t + t) x)‖ := by
    rw [form_semigroupMap_self hS]
    exact Complex.re_le_norm _
  exact (pow_le_pow_left₀ (zero_le_re_form_self hS _) hle 2).trans (norm_form_sq_le hQ hS _ _)
theorem re_form_semigroupMap_le (hQ : PosFormQuotient) (hS : S.IsAdmissible) (t : ℝ≥0) (x : V) :
    (S.form (S.semigroupMap t x) (S.semigroupMap t x)).re ≤ (S.form x x).re := by
  obtain ⟨σ, hσ⟩ := hS.bddAbove_semigroup x
  have hbdd : ∀ u : ℝ≥0, (S.form (S.semigroupMap u x) (S.semigroupMap u x)).re ≤ σ := fun u => by
    rw [form_semigroupMap_self hS]
    exact (Complex.re_le_norm _).trans (hσ ⟨u + u, rfl⟩)
  have hb := zero_le_re_form_self hS x
  have hiter : ∀ k : ℕ, ∃ e : ℕ, e + 1 = 2 ^ k ∧
      (S.form (S.semigroupMap t x) (S.semigroupMap t x)).re ^ (2 ^ k) ≤ (S.form x x).re ^ e *
        (S.form (S.semigroupMap ((2 : ℝ≥0) ^ k * t) x)
          (S.semigroupMap ((2 : ℝ≥0) ^ k * t) x)).re := by
    intro k
    induction k with
    | zero => exact ⟨0, by norm_num, by simp⟩
    | succ k ih =>
      obtain ⟨e, he, hk⟩ := ih
      have htime : (2 : ℝ≥0) ^ (k + 1) * t = 2 ^ k * t + 2 ^ k * t := by
        rw [pow_succ]
        ring
      refine ⟨2 * e + 1, by rw [pow_succ]; omega, ?_⟩
      calc (S.form (S.semigroupMap t x) (S.semigroupMap t x)).re ^ (2 ^ (k + 1))
          = ((S.form (S.semigroupMap t x) (S.semigroupMap t x)).re ^ (2 ^ k)) ^ 2 := by
            rw [pow_succ 2 k, pow_mul]
        _ ≤ ((S.form x x).re ^ e *
              (S.form (S.semigroupMap ((2 : ℝ≥0) ^ k * t) x)
                (S.semigroupMap ((2 : ℝ≥0) ^ k * t) x)).re) ^ 2 :=
            pow_le_pow_left₀ (pow_nonneg (zero_le_re_form_self hS _) _) hk 2
        _ = (S.form x x).re ^ (2 * e) *
              (S.form (S.semigroupMap ((2 : ℝ≥0) ^ k * t) x)
                (S.semigroupMap ((2 : ℝ≥0) ^ k * t) x)).re ^ 2 := by ring
        _ ≤ (S.form x x).re ^ (2 * e) * ((S.form x x).re *
              (S.form (S.semigroupMap (2 ^ k * t + 2 ^ k * t) x)
                (S.semigroupMap (2 ^ k * t + 2 ^ k * t) x)).re) :=
            mul_le_mul_of_nonneg_left (re_form_semigroupMap_sq_le hQ hS _ x) (pow_nonneg hb _)
        _ = (S.form x x).re ^ (2 * e + 1) *
              (S.form (S.semigroupMap ((2 : ℝ≥0) ^ (k + 1) * t) x)
                (S.semigroupMap ((2 : ℝ≥0) ^ (k + 1) * t) x)).re := by
            rw [htime]
            ring
  refine le_of_pow_two_pow_le_mul_pow (σ := σ) hb fun k => ?_
  obtain ⟨e, he, hk⟩ := hiter k
  exact ⟨e, he, hk.trans (mul_le_mul_of_nonneg_left (hbdd _) (pow_nonneg hb _))⟩
theorem form_semigroupMap_le (hQ : PosFormQuotient) (hS : S.IsAdmissible) (t : ℝ≥0) (x : V) :
    S.form (S.semigroupMap t x) (S.semigroupMap t x) ≤ S.form x x :=
  Complex.le_def.mpr ⟨re_form_semigroupMap_le hQ hS t x,
    by rw [im_form_self_eq_zero hS, im_form_self_eq_zero hS]⟩
end Contraction
section Classes
variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : PreHilbertData V}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem norm_embed_sub_sq (hS : S.IsAdmissible) (hq : IsSesquilinear S.form)
    (hmk : ∀ x y : V, formOnQuotient S.form hq (Submodule.Quotient.mk x)
      (Submodule.Quotient.mk y) = S.form x y)
    {j : (V ⧸ formRadical S.form hq) →ₗ[ℂ] H}
    (hj : IsHilbertCompletion (formOnQuotient S.form hq) j) (x y : V) :
    ‖embed S hq j x - embed S hq j y‖ ^ 2 = (S.form (x - y) (x - y)).re := by
  have hdiff : embed S hq j x - embed S hq j y = j (Submodule.Quotient.mk (x - y)) := by
    simp only [embed, Submodule.Quotient.mk_sub, map_sub]
  rw [hdiff, norm_eq_sqrt_re_inner_self, hj.inner_map, hmk,
    Real.sq_sqrt (zero_le_re_form_self hS _)]
end Classes
theorem statement_holds (hC : YangMills.Construction.FormsOperators.FormsAndCompletions) :
    Statement := by
  intro V _ _ S hS
  obtain ⟨-, hQ, -, -, -, -, hE⟩ := hC
  obtain ⟨-, -, -, c₄, c₅, c₆⟩ := hQ V S.form hS.hermitian hS.posSemidef
  refine ⟨⟨c₄, c₅, c₆⟩, ⟨form_semigroupMap_le hQ hS, fun t x hx => ?_⟩, (hE _ _ c₆).1, ?_⟩
  · have hx₀ : S.form x x = 0 := by
      have hmem : x ∈ ((formRadical S.form hS.hermitian.toIsSesquilinear : Submodule ℂ V) : Set V) :=
        hx
      rw [c₄] at hmem
      exact hmem
    have hzero : S.form (S.semigroupMap t x) (S.semigroupMap t x) = 0 :=
      le_antisymm (hx₀ ▸ form_semigroupMap_le hQ hS t x) (hS.posSemidef.nonneg _)
    exact show S.semigroupMap t x ∈
        ((formRadical S.form hS.hermitian.toIsSesquilinear : Submodule ℂ V) : Set V) from by
      rw [c₄]
      exact hzero
  · intro H _ _ _ j hj
    refine ⟨?_, fun D hD hdense => ?_⟩
    · have hone : ⟪vacuum S hS.hermitian.toIsSesquilinear j,
          vacuum S hS.hermitian.toIsSesquilinear j⟫_ℂ = 1 := by
        unfold vacuum embed
        rw [hj.inner_map, c₅, hS.form_unitVec]
      rw [norm_eq_sqrt_re_inner_self, hone, Complex.one_re, Real.sqrt_one]
    · refine ⟨embed S hS.hermitian.toIsSesquilinear j '' D, hD.image _,
        And.intro (subset_univ _) fun ψ _ ε hε => ?_⟩
      obtain ⟨_, hφ, w, rfl⟩ := hj.dense_range.2 ψ (mem_univ ψ) (ε / 2) (by positivity)
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      obtain ⟨y, hy, hlt⟩ := hdense x ((ε / 2) ^ 2) (by positivity)
      have hre : (S.form (x - y) (x - y)).re < (ε / 2) ^ 2 := by
        have hpart := (Complex.lt_def.mp hlt).1
        rwa [Complex.ofReal_re] at hpart
      have hnorm : ‖embed S hS.hermitian.toIsSesquilinear j x -
          embed S hS.hermitian.toIsSesquilinear j y‖ < ε / 2 := by
        refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
        rw [norm_embed_sub_sq hS _ c₅ hj]
        exact hre
      refine ⟨embed S hS.hermitian.toIsSesquilinear j y, ?_, mem_image_of_mem _ hy⟩
      have hφ' : ‖embed S hS.hermitian.toIsSesquilinear j x - ψ‖ < ε / 2 := hφ
      show ‖embed S hS.hermitian.toIsSesquilinear j y - ψ‖ < ε
      calc ‖embed S hS.hermitian.toIsSesquilinear j y - ψ‖
          = ‖(embed S hS.hermitian.toIsSesquilinear j y -
                embed S hS.hermitian.toIsSesquilinear j x) +
              (embed S hS.hermitian.toIsSesquilinear j x - ψ)‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ ‖embed S hS.hermitian.toIsSesquilinear j y -
                embed S hS.hermitian.toIsSesquilinear j x‖ +
              ‖embed S hS.hermitian.toIsSesquilinear j x - ψ‖ := norm_add_le _ _
        _ < ε := by
            rw [norm_sub_rev (embed S hS.hermitian.toIsSesquilinear j y)]
            linarith
end YangMills.Construction.PositiveFormReconstruction.QuotientCompletion
