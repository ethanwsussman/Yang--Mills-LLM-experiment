import YangMills.Construction.InfiniteLattice.PeriodicExtensionOfATorusOfAnyShape
import YangMills.Construction.ReflectionPositivity.ChessboardEstimateOnTheSlabsOfASplitTorus
import YangMills.Construction.ReflectionPositivity.CopyRuleOnTheSlabs
import YangMills.Construction.ReflectionPositivity.ReflectionPositivityOnSplitTori
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.InfiniteLattice.SlabChessboard
section Folding
variable {J : ℕ} [NeZero (2 * J)]
def pairedIndex (s k : ZMod (2 * J)) : ZMod (2 * J) := s + s - 1 - k
omit [NeZero (2 * J)] in
theorem pairedIndex_pairedIndex (s k : ZMod (2 * J)) : pairedIndex s (pairedIndex s k) = k := by
  simp only [pairedIndex]
  ring
def aboveMirror (s : ZMod (2 * J)) : Finset (ZMod (2 * J)) :=
  Finset.univ.filter fun k => (k - s).val < J
theorem mem_aboveMirror {s k : ZMod (2 * J)} : k ∈ aboveMirror s ↔ (k - s).val < J := by
  simp [aboveMirror]
theorem val_neg_one_sub_eq (i : ZMod (2 * J)) : (-1 - i).val = 2 * J - 1 - i.val := by
  have hi := ZMod.val_lt i
  have e : ((2 * J - 1 - i.val : ℕ) : ZMod (2 * J)) + (i.val : ZMod (2 * J)) + 1 =
      ((2 * J : ℕ) : ZMod (2 * J)) := by
    have h : 2 * J - 1 - i.val + i.val + 1 = 2 * J := by omega
    rw [← Nat.cast_add, ← Nat.cast_succ]
    exact congrArg Nat.cast h
  rw [ZMod.natCast_self, ZMod.natCast_zmod_val] at e
  have e' : -1 - i = ((2 * J - 1 - i.val : ℕ) : ZMod (2 * J)) := by
    linear_combination -e
  rw [e', ZMod.val_natCast_of_lt (show 2 * J - 1 - i.val < 2 * J by omega)]
theorem pairedIndex_mem_aboveMirror_iff {s k : ZMod (2 * J)} :
    pairedIndex s k ∈ aboveMirror s ↔ k ∉ aboveMirror s := by
  rw [mem_aboveMirror, mem_aboveMirror]
  have e : pairedIndex s k - s = -1 - (k - s) := by
    simp only [pairedIndex]
    ring
  rw [e, val_neg_one_sub_eq]
  have := ZMod.val_lt (k - s)
  omega
theorem prod_eq_prod_aboveMirror_mul {M : Type*} [CommMonoid M] (s : ZMod (2 * J))
    (g : ZMod (2 * J) → M) :
    ∏ k, g k = (∏ k ∈ aboveMirror s, g k) * ∏ k ∈ aboveMirror s, g (pairedIndex s k) := by
  have h := Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => (k - s).val < J) g
  rw [← h]
  congr 1
  refine Finset.prod_nbij' (pairedIndex s) (pairedIndex s) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    have hk' : k ∉ aboveMirror s := by
      rw [mem_aboveMirror]
      simpa using hk
    exact pairedIndex_mem_aboveMirror_iff.2 hk'
  · intro k hk
    have h' : pairedIndex s k ∉ aboveMirror s := by
      rw [← pairedIndex_mem_aboveMirror_iff, pairedIndex_pairedIndex]
      exact hk
    rw [mem_aboveMirror] at h'
    simpa using h'
  · intro k _
    exact pairedIndex_pairedIndex s k
  · intro k _
    exact pairedIndex_pairedIndex s k
  · intro k _
    rw [pairedIndex_pairedIndex]
variable {ι : Type*}
def foldUp (s : ZMod (2 * J)) (ς : ZMod (2 * J) → ι) (k : ZMod (2 * J)) : ι :=
  if k ∈ aboveMirror s then ς k else ς (pairedIndex s k)
def foldDown (s : ZMod (2 * J)) (ς : ZMod (2 * J) → ι) (k : ZMod (2 * J)) : ι :=
  if k ∈ aboveMirror s then ς (pairedIndex s k) else ς k
theorem foldUp_of_mem {s k : ZMod (2 * J)} (ς : ZMod (2 * J) → ι) (hk : k ∈ aboveMirror s) :
    foldUp s ς k = ς k := if_pos hk
theorem foldUp_pairedIndex {s k : ZMod (2 * J)} (ς : ZMod (2 * J) → ι) (hk : k ∈ aboveMirror s) :
    foldUp s ς (pairedIndex s k) = ς k := by
  have h : pairedIndex s k ∉ aboveMirror s := by
    rw [← pairedIndex_mem_aboveMirror_iff, pairedIndex_pairedIndex]
    exact hk
  rw [foldUp, if_neg h, pairedIndex_pairedIndex]
theorem foldDown_of_mem {s k : ZMod (2 * J)} (ς : ZMod (2 * J) → ι) (hk : k ∈ aboveMirror s) :
    foldDown s ς k = ς (pairedIndex s k) := if_pos hk
theorem foldDown_pairedIndex {s k : ZMod (2 * J)} (ς : ZMod (2 * J) → ι)
    (hk : k ∈ aboveMirror s) :
    foldDown s ς (pairedIndex s k) = ς (pairedIndex s k) := by
  have h : pairedIndex s k ∉ aboveMirror s := by
    rw [← pairedIndex_mem_aboveMirror_iff, pairedIndex_pairedIndex]
    exact hk
  rw [foldDown, if_neg h]
theorem prod_foldUp {M : Type*} [CommMonoid M] (s : ZMod (2 * J)) (ς : ZMod (2 * J) → ι)
    (g : ZMod (2 * J) → ι → M) :
    ∏ k, g k (foldUp s ς k) =
      (∏ k ∈ aboveMirror s, g k (ς k)) * ∏ k ∈ aboveMirror s, g (pairedIndex s k) (ς k) := by
  rw [prod_eq_prod_aboveMirror_mul s]
  congr 1
  · exact Finset.prod_congr rfl fun k hk => by rw [foldUp_of_mem ς hk]
  · exact Finset.prod_congr rfl fun k hk => by rw [foldUp_pairedIndex ς hk]
theorem prod_foldDown {M : Type*} [CommMonoid M] (s : ZMod (2 * J)) (ς : ZMod (2 * J) → ι)
    (g : ZMod (2 * J) → ι → M) :
    ∏ k, g k (foldDown s ς k) =
      (∏ k ∈ aboveMirror s, g k (ς (pairedIndex s k))) *
        ∏ k ∈ aboveMirror s, g (pairedIndex s k) (ς (pairedIndex s k)) := by
  rw [prod_eq_prod_aboveMirror_mul s]
  congr 1
  · exact Finset.prod_congr rfl fun k hk => by rw [foldDown_of_mem ς hk]
  · exact Finset.prod_congr rfl fun k hk => by rw [foldDown_pairedIndex ς hk]
theorem exists_le_const_of_fold_ineq [Finite ι] (hJ : 1 ≤ J) (T : (ZMod (2 * J) → ι) → ℝ)
    (hpos : ∀ ς, 0 < T ς)
    (hstep : ∀ ς s, T ς ^ 2 ≤ T (foldUp s ς) * T (foldDown s ς)) (ς₀ : ZMod (2 * J) → ι) :
    ∃ j, T ς₀ ≤ T fun _ => j := by
  have : Nonempty (ZMod (2 * J) → ι) := ⟨ς₀⟩
  obtain ⟨m, hm⟩ := Finite.exists_max T
  have stable : ∀ ς s, T ς = T m → T (foldUp s ς) = T m := by
    intro ς s h
    have h₁ := hstep ς s
    rw [h] at h₁
    have h₂ := hm (foldUp s ς)
    have h₃ := hm (foldDown s ς)
    have h₄ := hpos (foldUp s ς)
    have h₅ := hpos (foldDown s ς)
    have h₆ := hpos m
    refine le_antisymm h₂ ?_
    by_contra hc
    have h₇ : T (foldUp s ς) < T m := not_le.mp hc
    nlinarith
  have run : ∀ χ : ℕ, χ ≤ J →
      ∃ (ς : ZMod (2 * J) → ι) (s : ZMod (2 * J)), T ς = T m ∧
        ∀ i : ℕ, i < χ → ς (s + (i : ZMod (2 * J))) = ς s := by
    intro χ
    induction χ with
    | zero =>
      intro _
      exact ⟨m, 0, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    | succ χ ih =>
      intro hχ
      obtain ⟨ς, s, hς, hrun⟩ := ih (by omega)
      have hs : s ∈ aboveMirror s := by
        rw [mem_aboveMirror, sub_self, ZMod.val_zero]
        omega
      have e₀ : foldUp s ς (s - 1) = ς s := by
        have e : s - 1 = pairedIndex s s := by
          simp only [pairedIndex]
          ring
        rw [e, foldUp_pairedIndex ς hs]
      refine ⟨foldUp s ς, s - 1, stable ς s hς, fun i hi => ?_⟩
      rw [e₀]
      rcases i with _ | i
      · simpa using e₀
      · have e : s - 1 + ((i + 1 : ℕ) : ZMod (2 * J)) = s + (i : ZMod (2 * J)) := by
          push_cast
          ring
        have hk : s + (i : ZMod (2 * J)) ∈ aboveMirror s := by
          rw [mem_aboveMirror, add_sub_cancel_left,
            ZMod.val_natCast_of_lt (show i < 2 * J by omega)]
          omega
        rw [e, foldUp_of_mem ς hk]
        exact hrun i (by omega)
  obtain ⟨ς, s, hς, hrun⟩ := run J le_rfl
  have hup : ∀ k ∈ aboveMirror s, ς k = ς s := by
    intro k hk
    have h := hrun _ (mem_aboveMirror.1 hk)
    rwa [ZMod.natCast_zmod_val, add_sub_cancel] at h
  have hconst : foldUp s ς = fun _ => ς s := by
    funext k
    by_cases hk : k ∈ aboveMirror s
    · rw [foldUp_of_mem ς hk, hup k hk]
    · rw [foldUp, if_neg hk, hup _ (pairedIndex_mem_aboveMirror_iff.2 hk)]
  refine ⟨ς s, ?_⟩
  rw [← hconst, stable ς s hς]
  exact hm ς₀
end Folding
theorem re_sq_le_of_hermitian_form {E : Type*} [AddCommGroup E] [Module ℂ E] (A : Set E)
    (B : E → E → ℂ)
    {x y : E} (hx : x ∈ A) (hy : y ∈ A) (hcomb : ∀ w : ℂ, w • x + y ∈ A)
    (hsesq : ∀ F ∈ A, ∀ F' ∈ A, ∀ F'' ∈ A, ∀ w : ℂ,
      B F' (w • F + F'') = w * B F' F + B F' F'' ∧
        B (w • F + F'') F' = conj w * B F F' + B F'' F')
    (hherm : ∀ F ∈ A, ∀ F' ∈ A, B F' F = conj (B F F'))
    (hnonneg : ∀ F ∈ A, 0 ≤ B F F)
    (hyx : (B y x).im = 0) (hxx : 0 < (B x x).re) :
    (B y x).re ^ 2 ≤ (B x x).re * (B y y).re := by
  set a := (B x x).re with ha
  set b := (B y x).re with hb
  set d := (B y y).re with hd
  have eax : B x x = (a : ℂ) :=
    Complex.ext rfl (by simpa using ((Complex.le_def.1 (hnonneg x hx)).2).symm)
  have edy : B y y = (d : ℂ) :=
    Complex.ext rfl (by simpa using ((Complex.le_def.1 (hnonneg y hy)).2).symm)
  have ebx : B y x = (b : ℂ) := Complex.ext rfl (by simpa using hyx)
  have exy : B x y = (b : ℂ) := by
    rw [hherm y hy x hx, ebx, Complex.conj_ofReal]
  set t : ℝ := -b / a with ht
  have hzA := hcomb (t : ℂ)
  have h₁ := (hsesq x hx _ hzA y hy (t : ℂ)).2
  have h₂ := (hsesq x hx x hx y hy (t : ℂ)).1
  have h₃ := (hsesq x hx y hy y hy (t : ℂ)).1
  have hz := hnonneg _ hzA
  rw [h₁, h₂, h₃, eax, edy, ebx, exy, Complex.conj_ofReal] at hz
  have e : (t : ℂ) * ((t : ℂ) * (a : ℂ) + (b : ℂ)) + ((t : ℂ) * (b : ℂ) + (d : ℂ)) =
      ((t * (t * a + b) + (t * b + d) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e, Complex.zero_le_real] at hz
  have ha0 : a ≠ 0 := ne_of_gt hxx
  have ta : t * a + b = 0 := by
    rw [ht]
    field_simp
    ring
  have e' : a * (t * (t * a + b) + (t * b + d)) = a * d - b ^ 2 := by
    linear_combination (a * t + b) * ta
  have := mul_nonneg hxx.le hz
  rw [e'] at this
  linarith
instance instSecondCountableSpecialUnitary :
    SecondCountableTopology Matrices.ComplexMatrix2.specialUnitary :=
  haveI : SecondCountableTopology Matrices.ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _
instance quotientHaar_isProbabilityMeasure (Γ : PeriodSublattice 1) :
    IsProbabilityMeasure Γ.quotientHaar := by
  unfold PeriodSublattice.quotientHaar Matrices.ComplexMatrix2.haarPi
  infer_instance
theorem boltzmannWeight_props (Γ : PeriodSublattice 1) (hE : Γ.QuotientLiftFacts) {β : ℝ}
    (hβ : 0 < β) :
    Measurable (Γ.boltzmannWeight β) ∧
      ∀ U, 0 < Γ.boltzmannWeight β U ∧ Γ.boltzmannWeight β U ≤ 1 := by
  classical
  have := hE.finite_quotientPlaquette
  have := Fintype.ofFinite Γ.QuotientPlaquette
  have hsum : ∀ U, ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p =
      ∑ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p := fun U =>
    finsum_eq_sum_of_fintype _
  refine ⟨?_, fun U => ⟨Real.exp_pos _, ?_⟩⟩
  · have e : Γ.boltzmannWeight β =
        fun U => Real.exp (-β * ∑ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p) := by
      funext U
      rw [PeriodSublattice.boltzmannWeight, hsum]
    rw [e]
    exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_finsetSum _ fun p _ =>
        hE.continuous_quotientFaceEnergy p))).measurable
  · have h0 : 0 ≤ ∑ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p :=
      Finset.sum_nonneg fun p _ => (hE.quotientFaceEnergy_mem_Icc p U).1
    rw [PeriodSublattice.boltzmannWeight, hsum]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
section Slabs
variable (S : SlabDecomposition)
theorem measurable_bdd_of_mem_slabAlgebra {k : ZMod (2 * S.count)}
    {F : S.period.QuotientField → ℂ}
    (h : F ∈ S.slabAlgebraOfClass k) : Measurable F ∧ ∃ C : ℝ, ∀ U, ‖F U‖ ≤ C :=
  have h' := S.period.mem_boundedAlgebra.1 h
  ⟨h'.1, h'.2.1⟩
theorem slabAt_subset_plusHalf (s' i : ℤ) (h₀ : 0 ≤ i) (h₁ : i + 1 ≤ S.count) :
    S.slabAt (s' + i) ⊆
      S.period.plusHalf S.normal S.halfPeriod (S.level s') := by
  have hh : (0 : ℝ) < (S.width : ℝ) := by
    have := S.two_le_width
    exact_mod_cast (by omega : 0 < S.width)
  have hi₀ : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h₀
  have hi₁ : (i : ℝ) + 1 ≤ (S.count : ℝ) := by exact_mod_cast h₁
  rintro t ⟨u, hu, hl, hr⟩
  refine ⟨u, hu, ?_, ?_⟩
  · simp only [SlabDecomposition.level] at hl ⊢
    push_cast at hl
    nlinarith
  · simp only [SlabDecomposition.level, SlabDecomposition.halfPeriod] at hr ⊢
    push_cast at hr ⊢
    nlinarith
theorem slabAlgebraOfClass_le_plusAlgebra (s k : ZMod (2 * S.count)) (hk : k ∈ aboveMirror s) :
    S.slabAlgebraOfClass k ≤
      S.period.plusAlgebra S.normal S.halfPeriod (S.level (s.val : ℤ)) := by
  have hk' := mem_aboveMirror.1 hk
  have e : ((((s.val : ℤ) + ((k - s).val : ℤ)) : ℤ) : ZMod (2 * S.count)) = k := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  have hsub := slabAt_subset_plusHalf S (s.val : ℤ) ((k - s).val : ℤ) (by positivity)
    (by omega)
  intro F hF
  rw [← e, S.slabAlgebraOfClass_intCast] at hF
  have h' := S.period.mem_boundedAlgebra.1 hF
  refine S.period.mem_boundedAlgebra.2 ⟨h'.1, h'.2.1, fun U U' h => h'.2.2 U U' fun b hb => ?_⟩
  exact h b (hb.trans hsub)
end Slabs
section Integrals
variable (S : SlabDecomposition)
def chessIntegral (β : ℝ)
    (c : ZMod (2 * S.count) → ZMod (2 * S.count) → S.period.QuotientField → ℂ)
    (ς : ZMod (2 * S.count) → ZMod (2 * S.count)) : ℂ :=
  ∫ U, (∏ k, c k (ς k) U) * (S.period.boltzmannWeight β U : ℂ) ∂S.period.quotientHaar
structure IsCopySystem
    (c : ZMod (2 * S.count) → ZMod (2 * S.count) → S.period.QuotientField → ℂ) : Prop where
  mem : ∀ k j, c k j ∈ S.slabAlgebraOfClass k
  im_eq_zero : ∀ k j U, (c k j U).im = 0
  re_pos : ∀ k j U, 0 < (c k j U).re
  reflect_eq : ∀ s i j, S.conjReflectOfClass s (c (s + i) j) = c (s - 1 - i) j
variable {S}
variable {c : ZMod (2 * S.count) → ZMod (2 * S.count) → S.period.QuotientField → ℂ}
theorem chessIntegral_pos (hE : S.period.QuotientLiftFacts) {β : ℝ} (hβ : 0 < β)
    (hc : IsCopySystem S c) (ς : ZMod (2 * S.count) → ZMod (2 * S.count)) :
    (chessIntegral S β c ς).im = 0 ∧ 0 < (chessIntegral S β c ς).re := by
  obtain ⟨hWm, hW⟩ := boltzmannWeight_props S.period hE hβ
  have hbd : ∀ k j, ∃ C : ℝ, ∀ U, ‖c k j U‖ ≤ C := fun k j =>
    (measurable_bdd_of_mem_slabAlgebra S (hc.mem k j)).2
  choose C hC using hbd
  set g : S.period.QuotientField → ℝ := fun U => ∏ k, (c k (ς k) U).re with hg
  have hval : ∀ U, ∏ k, c k (ς k) U = (g U : ℂ) := fun U => by
    rw [hg, Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun k _ =>
      Complex.ext rfl (by simpa using hc.im_eq_zero k (ς k) U)
  have hgm : Measurable g :=
    Finset.measurable_fun_prod _ fun k _ =>
      Complex.measurable_re.comp (measurable_bdd_of_mem_slabAlgebra S (hc.mem k (ς k))).1
  have hgpos : ∀ U, 0 < g U := fun U => Finset.prod_pos fun k _ => hc.re_pos k (ς k) U
  have hgle : ∀ U, g U ≤ ∏ k, C k (ς k) := fun U =>
    Finset.prod_le_prod (fun k _ => (hc.re_pos k (ς k) U).le) fun k _ =>
      (Complex.re_le_norm _).trans (hC k (ς k) U)
  have hint : Integrable (fun U => g U * S.period.boltzmannWeight β U) S.period.quotientHaar := by
    refine Integrable.of_bound (hgm.mul hWm).aestronglyMeasurable (∏ k, C k (ς k))
      (Filter.Eventually.of_forall fun U => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hgpos U) (hW U).1)]
    calc g U * S.period.boltzmannWeight β U ≤ g U * 1 :=
          mul_le_mul_of_nonneg_left (hW U).2 (hgpos U).le
      _ ≤ ∏ k, C k (ς k) := by simpa using hgle U
  have e : chessIntegral S β c ς =
      ((∫ U, g U * S.period.boltzmannWeight β U ∂S.period.quotientHaar : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp only [hval, Complex.ofReal_mul]
  have hp : 0 < ∫ U, g U * S.period.boltzmannWeight β U ∂S.period.quotientHaar := by
    refine (integral_pos_iff_support_of_nonneg
      (fun U => (mul_pos (hgpos U) (hW U).1).le) hint).2 ?_
    have hs : Function.support (fun U => g U * S.period.boltzmannWeight β U) = Set.univ :=
      Function.support_eq_univ fun U => (mul_pos (hgpos U) (hW U).1).ne'
    rw [hs, measure_univ]
    exact one_pos
  rw [e]
  exact ⟨Complex.ofReal_im _, by simpa using hp⟩
def upperProduct
    (c : ZMod (2 * S.count) → ZMod (2 * S.count) → S.period.QuotientField → ℂ)
    (s : ZMod (2 * S.count)) (σ : ZMod (2 * S.count) → ZMod (2 * S.count)) :
    S.period.QuotientField → ℂ :=
  ∏ k ∈ aboveMirror s, c k (σ k)
theorem upperProduct_mem (hc : IsCopySystem S c) (s : ZMod (2 * S.count))
    (σ : ZMod (2 * S.count) → ZMod (2 * S.count)) :
    upperProduct c s σ ∈ S.period.plusAlgebra S.normal S.halfPeriod (S.level (s.val : ℤ)) :=
  Subalgebra.prod_mem _ fun k hk =>
    slabAlgebraOfClass_le_plusAlgebra S s k hk (hc.mem k (σ k))
theorem conjReflect_pairedIndex (hc : IsCopySystem S c) (s k j : ZMod (2 * S.count)) :
    S.period.conjReflect (S.levelPair (s.val : ℤ)) (c k j) = c (pairedIndex s k) j := by
  have h := hc.reflect_eq s (k - s) j
  have e₁ : s + (k - s) = k := by ring
  have e₂ : s - 1 - (k - s) = pairedIndex s k := by
    simp only [pairedIndex]
    ring
  rw [e₁, e₂] at h
  exact h
theorem conjReflect_upperProduct (hc : IsCopySystem S c) (s : ZMod (2 * S.count))
    (σ : ZMod (2 * S.count) → ZMod (2 * S.count)) (U : S.period.QuotientField) :
    S.period.conjReflect (S.levelPair (s.val : ℤ)) (upperProduct c s σ) U =
      ∏ k ∈ aboveMirror s, c (pairedIndex s k) (σ k) U := by
  have h : ∀ k, c (pairedIndex s k) (σ k) U =
      conj (c k (σ k) (S.period.pullbackField
        (S.levelPair (s.val : ℤ)).reflectSymmetry U)) := fun k =>
    (congrFun (conjReflect_pairedIndex hc s k (σ k)) U).symm
  simp only [h, PeriodSublattice.conjReflect, PeriodSublattice.compPullback, upperProduct,
    Finset.prod_apply, map_prod]
theorem reflectionPairing_eq_chessIntegral (hc : IsCopySystem S c) {β : ℝ}
    (s : ZMod (2 * S.count))
    (σ' σ ς' : ZMod (2 * S.count) → ZMod (2 * S.count))
    (h : ∀ U, (∏ k ∈ aboveMirror s, c (pairedIndex s k) (σ' k) U) *
      ∏ k ∈ aboveMirror s, c k (σ k) U = ∏ k, c k (ς' k) U) :
    S.period.reflectionPairing β (S.levelPair (s.val : ℤ)) (upperProduct c s σ')
        (upperProduct c s σ) =
      chessIntegral S β c ς' := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  show S.period.conjReflect _ (upperProduct c s σ') U * upperProduct c s σ U * _ = _ * _
  rw [conjReflect_upperProduct hc, upperProduct, Finset.prod_apply, h]
theorem chessIntegral_sq_le (h₃ : SplitTorusReflectionPositivity)
    (hE : S.period.QuotientLiftFacts) {β : ℝ} (hβ : 0 < β) (hc : IsCopySystem S c)
    (ς : ZMod (2 * S.count) → ZMod (2 * S.count)) (s : ZMod (2 * S.count)) :
    (chessIntegral S β c ς).re ^ 2 ≤
      (chessIntegral S β c (foldUp s ς)).re * (chessIntegral S β c (foldDown s ς)).re := by
  obtain ⟨-, -, hsesq, hherm, hnonneg, -, -⟩ := h₃ β hβ S.period S.normal S.normal_mem
    S.halfPeriod S.splits (S.level (s.val : ℤ)) (S.level_allowed _)
  have e₁ := reflectionPairing_eq_chessIntegral (β := β) hc s (fun k => ς (pairedIndex s k)) ς ς
    fun U => by
      rw [prod_eq_prod_aboveMirror_mul s (fun k => c k (ς k) U), mul_comm]
  have e₂ := reflectionPairing_eq_chessIntegral (β := β) hc s ς ς (foldUp s ς) fun U => by
    rw [prod_foldUp s ς (fun k j => c k j U), mul_comm]
  have e₃ := reflectionPairing_eq_chessIntegral (β := β) hc s (fun k => ς (pairedIndex s k))
    (fun k => ς (pairedIndex s k)) (foldDown s ς) fun U => by
    rw [prod_foldDown s ς (fun k j => c k j U), mul_comm]
  have hx := upperProduct_mem hc s ς
  have hy := upperProduct_mem hc s fun k => ς (pairedIndex s k)
  have h := re_sq_le_of_hermitian_form
    (S.period.plusAlgebra S.normal S.halfPeriod (S.level (s.val : ℤ)) :
      Set (S.period.QuotientField → ℂ))
    (S.period.reflectionPairing β (S.levelPair (s.val : ℤ))) hx hy
    (fun w => add_mem (Subalgebra.smul_mem _ hx w) hy) hsesq hherm hnonneg
    (by rw [e₁]; exact (chessIntegral_pos hE hβ hc ς).1)
    (by rw [e₂]; exact (chessIntegral_pos hE hβ hc _).2)
  rwa [e₁, e₂, e₃] at h
end Integrals
theorem slabChessboardEstimate_holds (h₁ : SlabCopyRule)
    (h₂ : PeriodicQuotient.FinitenessClaim)
    (h₃ : SplitTorusReflectionPositivity) : SlabChessboardEstimate := by
  intro S β hβ f hmem hreal
  have hE := h₂.1 S.period
  have hrule := fun j => h₁ S j (f j) (hmem j)
  set c : ZMod (2 * S.count) → ZMod (2 * S.count) → S.period.QuotientField → ℂ :=
    fun k j => S.slabCopy j k (f j) with hcdef
  have hcopies : IsCopySystem S c := by
    refine ⟨fun k j => (hrule j).1 k, fun k j U => ((hrule j).2.2.2.1 (hreal j).1 k).1 U,
      fun k j U => ?_, fun s i j => (hrule j).2.2.2.2 s i⟩
    obtain ⟨C, hC⟩ := (measurable_bdd_of_mem_slabAlgebra S ((hrule j).1 k)).2
    have hb : BddBelow (Set.range fun U => (S.slabCopy j k (f j) U).re) :=
      ⟨-C, by
        rintro _ ⟨U, rfl⟩
        have h := (Complex.abs_re_le_norm (S.slabCopy j k (f j) U)).trans (hC U)
        exact (abs_le.1 h).1⟩
    have h := ciInf_le hb U
    have hinf := ((hrule j).2.2.2.1 (hreal j).1 k).2
    rw [hinf] at h
    exact (hreal j).2.trans_le h
  have hpos := chessIntegral_pos hE hβ hcopies
  have hfold : ∀ j, S.fold β j (f j) = chessIntegral S β c (fun _ => j) := fun j => rfl
  have hfoldpos : ∀ j, 0 < (S.fold β j (f j)).re := fun j => by
    rw [hfold]
    exact (hpos _).2
  have hJ : 1 ≤ S.count := S.one_le_count
  set ϖ : ZMod (2 * S.count) → ℝ :=
    fun j => (S.fold β j (f j)).re ^ (1 / (2 * (S.count : ℝ))) with hϖdef
  have hϖ : ∀ j, 0 < ϖ j := fun j => Real.rpow_pos_of_pos (hfoldpos j) _
  set D : (ZMod (2 * S.count) → ZMod (2 * S.count)) → ℝ := fun ς => ∏ k, ϖ (ς k) with hD
  have hDpos : ∀ ς, 0 < D ς := fun ς => Finset.prod_pos fun k _ => hϖ _
  have hDstep : ∀ ς s, D (foldUp s ς) * D (foldDown s ς) = D ς ^ 2 := by
    intro ς s
    simp only [hD]
    rw [prod_foldUp s ς (fun _ j => ϖ j), prod_foldDown s ς (fun _ j => ϖ j),
      prod_eq_prod_aboveMirror_mul s (fun k => ϖ (ς k))]
    ring
  have hconst : ∀ j, D (fun _ => j) = (chessIntegral S β c fun _ => j).re := by
    intro j
    simp only [hD, Finset.prod_const, Finset.card_univ, ZMod.card]
    rw [← hfold, hϖdef]
    simp only []
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hfoldpos j).le]
    have e : 1 / (2 * (S.count : ℝ)) * ((2 * S.count : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [e, Real.rpow_one]
  obtain ⟨j, hj⟩ := exists_le_const_of_fold_ineq hJ
    (fun ς => (chessIntegral S β c ς).re / D ς)
    (fun ς => div_pos (hpos ς).2 (hDpos ς))
    (fun ς s => by
      rw [div_pow, div_mul_div_comm, hDstep]
      exact div_le_div_of_nonneg_right (chessIntegral_sq_le h₃ hE hβ hcopies ς s)
        (pow_pos (hDpos ς) 2).le)
    id
  have hone : (chessIntegral S β c fun _ => j).re / D (fun _ => j) = 1 := by
    rw [hconst]
    exact div_self (hpos _).2.ne'
  simp only [hone] at hj
  have hle : (chessIntegral S β c id).re ≤ D id := by
    rwa [div_le_one (hDpos id)] at hj
  have hid : S.familyIntegral β f = chessIntegral S β c id := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    show (∏ k, f k U) * _ = (∏ k, c k k U) * _
    congr 1
    exact Finset.prod_congr rfl fun k _ => (congrFun (hrule k).2.1 U).symm
  refine ⟨fun k => ⟨?_, hfoldpos k⟩, ?_, ?_⟩
  · rw [hfold]
    exact (hpos _).1
  · rw [hid]
    exact (hpos _).1
  · rw [hid]
    exact hle
end YangMills.Construction.InfiniteLattice.SlabChessboard
end
