import YangMills.Construction.InfiniteLattice.ContinuousLocalFunctionsAreDenseAndTestMeasuresProof
import YangMills.Construction.TransferOperators.ClassesOfSymmetricStacksAreGaugeInvariantPolynomials
import YangMills.Construction.TransferOperators.TemporalGaugeOfAStack
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set InfiniteLattice SpinHarmonics Matrices
namespace TransferOperators.CenteredStackClasses
theorem isEntryPolynomial_comp_optionElim {K J : Type*} (e : J → Option K)
    {F : (J → ComplexMatrix2.specialUnitary) → ℂ} (hF : IsEntryPolynomial F) :
    IsEntryPolynomial fun u : K → ComplexMatrix2.specialUnitary => F fun x => (e x).elim 1 u := by
  obtain ⟨p, hp⟩ := hF
  have key : ∀ x : EntryVar J, ∃ q : MvPolynomial (EntryVar K) ℂ,
      ∀ u : K → ComplexMatrix2.specialUnitary,
      entryEval (fun x => (e x).elim 1 u) x = MvPolynomial.eval (entryEval u) q := by
    rintro (⟨b, r, s⟩ | ⟨b, r, s⟩)
    · cases h : e b with
      | none =>
        exact ⟨MvPolynomial.C (((1 : ComplexMatrix2.specialUnitary) : ComplexMatrix2) r s),
          fun u => by simp [entryEval, h]⟩
      | some k =>
        exact ⟨MvPolynomial.X (.inl (k, r, s)), fun u => by simp [entryEval, h]⟩
    · cases h : e b with
      | none =>
        exact ⟨MvPolynomial.C (star (((1 : ComplexMatrix2.specialUnitary) : ComplexMatrix2) r s)),
          fun u => by simp [entryEval, h]⟩
      | some k =>
        exact ⟨MvPolynomial.X (.inr (k, r, s)), fun u => by simp [entryEval, h]⟩
  choose f hf using key
  refine ⟨MvPolynomial.bind₁ f p, fun u => ?_⟩
  change F _ = _
  rw [hp]
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p x hp => simp [hp, hf]
theorem gaugeFieldOfPositive_apply (g : positiveLinks (1 : ℝ) → ComplexMatrix2.specialUnitary)
    (c : positiveLinks (1 : ℝ)) : (gaugeFieldOfPositive one_pos g) c.1 = g c :=
  dif_pos c.2
theorem continuous_linkEval (b : Link 1) : Continuous fun U : GaugeField 1 => U b := by apply _root_.YangMills.Construction.InfiniteLattice.ContinuousLocalDensity.continuous_eval_link <;> assumption
open Classical in
def extendByOne (S : Set (positiveLinks (1 : ℝ))) (g : S → ComplexMatrix2.specialUnitary) :
    positiveLinks (1 : ℝ) → ComplexMatrix2.specialUnitary :=
  fun c => ((if h : c ∈ S then some ⟨c, h⟩ else none : Option S)).elim 1 g
theorem extendByOne_of_mem (S : Set (positiveLinks (1 : ℝ)))
    (g : S → ComplexMatrix2.specialUnitary)
    (c : positiveLinks (1 : ℝ)) (h : c ∈ S) : extendByOne S g c = g ⟨c, h⟩ := by
  simp [extendByOne, h]
theorem exists_entryPolynomial_of_dependsOnlyOn (S : Set (positiveLinks (1 : ℝ)))
    {F : GaugeField 1 → ℂ}
    (hD : DependsOnlyOn (Subtype.val '' S) F) (hp : IsPolynomialInLinkEntries F) :
    ∃ P : (S → ComplexMatrix2.specialUnitary) → ℂ, IsEntryPolynomial P ∧
      ∀ U : GaugeField 1, F U = P fun c => U c.1.1 := by
  classical
  refine ⟨fun g => F (gaugeFieldOfPositive one_pos (extendByOne S g)), ?_, fun U => hD _ _ ?_⟩
  · exact isEntryPolynomial_comp_optionElim
      (fun c : positiveLinks (1 : ℝ) => if h : c ∈ S then some (⟨c, h⟩ : S) else none) hp
  · rintro _ ⟨c, hc, rfl⟩
    rw [gaugeFieldOfPositive_apply, extendByOne_of_mem S _ c hc]
theorem isPolynomialInLinkEntries_of_factor (S : Set (positiveLinks (1 : ℝ)))
    {F : GaugeField 1 → ℂ} {P : (S → ComplexMatrix2.specialUnitary) → ℂ}
    (hP : IsEntryPolynomial P)
    (hF : ∀ U : GaugeField 1, F U = P fun c => U c.1.1) : IsPolynomialInLinkEntries F := by
  have h := isEntryPolynomial_comp_optionElim (K := positiveLinks (1 : ℝ))
    (fun c : S => some c.1) hP
  have he : (fun g : positiveLinks (1 : ℝ) → ComplexMatrix2.specialUnitary =>
      F (gaugeFieldOfPositive one_pos g)) =
      fun g => P fun c => (some c.1 : Option (positiveLinks (1 : ℝ))).elim 1 g := by
    funext g
    rw [hF]
    exact congrArg P (funext fun c => gaugeFieldOfPositive_apply g c.1)
  unfold IsPolynomialInLinkEntries
  rw [he]
  exact h
theorem isBoundedObservable_of_factor (S : Set (positiveLinks (1 : ℝ))) {F : GaugeField 1 → ℂ}
    {P : (S → ComplexMatrix2.specialUnitary) → ℂ} (hP : IsEntryPolynomial P)
    (hF : ∀ U : GaugeField 1, F U = P fun c => U c.1.1) : IsBoundedObservable F := by
  have hc : Continuous P := hP.continuous
  have hr : Continuous fun U : GaugeField 1 => fun c : S => U c.1.1 :=
    continuous_pi fun c => continuous_linkEval c.1.1
  have hFc : Continuous F := by
    rw [show F = fun U => P fun c => U c.1.1 from funext hF]
    exact hc.comp hr
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨hFc.measurable, C, fun U => by
    rw [hF]
    exact hC _ (mem_univ _)⟩
theorem dependsOnlyOn_of_factor (S : Set (positiveLinks (1 : ℝ))) {F : GaugeField 1 → ℂ}
    {P : (S → ComplexMatrix2.specialUnitary) → ℂ}
    (hF : ∀ U : GaugeField 1, F U = P fun c => U c.1.1) :
    DependsOnlyOn (Subtype.val '' S) F := by
  intro U U' h
  rw [hF, hF]
  exact congrArg P (funext fun c => h _ ⟨c.1, c.2, rfl⟩)
theorem centeredStackClassStatement_holds (hT : TemporalGauge.MainStatement) :
    CenteredStackClassStatement := by
  intro μ n k hk F
  constructor
  · rintro ⟨v, hv, Ψ, hne, hΨ, hinv, hX⟩
    have := hv
    have hc : Continuous Ψ := hΨ.1.continuous
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    obtain ⟨-, hG, hD, -, hp⟩ := ((hT μ (centeredStack n k hk)).1 v hne).2 Ψ hc.measurable
      ⟨C, fun u => hC u (mem_univ _)⟩ hinv
    have hF : F = fun U => Ψ ((centeredStack n k hk).transportedIndexed v U) := funext hX
    rw [← hF] at hG hD hp
    refine ⟨hG, fun U => ?_, v, hv, hne, exists_entryPolynomial_of_dependsOnlyOn _ hD (hp hΨ.1)⟩
    rw [hX]
    exact hΨ.2 _
  · rintro ⟨hG, him, v, hv, hne, P, hP, hF⟩
    have := hv
    obtain ⟨-, h₂, -, -, h₅, -, h₇⟩ := ((hT μ (centeredStack n k hk)).1 v hne).1 F
      (isBoundedObservable_of_factor _ hP hF) hG (dependsOnlyOn_of_factor _ hF)
    exact ⟨v, hv, (centeredStack n k hk).temporalGaugeValue v F, hne,
      ⟨h₇ (isPolynomialInLinkEntries_of_factor _ hP hF), fun u => him _⟩, h₅, h₂⟩
end TransferOperators.CenteredStackClasses
end YangMills.Construction
end
