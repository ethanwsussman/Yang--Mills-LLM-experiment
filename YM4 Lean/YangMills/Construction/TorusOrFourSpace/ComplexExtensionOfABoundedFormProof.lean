import YangMills.Construction.TorusOrFourSpace.ComplexExtensionOfABoundedForm
import YangMills.Construction.TorusOrFourSpace.SmallFactsOnLiftsProductsAndDistributions
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.ComplexExtension
open Kind Kind.Tuple
section Coefficients
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def choiceCoeff (s : ι → Bool) : ℂ := ∏ i, cond (s i) Complex.I 1
def flipAt (l : ι) (s : ι → Bool) : ι → Bool := Function.update s l (!s l)
omit [Fintype ι] in
theorem flipAt_self (l : ι) (s : ι → Bool) : flipAt l s l = !s l := by
  simp [flipAt]
omit [Fintype ι] in
theorem flipAt_of_ne {l i : ι} (s : ι → Bool) (hne : i ≠ l) : flipAt l s i = s i := by
  simp [flipAt, Function.update_of_ne hne]
omit [Fintype ι] in
theorem flipAt_involutive (l : ι) : Function.Involutive (flipAt l) := by
  intro s
  funext i
  by_cases hne : i = l
  · subst hne
    simp [flipAt_self]
  · simp [flipAt_of_ne _ hne]
theorem choiceCoeff_flipAt (l : ι) (s : ι → Bool) :
    choiceCoeff (flipAt l s) * cond (s l) Complex.I 1 = cond (!s l) Complex.I 1 * choiceCoeff s := by
  have hrest : ∏ i ∈ Finset.univ.erase l, cond (flipAt l s i) Complex.I 1 =
      ∏ i ∈ Finset.univ.erase l, cond (s i) Complex.I 1 :=
    Finset.prod_congr rfl fun i hi => by rw [flipAt_of_ne s (Finset.ne_of_mem_erase hi)]
  unfold choiceCoeff
  rw [← Finset.mul_prod_erase Finset.univ (fun i => cond (flipAt l s i) Complex.I 1)
      (Finset.mem_univ l),
    ← Finset.mul_prod_erase Finset.univ (fun i => cond (s i) Complex.I 1) (Finset.mem_univ l),
    hrest, flipAt_self]
  ring
omit [DecidableEq ι] in
theorem norm_choiceCoeff (s : ι → Bool) : ‖choiceCoeff s‖ = 1 := by
  unfold choiceCoeff
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  cases s i <;> simp
theorem sum_choiceCoeff_of_flipAt (l : ι) (T T' : (ι → Bool) → ℝ) (a : ℂ)
    (hT : ∀ s, T' s = a.re * T s + cond (s l) a.im (-a.im) * T (flipAt l s)) :
    ∑ s, choiceCoeff s * (T' s : ℂ) = a * ∑ s, choiceCoeff s * (T s : ℂ) := by
  have hterm : ∀ s, choiceCoeff s * (T' s : ℂ) = (a.re : ℂ) * (choiceCoeff s * (T s : ℂ)) +
      (a.im : ℂ) * Complex.I * (choiceCoeff (flipAt l s) * (T (flipAt l s) : ℂ)) := by
    intro s
    have hc := choiceCoeff_flipAt l s
    rw [hT s]
    cases hs : s l with
    | false =>
      simp only [hs, Bool.not_false, cond_true, cond_false, mul_one] at hc ⊢
      rw [hc]
      push_cast
      linear_combination (-(a.im : ℂ) * choiceCoeff s * (T (flipAt l s) : ℂ)) * Complex.I_mul_I
    | true =>
      simp only [hs, Bool.not_true, cond_true, cond_false, one_mul] at hc ⊢
      rw [← hc]
      push_cast
      ring
  have hsum : ∑ s, choiceCoeff (flipAt l s) * (T (flipAt l s) : ℂ) =
      ∑ s, choiceCoeff s * (T s : ℂ) :=
    Equiv.sum_comp (flipAt_involutive l).toPerm fun s => choiceCoeff s * (T s : ℂ)
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  linear_combination (∑ s, choiceCoeff s * (T s : ℂ)) * Complex.re_add_im a
end Coefficients
section Parts
variable (D : Params) (E : Kind)
def reImPart (b : Bool) (x : E.Pt D → ℂ) : E.Pt D → ℝ :=
  cond b (fun y => (x y).im) (fun y => (x y).re)
theorem reImPart_add (b : Bool) (u v : E.Pt D → ℂ) :
    reImPart D E b (u + v) = (1 : ℝ) • reImPart D E b u + (1 : ℝ) • reImPart D E b v := by
  funext y
  cases b <;> simp [reImPart]
theorem reImPart_smul (a : ℂ) (b : Bool) (u : E.Pt D → ℂ) :
    reImPart D E b (a • u) = a.re • reImPart D E b u + cond b a.im (-a.im) • reImPart D E (!b) u := by
  funext y
  cases b <;> simp [reImPart, Complex.mul_re, Complex.mul_im]
  ring
variable {D E}
theorem reImPart_mem {O : Set (E.Pt D)} (hf : ComplexSupportedFacts D E O) (b : Bool)
    {x : E.Pt D → ℂ} (hx : x ∈ complexC1SupportedIn D E O) :
    reImPart D E b x ∈ c1SupportedIn D E O := by
  cases b
  · exact (hf.2.2.2.2.2.2.1 x hx).1
  · exact (hf.2.2.2.2.2.2.1 x hx).2
theorem add_mem_complex {O : Set (E.Pt D)} (hf : ComplexSupportedFacts D E O)
    {u v : E.Pt D → ℂ} (hu : u ∈ complexC1SupportedIn D E O) (hv : v ∈ complexC1SupportedIn D E O) :
    u + v ∈ complexC1SupportedIn D E O := by
  obtain ⟨S, hS⟩ := hf.1
  rw [← hS] at hu hv ⊢
  exact S.add_mem hu hv
theorem smul_mem_complex {O : Set (E.Pt D)} (hf : ComplexSupportedFacts D E O) (a : ℂ)
    {u : E.Pt D → ℂ} (hu : u ∈ complexC1SupportedIn D E O) : a • u ∈ complexC1SupportedIn D E O := by
  obtain ⟨S, hS⟩ := hf.1
  rw [← hS] at hu ⊢
  exact S.smul_mem a hu
end Parts
section Extension
variable {D : Params} {E : Kind} {n : ℕ+} {O : Fin (n : ℕ) → Set (E.Pt D)}
def partsTuple (hf : ∀ i, ComplexSupportedFacts D E (O i)) (h : Fin (n : ℕ) → E.Pt D → ℂ)
    (hh : ∀ i, h i ∈ complexC1SupportedIn D E (O i)) (s : Fin (n : ℕ) → Bool) :
    ∀ i, c1SupportedIn D E (O i) :=
  fun i => ⟨reImPart D E (s i) (h i), reImPart_mem (hf i) (s i) (hh i)⟩
theorem update_mem_complex {h : Fin (n : ℕ) → E.Pt D → ℂ}
    (hh : ∀ i, h i ∈ complexC1SupportedIn D E (O i))
    (l : Fin (n : ℕ)) {w : E.Pt D → ℂ} (hw : w ∈ complexC1SupportedIn D E (O l)) :
    ∀ i, Function.update h l w i ∈ complexC1SupportedIn D E (O i) := by
  intro i
  by_cases hne : i = l
  · subst hne
    simpa using hw
  · simpa [Function.update_of_ne hne] using hh i
theorem partsTuple_update (hf : ∀ i, ComplexSupportedFacts D E (O i))
    {h : Fin (n : ℕ) → E.Pt D → ℂ} (hh : ∀ i, h i ∈ complexC1SupportedIn D E (O i))
    (l : Fin (n : ℕ)) {w : E.Pt D → ℂ} (hw : w ∈ complexC1SupportedIn D E (O l))
    (hh' : ∀ i, Function.update h l w i ∈ complexC1SupportedIn D E (O i))
    (s s' : Fin (n : ℕ) → Bool) (hs : ∀ i, i ≠ l → s' i = s i) :
    partsTuple hf (Function.update h l w) hh' s' =
      Function.update (partsTuple hf h hh s) l ⟨reImPart D E (s' l) w, reImPart_mem (hf l) _ hw⟩ := by
  funext i
  by_cases hne : i = l
  · subst hne
    rw [Function.update_self]
    apply Subtype.ext
    simp [partsTuple]
  · rw [Function.update_of_ne hne]
    apply Subtype.ext
    simp [partsTuple, Function.update_of_ne hne, hs i hne]
open Classical in
def complexExt (hf : ∀ i, ComplexSupportedFacts D E (O i)) (B : (∀ i, c1SupportedIn D E (O i)) → ℝ)
    (h : Fin (n : ℕ) → E.Pt D → ℂ) : ℂ :=
  if hh : ∀ i, h i ∈ complexC1SupportedIn D E (O i) then
    ∑ s : Fin (n : ℕ) → Bool, choiceCoeff s * (B (partsTuple hf h hh s) : ℂ)
  else 0
theorem complexExt_of_mem (hf : ∀ i, ComplexSupportedFacts D E (O i))
    (B : (∀ i, c1SupportedIn D E (O i)) → ℝ) {h : Fin (n : ℕ) → E.Pt D → ℂ}
    (hh : ∀ i, h i ∈ complexC1SupportedIn D E (O i)) :
    complexExt hf B h = ∑ s : Fin (n : ℕ) → Bool, choiceCoeff s * (B (partsTuple hf h hh s) : ℂ) :=
  dif_pos hh
def IsLinearInEach (B : (∀ i, c1SupportedIn D E (O i)) → ℝ) : Prop :=
  ∀ (g : ∀ i, c1SupportedIn D E (O i)) (i : Fin (n : ℕ)) (u v w : c1SupportedIn D E (O i))
    (a b : ℝ), w.1 = a • u.1 + b • v.1 →
      B (Function.update g i w) = a * B (Function.update g i u) + b * B (Function.update g i v)
theorem complexExt_add (hf : ∀ i, ComplexSupportedFacts D E (O i))
    {B : (∀ i, c1SupportedIn D E (O i)) → ℝ} (hB : IsLinearInEach B)
    {h : Fin (n : ℕ) → E.Pt D → ℂ} (hh : ∀ i, h i ∈ complexC1SupportedIn D E (O i))
    (l : Fin (n : ℕ)) {u v : E.Pt D → ℂ} (hu : u ∈ complexC1SupportedIn D E (O l))
    (hv : v ∈ complexC1SupportedIn D E (O l)) :
    complexExt hf B (Function.update h l (u + v)) =
      complexExt hf B (Function.update h l u) + complexExt hf B (Function.update h l v) := by
  have huv := add_mem_complex (hf l) hu hv
  have h1 := update_mem_complex hh l huv
  have h2 := update_mem_complex hh l hu
  have h3 := update_mem_complex hh l hv
  rw [complexExt_of_mem hf B h1, complexExt_of_mem hf B h2, complexExt_of_mem hf B h3,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e := hB (partsTuple hf h hh s) l ⟨reImPart D E (s l) u, reImPart_mem (hf l) _ hu⟩
    ⟨reImPart D E (s l) v, reImPart_mem (hf l) _ hv⟩
    ⟨reImPart D E (s l) (u + v), reImPart_mem (hf l) _ huv⟩
    1 1 (reImPart_add D E (s l) u v)
  rw [partsTuple_update hf hh l huv h1 s s fun _ _ => rfl,
    partsTuple_update hf hh l hu h2 s s fun _ _ => rfl,
    partsTuple_update hf hh l hv h3 s s fun _ _ => rfl, e]
  push_cast
  ring
theorem complexExt_smul (hf : ∀ i, ComplexSupportedFacts D E (O i))
    {B : (∀ i, c1SupportedIn D E (O i)) → ℝ} (hB : IsLinearInEach B)
    {h : Fin (n : ℕ) → E.Pt D → ℂ} (hh : ∀ i, h i ∈ complexC1SupportedIn D E (O i))
    (l : Fin (n : ℕ)) {u : E.Pt D → ℂ} (hu : u ∈ complexC1SupportedIn D E (O l)) (a : ℂ) :
    complexExt hf B (Function.update h l (a • u)) = a * complexExt hf B (Function.update h l u) := by
  have hau := smul_mem_complex (hf l) a hu
  have h1 := update_mem_complex hh l hau
  have h2 := update_mem_complex hh l hu
  rw [complexExt_of_mem hf B h1, complexExt_of_mem hf B h2]
  refine sum_choiceCoeff_of_flipAt l (fun s => B (partsTuple hf _ h2 s))
    (fun s => B (partsTuple hf _ h1 s)) a ?_
  intro s
  have e := hB (partsTuple hf h hh s) l ⟨reImPart D E (s l) u, reImPart_mem (hf l) _ hu⟩
    ⟨reImPart D E (flipAt l s l) u, reImPart_mem (hf l) _ hu⟩
    ⟨reImPart D E (s l) (a • u), reImPart_mem (hf l) _ hau⟩ a.re (cond (s l) a.im (-a.im))
    (by
      show reImPart D E (s l) (a • u) = a.re • reImPart D E (s l) u +
        cond (s l) a.im (-a.im) • reImPart D E (flipAt l s l) u
      rw [flipAt_self]
      exact reImPart_smul D E a (s l) u)
  show B (partsTuple hf _ h1 s) = a.re * B (partsTuple hf _ h2 s) +
    cond (s l) a.im (-a.im) * B (partsTuple hf _ h2 (flipAt l s))
  rw [partsTuple_update hf hh l hau h1 s s fun _ _ => rfl,
    partsTuple_update hf hh l hu h2 s s fun _ _ => rfl,
    partsTuple_update hf hh l hu h2 s (flipAt l s) fun i hi => flipAt_of_ne s hi, e]
theorem complexExt_bound (hsmall : ∀ (g : E.Pt D → ℂ),
      Tuple.IsClassC D E 1 (ofSingle D E g) → c1NormSingle D E g < ⊤ →
        c1NormSingleReal D E (fun y => (g y).re) ≤ c1NormSingle D E g ∧
          c1NormSingleReal D E (fun y => (g y).im) ≤ c1NormSingle D E g)
    (hf : ∀ i, ComplexSupportedFacts D E (O i)) {B : (∀ i, c1SupportedIn D E (O i)) → ℝ} {c : ℝ}
    (hbound : ∀ g : ∀ i, c1SupportedIn D E (O i), ENNReal.ofReal |B g| ≤
      ENNReal.ofReal c * ∏ i, c1NormSingleReal D E (g i).1)
    {h : Fin (n : ℕ) → E.Pt D → ℂ} (hh : ∀ i, h i ∈ complexC1SupportedIn D E (O i)) :
    ENNReal.ofReal ‖complexExt hf B h‖ ≤
      ENNReal.ofReal (2 ^ (n : ℕ) * c) * ∏ i, c1NormSingle D E (h i) := by
  have hpart : ∀ (i : Fin (n : ℕ)) (b : Bool),
      c1NormSingleReal D E (reImPart D E b (h i)) ≤ c1NormSingle D E (h i) := by
    intro i b
    have hs := hsmall (h i) (hh i).1 ((hf i).2.2.2.2.2.2.2 (h i) (hh i))
    cases b
    · exact hs.1
    · exact hs.2
  have hterm : ∀ s : Fin (n : ℕ) → Bool, ENNReal.ofReal |B (partsTuple hf h hh s)| ≤
      ENNReal.ofReal c * ∏ i, c1NormSingle D E (h i) := by
    intro s
    refine (hbound _).trans ?_
    gcongr with i _
    exact hpart i (s i)
  rw [complexExt_of_mem hf B hh]
  calc ENNReal.ofReal ‖∑ s : Fin (n : ℕ) → Bool, choiceCoeff s * (B (partsTuple hf h hh s) : ℂ)‖
      ≤ ENNReal.ofReal (∑ s : Fin (n : ℕ) → Bool, |B (partsTuple hf h hh s)|) := by
        refine ENNReal.ofReal_le_ofReal ((norm_sum_le _ _).trans (le_of_eq ?_))
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [norm_mul, norm_choiceCoeff, one_mul, Complex.norm_real, Real.norm_eq_abs]
    _ = ∑ s : Fin (n : ℕ) → Bool, ENNReal.ofReal |B (partsTuple hf h hh s)| :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _
    _ ≤ ∑ _s : Fin (n : ℕ) → Bool, ENNReal.ofReal c * ∏ i, c1NormSingle D E (h i) :=
        Finset.sum_le_sum fun s _ => hterm s
    _ = ENNReal.ofReal (2 ^ (n : ℕ) * c) * ∏ i, c1NormSingle D E (h i) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity), ← mul_assoc]
        simp [Finset.card_univ, ENNReal.ofReal_pow]
theorem complexExt_of_real (hf : ∀ i, ComplexSupportedFacts D E (O i))
    {B : (∀ i, c1SupportedIn D E (O i)) → ℝ} (hB : IsLinearInEach B)
    (g : ∀ i, c1SupportedIn D E (O i)) :
    complexExt hf B (fun i y => ((g i).1 y : ℂ)) = (B g : ℂ) := by
  have hh : ∀ i, (fun y => ((g i).1 y : ℂ)) ∈ complexC1SupportedIn D E (O i) :=
    fun i => (hf i).2.2.2.2.2.1 (g i).1 (g i).2
  rw [complexExt_of_mem hf B hh, Finset.sum_eq_single fun _ => false]
  · have hg : partsTuple hf (fun i y => ((g i).1 y : ℂ)) hh (fun _ => false) = g := by
      funext i
      apply Subtype.ext
      funext y
      simp [partsTuple, reImPart]
    rw [hg]
    simp [choiceCoeff]
  · intro s _ hs
    obtain ⟨i, hi⟩ : ∃ i, s i = true := by
      by_contra hne
      exact hs (funext fun i => by simpa using fun hi => hne ⟨i, hi⟩)
    have hzero : (partsTuple hf (fun i y => ((g i).1 y : ℂ)) hh s i).1 =
        (0 : ℝ) • (partsTuple hf (fun i y => ((g i).1 y : ℂ)) hh s i).1 +
          (0 : ℝ) • (partsTuple hf (fun i y => ((g i).1 y : ℂ)) hh s i).1 := by
      funext y
      simp [partsTuple, reImPart, hi]
    have e := hB (partsTuple hf (fun i y => ((g i).1 y : ℂ)) hh s) i _ _ _ 0 0 hzero
    simp only [Function.update_eq_self, zero_mul, add_zero] at e
    rw [e]
    simp
  · intro hs
    exact absurd (Finset.mem_univ _) hs
end Extension
theorem complexExtensionClaim_holds (hsmall : LiftsProductsDistributions.Statement)
    (hclass : ComplexSupportedClassesClaim) : ComplexExtensionClaim := by
  intro D E n c _ O hO B hB hbound
  have hf : ∀ i, ComplexSupportedFacts D E (O i) := fun i => hclass D E (O i) (hO i)
  have hlin : IsLinearInEach B := hB
  refine ⟨complexExt hf B, ⟨?_, ?_, ?_⟩, complexExt_of_real hf hlin⟩
  · intro h l u v hh hu hv
    exact complexExt_add hf hlin hh l hu hv
  · intro h l u a hh hu
    exact complexExt_smul hf hlin hh l hu a
  · intro h hh
    exact complexExt_bound (hsmall D E).2.2.2.1 hf hbound hh
end YangMills.Construction.PeriodicSpace.ComplexExtension
