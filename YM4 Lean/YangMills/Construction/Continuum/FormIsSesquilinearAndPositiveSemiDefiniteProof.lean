import YangMills.Construction.Continuum.ArgumentsOfTheConditionsLieInTheirDomainsAndTheirSumsAreFiniteProof
import YangMills.Construction.Continuum.FormIsSesquilinearAndPositiveSemiDefinite
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ConfigSpace.ReflectionFormFacts
theorem linCombAt_cast {a b : ℕ} (h : a = b) (c c' : ℂ) (f g : FnOrScalar a) :
    (h ▸ linCombAt c c' f g : FnOrScalar b) =
      linCombAt c c' (h ▸ f : FnOrScalar b) (h ▸ g : FnOrScalar b) := by
  subst h
  rfl
theorem linCombAt_zero_zero {n : ℕ} (f : FnOrScalar n) :
    linCombAt 0 0 f f = zeroOfDegree n := by
  cases n with
  | zero =>
    exact (fun a : ℂ => by simp : ∀ a : ℂ, (0 : ℂ) * a + 0 * a = 0) f
  | succ n =>
    funext y
    show (0 : ℂ) * f y + 0 * f y = 0
    simp
theorem flipConjAt_linCombAt (c c' : ℂ) {n : ℕ} (f g : FnOrScalar n) :
    flipConjAt (linCombAt c c' f g) =
      linCombAt (conj c) (conj c') (flipConjAt f) (flipConjAt g) := by
  cases n with
  | zero =>
    exact (fun a b : ℂ => by simp :
      ∀ a b : ℂ, conj (c * a + c' * b) = conj c * conj a + conj c' * conj b) f g
  | succ n =>
    funext x
    show conj (c * f _ + c' * g _) = conj c * conj (f _) + conj c' * conj (g _)
    simp
theorem smulAt_linComb_left (c c' a b : ℂ) {n : ℕ} (ψ : FnOrScalar n) :
    smulAt (c * a + c' * b) ψ =
      linCombAt c c' (smulAt a ψ) (smulAt b ψ) := by
  cases n with
  | zero =>
    show (c * a + c' * b) * (show ℂ from ψ) =
      c * (a * (show ℂ from ψ)) + c' * (b * (show ℂ from ψ))
    ring
  | succ n =>
    funext y
    show (c * a + c' * b) * ψ y = c * (a * ψ y) + c' * (b * ψ y)
    ring
theorem smulAt_linComb_right (a c c' : ℂ) {n : ℕ} (f g : FnOrScalar n) :
    smulAt a (linCombAt c c' f g) =
      linCombAt c c' (smulAt a f) (smulAt a g) := by
  cases n with
  | zero =>
    show a * (c * (show ℂ from f) + c' * (show ℂ from g)) =
      c * (a * (show ℂ from f)) + c' * (a * (show ℂ from g))
    ring
  | succ n =>
    funext y
    show a * (c * f y + c' * g y) = c * (a * f y) + c' * (a * g y)
    ring
theorem tensorAt_linComb_left (c c' : ℂ) {q q' : ℕ} (a b : FnOrScalar q)
    (ψ : FnOrScalar q') :
    tensorAt (linCombAt c c' a b) ψ =
      linCombAt c c' (tensorAt a ψ) (tensorAt b ψ) := by
  cases q with
  | zero =>
    show (Nat.zero_add q').symm ▸
        smulAt (c * (show ℂ from a) + c' * (show ℂ from b)) ψ = _
    rw [smulAt_linComb_left, linCombAt_cast]
    rfl
  | succ m =>
    cases q' with
    | zero => exact smulAt_linComb_right _ c c' a b
    | succ k =>
      funext z
      show (c * a _ + c' * b _) * ψ _ = c * (a _ * ψ _) + c' * (b _ * ψ _)
      ring
theorem tensorAt_linComb_right (c c' : ℂ) {q q' : ℕ} (χ : FnOrScalar q)
    (a b : FnOrScalar q') :
    tensorAt χ (linCombAt c c' a b) =
      linCombAt c c' (tensorAt χ a) (tensorAt χ b) := by
  cases q with
  | zero =>
    show (Nat.zero_add q').symm ▸ smulAt (show ℂ from χ) (linCombAt c c' a b) = _
    rw [smulAt_linComb_right, linCombAt_cast]
    rfl
  | succ m =>
    cases q' with
    | zero => exact smulAt_linComb_left c c' a b χ
    | succ k =>
      funext z
      show χ _ * (c * a _ + c' * b _) = c * (χ _ * a _) + c' * (χ _ * b _)
      ring
theorem flat_subspace_facts (h : OpenLociAndFlatSubspaces) {n : ℕ} (hn : 1 ≤ n) :
    schwartzFlatOffPosTime n ⊆ schwartzFlatOffDiagonal n ∧
      schwartzFlatOffNegTime n ⊆ schwartzFlatOffDiagonal n ∧
      ∀ (c c' : ℂ) (φ ψ : Config n → ℂ), φ ∈ schwartzFlatOffDiagonal n →
        ψ ∈ schwartzFlatOffDiagonal n → c • φ + c' • ψ ∈ schwartzFlatOffDiagonal n := by
  obtain ⟨-, -, S, W, Wp, Wm, -, hW, hWp, hWm, -, -, -, hpW, hmW⟩ := h n hn
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun c c' φ ψ hφ hψ => ?_⟩
  · rw [← hWp] at hφ
    rw [← hW]
    exact hpW hφ
  · rw [← hWm] at hφ
    rw [← hW]
    exact hmW hφ
  · rw [← hW] at hφ hψ ⊢
    exact W.add_mem (W.smul_mem c hφ) (W.smul_mem c' hψ)
theorem tensorAt_flipConjAt_mem (hT : TensorAcrossZeroTime)
    (hO : OperationsPreserveSchwartzSpaces) (hS : OpenLociAndFlatSubspaces)
    {q q' : ℕ} {φ : FnOrScalar q} {ψ : FnOrScalar q'}
    (hφ : φ ∈ flatOffPosTimeAt q) (hψ : ψ ∈ flatOffPosTimeAt q') :
    tensorAt (flipConjAt φ) ψ ∈ flatOffDiagonalAt (q + q') := by apply _root_.YangMills.Construction.ConfigSpace.DomainsAndFiniteSums.tensorAt_flipConjAt_mem <;> assumption
section Terms
variable {S : FlatSequence}
theorem evalAt_linCombAt (hS : OpenLociAndFlatSubspaces)
    (hseq : IsCLMSequence S) (c c' : ℂ) {n : ℕ}
    {f g : FnOrScalar n} (hf : f ∈ flatOffDiagonalAt n)
    (hg : g ∈ flatOffDiagonalAt n) :
    S.evalAt (linCombAt c c' f g) = c * S.evalAt f + c' * S.evalAt g := by
  cases n with
  | zero =>
    have e : ∀ x : FnOrScalar 0, S.evalAt x = (show ℂ from x) := fun x => by
      rw [S.evalAt_of_mem (Set.mem_univ x)]
      exact hseq.1 ⟨x, Set.mem_univ x⟩
    rw [e, e, e]
    rfl
  | succ m =>
    have e : linCombAt (n := m + 1) c c' f g =
        c • (show Config (m + 1) → ℂ from f) + c' • (show Config (m + 1) → ℂ from g) := by
      funext y
      rfl
    have hm : linCombAt c c' f g ∈ flatOffDiagonalAt (m + 1) := by
      rw [e]
      exact (flat_subspace_facts hS (Nat.succ_pos m)).2.2 c c' f g hf hg
    rw [S.evalAt_of_mem hm, S.evalAt_of_mem hf, S.evalAt_of_mem hg]
    exact (hseq.2 m).1 c c' ⟨f, hf⟩ ⟨g, hg⟩ ⟨_, hm⟩ e
theorem evalAt_term_linComb_left (hT : TensorAcrossZeroTime)
    (hO : OperationsPreserveSchwartzSpaces) (hS : OpenLociAndFlatSubspaces)
    (hseq : IsCLMSequence S) (c c' : ℂ) {q q' : ℕ}
    {a b : FnOrScalar q} {ψ : FnOrScalar q'}
    (ha : a ∈ flatOffPosTimeAt q) (hb : b ∈ flatOffPosTimeAt q)
    (hψ : ψ ∈ flatOffPosTimeAt q') :
    S.evalAt (tensorAt (flipConjAt (linCombAt c c' a b)) ψ) =
      conj c * S.evalAt (tensorAt (flipConjAt a) ψ) +
        conj c' * S.evalAt (tensorAt (flipConjAt b) ψ) := by
  rw [flipConjAt_linCombAt, tensorAt_linComb_left]
  exact evalAt_linCombAt hS hseq _ _ (tensorAt_flipConjAt_mem hT hO hS ha hψ)
    (tensorAt_flipConjAt_mem hT hO hS hb hψ)
theorem evalAt_term_linComb_right (hT : TensorAcrossZeroTime)
    (hO : OperationsPreserveSchwartzSpaces) (hS : OpenLociAndFlatSubspaces)
    (hseq : IsCLMSequence S) (c c' : ℂ) {q q' : ℕ}
    {φ : FnOrScalar q} {a b : FnOrScalar q'}
    (hφ : φ ∈ flatOffPosTimeAt q) (ha : a ∈ flatOffPosTimeAt q')
    (hb : b ∈ flatOffPosTimeAt q') :
    S.evalAt (tensorAt (flipConjAt φ) (linCombAt c c' a b)) =
      c * S.evalAt (tensorAt (flipConjAt φ) a) +
        c' * S.evalAt (tensorAt (flipConjAt φ) b) := by
  rw [tensorAt_linComb_right]
  exact evalAt_linCombAt hS hseq _ _ (tensorAt_flipConjAt_mem hT hO hS hφ ha)
    (tensorAt_flipConjAt_mem hT hO hS hφ hb)
theorem evalAt_term_eq_zero_left (hT : TensorAcrossZeroTime)
    (hO : OperationsPreserveSchwartzSpaces) (hS : OpenLociAndFlatSubspaces)
    (hseq : IsCLMSequence S) {q q' : ℕ}
    {a : FnOrScalar q} {ψ : FnOrScalar q'}
    (ha : a ∈ flatOffPosTimeAt q) (hψ : ψ ∈ flatOffPosTimeAt q')
    (h0 : a = zeroOfDegree q) :
    S.evalAt (tensorAt (flipConjAt a) ψ) = 0 := by
  have h := evalAt_term_linComb_left hT hO hS hseq 0 0 ha ha hψ
  rw [linCombAt_zero_zero, ← h0] at h
  simpa using h
theorem evalAt_term_eq_zero_right (hT : TensorAcrossZeroTime)
    (hO : OperationsPreserveSchwartzSpaces) (hS : OpenLociAndFlatSubspaces)
    (hseq : IsCLMSequence S) {q q' : ℕ}
    {φ : FnOrScalar q} {a : FnOrScalar q'}
    (hφ : φ ∈ flatOffPosTimeAt q) (ha : a ∈ flatOffPosTimeAt q')
    (h0 : a = zeroOfDegree q') :
    S.evalAt (tensorAt (flipConjAt φ) a) = 0 := by
  have h := evalAt_term_linComb_right hT hO hS hseq 0 0 hφ ha ha
  rw [linCombAt_zero_zero, ← h0] at h
  simpa using h
theorem finite_nonzero_terms (hT : TensorAcrossZeroTime)
    (hO : OperationsPreserveSchwartzSpaces) (hS : OpenLociAndFlatSubspaces)
    (hseq : IsCLMSequence S) (Φ Ψ : AdmissibleSeq) :
    {p : ℕ × ℕ | S.evalAt (formTermArg Φ Ψ p.1 p.2) ≠ 0}.Finite := by
  have hΦ : {q | (Φ.1 q).1 ≠ zeroOfDegree q}.Finite := Φ.2
  have hΨ : {q | (Ψ.1 q).1 ≠ zeroOfDegree q}.Finite := Ψ.2
  refine (hΦ.prod hΨ).subset ?_
  rintro ⟨q, q'⟩ hp
  exact ⟨fun h0 => hp (evalAt_term_eq_zero_left hT hO hS hseq (Φ.1 q).2 (Ψ.1 q').2 h0),
    fun h0 => hp (evalAt_term_eq_zero_right hT hO hS hseq (Φ.1 q).2 (Ψ.1 q').2 h0)⟩
theorem reflectionForm_eq_finsum (Φ Ψ : AdmissibleSeq) :
    S.reflectionForm Φ Ψ =
      ∑ᶠ p : ℕ × ℕ, S.evalAt (formTermArg Φ Ψ p.1 p.2) :=
  rfl
theorem finsum_linComb {ι : Type} {f g h : ι → ℂ} (a b : ℂ) (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (e : ∀ i, h i = a * f i + b * g i) :
    ∑ᶠ i, h i = a * ∑ᶠ i, f i + b * ∑ᶠ i, g i := by
  rw [mul_finsum f a, mul_finsum g b,
    ← finsum_add_distrib (hf.subset fun i hi h0 => hi (by simp [h0]))
      (hg.subset fun i hi h0 => hi (by simp [h0]))]
  exact finsum_congr e
theorem isSesquilinear (hT : TensorAcrossZeroTime)
    (hO : OperationsPreserveSchwartzSpaces) (hS : OpenLociAndFlatSubspaces)
    (hseq : IsCLMSequence S) : S.IsSesquilinear := by
  refine ⟨fun Φ Ψ q q' => tensorAt_flipConjAt_mem hT hO hS (Φ.1 q).2 (Ψ.1 q').2,
    finite_nonzero_terms hT hO hS hseq, ?_, ?_⟩
  · intro c c' Φ Φ' Φ'' Ψ hc
    simp only [reflectionForm_eq_finsum]
    refine finsum_linComb _ _ (finite_nonzero_terms hT hO hS hseq Φ Ψ)
      (finite_nonzero_terms hT hO hS hseq Φ' Ψ) fun p => ?_
    show S.evalAt (tensorAt (flipConjAt (Φ''.1 p.1).1) (Ψ.1 p.2).1) = _
    rw [hc p.1]
    exact evalAt_term_linComb_left hT hO hS hseq c c' (Φ.1 p.1).2 (Φ'.1 p.1).2 (Ψ.1 p.2).2
  · intro c c' Φ Ψ Ψ' Ψ'' hc
    simp only [reflectionForm_eq_finsum]
    refine finsum_linComb _ _ (finite_nonzero_terms hT hO hS hseq Φ Ψ)
      (finite_nonzero_terms hT hO hS hseq Φ Ψ') fun p => ?_
    show S.evalAt (tensorAt (flipConjAt (Φ.1 p.1).1) (Ψ''.1 p.2).1) = _
    rw [hc p.2]
    exact evalAt_term_linComb_right hT hO hS hseq c c' (Φ.1 p.1).2 (Ψ.1 p.2).2 (Ψ'.1 p.2).2
end Terms
section Positive
variable {A : Type} {h : A → A → ℂ} {comb : ℂ → ℂ → A → A → A}
theorem conj_symm_of_nonneg
    (hl : ∀ c c' x x' y, h (comb c c' x x') y = conj c * h x y + conj c' * h x' y)
    (hr : ∀ c c' x y y', h x (comb c c' y y') = c * h x y + c' * h x y')
    (hp : ∀ x, (h x x).im = 0 ∧ 0 ≤ (h x x).re) (x y : A) : h y x = conj (h x y) := by
  have h1 := (hp (comb 1 1 x y)).1
  have h2 := (hp (comb 1 Complex.I x y)).1
  rw [hl, hr, hr] at h1 h2
  have hx := (hp x).1
  have hy := (hp y).1
  simp only [map_one, Complex.conj_I, one_mul, Complex.add_im, Complex.mul_im, Complex.add_re,
    Complex.mul_re, Complex.neg_im, Complex.I_re, Complex.I_im, zero_mul, zero_add, neg_mul] at h1 h2
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith
theorem quadratic_nonneg
    (hl : ∀ c c' x x' y, h (comb c c' x x') y = conj c * h x y + conj c' * h x' y)
    (hr : ∀ c c' x y y', h x (comb c c' y y') = c * h x y + c' * h x y')
    (hp : ∀ x, (h x x).im = 0 ∧ 0 ≤ (h x x).re) (x y : A) (t : ℝ) :
    0 ≤ (h x x).re - 2 * t * Complex.normSq (h x y) +
      t ^ 2 * Complex.normSq (h x y) * (h y y).re := by
  have hyx := conj_symm_of_nonneg hl hr hp x y
  have hw := (hp (comb 1 (-(t : ℂ) * conj (h x y)) x y)).2
  rw [hl, hr, hr, hyx] at hw
  have hN : h x y * conj (h x y) = (Complex.normSq (h x y) : ℂ) := Complex.mul_conj _
  have e : conj (1 : ℂ) * (1 * h x x + -(t : ℂ) * conj (h x y) * h x y) +
        conj (-(t : ℂ) * conj (h x y)) * (1 * conj (h x y) + -(t : ℂ) * conj (h x y) * h y y) =
      h x x - ((2 * t * Complex.normSq (h x y) : ℝ) : ℂ) +
        ((t ^ 2 * Complex.normSq (h x y) : ℝ) : ℂ) * h y y := by
    simp only [map_one, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj]
    push_cast
    rw [← hN]
    ring
  rw [e] at hw
  simpa only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul] using hw
theorem norm_sq_le_mul_of_nonneg
    (hl : ∀ c c' x x' y, h (comb c c' x x') y = conj c * h x y + conj c' * h x' y)
    (hr : ∀ c c' x y y', h x (comb c c' y y') = c * h x y + c' * h x y')
    (hp : ∀ x, (h x x).im = 0 ∧ 0 ≤ (h x x).re) (x y : A) :
    ‖h x y‖ ^ 2 ≤ (h x x).re * (h y y).re := by
  have key := quadratic_nonneg hl hr hp x y
  rw [← Complex.normSq_eq_norm_sq]
  rcases (hp y).2.eq_or_lt with hb | hb
  · rw [← hb, mul_zero]
    by_contra hlt
    have hpos : 0 < Complex.normSq (h x y) := not_le.1 hlt
    have := key (((h x x).re + 1) / (2 * Complex.normSq (h x y)))
    rw [← hb] at this
    have e : 2 * (((h x x).re + 1) / (2 * Complex.normSq (h x y))) * Complex.normSq (h x y) =
        (h x x).re + 1 := by
      field_simp
    rw [e] at this
    linarith
  · have := key (1 / (h y y).re)
    have e : (1 / (h y y).re) ^ 2 * Complex.normSq (h x y) * (h y y).re =
        Complex.normSq (h x y) / (h y y).re := by
      field_simp
    have e' : 2 * (1 / (h y y).re) * Complex.normSq (h x y) =
        2 * (Complex.normSq (h x y) / (h y y).re) := by
      field_simp
    rw [e, e'] at this
    have h3 : Complex.normSq (h x y) / (h y y).re ≤ (h x x).re := by linarith
    exact (div_le_iff₀ hb).1 h3
end Positive
theorem isPosSemidef {S : FlatSequence}
    (hL : LinCombClosure) (hs : S.IsSesquilinear)
    (hE : IsOSPositive S) : S.IsPosSemidef := by
  have hex : ∀ (c c' : ℂ) (x y : AdmissibleSeq), ∃ z : AdmissibleSeq,
      IsLinComb c c' x.1 y.1 z.1 := fun c c' x y => by
    obtain ⟨z, hz, hc⟩ := hL.2 c c' x.1 y.1 x.2 y.2
    exact ⟨⟨z, hz⟩, hc⟩
  choose comb hcomb using hex
  obtain ⟨-, -, hsl, hsr⟩ := hs
  have hl : ∀ c c' x x' y, S.reflectionForm (comb c c' x x') y =
      conj c * S.reflectionForm x y + conj c' * S.reflectionForm x' y :=
    fun c c' x x' y => hsl c c' x x' _ y (hcomb c c' x x')
  have hr : ∀ c c' x y y', S.reflectionForm x (comb c c' y y') =
      c * S.reflectionForm x y + c' * S.reflectionForm x y' :=
    fun c c' x y y' => hsr c c' x y y' _ (hcomb c c' y y')
  have hp : ∀ x : AdmissibleSeq, (S.reflectionForm x x).im = 0 ∧
      0 ≤ (S.reflectionForm x x).re := fun x => hE x.1 x.2
  have hcs := norm_sq_le_mul_of_nonneg hl hr hp
  have hnull : ∀ Φ : AdmissibleSeq, S.reflectionForm Φ Φ = 0 →
      ∀ Ψ, S.reflectionForm Φ Ψ = 0 := by
    intro Φ h0 Ψ
    have h1 := hcs Φ Ψ
    rw [h0, Complex.zero_re, zero_mul] at h1
    have h2 : ‖S.reflectionForm Φ Ψ‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  refine ⟨hp, fun Φ Ψ => conj_symm_of_nonneg hl hr hp Φ Ψ, hcs, ⟨?_, ?_⟩, ?_⟩
  · intro Φ hz
    have hc : IsLinComb 0 0 Φ.1 Φ.1 Φ.1 := fun q =>
      (hz q).trans (linCombAt_zero_zero _).symm
    have h1 := hsl 0 0 Φ Φ Φ Φ hc
    show S.reflectionForm Φ Φ = 0
    simpa using h1
  · intro c c' Φ Φ' Φ'' hΦ hΦ' hc
    show S.reflectionForm Φ'' Φ'' = 0
    rw [hsl c c' Φ Φ' Φ'' Φ'' hc, hnull Φ hΦ, hnull Φ' hΦ']
    simp
  · exact Set.ext fun Φ => ⟨fun h0 => hnull Φ h0, fun h0 => h0 Φ⟩
theorem sesquilinearPosSemidef (hT : TensorAcrossZeroTime)
    (hO : OperationsPreserveSchwartzSpaces) (hS : OpenLociAndFlatSubspaces)
    (hL : LinCombClosure) :
    SesquilinearPosSemidefStatement := fun _ hseq =>
  ⟨isSesquilinear hT hO hS hseq,
    isPosSemidef hL (isSesquilinear hT hO hS hseq)⟩
end YangMills.Construction.ConfigSpace.ReflectionFormFacts
end
