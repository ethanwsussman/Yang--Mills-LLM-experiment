import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.SymbolOfAProductProof
import YangMills.Construction.PeriodicOperators.SymbolsOfCombinationsAndProductsAtAPoint
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SymbolAtPoint
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
variable {P P' P'' : PeriodicData}
theorem expDecay_mono_rate {T : P'.Carrier → P.Carrier → ℂ} {C δ δ' : ℝ} (hC : 0 < C)
    (hδ : δ' ≤ δ) (h : ExpDecay P P' T C δ) : ExpDecay P P' T C δ' := fun x' x => by
  refine (h x' x).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le)
  have hd : 0 ≤ euclidNormVec (P'.pos x' - P.pos x) := Real.sqrt_nonneg _
  nlinarith
theorem exists_common_decayRate {A B A' B' : PeriodicData} {T : A'.Carrier → A.Carrier → ℂ}
    {S : B'.Carrier → B.Carrier → ℂ} (hT : IsPeriodicKernel A A' T)
    (hS : IsPeriodicKernel B B' S) :
    ∃ δ : ℝ, IsDecayRate A A' T δ ∧ IsDecayRate B B' S δ := by
  obtain ⟨-, C, δ, hC, hδ, hb⟩ := hT
  obtain ⟨-, C', δ', hC', hδ', hb'⟩ := hS
  exact ⟨min δ δ', ⟨lt_min hδ hδ', C, hC, expDecay_mono_rate hC (min_le_left _ _) hb⟩,
    ⟨lt_min hδ hδ', C', hC', expDecay_mono_rate hC' (min_le_right _ _) hb'⟩⟩
theorem isPeriodicKernel_linearCombination {T T' : P'.Carrier → P.Carrier → ℂ} (a a' : ℂ)
    (hT : IsPeriodicKernel P P' T) (hT' : IsPeriodicKernel P P' T') :
    IsPeriodicKernel P P' (fun x' x => a * T x' x + a' * T' x' x) := by
  obtain ⟨δ, ⟨hδ, C, hC, hb⟩, ⟨-, C', hC', hb'⟩⟩ := exists_common_decayRate hT hT'
  refine ⟨fun n x' x => ?_, ‖a‖ * C + ‖a'‖ * C' + 1, δ, by positivity, hδ, fun x' x => ?_⟩
  · simp only [hT.1 n x' x, hT'.1 n x' x]
  · set E := Real.exp (-δ * euclidNormVec (P'.pos x' - P.pos x)) with hE
    have hE0 : 0 ≤ E := Real.exp_nonneg _
    have h1 : ‖a * T x' x‖ ≤ ‖a‖ * (C * E) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb x' x) (norm_nonneg _)
    have h2 : ‖a' * T' x' x‖ ≤ ‖a'‖ * (C' * E) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb' x' x) (norm_nonneg _)
    calc ‖a * T x' x + a' * T' x' x‖ ≤ ‖a * T x' x‖ + ‖a' * T' x' x‖ := norm_add_le _ _
      _ ≤ ‖a‖ * (C * E) + ‖a'‖ * (C' * E) := add_le_add h1 h2
      _ ≤ (‖a‖ * C + ‖a'‖ * C' + 1) * E := by nlinarith
theorem symbolSummand_linearCombination (T T' : P'.Carrier → P.Carrier → ℂ) (a a' : ℂ)
    (k : Fin 4 → ℂ) (x' : P'.Carrier) (x : P.Carrier) (n : Fin 4 → ℤ) :
    symbolSummand P P' (fun x' x => a * T x' x + a' * T' x' x) k x' x n =
      a * symbolSummand P P' T k x' x n + a' * symbolSummand P P' T' k x' x n := by
  simp only [symbolSummand]
  ring
theorem symbolSummableAt_linearCombination {T T' : P'.Carrier → P.Carrier → ℂ} (a a' : ℂ)
    {k : Fin 4 → ℂ} (f : SymbolSummableAt P P' T k) (f' : SymbolSummableAt P P' T' k) :
    SymbolSummableAt P P' (fun x' x => a * T x' x + a' * T' x' x) k := fun x' x => by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (((f x' x).mul_left ‖a‖).add ((f' x' x).mul_left ‖a'‖))
  rw [symbolSummand_linearCombination, ← norm_mul, ← norm_mul]
  exact norm_add_le _ _
theorem fourierSymbol_linearCombination {T T' : P'.Carrier → P.Carrier → ℂ} (a a' : ℂ)
    {k : Fin 4 → ℂ} (f : SymbolSummableAt P P' T k) (f' : SymbolSummableAt P P' T' k)
    (x' : P'.Carrier) (x : P.Carrier) :
    fourierSymbol P P' (fun x' x => a * T x' x + a' * T' x' x) k x' x =
      a * fourierSymbol P P' T k x' x + a' * fourierSymbol P P' T' k x' x := by
  simp only [fourierSymbol, symbolSummand_linearCombination]
  rw [((f x' x).of_norm.mul_left a).tsum_add ((f' x' x).of_norm.mul_left a'), tsum_mul_left,
    tsum_mul_left]
theorem linearMapOfEntries_linearCombination {J J' : Type} [Finite J] (M M' : J' → J → ℂ)
    (a a' : ℂ) :
    linearMapOfEntries (fun i j => a * M i j + a' * M' i j) =
      a • linearMapOfEntries M + a' • linearMapOfEntries M' := by
  classical
  have := Fintype.ofFinite J
  refine LinearMap.ext fun f => ?_
  funext i
  simp only [LinearMap.add_apply, LinearMap.smul_apply, linearMapOfEntries_eq_applyKernel,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, applyKernel, tsum_fintype, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
theorem linearMapOfEntries_compKernel {J J' J'' : Type} [Finite J] [Finite J'']
    (M : J' → J → ℂ) (N : J → J'' → ℂ) :
    linearMapOfEntries (compKernel M N) = (linearMapOfEntries M).comp (linearMapOfEntries N) := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapOfEntries_compKernel <;> assumption
theorem exp_bilinDot_sub_split (k : Fin 4 → ℂ) (u v w : AmbientSpace) :
    Complex.exp (Complex.I * bilinDot k (toComplexVec (u - v))) =
      Complex.exp (Complex.I * bilinDot k (toComplexVec (w - v))) *
        Complex.exp (Complex.I * bilinDot k (toComplexVec (u - w))) := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolComp.exp_I_bilinDot_sub_split <;> assumption
def pairSummand (T : P'.Carrier → P.Carrier → ℂ) (S : P.Carrier → P''.Carrier → ℂ)
    (k : Fin 4 → ℂ) (x' : P'.Carrier) (x'' : P''.Carrier) (p : P.Carrier × (Fin 4 → ℤ)) : ℂ :=
  T x' p.1 * S p.1 (P''.translate p.2 x'') *
    Complex.exp (Complex.I * bilinDot k
      (toComplexVec (P''.pos (P''.translate p.2 x'') - P'.pos x')))
theorem pairSummand_translate (hP : IsPeriodic P) (hP'' : IsPeriodic P'')
    (T : P'.Carrier → P.Carrier → ℂ) {S : P.Carrier → P''.Carrier → ℂ}
    (hS : IsShiftInvariant P'' P S) (k : Fin 4 → ℂ) (x' : P'.Carrier) (x'' : P''.Carrier)
    (x₀ : P.Carrier) (m n : Fin 4 → ℤ) :
    pairSummand T S k x' x'' (P.translate m x₀, n) =
      symbolSummand P P' T k x' x₀ m * symbolSummand P'' P S k x₀ x'' (n - m) := by
  have htr : P''.translate n x'' = P''.translate m (P''.translate (n - m) x'') := by
    rw [← hP''.translate_add, sub_add_cancel]
  have hS' : S (P.translate m x₀) (P''.translate n x'') = S x₀ (P''.translate (n - m) x'') := by
    rw [htr]
    exact hS m x₀ _
  have hpos : P''.pos (P''.translate n x'') - P.pos (P.translate m x₀) =
      P''.pos (P''.translate (n - m) x'') - P.pos x₀ := by
    simp only [hP''.pos_translate, hP.pos_translate]
    funext μ
    simp only [Pi.sub_apply, Pi.add_apply, castVec]
    push_cast
    ring
  unfold pairSummand symbolSummand
  simp only
  rw [hS', exp_bilinDot_sub_split k _ (P'.pos x') (P.pos (P.translate m x₀)), hpos]
  ring
theorem summable_mul_sub {C G : Type} [Finite C] [AddGroup G] {a b : C → G → ℝ}
    (ha : ∀ c, Summable (a c)) (hb : ∀ c, Summable (b c)) (ha0 : ∀ c m, 0 ≤ a c m)
    (hb0 : ∀ c j, 0 ≤ b c j) :
    Summable fun q : (C × G) × G => a q.1.1 q.1.2 * b q.1.1 (q.2 - q.1.2) := by
  have := Fintype.ofFinite C
  have hinner : ∀ (c : C) (m : G), Summable fun n => b c (n - m) := fun c m =>
    ((Equiv.subRight m).summable_iff (f := b c)).mpr (hb c)
  have hsum : ∀ (c : C) (m : G), ∑' n, b c (n - m) = ∑' j, b c j := fun c m =>
    (Equiv.subRight m).tsum_eq (b c)
  have hnn : 0 ≤ fun q : (C × G) × G => a q.1.1 q.1.2 * b q.1.1 (q.2 - q.1.2) :=
    fun q => mul_nonneg (ha0 _ _) (hb0 _ _)
  have hnn' : 0 ≤ fun p : C × G => a p.1 p.2 * ∑' j, b p.1 j :=
    fun p => mul_nonneg (ha0 _ _) (tsum_nonneg (hb0 _))
  have hfirst : Summable fun p : C × G => a p.1 p.2 * ∑' j, b p.1 j := by
    refine (summable_prod_of_nonneg hnn').mpr ⟨fun c => (ha c).mul_right (∑' j, b c j), ?_⟩
    exact (hasSum_fintype _).summable
  refine (summable_prod_of_nonneg hnn).mpr ⟨fun p => (hinner p.1 p.2).mul_left (a p.1 p.2), ?_⟩
  refine hfirst.congr fun p => ?_
  show a p.1 p.2 * ∑' j, b p.1 j = ∑' y, a p.1 p.2 * b p.1 (y - p.2)
  rw [tsum_mul_left, hsum]
theorem summable_pairSummand (hOrb : QuotOrbits.Claim) (hP : IsPeriodic P)
    (hP'' : IsPeriodic P'') {T : P'.Carrier → P.Carrier → ℂ}
    {S : P.Carrier → P''.Carrier → ℂ} (hS : IsShiftInvariant P'' P S) {k : Fin 4 → ℂ}
    (fT : SymbolSummableAt P P' T k) (fS : SymbolSummableAt P'' P S k) (x' : P'.Carrier)
    (x'' : P''.Carrier) : Summable (pairSummand T S k x' x'') := by
  have hfin := hP.finite_quot
  have hrep : ∀ c : P.UnitQuot, ∃ x, P.mkQuot 1 x = c := fun c => Quot.exists_rep c
  choose r hr using hrep
  have hbij := (hOrb P hP).2 1 one_pos r hr
  obtain ⟨e, he⟩ : ∃ e : P.UnitQuot × (Fin 4 → ℤ) ≃ P.Carrier,
      ∀ c m, e (c, m) = P.translate m (r c) :=
    ⟨Equiv.ofBijective _ hbij, fun c m => by simp [Equiv.ofBijective_apply]⟩
  have hs := summable_mul_sub (C := P.UnitQuot)
    (a := fun c m => ‖symbolSummand P P' T k x' (r c) m‖)
    (b := fun c j => ‖symbolSummand P'' P S k (r c) x'' j‖)
    (fun c => fT x' (r c)) (fun c => fS (r c) x'') (fun _ _ => norm_nonneg _)
    (fun _ _ => norm_nonneg _)
  have hn : Summable fun q : (P.UnitQuot × (Fin 4 → ℤ)) × (Fin 4 → ℤ) =>
      ‖pairSummand T S k x' x'' (e q.1, q.2)‖ := by
    refine hs.congr fun q => ?_
    obtain ⟨⟨c, m⟩, n⟩ := q
    simp only
    rw [he, pairSummand_translate hP hP'' T hS, norm_mul]
  refine Summable.of_norm ?_
  exact ((e.prodCongr (Equiv.refl (Fin 4 → ℤ))).summable_iff
    (f := fun p => ‖pairSummand T S k x' x'' p‖)).mp hn
theorem symbolSummand_compKernel_eq_tsum (T : P'.Carrier → P.Carrier → ℂ)
    (S : P.Carrier → P''.Carrier → ℂ) (k : Fin 4 → ℂ) (x' : P'.Carrier) (x'' : P''.Carrier)
    (n : Fin 4 → ℤ) :
    symbolSummand P'' P' (compKernel T S) k x' x'' n =
      ∑' x, pairSummand T S k x' x'' (x, n) := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolComp.symbolSummand_compKernel_eq_tsum <;> assumption
theorem summable_symbolSummand_compKernel {T : P'.Carrier → P.Carrier → ℂ}
    {S : P.Carrier → P''.Carrier → ℂ} {k : Fin 4 → ℂ} {x' : P'.Carrier} {x'' : P''.Carrier}
    (hG : Summable (pairSummand T S k x' x'')) :
    Summable fun n => ‖symbolSummand P'' P' (compKernel T S) k x' x'' n‖ := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolComp.summable_norm_symbolSummand_of_summable <;> assumption
theorem tsum_pairSummand_snd (T : P'.Carrier → P.Carrier → ℂ)
    (S : P.Carrier → P''.Carrier → ℂ) (k : Fin 4 → ℂ) (x' : P'.Carrier) (x'' : P''.Carrier)
    (x : P.Carrier) :
    ∑' n, pairSummand T S k x' x'' (x, n) =
      T x' x * Complex.exp (Complex.I * bilinDot k (toComplexVec (P.pos x - P'.pos x'))) *
        fourierSymbol P'' P S k x x'' := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolComp.tsum_pairSummand_snd <;> assumption
theorem fourierSymbol_compKernel_eq_tsum_quot (hOrb : QuotOrbits.Claim) (hP : IsPeriodic P)
    {T : P'.Carrier → P.Carrier → ℂ} {S : P.Carrier → P''.Carrier → ℂ} {k : Fin 4 → ℂ}
    {x' : P'.Carrier} {x'' : P''.Carrier} (hG : Summable (pairSummand T S k x' x''))
    (hcongr : ∀ x₁ x₂, P.mkQuot 1 x₁ = P.mkQuot 1 x₂ →
      fourierSymbol P'' P S k x₁ x'' = fourierSymbol P'' P S k x₂ x'')
    (r : P.UnitQuot → P.Carrier) (hr : ∀ c, P.mkQuot 1 (r c) = c) :
    fourierSymbol P'' P' (compKernel T S) k x' x'' =
      ∑' c, fourierSymbol P P' T k x' (r c) * fourierSymbol P'' P S k (r c) x'' := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolComp.fourierSymbol_compKernel_eq_tsum_quot <;> assumption
theorem claim_holds (hQuot : SymbolOnQuotients.Claim) (hOrb : QuotOrbits.Claim)
    (hComp : CompClaim) : Claim := by
  refine ⟨?_, ?_⟩
  · intro P P' hP hP' T T' k a a' hT fT hT' fT'
    have hfin := hP.finite_quot
    have hK := isPeriodicKernel_linearCombination a a' hT hT'
    have fK := symbolSummableAt_linearCombination a a' fT fT'
    refine ⟨hK, fK, ?_⟩
    have e : descendMatrix P P' 1
          (fourierSymbol P P' (fun x' x => a * T x' x + a' * T' x' x) k) =
        fun i j => a * descendMatrix P P' 1 (fourierSymbol P P' T k) i j +
          a' * descendMatrix P P' 1 (fourierSymbol P P' T' k) i j := by
      funext i j
      obtain ⟨x', rfl⟩ : ∃ x', P'.mkQuot 1 x' = i := Quot.exists_rep i
      obtain ⟨x, rfl⟩ : ∃ x, P.mkQuot 1 x = j := Quot.exists_rep j
      have h0 := (hQuot P P' hP hP' _ hK).quotSymbol_mkQuot k fK x' x
      have h1 := (hQuot P P' hP hP' _ hT).quotSymbol_mkQuot k fT x' x
      have h2 := (hQuot P P' hP hP' _ hT').quotSymbol_mkQuot k fT' x' x
      simp only [quotSymbol] at h0 h1 h2
      rw [h0, h1, h2]
      exact fourierSymbol_linearCombination a a' fT fT' x' x
    simp only [symbolHom]
    rw [e]
    exact linearMapOfEntries_linearCombination _ _ a a'
  · intro P P' P'' hP hP' hP'' T S k hT fT hS fS
    have hfin := hP.finite_quot
    have hfin'' := hP''.finite_quot
    obtain ⟨δ, hδT, hδS⟩ := exists_common_decayRate hT hS
    have hTS := (hComp P P' P'' hP hP' hP'' T S δ hT hδT hS hδS).comp_periodic
    have hG := summable_pairSummand hOrb hP hP'' hS.1 fT fS
    have hformed : SymbolSummableAt P'' P' (compKernel T S) k := fun x' x'' =>
      summable_symbolSummand_compKernel (hG x' x'')
    refine ⟨hTS.1, hTS.2, hformed, ?_⟩
    have cTS := hQuot P'' P' hP'' hP' _ hTS.2
    have cT := hQuot P P' hP hP' T hT
    have cS := hQuot P'' P hP'' hP S hS
    have hrep : ∀ c : P.UnitQuot, ∃ x, P.mkQuot 1 x = c := fun c => Quot.exists_rep c
    choose r hr using hrep
    have e : descendMatrix P'' P' 1 (fourierSymbol P'' P' (compKernel T S) k) =
        compKernel (descendMatrix P P' 1 (fourierSymbol P P' T k))
          (descendMatrix P'' P 1 (fourierSymbol P'' P S k)) := by
      funext c' c''
      obtain ⟨x', rfl⟩ : ∃ x', P'.mkQuot 1 x' = c' := Quot.exists_rep c'
      obtain ⟨x'', rfl⟩ : ∃ x'', P''.mkQuot 1 x'' = c'' := Quot.exists_rep c''
      have h0 := cTS.quotSymbol_mkQuot k hformed x' x''
      simp only [quotSymbol] at h0
      rw [h0, fourierSymbol_compKernel_eq_tsum_quot hOrb hP (hG x' x'')
        (fun x₁ x₂ h => cS.fourierSymbol_congr_mkQuot k fS x₁ x₂ x'' x'' h rfl) r hr]
      unfold compKernel
      refine tsum_congr fun c => ?_
      have e1 := cT.quotSymbol_mkQuot k fT x' (r c)
      have e2 := cS.quotSymbol_mkQuot k fS (r c) x''
      simp only [quotSymbol] at e1 e2
      rw [hr c] at e1 e2
      rw [e1, e2]
    simp only [symbolHom]
    rw [e]
    exact linearMapOfEntries_compKernel _ _
end YangMills.Construction.PeriodicOperators.SymbolAtPoint
end
