import YangMills.Construction.InfiniteLattice.TraceOnTheGroupAndOneBondWeight
import YangMills.Construction.Matrices.ClassicalHarmonicAnalysisOnG
import YangMills.Construction.Matrices.MultiplicationByAPolynomialOnPowersOfGForm
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open Matrices
namespace SpinHarmonics.PolyMulShift
open SeveralVariables
theorem eq_of_toReal_eq {s t : HalfNatural} (h : s.toReal = t.toReal) : s = t := by
  obtain ⟨a⟩ := s
  obtain ⟨b⟩ := t
  have hab : (a : ℝ) = b := by
    have h₂ := h
    simp only [HalfNatural.toReal] at h₂
    linarith
  have hab' : a = b := by exact_mod_cast hab
  rw [hab']
theorem star_entry_eq_mul_entry (hT : InfiniteLattice.SpecialUnitaryTraceFacts) (i j : Fin 2) :
    ∃ (a : ℂ) (k m : Fin 2), ∀ g : ComplexMatrix2.specialUnitary,
      star ((g : ComplexMatrix2) i j) = a * (g : ComplexMatrix2) k m := by
  have h₁ : ∀ g : ComplexMatrix2.specialUnitary,
      (g : ComplexMatrix2) 1 1 = star ((g : ComplexMatrix2) 0 0) := fun g => (hT.2 g).1
  have h₂ : ∀ g : ComplexMatrix2.specialUnitary,
      (g : ComplexMatrix2) 1 0 = -star ((g : ComplexMatrix2) 0 1) := fun g => (hT.2 g).2.1
  have e₀₀ : ∀ g : ComplexMatrix2.specialUnitary,
      star ((g : ComplexMatrix2) 0 0) = 1 * (g : ComplexMatrix2) 1 1 := fun g => by
    rw [h₁ g, one_mul]
  have e₀₁ : ∀ g : ComplexMatrix2.specialUnitary,
      star ((g : ComplexMatrix2) 0 1) = -1 * (g : ComplexMatrix2) 1 0 := fun g => by
    rw [h₂ g]
    ring
  have e₁₀ : ∀ g : ComplexMatrix2.specialUnitary,
      star ((g : ComplexMatrix2) 1 0) = -1 * (g : ComplexMatrix2) 0 1 := fun g => by
    rw [h₂ g]
    simp
  have e₁₁ : ∀ g : ComplexMatrix2.specialUnitary,
      star ((g : ComplexMatrix2) 1 1) = 1 * (g : ComplexMatrix2) 0 0 := fun g => by
    rw [h₁ g]
    simp
  fin_cases i <;> fin_cases j
  exacts [⟨1, 1, 1, e₀₀⟩, ⟨-1, 1, 0, e₀₁⟩, ⟨-1, 0, 1, e₁₀⟩, ⟨1, 0, 0, e₁₁⟩]
theorem coe_inv_eq_star (g : ComplexMatrix2.specialUnitary) :
    ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) = star (g : ComplexMatrix2) := by
  have h₁ : ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) * (g : ComplexMatrix2) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    rfl
  have h₂ : (g : ComplexMatrix2) * star (g : ComplexMatrix2) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  calc ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2)
        = ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) *
            ((g : ComplexMatrix2) * star (g : ComplexMatrix2)) := by
        rw [h₂, mul_one]
    _ = star (g : ComplexMatrix2) := by rw [← mul_assoc, h₁, one_mul]
theorem exists_eq_mul_entryMap (hT : InfiniteLattice.SpecialUnitaryTraceFacts)
    {f : ComplexMatrix2.specialUnitary → ℂ} (hf : f ∈ entryFns) :
    ∃ (a : ℂ) (i j : Fin 2), ∀ g, f g = a * entryMap i j g := by
  obtain ⟨i, j, rfl | rfl | rfl⟩ := hf
  · exact ⟨1, i, j, fun g => by simp [entryMap]⟩
  · obtain ⟨a, k, m, h⟩ := star_entry_eq_mul_entry hT i j
    exact ⟨a, k, m, h⟩
  · obtain ⟨a, k, m, h⟩ := star_entry_eq_mul_entry hT j i
    refine ⟨a, k, m, fun g => ?_⟩
    have e := h g
    change ((g⁻¹ : ComplexMatrix2.specialUnitary) : ComplexMatrix2) i j = a * (g : ComplexMatrix2) k m
    rw [coe_inv_eq_star, Matrix.star_apply]
    exact e
variable {J : Type} [Finite J]
def shiftSpan (l : J → HalfNatural) (E : J → ℕ) :
    Submodule ℂ C(J → ComplexMatrix2.specialUnitary, ℂ) :=
  ⨆ (l' : J → HalfNatural) (_ : ∀ b, |(l' b).toReal - (l b).toReal| ≤ (E b : ℝ) / 2),
    prodCoeffSpan l'
theorem le_shiftSpan {l l' : J → HalfNatural} {E : J → ℕ}
    (h : ∀ b, |(l' b).toReal - (l b).toReal| ≤ (E b : ℝ) / 2) :
    prodCoeffSpan l' ≤ shiftSpan l E := by
  unfold shiftSpan
  exact le_iSup₂ (f := fun (l' : J → HalfNatural)
    (_ : ∀ b, |(l' b).toReal - (l b).toReal| ≤ (E b : ℝ) / 2) => prodCoeffSpan l') l' h
theorem shiftSpan_mono {l : J → HalfNatural} {E E' : J → ℕ} (h : ∀ b, E b ≤ E' b) :
    shiftSpan l E ≤ shiftSpan l E' := by
  refine iSup₂_le fun l' hl' => le_shiftSpan fun b => (hl' b).trans ?_
  have h' : (E b : ℝ) ≤ E' b := by exact_mod_cast h b
  linarith
def evalAt (c : J) (x : C(ComplexMatrix2.specialUnitary, ℂ)) :
    C(J → ComplexMatrix2.specialUnitary, ℂ) :=
  ⟨fun u => x (u c), x.continuous.comp (continuous_apply c)⟩
@[simp] theorem evalAt_apply (c : J) (x : C(ComplexMatrix2.specialUnitary, ℂ))
    (u : J → ComplexMatrix2.specialUnitary) : evalAt c x u = x (u c) := rfl
theorem coordProduct_update [DecidableEq J] (φ : J → C(ComplexMatrix2.specialUnitary, ℂ)) (c : J)
    (y : C(ComplexMatrix2.specialUnitary, ℂ)) :
    coordProduct (Function.update φ c y) =
      evalAt c y * coordProduct (Function.update φ c 1) := by
  let _ : Fintype J := Fintype.ofFinite J
  ext u
  change (∏ᶠ b, Function.update φ c y b (u b)) =
    y (u c) * ∏ᶠ b, Function.update φ c 1 b (u b)
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype,
    ← Finset.mul_prod_erase Finset.univ (fun b => Function.update φ c y b (u b))
      (Finset.mem_univ c),
    ← Finset.mul_prod_erase Finset.univ (fun b => Function.update φ c 1 b (u b))
      (Finset.mem_univ c)]
  simp only [Function.update_self, ContinuousMap.one_apply, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hb),
    Function.update_of_ne (Finset.ne_of_mem_erase hb)]
theorem eq_zero_or_mem_coeffSpan_of_mem_coeffSpanPred (t : HalfNatural)
    {y : C(ComplexMatrix2.specialUnitary, ℂ)} (hy : y ∈ coeffSpanPred t) :
    y = 0 ∨ ∃ s : HalfNatural, y ∈ coeffSpan s ∧ |s.toReal - t.toReal| ≤ 1 / 2 := by
  obtain ⟨n⟩ := t
  cases n with
  | zero => exact Or.inl ((Submodule.mem_bot ℂ).mp hy)
  | succ n =>
    refine Or.inr ⟨⟨n⟩, hy, ?_⟩
    simp only [HalfNatural.toReal]
    push_cast
    rw [abs_le]
    constructor <;> linarith
theorem abs_toReal_addHalf_sub (t : HalfNatural) : |t.addHalf.toReal - t.toReal| ≤ 1 / 2 := by
  simp only [HalfNatural.toReal, HalfNatural.addHalf]
  push_cast
  rw [abs_le]
  constructor <;> linarith
theorem coordProduct_update_mem_shiftSpan [DecidableEq J] {l l' : J → HalfNatural} {E E' : J → ℕ}
    {c : J} (hE : ∀ b, b ≠ c → E b ≤ E' b) (hEc : E c + 1 ≤ E' c)
    (hl' : ∀ b, |(l' b).toReal - (l b).toReal| ≤ (E b : ℝ) / 2)
    {φ : J → C(ComplexMatrix2.specialUnitary, ℂ)} (hφ : ∀ b, φ b ∈ coeffSpan (l' b))
    {t : HalfNatural} {y : C(ComplexMatrix2.specialUnitary, ℂ)} (hy : y ∈ coeffSpan t)
    (ht : |t.toReal - (l' c).toReal| ≤ 1 / 2) :
    coordProduct (Function.update φ c y) ∈ shiftSpan l E' := by
  refine le_shiftSpan (l' := Function.update l' c t) (fun b => ?_)
    (Submodule.subset_span ⟨Function.update φ c y, fun b => ?_, rfl⟩)
  · by_cases hb : b = c
    · subst hb
      rw [Function.update_self]
      have h₁ := abs_sub_le t.toReal (l' b).toReal (l b).toReal
      have h₂ := hl' b
      have h₃ : ((E b : ℝ) + 1) ≤ E' b := by exact_mod_cast hEc
      linarith
    · rw [Function.update_of_ne hb]
      have h' : (E b : ℝ) ≤ E' b := by exact_mod_cast hE b hb
      have h₂ := hl' b
      linarith
  · by_cases hb : b = c
    · subst hb
      simpa using hy
    · simpa [Function.update_of_ne hb] using hφ b
theorem evalAt_entryMap_mul_mem (hcg : ∀ t, ClebschGordanFacts t) {l : J → HalfNatural}
    {E E' : J → ℕ} (c : J) (hE : ∀ b, b ≠ c → E b ≤ E' b) (hEc : E c + 1 ≤ E' c) (i j : Fin 2)
    {H : C(J → ComplexMatrix2.specialUnitary, ℂ)} (hH : H ∈ shiftSpan l E) :
    evalAt c (entryMap i j) * H ∈ shiftSpan l E' := by
  classical
  have key : shiftSpan l E ≤
      (shiftSpan l E').comap (LinearMap.mulLeft ℂ (evalAt c (entryMap i j))) := by
    refine iSup₂_le fun l' hl' => Submodule.span_le.mpr ?_
    rintro _ ⟨φ, hφ, rfl⟩
    change evalAt c (entryMap i j) * coordProduct φ ∈ shiftSpan l E'
    obtain ⟨y, hy, z, hz, hyz⟩ :=
      Submodule.mem_sup.mp ((hcg (l' c)).entryMap_mul_mem i j (φ c) (hφ c))
    have e : evalAt c (entryMap i j) * coordProduct φ =
        coordProduct (Function.update φ c y) + coordProduct (Function.update φ c z) := by
      have e₀ := coordProduct_update φ c (φ c)
      rw [Function.update_eq_self] at e₀
      rw [coordProduct_update φ c y, coordProduct_update φ c z, e₀]
      ext u
      have e₁ := congrArg (fun F : C(ComplexMatrix2.specialUnitary, ℂ) => F (u c)) hyz
      simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply] at e₁
      simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, evalAt_apply]
      rw [← mul_assoc, ← e₁]
      ring
    rw [e]
    refine Submodule.add_mem _ ?_ ?_
    · rcases eq_zero_or_mem_coeffSpan_of_mem_coeffSpanPred (l' c) hy with rfl | ⟨s, hs, hd⟩
      · have e₂ : coordProduct
            (Function.update φ c (0 : C(ComplexMatrix2.specialUnitary, ℂ))) = 0 := by
          rw [coordProduct_update]
          ext u
          simp
        rw [e₂]
        exact Submodule.zero_mem _
      · exact coordProduct_update_mem_shiftSpan hE hEc hl' hφ hs hd
    · exact coordProduct_update_mem_shiftSpan hE hEc hl' hφ hz (abs_toReal_addHalf_sub (l' c))
  exact key hH
theorem list_prod_mul_mem (hT : InfiniteLattice.SpecialUnitaryTraceFacts)
    (hcg : ∀ t, ClebschGordanFacts t) {l : J → HalfNatural} (c : J)
    (w : List (ComplexMatrix2.specialUnitary → ℂ)) :
    (∀ f ∈ w, f ∈ entryFns) → ∀ {E E' : J → ℕ}, (∀ b, b ≠ c → E b ≤ E' b) →
      E c + w.length ≤ E' c → ∀ {H : C(J → ComplexMatrix2.specialUnitary, ℂ)},
        H ∈ shiftSpan l E →
        ∃ H' ∈ shiftSpan l E', ∀ u, H' u = (w.map fun f => f (u c)).prod * H u := by
  classical
  induction w with
  | nil =>
    intro _ E E' hE hEc H hH
    refine ⟨H, shiftSpan_mono (fun b => ?_) hH, fun u => by simp⟩
    by_cases hb : b = c
    · subst hb
      simpa using hEc
    · exact hE b hb
  | cons f w ih =>
    intro hwf E E' hE hEc H hH
    obtain ⟨a, i, j, hf⟩ := exists_eq_mul_entryMap hT (hwf f List.mem_cons_self)
    obtain ⟨H₁, h₁, v₁⟩ := ih (fun f hf => hwf f (List.mem_cons_of_mem _ hf))
      (E' := fun b => if b = c then E c + w.length else E b)
      (fun b hb => by simp [hb]) (by simp) hH
    refine ⟨a • (evalAt c (entryMap i j) * H₁), Submodule.smul_mem _ _
      (evalAt_entryMap_mul_mem hcg c (fun b hb => ?_) ?_ i j h₁), fun u => ?_⟩
    · simpa [hb] using hE b hb
    · simp only [if_true]
      simp only [List.length_cons] at hEc
      omega
    · simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply, evalAt_apply, smul_eq_mul,
        List.map_cons, List.prod_cons, hf, v₁]
      ring
theorem finset_prod_mul_mem [DecidableEq J] (hT : InfiniteLattice.SpecialUnitaryTraceFacts)
    (hcg : ∀ t, ClebschGordanFacts t) {l : J → HalfNatural} {ι : Type} (e : ι → J) (D : ι → ℕ)
    (M : ι → ComplexMatrix2.specialUnitary → ℂ) (hM : ∀ b, IsEntryMonomial (D b) (M b))
    (s : Finset ι) {H : C(J → ComplexMatrix2.specialUnitary, ℂ)}
    (hH : H ∈ shiftSpan l fun _ => 0) :
    ∃ H' ∈ shiftSpan l (fun c => ∑ b ∈ s, if e b = c then D b else 0),
      ∀ u, H' u = (∏ b ∈ s, M b (u (e b))) * H u := by
  classical
  refine Finset.induction_on s ?_ ?_
  · exact ⟨H, by simpa using hH, fun u => by simp⟩
  · intro a s ha ih
    obtain ⟨H₁, h₁, v₁⟩ := ih
    obtain ⟨w, hwl, hwf, hv⟩ := hM a
    have hA : ∀ c, c ≠ e a → (∑ b ∈ s, if e b = c then D b else 0) ≤
        ∑ b ∈ insert a s, if e b = c then D b else 0 := fun c _ => by
      rw [Finset.sum_insert ha]
      exact Nat.le_add_left _ _
    have hB : (∑ b ∈ s, if e b = e a then D b else 0) + w.length ≤
        ∑ b ∈ insert a s, if e b = e a then D b else 0 := by
      rw [Finset.sum_insert ha, if_pos rfl]
      omega
    obtain ⟨H₂, h₂, v₂⟩ := list_prod_mul_mem hT hcg (e a) w hwf
      (E := fun c => ∑ b ∈ s, if e b = c then D b else 0)
      (E' := fun c => ∑ b ∈ insert a s, if e b = c then D b else 0) hA hB h₁
    refine ⟨H₂, h₂, fun u => ?_⟩
    rw [v₂, v₁, Finset.prod_insert ha, hv (u (e a)), mul_assoc]
theorem one_mem_coeffSpan_zero : (1 : C(ComplexMatrix2.specialUnitary, ℂ)) ∈ coeffSpan ⟨0⟩ := by
  refine Submodule.subset_span ⟨(0, 0), ?_⟩
  ext g
  change spinCoeff ⟨0⟩ 0 0 g = 1
  have h : spinRep ⟨0⟩ g (monomialBasis ⟨0⟩ 0) = monomialBasis ⟨0⟩ 0 := by
    apply Subtype.ext
    change MvPolynomial.aeval (columnForms (g : ComplexMatrix2)) (normalizedMonomial ⟨0⟩ 0) =
      normalizedMonomial ⟨0⟩ 0
    simp [normalizedMonomial]
  rw [spinCoeff, h, homogeneousInner_monomialBasis]
  simp
theorem mul_isRealizedIn_nearbySpinSpan (hT : InfiniteLattice.SpecialUnitaryTraceFacts)
    (hcg : ∀ t, ClebschGordanFacts t) (l : J → HalfNatural) (B : Set J) (D : ↥B → ℕ)
    (f : (↥B → ComplexMatrix2.specialUnitary) → ℂ) (hf : HasDegreeBound D f)
    (ψ : C(J → ComplexMatrix2.specialUnitary, ℂ)) (hψ : ψ ∈ prodCoeffSpan l) :
    IsRealizedIn (fun u => pullFromPart B f u * ψ u) (nearbySpinSpan B D l) := by
  classical
  have hψ' : ψ ∈ shiftSpan l fun _ => 0 := le_shiftSpan (fun b => by simp) hψ
  obtain ⟨-, hspan⟩ := hf
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨M, hM, rfl⟩ := hx
    let _ : Fintype ↥B := Fintype.ofFinite _
    obtain ⟨H, hH, v⟩ := finset_prod_mul_mem hT hcg Subtype.val D M hM Finset.univ hψ'
    refine ⟨H, ?_, fun u => ?_⟩
    · have hle : shiftSpan l (fun c => ∑ b : ↥B, if (b : J) = c then D b else 0) ≤
          nearbySpinSpan B D l := by
        unfold shiftSpan nearbySpinSpan
        refine iSup₂_le fun l' hl' => ?_
        refine le_iSup₂_of_le (f := fun (l' : J → HalfNatural) (_ : (∀ b : ↥B,
          |(l' b).toReal - (l b).toReal| ≤ (D b : ℝ) / 2) ∧ ∀ b, b ∉ B → l' b = l b) =>
          prodCoeffSpan l') l' ⟨fun b => ?_, fun b hb => ?_⟩ le_rfl
        · have h := hl' b
          have e : (∑ x : ↥B, if (x : J) = (b : J) then D x else 0) = D b := by
            rw [Finset.sum_eq_single b]
            · simp
            · intro x _ hx
              exact if_neg fun e => hx (Subtype.ext e)
            · simp
          simpa only [e] using h
        · have h := hl' b
          have e : (∑ x : ↥B, if (x : J) = b then D x else 0) = 0 :=
            Finset.sum_eq_zero fun x _ => if_neg fun e : (x : J) = b => hb (e ▸ x.2)
          simp only [e, Nat.cast_zero, zero_div] at h
          exact eq_of_toReal_eq (sub_eq_zero.mp (abs_nonpos_iff.mp h))
      exact hle hH
    · rw [v u]
      simp only [pullFromPart, restrictTo, finprod_eq_prod_of_fintype]
  | zero => exact ⟨0, Submodule.zero_mem _, fun u => by simp [pullFromPart]⟩
  | add x y _ _ hx hy =>
    obtain ⟨H₁, h₁, v₁⟩ := hx
    obtain ⟨H₂, h₂, v₂⟩ := hy
    refine ⟨H₁ + H₂, Submodule.add_mem _ h₁ h₂, fun u => ?_⟩
    have e₁ := v₁ u
    have e₂ := v₂ u
    simp only [pullFromPart, Pi.add_apply, ContinuousMap.add_apply, add_mul] at e₁ e₂ ⊢
    rw [e₁, e₂]
  | smul a x _ hx =>
    obtain ⟨H₁, h₁, v₁⟩ := hx
    refine ⟨a • H₁, Submodule.smul_mem _ _ h₁, fun u => ?_⟩
    have e₁ := v₁ u
    simp only [pullFromPart, Pi.smul_apply, ContinuousMap.smul_apply, smul_eq_mul] at e₁ ⊢
    rw [mul_assoc, e₁]
theorem isRealizedIn_truncatedCoeffSpan (hT : InfiniteLattice.SpecialUnitaryTraceFacts)
    (hcg : ∀ t, ClebschGordanFacts t) (D : ℕ) (F : (J → ComplexMatrix2.specialUnitary) → ℂ)
    (hF : HasDegreeBound (fun _ : J => D) F) :
    IsRealizedIn F (truncatedCoeffSpan J ⟨D⟩) := by
  classical
  obtain ⟨-, hspan⟩ := hF
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨M, hM, rfl⟩ := hx
    let _ : Fintype J := Fintype.ofFinite J
    have h₀ : coordProduct (fun _ : J => (1 : C(ComplexMatrix2.specialUnitary, ℂ))) ∈
        shiftSpan (fun _ : J => (⟨0⟩ : HalfNatural)) fun _ => 0 :=
      le_shiftSpan (fun b => by simp)
        (Submodule.subset_span ⟨fun _ => 1, fun _ => one_mem_coeffSpan_zero, rfl⟩)
    obtain ⟨H, hH, v⟩ :=
      finset_prod_mul_mem hT hcg (fun b : J => b) (fun _ => D) M hM Finset.univ h₀
    refine ⟨H, ?_, fun u => ?_⟩
    · have hle : shiftSpan (fun _ : J => (⟨0⟩ : HalfNatural))
          (fun c => ∑ b : J, if b = c then D else 0) ≤ truncatedCoeffSpan J ⟨D⟩ := by
        unfold shiftSpan truncatedCoeffSpan
        refine iSup₂_le fun l' hl' => ?_
        refine le_iSup₂_of_le (f := fun l (_ : l ∈ boundedWeights J ⟨D⟩) =>
          prodCoeffSpan l) l' (mem_boundedWeights.mpr fun b => ?_) le_rfl
        have h := hl' b
        have e : (∑ x : J, if x = b then D else 0) = D := by simp
        dsimp only at h
        rw [e] at h
        have h₂ := (abs_le.mp h).2
        simp only [HalfNatural.toReal] at h₂ ⊢
        simpa using h₂
      exact hle hH
    · rw [v u]
      have e : coordProduct (fun _ : J => (1 : C(ComplexMatrix2.specialUnitary, ℂ))) u = 1 := by
        change (∏ᶠ _ : J, (1 : C(ComplexMatrix2.specialUnitary, ℂ)) _) = 1
        simp
      rw [e, mul_one]
      exact finprod_eq_prod_of_fintype _
  | zero => exact ⟨0, Submodule.zero_mem _, fun u => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨H₁, h₁, v₁⟩ := hx
    obtain ⟨H₂, h₂, v₂⟩ := hy
    exact ⟨H₁ + H₂, Submodule.add_mem _ h₁ h₂, fun u => by simp [v₁ u, v₂ u]⟩
  | smul a x _ hx =>
    obtain ⟨H₁, h₁, v₁⟩ := hx
    exact ⟨a • H₁, Submodule.smul_mem _ _ h₁, fun u => by simp [v₁ u]⟩
theorem allPolyMulShiftSpins_of (h₁ : HarmonicAnalysisFacts)
    (h₂ : InfiniteLattice.TraceAndSingleBondWeight) : AllPolyMulShiftSpins := by
  intro J _ _ l
  have hcg : ∀ t, ClebschGordanFacts t := fun t => (h₁ t t).2.2.2.2.2.1
  exact ⟨fun B _ D f hf ψ hψ => mul_isRealizedIn_nearbySpinSpan h₂.1 hcg l B D f hf ψ hψ,
    fun D F hF => isRealizedIn_truncatedCoeffSpan h₂.1 hcg D F hF⟩
end SpinHarmonics.PolyMulShift
end YangMills.Construction
end
