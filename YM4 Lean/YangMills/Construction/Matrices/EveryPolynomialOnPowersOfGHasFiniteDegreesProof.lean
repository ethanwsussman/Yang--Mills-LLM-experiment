import YangMills.Construction.Matrices.EveryPolynomialOnPowersOfGHasFiniteDegrees
import YangMills.Construction.Matrices.PolynomialsAreSpannedByThePeterWeylFunctionsForm
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open Matrices Matrices.ComplexMatrix2 HilbertSpaceBasics
namespace SpinHarmonics.PolynomialDegrees
variable {J : Type} [Finite J]
theorem truncatedCoeffSpan_mono {κ κ' : HalfNatural} (hκ : κ.toReal ≤ κ'.toReal) :
    truncatedCoeffSpan J κ ≤ truncatedCoeffSpan J κ' := by
  refine iSup₂_le fun s hs => ?_
  have hs' : s ∈ boundedWeights J κ' :=
    mem_boundedWeights.mpr fun b => (mem_boundedWeights.mp hs b).trans hκ
  exact le_iSup₂_of_le (f := fun s (_ : s ∈ boundedWeights J κ') =>
    prodCoeffSpan s) s hs' le_rfl
theorem normalizedCoeff_mem_coeffSpan (e : PeterWeylLabel) :
    normalizedCoeff e ∈ coeffSpan e.spin :=
  Submodule.smul_mem _ _ (Submodule.subset_span ⟨(e.rowIdx, e.colIdx), rfl⟩)
theorem exists_peterWeylFn_mem_truncated (a : PeterWeylIndex J) :
    ∃ κ : HalfNatural, peterWeylFn a ∈ truncatedCoeffSpan J κ := by
  let _ : Fintype J := Fintype.ofFinite J
  refine ⟨⟨∑ b, (a b).spin.doubled⟩, ?_⟩
  have hs : spins a ∈ boundedWeights J ⟨∑ b, (a b).spin.doubled⟩ := by
    refine mem_boundedWeights.mpr fun b => ?_
    have hle : (a b).spin.doubled ≤ ∑ c, (a c).spin.doubled :=
      Finset.single_le_sum (f := fun c => (a c).spin.doubled) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    have hle' : ((a b).spin.doubled : ℝ) ≤ ((∑ c, (a c).spin.doubled : ℕ) : ℝ) := by
      exact_mod_cast hle
    simp only [spins, HalfNatural.toReal]
    linarith
  have hmem : peterWeylFn a ∈ prodCoeffSpan (spins a) :=
    Submodule.subset_span
      ⟨fun b => normalizedCoeff (a b), fun b => normalizedCoeff_mem_coeffSpan (a b), rfl⟩
  exact (le_iSup₂_of_le (f := fun s (_ : s ∈ boundedWeights J ⟨∑ b, (a b).spin.doubled⟩) =>
    prodCoeffSpan s) (spins a) hs le_rfl) hmem
theorem exists_mem_truncatedCoeffSpan {H : C(J → specialUnitary, ℂ)}
    (hH : H ∈ Submodule.span ℂ
      (Set.range (peterWeylFn : PeterWeylIndex J → C(J → specialUnitary, ℂ)))) :
    ∃ κ : HalfNatural, H ∈ truncatedCoeffSpan J κ := by
  induction hH using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact exists_peterWeylFn_mem_truncated a
  | zero => exact ⟨⟨0⟩, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨κ₁, hx₁⟩ := hx
    obtain ⟨κ₂, hy₂⟩ := hy
    have le₁ : κ₁.toReal ≤ (⟨κ₁.doubled + κ₂.doubled⟩ : HalfNatural).toReal := by
      simp only [HalfNatural.toReal]
      push_cast
      have : (0 : ℝ) ≤ κ₂.doubled := Nat.cast_nonneg _
      linarith
    have le₂ : κ₂.toReal ≤ (⟨κ₁.doubled + κ₂.doubled⟩ : HalfNatural).toReal := by
      simp only [HalfNatural.toReal]
      push_cast
      have : (0 : ℝ) ≤ κ₁.doubled := Nat.cast_nonneg _
      linarith
    exact ⟨⟨κ₁.doubled + κ₂.doubled⟩, Submodule.add_mem _ (truncatedCoeffSpan_mono le₁ hx₁)
      (truncatedCoeffSpan_mono le₂ hy₂)⟩
  | smul c x _ hx =>
    obtain ⟨κ, hκ⟩ := hx
    exact ⟨κ, Submodule.smul_mem _ c hκ⟩
def entryMonomialProducts (D : J → ℕ) : Set ((J → specialUnitary) → ℂ) :=
  {P | ∃ M : J → specialUnitary → ℂ, (∀ b, IsEntryMonomial (D b) (M b)) ∧
    P = fun u => ∏ᶠ b, M b (u b)}
theorem isEntryMonomial_mono {D D' : ℕ} (hD : D ≤ D') {M : specialUnitary → ℂ}
    (hM : IsEntryMonomial D M) : IsEntryMonomial D' M := by
  obtain ⟨w, hw, hf, hv⟩ := hM
  exact ⟨w, hw.trans hD, hf, hv⟩
theorem isEntryMonomial_mul {D : ℕ} {M f : specialUnitary → ℂ} (hM : IsEntryMonomial D M)
    (hf : f ∈ entryFns) : IsEntryMonomial (D + 1) fun g => M g * f g := by
  obtain ⟨w, hw, hw', hv⟩ := hM
  refine ⟨w ++ [f], ?_, ?_, fun g => ?_⟩
  · simpa using hw
  · intro e he
    rcases List.mem_append.mp he with h | h
    · exact hw' e h
    · rw [List.mem_singleton.mp h]
      exact hf
  · simp [hv g]
theorem span_entryMonomialProducts_mono {D D' : J → ℕ} (hD : ∀ b, D b ≤ D' b) :
    Submodule.span ℂ (entryMonomialProducts D) ≤
      Submodule.span ℂ (entryMonomialProducts D') :=
  Submodule.span_mono fun _ ⟨M, hM, hP⟩ =>
    ⟨M, fun b => isEntryMonomial_mono (hD b) (hM b), hP⟩
theorem exists_entryFn (x : EntryVar J) :
    ∃ (b : J) (f : specialUnitary → ℂ), f ∈ entryFns ∧
      ∀ u : J → specialUnitary, entryEval u x = f (u b) := by
  rcases x with ⟨b, i, j⟩ | ⟨b, i, j⟩
  · exact ⟨b, _, ⟨i, j, Or.inl rfl⟩, fun _ => rfl⟩
  · exact ⟨b, _, ⟨i, j, Or.inr (Or.inl rfl)⟩, fun _ => rfl⟩
theorem mul_entryFn_mem_span {D : J → ℕ} {P : (J → specialUnitary) → ℂ}
    (hP : P ∈ Submodule.span ℂ (entryMonomialProducts D)) (b : J) {f : specialUnitary → ℂ}
    (hf : f ∈ entryFns) :
    (fun u => P u * f (u b)) ∈ Submodule.span ℂ (entryMonomialProducts fun c => D c + 1) := by
  classical
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨M, hM, rfl⟩ := hx
    let _ : Fintype J := Fintype.ofFinite J
    refine Submodule.subset_span
      ⟨fun c g => M c g * (if c = b then f g else 1), fun c => ?_, ?_⟩
    · by_cases hc : c = b
      · subst hc
        simpa using isEntryMonomial_mul (hM c) hf
      · simpa [hc] using isEntryMonomial_mono (Nat.le_succ _) (hM c)
    · funext u
      simp only [finprod_eq_prod_of_fintype, Finset.prod_mul_distrib]
      congr 1
      simp [Finset.prod_ite_eq']
  | zero =>
    have hz : (fun u : J → specialUnitary => (0 : (J → specialUnitary) → ℂ) u * f (u b)) = 0 := by
      funext u
      simp
    rw [hz]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have hsum : (fun u => (x + y) u * f (u b)) =
        (fun u => x u * f (u b)) + fun u => y u * f (u b) := by
      funext u
      simp [add_mul]
    rw [hsum]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have hsmul : (fun u => (c • x) u * f (u b)) = c • fun u => x u * f (u b) := by
      funext u
      simp [mul_assoc]
    rw [hsmul]
    exact Submodule.smul_mem _ c hx
theorem exists_degreeBounds (p : MvPolynomial (EntryVar J) ℂ) :
    ∃ D : J → ℕ, (fun u : J → specialUnitary => MvPolynomial.eval (entryEval u) p) ∈
      Submodule.span ℂ (entryMonomialProducts D) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨fun _ => 0, ?_⟩
    have hC : (fun u : J → specialUnitary => MvPolynomial.eval (entryEval u) (MvPolynomial.C c)) =
        c • fun _ => 1 := by
      funext u
      simp
    rw [hC]
    refine Submodule.smul_mem _ c (Submodule.subset_span
      ⟨fun _ _ => 1, fun _ => ⟨[], by simp, by simp, by simp⟩, ?_⟩)
    funext u
    simp
  | add p q hp hq =>
    obtain ⟨D₁, hD₁⟩ := hp
    obtain ⟨D₂, hD₂⟩ := hq
    refine ⟨fun b => D₁ b + D₂ b, ?_⟩
    have hsum : (fun u : J → specialUnitary => MvPolynomial.eval (entryEval u) (p + q)) =
        (fun u => MvPolynomial.eval (entryEval u) p) +
          fun u => MvPolynomial.eval (entryEval u) q := by
      funext u
      simp
    rw [hsum]
    exact Submodule.add_mem _
      (span_entryMonomialProducts_mono (fun b => Nat.le_add_right _ _) hD₁)
      (span_entryMonomialProducts_mono (fun b => Nat.le_add_left _ _) hD₂)
  | mul_X p x hp =>
    obtain ⟨D, hD⟩ := hp
    obtain ⟨b, f, hf, hx⟩ := exists_entryFn x
    refine ⟨fun c => D c + 1, ?_⟩
    have hprod : (fun u : J → specialUnitary =>
        MvPolynomial.eval (entryEval u) (p * MvPolynomial.X x)) =
        fun u => (fun u : J → specialUnitary => MvPolynomial.eval (entryEval u) p) u * f (u b) := by
      funext u
      simp [hx u]
    rw [hprod]
    exact mul_entryFn_mem_span hD b hf
theorem statement_holds (hspan : PolynomialIffInPeterWeylSpan) : Statement := by
  intro J _ _ F hF
  obtain ⟨H, hH, hFH⟩ := (hspan J F).mp hF
  obtain ⟨κ, hκ⟩ := exists_mem_truncatedCoeffSpan hH
  refine ⟨⟨κ, H, hκ, hFH⟩, ?_⟩
  obtain ⟨p, hp⟩ := id hF
  obtain ⟨D, hD⟩ := exists_degreeBounds p
  have hFp : F = fun u => MvPolynomial.eval (entryEval u) p := funext hp
  exact ⟨D, hF, by rw [hFp]; exact hD⟩
end SpinHarmonics.PolynomialDegrees
end YangMills.Construction
end
