import YangMills.Construction.Matrices.RealPolynomialsOfADisjointUnionOfIndexSets
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction
open Matrices Matrices.ComplexMatrix2
namespace SpinHarmonics
namespace DisjointUnionSplit
section EntryPolynomials
variable {ι : Type}
theorem isRealEntryPolynomial_const (c : ℝ) :
    IsRealEntryPolynomial fun _ : ι → specialUnitary => (c : ℂ) :=
  ⟨⟨MvPolynomial.C (c : ℂ), fun u => by simp⟩, fun u => by simp⟩
theorem isRealEntryPolynomial_mul {F G : (ι → specialUnitary) → ℂ}
    (hF : IsRealEntryPolynomial F) (hG : IsRealEntryPolynomial G) :
    IsRealEntryPolynomial fun u => F u * G u := by
  obtain ⟨⟨p, hp⟩, hFr⟩ := hF
  obtain ⟨⟨q, hq⟩, hGr⟩ := hG
  exact ⟨⟨p * q, fun u => by simp [hp u, hq u]⟩,
    fun u => by simp [Complex.mul_im, hFr u, hGr u]⟩
theorem isRealEntryPolynomial_re_apply (a : ι) (i j : Fin 2) :
    IsRealEntryPolynomial fun v : ι → specialUnitary =>
      ((((v a : ComplexMatrix2) i j).re : ℝ) : ℂ) := by
  refine ⟨⟨MvPolynomial.C (1 / 2) * (MvPolynomial.X (Sum.inl (a, i, j)) +
    MvPolynomial.X (Sum.inr (a, i, j))), fun v => ?_⟩, fun v => by simp⟩
  simp only [map_mul, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X, entryEval]
  rw [Complex.star_def, Complex.add_conj]
  push_cast
  ring
theorem isRealEntryPolynomial_im_apply (a : ι) (i j : Fin 2) :
    IsRealEntryPolynomial fun v : ι → specialUnitary =>
      ((((v a : ComplexMatrix2) i j).im : ℝ) : ℂ) := by
  refine ⟨⟨MvPolynomial.C (-Complex.I / 2) * (MvPolynomial.X (Sum.inl (a, i, j)) -
    MvPolynomial.X (Sum.inr (a, i, j))), fun v => ?_⟩, fun v => by simp⟩
  simp only [map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X, entryEval]
  rw [Complex.star_def, Complex.sub_conj]
  push_cast
  linear_combination (((v a : ComplexMatrix2) i j).im : ℂ) * Complex.I_mul_I
end EntryPolynomials
section Blocks
variable {ι : Type} {n : ℕ} (S : Fin n → Set ι)
def blockProducts : Submonoid ((ι → specialUnitary) → ℂ) where
  carrier := {F | ∃ f : (r : Fin n) → (↥(S r) → specialUnitary) → ℂ,
    (∀ r, IsRealEntryPolynomial (f r)) ∧ ∀ u, F u = ∏ r, f r (restrictTo (S r) u)}
  one_mem' := ⟨fun _ _ => ((1 : ℝ) : ℂ), fun _ => isRealEntryPolynomial_const 1, fun u => by simp⟩
  mul_mem' := by
    rintro F G ⟨f, hf, hF⟩ ⟨g, hg, hG⟩
    exact ⟨fun r v => f r v * g r v, fun r => isRealEntryPolynomial_mul (hf r) (hg r),
      fun u => by simp [hF u, hG u, Finset.prod_mul_distrib]⟩
def blockAlgebra : Subalgebra ℝ ((ι → specialUnitary) → ℂ) :=
  Algebra.adjoin ℝ (blockProducts S : Set ((ι → specialUnitary) → ℂ))
variable {S}
theorem mem_span_of_mem_blockAlgebra {F : (ι → specialUnitary) → ℂ} (hF : F ∈ blockAlgebra S) :
    F ∈ Submodule.span ℝ (blockProducts S : Set ((ι → specialUnitary) → ℂ)) := by
  have h := Algebra.adjoin_eq_span (R := ℝ) (s := (blockProducts S : Set ((ι → specialUnitary) → ℂ)))
  rw [Submonoid.closure_eq] at h
  rw [← h]
  exact hF
theorem comp_restrictTo_mem_blockProducts (r₀ : Fin n) {g : (↥(S r₀) → specialUnitary) → ℂ}
    (hg : IsRealEntryPolynomial g) :
    (fun u => g (restrictTo (S r₀) u)) ∈ blockProducts S := by
  refine ⟨Function.update (fun _ _ => ((1 : ℝ) : ℂ)) r₀ g, fun r => ?_, fun u => ?_⟩
  · by_cases h : r = r₀
    · subst h
      simpa using hg
    · simpa [Function.update_of_ne h] using isRealEntryPolynomial_const 1
  · rw [Finset.prod_eq_single r₀]
    · simp
    · intro r _ h
      simp [Function.update_of_ne h]
    · simp
theorem im_eq_zero_of_mem_blockProducts {F : (ι → specialUnitary) → ℂ}
    (hF : F ∈ blockProducts S) (u : ι → specialUnitary) : (F u).im = 0 := by
  obtain ⟨f, hf, hu⟩ := hF
  rw [hu u]
  have h : ∀ r, f r (restrictTo (S r) u) = (((f r (restrictTo (S r) u)).re : ℝ) : ℂ) :=
    fun r => Complex.ext (by simp) (by simpa using (hf r).2 _)
  rw [Finset.prod_congr rfl fun r _ => h r, ← Complex.ofReal_prod]
  exact Complex.ofReal_im _
theorem im_eq_zero_of_mem_span {F : (ι → specialUnitary) → ℂ}
    (hF : F ∈ Submodule.span ℝ (blockProducts S : Set ((ι → specialUnitary) → ℂ)))
    (u : ι → specialUnitary) : (F u).im = 0 := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact im_eq_zero_of_mem_blockProducts hx u
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]
theorem exists_sum_prod_of_mem_span (r₀ : Fin n) {F : (ι → specialUnitary) → ℂ}
    (hF : F ∈ Submodule.span ℝ (blockProducts S : Set ((ι → specialUnitary) → ℂ))) :
    ∃ (m : ℕ) (f : Fin m → (r : Fin n) → (↥(S r) → specialUnitary) → ℂ),
      (∀ k r, IsRealEntryPolynomial (f k r)) ∧
      ∀ u, F u = ∑ k, ∏ r, f k r (restrictTo (S r) u) := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, hu⟩ := hx
    exact ⟨1, fun _ => f, fun _ => hf, fun u => by simp [hu u]⟩
  | zero => exact ⟨0, Fin.elim0, fun k => k.elim0, fun u => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m₁, f₁, h₁, e₁⟩ := hx
    obtain ⟨m₂, f₂, h₂, e₂⟩ := hy
    refine ⟨m₁ + m₂, Fin.append f₁ f₂, fun k => ?_, fun u => ?_⟩
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simpa using h₁ k
      · simpa using h₂ k
    · simp [Fin.sum_univ_add, e₁ u, e₂ u]
  | smul a x _ hx =>
    obtain ⟨m, f, h, e⟩ := hx
    have ht : ∀ k, (fun u => (a : ℂ) * ∏ r, f k r (restrictTo (S r) u)) ∈
        blockProducts S := fun k =>
      (blockProducts S).mul_mem
        (comp_restrictTo_mem_blockProducts r₀ (isRealEntryPolynomial_const a))
        ⟨f k, h k, fun _ => rfl⟩
    choose g hg eg using ht
    have eg' : ∀ k u, (a : ℂ) * ∏ r, f k r (restrictTo (S r) u) =
        ∏ r, g k r (restrictTo (S r) u) := eg
    refine ⟨m, g, hg, fun u => ?_⟩
    simp only [Pi.smul_apply, e u, ← eg', Complex.real_smul, Finset.mul_sum]
theorem exists_re_im_of_entryVar (hcover : (⋃ r, S r) = Set.univ) (x : EntryVar ι) :
    ∃ A ∈ blockAlgebra S, ∃ B ∈ blockAlgebra S,
      ∀ u, entryEval u x = A u + Complex.I * B u := by
  have key : ∀ (a : ι) (i j : Fin 2),
      (fun u : ι → specialUnitary => ((((u a : ComplexMatrix2) i j).re : ℝ) : ℂ)) ∈
        blockAlgebra S ∧
      (fun u : ι → specialUnitary => ((((u a : ComplexMatrix2) i j).im : ℝ) : ℂ)) ∈
        blockAlgebra S := by
    intro a i j
    have ha : a ∈ ⋃ r, S r := by
      rw [hcover]
      trivial
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp ha
    exact ⟨Algebra.subset_adjoin
        (comp_restrictTo_mem_blockProducts r
          (isRealEntryPolynomial_re_apply (⟨a, hr⟩ : ↥(S r)) i j)),
      Algebra.subset_adjoin
        (comp_restrictTo_mem_blockProducts r
          (isRealEntryPolynomial_im_apply (⟨a, hr⟩ : ↥(S r)) i j))⟩
  rcases x with ⟨a, i, j⟩ | ⟨a, i, j⟩
  · refine ⟨_, (key a i j).1, _, (key a i j).2, fun u => ?_⟩
    apply Complex.ext <;> simp [entryEval]
  · refine ⟨_, (key a i j).1, _, neg_mem (key a i j).2, fun u => ?_⟩
    apply Complex.ext <;> simp [entryEval]
theorem exists_re_im_of_mvPolynomial (hcover : (⋃ r, S r) = Set.univ)
    (p : MvPolynomial (EntryVar ι) ℂ) :
    ∃ A ∈ blockAlgebra S, ∃ B ∈ blockAlgebra S,
      ∀ u, MvPolynomial.eval (entryEval u) p = A u + Complex.I * B u := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨algebraMap ℝ _ c.re, Subalgebra.algebraMap_mem _ _,
      algebraMap ℝ _ c.im, Subalgebra.algebraMap_mem _ _, fun u => ?_⟩
    apply Complex.ext <;> simp
  | add p q hp hq =>
    obtain ⟨A₁, hA₁, B₁, hB₁, e₁⟩ := hp
    obtain ⟨A₂, hA₂, B₂, hB₂, e₂⟩ := hq
    refine ⟨A₁ + A₂, add_mem hA₁ hA₂, B₁ + B₂, add_mem hB₁ hB₂, fun u => ?_⟩
    simp only [map_add, e₁ u, e₂ u, Pi.add_apply]
    ring
  | mul_X p x hp =>
    obtain ⟨A, hA, B, hB, e⟩ := hp
    obtain ⟨a, ha, b, hb, e'⟩ := exists_re_im_of_entryVar hcover x
    refine ⟨A * a - B * b, sub_mem (mul_mem hA ha) (mul_mem hB hb),
      A * b + B * a, add_mem (mul_mem hA hb) (mul_mem hB ha), fun u => ?_⟩
    simp only [map_mul, MvPolynomial.eval_X, e u, e' u, Pi.sub_apply, Pi.mul_apply, Pi.add_apply]
    linear_combination (B u * b u) * Complex.I_mul_I
end Blocks
end DisjointUnionSplit
theorem allRealPolyDisjointUnionSplit : AllRealPolyDisjointUnionSplit := by
  intro ι _ _ n S _ _ hcover F hF
  obtain ⟨⟨p, hp⟩, hreal⟩ := id hF
  obtain ⟨A, hA, B, hB, e⟩ := DisjointUnionSplit.exists_re_im_of_mvPolynomial hcover p
  obtain ⟨a⟩ := ‹Nonempty ι›
  have ha : a ∈ ⋃ r, S r := by
    rw [hcover]
    trivial
  obtain ⟨r₀, _⟩ := Set.mem_iUnion.mp ha
  have hA' := DisjointUnionSplit.mem_span_of_mem_blockAlgebra hA
  have hB' := DisjointUnionSplit.mem_span_of_mem_blockAlgebra hB
  obtain ⟨m, f, hf, hs⟩ := DisjointUnionSplit.exists_sum_prod_of_mem_span r₀ hA'
  refine ⟨m, f, hf, fun u => ?_⟩
  have hAi := DisjointUnionSplit.im_eq_zero_of_mem_span hA' u
  have hBi := DisjointUnionSplit.im_eq_zero_of_mem_span hB' u
  have hBr : (B u).re = 0 := by
    have h := hreal u
    rw [hp u, e u] at h
    simpa [hAi] using h
  have hB0 : B u = 0 := Complex.ext hBr hBi
  rw [← hs u, hp u, e u, hB0]
  simp
end SpinHarmonics
end YangMills.Construction
end
