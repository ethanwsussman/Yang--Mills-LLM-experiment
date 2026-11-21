import YangMills.Construction.Matrices.RealPolynomialsOfADisjointUnionOfIndexSetsProof
import YangMills.Construction.Matrices.RealPolynomialsOnPowersOfGAreDense
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SpinHarmonics.RealPolyDense
variable {J : Type}
theorem isRealEntryPolynomial_const (c : ℝ) :
    IsRealEntryPolynomial fun _ : J → Matrices.ComplexMatrix2.specialUnitary => (c : ℂ) :=
  ⟨⟨MvPolynomial.C (c : ℂ), fun u => by simp⟩, fun _ => Complex.ofReal_im c⟩
theorem isRealEntryPolynomial_add {F H : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ}
    (hF : IsRealEntryPolynomial F) (hH : IsRealEntryPolynomial H) :
    IsRealEntryPolynomial fun u => F u + H u := by
  obtain ⟨⟨p, hp⟩, hFr⟩ := hF
  obtain ⟨⟨q, hq⟩, hHr⟩ := hH
  exact ⟨⟨p + q, fun u => by simp only [hp u, hq u, map_add]⟩,
    fun u => by simp [Complex.add_im, hFr u, hHr u]⟩
theorem isRealEntryPolynomial_mul {F H : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ}
    (hF : IsRealEntryPolynomial F) (hH : IsRealEntryPolynomial H) :
    IsRealEntryPolynomial fun u => F u * H u := by apply _root_.YangMills.Construction.SpinHarmonics.DisjointUnionSplit.isRealEntryPolynomial_mul <;> assumption
theorem continuous_coord (a : J) (i k : Fin 2) :
    Continuous fun u : J → Matrices.ComplexMatrix2.specialUnitary =>
      (u a : Matrices.ComplexMatrix2) i k :=
  (continuous_subtype_val.comp (continuous_apply a)).matrix_elem i k
def entryRe (a : J) (i k : Fin 2) : C(J → Matrices.ComplexMatrix2.specialUnitary, ℝ) where
  toFun u := ((u a : Matrices.ComplexMatrix2) i k).re
  continuous_toFun := Complex.continuous_re.comp (continuous_coord a i k)
def entryIm (a : J) (i k : Fin 2) : C(J → Matrices.ComplexMatrix2.specialUnitary, ℝ) where
  toFun u := ((u a : Matrices.ComplexMatrix2) i k).im
  continuous_toFun := Complex.continuous_im.comp (continuous_coord a i k)
theorem isRealEntryPolynomial_entryRe (a : J) (i k : Fin 2) :
    IsRealEntryPolynomial fun u => ((entryRe a i k u : ℝ) : ℂ) := by
  refine ⟨⟨MvPolynomial.C (1 / 2 : ℂ) *
    (MvPolynomial.X (.inl (a, i, k)) + MvPolynomial.X (.inr (a, i, k))), fun u => ?_⟩,
    fun _ => Complex.ofReal_im _⟩
  have h := Complex.add_conj ((u a : Matrices.ComplexMatrix2) i k)
  simp only [map_mul, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X, entryEval,
    Complex.star_def, h]
  simp [entryRe]
theorem isRealEntryPolynomial_entryIm (a : J) (i k : Fin 2) :
    IsRealEntryPolynomial fun u => ((entryIm a i k u : ℝ) : ℂ) := by
  refine ⟨⟨MvPolynomial.C (-Complex.I / 2 : ℂ) *
    (MvPolynomial.X (.inl (a, i, k)) - MvPolynomial.X (.inr (a, i, k))), fun u => ?_⟩,
    fun _ => Complex.ofReal_im _⟩
  have h := Complex.sub_conj ((u a : Matrices.ComplexMatrix2) i k)
  simp only [map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X, entryEval,
    Complex.star_def, h]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [entryIm, ContinuousMap.coe_mk]
  push_cast
  linear_combination (((u a : Matrices.ComplexMatrix2) i k).im : ℂ) * hI
theorem exists_coord_ne {u w : J → Matrices.ComplexMatrix2.specialUnitary} (h : u ≠ w) :
    ∃ a i k, (u a : Matrices.ComplexMatrix2) i k ≠ (w a : Matrices.ComplexMatrix2) i k := by
  by_contra hc
  push Not at hc
  exact h (funext fun a => Subtype.ext (Matrix.ext (hc a)))
theorem exists_separating_realPoly {u w : J → Matrices.ComplexMatrix2.specialUnitary}
    (h : u ≠ w) :
    ∃ f : C(J → Matrices.ComplexMatrix2.specialUnitary, ℝ),
      (IsRealEntryPolynomial fun v => ((f v : ℝ) : ℂ)) ∧ f u ≠ f w := by
  obtain ⟨a, i, k, hne⟩ := exists_coord_ne h
  by_cases hre : ((u a : Matrices.ComplexMatrix2) i k).re =
      ((w a : Matrices.ComplexMatrix2) i k).re
  · exact ⟨entryIm a i k, isRealEntryPolynomial_entryIm a i k,
      fun him => hne (Complex.ext hre him)⟩
  · exact ⟨entryRe a i k, isRealEntryPolynomial_entryRe a i k, hre⟩
variable (J) in
def realEntryPolySubalgebra :
    Subalgebra ℝ C(J → Matrices.ComplexMatrix2.specialUnitary, ℝ) where
  carrier := {f | IsRealEntryPolynomial fun u => ((f u : ℝ) : ℂ)}
  mul_mem' {f g} hf hg := by
    have e : (fun u => (((f * g) u : ℝ) : ℂ)) = fun u => ((f u : ℝ) : ℂ) * ((g u : ℝ) : ℂ) := by
      funext u
      simp
    change IsRealEntryPolynomial fun u => (((f * g) u : ℝ) : ℂ)
    rw [e]
    exact isRealEntryPolynomial_mul hf hg
  add_mem' {f g} hf hg := by
    have e : (fun u => (((f + g) u : ℝ) : ℂ)) = fun u => ((f u : ℝ) : ℂ) + ((g u : ℝ) : ℂ) := by
      funext u
      simp
    change IsRealEntryPolynomial fun u => (((f + g) u : ℝ) : ℂ)
    rw [e]
    exact isRealEntryPolynomial_add hf hg
  algebraMap_mem' c := by
    have e : (fun u => (((algebraMap ℝ C(J → Matrices.ComplexMatrix2.specialUnitary, ℝ) c) u :
        ℝ) : ℂ)) = fun _ => (c : ℂ) := by
      funext u
      simp
    change IsRealEntryPolynomial fun u =>
      (((algebraMap ℝ C(J → Matrices.ComplexMatrix2.specialUnitary, ℝ) c) u : ℝ) : ℂ)
    rw [e]
    exact isRealEntryPolynomial_const c
theorem realPolyDenseOnPowers_holds : RealPolyDenseOnPowers := by
  intro J _ _
  refine ⟨isRealEntryPolynomial_const, fun F H hF hH =>
    ⟨isRealEntryPolynomial_add hF hH, isRealEntryPolynomial_mul hF hH⟩,
    fun c F hF => isRealEntryPolynomial_mul (isRealEntryPolynomial_const c) hF,
    fun u w h => ?_, fun f ε hε => ?_⟩
  · obtain ⟨f, hf, hne⟩ := exists_separating_realPoly h
    exact ⟨_, hf, fun e => hne (Complex.ofReal_injective e)⟩
  · have hsep : (realEntryPolySubalgebra J).SeparatesPoints := fun u w h => by
      obtain ⟨f, hf, hne⟩ := exists_separating_realPoly h
      exact ⟨f, ⟨f, hf, rfl⟩, hne⟩
    have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
      (realEntryPolySubalgebra J) hsep
    have hf : f ∈ closure ((realEntryPolySubalgebra J :
        Subalgebra ℝ C(J → Matrices.ComplexMatrix2.specialUnitary, ℝ)) :
        Set C(J → Matrices.ComplexMatrix2.specialUnitary, ℝ)) := by
      rw [← Subalgebra.topologicalClosure_coe, htop]
      trivial
    obtain ⟨g, hg, hd⟩ := Metric.mem_closure_iff.mp hf ε hε
    refine ⟨fun u => ((g u : ℝ) : ℂ), hg, fun u => ?_⟩
    have h₁ : dist (f u) (g u) < ε := (ContinuousMap.dist_apply_le_dist u).trans_lt hd
    rw [Real.dist_eq, abs_sub_comm] at h₁
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact h₁
end YangMills.Construction.SpinHarmonics.RealPolyDense
end
