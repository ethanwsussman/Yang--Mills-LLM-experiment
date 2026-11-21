import YangMills.Construction.LawInAState.ReflectionKernelAtADistanceProof
import YangMills.Construction.Constants.HeatKernelNumbersFinite
import YangMills.Construction.FreeKernel.HeatKernelsAndTheGreensFunctions
import YangMills.Construction.FreeKernel.MultipliersSymbolCharactersAndGreensFunctionsOnClasses
import YangMills.Construction.FreeKernel.OneDimensionalKernelEstimates
import YangMills.Construction.FreeKernel.SymbolsAddUpAndKernelsAsFourierIntegrals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.HeatKernelGreen
open MeasureTheory YangMills.Construction.FourDimKernel YangMills.Construction.Constants.HeatKernel
open YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint
open YangMills.Construction.PeriodicLattice.VectorClasses
open scoped ComplexOrder
namespace Periodize
open YangMills.Construction.PeriodicLattice.DiscreteTorusData
theorem hasSum_fintype_prod_of_summable_norm : ∀ (m : ℕ) (f : Fin m → ℤ → ℂ) (a : Fin m → ℂ),
    (∀ i, Summable fun j => ‖f i j‖) → (∀ i, HasSum (f i) (a i)) →
    (Summable fun z : Fin m → ℤ => ‖∏ i, f i (z i)‖) ∧
      HasSum (fun z : Fin m → ℤ => ∏ i, f i (z i)) (∏ i, a i) := by
  intro m
  induction m with
  | zero =>
    intro f a _ _
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact ⟨(hasSum_unique _).summable, by simp⟩
  | succ m ih =>
    intro f a hs h
    obtain ⟨ihs, ihh⟩ := ih (fun i => f i.succ) (fun i => a i.succ) (fun i => hs _) (fun i => h _)
    obtain ⟨e, he⟩ : ∃ e : ℤ × (Fin m → ℤ) ≃ (Fin (m + 1) → ℤ),
        ∀ p, e p = Fin.cons (α := fun _ => ℤ) p.1 p.2 := ⟨Fin.consEquiv fun _ => ℤ, fun _ => rfl⟩
    have conv : ∀ p : ℤ × (Fin m → ℤ), (∏ i, f i (e p i)) =
        f 0 p.1 * ∏ i : Fin m, f i.succ (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [he]
    have key : HasSum (fun p : ℤ × (Fin m → ℤ) => f 0 p.1 * ∏ i : Fin m, f i.succ (p.2 i))
        (a 0 * ∏ i : Fin m, a i.succ) := by
      have h1 := (summable_mul_of_summable_norm (hs 0) ihs).hasSum
      rw [← tsum_mul_tsum_of_summable_norm (hs 0) ihs, (h 0).tsum_eq, ihh.tsum_eq] at h1
      exact h1
    have keyn : Summable (fun p : ℤ × (Fin m → ℤ) => ‖f 0 p.1 * ∏ i : Fin m, f i.succ (p.2 i)‖) := by
      have h2 := Summable.mul_of_nonneg (hs 0) ihs (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      exact h2.congr fun p => (norm_mul _ _).symm
    constructor
    · refine (e.summable_iff).1 ?_
      refine keyn.congr fun p => ?_
      simp only [Function.comp]
      rw [conv]
    · rw [Fin.prod_univ_succ]
      refine (e.hasSum_iff).1 ?_
      have : ((fun z : Fin (m + 1) → ℤ => ∏ i, f i (z i)) ∘ e) =
          fun p : ℤ × (Fin m → ℤ) => f 0 p.1 * ∏ i : Fin m, f i.succ (p.2 i) := funext conv
      rw [this]
      exact key
theorem expWave_neg (k : Fin 4 → ℝ) (z : Fin 4 → ℤ) :
    expWave (-k) z = Complex.exp (-(Complex.I * (wavePairing k z : ℝ))) := by
  have : wavePairing (-k) z = -wavePairing k z := by
    simp [wavePairing]
  simp only [expWave, this]
  push_cast
  ring_nf
theorem expWave_neg_eq_inv (k : Fin 4 → ℝ) (z : Fin 4 → ℤ) :
    expWave (-k) z = (expWave k z)⁻¹ := by
  rw [expWave_neg, expWave, Complex.exp_neg]
theorem expWave_mul_expWave_neg (k k' : Fin 4 → ℝ) (z : Fin 4 → ℤ) :
    expWave k' z * expWave (-k) z = expWave (k' - k) z := by
  have : wavePairing (k' - k) z = wavePairing k' z + wavePairing (-k) z := by
    simp only [wavePairing, ← Finset.sum_add_distrib, Pi.sub_apply, Pi.neg_apply]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [expWave, this]
  push_cast
  rw [← Complex.exp_add]
  ring_nf
theorem hasSum_latticeHeatKernel_fourier (hF : FreeKernel.symbolsAndFourierIntegrals)
    (hO : LatticeKernelBounds.OneDimensionalEstimates) {t : ℝ} (ht : 0 < t) (k : Fin 4 → ℝ) :
    HasSum
      (fun z : Fin 4 → ℤ =>
        latticeHeatKernel4 t z * Complex.exp (-(Complex.I * (wavePairing k z : ℝ))))
      ((Real.exp (-t * laplacianSymbol k) : ℝ) : ℂ) := by
  obtain ⟨-, -, -, -, hS, -⟩ := hO
  have h := (hasSum_fintype_prod_of_summable_norm 4
    (fun μ j => LatticeKernel.discreteHeatKernel t j *
      Complex.exp (-(Complex.I * (j : ℂ) * ((k μ : ℝ) : ℂ))))
    (fun μ => ((Real.exp (-t * LatticeKernel.laplacianSymbol (k μ)) : ℝ) : ℂ))
    (fun μ => (hS t ht (k μ)).1) (fun μ => (hS t ht (k μ)).2)).2
  have hval : (∏ μ, ((Real.exp (-t * LatticeKernel.laplacianSymbol (k μ)) : ℝ) : ℂ)) =
      ((Real.exp (-t * laplacianSymbol k) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod, ← Real.exp_sum, hF.1.2.1 k, Finset.mul_sum]
  rw [hval] at h
  have hfun : (fun z : Fin 4 → ℤ => ∏ μ, (LatticeKernel.discreteHeatKernel t (z μ) *
      Complex.exp (-(Complex.I * ((z μ : ℤ) : ℂ) * ((k μ : ℝ) : ℂ))))) =
      fun z : Fin 4 → ℤ =>
        latticeHeatKernel4 t z * Complex.exp (-(Complex.I * (wavePairing k z : ℝ))) := by
    funext z
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 2
    simp only [wavePairing]
    push_cast
    rw [Finset.sum_neg_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hfun] at h
  exact h
theorem tsum_eq_sum_residueCube_tsum {n : ℕ} [NeZero n] {h : (Fin 4 → ℤ) → ℂ} (hh : Summable h) :
    ∑' x, h x = ∑ N ∈ residueCube n, ∑' w : Fin 4 → ℤ, h (N + (n : ℤ) • w) := by
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hbij : Function.Bijective
      (fun p : (residueCube n) × (Fin 4 → ℤ) => (p.1 : Fin 4 → ℤ) + (n : ℤ) • p.2) := by
    constructor
    · rintro ⟨⟨N, hN⟩, w⟩ ⟨⟨N', hN'⟩, w'⟩ hEq
      simp only at hEq
      have hc : zmodClass n N = zmodClass n N' :=
        (zmodClass_eq_zmodClass_iff N N').2 ⟨w - w', by
          have : N' = N + (n : ℤ) • w - (n : ℤ) • w' := by rw [hEq]; abel
          rw [this, smul_sub]
          abel⟩
      have hNN : N = N' := by
        rw [← residueLift_zmodClass hN, hc, residueLift_zmodClass hN']
      subst hNN
      have hs : (n : ℤ) • w = (n : ℤ) • w' := add_left_cancel hEq
      have hw : w = w' := by
        funext μ
        have := congrFun hs μ
        simp only [Pi.smul_apply, smul_eq_mul] at this
        exact mul_left_cancel₀ hn this
      subst hw
      rfl
    · intro x
      obtain ⟨w, hw⟩ := (zmodClass_eq_zmodClass_iff (residueLift (zmodClass n x)) x).1 (zmodClass_residueLift _)
      exact ⟨(⟨residueLift (zmodClass n x), residueLift_mem_residueCube _⟩, w), hw.symm⟩
  let e := Equiv.ofBijective _ hbij
  have hs : Summable (h ∘ e) := (e.summable_iff).2 hh
  rw [← e.tsum_eq h]
  have := hs.tsum_prod
  simp only [Function.comp] at this
  rw [this, tsum_fintype]
  exact Finset.sum_coe_sort (residueCube n) fun N => ∑' w : Fin 4 → ℤ, h (N + (n : ℤ) • w)
def periodizedKernel (n : ℕ) (t : ℝ) (z : Fin 4 → ℤ) : ℂ :=
  ∑' w : Fin 4 → ℤ, latticeHeatKernel4 t (z + (n : ℤ) • w)
theorem summable_comp_translate {n : ℕ} [NeZero n] {h : (Fin 4 → ℤ) → ℂ} (hh : Summable h)
    (z : Fin 4 → ℤ) : Summable fun w : Fin 4 → ℤ => h (z + (n : ℤ) • w) := by
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  refine hh.comp_injective (i := fun w : Fin 4 → ℤ => z + (n : ℤ) • w) ?_
  intro w w' hEq
  have hs : (n : ℤ) • w = (n : ℤ) • w' := add_left_cancel hEq
  funext μ
  have := congrFun hs μ
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hn this
theorem isClassFunction_periodizedKernel {n : ℕ} (t : ℝ) :
    IsClassFunction n (periodizedKernel n t) := by
  intro N v
  simp only [periodizedKernel]
  rw [← (Equiv.addRight v).tsum_eq (fun w : Fin 4 → ℤ => latticeHeatKernel4 t (N + (n : ℤ) • w))]
  refine tsum_congr fun w => ?_
  simp only [Equiv.coe_addRight, smul_add]
  congr 1
  abel
theorem classSum_periodizedKernel_mul (hF : FreeKernel.symbolsAndFourierIntegrals)
    (hO : LatticeKernelBounds.OneDimensionalEstimates) {n : ℕ} [NeZero n] {t : ℝ} (ht : 0 < t)
    {k : Fin 4 → ℝ} (hk : IsClassFunction n (expWave k)) :
    classSum n (fun z => periodizedKernel n t z * expWave (-k) z) =
      ((Real.exp (-t * laplacianSymbol k) : ℝ) : ℂ) := by
  have hsum := hasSum_latticeHeatKernel_fourier hF hO ht k
  rw [← hsum.tsum_eq, tsum_eq_sum_residueCube_tsum (n := n) hsum.summable, classSum_eq_sum_residueCube]
  refine Finset.sum_congr rfl fun N _ => ?_
  simp only [periodizedKernel]
  rw [← tsum_mul_right]
  refine tsum_congr fun w => ?_
  rw [← expWave_neg, expWave_neg_eq_inv, expWave_neg_eq_inv, hk N w]
theorem classSum_torusHeatKernel_mul {n : ℕ} [NeZero n] (hC : ExpWaveCharacters n) (t : ℝ)
    {k : Fin 4 → ℝ} (hk : k ∈ momentumSet n) :
    classSum n (fun z => torusHeatKernel n t z * expWave (-k) z) =
      ((Real.exp (-t * laplacianSymbol k) : ℝ) : ℂ) := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hfin := momentumSet_finite (NeZero.ne n)
  obtain ⟨-, -, hort, -⟩ := hC
  have hexp : ∀ z, torusHeatKernel n t z = (1 / (n : ℂ) ^ 4) *
      ∑ k' ∈ hfin.toFinset, expWave k' z * ((Real.exp (-t * laplacianSymbol k') : ℝ) : ℂ) := by
    intro z
    rw [torusHeatKernel, finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [classSum_eq_sum_residueCube]
  simp only [hexp, mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hinner : ∀ k' ∈ hfin.toFinset,
      ∑ N ∈ residueCube n, expWave k' N * (((Real.exp (-t * laplacianSymbol k') : ℝ) : ℂ) *
        expWave (-k) N) =
      ((Real.exp (-t * laplacianSymbol k') : ℝ) : ℂ) *
        ((n : ℂ) ^ 4 * (FourVector.propIndicator (k' = k) : ℂ)) := by
    intro k' hk'
    have hk'' : k' ∈ momentumSet n := hfin.mem_toFinset.1 hk'
    rw [← hort k' hk'' k hk, classSum_eq_sum_residueCube, Finset.mul_sum]
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [← expWave_mul_expWave_neg]
    ring
  rw [Finset.sum_congr rfl hinner]
  simp only [FourVector.propIndicator]
  have hmem : k ∈ hfin.toFinset := hfin.mem_toFinset.2 hk
  rw [Finset.sum_eq_single k]
  · simp only [if_true, Complex.ofReal_one, mul_one]
    field_simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd hmem h
theorem periodicSummation_holds (hF : FreeKernel.symbolsAndFourierIntegrals)
    (hO : LatticeKernelBounds.OneDimensionalEstimates)
    (hT : PeriodicLattice.VectorClasses.FourierFactsAndGreenIdentities.Statement)
    (n : ℕ) (hn : 2 ≤ n) : PeriodicSummation n := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨-, -, hC, -, -⟩ := hT n hn
  intro t ht
  have hone : HasSum (latticeHeatKernel4 t) 1 := by
    have h0 := hasSum_latticeHeatKernel_fourier hF hO ht 0
    have hpair : ∀ z, wavePairing 0 z = 0 := fun z => by simp [wavePairing]
    have hsym : laplacianSymbol (0 : Fin 4 → ℝ) = 0 := by simp [laplacianSymbol]
    simpa [hpair, hsym] using h0
  refine ⟨fun z => ?_, hone, fun k => hasSum_latticeHeatKernel_fourier hF hO ht k, fun z => ?_⟩
  · obtain ⟨-, hP, -⟩ := hO
    refine Finset.prod_pos fun μ _ => ?_
    obtain ⟨him, hre⟩ := hP t ht (z μ)
    exact Complex.lt_def.2 ⟨by simpa using hre, by simpa using him.symm⟩
  · have hper : periodizedKernel n t = torusHeatKernel n t := by
      refine hC.2.2.2 _ _ (isClassFunction_periodizedKernel t) (isClassFunction_torusHeatKernel t) ?_
      intro k hk
      rw [classSum_periodizedKernel_mul hF hO ht (hC.2.1 k hk), classSum_torusHeatKernel_mul hC t hk]
    have hs := (summable_comp_translate (n := n) hone.summable z).hasSum
    have : (∑' w : Fin 4 → ℤ, latticeHeatKernel4 t (z + (n : ℤ) • w)) = torusHeatKernel n t z := by
      rw [← hper]; rfl
    rwa [this] at hs
end Periodize
namespace TorusTime
theorem integrableOn_const_mul_exp (w : ℂ) {ω : ℝ} (hω : 0 < ω) :
    IntegrableOn (fun t : ℝ => w * ((Real.exp (-t * ω) : ℝ) : ℂ)) (Set.Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => Real.exp (-ω * t)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hω
  have e : (fun t : ℝ => ((Real.exp (-t * ω) : ℝ) : ℂ)) =
      fun t => ((Real.exp (-ω * t) : ℝ) : ℂ) := by
    funext t; congr 2; ring
  have h2 : Integrable (fun t : ℝ => ((Real.exp (-t * ω) : ℝ) : ℂ))
      (volume.restrict (Set.Ioi 0)) := by
    rw [e]; exact Integrable.ofReal h
  exact h2.const_mul w
theorem integral_const_mul_exp (w : ℂ) {ω : ℝ} (hω : 0 < ω) :
    ∫ t in Set.Ioi (0 : ℝ), w * ((Real.exp (-t * ω) : ℝ) : ℂ) = w / (ω : ℂ) := by
  have h : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * ω) = 1 / ω := by
    have e := integral_exp_mul_Ioi (a := -ω) (by linarith) 0
    have e2 : (fun t : ℝ => Real.exp (-t * ω)) = fun t => Real.exp (-ω * t) := by
      funext t; ring_nf
    simp only [e2]
    rw [e]
    simp
  rw [MeasureTheory.integral_const_mul, integral_complex_ofReal, h]
  push_cast
  ring
theorem zero_mem_momentumSet (n : ℕ) : (0 : Fin 4 → ℝ) ∈ momentumSet n :=
  ⟨⟨0, by simp⟩, fun μ => ⟨by simpa using Real.pi_pos, by simpa using Real.pi_pos.le⟩⟩
theorem torusHeatKernel_sub_mean {n : ℕ} (hn : n ≠ 0) (t : ℝ) (z : Fin 4 → ℤ) :
    torusHeatKernel n t z - (n : ℂ) ^ (-4 : ℤ) =
      (1 / (n : ℂ) ^ 4) * ∑ k ∈ (momentumSet_finite hn).toFinset.erase 0,
        expWave k z * ((Real.exp (-t * laplacianSymbol k) : ℝ) : ℂ) := by
  have hmem : (0 : Fin 4 → ℝ) ∈ (momentumSet_finite hn).toFinset := by
    simpa using zero_mem_momentumSet n
  have h1 : expWave 0 z = 1 := by simp [expWave, wavePairing]
  have h0 : laplacianSymbol 0 = 0 := by simp [laplacianSymbol]
  rw [torusHeatKernel, finsum_mem_eq_finite_toFinset_sum _ (momentumSet_finite hn),
    ← Finset.add_sum_erase _ _ hmem, h1, h0]
  simp only [mul_zero, Real.exp_zero, Complex.ofReal_one, mul_one, mul_add]
  rw [zpow_neg]
  have : ((n : ℂ) ^ (4 : ℤ))⁻¹ = 1 / (n : ℂ) ^ 4 := by
    rw [one_div]; norm_cast
  rw [this]
  ring
theorem finsum_greenTerms_eq {n : ℕ} (hn : n ≠ 0) (z : Fin 4 → ℤ) :
    ∑ᶠ k ∈ momentumSet n \ {0}, expWave k z / (laplacianSymbol k : ℂ) =
      ∑ k ∈ (momentumSet_finite hn).toFinset.erase 0, expWave k z / (laplacianSymbol k : ℂ) := by
  have hs : momentumSet n \ {0} = ↑((momentumSet_finite hn).toFinset.erase 0) := by
    ext k; simp
  rw [hs, finsum_mem_coe_finset]
theorem laplacianSymbol_pos_of_mem {n : ℕ} (hn : n ≠ 0) {k : Fin 4 → ℝ}
    (hk : k ∈ (momentumSet_finite hn).toFinset.erase 0) : 0 < laplacianSymbol k := by
  have h := Finset.mem_erase.1 hk
  exact laplacianSymbol_pos ⟨by simpa using h.2, by simpa using h.1⟩
theorem integrableOn_torusHeatKernel_sub_mean {n : ℕ} (hn : n ≠ 0) (z : Fin 4 → ℤ) :
    IntegrableOn (fun t : ℝ => torusHeatKernel n t z - (n : ℂ) ^ (-4 : ℤ)) (Set.Ioi 0) := by
  simp only [torusHeatKernel_sub_mean hn]
  refine Integrable.const_mul ?_ _
  exact integrable_finsetSum _ fun k hk => integrableOn_const_mul_exp _ (laplacianSymbol_pos_of_mem hn hk)
theorem greenOnVectors_eq_integral {n : ℕ} [NeZero n] (z : Fin 4 → ℤ) :
    greenOnVectors n z =
      ∫ t in Set.Ioi (0 : ℝ), (torusHeatKernel n t z - (n : ℂ) ^ (-4 : ℤ)) := by
  have hn : n ≠ 0 := NeZero.ne n
  simp only [torusHeatKernel_sub_mean hn]
  rw [MeasureTheory.integral_const_mul, greenOnVectors_apply, finsum_greenTerms_eq hn,
    MeasureTheory.integral_finsetSum _
      fun k hk => integrableOn_const_mul_exp _ (laplacianSymbol_pos_of_mem hn hk)]
  congr 1
  exact Finset.sum_congr rfl fun k hk => (integral_const_mul_exp _ (laplacianSymbol_pos_of_mem hn hk)).symm
theorem mixedSecondDiff_eq (ν ν' : Fin 4) (f : (Fin 4 → ℤ) → ℂ) (z : Fin 4 → ℤ) :
    mixedSecondDiff ν ν' f z =
      f (z + unitVector ν) - f (z + unitVector ν - unitVector ν') - f z + f (z - unitVector ν') := by
  simp only [mixedSecondDiff, forwardDiff, backwardDiff]
  ring
theorem torusTimeIntegrals_holds (n : ℕ) (hn : 2 ≤ n) (ν ν' : Fin 4) : TorusTimeIntegrals n ν ν' := by
  have : NeZero n := ⟨by omega⟩
  have hn0 : n ≠ 0 := by omega
  intro z
  refine ⟨⟨integrableOn_torusHeatKernel_sub_mean hn0 z, greenOnVectors_eq_integral z⟩, ?_⟩
  set c : ℂ := (n : ℂ) ^ (-4 : ℤ)
  set F : (Fin 4 → ℤ) → ℝ → ℂ := fun y t => torusHeatKernel n t y - c with hFdef
  have hI : ∀ y, IntegrableOn (F y) (Set.Ioi 0) := fun y => integrableOn_torusHeatKernel_sub_mean hn0 y
  have hfun : (fun t : ℝ => mixedSecondDiff ν ν' (torusHeatKernel n t) z) =
      fun t => F (z + unitVector ν) t - F (z + unitVector ν - unitVector ν') t - F z t +
        F (z - unitVector ν') t := by
    funext t
    simp only [mixedSecondDiff_eq, hFdef]
    ring
  rw [hfun]
  have h12 := (hI (z + unitVector ν)).sub (hI (z + unitVector ν - unitVector ν'))
  have h123 := h12.sub (hI z)
  refine ⟨h123.add (hI (z - unitVector ν')), ?_⟩
  rw [mixedSecondDiff_eq]
  have hG : ∀ y, greenOnVectors n y = ∫ t in Set.Ioi (0 : ℝ), F y t :=
    fun y => greenOnVectors_eq_integral y
  rw [hG, hG, hG, hG]
  have a1 := integral_sub (hI (z + unitVector ν)) (hI (z + unitVector ν - unitVector ν'))
  have a2 := integral_sub h12 (hI z)
  have a3 := integral_add h123 (hI (z - unitVector ν'))
  simp only [Pi.sub_apply] at a2 a3
  rw [a3, a2, a1]
end TorusTime
namespace Continuum
def sqSum (u : Fin 4 → ℝ) : ℝ := ∑ μ, u μ ^ 2
theorem realVecNorm_sq (u : Fin 4 → ℝ) : realVecNorm u ^ 2 = sqSum u := by
  have h : 0 ≤ FourVector.inner4 u u :=
    Finset.sum_nonneg fun μ _ => mul_self_nonneg (u μ)
  simp only [realVecNorm, FourVector.euclidNorm]
  rw [Real.sq_sqrt h]
  simp [FourVector.inner4, sqSum, pow_two]
def gaussianClosedForm (t : ℝ) (u : Fin 4 → ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-2 : ℤ) * Real.exp (-sqSum u / (4 * t))
theorem gaussianHeatKernel4_eq_closedForm (hF : FreeKernel.symbolsAndFourierIntegrals)
    {t : ℝ} (ht : 0 < t) : gaussianHeatKernel4 t = gaussianClosedForm t := by
  funext u
  rw [hF.1.2.2.2.2 t u ht, realVecNorm_sq, gaussianClosedForm]
theorem hasDerivAt_coord_line (x : Fin 4 → ℝ) (ν μ : Fin 4) :
    HasDerivAt (fun s : ℝ => (x + s • FourVector.unitVec ν) μ)
      (FourVector.unitVec ν μ) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const (FourVector.unitVec ν μ)).const_add (x μ)
  simpa using h
theorem hasDerivAt_sqSum_line (x : Fin 4 → ℝ) (ν : Fin 4) :
    HasDerivAt (fun s : ℝ => sqSum (x + s • FourVector.unitVec ν)) (2 * x ν) 0 := by
  have h : HasDerivAt (fun s : ℝ => ∑ μ, ((x + s • FourVector.unitVec ν) μ) ^ 2)
      (∑ μ, (2 : ℕ) * ((x + (0 : ℝ) • FourVector.unitVec ν) μ) ^ (2 - 1) *
        FourVector.unitVec ν μ) 0 :=
    HasDerivAt.fun_sum fun μ _ => (hasDerivAt_coord_line x ν μ).pow 2
  have e : (∑ μ, ((2 : ℕ) : ℝ) * ((x + (0 : ℝ) • FourVector.unitVec ν) μ) ^ (2 - 1) *
      FourVector.unitVec ν μ) = 2 * x ν := by
    simp [FourVector.unitVec, Pi.single_apply]
  rw [e] at h
  exact h
theorem unitVec_apply (ν ν' : Fin 4) :
    FourVector.unitVec ν ν' = FourVector.kronecker ν ν' := by
  by_cases h : ν = ν'
  · subst h
    simp [FourVector.unitVec, FourVector.kronecker,
      FourVector.propIndicator]
  · have h' : ν' ≠ ν := fun e => h e.symm
    simp [FourVector.unitVec, FourVector.kronecker,
      FourVector.propIndicator, h, h']
theorem hasDerivAt_closedForm_line {t : ℝ} (x : Fin 4 → ℝ) (ν : Fin 4) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => gaussianClosedForm t (x + s • FourVector.unitVec ν))
      (-(x ν) / (2 * t) * gaussianClosedForm t x) 0 := by
  have h := (((hasDerivAt_sqSum_line x ν).neg.div_const (4 * t)).exp).const_mul
    ((4 * Real.pi * t) ^ (-2 : ℤ))
  have e : (4 * Real.pi * t) ^ (-2 : ℤ) *
      (Real.exp (-sqSum (x + (0 : ℝ) • FourVector.unitVec ν) / (4 * t)) *
        (-(2 * x ν) / (4 * t))) = -(x ν) / (2 * t) * gaussianClosedForm t x := by
    simp only [zero_smul, add_zero, gaussianClosedForm]
    have : t ≠ 0 := ht.ne'
    field_simp
    ring
  have h' : HasDerivAt (fun s : ℝ => gaussianClosedForm t (x + s • FourVector.unitVec ν))
      ((4 * Real.pi * t) ^ (-2 : ℤ) *
      (Real.exp (-sqSum (x + (0 : ℝ) • FourVector.unitVec ν) / (4 * t)) *
        (-(2 * x ν) / (4 * t)))) 0 := h
  rw [e] at h'
  exact h'
theorem coordPartialDeriv_closedForm {t : ℝ} (ν : Fin 4) (ht : 0 < t) :
    FourVector.coordPartialDeriv ν (gaussianClosedForm t) =
      fun x => -(x ν) / (2 * t) * gaussianClosedForm t x :=
  funext fun x => HasLineDerivAt.lineDeriv (hasDerivAt_closedForm_line x ν ht)
theorem mixedSecondPartial_gaussian (hF : FreeKernel.symbolsAndFourierIntegrals) (ν ν' : Fin 4)
    (t : ℝ) (u : Fin 4 → ℝ) (ht : 0 < t) :
    mixedSecondPartial ν ν' (gaussianHeatKernel4 t) u =
      gaussianHeatKernel4 t u *
        (u ν * u ν' / (4 * t ^ 2) - FourVector.kronecker ν ν' / (2 * t)) := by
  rw [gaussianHeatKernel4_eq_closedForm hF ht, mixedSecondPartial, coordPartialDeriv_closedForm ν' ht]
  have h1 : HasDerivAt (fun s : ℝ => -((u + s • FourVector.unitVec ν) ν') / (2 * t))
      (-(FourVector.unitVec ν ν') / (2 * t)) 0 :=
    (hasDerivAt_coord_line u ν ν').neg.div_const (2 * t)
  have h2 := h1.mul (hasDerivAt_closedForm_line u ν ht)
  have h3 : HasLineDerivAt ℝ (fun x : Fin 4 → ℝ => -(x ν') / (2 * t) * gaussianClosedForm t x) _ u
      (FourVector.unitVec ν) := h2
  rw [FourVector.coordPartialDeriv, h3.lineDeriv, unitVec_apply]
  simp only [zero_smul, add_zero]
  have : t ≠ 0 := ht.ne'
  field_simp
  ring
theorem integral_inv_pow_mul_exp (a : ℝ) (ha : 0 < a) (κ : ℕ) :
    IntegrableOn (fun t : ℝ => (t⁻¹) ^ (κ + 2) * Real.exp (-(a * t⁻¹))) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), (t⁻¹) ^ (κ + 2) * Real.exp (-(a * t⁻¹)) =
        (κ.factorial : ℝ) / a ^ (κ + 1) := by
  set f : ℝ → ℝ := fun w => w ^ (((κ : ℝ) + 1) - 1) * Real.exp (-(a * w)) with hf
  have hp : (-1 : ℝ) ≠ 0 := by norm_num
  have hfi : IntegrableOn f (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := ((κ : ℝ) + 1) - 1) (b := a)
      (by linarith) one_pos ha
    refine h.congr_fun (fun w _ => ?_) measurableSet_Ioi
    simp [hf, Real.rpow_one]
  have hcomp : ∀ x ∈ Set.Ioi (0 : ℝ), (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • f (x ^ (-1 : ℝ)) =
      (x⁻¹) ^ (κ + 2) * Real.exp (-(a * x⁻¹)) := by
    intro x hx
    have hx' : 0 < x := hx
    have h1 : x ^ ((-1 : ℝ) - 1) = (x⁻¹) ^ 2 := by
      rw [show ((-1 : ℝ) - 1) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx'.le,
        Real.rpow_natCast, inv_pow]
    have h2 : (x⁻¹) ^ (((κ : ℝ) + 1) - 1) = (x⁻¹) ^ κ := by
      rw [add_sub_cancel_right, Real.rpow_natCast]
    simp only [hf, Real.rpow_neg_one, abs_neg, abs_one, one_mul, smul_eq_mul, h1, h2]
    ring
  constructor
  · exact ((integrableOn_Ioi_comp_rpow_iff f hp).2 hfi).congr_fun hcomp measurableSet_Ioi
  · rw [← setIntegral_congr_fun measurableSet_Ioi hcomp, integral_comp_rpow_Ioi f hp]
    have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (κ : ℝ) + 1) (r := a)
      (by linarith) ha
    simp only [hf]
    rw [hi, Real.Gamma_nat_eq_factorial,
      show ((κ : ℝ) + 1) = ((κ + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [one_div, inv_pow]
    field_simp
theorem sqSum_pos {u : Fin 4 → ℝ} (hu : u ≠ 0) : 0 < sqSum u := by apply _root_.YangMills.Construction.ReflectionKernel.normSq_pos <;> assumption
theorem gaussian_eq_gamma_form (hF : FreeKernel.symbolsAndFourierIntegrals)
    (u : Fin 4 → ℝ) {t : ℝ} (ht : 0 < t) :
    gaussianHeatKernel4 t u = 1 / (16 * Real.pi ^ 2) *
      ((t⁻¹) ^ (0 + 2) * Real.exp (-(sqSum u / 4 * t⁻¹))) := by
  rw [gaussianHeatKernel4_eq_closedForm hF ht, gaussianClosedForm]
  have e : -sqSum u / (4 * t) = -(sqSum u / 4 * t⁻¹) := by
    field_simp
  rw [e, zpow_neg]
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  have : t ≠ 0 := ht.ne'
  norm_cast
  simp only [inv_pow]
  field_simp
  ring
theorem hessian_eq_gamma_form (hF : FreeKernel.symbolsAndFourierIntegrals) (ν ν' : Fin 4)
    (u : Fin 4 → ℝ) {t : ℝ} (ht : 0 < t) :
    mixedSecondPartial ν ν' (gaussianHeatKernel4 t) u =
      1 / (16 * Real.pi ^ 2) * (u ν * u ν' / 4) *
          ((t⁻¹) ^ (2 + 2) * Real.exp (-(sqSum u / 4 * t⁻¹))) -
        1 / (16 * Real.pi ^ 2) * (FourVector.kronecker ν ν' / 2) *
          ((t⁻¹) ^ (1 + 2) * Real.exp (-(sqSum u / 4 * t⁻¹))) := by
  rw [mixedSecondPartial_gaussian hF ν ν' t u ht, gaussian_eq_gamma_form hF u ht]
  have : t ≠ 0 := ht.ne'
  simp only [inv_pow]
  field_simp
  ring
theorem continuumTimeIntegrals_holds (hF : FreeKernel.symbolsAndFourierIntegrals)
    (hT : PeriodicLattice.VectorClasses.FourierFactsAndGreenIdentities.Statement) (ν ν' : Fin 4) :
    ContinuumTimeIntegrals ν ν' := by
  intro u hu
  have hS := sqSum_pos hu
  have ha : 0 < sqSum u / 4 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  obtain ⟨i0, v0⟩ := integral_inv_pow_mul_exp _ ha 0
  obtain ⟨i1, v1⟩ := integral_inv_pow_mul_exp _ ha 1
  obtain ⟨i2, v2⟩ := integral_inv_pow_mul_exp _ ha 2
  have c0 : ∀ t ∈ Set.Ioi (0 : ℝ), 1 / (16 * Real.pi ^ 2) *
      ((t⁻¹) ^ (0 + 2) * Real.exp (-(sqSum u / 4 * t⁻¹))) = gaussianHeatKernel4 t u :=
    fun t ht => (gaussian_eq_gamma_form hF u ht).symm
  have c2 : ∀ t ∈ Set.Ioi (0 : ℝ),
      1 / (16 * Real.pi ^ 2) * (u ν * u ν' / 4) *
          ((t⁻¹) ^ (2 + 2) * Real.exp (-(sqSum u / 4 * t⁻¹))) -
        1 / (16 * Real.pi ^ 2) * (FourVector.kronecker ν ν' / 2) *
          ((t⁻¹) ^ (1 + 2) * Real.exp (-(sqSum u / 4 * t⁻¹))) =
      mixedSecondPartial ν ν' (gaussianHeatKernel4 t) u :=
    fun t ht => (hessian_eq_gamma_form hF ν ν' u ht).symm
  have j2 := i2.const_mul (1 / (16 * Real.pi ^ 2) * (u ν * u ν' / 4))
  have j1 := i1.const_mul (1 / (16 * Real.pi ^ 2) * (FourVector.kronecker ν ν' / 2))
  have hlen : FourVector.euclidNorm u ^ 2 = sqSum u := realVecNorm_sq u
  refine ⟨⟨IntegrableOn.congr_fun (i0.const_mul _) c0 measurableSet_Ioi, ?_⟩,
    ⟨IntegrableOn.congr_fun (j2.sub j1) c2 measurableSet_Ioi, ?_⟩⟩
  · rw [← setIntegral_congr_fun measurableSet_Ioi c0, integral_const_mul, v0, continuumGreenFunction_eq,
      hlen]
    simp only [Nat.factorial_zero, Nat.cast_one]
    field_simp
    ring
  · rw [← setIntegral_congr_fun measurableSet_Ioi c2, integral_sub j2 j1, integral_const_mul,
      integral_const_mul, v1, v2]
    have hd := ((hT 2 (by norm_num)).2.2.2.2 ν ν' u hu).2.2
    have h4 : FourVector.euclidNorm u ^ 4 = sqSum u ^ 2 := by
      rw [← hlen]; ring
    rw [mixedSecondPartial, hd, h4, hlen]
    simp only [Nat.factorial]
    push_cast
    field_simp
    ring
theorem nearDiagonalBound_holds (hF : FreeKernel.symbolsAndFourierIntegrals) (ν ν' : Fin 4) :
    NearDiagonalBound ν ν' := by
  intro t u ht hu
  rw [mixedSecondPartial_gaussian hF ν ν' t u ht]
  rw [realVecNorm_sq] at hu
  have hsq : ∀ μ, u μ ^ 2 ≤ sqSum u := fun μ =>
    Finset.single_le_sum (f := fun μ => u μ ^ 2) (fun ν _ => sq_nonneg (u ν)) (Finset.mem_univ μ)
  have hprod : |u ν * u ν'| ≤ t := by
    have h1 := hsq ν
    have h2 := hsq ν'
    refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [sq_nonneg (u ν + u ν'), sq_nonneg (u ν - u ν')]
  have hδ : |FourVector.kronecker ν ν'| ≤ 1 := by
    by_cases h : ν = ν' <;>
      simp [FourVector.kronecker, FourVector.propIndicator, h]
  have hker : |gaussianHeatKernel4 t u| ≤ (4 * Real.pi * t) ^ (-2 : ℤ) := by
    rw [gaussianHeatKernel4_eq_closedForm hF ht, gaussianClosedForm]
    have hp : 0 < (4 * Real.pi * t) ^ (-2 : ℤ) := by positivity
    rw [abs_of_pos (by positivity)]
    have he : Real.exp (-sqSum u / (4 * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ sqSum u := Finset.sum_nonneg fun μ _ => sq_nonneg (u μ)
      have : 0 ≤ sqSum u / (4 * t) := by positivity
      rw [neg_div]
      linarith
    nlinarith
  have hbr : |u ν * u ν' / (4 * t ^ 2) - FourVector.kronecker ν ν' / (2 * t)| ≤
      3 / (4 * t) := by
    calc _ ≤ |u ν * u ν' / (4 * t ^ 2)| + |FourVector.kronecker ν ν' / (2 * t)| :=
          abs_sub _ _
      _ = |u ν * u ν'| / (4 * t ^ 2) + |FourVector.kronecker ν ν'| / (2 * t) := by
          rw [abs_div, abs_div, abs_of_pos (by positivity : 0 < 4 * t ^ 2),
            abs_of_pos (by positivity : 0 < 2 * t)]
      _ ≤ t / (4 * t ^ 2) + 1 / (2 * t) := by gcongr
      _ = 3 / (4 * t) := by field_simp; ring
  rw [abs_mul]
  calc _ ≤ (4 * Real.pi * t) ^ (-2 : ℤ) * (3 / (4 * t)) :=
        mul_le_mul hker hbr (abs_nonneg _) (by positivity)
    _ = lowerDiagonalConstant * t ^ (-3 : ℤ) := by
        simp only [lowerDiagonalConstant, zpow_neg]
        norm_cast
        field_simp
        ring
end Continuum
namespace SmallTime
theorem norm_discreteHeatKernel_eq_re (hpos : LatticeKernelBounds.KernelPositive) {t : ℝ} (ht : 0 < t)
    (j : ℤ) : ‖LatticeKernel.discreteHeatKernel t j‖ = (LatticeKernel.discreteHeatKernel t j).re := by
  obtain ⟨him, hre⟩ := hpos t ht j
  have h : LatticeKernel.discreteHeatKernel t j = ((LatticeKernel.discreteHeatKernel t j).re : ℂ) :=
    Complex.ext (by simp) (by simp [him])
  conv_lhs => rw [h]
  rw [Complex.norm_real, Real.norm_of_nonneg hre.le]
theorem norm_discreteHeatKernel_le_one (hpos : LatticeKernelBounds.KernelPositive)
    (hsum : LatticeKernelBounds.KernelSumsToOne) {t : ℝ} (ht : 0 < t) (j : ℤ) :
    ‖LatticeKernel.discreteHeatKernel t j‖ ≤ 1 := by
  rw [norm_discreteHeatKernel_eq_re hpos ht]
  have h := Complex.reCLM.hasSum (hsum t ht)
  have h' := le_hasSum h j (fun i _ => (hpos t ht i).2.le)
  simpa using h'
theorem norm_latticeHeatKernel4_le (hpos : LatticeKernelBounds.KernelPositive)
    (hsum : LatticeKernelBounds.KernelSumsToOne)
    (hsh : LatticeKernelBounds.ShortTimeBound) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (z : Fin 4 → ℤ) (μ₀ : Fin 4) :
    ‖latticeHeatKernel4 t z‖ ≤ shiftConstant / ((z μ₀).natAbs.factorial : ℝ) := by
  have hprod : ‖latticeHeatKernel4 t z‖ = ∏ μ, ‖LatticeKernel.discreteHeatKernel t (z μ)‖ := by
    simp [latticeHeatKernel4]
  rw [hprod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ₀)]
  have h1 : ∏ μ ∈ Finset.univ.erase μ₀, ‖LatticeKernel.discreteHeatKernel t (z μ)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun μ _ => norm_discreteHeatKernel_le_one hpos hsum ht _)
  have h2 : ‖LatticeKernel.discreteHeatKernel t (z μ₀)‖ ≤
      shiftConstant / ((z μ₀).natAbs.factorial : ℝ) := by
    rw [norm_discreteHeatKernel_eq_re hpos ht]
    refine (hsh t ht ht1 (z μ₀)).trans ?_
    have hc : 0 ≤ shiftConstant := (Real.exp_pos 1).le
    have hp : t ^ (z μ₀).natAbs ≤ 1 := pow_le_one₀ ht.le ht1
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc shiftConstant * (t ^ (z μ₀).natAbs * (((z μ₀).natAbs.factorial : ℝ))⁻¹)
        ≤ shiftConstant * (1 * (((z μ₀).natAbs.factorial : ℝ))⁻¹) := by gcongr
      _ = shiftConstant * (((z μ₀).natAbs.factorial : ℝ))⁻¹ := by ring
  calc _ ≤ ‖LatticeKernel.discreteHeatKernel t (z μ₀)‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ _ := by simpa using h2
theorem intVecNorm_le_of_coord_le (z : Fin 4 → ℤ) (l : ℕ) (h : ∀ μ, |(z μ : ℝ)| ≤ (l : ℝ) + 1) :
    intVecNorm z ≤ 2 * ((l : ℝ) + 1) := by
  have hsq : ∀ μ, (z μ : ℝ) * (z μ : ℝ) ≤ ((l : ℝ) + 1) ^ 2 := fun μ => by
    have := sq_le_sq' (by linarith [(abs_le.1 (h μ)).1]) (abs_le.1 (h μ)).2
    nlinarith
  simp only [intVecNorm, FourVector.euclidNorm, FourVector.inner4]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [Fin.sum_univ_four]
  nlinarith [hsq 0, hsq 1, hsq 2, hsq 3]
theorem factorial_term_le {m : ℕ} (hC : gaussianComparison m ≠ ⊤) (l : ℕ) :
    4 * shiftConstant * ((2 * (l : ℝ) + 3) ^ m / (l.factorial : ℝ)) ≤ (gaussianComparison m).toReal := by
  have hc : 0 ≤ 4 * shiftConstant := by
    have : 0 < shiftConstant := Real.exp_pos 1
    positivity
  have h1 : ENNReal.ofReal (4 * shiftConstant) *
      ENNReal.ofReal ((2 * (l : ℝ) + 3) ^ m / (l.factorial : ℝ)) ≤ gaussianComparison m := by
    unfold gaussianComparison
    refine le_trans ?_ (le_trans (le_max_left _ _) (le_max_left _ _))
    gcongr
    exact le_iSup (fun l : ℕ => ENNReal.ofReal ((2 * (l : ℝ) + 3) ^ m / (l.factorial : ℝ))) l
  rw [← ENNReal.ofReal_mul hc] at h1
  exact (ENNReal.ofReal_le_iff_le_toReal hC).1 h1
theorem gaussian_term_le {m : ℕ} (hC : gaussianComparison m ≠ ⊤) {y y' : ℝ} (hy : 0 ≤ y) (hy' : 0 ≤ y') :
    1 / (16 * Real.pi ^ 2) * ((y ^ 4 + y ^ 3) * Real.exp (-(y / 8))) *
      ((1 + y') ^ m * Real.exp (-(y' ^ 2 / 8))) ≤ (gaussianComparison m).toReal := by
  have hc : 0 ≤ 1 / (16 * Real.pi ^ 2) := by positivity
  have hA : 0 ≤ (y ^ 4 + y ^ 3) * Real.exp (-(y / 8)) := by positivity
  have h1 : ENNReal.ofReal (1 / (16 * Real.pi ^ 2)) *
      ENNReal.ofReal ((y ^ 4 + y ^ 3) * Real.exp (-(y / 8))) *
      ENNReal.ofReal ((1 + y') ^ m * Real.exp (-(y' ^ 2 / 8))) ≤ gaussianComparison m := by
    unfold gaussianComparison
    refine le_trans ?_ (le_trans (le_max_right _ _) (le_max_left _ _))
    gcongr
    · exact le_iSup₂ (f := fun (y : ℝ) (_ : 0 ≤ y) =>
        ENNReal.ofReal ((y ^ 4 + y ^ 3) * Real.exp (-(y / 8)))) y hy
    · exact le_iSup₂ (f := fun (y : ℝ) (_ : 0 ≤ y) =>
        ENNReal.ofReal ((1 + y) ^ m * Real.exp (-(y ^ 2 / 8)))) y' hy'
  rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul (mul_nonneg hc hA)] at h1
  exact (ENNReal.ofReal_le_iff_le_toReal hC).1 h1
theorem intVecNorm_nonneg (z : Fin 4 → ℤ) : 0 ≤ intVecNorm z := Real.sqrt_nonneg _
theorem norm_latticeHeatKernel4_near_le (hpos : LatticeKernelBounds.KernelPositive)
    (hsum : LatticeKernelBounds.KernelSumsToOne)
    (hsh : LatticeKernelBounds.ShortTimeBound) {m : ℕ} (hC : gaussianComparison m ≠ ⊤) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (z z' : Fin 4 → ℤ) (hz : ∀ μ, |(z' μ : ℝ) - (z μ : ℝ)| ≤ 1) :
    ‖latticeHeatKernel4 t z'‖ ≤ (gaussianComparison m).toReal / 4 * bracketOnePlus (intVecNorm z) ^ (-(m : ℤ)) := by
  obtain ⟨μ₀, hμ⟩ := Finite.exists_max (fun μ => (z' μ).natAbs)
  set l := (z' μ₀).natAbs with hl
  have hb : ∀ μ, |(z μ : ℝ)| ≤ (l : ℝ) + 1 := fun μ => by
    have h1 : |(z' μ : ℝ)| ≤ (l : ℝ) := by
      have h2 : (((z' μ).natAbs : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hμ μ
      rwa [Nat.cast_natAbs, Int.cast_abs] at h2
    have h3 : |(z μ : ℝ)| ≤ |(z' μ : ℝ)| + |(z' μ : ℝ) - (z μ : ℝ)| := by
      have := abs_sub_abs_le_abs_sub (z μ : ℝ) (z' μ : ℝ)
      rw [abs_sub_comm (z μ : ℝ)] at this
      linarith
    linarith [hz μ]
  have hR := intVecNorm_le_of_coord_le z l hb
  have hR0 := intVecNorm_nonneg z
  have hP : 0 < bracketOnePlus (intVecNorm z) := by simp only [bracketOnePlus]; linarith
  have hP2 : bracketOnePlus (intVecNorm z) ≤ 2 * (l : ℝ) + 3 := by
    simp only [bracketOnePlus]; linarith
  have hm := factorial_term_le hC l
  have hc : 0 < shiftConstant := Real.exp_pos 1
  refine (norm_latticeHeatKernel4_le hpos hsum hsh ht ht1 z' μ₀).trans ?_
  rw [zpow_neg, zpow_natCast, le_mul_inv_iff₀ (by positivity)]
  calc shiftConstant / (l.factorial : ℝ) * bracketOnePlus (intVecNorm z) ^ m
      ≤ shiftConstant / (l.factorial : ℝ) * (2 * (l : ℝ) + 3) ^ m := by gcongr
    _ = 4 * shiftConstant * ((2 * (l : ℝ) + 3) ^ m / (l.factorial : ℝ)) / 4 := by ring
    _ ≤ _ := by linarith
theorem unitVector_apply_cases (ν μ : Fin 4) :
    (unitVector ν : Fin 4 → ℤ) μ = 0 ∨ (unitVector ν : Fin 4 → ℤ) μ = 1 := by
  by_cases h : μ = ν
  · subst h; right; simp [unitVector]
  · left; simp [unitVector, h]
theorem norm_mixedSecondDiff_le (hpos : LatticeKernelBounds.KernelPositive)
    (hsum : LatticeKernelBounds.KernelSumsToOne)
    (hsh : LatticeKernelBounds.ShortTimeBound) {m : ℕ} (hC : gaussianComparison m ≠ ⊤) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (ν ν' : Fin 4) (z : Fin 4 → ℤ) :
    ‖mixedSecondDiff ν ν' (latticeHeatKernel4 t) z‖ ≤
      (gaussianComparison m).toReal * bracketOnePlus (intVecNorm z) ^ (-(m : ℤ)) := by
  have key := fun z' hz => norm_latticeHeatKernel4_near_le hpos hsum hsh hC ht ht1 z z' hz
  have a1 := key (z + unitVector ν) (fun μ => by
    rcases unitVector_apply_cases ν μ with h | h <;> simp [h])
  have a2 := key (z + unitVector ν - unitVector ν') (fun μ => by
    rcases unitVector_apply_cases ν μ with h | h <;> rcases unitVector_apply_cases ν' μ with h' | h' <;>
      simp [h, h'])
  have a3 := key z (fun μ => by simp)
  have a4 := key (z - unitVector ν') (fun μ => by
    rcases unitVector_apply_cases ν' μ with h | h <;> simp [h])
  simp only [mixedSecondDiff, forwardDiff, backwardDiff]
  refine (norm_sub_le _ _).trans ?_
  have b1 := norm_sub_le (latticeHeatKernel4 t (z + unitVector ν))
    (latticeHeatKernel4 t (z + unitVector ν - unitVector ν'))
  have b2 := norm_sub_le (latticeHeatKernel4 t z) (latticeHeatKernel4 t (z - unitVector ν'))
  linarith
theorem poly_le {R s : ℝ} (hR : 1 ≤ R) (hs : 0 < s) :
    s ^ 2 * (R ^ 2 * s ^ 2 / 4 + s / 2) ≤ (R ^ 2 * s) ^ 4 + (R ^ 2 * s) ^ 3 := by
  have h1 : R ^ 2 ≤ R ^ 8 := pow_le_pow_right₀ hR (by norm_num)
  have h2 : (1 : ℝ) ≤ R ^ 6 := one_le_pow₀ hR
  have h3 : 0 < s ^ 4 := by positivity
  have h4 : 0 < s ^ 3 := by positivity
  have e : (R ^ 2 * s) ^ 4 + (R ^ 2 * s) ^ 3 = R ^ 8 * s ^ 4 + R ^ 6 * s ^ 3 := by ring
  have e' : s ^ 2 * (R ^ 2 * s ^ 2 / 4 + s / 2) = R ^ 2 * s ^ 4 / 4 + s ^ 3 / 2 := by ring
  rw [e, e']
  have h5 : R ^ 2 * s ^ 4 ≤ R ^ 8 * s ^ 4 := by gcongr
  have h6 : s ^ 3 ≤ R ^ 6 * s ^ 3 := by nlinarith
  have h7 : 0 ≤ R ^ 2 * s ^ 4 := by positivity
  linarith
theorem abs_gaussianHessian_le {R t a d : ℝ} (hR : 1 ≤ R) (ht : 0 < t) (ht1 : t ≤ 1)
    (ha : |a| ≤ R ^ 2) (hd : |d| ≤ 1) :
    |(4 * Real.pi * t) ^ (-2 : ℤ) * Real.exp (-R ^ 2 / (4 * t)) * (a / (4 * t ^ 2) - d / (2 * t))| ≤
      1 / (16 * Real.pi ^ 2) *
        (((R ^ 2 / t) ^ 4 + (R ^ 2 / t) ^ 3) * Real.exp (-(R ^ 2 / t / 8))) *
        Real.exp (-(R ^ 2 / 8)) := by
  set s := t⁻¹ with hs
  have hs0 : 0 < s := inv_pos.2 ht
  have hs1 : 1 ≤ s := (one_le_inv₀ ht).2 ht1
  have hy : R ^ 2 / t = R ^ 2 * s := by rw [hs, div_eq_mul_inv]
  rw [hy]
  have hP : (4 * Real.pi * t) ^ (-2 : ℤ) = 1 / (16 * Real.pi ^ 2) * s ^ 2 := by
    rw [zpow_neg, hs]
    have : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
    rw [this, zpow_natCast]
    field_simp
    ring
  have hE : Real.exp (-R ^ 2 / (4 * t)) =
      Real.exp (-(R ^ 2 * s / 8)) * Real.exp (-(R ^ 2 * s / 8)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hs]
    field_simp
    ring
  have hE2 : Real.exp (-(R ^ 2 * s / 8)) ≤ Real.exp (-(R ^ 2 / 8)) := by
    apply Real.exp_le_exp.2
    have : R ^ 2 ≤ R ^ 2 * s := le_mul_of_one_le_right (by positivity) hs1
    linarith
  have hB : |a / (4 * t ^ 2) - d / (2 * t)| ≤ R ^ 2 * s ^ 2 / 4 + s / 2 := by
    have e1 : a / (4 * t ^ 2) = a * s ^ 2 / 4 := by rw [hs]; field_simp
    have e2 : d / (2 * t) = d * s / 2 := by rw [hs]; field_simp
    rw [e1, e2]
    refine (abs_sub _ _).trans ?_
    rw [abs_div, abs_div, abs_mul, abs_mul, abs_of_pos hs0, abs_of_pos (by positivity : 0 < s ^ 2)]
    have : |(4 : ℝ)| = 4 := by norm_num
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [this, h2]
    have h3 : |a| * s ^ 2 ≤ R ^ 2 * s ^ 2 := by gcongr
    have h4 : |d| * s ≤ 1 * s := by gcongr
    linarith
  rw [abs_mul, abs_mul, hP, hE]
  rw [abs_of_pos (by positivity : 0 < 1 / (16 * Real.pi ^ 2) * s ^ 2),
    abs_of_pos (by positivity :
      0 < Real.exp (-(R ^ 2 * s / 8)) * Real.exp (-(R ^ 2 * s / 8)))]
  have hpoly := poly_le hR hs0
  set e₁ := Real.exp (-(R ^ 2 * s / 8)) with he₁
  set e₂ := Real.exp (-(R ^ 2 / 8)) with he₂
  calc 1 / (16 * Real.pi ^ 2) * s ^ 2 * (e₁ * e₁) * |a / (4 * t ^ 2) - d / (2 * t)|
      ≤ 1 / (16 * Real.pi ^ 2) * s ^ 2 * (e₁ * e₂) * (R ^ 2 * s ^ 2 / 4 + s / 2) := by gcongr
    _ = 1 / (16 * Real.pi ^ 2) * (s ^ 2 * (R ^ 2 * s ^ 2 / 4 + s / 2)) * e₁ * e₂ := by ring
    _ ≤ 1 / (16 * Real.pi ^ 2) * ((R ^ 2 * s) ^ 4 + (R ^ 2 * s) ^ 3) * e₁ * e₂ := by gcongr
    _ = _ := by ring
theorem abs_mixedSecondPartial_le (hcl : ∀ (t : ℝ) (u : Fin 4 → ℝ), 0 < t →
      gaussianHeatKernel4 t u =
        (4 * Real.pi * t) ^ (-2 : ℤ) * Real.exp (-realVecNorm u ^ 2 / (4 * t)))
    (hess : ∀ (ν ν' : Fin 4) (t : ℝ) (u : Fin 4 → ℝ), 0 < t →
      mixedSecondPartial ν ν' (gaussianHeatKernel4 t) u =
        gaussianHeatKernel4 t u * (u ν * u ν' / (4 * t ^ 2) -
          FourVector.kronecker ν ν' / (2 * t)))
    {m : ℕ} (hC : gaussianComparison m ≠ ⊤) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (ν ν' : Fin 4)
    (z : Fin 4 → ℤ) (hz : z ≠ 0) :
    |mixedSecondPartial ν ν' (gaussianHeatKernel4 t) (castVec z)| ≤
      (gaussianComparison m).toReal * bracketOnePlus (intVecNorm z) ^ (-(m : ℤ)) := by
  set R := intVecNorm z with hRdef
  have hRe : R = Real.sqrt (∑ μ, (z μ : ℝ) * (z μ : ℝ)) := rfl
  have hsq : ∀ μ, |(z μ : ℝ)| ≤ R := fun μ => by
    rw [hRe]
    apply Real.abs_le_sqrt
    rw [pow_two]
    exact Finset.single_le_sum (f := fun μ => (z μ : ℝ) * (z μ : ℝ))
      (fun i _ => mul_self_nonneg _) (Finset.mem_univ μ)
  have hR1 : 1 ≤ R := by
    obtain ⟨μ, hμ⟩ := Function.ne_iff.1 hz
    have h1 : (1 : ℤ) ≤ |z μ| := Int.one_le_abs hμ
    have h2 : (1 : ℝ) ≤ |(z μ : ℝ)| := by exact_mod_cast h1
    exact h2.trans (hsq μ)
  have hR0 : 0 ≤ R := by linarith
  have ha : |(z ν : ℝ) * (z ν' : ℝ)| ≤ R ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hsq ν) (hsq ν') (abs_nonneg _) hR0
  have hd : |FourVector.kronecker ν ν'| ≤ 1 := by
    simp only [FourVector.kronecker, FourVector.propIndicator]
    split_ifs <;> simp
  rw [hess ν ν' t _ ht, hcl t _ ht]
  have hlen : realVecNorm (castVec z) = R := rfl
  rw [hlen]
  have hmain := abs_gaussianHessian_le hR1 ht ht1 ha hd
  refine hmain.trans ?_
  set y := R ^ 2 / t with hy
  have hy0 : 0 ≤ y := by positivity
  have hmem := gaussian_term_le hC hy0 hR0
  have hP : 0 < bracketOnePlus R := by simp only [bracketOnePlus]; linarith
  rw [zpow_neg, zpow_natCast]
  have hop : bracketOnePlus R = 1 + R := rfl
  rw [le_mul_inv_iff₀ (by positivity)]
  rw [hop] at *
  calc _ = 1 / (16 * Real.pi ^ 2) * ((y ^ 4 + y ^ 3) * Real.exp (-(y / 8))) *
        ((1 + R) ^ m * Real.exp (-(R ^ 2 / 8))) := by ring
    _ ≤ _ := hmem
theorem shortTimeBounds_holds (hF : FreeKernel.symbolsAndFourierIntegrals)
    (hN : Constants.HeatKernel.finite_and_pos)
    (hO : LatticeKernelBounds.OneDimensionalEstimates)
    (hess : ∀ (ν ν' : Fin 4) (t : ℝ) (u : Fin 4 → ℝ), 0 < t →
      mixedSecondPartial ν ν' (gaussianHeatKernel4 t) u =
        gaussianHeatKernel4 t u * (u ν * u ν' / (4 * t ^ 2) -
          FourVector.kronecker ν ν' / (2 * t)))
    (𝔫 : ℕ) (ν ν' : Fin 4) : ShortTimeBounds 𝔫 ν ν' := by
  obtain ⟨-, hpos, -, hsum, -, hsh, -⟩ := hO
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hCfin, -⟩ := hN
  have hcl := hF.1.2.2.2.2
  intro z t ht ht1
  exact ⟨norm_mixedSecondDiff_le hpos hsum hsh (hCfin 𝔫).1 ht ht1 ν ν' z,
    fun hz => abs_mixedSecondPartial_le hcl hess (hCfin 𝔫).1 ht ht1 ν ν' z hz⟩
end SmallTime
namespace LargeTime
def axisDiffKind (ν ν' μ : Fin 4) : LatticeKernel.DiffKind :=
  if ν = ν' then (if μ = ν then .laplacian else .identity)
  else if μ = ν then .forward else if μ = ν' then .backward else .identity
theorem sum_diffOrder_axisDiffKind (ν ν' : Fin 4) :
    ∑ μ, LatticeKernel.diffOrder (axisDiffKind ν ν' μ) = 2 := by
  fin_cases ν <;> fin_cases ν' <;>
    simp [Fin.sum_univ_four, axisDiffKind, LatticeKernel.diffOrder]
theorem forwardDiff_prod (G : Fin 4 → ℤ → ℂ) (ν : Fin 4) :
    forwardDiff ν (fun z : Fin 4 → ℤ => ∏ μ, G μ (z μ)) =
      fun z => ∏ μ, (Function.update G ν (LatticeKernel.fwdDiff (G ν))) μ (z μ) := by
  funext z
  simp only [forwardDiff, unitVector]
  fin_cases ν <;>
    simp [Fin.prod_univ_four, Function.update, Pi.single_apply,
      LatticeKernel.fwdDiff] <;> ring
theorem backwardDiff_prod (G : Fin 4 → ℤ → ℂ) (ν : Fin 4) :
    backwardDiff ν (fun z : Fin 4 → ℤ => ∏ μ, G μ (z μ)) =
      fun z => ∏ μ, (Function.update G ν (LatticeKernel.bwdDiff (G ν))) μ (z μ) := by
  funext z
  simp only [backwardDiff, unitVector]
  fin_cases ν <;>
    simp [Fin.prod_univ_four, Function.update, Pi.single_apply,
      LatticeKernel.bwdDiff] <;> ring
theorem mixedSecondDiff_latticeHeatKernel4 (ν ν' : Fin 4) (t : ℝ) (z : Fin 4 → ℤ) :
    mixedSecondDiff ν ν' (latticeHeatKernel4 t) z =
      ∏ μ, LatticeKernel.diffOp (axisDiffKind ν ν' μ)
        (LatticeKernel.discreteHeatKernel t) (z μ) := by
  have h : latticeHeatKernel4 t =
      fun z : Fin 4 → ℤ => ∏ μ, (fun _ : Fin 4 => LatticeKernel.discreteHeatKernel t) μ (z μ) := rfl
  rw [mixedSecondDiff, h, backwardDiff_prod, forwardDiff_prod]
  refine Finset.prod_congr rfl fun μ _ => ?_
  by_cases h1 : ν = ν'
  · subst h1
    by_cases h2 : μ = ν
    · subst h2
      simp [axisDiffKind, LatticeKernel.diffOp]
    · simp [axisDiffKind, LatticeKernel.diffOp, h2, Function.update]
  · by_cases h2 : μ = ν
    · subst h2
      simp [axisDiffKind, LatticeKernel.diffOp, h1, Function.update]
    · by_cases h3 : μ = ν'
      · subst h3
        simp [axisDiffKind, LatticeKernel.diffOp, h1, h2, Function.update]
      · simp [axisDiffKind, LatticeKernel.diffOp, h1, h2, h3, Function.update]
theorem hasDerivAt_gaussianHeatKernel {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    HasDerivAt (LatticeKernel.gaussianHeatKernel t)
      (-ξ / (2 * t) * LatticeKernel.gaussianHeatKernel t ξ) ξ := by
  have h0 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * ξ) ξ := by simpa using hasDerivAt_pow 2 ξ
  have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / (4 * t)) (-(2 * ξ) / (4 * t)) ξ :=
    (h0.neg).div_const (4 * t)
  have h : HasDerivAt (fun x : ℝ => -x ^ 2 / (4 * t)) (-ξ / (2 * t)) ξ :=
    h1.congr_deriv (by field_simp; ring)
  have h2 := h.exp.div_const (Real.sqrt (4 * Real.pi * t))
  exact h2.congr_deriv (by simp only [LatticeKernel.gaussianHeatKernel]; ring)
theorem deriv_gaussianHeatKernel {t : ℝ} (ht : 0 < t) :
    deriv (LatticeKernel.gaussianHeatKernel t) =
      fun ξ => -ξ / (2 * t) * LatticeKernel.gaussianHeatKernel t ξ :=
  funext fun ξ => (hasDerivAt_gaussianHeatKernel ht ξ).deriv
theorem gaussianHeatKernelDeriv_one {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    LatticeKernel.gaussianHeatKernelDeriv 1 t ξ =
      LatticeKernel.gaussianHeatKernel t ξ * (-ξ / (2 * t)) := by
  rw [LatticeKernel.gaussianHeatKernelDeriv, iteratedDeriv_one, deriv_gaussianHeatKernel ht]
  ring
theorem gaussianHeatKernelDeriv_two {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    LatticeKernel.gaussianHeatKernelDeriv 2 t ξ =
      LatticeKernel.gaussianHeatKernel t ξ * (ξ ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
  rw [LatticeKernel.gaussianHeatKernelDeriv, iteratedDeriv_succ, iteratedDeriv_one,
    deriv_gaussianHeatKernel ht]
  have h1 : HasDerivAt (fun x : ℝ => -x / (2 * t)) (-1 / (2 * t)) ξ :=
    ((hasDerivAt_id ξ).neg).div_const (2 * t)
  have h2 : HasDerivAt (fun x : ℝ => -x / (2 * t) * LatticeKernel.gaussianHeatKernel t x)
      (-1 / (2 * t) * LatticeKernel.gaussianHeatKernel t ξ +
        -ξ / (2 * t) * (-ξ / (2 * t) * LatticeKernel.gaussianHeatKernel t ξ)) ξ :=
    h1.mul (hasDerivAt_gaussianHeatKernel ht ξ)
  rw [h2.deriv]
  field_simp
  ring
theorem gaussianHeatKernelDeriv_zero (t ξ : ℝ) :
    LatticeKernel.gaussianHeatKernelDeriv 0 t ξ =
      LatticeKernel.gaussianHeatKernel t ξ := by
  simp [LatticeKernel.gaussianHeatKernelDeriv]
theorem mixedSecondPartial_eq_prod
    (hess : ∀ (ν ν' : Fin 4) (t : ℝ) (u : Fin 4 → ℝ), 0 < t →
      mixedSecondPartial ν ν' (gaussianHeatKernel4 t) u =
        gaussianHeatKernel4 t u * (u ν * u ν' / (4 * t ^ 2) - FourVector.kronecker ν ν' / (2 * t)))
    (ν ν' : Fin 4) {t : ℝ} (ht : 0 < t) (u : Fin 4 → ℝ) :
    mixedSecondPartial ν ν' (gaussianHeatKernel4 t) u =
      ∏ μ, LatticeKernel.gaussianHeatKernelDeriv
        (LatticeKernel.diffOrder (axisDiffKind ν ν' μ)) t (u μ) := by
  rw [hess ν ν' t u ht, gaussianHeatKernel4]
  have h2t : t ≠ 0 := ht.ne'
  fin_cases ν <;> fin_cases ν' <;>
    simp [Fin.prod_univ_four, axisDiffKind, LatticeKernel.diffOrder,
      gaussianHeatKernelDeriv_zero, gaussianHeatKernelDeriv_one ht,
      gaussianHeatKernelDeriv_two ht, FourVector.kronecker,
      FourVector.propIndicator] <;> field_simp <;> ring
theorem norm_mul_mul_mul_le {x y z u : ℂ} {p q r s : ℝ} (hx : ‖x‖ ≤ p) (hy : ‖y‖ ≤ q) (hz : ‖z‖ ≤ r)
    (hu : ‖u‖ ≤ s) : ‖x * y * z * u‖ ≤ p * q * r * s := by
  have hp := (norm_nonneg x).trans hx
  have hq := (norm_nonneg y).trans hy
  have hr := (norm_nonneg z).trans hz
  rw [norm_mul, norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul (mul_le_mul hx hy (norm_nonneg _) hp) hz (norm_nonneg _)
    (mul_nonneg hp hq)) hu (norm_nonneg _) (mul_nonneg (mul_nonneg hp hq) hr)
theorem norm_prod_sub_prod_le (a b : Fin 4 → ℂ) (c : Fin 4 → ℝ) (r : ℝ) (ha : ∀ μ, ‖a μ‖ ≤ c μ)
    (hb : ∀ μ, ‖b μ‖ ≤ c μ) (hab : ∀ μ, ‖a μ - b μ‖ ≤ c μ * r) :
    ‖∏ μ, a μ - ∏ μ, b μ‖ ≤ 4 * (∏ μ, c μ) * r := by
  simp only [Fin.prod_univ_four]
  have e : a 0 * a 1 * a 2 * a 3 - b 0 * b 1 * b 2 * b 3 =
      (a 0 - b 0) * a 1 * a 2 * a 3 + b 0 * (a 1 - b 1) * a 2 * a 3 +
        b 0 * b 1 * (a 2 - b 2) * a 3 + b 0 * b 1 * b 2 * (a 3 - b 3) := by ring
  rw [e]
  have h1 := norm_mul_mul_mul_le (hab 0) (ha 1) (ha 2) (ha 3)
  have h2 := norm_mul_mul_mul_le (hb 0) (hab 1) (ha 2) (ha 3)
  have h3 := norm_mul_mul_mul_le (hb 0) (hb 1) (hab 2) (ha 3)
  have h4 := norm_mul_mul_mul_le (hb 0) (hb 1) (hb 2) (hab 3)
  calc _ ≤ _ := norm_add₄_le
    _ ≤ _ := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by ring
theorem exists_coord_ge_half_norm (z : Fin 4 → ℤ) :
    ∃ μ, intVecNorm z / 2 ≤ |(z μ : ℝ)| := by
  by_contra h
  simp only [not_exists, not_le] at h
  have hsum : 0 ≤ ∑ μ, (z μ : ℝ) * (z μ : ℝ) :=
    Finset.sum_nonneg fun μ _ => mul_self_nonneg _
  have hR2 : intVecNorm z ^ 2 = ∑ μ, (z μ : ℝ) * (z μ : ℝ) :=
    Real.sq_sqrt hsum
  have hlt : ∀ μ, (z μ : ℝ) * (z μ : ℝ) < intVecNorm z ^ 2 / 4 := by
    intro μ
    have h1 := h μ
    have h2 := abs_mul_abs_self (z μ : ℝ)
    have h3 := abs_nonneg (z μ : ℝ)
    nlinarith
  have := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 4)))
    Finset.univ_nonempty fun μ _ => hlt μ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  rw [← hR2] at this
  push_cast at this
  linarith
theorem bracketOnePlus_zpow_pos {y : ℝ} (hy : 0 ≤ y) (m : ℕ) : 0 < bracketOnePlus y ^ (-(m : ℤ)) := by
  have : 0 < bracketOnePlus y := by simp only [bracketOnePlus]; linarith
  exact zpow_pos this _
theorem bracketOnePlus_zpow_le_one {y : ℝ} (hy : 0 ≤ y) (m : ℕ) : bracketOnePlus y ^ (-(m : ℤ)) ≤ 1 := by
  have h1 : 1 ≤ bracketOnePlus y := by simp only [bracketOnePlus]; linarith
  rw [zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
theorem prod_bracketOnePlus_le {t : ℝ} (ht : 0 < t) (z : Fin 4 → ℤ) (m : ℕ) :
    ∏ μ, bracketOnePlus (|(z μ : ℝ)| / Real.sqrt t) ^ (-(m : ℤ)) ≤
      bracketOnePlus (intVecNorm z / (2 * Real.sqrt t)) ^ (-(m : ℤ)) := by
  obtain ⟨μ₀, h₀⟩ := exists_coord_ge_half_norm z
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hnn : ∀ μ, 0 ≤ |(z μ : ℝ)| / Real.sqrt t := fun μ => div_nonneg (abs_nonneg _) hs.le
  have hR : 0 ≤ intVecNorm z / (2 * Real.sqrt t) :=
    div_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hstep : ∏ μ, bracketOnePlus (|(z μ : ℝ)| / Real.sqrt t) ^ (-(m : ℤ)) ≤
      bracketOnePlus (|(z μ₀ : ℝ)| / Real.sqrt t) ^ (-(m : ℤ)) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ₀)]
    refine mul_le_of_le_one_right (bracketOnePlus_zpow_pos (hnn μ₀) m).le ?_
    exact Finset.prod_le_one (fun μ _ => (bracketOnePlus_zpow_pos (hnn μ) m).le)
      fun μ _ => bracketOnePlus_zpow_le_one (hnn μ) m
  refine hstep.trans ?_
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  have hle : intVecNorm z / (2 * Real.sqrt t) ≤ |(z μ₀ : ℝ)| / Real.sqrt t := by
    rw [show intVecNorm z / (2 * Real.sqrt t) =
      intVecNorm z / 2 / Real.sqrt t by field_simp]
    exact div_le_div_of_nonneg_right h₀ hs.le
  have hpos : 0 < bracketOnePlus (intVecNorm z / (2 * Real.sqrt t)) := by
    simp only [bracketOnePlus]; linarith
  refine inv_anti₀ (pow_pos hpos m) (pow_le_pow_left₀ hpos.le ?_ m)
  simp only [bracketOnePlus]; linarith
theorem bracketOnePlus_rpow_neg (y : ℝ) (m : ℕ) :
    bracketOnePlus y ^ (-(m : ℝ)) = bracketOnePlus y ^ (-(m : ℤ)) := by
  rw [← Real.rpow_intCast]
  push_cast
  rfl
theorem prod_time_rpow {t : ℝ} (ht : 0 < t) (ν ν' : Fin 4) :
    ∏ μ, t ^ (-(((LatticeKernel.diffOrder (axisDiffKind ν ν' μ) : ℝ) + 1) / 2)) =
      t ^ (-3 : ℤ) := by
  rw [← Real.rpow_sum_of_pos ht, ← Real.rpow_intCast]
  congr 1
  have h : ((∑ μ, LatticeKernel.diffOrder (axisDiffKind ν ν' μ) : ℕ) : ℝ) = 2 := by
    rw [sum_diffOrder_axisDiffKind]; norm_num
  push_cast at h
  have e : ∑ μ, -(((LatticeKernel.diffOrder (axisDiffKind ν ν' μ) : ℝ) + 1) / 2) =
      -((∑ μ, (LatticeKernel.diffOrder (axisDiffKind ν ν' μ) : ℝ)) + 4) / 2 := by
    simp only [Fin.sum_univ_four]
    ring
  rw [e, h]
  norm_num
theorem longTimeBounds_holds (hN : Constants.HeatKernel.finite_and_pos)
    (hO : LatticeKernelBounds.OneDimensionalEstimates)
    (hess : ∀ (ν ν' : Fin 4) (t : ℝ) (u : Fin 4 → ℝ), 0 < t →
      mixedSecondPartial ν ν' (gaussianHeatKernel4 t) u =
        gaussianHeatKernel4 t u * (u ν * u ν' / (4 * t ^ 2) - FourVector.kronecker ν ν' / (2 * t)))
    (𝔫 : ℕ) (ν ν' : Fin 4) : LongTimeBounds 𝔫 ν ν' := by
  intro z t ht
  obtain ⟨-, -, -, -, -, -, -, -, -, hB, hC, -⟩ := hN
  obtain ⟨-, -, -, -, -, -, hO'⟩ := hO
  have ht0 : 0 < t := by linarith
  obtain ⟨hBtop, hbd⟩ := hO' 𝔫
  have hB0 : 0 ≤ (kernelDerivativeBound 𝔫).toReal := ENNReal.toReal_nonneg
  have hBC : 4 * (kernelDerivativeBound 𝔫).toReal ^ 4 ≤ (gaussianComparison 𝔫).toReal := by
    have h1 : 4 * kernelDerivativeBound 𝔫 ^ 4 ≤ gaussianComparison 𝔫 := le_max_right _ _
    have h2 := ENNReal.toReal_mono (hC 𝔫).1 h1
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow] using h2
  have hsq : ∀ μ, 0 ≤ |(z μ : ℝ)| / Real.sqrt t := fun μ =>
    div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  set a : Fin 4 → ℂ := fun μ => LatticeKernel.diffOp (axisDiffKind ν ν' μ)
    (LatticeKernel.discreteHeatKernel t) (z μ) with ha_def
  set b : Fin 4 → ℂ := fun μ => ((LatticeKernel.gaussianHeatKernelDeriv
    (LatticeKernel.diffOrder (axisDiffKind ν ν' μ)) t (z μ : ℝ) : ℝ) : ℂ) with hb_def
  set w : Fin 4 → ℝ := fun μ => bracketOnePlus (|(z μ : ℝ)| / Real.sqrt t) ^ (-(𝔫 : ℤ)) with hw_def
  set s : Fin 4 → ℝ := fun μ =>
    t ^ (-(((LatticeKernel.diffOrder (axisDiffKind ν ν' μ) : ℝ) + 1) / 2)) with hs_def
  set r : ℝ := t ^ (-(1 / 2 : ℝ)) with hr_def
  have ha : ∀ μ, ‖a μ‖ ≤ (kernelDerivativeBound 𝔫).toReal * s μ * w μ := fun μ => by
    have := (hbd (axisDiffKind ν ν' μ)).1 t ht (z μ)
    rwa [bracketOnePlus_rpow_neg] at this
  have hb : ∀ μ, ‖b μ‖ ≤ (kernelDerivativeBound 𝔫).toReal * s μ * w μ := fun μ => by
    have := (hbd (axisDiffKind ν ν' μ)).2.1 t ht0 (z μ : ℝ)
    rw [bracketOnePlus_rpow_neg] at this
    simp only [hb_def, Complex.norm_real, Real.norm_eq_abs]
    exact this
  have hab : ∀ μ, ‖a μ - b μ‖ ≤ (kernelDerivativeBound 𝔫).toReal * s μ * w μ * r := fun μ => by
    have := (hbd (axisDiffKind ν ν' μ)).2.2 t ht (z μ)
    rw [bracketOnePlus_rpow_neg] at this
    have e : t ^ (-(((LatticeKernel.diffOrder (axisDiffKind ν ν' μ) : ℝ) + 2) / 2)) =
        s μ * r := by
      simp only [hs_def, hr_def]
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    rw [e] at this
    calc ‖a μ - b μ‖ ≤ _ := this
      _ = _ := by ring
  have hprod : ∏ μ, ((kernelDerivativeBound 𝔫).toReal * s μ * w μ) =
      (kernelDerivativeBound 𝔫).toReal ^ 4 * t ^ (-3 : ℤ) * ∏ μ, w μ := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, prod_time_rpow ht0 ν ν']
    simp
  have hw0 : 0 ≤ ∏ μ, w μ := Finset.prod_nonneg fun μ _ => (bracketOnePlus_zpow_pos (hsq μ) 𝔫).le
  have ht3 : 0 ≤ t ^ (-3 : ℤ) := (zpow_pos ht0 _).le
  have hdec : ∏ μ, w μ ≤ bracketOnePlus (intVecNorm z / (2 * Real.sqrt t)) ^ (-(𝔫 : ℤ)) :=
    prod_bracketOnePlus_le ht0 z 𝔫
  have hB4 : (kernelDerivativeBound 𝔫).toReal ^ 4 ≤ (gaussianComparison 𝔫).toReal := by
    have := pow_nonneg hB0 4
    linarith
  have hC0 : 0 ≤ (gaussianComparison 𝔫).toReal := ENNReal.toReal_nonneg
  have hsd : mixedSecondDiff ν ν' (latticeHeatKernel4 t) z = ∏ μ, a μ :=
    mixedSecondDiff_latticeHeatKernel4 ν ν' t z
  have hdd : ((mixedSecondPartial ν ν' (gaussianHeatKernel4 t) (castVec z) : ℝ) : ℂ) =
      ∏ μ, b μ := by
    rw [mixedSecondPartial_eq_prod hess ν ν' ht0]
    simp [hb_def, Complex.ofReal_prod, castVec]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsd, norm_prod]
    calc ∏ μ, ‖a μ‖ ≤ ∏ μ, ((kernelDerivativeBound 𝔫).toReal * s μ * w μ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun μ _ => ha μ
      _ = (kernelDerivativeBound 𝔫).toReal ^ 4 * t ^ (-3 : ℤ) * ∏ μ, w μ := hprod
      _ ≤ (gaussianComparison 𝔫).toReal * t ^ (-3 : ℤ) * ∏ μ, w μ := by gcongr
  · exact mul_le_mul_of_nonneg_left hdec (mul_nonneg hC0 ht3)
  · rw [hsd, hdd]
    have h7 : t ^ (-(7 / 2) : ℝ) = t ^ (-3 : ℤ) * r := by
      have : t ^ (-3 : ℤ) = t ^ (-3 : ℝ) := by
        rw [← Real.rpow_intCast]; norm_num
      rw [this, hr_def, ← Real.rpow_add ht0]
      norm_num
    have hr0 : 0 ≤ r := Real.rpow_nonneg ht0.le _
    calc ‖∏ μ, a μ - ∏ μ, b μ‖ ≤ 4 * (∏ μ, ((kernelDerivativeBound 𝔫).toReal * s μ * w μ)) * r :=
          norm_prod_sub_prod_le a b _ r ha hb hab
      _ = 4 * (kernelDerivativeBound 𝔫).toReal ^ 4 * (t ^ (-3 : ℤ) * r) * ∏ μ, w μ := by rw [hprod]; ring
      _ ≤ (gaussianComparison 𝔫).toReal * (t ^ (-3 : ℤ) * r) *
            bracketOnePlus (intVecNorm z / (2 * Real.sqrt t)) ^ (-(𝔫 : ℤ)) := by
          have h0 : 0 ≤ t ^ (-3 : ℤ) * r := mul_nonneg ht3 hr0
          gcongr
      _ = _ := by rw [h7]
end LargeTime
theorem heatKernelGreenProperties_holds (hF : FreeKernel.symbolsAndFourierIntegrals)
    (hN : Constants.HeatKernel.finite_and_pos)
    (hO : LatticeKernelBounds.OneDimensionalEstimates)
    (hT : PeriodicLattice.VectorClasses.FourierFactsAndGreenIdentities.Statement) :
    HeatKernelGreenProperties := by
  intro n hn ν ν'
  have hess := fun (ν ν' : Fin 4) (t : ℝ) (u : Fin 4 → ℝ) (ht : 0 < t) =>
    Continuum.mixedSecondPartial_gaussian hF ν ν' t u ht
  exact ⟨Periodize.periodicSummation_holds hF hO hT n hn, TorusTime.torusTimeIntegrals_holds n hn ν ν',
    Continuum.continuumTimeIntegrals_holds hF hT ν ν',
    fun 𝔫 => ⟨SmallTime.shortTimeBounds_holds hF hN hO hess 𝔫 ν ν',
      LargeTime.longTimeBounds_holds hN hO hess 𝔫 ν ν'⟩,
    Continuum.nearDiagonalBound_holds hF ν ν'⟩
end YangMills.Construction.FreeKernel.HeatKernelGreen
end
