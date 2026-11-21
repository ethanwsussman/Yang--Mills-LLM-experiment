import YangMills.Construction.FreeKernel.HeatKernelsAndTheGreensFunctionsProof
import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.LinearAlgebra.PropertiesOfTheFreeCurvaturePropagatorProof
import YangMills.Construction.FreeKernel.MultipliersSymbolCharactersAndGreensFunctionsOnClasses
import YangMills.Construction.LatticeForms.LatticeSymbolAndTheTwoGreensFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.VectorClasses
open YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint YangMills.Construction.PeriodicLattice.DiscreteTorusData YangMills.Construction.FourVector
namespace FourierFactsAndGreenIdentities
theorem wavePairing_add (k : Fin 4 → ℝ) (a b : Fin 4 → ℤ) :
    wavePairing k (a + b) = wavePairing k a + wavePairing k b := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.pairing_add <;> assumption
theorem expWave_add (k : Fin 4 → ℝ) (a b : Fin 4 → ℤ) :
    expWave k (a + b) = expWave k a * expWave k b := by
  simp only [expWave, wavePairing_add]
  push_cast
  rw [mul_add, Complex.exp_add]
theorem expWave_unitVector (k : Fin 4 → ℝ) (μ : Fin 4) :
    expWave k (ShortDistanceTwoPoint.unitVector μ) = Complex.exp (Complex.I * (k μ : ℂ)) := by
  have h : wavePairing k (ShortDistanceTwoPoint.unitVector μ) = k μ := by
    simp [wavePairing, ShortDistanceTwoPoint.unitVector, Pi.single_apply]
  simp only [expWave, h]
theorem expWave_sub_unitVector (k : Fin 4 → ℝ) (a : Fin 4 → ℤ) (μ : Fin 4) :
    expWave k (a - ShortDistanceTwoPoint.unitVector μ) =
      Complex.exp (-(Complex.I * (k μ : ℂ))) * expWave k a := by
  have h := expWave_add k (a - ShortDistanceTwoPoint.unitVector μ) (ShortDistanceTwoPoint.unitVector μ)
  rw [sub_add_cancel, expWave_unitVector] at h
  rw [h, mul_comm (expWave k _), ← mul_assoc, ← Complex.exp_add]
  simp
theorem expWave_sub (k : Fin 4 → ℝ) (z a : Fin 4 → ℤ) :
    expWave k (z - a) = expWave (-k) a * expWave k z := by
  have h1 : wavePairing k (z - a) = wavePairing (-k) a + wavePairing k z := by
    simp only [wavePairing, Pi.sub_apply, Pi.neg_apply]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    ring
  simp only [expWave, h1]
  push_cast
  rw [mul_add, Complex.exp_add]
theorem expWaveMultipliers_of_laplacian
    (h : ∀ k : Fin 4 → ℝ,
      discreteLaplacian (expWave k) = fun z => (laplacianSymbol k : ℂ) * expWave k z) :
    ExpWaveMultipliers := by
  intro k μ
  refine ⟨funext fun z => ?_, funext fun z => ?_, h k⟩
  · simp only [forwardDiff, expWave_add, expWave_unitVector]
    ring
  · simp only [backwardDiff, expWave_sub_unitVector]
    ring
theorem four_sin_sq_half_eq_norm_sq (t : ℝ) :
    4 * Real.sin (t / 2) ^ 2 = ‖Complex.exp (Complex.I * (t : ℂ)) - 1‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, mul_comm Complex.I]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im, sub_zero]
  have h1 := Real.cos_two_mul (t / 2)
  have h2 := Real.sin_two_mul (t / 2)
  have h3 := Real.sin_sq_add_cos_sq (t / 2)
  rw [show 2 * (t / 2) = t by ring] at h1 h2
  rw [h1, h2]
  linear_combination (4 - 4 * Real.cos (t / 2) ^ 2) * h3
theorem laplacianSymbolModulusFormAndBounds_of_comparable (h : SymbolComparableToSquare) :
    LaplacianSymbolModulusFormAndBounds := by
  refine ⟨fun k => Finset.sum_congr rfl fun μ _ => four_sin_sq_half_eq_norm_sq (k μ), fun k hk => ?_⟩
  simpa only [euclidNorm_eq_euclidNormVec] using h k hk
def unityRootPow (n : ℕ) (a b : ℤ) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi / n * (a : ℝ) * (b : ℝ) : ℝ) : ℂ))
theorem unityRootPow_comm (n : ℕ) (a b : ℤ) : unityRootPow n a b = unityRootPow n b a := by
  simp only [unityRootPow]
  congr 3
  ring
theorem expWave_momentumVec (n : ℕ) (d a : Fin 4 → ℤ) :
    expWave (momentumVec n d) a = ∏ μ, unityRootPow n (d μ) (a μ) := by
  simp only [expWave, wavePairing, momentumVec, unityRootPow]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
theorem unityRootPow_one_eq_one_iff (n : ℕ) [NeZero n] (a : ℤ) :
    unityRootPow n a 1 = 1 ↔ (n : ℤ) ∣ a := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  rw [unityRootPow, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    push_cast at hm
    have h : (a : ℂ) = (n : ℂ) * m := by
      field_simp at hm
      exact hm
    exact_mod_cast h
  · rintro ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    push_cast
    field_simp
theorem unityRootPow_eq_zpow (n : ℕ) (a l : ℤ) : unityRootPow n a l = unityRootPow n a 1 ^ l := by
  rw [unityRootPow, unityRootPow, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring
theorem unityRootPow_one_pow_self (n : ℕ) [NeZero n] (a : ℤ) : unityRootPow n a 1 ^ n = 1 := by
  have h := unityRootPow_eq_zpow n a (n : ℤ)
  rw [zpow_natCast] at h
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  rw [← h, unityRootPow, Complex.exp_eq_one_iff]
  refine ⟨a, ?_⟩
  push_cast
  field_simp
theorem sum_Ico_unityRootPow (n : ℕ) [NeZero n] (a s : ℤ) :
    ∑ l ∈ Finset.Ico s (s + n), unityRootPow n a l = if (n : ℤ) ∣ a then (n : ℂ) else 0 := by
  have hrange : Finset.Ico s (s + n) = (Finset.range n).image fun i : ℕ => s + (i : ℤ) := by
    ext l
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(l - s).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  have hinj : Set.InjOn (fun i : ℕ => s + (i : ℤ)) (Finset.range n : Set ℕ) := by
    intro i _ j _ h
    simpa using h
  rw [hrange, Finset.sum_image hinj]
  have hρ0 : unityRootPow n a 1 ≠ 0 := Complex.exp_ne_zero _
  simp only [unityRootPow_eq_zpow n a (s + _), zpow_add₀ hρ0, zpow_natCast]
  rw [← Finset.mul_sum]
  split_ifs with h
  · rw [(unityRootPow_one_eq_one_iff n a).2 h]
    simp
  · have hne : unityRootPow n a 1 ≠ 1 := fun h' => h ((unityRootPow_one_eq_one_iff n a).1 h')
    rw [geom_sum_eq hne, unityRootPow_one_pow_self]
    simp
theorem sum_piFinset_prod_unityRootPow (n : ℕ) [NeZero n] (d : Fin 4 → ℤ) (s : ℤ) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Ico s (s + n)),
        ∏ μ, unityRootPow n (d μ) (a μ) =
      if ∀ μ, (n : ℤ) ∣ d μ then (n : ℂ) ^ 4 else 0 := by
  rw [← Finset.prod_univ_sum]
  simp only [sum_Ico_unityRootPow]
  rw [Finset.prod_ite_zero]
  simp
theorem sum_residueCube_expWave (n : ℕ) [NeZero n] (d : Fin 4 → ℤ) :
    ∑ a ∈ residueCube n, expWave (momentumVec n d) a =
      if ∀ μ, (n : ℤ) ∣ d μ then (n : ℂ) ^ 4 else 0 := by
  have h : residueCube n = Fintype.piFinset fun _ : Fin 4 => Finset.Ico (0 : ℤ) (0 + n) := by
    simp [residueCube]
  rw [h, ← sum_piFinset_prod_unityRootPow n d 0]
  exact Finset.sum_congr rfl fun a _ => expWave_momentumVec n d a
theorem momentumRange_eq_Ico (n : ℕ) :
    momentumRange n = Finset.Ico ((n : ℤ) / 2 - n + 1) ((n : ℤ) / 2 - n + 1 + n) := by
  ext a
  simp only [momentumRange, Finset.mem_Ioc, Finset.mem_Ico]
  omega
def momentumFinset (n : ℕ) : Finset (Fin 4 → ℝ) :=
  (Fintype.piFinset fun _ : Fin 4 => momentumRange n).image (momentumVec n)
theorem coe_momentumFinset {n : ℕ} (hn : n ≠ 0) :
    (momentumFinset n : Set (Fin 4 → ℝ)) = momentumSet n := by
  rw [momentumSet_eq_image hn, momentumFinset, Finset.coe_image]
theorem sum_momentumFinset_expWave (n : ℕ) [NeZero n] (z : Fin 4 → ℤ) :
    ∑ k ∈ momentumFinset n, expWave k z =
      if ∀ μ, (n : ℤ) ∣ z μ then (n : ℂ) ^ 4 else 0 := by
  rw [momentumFinset, Finset.sum_image fun _ _ _ _ h => momentumVec_injective (NeZero.ne n) h,
    ← sum_piFinset_prod_unityRootPow n z ((n : ℤ) / 2 - n + 1), ← momentumRange_eq_Ico]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [expWave_momentumVec]
  exact Finset.prod_congr rfl fun μ _ => unityRootPow_comm n _ _
theorem forall_dvd_sub_iff_zmodClass_eq (n : ℕ) (a b : Fin 4 → ℤ) :
    (∀ μ, (n : ℤ) ∣ b μ - a μ) ↔ zmodClass n a = zmodClass n b := by
  constructor
  · intro h
    funext μ
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (h μ)
  · intro h μ
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (congrFun h μ)
theorem forall_dvd_iff_zmodClass_eq_zero (n : ℕ) (z : Fin 4 → ℤ) :
    (∀ μ, (n : ℤ) ∣ z μ) ↔ zmodClass n z = zmodClass n 0 := by
  rw [eq_comm, ← forall_dvd_sub_iff_zmodClass_eq]
  simp
theorem classSum_expWave_sub (n : ℕ) [NeZero n] {k k' : Fin 4 → ℝ} (hk : k ∈ momentumSet n)
    (hk' : k' ∈ momentumSet n) :
    classSum n (expWave (k - k')) = (n : ℂ) ^ 4 * (propIndicator (k = k') : ℂ) := by
  rw [momentumSet_eq_image (NeZero.ne n)] at hk hk'
  obtain ⟨m, hm, rfl⟩ := hk
  obtain ⟨m', hm', rfl⟩ := hk'
  have hsub : momentumVec n m - momentumVec n m' = momentumVec n (m - m') := by
    funext μ
    simp only [momentumVec, Pi.sub_apply]
    push_cast
    ring
  have hm2 := Fintype.mem_piFinset.1 (Finset.mem_coe.1 hm)
  have hm2' := Fintype.mem_piFinset.1 (Finset.mem_coe.1 hm')
  have key : (∀ μ, (n : ℤ) ∣ (m - m') μ) ↔ momentumVec n m = momentumVec n m' := by
    constructor
    · intro h
      have hmm : m = m' := by
        funext μ
        have h1 := mem_momentumRange.1 (hm2 μ)
        have h2 := mem_momentumRange.1 (hm2' μ)
        have h3 : m μ - m' μ = 0 := by
          refine Int.eq_zero_of_abs_lt_dvd (h μ) ?_
          rw [abs_lt]
          omega
        omega
      rw [hmm]
    · intro h μ
      rw [momentumVec_injective (NeZero.ne n) h]
      simp
  rw [classSum_eq_sum_residueCube, hsub, sum_residueCube_expWave]
  simp only [key, propIndicator]
  split_ifs <;> simp
theorem fourier_inversion_sum (n : ℕ) [NeZero n] {f : (Fin 4 → ℤ) → ℂ} (hf : IsClassFunction n f)
    (z : Fin 4 → ℤ) :
    ∑ k ∈ momentumFinset n,
        classSum n (fun y => f y * expWave (-k) y) * expWave k z =
      (n : ℂ) ^ 4 * f z := by
  simp only [classSum_eq_sum_residueCube, Finset.sum_mul]
  rw [Finset.sum_comm]
  have term : ∀ a ∈ residueCube n,
      ∑ k ∈ momentumFinset n, f a * expWave (-k) a * expWave k z =
        f a * if ∀ μ, (n : ℤ) ∣ (z - a) μ then (n : ℂ) ^ 4 else 0 := by
    intro a _
    rw [← sum_momentumFinset_expWave, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [expWave_sub, mul_assoc]
  rw [Finset.sum_congr rfl term, Finset.sum_eq_single (residueLift (zmodClass n z))]
  · have hdvd : ∀ μ, (n : ℤ) ∣ (z - residueLift (zmodClass n z)) μ :=
      (forall_dvd_sub_iff_zmodClass_eq n _ _).2 (zmodClass_residueLift _)
    rw [if_pos hdvd, mul_comm]
    congr 1
    exact evalAtClass_zmodClass hf z
  · intro a ha hne
    rw [if_neg, mul_zero]
    intro hdvd
    apply hne
    have h := (forall_dvd_sub_iff_zmodClass_eq n a z).1 hdvd
    rw [← h, residueLift_zmodClass ha]
  · intro h
    exact absurd (residueLift_mem_residueCube _) h
theorem expWaveCharacters (n : ℕ) [NeZero n] : ExpWaveCharacters n := by
  refine ⟨momentumSet_ncard (NeZero.ne n), fun k hk => ?_, fun k hk k' hk' => classSum_expWave_sub n hk hk',
    fun f f' hf hf' h => funext fun z => ?_⟩
  · exact (isPeriodicModulo_iff _).2
      ⟨expWaveOnTorus k, funext fun a => (expWaveOnTorus_zmodClass hk a).symm⟩
  · have e : ∑ k ∈ momentumFinset n,
          classSum n (fun y => f y * expWave (-k) y) * expWave k z =
        ∑ k ∈ momentumFinset n,
          classSum n (fun y => f' y * expWave (-k) y) * expWave k z := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ∈ momentumSet n := by
        rw [← coe_momentumFinset (NeZero.ne n)]
        exact hk
      rw [h k hk']
    rw [fourier_inversion_sum n hf z, fourier_inversion_sum n hf' z] at e
    exact mul_left_cancel₀ (pow_ne_zero 4 (Nat.cast_ne_zero.2 (NeZero.ne n))) e
theorem expWave_zero (z : Fin 4 → ℤ) : expWave 0 z = 1 := by
  simp [expWave, wavePairing]
theorem zero_mem_momentumFinset (n : ℕ) [NeZero n] : (0 : Fin 4 → ℝ) ∈ momentumFinset n := by
  have h : (0 : Fin 4 → ℝ) ∈ momentumSet n := by
    refine ⟨⟨0, fun μ => by simp⟩, fun μ => ⟨?_, ?_⟩⟩
    · simpa using Real.pi_pos
    · simpa using Real.pi_pos.le
  rw [← coe_momentumFinset (NeZero.ne n)] at h
  exact h
theorem discreteLaplacianOfGreen_of_laplacian (n : ℕ) [NeZero n]
    (hL : ∀ k : Fin 4 → ℝ,
      discreteLaplacian (expWave k) = fun z => (laplacianSymbol k : ℂ) * expWave k z) :
    DiscreteLaplacianOfGreen n := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have hF : (((momentumFinset n).erase 0 : Finset (Fin 4 → ℝ)) : Set (Fin 4 → ℝ)) =
      momentumSet n \ {0} := by
    rw [Finset.coe_erase, coe_momentumFinset (NeZero.ne n)]
  have hΦ : greenOnVectors n = (1 / (n : ℂ) ^ 4) •
      ∑ k ∈ (momentumFinset n).erase 0, ((laplacianSymbol k : ℂ)⁻¹) • expWave k := by
    funext a
    rw [greenOnVectors_apply, ← hF, finsum_mem_coe_finset]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [div_eq_inv_mul]
  have hterm : ∀ k ∈ (momentumFinset n).erase 0,
      discreteLaplacianLinear ℂ (((laplacianSymbol k : ℂ)⁻¹) • expWave k) = expWave k := by
    intro k hk
    have hk' : k ∈ momentumSet n \ {0} := by
      rw [← hF]
      exact hk
    have hpos : (laplacianSymbol k : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (laplacianSymbol_pos hk').ne'
    rw [map_smul]
    change ((laplacianSymbol k : ℂ)⁻¹) • discreteLaplacian (expWave k) = expWave k
    rw [hL]
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hpos, one_mul]
  funext z
  change discreteLaplacianLinear ℂ (greenOnVectors n) z = _
  rw [hΦ, map_smul, map_sum, Finset.sum_congr rfl hterm]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hs := Finset.add_sum_erase (momentumFinset n) (fun k => expWave k z)
    (zero_mem_momentumFinset n)
  rw [sum_momentumFinset_expWave] at hs
  simp only [expWave_zero] at hs
  have hsum : ∑ k ∈ (momentumFinset n).erase 0, expWave k z =
      (if ∀ μ, (n : ℤ) ∣ z μ then (n : ℂ) ^ 4 else 0) - 1 := by
    rw [← hs]
    ring
  rw [hsum, deltaAtZeroClass]
  simp only [forall_dvd_iff_zmodClass_eq_zero, propIndicator]
  split_ifs <;> simp
  field_simp
def sqSum (u : Fin 4 → ℝ) : ℝ := ∑ μ, u μ ^ 2
theorem euclidNorm_sq (u : Fin 4 → ℝ) : euclidNorm u ^ 2 = sqSum u := by apply _root_.YangMills.Construction.FreeKernel.HeatKernelGreen.Continuum.realVecNorm_sq <;> assumption
theorem sqSum_ne_zero {u : Fin 4 → ℝ} (hu : u ≠ 0) : sqSum u ≠ 0 := by apply _root_.YangMills.Construction.Exterior.PropagatorProperties.sum_sq_ne_zero_of_ne_zero <;> assumption
theorem continuumGreenFunction_eq_sqSum (u : Fin 4 → ℝ) :
    continuumGreenFunction u = 1 / (4 * Real.pi ^ 2 * sqSum u) := by
  rw [continuumGreenFunction_eq, euclidNorm_sq]
theorem self_add_zero_smul (x v : Fin 4 → ℝ) : x + (0 : ℝ) • v = x := by simp
theorem hasDerivAt_sqSum_line (x : Fin 4 → ℝ) (ν : Fin 4) :
    HasDerivAt (fun t : ℝ => sqSum (x + t • unitVec ν)) (2 * x ν) 0 := by apply _root_.YangMills.Construction.FreeKernel.HeatKernelGreen.Continuum.hasDerivAt_sqSum_line <;> assumption
def greenFirstPartial (ν : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  -(2 * x ν) / (4 * Real.pi ^ 2 * sqSum x ^ 2)
theorem hasLineDerivAt_continuumGreenFunction {x : Fin 4 → ℝ} (hx : x ≠ 0) (ν : Fin 4) :
    HasLineDerivAt ℝ continuumGreenFunction (greenFirstPartial ν x) x (unitVec ν) := by
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hS := sqSum_ne_zero hx
  have hd := (hasDerivAt_sqSum_line x ν).const_mul (4 * Real.pi ^ 2)
  have hne : 4 * Real.pi ^ 2 * sqSum (x + (0 : ℝ) • unitVec ν) ≠ 0 := by
    rw [self_add_zero_smul]
    positivity
  have h := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_div hd hne
  have hfun : (fun t : ℝ => continuumGreenFunction (x + t • unitVec ν)) =
      fun t => 1 / (4 * Real.pi ^ 2 * sqSum (x + t • unitVec ν)) :=
    funext fun t => continuumGreenFunction_eq_sqSum _
  unfold HasLineDerivAt
  rw [hfun]
  refine h.congr_deriv ?_
  rw [self_add_zero_smul, greenFirstPartial]
  field_simp
  ring
theorem eventually_add_smul_ne_zero {x : Fin 4 → ℝ} (hx : x ≠ 0) (v : Fin 4 → ℝ) :
    ∀ᶠ t : ℝ in nhds 0, x + t • v ≠ 0 := by
  have hc : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
  have h0 : (fun t : ℝ => x + t • v) 0 ≠ 0 := by
    simpa using hx
  exact hc.eventually_ne h0
theorem hasLineDerivAt_coordPartialDeriv {x : Fin 4 → ℝ} (hx : x ≠ 0) (ν ν' : Fin 4) :
    HasLineDerivAt ℝ (coordPartialDeriv ν' continuumGreenFunction)
      (-(1 / (2 * Real.pi ^ 2 * euclidNorm x ^ 4)) *
        (kronecker ν ν' - 4 * x ν * x ν' / euclidNorm x ^ 2)) x (unitVec ν) := by
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hS := sqSum_ne_zero hx
  have hS0 : sqSum (x + (0 : ℝ) • unitVec ν) ≠ 0 := by
    rwa [self_add_zero_smul]
  have hnum : HasDerivAt (fun t : ℝ => -(2 * (x + t • unitVec ν) ν'))
      (-(2 * kronecker ν ν')) 0 := by
    have hδ : unitVec ν ν' = kronecker ν ν' := by
      by_cases h : ν = ν'
      · subst h
        simp [unitVec, kronecker, propIndicator]
      · simp [unitVec, kronecker, propIndicator, h, Ne.symm h]
    have h1 : HasDerivAt (fun t : ℝ => x ν' + t * unitVec ν ν') (unitVec ν ν') 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (unitVec ν ν')).const_add (x ν')
    have h2 := (h1.const_mul 2).neg
    rw [hδ] at h2
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp [hδ]
  have hden := ((hasDerivAt_sqSum_line x ν).fun_pow 2).const_mul (4 * Real.pi ^ 2)
  have hne : 4 * Real.pi ^ 2 * sqSum (x + (0 : ℝ) • unitVec ν) ^ 2 ≠ 0 := by
    positivity
  have hquot := hnum.fun_div hden hne
  have hev : (fun t : ℝ => coordPartialDeriv ν' continuumGreenFunction (x + t • unitVec ν)) =ᶠ[nhds 0]
      fun t => -(2 * (x + t • unitVec ν) ν') /
        (4 * Real.pi ^ 2 * sqSum (x + t • unitVec ν) ^ 2) := by
    filter_upwards [eventually_add_smul_ne_zero hx (unitVec ν)] with t ht
    exact (hasLineDerivAt_continuumGreenFunction ht ν').lineDeriv
  unfold HasLineDerivAt
  refine (hquot.congr_of_eventuallyEq hev).congr_deriv ?_
  have hn2 : euclidNorm x ^ 2 = sqSum x := euclidNorm_sq x
  have hn4 : euclidNorm x ^ 4 = sqSum x ^ 2 := by
    rw [← hn2]
    ring
  rw [hn2, hn4]
  simp only [self_add_zero_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring
theorem continuumGreenSecondPartials : ContinuumGreenSecondPartials := by
  intro ν ν' u hu
  have h := hasLineDerivAt_coordPartialDeriv hu ν ν'
  exact ⟨(hasLineDerivAt_continuumGreenFunction hu ν').lineDifferentiableAt, h.lineDifferentiableAt,
    h.lineDeriv⟩
end FourierFactsAndGreenIdentities
open FourierFactsAndGreenIdentities in
theorem FourierFactsAndGreenIdentities.proof
    (h : ShortDistanceTwoPoint.SymbolAndGreenFunctions) :
    FourierFactsAndGreenIdentities.Statement := by
  intro n _ hn
  obtain ⟨hw, hb, -, -, -⟩ := h n hn
  exact ⟨expWaveMultipliers_of_laplacian hw.1, laplacianSymbolModulusFormAndBounds_of_comparable hb,
    expWaveCharacters n, discreteLaplacianOfGreen_of_laplacian n hw.1, continuumGreenSecondPartials⟩
end YangMills.Construction.PeriodicLattice.VectorClasses
end
