import YangMills.Construction.LawInAState.ReflectionKernelAtADistanceProof
import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.EnergyMomentum.ArcoshCurveChordProof
import YangMills.Construction.LatticeForms.LatticeSymbolAndTheTwoGreensFunctions
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate ContDiff
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint.SymbolAndGreen
open YangMills.Construction.TorusMetric
theorem cos_eq_one_sub_two_mul_sin_half_sq (t : ℝ) :
    Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by apply _root_.YangMills.Construction.EnergyMomentum.ArcoshCurve.cos_eq_one_sub_two_sin_half_sq <;> assumption
theorem cexp_add_cexp_neg_sub_two (t : ℝ) :
    Complex.exp (Complex.I * t) + Complex.exp (-(Complex.I * t)) - 2 =
      -((4 * Real.sin (t / 2) ^ 2 : ℝ) : ℂ) := by
  have hsum : Complex.exp (Complex.I * t) + Complex.exp (-(Complex.I * t)) =
      2 * (Real.cos t : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos]
    have ha : (t : ℂ) * Complex.I = Complex.I * t := mul_comm _ _
    have hb : -(t : ℂ) * Complex.I = -(Complex.I * t) := by ring
    rw [ha, hb]
    ring
  rw [hsum, cos_eq_one_sub_two_mul_sin_half_sq]
  push_cast
  ring
theorem discreteLaplacian_of_shift {A : Type*} [Ring A] (f : (Fin 4 → A) → ℂ) (k : Fin 4 → ℝ)
    (hshift : ∀ μ z, f (z + unitVector μ) = Complex.exp (Complex.I * k μ) * f z) :
    discreteLaplacian f = fun z => (laplacianSymbol k : ℂ) * f z := by
  funext z
  have hback : ∀ μ, f (z - unitVector μ) = Complex.exp (-(Complex.I * k μ)) * f z := by
    intro μ
    have hz := hshift μ (z - unitVector μ)
    rw [sub_add_cancel] at hz
    rw [hz, ← mul_assoc, ← Complex.exp_add]
    simp
  have hterm : ∀ μ, backwardDiff μ (forwardDiff μ f) z =
      -((4 * Real.sin (k μ / 2) ^ 2 : ℝ) : ℂ) * f z := by
    intro μ
    simp only [backwardDiff, forwardDiff, sub_add_cancel]
    rw [hshift μ z, hback μ, ← cexp_add_cexp_neg_sub_two]
    ring
  simp only [discreteLaplacian, Pi.neg_apply, Finset.sum_apply, hterm, laplacianSymbol]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring
theorem expWave_add_unitVector (k : Fin 4 → ℝ) (N : Fin 4 → ℤ) (μ : Fin 4) :
    expWave k (N + unitVector μ) = Complex.exp (Complex.I * k μ) * expWave k N := by
  have hpair : wavePairing k (N + unitVector μ) = k μ + wavePairing k N := by
    simp only [wavePairing, unitVector, Pi.add_apply, Pi.single_apply]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
    simp [add_comm]
  simp only [expWave, hpair]
  push_cast
  rw [mul_add, Complex.exp_add]
section OnTorus
variable {n : ℕ} [NeZero n]
theorem add_unitVector_eq (z : IntegerTorus n) (μ : Fin 4) :
    z + unitVector μ = zmodClass n (residueLift z + unitVector μ) := by
  funext ν
  simp only [zmodClass, residueLift, unitVector, Pi.add_apply, Pi.single_apply]
  split_ifs <;> simp
theorem expWaveOnTorus_add_unitVector {k : Fin 4 → ℝ} (hk : k ∈ momentumSet n)
    (z : IntegerTorus n) (μ : Fin 4) :
    expWaveOnTorus k (z + unitVector μ) =
      Complex.exp (Complex.I * k μ) * expWaveOnTorus k z := by
  rw [add_unitVector_eq, expWaveOnTorus_zmodClass hk, expWave_add_unitVector]
  rfl
end OnTorus
theorem expWavesAreEigenvectors (n : ℕ) [NeZero n] : ExpWavesAreEigenvectors n :=
  ⟨fun k => discreteLaplacian_of_shift _ k fun μ z => expWave_add_unitVector k z μ,
    fun _ hk => discreteLaplacian_of_shift _ _ fun μ z => expWaveOnTorus_add_unitVector hk z μ⟩
theorem euclidNormVec_sq_eq_sum (k : Fin 4 → ℝ) : euclidNormVec k ^ 2 = ∑ μ, k μ ^ 2 := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_sq <;> assumption
theorem symbolComparableToSquare : SymbolComparableToSquare := by
  intro k hk
  rw [euclidNormVec_sq_eq_sum]
  simp only [laplacianSymbol]
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun μ _ => ?_
    have habs : |k μ / 2| ≤ Real.pi / 2 := by
      rw [abs_le]
      have := (hk μ).1
      have := (hk μ).2
      constructor <;> linarith
    have hjordan := Real.mul_abs_le_abs_sin habs
    have hnn : 0 ≤ 2 / Real.pi * |k μ / 2| := by positivity
    have hsq := pow_le_pow_left₀ hnn hjordan 2
    rw [mul_pow, sq_abs, sq_abs] at hsq
    have hrw : 4 / Real.pi ^ 2 * k μ ^ 2 = 4 * ((2 / Real.pi) ^ 2 * (k μ / 2) ^ 2) := by
      field_simp
    rw [hrw]
    linarith
  · refine Finset.sum_le_sum fun μ _ => ?_
    have hsin := Real.sin_sq_le_sq (x := k μ / 2)
    have hrw : k μ ^ 2 = 4 * (k μ / 2) ^ 2 := by ring
    rw [hrw]
    linarith
section KernelOfPinv
variable {n : ℕ} [NeZero n]
def momentumFinset (n : ℕ) : Finset (Fin 4 → ℝ) :=
  (Fintype.piFinset fun _ : Fin 4 => momentumRange n).image (momentumVec n)
theorem coe_momentumFinset : (momentumFinset n : Set (Fin 4 → ℝ)) = momentumSet n := by
  rw [momentumFinset, Finset.coe_image, momentumSet_eq_image (NeZero.ne n)]
theorem mem_erase_momentumFinset {k : Fin 4 → ℝ} :
    k ∈ (momentumFinset n).erase 0 ↔ k ∈ momentumSet n \ {0} := by
  rw [← coe_momentumFinset, Finset.mem_erase]
  simp only [Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
  tauto
theorem latticeGreenFunction_eq (z : IntegerTorus n) :
    latticeGreenFunction n z = 1 / (n : ℂ) ^ 4 *
      ∑ k ∈ (momentumFinset n).erase 0, expWaveOnTorus k z / (laplacianSymbol k : ℂ) := by
  have hset : momentumSet n \ {0} = ((momentumFinset n).erase 0 : Finset (Fin 4 → ℝ)) := by
    rw [Finset.coe_erase, coe_momentumFinset]
  rw [latticeGreenFunction, hset, finsum_mem_coe_finset]
omit [NeZero n] in
theorem zero_mem_momentumSet : (0 : Fin 4 → ℝ) ∈ momentumSet n := by
  refine ⟨⟨0, by simp⟩, fun μ => ⟨?_, ?_⟩⟩ <;> simp [Real.pi_pos, Real.pi_pos.le]
omit [NeZero n] in
theorem expWaveOnTorus_zero (z : IntegerTorus n) : expWaveOnTorus 0 z = 1 := by
  simp [expWaveOnTorus, expWave, wavePairing]
theorem sum_expWaveOnTorus {k : Fin 4 → ℝ} (hk : k ∈ momentumSet n \ {0}) :
    ∑ z : IntegerTorus n, expWaveOnTorus k z = 0 := by
  obtain ⟨hkm, hk0⟩ := hk
  obtain ⟨μ, hμ⟩ : ∃ μ, k μ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hk0 (funext hall)
  have hne : Complex.exp (Complex.I * k μ) ≠ 1 := by
    intro hone
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hone
    have hmc : (k μ : ℂ) = ((2 * Real.pi * m : ℝ) : ℂ) := by
      have hI := Complex.I_ne_zero
      push_cast
      apply mul_left_cancel₀ hI
      rw [hm]
      ring
    have hkr : k μ = 2 * Real.pi * m := by exact_mod_cast hmc
    obtain ⟨hlo, hhi⟩ := hkm.2 μ
    rw [hkr] at hlo hhi
    have hm1 : (-1 : ℝ) < 2 * m := by nlinarith
    have hm2 : (2 : ℝ) * m ≤ 1 := by nlinarith
    have hm1z : (-1 : ℤ) < 2 * m := by exact_mod_cast hm1
    have hm2z : (2 : ℤ) * m ≤ 1 := by exact_mod_cast hm2
    have hm0 : m = 0 := by omega
    apply hμ
    rw [hkr, hm0]
    simp
  have hshift : ∑ z : IntegerTorus n, expWaveOnTorus k (z + unitVector μ) =
      ∑ z : IntegerTorus n, expWaveOnTorus k z :=
    Equiv.sum_comp (Equiv.addRight (unitVector μ)) (expWaveOnTorus k)
  simp_rw [expWaveOnTorus_add_unitVector hkm] at hshift
  rw [← Finset.mul_sum] at hshift
  have hprod : (Complex.exp (Complex.I * k μ) - 1) *
      ∑ z : IntegerTorus n, expWaveOnTorus k z = 0 := by
    rw [sub_mul, hshift, one_mul, sub_self]
  exact (mul_eq_zero.1 hprod).resolve_left (sub_ne_zero.2 hne)
theorem geomSum_Ioc_mul (ζ : ℂ) (hζ : ζ ≠ 0) (a : ℤ) (m : ℕ) :
    (ζ - 1) * ∑ N ∈ Finset.Ioc a (a + m), ζ ^ N = ζ ^ (a + m + 1) - ζ ^ (a + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hins : Finset.Ioc a (a + ((m + 1 : ℕ) : ℤ)) =
        insert (a + m + 1) (Finset.Ioc a (a + m)) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      push_cast
      omega
    rw [hins, Finset.sum_insert (by simp), mul_add, ih]
    push_cast
    rw [show a + ((m : ℤ) + 1) + 1 = a + m + 1 + 1 by ring, zpow_add₀ hζ (a + m + 1) 1, zpow_one]
    ring
theorem sum_momentumRange_cexp (r : ℕ) (hr : r < n) :
    ∑ N ∈ momentumRange n,
        Complex.exp (Complex.I * ((2 * Real.pi / n * (N : ℝ) * (r : ℝ) : ℝ) : ℂ)) =
      if r = 0 then (n : ℂ) else 0 := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  split_ifs with hr0
  · subst hr0
    simp [card_momentumRange]
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * r / n) with hζdef
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hterm : ∀ N : ℤ,
      Complex.exp (Complex.I * ((2 * Real.pi / n * (N : ℝ) * (r : ℝ) : ℝ) : ℂ)) = ζ ^ N := by
    intro N
    rw [hζdef, ← Complex.exp_int_mul]
    congr 1
    push_cast
    field_simp
  have hζn : ζ ^ (n : ℤ) = 1 := by
    rw [hζdef, ← Complex.exp_int_mul, Complex.exp_eq_one_iff]
    refine ⟨r, ?_⟩
    push_cast
    field_simp
  have hζ1 : ζ ≠ 1 := by
    intro hone
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hone
    have htwo : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have hrc : (r : ℂ) = m * n := by
      apply mul_left_cancel₀ htwo
      field_simp at hm
      rw [hm]
      ring
    have hrz : (r : ℤ) = m * n := by exact_mod_cast hrc
    have hrpos : 0 < (r : ℤ) := by omega
    have hrlt : (r : ℤ) < n := by exact_mod_cast hr
    have hnpos : (0 : ℤ) < n := by omega
    have hmpos : 0 < m := by
      by_contra hc
      push Not at hc
      nlinarith
    nlinarith
  simp_rw [hterm]
  have hidx : momentumRange n = Finset.Ioc ((n : ℤ) / 2 - n) ((n : ℤ) / 2 - n + (n : ℕ)) := by
    simp [momentumRange]
  rw [hidx]
  have hgeom := geomSum_Ioc_mul ζ hζ0 ((n : ℤ) / 2 - n) n
  have hwrap : ζ ^ ((n : ℤ) / 2 - n + n + 1) = ζ ^ ((n : ℤ) / 2 - n + 1) := by
    rw [show (n : ℤ) / 2 - n + n + 1 = (n : ℤ) / 2 - n + 1 + n by ring, zpow_add₀ hζ0, hζn,
      mul_one]
  rw [hwrap, sub_self] at hgeom
  exact (mul_eq_zero.1 hgeom).resolve_left (sub_ne_zero.2 hζ1)
theorem sum_momentumFinset_expWaveOnTorus (z : IntegerTorus n) :
    ∑ k ∈ momentumFinset n, expWaveOnTorus k z = if z = 0 then (n : ℂ) ^ 4 else 0 := by
  rw [momentumFinset, Finset.sum_image fun a _ b _ h => momentumVec_injective (NeZero.ne n) h]
  have hterm : ∀ N : Fin 4 → ℤ, expWaveOnTorus (momentumVec n N) z =
      ∏ μ, Complex.exp (Complex.I *
        ((2 * Real.pi / n * (N μ : ℝ) * (((z μ).val : ℕ) : ℝ) : ℝ) : ℂ)) := by
    intro N
    rw [← Complex.exp_sum]
    simp only [expWaveOnTorus, expWave, wavePairing, momentumVec, residueLift]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  simp_rw [hterm]
  rw [← Finset.prod_univ_sum (t := fun _ : Fin 4 => momentumRange n)
    (f := fun μ N => Complex.exp (Complex.I *
      ((2 * Real.pi / n * (N : ℝ) * (((z μ).val : ℕ) : ℝ) : ℝ) : ℂ)))]
  simp_rw [fun μ => sum_momentumRange_cexp (n := n) (z μ).val (ZMod.val_lt (z μ))]
  split_ifs with hz
  · subst hz
    simp
  · obtain ⟨μ, hμ⟩ : ∃ μ, z μ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hz (funext hall)
    refine Finset.prod_eq_zero (Finset.mem_univ μ) ?_
    rw [if_neg]
    rwa [ZMod.val_eq_zero]
def reflectMomentum (k : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun μ => if k μ = Real.pi then Real.pi else -k μ
omit [NeZero n] in
theorem reflectMomentum_mem {k : Fin 4 → ℝ} (hk : k ∈ momentumSet n \ {0}) :
    reflectMomentum k ∈ momentumSet n \ {0} := by
  obtain ⟨⟨⟨N, hN⟩, hI⟩, hk0⟩ := hk
  have hpi := Real.pi_pos
  refine ⟨⟨⟨fun μ => if k μ = Real.pi then N μ else -N μ, fun μ => ?_⟩, fun μ => ?_⟩, ?_⟩
  · simp only [reflectMomentum]
    split_ifs with heq
    · rw [← hN μ, heq]
    · rw [hN μ]
      push_cast
      ring
  · simp only [reflectMomentum]
    obtain ⟨hlo, hhi⟩ := hI μ
    split_ifs with heq
    · exact ⟨by linarith, le_rfl⟩
    · have hlt := lt_of_le_of_ne hhi heq
      exact ⟨by linarith, by linarith⟩
  · intro hrefl
    apply hk0
    funext μ
    have hμ := congrFun (Set.mem_singleton_iff.1 hrefl) μ
    simp only [reflectMomentum, Pi.zero_apply] at hμ ⊢
    split_ifs at hμ with heq
    · exact absurd hμ hpi.ne'
    · linarith
omit [NeZero n] in
theorem reflectMomentum_reflectMomentum {k : Fin 4 → ℝ} (hk : k ∈ momentumSet n) :
    reflectMomentum (reflectMomentum k) = k := by
  funext μ
  obtain ⟨hlo, -⟩ := hk.2 μ
  simp only [reflectMomentum]
  by_cases heq : k μ = Real.pi
  · simp [heq]
  · have hneg : -k μ ≠ Real.pi := fun h2 => by linarith
    simp [heq, hneg]
theorem laplacianSymbol_reflectMomentum (k : Fin 4 → ℝ) :
    laplacianSymbol (reflectMomentum k) = laplacianSymbol k := by
  simp only [laplacianSymbol, reflectMomentum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  split_ifs with heq
  · rw [heq]
  · rw [neg_div, Real.sin_neg, neg_sq]
theorem expWave_reflectMomentum (k : Fin 4 → ℝ) (N : Fin 4 → ℤ) :
    expWave (reflectMomentum k) N = conj (expWave k N) := by
  simp only [expWave]
  rw [← Complex.exp_conj, Complex.exp_eq_exp_iff_exists_int]
  obtain ⟨M, hM⟩ : ∃ M : ℤ, M = ∑ μ, if k μ = Real.pi then N μ else 0 := ⟨_, rfl⟩
  refine ⟨M, ?_⟩
  have hpair : wavePairing (reflectMomentum k) N =
      -wavePairing k N + 2 * Real.pi * (M : ℝ) := by
    rw [hM]
    simp only [wavePairing, reflectMomentum]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    split_ifs with heq
    · rw [heq]
      ring
    · ring
  rw [hpair]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring
theorem conj_latticeGreenFunction (z : IntegerTorus n) :
    conj (latticeGreenFunction n z) = latticeGreenFunction n z := by
  rw [latticeGreenFunction_eq, map_mul, map_sum]
  congr 1
  · simp
  · refine Finset.sum_nbij' reflectMomentum reflectMomentum ?_ ?_ ?_ ?_ ?_
    · intro k hk
      exact mem_erase_momentumFinset.2 (reflectMomentum_mem (mem_erase_momentumFinset.1 hk))
    · intro k hk
      exact mem_erase_momentumFinset.2 (reflectMomentum_mem (mem_erase_momentumFinset.1 hk))
    · intro k hk
      exact reflectMomentum_reflectMomentum (mem_erase_momentumFinset.1 hk).1
    · intro k hk
      exact reflectMomentum_reflectMomentum (mem_erase_momentumFinset.1 hk).1
    · intro k _
      rw [laplacianSymbol_reflectMomentum, map_div₀, Complex.conj_ofReal]
      simp only [expWaveOnTorus]
      rw [expWave_reflectMomentum]
def realGreen (n : ℕ) [NeZero n] (z : IntegerTorus n) : ℝ := (latticeGreenFunction n z).re
theorem coe_realGreen (z : IntegerTorus n) : (realGreen n z : ℂ) = latticeGreenFunction n z :=
  Complex.conj_eq_iff_re.1 (conj_latticeGreenFunction z)
theorem discreteLaplacian_latticeGreenFunction (z : IntegerTorus n) :
    discreteLaplacian (latticeGreenFunction n) z =
      (if z = 0 then 1 else 0) - 1 / (n : ℂ) ^ 4 := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hfun : latticeGreenFunction n = (1 / (n : ℂ) ^ 4) • ∑ k ∈ (momentumFinset n).erase 0,
      (laplacianSymbol k : ℂ)⁻¹ • expWaveOnTorus (n := n) k := by
    funext w
    simp only [latticeGreenFunction_eq, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      div_eq_mul_inv, mul_comm]
  have hop : discreteLaplacian (latticeGreenFunction n) =
      (discreteLaplacianLinear ℂ : (IntegerTorus n → ℂ) →ₗ[ℂ] IntegerTorus n → ℂ)
        (latticeGreenFunction n) := rfl
  have heig : ∀ k ∈ (momentumFinset n).erase 0,
      (laplacianSymbol k : ℂ)⁻¹ • (discreteLaplacianLinear ℂ :
        (IntegerTorus n → ℂ) →ₗ[ℂ] IntegerTorus n → ℂ) (expWaveOnTorus k) =
        expWaveOnTorus k := by
    intro k hk
    have hm := mem_erase_momentumFinset.1 hk
    have hω : (laplacianSymbol k : ℂ) ≠ 0 := by exact_mod_cast (laplacianSymbol_pos hm).ne'
    have hL := (expWavesAreEigenvectors n).2 k hm.1
    change (laplacianSymbol k : ℂ)⁻¹ • discreteLaplacian (expWaveOnTorus k) = _
    rw [hL]
    funext w
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [hop, hfun, map_smul, map_sum]
  simp_rw [map_smul]
  rw [Finset.sum_congr rfl heig]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hmem : (0 : Fin 4 → ℝ) ∈ momentumFinset n := by
    have hcoe : (0 : Fin 4 → ℝ) ∈ (momentumFinset n : Set (Fin 4 → ℝ)) := by
      rw [coe_momentumFinset]
      exact zero_mem_momentumSet
    exact_mod_cast hcoe
  have hsplit := Finset.add_sum_erase _ (fun k => expWaveOnTorus k z) hmem
  rw [sum_momentumFinset_expWaveOnTorus, expWaveOnTorus_zero] at hsplit
  have hrest : ∑ k ∈ (momentumFinset n).erase 0, expWaveOnTorus k z =
      (if z = 0 then (n : ℂ) ^ 4 else 0) - 1 := by
    rw [← hsplit]
    ring
  rw [hrest]
  split_ifs <;> field_simp <;> ring
theorem discreteLaplacian_realGreen (z : IntegerTorus n) :
    discreteLaplacian (realGreen n) z = (if z = 0 then 1 else 0) - 1 / (n : ℝ) ^ 4 := by
  apply Complex.ofReal_injective
  have hcast : ((discreteLaplacian (realGreen n) z : ℝ) : ℂ) =
      discreteLaplacian (latticeGreenFunction n) z := by
    simp only [discreteLaplacian, backwardDiff, forwardDiff, Pi.neg_apply, Finset.sum_apply]
    push_cast
    simp only [coe_realGreen]
  rw [hcast, discreteLaplacian_latticeGreenFunction]
  split_ifs <;> simp
theorem sum_realGreen : ∑ z : IntegerTorus n, realGreen n z = 0 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [coe_realGreen, latticeGreenFunction_eq]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.sum_div]
  rw [Finset.sum_eq_zero, mul_zero]
  intro k hk
  rw [sum_expWaveOnTorus (mem_erase_momentumFinset.1 hk), zero_div]
theorem torusInner_discreteLaplacian (f f' : IntegerTorus n → ℝ) :
    torusInner f (discreteLaplacian f') =
      ∑ μ : Fin 4, ∑ z, forwardDiff μ f z * forwardDiff μ f' z := by
  simp only [torusInner, discreteLaplacian, Pi.neg_apply, Finset.sum_apply, mul_neg,
    Finset.mul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  set g := forwardDiff μ f' with hg
  have hshift : ∑ z : IntegerTorus n, f z * g (z - unitVector μ) =
      ∑ z : IntegerTorus n, f (z + unitVector μ) * g z := by
    have hcomp := Equiv.sum_comp (Equiv.subRight (unitVector μ : IntegerTorus n))
      (fun z => f (z + unitVector μ) * g z)
    simpa using hcomp
  simp only [backwardDiff, mul_sub, Finset.sum_sub_distrib, hshift]
  simp only [forwardDiff, sub_mul, Finset.sum_sub_distrib]
  ring
theorem torusInner_comm (f f' : IntegerTorus n → ℝ) :
    torusInner f f' = torusInner f' f := by
  simp only [torusInner, mul_comm]
theorem discreteLaplacian_symm (f f' : IntegerTorus n → ℝ) :
    torusInner f (discreteLaplacian f') = torusInner (discreteLaplacian f) f' := by
  rw [torusInner_comm (discreteLaplacian f), torusInner_discreteLaplacian,
    torusInner_discreteLaplacian]
  simp only [mul_comm]
theorem discreteLaplacian_nonneg (f : IntegerTorus n → ℝ) :
    0 ≤ torusInner f (discreteLaplacian f) := by
  rw [torusInner_discreteLaplacian]
  exact Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun z _ => mul_self_nonneg _
abbrev euclidLaplacian (n : ℕ) [NeZero n] :
    EuclideanSpace ℝ (IntegerTorus n) →ₗ[ℝ] EuclideanSpace ℝ (IntegerTorus n) :=
  (torusEuclideanEquiv n).conj (discreteLaplacianLinear ℝ)
theorem euclidLaplacian_apply (f : IntegerTorus n → ℝ) :
    euclidLaplacian n (torusEuclideanEquiv n f) =
      torusEuclideanEquiv n (discreteLaplacian f) := by
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  rfl
theorem euclidLaplacian_isPositive : (euclidLaplacian n).IsPositive := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · obtain ⟨f, rfl⟩ := (torusEuclideanEquiv n).surjective x
    obtain ⟨f', rfl⟩ := (torusEuclideanEquiv n).surjective y
    rw [euclidLaplacian_apply, euclidLaplacian_apply, inner_torusEuclideanEquiv,
      inner_torusEuclideanEquiv, discreteLaplacian_symm]
  · obtain ⟨f, rfl⟩ := (torusEuclideanEquiv n).surjective x
    rw [euclidLaplacian_apply, inner_torusEuclideanEquiv, ← discreteLaplacian_symm]
    exact discreteLaplacian_nonneg f
theorem discreteLaplacianPinv_apply (f : IntegerTorus n → ℝ) :
    torusEuclideanEquiv n (discreteLaplacianPinv n f) =
      LatticeForms.moorePenrose (euclidLaplacian n) (torusEuclideanEquiv n f) := by
  simp [discreteLaplacianPinv, LinearEquiv.conj_apply_apply]
omit [NeZero n] in
theorem discreteLaplacian_translate (h : IntegerTorus n → ℝ) (w z : IntegerTorus n) :
    discreteLaplacian (fun x => h (x - w)) z = discreteLaplacian h (z - w) := by
  have hadd : ∀ a b : IntegerTorus n, a + b - w = a - w + b := fun a b => by abel
  have hsub : ∀ a b : IntegerTorus n, a - b - w = a - w - b := fun a b => by abel
  simp only [discreteLaplacian, backwardDiff, forwardDiff, Pi.neg_apply,
    Finset.sum_apply, hadd, hsub]
def greenShift (n : ℕ) [NeZero n] (w z : IntegerTorus n) : ℝ := realGreen n (z - w)
theorem discreteLaplacian_greenShift (w z : IntegerTorus n) :
    discreteLaplacian (greenShift n w) z = (if z = w then 1 else 0) - 1 / (n : ℝ) ^ 4 := by
  have hdef : greenShift n w = fun x => realGreen n (x - w) := rfl
  rw [hdef, discreteLaplacian_translate, discreteLaplacian_realGreen]
  simp only [sub_eq_zero]
theorem sum_greenShift (w : IntegerTorus n) : ∑ z, greenShift n w z = 0 := by
  have hcomp := Equiv.sum_comp (Equiv.subRight w) (realGreen n)
  simp only [Equiv.subRight_apply] at hcomp
  rw [← sum_realGreen (n := n), ← hcomp]
  rfl
theorem mem_range_euclidLaplacian (f : IntegerTorus n → ℝ) (hf : ∑ z, f z = 0) :
    torusEuclideanEquiv n f ∈ LinearMap.range (euclidLaplacian n) := by
  refine ⟨torusEuclideanEquiv n (∑ w, f w • greenShift n w), ?_⟩
  rw [euclidLaplacian_apply]
  congr 1
  funext z
  change (discreteLaplacianLinear ℝ : (IntegerTorus n → ℝ) →ₗ[ℝ] IntegerTorus n → ℝ) _ z = _
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change ∑ w, f w * discreteLaplacian (greenShift n w) z = _
  simp only [discreteLaplacian_greenShift, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hf]
  simp
theorem discreteLaplacianPinv_indicator (w : IntegerTorus n) :
    discreteLaplacianPinv n (torusIndicator w) = greenShift n w := by
  apply (torusEuclideanEquiv n).injective
  have hpos := euclidLaplacian_isPositive (n := n)
  have hind : torusIndicator w =
      discreteLaplacian (greenShift n w) + fun _ => 1 / (n : ℝ) ^ 4 := by
    funext z
    simp only [Pi.add_apply, discreteLaplacian_greenShift, torusIndicator, Pi.single_apply]
    ring
  have hconst : torusEuclideanEquiv n (fun _ => 1 / (n : ℝ) ^ 4) ∈
      LinearMap.ker (euclidLaplacian n) := by
    rw [LinearMap.mem_ker, euclidLaplacian_apply]
    have hzero : discreteLaplacian (fun _ : IntegerTorus n => 1 / (n : ℝ) ^ 4) = 0 := by
      funext z
      simp [discreteLaplacian, backwardDiff, forwardDiff]
    rw [hzero, map_zero]
  rw [discreteLaplacianPinv_apply, hind, map_add, map_add,
    LatticeForms.moorePenrose_apply_of_mem_ker hpos hconst, add_zero,
    ← euclidLaplacian_apply,
    LatticeForms.moorePenrose_apply_apply_of_mem hpos
      (mem_range_euclidLaplacian _ (sum_greenShift w))]
theorem pinvKernelIsLatticeGreen (n : ℕ) [NeZero n] : PinvKernelIsLatticeGreen n := by
  refine ⟨discreteLaplacian_symm, discreteLaplacian_nonneg, fun z => ?_, fun z z' => ?_⟩
  · exact Complex.conj_eq_iff_im.1 (conj_latticeGreenFunction z)
  · rw [kernelOf, discreteLaplacianPinv_indicator, ← coe_realGreen]
    congr 1
    simp [torusInner, torusIndicator, Pi.single_apply, greenShift]
end KernelOfPinv
section ContinuumKernel
open MeasureTheory Filter Topology
def normSq4 (u : Fin 4 → ℝ) : ℝ := ∑ μ, u μ ^ 2
theorem normSq4_nonneg (u : Fin 4 → ℝ) : 0 ≤ normSq4 u := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.sumSq_nonneg <;> assumption
theorem euclidNormVec_sq (u : Fin 4 → ℝ) : euclidNormVec u ^ 2 = normSq4 u := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_sq <;> assumption
theorem normSq4_line (u : Fin 4 → ℝ) (ν : Fin 4) (t : ℝ) :
    normSq4 (u + t • Pi.single ν (1 : ℝ)) = normSq4 u + 2 * t * u ν + t ^ 2 := by
  have hcoord : ∀ μ, (u μ + t * (Pi.single ν (1 : ℝ) : Fin 4 → ℝ) μ) ^ 2 =
      u μ ^ 2 + (if μ = ν then 2 * t * u ν + t ^ 2 else 0) := by
    intro μ
    by_cases hμ : μ = ν
    · subst hμ
      simp
      ring
    · simp [hμ]
  simp only [normSq4, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcoord, Finset.sum_add_distrib]
  simp
  ring
def inverseQuadratic (c a : ℝ) (u : Fin 4 → ℝ) : ℝ := c / (normSq4 u + a)
theorem hasDerivAt_shiftedDenom (u : Fin 4 → ℝ) (ν : Fin 4) (a : ℝ) :
    HasDerivAt (fun t : ℝ => normSq4 u + 2 * t * u ν + t ^ 2 + a) (2 * u ν) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * t * u ν) (2 * u ν) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (u ν)
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
    simpa using hasDerivAt_pow 2 (0 : ℝ)
  simpa [add_assoc] using ((hlin.add hsq).const_add (normSq4 u)).add_const a
theorem partialDerivR4_inverseQuadratic (c a : ℝ) (u : Fin 4 → ℝ) (ν : Fin 4)
    (h : normSq4 u + a ≠ 0) :
    TestFunctions.partialDerivR4 ν (inverseQuadratic c a) u =
      -2 * c * u ν / (normSq4 u + a) ^ 2 := by
  have hd := (hasDerivAt_shiftedDenom u ν a)
  have hline : (fun t : ℝ => inverseQuadratic c a (u + t • Pi.single ν (1 : ℝ))) =
      fun t => c / (normSq4 u + 2 * t * u ν + t ^ 2 + a) := by
    funext t
    rw [inverseQuadratic, normSq4_line]
  have h0 : normSq4 u + 2 * 0 * u ν + 0 ^ 2 + a ≠ 0 := by simpa using h
  have hder := (hasDerivAt_const (0 : ℝ) c).fun_div hd h0
  rw [TestFunctions.partialDerivR4, hline, hder.deriv]
  simp
  field_simp
theorem secondPartial_inverseQuadratic (c a : ℝ) (u : Fin 4 → ℝ) (ν ν' : Fin 4)
    (h : normSq4 u + a ≠ 0) :
    TestFunctions.partialDerivR4 ν (TestFunctions.partialDerivR4 ν' (inverseQuadratic c a)) u =
      c * (-2 * (if ν = ν' then 1 else 0) / (normSq4 u + a) ^ 2 +
        8 * u ν * u ν' / (normSq4 u + a) ^ 3) := by
  have hd := hasDerivAt_shiftedDenom u ν a
  have hcont : ContinuousAt (fun t : ℝ => normSq4 u + 2 * t * u ν + t ^ 2 + a) 0 :=
    hd.continuousAt
  have h0 : normSq4 u + 2 * 0 * u ν + 0 ^ 2 + a ≠ 0 := by simpa using h
  have hev : ∀ᶠ t : ℝ in 𝓝 0, normSq4 u + 2 * t * u ν + t ^ 2 + a ≠ 0 :=
    hcont.eventually_ne h0
  have hline : (fun t : ℝ => TestFunctions.partialDerivR4 ν' (inverseQuadratic c a)
      (u + t • Pi.single ν (1 : ℝ))) =ᶠ[𝓝 0]
      fun t => -2 * c * (u ν' + t * (if ν = ν' then 1 else 0)) /
        (normSq4 u + 2 * t * u ν + t ^ 2 + a) ^ 2 := by
    filter_upwards [hev] with t ht
    rw [partialDerivR4_inverseQuadratic c a _ ν' (by rwa [normSq4_line])]
    rw [normSq4_line]
    congr 2
    by_cases hν : ν = ν'
    · subst hν
      simp
    · simp [hν, Ne.symm hν]
  have hnum : HasDerivAt (fun t : ℝ => -2 * c * (u ν' + t * (if ν = ν' then 1 else 0)))
      (-2 * c * (if ν = ν' then 1 else 0)) 0 := by
    have hinner : HasDerivAt (fun t : ℝ => u ν' + t * (if ν = ν' then (1 : ℝ) else 0))
        (if ν = ν' then 1 else 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
        (if ν = ν' then (1 : ℝ) else 0)).const_add (u ν')
    exact hinner.const_mul _
  have hden := hd.fun_pow 2
  have hquot := hnum.fun_div hden (pow_ne_zero 2 h0)
  rw [TestFunctions.partialDerivR4, hline.deriv_eq, hquot.deriv]
  simp only [mul_zero, zero_mul, add_zero]
  have hzsq : (0 : ℝ) ^ 2 = 0 := by norm_num
  simp only [hzsq, add_zero]
  field_simp
  ring
theorem continuumGreenFunction_eq_inverseQuadratic :
    continuumGreenFunction = inverseQuadratic (1 / (4 * Real.pi ^ 2)) 0 := by
  funext u
  simp only [continuumGreenFunction, inverseQuadratic, euclidNormVec_sq, add_zero]
  rw [div_div]
theorem continuumGreenSecondDerivatives : ContinuumGreenSecondDerivatives := by
  intro u hu ν ν'
  have hq : normSq4 u ≠ 0 := by
    intro h
    apply hu
    funext μ
    have hμ := (Finset.sum_eq_zero_iff_of_nonneg (fun μ _ => sq_nonneg (u μ))).1 h μ
      (Finset.mem_univ _)
    simpa using hμ
  have hq' : normSq4 u + 0 ≠ 0 := by simpa using hq
  have h4 : euclidNormVec u ^ 4 = normSq4 u ^ 2 := by
    rw [← euclidNormVec_sq]
    ring
  rw [continuumGreenFunction_eq_inverseQuadratic, secondPartial_inverseQuadratic _ _ _ _ _ hq',
    h4, euclidNormVec_sq]
  simp only [add_zero]
  field_simp
  split_ifs <;> ring
theorem normSq4_smul (r : ℝ) (u : Fin 4 → ℝ) :
    normSq4 (r • u) = r ^ 2 * normSq4 u := by
  simp only [normSq4, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
theorem contDiff_normSq4 : ContDiff ℝ ∞ normSq4 := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.contDiff_sumSq <;> assumption
theorem contDiff_inverseQuadratic (c : ℝ) {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ ∞ (inverseQuadratic c a) := by
  unfold inverseQuadratic
  refine contDiff_const.div (contDiff_normSq4.add contDiff_const) fun u => ?_
  have := normSq4_nonneg u
  positivity
theorem euclidNormVec_eq_norm (u : Fin 4 → ℝ) :
    euclidNormVec u = ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 4))‖ := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_eq_norm <;> assumption
theorem normSq4_eq_norm_sq (u : Fin 4 → ℝ) :
    normSq4 u = ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 4))‖ ^ 2 := by
  rw [← euclidNormVec_eq_norm, euclidNormVec_sq]
theorem integrableOn_continuumGreenFunction {B : Set (Fin 4 → ℝ)}
    (hB : Bornology.IsBounded B) : IntegrableOn continuumGreenFunction B := by
  have hb : Bornology.IsBounded
      ((WithLp.toLp 2 : (Fin 4 → ℝ) → EuclideanSpace ℝ (Fin 4)) '' B) :=
    (PiLp.lipschitzWith_toLp 2 (fun _ : Fin 4 => ℝ)).isBounded_image hB
  obtain ⟨R, hR⟩ := hb.subset_ball (0 : EuclideanSpace ℝ (Fin 4))
  have hball : IntegrableOn (fun x : EuclideanSpace ℝ (Fin 4) =>
      (fun r : ℝ => 1 / (4 * Real.pi ^ 2 * r ^ 2)) ‖x‖) (Metric.ball 0 (R + 1)) := by
    refine (integrableOn_fun_norm_addHaar volume
      (f := fun r : ℝ => 1 / (4 * Real.pi ^ 2 * r ^ 2)) (r := R + 1)).2 ?_
    simp only [finrank_euclideanSpace_fin]
    have hlin : IntegrableOn (fun y : ℝ => y / (4 * Real.pi ^ 2)) (Ioo 0 (R + 1)) :=
      ((continuous_id.div_const _).integrableOn_Icc (a := 0) (b := R + 1)).mono_set
        Ioo_subset_Icc_self
    refine hlin.congr_fun (fun y hy => ?_) measurableSet_Ioo
    have hy0 : y ≠ 0 := hy.1.ne'
    simp only [smul_eq_mul]
    field_simp
  have hpull := ((PiLp.volume_preserving_toLp (Fin 4)).integrableOn_comp_preimage
    (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).measurableEmbedding).2 hball
  have hcomp : ((fun x : EuclideanSpace ℝ (Fin 4) =>
      (fun r : ℝ => 1 / (4 * Real.pi ^ 2 * r ^ 2)) ‖x‖) ∘
        (WithLp.toLp 2 : (Fin 4 → ℝ) → EuclideanSpace ℝ (Fin 4))) = continuumGreenFunction := by
    funext u
    simp only [Function.comp, continuumGreenFunction, euclidNormVec_eq_norm]
  rw [hcomp] at hpull
  refine hpull.mono_set fun u hu => ?_
  have hin := hR (mem_image_of_mem _ hu)
  simp only [Metric.mem_ball, dist_zero_right] at hin
  simp only [mem_preimage, Metric.mem_ball, dist_zero_right]
  linarith
theorem partialDerivR4_eq_fderiv {f : (Fin 4 → ℝ) → ℝ} (hf : Differentiable ℝ f) (ν : Fin 4) :
    TestFunctions.partialDerivR4 ν f = fun x => fderiv ℝ f x (Pi.single ν (1 : ℝ)) := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.partialDerivR4_eq_fderiv <;> assumption
theorem contDiff_partialDerivR4 {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (ν : Fin 4) :
    ContDiff ℝ ∞ (TestFunctions.partialDerivR4 ν f) := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.contDiff_partialDerivR4 <;> assumption
theorem hasCompactSupport_partialDerivR4 {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (ν : Fin 4) :
    HasCompactSupport (TestFunctions.partialDerivR4 ν f) := by
  rw [partialDerivR4_eq_fderiv (hf.differentiable (by simp))]
  exact hc.fderiv_apply (𝕜 := ℝ) _
theorem integral_mul_partialDerivR4 {f h : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (ν : Fin 4) :
    ∫ x, f x * TestFunctions.partialDerivR4 ν h x =
      -∫ x, TestFunctions.partialDerivR4 ν f x * h x := by
  have hcf := (contDiff_partialDerivR4 hf ν).continuous
  have hch := (contDiff_partialDerivR4 hh ν).continuous
  have hsh := hasCompactSupport_partialDerivR4 hh hc ν
  have hint1 : Integrable (fun x => TestFunctions.partialDerivR4 ν f x * h x) :=
    (hcf.mul hh.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hint2 : Integrable (fun x => f x * TestFunctions.partialDerivR4 ν h x) :=
    (hf.continuous.mul hch).integrable_of_hasCompactSupport hsh.mul_left
  have hint3 : Integrable (fun x => f x * h x) :=
    (hf.continuous.mul hh.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hef := partialDerivR4_eq_fderiv (hf.differentiable (by simp)) ν
  have heh := partialDerivR4_eq_fderiv (hh.differentiable (by simp)) ν
  rw [hef] at hint1 ⊢
  rw [heh] at hint2 ⊢
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hint1 hint2 hint3
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hh.differentiable (by simp) x)
theorem integrable_mul_secondPartialR4 {f h : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (ν : Fin 4) :
    Integrable (fun x =>
      f x * TestFunctions.partialDerivR4 ν (TestFunctions.partialDerivR4 ν h) x) :=
  (hf.continuous.mul
    (contDiff_partialDerivR4 (contDiff_partialDerivR4 hh ν) ν).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_partialDerivR4 (contDiff_partialDerivR4 hh ν)
      (hasCompactSupport_partialDerivR4 hh hc ν) ν).mul_left
theorem integral_mul_laplacianR4 {f h : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    ∫ x, f x * TestFunctions.laplacianR4 h x =
      ∫ x, TestFunctions.laplacianR4 f x * h x := by
  have hstep : ∀ ν : Fin 4,
      ∫ x, f x * TestFunctions.partialDerivR4 ν (TestFunctions.partialDerivR4 ν h) x =
        ∫ x, TestFunctions.partialDerivR4 ν (TestFunctions.partialDerivR4 ν f) x * h x := by
    intro ν
    rw [integral_mul_partialDerivR4 hf (contDiff_partialDerivR4 hh ν)
      (hasCompactSupport_partialDerivR4 hh hc ν) ν,
      integral_mul_partialDerivR4 (contDiff_partialDerivR4 hf ν) hh hc ν, neg_neg]
  have hint1 : ∀ ν ∈ (Finset.univ : Finset (Fin 4)), Integrable
      (fun x => f x * TestFunctions.partialDerivR4 ν (TestFunctions.partialDerivR4 ν h) x) :=
    fun ν _ => integrable_mul_secondPartialR4 hf hh hc ν
  have hint2 : ∀ ν ∈ (Finset.univ : Finset (Fin 4)), Integrable
      (fun x => TestFunctions.partialDerivR4 ν (TestFunctions.partialDerivR4 ν f) x * h x) :=
    fun ν _ => ((contDiff_partialDerivR4 (contDiff_partialDerivR4 hf ν) ν).continuous.mul
      hh.continuous).integrable_of_hasCompactSupport hc.mul_left
  simp only [TestFunctions.laplacianR4, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ hint1, integral_finsetSum _ hint2]
  exact Finset.sum_congr rfl fun ν _ => hstep ν
theorem laplacianR4_inverseQuadratic (c : ℝ) {a : ℝ} (ha : 0 < a) (u : Fin 4 → ℝ) :
    TestFunctions.laplacianR4 (inverseQuadratic c a) u =
      -(8 * c * a / (normSq4 u + a) ^ 3) := by
  have hQ : normSq4 u + a ≠ 0 := by
    have := normSq4_nonneg u
    positivity
  simp only [TestFunctions.laplacianR4, secondPartial_inverseQuadratic c a u _ _ hQ, if_true]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hdiag : ∑ ν : Fin 4, 8 * u ν * u ν / (normSq4 u + a) ^ 3 =
      8 * normSq4 u / (normSq4 u + a) ^ 3 := by
    rw [← Finset.sum_div]
    congr 1
    simp only [normSq4, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  rw [hdiag]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring
def mollifier (v : Fin 4 → ℝ) : ℝ := 2 / (Real.pi ^ 2 * (1 + normSq4 v) ^ 3)
theorem mollifier_nonneg (v : Fin 4 → ℝ) : 0 ≤ mollifier v := by
  have := normSq4_nonneg v
  unfold mollifier
  positivity
theorem continuous_mollifier : Continuous mollifier := by
  unfold mollifier
  refine continuous_const.div (continuous_const.mul
    ((continuous_const.add contDiff_normSq4.continuous).pow 3)) fun v => ?_
  have := normSq4_nonneg v
  have := Real.pi_pos
  positivity
def mollifierProfile (r : ℝ) : ℝ := 2 / (Real.pi ^ 2 * (1 + r ^ 2) ^ 3)
def mollifierPrimitive (r : ℝ) : ℝ :=
  2 / Real.pi ^ 2 * (-(1 / (2 * (1 + r ^ 2))) + 1 / (4 * (1 + r ^ 2) ^ 2))
theorem hasDerivAt_mollifierPrimitive (y : ℝ) :
    HasDerivAt mollifierPrimitive (y ^ 3 * mollifierProfile y) y := by
  have hp : (1 + y ^ 2) ≠ 0 := by positivity
  have hd : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add 1
  have hfirst := ((hasDerivAt_const y (1 : ℝ)).fun_div (hd.const_mul 2)
    (mul_ne_zero two_ne_zero hp)).fun_neg
  have hsecond := (hasDerivAt_const y (1 : ℝ)).fun_div ((hd.fun_pow 2).const_mul 4)
    (mul_ne_zero four_ne_zero (pow_ne_zero 2 hp))
  have hall : HasDerivAt mollifierPrimitive _ y :=
    (hfirst.add hsecond).const_mul (2 / Real.pi ^ 2)
  refine hall.congr_deriv ?_
  simp only [mollifierProfile]
  field_simp
  ring
theorem tendsto_mollifierPrimitive : Tendsto mollifierPrimitive atTop (𝓝 0) := by
  have hq : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have hfirst : Tendsto (fun r : ℝ => 1 / (2 * (1 + r ^ 2))) atTop (𝓝 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp (hq.const_mul_atTop two_pos)
  have hsecond : Tendsto (fun r : ℝ => 1 / (4 * (1 + r ^ 2) ^ 2)) atTop (𝓝 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop two_ne_zero |>.comp hq).const_mul_atTop four_pos)
  have hall := (hfirst.neg.add hsecond).const_mul (2 / Real.pi ^ 2)
  simp only [neg_zero, add_zero, mul_zero] at hall
  exact hall
theorem integrableOn_mollifierProfile :
    IntegrableOn (fun y : ℝ => y ^ 3 * mollifierProfile y) (Ioi 0) := by
  refine integrableOn_Ioi_deriv_of_nonneg' (g := mollifierPrimitive)
    (fun x _ => hasDerivAt_mollifierPrimitive x) (fun x hx => ?_) tendsto_mollifierPrimitive
  have hx' : (0 : ℝ) < x := hx
  unfold mollifierProfile
  positivity
theorem integral_mollifierProfile :
    ∫ y in Ioi (0 : ℝ), y ^ 3 * mollifierProfile y = 1 / (2 * Real.pi ^ 2) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_mollifierPrimitive x)
    integrableOn_mollifierProfile tendsto_mollifierPrimitive]
  simp only [mollifierPrimitive]
  field_simp
  norm_num
theorem mollifier_eq_profile (v : Fin 4 → ℝ) :
    mollifier v = mollifierProfile ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 4))‖ := by
  simp only [mollifier, mollifierProfile, normSq4_eq_norm_sq]
theorem integrable_mollifier : Integrable mollifier := by
  have hrad : Integrable (fun x : EuclideanSpace ℝ (Fin 4) => mollifierProfile ‖x‖) := by
    rw [integrable_fun_norm_addHaar volume]
    simpa [finrank_euclideanSpace_fin] using integrableOn_mollifierProfile
  have hpull := ((PiLp.volume_preserving_toLp (Fin 4)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).measurableEmbedding).2 hrad
  refine hpull.congr (Eventually.of_forall fun v => ?_)
  simp only [Function.comp, mollifier_eq_profile]
theorem volume_unitBall_four :
    (volume : Measure (EuclideanSpace ℝ (Fin 4))).real (Metric.ball 0 1) = Real.pi ^ 2 / 2 := by
  have hG : Real.Gamma (4 / 2 + 1) = 2 := by
    have hrw : ((4 : ℝ) / 2 + 1) = ((2 : ℕ) : ℝ) + 1 := by norm_num
    rw [hrw, Real.Gamma_nat_eq_factorial]
    norm_num
  have hs : Real.sqrt Real.pi ^ 4 = Real.pi ^ 2 := by
    have hsq := Real.sq_sqrt Real.pi_pos.le
    calc Real.sqrt Real.pi ^ 4 = (Real.sqrt Real.pi ^ 2) ^ 2 := by ring
      _ = Real.pi ^ 2 := by rw [hsq]
  simp only [Measure.real, EuclideanSpace.volume_ball, Fintype.card_fin]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, Nat.cast_ofNat, hG, hs]
  exact ENNReal.toReal_ofReal (by positivity)
theorem integral_mollifier : ∫ v, mollifier v = 1 := by
  have hpolar : ∫ v, mollifier v = ∫ x : EuclideanSpace ℝ (Fin 4), mollifierProfile ‖x‖ := by
    rw [← (PiLp.volume_preserving_toLp (Fin 4)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).measurableEmbedding]
    exact integral_congr_ae (Eventually.of_forall fun v => mollifier_eq_profile v)
  rw [hpolar, integral_fun_norm_addHaar volume]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  rw [volume_unitBall_four]
  norm_num
  rw [integral_mollifierProfile]
  field_simp
  norm_num
theorem mollifier_inv_smul {ε : ℝ} (hε : 0 < ε) (u : Fin 4 → ℝ) :
    mollifier (ε⁻¹ • u) = 2 * ε ^ 6 / (Real.pi ^ 2 * (normSq4 u + ε ^ 2) ^ 3) := by
  have hq := normSq4_nonneg u
  have hQ : normSq4 u + ε ^ 2 ≠ 0 := by positivity
  have hrw : 1 + ε⁻¹ ^ 2 * normSq4 u = (normSq4 u + ε ^ 2) / ε ^ 2 := by
    field_simp
    ring
  rw [mollifier, normSq4_smul, hrw]
  field_simp
theorem regularized_identity {φ : (Fin 4 → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) {ε : ℝ} (hε : 0 < ε) :
    ∫ u, inverseQuadratic (1 / (4 * Real.pi ^ 2)) (ε ^ 2) u *
        (-TestFunctions.laplacianR4 φ u) =
      ∫ v, mollifier v * φ (ε • v) := by
  have ha : 0 < ε ^ 2 := by positivity
  have hparts :=
    integral_mul_laplacianR4 (contDiff_inverseQuadratic (1 / (4 * Real.pi ^ 2)) ha) hφ hc
  have hscale : ∫ v, mollifier v * φ (ε • v) =
      (ε ^ 4)⁻¹ * ∫ u, mollifier (ε⁻¹ • u) * φ u := by
    have hsub := Measure.integral_comp_smul (volume : Measure (Fin 4 → ℝ))
      (fun u => mollifier (ε⁻¹ • u) * φ u) ε
    simp only [Module.finrank_fin_fun, smul_smul, inv_mul_cancel₀ hε.ne', one_smul,
      smul_eq_mul] at hsub
    rw [hsub, abs_of_pos (by positivity)]
  simp only [mul_neg]
  rw [integral_neg, hparts, hscale, ← integral_const_mul, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hq := normSq4_nonneg u
  have hQ : normSq4 u + ε ^ 2 ≠ 0 := by positivity
  simp only [laplacianR4_inverseQuadratic _ ha, mollifier_inv_smul hε]
  field_simp
  ring
theorem normSq4_pos {u : Fin 4 → ℝ} (hu : u ≠ 0) : 0 < normSq4 u := by apply _root_.YangMills.Construction.ReflectionKernel.normSq_pos <;> assumption
theorem continuumGreenIsFundamentalSolution : ContinuumGreenIsFundamentalSolution := by
  refine ⟨fun B _ hB => integrableOn_continuumGreenFunction hB, fun φ hφ hc => ?_⟩
  have hsec : ∀ ν : Fin 4, ContDiff ℝ ∞
      (TestFunctions.partialDerivR4 ν (TestFunctions.partialDerivR4 ν φ)) :=
    fun ν => contDiff_partialDerivR4 (contDiff_partialDerivR4 hφ ν) ν
  have hsup : ∀ ν : Fin 4, HasCompactSupport
      (TestFunctions.partialDerivR4 ν (TestFunctions.partialDerivR4 ν φ)) := fun ν =>
    hasCompactSupport_partialDerivR4 (contDiff_partialDerivR4 hφ ν)
      (hasCompactSupport_partialDerivR4 hφ hc ν) ν
  have hlap : TestFunctions.laplacianR4 φ = fun u =>
      TestFunctions.partialDerivR4 0 (TestFunctions.partialDerivR4 0 φ) u +
        TestFunctions.partialDerivR4 1 (TestFunctions.partialDerivR4 1 φ) u +
        TestFunctions.partialDerivR4 2 (TestFunctions.partialDerivR4 2 φ) u +
        TestFunctions.partialDerivR4 3 (TestFunctions.partialDerivR4 3 φ) u := by
    funext u
    simp [TestFunctions.laplacianR4, Fin.sum_univ_four]
  have hwc : Continuous fun u => -TestFunctions.laplacianR4 φ u := by
    rw [hlap]
    exact ((((hsec 0).continuous.add (hsec 1).continuous).add (hsec 2).continuous).add
      (hsec 3).continuous).neg
  have hws : HasCompactSupport fun u => -TestFunctions.laplacianR4 φ u := by
    rw [hlap]
    exact (((((hsup 0).add (hsup 1)).add (hsup 2)).add (hsup 3))).neg
  set w : (Fin 4 → ℝ) → ℝ := fun u => -TestFunctions.laplacianR4 φ u with hw
  set c : ℝ := 1 / (4 * Real.pi ^ 2) with hcdef
  have hc0 : 0 < c := by positivity
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε0 : ∀ k, 0 < ε k := fun k => by positivity
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hc
  have hright : Tendsto (fun k => ∫ v, mollifier v * φ (ε k • v)) atTop (𝓝 (φ 0)) := by
    have hdom := tendsto_integral_of_dominated_convergence (fun v => mollifier v * C)
      (F := fun k v => mollifier v * φ (ε k • v)) (f := fun v => mollifier v * φ 0)
      (fun k => (continuous_mollifier.mul
        (hφ.continuous.comp (continuous_const_smul (ε k)))).aestronglyMeasurable)
      (integrable_mollifier.mul_const C)
      (fun k => Eventually.of_forall fun v => by
        rw [norm_mul, Real.norm_of_nonneg (mollifier_nonneg v)]
        exact mul_le_mul_of_nonneg_left (hC _) (mollifier_nonneg v))
      (Eventually.of_forall fun v => by
        refine Tendsto.const_mul _ ?_
        have hlim : Tendsto (fun k => ε k • v) atTop (𝓝 ((0 : ℝ) • v)) := hεt.smul_const v
        rw [zero_smul] at hlim
        exact (hφ.continuous.tendsto 0).comp hlim)
    rw [integral_mul_const, integral_mollifier, one_mul] at hdom
    exact hdom
  have hbound : Integrable fun u => continuumGreenFunction u * |w u| := by
    have hK := hws.isCompact
    have hon : IntegrableOn (fun u => continuumGreenFunction u * |w u|) (tsupport w) :=
      (integrableOn_continuumGreenFunction hK.isBounded).mul_continuousOn
        hwc.abs.continuousOn hK
    refine (integrableOn_iff_integrable_of_support_subset fun u hu => ?_).1 hon
    refine subset_tsupport w fun h0 => hu ?_
    simp [h0]
  have hne : ∀ᵐ u : Fin 4 → ℝ, u ≠ 0 := by
    exact show ({0}ᶜ : Set (Fin 4 → ℝ)) ∈ ae volume from
      compl_mem_ae_iff.2 (measure_singleton 0)
  have hleft : Tendsto (fun k => ∫ u, inverseQuadratic c (ε k ^ 2) u * w u) atTop
      (𝓝 (∫ u, continuumGreenFunction u * w u)) := by
    refine tendsto_integral_of_dominated_convergence _
      (fun k => ((contDiff_inverseQuadratic c (pow_pos (hε0 k) 2)).continuous.mul
        hwc).aestronglyMeasurable) hbound (fun k => ?_) ?_
    · filter_upwards [hne] with u hu
      have hq := normSq4_pos hu
      have ha := pow_pos (hε0 k) 2
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [continuumGreenFunction_eq_inverseQuadratic]
      simp only [inverseQuadratic, add_zero]
      rw [abs_of_pos (by positivity)]
      exact div_le_div_of_nonneg_left hc0.le hq (by linarith)
    · filter_upwards [hne] with u hu
      have hq := normSq4_pos hu
      refine Tendsto.mul_const _ ?_
      rw [continuumGreenFunction_eq_inverseQuadratic]
      simp only [inverseQuadratic]
      have hsq : Tendsto (fun k => ε k ^ 2) atTop (𝓝 0) := by
        simpa using hεt.pow 2
      exact tendsto_const_nhds.div (tendsto_const_nhds.add hsq) (by simpa using hq.ne')
  have heq : (fun k => ∫ u, inverseQuadratic c (ε k ^ 2) u * w u) =
      fun k => ∫ v, mollifier v * φ (ε k • v) := by
    funext k
    exact regularized_identity hφ hc (hε0 k)
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright
end ContinuumKernel
theorem symbolAndGreenFunctions : SymbolAndGreenFunctions := fun n _ _ =>
  ⟨expWavesAreEigenvectors n, symbolComparableToSquare,
    pinvKernelIsLatticeGreen n, continuumGreenIsFundamentalSolution,
    continuumGreenSecondDerivatives⟩
end YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint.SymbolAndGreen
