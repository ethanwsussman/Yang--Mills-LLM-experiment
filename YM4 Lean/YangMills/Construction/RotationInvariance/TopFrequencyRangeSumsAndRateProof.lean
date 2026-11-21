import YangMills.Construction.RotationInvariance.FinitelyManyHarmonicsOnPencils
import YangMills.Construction.RotationInvariance.TopFrequencyRangeSumsAndRate
import Mathlib
set_option autoImplicit false
open Complex (I)
open YangMills.Construction.RealPlane
open Filter Topology
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.MaxFrequencyFacts
open PencilHarmonics
theorem frequency_le_harmonicBound (h : PencilHarmonics.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q)
    {k : ℕ} (hk : k ∈ harmonicFrequencies S d.angle q) :
    (k : ℝ) ≤ harmonicBound d q := by
  rcases hk with hk | ⟨ν, rfl, y, hy, φ, hne⟩
  · have hk0 : k = 0 := hk
    subst hk0
    have hpos := d.base.expo_pos
    simp only [harmonicBound, Nat.cast_zero]
    positivity
  · by_contra hlt
    apply hne
    refine (h m S d q hq y hy φ).1 ν ?_
    have hcast : ((ν.natAbs : ℕ) : ℝ) = |(ν : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← hcast]
    exact not_le.mp hlt
theorem bddAbove_harmonicFrequencies (h : PencilHarmonics.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q) :
    BddAbove (harmonicFrequencies S d.angle q) :=
  ⟨⌈harmonicBound d q⌉₊, fun _ hk =>
    Nat.cast_le (α := ℝ).mp ((frequency_le_harmonicBound h d hq hk).trans (Nat.le_ceil _))⟩
theorem maxFrequency_eq_sSup {S : ConnFamily} {θ₀ : openingAngles} {q : ℕ} (hq : 1 ≤ q) :
    maxFrequency S θ₀ (q + 1) = sSup (harmonicFrequencies S θ₀ q) := by
  rw [maxFrequency, if_pos hq]
theorem maxFrequency_mem (h : PencilHarmonics.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q) :
    maxFrequency S d.angle (q + 1) ∈ harmonicFrequencies S d.angle q := by
  rw [maxFrequency_eq_sSup hq]
  exact Nat.sSup_mem ⟨0, Or.inl rfl⟩ (bddAbove_harmonicFrequencies h d hq)
theorem le_maxFrequency (h : PencilHarmonics.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q)
    {k : ℕ} (hk : k ∈ harmonicFrequencies S d.angle q) :
    k ≤ maxFrequency S d.angle (q + 1) := by
  rw [maxFrequency_eq_sSup hq]
  exact le_csSup (bddAbove_harmonicFrequencies h d hq) hk
theorem maxFrequencyLe_of (h : PencilHarmonics.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) :
    MaxFrequencyLe d := by
  intro n
  have hpos := d.base.expo_pos
  cases n with
  | zero => simp [maxFrequency]
  | succ q =>
    by_cases hq : 1 ≤ q
    · exact frequency_le_harmonicBound h d hq (maxFrequency_mem h d hq)
    · have htop : maxFrequency S d.angle (q + 1) = 0 := by
        rw [maxFrequency, if_neg hq]
      rw [htop, Nat.cast_zero]
      positivity
theorem angleHarmonic_eq_zero_of_lt (h : PencilHarmonics.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q)
    {y : Fin (q + 1) → RealPlane} (hy : y ∈ pencilSet d.angle (q + 1))
    (φ : Fin (q + 1) → realLabels) {ν : ℤ}
    (hν : maxFrequency S d.angle (q + 1) < ν.natAbs) :
    angleHarmonic S d.angle y φ ν = 0 := by
  by_contra hne
  exact absurd (le_maxFrequency h d hq (Or.inr ⟨ν, rfl, y, hy, φ, hne⟩)) (not_le.mpr hν)
theorem angleFunction_eq_sum_symmIcc (h : PencilHarmonics.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q)
    {y : Fin (q + 1) → RealPlane} (hy : y ∈ pencilSet d.angle (q + 1))
    (φ : Fin (q + 1) → realLabels) (t s : ℝ) :
    angleFunction S d.angle y φ ((t : ℂ) + I * (s : ℂ)) =
      ∑ ν ∈ symmIcc (maxFrequency S d.angle (q + 1)),
        angleHarmonic S d.angle y φ ν *
          Complex.exp (4 * I * (ν : ℂ) * ((t : ℂ) + I * (s : ℂ))) := by
  have htop : (maxFrequency S d.angle (q + 1) : ℤ) ≤ ⌊harmonicBound d q⌋ := by
    apply Int.le_floor.mpr
    have hle := frequency_le_harmonicBound h d hq (maxFrequency_mem h d hq)
    exact_mod_cast hle
  rw [(h m S d q hq y hy φ).2.1 t s]
  symm
  apply Finset.sum_subset
  · intro ν hν
    simp only [symmIcc, Finset.mem_Icc] at hν ⊢
    constructor <;> omega
  · intro ν _ hν
    simp only [symmIcc, Finset.mem_Icc, not_and_or, not_le] at hν
    rw [angleHarmonic_eq_zero_of_lt h d hq hy φ (by omega), zero_mul]
theorem angleFunction_imag_eq_sum (h : PencilHarmonics.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q)
    {y : Fin (q + 1) → RealPlane} (hy : y ∈ pencilSet d.angle (q + 1))
    (φ : Fin (q + 1) → realLabels) (s : ℝ) :
    angleFunction S d.angle y φ (I * (s : ℂ)) =
      ∑ ν ∈ symmIcc (maxFrequency S d.angle (q + 1)),
        angleHarmonic S d.angle y φ ν * Complex.exp (-(4 * (ν : ℂ) * (s : ℂ))) := by
  have hexp := angleFunction_eq_sum_symmIcc h d hq hy φ 0 s
  rw [Complex.ofReal_zero, zero_add] at hexp
  rw [hexp]
  refine Finset.sum_congr rfl fun ν _ => ?_
  congr 2
  linear_combination (4 * (ν : ℂ) * (s : ℂ)) * Complex.I_mul_I
theorem finiteHarmonicSum_of (h : PencilHarmonics.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q)
    {y : Fin (q + 1) → RealPlane} (hy : y ∈ pencilSet d.angle (q + 1))
    (φ : Fin (q + 1) → realLabels) :
    FiniteHarmonicSum S d.angle y φ :=
  ⟨fun _ hν => angleHarmonic_eq_zero_of_lt h d hq hy φ hν,
    angleFunction_eq_sum_symmIcc h d hq hy φ,
    angleFunction_imag_eq_sum h d hq hy φ⟩
theorem imagAngleAsymptotic_of (h : PencilHarmonics.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) {q : ℕ} (hq : 1 ≤ q)
    {y : Fin (q + 1) → RealPlane} (hy : y ∈ pencilSet d.angle (q + 1))
    (φ : Fin (q + 1) → realLabels) :
    ImagAngleAsymptotic S d.angle y φ := by
  unfold ImagAngleAsymptotic
  set N : ℕ := maxFrequency S d.angle (q + 1) with hN
  set c : ℤ → ℂ := angleHarmonic S d.angle y φ with hc
  have hfun : (fun s : ℝ => ((Real.exp (-(4 * (N : ℝ) * s)) : ℝ) : ℂ) *
        angleFunction S d.angle y φ (I * (s : ℂ))) =
      fun s : ℝ => ∑ ν ∈ symmIcc N,
        c ν * ((Real.exp (-(4 * ((ν : ℝ) + (N : ℝ))) * s) : ℝ) : ℂ) := by
    funext s
    rw [angleFunction_imag_eq_sum h d hq hy φ s, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Complex.ofReal_exp, Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hlim : (c (-(N : ℤ))) = ∑ ν ∈ symmIcc N, if ν = -(N : ℤ) then c ν else 0 := by
    rw [Finset.sum_ite_eq' (symmIcc N) (-(N : ℤ)) c, if_pos]
    simp only [symmIcc, Finset.mem_Icc]
    omega
  rw [hfun, hlim]
  refine tendsto_finsetSum _ fun ν hν => ?_
  by_cases hνN : ν = -(N : ℤ)
  · rw [if_pos hνN]
    have hzero : (ν : ℝ) + (N : ℝ) = 0 := by
      rw [hνN]
      push_cast
      ring
    simp only [hzero, mul_zero, neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, mul_one]
    exact tendsto_const_nhds
  · rw [if_neg hνN]
    simp only [symmIcc, Finset.mem_Icc] at hν
    have hk : (0 : ℝ) < (ν : ℝ) + (N : ℝ) := by
      have hint : 0 < ν + (N : ℤ) := by omega
      exact_mod_cast hint
    have hlin : Tendsto (fun s : ℝ => -(4 * ((ν : ℝ) + (N : ℝ))) * s) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    have hreal := Real.tendsto_exp_atBot.comp hlin
    have hcomplex := ((Complex.continuous_ofReal.tendsto 0).comp hreal).const_mul (c ν)
    simpa [Function.comp_def] using hcomplex
theorem maxFrequencyAttained_of (h : PencilHarmonics.Holds)
    {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S) :
    MaxFrequencyAttained S d.angle := by
  intro n hn
  cases n with
  | zero => simp [maxFrequency] at hn
  | succ p =>
    have hp : 1 ≤ p := by
      by_contra hp
      rw [maxFrequency, if_neg hp] at hn
      omega
    refine ⟨by omega, fun q hq => ?_⟩
    obtain rfl : p = q := by omega
    rcases maxFrequency_mem h d hp with h0 | ⟨ν, hν, y, hy, φ, hne⟩
    · have h0' : maxFrequency S d.angle (p + 1) = 0 := h0
      omega
    · refine ⟨y, hy, φ, ?_⟩
      rcases Int.natAbs_eq ν with hpos | hneg
      · have hconj := (h m S d p hp y hy φ).2.2.2.1 ν
        have hidx : -(maxFrequency S d.angle (p + 1) : ℤ) = -ν := by omega
        rw [hidx, hconj]
        exact (map_ne_zero _).mpr hne
      · have hidx : -(maxFrequency S d.angle (p + 1) : ℤ) = ν := by omega
        rw [hidx]
        exact hne
theorem holds_of_pencilHarmonics (h : PencilHarmonics.Holds) : Holds :=
  fun _ _ d => ⟨maxFrequencyLe_of h d,
    fun _ hq _ hy φ => ⟨finiteHarmonicSum_of h d hq hy φ, imagAngleAsymptotic_of h d hq hy φ⟩,
    maxFrequencyAttained_of h d⟩
end YangMills.Construction.EuclideanFunctionals.MaxFrequencyFacts
end
