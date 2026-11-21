import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.PeriodicOperators.SumsOfExponentials
import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
namespace ExponentialSums
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
theorem summable_expHalfTerm {c : ℝ} (hc : 0 < c) : Summable (expHalfTerm c) := by
  have hr : Real.exp (-c / 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hg : Summable fun n : ℕ => Real.exp (-c / 2) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le hr
  have hpow : ∀ n : ℕ, Real.exp (-c / 2) ^ n = Real.exp (-c * (n : ℝ) / 2) := by
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hg.congr fun n => ?_
    simp [expHalfTerm, hpow]
  · refine hg.congr fun n => ?_
    simp [expHalfTerm, hpow]
theorem summable_and_tsum_pi_prod (f : ℤ → ℝ) (hf : Summable f) (k : ℕ) :
    Summable (fun n : Fin k → ℤ => ∏ i, f (n i)) ∧
      ∑' n : Fin k → ℤ, ∏ i, f (n i) = (∑' m, f m) ^ k := by
  induction k with
  | zero =>
    refine ⟨(hasSum_fintype _).summable, ?_⟩
    simp
  | succ k ih =>
    obtain ⟨hs, ht⟩ := ih
    obtain ⟨e, he⟩ : ∃ e : ℤ × (Fin k → ℤ) ≃ (Fin (k + 1) → ℤ),
        ∀ p, ∏ i, f (e p i) = f p.1 * ∏ i, f (p.2 i) :=
      ⟨Fin.consEquiv (fun _ => ℤ), fun p => by simp [Fin.prod_univ_succ, Fin.consEquiv]⟩
    have hp : Summable (fun p : ℤ × (Fin k → ℤ) => f p.1 * ∏ i, f (p.2 i)) :=
      summable_mul_of_summable_norm (f := f) (g := fun n : Fin k → ℤ => ∏ i, f (n i)) hf.norm hs.norm
    constructor
    · have h1 : Summable ((fun n : Fin (k + 1) → ℤ => ∏ i, f (n i)) ∘ e) :=
        hp.congr fun p => (he p).symm
      exact e.summable_iff.mp h1
    · rw [← e.tsum_eq]
      simp_rw [he]
      rw [← hf.tsum_mul_tsum hs hp, ht, pow_succ']
theorem euclidNormVec_add_le (u v : Fin 4 → ℝ) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem sum_abs_le_two_mul_euclidNormVec (v : Fin 4 → ℝ) :
    ∑ i, |v i| ≤ 2 * euclidNormVec v := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.sum_abs_le_two_mul_euclidNormVec <;> assumption
theorem exp_neg_mul_le_prod {c : ℝ} (hc : 0 < c) (y : AmbientSpace) (hy : euclidNormVec y ≤ 2)
    (n : Fin 4 → ℤ) :
    Real.exp (-c * euclidNormVec (y + castVec n)) ≤
      Real.exp (2 * c) * ∏ i, expHalfTerm c (n i) := by
  have hprod : ∏ i, expHalfTerm c (n i) = Real.exp (∑ i, -c * |(n i : ℝ)| / 2) := by
    rw [Real.exp_sum]
    rfl
  rw [hprod, ← Real.exp_add, Real.exp_le_exp]
  have h1 : ∑ i, |(n i : ℝ)| ≤ 2 * euclidNormVec (castVec n) :=
    sum_abs_le_two_mul_euclidNormVec (castVec n)
  have h2 : euclidNormVec (castVec n) ≤ euclidNormVec (y + castVec n) + euclidNormVec (-y) := by
    have := euclidNormVec_add_le (y + castVec n) (-y)
    simpa using this
  have h3 : euclidNormVec (-y) = euclidNormVec y := by
    simp [euclidNormVec]
  have h4 : ∑ i, -c * |(n i : ℝ)| / 2 = -c / 2 * ∑ i, |(n i : ℝ)| := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h4]
  have h5 : ∑ i, |(n i : ℝ)| ≤ 2 * euclidNormVec (y + castVec n) + 4 := by
    rw [h3] at h2
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h5 hc.le]
theorem castVec_add (m n : Fin 4 → ℤ) : castVec (m + n) = castVec m + castVec n := by
  funext i
  simp [castVec]
theorem euclidNormVec_add_neg_floor_le (y : AmbientSpace) :
    euclidNormVec (y + castVec (fun i => -⌊y i⌋)) ≤ 2 := by
  refine Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
  have hb : ∀ i, (y + castVec (fun i => -⌊y i⌋)) i ^ 2 ≤ 1 := by
    intro i
    have h : (y + castVec (fun i => -⌊y i⌋)) i = Int.fract (y i) := by
      simp [castVec, Int.fract, sub_eq_add_neg]
    rw [h]
    have h0 := Int.fract_nonneg (y i)
    have h1 := Int.fract_lt_one (y i)
    nlinarith
  calc ∑ i, (y + castVec (fun i => -⌊y i⌋)) i ^ 2 ≤ ∑ _i : Fin 4, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => hb i
    _ ≤ 2 ^ 2 := by norm_num
theorem summable_tsum_le_lattice {c : ℝ} (hc : 0 < c) (y : AmbientSpace) :
    Summable (fun n : Fin 4 → ℤ => Real.exp (-c * euclidNormVec (y + castVec n))) ∧
      ∑' n : Fin 4 → ℤ, Real.exp (-c * euclidNormVec (y + castVec n)) ≤
        Real.exp (2 * c) * expHalfSum c ^ 4 := by
  obtain ⟨hPs, hPt⟩ := summable_and_tsum_pi_prod (expHalfTerm c)
    (summable_expHalfTerm hc) 4
  set n₀ : Fin 4 → ℤ := fun i => -⌊y i⌋ with hn₀
  have hy : euclidNormVec (y + castVec n₀) ≤ 2 := euclidNormVec_add_neg_floor_le y
  have hle := exp_neg_mul_le_prod hc (y + castVec n₀) hy
  have hG : Summable
      (fun n : Fin 4 → ℤ => Real.exp (-c * euclidNormVec (y + castVec n₀ + castVec n))) :=
    Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hle (hPs.mul_left _)
  let e : (Fin 4 → ℤ) ≃ (Fin 4 → ℤ) := Equiv.addLeft n₀
  have hcomp : ∀ n, Real.exp (-c * euclidNormVec (y + castVec (e n))) =
      Real.exp (-c * euclidNormVec (y + castVec n₀ + castVec n)) := by
    intro n
    simp only [e, Equiv.coe_addLeft, castVec_add, add_assoc]
  constructor
  · rw [← e.summable_iff]
    exact hG.congr fun n => (hcomp n).symm
  · rw [← e.tsum_eq]
    simp_rw [hcomp]
    calc ∑' n : Fin 4 → ℤ, Real.exp (-c * euclidNormVec (y + castVec n₀ + castVec n))
        ≤ ∑' n : Fin 4 → ℤ, Real.exp (2 * c) * ∏ i, expHalfTerm c (n i) :=
          hG.tsum_le_tsum hle (hPs.mul_left _)
      _ = Real.exp (2 * c) * expHalfSum c ^ 4 := by
          rw [tsum_mul_left, hPt, expHalfSum]
variable {I : PeriodicData}
theorem exists_translate_of_mkQuot_eq (hI : IsPeriodic I) {a b : I.Carrier}
    (h : I.mkQuot 1 a = I.mkQuot 1 b) : ∃ n, b = I.translate n a := by
  have heq : Equivalence fun a b : I.Carrier => ∃ n : Fin 4 → ℤ, b = I.translate (1 • n) a := by
    refine ⟨fun a => ⟨0, by simp [hI.translate_zero]⟩, ?_, ?_⟩
    · rintro a b ⟨n, rfl⟩
      refine ⟨-n, ?_⟩
      rw [one_smul, one_smul, ← hI.translate_add, add_neg_cancel, hI.translate_zero]
    · rintro a b d ⟨m, rfl⟩ ⟨n, rfl⟩
      refine ⟨m + n, ?_⟩
      simp only [one_smul]
      rw [hI.translate_add]
  obtain ⟨n, hn⟩ := heq.eqvGen_iff.mp (Quot.eqvGen_exact h)
  exact ⟨n, by simpa using hn⟩
theorem mkQuot_translate (a : I.Carrier) (n : Fin 4 → ℤ) :
    I.mkQuot 1 (I.translate n a) = I.mkQuot 1 a :=
  (Quot.sound ⟨n, by simp⟩).symm
theorem translate_out_bijective (hI : IsPeriodic I) :
    Function.Bijective
      (fun p : I.UnitQuot × (Fin 4 → ℤ) => I.translate p.2 (Quot.out p.1)) := by
  have hout : ∀ k : I.UnitQuot, I.mkQuot 1 (Quot.out k) = k := fun k => Quot.out_eq k
  constructor
  · rintro ⟨k, m⟩ ⟨k', m'⟩ h
    simp only at h
    have hk : k = k' := by
      have := congrArg (I.mkQuot 1) h
      rwa [mkQuot_translate, mkQuot_translate, hout, hout] at this
    subst hk
    have h' := congrArg (I.translate (-m')) h
    rw [← hI.translate_add, ← hI.translate_add, add_neg_cancel, hI.translate_zero] at h'
    have := hI.free _ _ h'
    have hm : m = m' := by
      have h0 : m + -m' = 0 := this
      exact add_neg_eq_zero.mp h0
    rw [hm]
  · intro a
    obtain ⟨n, hn⟩ := exists_translate_of_mkQuot_eq hI (hout (I.mkQuot 1 a))
    exact ⟨(I.mkQuot 1 a, n), hn.symm⟩
theorem summable_tsum_le_carrier {c : ℝ} (hc : 0 < c) (hI : IsPeriodic I) (y : AmbientSpace) :
    Summable (fun a : I.Carrier => Real.exp (-c * euclidNormVec (I.pos a - y))) ∧
      ∑' a : I.Carrier, Real.exp (-c * euclidNormVec (I.pos a - y)) ≤
        (Nat.card I.UnitQuot : ℝ) * (Real.exp (2 * c) * expHalfSum c ^ 4) := by
  have := hI.finite_quot
  have := Fintype.ofFinite I.UnitQuot
  let e : I.UnitQuot × (Fin 4 → ℤ) ≃ I.Carrier := Equiv.ofBijective _ (translate_out_bijective hI)
  have hcomp : ∀ p : I.UnitQuot × (Fin 4 → ℤ),
      Real.exp (-c * euclidNormVec (I.pos (e p) - y)) =
        Real.exp (-c * euclidNormVec ((I.pos (Quot.out p.1) - y) + castVec p.2)) := by
    intro p
    have : I.pos (e p) - y = (I.pos (Quot.out p.1) - y) + castVec p.2 := by
      simp only [e, Equiv.ofBijective_apply, hI.pos_translate]
      abel
    rw [this]
  have hP : Summable (fun p : I.UnitQuot × (Fin 4 → ℤ) =>
      Real.exp (-c * euclidNormVec ((I.pos (Quot.out p.1) - y) + castVec p.2))) := by
    refine (summable_prod_of_nonneg fun p => (Real.exp_pos _).le).mpr
      ⟨fun k => (summable_tsum_le_lattice hc (I.pos (Quot.out k) - y)).1, ?_⟩
    exact (hasSum_fintype _).summable
  constructor
  · rw [← e.summable_iff]
    exact hP.congr fun p => (hcomp p).symm
  · rw [← e.tsum_eq]
    simp_rw [hcomp]
    rw [hP.tsum_prod, tsum_fintype]
    calc ∑ k : I.UnitQuot, ∑' n : Fin 4 → ℤ,
          Real.exp (-c * euclidNormVec ((I.pos (Quot.out k) - y) + castVec n))
        ≤ ∑ _k : I.UnitQuot, Real.exp (2 * c) * expHalfSum c ^ 4 :=
          Finset.sum_le_sum fun k _ => (summable_tsum_le_lattice hc (I.pos (Quot.out k) - y)).2
      _ = (Nat.card I.UnitQuot : ℝ) * (Real.exp (2 * c) * expHalfSum c ^ 4) := by
          simp [Nat.card_eq_fintype_card]
theorem bounds_holds : Bounds :=
  fun _ hc => ⟨summable_expHalfTerm hc, summable_tsum_le_lattice hc,
    fun _ hI y => summable_tsum_le_carrier hc hI y⟩
end ExponentialSums
end PeriodicOperators
end YangMills.Construction
end
