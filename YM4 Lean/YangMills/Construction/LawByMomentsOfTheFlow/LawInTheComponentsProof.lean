import YangMills.Construction.Cumulants.JointCumulantThroughMoments
import YangMills.Construction.Cumulants.MultilinearityShiftsAndMomentsOfJointCumulants
import YangMills.Construction.InequalityOnMirroredCopies.TheRatioIsBoundedProof
import YangMills.Construction.InfiniteLattice.PlaquetteFunctionSeesNeitherCornerNorSense
import YangMills.Construction.InfiniteLattice.WilsonKernelOfBondsWithOneOrientation
import YangMills.Construction.LawByMomentsOfTheFlow.ABoundAtClearStatesInALimitFieldProof
import YangMills.Construction.LawByMomentsOfTheFlow.ChainCumulantIsTheFreeOne
import YangMills.Construction.LawByMomentsOfTheFlow.CouplingOfAPointIsPositive
import YangMills.Construction.LawByMomentsOfTheFlow.LawInTheComponents
import YangMills.Construction.LawByMomentsOfTheFlow.MomentsInTheComponents
import YangMills.Construction.LawByMomentsOfTheFlow.TheChainHasItsGaussian
import YangMills.Construction.LawByMomentsOfTheFlow.ValueOfTheFreeCumulant
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusLumps WeightedResponses BlockAverages LumpContours ColdStepAtMirrorFrames
private theorem abs_prod_sub_prod_le_card_mul {α : Type} [DecidableEq α] (s : Finset α) (a b u : α → ℝ) (w : ℝ)
    (hw : 0 ≤ w) (ha : ∀ i ∈ s, |a i| ≤ u i) (hb : ∀ i ∈ s, |b i| ≤ u i) (hd : ∀ i ∈ s, |a i - b i| ≤ w * u i) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ (s.card : ℝ) * w * ∏ i ∈ s, u i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have ha' : ∀ j ∈ s, |a j| ≤ u j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hb' : ∀ j ∈ s, |b j| ≤ u j := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hd' : ∀ j ∈ s, |a j - b j| ≤ w * u j := fun j hj => hd j (Finset.mem_insert_of_mem hj)
    have ih' := ih ha' hb' hd'
    have hai := ha i (Finset.mem_insert_self _ _)
    have hbi := hb i (Finset.mem_insert_self _ _)
    have hdi := hd i (Finset.mem_insert_self _ _)
    have hui : 0 ≤ u i := (abs_nonneg _).trans hai
    have hA : |∏ j ∈ s, a j| ≤ ∏ j ∈ s, u j := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun j _ => abs_nonneg _) ha'
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have key : a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j =
        (a i - b i) * ∏ j ∈ s, a j + b i * (∏ j ∈ s, a j - ∏ j ∈ s, b j) := by ring
    rw [key]
    calc |(a i - b i) * ∏ j ∈ s, a j + b i * (∏ j ∈ s, a j - ∏ j ∈ s, b j)|
        ≤ |(a i - b i) * ∏ j ∈ s, a j| + |b i * (∏ j ∈ s, a j - ∏ j ∈ s, b j)| := abs_add_le _ _
      _ = |a i - b i| * |∏ j ∈ s, a j| + |b i| * |∏ j ∈ s, a j - ∏ j ∈ s, b j| := by
          rw [abs_mul, abs_mul]
      _ ≤ (w * u i) * ∏ j ∈ s, u j + u i * ((s.card : ℝ) * w * ∏ j ∈ s, u j) :=
          add_le_add (mul_le_mul hdi hA (abs_nonneg _) (mul_nonneg hw hui))
            (mul_le_mul hbi ih' (abs_nonneg _) hui)
      _ = ((s.card + 1 : ℕ) : ℝ) * w * (u i * ∏ j ∈ s, u j) := by
          push_cast
          ring
abbrev _root_.YangMills.SharedProofs.p34157 := @abs_prod_sub_prod_le_card_mul
private def partitionWeightSum (k : ℕ) (M : ℝ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin k)),
    ((π.parts.card - 1).factorial : ℝ) * (π.parts.card : ℝ) * M ^ π.parts.card
private theorem partitionWeightSum_nonneg (k : ℕ) {M : ℝ} (hM : 0 ≤ M) : 0 ≤ partitionWeightSum k M :=
  Finset.sum_nonneg fun _ _ => by positivity
private theorem abs_scaled_moebius_sub_le {k : ℕ} (m₁ m₂ : Finset (Fin k) → ℝ) (x r M : ℝ)
    (hx : 1 ≤ x) (hr : 0 ≤ r) (hM : 1 ≤ M)
    (hd : ∀ B : Finset (Fin k), |x ^ B.card * m₁ B - m₂ B| ≤
      M * r ^ (4 * B.card + 3) * x ^ (-(1 / 2) + 1 / 1000 : ℝ))
    (h₁ : ∀ B : Finset (Fin k), |x ^ B.card * m₁ B| ≤ M * r ^ (4 * B.card) * x ^ ((1 : ℝ) / 1000))
    (h₂ : ∀ B : Finset (Fin k), |m₂ B| ≤ M * r ^ (4 * B.card) * x ^ ((1 : ℝ) / 1000)) :
    |x ^ k * (∑ π : Finpartition (Finset.univ : Finset (Fin k)), (-1 : ℝ) ^ (π.parts.card - 1) *
        ((π.parts.card - 1).factorial : ℝ) * ∏ J ∈ π.parts, m₁ J) -
      ∑ π : Finpartition (Finset.univ : Finset (Fin k)), (-1 : ℝ) ^ (π.parts.card - 1) *
        ((π.parts.card - 1).factorial : ℝ) * ∏ J ∈ π.parts, m₂ J| ≤
      partitionWeightSum k M * r ^ (4 * k + 3) * x ^ (-(1 / 2) + ((k : ℝ) + 1) / 1000) := by
  have hx0 : 0 < x := by linarith
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [partitionWeightSum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun π _ => ?_
  have hsum : ∑ J ∈ π.parts, J.card = k := by
    simpa using π.sum_card_parts
  have hp : π.parts.card ≤ k := by
    simpa using π.card_parts_le_card
  obtain ⟨p, hpdef⟩ : ∃ p, p = π.parts.card := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = x ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = x ^ ((1 : ℝ) / 1000) := ⟨_, rfl⟩
  have hz0 : 0 ≤ z := hz ▸ Real.rpow_nonneg hx0.le _
  have hw0 : 0 ≤ r ^ 3 * z := by positivity
  have hprod : x ^ k * ∏ J ∈ π.parts, m₁ J = ∏ J ∈ π.parts, x ^ J.card * m₁ J := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
  have hsplit : x ^ (-(1 / 2) + 1 / 1000 : ℝ) = z * y := by
    rw [hz, hy, Real.rpow_add hx0]
  have hbound := abs_prod_sub_prod_le_card_mul π.parts (fun J => x ^ J.card * m₁ J) m₂
    (fun J => M * r ^ (4 * J.card) * y) (r ^ 3 * z) hw0
    (fun J _ => by simpa only [hy] using h₁ J) (fun J _ => by simpa only [hy] using h₂ J)
    (fun J _ => by
      refine (hd J).trans (le_of_eq ?_)
      rw [hsplit, pow_add]
      ring)
  have hU : ∏ J ∈ π.parts, (M * r ^ (4 * J.card) * y) = M ^ p * r ^ (4 * k) * y ^ p := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      ← Finset.mul_sum, hsum, Finset.prod_const, Finset.prod_const, hpdef]
  rw [hU] at hbound
  have hterm : x ^ k * ((-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) *
        ∏ J ∈ π.parts, m₁ J) -
      (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) * ∏ J ∈ π.parts, m₂ J =
      (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) *
        (∏ J ∈ π.parts, (x ^ J.card * m₁ J) - ∏ J ∈ π.parts, m₂ J) := by
    rw [← hprod]
    ring
  rw [hterm, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Nat.abs_cast]
  rw [← hpdef] at hbound hp ⊢
  have hexp : z * y ^ p ≤ x ^ (-(1 / 2) + ((k : ℝ) + 1) / 1000) := by
    have e : z * y ^ p = x ^ (-(1 / 2) + (p : ℝ) / 1000) := by
      rw [hz, hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
      congr 1
      ring
    rw [e]
    refine Real.rpow_le_rpow_of_exponent_le hx ?_
    have : (p : ℝ) ≤ k := by exact_mod_cast hp
    linarith
  have hf : (0 : ℝ) ≤ ((p - 1).factorial : ℝ) := by positivity
  calc ((p - 1).factorial : ℝ) * |∏ J ∈ π.parts, (x ^ J.card * m₁ J) - ∏ J ∈ π.parts, m₂ J|
      ≤ ((p - 1).factorial : ℝ) * ((p : ℝ) * (r ^ 3 * z) * (M ^ p * r ^ (4 * k) * y ^ p)) :=
        mul_le_mul_of_nonneg_left hbound hf
    _ = ((p - 1).factorial : ℝ) * (p : ℝ) * M ^ p * r ^ (4 * k + 3) * (z * y ^ p) := by
        rw [pow_add]
        ring
    _ ≤ ((p - 1).factorial : ℝ) * (p : ℝ) * M ^ p * r ^ (4 * k + 3) *
          x ^ (-(1 / 2) + ((k : ℝ) + 1) / 1000) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
abbrev _root_.YangMills.DeltaSharedProofs.p501138 := @abs_scaled_moebius_sub_le
private theorem clusterRange_le_two_mul_rpow {x : ℝ} (hx : 1 ≤ x) :
    (TorusLumps.clusterRange x : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 100) := by apply _root_.YangMills.SharedProofs.p52588 <;> assumption
private theorem pow_mul_rpow_le_of_le_two_mul_rpow {x r : ℝ} {n : ℕ} (hx : 1 ≤ x) (hr0 : 0 ≤ r)
    (hr : r ≤ 2 * x ^ ((1 : ℝ) / 100)) (hn : n ≤ 8) :
    r ^ (4 * n + 3) * x ^ (-(1 / 2) + ((n : ℝ) + 1) / 1000) ≤ 2 ^ (4 * n + 3) * x ^ (-(1 / 10) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hv : (x ^ ((1 : ℝ) / 100)) ^ (4 * n + 3) = x ^ ((4 * (n : ℝ) + 3) / 100) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  have hn' : (n : ℝ) ≤ 8 := by exact_mod_cast hn
  calc r ^ (4 * n + 3) * x ^ (-(1 / 2) + ((n : ℝ) + 1) / 1000)
      ≤ (2 * x ^ ((1 : ℝ) / 100)) ^ (4 * n + 3) * x ^ (-(1 / 2) + ((n : ℝ) + 1) / 1000) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr0 hr _) (Real.rpow_nonneg hx0.le _)
    _ = 2 ^ (4 * n + 3) * x ^ ((4 * (n : ℝ) + 3) / 100 + (-(1 / 2) + ((n : ℝ) + 1) / 1000)) := by
        rw [mul_pow, hv, mul_assoc, ← Real.rpow_add hx0]
    _ ≤ 2 ^ (4 * n + 3) * x ^ (-(1 / 10) : ℝ) := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx ?_) (by positivity)
        linarith
abbrev _root_.YangMills.SharedProofs.p93516 := @pow_mul_rpow_le_of_le_two_mul_rpow
private def moebiusSum {k : ℕ} (m : Finset (Fin k) → ℝ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin k)), (-1 : ℝ) ^ (π.parts.card - 1) *
    ((π.parts.card - 1).factorial : ℝ) * ∏ J ∈ π.parts, m J
private def moebiusBound (k : ℕ) (M : ℝ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin k)), ((π.parts.card - 1).factorial : ℝ) * M ^ π.parts.card
private theorem abs_moebiusSum_le {k : ℕ} (m : Finset (Fin k) → ℝ) {M : ℝ} (hm : ∀ J, |m J| ≤ M) :
    |moebiusSum m| ≤ moebiusBound k M := by
  unfold moebiusSum moebiusBound
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun π _ => ?_)
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast, Finset.abs_prod]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ∏ J ∈ π.parts, |m J| ≤ ∏ _J ∈ π.parts, M :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun J _ => hm J
    _ = M ^ π.parts.card := by rw [Finset.prod_const]
section NearPlaquettes
variable {a : ℝ}
private theorem finite_setOf_center_near (ha : 0 < a) (c : Fin 4 → ℝ) (ρ : ℝ) :
    {p : InfiniteLattice.ElementaryPlaquette a | ∀ μ, |p.center μ - c μ| ≤ ρ}.Finite := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ μ, (|c μ| + ρ + a) / a ≤ N := by
    obtain ⟨N, hN⟩ := exists_nat_ge (∑ μ, (|c μ| + |ρ| + a) / a)
    refine ⟨N, fun μ => le_trans ?_ hN⟩
    refine le_trans ?_ (Finset.single_le_sum (f := fun μ => (|c μ| + |ρ| + a) / a)
      (fun _ _ => by positivity) (Finset.mem_univ μ))
    have := le_abs_self ρ
    exact div_le_div_of_nonneg_right (by linarith) ha.le
  choose nb hnb using fun p : InfiniteLattice.ElementaryPlaquette a => p.corner.2
  refine Set.Finite.of_injOn (f := fun p => (nb p, p.lowAxis, p.highAxis))
    (t := ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(N : ℤ)) (N : ℤ)) ×ˢ
      (Finset.univ : Finset (Fin 4 × Fin 4)) : Finset _).image
        (fun q : (Fin 4 → ℤ) × Fin 4 × Fin 4 => (q.1, q.2.1, q.2.2))) ?_ ?_ (Finset.finite_toSet _)
  · intro p hp
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset,
      Finset.mem_Icc, Finset.mem_univ, and_true]
    refine ⟨(nb p, p.lowAxis, p.highAxis), fun μ => ?_, rfl⟩
    have h1 := abs_le.mp (hp μ)
    have h2 : p.center μ = (nb p μ : ℝ) * a + (Pi.single p.lowAxis (a / 2) : Fin 4 → ℝ) μ +
        (Pi.single p.highAxis (a / 2) : Fin 4 → ℝ) μ := by
      have := hnb p μ
      simp only [InfiniteLattice.ElementaryPlaquette.center, Pi.add_apply]
      rw [this]
    have h3 : ∀ ν : Fin 4, 0 ≤ (Pi.single ν (a / 2) : Fin 4 → ℝ) μ ∧ (Pi.single ν (a / 2) : Fin 4 → ℝ) μ ≤ a / 2 := by
      intro ν
      by_cases h : μ = ν
      · subst h; simp; linarith
      · simp [Pi.single_eq_of_ne h]; linarith
    have h4 := h3 p.lowAxis
    have h5 := h3 p.highAxis
    have hNμ := hN μ
    rw [div_le_iff₀ ha] at hNμ
    have hc := abs_le.mp (le_refl |c μ|)
    have hle : (nb p μ : ℝ) * a ≤ (N : ℝ) * a := by linarith [h1.2, h1.1]
    have hge : -((N : ℝ) * a) ≤ (nb p μ : ℝ) * a := by linarith [h1.2, h1.1]
    constructor
    · have : -(N : ℝ) ≤ nb p μ := by
        by_contra hlt
        push Not at hlt
        nlinarith
      exact_mod_cast this
    · have : (nb p μ : ℝ) ≤ N := by
        by_contra hlt
        push Not at hlt
        nlinarith
      exact_mod_cast this
  · intro p _ q _ hpq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨h1, h2, h3⟩ := hpq
    refine InfiniteLattice.ElementaryPlaquette.ext ?_ h2 h3
    apply Subtype.ext
    funext μ
    rw [hnb p μ, hnb q μ, h1]
end NearPlaquettes
section SmearedEnergies
open InfiniteLattice
variable {L K : ℕ}
private theorem smearedEnergy_eq_sum (f : InfiniteLattice.AmbientSpace → ℝ) (W : Finset (LatticeCutoffPlaquette L K))
    (hW : ∀ p : LatticeCutoffPlaquette L K, f p.center ≠ 0 → p ∈ W) (U : RefinedGaugeField L K) :
    cutoffSmearedEnergyRe f U = ∑ p ∈ W, f p.center * faceEnergy U p := by
  unfold cutoffSmearedEnergyRe
  rw [cutoffSmearedEnergy_eq_finsum, finsum_eq_sum_of_support_subset (s := W)]
  · simp only [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  · intro p hp
    apply Finset.mem_coe.mpr
    apply hW
    intro h0
    simp [h0] at hp
private theorem faceEnergy_isBoundedRealRV
    (hA : GibbsAtFixedSpacing.FaceEnergyIndependentOfBasepointAndOrientation) {a : ℝ} (ha : 0 < a)
    (p : ElementaryPlaquette a) : Probability.IsBoundedRealRV fun U : GaugeField a => faceEnergy U p := by
  refine ⟨(continuous_faceEnergy p).measurable, 2, fun U => ?_⟩
  obtain ⟨h0, h2⟩ := ((hA.2 a ha).2.1 p).2.2.2 U
  rw [abs_le]
  constructor <;> linarith
end SmearedEnergies
private theorem exp_neg_mul_clusterRange_le {x c : ℝ} (hx : 1 ≤ x) (hc : 0 < c) :
    Real.exp (-(c * (TorusLumps.clusterRange x : ℝ))) ≤ ((Nat.factorial 10 : ℝ) / c ^ 10) * x ^ (-(1 / 10) : ℝ) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨w, hw⟩ : ∃ w, w = x ^ ((1 : ℝ) / 100) := ⟨_, rfl⟩
  have hw1 : 1 ≤ w := hw ▸ Real.one_le_rpow hx (by norm_num)
  have hwr : w ≤ (TorusLumps.clusterRange x : ℝ) := by
    rw [hw]
    exact Nat.le_ceil _
  have hpow : w ^ 10 = x ^ ((1 : ℝ) / 10) := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hcr : 0 ≤ c * w := by positivity
  have h1 : (c * w) ^ 10 / (Nat.factorial 10 : ℝ) ≤ Real.exp (c * w) := Real.pow_div_factorial_le_exp _ hcr 10
  have h2 : Real.exp (c * w) ≤ Real.exp (c * (TorusLumps.clusterRange x : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hwr hc.le)
  have h3 : Real.exp (-(c * (TorusLumps.clusterRange x : ℝ))) ≤ ((c * w) ^ 10 / (Nat.factorial 10 : ℝ))⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) (h1.trans h2)
  refine h3.trans (le_of_eq ?_)
  rw [Real.rpow_neg hx0.le, ← hpow]
  field_simp
private theorem ae_forall_of_continuous_le {Ω E : Type} {Pt : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    [SecondCountableTopology E] (ν : Measure Ω) (arr : Pt → E) (G : Ω → E → ℝ) (b : ℝ) (hG : ∀ U, Continuous (G U))
    (h : ∀ S, ∀ᵐ U ∂ν, G U (arr S) ≤ b) : ∀ᵐ U ∂ν, ∀ S, G U (arr S) ≤ b := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense (Set.range arr)
  have hall : ∀ᵐ U ∂ν, ∀ w ∈ s, G U w.1 ≤ b := by
    rw [ae_ball_iff hsc]
    intro w _
    obtain ⟨S, hS⟩ := w.2
    have := h S
    simpa [hS] using this
  filter_upwards [hall] with U hU S
  have hcl : IsClosed {w : Set.range arr | G U w.1 ≤ b} :=
    isClosed_le ((hG U).comp continuous_subtype_val) continuous_const
  exact closure_minimal (fun w hw => hU w hw) hcl (hsd ⟨arr S, S, rfl⟩)
private theorem forAllHullParameters_of_forAllParameters {Q : MomentParameters → Prop} (h : ForAllParameters Q) :
    ForAllHullParameters Q := by apply _root_.YangMills.SharedProofs.p12974 <;> assumption
private theorem forAllHullParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllHullParameters Q₁)
    (h₂ : ForAllHullParameters Q₂) : ForAllHullParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p1668 <;> assumption
private theorem forAllHullParameters_mono {Q₁ Q₂ : MomentParameters → Prop} (h : ForAllHullParameters Q₁)
    (f : ∀ Λ : MomentParameters, 2 ≤ Λ.k → Λ.k ≤ 8 → 0 < Λ.stepParams.coupling → Q₁ Λ → Q₂ Λ) :
    ForAllHullParameters Q₂ := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hrt, ?_⟩
  intro L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  obtain ⟨M, G⟩ := H L hL hL₀ Tb e₁ e₂ d₁ d₂ d₃ d₄ d₅
  refine ⟨M, ?_⟩
  intro Kr k₁ k₂ k₃ k₄ k₅
  obtain ⟨y₀, Y⟩ := G Kr k₁ k₂ k₃ k₄ k₅
  refine ⟨y₀, ?_⟩
  intro y hy hrow hw g hg hgy k _ hk2 hk8 R d hd
  refine f _ hk2 hk8 ?_ (Y y hy hrow hw g hg hgy k hk2 hk8 R d hd)
  have : (Tb.stepParameters y).coupling = a := e₁
  show 0 < (Tb.stepParameters y).coupling
  linarith
abbrev _root_.YangMills.SharedProofs.p22893 := @forAllHullParameters_mono
section PointwiseBound
variable {Λ : MomentParameters}
private theorem stateUrsell_eq_moebiusSum (hJ : Cumulants.MixedCumulantMomentExpansion)
    (hML : Cumulants.MomentCumulantRelations.Holds) (S : MomentPoint Λ) {K : ℕ}
    (ρ : Measure (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K)) [IsProbabilityMeasure ρ] (hk : 2 ≤ Λ.k)
    (hb : ∀ i, Probability.IsBoundedRealRV
      (fun U : InfiniteLattice.RefinedGaugeField Λ.stepParams.side K =>
        InfiniteLattice.cutoffSmearedEnergyRe (S.rescaledTestFunction i) U))
    (c : Fin Λ.k → ℝ) : S.stateUrsell ρ = ((moebiusSum fun J => S.centredStateMoment ρ c J : ℝ) : ℂ) := by
  have shift := (hML _ ρ).2.2.1 Λ.k
    (fun i U => InfiniteLattice.cutoffSmearedEnergyRe (S.rescaledTestFunction i) U) (fun i => -c i) hk hb
  have hb' : ∀ i, Probability.IsBoundedRealRV
      (fun U : InfiniteLattice.RefinedGaugeField Λ.stepParams.side K =>
        InfiniteLattice.cutoffSmearedEnergyRe (S.rescaledTestFunction i) U + -c i) := by
    intro i
    obtain ⟨B, hB⟩ := (hb i).bounded
    refine ⟨(hb i).measurable.add_const _, B + |c i|, fun U => ?_⟩
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    linarith [hB U]
  have mom := hJ _ ρ Λ.k
    (fun i U => InfiniteLattice.cutoffSmearedEnergyRe (S.rescaledTestFunction i) U + -c i) (by omega) hb'
  unfold MomentPoint.stateUrsell InfiniteLattice.ursellFunctionOfFamily
  rw [← shift, mom]
  simp only [moebiusSum, MomentPoint.centredStateMoment, sub_eq_add_neg, SetPartition.blockCount]
  push_cast
  rfl
private theorem exists_finset_support_window (Λ : MomentParameters) (K s : ℕ) (c : Fin 4 → ℝ) {a : ℝ}
    (hLK : a = InfiniteLattice.refinedSpacing Λ.stepParams.side K) (ha : 0 < a) :
    ∃ W : Finset (InfiniteLattice.LatticeCutoffPlaquette Λ.stepParams.side K), W.Nonempty ∧
      ∀ S : MomentPoint Λ, S.data.windowLevel = K → S.data.scaleLevel = s → S.data.center = c →
      ∀ (i : Fin Λ.k) (p : InfiniteLattice.LatticeCutoffPlaquette Λ.stepParams.side K),
        S.rescaledTestFunction i p.center ≠ 0 → p ∈ W := by
  classical
  subst hLK
  have hLp : (0 : ℝ) < Λ.stepParams.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = Λ.R * (Λ.stepParams.side : ℝ) ^ s / (Λ.stepParams.side : ℝ) ^ K := ⟨_, rfl⟩
  let p₀ : InfiniteLattice.LatticeCutoffPlaquette Λ.stepParams.side K := ⟨0, 0, 1, by decide⟩
  refine ⟨(finite_setOf_center_near ha c ρ).toFinset ∪ {p₀}, ⟨p₀, by simp⟩, ?_⟩
  intro S hK hs hx i p hp
  refine Finset.mem_union_left _ ?_
  rw [Set.Finite.mem_toFinset]
  intro μ
  unfold MomentPoint.rescaledTestFunction at hp
  rw [hK, hs, hx] at hp
  have hv := S.supAdmissible.isSupTestFamily.abs_coord_le i _ (subset_tsupport _ hp) μ
  have hc : 0 < (Λ.stepParams.side : ℝ) ^ K / (Λ.stepParams.side : ℝ) ^ s := by positivity
  simp only [abs_mul, abs_of_pos hc] at hv
  rw [hρ]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hv
  rw [le_div_iff₀ (by positivity)]
  linarith
private def pointwiseConstant (k : ℕ) (C X₀ A c₁ D X₂ : ℝ) : ℝ :=
  partitionWeightSum k (10 * (|C| + 1)) * 2 ^ (4 * k + 3) + |A| * ((Nat.factorial 10 : ℝ) / c₁ ^ 10) +
    |D| * (1 + (max X₂ 1) ^ ((1 : ℝ) / 10)) + (X₀ ^ k * moebiusBound k (|C| + 1) + |D|) * X₀ ^ ((1 : ℝ) / 10)
set_option maxHeartbeats 1600000 in
private theorem abs_scaled_moebiusSum_sub_cycleSum_le (hk8 : Λ.k ≤ 8)
    (hGa : ∀ (s n : ℕ) [NeZero n], ∃ μ : Measure (LevelChain Λ.stepParams.side s n),
      IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling s n) μ)
    {C X₀ A c₁ D X₂ : ℝ} (hX₀ : 1 ≤ X₀) (hc₁ : 0 < c₁)
    (hF : ∀ S : MomentPoint Λ, ∀ d : ℕ, S.lastSeparated + d = S.data.windowLevel →
      ∀ μ : Measure (LevelChain Λ.stepParams.side (S.lastSeparated + d) (S.data.period Λ.stepParams.side)),
      IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (S.lastSeparated + d) (S.data.period Λ.stepParams.side)) μ →
      |jointCumulant μ (fun i => S.halfForm d (S.data.period Λ.stepParams.side) i) -
        jointCumulant μ (fun i => S.observableAt (S.lastSeparated + d) (S.data.period Λ.stepParams.side) i)| ≤
        A * Real.exp (-(c₁ * (S.range : ℝ))))
    (hV : ∀ S : MomentPoint Λ, ∀ μ : Measure (LevelChain Λ.stepParams.side S.data.windowLevel (S.data.period Λ.stepParams.side)),
      IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling S.data.windowLevel (S.data.period Λ.stepParams.side)) μ →
      |jointCumulant μ (fun i => S.observableAt S.data.windowLevel (S.data.period Λ.stepParams.side) i) -
          S.latticeCycleSumAt S.data.scaleLevel| ≤
        D * (Λ.stepParams.side : ℝ) ^ (-(4 * ((S.data.windowLevel : ℝ) - (S.data.scaleLevel : ℝ)))) ∧
      (X₂ ≤ S.scaleCoupling → |jointCumulant μ (fun i => S.observableAt S.data.windowLevel (S.data.period Λ.stepParams.side) i) -
          S.latticeCycleSumAt S.data.scaleLevel| ≤ D * S.scaleCoupling⁻¹) ∧
      |S.latticeCycleSumAt S.data.scaleLevel| ≤ D)
    (S : MomentPoint Λ) (hx0 : 0 < S.scaleCoupling) {K : ℕ}
    (ρ : Measure (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K)) (c : Fin Λ.k → ℝ)
    (small : S.scaleCoupling ≤ X₀ → ∀ B : Finset (Fin Λ.k), |S.centredStateMoment ρ c B| ≤ C)
    (large : X₀ ≤ S.scaleCoupling → ∀ δ : ℝ, 0 < δ → ∃ (S' : MomentPoint Λ) (d : ℕ)
      (_ : S'.lastSeparated + d = S'.data.windowLevel)
      (μ : Measure (LevelChain Λ.stepParams.side (S'.lastSeparated + d) (S'.data.period Λ.stepParams.side))),
        S.SameDataOtherSide S' ∧
        IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling (S'.lastSeparated + d) (S'.data.period Λ.stepParams.side)) μ ∧
        ∀ B : Finset (Fin Λ.k),
          |S.scaleCoupling ^ B.card * S.centredStateMoment ρ c B -
              ∫ X, ∏ i ∈ B, S'.halfForm d (S'.data.period Λ.stepParams.side) i X ∂μ| ≤
            C * (S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ) + δ ∧
          |∫ X, ∏ i ∈ B, S'.halfForm d (S'.data.period Λ.stepParams.side) i X ∂μ| ≤
            C * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000)) :
    |S.scaleCoupling ^ Λ.k * moebiusSum (fun J => S.centredStateMoment ρ c J) - S.latticeCycleSumAt S.data.scaleLevel| ≤
      pointwiseConstant Λ.k C X₀ A c₁ D X₂ * S.scaleCoupling ^ (-(1 / 10) : ℝ) := by
  have hCa : 0 ≤ |C| := abs_nonneg _
  have hy0 : 0 ≤ S.scaleCoupling ^ (-(1 / 10) : ℝ) := Real.rpow_nonneg hx0.le _
  have hP1 : 0 ≤ partitionWeightSum Λ.k (10 * (|C| + 1)) * 2 ^ (4 * Λ.k + 3) :=
    mul_nonneg (partitionWeightSum_nonneg _ (by linarith)) (by positivity)
  have hP2 : 0 ≤ |A| * ((Nat.factorial 10 : ℝ) / c₁ ^ 10) := by positivity
  have hP3 : 0 ≤ |D| * (1 + (max X₂ 1) ^ ((1 : ℝ) / 10)) :=
    mul_nonneg (abs_nonneg _) (add_nonneg zero_le_one (Real.rpow_nonneg (by positivity) _))
  have hPz : 0 ≤ moebiusBound Λ.k (|C| + 1) := Finset.sum_nonneg fun _ _ => by positivity
  have hX0 : 0 < X₀ := by linarith
  have hP4 : 0 ≤ (X₀ ^ Λ.k * moebiusBound Λ.k (|C| + 1) + |D|) * X₀ ^ ((1 : ℝ) / 10) := by positivity
  rcases le_total S.scaleCoupling X₀ with hs | hl
  · obtain ⟨μ, hμ⟩ := hGa S.data.windowLevel (S.data.period Λ.stepParams.side)
    have hγ : |S.latticeCycleSumAt S.data.scaleLevel| ≤ |D| := (hV S μ hμ).2.2.trans (le_abs_self _)
    have hmm : |moebiusSum (fun J => S.centredStateMoment ρ c J)| ≤ moebiusBound Λ.k (|C| + 1) :=
      abs_moebiusSum_le _ fun J => (small hs J).trans (by linarith [le_abs_self C])
    have hxk : S.scaleCoupling ^ Λ.k ≤ X₀ ^ Λ.k := pow_le_pow_left₀ hx0.le hs _
    have h1 : |S.scaleCoupling ^ Λ.k * moebiusSum (fun J => S.centredStateMoment ρ c J) -
          S.latticeCycleSumAt S.data.scaleLevel| ≤
        X₀ ^ Λ.k * moebiusBound Λ.k (|C| + 1) + |D| := by
      refine (abs_sub _ _).trans (add_le_add ?_ hγ)
      rw [abs_mul, abs_of_pos (pow_pos hx0 _)]
      exact mul_le_mul hxk hmm (abs_nonneg _) (by positivity)
    have h2 : 1 ≤ X₀ ^ ((1 : ℝ) / 10) * S.scaleCoupling ^ (-(1 / 10) : ℝ) := by
      have h3 : X₀ ^ (-(1 / 10) : ℝ) ≤ S.scaleCoupling ^ (-(1 / 10) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hx0 hs (by norm_num)
      have h4 : X₀ ^ ((1 : ℝ) / 10) * X₀ ^ (-(1 / 10) : ℝ) = 1 := by
        rw [← Real.rpow_add hX0]
        norm_num
      calc (1 : ℝ) = X₀ ^ ((1 : ℝ) / 10) * X₀ ^ (-(1 / 10) : ℝ) := h4.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hq : 0 ≤ X₀ ^ Λ.k * moebiusBound Λ.k (|C| + 1) + |D| := by positivity
    calc _ ≤ X₀ ^ Λ.k * moebiusBound Λ.k (|C| + 1) + |D| := h1
      _ ≤ (X₀ ^ Λ.k * moebiusBound Λ.k (|C| + 1) + |D|) *
            (X₀ ^ ((1 : ℝ) / 10) * S.scaleCoupling ^ (-(1 / 10) : ℝ)) :=
          le_mul_of_one_le_right hq h2
      _ = (X₀ ^ Λ.k * moebiusBound Λ.k (|C| + 1) + |D|) * X₀ ^ ((1 : ℝ) / 10) *
            S.scaleCoupling ^ (-(1 / 10) : ℝ) := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hy0
          unfold pointwiseConstant
          linarith
  · have hx1 : 1 ≤ S.scaleCoupling := hX₀.trans hl
    obtain ⟨e, he⟩ : ∃ e, e = S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ) := ⟨_, rfl⟩
    have he0 : 0 < e := he ▸ Real.rpow_pos_of_pos hx0 _
    obtain ⟨S', d, hd, μ, hS', hμ, hB⟩ := large hl e he0
    have hxs : S'.scaleCoupling = S.scaleCoupling := by
      unfold MomentPoint.scaleCoupling MomentPoint.coupling
      rw [hS'.scaleLevel_eq, hS'.β_eq]
    have hr : S'.range = S.range := by
      unfold MomentPoint.range
      rw [hxs]
    have hγ : S'.latticeCycleSumAt S'.data.scaleLevel = S.latticeCycleSumAt S.data.scaleLevel := by
      unfold MomentPoint.latticeCycleSumAt
      rw [hS'.scaleLevel_eq, hS'.fn_eq]
    have hval : ∀ n' : ℕ, n' = S'.data.windowLevel →
        ∀ μ' : Measure (LevelChain Λ.stepParams.side n' (S'.data.period Λ.stepParams.side)),
        IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling n' (S'.data.period Λ.stepParams.side)) μ' →
        |jointCumulant μ' (fun i => S'.observableAt n' (S'.data.period Λ.stepParams.side) i) -
            S'.latticeCycleSumAt S'.data.scaleLevel| ≤
          D * (Λ.stepParams.side : ℝ) ^ (-(4 * ((S'.data.windowLevel : ℝ) - (S'.data.scaleLevel : ℝ)))) ∧
        (X₂ ≤ S'.scaleCoupling → |jointCumulant μ' (fun i => S'.observableAt n' (S'.data.period Λ.stepParams.side) i) -
            S'.latticeCycleSumAt S'.data.scaleLevel| ≤ D * S'.scaleCoupling⁻¹) := by
      intro n' hn
      subst hn
      intro μ' hμ'
      exact ⟨(hV S' μ' hμ').1, (hV S' μ' hμ').2.1⟩
    obtain ⟨hv1, hv2⟩ := hval _ hd μ hμ
    rw [hγ, hxs] at hv2
    rw [hγ] at hv1
    have hL1 : (1 : ℝ) ≤ Λ.stepParams.side := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
    have hfree : |jointCumulant μ (fun i => S'.observableAt (S'.lastSeparated + d) (S'.data.period Λ.stepParams.side) i) -
          S.latticeCycleSumAt S.data.scaleLevel| ≤
        |D| * (1 + (max X₂ 1) ^ ((1 : ℝ) / 10)) * S.scaleCoupling ^ (-(1 / 10) : ℝ) := by
      have hm1 : (1 : ℝ) ≤ max X₂ 1 := le_max_right _ _
      have hm0 : 0 < max X₂ 1 := by linarith
      rcases le_total X₂ S.scaleCoupling with h2 | h2
      · refine (hv2 h2).trans ?_
        have h3 : S.scaleCoupling⁻¹ ≤ S.scaleCoupling ^ (-(1 / 10) : ℝ) := by
          rw [← Real.rpow_neg_one]
          exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        have h4 : 0 ≤ S.scaleCoupling⁻¹ := by positivity
        calc D * S.scaleCoupling⁻¹ ≤ |D| * S.scaleCoupling⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self _) h4
          _ ≤ |D| * S.scaleCoupling ^ (-(1 / 10) : ℝ) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
          _ ≤ |D| * (1 + (max X₂ 1) ^ ((1 : ℝ) / 10)) * S.scaleCoupling ^ (-(1 / 10) : ℝ) := by
              refine mul_le_mul_of_nonneg_right ?_ hy0
              refine le_mul_of_one_le_right (abs_nonneg _) ?_
              have := Real.rpow_nonneg hm0.le ((1 : ℝ) / 10)
              linarith
      · refine hv1.trans ?_
        have hsK : (S'.data.scaleLevel : ℝ) ≤ S'.data.windowLevel := by
          exact_mod_cast S'.supAdmissible.scaleLevel_le
        have h3 : (Λ.stepParams.side : ℝ) ^ (-(4 * ((S'.data.windowLevel : ℝ) - (S'.data.scaleLevel : ℝ)))) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
        have h3' : 0 ≤ (Λ.stepParams.side : ℝ) ^ (-(4 * ((S'.data.windowLevel : ℝ) - (S'.data.scaleLevel : ℝ)))) := by
          positivity
        have h4 : 1 ≤ (max X₂ 1) ^ ((1 : ℝ) / 10) * S.scaleCoupling ^ (-(1 / 10) : ℝ) := by
          have h5 : (max X₂ 1) ^ (-(1 / 10) : ℝ) ≤ S.scaleCoupling ^ (-(1 / 10) : ℝ) :=
            Real.rpow_le_rpow_of_nonpos hx0 (h2.trans (le_max_left _ _)) (by norm_num)
          have h6 : (max X₂ 1) ^ ((1 : ℝ) / 10) * (max X₂ 1) ^ (-(1 / 10) : ℝ) = 1 := by
            rw [← Real.rpow_add hm0]
            norm_num
          calc (1 : ℝ) = (max X₂ 1) ^ ((1 : ℝ) / 10) * (max X₂ 1) ^ (-(1 / 10) : ℝ) := h6.symm
            _ ≤ _ := mul_le_mul_of_nonneg_left h5 (by positivity)
        have h7 : 1 ≤ (1 + (max X₂ 1) ^ ((1 : ℝ) / 10)) * S.scaleCoupling ^ (-(1 / 10) : ℝ) := by
          rw [add_mul, one_mul]
          linarith
        calc D * (Λ.stepParams.side : ℝ) ^ (-(4 * ((S'.data.windowLevel : ℝ) - (S'.data.scaleLevel : ℝ)))) ≤ |D| * 1 :=
              mul_le_mul (le_abs_self _) h3 h3' (abs_nonneg _)
          _ ≤ |D| * ((1 + (max X₂ 1) ^ ((1 : ℝ) / 10)) * S.scaleCoupling ^ (-(1 / 10) : ℝ)) :=
              mul_le_mul_of_nonneg_left h7 (abs_nonneg _)
          _ = |D| * (1 + (max X₂ 1) ^ ((1 : ℝ) / 10)) * S.scaleCoupling ^ (-(1 / 10) : ℝ) := by ring
    have hchain : |jointCumulant μ (fun i => S'.halfForm d (S'.data.period Λ.stepParams.side) i) -
        jointCumulant μ (fun i => S'.observableAt (S'.lastSeparated + d) (S'.data.period Λ.stepParams.side) i)| ≤
        |A| * ((Nat.factorial 10 : ℝ) / c₁ ^ 10) * S.scaleCoupling ^ (-(1 / 10) : ℝ) := by
      refine (hF S' d hd μ hμ).trans ?_
      rw [hr]
      have hexp := exp_neg_mul_clusterRange_le hx1 hc₁
      have hexp0 : 0 ≤ Real.exp (-(c₁ * (S.range : ℝ))) := (Real.exp_pos _).le
      calc A * Real.exp (-(c₁ * (S.range : ℝ))) ≤ |A| * Real.exp (-(c₁ * (S.range : ℝ))) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hexp0
        _ ≤ |A| * (((Nat.factorial 10 : ℝ) / c₁ ^ 10) * S.scaleCoupling ^ (-(1 / 10) : ℝ)) :=
            mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
        _ = _ := by ring
    obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 10 * (|C| + 1) := ⟨_, rfl⟩
    have hM1 : 1 ≤ M := by rw [hMdef]; linarith
    have hr0 : (0 : ℝ) ≤ (S.range : ℝ) := Nat.cast_nonneg _
    have hrle : (S.range : ℝ) ≤ 2 * S.scaleCoupling ^ ((1 : ℝ) / 100) := clusterRange_le_two_mul_rpow hx1
    have hr1 : (1 : ℝ) ≤ (S.range : ℝ) := by
      have h1 : 1 ≤ S.scaleCoupling ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx1 (by norm_num)
      have h2 : S.scaleCoupling ^ ((1 : ℝ) / 100) ≤ (S.range : ℝ) := Nat.le_ceil _
      linarith
    obtain ⟨y', hy'⟩ : ∃ y', y' = S.scaleCoupling ^ ((1 : ℝ) / 1000) := ⟨_, rfl⟩
    have hy'0 : 0 < y' := hy' ▸ Real.rpow_pos_of_pos hx0 _
    have hsmall : (S.range : ℝ) ^ 3 * e ≤ 8 * y' := by
      have h1 : (S.range : ℝ) ^ 3 ≤ (2 * S.scaleCoupling ^ ((1 : ℝ) / 100)) ^ 3 := pow_le_pow_left₀ hr0 hrle 3
      have h2 : (2 * S.scaleCoupling ^ ((1 : ℝ) / 100)) ^ 3 * e =
          8 * (S.scaleCoupling ^ (-(47 / 100) : ℝ) * y') := by
        have h3 : (S.scaleCoupling ^ ((1 : ℝ) / 100)) ^ 3 = S.scaleCoupling ^ ((3 : ℝ) / 100) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
          norm_num
        rw [mul_pow, h3, he, hy', mul_assoc, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
        have h5 : (3 / 100 + (-(1 / 2) + 1 / 1000) : ℝ) = -(47 / 100) + 1 / 1000 := by norm_num
        rw [h5]
        norm_num
      have h4 : S.scaleCoupling ^ (-(47 / 100) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
      calc (S.range : ℝ) ^ 3 * e ≤ (2 * S.scaleCoupling ^ ((1 : ℝ) / 100)) ^ 3 * e :=
            mul_le_mul_of_nonneg_right h1 he0.le
        _ = 8 * (S.scaleCoupling ^ (-(47 / 100) : ℝ) * y') := h2
        _ ≤ 8 * (1 * y') := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hy'0.le) (by norm_num)
        _ = 8 * y' := by ring
    have hd1 : ∀ B : Finset (Fin Λ.k), |S.scaleCoupling ^ B.card * S.centredStateMoment ρ c B -
        ∫ X, ∏ i ∈ B, S'.halfForm d (S'.data.period Λ.stepParams.side) i X ∂μ| ≤
          (|C| + 1) * (S.range : ℝ) ^ (4 * B.card + 3) * e := by
      intro B
      refine (hB B).1.trans ?_
      rw [← he]
      have h1 : (1 : ℝ) ≤ (S.range : ℝ) ^ (4 * B.card + 3) := one_le_pow₀ hr1
      have h2 : C * (S.range : ℝ) ^ (4 * B.card + 3) * e ≤ |C| * (S.range : ℝ) ^ (4 * B.card + 3) * e := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) he0.le
      nlinarith
    have hb1 : ∀ B : Finset (Fin Λ.k), |∫ X, ∏ i ∈ B, S'.halfForm d (S'.data.period Λ.stepParams.side) i X ∂μ| ≤
        (|C| + 1) * (S.range : ℝ) ^ (4 * B.card) * y' := by
      intro B
      refine (hB B).2.trans ?_
      rw [← hy']
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) hy'0.le
      linarith [le_abs_self C]
    have hC1M : |C| + 1 ≤ M := by
      rw [hMdef]
      linarith
    have hA1 : ∀ B : Finset (Fin Λ.k), |S.scaleCoupling ^ B.card * S.centredStateMoment ρ c B -
        ∫ X, ∏ i ∈ B, S'.halfForm d (S'.data.period Λ.stepParams.side) i X ∂μ| ≤
        M * (S.range : ℝ) ^ (4 * B.card + 3) * S.scaleCoupling ^ (-(1 / 2) + 1 / 1000 : ℝ) := by
      intro B
      refine (hd1 B).trans ?_
      rw [← he]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1M (by positivity)) he0.le
    have hA3 : ∀ B : Finset (Fin Λ.k), |∫ X, ∏ i ∈ B, S'.halfForm d (S'.data.period Λ.stepParams.side) i X ∂μ| ≤
        M * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000) := by
      intro B
      refine (hb1 B).trans ?_
      rw [← hy']
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1M (by positivity)) hy'0.le
    have hA2 : ∀ B : Finset (Fin Λ.k), |S.scaleCoupling ^ B.card * S.centredStateMoment ρ c B| ≤
        M * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 1000) := by
      intro B
      obtain ⟨u, hu⟩ : ∃ u, u = S.scaleCoupling ^ B.card * S.centredStateMoment ρ c B := ⟨_, rfl⟩
      obtain ⟨v, hv⟩ : ∃ v, v = ∫ X, ∏ i ∈ B, S'.halfForm d (S'.data.period Λ.stepParams.side) i X ∂μ := ⟨_, rfl⟩
      have h1 := hd1 B
      have h2 := hb1 B
      rw [← hu, ← hv] at h1
      rw [← hv] at h2
      rw [← hu, ← hy']
      obtain ⟨Q, hQ⟩ : ∃ Q, Q = (|C| + 1) * (S.range : ℝ) ^ (4 * B.card) := ⟨_, rfl⟩
      have hQ0 : 0 ≤ Q := by
        rw [hQ]
        positivity
      have h4 : (|C| + 1) * (S.range : ℝ) ^ (4 * B.card + 3) * e = Q * ((S.range : ℝ) ^ 3 * e) := by
        rw [hQ, pow_add]
        ring
      rw [h4] at h1
      rw [← hQ] at h2
      have h5 : Q * ((S.range : ℝ) ^ 3 * e) ≤ Q * (8 * y') := mul_le_mul_of_nonneg_left hsmall hQ0
      have h6 : |u| ≤ |u - v| + |v| := by
        have := abs_add_le (u - v) v
        simpa using this
      have h7 : M * (S.range : ℝ) ^ (4 * B.card) * y' = 10 * (Q * y') := by
        rw [hMdef, hQ]
        ring
      rw [h7]
      have h8 : 0 ≤ Q * y' := mul_nonneg hQ0 hy'0.le
      linarith
    have hmain := abs_scaled_moebius_sub_le (fun B => S.centredStateMoment ρ c B)
      (fun B => ∫ X, ∏ i ∈ B, S'.halfForm d (S'.data.period Λ.stepParams.side) i X ∂μ)
      S.scaleCoupling (S.range : ℝ) M hx1 hr0 hM1 hA1 hA2 hA3
    have hpow := pow_mul_rpow_le_of_le_two_mul_rpow hx1 hr0 hrle hk8
    have hPc0 := partitionWeightSum_nonneg Λ.k (by linarith : (0 : ℝ) ≤ M)
    have hfirst : |S.scaleCoupling ^ Λ.k * moebiusSum (fun J => S.centredStateMoment ρ c J) -
        jointCumulant μ (fun i => S'.halfForm d (S'.data.period Λ.stepParams.side) i)| ≤
        partitionWeightSum Λ.k M * 2 ^ (4 * Λ.k + 3) * S.scaleCoupling ^ (-(1 / 10) : ℝ) := by
      refine (show _ ≤ _ from hmain).trans ?_
      calc partitionWeightSum Λ.k M * (S.range : ℝ) ^ (4 * Λ.k + 3) *
              S.scaleCoupling ^ (-(1 / 2) + ((Λ.k : ℝ) + 1) / 1000)
          = partitionWeightSum Λ.k M * ((S.range : ℝ) ^ (4 * Λ.k + 3) *
              S.scaleCoupling ^ (-(1 / 2) + ((Λ.k : ℝ) + 1) / 1000)) := by ring
        _ ≤ partitionWeightSum Λ.k M * (2 ^ (4 * Λ.k + 3) * S.scaleCoupling ^ (-(1 / 10) : ℝ)) :=
            mul_le_mul_of_nonneg_left hpow hPc0
        _ = _ := by ring
    have htri := abs_sub_le (S.scaleCoupling ^ Λ.k * moebiusSum (fun J => S.centredStateMoment ρ c J))
      (jointCumulant μ (fun i => S'.halfForm d (S'.data.period Λ.stepParams.side) i))
      (S.latticeCycleSumAt S.data.scaleLevel)
    have htri2 := abs_sub_le (jointCumulant μ (fun i => S'.halfForm d (S'.data.period Λ.stepParams.side) i))
      (jointCumulant μ (fun i => S'.observableAt (S'.lastSeparated + d) (S'.data.period Λ.stepParams.side) i))
      (S.latticeCycleSumAt S.data.scaleLevel)
    rw [hMdef] at hfirst
    have hfin : pointwiseConstant Λ.k C X₀ A c₁ D X₂ * S.scaleCoupling ^ (-(1 / 10) : ℝ) =
        partitionWeightSum Λ.k (10 * (|C| + 1)) * 2 ^ (4 * Λ.k + 3) * S.scaleCoupling ^ (-(1 / 10) : ℝ) +
        |A| * ((Nat.factorial 10 : ℝ) / c₁ ^ 10) * S.scaleCoupling ^ (-(1 / 10) : ℝ) +
        |D| * (1 + (max X₂ 1) ^ ((1 : ℝ) / 10)) * S.scaleCoupling ^ (-(1 / 10) : ℝ) +
        (X₀ ^ Λ.k * moebiusBound Λ.k (|C| + 1) + |D|) * X₀ ^ ((1 : ℝ) / 10) * S.scaleCoupling ^ (-(1 / 10) : ℝ) := by
      unfold pointwiseConstant
      ring
    have hlast := mul_nonneg hP4 hy0
    rw [hfin]
    linarith
end PointwiseBound
section SingleNullSet
variable {Λ : MomentParameters}
private def cycleSumOfValues (Λ : MomentParameters) (s : ℕ) (v : Fin Λ.k → IntPlaquette → ℝ) : ℝ :=
  3 * (if Λ.k = 2 then 1 / 2 else 1) * ∑ σ ∈ CyclicFormula.unorientedCyclicOrders Λ.k,
    ∑ p ∈ Fintype.piFinset (fun _ : Fin Λ.k => plaquetteBox (⌈Λ.R * (Λ.stepParams.side : ℝ) ^ s⌉₊ + 2)),
      (∏ i, v i (p i)) * ∏ c : Fin Λ.k, intCurvatureProjection (p (σ c)) (p (σ (c + 1)))
private theorem smearedEnergy_isBoundedRealRV
    (hA : GibbsAtFixedSpacing.FaceEnergyIndependentOfBasepointAndOrientation)
    (S : MomentPoint Λ) {K : ℕ} (hK : S.data.windowLevel = K)
    (ha : 0 < InfiniteLattice.refinedSpacing Λ.stepParams.side K) (i : Fin Λ.k) :
    Probability.IsBoundedRealRV
      (fun U : InfiniteLattice.RefinedGaugeField Λ.stepParams.side K =>
        InfiniteLattice.cutoffSmearedEnergyRe (S.rescaledTestFunction i) U) := by
  obtain ⟨W, -, hW⟩ := exists_finset_support_window Λ K S.data.scaleLevel S.data.center rfl ha
  have e : (fun U : InfiniteLattice.RefinedGaugeField Λ.stepParams.side K =>
        InfiniteLattice.cutoffSmearedEnergyRe (S.rescaledTestFunction i) U) =
      fun U : InfiniteLattice.RefinedGaugeField Λ.stepParams.side K =>
        ∑ p ∈ W, S.rescaledTestFunction i p.center * InfiniteLattice.faceEnergy U p :=
    funext fun U => smearedEnergy_eq_sum _ W (fun p hp => hW S hK rfl rfl i p hp) U
  rw [e]
  refine ⟨Finset.measurable_sum _ fun p _ => (faceEnergy_isBoundedRealRV hA ha p).measurable.const_mul _,
    ∑ p ∈ W, |S.rescaledTestFunction i p.center| * 2, fun U => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [abs_mul]
  obtain ⟨h0, h2⟩ := ((hA.2 _ ha).2.1 p).2.2.2 U
  rw [abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
private theorem stateUrsell_eq_sum_mixedCumulant (hML : Cumulants.MomentCumulantRelations.Holds)
    (hA : GibbsAtFixedSpacing.FaceEnergyIndependentOfBasepointAndOrientation) (S : MomentPoint Λ) {K : ℕ}
    (ha : 0 < InfiniteLattice.refinedSpacing Λ.stepParams.side K)
    (W : Finset (InfiniteLattice.LatticeCutoffPlaquette Λ.stepParams.side K)) [Nonempty ↥W]
    (hW : ∀ (i : Fin Λ.k) (p : InfiniteLattice.LatticeCutoffPlaquette Λ.stepParams.side K),
      S.rescaledTestFunction i p.center ≠ 0 → p ∈ W) (h1 : 1 ≤ Λ.k)
    (ρ : Measure (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K)) [IsProbabilityMeasure ρ] :
    S.stateUrsell ρ = ∑ r : Fin Λ.k → ↥W, ((∏ l, S.rescaledTestFunction l (r l).1.center : ℝ) : ℂ) *
      Cumulants.mixedCumulant ρ (fun (l : Fin Λ.k) (U : InfiniteLattice.RefinedGaugeField Λ.stepParams.side K) =>
        InfiniteLattice.faceEnergy U (r l).1) := by
  unfold MomentPoint.stateUrsell InfiniteLattice.ursellFunctionOfFamily
  have e : (fun (j : Fin Λ.k) (U : InfiniteLattice.RefinedGaugeField Λ.stepParams.side K) =>
        InfiniteLattice.cutoffSmearedEnergyRe (S.rescaledTestFunction j) U) =
      fun (l : Fin Λ.k) (U : InfiniteLattice.RefinedGaugeField Λ.stepParams.side K) =>
        ∑ p : ↥W, S.rescaledTestFunction l p.1.center * InfiniteLattice.faceEnergy U p.1 := by
    funext l U
    rw [smearedEnergy_eq_sum _ W (fun p hp => hW l p hp) U, ← Finset.sum_coe_sort]
  rw [e]
  exact (hML _ ρ).1 ↥W (fun (p : ↥W) (U : InfiniteLattice.RefinedGaugeField Λ.stepParams.side K) =>
      InfiniteLattice.faceEnergy U p.1) Λ.k (fun l p => S.rescaledTestFunction l p.1.center)
    (fun p => faceEnergy_isBoundedRealRV hA ha p.1) h1
private theorem ae_forall_momentPoints (hML : Cumulants.MomentCumulantRelations.Holds)
    (hA : GibbsAtFixedSpacing.FaceEnergyIndependentOfBasepointAndOrientation) (h1 : 1 ≤ Λ.k) {K : ℕ} {β Cf : ℝ}
    (ha : 0 < InfiniteLattice.refinedSpacing Λ.stepParams.side K)
    (ν : Measure (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K))
    (κ : Kernel (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K)
      (InfiniteLattice.RefinedGaugeField Λ.stepParams.side K)) [IsMarkovKernel κ]
    (hpt : ∀ S : MomentPoint Λ, S.data.windowLevel = K → S.β = β → ∀ᵐ U ∂ν,
      ‖(S.scaleCoupling : ℂ) ^ Λ.k * S.stateUrsell (κ U) - (S.latticeCycleSumAt S.data.scaleLevel : ℂ)‖ ≤
        Cf * S.scaleCoupling ^ (-(1 / 10) : ℝ)) :
    ∀ᵐ U ∂ν, ∀ S : MomentPoint Λ, S.data.windowLevel = K → S.β = β →
      ‖(S.scaleCoupling : ℂ) ^ Λ.k * S.stateUrsell (κ U) - (S.latticeCycleSumAt S.data.scaleLevel : ℂ)‖ ≤
        Cf * S.scaleCoupling ^ (-(1 / 10) : ℝ) := by
  have hclass : ∀ cz : ℕ × (Fin 4 → ℤ), ∀ᵐ U ∂ν, ∀ S : {S : MomentPoint Λ // S.data.windowLevel = K ∧ S.β = β ∧
      S.data.scaleLevel = cz.1 ∧ S.data.center = fun a => (cz.2 a : ℝ) / (Λ.stepParams.side : ℝ) ^ K},
      ‖(S.1.scaleCoupling : ℂ) ^ Λ.k * S.1.stateUrsell (κ U) - (S.1.latticeCycleSumAt S.1.data.scaleLevel : ℂ)‖ ≤
        Cf * S.1.scaleCoupling ^ (-(1 / 10) : ℝ) := by
    rintro ⟨s, z⟩
    obtain ⟨W, hWne, hW⟩ :=
      exists_finset_support_window Λ K s (fun a => (z a : ℝ) / (Λ.stepParams.side : ℝ) ^ K) rfl ha
    have : Nonempty ↥W := hWne.to_subtype
    obtain ⟨x, hx⟩ : ∃ x, x = (TorusLumps.couplingFlow Λ.stepParams β s).1 := ⟨_, rfl⟩
    let arr : {S : MomentPoint Λ // S.data.windowLevel = K ∧ S.β = β ∧ S.data.scaleLevel = s ∧
          S.data.center = fun a => (z a : ℝ) / (Λ.stepParams.side : ℝ) ^ K} →
        (Fin Λ.k → ↥W → ℝ) × (Fin Λ.k → IntPlaquette → ℝ) :=
      fun S => (fun l p => S.1.rescaledTestFunction l p.1.center,
        fun i P => scaledWeight Λ.stepParams.side s (S.1.data.fn i) P)
    let G : InfiniteLattice.RefinedGaugeField Λ.stepParams.side K →
        (Fin Λ.k → ↥W → ℝ) × (Fin Λ.k → IntPlaquette → ℝ) → ℝ := fun U v =>
      ‖(x : ℂ) ^ Λ.k * (∑ r : Fin Λ.k → ↥W, ((∏ l, v.1 l (r l) : ℝ) : ℂ) *
        Cumulants.mixedCumulant (κ U) (fun (l : Fin Λ.k) (U' : InfiniteLattice.RefinedGaugeField Λ.stepParams.side K) =>
          InfiniteLattice.faceEnergy U' (r l).1)) - ((cycleSumOfValues Λ s v.2 : ℝ) : ℂ)‖
    have hG : ∀ U, Continuous (G U) := by
      intro U
      simp only [G, cycleSumOfValues]
      fun_prop
    have heq : ∀ (S : {S : MomentPoint Λ // S.data.windowLevel = K ∧ S.β = β ∧ S.data.scaleLevel = s ∧
          S.data.center = fun a => (z a : ℝ) / (Λ.stepParams.side : ℝ) ^ K}) U,
        G U (arr S) = ‖(S.1.scaleCoupling : ℂ) ^ Λ.k * S.1.stateUrsell (κ U) -
          (S.1.latticeCycleSumAt S.1.data.scaleLevel : ℂ)‖ := by
      rintro ⟨S, hK, hβ, hs, hz⟩ U
      have hxs : S.scaleCoupling = x := by
        rw [hx]
        unfold MomentPoint.scaleCoupling MomentPoint.coupling
        rw [hβ, hs]
      have hγ : S.latticeCycleSumAt S.data.scaleLevel =
          cycleSumOfValues Λ s (fun i P => scaledWeight Λ.stepParams.side s (S.data.fn i) P) := by
        unfold MomentPoint.latticeCycleSumAt latticeCycleSum cycleSumOfValues
        rw [hs]
      have hcum := stateUrsell_eq_sum_mixedCumulant hML hA S ha W (fun i p hp => hW S hK hs hz i p hp) h1 (κ U)
      simp only [G, arr]
      rw [hxs, hcum, hγ]
    have hdense := ae_forall_of_continuous_le ν arr G (Cf * x ^ (-(1 / 10) : ℝ)) hG (fun S => by
      filter_upwards [hpt S.1 S.2.1 S.2.2.1] with U hU
      rw [heq]
      have hxs : S.1.scaleCoupling = x := by
        rw [hx]
        unfold MomentPoint.scaleCoupling MomentPoint.coupling
        rw [S.2.2.1, S.2.2.2.1]
      rw [← hxs]
      exact hU)
    filter_upwards [hdense] with U hU S
    have h := hU S
    rw [heq] at h
    have hxs : S.1.scaleCoupling = x := by
      rw [hx]
      unfold MomentPoint.scaleCoupling MomentPoint.coupling
      rw [S.2.2.1, S.2.2.2.1]
    rw [hxs]
    rw [hxs] at h
    exact h
  filter_upwards [ae_all_iff.mpr hclass] with U hU S hK hβ
  obtain ⟨z, hz⟩ := S.supAdmissible.center_mem_lattice
  exact hU (S.data.scaleLevel, z) ⟨S, hK, hβ, rfl, funext fun a => by rw [hz a, hK]⟩
end SingleNullSet
theorem periodicComponentCumulantStatement_holds (hM : componentMomentStatement)
    (hF : levelCumulantApproxStatement) (hV : freeCumulantValueStatement) (hP : scaleCouplingPosStatement)
    (hG : levelChainCanonicalGaussianStatement) (hJ : Cumulants.MixedCumulantMomentExpansion)
    (hML : Cumulants.MomentCumulantRelations.Holds)
    (hA : GibbsAtFixedSpacing.FaceEnergyIndependentOfBasepointAndOrientation) :
    periodicComponentCumulantStatement := by
  unfold levelCumulantApproxStatement ForAllPoints at hF
  unfold freeCumulantValueStatement ForAllPoints at hV
  unfold scaleCouplingPosStatement at hP
  have h := forAllHullParameters_and hM (forAllHullParameters_and (forAllHullParameters_of_forAllParameters hF)
    (forAllHullParameters_and (forAllHullParameters_of_forAllParameters hV) (forAllHullParameters_of_forAllParameters hP)))
  refine forAllHullParameters_mono h fun Λ hk2 hk8 hapos hh => ?_
  obtain ⟨⟨C, X₀, hX₀, hMom⟩, ⟨A, c₁, X₁, hc₁, hy₁, hFr⟩, ⟨D, c₃, X₂, hc₃, hy₃, hVa⟩, hpos⟩ := hh
  have hLpos : (0 : ℝ) < Λ.stepParams.side := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
  have hGa : ∀ (s n : ℕ) [NeZero n], ∃ μ : Measure (LevelChain Λ.stepParams.side s n),
      IsCanonicalGaussian (levelEnergy Λ.stepParams.coupling s n) μ :=
    fun s n _ => hG Λ.stepParams.side Λ.stepParams.coupling hapos s n
  refine ⟨pointwiseConstant Λ.k C X₀ (A 0) c₁ (D 0) X₂, ?_⟩
  intro K β hβ hKp ν hν p hp κ hκ
  have : IsMarkovKernel κ := hκ.isMarkovKernel
  have hsp : 0 < InfiniteLattice.refinedSpacing Λ.stepParams.side K := by
    unfold InfiniteLattice.refinedSpacing PeriodicLattice.meshSize
    positivity
  refine ae_forall_momentPoints hML hA (by omega) hsp ν κ fun S hK hβS => ?_
  obtain ⟨c, hc⟩ := hMom K β hβ hKp ν hν p hp κ hκ S hK hβS
  filter_upwards [hc] with U hU
  have hm := stateUrsell_eq_moebiusSum hJ hML S (κ U) hk2 (smearedEnergy_isBoundedRealRV hA S hK hsp) c
  have hb := abs_scaled_moebiusSum_sub_cycleSum_le (Λ := Λ) hk8 hGa hX₀ hc₁ (A := A 0) (D := D 0) (X₂ := X₂)
    (fun S d hd μ hμ => (hFr S d hd μ hμ).1)
    (fun S μ hμ => ⟨(hVa S μ hμ).2.2.1, (hVa S μ hμ).2.2.2.1, (hVa S μ hμ).2.2.2.2.1⟩)
    S (hpos S) (κ U) c hU.1 hU.2
  rw [hm, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hb
end YangMills.Construction.MomentLaw
end
