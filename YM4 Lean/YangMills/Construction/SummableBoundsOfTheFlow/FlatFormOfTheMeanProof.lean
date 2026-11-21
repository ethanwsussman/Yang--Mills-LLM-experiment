import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.BoundsOfTheExpansionAboveTheFrameProof
import YangMills.Construction.ColdStepAtMirrorFrames.CouplingFloorOfTheFrames
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import YangMills.Construction.SummableBoundsOfTheFlow.FlatFormOfTheMean
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOnOneTorus
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOnTwoTori
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceGoesUpALevelProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames BlockMeans Interpolation FamilyNorms Estimates
namespace SummableBounds
namespace MeanHessian
variable {F : BlockFrame}
theorem bondSpread_smul {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (m τ : Fin k → ℝ) :
    bondSpread c (fun l => m l • X l) τ = bondSpread c X (fun l => m l * τ l) := by apply _root_.YangMills.SharedProofs.p12456 <;> assumption
theorem bondDeriv_smul {j k : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (m : Fin k → ℝ)
    (hm : ∀ l, m l ≠ 0) :
    bondDeriv G W c (fun l => m l • X l) = (∏ l, m l) * bondDeriv G W c X := by
  let D₁ : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun l => m l • ContinuousLinearMap.proj l
  let D₂ : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun l => (m l)⁻¹ • ContinuousLinearMap.proj l
  let D : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ) := ContinuousLinearEquiv.equivOfInverse D₁ D₂
    (fun τ => by funext l; simp [D₁, D₂, hm l]) (fun τ => by funext l; simp [D₁, D₂, hm l])
  have hD : ∀ τ l, D τ l = m l * τ l := fun τ l => by simp [D, D₁]
  let φ : (Fin k → ℝ) → ℝ := fun τ => G (leftTranslate (bondSpread c X τ) W)
  have hcomp : (fun τ : Fin k → ℝ =>
      G (leftTranslate (bondSpread c (fun l => m l • X l) τ) W)) = φ ∘ D := by
    funext τ
    have : (fun l => m l * τ l) = D τ := by
      funext l
      rw [hD]
    simp only [Function.comp, φ, bondSpread_smul, this]
  have hsingle : (fun l => D (Pi.single l (1 : ℝ))) =
      fun l => m l • (Pi.single l (1 : ℝ) : Fin k → ℝ) := by
    funext l l'
    rw [hD]
    by_cases h : l' = l
    · subst h
      simp
    · simp [h]
  have hit : iteratedFDeriv ℝ k (φ ∘ D) 0 =
      (iteratedFDeriv ℝ k φ 0).compContinuousLinearMap
        fun _ => (D : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) := by
    have h := D.iteratedFDerivWithin_comp_right φ (s := Set.univ) uniqueDiffOn_univ (x := 0)
      (Set.mem_univ _) k
    rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ, map_zero] at h
    exact h
  unfold bondDeriv
  rw [hcomp, hit]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe]
  rw [hsingle, ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
theorem natAbs_valMinAbs_neg (N : ℕ) (z : ℤ) (h : 2 * z.natAbs < N) :
    ((0 - (z : ZMod N)).valMinAbs).natAbs = z.natAbs := by
  have : NeZero N := ⟨by omega⟩
  have e : (0 - (z : ZMod N)) = ((-z : ℤ) : ZMod N) := by
    push_cast
    ring
  have hs : (((-z : ℤ) : ZMod N)).valMinAbs = -z :=
    (ZMod.valMinAbs_spec _ _).2 ⟨rfl, by
      constructor <;> omega⟩
  rw [e, hs, Int.natAbs_neg]
def supNormInt (h : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (h i).natAbs
theorem natAbs_le_supNormInt (h : Fin 4 → ℤ) (i : Fin 4) : (h i).natAbs ≤ supNormInt h := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem supNormInt_le_siteSupDist (G : BlockFrame) (z : Fin 4 → ℤ)
    (hz : ∀ i, 2 * supNormInt z < G.period G.top i) :
    supNormInt z ≤ siteSupDist (0 : G.Cell) ((0 : G.Cell) + siteOfCoords G.top z) := by
  refine Finset.sup_le fun i _ => ?_
  have h1 := natAbs_valMinAbs_neg (G.period G.top i) (z i) (by
    have := natAbs_le_supNormInt z i
    have := hz i
    omega)
  rw [← h1]
  have h2 := Finset.le_sup (f := fun i => (((0 : G.Cell) i -
    (((0 : G.Cell) + siteOfCoords G.top z : G.Cell)) i).valMinAbs).natAbs) (Finset.mem_univ i)
  have e : (((0 : G.Cell) + siteOfCoords G.top z : G.Cell)) i = (z i : ZMod (G.period G.top i)) := by
    simp [siteOfCoords]
  simp only [e, Pi.zero_apply] at h2
  exact h2
theorem siteSupDist_le_bondSpan {G : BlockFrame} {k : ℕ} (y : G.Cell) (c : Fin k → G.Cell × Fin 4)
    (l : Fin k) : siteSupDist y (c l).1 ≤ bondSpan y c :=
  le_max_of_le_left (Finset.le_sup (f := fun l => siteSupDist y (c l).1) (Finset.mem_univ l))
theorem supNormInt_le_bondSpan (L t n : ℕ) (b b' : (Fin 4 → ℤ) × Fin 4)
    (hb : 2 * supNormInt b.1 < n) (hb' : 2 * supNormInt b'.1 < n) :
    max (supNormInt b.1) (supNormInt b'.1) ≤
      bondSpan (0 : (cubicTorusFrame L t n).Cell) (bondsAt 0 ![b, b']) := by
  have hN : ∀ i, (cubicTorusFrame L t n).period (cubicTorusFrame L t n).top i = n := fun i => by
    simp [BlockFrame.period, cubicTorusFrame]
  have e0 : (bondsAt (0 : (cubicTorusFrame L t n).Cell) ![b, b'] 0).1 =
      (0 : (cubicTorusFrame L t n).Cell) + siteOfCoords (cubicTorusFrame L t n).top b.1 := rfl
  have e1 : (bondsAt (0 : (cubicTorusFrame L t n).Cell) ![b, b'] 1).1 =
      (0 : (cubicTorusFrame L t n).Cell) + siteOfCoords (cubicTorusFrame L t n).top b'.1 := rfl
  have h0 := siteSupDist_le_bondSpan (0 : (cubicTorusFrame L t n).Cell) (bondsAt 0 ![b, b']) 0
  have h1 := siteSupDist_le_bondSpan (0 : (cubicTorusFrame L t n).Cell) (bondsAt 0 ![b, b']) 1
  rw [e0] at h0
  rw [e1] at h1
  exact max_le ((supNormInt_le_siteSupDist _ b.1 fun i => by rw [hN]; exact hb).trans h0)
    ((supNormInt_le_siteSupDist _ b'.1 fun i => by rw [hN]; exact hb').trans h1)
theorem uniformField_isSmallCurvature {j : ℕ} {s : ℝ} (hs : 0 < s) :
    IsSmallCurvature s (uniformField F j) := by apply _root_.YangMills.SharedProofs.p8038 <;> assumption
def bondWeight (c : ℝ) (b : (Fin 4 → ℤ) × Fin 4) : ℝ :=
  Real.exp (-(c * supNormInt b.1)) * (1 + (supNormInt b.1 : ℝ)) ^ 2
theorem bondWeight_nonneg (c : ℝ) (b : (Fin 4 → ℤ) × Fin 4) : 0 ≤ bondWeight c b := by
  unfold bondWeight
  positivity
theorem summable_prod_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun h : Fin 4 → ℤ => ∏ i, r ^ (h i).natAbs := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.summable_prod_pow_natAbs <;> assumption
theorem summable_exp_mul_sq {c : ℝ} (hc : 0 < c) :
    Summable fun h : Fin 4 → ℤ =>
      Real.exp (-(c * supNormInt h)) * (1 + (supNormInt h : ℝ)) ^ 2 := by
  set a : ℝ := c / 4 with ha
  have ha0 : 0 < a := by positivity
  set K : ℝ := 1 / a + 1 with hK
  have hK0 : 0 < K := by positivity
  set r : ℝ := Real.exp (-(c / 8)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith [show 0 < c / 8 by positivity]
  refine Summable.of_nonneg_of_le (fun h => by positivity) (fun h => ?_)
    ((summable_prod_pow_natAbs hr0 hr1).mul_left (K ^ 2))
  set s : ℝ := (supNormInt h : ℝ) with hs
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have h1 : 1 + s ≤ K * Real.exp (a * s) := by
    have h2 : 1 + a * s ≤ Real.exp (a * s) := by
      have := Real.add_one_le_exp (a * s)
      linarith
    have h3 : 1 + s ≤ K * (1 + a * s) := by
      rw [hK]
      have : (1 / a + 1) * (1 + a * s) = 1 / a + 1 + s + a * s := by
        field_simp
        ring
      rw [this]
      have : 0 < 1 / a := by positivity
      nlinarith [mul_nonneg ha0.le hs0]
    exact h3.trans (mul_le_mul_of_nonneg_left h2 hK0.le)
  have h2 : (1 + s) ^ 2 ≤ K ^ 2 * Real.exp (c / 2 * s) := by
    have h3 : (1 + s) ^ 2 ≤ (K * Real.exp (a * s)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h4 : (K * Real.exp (a * s)) ^ 2 = K ^ 2 * Real.exp (c / 2 * s) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      rw [ha]
      push_cast
      ring
    linarith
  have h3 : (∑ i, ((h i).natAbs : ℝ)) ≤ 4 * s := by
    have : ∀ i ∈ (Finset.univ : Finset (Fin 4)), ((h i).natAbs : ℝ) ≤ s := fun i _ => by
      rw [hs]
      exact_mod_cast natAbs_le_supNormInt h i
    simpa using Finset.sum_le_sum this
  have h4 : ∏ i, r ^ (h i).natAbs = Real.exp (-(c / 8) * ∑ i, ((h i).natAbs : ℝ)) := by
    rw [hr, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h4]
  calc Real.exp (-(c * s)) * (1 + s) ^ 2
      ≤ Real.exp (-(c * s)) * (K ^ 2 * Real.exp (c / 2 * s)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = K ^ 2 * Real.exp (-(c / 2 * s)) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
    _ ≤ K ^ 2 * Real.exp (-(c / 8) * ∑ i, ((h i).natAbs : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        nlinarith
theorem summable_bondWeight {c : ℝ} (hc : 0 < c) : Summable (bondWeight c) := by
  have h := Summable.mul_of_nonneg (summable_exp_mul_sq hc)
    ((hasSum_fintype fun _ : Fin 4 => (1 : ℝ)).summable)
    (fun _ => by positivity) (fun _ => zero_le_one)
  have hw : bondWeight c = fun x : (Fin 4 → ℤ) × Fin 4 =>
      Real.exp (-(c * supNormInt x.1)) * (1 + (supNormInt x.1 : ℝ)) ^ 2 * 1 := by
    funext b
    simp [bondWeight]
  rw [hw]
  exact h
theorem pow_mul_exp_bounded (N : ℕ) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 ≤ y → max 1 ((y * a) ^ N) * Real.exp (-(c * y)) ≤ K := by
  refine ⟨max 1 (a ^ N * (N.factorial : ℝ) / c ^ N), le_max_of_le_left zero_le_one, fun y hy => ?_⟩
  rw [max_mul_of_nonneg _ _ (Real.exp_pos _).le]
  refine max_le_max ?_ ?_
  · rw [one_mul]
    exact Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hc.le hy])
  · have h := Real.pow_div_factorial_le_exp (x := c * y) (by positivity) N
    have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
    have hcN : 0 < c ^ N := pow_pos hc N
    rw [div_le_iff₀ hf] at h
    rw [le_div_iff₀ hcN, Real.exp_neg]
    have he := Real.exp_pos (c * y)
    have h2 : (y * a) ^ N * (Real.exp (c * y))⁻¹ * c ^ N =
        a ^ N * ((c * y) ^ N * (Real.exp (c * y))⁻¹) := by
      rw [mul_pow, mul_pow]
      ring
    rw [h2]
    have h3 : (c * y) ^ N * (Real.exp (c * y))⁻¹ ≤ N.factorial := by
      rw [← div_eq_mul_inv, div_le_iff₀ he]
      linarith
    calc a ^ N * ((c * y) ^ N * (Real.exp (c * y))⁻¹)
        ≤ a ^ N * (N.factorial : ℝ) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := rfl
theorem eq_of_forall_approx {v w : ℝ} (H : ∀ ε : ℝ, 0 < ε → ∃ c g : ℝ, 0 < g ∧
    |c - g / 2 * v| ≤ ε * g ∧ |c - g / 2 * w| ≤ ε * g) : v = w := by
  by_contra hne
  have hd : 0 < |v - w| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨c, g, hg, h1, h2⟩ := H (|v - w| / 8) (by positivity)
  have h3 : |g / 2 * v - g / 2 * w| ≤ |c - g / 2 * v| + |c - g / 2 * w| := by
    have := abs_sub_le (g / 2 * v) c (g / 2 * w)
    rwa [abs_sub_comm (g / 2 * v) c] at this
  have h4 : |g / 2 * v - g / 2 * w| = g / 2 * |v - w| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
  nlinarith [mul_pos hg hd]
def planeCoefficient (μ ν : Fin 4) (b : (Fin 4 → ℤ) × Fin 4) : ℝ :=
  (if b.2 = μ then -((b.1 ν : ℤ) : ℝ) else 0) + 1 / 2
theorem planeCoefficient_ne_zero (μ ν : Fin 4) (b : (Fin 4 → ℤ) × Fin 4) :
    planeCoefficient μ ν b ≠ 0 := by
  unfold planeCoefficient
  split_ifs
  · intro h
    have h2 : ((2 * b.1 ν : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by
      push_cast
      linarith
    have h3 : 2 * b.1 ν = 1 := by exact_mod_cast h2
    omega
  · norm_num
theorem abs_planeCoefficient_le (μ ν : Fin 4) (b : (Fin 4 → ℤ) × Fin 4) :
    |planeCoefficient μ ν b| ≤ 1 + (supNormInt b.1 : ℝ) := by
  have h1 : |((b.1 ν : ℤ) : ℝ)| ≤ supNormInt b.1 := by
    have h2 : |((b.1 ν : ℤ) : ℝ)| = ((b.1 ν).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2]
    exact_mod_cast natAbs_le_supNormInt b.1 ν
  unfold planeCoefficient
  split_ifs
  · have := abs_le.1 h1
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]
  · rw [zero_add, abs_of_pos (by norm_num)]
    linarith
theorem isLinearPotential_planeCoefficient (X : imaginaryQuaternions) {μ ν : Fin 4} (hμν : μ < ν) :
    IsLinearPotential (constantPlaneCurvature X μ ν) fun b => planeCoefficient μ ν b • X := by
  have hne : μ ≠ ν := hμν.ne
  refine ⟨fun α β => if α = μ ∧ β = ν then -X else 0, fun _ => (1 / 2 : ℝ) • X, fun x α => ?_,
    fun α β => ?_⟩
  · by_cases hα : α = μ
    · subst hα
      have hs : (∑ β, ((x β : ℤ) : ℝ) • (if α = α ∧ β = ν then -X else 0)) =
          ((x ν : ℤ) : ℝ) • (-X) := by
        rw [Finset.sum_eq_single ν]
        · simp
        · intro β _ hβ
          simp [hβ]
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [hs]
      simp [planeCoefficient, add_smul]
    · simp [planeCoefficient, hα]
  · unfold constantPlaneCurvature
    by_cases h1 : α = μ ∧ β = ν
    · obtain ⟨rfl, rfl⟩ := h1
      simp [hne.symm]
    · by_cases h2 : α = ν ∧ β = μ
      · obtain ⟨rfl, rfl⟩ := h2
        simp [hne, hne.symm]
      · have h3 : ¬ (β = μ ∧ α = ν) := fun h => h2 ⟨h.2, h.1⟩
        simp [h1, h2, h3]
theorem exp_le_div_torusDecayFactor (T : StepParameters) (hT : T.IsOrdered) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      Real.exp (-(T.κ / 2 ^ 6 * n)) ≤ K / torusDecayFactor T.L T.decayRate n := by
  have hκ := hT.κ_pos
  have hc : 0 < T.κ / 2 ^ 6 - T.decayRate := by
    have e : T.κ / 2 ^ 6 - T.decayRate = T.κ * (15 / 1024) := by
      unfold StepParameters.decayRate
      ring
    rw [e]
    positivity
  obtain ⟨K, hK0, hK⟩ :=
    pow_mul_exp_bounded 16000 (a := ((T.L : ℝ) ^ (1 / 640 : ℝ))⁻¹) (by positivity) hc
  refine ⟨K, hK0, fun n => ?_⟩
  have hG : 0 < torusDecayFactor T.L T.decayRate n :=
    mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
  rw [le_div_iff₀ hG]
  have h := hK n (Nat.cast_nonneg n)
  have e2 : Real.exp (-((T.κ / 2 ^ 6 - T.decayRate) * n)) =
      Real.exp (-(T.κ / 2 ^ 6 * n)) * Real.exp (T.decayRate * n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e2, mul_left_comm] at h
  unfold torusDecayFactor
  rw [div_eq_mul_inv]
  exact h
theorem EventuallyInParameters.of_rescale {P Q : StepParameters → Prop} (M : ℝ → ℝ)
    (hM : ∀ κ, 0 < M κ)
    (hPQ : ∀ T, T.IsOrdered → P { T with CE := T.CE / M T.κ } → Q T)
    (H : EventuallyInParameters P) : EventuallyInParameters Q := by
  intro a ha
  obtain ⟨L₀, h⟩ := H a ha
  refine ⟨L₀, fun L hL hLe c hc => ?_⟩
  obtain ⟨Ct₀, h⟩ := h L hL hLe c hc
  refine ⟨Ct₀, fun Ct hCt => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h Ct hCt
  refine ⟨κ₀, hκ₀, fun κ hκ hκ' => ?_⟩
  obtain ⟨η₀, hη₀, h⟩ := h κ hκ hκ'
  refine ⟨η₀, hη₀, fun η₃ h1 h2 h3 => ?_⟩
  obtain ⟨N₀, h⟩ := h η₃ h1 h2 h3
  refine ⟨N₀, fun nss hn => ?_⟩
  obtain ⟨σ₀, hσ₀, h⟩ := h nss hn
  refine ⟨σ₀, hσ₀, fun σ hσ hσ' p hp => ?_⟩
  obtain ⟨C₀, h⟩ := h σ hσ hσ' p hp
  refine ⟨C₀, fun Cs hCs E hE => ?_⟩
  obtain ⟨m₀, h⟩ := h Cs hCs E hE
  refine ⟨m₀, fun n₀ hn₀ => ?_⟩
  obtain ⟨C₁, h⟩ := h n₀ hn₀
  refine ⟨M κ * C₁, fun CE hCE => ?_⟩
  obtain ⟨y₀, h⟩ := h (CE / M κ) (by
    rw [le_div_iff₀ (hM κ), mul_comm]
    exact hCE)
  exact ⟨y₀, fun y₁ hy₁ => hPQ _ ⟨ha, hL, hc, hκ, h1, h2, hσ, hp, hE⟩ (h y₁ hy₁)⟩
def CouplingThresholdAt (T : StepParameters) : Prop :=
  ∀ x : ℝ, T.coupling ≤ x →
    1 ≤ x ∧ Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) ≤ x ^ (-(1 / 2 : ℝ))
theorem eventually_couplingThresholdAt (hC : CouplingThreshold) :
    EventuallyInParameters CouplingThresholdAt := by
  intro a ha
  refine ⟨0, fun L _ _ c hc => ?_⟩
  have hδ₂ : 0 < c.δ₂ := hc.classical.1.2.2.2.1
  refine ⟨0, fun Ct _ => ⟨c.δ₂ / 2 ^ 14, by positivity, fun κ hκ hκ' => ⟨1, one_pos,
    fun η₃ _ _ _ => ⟨0, fun nss _ => ⟨1, one_pos, fun σ hσ _ p _ => ⟨0, fun Cs _ E _ =>
      ⟨0, fun n₀ _ => ⟨0, fun CE _ => ?_⟩⟩⟩⟩⟩⟩⟩⟩
  obtain ⟨y₀, hy⟩ := hC 1 1 c.δ₂ κ σ 0 hδ₂ hκ hκ' hσ
  refine ⟨max y₀ 1, fun y₁ hy₁ x hx => ?_⟩
  have hxy : y₁ ≤ x := hx
  refine ⟨le_trans (le_trans (le_max_right _ _) hy₁) hxy, ?_⟩
  have h := (hy x (le_trans (le_trans (le_max_left _ _) hy₁) hxy)).2.2.2.2.2
  rw [one_mul] at h
  exact h
theorem meanHessian_at (hE : secondOrderDensityStatement) (T : StepParameters)
    (hT : T.IsOrdered) (hone : SingleTorusMeanBoundsAt T) (htwo : TwoTorusMeanBoundsAt T)
    (hf : FlatLimitOfFamilyAt T) (hy : CouplingThresholdAt T)
    (t : ℕ) (x : ℝ) (φ h : LocalFamily) (ε : ℝ) (star : Bool) (hx : T.coupling ≤ x) (hε : 0 < ε)
    (hφ : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E (T.E / T.η₃) φ)
    (hh : IsRegularFamily T.L t T.n₀ T.σ T.decayRate ε (ε / T.η₃) h) :
    ∃ q : BondBilinearForm,
      (∀ b b' X X', Filter.Tendsto (fun n => secondDerivAtUniform
        (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p φ h)
        T.L t n b b' X X') Filter.atTop (𝓝 (q b b' X X'))) ∧
      ∀ (X : imaginaryQuaternions) (μ ν : Fin 4) (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
        ‖X‖ = 1 → μ < ν → IsLinearPotential (constantPlaneCurvature X μ ν) B →
        ∃ v : ℝ, HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
          q e.1 e.2 (B e.1) (B e.2)) v ∧
          |v| ≤ T.CE * ε * (1 + (∑' b, bondWeight (T.κ / 2 ^ 7) b) ^ 2) * x ^ (-(1 / 2 : ℝ)) := by
  have hσ := hT.σ_pos
  have hκ := hT.κ_pos
  have hη := hT.η₃_pos
  have hδ : 0 < T.decayRate := by
    unfold StepParameters.decayRate
    positivity
  have one := hone t x φ h ε star hx hε hφ hh
  have two := htwo t x φ h ε star hx hε hφ hh
  obtain ⟨K, hK0, hK⟩ := exp_le_div_torusDecayFactor T hT
  have hG : ∀ u : ℝ, 0 < torusDecayFactor T.L T.decayRate u := fun u =>
    mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = ε + ε / T.η₃ + |T.CE * ε * x ^ (-(1 / 2 : ℝ))| * K + 1 :=
    ⟨_, rfl⟩
  have hAK : 0 ≤ |T.CE * ε * x ^ (-(1 / 2 : ℝ))| * K := mul_nonneg (abs_nonneg _) hK0
  have hε3 : 0 ≤ ε / T.η₃ := by positivity
  have hC : 0 < C := by
    rw [hCdef]
    linarith
  have hcold : ∀ {F : BlockFrame} {V : F.GaugeField F.top}, IsSmallCurvature (9 / 8 * T.σ) V →
      IsSmallCurvature (5 / 4 * T.σ) V := fun hV p hp =>
    lt_of_lt_of_le (hV p hp) (by linarith)
  have hdens : IsLocalDensity T.L t T.n₀ (9 / 8 * T.σ)
      (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p φ h) :=
    ⟨fun F hF Y V hV => one.density.smooth F hF Y V (hcold hV),
      fun F hF Y V γ hV => one.density.gauge_invariant F hF Y V γ (hcold hV),
      fun F hF Y u V hV => one.density.translation_invariant F hF Y u V (hcold hV)⟩
  have hdecay : DerivDecay T.L t T.n₀ (9 / 8 * T.σ)
      (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p φ h)
      (fun _ n => C / torusDecayFactor T.L T.decayRate n) := by
    intro F hF Y V k c X hV h1 h3 hX
    have h' := one.decay F hF Y V k c X (hcold hV) h1 h3 hX
    beta_reduce at h'
    have hGn := hG (bondSpan Y c)
    have he := hK (bondSpan Y c)
    refine le_trans h' ?_
    have h2 : 2⁻¹ ^ 6 * (if k = 3 then ε / T.η₃ else ε) ≤ ε + ε / T.η₃ := by
      split_ifs
      · norm_num
        linarith
      · norm_num
        linarith
    have h4 : T.CE * ε * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c : ℕ))) ≤
        |T.CE * ε * x ^ (-(1 / 2 : ℝ))| * (K / torusDecayFactor T.L T.decayRate (bondSpan Y c)) :=
      mul_le_mul (le_abs_self _) he (Real.exp_pos _).le (abs_nonneg _)
    calc 2⁻¹ ^ 6 * (if k = 3 then ε / T.η₃ else ε) / torusDecayFactor T.L T.decayRate (bondSpan Y c) +
          T.CE * ε * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c : ℕ)))
        ≤ (ε + ε / T.η₃) / torusDecayFactor T.L T.decayRate (bondSpan Y c) +
          |T.CE * ε * x ^ (-(1 / 2 : ℝ))| *
            (K / torusDecayFactor T.L T.decayRate (bondSpan Y c)) :=
          add_le_add (div_le_div_of_nonneg_right h2 hGn.le) h4
      _ = (ε + ε / T.η₃ + |T.CE * ε * x ^ (-(1 / 2 : ℝ))| * K) /
            torusDecayFactor T.L T.decayRate (bondSpan Y c) := by
          ring
      _ ≤ C / torusDecayFactor T.L T.decayRate (bondSpan Y c) :=
          div_le_div_of_nonneg_right (by rw [hCdef]; linarith) hGn.le
  have hcomp : IsLocalOnTori T.L t T.n₀ (9 / 8 * T.σ)
      (centredFamily
        (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p φ h))
      (fun r => C / torusDecayFactor T.L T.decayRate r) := by
    intro F F' hF hF' Y Y' V V' r k hs X hV hV' hA hk hb' hX
    have h' := two.locality F F' hF hF' Y Y' V V' r k hs X hV hV' hA hk hb' hX
    beta_reduce at h'
    refine le_trans h' (div_le_div_of_nonneg_right ?_ (hG _).le)
    have h16 : (2 : ℝ)⁻¹ ^ 4 * ε ≤ ε := by
      norm_num
      linarith
    rw [hCdef]
    linarith
  obtain ⟨q, hq, hv⟩ := hE T.L t T.n₀ (9 / 8 * T.σ) T.decayRate C
    (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p φ h) hT.odd_L
    (by positivity) hδ hC hdens hdecay hcomp
  obtain ⟨hx1, hfl⟩ := hy x hx
  refine ⟨q, hq, fun X μ ν B hX hμν hB => ?_⟩
  have hB₁ := isLinearPotential_planeCoefficient X hμν
  obtain ⟨v, hvs, hvl⟩ := hv X μ ν 1 B hX hμν hB
  obtain ⟨v₁, hvs₁, hvl₁⟩ := hv X μ ν 1 _ hX hμν hB₁
  have hvv : v = v₁ := eq_of_forall_approx fun ε hε => by
    obtain ⟨n₁, h₁⟩ := hvl ε hε
    obtain ⟨n₂, h₂⟩ := hvl₁ ε hε
    have hn0 : (0 : ℝ) < ((n₁ + n₂ + 1 : ℕ) : ℝ) := by positivity
    exact ⟨_, (2 * Real.pi * ((1 : ℕ) : ℝ) / ((n₁ + n₂ + 1 : ℕ) : ℝ) ^ 2) ^ 2, by positivity,
      h₁ (n₁ + n₂ + 1) (by omega) 0, h₂ (n₁ + n₂ + 1) (by omega) 0⟩
  refine ⟨v, hvs, ?_⟩
  rw [hvv]
  have hxr : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hCE : 0 ≤ T.CE := by
    obtain ⟨qF, _, hqF'⟩ := (hf t x ε h hx hε hh).2
    obtain ⟨vF, _, hvFb⟩ := hqF' X μ ν _ hX hμν hB₁
    by_contra hneg
    have h1 : T.CE * ε * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (not_le.1 hneg) hε) (Real.exp_pos _)
    linarith [abs_nonneg vF]
  have hform : ∃ qF : BondBilinearForm, (∀ b b' X X', Filter.Tendsto (fun n => secondDerivAtUniform
      (expansionAtFrameFamily T star x h) T.L t n b b' X X') Filter.atTop (𝓝 (qF b b' X X'))) ∧
      ∃ vF : ℝ, HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        qF e.1 e.2 (planeCoefficient μ ν e.1 • X) (planeCoefficient μ ν e.2 • X)) vF ∧
        |vF| ≤ T.CE * ε * x ^ (-(1 / 2 : ℝ)) := by
    cases star with
    | true =>
      obtain ⟨qF, hqF, hqF'⟩ := (hf t x ε h hx hε hh).1
      obtain ⟨vF, hvF, hvFb⟩ := hqF' X μ ν _ hX hμν hB₁
      exact ⟨qF, hqF, vF, hvF, hvFb.trans (by positivity)⟩
    | false =>
      obtain ⟨qF, hqF, hqF'⟩ := (hf t x ε h hx hε hh).2
      obtain ⟨vF, hvF, hvFb⟩ := hqF' X μ ν _ hX hμν hB₁
      exact ⟨qF, hqF, vF, hvF, hvFb.trans (mul_le_mul_of_nonneg_left hfl (by positivity))⟩
  obtain ⟨qF, hqF, vF, hvF, hvF'⟩ := hform
  have hK₀ : 0 ≤ T.CE * ε * x ^ (-(1 / 2 : ℝ)) := by positivity
  have hc : 0 < T.κ / 2 ^ 7 := by positivity
  have hterm : ∀ e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4),
      |q e.1 e.2 (planeCoefficient μ ν e.1 • X) (planeCoefficient μ ν e.2 • X) -
        qF e.1 e.2 (planeCoefficient μ ν e.1 • X) (planeCoefficient μ ν e.2 • X)| ≤
      T.CE * ε * x ^ (-(1 / 2 : ℝ)) *
        (bondWeight (T.κ / 2 ^ 7) e.1 * bondWeight (T.κ / 2 ^ 7) e.2) := by
    intro e
    have tends := ((hq e.1 e.2 (planeCoefficient μ ν e.1 • X) (planeCoefficient μ ν e.2 • X)).sub
      (hqF e.1 e.2 (planeCoefficient μ ν e.1 • X) (planeCoefficient μ ν e.2 • X))).abs
    refine le_of_tendsto tends ?_
    filter_upwards [Filter.eventually_ge_atTop (T.n₀ + 2 * supNormInt e.1.1 + 2 * supNormInt e.2.1 + 1)]
      with n hnn
    have hd := one.near_block (cubicTorusFrame T.L t n) ⟨rfl, rfl, n, fun _ => rfl, by omega⟩ 0
      (uniformField _ _) 2 (bondsAt 0 ![e.1, e.2]) ![X, X]
      (uniformField_isSmallCurvature (by positivity)) le_rfl (by
        intro l
        fin_cases l <;> simpa using hX)
    have hsc : ∀ g : (cubicTorusFrame T.L t n).GaugeField (cubicTorusFrame T.L t n).top → ℝ,
        bondDeriv g (uniformField _ _) (bondsAt 0 ![e.1, e.2])
          ![planeCoefficient μ ν e.1 • X, planeCoefficient μ ν e.2 • X] =
        planeCoefficient μ ν e.1 * planeCoefficient μ ν e.2 *
          bondDeriv g (uniformField _ _) (bondsAt 0 ![e.1, e.2]) ![X, X] := by
      intro g
      have e3 : ![planeCoefficient μ ν e.1 • X, planeCoefficient μ ν e.2 • X] =
          fun l => (![planeCoefficient μ ν e.1, planeCoefficient μ ν e.2] l) • (![X, X] l) := by
        funext l
        fin_cases l <;> rfl
      rw [e3, bondDeriv_smul g _ _ _ _ (by
        intro l
        fin_cases l
        · exact planeCoefficient_ne_zero μ ν e.1
        · exact planeCoefficient_ne_zero μ ν e.2)]
      simp [Fin.prod_univ_two]
    have hspan := supNormInt_le_bondSpan T.L t n e.1 e.2 (by omega) (by omega)
    show |bondDeriv (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p φ h
        (cubicTorusFrame T.L t n) 0) (uniformField _ _) (bondsAt 0 ![e.1, e.2])
        ![planeCoefficient μ ν e.1 • X, planeCoefficient μ ν e.2 • X] -
      bondDeriv (expansionAtFrameFamily T star x h (cubicTorusFrame T.L t n) 0) (uniformField _ _)
        (bondsAt 0 ![e.1, e.2]) ![planeCoefficient μ ν e.1 • X, planeCoefficient μ ν e.2 • X]| ≤ _
    rw [hsc, hsc, ← mul_sub, abs_mul, abs_mul]
    have hd' : |bondDeriv (conditionalExpansionMean star T.a T.chainParams.ρA (T.σ / 64) x (frameRadius x) T.p φ h
          (cubicTorusFrame T.L t n) 0) (uniformField _ _)
          (bondsAt 0 ![e.1, e.2]) ![X, X] -
        bondDeriv (expansionAtFrameFamily T star x h (cubicTorusFrame T.L t n) 0) (uniformField _ _)
          (bondsAt 0 ![e.1, e.2]) ![X, X]| ≤
        T.CE * ε * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 *
          (bondSpan (0 : (cubicTorusFrame T.L t n).Cell) (bondsAt 0 ![e.1, e.2]) : ℕ))) := hd
    obtain ⟨s₁, hs₁⟩ : ∃ s : ℝ, s = (supNormInt e.1.1 : ℝ) := ⟨_, rfl⟩
    obtain ⟨s₂, hs₂⟩ : ∃ s : ℝ, s = (supNormInt e.2.1 : ℝ) := ⟨_, rfl⟩
    obtain ⟨sp, hsp⟩ : ∃ s : ℝ, s =
      ((bondSpan (0 : (cubicTorusFrame T.L t n).Cell) (bondsAt 0 ![e.1, e.2]) : ℕ) : ℝ) := ⟨_, rfl⟩
    have h1 : s₁ ≤ sp := by
      rw [hs₁, hsp]
      exact_mod_cast (le_max_left _ _).trans hspan
    have h2 : s₂ ≤ sp := by
      rw [hs₂, hsp]
      exact_mod_cast (le_max_right _ _).trans hspan
    have hs₁0 : 0 ≤ s₁ := by
      rw [hs₁]
      exact Nat.cast_nonneg _
    have hs₂0 : 0 ≤ s₂ := by
      rw [hs₂]
      exact Nat.cast_nonneg _
    have hexp : Real.exp (-(T.κ / 2 ^ 6 * sp)) ≤
        Real.exp (-(T.κ / 2 ^ 7 * s₁)) * Real.exp (-(T.κ / 2 ^ 7 * s₂)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h3 : T.κ / 2 ^ 7 * (s₁ + s₂) ≤ T.κ / 2 ^ 7 * (2 * sp) :=
        mul_le_mul_of_nonneg_left (by linarith) hc.le
      have e4 : T.κ / 2 ^ 7 * (2 * sp) = T.κ / 2 ^ 6 * sp := by ring
      have e5 : T.κ / 2 ^ 7 * (s₁ + s₂) = T.κ / 2 ^ 7 * s₁ + T.κ / 2 ^ 7 * s₂ := by ring
      linarith
    have hl1 := abs_planeCoefficient_le μ ν e.1
    have hl2 := abs_planeCoefficient_le μ ν e.2
    rw [← hs₁] at hl1
    rw [← hs₂] at hl2
    rw [← hsp] at hd'
    have hd2 := hd'.trans (mul_le_mul_of_nonneg_left hexp hK₀)
    unfold bondWeight
    rw [← hs₁, ← hs₂]
    obtain ⟨e₁, he₁⟩ : ∃ u : ℝ, u = Real.exp (-(T.κ / 2 ^ 7 * s₁)) := ⟨_, rfl⟩
    obtain ⟨e₂, he₂⟩ : ∃ u : ℝ, u = Real.exp (-(T.κ / 2 ^ 7 * s₂)) := ⟨_, rfl⟩
    rw [← he₁, ← he₂] at hd2 ⊢
    have he₁0 : 0 ≤ e₁ := by
      rw [he₁]
      exact (Real.exp_pos _).le
    have he₂0 : 0 ≤ e₂ := by
      rw [he₂]
      exact (Real.exp_pos _).le
    have ha1 : 1 ≤ 1 + s₁ := by linarith
    have ha2 : 1 ≤ 1 + s₂ := by linarith
    have hsq1 : 1 + s₁ ≤ (1 + s₁) ^ 2 := by nlinarith
    have hsq2 : 1 + s₂ ≤ (1 + s₂) ^ 2 := by nlinarith
    calc |planeCoefficient μ ν e.1| * |planeCoefficient μ ν e.2| * _
        ≤ (1 + s₁) ^ 2 * (1 + s₂) ^ 2 * (T.CE * ε * x ^ (-(1 / 2 : ℝ)) * (e₁ * e₂)) :=
          mul_le_mul (mul_le_mul (hl1.trans hsq1) (hl2.trans hsq2) (abs_nonneg _) (by positivity))
            hd2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hA := summable_bondWeight hc
  have hprod : HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
      bondWeight (T.κ / 2 ^ 7) e.1 * bondWeight (T.κ / 2 ^ 7) e.2)
      ((∑' b, bondWeight (T.κ / 2 ^ 7) b) * ∑' b, bondWeight (T.κ / 2 ^ 7) b) :=
    HasSum.mul hA.hasSum hA.hasSum
      (Summable.mul_of_nonneg hA hA (bondWeight_nonneg _) (bondWeight_nonneg _))
  have hle := HasSum.norm_le_of_bounded (hvs₁.sub hvF)
    (hprod.mul_left (T.CE * ε * x ^ (-(1 / 2 : ℝ))))
    (fun e => by simpa [Real.norm_eq_abs] using hterm e)
  rw [Real.norm_eq_abs] at hle
  have h3 : |v₁| ≤ |v₁ - vF| + |vF| := by
    have := abs_add_le (v₁ - vF) vF
    simpa using this
  calc |v₁| ≤ T.CE * ε * x ^ (-(1 / 2 : ℝ)) * ((∑' b, bondWeight (T.κ / 2 ^ 7) b) *
        ∑' b, bondWeight (T.κ / 2 ^ 7) b) + T.CE * ε * x ^ (-(1 / 2 : ℝ)) := by linarith
    _ = _ := by ring
end MeanHessian
open MeanHessian in
theorem meanHessianAtUniform_holds (hE : secondOrderDensityStatement)
    (hone : singleTorusMeanStatement) (htwo : twoTorusMeanStatement)
    (hF : flatLimitOfFamilyStatement) (hC : CouplingThreshold)
    (hJ : EventuallyInParametersCombines) : meanHessianAtUniformStatement := by
  have H := hJ.1 _ _ hone (hJ.1 _ _ htwo (hJ.1 _ _ hF (eventually_couplingThresholdAt hC)))
  refine EventuallyInParameters.of_rescale (fun κ => 1 + (∑' b, bondWeight (κ / 2 ^ 7) b) ^ 2)
    (fun κ => by positivity) (fun T hT h => ?_) H
  obtain ⟨h1, h2, hf, hy⟩ := h
  have hT' : StepParameters.IsOrdered
      { T with CE := T.CE / (1 + (∑' b, bondWeight (T.κ / 2 ^ 7) b) ^ 2) } :=
    ⟨hT.one_le_a, hT.odd_L, hT.chain_admissible, hT.κ_pos, hT.η₃_pos, hT.η₃_le_one, hT.σ_pos,
      hT.cutoff, hT.one_le_E⟩
  intro t x φ h ε star hx hε hφ hh
  obtain ⟨q, hq, hv⟩ := meanHessian_at hE _ hT' h1 h2 hf hy t x φ h ε star hx hε hφ hh
  refine ⟨q, hq, fun X μ ν B a1 a2 a3 => ?_⟩
  obtain ⟨v, hs, hb'⟩ := hv X μ ν B a1 a2 a3
  refine ⟨v, hs, le_trans hb' (le_of_eq ?_)⟩
  have hne : 1 + (∑' b, bondWeight (T.κ / 2 ^ 7) b) ^ 2 ≠ 0 := by positivity
  show T.CE / (1 + (∑' b, bondWeight (T.κ / 2 ^ 7) b) ^ 2) * ε *
    (1 + (∑' b, bondWeight (T.κ / 2 ^ 7) b) ^ 2) * x ^ (-(1 / 2 : ℝ)) =
      T.CE * ε * x ^ (-(1 / 2 : ℝ))
  field_simp
end SummableBounds
end YangMills.Construction
end
