import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdStepAtMirrorFrames.DensityNearTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionDensityBoundsForm
import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormAboveTheFrame
import YangMills.Construction.ColdStepAtMirrorFrames.FlatFormOfTheExpansionDensity
import YangMills.Construction.ColdStepAtMirrorFrames.MeansOfTheStepAreDensities
import YangMills.Construction.SummableBoundsOfTheFlow.FlatFormOfTheMeanProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
private lemma bondDeriv_smul {j k : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (m : Fin k → ℝ) (hm : ∀ l, m l ≠ 0) :
    bondDeriv G W c (fun l => m l • X l) = (∏ l, m l) * bondDeriv G W c X := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.bondDeriv_smul <;> assumption
private def supNorm (h : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (h i).natAbs
private lemma natAbs_le_supNorm (h : Fin 4 → ℤ) (i : Fin 4) : (h i).natAbs ≤ supNorm h := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
private lemma siteSupDist_le_bondSpan {G : BlockFrame} {k : ℕ} (y : G.Cell) (c : Fin k → G.Cell × Fin 4)
    (l : Fin k) : siteSupDist y (c l).1 ≤ bondSpan y c := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.siteSupDist_le_bondSpan <;> assumption
private lemma supNorm_le_bondSpan (L t n : ℕ) (b b' : (Fin 4 → ℤ) × Fin 4) (hb : 2 * supNorm b.1 < n)
    (hb' : 2 * supNorm b'.1 < n) :
    max (supNorm b.1) (supNorm b'.1) ≤
      bondSpan (0 : (cubicTorusFrame L t n).Cell) (bondsAt 0 ![b, b']) := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.supNormInt_le_bondSpan <;> assumption
private lemma uniformField_isSmallCurvature {j : ℕ} {s : ℝ} (hs : 0 < s) : IsSmallCurvature s (uniformField F j) := by apply _root_.YangMills.SharedProofs.p8038 <;> assumption
private def bondWeight (c : ℝ) (b : (Fin 4 → ℤ) × Fin 4) : ℝ :=
  Real.exp (-(c * supNorm b.1)) * (1 + (supNorm b.1 : ℝ)) ^ 2
private lemma bondWeight_nonneg (c : ℝ) (b : (Fin 4 → ℤ) × Fin 4) : 0 ≤ bondWeight c b := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.bondWeight_nonneg <;> assumption
private lemma summable_prod_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun h : Fin 4 → ℤ => ∏ i, r ^ (h i).natAbs := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.summable_prod_pow_natAbs <;> assumption
private lemma summable_siteWeight {c : ℝ} (hc : 0 < c) :
    Summable fun h : Fin 4 → ℤ => Real.exp (-(c * supNorm h)) * (1 + (supNorm h : ℝ)) ^ 2 := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.summable_exp_mul_sq <;> assumption
private lemma summable_bondWeight {c : ℝ} (hc : 0 < c) : Summable (bondWeight c) := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.summable_bondWeight <;> assumption
private lemma eq_of_forall_near {v w : ℝ} (H : ∀ ε : ℝ, 0 < ε → ∃ c g : ℝ, 0 < g ∧
    |c - g / 2 * v| ≤ ε * g ∧ |c - g / 2 * w| ≤ ε * g) : v = w := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.eq_of_forall_approx <;> assumption
private def planeCoefficient (μ ν : Fin 4) (b : (Fin 4 → ℤ) × Fin 4) : ℝ :=
  (if b.2 = μ then -((b.1 ν : ℤ) : ℝ) else 0) + 1 / 2
private lemma planeCoefficient_ne_zero (μ ν : Fin 4) (b : (Fin 4 → ℤ) × Fin 4) : planeCoefficient μ ν b ≠ 0 := by
  unfold planeCoefficient
  split_ifs
  · intro h
    have h2 : ((2 * b.1 ν : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by
      push_cast
      linarith
    have h3 : 2 * b.1 ν = 1 := by exact_mod_cast h2
    omega
  · norm_num
private lemma abs_planeCoefficient_le (μ ν : Fin 4) (b : (Fin 4 → ℤ) × Fin 4) :
    |planeCoefficient μ ν b| ≤ 1 + (supNorm b.1 : ℝ) := by
  have h1 : |((b.1 ν : ℤ) : ℝ)| ≤ supNorm b.1 := by
    have h2 : |((b.1 ν : ℤ) : ℝ)| = ((b.1 ν).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2]
    exact_mod_cast natAbs_le_supNorm b.1 ν
  unfold planeCoefficient
  split_ifs
  · have := abs_le.1 h1
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]
  · rw [zero_add, abs_of_pos (by norm_num)]
    linarith
private lemma isLinearPotential_planeCoefficient (X : imaginaryQuaternions) {μ ν : Fin 4} (hμν : μ < ν) :
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
private lemma exp_le_div_torusDecayFactor (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hT : T.IsOrdered) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, Real.exp (-(T.κ / 2 ^ 6 * n)) ≤ K / torusDecayFactor T.L T.decayRate n := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.exp_le_div_torusDecayFactor <;> assumption
private lemma EventuallyInParameters.of_rescale {P Q : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters → Prop} (M : ℝ → ℝ) (hM : ∀ κ, 0 < M κ)
    (hPQ : ∀ T, T.IsOrdered → P { T with CE := T.CE / M T.κ } → Q T) (H : EventuallyInParameters P) :
    EventuallyInParameters Q := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.EventuallyInParameters.of_rescale <;> assumption
private def CouplingAboveThreshold (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ x : ℝ, T.coupling ≤ x → 1 ≤ x ∧ Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) ≤ x ^ (-(1 / 2 : ℝ))
private lemma eventually_couplingAboveThreshold (hC : CouplingThreshold) : EventuallyInParameters CouplingAboveThreshold := by
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
private lemma flatLimit_bound_at (hE : secondOrderDensityStatement) (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters)
    (hT : T.IsOrdered) (hm : MeansAreLocalDensitiesAt T) (hb : StepDensityDerivBoundsAt T)
    (hf : FlatLimitAboveFrame T) (hn : StepDensityNearFrame T) (hy : CouplingAboveThreshold T)
    (t : ℕ) (x : ℝ) (hx : T.coupling ≤ x) (f : LocalFamily) (hrow : T.IsRegularExpansion t f) :
    ∃ q : BondBilinearForm,
      (∀ b b' X X', Filter.Tendsto (fun n => secondDerivAtUniform (T.expansionFamily x f) T.L t n b b' X X')
        Filter.atTop (𝓝 (q b b' X X'))) ∧
      ∀ (X : imaginaryQuaternions) (μ ν : Fin 4) (B : (Fin 4 → ℤ) × Fin 4 → imaginaryQuaternions),
        ‖X‖ = 1 → μ < ν → IsLinearPotential (constantPlaneCurvature X μ ν) B →
        ∃ v : ℝ, HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
          q e.1 e.2 (B e.1) (B e.2)) v ∧
          |v| ≤ T.CE * (1 + (∑' b, bondWeight (T.κ / 2 ^ 7) b) ^ 2) * x ^ (-(1 / 2 : ℝ)) := by
  have hσ := hT.σ_pos
  have hκ := hT.κ_pos
  have hδ : 0 < T.decayRate := by
    unfold StepParameters.decayRate
    positivity
  have hE1 := hT.one_le_E
  have hE3 : 0 ≤ T.energyRatio := by
    unfold StepParameters.energyRatio
    exact div_nonneg (by linarith) hT.η₃_pos.le
  obtain ⟨hdec, hloc⟩ := hb t x f hx hrow
  obtain ⟨K, hK0, hK⟩ := exp_le_div_torusDecayFactor T hT
  have hG : ∀ u : ℝ, 0 < torusDecayFactor T.L T.decayRate u := fun u =>
    mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = T.E + T.energyRatio + |T.CE * x ^ (-(1 / 2 : ℝ))| * K + 1 := ⟨_, rfl⟩
  have hAK : 0 ≤ |T.CE * x ^ (-(1 / 2 : ℝ))| * K := mul_nonneg (abs_nonneg _) hK0
  have hC : 0 < C := by
    rw [hCdef]
    linarith
  have hdecay : DerivDecay T.L t T.n₀ (9 / 8 * T.σ) (T.expansionFamily x f)
      (fun _ n => C / torusDecayFactor T.L T.decayRate n) := by
    intro F hF Y V k c X hV h1 h3 hX
    have h := hdec F hF Y V k c X (fun p hp => lt_of_lt_of_le (hV p hp) (by linarith)) h1 h3 hX
    beta_reduce at h
    have hGn := hG (bondSpan Y c)
    have he := hK (bondSpan Y c)
    refine le_trans h ?_
    have h2 : 2⁻¹ ^ 6 * (if k = 3 then T.energyRatio else T.E) ≤ T.E + T.energyRatio := by
      split_ifs
      · norm_num
        linarith
      · norm_num
        linarith
    have h4 : T.CE * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c : ℕ))) ≤
        |T.CE * x ^ (-(1 / 2 : ℝ))| * (K / torusDecayFactor T.L T.decayRate (bondSpan Y c)) :=
      mul_le_mul (le_abs_self _) he (Real.exp_pos _).le (abs_nonneg _)
    calc 2⁻¹ ^ 6 * (if k = 3 then T.energyRatio else T.E) / torusDecayFactor T.L T.decayRate (bondSpan Y c) +
          T.CE * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 * (bondSpan Y c : ℕ)))
        ≤ (T.E + T.energyRatio) / torusDecayFactor T.L T.decayRate (bondSpan Y c) +
          |T.CE * x ^ (-(1 / 2 : ℝ))| * (K / torusDecayFactor T.L T.decayRate (bondSpan Y c)) :=
          add_le_add (div_le_div_of_nonneg_right h2 hGn.le) h4
      _ = (T.E + T.energyRatio + |T.CE * x ^ (-(1 / 2 : ℝ))| * K) / torusDecayFactor T.L T.decayRate (bondSpan Y c) := by
          ring
      _ ≤ C / torusDecayFactor T.L T.decayRate (bondSpan Y c) :=
          div_le_div_of_nonneg_right (by rw [hCdef]; linarith) hGn.le
  have hcomp : IsLocalOnTori T.L t T.n₀ (9 / 8 * T.σ) (centredFamily (T.expansionFamily x f))
      (fun r => C / torusDecayFactor T.L T.decayRate r) := by
    intro F F' hF hF' Y Y' V V' r k h X hV hV' hA hk hb' hX
    have h' := hloc F F' hF hF' Y Y' V V' r k h X hV hV' hA hk hb' hX
    beta_reduce at h'
    refine le_trans h' (div_le_div_of_nonneg_right ?_ (hG _).le)
    have h16 : (2 : ℝ)⁻¹ ^ 4 * T.E ≤ T.E := by
      norm_num
      linarith
    rw [hCdef]
    linarith
  obtain ⟨q, hq, hv⟩ := hE T.L t T.n₀ (9 / 8 * T.σ) T.decayRate C (T.expansionFamily x f) hT.odd_L (by positivity)
    hδ hC (hm t x hx f hrow).2 hdecay hcomp
  obtain ⟨hx1, hfl⟩ := hy x hx
  refine ⟨q, hq, fun X μ ν B hX hμν hB => ?_⟩
  have hB₁ := isLinearPotential_planeCoefficient X hμν
  obtain ⟨v, hvs, hvl⟩ := hv X μ ν 1 B hX hμν hB
  obtain ⟨v₁, hvs₁, hvl₁⟩ := hv X μ ν 1 _ hX hμν hB₁
  have hvv : v = v₁ := eq_of_forall_near fun ε hε => by
    obtain ⟨n₁, h₁⟩ := hvl ε hε
    obtain ⟨n₂, h₂⟩ := hvl₁ ε hε
    have hn0 : (0 : ℝ) < ((n₁ + n₂ + 1 : ℕ) : ℝ) := by positivity
    exact ⟨_, (2 * Real.pi * ((1 : ℕ) : ℝ) / ((n₁ + n₂ + 1 : ℕ) : ℝ) ^ 2) ^ 2, by positivity,
      h₁ (n₁ + n₂ + 1) (by omega) 0, h₂ (n₁ + n₂ + 1) (by omega) 0⟩
  refine ⟨v, hvs, ?_⟩
  rw [hvv]
  obtain ⟨qF, hqF, hqF'⟩ := (hf t x f hx hrow).2
  obtain ⟨vF, hvF, hvFb⟩ := hqF' X μ ν _ hX hμν hB₁
  have hCE : 0 ≤ T.CE := by
    by_contra hneg
    have h1 : T.CE * Real.exp (-(T.chainParams.δ₂ / 4 * frameRadius x)) < 0 :=
      mul_neg_of_neg_of_pos (not_le.1 hneg) (Real.exp_pos _)
    linarith [abs_nonneg vF]
  have hxr : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hK₀ : 0 ≤ T.CE * x ^ (-(1 / 2 : ℝ)) := mul_nonneg hCE hxr
  have hvF' : |vF| ≤ T.CE * x ^ (-(1 / 2 : ℝ)) :=
    hvFb.trans (mul_le_mul_of_nonneg_left hfl hCE)
  have hc : 0 < T.κ / 2 ^ 7 := by positivity
  have hterm : ∀ e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4),
      |q e.1 e.2 (planeCoefficient μ ν e.1 • X) (planeCoefficient μ ν e.2 • X) -
        qF e.1 e.2 (planeCoefficient μ ν e.1 • X) (planeCoefficient μ ν e.2 • X)| ≤
      T.CE * x ^ (-(1 / 2 : ℝ)) * (bondWeight (T.κ / 2 ^ 7) e.1 * bondWeight (T.κ / 2 ^ 7) e.2) := by
    intro e
    have tends := ((hq e.1 e.2 (planeCoefficient μ ν e.1 • X) (planeCoefficient μ ν e.2 • X)).sub
      (hqF e.1 e.2 (planeCoefficient μ ν e.1 • X) (planeCoefficient μ ν e.2 • X))).abs
    refine le_of_tendsto tends ?_
    filter_upwards [Filter.eventually_ge_atTop (T.n₀ + 2 * supNorm e.1.1 + 2 * supNorm e.2.1 + 1)]
      with n hnn
    have hd := (hn t x f hx hrow (cubicTorusFrame T.L t n) ⟨rfl, rfl, n, fun _ => rfl, by omega⟩ 0
      (uniformField _ _) (uniformField_isSmallCurvature (by positivity))).2 2
      (bondsAt 0 ![e.1, e.2]) ![X, X] (by norm_num) le_rfl (by
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
    have hspan := supNorm_le_bondSpan T.L t n e.1 e.2 (by omega) (by omega)
    show |bondDeriv (T.expansionFamily x f (cubicTorusFrame T.L t n) 0) (uniformField _ _) (bondsAt 0 ![e.1, e.2])
        ![planeCoefficient μ ν e.1 • X, planeCoefficient μ ν e.2 • X] -
      bondDeriv (expansionAtFrameFamily T false x f (cubicTorusFrame T.L t n) 0) (uniformField _ _)
        (bondsAt 0 ![e.1, e.2]) ![planeCoefficient μ ν e.1 • X, planeCoefficient μ ν e.2 • X]| ≤ _
    rw [hsc, hsc, ← mul_sub, abs_mul, abs_mul]
    have hd' : |bondDeriv (T.expansionFamily x f (cubicTorusFrame T.L t n) 0) (uniformField _ _)
          (bondsAt 0 ![e.1, e.2]) ![X, X] -
        bondDeriv (expansionAtFrameFamily T false x f (cubicTorusFrame T.L t n) 0) (uniformField _ _)
          (bondsAt 0 ![e.1, e.2]) ![X, X]| ≤
        T.CE * x ^ (-(1 / 2 : ℝ)) * Real.exp (-(T.κ / 2 ^ 6 *
          (bondSpan (0 : (cubicTorusFrame T.L t n).Cell) (bondsAt 0 ![e.1, e.2]) : ℕ))) := hd
    obtain ⟨s₁, hs₁⟩ : ∃ s : ℝ, s = (supNorm e.1.1 : ℝ) := ⟨_, rfl⟩
    obtain ⟨s₂, hs₂⟩ : ∃ s : ℝ, s = (supNorm e.2.1 : ℝ) := ⟨_, rfl⟩
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
        ≤ (1 + s₁) ^ 2 * (1 + s₂) ^ 2 * (T.CE * x ^ (-(1 / 2 : ℝ)) * (e₁ * e₂)) :=
          mul_le_mul (mul_le_mul (hl1.trans hsq1) (hl2.trans hsq2) (abs_nonneg _) (by positivity))
            hd2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hA := summable_bondWeight hc
  have hprod : HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
      bondWeight (T.κ / 2 ^ 7) e.1 * bondWeight (T.κ / 2 ^ 7) e.2)
      ((∑' b, bondWeight (T.κ / 2 ^ 7) b) * ∑' b, bondWeight (T.κ / 2 ^ 7) b) :=
    HasSum.mul hA.hasSum hA.hasSum
      (Summable.mul_of_nonneg hA hA (bondWeight_nonneg _) (bondWeight_nonneg _))
  have hle := HasSum.norm_le_of_bounded (hvs₁.sub hvF) (hprod.mul_left (T.CE * x ^ (-(1 / 2 : ℝ))))
    (fun e => by simpa [Real.norm_eq_abs] using hterm e)
  rw [Real.norm_eq_abs] at hle
  have h3 : |v₁| ≤ |v₁ - vF| + |vF| := by
    have := abs_add_le (v₁ - vF) vF
    simpa using this
  calc |v₁| ≤ T.CE * x ^ (-(1 / 2 : ℝ)) * ((∑' b, bondWeight (T.κ / 2 ^ 7) b) *
        ∑' b, bondWeight (T.κ / 2 ^ 7) b) + T.CE * x ^ (-(1 / 2 : ℝ)) := by linarith
    _ = _ := by ring
theorem flatLimitOfStepDensity_of_bounds (hE : secondOrderDensityStatement)
    (hM : meansAreLocalDensities) (hB : stepDensityDerivBoundsStatement)
    (hF : flatLimitAboveFrameStatement) (hN : stepDensityNearFrameStatement)
    (hC : CouplingThreshold) (hJ : EventuallyInParametersCombines) :
    flatLimitOfStepDensity := by
  have H := hJ.1 _ _ hM (hJ.1 _ _ hB (hJ.1 _ _ hF (hJ.1 _ _ hN (eventually_couplingAboveThreshold hC))))
  refine EventuallyInParameters.of_rescale (fun κ => 1 + (∑' b, bondWeight (κ / 2 ^ 7) b) ^ 2)
    (fun κ => by positivity) (fun T hT h => ?_) H
  obtain ⟨hm, hb, hf, hn, hy⟩ := h
  have hT' : StepParameters.IsOrdered
      { T with CE := T.CE / (1 + (∑' b, bondWeight (T.κ / 2 ^ 7) b) ^ 2) } :=
    ⟨hT.one_le_a, hT.odd_L, hT.chain_admissible, hT.κ_pos, hT.η₃_pos, hT.η₃_le_one, hT.σ_pos, hT.cutoff,
      hT.one_le_E⟩
  intro t x hx f hrow
  obtain ⟨q, hq, hv⟩ := flatLimit_bound_at hE _ hT' hm hb hf hn hy t x hx f hrow
  refine ⟨q, hq, fun X μ ν B h1 h2 h3 => ?_⟩
  obtain ⟨v, hs, hb'⟩ := hv X μ ν B h1 h2 h3
  refine ⟨v, hs, le_trans hb' (le_of_eq ?_)⟩
  have hne : 1 + (∑' b, bondWeight (T.κ / 2 ^ 7) b) ^ 2 ≠ 0 := by positivity
  show T.CE / (1 + (∑' b, bondWeight (T.κ / 2 ^ 7) b) ^ 2) *
    (1 + (∑' b, bondWeight (T.κ / 2 ^ 7) b) ^ 2) * x ^ (-(1 / 2 : ℝ)) = T.CE * x ^ (-(1 / 2 : ℝ))
  rw [div_mul_cancel₀ _ hne]
end ColdStepAtMirrorFrames
end YangMills.Construction
end
