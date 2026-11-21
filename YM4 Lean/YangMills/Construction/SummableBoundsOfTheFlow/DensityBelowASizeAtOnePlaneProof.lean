import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.SummableBoundsOfTheFlow.FlatFormOfTheMeanProof
import YangMills.Construction.SummableBoundsOfTheFlow.FromTheMirrorFramesToTheLeastFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages hiding flatTopField
open YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.FamilyNorms
namespace PlaneDensityBound
variable {F : BlockFrame}
theorem bondDeriv_smul {j k : ℕ} (G : F.GaugeField j → ℝ) (W : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (m : Fin k → ℝ)
    (hm : ∀ l, m l ≠ 0) :
    bondDeriv G W c (fun l => m l • X l) = (∏ l, m l) * bondDeriv G W c X := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.bondDeriv_smul <;> assumption
def intSupNorm (h : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (h i).natAbs
theorem natAbs_le_intSupNorm (h : Fin 4 → ℤ) (i : Fin 4) : (h i).natAbs ≤ intSupNorm h := by apply _root_.YangMills.Construction.LatticePaths.natAbs_le_supNorm <;> assumption
theorem siteSupDist_le_bondSpan {G : BlockFrame} {k : ℕ} (y : G.Cell) (c : Fin k → G.Cell × Fin 4)
    (l : Fin k) : siteSupDist y (c l).1 ≤ bondSpan y c := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.siteSupDist_le_bondSpan <;> assumption
theorem max_intSupNorm_le_bondSpan (L t n : ℕ) (b b' : (Fin 4 → ℤ) × Fin 4)
    (hb : 2 * intSupNorm b.1 < n) (hb' : 2 * intSupNorm b'.1 < n) :
    max (intSupNorm b.1) (intSupNorm b'.1) ≤
      bondSpan (0 : (cubicTorusFrame L t n).Cell) (bondsAt 0 ![b, b']) := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.supNormInt_le_bondSpan <;> assumption
theorem uniformField_isSmallCurvature {j : ℕ} {s : ℝ} (hs : 0 < s) :
    IsSmallCurvature s (uniformField F j) := by apply _root_.YangMills.SharedProofs.p8038 <;> assumption
def bondWeight (c : ℝ) (b : (Fin 4 → ℤ) × Fin 4) : ℝ :=
  Real.exp (-(c * intSupNorm b.1)) * (1 + (intSupNorm b.1 : ℝ)) ^ 2
theorem bondWeight_nonneg (c : ℝ) (b : (Fin 4 → ℤ) × Fin 4) : 0 ≤ bondWeight c b := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.bondWeight_nonneg <;> assumption
theorem summable_prod_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun h : Fin 4 → ℤ => ∏ i, r ^ (h i).natAbs := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.summable_prod_pow_natAbs <;> assumption
theorem summable_bondWeight {c : ℝ} (hc : 0 < c) : Summable (bondWeight c) := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.summable_bondWeight <;> assumption
theorem eq_of_forall_approx {v w : ℝ} (H : ∀ ε : ℝ, 0 < ε → ∃ c g : ℝ, 0 < g ∧
    |c - g / 2 * v| ≤ ε * g ∧ |c - g / 2 * w| ≤ ε * g) : v = w := by apply _root_.YangMills.Construction.SummableBounds.MeanHessian.eq_of_forall_approx <;> assumption
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
    |planeCoefficient μ ν b| ≤ 1 + (intSupNorm b.1 : ℝ) := by
  have h1 : |((b.1 ν : ℤ) : ℝ)| ≤ intSupNorm b.1 := by
    have h2 : |((b.1 ν : ℤ) : ℝ)| = ((b.1 ν).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2]
    exact_mod_cast natAbs_le_intSupNorm b.1 ν
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
theorem torusDecayFactor_le_exp {L : ℕ} (hL : 1 ≤ L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℕ, torusDecayFactor L δ r ≤ C * Real.exp (2 * δ * r) := by apply _root_.YangMills.Construction.FrameInterpolationProof.torusDecayFactor_le <;> assumption
end PlaneDensityBound
open PlaneDensityBound in
theorem vanishingDensityPlaneBound_of_secondOrderDensity
    (hE : secondOrderDensityStatement) :
    vanishingDensityPlaneBoundStatement := by
  intro κ hκ
  have hc : 0 < κ / 2 := by positivity
  have hA := summable_bondWeight hc
  refine ⟨(∑' b, bondWeight (κ / 2) b) * (∑' b, bondWeight (κ / 2) b) + 1, ?_, ?_⟩
  · have : 0 ≤ ∑' b, bondWeight (κ / 2) b := tsum_nonneg (bondWeight_nonneg _)
    positivity
  intro L t n₀ δ σ A g hL hδ hδκ hσ hA0 hden hflat hdec hloc
  obtain ⟨C₁, hC₁, hw⟩ := torusDecayFactor_le_exp hL.pos hδ
  have hG : ∀ u : ℝ, 0 < torusDecayFactor L δ u := fun u =>
    mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
  have hexp : ∀ n : ℕ, Real.exp (-(κ * n)) ≤ C₁ / torusDecayFactor L δ n := by
    intro n
    rw [le_div_iff₀ (hG n)]
    calc Real.exp (-(κ * n)) * torusDecayFactor L δ n
        ≤ Real.exp (-(κ * n)) * (C₁ * Real.exp (2 * δ * n)) :=
          mul_le_mul_of_nonneg_left (hw n) (Real.exp_pos _).le
      _ = C₁ * Real.exp (-(κ * n) + 2 * δ * n) := by
          rw [Real.exp_add]
          ring
      _ ≤ C₁ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          refine Real.exp_le_one_iff.mpr ?_
          have := mul_le_mul_of_nonneg_right hδκ (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
          linarith
      _ = C₁ := mul_one _
  have hC : 0 < A * C₁ := by positivity
  have hdecay : DerivDecay L t n₀ σ g (fun _ n => A * C₁ / torusDecayFactor L δ n) := by
    intro F hF Y V k c X hV h1 h3 hX
    refine (hdec F hF Y V k c X hV h1 h3 hX).trans ?_
    have := mul_le_mul_of_nonneg_left (hexp (bondSpan Y c)) hA0.le
    simpa [mul_div_assoc] using this
  have hcent : ∀ (F : BlockFrame) (Y : F.Cell), IsCubicTopTorus L t n₀ F →
      centredFamily g F Y = g F Y := by
    intro F Y hF
    funext V
    have h0 : g F Y (uniformField F F.top) = 0 := hflat F Y hF
    simp [centredFamily, h0]
  have hcomp : IsLocalOnTori L t n₀ σ (centredFamily g)
      (fun r => A * C₁ / torusDecayFactor L δ r) := by
    intro F F' hF hF' Y Y' V V' r k h X hV hV' hag hk hb hX
    rw [hcent F Y hF, hcent F' Y' hF']
    refine (hloc F F' hF hF' Y Y' V V' r k h X hV hV' hag hk hb hX).trans ?_
    refine div_le_div_of_nonneg_right ?_ (hG _).le
    nlinarith
  obtain ⟨q, hq, hv⟩ := hE L t n₀ σ δ (A * C₁) g hL hσ hδ hC hden hdecay hcomp
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
  have hterm : ∀ e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4),
      |q e.1 e.2 (planeCoefficient μ ν e.1 • X) (planeCoefficient μ ν e.2 • X)| ≤
      A * (bondWeight (κ / 2) e.1 * bondWeight (κ / 2) e.2) := by
    intro e
    have tends := (hq e.1 e.2 (planeCoefficient μ ν e.1 • X) (planeCoefficient μ ν e.2 • X)).abs
    refine le_of_tendsto tends ?_
    filter_upwards [Filter.eventually_ge_atTop (n₀ + 2 * intSupNorm e.1.1 + 2 * intSupNorm e.2.1 + 1)]
      with n hnn
    have hd := hdec (cubicTorusFrame L t n) ⟨rfl, rfl, n, fun _ => rfl, by omega⟩ 0
      (uniformField _ _) 2 (bondsAt 0 ![e.1, e.2]) ![X, X] (uniformField_isSmallCurvature hσ)
      (by norm_num) (by norm_num) (by
        intro l
        fin_cases l <;> simpa using hX)
    have hsc : bondDeriv (g (cubicTorusFrame L t n) 0) (uniformField _ _) (bondsAt 0 ![e.1, e.2])
          ![planeCoefficient μ ν e.1 • X, planeCoefficient μ ν e.2 • X] =
        planeCoefficient μ ν e.1 * planeCoefficient μ ν e.2 *
          bondDeriv (g (cubicTorusFrame L t n) 0) (uniformField _ _) (bondsAt 0 ![e.1, e.2]) ![X, X] := by
      have e3 : ![planeCoefficient μ ν e.1 • X, planeCoefficient μ ν e.2 • X] =
          fun l => (![planeCoefficient μ ν e.1, planeCoefficient μ ν e.2] l) • (![X, X] l) := by
        funext l
        fin_cases l <;> rfl
      rw [e3, bondDeriv_smul _ _ _ _ _ (by
        intro l
        fin_cases l
        · exact planeCoefficient_ne_zero μ ν e.1
        · exact planeCoefficient_ne_zero μ ν e.2)]
      simp [Fin.prod_univ_two]
    have hspan := max_intSupNorm_le_bondSpan L t n e.1 e.2 (by omega) (by omega)
    show |bondDeriv (g (cubicTorusFrame L t n) 0) (uniformField _ _) (bondsAt 0 ![e.1, e.2])
        ![planeCoefficient μ ν e.1 • X, planeCoefficient μ ν e.2 • X]| ≤ _
    rw [hsc, abs_mul, abs_mul]
    obtain ⟨s₁, hs₁⟩ : ∃ s : ℝ, s = (intSupNorm e.1.1 : ℝ) := ⟨_, rfl⟩
    obtain ⟨s₂, hs₂⟩ : ∃ s : ℝ, s = (intSupNorm e.2.1 : ℝ) := ⟨_, rfl⟩
    obtain ⟨sp, hsp⟩ : ∃ s : ℝ, s =
      ((bondSpan (0 : (cubicTorusFrame L t n).Cell) (bondsAt 0 ![e.1, e.2]) : ℕ) : ℝ) := ⟨_, rfl⟩
    have hd' : |bondDeriv (g (cubicTorusFrame L t n) 0) (uniformField _ _) (bondsAt 0 ![e.1, e.2])
        ![X, X]| ≤ A * Real.exp (-(κ * sp)) := by
      rw [hsp]
      exact hd
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
    have hexp2 : Real.exp (-(κ * sp)) ≤
        Real.exp (-(κ / 2 * s₁)) * Real.exp (-(κ / 2 * s₂)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hl1 := abs_planeCoefficient_le μ ν e.1
    have hl2 := abs_planeCoefficient_le μ ν e.2
    rw [← hs₁] at hl1
    rw [← hs₂] at hl2
    have hd2 := hd'.trans (mul_le_mul_of_nonneg_left hexp2 hA0.le)
    unfold bondWeight
    rw [← hs₁, ← hs₂]
    obtain ⟨e₁, he₁⟩ : ∃ u : ℝ, u = Real.exp (-(κ / 2 * s₁)) := ⟨_, rfl⟩
    obtain ⟨e₂, he₂⟩ : ∃ u : ℝ, u = Real.exp (-(κ / 2 * s₂)) := ⟨_, rfl⟩
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
        ≤ (1 + s₁) ^ 2 * (1 + s₂) ^ 2 * (A * (e₁ * e₂)) :=
          mul_le_mul (mul_le_mul (hl1.trans hsq1) (hl2.trans hsq2) (abs_nonneg _) (by positivity))
            hd2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hprod : HasSum (fun e : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
      bondWeight (κ / 2) e.1 * bondWeight (κ / 2) e.2)
      ((∑' b, bondWeight (κ / 2) b) * ∑' b, bondWeight (κ / 2) b) :=
    HasSum.mul hA.hasSum hA.hasSum
      (Summable.mul_of_nonneg hA hA (bondWeight_nonneg _) (bondWeight_nonneg _))
  have hle := HasSum.norm_le_of_bounded hvs₁ (hprod.mul_left A)
    (fun e => by simpa [Real.norm_eq_abs] using hterm e)
  rw [Real.norm_eq_abs] at hle
  refine hle.trans ?_
  nlinarith
end YangMills.Construction.FamilyNorms
end
