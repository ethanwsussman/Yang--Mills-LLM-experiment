import YangMills.Construction.ResponseInTheExpansion.CumulantsOfQuadraticFormsProof
import YangMills.Construction.FourPointCondition.CumulantOfAnObservableProof
import YangMills.Construction.FreeEnergiesOfTheFlow.ScoredTowerOfTheFlow
import YangMills.Construction.ResponseInTheExpansion.LawOfTheDrawsBelow
import YangMills.Construction.ResponseInTheExpansion.LevelsBelowATuple
import YangMills.Construction.ResponseInTheExpansion.LocalRestrictionOfATuple
import YangMills.Construction.ResponseInTheExpansion.NumbersOfAScoredTowerAreTheChain
import YangMills.Construction.ResponseInTheExpansion.NumbersOfTheChainAreOne
import YangMills.Construction.ResponseInTheExpansion.TheWindowHasATower
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ENNReal
namespace YangMills.Construction.ResponseInTheExpansion
open Probability (IsBoundedRealRV)
open Cumulants
section CumulantBounds
variable {Ω : Type} [MeasurableSpace Ω]
private theorem mixedCumulant_congr_ae {ν : Measure Ω} {k : ℕ} {X Y : Fin k → Ω → ℝ}
    (h : ∀ i, X i =ᵐ[ν] Y i) : mixedCumulant ν X = mixedCumulant ν Y := by apply _root_.YangMills.Construction.ReflectionPositivity.CutoffMirrors.CentredMomentExpansion.mixedCumulant_congr_ae <;> assumption
private theorem mixedCumulant_map {Ω' : Type} [MeasurableSpace Ω'] {μ : Measure Ω'} {Φ : Ω' → Ω}
    (hΦ : Measurable Φ) {k : ℕ} {X : Fin k → Ω → ℝ} (hX : ∀ i, Measurable (X i)) :
    mixedCumulant (μ.map Φ) X = mixedCumulant μ fun i => X i ∘ Φ := by
  have e : (fun t : Fin k → ℂ => Complex.log (momentGeneratingFunction (μ.map Φ) X t)) =
      fun t => Complex.log (momentGeneratingFunction μ (fun i => X i ∘ Φ) t) := by
    funext t
    congr 1
    unfold momentGeneratingFunction
    refine integral_map hΦ.aemeasurable ?_
    have : Measurable fun ω => Complex.exp (∑ i, t i * (X i ω : ℂ)) := by
      refine Complex.measurable_exp.comp (Finset.measurable_sum _ fun i _ => ?_)
      exact measurable_const.mul (Complex.measurable_ofReal.comp (hX i))
    exact this.aestronglyMeasurable
  unfold mixedCumulant
  rw [e]
private theorem boundedRV_add {X Y : Ω → ℝ} (hX : IsBoundedRealRV X) (hY : IsBoundedRealRV Y) :
    IsBoundedRealRV fun ω => X ω + Y ω := by
  obtain ⟨a, ha⟩ := hX.bounded
  obtain ⟨b, hb⟩ := hY.bounded
  exact ⟨hX.measurable.add hY.measurable, a + b, fun ω => (abs_add_le _ _).trans (add_le_add (ha ω) (hb ω))⟩
private theorem boundedRV_const_mul {X : Ω → ℝ} (a : ℝ) (hX : IsBoundedRealRV X) :
    IsBoundedRealRV fun ω => a * X ω := by apply _root_.YangMills.SharedProofs.p15020 <;> assumption
private theorem boundedRV_const (a : ℝ) : IsBoundedRealRV fun _ : Ω => a :=
  ⟨measurable_const, |a|, fun _ => le_rfl⟩
private theorem eLpNorm_four_le (ν : Measure Ω) [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (hf : IsBoundedRealRV f) {B : ℝ} (hB : 0 ≤ B) (h : ∫ ω, f ω ^ 4 ∂ν ≤ B ^ 4) :
    (eLpNorm f 4 ν).toReal ≤ B := by apply _root_.YangMills.SharedProofs.p27363 <;> assumption
private theorem eLpNorm_four_add_le (ν : Measure Ω) [IsProbabilityMeasure ν] {f g : Ω → ℝ}
    (hf : IsBoundedRealRV f) (hg : IsBoundedRealRV g) :
    (eLpNorm (fun ω => f ω + g ω) 4 ν).toReal ≤ (eLpNorm f 4 ν).toReal + (eLpNorm g 4 ν).toReal := by apply _root_.YangMills.SharedProofs.p72579 <;> assumption
end CumulantBounds
section NearQuadratic
open BlockAverages
variable {Ω : Type} [MeasurableSpace Ω]
private theorem quadraticForm_boundedRV {I : Type} [Fintype I] (κ : Matrix I I ℝ) (H : Ω → I → imaginaryQuaternions)
    {Bg : ℝ} (hm : ∀ (a : I) (e : Fin 3), Measurable fun ω => imaginaryComponent e (H ω a))
    (hb : ∀ ω a e, |imaginaryComponent e (H ω a)| ≤ Bg) :
    IsBoundedRealRV fun ω => quadraticForm κ (H ω) := by apply _root_.YangMills.SharedProofs.p57896 <;> assumption
private theorem boundedRV_indicator {S : Set Ω} (hS : MeasurableSet S) {f : Ω → ℝ}
    (hf : IsBoundedRealRV f) : IsBoundedRealRV (S.indicator f) := by apply _root_.YangMills.SharedProofs.p34315 <;> assumption
private theorem eLpNorm_four_quadraticForm_le (ν : Measure Ω) [IsProbabilityMeasure ν] {S : Set Ω}
    (hS : MeasurableSet S) {I : Type} [Fintype I] (κ : Matrix I I ℝ) (H : Ω → I → imaginaryQuaternions) {Bg K : ℝ}
    (hm : ∀ (a : I) (e : Fin 3), Measurable fun ω => imaginaryComponent e (H ω a))
    (hb : ∀ ω a e, |imaginaryComponent e (H ω a)| ≤ Bg) (hK : 0 ≤ K)
    (h8 : ∀ (a b : I) (e : Fin 3), ∫ ω, S.indicator
      (fun ω => imaginaryComponent e (H ω a) ^ 4 * imaginaryComponent e (H ω b) ^ 4) ω ∂ν ≤ K ^ 4) :
    (eLpNorm (S.indicator fun ω => quadraticForm κ (H ω)) 4 ν).toReal ≤ 3 / 2 * (∑ a, ∑ b, |κ a b|) * K := by apply _root_.YangMills.SharedProofs.p29187 <;> assumption
private theorem mixedCumulant_near_quadratic (hT : MixedCumulantFacts.MixedCumulantProperties)
    (hCQ : quadraticFormCumulantsStatement) (q : ℕ) (Bt : ℝ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (A E : Set Ω) (I : Type) [Fintype I] (H : Ω → I → imaginaryQuaternions) (Tc : Matrix I I ℝ) (ε₂ Bg : ℝ)
      (κ : Fin (q + 1) → Matrix I I ℝ) (X : Fin (q + 1) → Ω → ℝ) (a : ℝ) (b : Fin (q + 1) → ℝ)
      (ρ τ τ' K Kap : ℝ),
      MeasurableSet A → MeasurableSet E → E ⊆ A → (∀ i, (κ i).IsSymm) →
      (∀ (a : I) (e : Fin 3), Measurable fun ω => imaginaryComponent e (H ω a)) →
      (∀ ω a e, |imaginaryComponent e (H ω a)| ≤ Bg) → Tc.IsSymm → (∀ a b, |Tc a b| ≤ Bt) → 0 ≤ ε₂ → ε₂ ≤ 1 →
      (∀ (r : ℕ) (a : Fin r → I) (e : Fin r → Fin 3), r ≤ 2 * (q + 1) →
        |∫ ω, Set.indicator A (fun ω => ∏ i, imaginaryComponent (e i) (H ω (a i))) ω ∂μ -
          wickPairingSum fun i i' => if e i = e i' then Tc (a i) (a i') else 0| ≤ ε₂) →
      (∀ i, IsBoundedRealRV (X i)) → 0 ≤ ρ → 0 ≤ τ → 0 ≤ τ' → 0 ≤ K → 0 ≤ Kap →
      (∀ i, ∑ a, ∑ b, |κ i a b| ≤ Kap) →
      (∀ i, ∫ ω, E.indicator (fun ω => (a * (X i ω + b i) - quadraticForm (κ i) (H ω)) ^ 4) ω ∂μ ≤ ρ ^ 4) →
      (∀ i, ∫ ω, Eᶜ.indicator (fun ω => (a * (X i ω + b i)) ^ 4) ω ∂μ ≤ τ ^ 4) →
      (∀ (c d : I) (e : Fin 3), ∫ ω, A.indicator
        (fun ω => imaginaryComponent e (H ω c) ^ 4 * imaginaryComponent e (H ω d) ^ 4) ω ∂μ ≤ K ^ 4) →
      (∀ (c d : I) (e : Fin 3), ∫ ω, (A \ E).indicator
        (fun ω => imaginaryComponent e (H ω c) ^ 4 * imaginaryComponent e (H ω d) ^ 4) ω ∂μ ≤ τ' ^ 4) →
      ‖(a : ℂ) ^ (q + 1) * mixedCumulant μ X - ((cyclicTraceSum κ Tc : ℝ) : ℂ)‖ ≤
        26 * ((q : ℝ) + 1) * ((ρ + τ + 3 / 2 * Kap * τ') *
          (ρ + τ + 3 / 2 * Kap * τ' + 3 / 2 * Kap * K) ^ q) + C * Kap ^ (q + 1) * ε₂ := by apply _root_.YangMills.SharedProofs.p29850 <;> assumption
end NearQuadratic
section QuadraticEvaluation
open BlockAverages
variable {Ω : Type} [MeasurableSpace Ω]
private theorem integrable_of_boundedRV (ν : Measure Ω) [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (hf : IsBoundedRealRV f) : Integrable f ν := by apply _root_.YangMills.Construction.SourcesAndGluing.BoundedCumulants.integrable_of_isBoundedRealRV <;> assumption
private theorem boundedRV_pow {f : Ω → ℝ} (hf : IsBoundedRealRV f) (k : ℕ) :
    IsBoundedRealRV fun ω => f ω ^ k := by apply _root_.YangMills.SharedProofs.p10820 <;> assumption
private theorem integral_indicator_pow_four_le (ν : Measure Ω) [IsProbabilityMeasure ν] {S : Set Ω}
    (hS : MeasurableSet S) {f : Ω → ℝ} (hf : IsBoundedRealRV f) {t : ℝ} (ht : 0 < t) :
    ∫ ω, S.indicator (fun ω => f ω ^ 4) ω ∂ν ≤ (t * ν.real S + (∫ ω, f ω ^ 8 ∂ν) / t) / 2 := by apply _root_.YangMills.SharedProofs.p45780 <;> assumption
private theorem abs_le_two_mul_eLpNorm_indicator_const (ν : Measure Ω) [IsProbabilityMeasure ν] {E : Set Ω}
    (hE : MeasurableSet E) (hp : 1 / 2 ≤ ν.real E) (D : ℝ) :
    |D| ≤ 2 * (eLpNorm (E.indicator fun _ => D) 4 ν).toReal := by apply _root_.YangMills.SharedProofs.p8036 <;> assumption
private theorem imaginaryComponent_smul (s : ℝ) (v : imaginaryQuaternions) (e : Fin 3) :
    imaginaryComponent e (s • v) = s * imaginaryComponent e v := by
  fin_cases e <;> simp [imaginaryComponent]
private theorem quadraticForm_smul {I : Type} [Fintype I] (κ : Matrix I I ℝ) (s : ℝ) (G : I → imaginaryQuaternions) :
    quadraticForm κ (fun a => s • G a) = s ^ 2 * quadraticForm κ G := by apply _root_.YangMills.SharedProofs.p23085 <;> assumption
open Classical in
private def pairingMajorant (r : ℕ) (D : ℝ) : ℝ :=
  ∑ _π : Finpartition (Finset.univ : Finset (Fin r)), D ^ r
private theorem abs_wickPairingSum_le {r : ℕ} {g : Fin r → Fin r → ℝ} {D : ℝ} (hD : 1 ≤ D)
    (hg : ∀ i j, |g i j| ≤ D) : |wickPairingSum g| ≤ pairingMajorant r D := by apply _root_.YangMills.DeltaSharedProofs.p500570 <;> assumption
private def logPowerConst : ℝ := 5000 ^ 24
private theorem logPowerConst_nonneg : 0 ≤ logPowerConst := by
  unfold logPowerConst
  norm_num
private theorem log_pow_le_rpow {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 24 ≤ logPowerConst * x ^ ((24 : ℝ) / 5000) := by
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 := Real.log_le_rpow_div (by linarith : 0 ≤ x) (by norm_num : (0 : ℝ) < 1 / 5000)
  have h2 : Real.log x ≤ 5000 * x ^ ((1 : ℝ) / 5000) := by
    refine h1.trans (le_of_eq ?_)
    ring
  calc Real.log x ^ 24 ≤ (5000 * x ^ ((1 : ℝ) / 5000)) ^ 24 := pow_le_pow_left₀ h0 h2 24
    _ = logPowerConst * x ^ ((24 : ℝ) / 5000) := by
      unfold logPowerConst
      rw [mul_pow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 5000)), ← Real.rpow_mul (by linarith)]
      norm_num
private theorem pairingMajorant_nonneg (r : ℕ) {D : ℝ} (hD : 0 ≤ D) : 0 ≤ pairingMajorant r D := by apply _root_.YangMills.DeltaSharedProofs.p500915 <;> assumption
private theorem add_pow_eight_le (a b : ℝ) : (a + b) ^ 8 ≤ 128 * (a ^ 8 + b ^ 8) := by apply _root_.YangMills.SharedProofs.p54202 <;> assumption
private theorem prod_addCases_const {I : Type} (m : ℕ) (f : I → ℝ) (c d : I) :
    ∏ i : Fin (m + m), f (Fin.addCases (motive := fun _ => I) (fun _ => c) (fun _ => d) i) =
      f c ^ m * f d ^ m := by
  rw [Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
set_option maxHeartbeats 2000000 in
private theorem cumulant_of_quadratic (hT : MixedCumulantFacts.MixedCumulantProperties)
    (hCQ : quadraticFormCumulantsStatement) (q : ℕ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3) (Cr xr Cq : ℕ → ℝ) (C : ℝ) :
    ∃ C' x₁ : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Type) [Fintype I]
      (F : Fin (q + 1) → Ω → ℝ) (G : Ω → I → imaginaryQuaternions) (A B : Set Ω) (κ : Fin (q + 1) → Matrix I I ℝ)
      (Tc : Matrix I I ℝ) (c κ₀ : Fin (q + 1) → ℝ) (x n w Bg : ℝ),
      x₁ ≤ x → xr 2 ≤ x → 1 ≤ n → n ≤ x ^ ((1 : ℝ) / 90) → 0 ≤ w → w ≤ x →
      IsLocalQuadraticObservable μ F G A B κ Tc c x n C 40 Cr xr →
      (∀ (a : I) (e : Fin 3), Measurable fun ω => imaginaryComponent e (G ω a)) →
      (∀ ω a e, |imaginaryComponent e (G ω a)| ≤ Bg) →
      (∀ i, Measurable (F i)) → (∀ i, ∃ Cb : ℝ, ∀ᵐ ω ∂μ, |F i ω| ≤ Cb) →
      (∀ i (r : ℕ), 1 ≤ r → ∫ ω, |F i ω - κ₀ i| ^ (2 * r) ∂μ ≤ (Cq r * w) ^ (2 * r)) →
      ‖(x : ℂ) ^ (q + 1) * mixedCumulant μ F - ((cyclicTraceSum κ Tc : ℝ) : ℂ)‖ ≤
        C' * x ^ (-(1 / 5 : ℝ)) := by
  obtain ⟨C', x₁, h⟩ :=
    FourPointCondition.mixedCumulant_of_fourthMomentApproximation hT hCQ q hq1 hq3 (Cr 2) Cq C
  refine ⟨C', x₁, ?_⟩
  intro Ω _ μ _ I _ F G A B κ Tc c κ₀ x n w Bg hx hxr hn1 hn hw0 hwx R hm hb hFm hFb hFmom
  exact h Ω μ I F G A B κ Tc c κ₀ x n w Bg hx hn1 hn hw0 hwx
    ⟨R.measurableSet_good, hm, hb, R.gaussian_moments, R.covariance_symm, R.covariance_bounded,
      R.kernel_symm, R.kernel_mass, fun i => R.quadratic_approx i 2 (by norm_num) hxr,
      R.bad_small, R.bad_within_small⟩ hFm hFb hFmom
private def imaginaryQuaternionOf (u v t : ℝ) : imaginaryQuaternions := ⟨⟨0, u, v, t⟩, rfl⟩
private theorem imaginaryComponent_imaginaryQuaternionOf (g : Fin 3 → ℝ) (e : Fin 3) :
    imaginaryComponent e (imaginaryQuaternionOf (g 0) (g 1) (g 2)) = g e := by
  fin_cases e <;> simp [imaginaryComponent, imaginaryQuaternionOf]
private theorem quadraticForm_congr {I : Type} [Fintype I] (κ : Matrix I I ℝ) {G G' : I → imaginaryQuaternions}
    (h : ∀ a e, imaginaryComponent e (G a) = imaginaryComponent e (G' a)) :
    quadraticForm κ G = quadraticForm κ G' := by
  unfold quadraticForm
  simp only [h]
private theorem cumulant_of_quadratic_ae (hT : MixedCumulantFacts.MixedCumulantProperties)
    (hCQ : quadraticFormCumulantsStatement) (q : ℕ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3) (Cr xr Cq : ℕ → ℝ) (C : ℝ) :
    ∃ C' x₁ : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Type) [Fintype I]
      (F : Fin (q + 1) → Ω → ℝ) (G : Ω → I → imaginaryQuaternions) (A B : Set Ω) (κ : Fin (q + 1) → Matrix I I ℝ)
      (Tc : Matrix I I ℝ) (c κ₀ : Fin (q + 1) → ℝ) (x n w : ℝ),
      x₁ ≤ x → xr 2 ≤ x → 1 ≤ n → n ≤ x ^ ((1 : ℝ) / 90) → 0 ≤ w → w ≤ x →
      IsLocalQuadraticObservable μ F G A B κ Tc c x n C 40 Cr xr →
      (∀ i, Measurable (F i)) → (∀ i, ∃ Cb : ℝ, ∀ᵐ ω ∂μ, |F i ω| ≤ Cb) →
      (∀ i (r : ℕ), 1 ≤ r → ∫ ω, |F i ω - κ₀ i| ^ (2 * r) ∂μ ≤ (Cq r * w) ^ (2 * r)) →
      ‖(x : ℂ) ^ (q + 1) * mixedCumulant μ F - ((cyclicTraceSum κ Tc : ℝ) : ℂ)‖ ≤
        C' * x ^ (-(1 / 5 : ℝ)) := by
  obtain ⟨C', x₁, h⟩ := cumulant_of_quadratic hT hCQ q hq1 hq3 Cr xr Cq C
  refine ⟨C', x₁, ?_⟩
  intro Ω _ μ _ I _ F G A B κ Tc c κ₀ x n w hx₁ hxr hn1 hn hw0 hwx R hFm hFb hFmom
  obtain ⟨Bg, hBg⟩ := R.comp_bounded
  set g : I → Fin 3 → Ω → ℝ := fun a e ω =>
    max (-|Bg|) (min |Bg| ((R.aestronglyMeasurable_comp a e).mk _ ω)) with hg
  have hgm : ∀ a e, Measurable (g a e) := fun a e =>
    measurable_const.max (measurable_const.min (R.aestronglyMeasurable_comp a e).stronglyMeasurable_mk.measurable)
  have hgb : ∀ a e ω, |g a e ω| ≤ |Bg| := by
    intro a e ω
    rw [abs_le]
    refine ⟨le_max_left _ _, max_le ?_ (min_le_left _ _)⟩
    have := abs_nonneg Bg
    linarith
  have hgae : ∀ a e, ∀ᵐ ω ∂μ, g a e ω = A.indicator (fun ω => imaginaryComponent e (G ω a)) ω := by
    intro a e
    filter_upwards [(R.aestronglyMeasurable_comp a e).ae_eq_mk, hBg] with ω h1 h2
    simp only [hg]
    rw [← h1]
    by_cases hA : ω ∈ A
    · rw [Set.indicator_of_mem hA]
      have h3 := abs_le.1 ((h2 hA a e).trans (le_abs_self _))
      rw [min_eq_right h3.2, max_eq_right h3.1]
    · rw [Set.indicator_of_notMem hA]
      have h0 := abs_nonneg Bg
      rw [min_eq_right h0, max_eq_right (by linarith)]
  set Gt : Ω → I → imaginaryQuaternions := fun ω a => imaginaryQuaternionOf (g a 0 ω) (g a 1 ω) (g a 2 ω) with hGt
  have hc : ∀ ω a e, imaginaryComponent e (Gt ω a) = g a e ω := fun ω a e =>
    imaginaryComponent_imaginaryQuaternionOf (fun e => g a e ω) e
  have hall : ∀ᵐ ω ∂μ, ∀ (a : I) (e : Fin 3), ω ∈ A →
      imaginaryComponent e (Gt ω a) = imaginaryComponent e (G ω a) := by
    have h1 : ∀ᵐ ω ∂μ, ∀ (a : I) (e : Fin 3), g a e ω = A.indicator (fun ω => imaginaryComponent e (G ω a)) ω :=
      ae_all_iff.2 fun a => ae_all_iff.2 fun e => hgae a e
    filter_upwards [h1] with ω h2 a e hA
    rw [hc, h2, Set.indicator_of_mem hA]
  have hm : ∀ (a : I) (e : Fin 3), Measurable fun ω => imaginaryComponent e (Gt ω a) := by
    intro a e
    simp only [hc]
    exact hgm a e
  have hb : ∀ ω a e, |imaginaryComponent e (Gt ω a)| ≤ |Bg| := by
    intro ω a e
    rw [hc]
    exact hgb a e ω
  have R' : IsLocalQuadraticObservable μ F Gt A B κ Tc c x n C 40 Cr xr := by
    refine ⟨R.measurableSet_good, fun a e => (hm a e).aestronglyMeasurable.indicator R.measurableSet_good,
      ⟨|Bg|, ae_of_all _ fun ω _ a e => hb ω a e⟩, ?_, R.covariance_symm, R.covariance_bounded, R.kernel_symm,
      R.kernel_mass, ?_, R.bad_small, R.bad_within_small⟩
    · intro r a e hr
      obtain ⟨hi, hv⟩ := R.gaussian_moments r a e hr
      have hae : (Set.indicator A fun ω => ∏ i, imaginaryComponent (e i) (Gt ω (a i))) =ᵐ[μ]
          Set.indicator A fun ω => ∏ i, imaginaryComponent (e i) (G ω (a i)) := by
        filter_upwards [hall] with ω h2
        by_cases hA : ω ∈ A
        · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA]
          exact Finset.prod_congr rfl fun i _ => h2 _ _ hA
        · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]
      refine ⟨hi.congr hae.symm, ?_⟩
      rw [integral_congr_ae hae]
      exact hv
    · intro i r hr hx
      refine le_trans (le_of_eq ?_) (R.quadratic_approx i r hr hx)
      refine lintegral_congr_ae ?_
      filter_upwards [hall] with ω h2
      by_cases hA : ω ∈ A ∩ B
      · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA,
          quadraticForm_congr (κ i) fun a e => h2 a e hA.1]
      · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]
  exact h Ω μ I F Gt A B κ Tc c κ₀ x n w |Bg| hx₁ hxr hn1 hn hw0 hwx R' hm hb hFm hFb hFmom
end QuadraticEvaluation
section Conclusion
open WeightedResponses TorusLumps RenormalizationStepParameters FreeEnergies
variable {ℓ : TorusLumps.StepParameters}
private theorem response_congr_coeffs (T : StageTower ℓ) (β : ℝ) {al al' : ℕ → ℝ} :
    ∀ (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side s n)), (∀ j < s, al j = al' j) →
      response T β al s n h = response T β al' s n h := by
  intro s
  induction s with
  | zero => intro n _ h _; funext u; simp only [response]
  | succ s ih =>
    intro n _ h hal
    have e1 := ih (n * ℓ.side) h fun j hj => hal j (by omega)
    have e2 : sourceTerm T al s n h = sourceTerm T al' s n h := by
      funext u
      simp only [sourceTerm, hal s (by omega)]
    funext u
    rw [response, response, e1, e2]
private theorem followsFlow_mono {Tb : ParameterAssignment} {y β : ℝ} {T : StageTower (Tb.stepParameters y)}
    {S : ScoredStageTower T} {tp k : ℕ} (h : S.FollowsFlow β tp) (hk : k ≤ tp) : S.FollowsFlow β k where
  isFlowStep u hu := h.isFlowStep u (hu.trans hk)
  startsAtWilson := h.startsAtWilson
  bottom_coupling := h.bottom_coupling
  isCutoff_bottom := h.isCutoff_bottom
  marksMeasurable := h.marksMeasurable
  params_eq := h.params_eq
  N₀_eq := h.N₀_eq
  coeff_zero := h.coeff_zero
  score_zero := h.score_zero
  cold_zero := h.cold_zero
  hull_zero := h.hull_zero
  score_succ u hu := h.score_succ u (lt_of_lt_of_le hu hk)
  cold_succ u hu := h.cold_succ u (lt_of_lt_of_le hu hk)
  hull_succ u hu := h.hull_succ u (lt_of_lt_of_le hu hk)
  isAdmissible u hu := h.isAdmissible u (hu.trans hk)
  coeff_near_one u hu := h.coeff_near_one u (hu.trans hk)
private theorem isTowerOnParameters_of_followsFlow {Tb : ParameterAssignment} {y β : ℝ}
    {T : StageTower (Tb.stepParameters y)} {S : ScoredStageTower T} {tp : ℕ} (h : S.FollowsFlow β tp) :
    IsTowerAtParameters Tb y T β tp where
  startsAtWilson := h.startsAtWilson
  coupling_eq j hj := by
    rcases Nat.lt_or_ge j (tp + 1) with h1 | h1
    · exact (h.isFlowStep j (by omega)).coupling_eq
    · obtain rfl : j = tp + 1 := by omega
      exact (h.isFlowStep tp le_rfl).nextCoupling_eq
  onFamily j hj := (h.isFlowStep j hj).onFamily
private theorem connected_bound_of_cumulants (hT : MixedCumulantFacts.MixedCumulantProperties)
    (hCQ : quadraticFormCumulantsStatement) (hLaw : sampleBelowLawStatement)
    {Tb : ParameterAssignment} {y : ℝ} (Kr₀ : ResponseParameters) (hfit : (Tb.stepParameters y).Admissible)
    (hJ : 11 * 2 ^ 12 * (Tb.stepParameters y).baseDepth < (Tb.stepParameters y).side)
    (G₁ : ∀ (β : ℝ) (tp : ℕ), CouplingsAboveFloor (Tb.stepParameters y) β tp →
      ∃ (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T), S.params = Kr₀ ∧ S.FollowsFlow β tp)
    (G₂ : tupleCumulantApproxAt Tb Kr₀ y) (G₃ : localQuadraticEstimateAt Tb y)
    (G₄ : ∀ (β : ℝ) (k : ℕ) (T : StageTower (Tb.stepParameters y)) (S : ScoredStageTower T),
      S.FollowsFlow β k → IsChainResponseCoeff (Tb.stepParameters y) S.params β k S.coeffs)
    (G₅ : ∀ K K' : ResponseParameters, K.Admissible (Tb.stepParameters y) → K'.Admissible (Tb.stepParameters y) →
      ∀ (β : ℝ) (k : ℕ) (al al' : ℕ → ℝ), (∀ j ≤ k, y ≤ flowCouplings (Tb.stepParameters y) β j) →
      IsChainResponseCoeff (Tb.stepParameters y) K β k al → IsChainResponseCoeff (Tb.stepParameters y) K' β k al' →
      ∀ j ≤ k, al j = al' j) :
    ∀ Kr : ResponseParameters, Kr.Admissible (Tb.stepParameters y) → ∀ vt : ℝ, 0 < vt → vt ≤ 1 → ∃ C x₀ : ℝ,
    ∀ (q : ℕ) (β : ℝ) (k m : ℕ) (n : ℝ) (al : ℕ → ℝ), 1 ≤ q → q ≤ 3 →
      InScaleWindow (Tb.stepParameters y) β k m n x₀ →
      IsChainResponseCoeff (Tb.stepParameters y) Kr β k al →
      ∀ f : Fin (q + 1) → PeriodicLattice.FourTorus (Tb.stepParameters y).side m → ℝ,
        IsSeparatedTestTuple (Tb.stepParameters y) m n vt f →
        ‖((((couplingFlow (Tb.stepParameters y) β k).1 ^ (q + 1) : ℝ)) : ℂ) *
              connectedCurvature β (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ m))
                (fun i => testWeight (Tb.stepParameters y).side k m (f i)) -
            ((al k ^ (q + 1) *
              gaussianCumulantLimit (PeriodicLattice.torusSide (Tb.stepParameters y).side m) f : ℝ) : ℂ)‖ ≤
          C * (couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 100 : ℝ)) := by
  intro Kr hKr vt h0 h1
  by_cases hK₀ : Kr₀.Admissible (Tb.stepParameters y)
  swap
  · refine ⟨0, 0, ?_⟩
    intro q β k m n al hq1 hq3 hw hnum f hf
    exfalso
    obtain ⟨T, S, hSK, hS⟩ :=
      G₁ β (k + 2 * chainDepth (couplingFlow (Tb.stepParameters y) β k).1) fun j hj => hw.flow_ge j hj
    apply hK₀
    have h2 := (hS.isAdmissible 0 (Nat.zero_le _)).params_admissible
    rw [hS.params_eq 0, hSK] at h2
    exact h2
  obtain ⟨Cq, xb, kB⟩ := G₂ vt h0 h1
  obtain ⟨Cr, xr, Cl, xl, kR⟩ := G₃ Kr₀ hK₀ vt h0 h1 40
  choose! Cc xc hcore using fun (q : ℕ) (hq : 1 ≤ q ∧ q ≤ 3) =>
    cumulant_of_quadratic_ae hT hCQ q hq.1 hq.2 Cr xr Cq Cl
  refine ⟨1 + (|Cc 1| + |Cc 2| + |Cc 3|) + 2 * |Cl|,
    max (max xb xl) (max (max (xc 1) (max (xc 2) (xc 3))) (max (32 ^ 5) (xr 2))), ?_⟩
  intro q β k m n al hq1 hq3 hw hnum f hf
  have hf₀ := hw.le_coupling
  obtain ⟨x, hxd⟩ : ∃ x : ℝ, x = (couplingFlow (Tb.stepParameters y) β k).1 := ⟨_, rfl⟩
  rw [← hxd] at hf₀ ⊢
  have hxb : xb ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hf₀
  have hxl : xl ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hf₀
  have hxc : xc q ≤ x := by
    have h2 : max (xc 1) (max (xc 2) (xc 3)) ≤ x :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans hf₀
    simp only [max_le_iff] at h2
    have hp : ∀ p : ℕ, 1 ≤ p → p ≤ 3 → xc p ≤ x := by
      intro p hp1 hp3
      interval_cases p
      · exact h2.1
      · exact h2.2.1
      · exact h2.2.2
    exact hp q hq1 hq3
  have hx32 : (32 : ℝ) ^ 5 ≤ x :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hf₀
  have hxr : xr 2 ≤ x := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hf₀
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx32
  have hx0 : 0 < x := by linarith
  have hwB : InScaleWindow (Tb.stepParameters y) β k m n xb :=
    ⟨hxd ▸ hxb, hw.flow_ge, hw.lower_le, hw.le_upper, hw.side_ge⟩
  have hwR : InScaleWindow (Tb.stepParameters y) β k m n xl :=
    ⟨hxd ▸ hxl, hw.flow_ge, hw.lower_le, hw.le_upper, hw.side_ge⟩
  obtain ⟨T, S, hSK, hS⟩ :=
    G₁ β (k + 2 * chainDepth (couplingFlow (Tb.stepParameters y) β k).1) fun j hj => hw.flow_ge j hj
  have hSk := followsFlow_mono hS (Nat.le_add_right k _)
  have hfloor : ∀ j ≤ k, y ≤ flowCouplings (Tb.stepParameters y) β j := fun j hj => hw.flow_ge j (by omega)
  have hSfit : S.params.Admissible (Tb.stepParameters y) := by
    have h2 := (hS.isAdmissible 0 (Nat.zero_le _)).params_admissible
    rw [hS.params_eq 0] at h2
    exact h2
  have hal : ∀ j ≤ k, al j = S.coeffs j := fun j hj =>
    G₅ Kr S.params hKr hSfit β k al S.coeffs hfloor hnum (G₄ β k T S hSk) j hj
  have hal2 : |al k| ≤ 2 := by
    rw [hal k le_rfl]
    have h2 := abs_le.1 (hS.coeff_near_one k (Nat.le_add_right k _))
    have h3 : S.coeffs k = (S.setup k).coeff := rfl
    rw [h3, abs_le]
    constructor <;> linarith [h2.1, h2.2]
  have hresp : ∀ i, response T β S.coeffs k (2 * (Tb.stepParameters y).side ^ m)
      (testWeight (Tb.stepParameters y).side k m (f i)) =
      response T β al k (2 * (Tb.stepParameters y).side ^ m) (testWeight (Tb.stepParameters y).side k m (f i)) :=
    fun i => (response_congr_coeffs T β k _ _ fun j hj => hal j hj.le).symm
  obtain ⟨hcumB, hmomB⟩ := kB q β k m n T S hq1 hq3 hwB hSK hSk f hf
  obtain ⟨Ω, _, μ, _, Φ, I, _, G, A, B, κ, Tc, c, hΦ, hmap, R, htr⟩ :=
    kR q β k m n S.coeffs T S _ hq1 hq3 hwR (hSK ▸ G₄ β k T S hSk) (hal k le_rfl ▸ hal2) (Nat.le_add_right k _)
      hSK hS rfl (isTowerOnParameters_of_followsFlow hS) hS.isCutoff_bottom hS.marksMeasurable f hf
  simp only [hresp] at hcumB hmomB R
  rw [← hal k le_rfl] at htr
  choose κ₀ hκ₀ using hmomB
  obtain ⟨hreg1, hreg2⟩ := hLaw (Tb.stepParameters y) hfit hJ T hS.isCutoff_bottom hS.marksMeasurable β al
  set Fk : Fin (q + 1) → MarkedSample (Tb.stepParameters y) k (2 * (Tb.stepParameters y).side ^ m) → ℝ := fun i =>
    response T β al k (2 * (Tb.stepParameters y).side ^ m) (testWeight (Tb.stepParameters y).side k m (f i)) with hFk
  have hFm : ∀ i, Measurable (Fk i) := fun i => (hreg2 k _ _).1
  have hcumΦ : mixedCumulant (markedSampleLaw T β k (2 * (Tb.stepParameters y).side ^ m)) Fk =
      mixedCumulant μ fun i ω => Fk i (Φ ω) := by
    rw [← hmap]
    exact mixedCumulant_map hΦ hFm
  have hRle : (clusterRange x : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 100) := by
    have h2 := (Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le ((1 : ℝ) / 100))).le
    have h3 : 1 ≤ x ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx1 (by norm_num)
    unfold clusterRange
    linarith
  have hRge : x ^ ((1 : ℝ) / 100) ≤ (clusterRange x : ℝ) := Nat.le_ceil _
  have hx100 : 1 ≤ x ^ ((1 : ℝ) / 100) := Real.one_le_rpow hx1 (by norm_num)
  have hLpos : (1 : ℝ) ≤ ((Tb.stepParameters y).side : ℝ) := by
    have : 1 ≤ (Tb.stepParameters y).side := by omega
    exact_mod_cast this
  have hnR : x ^ ((1 : ℝ) / 100) ≤ n := by
    have h2 := hw.lower_le
    rw [← hxd] at h2
    have h3 : (clusterRange x : ℝ) ≤ 2 ^ 12 * ((Tb.stepParameters y).side : ℝ) * (clusterRange x : ℝ) := by
      have h4 : (1 : ℝ) ≤ 2 ^ 12 * ((Tb.stepParameters y).side : ℝ) := by nlinarith
      have h5 : (0 : ℝ) ≤ (clusterRange x : ℝ) := Nat.cast_nonneg _
      nlinarith
    linarith
  have hn1 : 1 ≤ n := hx100.trans hnR
  have hnx : n ≤ x ^ ((1 : ℝ) / 90) := by
    have := hw.le_upper
    rwa [← hxd] at this
  obtain ⟨w, hwd⟩ : ∃ w : ℝ, w = n ^ 4 * (clusterRange x : ℝ) ^ 4 * Real.log x := ⟨_, rfl⟩
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hw0 : 0 ≤ w := by
    rw [hwd]
    positivity
  have hwx : w ≤ x := by
    have hl : Real.log x ≤ 2 * x ^ ((1 : ℝ) / 2) := by
      refine (Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 2)).trans (le_of_eq ?_)
      ring
    have hn4 : n ^ 4 ≤ x ^ ((4 : ℝ) / 90) := by
      have h2 := pow_le_pow_left₀ (by linarith : 0 ≤ n) hnx 4
      rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / 90)), ← Real.rpow_mul hx0.le] at h2
      refine h2.trans (le_of_eq ?_)
      norm_num
    have hR4 : (clusterRange x : ℝ) ^ 4 ≤ 16 * x ^ ((4 : ℝ) / 100) := by
      have h2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hRle 4
      refine h2.trans (le_of_eq ?_)
      rw [mul_pow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 100)), ← Real.rpow_mul hx0.le]
      norm_num
    have h32 : 32 ≤ x ^ ((1 : ℝ) / 5) := by
      have h2 := Real.rpow_le_rpow (by positivity) hx32 (by norm_num : (0 : ℝ) ≤ 1 / 5)
      have e : ((32 : ℝ) ^ 5) ^ ((1 : ℝ) / 5) = 32 := by
        have := Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 32) (by norm_num : (5 : ℕ) ≠ 0)
        norm_num at this ⊢
      rwa [e] at h2
    have hprod : n ^ 4 * (clusterRange x : ℝ) ^ 4 * Real.log x ≤
        x ^ ((4 : ℝ) / 90) * (16 * x ^ ((4 : ℝ) / 100)) * (2 * x ^ ((1 : ℝ) / 2)) := by
      have hp : ∀ a : ℝ, 0 < x ^ a := fun a => Real.rpow_pos_of_pos hx0 a
      refine mul_le_mul (mul_le_mul hn4 hR4 (by positivity) (hp _).le) hl hlog0 ?_
      have := hp ((4 : ℝ) / 90)
      have := hp ((4 : ℝ) / 100)
      positivity
    have he : x ^ ((4 : ℝ) / 90) * (16 * x ^ ((4 : ℝ) / 100)) * (2 * x ^ ((1 : ℝ) / 2)) =
        32 * x ^ ((4 : ℝ) / 90 + 4 / 100 + 1 / 2) := by
      rw [Real.rpow_add hx0, Real.rpow_add hx0]
      ring
    have he2 : 32 * x ^ ((4 : ℝ) / 90 + 4 / 100 + 1 / 2) ≤ x ^ ((1 : ℝ) / 5) * x ^ ((4 : ℝ) / 5) := by
      refine mul_le_mul h32 (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (Real.rpow_nonneg hx0.le _)
        (Real.rpow_nonneg hx0.le _)
    have he3 : x ^ ((1 : ℝ) / 5) * x ^ ((4 : ℝ) / 5) = x := by
      rw [← Real.rpow_add hx0]
      norm_num
    rw [hwd]
    linarith
  have hmomΦ : ∀ i (r : ℕ), 1 ≤ r → ∫ ω, |Fk i (Φ ω) - κ₀ i| ^ (2 * r) ∂μ ≤ (Cq r * w) ^ (2 * r) := by
    intro i r hr
    have h2 := hκ₀ i r hr
    rw [← hmap, integral_map hΦ.aemeasurable] at h2
    · refine h2.trans (le_of_eq ?_)
      rw [hwd, hxd]
      ring_nf
    · exact (((continuous_abs.measurable.comp ((hFm i).sub_const _)).pow_const _)).aestronglyMeasurable
  have hbdd : ∀ i, ∃ Cb : ℝ, ∀ᵐ ω ∂μ, |Fk i (Φ ω)| ≤ Cb := by
    intro i
    obtain ⟨Cb, hCb⟩ :=
      (hreg2 k (2 * (Tb.stepParameters y).side ^ m) (testWeight (Tb.stepParameters y).side k m (f i))).2
    refine ⟨Cb, ?_⟩
    rw [← hmap] at hCb
    exact ae_of_ae_map hΦ.aemeasurable hCb
  have hmain := hcore q ⟨hq1, hq3⟩ Ω μ I (fun i ω => Fk i (Φ ω)) G A B κ Tc c κ₀ x n w hxc hxr hn1 hnx hw0 hwx
    (hxd ▸ R) (fun i => (hFm i).comp hΦ) hbdd hmomΦ
  have hcB : ‖connectedCurvature β (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ m))
      (fun i => testWeight (Tb.stepParameters y).side k m (f i)) - mixedCumulant μ fun i ω => Fk i (Φ ω)‖ ≤
      x ^ (-(20 : ℝ)) := by
    rw [← hcumΦ, hxd]
    exact hcumB
  set Sp := connectedCurvature β (fineSide (Tb.stepParameters y).side k (2 * (Tb.stepParameters y).side ^ m))
      (fun i => testWeight (Tb.stepParameters y).side k m (f i)) with hSp
  set Cm := mixedCumulant μ fun i ω => Fk i (Φ ω) with hCm
  set Lw : ℝ := al k ^ (q + 1) * gaussianCumulantLimit (PeriodicLattice.torusSide (Tb.stepParameters y).side m) f
    with hLw
  have hx100b : x ^ (-(1 / 100 : ℝ)) > 0 := Real.rpow_pos_of_pos hx0 _
  have e0 : (((x ^ (q + 1) : ℝ)) : ℂ) * Sp - (Lw : ℂ) = (((x ^ (q + 1) : ℝ)) : ℂ) * (Sp - Cm) +
      (((x : ℂ) ^ (q + 1) * Cm - ((cyclicTraceSum κ Tc : ℝ) : ℂ)) +
        (((cyclicTraceSum κ Tc - Lw : ℝ)) : ℂ)) := by
    push_cast
    ring
  rw [e0]
  have t1 : ‖(((x ^ (q + 1) : ℝ)) : ℂ) * (Sp - Cm)‖ ≤ x ^ (-(1 / 100 : ℝ)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h2 : x ^ (q + 1) ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by omega)
    calc x ^ (q + 1) * ‖Sp - Cm‖ ≤ x ^ 4 * x ^ (-(20 : ℝ)) :=
          mul_le_mul h2 hcB (norm_nonneg _) (by positivity)
      _ ≤ x ^ (-(1 / 100 : ℝ)) := by
          rw [← Real.rpow_natCast x 4, ← Real.rpow_add hx0]
          exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have t2 : ‖(x : ℂ) ^ (q + 1) * Cm - ((cyclicTraceSum κ Tc : ℝ) : ℂ)‖ ≤
      (|Cc 1| + |Cc 2| + |Cc 3|) * x ^ (-(1 / 100 : ℝ)) := by
    refine hmain.trans ?_
    have h2 : Cc q ≤ |Cc 1| + |Cc 2| + |Cc 3| := by
      have a1 := abs_nonneg (Cc 1)
      have a2 := abs_nonneg (Cc 2)
      have a3 := abs_nonneg (Cc 3)
      have hp : ∀ p : ℕ, 1 ≤ p → p ≤ 3 → Cc p ≤ |Cc 1| + |Cc 2| + |Cc 3| := by
        intro p hp1 hp3
        interval_cases p
        · linarith [le_abs_self (Cc 1)]
        · linarith [le_abs_self (Cc 2)]
        · linarith [le_abs_self (Cc 3)]
      exact hp q hq1 hq3
    have h3 : x ^ (-(1 / 5 : ℝ)) ≤ x ^ (-(1 / 100 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have h4 : 0 ≤ |Cc 1| + |Cc 2| + |Cc 3| := by positivity
    calc Cc q * x ^ (-(1 / 5 : ℝ)) ≤ (|Cc 1| + |Cc 2| + |Cc 3|) * x ^ (-(1 / 5 : ℝ)) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 h4
  have t3 : ‖(((cyclicTraceSum κ Tc - Lw : ℝ)) : ℂ)‖ ≤ 2 * |Cl| * x ^ (-(1 / 100 : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h2 : x ^ (-(1 / 2 : ℝ)) ≤ x ^ (-(1 / 100 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have h3 : 1 / n ≤ x ^ (-(1 / 100 : ℝ)) := by
      rw [Real.rpow_neg hx0.le, one_div]
      exact inv_anti₀ (by linarith) hnR
    have h4 : 0 ≤ x ^ (-(1 / 2 : ℝ)) + 1 / n := by positivity
    have h5 : |cyclicTraceSum κ Tc - Lw| ≤ Cl * (x ^ (-(1 / 2 : ℝ)) + 1 / n) := by
      have := htr
      rw [← hxd] at this
      exact this
    calc |cyclicTraceSum κ Tc - Lw| ≤ |Cl| * (x ^ (-(1 / 2 : ℝ)) + 1 / n) :=
          h5.trans (mul_le_mul_of_nonneg_right (le_abs_self _) h4)
      _ ≤ |Cl| * (2 * x ^ (-(1 / 100 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          linarith
      _ = _ := by ring
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add t1 (norm_add_le _ _)
    _ ≤ x ^ (-(1 / 100 : ℝ)) + ((|Cc 1| + |Cc 2| + |Cc 3|) * x ^ (-(1 / 100 : ℝ)) +
          2 * |Cl| * x ^ (-(1 / 100 : ℝ))) := by
        gcongr
    _ = _ := by ring
theorem connectedFunctionsStatement_holds (hT : MixedCumulantFacts.MixedCumulantProperties)
    (hCQ : quadraticFormCumulantsStatement) (hLaw : sampleBelowLawStatement)
    (hTow : scoredTowerExistsStatement) (hBelow : tupleCumulantApproxStatement)
    (hRead : localQuadraticEstimateStatement) (hNum : scoredTowerCoeffsAreChainStatement)
    (hOne : chainResponseCoeffsUnique) (hWin : windowTowerExistsStatement) :
    connectedFunctionsStatement := by
  intro a ha
  obtain ⟨L₁, r₁, c₁, p₁, h₁⟩ := hTow a ha
  obtain ⟨L₂, r₂, c₂, p₂, h₂⟩ := hBelow a ha
  obtain ⟨L₃, r₃, c₃, p₃, h₃⟩ := hRead a ha
  obtain ⟨L₄, r₄, c₄, p₄, h₄⟩ := hNum a ha
  obtain ⟨L₅, r₅, c₅, p₅, h₅⟩ := hOne a ha
  obtain ⟨L₆, r₆, c₆, p₆, h₆⟩ := hWin a ha
  refine ⟨max L₁ (max L₂ (max L₃ (max L₄ (max L₅ L₆)))),
    fun c => min (r₁ c) (min (r₂ c) (min (r₃ c) (min (r₄ c) (min (r₅ c) (r₆ c))))),
    max c₁ (max c₂ (max c₃ (max c₄ (max c₅ c₆)))),
    fun c => lt_min (p₁ c) (lt_min (p₂ c) (lt_min (p₃ c) (lt_min (p₄ c) (lt_min (p₅ c) (p₆ c))))),
    fun L hodd hL T hTa hTL hD hC hH hr hc => ?_⟩
  simp only [max_le_iff, le_min_iff] at hL hr hc
  obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6⟩ := hL
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6⟩ := hr
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hc
  obtain ⟨Kr₀, y₁, g₁⟩ := h₁ L hodd hL1 T hTa hTL hD hC hH hr1 hc1
  obtain ⟨y₂, g₂⟩ := h₂ L hodd hL2 T hTa hTL hD hC hH hr2 hc2 Kr₀
  obtain ⟨y₃, g₃⟩ := h₃ L hodd hL3 T hTa hTL hD hC hH hr3 hc3
  obtain ⟨y₄, g₄⟩ := h₄ L hodd hL4 T hTa hTL hD hC hH hr4 hc4
  obtain ⟨y₅, g₅⟩ := h₅ L hodd hL5 T hTa hTL hD hC hH hr5 hc5
  obtain ⟨y₆, g₆⟩ := h₆ L hodd hL6 T hTa hTL hD hC hH hr6 hc6
  refine ⟨max y₁ (max y₂ (max y₃ (max y₄ (max y₅ y₆)))), fun y hy hR hW => ?_⟩
  simp only [max_le_iff] at hy
  obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6⟩ := hy
  have hst : ExpansionHolds (T.stepParameters y) := ⟨hR, hW⟩
  obtain ⟨hfit, hJ, -⟩ := g₆ y hy6 hR hW
  exact connected_bound_of_cumulants hT hCQ hLaw Kr₀ hfit hJ (g₁ y hy1 hst) (g₂ y hy2 hst) (g₃ y hy3 hR hW)
    (g₄ y hy4 hR hW) (g₅ y hy5 hR hW)
end Conclusion
end YangMills.Construction.ResponseInTheExpansion
end
