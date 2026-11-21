import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfSumsWithMoments
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsSummedOverPlaces
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfTheMeanOfAPartProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames ConvexObservables
namespace Cumulants
variable {ι : Type} [Fintype ι]
theorem ballDensity_eq_zero_of_not_mem {ρ : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ} {η : BondField ι}
    (h : ¬ ∀ b, ‖η b‖ < ρ) : ballDensity (cutoffFactor ρ p) Φ η = 0 := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.ballDensity_eq_zero_of_not_mem <;> assumption
theorem abs_prod_le_one_add_sum_pow {α : Type} (P : Finset α) (a : α → ℝ) :
    |∏ t ∈ P, a t| ≤ 1 + ∑ t ∈ P, |a t| ^ P.card := by
  rcases P.eq_empty_or_nonempty with rfl | hP
  · simp
  · obtain ⟨t₀, h₀, ht⟩ := Finset.exists_max_image P (fun t => |a t|) hP
    have h1 : |∏ t ∈ P, a t| ≤ |a t₀| ^ P.card := by
      rw [Finset.abs_prod]
      calc ∏ t ∈ P, |a t| ≤ ∏ _t ∈ P, |a t₀| :=
            Finset.prod_le_prod (fun t _ => abs_nonneg _) fun t h => ht t h
        _ = |a t₀| ^ P.card := by simp
    have h2 : |a t₀| ^ P.card ≤ ∑ t ∈ P, |a t| ^ P.card :=
      Finset.single_le_sum (f := fun t => |a t| ^ P.card) (fun t _ => by positivity) h₀
    linarith
theorem integrable_finsetProd_mul_ballDensity {ρ : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ} {α : Type}
    (J : Finset α) (f : α → BondField ι → ℝ) (hc : ∀ l ∈ J, ContinuousOn (f l) {η | ∀ b, ‖η b‖ < ρ})
    (hm : ∀ l ∈ J, ∀ m : ℕ, 1 ≤ m → Integrable fun η => |f l η| ^ m * ballDensity (cutoffFactor ρ p) Φ η)
    (hI : Integrable (ballDensity (cutoffFactor ρ p) Φ))
    (hcd : ContinuousOn (ballDensity (cutoffFactor ρ p) Φ) {η | ∀ b, ‖η b‖ < ρ}) :
    Integrable fun η => (∏ l ∈ J, f l η) * ballDensity (cutoffFactor ρ p) Φ η := by
  classical
  set U : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hU
  have hUo : IsOpen U := by
    have : U = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
      ext η
      simp [hU]
    rw [this]
    exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_apply b).norm continuous_const
  have hcont : ContinuousOn (fun η => (∏ l ∈ J, f l η) * ballDensity (cutoffFactor ρ p) Φ η) U :=
    (continuousOn_finsetProd _ hc).mul hcd
  have hmeas : AEStronglyMeasurable (fun η => (∏ l ∈ J, f l η) * ballDensity (cutoffFactor ρ p) Φ η) volume := by
    have h1 : AEStronglyMeasurable (fun η => (∏ l ∈ J, f l η) * ballDensity (cutoffFactor ρ p) Φ η)
        (volume.restrict U) :=
      hcont.aestronglyMeasurable hUo.measurableSet
    have h2 : U.indicator (fun η => (∏ l ∈ J, f l η) * ballDensity (cutoffFactor ρ p) Φ η) =
        fun η => (∏ l ∈ J, f l η) * ballDensity (cutoffFactor ρ p) Φ η := by
      funext η
      by_cases h : η ∈ U
      · simp [h]
      · have h0 : ¬ ∀ b, ‖η b‖ < ρ := h
        simp [h, ballDensity_eq_zero_of_not_mem h0]
    rw [← h2]
    exact (aestronglyMeasurable_indicator_iff hUo.measurableSet).mpr h1
  have hdn : ∀ η, 0 ≤ ballDensity (cutoffFactor ρ p) Φ η := fun η => by
    refine mul_nonneg (Finset.prod_nonneg fun b _ => ?_) (Real.exp_pos _).le
    unfold cutoffFactor
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · simpa using hI
  have hg : Integrable fun η => ballDensity (cutoffFactor ρ p) Φ η +
      ∑ l ∈ J, |f l η| ^ J.card * ballDensity (cutoffFactor ρ p) Φ η :=
    hI.add (integrable_finsetSum _ fun l hl => hm l hl _ (Finset.card_pos.mpr hJ))
  refine hg.mono' hmeas (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hdn η)]
  have h1 := mul_le_mul_of_nonneg_right (abs_prod_le_one_add_sum_pow J fun l => f l η) (hdn η)
  refine h1.trans (le_of_eq ?_)
  rw [add_mul, one_mul, Finset.sum_mul]
theorem summedObservableCumulantBound_of_bounds (hCum : cumulantDecayBound)
    (hSum : placeSummedCumulantBound) : summedObservableCumulantBound := by
  classical
  intro N N' κ lam M hκ hlam hM2 hM9
  obtain ⟨T, hT0, hT⟩ := hCum N κ lam hκ hlam
  obtain ⟨W, hW0, hW⟩ := hSum N' κ M hκ (by omega)
  have hc0 : ∀ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) → 0 ≤ sizeConstantSum Cq M := fun Cq h => by
    unfold sizeConstantSum
    have : 0 ≤ ∑ q ∈ Finset.range (2 * M + 1), Cq q := Finset.sum_nonneg fun q _ => h q
    linarith
  refine ⟨fun Cq => W * (T * sizeConstantSum Cq M ^ M), fun Cq h =>
    mul_nonneg hW0 (mul_nonneg hT0 (pow_nonneg (hc0 Cq h) _)), ?_⟩
  intro F ι _ _ y ρ x p Ψ K Qa _ za P O e A Cq r₀ n Y₀ i₀ hρ hx hp hy hconv hslope hI hCq hA he
    hr₀ hne hza hanch hC1 hmom hsize hreach
  set Q : Fin M → Type := fun i => {q // P i q} with hQ
  set T₀ : ℝ := T * sizeConstantSum Cq M ^ M with hT₀
  have hT₀0 : 0 ≤ T₀ := mul_nonneg hT0 (pow_nonneg (hc0 Cq hCq) _)
  have hcd : ContinuousOn (ballDensity (cutoffFactor ρ p) Ψ) {η | ∀ b, ‖η b‖ < ρ} := by
    have hΨc : Continuous Ψ := hconv.smooth.continuous
    unfold ballDensity radialWeightProd
    refine ContinuousOn.mul (continuousOn_finsetProd _ fun b _ => ?_)
      (Real.continuous_exp.comp hΨc.neg).continuousOn
    have h1 : ContinuousOn (fun η : BondField ι => Real.exp (-p ‖η b‖)) {η | ∀ b, ‖η b‖ < ρ} := by
      have h2 : ContinuousOn p (Set.Ico 0 ρ) := hp.smooth.continuousOn
      have h3 : ContinuousOn (fun η : BondField ι => p ‖η b‖) {η | ∀ b, ‖η b‖ < ρ} :=
        h2.comp (continuous_norm.comp (continuous_apply b)).continuousOn fun η hη => ⟨norm_nonneg _, hη b⟩
      exact Real.continuous_exp.comp_continuousOn h3.neg
    refine h1.congr fun η hη => ?_
    have h4 : ‖η b‖ < ρ := hη b
    simp [cutoffFactor, h4]
  have key := hW F ι (cutoffFactor ρ p) Ψ Q (fun i q => za q.1) (fun i q => O i q.1)
    (fun i q => e i q.1) A T₀ r₀ n Y₀ hr₀ hT₀0 hA (fun i q => he i q.1)
    (fun i => by
      obtain ⟨q, hq⟩ := hne i
      exact ⟨⟨q, hq⟩⟩)
    (fun i u => by
      refine le_trans ?_ (hza u)
      refine Finset.card_le_card_of_injOn (fun q => q.1) ?_ ?_
      · intro q hq
        simpa using hq
      · intro a _ b _ hab
        exact Subtype.ext hab)
    (fun s J => integrable_finsetProd_mul_ballDensity J (fun l => O l (s l).1)
      (fun l _ => (hC1 l _ (s l).2).continuousOn) (fun l _ m hm => hmom l _ (s l).2 m hm) hI hcd)
    (fun s => by
      have hs := hT F ι (fun b => y b) ρ x p Ψ K hρ hx hp hy hconv hslope M (fun i => O i (s i).1)
        (fun i => za (s i).1) (fun i => A i * Real.exp (-(r₀ * e i (s i).1))) (fun _ => Cq) hM2 hM9
        (fun i => hC1 i _ (s i).2) (fun i => mul_nonneg (hA i) (Real.exp_pos _).le)
        (fun _ q => hCq q) (fun i => hsize i _ (s i).2)
      have h2 := hs.2
      refine h2.trans (le_of_eq ?_)
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hT₀]
      ring)
    (fun s i => by
      have h1 : za (s i₀).1 = Y₀ := hanch _ (s i₀).2
      rw [← h1]
      unfold cellsDiameter
      exact le_trans (Finset.le_sup (f := fun j => cellSupDist (za (s i).1) (za (s j).1)) (Finset.mem_univ i₀))
        (Finset.le_sup (f := fun i' => Finset.univ.sup fun j => cellSupDist (za (s i').1) (za (s j).1))
          (Finset.mem_univ i)))
    (fun s => hreach (fun i => (s i).1) fun i => (s i).2)
  have esum : (fun i η => ∑ q ∈ Finset.univ.filter (P i), O i q η) =
      fun (i : Fin M) (η : BondField ι) => ∑ q : Q i, O i q.1 η := by
    funext i η
    exact Finset.sum_subtype _ (fun q => by simp) _
  rw [esum]
  refine key.trans (le_of_eq ?_)
  simp only [hT₀]
end Cumulants
end YangMills.Construction
end
