import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfSizedSumsProof
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsWithOneUnboundedSum
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation ConvexObservables
namespace Cumulants
variable {ι : Type} [Fintype ι]
theorem ballDensity_cutoff_eq_zero_of_not_mem {ρ : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ} {η : BondField ι}
    (h : ¬ ∀ b, ‖η b‖ < ρ) : ballDensity (cutoffFactor ρ p) Φ η = 0 := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.ballDensity_eq_zero_of_not_mem <;> assumption
theorem ballDensity_congr_of_eqOn_balls {ρ : ℝ} {p : ℝ → ℝ} {Ψ Φ : BondField ι → ℝ}
    (hΦΨ : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Φ η = Ψ η) :
    ballDensity (cutoffFactor ρ p) Φ = ballDensity (cutoffFactor ρ p) Ψ := by apply _root_.YangMills.Construction.Cumulants.SizedSums.ballDensity_congr <;> assumption
theorem cumulantFromMoments_congr {r : ℝ → ℝ} {Ψ Φ : BondField ι → ℝ}
    (hdens : ballDensity r Φ = ballDensity r Ψ) {M : ℕ} (H : Fin M → BondField ι → ℝ) :
    cumulantFromMoments r Φ H = cumulantFromMoments r Ψ H := by
  simp only [cumulantFromMoments, ballExpectation, hdens]
variable [DecidableEq ι]
theorem hasLocalSize_congr {ρ x κ h : ℝ} {r : ℝ → ℝ} {Ψ Φ : BondField ι → ℝ} {Cq : ℕ → ℝ} {dZ : ι → ℝ}
    {H : BondField ι → ℝ} (hd : ballDensity r Φ = ballDensity r Ψ)
    (hs : HasLocalSize ρ r Φ Cq x κ h dZ H) : HasLocalSize ρ r Ψ Cq x κ h dZ H := by
  simpa only [HasLocalSize, MomentBound, ballExpectation, hd] using hs
theorem integrable_prod_mul_ballDensity {ρ : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ} {α : Type} (J : Finset α)
    (f : α → BondField ι → ℝ) (hc : ∀ l ∈ J, ContinuousOn (f l) {η | ∀ b, ‖η b‖ < ρ})
    (hb : ∀ l ∈ J, ∃ D : ℝ, ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |f l η| ≤ D)
    (hI : Integrable (ballDensity (cutoffFactor ρ p) Φ)) :
    Integrable fun η => (∏ l ∈ J, f l η) * ballDensity (cutoffFactor ρ p) Φ η := by apply _root_.YangMills.Construction.Cumulants.SizedSums.integrable_prod_mul_ballDensity <;> assumption
theorem integrable_prod_mul_ballDensity_of_one {ρ : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ} {α : Type}
    [DecidableEq α]
    (J : Finset α) (a : α) (f : α → BondField ι → ℝ)
    (hc : ∀ l ∈ J, l ≠ a → ContinuousOn (f l) {η | ∀ b, ‖η b‖ < ρ})
    (hb : ∀ l ∈ J, l ≠ a → ∃ D : ℝ, ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |f l η| ≤ D)
    (hI : Integrable (ballDensity (cutoffFactor ρ p) Φ))
    (hI₀ : Integrable fun η => f a η * ballDensity (cutoffFactor ρ p) Φ η) :
    Integrable fun η => (∏ l ∈ J, f l η) * ballDensity (cutoffFactor ρ p) Φ η := by
  classical
  by_cases haJ : a ∈ J
  · set U : Set (BondField ι) := {η | ∀ b, ‖η b‖ < ρ} with hU
    have hUo : IsOpen U := by
      have : U = ⋂ b, {η : BondField ι | ‖η b‖ < ρ} := by
        ext η
        simp [hU]
      rw [this]
      exact isOpen_iInter_of_finite fun b => isOpen_lt (continuous_apply b).norm continuous_const
    have hcont : ContinuousOn (fun η => ∏ l ∈ J.erase a, f l η) U :=
      continuousOn_finset_prod _ fun l hl => hc l (Finset.mem_of_mem_erase hl) (Finset.ne_of_mem_erase hl)
    choose! D hD using fun l (hl : l ∈ J.erase a) =>
      hb l (Finset.mem_of_mem_erase hl) (Finset.ne_of_mem_erase hl)
    set g : BondField ι → ℝ := U.indicator fun η => ∏ l ∈ J.erase a, f l η with hg
    have hgm : AEStronglyMeasurable g volume :=
      (aestronglyMeasurable_indicator_iff hUo.measurableSet).mpr
        (hcont.aestronglyMeasurable hUo.measurableSet)
    have hgb : ∀ η, ‖g η‖ ≤ ∏ l ∈ J.erase a, |D l| := fun η => by
      by_cases hη : η ∈ U
      · rw [hg, Set.indicator_of_mem hη, Real.norm_eq_abs, Finset.abs_prod]
        exact Finset.prod_le_prod (fun l _ => abs_nonneg _) fun l hl =>
          (hD l hl η hη).trans (le_abs_self _)
      · rw [hg, Set.indicator_of_notMem hη, norm_zero]
        exact Finset.prod_nonneg fun l _ => abs_nonneg _
    have hmul := hI₀.bdd_mul hgm (Filter.Eventually.of_forall hgb)
    refine hmul.congr (Filter.Eventually.of_forall fun η => ?_)
    by_cases hη : η ∈ U
    · simp only [hg, Set.indicator_of_mem hη]
      rw [← Finset.mul_prod_erase J (fun l => f l η) haJ]
      ring
    · have h0 : ¬ ∀ b, ‖η b‖ < ρ := hη
      simp only [hg, Set.indicator_of_notMem hη, ballDensity_cutoff_eq_zero_of_not_mem h0, mul_zero]
  · exact integrable_prod_mul_ballDensity J f (fun l hl => hc l hl fun h => haJ (h ▸ hl))
      (fun l hl => hb l hl fun h => haJ (h ▸ hl)) hI
theorem cumulantDecayBoundOneUnbounded_holds (hCum : cumulantDecayBound)
    (hSum : placeSummedCumulantBound) : cumulantDecayBoundOneUnbounded := by
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
  intro F ι _ _ y ρ x p Ψ Φ K Qa _ za P O e A Cq r₀ n Y₀ i₀ hρ hx hp hy hconv hslope hagree hI hCq hA he
    hr₀ hne hza hanch hC1 hbd hI₀ hsize hreach
  have hd : ballDensity (cutoffFactor ρ p) Φ = ballDensity (cutoffFactor ρ p) Ψ :=
    ballDensity_congr_of_eqOn_balls hagree
  set Q : Fin M → Type := fun i => {q // P i q} with hQ
  set T₀ : ℝ := T * sizeConstantSum Cq M ^ M with hT₀
  have hT₀0 : 0 ≤ T₀ := mul_nonneg hT0 (pow_nonneg (hc0 Cq hCq) _)
  have key := hW F ι (cutoffFactor ρ p) Φ Q (fun i q => za q.1) (fun i q => O i q.1)
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
    (fun s J => integrable_prod_mul_ballDensity_of_one J i₀ (fun l => O l (s l).1)
      (fun l _ _ => (hC1 l _ (s l).2).continuousOn) (fun l _ hl => hbd l _ hl (s l).2) hI
      (hI₀ _ (s i₀).2))
    (fun s => by
      have hs := hT F ι (fun b => y b) ρ x p Ψ K hρ hx hp hy hconv hslope M (fun i => O i (s i).1)
        (fun i => za (s i).1) (fun i => A i * Real.exp (-(r₀ * e i (s i).1))) (fun _ => Cq) hM2 hM9
        (fun i => hC1 i _ (s i).2) (fun i => mul_nonneg (hA i) (Real.exp_pos _).le)
        (fun _ q => hCq q) (fun i => hasLocalSize_congr hd (hsize i _ (s i).2))
      have h2 := hs.2
      rw [cumulantFromMoments_congr hd]
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
