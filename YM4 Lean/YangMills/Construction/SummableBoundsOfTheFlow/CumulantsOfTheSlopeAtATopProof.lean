import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfTheMeanOfAPartProof
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfTheMeanAtATopProof
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfTheSlopeAtATop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory BlockAverages ColdStepAtMirrorFrames Estimates LawAtTop
namespace Cumulants
variable {F : BlockFrame}
namespace SlopeAtTop
section Congr
variable {ι : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ}
def InOpenBalls (ρ : ℝ) (η : BondField ι) : Prop := ∀ b, ‖η b‖ < ρ
theorem ballExpectation_congr {u u' : BondField ι → ℝ} (h : ∀ η, InOpenBalls ρ η → u η = u' η) :
    ballExpectation (cutoffFactor ρ p) Φ u = ballExpectation (cutoffFactor ρ p) Φ u' := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.ballExpectation_congr <;> assumption
omit [Fintype ι] in
theorem mul_eq_on_openBalls {u u' v v' : BondField ι → ℝ} (hu : ∀ η, InOpenBalls ρ η → u η = u' η)
    (hv : ∀ η, InOpenBalls ρ η → v η = v' η) : ∀ η, InOpenBalls ρ η → u η * v η = u' η * v' η := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.mul_eq_on_openBalls <;> assumption
variable {f f' g g' h h' l l' : BondField ι → ℝ}
theorem ballCovariance_congr (hf : ∀ η, InOpenBalls ρ η → f η = f' η)
    (hg : ∀ η, InOpenBalls ρ η → g η = g' η) :
    ballCovariance (cutoffFactor ρ p) Φ f g = ballCovariance (cutoffFactor ρ p) Φ f' g' := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.ballCovariance_congr <;> assumption
theorem ballThirdCumulant_congr (hf : ∀ η, InOpenBalls ρ η → f η = f' η)
    (hg : ∀ η, InOpenBalls ρ η → g η = g' η) (hh : ∀ η, InOpenBalls ρ η → h η = h' η) :
    ballThirdCumulant (cutoffFactor ρ p) Φ f g h = ballThirdCumulant (cutoffFactor ρ p) Φ f' g' h' := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.ballThirdCumulant_congr <;> assumption
theorem ballFourthCumulant_congr (hf : ∀ η, InOpenBalls ρ η → f η = f' η)
    (hg : ∀ η, InOpenBalls ρ η → g η = g' η) (hh : ∀ η, InOpenBalls ρ η → h η = h' η)
    (hl : ∀ η, InOpenBalls ρ η → l η = l' η) :
    ballFourthCumulant (cutoffFactor ρ p) Φ f g h l =
      ballFourthCumulant (cutoffFactor ρ p) Φ f' g' h' l' := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.ballFourthCumulant_congr <;> assumption
end Congr
theorem contDiffAt_field_slice {ρ : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    (hG : JointlyContDiffOnBalls ρ V G) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ContDiffAt ℝ k (fun τ : Fin k → ℝ => G η (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0 := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.contDiffAt_slice <;> assumption
theorem fieldDeriv_finset_sum {α : Type} (S : Finset α)
    (G : α → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    {V : F.GaugeField F.top} {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (η : StepVariable (finiteCells F))
    (hG : ∀ a ∈ S, ContDiffAt ℝ k (fun τ : Fin k → ℝ => G a η (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0) :
    fieldDeriv (fun η V' => ∑ a ∈ S, G a η V') V c X η = ∑ a ∈ S, fieldDeriv (G a) V c X η := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.fieldDeriv_sum <;> assumption
end SlopeAtTop
namespace SlopeAtTop
variable {s a ρA x : ℝ} {m : ℕ} {ρ lam κ β : ℝ} {p : ℝ → ℝ} {Cq : ℕ → ℝ} {N N' : ℕ}
  {φ : LocalFamily} {V : F.GaugeField F.top}
open Classical in
theorem sum_slotTerms_eq_fieldDeriv_exponent (hL : InterpolatedLawAtTop s a ρA x m ρ lam κ β p Cq N N' φ V)
    {M : ℕ} (Y : F.Cell) (i₀ i : Fin M) (only : Fin M → Prop) (hi : i ≠ i₀) (ho : ¬ only i) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hk : k ≤ 3) {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ∑ q ∈ Finset.univ.filter (cumulantSlotTerms Y i₀ only i),
        fieldDeriv (interpolatedExponentTerm s a ρA x m φ q) V c X η =
      fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V c X η := by
  have e1 : (interpolatedExponentOfTerms s a ρA x m φ :
      StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) = fun η V' =>
      ∑ q ∈ Finset.univ, interpolatedExponentTerm s a ρA x m φ q η V' := rfl
  rw [e1, fieldDeriv_finset_sum _ (interpolatedExponentTerm s a ρA x m φ) c X η
    (fun q _ => contDiffAt_field_slice (hL.smooth_term q) c X hk hη)]
  have hall : ∀ q ∈ (Finset.univ : Finset (TermPlace F)), cumulantSlotTerms Y i₀ only i q :=
    fun q _ => Or.inr ⟨hi, fun h => absurd h ho⟩
  rw [Finset.filter_true_of_mem hall]
open Classical in
theorem sum_slotTerms_eq_fieldDeriv_cells (hL : InterpolatedLawAtTop s a ρA x m ρ lam κ β p Cq N N' φ V)
    {M : ℕ} (Y : F.Cell) (i₀ i : Fin M) (only : Fin M → Prop) (hi : i ≠ i₀) (ho : only i) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hk : k ≤ 3) {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ∑ q ∈ Finset.univ.filter (cumulantSlotTerms Y i₀ only i),
        fieldDeriv (interpolatedExponentTerm s a ρA x m φ q) V c X η =
      fieldDeriv (interpolatedCellExponent s a ρA x m φ) V c X η := by
  have e1 : (interpolatedCellExponent s a ρA x m φ :
      StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) = fun η V' =>
      ∑ Z ∈ (Finset.univ : Finset ↥(finiteCells F)), interpolatedExponentTerm s a ρA x m φ (Sum.inl Z) η V' := rfl
  rw [e1, fieldDeriv_finset_sum _ (fun Z => interpolatedExponentTerm s a ρA x m φ (Sum.inl Z)) c X η
    (fun Z _ => contDiffAt_field_slice (hL.smooth_term _) c X hk hη)]
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  have z1 : ∀ Z : ↥(finiteCells F), cumulantSlotTerms Y i₀ only i (Sum.inl Z) :=
    fun Z => Or.inr ⟨hi, fun _ => ⟨Z, rfl⟩⟩
  have z2 : ∀ y : ↥(sitesOfCells (finiteCells F) F.depth), ¬ cumulantSlotTerms Y i₀ only i (Sum.inr y) := by
    rintro y (⟨h, -⟩ | ⟨-, h⟩)
    · exact hi h
    · obtain ⟨Z, hZ⟩ := h ho
      simp at hZ
  simp only [z1, z2, if_true, if_false, Finset.sum_const_zero, add_zero]
abbrev BondDirections (F : BlockFrame) : Type :=
  Σ j : ℕ, (Fin j → F.Site F.top × Fin 4) × (Fin j → imaginaryQuaternions)
section FromMoments
variable {ι : Type} [Fintype ι] {r : ℝ → ℝ} {ρ' : ℝ} {p' : ℝ → ℝ} {Φ : BondField ι → ℝ}
theorem abs_ballCovariance_le (hEx : lowOrderCumulantFormulas) {H : Fin 2 → BondField ι → ℝ}
    {f g : BondField ι → ℝ} {R : ℝ} (key : |cumulantFromMoments (cutoffFactor ρ' p') Φ H| ≤ R)
    (h0 : ∀ η, InOpenBalls ρ' η → H 0 η = f η) (h1 : ∀ η, InOpenBalls ρ' η → H 1 η = g η) :
    |ballCovariance (cutoffFactor ρ' p') Φ f g| ≤ R := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.abs_ballCovariance_le_of_cumulant <;> assumption
theorem abs_ballThirdCumulant_le (hEx : lowOrderCumulantFormulas) {H : Fin 3 → BondField ι → ℝ}
    {f g u : BondField ι → ℝ} {R : ℝ} (key : |cumulantFromMoments (cutoffFactor ρ' p') Φ H| ≤ R)
    (h0 : ∀ η, InOpenBalls ρ' η → H 0 η = f η) (h1 : ∀ η, InOpenBalls ρ' η → H 1 η = g η)
    (h2 : ∀ η, InOpenBalls ρ' η → H 2 η = u η) :
    |ballThirdCumulant (cutoffFactor ρ' p') Φ f g u| ≤ R := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.abs_ballThirdCumulant_le_of_cumulant <;> assumption
theorem abs_ballFourthCumulant_le (hEx : lowOrderCumulantFormulas) {H : Fin 4 → BondField ι → ℝ}
    {f g u v : BondField ι → ℝ} {R : ℝ} (key : |cumulantFromMoments (cutoffFactor ρ' p') Φ H| ≤ R)
    (h0 : ∀ η, InOpenBalls ρ' η → H 0 η = f η) (h1 : ∀ η, InOpenBalls ρ' η → H 1 η = g η)
    (h2 : ∀ η, InOpenBalls ρ' η → H 2 η = u η) (h3 : ∀ η, InOpenBalls ρ' η → H 3 η = v η) :
    |ballFourthCumulant (cutoffFactor ρ' p') Φ f g u v| ≤ R := by apply _root_.YangMills.Construction.Cumulants.MeanAtTop.abs_ballFourthCumulant_le_of_cumulant <;> assumption
end FromMoments
end SlopeAtTop
open SlopeAtTop in
theorem slopeCumulantsAtTopBound_of_decay (hCum : slopeCumulantDecay)
    (hEx : lowOrderCumulantFormulas) : slopeCumulantsAtTopBound := by
  classical
  intro N N' κ lam hκ hlam
  obtain ⟨B₂, h₂0, h₂⟩ := hCum N N' κ lam 2 hκ hlam (by norm_num) (by norm_num)
  obtain ⟨B₃, h₃0, h₃⟩ := hCum N N' κ lam 3 hκ hlam (by norm_num) (by norm_num)
  obtain ⟨B₄, h₄0, h₄⟩ := hCum N N' κ lam 4 hκ hlam (by norm_num) (by norm_num)
  refine ⟨fun Cq => B₂ Cq + B₃ Cq + B₄ Cq, fun Cq hq => by
    have := h₂0 Cq hq
    have := h₃0 Cq hq
    have := h₄0 Cq hq
    positivity, ?_⟩
  intro F s a ρA x m ρ α β p Cq φ V hL hα Y Hf hH
  have b₂ := h₂0 Cq hL.Cq_nonneg
  have b₃ := h₃0 Cq hL.Cq_nonneg
  have b₄ := h₄0 Cq hL.Cq_nonneg
  have hβ := hL.β_nonneg
  have hcl : ∀ {η : StepVariable (finiteCells F)}, InOpenBalls ρ η → ∀ b, ‖η b‖ ≤ ρ :=
    fun hη b => (hη b).le
  have p₂ : (∏ i : Fin 2, if i = 0 then α else β) = α * β := by
    simp [Fin.prod_univ_two]
  have p₃ : (∏ i : Fin 3, if i = 0 then α else β) = α * β ^ 2 := by
    simp [Fin.prod_univ_three]
    ring
  have p₄ : (∏ i : Fin 4, if i = 0 then α else β) = α * β ^ 3 := by
    simp [Fin.prod_univ_four]
    ring
  have raise : ∀ {B B' P e : ℝ}, B ≤ B' → 0 ≤ P → 0 ≤ e → B * P * e ≤ B' * P * e := fun hB hP he =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hP) he
  constructor
  · intro j₀ j₁ k c₀ X₀ c₁ X₁ c h0 h1 u0 u1 hcov
    set L : Fin 2 → BondDirections F := ![⟨j₀, c₀, X₀⟩, ⟨j₁, c₁, X₁⟩] with hLdef
    have key := h₂ F s a ρA x m ρ α β p Cq φ V hL hα Y 0 (fun i => (L i).1) (fun i => (L i).2.1)
      (fun i => (L i).2.2) (fun _ => False) k c (fieldDeriv Hf V c₀ X₀) (hH j₀ c₀ X₀ h0 u0)
      (by intro i hi; fin_cases i; exacts [absurd rfl hi, u1])
      (by intro i hi; fin_cases i; exacts [absurd rfl hi, Or.inl h1])
      (by
        intro l
        rcases hcov l with ⟨u, hu⟩ | ⟨u, hu⟩
        · exact ⟨0, u, hu⟩
        · exact ⟨1, u, hu⟩)
    rw [p₂] at key
    refine (abs_ballCovariance_le hEx key (fun η hη => by simp)
      (fun η hη => by
        simp only [if_neg (show (1 : Fin 2) ≠ 0 by decide)]
        exact sum_slotTerms_eq_fieldDeriv_exponent hL Y 0 1 _ (by decide) (by simp) c₁ X₁ (by omega)
          (hcl hη))).trans ?_
    refine raise (by linarith) (by positivity) (Real.exp_pos _).le
  · intro j₀ j₁ k c₀ X₀ c₁ X₁ c h0 h1 u0 u1 hcov
    set L : Fin 2 → BondDirections F := ![⟨j₀, c₀, X₀⟩, ⟨j₁, c₁, X₁⟩] with hLdef
    have key := h₂ F s a ρA x m ρ α β p Cq φ V hL hα Y 0 (fun i => (L i).1) (fun i => (L i).2.1)
      (fun i => (L i).2.2) (fun i => i = 1) k c (fieldDeriv Hf V c₀ X₀) (hH j₀ c₀ X₀ h0 u0)
      (by intro i hi; fin_cases i; exacts [absurd rfl hi, u1])
      (by intro i hi; fin_cases i; exacts [absurd rfl hi, Or.inr ⟨h1, rfl⟩])
      (by
        intro l
        rcases hcov l with ⟨u, hu⟩ | ⟨u, hu⟩
        · exact ⟨0, u, hu⟩
        · exact ⟨1, u, hu⟩)
    rw [p₂] at key
    refine (abs_ballCovariance_le hEx key (fun η hη => by simp)
      (fun η hη => by
        simp only [if_neg (show (1 : Fin 2) ≠ 0 by decide)]
        exact sum_slotTerms_eq_fieldDeriv_cells hL Y 0 1 _ (by decide) rfl c₁ X₁ (by omega)
          (hcl hη))).trans ?_
    refine raise (by linarith) (by positivity) (Real.exp_pos _).le
  · intro j₀ j₁ j₂ k c₀ X₀ c₁ X₁ c₂ X₂ c h0 h1 h2 u0 u1 u2 hcov
    set L : Fin 3 → BondDirections F := ![⟨j₀, c₀, X₀⟩, ⟨j₁, c₁, X₁⟩, ⟨j₂, c₂, X₂⟩] with hLdef
    have key := h₃ F s a ρA x m ρ α β p Cq φ V hL hα Y 0 (fun i => (L i).1) (fun i => (L i).2.1)
      (fun i => (L i).2.2) (fun _ => False) k c (fieldDeriv Hf V c₀ X₀) (hH j₀ c₀ X₀ h0 u0)
      (by intro i hi; fin_cases i; exacts [absurd rfl hi, u1, u2])
      (by intro i hi; fin_cases i; exacts [absurd rfl hi, Or.inl h1, Or.inl h2])
      (by
        intro l
        rcases hcov l with ⟨u, hu⟩ | ⟨u, hu⟩ | ⟨u, hu⟩
        · exact ⟨0, u, hu⟩
        · exact ⟨1, u, hu⟩
        · exact ⟨2, u, hu⟩)
    rw [p₃] at key
    refine (abs_ballThirdCumulant_le hEx key (fun η hη => by simp)
      (fun η hη => by
        simp only [if_neg (show (1 : Fin 3) ≠ 0 by decide)]
        exact sum_slotTerms_eq_fieldDeriv_exponent hL Y 0 1 _ (by decide) (by simp) c₁ X₁ (by omega)
          (hcl hη))
      (fun η hη => by
        simp only [if_neg (show (2 : Fin 3) ≠ 0 by decide)]
        exact sum_slotTerms_eq_fieldDeriv_exponent hL Y 0 2 _ (by decide) (by simp) c₂ X₂ (by omega)
          (hcl hη))).trans ?_
    refine raise (by linarith) (by positivity) (Real.exp_pos _).le
  · intro j₀ j₁ j₂ j₃ k c₀ X₀ c₁ X₁ c₂ X₂ c₃ X₃ c h0 h1 h2 h3 u0 u1 u2 u3 hcov
    set L : Fin 4 → BondDirections F :=
      ![⟨j₀, c₀, X₀⟩, ⟨j₁, c₁, X₁⟩, ⟨j₂, c₂, X₂⟩, ⟨j₃, c₃, X₃⟩] with hLdef
    have key := h₄ F s a ρA x m ρ α β p Cq φ V hL hα Y 0 (fun i => (L i).1) (fun i => (L i).2.1)
      (fun i => (L i).2.2) (fun _ => False) k c (fieldDeriv Hf V c₀ X₀) (hH j₀ c₀ X₀ h0 u0)
      (by intro i hi; fin_cases i; exacts [absurd rfl hi, u1, u2, u3])
      (by intro i hi; fin_cases i; exacts [absurd rfl hi, Or.inl h1, Or.inl h2, Or.inl h3])
      (by
        intro l
        rcases hcov l with ⟨u, hu⟩ | ⟨u, hu⟩ | ⟨u, hu⟩ | ⟨u, hu⟩
        · exact ⟨0, u, hu⟩
        · exact ⟨1, u, hu⟩
        · exact ⟨2, u, hu⟩
        · exact ⟨3, u, hu⟩)
    rw [p₄] at key
    refine (abs_ballFourthCumulant_le hEx key (fun η hη => by simp)
      (fun η hη => by
        simp only [if_neg (show (1 : Fin 4) ≠ 0 by decide)]
        exact sum_slotTerms_eq_fieldDeriv_exponent hL Y 0 1 _ (by decide) (by simp) c₁ X₁ (by omega)
          (hcl hη))
      (fun η hη => by
        simp only [if_neg (show (2 : Fin 4) ≠ 0 by decide)]
        exact sum_slotTerms_eq_fieldDeriv_exponent hL Y 0 2 _ (by decide) (by simp) c₂ X₂ (by omega)
          (hcl hη))
      (fun η hη => by
        simp only [if_neg (show (3 : Fin 4) ≠ 0 by decide)]
        exact sum_slotTerms_eq_fieldDeriv_exponent hL Y 0 3 _ (by decide) (by simp) c₃ X₃ (by omega)
          (hcl hη))).trans ?_
    refine raise (by linarith) (by positivity) (Real.exp_pos _).le
end Cumulants
end YangMills.Construction
end
