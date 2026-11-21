import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfTheMeanOfAPartProof
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfExpansionsAtATop
import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfTheMeanAtATop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory BlockAverages ColdStepAtMirrorFrames
namespace Cumulants
namespace MeanAtTop
variable {F : BlockFrame}
section Congr
variable {ι : Type} [Fintype ι] {ρ : ℝ} {p : ℝ → ℝ} {Φ : BondField ι → ℝ}
def InOpenBalls (ρ : ℝ) (η : BondField ι) : Prop := ∀ b, ‖η b‖ < ρ
theorem ballExpectation_congr {u u' : BondField ι → ℝ} (hu : ∀ η, InOpenBalls ρ η → u η = u' η) :
    ballExpectation (cutoffFactor ρ p) Φ u = ballExpectation (cutoffFactor ρ p) Φ u' := by apply _root_.YangMills.Construction.Interpolation.PartMeanDeriv.ballExpectation_congr <;> assumption
omit [Fintype ι] in
theorem mul_eq_on_openBalls {u u' v v' : BondField ι → ℝ} (hu : ∀ η, InOpenBalls ρ η → u η = u' η)
    (hv : ∀ η, InOpenBalls ρ η → v η = v' η) : ∀ η, InOpenBalls ρ η → u η * v η = u' η * v' η :=
  fun η hη => by rw [hu η hη, hv η hη]
variable {f f' g g' k k' l l' : BondField ι → ℝ}
theorem ballCovariance_congr (hf : ∀ η, InOpenBalls ρ η → f η = f' η)
    (hg : ∀ η, InOpenBalls ρ η → g η = g' η) :
    ballCovariance (cutoffFactor ρ p) Φ f g = ballCovariance (cutoffFactor ρ p) Φ f' g' := by
  unfold ballCovariance
  have e := fun {u u' : BondField ι → ℝ} (hu : ∀ η, InOpenBalls ρ η → u η = u' η) =>
    ballExpectation_congr (ρ := ρ) (p := p) (Φ := Φ) hu
  have fg : ∀ η, InOpenBalls ρ η → f η * g η = f' η * g' η := mul_eq_on_openBalls hf hg
  rw [e fg, e hf, e hg]
theorem ballThirdCumulant_congr (hf : ∀ η, InOpenBalls ρ η → f η = f' η)
    (hg : ∀ η, InOpenBalls ρ η → g η = g' η) (hk : ∀ η, InOpenBalls ρ η → k η = k' η) :
    ballThirdCumulant (cutoffFactor ρ p) Φ f g k = ballThirdCumulant (cutoffFactor ρ p) Φ f' g' k' := by
  unfold ballThirdCumulant
  have e := fun {u u' : BondField ι → ℝ} (hu : ∀ η, InOpenBalls ρ η → u η = u' η) =>
    ballExpectation_congr (ρ := ρ) (p := p) (Φ := Φ) hu
  have fg : ∀ η, InOpenBalls ρ η → f η * g η = f' η * g' η := mul_eq_on_openBalls hf hg
  have fk : ∀ η, InOpenBalls ρ η → f η * k η = f' η * k' η := mul_eq_on_openBalls hf hk
  have gk : ∀ η, InOpenBalls ρ η → g η * k η = g' η * k' η := mul_eq_on_openBalls hg hk
  have fgk : ∀ η, InOpenBalls ρ η → f η * g η * k η = f' η * g' η * k' η :=
    mul_eq_on_openBalls (mul_eq_on_openBalls hf hg) hk
  rw [e fgk, e fg, e fk, e gk, e hf, e hg, e hk]
theorem ballFourthCumulant_congr (hf : ∀ η, InOpenBalls ρ η → f η = f' η)
    (hg : ∀ η, InOpenBalls ρ η → g η = g' η) (hk : ∀ η, InOpenBalls ρ η → k η = k' η)
    (hl : ∀ η, InOpenBalls ρ η → l η = l' η) :
    ballFourthCumulant (cutoffFactor ρ p) Φ f g k l =
      ballFourthCumulant (cutoffFactor ρ p) Φ f' g' k' l' := by
  unfold ballFourthCumulant
  have e := fun {u u' : BondField ι → ℝ} (hu : ∀ η, InOpenBalls ρ η → u η = u' η) =>
    ballExpectation_congr (ρ := ρ) (p := p) (Φ := Φ) hu
  have fg : ∀ η, InOpenBalls ρ η → f η * g η = f' η * g' η := mul_eq_on_openBalls hf hg
  have fk : ∀ η, InOpenBalls ρ η → f η * k η = f' η * k' η := mul_eq_on_openBalls hf hk
  have fl : ∀ η, InOpenBalls ρ η → f η * l η = f' η * l' η := mul_eq_on_openBalls hf hl
  have gk : ∀ η, InOpenBalls ρ η → g η * k η = g' η * k' η := mul_eq_on_openBalls hg hk
  have gl : ∀ η, InOpenBalls ρ η → g η * l η = g' η * l' η := mul_eq_on_openBalls hg hl
  have kl : ∀ η, InOpenBalls ρ η → k η * l η = k' η * l' η := mul_eq_on_openBalls hk hl
  have fgk : ∀ η, InOpenBalls ρ η → f η * g η * k η = f' η * g' η * k' η :=
    mul_eq_on_openBalls (mul_eq_on_openBalls hf hg) hk
  have fgl : ∀ η, InOpenBalls ρ η → f η * g η * l η = f' η * g' η * l' η :=
    mul_eq_on_openBalls (mul_eq_on_openBalls hf hg) hl
  have fkl : ∀ η, InOpenBalls ρ η → f η * k η * l η = f' η * k' η * l' η :=
    mul_eq_on_openBalls (mul_eq_on_openBalls hf hk) hl
  have gkl : ∀ η, InOpenBalls ρ η → g η * k η * l η = g' η * k' η * l' η :=
    mul_eq_on_openBalls (mul_eq_on_openBalls hg hk) hl
  have fgkl : ∀ η, InOpenBalls ρ η → f η * g η * k η * l η = f' η * g' η * k' η * l' η :=
    mul_eq_on_openBalls (mul_eq_on_openBalls (mul_eq_on_openBalls hf hg) hk) hl
  rw [e fgkl, e fgk, e fgl, e fkl, e gkl, e fg, e kl, e fk, e gl, e fl, e gk, e hf, e hg, e hk, e hl]
end Congr
theorem contDiffAt_slice {ρ : ℝ} {V : F.GaugeField F.top}
    {G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ}
    (hG : Estimates.JointlyContDiffOnBalls ρ V G) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ContDiffAt ℝ k
      (fun τ : Fin k → ℝ => G η (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0 := by
  have h3 := hG k c X η hη
  have hemb : ContDiff ℝ 3 (fun τ : Fin k → ℝ => (τ, η)) := contDiff_id.prodMk contDiff_const
  have := ContDiffAt.comp
    (g := fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      G q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V))
    (0 : Fin k → ℝ) h3 hemb.contDiffAt
  exact ContDiffAt.of_le this (by exact_mod_cast hk)
theorem fieldDeriv_sum {α : Type} (S : Finset α)
    (G : α → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    {V : F.GaugeField F.top} {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (η : StepVariable (finiteCells F))
    (hG : ∀ a ∈ S, ContDiffAt ℝ k
      (fun τ : Fin k → ℝ => G a η (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0) :
    Estimates.fieldDeriv (fun η V' => ∑ a ∈ S, G a η V') V c X η =
      ∑ a ∈ S, Estimates.fieldDeriv (G a) V c X η := by
  unfold Estimates.fieldDeriv bondDeriv
  have h := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ)
    (f := fun a (τ : Fin k → ℝ) => G a η (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V))
    (u := S) (x := 0) hG
  have h' : iteratedFDeriv ℝ k
      (fun τ : Fin k → ℝ =>
        ∑ a ∈ S, G a η (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0 =
      ∑ a ∈ S, iteratedFDeriv ℝ k
        (fun τ : Fin k → ℝ => G a η (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0 := h
  rw [h']
  simp
end MeanAtTop
namespace MeanAtTop
variable {F : BlockFrame}
variable {star : Bool} {a ρA x : ℝ} {m : ℕ} {ρ lam κ α β : ℝ} {p : ℝ → ℝ} {Cq : ℕ → ℝ} {N N' : ℕ}
  {φ h : LocalFamily} {V : F.GaugeField F.top}
open Classical in
theorem sum_fieldDeriv_slot_expansion (hL : LawAtTop.LawAtTop star a ρA x m ρ lam κ α β p Cq N N' φ h V)
    {M : ℕ} (Y : F.Cell) (i₀ : Fin M) (only : Fin M → Prop) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3)
    {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ∑ q ∈ Finset.univ.filter (jointSlotPlaces Y i₀ only i₀),
        Estimates.fieldDeriv (jointSlotTerm star a ρA x m φ h i₀ i₀ q) V c X η =
      Estimates.fieldDeriv (cellExpansionInField star a ρA m h Y) V c X η := by
  have e1 : (cellExpansionInField star a ρA m h Y : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) =
      fun η V' => ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
        centredExpansion star a ρA m h y η V' := rfl
  rw [e1, fieldDeriv_sum _ (fun y => centredExpansion star a ρA m h y) c X η (fun y hy => contDiffAt_slice
    (G := LawAtTop.seriesExpansionTerm star a ρA m h (Sum.inr ⟨y, (Finset.mem_filter.mp hy).1⟩))
    (hL.smooth_expansion _) c X hk hη)]
  rw [Finset.sum_filter, Fintype.sum_sum_type, Finset.sum_filter]
  have z1 : ∀ Z : ↥(finiteCells F), ¬ jointSlotPlaces Y i₀ only i₀ (Sum.inl Z) := by
    rintro Z (⟨-, y, hy, -⟩ | ⟨h, -⟩)
    · simp at hy
    · exact h rfl
  have z2 : ∀ y : ↥(sitesOfCells (finiteCells F) F.depth),
      jointSlotPlaces Y i₀ only i₀ (Sum.inr y) ↔ enclosingCell y.1 = Y := by
    intro y
    constructor
    · rintro (⟨-, y', hy, hc⟩ | ⟨h, -⟩)
      · rw [Sum.inr.inj hy]
        exact hc
      · exact absurd rfl h
    · intro hc
      exact Or.inl ⟨rfl, y, rfl, hc⟩
  simp only [z1, if_false, Finset.sum_const_zero, zero_add, z2]
  rw [← Finset.sum_coe_sort (sitesOfCells (finiteCells F) F.depth)
    (fun y => if enclosingCell y = Y then Estimates.fieldDeriv (centredExpansion star a ρA m h y) V c X η else 0)]
  refine Finset.sum_congr rfl fun y _ => ?_
  have e2 : jointSlotTerm star a ρA x m φ h i₀ i₀ (Sum.inr y) = centredExpansion star a ρA m h y.1 := by
    simp only [jointSlotTerm, if_true]
    rfl
  rw [e2]
open Classical in
theorem sum_fieldDeriv_slot_exponent
    (hL : LawAtTop.LawAtTop star a ρA x m ρ lam κ α β p Cq N N' φ h V) {M : ℕ} (Y : F.Cell)
    (i₀ i : Fin M) (only : Fin M → Prop) (hi : i ≠ i₀) (ho : ¬ only i) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hk : k ≤ 3) {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ∑ q ∈ Finset.univ.filter (jointSlotPlaces Y i₀ only i),
        Estimates.fieldDeriv (jointSlotTerm star a ρA x m φ h i₀ i q) V c X η =
      Estimates.fieldDeriv (LawAtTop.exponentSum star a ρA x m φ) V c X η := by
  have e1 : (LawAtTop.exponentSum star a ρA x m φ :
      StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) = fun η V' =>
      ∑ q ∈ Finset.univ, LawAtTop.exponentTerm star a ρA x m φ q η V' := rfl
  rw [e1, fieldDeriv_sum _ (LawAtTop.exponentTerm star a ρA x m φ) c X η (fun q _ => contDiffAt_slice
    (hL.smooth_term q) c X hk hη)]
  have hall : ∀ q ∈ (Finset.univ : Finset (LawAtTop.TermPlace F)), jointSlotPlaces Y i₀ only i q :=
    fun q _ => Or.inr ⟨hi, fun h => absurd h ho⟩
  rw [Finset.filter_true_of_mem hall]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [jointSlotTerm, if_neg hi]
open Classical in
theorem sum_fieldDeriv_slot_cells
    (hL : LawAtTop.LawAtTop star a ρA x m ρ lam κ α β p Cq N N' φ h V) {M : ℕ} (Y : F.Cell)
    (i₀ i : Fin M) (only : Fin M → Prop) (hi : i ≠ i₀) (ho : only i) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hk : k ≤ 3) {η : StepVariable (finiteCells F)} (hη : ∀ b, ‖η b‖ ≤ ρ) :
    ∑ q ∈ Finset.univ.filter (jointSlotPlaces Y i₀ only i),
        Estimates.fieldDeriv (jointSlotTerm star a ρA x m φ h i₀ i q) V c X η =
      Estimates.fieldDeriv (cellExponentTotal star a ρA x m φ) V c X η := by
  have e1 : (cellExponentTotal star a ρA x m φ :
      StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) = fun η V' =>
      ∑ Z ∈ (Finset.univ : Finset ↥(finiteCells F)),
        LawAtTop.exponentTerm star a ρA x m φ (Sum.inl Z) η V' := rfl
  rw [e1, fieldDeriv_sum _ (fun Z => LawAtTop.exponentTerm star a ρA x m φ (Sum.inl Z)) c X η
    (fun Z _ => contDiffAt_slice (hL.smooth_term _) c X hk hη)]
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  have z1 : ∀ Z : ↥(finiteCells F), jointSlotPlaces Y i₀ only i (Sum.inl Z) :=
    fun Z => Or.inr ⟨hi, fun _ => ⟨Z, rfl⟩⟩
  have z2 : ∀ y : ↥(sitesOfCells (finiteCells F) F.depth), ¬ jointSlotPlaces Y i₀ only i (Sum.inr y) := by
    rintro y (⟨h, -⟩ | ⟨-, h⟩)
    · exact hi h
    · obtain ⟨Z, hZ⟩ := h ho
      simp at hZ
  simp only [z1, z2, if_true, if_false, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun Z _ => ?_
  simp only [jointSlotTerm, if_neg hi]
abbrev BondList (F : BlockFrame) : Type :=
  Σ j : ℕ, (Fin j → F.Site F.top × Fin 4) × (Fin j → imaginaryQuaternions)
section FromCumulants
variable {ι : Type} [Fintype ι] {ρ' : ℝ} {p' : ℝ → ℝ} {Φ : BondField ι → ℝ}
theorem abs_ballCovariance_le_of_cumulant (hEx : lowOrderCumulantFormulas)
    {H : Fin 2 → BondField ι → ℝ} {f g : BondField ι → ℝ} {R : ℝ}
    (key : |cumulantFromMoments (cutoffFactor ρ' p') Φ H| ≤ R)
    (h0 : ∀ η, InOpenBalls ρ' η → H 0 η = f η) (h1 : ∀ η, InOpenBalls ρ' η → H 1 η = g η) :
    |ballCovariance (cutoffFactor ρ' p') Φ f g| ≤ R := by
  rw [← ballCovariance_congr h0 h1, ← (hEx ι (cutoffFactor ρ' p') Φ).1 H]
  exact key
theorem abs_ballThirdCumulant_le_of_cumulant (hEx : lowOrderCumulantFormulas)
    {H : Fin 3 → BondField ι → ℝ} {f g u : BondField ι → ℝ} {R : ℝ}
    (key : |cumulantFromMoments (cutoffFactor ρ' p') Φ H| ≤ R)
    (h0 : ∀ η, InOpenBalls ρ' η → H 0 η = f η) (h1 : ∀ η, InOpenBalls ρ' η → H 1 η = g η)
    (h2 : ∀ η, InOpenBalls ρ' η → H 2 η = u η) :
    |ballThirdCumulant (cutoffFactor ρ' p') Φ f g u| ≤ R := by
  rw [← ballThirdCumulant_congr h0 h1 h2, ← (hEx ι (cutoffFactor ρ' p') Φ).2.1 H]
  exact key
theorem abs_ballFourthCumulant_le_of_cumulant (hEx : lowOrderCumulantFormulas)
    {H : Fin 4 → BondField ι → ℝ} {f g u v : BondField ι → ℝ} {R : ℝ}
    (key : |cumulantFromMoments (cutoffFactor ρ' p') Φ H| ≤ R)
    (h0 : ∀ η, InOpenBalls ρ' η → H 0 η = f η) (h1 : ∀ η, InOpenBalls ρ' η → H 1 η = g η)
    (h2 : ∀ η, InOpenBalls ρ' η → H 2 η = u η) (h3 : ∀ η, InOpenBalls ρ' η → H 3 η = v η) :
    |ballFourthCumulant (cutoffFactor ρ' p') Φ f g u v| ≤ R := by
  rw [← ballFourthCumulant_congr h0 h1 h2 h3, ← (hEx ι (cutoffFactor ρ' p') Φ).2.2 H]
  exact key
end FromCumulants
end MeanAtTop
open MeanAtTop in
theorem meanCumulantsAtTop (hCum : expansionExponentCumulantBound)
    (hEx : lowOrderCumulantFormulas) : meanCumulantsAtTopStatement := by
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
  intro F star a ρA x m ρ α β p Cq φ h V hL Y
  have b₂ := h₂0 Cq hL.Cq_nonneg
  have b₃ := h₃0 Cq hL.Cq_nonneg
  have b₄ := h₄0 Cq hL.Cq_nonneg
  have hα := hL.α_nonneg
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
  have raise : ∀ {B B' P e : ℝ}, B ≤ B' → 0 ≤ P → 0 ≤ e → B * P * e ≤ B' * P * e :=
    fun hB hP he => mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hP) he
  constructor
  · intro j₀ j₁ k c₀ X₀ c₁ X₁ c h0 h1 u0 u1 hcov
    set L : Fin 2 → BondList F := ![⟨j₀, c₀, X₀⟩, ⟨j₁, c₁, X₁⟩] with hLdef
    have key := h₂ F star a ρA x m ρ α β p Cq φ h V hL Y 0 (fun i => (L i).1) (fun i => (L i).2.1)
      (fun i => (L i).2.2) (fun _ => False) k c
      (by intro i; fin_cases i; exacts [u0, u1])
      (by intro i; fin_cases i; exacts [Or.inl h0, Or.inl h1])
      (by
        intro l
        rcases hcov l with ⟨u, hu⟩ | ⟨u, hu⟩
        · exact ⟨0, u, hu⟩
        · exact ⟨1, u, hu⟩)
    rw [p₂] at key
    refine (abs_ballCovariance_le_of_cumulant hEx key
      (fun η hη => sum_fieldDeriv_slot_expansion hL Y 0 _ c₀ X₀ (by omega) (hcl hη))
      (fun η hη => sum_fieldDeriv_slot_exponent hL Y 0 1 _ (by decide) (by simp) c₁ X₁ (by omega)
        (hcl hη))).trans ?_
    refine raise (by linarith) (by positivity) (Real.exp_pos _).le
  · intro j₀ j₁ k c₀ X₀ c₁ X₁ c h0 h1 u0 u1 hcov
    set L : Fin 2 → BondList F := ![⟨j₀, c₀, X₀⟩, ⟨j₁, c₁, X₁⟩] with hLdef
    have key := h₂ F star a ρA x m ρ α β p Cq φ h V hL Y 0 (fun i => (L i).1) (fun i => (L i).2.1)
      (fun i => (L i).2.2) (fun i => i = 1) k c
      (by intro i; fin_cases i; exacts [u0, u1])
      (by intro i; fin_cases i; exacts [Or.inl h0, Or.inr ⟨h1, by decide, rfl⟩])
      (by
        intro l
        rcases hcov l with ⟨u, hu⟩ | ⟨u, hu⟩
        · exact ⟨0, u, hu⟩
        · exact ⟨1, u, hu⟩)
    rw [p₂] at key
    refine (abs_ballCovariance_le_of_cumulant hEx key
      (fun η hη => sum_fieldDeriv_slot_expansion hL Y 0 _ c₀ X₀ (by omega) (hcl hη))
      (fun η hη => sum_fieldDeriv_slot_cells hL Y 0 1 _ (by decide) rfl c₁ X₁ (by omega)
        (hcl hη))).trans ?_
    refine raise (by linarith) (by positivity) (Real.exp_pos _).le
  · intro j₀ j₁ j₂ k c₀ X₀ c₁ X₁ c₂ X₂ c h0 h1 h2 u0 u1 u2 hcov
    set L : Fin 3 → BondList F := ![⟨j₀, c₀, X₀⟩, ⟨j₁, c₁, X₁⟩, ⟨j₂, c₂, X₂⟩] with hLdef
    have key := h₃ F star a ρA x m ρ α β p Cq φ h V hL Y 0 (fun i => (L i).1) (fun i => (L i).2.1)
      (fun i => (L i).2.2) (fun _ => False) k c
      (by intro i; fin_cases i; exacts [u0, u1, u2])
      (by intro i; fin_cases i; exacts [Or.inl h0, Or.inl h1, Or.inl h2])
      (by
        intro l
        rcases hcov l with ⟨u, hu⟩ | ⟨u, hu⟩ | ⟨u, hu⟩
        · exact ⟨0, u, hu⟩
        · exact ⟨1, u, hu⟩
        · exact ⟨2, u, hu⟩)
    rw [p₃] at key
    refine (abs_ballThirdCumulant_le_of_cumulant hEx key
      (fun η hη => sum_fieldDeriv_slot_expansion hL Y 0 _ c₀ X₀ (by omega) (hcl hη))
      (fun η hη => sum_fieldDeriv_slot_exponent hL Y 0 1 _ (by decide) (by simp) c₁ X₁ (by omega)
        (hcl hη))
      (fun η hη => sum_fieldDeriv_slot_exponent hL Y 0 2 _ (by decide) (by simp) c₂ X₂ (by omega)
        (hcl hη))).trans ?_
    refine raise (by linarith) (by positivity) (Real.exp_pos _).le
  · intro j₀ j₁ j₂ j₃ k c₀ X₀ c₁ X₁ c₂ X₂ c₃ X₃ c h0 h1 h2 h3 u0 u1 u2 u3 hcov
    set L : Fin 4 → BondList F := ![⟨j₀, c₀, X₀⟩, ⟨j₁, c₁, X₁⟩, ⟨j₂, c₂, X₂⟩, ⟨j₃, c₃, X₃⟩] with hLdef
    have key := h₄ F star a ρA x m ρ α β p Cq φ h V hL Y 0 (fun i => (L i).1) (fun i => (L i).2.1)
      (fun i => (L i).2.2) (fun _ => False) k c
      (by intro i; fin_cases i; exacts [u0, u1, u2, u3])
      (by intro i; fin_cases i; exacts [Or.inl h0, Or.inl h1, Or.inl h2, Or.inl h3])
      (by
        intro l
        rcases hcov l with ⟨u, hu⟩ | ⟨u, hu⟩ | ⟨u, hu⟩ | ⟨u, hu⟩
        · exact ⟨0, u, hu⟩
        · exact ⟨1, u, hu⟩
        · exact ⟨2, u, hu⟩
        · exact ⟨3, u, hu⟩)
    rw [p₄] at key
    refine (abs_ballFourthCumulant_le_of_cumulant hEx key
      (fun η hη => sum_fieldDeriv_slot_expansion hL Y 0 _ c₀ X₀ (by omega) (hcl hη))
      (fun η hη => sum_fieldDeriv_slot_exponent hL Y 0 1 _ (by decide) (by simp) c₁ X₁ (by omega)
        (hcl hη))
      (fun η hη => sum_fieldDeriv_slot_exponent hL Y 0 2 _ (by decide) (by simp) c₂ X₂ (by omega)
        (hcl hη))
      (fun η hη => sum_fieldDeriv_slot_exponent hL Y 0 3 _ (by decide) (by simp) c₃ X₃ (by omega)
        (hcl hη))).trans ?_
    refine raise (by linarith) (by positivity) (Real.exp_pos _).le
end Cumulants
end YangMills.Construction
end
