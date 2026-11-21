import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfATameObservableProof
import YangMills.Construction.SummableBoundsOfTheFlow.ScaledExponentIsTheExponentOfTheStepProof
import YangMills.Construction.SummableBoundsOfTheFlow.SlicesOfASmoothFunction
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansAreTameMeans
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledPartsAreSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames StepDensities SmoothSlices MeasureTheory Set Filter
open scoped Topology
namespace ScaledVariables
namespace TiltedMeans
variable {F : BlockFrame}
abbrev Vars (F : BlockFrame) : Type := StepVariable (finiteCells F)
theorem isOpen_scalesInBalls (ρ lo hi : ℝ) (ζ : Vars F) :
    IsOpen {l : ℝ | lo < l ∧ l < hi ∧ MemScaledBalls ρ l ζ} := by apply _root_.YangMills.Construction.ScaledVariables.TiltedMeanSmoothness.isOpen_admissibleScales <;> assumption
theorem contDiffAt_bondDeriv_scale (hS : IteratedFDerivSlices) {s ρ lo hi D : ℝ}
    {O : ℝ → Vars F → F.GaugeField F.top → ℝ} (hO : IsTameOnScales s ρ lo hi D O) {W : F.GaugeField F.top}
    (hW : IsSmallCurvature s W) {l : ℝ} {ζ : Vars F} (h1 : lo < l) (h2 : l < hi) (h3 : MemScaledBalls ρ l ζ)
    {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hk : k ≤ 3) :
    ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun l' => bondDeriv (O l' ζ) W c X) l := by
  have h6 := hO.contDiffAt W hW l ζ k c X h1 h2 h3
  have hG : ContDiffAt ℝ ((3 + k : ℕ) : WithTop ℕ∞)
      (fun q : (Fin k → ℝ) × ℝ => O q.2 ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) W)) ((0 : Fin k → ℝ), l) := by
    have h7 : ContDiffAt ℝ ((3 + k : ℕ) : WithTop ℕ∞) (fun q : (ℝ × Vars F) × (Fin k → ℝ) =>
        O q.1.1 q.1.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.2) W)) ((l, ζ), (0 : Fin k → ℝ)) :=
      h6.of_le (by exact_mod_cast (show 3 + k ≤ 6 by omega))
    exact ContDiffAt.comp (f := fun q : (Fin k → ℝ) × ℝ => ((q.2, ζ), q.1)) ((0 : Fin k → ℝ), l) h7
      (((contDiff_snd.prodMk contDiff_const).prodMk contDiff_fst).contDiffAt)
  exact hS.2.1 (Fin k → ℝ) ℝ _ k 3 (fun l => Pi.single l 1) l hG
theorem contDiffAt_bondSpread {s ρ lo hi D : ℝ} {O : ℝ → Vars F → F.GaugeField F.top → ℝ}
    (hO : IsTameOnScales s ρ lo hi D O)
    {W : F.GaugeField F.top} (hW : IsSmallCurvature s W) {l : ℝ} {ζ : Vars F} (h1 : lo < l) (h2 : l < hi)
    (h3 : MemScaledBalls ρ l ζ) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hk : k ≤ 3) :
    ContDiffAt ℝ (k : ℕ) (fun τ : Fin k → ℝ => O l ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) W)) 0 := by
  have h6 := hO.contDiffAt W hW l ζ k c X h1 h2 h3
  have h7 := ContDiffAt.comp (f := fun σ : Fin k → ℝ => ((l, ζ), σ)) (0 : Fin k → ℝ) h6
    ((contDiff_const.prodMk contDiff_id).contDiffAt)
  exact h7.of_le (by exact_mod_cast (show k ≤ 6 by omega))
theorem isControlledOrder_le {k i : ℕ} (h : IsControlledOrder k i) : k ≤ 3 ∧ i ≤ 3 := by
  rcases h with h | h <;> omega
theorem isTameOnScales_add (hS : IteratedFDerivSlices) {s ρ lo hi D₁ D₂ : ℝ}
    {O₁ O₂ : ℝ → Vars F → F.GaugeField F.top → ℝ} (h₁ : IsTameOnScales s ρ lo hi D₁ O₁)
    (h₂ : IsTameOnScales s ρ lo hi D₂ O₂) :
    IsTameOnScales s ρ lo hi (D₁ + D₂) fun l ζ A => O₁ l ζ A + O₂ l ζ A := by
  refine ⟨fun W hW l ζ k c X a b d =>
    (h₁.contDiffAt W hW l ζ k c X a b d).add (h₂.contDiffAt W hW l ζ k c X a b d), ?_⟩
  intro W hW k i c X l ζ hr hX a b d
  obtain ⟨hk, hii⟩ := isControlledOrder_le hr
  have ev : (fun l' => bondDeriv (fun A => O₁ l' ζ A + O₂ l' ζ A) W c X) =ᶠ[𝓝 l]
      fun l' => bondDeriv (O₁ l' ζ) W c X + bondDeriv (O₂ l' ζ) W c X := by
    filter_upwards [(isOpen_scalesInBalls ρ lo hi ζ).mem_nhds ⟨a, b, d⟩] with l' hl'
    unfold bondDeriv
    have e : (fun τ : Fin k → ℝ => O₁ l' ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) W) +
          O₂ l' ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) W)) =
        (fun τ : Fin k → ℝ => O₁ l' ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) W)) +
          fun τ : Fin k → ℝ => O₂ l' ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) W) := rfl
    rw [e, iteratedFDeriv_add_apply (contDiffAt_bondSpread h₁ hW hl'.1 hl'.2.1 hl'.2.2 c X hk)
      (contDiffAt_bondSpread h₂ hW hl'.1 hl'.2.1 hl'.2.2 c X hk)]
    rfl
  have e1 : scaleDeriv (fun l ζ A => O₁ l ζ A + O₂ l ζ A) W c X i ζ l =
      iteratedDeriv i (fun l' => bondDeriv (O₁ l' ζ) W c X + bondDeriv (O₂ l' ζ) W c X) l :=
    (Filter.EventuallyEq.iteratedDeriv ev i).self_of_nhds
  have c₁ := (contDiffAt_bondDeriv_scale hS h₁ hW a b d c X hk).of_le
    (by exact_mod_cast hii : ((i : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞))
  have c₂ := (contDiffAt_bondDeriv_scale hS h₂ hW a b d c X hk).of_le
    (by exact_mod_cast hii : ((i : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞))
  have e2 := iteratedDeriv_add (n := i) (x := l) c₁ c₂
  have e3 : iteratedDeriv i (fun l' => bondDeriv (O₁ l' ζ) W c X + bondDeriv (O₂ l' ζ) W c X) l = _ := e2
  rw [e1, e3]
  exact (abs_add_le _ _).trans (add_le_add (h₁.deriv_le W hW k i c X l ζ hr hX a b d)
    (h₂.deriv_le W hW k i c X l ζ hr hX a b d))
theorem isTameOnScales_const_mul (hS : IteratedFDerivSlices) {s ρ lo hi D : ℝ} (u : ℝ)
    {O : ℝ → Vars F → F.GaugeField F.top → ℝ} (h : IsTameOnScales s ρ lo hi D O) :
    IsTameOnScales s ρ lo hi (|u| * D) fun l ζ A => u * O l ζ A := by
  refine ⟨fun W hW l ζ k c X a b d => contDiffAt_const.mul (h.contDiffAt W hW l ζ k c X a b d), ?_⟩
  intro W hW k i c X l ζ hr hX a b d
  obtain ⟨hk, hii⟩ := isControlledOrder_le hr
  have ev : (fun l' => bondDeriv (fun A => u * O l' ζ A) W c X) =ᶠ[𝓝 l]
      fun l' => u * bondDeriv (O l' ζ) W c X := by
    filter_upwards [(isOpen_scalesInBalls ρ lo hi ζ).mem_nhds ⟨a, b, d⟩] with l' hl'
    unfold bondDeriv
    have e := iteratedFDeriv_const_smul_apply' (a := u)
      (contDiffAt_bondSpread h hW hl'.1 hl'.2.1 hl'.2.2 c X hk)
    have e' : iteratedFDeriv ℝ k
          (fun τ : Fin k → ℝ => u * O l' ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) W)) 0 =
        u • iteratedFDeriv ℝ k
          (fun τ : Fin k → ℝ => O l' ζ (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) W)) 0 := e
    rw [e']
    rfl
  have e1 : scaleDeriv (fun l ζ A => u * O l ζ A) W c X i ζ l =
      iteratedDeriv i (fun l' => u * bondDeriv (O l' ζ) W c X) l :=
    (Filter.EventuallyEq.iteratedDeriv ev i).self_of_nhds
  have c₁ := (contDiffAt_bondDeriv_scale hS h hW a b d c X hk).of_le
    (by exact_mod_cast hii : ((i : ℕ) : WithTop ℕ∞) ≤ ((3 : ℕ) : WithTop ℕ∞))
  rw [e1, iteratedDeriv_const_mul u c₁, abs_mul]
  exact mul_le_mul_of_nonneg_left (h.deriv_le W hW k i c X l ζ hr hX a b d) (abs_nonneg _)
theorem isTameOnScales_zero {s ρ lo hi : ℝ} :
    IsTameOnScales (F := F) s ρ lo hi 0 fun _ _ _ => 0 := by
  refine ⟨fun W hW l ζ k c X a b d => contDiffAt_const, ?_⟩
  intro W hW k i c X l ζ hr hX a b d
  have e : (fun l' : ℝ => bondDeriv (fun _ : F.GaugeField F.top => (0 : ℝ)) W c X) = fun _ => 0 := by
    funext l'
    simp [bondDeriv]
  simp only [scaleDeriv, e]
  simp
theorem isTameOnScales_sum (hS : IteratedFDerivSlices) {s ρ lo hi D : ℝ} {ι : Type} (t : Finset ι)
    {O : ι → ℝ → Vars F → F.GaugeField F.top → ℝ} (h : ∀ i ∈ t, IsTameOnScales s ρ lo hi D (O i)) :
    IsTameOnScales s ρ lo hi (t.card * D) fun l ζ A => ∑ i ∈ t, O i l ζ A := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isTameOnScales_zero
  | insert i t hi ih =>
    have h1 := isTameOnScales_add hS (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    have e : (t.card + 1 : ℝ) * D = D + t.card * D := by ring
    simp only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, e]
    exact h1
theorem isTameOnScales_of_smooth {s κ ρ lo l₂ K : ℝ} {Y : F.Cell} {O : ℝ → Vars F → F.GaugeField F.top → ℝ}
    (hκ : 0 < κ) (hlo : 0 < lo) (hK : 0 ≤ K) (h : IsSmoothAtSmallCurvature s κ ρ l₂ K Y O) :
    IsTameOnScales s ρ lo l₂ (K * (1 + (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) * (ρ / lo)) ^ 7) O := by
  refine ⟨fun W hW l ζ k c X a _ d => ?_, ?_⟩
  · refine (h W hW).contDiffAt l ζ k c X ?_
    rwa [abs_of_pos (hlo.trans a)]
  · intro W hW k i c X l ζ hr hX a b d
    have hl : 0 < l := hlo.trans a
    refine ((h W hW).deriv_le k i c X l ζ hr hX hl b.le d).trans ?_
    have hN0 : 0 ≤ localWeight κ Y ζ := Finset.sum_nonneg fun b _ => by positivity
    have hN : localWeight κ Y ζ ≤ (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) * (ρ / lo) := by
      unfold localWeight
      have hb : ∀ b : ↥(chordBonds (finiteCells F)),
          Real.exp (-(2 ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y)) * ‖ζ b‖ ≤ ρ / lo := by
        intro b
        have h1 : Real.exp (-(2 ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y)) ≤ 1 :=
          Real.exp_le_one_iff.2 (by
            have : 0 ≤ (2 : ℝ) ^ 4 * κ * cellSupDist (enclosingCell b.1.1) Y := by positivity
            linarith)
        have h2 : ‖ζ b‖ ≤ ρ / lo := by
          rw [le_div_iff₀ hlo]
          have h3 := d b
          have h4 : lo * ‖ζ b‖ ≤ l * ‖ζ b‖ := mul_le_mul_of_nonneg_right a.le (norm_nonneg _)
          linarith
        calc _ ≤ 1 * ‖ζ b‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ ≤ ρ / lo := by simpa using h2
      calc _ ≤ ∑ _b : ↥(chordBonds (finiteCells F)), ρ / lo := Finset.sum_le_sum fun b _ => hb b
        _ = _ := by simp
    have hE : Real.exp (-(2 ^ 4 * κ * bondSpan Y c)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by
        have : 0 ≤ (2 : ℝ) ^ 4 * κ * bondSpan Y c := by positivity
        linarith)
    have hP : (1 + localWeight κ Y ζ) ^ 7 ≤
        (1 + (Fintype.card ↥(chordBonds (finiteCells F)) : ℝ) * (ρ / lo)) ^ 7 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 7
    calc _ ≤ K * (1 + localWeight κ Y ζ) ^ 7 * 1 :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ _ := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hP hK
theorem finite_cell (hF : ∀ i, F.extent i ≠ 0) : Finite F.Cell := by
  have h : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by simp [BlockFrame.period, hF i]⟩
  exact Pi.finite
theorem mem_finiteCells (hF : ∀ i, F.extent i ≠ 0) (Y : F.Cell) : Y ∈ finiteCells F := by apply _root_.YangMills.SharedProofs.p16107 <;> assumption
theorem sum_rescaledCellRemainder (hF : ∀ i, F.extent i ≠ 0) (a ρ lam l : ℝ) (A : F.GaugeField F.top)
    (ζ : Vars F) :
    ∑ Y ∈ finiteCells F, rescaledCellRemainder a ρ lam l Y A ζ =
      (∑ Y ∈ finiteCells F, rescaledCellTerm a ρ l Y A ζ) - gaussianPart lam ζ := by
  classical
  unfold rescaledCellRemainder gaussianPart
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm]
  congr 2
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq, if_pos (_root_.YangMills.Construction.ScaledVariables.TiltedMeans.mem_finiteCells hF _)]
theorem sum_rescaledCellExpansion (hF : ∀ i, F.extent i ≠ 0) (a ρ : ℝ) (f : LocalFamily) (l : ℝ)
    (A : F.GaugeField F.top) (ζ : Vars F) :
    ∑ Y ∈ finiteCells F, rescaledCellExpansion a ρ f l Y A ζ =
      ∑ y ∈ sitesOfCells (finiteCells F) F.depth, centredExpansion true a ρ 0 f y (l • ζ) A := by
  classical
  unfold rescaledCellExpansion cellCentredExpansion
  exact Finset.sum_fiberwise_of_maps_to (fun y _ => _root_.YangMills.Construction.ScaledVariables.TiltedMeans.mem_finiteCells hF _) _
theorem stepLawExponent_smul (hF : ∀ i, F.extent i ≠ 0) {a ρ lam l : ℝ} {f : LocalFamily}
    {A : F.GaugeField F.top} {ζ : Vars F} (law : StepLaw) (hl : 0 < l)
    (hE : ∀ ν : ℝ, stepExponent true a ρ (l⁻¹ ^ 2) 0 f ν A (l • ζ) = rescaledExponent a ρ f ν l A ζ) :
    stepLawExponent a ρ lam (l⁻¹ ^ 2) f A law (l • ζ) =
      gaussianPart lam ζ - lawExponent a ρ lam f law l ζ A := by
  cases law with
  | tilted ν =>
    simp only [stepLawExponent, hE, rescaledExponent, lawExponent, remainderCoefficient, expansionCoefficient]
    rw [sum_rescaledCellRemainder hF a ρ lam l A ζ, sum_rescaledCellExpansion hF]
    ring
  | interpolated τ =>
    have hsq : totalQuadratic lam (l⁻¹ ^ 2) (l • ζ) = gaussianPart lam ζ := by
      unfold totalQuadratic gaussianPart
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hl.le]
      field_simp
    simp only [stepLawExponent, hE, rescaledExponent, lawExponent, remainderCoefficient, expansionCoefficient, hsq]
    rw [sum_rescaledCellRemainder hF a ρ lam l A ζ]
    ring
theorem cutoffWeight_smul {ρ l : ℝ} {p : ℝ → ℝ} (hl : 0 < l) (ζ : Vars F) :
    ColdStepAtMirrorFrames.cutoffWeight ρ p (l • ζ) = scaledCutoff (ScaledVariables.cutoffWeight ρ p) l ζ := by
  unfold ColdStepAtMirrorFrames.cutoffWeight scaledCutoff ScaledVariables.cutoffWeight
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hl.le,
    max_eq_left (mul_nonneg hl.le (norm_nonneg _))]
theorem scaledCutoff_eq_zero {ρ l : ℝ} {p : ℝ → ℝ} {ζ : Vars F} (hζ : ¬ MemScaledBalls ρ l ζ) :
    scaledCutoff (ScaledVariables.cutoffWeight ρ p) l ζ = 0 := by
  unfold MemScaledBalls at hζ
  simp only [not_forall, not_lt] at hζ
  obtain ⟨b, hb⟩ := hζ
  unfold scaledCutoff
  refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
  unfold ScaledVariables.cutoffWeight cutoffFactor
  rw [if_neg (not_lt.2 (hb.trans (le_max_left _ _)))]
theorem integral_div_integral_smul {l : ℝ} (hl : 0 < l) (g₁ g₂ : Vars F → ℝ) :
    (∫ η, g₁ η) / ∫ η, g₂ η = (∫ ζ, g₁ (l • ζ)) / ∫ ζ, g₂ (l • ζ) := by
  rw [Measure.integral_comp_smul, Measure.integral_comp_smul]
  set c : ℝ := |(l ^ Module.finrank ℝ (Vars F))⁻¹| with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact abs_ne_zero.2 (inv_ne_zero (pow_ne_zero _ hl.ne'))
  simp only [smul_eq_mul]
  rw [mul_div_mul_left _ _ hc0]
end TiltedMeans
open TiltedMeans in
theorem scaledMeansTameStatement_holds (hE : RescaledExponentAgrees)
    (hP : rescaledPartsSmoothStatement) (hS : IteratedFDerivSlices) :
    scaledMeansTameStatement := by
  refine EventuallyOrdered.mono (EventuallyOrdered.and hP hE) ?_
  rintro T hT hn ⟨gP, gE⟩ e
  obtain ⟨lP, K, hlP, hK, gP⟩ := gP e
  obtain ⟨lE, hlE, gE⟩ := gE
  refine ⟨min lP lE / 2, by positivity, fun l₁ h0 hle t f F law hf hF => ?_⟩
  have h2P : 2 * l₁ ≤ lP := by
    have := min_le_left lP lE
    linarith
  have h2E : 2 * l₁ ≤ lE := by
    have := min_le_right lP lE
    linarith
  have hside : ∀ i, F.extent i ≠ 0 := by
    obtain ⟨-, -, m, hm, hm₀⟩ := hF
    intro i
    rw [hm i]
    omega
  have hκ : 0 < T.κ := hT.κ_pos
  have hρ : 0 < T.ballRadius := by
    have := hT.σ_pos
    unfold StepParameters.ballRadius
    positivity
  refine ⟨fun lo hlo => ?_, fun K' Y Ob hK' h lo hlo => ⟨_, by positivity, isTameOnScales_of_smooth hκ hlo hK' h⟩,
    fun A l Ob hA h1 h2 => ?_⟩
  · have hb := fun Y : F.Cell => isTameOnScales_of_smooth (Y := Y)
      (O := fun l ζ A' => rescaledCellRemainder T.a T.ρA T.lam l Y A' ζ)
      (l₂ := 2 * l₁) hκ hlo hK
      (fun A' hA' => (gP (2 * l₁) (by positivity) h2P t f F A' Y hf hF hA').1)
    have hr := fun Y : F.Cell => isTameOnScales_of_smooth (Y := Y)
      (O := fun l ζ A' => rescaledCellExpansion T.a T.ρA f l Y A' ζ)
      (l₂ := 2 * l₁) hκ hlo hK
      (fun A' hA' => (gP (2 * l₁) (by positivity) h2P t f F A' Y hf hF hA').2)
    have sB := isTameOnScales_sum hS (finiteCells F) fun Y _ => hb Y
    have sR := isTameOnScales_sum hS (finiteCells F) fun Y _ => hr Y
    exact ⟨_, by positivity, isTameOnScales_add hS (isTameOnScales_const_mul hS (-remainderCoefficient law) sB)
      (isTameOnScales_const_mul hS (expansionCoefficient law) sR)⟩
  · have hl2 : l ≤ lE := h2.trans h2E
    have hw : ∀ ζ : Vars F, ColdStepAtMirrorFrames.cutoffWeight T.ballRadius T.p (l • ζ) *
        Real.exp (-stepLawExponent T.a T.ρA T.lam (l⁻¹ ^ 2) f A law (l • ζ)) =
        tiltedWeight (ScaledVariables.cutoffWeight T.ballRadius T.p) (gaussianPart T.lam)
          (lawExponent T.a T.ρA T.lam f law) l A ζ := by
      intro ζ
      rw [cutoffWeight_smul h1]
      unfold tiltedWeight
      by_cases hζ : MemScaledBalls T.ballRadius l ζ
      · rw [stepLawExponent_smul hside law h1 fun ν => (gE t F A f ν l 0 ζ hF hA h1 hl2 hζ).1, neg_sub,
          sub_eq_add_neg, Real.exp_add]
        ring
      · rw [scaledCutoff_eq_zero hζ]
        ring
    unfold observableMean rescaledMean cutoffMean tiltedMean tiltedAverage
    rw [integral_div_integral_smul h1]
    congr 1
    · refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
      change Ob l (l⁻¹ • l • ζ) A * (ColdStepAtMirrorFrames.cutoffWeight T.ballRadius T.p (l • ζ) *
        Real.exp (-stepLawExponent T.a T.ρA T.lam (l⁻¹ ^ 2) f A law (l • ζ))) = _
      rw [hw ζ, smul_smul, inv_mul_cancel₀ h1.ne', one_smul]
    · exact integral_congr_ae (Eventually.of_forall hw)
end ScaledVariables
end YangMills.Construction
end
