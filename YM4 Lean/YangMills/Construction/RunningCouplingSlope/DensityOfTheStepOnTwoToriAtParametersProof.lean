import YangMills.Construction.ClusterExpansionOfAStep.ThreeFactsOfAnExpansionProof
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfADensityAtConstantCurvatureProof
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsAnalyticAtParameters
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepOnTwoToriAtParameters
import YangMills.Construction.RunningCouplingSlope.DerivativesOfTheDensityOfTheStepDecayAtParameters
import YangMills.Construction.RunningCouplingSlope.ValueOfTheDensityOfTheStepOnTwoToriAtParameters
import YangMills.Construction.SummableBoundsOfTheFlow.LinesOfTwoTops
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps RenormalizationStepParameters ReferenceDensity
open DerivativeInterpolation FrameTorusAction StepDensity
namespace RunningCouplingSlope
namespace TorusComparison
section Transfer
variable {F : BlockFrame} {m j : ℕ}
def torusBondOfBond (m : ℕ) (c : F.Site j × Fin 4) : TorusBond m := (toTorusSite m c.1, c.2)
def bondOfTorusBond (j : ℕ) (c : TorusBond m) : F.Site j × Fin 4 := (siteOfTorusSite j c.1, c.2)
theorem toTorusSite_injective (hp : ∀ i, F.period j i = m) :
    Function.Injective (toTorusSite m : F.Site j → TorusSite m) := fun x y h => by
  rw [← siteOfTorusSite_toTorusSite hp x, h, siteOfTorusSite_toTorusSite hp y]
theorem toTorusSite_siteOfCoords (hp : ∀ i, F.period j i = m) (z : Fin 4 → ℤ) :
    toTorusSite m (siteOfCoords (F := F) j z) = siteOfInt z :=
  funext fun k => intCast_cast_intCast (hp k) (z k)
theorem bondSpread_siteOfTorusSite (hp : ∀ i, F.period j i = m) {k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) (x : TorusSite m) (i : Fin 4) :
    bondSpread c X τ (siteOfTorusSite j x) i =
      ∑ l, if torusBondOfBond m (c l) = (x, i) then τ l • X l else 0 := by
  unfold ColdStepAtMirrorFrames.bondSpread
  refine Finset.sum_congr rfl fun l _ => ?_
  have hiff : c l = (siteOfTorusSite j x, i) ↔ torusBondOfBond m (c l) = (x, i) := by
    constructor
    · intro h
      rw [torusBondOfBond, h]
      simp [toTorusSite_siteOfTorusSite hp]
    · intro h
      have h1 : toTorusSite m (c l).1 = x := congrArg Prod.fst h
      have h2 : (c l).2 = i := congrArg Prod.snd h
      refine Prod.ext ?_ h2
      rw [← h1, siteOfTorusSite_toTorusSite hp]
  simp only [hiff]
theorem restrictToTorus_leftTranslate (hp : ∀ i, F.period j i = m) {k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) (W : F.GaugeField j) :
    restrictToTorus m (leftTranslate (bondSpread c X τ) W) =
      perturb (fun l => torusBondOfBond m (c l)) X τ (restrictToTorus m W) := by
  funext x i
  show expUnit (bondSpread c X τ (siteOfTorusSite j x) i) * W (siteOfTorusSite j x) i = _
  rw [bondSpread_siteOfTorusSite hp]
  rfl
theorem readAtLevel_restrictToTorus (hp : ∀ i, F.period j i = m) (W : F.GaugeField j) :
    readAtLevel F j (restrictToTorus m W) = W := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.readAtLevel_restrictToTorus <;> assumption
theorem restrictToTorus_readAtLevel (hp : ∀ i, F.period j i = m) (V : TorusField m) :
    restrictToTorus m (readAtLevel F j V) = V := by
  funext x i
  show V (toTorusSite m (siteOfTorusSite (F := F) j x)) i = V x i
  rw [toTorusSite_siteOfTorusSite hp]
theorem isSmallCurvature_readAtLevel (hp : ∀ i, F.period j i = m) {s : ℝ} {V : TorusField m}
    (h : IsCold s V) : IsSmallCurvature s (readAtLevel F j V) := by
  rintro ⟨y, μ, ν⟩ hμν
  unfold plaquetteDefect
  rw [plaquetteHolonomy_eq_holonomy hp, restrictToTorus_readAtLevel hp]
  exact h _ μ ν hμν
theorem bondDeriv_eq_mixedDeriv (hp : ∀ i, F.period j i = m) {G : F.GaugeField j → ℝ}
    {G' : TorusField m → ℝ} (hG : ∀ W, G W = G' (restrictToTorus m W)) {k : ℕ} (W : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv G W c X = mixedDeriv G' (restrictToTorus m W) (fun l => torusBondOfBond m (c l)) X := by
  unfold bondDeriv mixedDeriv
  congr 2
  funext τ
  rw [hG, restrictToTorus_leftTranslate hp]
theorem torusBondOfBond_bondOfTorusBond (hp : ∀ i, F.period j i = m) (c : TorusBond m) :
    torusBondOfBond (F := F) (j := j) m (bondOfTorusBond j c) = c :=
  Prod.ext (toTorusSite_siteOfTorusSite hp c.1) rfl
theorem mixedDeriv_eq_bondDeriv (hp : ∀ i, F.period j i = m) {G : F.GaugeField j → ℝ}
    {G' : TorusField m → ℝ} (hG : ∀ V, G' V = G (readAtLevel F j V)) {k : ℕ} (V : TorusField m)
    (c : Fin k → TorusBond m) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv G' V c X = bondDeriv G (readAtLevel F j V) (fun l => bondOfTorusBond j (c l)) X := by
  have h := bondDeriv_eq_mixedDeriv (G := G) (G' := G') hp
    (fun W => by rw [hG, readAtLevel_restrictToTorus hp])
    (readAtLevel F j V) (fun l => bondOfTorusBond j (c l)) X
  rw [h, restrictToTorus_readAtLevel hp]
  simp only [torusBondOfBond_bondOfTorusBond hp]
end Transfer
theorem mixedDeriv_zero {n : ℕ} (G : TorusField n → ℝ) (W : TorusField n) (c : Fin 0 → TorusBond n)
    (X : Fin 0 → imaginaryQuaternions) : mixedDeriv G W c X = G W := by apply _root_.YangMills.Construction.TorusLumps.mixedDeriv_of_fin_zero <;> assumption
theorem torusFrame_period (L t n : ℕ) (i : Fin 4) :
    (torusFrame L t n).period (torusFrame L t n).top i = n := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.torusFrame_period_top <;> assumption
theorem stepDensity_eq_family (a ρ lam : ℝ) (L t n : ℕ) (Y : (torusFrame L t n).Cell)
    (U : (torusFrame L t n).GaugeField (torusFrame L t n).top) :
    stepDensity a ρ lam Y U =
      stepDensityFamily a ρ lam L t n (toTorusSite n Y) (restrictToTorus n U) := by
  have h := torusFrame_period L t n
  show _ = stepDensity a ρ lam (siteOfTorusSite _ (toTorusSite n Y))
    (readAtLevel (torusFrame L t n) (torusFrame L t n).top (restrictToTorus n U))
  rw [siteOfTorusSite_toTorusSite h, readAtLevel_restrictToTorus h]
theorem stepDensity_leftTranslate_eq (a ρ lam : ℝ) (L t n k : ℕ) (Y : (torusFrame L t n).Cell)
    (U : (torusFrame L t n).GaugeField (torusFrame L t n).top)
    (c : Fin k → (torusFrame L t n).Site (torusFrame L t n).top × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    (fun τ : Fin k → ℝ =>
      stepDensity a ρ lam Y (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) U)) =
      fun τ => stepDensityFamily a ρ lam L t n (toTorusSite n Y)
        (perturb (fun l => torusBondOfBond n (c l)) X τ (restrictToTorus n U)) := by
  funext τ
  rw [stepDensity_eq_family, restrictToTorus_leftTranslate (torusFrame_period L t n)]
theorem bondOfTorusBond_bondFrom {L t n k : ℕ} (z : TorusSite n) (h : Fin k → (Fin 4 → ℤ) × Fin 4) :
    (fun l => bondOfTorusBond (F := torusFrame L t n) (torusFrame L t n).top (bondFrom z (h l))) =
      bondsAt (siteOfTorusSite _ z) h := by
  have hp := torusFrame_period L t n
  funext l
  refine Prod.ext ?_ rfl
  apply toTorusSite_injective hp
  simp only [bondOfTorusBond, bondFrom, bondsAt]
  rw [toTorusSite_siteOfTorusSite hp, toTorusSite_add hp, toTorusSite_siteOfTorusSite hp,
    toTorusSite_siteOfCoords hp]
theorem agreeOnBall_readAtLevel {L t n n' m : ℕ} (hn : 0 < n) (hn' : 0 < n') (h1 : 2 * m + 2 < n)
    (h2 : 2 * m + 2 < n') {y : TorusSite n} {y' : TorusSite n'} {V : TorusField n} {V' : TorusField n'}
    (hA : FieldsAgreeNear V V' y y' m) :
    AgreeOnBall (finiteCells (torusFrame L t n)) (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
      (finiteCells (torusFrame L t n')) (readAtLevel (torusFrame L t n') (torusFrame L t n').top V')
      (siteOfTorusSite _ y) (siteOfTorusSite _ y') m := by
  have hp := torusFrame_period L t n
  have hp' := torusFrame_period L t n'
  refine ⟨fun _ => Or.inr h1, fun _ => Or.inr h2, fun z _ => ?_, fun b hbb => ?_⟩
  · exact iff_of_true (mem_finiteCells _ (fun _ => hn) _) (mem_finiteCells _ (fun _ => hn') _)
  · have hq := hA b hbb
    have e1 : toTorusSite n (siteOfTorusSite (F := torusFrame L t n) (torusFrame L t n).top y +
        siteOfCoords _ b.1) = (bondFrom y b).1 := by
      rw [toTorusSite_add hp, toTorusSite_siteOfTorusSite hp, toTorusSite_siteOfCoords hp]
      rfl
    have e2 : toTorusSite n' (siteOfTorusSite (F := torusFrame L t n') (torusFrame L t n').top y' +
        siteOfCoords _ b.1) = (bondFrom y' b).1 := by
      rw [toTorusSite_add hp', toTorusSite_siteOfTorusSite hp', toTorusSite_siteOfCoords hp']
      rfl
    show V (toTorusSite n _) b.2 = V' (toTorusSite n' _) b.2
    rw [e1, e2]
    exact hq
section Interpolation
def interpolationBound (σ M₀ M₃ : ℝ) (k : ℕ) : ℝ :=
  M₀ / (σ / 64) ^ k + M₀ ^ (1 - (k : ℝ) / 3) * M₃ ^ ((k : ℝ) / 3)
variable {F : BlockFrame}
theorem interpolationBound_le {σ A h E : ℝ} {k : ℕ} (hσ : 0 < σ) (hA : 1 ≤ A) (hh : 0 < h) (hE0 : 0 < E)
    (hE1 : E ≤ 1) (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
    interpolationBound σ (A * h * E) (A * h) k ≤
      A * (1 + (64 / σ) + (64 / σ) ^ 2 + 1) * h * E ^ (1 / 3 : ℝ) := by
  unfold interpolationBound
  have hAh : 0 < A * h := by positivity
  have h64 : 0 < 64 / σ := by positivity
  have e1 : A * h * E / (σ / 64) ^ k ≤ A * (1 + (64 / σ) + (64 / σ) ^ 2) * h * E ^ (1 / 3 : ℝ) := by
    have hEp : E ≤ E ^ (1 / 3 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_ge hE0 hE1 (show (1 / 3 : ℝ) ≤ 1 by norm_num)
      simpa using this
    have hk : 1 / (σ / 64) ^ k ≤ 1 + 64 / σ + (64 / σ) ^ 2 := by
      have e : 1 / (σ / 64) ^ k = (64 / σ) ^ k := by
        rw [one_div, ← inv_pow, inv_div]
      rw [e]
      have hk' : k = 1 ∨ k = 2 := by omega
      rcases hk' with rfl | rfl
      · nlinarith [sq_nonneg (64 / σ)]
      · nlinarith
    calc A * h * E / (σ / 64) ^ k = A * h * E * (1 / (σ / 64) ^ k) := by ring
      _ ≤ A * h * E ^ (1 / 3 : ℝ) * (1 + 64 / σ + (64 / σ) ^ 2) := by
          gcongr
      _ = _ := by ring
  have e2 : (A * h * E) ^ (1 - (k : ℝ) / 3) * (A * h) ^ ((k : ℝ) / 3) ≤ A * h * E ^ (1 / 3 : ℝ) := by
    have hθ : (1 - (k : ℝ) / 3) + (k : ℝ) / 3 = 1 := by ring
    rw [Real.mul_rpow hAh.le hE0.le, mul_comm ((A * h) ^ (1 - (k : ℝ) / 3)), mul_assoc,
      ← Real.rpow_add hAh, hθ, Real.rpow_one, mul_comm]
    have hk3 : (1 / 3 : ℝ) ≤ 1 - (k : ℝ) / 3 := by
      have : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
      linarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hE0 hE1 hk3) hAh.le
  calc _ ≤ A * (1 + 64 / σ + (64 / σ) ^ 2) * h * E ^ (1 / 3 : ℝ) + A * h * E ^ (1 / 3 : ℝ) :=
        add_le_add e1 e2
    _ = _ := by ring
theorem bondDeriv_sub_le_interpolation {C₀ : ℝ}
    (hb : ∀ (F F' : BlockFrame) (G : F.GaugeField F.top → ℝ) (G' : F'.GaugeField F'.top → ℝ)
      (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
      (c' : Fin k → F'.Site F'.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ₀ M₀ M₃ : ℝ),
      1 ≤ k → k ≤ 2 → 0 < τ₀ → 0 < M₀ → 0 ≤ M₃ →
      (∀ ς : Fin k → ℝ, (∀ l, ς l = 1 ∨ ς l = -1) →
        IsControlledAlongLine G V c (fun l => ς l • X l) τ₀ M₃ ∧
        IsControlledAlongLine G' V' c' (fun l => ς l • X l) τ₀ M₃ ∧
        ∀ s : ℝ, |s| ≤ τ₀ → |G (alongLine c (fun l => ς l • X l) s V) -
          G' (alongLine c' (fun l => ς l • X l) s V')| ≤ M₀) →
      |bondDeriv G V c X - bondDeriv G' V' c' X| ≤
        C₀ * (M₀ / τ₀ ^ k + M₀ ^ (1 - (k : ℝ) / 3) * M₃ ^ ((k : ℝ) / 3)))
    (h₂ : SmallCurvatureAlongLineAndAgreeOn) {σ M₀ M₃ : ℝ} {F F' : BlockFrame}
    {G : F.GaugeField F.top → ℝ} {G' : F'.GaugeField F'.top → ℝ}
    {Y : F.Cell} {Y' : F'.Cell} {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top} {r k : ℕ}
    {h : Fin k → (Fin 4 → ℤ) × Fin 4} {X : Fin k → imaginaryQuaternions} (hσ : 0 < σ) (hM₀ : 0 < M₀)
    (hM₃ : 0 ≤ M₃) (hk1 : 1 ≤ k) (hk2 : k ≤ 2)
    (hs : ∀ W : F.GaugeField F.top, IsSmallCurvature (5 / 4 * σ) W → ContDiffThreeAlongBonds G W)
    (hs' : ∀ W : F'.GaugeField F'.top, IsSmallCurvature (5 / 4 * σ) W → ContDiffThreeAlongBonds G' W)
    (h3 : ∀ (W : F.GaugeField F.top) (c : Fin 3 → F.Site F.top × Fin 4) (X' : Fin 3 → imaginaryQuaternions),
      IsSmallCurvature (5 / 4 * σ) W → AreUnitVectors X' → |bondDeriv G W c X'| ≤ M₃)
    (h3' : ∀ (W : F'.GaugeField F'.top) (c : Fin 3 → F'.Site F'.top × Fin 4)
      (X' : Fin 3 → imaginaryQuaternions),
      IsSmallCurvature (5 / 4 * σ) W → AreUnitVectors X' → |bondDeriv G' W c X'| ≤ M₃)
    (hclose : ∀ (W : F.GaugeField F.top) (W' : F'.GaugeField F'.top), IsSmallCurvature (5 / 4 * σ) W →
      IsSmallCurvature (5 / 4 * σ) W' → AgreeOnBall (finiteCells F) W (finiteCells F') W' Y Y' r →
      |G W - G' W'| ≤ M₀)
    (hV : IsSmallCurvature (9 / 8 * σ) V) (hV' : IsSmallCurvature (9 / 8 * σ) V')
    (hA : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r)
    (hbox : ∀ l, BlockAverages.BondWithinRadius r (h l)) (hX : AreUnitVectors X) :
    |bondDeriv G V (bondsAt Y h) X - bondDeriv G' V' (bondsAt Y' h) X| ≤
      C₀ * interpolationBound σ M₀ M₃ k := by
  have hτ : 0 < σ / 64 := by positivity
  have hnorm : ∀ ς : Fin k → ℝ, (∀ l, ς l = 1 ∨ ς l = -1) → ∀ l, ‖ς l • X l‖ = 1 := by
    intro ς hς l
    rw [norm_smul, hX l, mul_one]
    rcases hς l with e | e <;> simp [e]
  have hcold : ∀ {F'' : BlockFrame} (W : F''.GaugeField F''.top) (c : Fin k → F''.Site F''.top × Fin 4)
      (ς : Fin k → ℝ), (∀ l, ς l = 1 ∨ ς l = -1) → IsSmallCurvature (9 / 8 * σ) W →
      ∀ s : ℝ, |s| ≤ σ / 64 → IsSmallCurvature (5 / 4 * σ) (alongLine c (fun l => ς l • X l) s W) := by
    intro F'' W c ς hς hW s hs
    have h1 := h₂.1 F'' W k c (fun l => ς l • X l) s (9 / 8 * σ)
      (fun l => (hnorm ς hς l).le) hW
    intro p hp
    refine (h1 p hp).trans_le ?_
    have hk : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
    have : 4 * (k : ℝ) * |s| ≤ 4 * 2 * (σ / 64) := by
      have h0 : (0 : ℝ) ≤ |s| := abs_nonneg s
      nlinarith
    linarith
  have key := hb F F' G G' V V' k (bondsAt Y h) (bondsAt Y' h) X (σ / 64) M₀ M₃ hk1 hk2
    hτ hM₀ hM₃ ?_
  · exact key
  · intro ς hς
    refine ⟨⟨fun s hs₁ => hs _ (hcold V _ ς hς hV s hs₁), fun s hs₁ e => ?_⟩,
      ⟨fun s hs₁ => hs' _ (hcold V' _ ς hς hV' s hs₁), fun s hs₁ e => ?_⟩, fun s hs₁ => ?_⟩
    · exact h3 _ _ _ (hcold V _ ς hς hV s hs₁) (fun l => hnorm ς hς (e l))
    · exact h3' _ _ _ (hcold V' _ ς hς hV' s hs₁) (fun l => hnorm ς hς (e l))
    · exact hclose _ _ (hcold V _ ς hς hV s hs₁) (hcold V' _ ς hς hV' s hs₁)
        (h₂.2 F F' V V' Y Y' r k h _ s hA hbox)
theorem interpolation_le_decay {C₀ σ A h κ CE : ℝ} {k q : ℕ} (hC₀ : 0 < C₀) (hσ : 0 < σ) (hA : 1 ≤ A)
    (hh : 0 < h) (hκ : 0 < κ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2)
    (hCE : C₀ * (A * (1 + 64 / σ + (64 / σ) ^ 2 + 1)) ≤ CE) :
    C₀ * interpolationBound σ (A * h * Real.exp (-(κ * q / 2 ^ 7))) (A * h) k ≤
      CE * h * Real.exp (-(2 * (κ / 2 ^ 10) * q)) := by
  set E := Real.exp (-(κ * q / 2 ^ 7)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ κ * (q : ℝ) / 2 ^ 7 := by positivity
    linarith)
  have h1 := interpolationBound_le hσ hA hh hE0 hE1 hk1 hk2
  have h2 : E ^ (1 / 3 : ℝ) ≤ Real.exp (-(2 * (κ / 2 ^ 10) * q)) := by
    rw [hE, ← Real.exp_mul, Real.exp_le_exp]
    have : 0 ≤ κ * (q : ℝ) := by positivity
    nlinarith
  calc C₀ * interpolationBound σ (A * h * E) (A * h) k
      ≤ C₀ * (A * (1 + 64 / σ + (64 / σ) ^ 2 + 1) * h * E ^ (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 hC₀.le
    _ = C₀ * (A * (1 + 64 / σ + (64 / σ) ^ 2 + 1)) * h * E ^ (1 / 3 : ℝ) := by ring
    _ ≤ CE * h * E ^ (1 / 3 : ℝ) := by gcongr
    _ ≤ _ := by
        have hpos : 0 < C₀ * (A * (1 + 64 / σ + (64 / σ) ^ 2 + 1)) := by positivity
        have : 0 ≤ CE * h := mul_nonneg (hpos.le.trans hCE) hh.le
        exact mul_le_mul_of_nonneg_left h2 this
end Interpolation
end TorusComparison
open TorusComparison in
theorem stepDensityLocality_proof (hV : stepDensityLocalityStatement)
    (hD : DensityDerivativesDecay)
    (hA : AnalyticAtAdmissibleParameters)
    (hT2 : DerivDiffLeOfCloseAlongLines) (hLn : SmallCurvatureAlongLineAndAgreeOn) :
    StepDensityLocality := by
  obtain ⟨cv, hcv, hV⟩ := hV
  obtain ⟨cd, Cd, hcd, hCd, hD⟩ := hD
  obtain ⟨C₀, hC₀, hb⟩ := hT2
  refine ⟨fun l => cv l / 4, fun l => by have := hcv l; positivity, fun T hT => ?_⟩
  obtain ⟨Cv, hCv, hV⟩ := hV T hT
  have hσ := hT.σ_pos
  have hcd' := hcd T.toChainParameters
  have hCd' := hCd T.toChainParameters
  have hcv' := hcv T.toChainParameters
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : ℝ, σ₀ = 8 / 9 * T.threshold := ⟨_, rfl⟩
  have h0 : 0 < σ₀ := by rw [hσ₀]; positivity
  have e98 : 9 / 8 * σ₀ = T.threshold := by rw [hσ₀]; ring
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 1 + Cv + Cd T.toChainParameters := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by rw [hAdef]; linarith
  have hA0 : 0 < A := by linarith
  obtain ⟨CE, hCE⟩ : ∃ CE : ℝ, CE = C₀ * (A * (1 + 64 / σ₀ + (64 / σ₀) ^ 2 + 1)) + A := ⟨_, rfl⟩
  have hCE0 : 0 < CE := by rw [hCE]; positivity
  have hcold : ∀ {F : BlockFrame} {W : F.GaugeField F.top}, IsSmallCurvature (5 / 4 * σ₀) W →
      IsSmallCurvature (9 / 8 * T.threshold) W :=
    fun {F W} hW p hp => (hW p hp).trans_le (by rw [hσ₀]; linarith)
  have hwarm : ∀ {F : BlockFrame} {W : F.GaugeField F.top}, IsSmallCurvature T.threshold W →
      IsSmallCurvature (9 / 8 * T.threshold) W :=
    fun {F W} hW p hp => (hW p hp).trans_le (by linarith)
  refine ⟨CE, hCE0, fun t n n' _ _ hn hn' y y' W W' m h1 h2 hW hW' hAg k b X hk hbox hX => ?_⟩
  have hnp : 0 < n := by omega
  have hnp' : 0 < n' := by omega
  have hAgr := agreeOnBall_readAtLevel (L := T.side) (t := t) hnp hnp' h1 h2 hAg
  have hcW := isSmallCurvature_readAtLevel (F := torusFrame T.side t n) (j := (torusFrame T.side t n).top)
    (torusFrame_period T.side t n) hW
  have hcW' := isSmallCurvature_readAtLevel (F := torusFrame T.side t n') (j := (torusFrame T.side t n').top)
    (torusFrame_period T.side t n') hW'
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [mixedDeriv_zero, mixedDeriv_zero]
    refine (hV t n n' hn hn' _ _ _ _ m (hwarm hcW) (hwarm hcW') hAgr).trans ?_
    have hle : Cv ≤ CE := by
      have : 0 ≤ C₀ * (A * (1 + 64 / σ₀ + (64 / σ₀) ^ 2 + 1)) := by positivity
      rw [hCE, hAdef] at *
      linarith
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hexp : Real.exp (-(cv T.toChainParameters * m)) ≤ Real.exp (-(cv T.toChainParameters / 4 * m)) :=
      Real.exp_le_exp.2 (by nlinarith)
    exact mul_le_mul hle hexp (Real.exp_pos _).le hCE0.le
  · have hs : ∀ (n : ℕ) [NeZero n], 64 ≤ n → ∀ (Y : (torusFrame T.side t n).Cell)
        (U : (torusFrame T.side t n).GaugeField (torusFrame T.side t n).top),
        IsSmallCurvature (5 / 4 * σ₀) U →
        ContDiffThreeAlongBonds (stepDensity T.coupling T.ρA T.lam Y) U := by
      intro n _ hn Y U hU k c X
      show ContDiffAt ℝ 3
        (fun τ : Fin k → ℝ => stepDensity T.coupling T.ρA T.lam Y
          (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) U)) 0
      rw [stepDensity_leftTranslate_eq]
      exact (hA T hT t n hn _ _ (isCold_restrictToTorus (torusFrame_period T.side t n) (hcold hU))
        k _ X).contDiffAt
    have h3 : ∀ (n : ℕ) [NeZero n], 64 ≤ n → ∀ (Y : (torusFrame T.side t n).Cell)
        (U : (torusFrame T.side t n).GaugeField (torusFrame T.side t n).top)
        (e : Fin 3 → (torusFrame T.side t n).Site (torusFrame T.side t n).top × Fin 4)
        (X' : Fin 3 → imaginaryQuaternions),
        IsSmallCurvature (5 / 4 * σ₀) U → AreUnitVectors X' →
        |bondDeriv (stepDensity T.coupling T.ρA T.lam Y) U e X'| ≤ A * 1 := by
      intro n _ hn Y U e X' hU hX'
      have h := hD T hT t n hn (toTorusSite n Y) _
        (isCold_restrictToTorus (torusFrame_period T.side t n) (hcold hU)) 3
        (fun l => torusBondOfBond n (e l)) X' (by norm_num) le_rfl hX'
      have e1 : bondDeriv (stepDensity T.coupling T.ρA T.lam Y) U e X' =
          mixedDeriv (stepDensityFamily T.coupling T.ρA T.lam T.side t n (toTorusSite n Y))
            (restrictToTorus n U) (fun l => torusBondOfBond n (e l)) X' := by
        unfold bondDeriv mixedDeriv
        rw [stepDensity_leftTranslate_eq]
      rw [e1]
      refine h.trans ?_
      have hexp : Real.exp (-(cd T.toChainParameters *
          (supportDiam (toTorusSite n Y) fun l => torusBondOfBond n (e l) : ℕ))) ≤ 1 :=
        Real.exp_le_one_iff.2 (by
          have : (0 : ℝ) ≤ cd T.toChainParameters *
              (supportDiam (toTorusSite n Y) fun l => torusBondOfBond n (e l) : ℕ) := by positivity
          linarith)
      rw [hAdef]
      nlinarith
    have hclose : ∀ (U : (torusFrame T.side t n).GaugeField (torusFrame T.side t n).top)
        (U' : (torusFrame T.side t n').GaugeField (torusFrame T.side t n').top),
        IsSmallCurvature (5 / 4 * σ₀) U → IsSmallCurvature (5 / 4 * σ₀) U' →
        AgreeOnBall (finiteCells (torusFrame T.side t n)) U (finiteCells (torusFrame T.side t n')) U'
          (siteOfTorusSite _ y) (siteOfTorusSite _ y') m →
        |stepDensity T.coupling T.ρA T.lam (siteOfTorusSite _ y : (torusFrame T.side t n).Cell) U -
          stepDensity T.coupling T.ρA T.lam (siteOfTorusSite _ y' : (torusFrame T.side t n').Cell) U'| ≤
          A * 1 * Real.exp (-(2 ^ 7 * cv T.toChainParameters * m / 2 ^ 7)) := by
      intro U U' hU hU' hAU
      have h := hV t n n' hn hn' _ _ U U' m (hcold hU) (hcold hU') hAU
      have e : 2 ^ 7 * cv T.toChainParameters * (m : ℝ) / 2 ^ 7 = cv T.toChainParameters * m := by ring
      rw [e, mul_one]
      refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      rw [hAdef]
      linarith
    rw [mixedDeriv_eq_bondDeriv
        (G := stepDensity T.coupling T.ρA T.lam (siteOfTorusSite _ y : (torusFrame T.side t n).Cell))
        (G' := stepDensityFamily T.coupling T.ρA T.lam T.side t n y) (torusFrame_period T.side t n)
        (fun _ => rfl),
      mixedDeriv_eq_bondDeriv
        (G := stepDensity T.coupling T.ρA T.lam (siteOfTorusSite _ y' : (torusFrame T.side t n').Cell))
        (G' := stepDensityFamily T.coupling T.ρA T.lam T.side t n' y') (torusFrame_period T.side t n')
        (fun _ => rfl),
      bondOfTorusBond_bondFrom, bondOfTorusBond_bondFrom]
    have hM₀ : 0 < A * 1 * Real.exp (-(2 ^ 7 * cv T.toChainParameters * m / 2 ^ 7)) := by positivity
    have key := bondDeriv_sub_le_interpolation hb hLn (k := k) h0 hM₀ (show 0 ≤ A * 1 by positivity)
      hk1 hk (hs n hn _) (hs n' hn' _) (h3 n hn _) (h3 n' hn' _) hclose
      (by rw [e98]; exact hcW) (by rw [e98]; exact hcW') hAgr hbox hX
    have fin := interpolation_le_decay (κ := 2 ^ 7 * cv T.toChainParameters) (q := m) (CE := CE) hC₀ h0
      hA1 one_pos (by positivity) hk1 hk (by rw [hCE]; linarith)
    have e : 2 * (2 ^ 7 * cv T.toChainParameters / 2 ^ 10) * (m : ℝ) = cv T.toChainParameters / 4 * m := by
      ring
    rw [e, mul_one CE] at fin
    exact key.trans fin
end RunningCouplingSlope
end YangMills.Construction
end
