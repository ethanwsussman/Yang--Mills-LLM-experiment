import YangMills.Construction.ColdStepAtMirrorFrames.ComparisonOfTwoTops
import YangMills.Construction.ColdStepAtMirrorFrames.CurvesOfTheFrames
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeBetweenSizes
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentialOfTheLieAlgebra
import YangMills.Construction.ColdStepAtMirrorFrames.HolonomyIsLipschitz
import YangMills.Construction.ColdStepAtMirrorFrames.SlopeAlongASegmentProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreNearTheirLimitsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages Calculus
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
namespace TwoFieldComparison
theorem iteratedFDeriv_comp_clm_zero {A B E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : A →L[ℝ] B) (f : B → E) (k : ℕ) (hf : ContDiffAt ℝ k f 0) (v : Fin k → A) :
    iteratedFDeriv ℝ k (f ∘ g) 0 v = iteratedFDeriv ℝ k f 0 (fun l => g (v l)) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.iteratedFDeriv_comp_clm_zero <;> assumption
def coordEmbedding {k p : ℕ} (e' : Fin p → Fin k) : (Fin p → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin p → ℝ) →L[ℝ] ℝ).smulRight (Pi.single (e' l) (1 : ℝ))
theorem iteratedFDeriv_single_eq_bondDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j k p : ℕ}
    (G : F.GaugeField j → E)
    (W : F.GaugeField j) (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (e' : Fin p → Fin k)
    (hG : ContDiffAt ℝ p (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0) :
    iteratedFDeriv ℝ p (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) 0 (fun l => Pi.single (e' l) 1) =
      bondDeriv G W (c ∘ e') (X ∘ e') := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.iteratedFDeriv_single_eq_bondDeriv <;> assumption
theorem leftTranslate_bondSpread_zero {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (W : F.GaugeField j) :
    leftTranslate (bondSpread c X 0) W = W := by apply _root_.YangMills.SharedProofs.p1939 <;> assumption
def bondSpreadCLM {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (y : F.Site j)
    (i : Fin 4) :
    (Fin k → ℝ) →L[ℝ] imaginaryQuaternions :=
  ∑ l, (ContinuousLinearMap.proj l : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (if c l = (y, i) then X l else 0)
theorem bondSpreadCLM_apply {j k : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (y : F.Site j) (i : Fin 4)
    (τ : Fin k → ℝ) : bondSpreadCLM c X y i τ = bondSpread c X τ y i := by
  simp only [bondSpreadCLM, bondSpread, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
theorem iteratedFDeriv_comp_add_left_zero {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : E → H) (n : ℕ) (p : E) : iteratedFDeriv ℝ n (fun z => f (p + z)) 0 = iteratedFDeriv ℝ n f p := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FrameCurves.iteratedFDeriv_comp_add_left_zero <;> assumption
theorem abs_multilinear_le_weightedNorm {N j : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin N → ℝ) ℝ) (K : ℝ)
    (wt : Fin N → ℝ) (hw : ∀ n, 0 ≤ wt n) (hK : 0 ≤ K)
    (hT : ∀ r : Fin j → Fin N, |T (fun i => Pi.single (r i) 1)| ≤ K * ∏ i, wt (r i))
    (ξ : Fin j → Fin N → ℝ) : |T ξ| ≤ K * ∏ i, _root_.YangMills.Construction.Calculus.weightedNorm wt (ξ i) := by apply _root_.YangMills.Construction.Calculus.abs_multilinear_le_prod_weightedNorm <;> assumption
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem expUnit_add_smul (s t : ℝ) (z : imaginaryQuaternions) :
    expUnit ((s + t) • z) = expUnit (t • z) * expUnit (s • z) := by
  let +nondep : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ ℍ[ℝ]
  apply Subtype.ext
  change NormedSpace.exp (((s + t) • z : imaginaryQuaternions) : ℍ[ℝ]) =
    NormedSpace.exp ((t • z : imaginaryQuaternions) : ℍ[ℝ]) * NormedSpace.exp ((s • z : imaginaryQuaternions) : ℍ[ℝ])
  have e : (((s + t) • z : imaginaryQuaternions) : ℍ[ℝ]) = t • (z : ℍ[ℝ]) + s • (z : ℍ[ℝ]) := by
    change (s + t) • (z : ℍ[ℝ]) = _
    rw [add_smul, add_comm]
  rw [e]
  exact NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left t).smul_right s)
theorem leftTranslate_add_smul {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (v : Fin k → ℝ) (s t : ℝ) (W : F.GaugeField F.top) :
    leftTranslate (bondSpread c X ((s + t) • v)) W =
      leftTranslate (bondSpread c X (t • v)) (leftTranslate (bondSpread c X (s • v)) W) := by
  funext y i
  simp only [leftTranslate, ← bondSpreadCLM_apply, map_smul]
  rw [expUnit_add_smul, mul_assoc]
def lineCLM {k : ℕ} (v : Fin k → ℝ) : ℝ →L[ℝ] (Fin k → ℝ) := (1 : ℝ →L[ℝ] ℝ).smulRight v
theorem lineCLM_apply {k : ℕ} (v : Fin k → ℝ) (s : ℝ) : lineCLM v s = s • v := by
  simp [lineCLM]
def restrictToParams {k : ℕ} (G : F.GaugeField F.top → ℝ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (W : F.GaugeField F.top) :
    (Fin k → ℝ) → ℝ := fun τ => G (leftTranslate (bondSpread c X τ) W)
theorem restrictToParams_line_shift {k : ℕ} (G : F.GaugeField F.top → ℝ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (v : Fin k → ℝ)
    (W : F.GaugeField F.top) (s : ℝ) :
    (fun z => restrictToParams G c X W ((s + z) • v)) =
      restrictToParams G c X (leftTranslate (bondSpread c X (s • v)) W) ∘ lineCLM v := by
  funext z
  simp only [restrictToParams, Function.comp, lineCLM_apply]
  rw [leftTranslate_add_smul]
theorem analyticAt_restrictToParams_line {k : ℕ} {G : F.GaugeField F.top → ℝ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (v : Fin k → ℝ)
    {W : F.GaugeField F.top} {s : ℝ} (h : IsBondAnalyticAt G (leftTranslate (bondSpread c X (s • v)) W)) :
    AnalyticAt ℝ (fun z => restrictToParams G c X W (z • v)) s := by
  have h1 : AnalyticAt ℝ (restrictToParams G c X (leftTranslate (bondSpread c X (s • v)) W)) (lineCLM v 0) := by
    rw [map_zero]
    exact h k c X
  have h2 : AnalyticAt ℝ (fun z => restrictToParams G c X W ((s + z) • v)) 0 := by
    rw [restrictToParams_line_shift]
    exact h1.comp ((lineCLM v).analyticAt 0)
  have e : (fun z => restrictToParams G c X W (z • v)) =
      (fun z => restrictToParams G c X W ((s + z) • v)) ∘ fun z => z - s := by
    funext z
    simp
  rw [e]
  exact AnalyticAt.comp_of_eq h2 (analyticAt_id.sub analyticAt_const) (sub_self s)
theorem iteratedFDeriv_restrictToParams_line {k : ℕ} {G : F.GaugeField F.top → ℝ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (v : Fin k → ℝ)
    {W : F.GaugeField F.top} {s : ℝ} (h : IsBondAnalyticAt G (leftTranslate (bondSpread c X (s • v)) W)) (i : ℕ) :
    iteratedFDeriv ℝ i (fun z => restrictToParams G c X W (z • v)) s (fun _ => 1) =
      iteratedFDeriv ℝ i (restrictToParams G c X (leftTranslate (bondSpread c X (s • v)) W)) 0 (fun _ => v) := by
  have hA : ContDiffAt ℝ i (restrictToParams G c X (leftTranslate (bondSpread c X (s • v)) W)) 0 :=
    (h k c X).contDiffAt
  rw [← iteratedFDeriv_comp_add_left_zero (fun z => restrictToParams G c X W (z • v)) i s,
    restrictToParams_line_shift, iteratedFDeriv_comp_clm_zero _ _ i hA]
  congr 1
  funext _
  rw [lineCLM_apply, one_smul]
theorem plaquetteDefect_leftTranslate_le (hexp : QuaternionExp.ExpUnitLipschitzInjective)
    (hhol : PathHolonomyLipschitz) {k : ℕ}
    (hk : k ≤ 2) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X)
    (v : Fin k → ℝ)
    (hv : ∀ l, |v l| ≤ 1) (s : ℝ) (W : F.GaugeField F.top) (p : F.Site F.top × Fin 4 × Fin 4) :
    plaquetteDefect (leftTranslate (bondSpread c X (s • v)) W) p ≤ plaquetteDefect W p + 8 * |s| := by
  have hmove : ∀ y i, ‖bondSpread c X (s • v) y i‖ ≤ 2 * |s| := by
    intro y i
    unfold bondSpread
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ l : Fin k, ‖if c l = (y, i) then (s • v) l • X l else 0‖ ≤ |s| := by
      intro l
      split_ifs
      · rw [norm_smul, hX l, mul_one, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hv l)
      · simp
    refine (Finset.sum_le_sum fun l _ => hterm l).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hzero : ((expUnit 0 : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    change NormedSpace.exp (((0 : imaginaryQuaternions)) : ℍ[ℝ]) = 1
    simp
  have hbond : ∀ x i, ‖((leftTranslate (bondSpread c X (s • v)) W x i : UnitQuaternion) : ℍ[ℝ]) -
      ((W x i : UnitQuaternion) : ℍ[ℝ])‖ ≤ 2 * |s| := by
    intro x i
    have e : ((leftTranslate (bondSpread c X (s • v)) W x i : UnitQuaternion) : ℍ[ℝ]) -
        ((W x i : UnitQuaternion) : ℍ[ℝ]) =
        (((expUnit (bondSpread c X (s • v) x i) : UnitQuaternion) : ℍ[ℝ]) - 1) * ((W x i : UnitQuaternion) : ℍ[ℝ]) := by
      simp only [leftTranslate, Submonoid.coe_mul, sub_mul, one_mul]
    rw [e, norm_mul, _root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoFieldComparison.norm_coe_unitQuaternion, mul_one]
    have h1 := hexp.1 (bondSpread c X (s • v) x i) 0
    rw [hzero, sub_zero] at h1
    exact h1.trans (hmove x i)
  have h2 := hhol F F.top _ _ _ hbond p.1 [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)]
  simp only [List.length_cons, List.length_nil] at h2
  unfold plaquetteDefect plaquetteHolonomy
  obtain ⟨A, hAd⟩ : ∃ A, A = (((pathHolonomy (leftTranslate (bondSpread c X (s • v)) W) p.1
    [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ])) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = ((pathHolonomy W p.1
    [(p.2.1, true), (p.2.2, true), (p.2.1, false), (p.2.2, false)] : UnitQuaternion) : ℍ[ℝ]) := ⟨_, rfl⟩
  rw [← hAd, ← hBd] at h2 ⊢
  have h3 : ‖A - 1‖ ≤ ‖A - B‖ + ‖B - 1‖ := by
    have := norm_add_le (A - B) (B - 1)
    simpa using this
  norm_num at h2
  linarith
theorem siteOfCoords_injOn {r : ℕ} {u v : Fin 4 → ℤ} (hu : WithinRadius r u) (hv : WithinRadius r v)
    (hs : ∀ i, 2 * r + 2 < F.extent i)
    (h : (_root_.YangMills.Construction.BlockAverages.siteOfCoords F.top u : F.Cell) = _root_.YangMills.Construction.BlockAverages.siteOfCoords F.top v) : u = v := by
  funext i
  have h1 := congrFun h i
  simp only [_root_.YangMills.Construction.BlockAverages.siteOfCoords] at h1
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  have hper : (F.period F.top i : ℤ) = F.extent i := by simp [BlockFrame.period]
  rw [hper] at h1
  have h2 := hu i
  have h3 := hv i
  have h4 := hs i
  have h5 : |v i - u i| < (F.extent i : ℤ) := by
    rw [abs_lt] at *
    have h6 := abs_le.mp h2
    have h7 := abs_le.mp h3
    constructor <;> omega
  have h8 := Int.eq_zero_of_abs_lt_dvd h1 h5
  omega
theorem agreeOnBall_leftTranslate {F' : BlockFrame} (hs : ∀ i, 2 ≤ F.extent i) (hs' : ∀ i, 2 ≤ F'.extent i)
    {V : F.GaugeField F.top} {V' : F'.GaugeField F'.top}
    {Y : F.Cell} {Y' : F'.Cell} {r : ℕ} (hA : AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r) {k : ℕ}
    (h : Fin k → (Fin 4 → ℤ) × Fin 4) (hb : ∀ l, BondWithinRadius r (h l)) (X : Fin k → imaginaryQuaternions)
    (τ : Fin k → ℝ) :
    AgreeOnBall (finiteCells F) (leftTranslate (bondSpread (bondsAt Y h) X τ) V) (finiteCells F')
      (leftTranslate (bondSpread (bondsAt Y' h) X τ) V') Y Y' r := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := hA
  have hsF : ∀ i, 2 * r + 2 < F.extent i := fun i => (h1 i).resolve_left (by have := hs i; omega)
  have hsF' : ∀ i, 2 * r + 2 < F'.extent i := fun i => (h2 i).resolve_left (by have := hs' i; omega)
  refine ⟨h1, h2, h3, fun b hbb => ?_⟩
  simp only [leftTranslate]
  rw [h4 b hbb]
  congr 2
  unfold bondSpread
  refine Finset.sum_congr rfl fun l _ => ?_
  have key : ∀ {G : BlockFrame} (Z : G.Cell), (∀ i, 2 * r + 2 < G.extent i) →
      (bondsAt Z h l = (Z + _root_.YangMills.Construction.BlockAverages.siteOfCoords G.top b.1, b.2) ↔ h l = b) := by
    intro G Z hG
    constructor
    · intro e
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      simp only [bondsAt] at e1 e2
      exact Prod.ext (_root_.YangMills.Construction.ColdStepAtMirrorFrames.TwoFieldComparison.siteOfCoords_injOn (hb l).1 hbb.1 hG (add_left_cancel e1)) e2
    · intro e
      simp only [bondsAt, e]
  by_cases hl : h l = b
  · rw [if_pos ((key Y hsF).mpr hl), if_pos ((key Y' hsF').mpr hl)]
  · rw [if_neg (fun e => hl ((key Y hsF).mp e)), if_neg (fun e => hl ((key Y' hsF').mp e))]
theorem abs_iteratedFDeriv_six_le {k : ℕ} (hk : k ≤ 2) {G : F.GaugeField F.top → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions) (hX : AreUnitVectors X) (v : Fin k → ℝ) (hv : ∀ l, |v l| ≤ 1)
    {W : F.GaugeField F.top}
    (hW : IsBondAnalyticAt G W)
    (hd : ∀ (e : Fin 6 → F.Site F.top × Fin 4) (X : Fin 6 → imaginaryQuaternions), AreUnitVectors X →
      |bondDeriv G W e X| ≤ B) :
    |iteratedFDeriv ℝ 6 (restrictToParams G c X W) 0 (fun _ => v)| ≤ 64 * B := by
  have hc : ContDiffAt ℝ (6 : ℕ) (restrictToParams G c X W) 0 := (hW k c X).contDiffAt
  have h1 := abs_multilinear_le_weightedNorm (iteratedFDeriv ℝ 6 (restrictToParams G c X W) 0) B (fun _ => 1)
    (fun _ => zero_le_one) hB
    (fun r => by
      have e := iteratedFDeriv_single_eq_bondDeriv G W c X r hc
      simp only [Finset.prod_const_one, mul_one]
      change |iteratedFDeriv ℝ 6 (fun τ => G (leftTranslate (bondSpread c X τ) W)) 0 _| ≤ B
      rw [e]
      exact hd _ _ fun l => hX _) (fun _ => v)
  refine h1.trans ?_
  have h2 : _root_.YangMills.Construction.Calculus.weightedNorm (fun _ => (1 : ℝ)) v ≤ 2 := by
    unfold _root_.YangMills.Construction.Calculus.weightedNorm
    simp only [mul_one]
    refine (Finset.sum_le_sum fun l _ => hv l).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact_mod_cast hk
  have h3 : 0 ≤ _root_.YangMills.Construction.Calculus.weightedNorm (fun _ => (1 : ℝ)) v :=
    Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) zero_le_one
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc B * _root_.YangMills.Construction.Calculus.weightedNorm (fun _ => (1 : ℝ)) v ^ 6 ≤ B * 2 ^ 6 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 6) hB
    _ = 64 * B := by ring
theorem iteratedFDeriv_sub_line {i : ℕ} {φ φ' : ℝ → ℝ} {s : ℝ} (h : AnalyticAt ℝ φ s) (h' : AnalyticAt ℝ φ' s) :
    iteratedFDeriv ℝ i (fun z => φ z - φ' z) s (fun _ => 1) =
      iteratedFDeriv ℝ i φ s (fun _ => 1) - iteratedFDeriv ℝ i φ' s (fun _ => 1) := by
  have e : (fun z => φ z - φ' z) = φ + (-1 : ℝ) • φ' := by
    funext z
    simp [sub_eq_add_neg]
  have hc : ContDiffAt ℝ i φ s := h.contDiffAt
  have hc' : ContDiffAt ℝ i φ' s := h'.contDiffAt
  have h1 : ContDiffAt ℝ i ((-1 : ℝ) • φ') s := hc'.const_smul (-1 : ℝ)
  rw [e, iteratedFDeriv_add_apply hc h1, iteratedFDeriv_const_smul_apply hc']
  change iteratedFDeriv ℝ i φ s (fun _ => 1) + (-1) * iteratedFDeriv ℝ i φ' s (fun _ => 1) = _
  ring
theorem rpow_interp_bounds {M B : ℝ} (h0 : 0 < M) (h : M ≤ B) :
    M ≤ M ^ (2 / 3 : ℝ) * B ^ (1 / 3 : ℝ) ∧
      M ^ (5 / 6 : ℝ) * B ^ (1 / 6 : ℝ) ≤ M ^ (2 / 3 : ℝ) * B ^ (1 / 3 : ℝ) := by
  have hB : 0 < B := lt_of_lt_of_le h0 h
  constructor
  · have e : M = M ^ (2 / 3 : ℝ) * M ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_add h0]
      norm_num
    calc M = M ^ (2 / 3 : ℝ) * M ^ (1 / 3 : ℝ) := e
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0.le h (by norm_num)) (by positivity)
  · have e1 : M ^ (5 / 6 : ℝ) = M ^ (2 / 3 : ℝ) * M ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_add h0]
      norm_num
    have e2 : B ^ (1 / 3 : ℝ) = B ^ (1 / 6 : ℝ) * B ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_add hB]
      norm_num
    rw [e1, e2, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow h0.le h (by norm_num)) (by positivity)
theorem iteratedFDeriv_two_polarization (f : (Fin 2 → ℝ) → ℝ) (hf : AnalyticAt ℝ f 0) :
    iteratedFDeriv ℝ 2 f 0 (fun l => Pi.single l 1) =
      (iteratedFDeriv ℝ 2 f 0 (fun _ => Pi.single 0 1 + Pi.single 1 1) -
        iteratedFDeriv ℝ 2 f 0 (fun _ => Pi.single 0 1 - Pi.single 1 1)) / 4 := by
  have hc : ContDiffAt ℝ 2 f 0 := hf.contDiffAt
  have hsym := hc.isSymmSndFDerivAt (by simp)
  have e := hsym.eq (Pi.single 0 1) (Pi.single 1 1)
  simp only [iteratedFDeriv_two_apply, map_add, map_sub, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply]
  linarith
theorem bondDeriv_fin_zero {G : F.GaugeField F.top → ℝ} (W : F.GaugeField F.top) (c : Fin 0 → F.Site F.top × Fin 4)
    (X : Fin 0 → imaginaryQuaternions) :
    bondDeriv G W c X = G W := by apply _root_.YangMills.SharedProofs.p1654 <;> assumption
end TwoFieldComparison
open TwoFieldComparison in
theorem derivativesCloseOfValuesClose_proof (hD : LandauKolmogorovAtZero)
    (hexp : QuaternionExp.ExpUnitLipschitzInjective)
    (hhol : PathHolonomyLipschitz) : DerivativesCloseOfValuesClose := by
  classical
  obtain ⟨C1, hC1p, hC1⟩ := hD 6 1 (by norm_num)
  obtain ⟨C2, hC2p, hC2⟩ := hD 6 2 (by norm_num)
  refine ⟨128 * C1 + 128 * C2 + 1, by positivity, ?_⟩
  intro F F' G G' s₁ s₂ τ₀ M₀ B V V' Y Y' r hs hs' hτ hτ1 hss hM hMB hG hG' hcomp hV hV' hA k h X hk hb hX
  have hB0 : 0 < B := lt_of_lt_of_le hM hMB
  have hline : ∀ (j : ℕ) (Cj : ℝ), (∀ (g : ℕ → ℝ → ℝ) (τ₀ M₀ Mp : ℝ), 0 < τ₀ → 0 < M₀ → 0 ≤ Mp →
      (∀ i, i < 6 → ∀ s, |s| ≤ τ₀ → HasDerivAt (g i) (g (i + 1) s) s) →
      (∀ s, |s| ≤ τ₀ → |g 0 s| ≤ M₀) → (∀ s, |s| ≤ τ₀ → |g 6 s| ≤ Mp) →
      |g j 0| ≤ Cj * (M₀ / τ₀ ^ j + M₀ ^ (1 - (j : ℝ) / (6 : ℕ)) * Mp ^ ((j : ℝ) / (6 : ℕ)))) →
      ∀ v : Fin k → ℝ, (∀ l, |v l| ≤ 1) →
      |iteratedFDeriv ℝ j (restrictToParams G (bondsAt Y h) X V) 0 (fun _ => v) -
        iteratedFDeriv ℝ j (restrictToParams G' (bondsAt Y' h) X V') 0 (fun _ => v)| ≤
        Cj * (M₀ / τ₀ ^ j + M₀ ^ (1 - (j : ℝ) / (6 : ℕ)) * (128 * B) ^ ((j : ℝ) / (6 : ℕ))) := by
    intro j Cj hCj v hv
    have hcold : ∀ s, |s| ≤ τ₀ → IsSmallCurvature s₂ (leftTranslate (bondSpread (bondsAt Y h) X (s • v)) V) := by
      intro s hs₀ p hp
      have h1 := plaquetteDefect_leftTranslate_le hexp hhol hk (bondsAt Y h) X hX v hv s V p
      have h2 := hV p hp
      linarith
    have hcold' : ∀ s, |s| ≤ τ₀ →
        IsSmallCurvature s₂ (leftTranslate (bondSpread (bondsAt Y' h) X (s • v)) V') := by
      intro s hs₀ p hp
      have h1 := plaquetteDefect_leftTranslate_le hexp hhol hk (bondsAt Y' h) X hX v hv s V' p
      have h2 := hV' p hp
      linarith
    have hφ : ∀ s, |s| ≤ τ₀ → AnalyticAt ℝ (fun z => restrictToParams G (bondsAt Y h) X V (z • v)) s :=
      fun s hs₀ => analyticAt_restrictToParams_line _ X v (hG _ (hcold s hs₀)).1
    have hφ' : ∀ s, |s| ≤ τ₀ → AnalyticAt ℝ (fun z => restrictToParams G' (bondsAt Y' h) X V' (z • v)) s :=
      fun s hs₀ => analyticAt_restrictToParams_line _ X v (hG' _ (hcold' s hs₀)).1
    obtain ⟨u, hu⟩ : ∃ u : ℝ → ℝ, u = fun z => restrictToParams G (bondsAt Y h) X V (z • v) -
        restrictToParams G' (bondsAt Y' h) X V' (z • v) := ⟨_, rfl⟩
    have hua : ∀ s, |s| ≤ τ₀ → AnalyticAt ℝ u s := fun s hs₀ => by
      rw [hu]
      exact (hφ s hs₀).sub (hφ' s hs₀)
    have h0 : |(0 : ℝ)| ≤ τ₀ := by simpa using hτ.le
    have hkey := hCj (fun i => deriv^[i] u) τ₀ M₀ (128 * B) hτ hM (by positivity)
      (fun i _ s hs₀ => by
        have hd : AnalyticAt ℝ (deriv^[i] u) s := (hua s hs₀).iterated_deriv i
        have h1 := hd.differentiableAt.hasDerivAt
        simp only [Function.iterate_succ_apply']
        exact h1)
      (fun s hs₀ => by
        simp only [Function.iterate_zero, id_eq]
        rw [hu]
        exact hcomp _ _ (hcold s hs₀) (hcold' s hs₀) (agreeOnBall_leftTranslate hs hs' hA h hb X (s • v)))
      (fun s hs₀ => by
        change |deriv^[6] u s| ≤ _
        rw [← iteratedDeriv_eq_iterate, iteratedDeriv_eq_iteratedFDeriv, hu,
          iteratedFDeriv_sub_line (hφ s hs₀) (hφ' s hs₀)]
        have a1 := (hG _ (hcold s hs₀)).1
        have a2 := (hG' _ (hcold' s hs₀)).1
        rw [iteratedFDeriv_restrictToParams_line _ X v a1, iteratedFDeriv_restrictToParams_line _ X v a2]
        have b1 := abs_iteratedFDeriv_six_le hk hB0.le (bondsAt Y h) X hX v hv a1 (hG _ (hcold s hs₀)).2
        have b2 := abs_iteratedFDeriv_six_le hk hB0.le (bondsAt Y' h) X hX v hv a2 (hG' _ (hcold' s hs₀)).2
        have b3 := abs_sub (iteratedFDeriv ℝ 6 (restrictToParams G (bondsAt Y h) X
            (leftTranslate (bondSpread (bondsAt Y h) X (s • v)) V)) 0 (fun _ => v))
          (iteratedFDeriv ℝ 6 (restrictToParams G' (bondsAt Y' h) X
            (leftTranslate (bondSpread (bondsAt Y' h) X (s • v)) V')) 0 (fun _ => v))
        linarith)
    have e0 : leftTranslate (bondSpread (bondsAt Y h) X ((0 : ℝ) • v)) V = V := by
      rw [zero_smul, leftTranslate_bondSpread_zero]
    have e0' : leftTranslate (bondSpread (bondsAt Y' h) X ((0 : ℝ) • v)) V' = V' := by
      rw [zero_smul, leftTranslate_bondSpread_zero]
    have a1 := (hG _ (hcold 0 h0)).1
    have a2 := (hG' _ (hcold' 0 h0)).1
    have d1 := iteratedFDeriv_restrictToParams_line _ X v a1 j
    have d2 := iteratedFDeriv_restrictToParams_line _ X v a2 j
    rw [e0] at d1
    rw [e0'] at d2
    have hval : deriv^[j] u 0 = iteratedFDeriv ℝ j (restrictToParams G (bondsAt Y h) X V) 0 (fun _ => v) -
        iteratedFDeriv ℝ j (restrictToParams G' (bondsAt Y' h) X V') 0 (fun _ => v) := by
      rw [← iteratedDeriv_eq_iterate, iteratedDeriv_eq_iteratedFDeriv, hu,
        iteratedFDeriv_sub_line (hφ 0 h0) (hφ' 0 h0), d1, d2]
    rw [← hval]
    exact hkey
  have hV2 : IsSmallCurvature s₂ V := fun p hp => by
    have := hV p hp
    linarith
  have hV2' : IsSmallCurvature s₂ V' := fun p hp => by
    have := hV' p hp
    linarith
  obtain ⟨hQ1, hQ2⟩ := rpow_interp_bounds hM hMB
  obtain ⟨P, hP⟩ : ∃ P, P = M₀ / τ₀ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = M₀ ^ (2 / 3 : ℝ) * B ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  rw [← hP, ← hQ]
  rw [← hQ] at hQ1 hQ2
  have hP0 : 0 ≤ P := by
    rw [hP]
    positivity
  have hQ0 : 0 ≤ Q := hM.le.trans hQ1
  have hP1 : M₀ / τ₀ ≤ P := by
    rw [hP]
    refine div_le_div_of_nonneg_left hM.le (by positivity) ?_
    nlinarith
  have h128 : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → (128 * B) ^ y ≤ 128 * B ^ y := by
    intro y hy0 hy1
    rw [Real.mul_rpow (by norm_num) hB0.le]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc (128 : ℝ) ^ y ≤ (128 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hy1
      _ = 128 := Real.rpow_one _
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · rw [bondDeriv_fin_zero, bondDeriv_fin_zero]
    have h1 := hcomp V V' hV2 hV2' hA
    nlinarith [mul_nonneg hC1p.le (add_nonneg hP0 hQ0), mul_nonneg hC2p.le (add_nonneg hP0 hQ0)]
  · have hsing : (fun l : Fin 1 => (Pi.single l 1 : Fin 1 → ℝ)) = fun _ => fun _ => 1 := by
      funext l j
      have : j = l := Subsingleton.elim _ _
      subst this
      simp
    have h1 := hline 1 C1 hC1 (fun _ => 1) (fun _ => by simp)
    have e1 : (1 : ℝ) - ((1 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 5 / 6 := by norm_num
    have e2 : ((1 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 1 / 6 := by norm_num
    rw [e1, e2, pow_one] at h1
    change |iteratedFDeriv ℝ 1 (restrictToParams G (bondsAt Y h) X V) 0 (fun l => Pi.single l 1) -
      iteratedFDeriv ℝ 1 (restrictToParams G' (bondsAt Y' h) X V') 0 (fun l => Pi.single l 1)| ≤ _
    rw [hsing]
    refine h1.trans ?_
    have h2 : M₀ ^ (5 / 6 : ℝ) * (128 * B) ^ (1 / 6 : ℝ) ≤ 128 * Q := by
      calc M₀ ^ (5 / 6 : ℝ) * (128 * B) ^ (1 / 6 : ℝ) ≤ M₀ ^ (5 / 6 : ℝ) * (128 * B ^ (1 / 6 : ℝ)) :=
            mul_le_mul_of_nonneg_left (h128 _ (by norm_num) (by norm_num)) (by positivity)
        _ = 128 * (M₀ ^ (5 / 6 : ℝ) * B ^ (1 / 6 : ℝ)) := by ring
        _ ≤ 128 * Q := by linarith
    have h3 : C1 * (M₀ / τ₀ + M₀ ^ (5 / 6 : ℝ) * (128 * B) ^ (1 / 6 : ℝ)) ≤ C1 * (P + 128 * Q) :=
      mul_le_mul_of_nonneg_left (by linarith) hC1p.le
    nlinarith [mul_nonneg hC1p.le hP0, mul_nonneg hC1p.le hQ0, mul_nonneg hC2p.le (add_nonneg hP0 hQ0)]
  · have hz1 : (Pi.single 0 1 + Pi.single 1 1 : Fin 2 → ℝ) = fun l => if l = 0 then 1 else 1 := by
      funext l
      fin_cases l <;> simp
    have hvp : ∀ l, |(Pi.single 0 1 + Pi.single 1 1 : Fin 2 → ℝ) l| ≤ 1 := fun l => by
      fin_cases l <;> simp
    have hvm : ∀ l, |(Pi.single 0 1 - Pi.single 1 1 : Fin 2 → ℝ) l| ≤ 1 := fun l => by
      fin_cases l <;> simp
    have h1 := hline 2 C2 hC2 _ hvp
    have h2 := hline 2 C2 hC2 _ hvm
    have e1 : (1 : ℝ) - ((2 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 2 / 3 := by norm_num
    have e2 : ((2 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) = 1 / 3 := by norm_num
    rw [e1, e2] at h1 h2
    rw [← hP] at h1 h2
    have p1 := iteratedFDeriv_two_polarization (restrictToParams G (bondsAt Y h) X V)
      ((hG _ hV2).1 2 (bondsAt Y h) X)
    have p2 := iteratedFDeriv_two_polarization (restrictToParams G' (bondsAt Y' h) X V')
      ((hG' _ hV2').1 2 (bondsAt Y' h) X)
    change |iteratedFDeriv ℝ 2 (restrictToParams G (bondsAt Y h) X V) 0 (fun l => Pi.single l 1) -
      iteratedFDeriv ℝ 2 (restrictToParams G' (bondsAt Y' h) X V') 0 (fun l => Pi.single l 1)| ≤ _
    rw [p1, p2]
    have h3 : M₀ ^ (2 / 3 : ℝ) * (128 * B) ^ (1 / 3 : ℝ) ≤ 128 * Q := by
      calc M₀ ^ (2 / 3 : ℝ) * (128 * B) ^ (1 / 3 : ℝ) ≤ M₀ ^ (2 / 3 : ℝ) * (128 * B ^ (1 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_left (h128 _ (by norm_num) (by norm_num)) (by positivity)
        _ = 128 * Q := by rw [hQ]; ring
    have h4 : C2 * (P + M₀ ^ (2 / 3 : ℝ) * (128 * B) ^ (1 / 3 : ℝ)) ≤ C2 * (P + 128 * Q) :=
      mul_le_mul_of_nonneg_left (by linarith) hC2p.le
    have hE : C2 * (P + 128 * Q) ≤ (128 * C1 + 128 * C2 + 1) * (P + Q) := by
      nlinarith [mul_nonneg hC1p.le (add_nonneg hP0 hQ0), mul_nonneg hC2p.le hP0, mul_nonneg hC2p.le hQ0,
        add_nonneg hP0 hQ0]
    rw [abs_le] at h1 h2 ⊢
    obtain ⟨a1, a2⟩ := h1
    obtain ⟨b1, b2⟩ := h2
    have hpos : 0 ≤ C2 * (P + 128 * Q) := by positivity
    constructor <;> linarith
end ColdStepAtMirrorFrames
end YangMills.Construction
end
