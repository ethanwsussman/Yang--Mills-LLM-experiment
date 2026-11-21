import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.LawByMomentsOfTheFlow.CurlOverAReference
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheLogarithmsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MomentLaw
open LumpContours TorusFields ResponseInTheExpansion TopLevelSites
open ColdStepAtMirrorFrames.BlockOffsets ColdStepAtMirrorFrames.SmallUnits
namespace CurlOverReference
private theorem norm_minimalLog_le_two_mul (u : BlockAverages.UnitQuaternion) (hu : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne u < 1) :
    ‖minimalLog u‖ ≤ 2 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne u := by apply _root_.YangMills.SharedProofs.p16086 <;> assumption
variable {N : ℕ} [NeZero N]
private theorem norm_lieFormCurl_le (A : TorusBond N → BlockAverages.imaginaryQuaternions) (x : TorusSite N) (μ ν : Fin 4) :
    ‖lieFormCurl A (x, μ, ν)‖ ≤ plaquetteLogSize A x μ ν := by
  unfold lieFormCurl plaquetteLogSize
  refine (norm_sub_le _ _).trans ?_
  gcongr
  refine (norm_sub_le _ _).trans ?_
  gcongr
  exact norm_add_le _ _
private theorem plaquetteSum_eq (e : TorusBond N → ℝ) (x : TorusSite N) (μ ν : Fin 4) :
    plaquetteSum e x μ ν = e (x, μ) + e (x + unitStep N μ, ν) + e (x + unitStep N ν, μ) + e (x, ν) := by
  simp [plaquetteSum, pathSum, plaquetteBonds]
  ring
private theorem sq_bound {κ y h : ℝ} (hκ : 1 ≤ κ) (hy : 0 ≤ y) (hh : 0 ≤ h) :
    (8 * (κ * y) + 2 * h) ^ 2 ≤ 64 * (κ ^ 2 * (y + h) ^ 2) := by
  have h1 : 2 * h ≤ 8 * (κ * h) := by
    have := mul_le_mul_of_nonneg_right hκ hh
    linarith
  have h2 : 8 * (κ * y) + 2 * h ≤ 8 * κ * (y + h) := by
    have : 8 * κ * (y + h) = 8 * (κ * y) + 8 * (κ * h) := by ring
    linarith
  have h3 : 0 ≤ 8 * (κ * y) + 2 * h := by positivity
  calc (8 * (κ * y) + 2 * h) ^ 2 ≤ (8 * κ * (y + h)) ^ 2 := pow_le_pow_left₀ h3 h2 2
    _ = 64 * (κ ^ 2 * (y + h) ^ 2) := by ring
private theorem mul_le_sq_mul {κ z : ℝ} (hκ : 1 ≤ κ) (hz : 0 ≤ z) : κ * z ≤ κ ^ 2 * z := by
  have : κ ≤ κ ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right this hz
private theorem plaquette_bounds (hA : axialGaugePathBoundsStatement) (W : TorusField N)
    (M Nf : TorusBond N → BlockAverages.imaginaryQuaternions) (x : TorusSite N) (μ ν : Fin 4)
    (e₁ e₂ e₃ e₄ y κ v ω : ℝ) (h₁ : 0 ≤ e₁) (h₂ : 0 ≤ e₂) (h₃ : 0 ≤ e₃) (h₄ : 0 ≤ e₄) (hκ : 1 ≤ κ) (hy : 0 ≤ y)
    (hv : 0 ≤ v) (hω : 0 ≤ ω)
    (g₁ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W x μ) ≤ κ * y + e₁) (g₂ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W (x + unitStep N μ) ν) ≤ κ * y + e₂)
    (g₃ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W (x + unitStep N ν) μ) ≤ κ * y + e₃) (g₄ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W x ν) ≤ κ * y + e₄)
    (l₁ : ‖minimalLog (W x μ) - M (x, μ) - Nf (x, μ)‖ ≤ κ * (y + e₁) ^ 2 + ω)
    (l₂ : ‖minimalLog (W (x + unitStep N μ) ν) - M (x + unitStep N μ, ν) - Nf (x + unitStep N μ, ν)‖ ≤ κ * (y + e₂) ^ 2 + ω)
    (l₃ : ‖minimalLog (W (x + unitStep N ν) μ) - M (x + unitStep N ν, μ) - Nf (x + unitStep N ν, μ)‖ ≤ κ * (y + e₃) ^ 2 + ω)
    (l₄ : ‖minimalLog (W x ν) - M (x, ν) - Nf (x, ν)‖ ≤ κ * (y + e₄) ^ 2 + ω)
    (f₁ : ‖Nf (x, μ)‖ ≤ e₁) (f₂ : ‖Nf (x + unitStep N μ, ν)‖ ≤ e₂) (f₃ : ‖Nf (x + unitStep N ν, μ)‖ ≤ e₃)
    (f₄ : ‖Nf (x, ν)‖ ≤ e₄)
    (hM : ‖lieFormCurl M (x, μ, ν)‖ ≤ v / 16)
    (hsm : 8 * (κ * y) + 2 * (e₁ + e₂ + e₃ + e₄) ≤ 1 / 2) :
    plaquetteLogSize (fun c : TorusBond N => minimalLog (W c.1 c.2)) x μ ν ≤ 8 * (κ * y) + 2 * (e₁ + e₂ + e₃ + e₄) ∧
    ‖lieFormCurl (fun c : TorusBond N => minimalLog (W c.1 c.2)) (x, μ, ν) - lieFormCurl M (x, μ, ν) -
        lieFormCurl Nf (x, μ, ν)‖ ≤
      4 * κ * (y + (e₁ + e₂ + e₃ + e₄)) ^ 2 + 4 * ω ∧
    curvature W x μ ν ≤ v / 16 + (e₁ + e₂ + e₃ + e₄) + 4 * ω + 200 * κ ^ 2 * (y + (e₁ + e₂ + e₃ + e₄)) ^ 2 := by
  set B : TorusBond N → BlockAverages.imaginaryQuaternions := fun c => minimalLog (W c.1 c.2) with hB
  set h := e₁ + e₂ + e₃ + e₄ with hh
  have hκ0 : 0 ≤ κ := by linarith
  have hκy : 0 ≤ κ * y := mul_nonneg hκ0 hy
  have b₁ : ‖B (x, μ)‖ ≤ 2 * (κ * y + e₁) := (norm_minimalLog_le_two_mul _ (by linarith)).trans (by linarith)
  have b₂ : ‖B (x + unitStep N μ, ν)‖ ≤ 2 * (κ * y + e₂) :=
    (norm_minimalLog_le_two_mul _ (by linarith)).trans (by linarith)
  have b₃ : ‖B (x + unitStep N ν, μ)‖ ≤ 2 * (κ * y + e₃) :=
    (norm_minimalLog_le_two_mul _ (by linarith)).trans (by linarith)
  have b₄ : ‖B (x, ν)‖ ≤ 2 * (κ * y + e₄) := (norm_minimalLog_le_two_mul _ (by linarith)).trans (by linarith)
  have hS : plaquetteLogSize B x μ ν ≤ 8 * (κ * y) + 2 * h := by
    unfold plaquetteLogSize
    linarith
  have hS0 : 0 ≤ plaquetteLogSize B x μ ν := by
    unfold plaquetteLogSize
    positivity
  have hE : ‖lieFormCurl (fun c => B c - M c - Nf c) (x, μ, ν)‖ ≤ 4 * κ * (y + h) ^ 2 + 4 * ω := by
    refine (norm_lieFormCurl_le _ x μ ν).trans ?_
    unfold plaquetteLogSize
    have m₁ : (y + e₁) ^ 2 ≤ (y + h) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have m₂ : (y + e₂) ^ 2 ≤ (y + h) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have m₃ : (y + e₃) ^ 2 ≤ (y + h) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have m₄ : (y + e₄) ^ 2 ≤ (y + h) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have k₁ := mul_le_mul_of_nonneg_left m₁ hκ0
    have k₂ := mul_le_mul_of_nonneg_left m₂ hκ0
    have k₃ := mul_le_mul_of_nonneg_left m₃ hκ0
    have k₄ := mul_le_mul_of_nonneg_left m₄ hκ0
    linarith
  have hC : lieFormCurl (fun c => B c - M c - Nf c) (x, μ, ν) =
      lieFormCurl B (x, μ, ν) - lieFormCurl M (x, μ, ν) - lieFormCurl Nf (x, μ, ν) := by
    unfold lieFormCurl
    module
  refine ⟨hS, by rw [← hC]; exact hE, ?_⟩
  have hN : ‖lieFormCurl Nf (x, μ, ν)‖ ≤ h := by
    refine (norm_lieFormCurl_le _ x μ ν).trans ?_
    unfold plaquetteLogSize
    linarith
  have hCB : ‖lieFormCurl B (x, μ, ν)‖ ≤ v / 16 + h + 4 * κ * (y + h) ^ 2 + 4 * ω := by
    have e : lieFormCurl B (x, μ, ν) = lieFormCurl M (x, μ, ν) + lieFormCurl Nf (x, μ, ν) +
        lieFormCurl (fun c => B c - M c - Nf c) (x, μ, ν) := by
      rw [hC]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le (lieFormCurl M (x, μ, ν)) (lieFormCurl Nf (x, μ, ν))
    linarith
  obtain ⟨-, -, hcurl, -⟩ := hA
  have hexp : ∀ c : TorusBond N, W c.1 c.2 = BlockAverages.expUnit (B c) := fun c => (expUnit_minimalLog _).symm
  have hq := (hcurl N W (fun _ => 1) B x μ ν (hexp (x, μ)) (hexp (x + unitStep N μ, ν)) (hexp (x + unitStep N ν, μ))
      (hexp (x, ν)) (by linarith) (by
      have e : (fun b : TorusBond N =>
          minimalLog (ResponseInTheExpansion.gaugeTransform (fun _ => (1 : BlockAverages.UnitQuaternion)) W b)) = B := by
        funext b
        simp only [hB, ResponseInTheExpansion.gaugeTransform, one_mul, inv_one, mul_one]
      rw [e]
      linarith)).1
  have hc : curvature W x μ ν ≤ ‖lieFormCurl B (x, μ, ν)‖ + 3 * plaquetteLogSize B x μ ν ^ 2 := by
    have h0 : curvature W x μ ν = ‖((holonomy W x μ ν : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ := rfl
    rw [h0]
    have e : ((holonomy W x μ ν : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 =
        (((holonomy W x μ ν : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1 -
          ((lieFormCurl B (x, μ, ν) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])) +
        ((lieFormCurl B (x, μ, ν) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ]) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖((lieFormCurl B (x, μ, ν) : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ =
        ‖lieFormCurl B (x, μ, ν)‖ := rfl
    rw [h2]
    linarith
  have hsq : plaquetteLogSize B x μ ν ^ 2 ≤ (8 * (κ * y) + 2 * h) ^ 2 := pow_le_pow_left₀ hS0 hS 2
  have hh0 : 0 ≤ h := by positivity
  have h1 := sq_bound hκ hy hh0
  have h3 : 0 ≤ (y + h) ^ 2 := by positivity
  have h2 := mul_le_sq_mul hκ h3
  have e1 : 4 * κ * (y + h) ^ 2 = 4 * (κ * (y + h) ^ 2) := by ring
  have e2 : 200 * κ ^ 2 * (y + h) ^ 2 = 200 * (κ ^ 2 * (y + h) ^ 2) := by ring
  rw [e1] at hCB
  rw [e2]
  have h4 : 0 ≤ κ ^ 2 * (y + h) ^ 2 := by positivity
  linarith
private theorem small_consequences {κ A ς : ℝ} (hκ : 1 ≤ κ) (hA : 1 ≤ A) (hς : 0 ≤ ς)
    (h : 10 ^ 4 * κ ^ 2 * A ^ 2 * ς ≤ 1) :
    κ ^ 2 * A ^ 2 * ς ≤ 1 / 10 ^ 4 ∧ κ ^ 2 * (A * ς) ≤ 1 / 10 ^ 4 ∧ κ * (A * ς) ≤ 1 / 10 ^ 4 := by
  have h0 : κ ^ 2 * A ^ 2 * ς ≤ 1 / 10 ^ 4 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hA2 : A ≤ A ^ 2 := by nlinarith
  have hκ2 : κ ≤ κ ^ 2 := by nlinarith
  have hAς : 0 ≤ A * ς := by positivity
  have h1 : κ ^ 2 * (A * ς) ≤ κ ^ 2 * A ^ 2 * ς := by
    have := mul_le_mul_of_nonneg_right hA2 hς
    have h2 := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ κ ^ 2)
    calc κ ^ 2 * (A * ς) ≤ κ ^ 2 * (A ^ 2 * ς) := h2
      _ = κ ^ 2 * A ^ 2 * ς := by ring
  have h2 : κ * (A * ς) ≤ κ ^ 2 * (A * ς) := mul_le_mul_of_nonneg_right hκ2 hAς
  exact ⟨h0, h1.trans h0, (h2.trans h1).trans h0⟩
private theorem curvature_arith {κ A ς v ω h y : ℝ} (hκ : 1 ≤ κ) (hA : 1 ≤ A) (hv : 0 ≤ v) (hω : 0 ≤ ω)
    (hh : 0 ≤ h) (hy : 0 ≤ y)
    (hsm : 10 ^ 4 * κ ^ 2 * A ^ 2 * ς ≤ 1) (hς : v + ω ≤ ς) (hyh : y + h ≤ A * ς) (hyh' : y + h ≤ A * (v + ω) + h) :
    8 * (κ * y) + 2 * (h) ≤ 1 / 2 ∧ 200 * κ ^ 2 * (y + h) ^ 2 ≤ (v + ω + h) / 50 := by
  have hς0 : 0 ≤ ς := by linarith
  obtain ⟨n0, n1, n2⟩ := small_consequences hκ hA hς0 hsm
  constructor
  · have h1 : κ * (y + h) ≤ κ * (A * ς) := mul_le_mul_of_nonneg_left hyh (by linarith)
    have h2 : h ≤ κ * h := by
      have := mul_le_mul_of_nonneg_right hκ hh
      linarith
    have e : κ * (y + h) = κ * y + κ * h := by ring
    rw [e] at h1
    norm_num at n2
    linarith
  · have hvo : 0 ≤ v + ω := by linarith
    have h1 : (y + h) ^ 2 ≤ (A * ς) * (A * (v + ω) + h) := by
      rw [sq]
      exact mul_le_mul hyh hyh' (by linarith) (by positivity)
    have h2 : κ ^ 2 * (y + h) ^ 2 ≤ κ ^ 2 * ((A * ς) * (A * (v + ω) + h)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e : κ ^ 2 * ((A * ς) * (A * (v + ω) + h)) = (κ ^ 2 * A ^ 2 * ς) * (v + ω) + (κ ^ 2 * (A * ς)) * h := by ring
    rw [e] at h2
    have h3 := mul_le_mul_of_nonneg_right n0 hvo
    have h4 := mul_le_mul_of_nonneg_right n1 hh
    have e2 : 200 * κ ^ 2 * (y + h) ^ 2 = 200 * (κ ^ 2 * (y + h) ^ 2) := by ring
    rw [e2]
    norm_num at h3 h4
    linarith
private theorem supDist_add_unitStep_le_succ (x o : TorusSite N) (μ : Fin 4) :
    TorusFields.supDist (x + unitStep N μ) o ≤ TorusFields.supDist x o + 1 := by apply _root_.YangMills.SharedProofs.p13239 <;> assumption
private theorem pathSum_le_length_mul (f : TorusBond N → ℝ) (l : List (TorusBond N)) (a : ℝ) (h : ∀ c ∈ l, f c ≤ a) :
    pathSum f l ≤ l.length * a := by
  induction l with
  | nil => simp [pathSum]
  | cons c r ih =>
    have h1 := h c (by simp)
    have h2 := ih fun c' hc' => h c' (by simp [hc'])
    simp only [pathSum, List.map_cons, List.sum_cons, List.length_cons] at h2 ⊢
    push_cast
    linarith
private theorem pathSum_mono (f g : TorusBond N → ℝ) (l : List (TorusBond N)) (h : ∀ c ∈ l, f c ≤ g c) :
    pathSum f l ≤ pathSum g l := by
  induction l with
  | nil => simp [pathSum]
  | cons c r ih =>
    have h1 := h c (by simp)
    have h2 := ih fun c' hc' => h c' (by simp [hc'])
    simp only [pathSum, List.map_cons, List.sum_cons] at h2 ⊢
    linarith
private theorem pathSum_le_length_mul_add (f g : TorusBond N → ℝ) (a : ℝ) (l : List (TorusBond N))
    (h : ∀ c ∈ l, f c ≤ a + g c) :
    pathSum f l ≤ l.length * a + pathSum g l := by
  induction l with
  | nil => simp [pathSum]
  | cons c r ih =>
    have h1 := h c (by simp)
    have h2 := ih fun c' hc' => h c' (by simp [hc'])
    simp only [pathSum, List.map_cons, List.sum_cons, List.length_cons] at h2 ⊢
    push_cast
    linarith
private theorem pathSum_nonneg (e : TorusBond N → ℝ) (he : ∀ c, 0 ≤ e c) (l : List (TorusBond N)) :
    0 ≤ pathSum e l := by
  induction l with
  | nil => simp [pathSum]
  | cons c r ih =>
    have h1 := he c
    simp only [pathSum, List.map_cons, List.sum_cons] at ih ⊢
    linarith
private theorem pathSum_append (e : TorusBond N → ℝ) (l₁ l₂ : List (TorusBond N)) :
    pathSum e (l₁ ++ l₂) = pathSum e l₁ + pathSum e l₂ := by
  simp [pathSum]
private theorem plaquette_arith {κ v ω ε d A y h : ℝ} (hκ : 1 ≤ κ) (hv : 0 ≤ v) (hω : 0 ≤ ω) (hε : 0 ≤ ε)
    (hd0 : 0 ≤ d) (hdA : d + 2 ≤ A)
    (hA1 : 1 ≤ A) (hy : y = (d + 2) * v + ω) (hh0 : 0 ≤ h) (hh4 : h ≤ 4 * ε)
    (hsm : 10 ^ 4 * κ ^ 2 * A ^ 2 * (v + ω + 100 * A * ε) ≤ 1) :
    8 * (κ * y) + 2 * h ≤ 1 / 2 ∧ 200 * κ ^ 2 * (y + h) ^ 2 ≤ (v + ω + h) / 50 := by
  subst hy
  have hy0 : 0 ≤ (d + 2) * v + ω := by positivity
  have hyA : (d + 2) * v + ω ≤ A * (v + ω) := by
    have h1 : (d + 2) * v ≤ A * v := mul_le_mul_of_nonneg_right hdA hv
    have h2 : ω ≤ A * ω := by nlinarith
    have : A * (v + ω) = A * v + A * ω := by ring
    linarith
  have hyh : (d + 2) * v + ω + h ≤ A * (v + ω + 100 * A * ε) := by
    have e : A * (v + ω + 100 * A * ε) = A * (v + ω) + 100 * A * (A * ε) := by ring
    have h1 : A * ε ≥ ε := by nlinarith
    have h2 : 100 * A * (A * ε) ≥ 4 * ε := by nlinarith
    rw [e]
    linarith
  have hvo : v + ω ≤ v + ω + 100 * A * ε := by
    have : 0 ≤ 100 * A * ε := by positivity
    linarith
  exact curvature_arith hκ hA1 hv hω hh0 hy0 hsm hvo hyh (by linarith)
private theorem plaquette_curvature_bounds (hA : axialGaugePathBoundsStatement) (W : TorusField N)
    (M Nf : TorusBond N → BlockAverages.imaginaryQuaternions) (e : TorusBond N → ℝ) (o : TorusSite N)
    (D : ℕ) (v ω κ ε : ℝ) (hκ : 1 ≤ κ) (hv : 0 ≤ v) (hω : 0 ≤ ω) (hε : 0 ≤ ε) (he : ∀ c, 0 ≤ e c)
    (hg : ∀ c : TorusBond N, TorusFields.supDist c.1 o ≤ D →
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W c.1 c.2) ≤ κ * (weightedBondSize o v c + ω) + e c)
    (hl : ∀ c : TorusBond N, TorusFields.supDist c.1 o ≤ D →
      ‖minimalLog (W c.1 c.2) - M c - Nf c‖ ≤ κ * (weightedBondSize o v c + ω + e c) ^ 2 + ω)
    (hf : ∀ c, ‖Nf c‖ ≤ e c)
    (hM : ∀ (x : TorusSite N) (μ ν : Fin 4), μ < ν → ‖lieFormCurl M (x, μ, ν)‖ ≤ v / 16)
    (hsm : 10 ^ 4 * κ ^ 2 * ((D : ℝ) + 3) ^ 2 * (v + ω + 100 * ((D : ℝ) + 3) * ε) ≤ 1)
    (x : TorusSite N) (μ ν : Fin 4) (hμν : μ < ν) (hd : TorusFields.supDist x o + 1 ≤ D)
    (hb : ∀ c ∈ plaquetteBonds x μ ν, e c ≤ ε) :
    plaquetteLogSize (fun c : TorusBond N => minimalLog (W c.1 c.2)) x μ ν ≤
        8 * (κ * (((TorusFields.supDist x o : ℝ) + 2) * v + ω)) + 2 * plaquetteSum e x μ ν ∧
    ‖lieFormCurl (fun c : TorusBond N => minimalLog (W c.1 c.2)) (x, μ, ν) - lieFormCurl M (x, μ, ν) -
        lieFormCurl Nf (x, μ, ν)‖ ≤
      4 * κ * (((TorusFields.supDist x o : ℝ) + 2) * v + ω + plaquetteSum e x μ ν) ^ 2 + 4 * ω ∧
    curvature W x μ ν ≤ v / 2 + 2 * plaquetteSum e x μ ν + 5 * ω := by
  have hd0 : (0 : ℝ) ≤ (TorusFields.supDist x o : ℝ) := by positivity
  have hdD : (TorusFields.supDist x o : ℝ) + 1 ≤ D := by exact_mod_cast hd
  have hsz : ∀ c : TorusBond N, TorusFields.supDist c.1 o ≤ TorusFields.supDist x o + 1 →
      weightedBondSize o v c + ω ≤ ((TorusFields.supDist x o : ℝ) + 2) * v + ω := by
    intro c hc
    have h1 : (TorusFields.supDist c.1 o : ℝ) ≤ (TorusFields.supDist x o : ℝ) + 1 := by exact_mod_cast hc
    have h2 : (1 + (TorusFields.supDist c.1 o : ℝ)) * v ≤ ((TorusFields.supDist x o : ℝ) + 2) * v :=
      mul_le_mul_of_nonneg_right (by linarith) hv
    unfold weightedBondSize
    linarith
  have hsz0 : ∀ c : TorusBond N, 0 ≤ weightedBondSize o v c + ω := fun c => by
    unfold weightedBondSize
    positivity
  have hκ0 : 0 ≤ κ := by linarith
  have hgap : ∀ c : TorusBond N, TorusFields.supDist c.1 o ≤ TorusFields.supDist x o + 1 →
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W c.1 c.2) ≤ κ * (((TorusFields.supDist x o : ℝ) + 2) * v + ω) + e c := fun c hc =>
    (hg c (hc.trans hd)).trans (by
      have := mul_le_mul_of_nonneg_left (hsz c hc) hκ0
      linarith)
  have hlog : ∀ c : TorusBond N, TorusFields.supDist c.1 o ≤ TorusFields.supDist x o + 1 →
      ‖minimalLog (W c.1 c.2) - M c - Nf c‖ ≤ κ * (((TorusFields.supDist x o : ℝ) + 2) * v + ω + e c) ^ 2 + ω := fun c hc =>
    (hl c (hc.trans hd)).trans (by
      have h1 : (weightedBondSize o v c + ω + e c) ^ 2 ≤ (((TorusFields.supDist x o : ℝ) + 2) * v + ω + e c) ^ 2 :=
        pow_le_pow_left₀ (add_nonneg (hsz0 c) (he c)) (by linarith [hsz c hc]) 2
      have := mul_le_mul_of_nonneg_left h1 hκ0
      linarith)
  have c₁ : TorusFields.supDist x o ≤ TorusFields.supDist x o + 1 := by omega
  have c₂ : TorusFields.supDist (x + unitStep N μ) o ≤ TorusFields.supDist x o + 1 := supDist_add_unitStep_le_succ x o μ
  have c₃ : TorusFields.supDist (x + unitStep N ν) o ≤ TorusFields.supDist x o + 1 := supDist_add_unitStep_le_succ x o ν
  have b₁ : e (x, μ) ≤ ε := hb _ (by simp [plaquetteBonds])
  have b₂ : e (x + unitStep N μ, ν) ≤ ε := hb _ (by simp [plaquetteBonds])
  have b₃ : e (x + unitStep N ν, μ) ≤ ε := hb _ (by simp [plaquetteBonds])
  have b₄ : e (x, ν) ≤ ε := hb _ (by simp [plaquetteBonds])
  have p₁ := he (x, μ)
  have p₂ := he (x + unitStep N μ, ν)
  have p₃ := he (x + unitStep N ν, μ)
  have p₄ := he (x, ν)
  have hh0 : 0 ≤ e (x, μ) + e (x + unitStep N μ, ν) + e (x + unitStep N ν, μ) + e (x, ν) := by positivity
  obtain ⟨n1, n2⟩ := plaquette_arith (A := (D : ℝ) + 3) (y := ((TorusFields.supDist x o : ℝ) + 2) * v + ω)
    (h := e (x, μ) + e (x + unitStep N μ, ν) + e (x + unitStep N ν, μ) + e (x, ν)) hκ hv hω hε hd0 (by linarith)
    (by linarith) rfl hh0 (by linarith) hsm
  obtain ⟨r1, r2, r3⟩ := plaquette_bounds hA W M Nf x μ ν (e (x, μ)) (e (x + unitStep N μ, ν))
    (e (x + unitStep N ν, μ)) (e (x, ν))
    (((TorusFields.supDist x o : ℝ) + 2) * v + ω) κ v ω p₁ p₂ p₃ p₄ hκ (by positivity) hv hω
    (hgap (x, μ) c₁) (hgap (x + unitStep N μ, ν) c₂) (hgap (x + unitStep N ν, μ) c₃) (hgap (x, ν) c₁)
    (hlog (x, μ) c₁) (hlog (x + unitStep N μ, ν) c₂) (hlog (x + unitStep N ν, μ) c₃) (hlog (x, ν) c₁)
    (hf _) (hf _) (hf _) (hf _) (hM x μ ν hμν) n1
  rw [plaquetteSum_eq]
  refine ⟨r1, r2, r3.trans ?_⟩
  linarith
private theorem total_small {κ v ω ε d A h H : ℝ} (hκ : 1 ≤ κ) (hv : 0 ≤ v) (hω : 0 ≤ ω) (hε : 0 ≤ ε) (hd : 0 ≤ d)
    (hdA : d + 3 ≤ A) (hh : 0 ≤ h) (hH : H ≤ (16 * d + 20) * ε) (hh4 : h ≤ 4 * ε)
    (hsm : 10 ^ 4 * κ ^ 2 * A ^ 2 * (v + ω + 100 * A * ε) ≤ 1) : (d + 2) * (v + ω + h) + H ≤ 1 / 10 ^ 4 := by
  have hA1 : 1 ≤ A := by linarith
  have hς0 : 0 ≤ v + ω + 100 * A * ε := by positivity
  obtain ⟨-, -, n2⟩ := small_consequences hκ hA1 hς0 hsm
  have hUs : (d + 2) * (v + ω + h) + H ≤ A * (v + ω + 100 * A * ε) := by
    have e : A * (v + ω + 100 * A * ε) = A * (v + ω) + 100 * (A * (A * ε)) := by ring
    have a1 : (d + 2) * (v + ω) ≤ A * (v + ω) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have a2 : (d + 2) * h ≤ A * (4 * ε) := mul_le_mul (by linarith) hh4 hh (by linarith)
    have a3 : (16 * d + 20) * ε ≤ 20 * A * ε := by
      have : 16 * d + 20 ≤ 20 * A := by linarith
      exact mul_le_mul_of_nonneg_right this hε
    have a4 : A * ε ≤ A * (A * ε) := by
      have h1 : ε ≤ A * ε := by nlinarith
      exact mul_le_mul_of_nonneg_left h1 (by linarith)
    have a5 : 0 ≤ A * ε := by positivity
    rw [e]
    have e2 : (d + 2) * (v + ω + h) = (d + 2) * (v + ω) + (d + 2) * h := by ring
    have e3 : 20 * A * ε = 20 * (A * ε) := by ring
    have e4 : A * (4 * ε) = 4 * (A * ε) := by ring
    rw [e2]
    rw [e3] at a3
    rw [e4] at a2
    linarith
  have h1 : A * (v + ω + 100 * A * ε) ≤ κ * (A * (v + ω + 100 * A * ε)) := by
    have h0 : 0 ≤ A * (v + ω + 100 * A * ε) := by positivity
    have := mul_le_mul_of_nonneg_right hκ h0
    linarith
  linarith
private theorem gauge_curvature_product_le {κ v ω d h H U A₁ Q : ℝ} (hκ : 1 ≤ κ) (hv : 0 ≤ v) (hω : 0 ≤ ω)
    (hd : 0 ≤ d) (hh : 0 ≤ h) (hH0 : 0 ≤ H)
    (hU : U = (d + 2) * (v + ω + h) + H) (hA₁ : A₁ ≤ 4 * d * (κ * ((1 + d) * v + ω)) + H)
    (hQ : Q ≤ v / 2 + 2 * h + 5 * ω)
    (hQ0 : 0 ≤ Q) : A₁ * Q ≤ 25 * (κ * U ^ 2) := by
  have hd2 : 0 ≤ d + 2 := by linarith
  have hp0 : 0 ≤ v + ω + h := by positivity
  have hP0 : 0 ≤ (d + 2) * (v + ω + h) := by positivity
  have hPU : (d + 2) * (v + ω + h) ≤ U := by linarith
  have hHU : H ≤ U := by linarith
  have hU0 : 0 ≤ U := hH0.trans hHU
  have hP1 : v + ω + h ≤ (d + 2) * (v + ω + h) := by
    have : (d + 1) * (v + ω + h) ≥ 0 := by positivity
    linarith [this]
  have hvo : (d + 2) * (v + ω) ≤ U := by
    have : (d + 2) * (v + ω) ≤ (d + 2) * (v + ω + h) := mul_le_mul_of_nonneg_left (by linarith) hd2
    linarith
  have hp5 : v / 2 + 2 * h + 5 * ω ≤ 5 * (v + ω + h) := by linarith
  have a1 : 4 * d * (κ * ((1 + d) * v + ω)) ≤ 4 * κ * ((d + 2) * ((d + 2) * (v + ω))) := by
    have b1 : (1 + d) * v + ω ≤ (d + 2) * (v + ω) := by
      have c2 : ω ≤ (d + 2) * ω := by
        have : 0 ≤ (d + 1) * ω := by positivity
        linarith
      have e : (d + 2) * (v + ω) = (d + 2) * v + (d + 2) * ω := by ring
      linarith
    have b2 : κ * ((1 + d) * v + ω) ≤ κ * ((d + 2) * (v + ω)) := mul_le_mul_of_nonneg_left b1 (by linarith)
    have b3 : 4 * d * (κ * ((1 + d) * v + ω)) ≤ 4 * d * (κ * ((d + 2) * (v + ω))) :=
      mul_le_mul_of_nonneg_left b2 (by linarith)
    have b5 : 0 ≤ κ * ((d + 2) * (v + ω)) := by
      have : 0 ≤ κ := by linarith
      positivity
    have e : 4 * (d + 2) * (κ * ((d + 2) * (v + ω))) = 4 * κ * ((d + 2) * ((d + 2) * (v + ω))) := by ring
    linarith
  have a2 : (d + 2) * ((d + 2) * (v + ω)) ≤ (d + 2) * U := mul_le_mul_of_nonneg_left hvo hd2
  have a3 : A₁ ≤ 4 * κ * ((d + 2) * U) + H := by
    have := mul_le_mul_of_nonneg_left a2 (by linarith : 0 ≤ 4 * κ)
    linarith
  have a4 : Q ≤ 5 * (v + ω + h) := hQ.trans hp5
  have a5 : A₁ * Q ≤ (4 * κ * ((d + 2) * U) + H) * (5 * (v + ω + h)) :=
    mul_le_mul a3 a4 hQ0 (by positivity)
  have e : (4 * κ * ((d + 2) * U) + H) * (5 * (v + ω + h)) =
      20 * (κ * U * ((d + 2) * (v + ω + h))) + 5 * (H * (v + ω + h)) := by ring
  have a6 : κ * U * ((d + 2) * (v + ω + h)) ≤ κ * U * U := mul_le_mul_of_nonneg_left hPU (by positivity)
  have a7 : H * (v + ω + h) ≤ U * U := mul_le_mul hHU (hP1.trans hPU) hp0 hU0
  have a8 : U * U ≤ κ * (U * U) := by
    have := mul_le_mul_of_nonneg_right hκ (mul_nonneg hU0 hU0)
    linarith
  have e2 : κ * U * U = κ * U ^ 2 := by ring
  have e3 : κ * (U * U) = κ * U ^ 2 := by ring
  rw [e] at a5
  rw [e2] at a6
  rw [e3] at a8
  linarith
private theorem four_terms_le {κ U a b c e : ℝ} (hκ : 1 ≤ κ) (ha : a ≤ 25 * (κ * U ^ 2)) (hb : b ≤ 16384 * U ^ 2)
    (hc : c ≤ 64 * (κ ^ 2 * U ^ 2)) (he : e ≤ 4 * (κ * U ^ 2)) :
    2 * a + 3 * b + 3 * c + e ≤ 2 * 10 ^ 5 * κ ^ 2 * U ^ 2 := by
  have hU2 : 0 ≤ U ^ 2 := by positivity
  have hκ1 : 1 ≤ κ ^ 2 := by nlinarith
  have hZ : U ^ 2 ≤ κ ^ 2 * U ^ 2 := by
    have := mul_le_mul_of_nonneg_right hκ1 hU2
    linarith
  have hκZ := mul_le_sq_mul hκ hU2
  have e5 : 2 * 10 ^ 5 * κ ^ 2 * U ^ 2 = 200000 * (κ ^ 2 * U ^ 2) := by ring
  rw [e5]
  linarith
private theorem path_arith {κ v ω ε d A h H G s A₁ Q Sa Sb : ℝ} (hκ : 1 ≤ κ) (hv : 0 ≤ v) (hω : 0 ≤ ω)
    (hε : 0 ≤ ε) (hd : 0 ≤ d)
    (hdA : d + 3 ≤ A) (hh : 0 ≤ h) (hhH : h ≤ H) (hH : H ≤ (16 * d + 20) * ε) (hh4 : h ≤ 4 * ε)
    (hsm : 10 ^ 4 * κ ^ 2 * A ^ 2 * (v + ω + 100 * A * ε) ≤ 1) (hs : s = v / 2 + 5 * ω)
    (hG : G = 3 * (d + 2) * s + H)
    (hA₁ : A₁ ≤ 4 * d * (κ * ((1 + d) * v + ω)) + H) (hQ : Q ≤ v / 2 + 2 * h + 5 * ω) (hQ0 : 0 ≤ Q)
    (hSa : Sa ≤ 8 * G) (hSa0 : 0 ≤ Sa) (hSb : Sb ≤ 8 * (κ * ((d + 2) * v + ω)) + 2 * h) (hSb0 : 0 ≤ Sb) :
    G ≤ 1 / 500 ∧ 2 * G ≤ 62 * ((d + 2) * (v + ω + h) + H) ∧
    2 * (A₁ * Q) + 3 * Sa ^ 2 + 3 * Sb ^ 2 + 4 * κ * ((d + 2) * v + ω + h) ^ 2 ≤
      2 * 10 ^ 5 * κ ^ 2 * ((d + 2) * (v + ω + h) + H) ^ 2 := by
  subst hs hG
  have hH0 : 0 ≤ H := hh.trans hhH
  have hUsm := total_small hκ hv hω hε hd hdA hh hH hh4 hsm
  obtain ⟨U, hU⟩ : ∃ U, U = (d + 2) * (v + ω + h) + H := ⟨_, rfl⟩
  have hAQ := gauge_curvature_product_le hκ hv hω hd hh hH0 hU hA₁ hQ hQ0
  rw [← hU] at hUsm ⊢
  have hd2 : 0 ≤ d + 2 := by linarith
  have hP0 : 0 ≤ (d + 2) * (v + ω + h) := by positivity
  have hHU : H ≤ U := by linarith
  have hvo : (d + 2) * (v + ω) ≤ U := by
    have : (d + 2) * (v + ω) ≤ (d + 2) * (v + ω + h) := mul_le_mul_of_nonneg_left (by linarith) hd2
    linarith
  have hG15 : 3 * (d + 2) * (v / 2 + 5 * ω) ≤ 15 * U := by
    have e : 3 * (d + 2) * (v / 2 + 5 * ω) ≤ 15 * ((d + 2) * (v + ω)) := by
      have c1 : 0 ≤ (d + 2) * v := by positivity
      have e1 : 3 * (d + 2) * (v / 2 + 5 * ω) = 3 / 2 * ((d + 2) * v) + 15 * ((d + 2) * ω) := by ring
      have e2 : 15 * ((d + 2) * (v + ω)) = 15 * ((d + 2) * v) + 15 * ((d + 2) * ω) := by ring
      rw [e1, e2]
      linarith
    linarith
  have hu4 : (1 : ℝ) / 10 ^ 4 = 1 / 10000 := by norm_num
  rw [hu4] at hUsm
  refine ⟨by linarith, by linarith, ?_⟩
  have hSa' : Sa ≤ 128 * U := by linarith
  have hSa2 : Sa ^ 2 ≤ 16384 * U ^ 2 := by
    calc Sa ^ 2 ≤ (128 * U) ^ 2 := pow_le_pow_left₀ hSa0 hSa' 2
      _ = 16384 * U ^ 2 := by ring
  have hyU : (d + 2) * v + ω + h ≤ U := by
    have a1 : (d + 2) * v + ω ≤ (d + 2) * (v + ω) := by
      have : 0 ≤ (d + 1) * ω := by positivity
      have e : (d + 2) * (v + ω) = (d + 2) * v + (d + 1) * ω + ω := by ring
      linarith
    have a2 : h ≤ (d + 2) * h := by
      have : 0 ≤ (d + 1) * h := by positivity
      linarith
    have e2 : (d + 2) * (v + ω + h) = (d + 2) * (v + ω) + (d + 2) * h := by ring
    linarith
  have hκ0 : 0 ≤ κ := by linarith
  have hSb' : Sb ≤ 8 * κ * U := by
    have a1 : κ * ((d + 2) * v + ω) ≤ κ * (U - h) := mul_le_mul_of_nonneg_left (by linarith) hκ0
    have a2 : h ≤ κ * h := by
      have := mul_le_mul_of_nonneg_right hκ hh
      linarith
    have e : κ * (U - h) = κ * U - κ * h := by ring
    have e2 : 8 * κ * U = 8 * (κ * U) := by ring
    rw [e2]
    linarith
  have hSb2 : Sb ^ 2 ≤ 64 * (κ ^ 2 * U ^ 2) := by
    calc Sb ^ 2 ≤ (8 * κ * U) ^ 2 := pow_le_pow_left₀ hSb0 hSb' 2
      _ = 64 * (κ ^ 2 * U ^ 2) := by ring
  have hy2 : 4 * κ * ((d + 2) * v + ω + h) ^ 2 ≤ 4 * (κ * U ^ 2) := by
    have h1 : ((d + 2) * v + ω + h) ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ (by positivity) hyU 2
    have h2 := mul_le_mul_of_nonneg_left h1 hκ0
    have e : 4 * κ * ((d + 2) * v + ω + h) ^ 2 = 4 * (κ * ((d + 2) * v + ω + h) ^ 2) := by ring
    rw [e]
    linarith
  exact four_terms_le hκ hAQ hSa2 hSb2 hy2
private theorem distFromOne_gauged_le (hA : axialGaugePathBoundsStatement) (ℓ : TorusLumps.StepParameters)
    (W W₀ : TorusField N) (o : TorusSite N) (b : TorusBond N) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W b) ≤
      _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W₀ o) W₀ b) +
      (pathSum (fun c => ‖((W c.1 c.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
          (W₀ c.1 c.2 : BlockAverages.UnitQuaternion)‖) (latticePath o b.1) +
        ‖((W b.1 b.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - (W₀ b.1 b.2 : BlockAverages.UnitQuaternion)‖ +
        pathSum (fun c => ‖((W c.1 c.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
          (W₀ c.1 c.2 : BlockAverages.UnitQuaternion)‖) (latticePath o (b.1 + unitStep N b.2))) := by
  have h1 := (hA.1 ℓ N o b.1).2.1 W W₀
  have h2 := (hA.1 ℓ N o (b.1 + unitStep N b.2)).2.1 W W₀
  have h3 := norm_mul_sub_mul_le (axialGaugeAt ℓ W o b.1 * W b.1 b.2) (axialGaugeAt ℓ W₀ o b.1 * W₀ b.1 b.2)
    (axialGaugeAt ℓ W o (b.1 + unitStep N b.2))⁻¹ (axialGaugeAt ℓ W₀ o (b.1 + unitStep N b.2))⁻¹
  have h4 := norm_mul_sub_mul_le (axialGaugeAt ℓ W o b.1) (axialGaugeAt ℓ W₀ o b.1) (W b.1 b.2) (W₀ b.1 b.2)
  rw [norm_inv_sub_inv] at h3
  have h5 := norm_sub_le_norm_sub_add_norm_sub
    ((ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W b : BlockAverages.UnitQuaternion) : ℍ[ℝ])
    ((ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W₀ o) W₀ b : BlockAverages.UnitQuaternion) : ℍ[ℝ]) 1
  have e1 : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W b) =
      ‖((ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W b : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ := rfl
  have e2 : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W₀ o) W₀ b) =
      ‖((ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W₀ o) W₀ b : BlockAverages.UnitQuaternion) : ℍ[ℝ]) - 1‖ := rfl
  have e3 : ‖((ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W b : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
      ((ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W₀ o) W₀ b : BlockAverages.UnitQuaternion) : ℍ[ℝ])‖ ≤
      ‖((axialGaugeAt ℓ W o b.1 * W b.1 b.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
          ((axialGaugeAt ℓ W₀ o b.1 * W₀ b.1 b.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ])‖ +
        ‖((axialGaugeAt ℓ W o (b.1 + unitStep N b.2) : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
          (axialGaugeAt ℓ W₀ o (b.1 + unitStep N b.2) : BlockAverages.UnitQuaternion)‖ := h3
  rw [e1, e2]
  linarith
private theorem plaquetteSum_zero (x : TorusSite N) (μ ν : Fin 4) : plaquetteSum (fun _ => (0 : ℝ)) x μ ν = 0 := by
  rw [plaquetteSum_eq]
  simp
end CurlOverReference
set_option maxHeartbeats 1600000 in
open CurlOverReference in
theorem curlOverReference (hA : axialGaugePathBoundsStatement) : curlOverReferenceStatement := by
  intro ℓ N _ o D W W₀ M Nf e v ω κ ε hR hκ hv hω hε hN hsm
  refine ⟨fun x μ ν hμν hd hb => (plaquette_curvature_bounds hA W M Nf e o D v ω κ ε hκ hv hω hε hR.size_nonneg
    hR.distFromOne_field_le hR.log_field_le hR.free_le hR.curl_le hsm x μ ν hμν hd hb).2.2, ?_⟩
  intro x μ ν hμν hd hb
  have hbonds : ∀ c ∈ plaquetteBonds x μ ν, e c ≤ ε := fun c hc => hb c (by simp [plaquettePathBonds, hc])
  have hcu := plaquette_curvature_bounds hA W M Nf e o D v ω κ ε hκ hv hω hε hR.size_nonneg hR.distFromOne_field_le
    hR.log_field_le hR.free_le hR.curl_le hsm x μ ν hμν (by omega) hbonds
  have hcur₀ : ∀ (y : TorusSite N) (μ' ν' : Fin 4), μ' < ν' → TorusFields.supDist y o + 1 ≤ D →
      curvature W₀ y μ' ν' ≤ v / 2 + 5 * ω := by
    intro y μ' ν' h1 h2
    have := (plaquette_curvature_bounds hA W₀ M (fun _ => 0) (fun _ => 0) o D v ω κ ε hκ hv hω hε (fun _ => le_rfl)
      (fun c hc => by simpa using hR.distFromOne_reference_le c hc)
      (fun c hc => by simpa using hR.log_reference_le c hc)
      (fun c => by simp) hR.curl_le hsm y μ' ν' h1 h2 (fun c _ => hε)).2.2
    rw [plaquetteSum_zero] at this
    linarith
  have hs0 : 0 ≤ v / 2 + 5 * ω := by positivity
  have hrN : 2 * (TorusFields.supDist x o + 2) + 2 < N := by omega
  have hnear₀ := hA.2.1 ℓ N o W₀ (TorusFields.supDist x o + 2) (v / 2 + 5 * ω) hrN hs0
    (fun y μ' ν' h1 h2 _ _ _ => hcur₀ y μ' ν' h1 (by omega))
  have z₁ : TorusFields.supDist (x + unitStep N μ) o ≤ TorusFields.supDist x o + 1 := supDist_add_unitStep_le_succ x o μ
  have z₂ : TorusFields.supDist (x + unitStep N ν) o ≤ TorusFields.supDist x o + 1 := supDist_add_unitStep_le_succ x o ν
  have z₃ : TorusFields.supDist (x + unitStep N μ + unitStep N ν) o ≤ TorusFields.supDist x o + 2 :=
    (supDist_add_unitStep_le_succ _ o ν).trans (by omega)
  have hcomm : x + unitStep N ν + unitStep N μ = x + unitStep N μ + unitStep N ν := by abel
  have hS : ∀ z : TorusSite N, TorusFields.supDist z o ≤ D →
      pathSum (fun c => ‖((W c.1 c.2 : BlockAverages.UnitQuaternion) : ℍ[ℝ]) -
        (W₀ c.1 c.2 : BlockAverages.UnitQuaternion)‖) (latticePath o z) ≤ pathSum e (latticePath o z) := by
    intro z hz
    refine pathSum_mono _ _ _ fun c hc => hR.norm_sub_reference_le c (((hA.1 ℓ N o z).2.2.1 c hc).trans hz)
  have hS₀ := hS x (by omega)
  have hS₁ := hS (x + unitStep N μ) (by omega)
  have hS₂ := hS (x + unitStep N ν) (by omega)
  have hS₃ := hS (x + unitStep N μ + unitStep N ν) (by omega)
  have he := hR.size_nonneg
  have q₀ := pathSum_nonneg e he (latticePath o x)
  have q₁ := pathSum_nonneg e he (latticePath o (x + unitStep N μ))
  have q₂ := pathSum_nonneg e he (latticePath o (x + unitStep N ν))
  have q₃ := pathSum_nonneg e he (latticePath o (x + unitStep N μ + unitStep N ν))
  have hP : pathSum e (plaquettePathBonds o x μ ν) = pathSum e (latticePath o x) +
      pathSum e (latticePath o (x + unitStep N μ)) +
      pathSum e (latticePath o (x + unitStep N ν)) + pathSum e (latticePath o (x + unitStep N μ + unitStep N ν)) +
      plaquetteSum e x μ ν := by
    unfold plaquettePathBonds plaquetteSum
    rw [pathSum_append, pathSum_append, pathSum_append, pathSum_append]
  have hp := plaquetteSum_eq e x μ ν
  have p₁ := he (x, μ)
  have p₂ := he (x + unitStep N μ, ν)
  have p₃ := he (x + unitStep N ν, μ)
  have p₄ := he (x, ν)
  have hb₁ := hnear₀ (x, μ) (by simp) (by simpa using z₁.trans (by omega))
  have hb₂ := hnear₀ (x + unitStep N μ, ν) (by simpa using z₁.trans (by omega)) (by simpa using z₃)
  have hb₃ := hnear₀ (x + unitStep N ν, μ) (by simpa using z₂.trans (by omega)) (by simpa [hcomm] using z₃)
  have hb₄ := hnear₀ (x, ν) (by simp) (by simpa using z₂.trans (by omega))
  have g₁ := distFromOne_gauged_le hA ℓ W W₀ o (x, μ)
  have g₂ := distFromOne_gauged_le hA ℓ W W₀ o (x + unitStep N μ, ν)
  have g₃ := distFromOne_gauged_le hA ℓ W W₀ o (x + unitStep N ν, μ)
  have g₄ := distFromOne_gauged_le hA ℓ W W₀ o (x, ν)
  simp only [hcomm] at g₃
  have w₁ := hR.norm_sub_reference_le (x, μ) (by simp; omega)
  have w₂ := hR.norm_sub_reference_le (x + unitStep N μ, ν) (by simpa using z₁.trans (by omega))
  have w₃ := hR.norm_sub_reference_le (x + unitStep N ν, μ) (by simpa using z₂.trans (by omega))
  have w₄ := hR.norm_sub_reference_le (x, ν) (by simp; omega)
  dsimp only at g₁ g₂ g₃ g₄ w₁ w₂ w₃ w₄ hb₁ hb₂ hb₃ hb₄
  obtain ⟨d, hdd⟩ : ∃ d : ℝ, d = (TorusFields.supDist x o : ℝ) := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := by rw [hdd]; positivity
  have hcast : ((TorusFields.supDist x o + 2 : ℕ) : ℝ) = d + 2 := by rw [hdd]; push_cast; ring
  rw [hcast] at hb₁ hb₂ hb₃ hb₄
  obtain ⟨h, hhd⟩ : ∃ h : ℝ, h = plaquetteSum e x μ ν := ⟨_, rfl⟩
  obtain ⟨H, hHd⟩ : ∃ H : ℝ, H = pathSum e (plaquettePathBonds o x μ ν) := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G : ℝ, G = 3 * (d + 2) * (v / 2 + 5 * ω) + H := ⟨_, rfl⟩
  rw [← hdd, ← hhd, ← hHd]
  rw [← hhd] at hP hp
  rw [← hHd] at hP
  rw [← hdd, ← hhd] at hcu
  have hh0 : 0 ≤ h := by rw [hp]; positivity
  have hhH : h ≤ H := by rw [hP]; linarith
  have hh4 : h ≤ 4 * ε := by
    have := pathSum_le_length_mul e (plaquetteBonds x μ ν) ε hbonds
    rw [hhd]
    simpa [plaquetteBonds, plaquetteSum] using this
  have hlen : ((plaquettePathBonds o x μ ν).length : ℝ) ≤ 16 * d + 20 := by
    have l₀ := (hA.1 ℓ N o x).2.2.2
    have l₁ := (hA.1 ℓ N o (x + unitStep N μ)).2.2.2
    have l₂ := (hA.1 ℓ N o (x + unitStep N ν)).2.2.2
    have l₃ := (hA.1 ℓ N o (x + unitStep N μ + unitStep N ν)).2.2.2
    have : (plaquettePathBonds o x μ ν).length ≤ 16 * TorusFields.supDist x o + 20 := by
      simp only [plaquettePathBonds, plaquetteBonds, List.length_append, List.length_cons, List.length_nil]
      omega
    have h2 : ((plaquettePathBonds o x μ ν).length : ℝ) ≤ ((16 * TorusFields.supDist x o + 20 : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [hdd]
    push_cast at h2
    exact h2
  have hH : H ≤ (16 * d + 20) * ε := by
    rw [hHd]
    exact (pathSum_le_length_mul e _ ε hb).trans (mul_le_mul_of_nonneg_right hlen hε)
  have hdD : d + 3 ≤ (D : ℝ) := by
    rw [hdd]
    exact_mod_cast hd
  have hD0 : (0 : ℝ) ≤ D := by positivity
  have k₁ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W (x, μ)) ≤ G := by
    rw [hGd]
    linarith
  have k₂ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W (x + unitStep N μ, ν)) ≤ G := by
    rw [hGd]
    linarith
  have k₃ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W (x + unitStep N ν, μ)) ≤ G := by
    rw [hGd]
    linarith
  have k₄ : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W (x, ν)) ≤ G := by
    rw [hGd]
    linarith
  have hgx : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (axialGaugeAt ℓ W o x) ≤ 4 * d * (κ * ((1 + d) * v + ω)) + H := by
    have hκ0 : 0 ≤ κ := by linarith
    have a0 : 0 ≤ κ * ((1 + d) * v + ω) := by positivity
    have a1 := (hA.1 ℓ N o x).1 W
    have a2 := pathSum_le_length_mul_add (fun c : TorusBond N => _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (W c.1 c.2)) e
      (κ * ((1 + d) * v + ω)) (latticePath o x) (fun c hc => by
      have c1 := (hA.1 ℓ N o x).2.2.1 c hc
      have c2 := hR.distFromOne_field_le c (c1.trans (by omega))
      have c3 : (TorusFields.supDist c.1 o : ℝ) ≤ d := by
        rw [hdd]
        exact_mod_cast c1
      have c4 : weightedBondSize o v c ≤ (1 + d) * v := mul_le_mul_of_nonneg_right (by linarith) hv
      have c5 : κ * (weightedBondSize o v c + ω) ≤ κ * ((1 + d) * v + ω) :=
        mul_le_mul_of_nonneg_left (by linarith) hκ0
      linarith)
    have a3 : ((latticePath o x).length : ℝ) ≤ 4 * d := by
      have := (hA.1 ℓ N o x).2.2.2
      rw [hdd]
      exact_mod_cast this
    have a4 := mul_le_mul_of_nonneg_right a3 a0
    have a5 : pathSum e (latticePath o x) ≤ H := by
      rw [hP]
      linarith
    have e1 : 4 * d * (κ * ((1 + d) * v + ω)) = 4 * d * (κ * ((1 + d) * v + ω)) := rfl
    linarith
  have hG0 : 0 ≤ G := (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne_nonneg _).trans k₁
  have hcur := hcu.2.2
  have hQ0 : 0 ≤ curvature W x μ ν := norm_nonneg _
  have hB0 : 0 ≤ plaquetteLogSize (fun c : TorusBond N => minimalLog (W c.1 c.2)) x μ ν := by
    unfold plaquetteLogSize
    positivity
  have hGs := (path_arith (A := (D : ℝ) + 3) (s := v / 2 + 5 * ω) (Sa := 8 * G) hκ hv hω hε hd0 (by linarith)
    hh0 hhH hH hh4 hsm rfl hGd
    hgx hcur hQ0 le_rfl (by positivity) hcu.1 hB0).1
  have hax : axialCoords ℓ W o = fun b => minimalLog (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W b) := rfl
  have m₁ : ‖minimalLog (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W (x, μ))‖ ≤ 2 * G :=
    (norm_minimalLog_le_two_mul _ (by linarith)).trans (by linarith)
  have m₂ : ‖minimalLog (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W (x + unitStep N μ, ν))‖ ≤ 2 * G :=
    (norm_minimalLog_le_two_mul _ (by linarith)).trans (by linarith)
  have m₃ : ‖minimalLog (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W (x + unitStep N ν, μ))‖ ≤ 2 * G :=
    (norm_minimalLog_le_two_mul _ (by linarith)).trans (by linarith)
  have m₄ : ‖minimalLog (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W (x, ν))‖ ≤ 2 * G :=
    (norm_minimalLog_le_two_mul _ (by linarith)).trans (by linarith)
  have hSa : plaquetteLogSize (fun b => minimalLog (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W b))
      x μ ν ≤ 8 * G := by
    unfold plaquetteLogSize
    linarith
  have hSa0 : 0 ≤ plaquetteLogSize (fun b => minimalLog (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W b))
      x μ ν := by
    unfold plaquetteLogSize
    positivity
  obtain ⟨-, hG62, hnum⟩ := path_arith (A := (D : ℝ) + 3) (s := v / 2 + 5 * ω) hκ hv hω hε hd0 (by linarith)
    hh0 hhH hH hh4 hsm rfl hGd
    hgx hcur hQ0 hSa hSa0 hcu.1 hB0
  have hn1 := (plaquette_arith (A := (D : ℝ) + 3) (y := (d + 2) * v + ω) (h := h) hκ hv hω hε hd0 (by linarith)
    (by linarith) rfl hh0 hh4 hsm).1
  have hexp : ∀ c : TorusBond N, W c.1 c.2 = BlockAverages.expUnit (minimalLog (W c.1 c.2)) :=
    fun c => (expUnit_minimalLog _).symm
  have hcl := (hA.2.2.1 N W (axialGaugeAt ℓ W o) (fun c => minimalLog (W c.1 c.2)) x μ ν (hexp (x, μ))
    (hexp (x + unitStep N μ, ν))
    (hexp (x + unitStep N ν, μ)) (hexp (x, ν)) (by linarith [hcu.1]) (by linarith)).2
  rw [hax]
  refine ⟨?_, fun c hc => ?_⟩
  · have e : lieFormCurl (fun b => minimalLog (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W b)) (x, μ, ν) -
          lieFormCurl M (x, μ, ν) - lieFormCurl Nf (x, μ, ν) =
        (lieFormCurl (fun b => minimalLog (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W b)) (x, μ, ν) -
            lieFormCurl (fun c : TorusBond N => minimalLog (W c.1 c.2)) (x, μ, ν)) +
          (lieFormCurl (fun c : TorusBond N => minimalLog (W c.1 c.2)) (x, μ, ν) - lieFormCurl M (x, μ, ν) -
            lieFormCurl Nf (x, μ, ν)) := by
      module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have c1 := hcu.2.1
    have c2 : ‖lieFormCurl (fun b => minimalLog (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W b)) (x, μ, ν) -
          lieFormCurl (fun c : TorusBond N => minimalLog (W c.1 c.2)) (x, μ, ν)‖ ≤
        2 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (axialGaugeAt ℓ W o x) * curvature W x μ ν +
          3 * plaquetteLogSize (fun b => minimalLog (ResponseInTheExpansion.gaugeTransform (axialGaugeAt ℓ W o) W b))
            x μ ν ^ 2 +
          3 * plaquetteLogSize (fun c : TorusBond N => minimalLog (W c.1 c.2)) x μ ν ^ 2 := hcl
    have e2 : 2 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (axialGaugeAt ℓ W o x) * curvature W x μ ν =
        2 * (_root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne (axialGaugeAt ℓ W o x) * curvature W x μ ν) := by ring
    rw [e2] at c2
    linarith
  · simp only [plaquetteBonds, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact m₁.trans hG62
    · exact m₂.trans hG62
    · exact m₃.trans hG62
    · exact m₄.trans hG62
end YangMills.Construction.MomentLaw
end
