import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.LawByMomentsOfTheFlow.CurlOfTheCutOverAReference
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps ResponseInTheExpansion
namespace CutoffCurlSteps
section Forms
variable {m : ℕ}
private theorem norm_lieFormCurl_le_logSize (A : TorusBond m → BlockAverages.imaginaryQuaternions) (x : TorusSite m) (μ ν : Fin 4) :
    ‖lieFormCurl A (x, μ, ν)‖ ≤ plaquetteLogSize A x μ ν := by
  unfold lieFormCurl plaquetteLogSize
  refine (norm_sub_le _ _).trans ?_
  gcongr
  refine (norm_sub_le _ _).trans ?_
  gcongr
  exact norm_add_le _ _
private theorem le_pathSum_of_mem (f : TorusBond m → ℝ) (hf : ∀ c, 0 ≤ f c) (l : List (TorusBond m)) (c : TorusBond m) (hc : c ∈ l) :
    f c ≤ pathSum f l := by
  induction l with
  | nil => simp at hc
  | cons a r ih =>
    have hs : 0 ≤ pathSum f r := by
      have : ∀ l' : List (TorusBond m), 0 ≤ pathSum f l' := by
        intro l'
        induction l' with
        | nil => simp [pathSum]
        | cons a' r' ih' =>
          have := hf a'
          simp only [pathSum, List.map_cons, List.sum_cons] at ih' ⊢
          linarith
      exact this r
    simp only [pathSum, List.map_cons, List.sum_cons] at hs ih ⊢
    rcases List.mem_cons.1 hc with h | h
    · subst h
      linarith
    · have := ih h
      have := hf a
      linarith
private theorem plaquetteSum_eq_four (e : TorusBond m → ℝ) (x : TorusSite m) (μ ν : Fin 4) [NeZero m] :
    plaquetteSum e x μ ν = e (x, μ) + e (x + TorusFields.unitStep m μ, ν) + e (x + TorusFields.unitStep m ν, μ) + e (x, ν) := by
  simp [plaquetteSum, pathSum, plaquetteBonds]
  ring
end Forms
section Pointwise
variable {N : ℕ} [NeZero N]
private theorem supDist_le_step_add_one (x o : TorusSite N) (μ : Fin 4) :
    TorusFields.supDist x o ≤ TorusFields.supDist (x + TorusFields.unitStep N μ) o + 1 := by apply _root_.YangMills.SharedProofs.p7518 <;> assumption
private theorem step_supDist_le_add_one (x o : TorusSite N) (μ : Fin 4) :
    TorusFields.supDist (x + TorusFields.unitStep N μ) o ≤ TorusFields.supDist x o + 1 := by apply _root_.YangMills.SharedProofs.p13239 <;> assumption
private theorem one_le_pathSum_pow (e : TorusBond N → ℝ) (he : ∀ c, 0 ≤ e c) {ε : ℝ} (hε : 0 < ε) (l : List (TorusBond N))
    (h : ¬ ∀ c ∈ l, e c ≤ ε) : 1 ≤ pathSum (fun c => (e c / ε) ^ 20) l := by
  push_neg at h
  obtain ⟨c, hc, hlt⟩ := h
  have h1 : (1 : ℝ) ≤ e c / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have h2 : (1 : ℝ) ≤ (e c / ε) ^ 20 := one_le_pow₀ h1
  exact h2.trans (le_pathSum_of_mem (fun c => (e c / ε) ^ 20) (fun c => by have := he c; positivity) l c hc)
private theorem axial_logSize_le (hA : axialGaugePathBoundsStatement) (ℓ : StepParameters) (W : TorusField N) (o x : TorusSite N) (μ ν : Fin 4) :
    plaquetteLogSize (axialCoords ℓ W o) x μ ν ≤ 4 * Real.pi := by
  have h := hA.2.2.2
  unfold plaquetteLogSize axialCoords
  have h1 := h (gaugeTransform (axialGaugeAt ℓ W o) W (x, μ))
  have h2 := h (gaugeTransform (axialGaugeAt ℓ W o) W (x + TorusFields.unitStep N μ, ν))
  have h3 := h (gaugeTransform (axialGaugeAt ℓ W o) W (x + TorusFields.unitStep N ν, μ))
  have h4 := h (gaugeTransform (axialGaugeAt ℓ W o) W (x, ν))
  linarith
private theorem norm_axial_curl_sub_le (hC : curlOverReferenceStatement) (hA : axialGaugePathBoundsStatement) (ℓ : StepParameters) (o : TorusSite N) (D : ℕ)
    (W W₀ : TorusField N) (M Nf : TorusBond N → BlockAverages.imaginaryQuaternions) (e : TorusBond N → ℝ) (v ω κ ε : ℝ) (hR : IsNearReference o D W W₀ M Nf e v ω κ)
    (hκ : 1 ≤ κ) (hv : 0 ≤ v) (hv1 : v ≤ 1) (hω : 0 ≤ ω) (hε : 0 < ε) (hN : 2 * D + 2 < N)
    (hsm : 10 ^ 4 * κ ^ 2 * ((D : ℝ) + 3) ^ 2 * (v + ω + 100 * ((D : ℝ) + 3) * ε) ≤ 1)
    (he1 : ∀ c, e c ≤ 1 / 64) (x : TorusSite N) (μ ν : Fin 4) (hμν : μ < ν) (hd : TorusFields.supDist x o + 3 ≤ D) :
    ‖lieFormCurl (axialCoords ℓ W o) (x, μ, ν) - lieFormCurl M (x, μ, ν) - lieFormCurl Nf (x, μ, ν)‖ ≤
      2 * 10 ^ 5 * κ ^ 2 * (((TorusFields.supDist x o : ℝ) + 2) * (v + ω + plaquetteSum e x μ ν) + pathSum e (plaquettePathBonds o x μ ν)) ^ 2 + 4 * ω +
        20 * pathSum (fun c => (e c / ε) ^ 20) (plaquettePathBonds o x μ ν) := by
  have h0 : 0 ≤ pathSum (fun c => (e c / ε) ^ 20) (plaquettePathBonds o x μ ν) := by
    have : ∀ l' : List (TorusBond N), 0 ≤ pathSum (fun c => (e c / ε) ^ 20) l' := by
      intro l'
      induction l' with
      | nil => simp [pathSum]
      | cons a' r' ih' =>
        have h1 := hR.size_nonneg a'
        have h2 : 0 ≤ (e a' / ε) ^ 20 := by positivity
        simp only [pathSum, List.map_cons, List.sum_cons] at ih' ⊢
        linarith
    exact this _
  have hP : 0 ≤ 2 * 10 ^ 5 * κ ^ 2 * (((TorusFields.supDist x o : ℝ) + 2) * (v + ω + plaquetteSum e x μ ν) + pathSum e (plaquettePathBonds o x μ ν)) ^ 2 := by
    positivity
  by_cases hG : ∀ c ∈ plaquettePathBonds o x μ ν, e c ≤ ε
  · have := ((hC ℓ N o D W W₀ M Nf e v ω κ ε hR hκ hv hω hε.le hN hsm).2 x μ ν hμν hd hG).1
    linarith
  · have h1 := one_le_pathSum_pow e hR.size_nonneg hε _ hG
    have c1 := (norm_lieFormCurl_le_logSize (axialCoords ℓ W o) x μ ν).trans (axial_logSize_le hA ℓ W o x μ ν)
    have c2 := hR.curl_le x μ ν hμν
    have c3 : ‖lieFormCurl Nf (x, μ, ν)‖ ≤ 1 := by
      refine (norm_lieFormCurl_le_logSize Nf x μ ν).trans ?_
      unfold plaquetteLogSize
      have a1 := (hR.free_le (x, μ)).trans (he1 _)
      have a2 := (hR.free_le (x + TorusFields.unitStep N μ, ν)).trans (he1 _)
      have a3 := (hR.free_le (x + TorusFields.unitStep N ν, μ)).trans (he1 _)
      have a4 := (hR.free_le (x, ν)).trans (he1 _)
      linarith
    have hpi := Real.pi_lt_d2
    have : ‖lieFormCurl (axialCoords ℓ W o) (x, μ, ν) - lieFormCurl M (x, μ, ν) - lieFormCurl Nf (x, μ, ν)‖ ≤ 20 := by
      refine (norm_sub_le _ _).trans ?_
      have := norm_sub_le (lieFormCurl (axialCoords ℓ W o) (x, μ, ν)) (lieFormCurl M (x, μ, ν))
      linarith
    linarith
private theorem abs_cutoffProfile_sub_le (o z z' : TorusSite N) (m : ℕ) (hm : 2 ≤ m)
    (h1 : TorusFields.supDist z o ≤ TorusFields.supDist z' o + 1) (h2 : TorusFields.supDist z' o ≤ TorusFields.supDist z o + 1) :
    |cutoffProfile o m z - cutoffProfile o m z'| ≤ 1 / ((m : ℝ) - 1) := by
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  unfold cutoffProfile
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le (by positivity) ?_
  have e : (2 * (m : ℝ) - 1 - (TorusFields.supDist z o : ℝ)) / ((m : ℝ) - 1) - (2 * (m : ℝ) - 1 - (TorusFields.supDist z' o : ℝ)) / ((m : ℝ) - 1) =
      ((TorusFields.supDist z' o : ℝ) - (TorusFields.supDist z o : ℝ)) / ((m : ℝ) - 1) := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hm1]
  refine div_le_div_of_nonneg_right ?_ hm1.le
  rw [abs_le]
  have h1' : (TorusFields.supDist z o : ℝ) ≤ (TorusFields.supDist z' o : ℝ) + 1 := by exact_mod_cast h1
  have h2' : (TorusFields.supDist z' o : ℝ) ≤ (TorusFields.supDist z o : ℝ) + 1 := by exact_mod_cast h2
  constructor <;> linarith
private theorem abs_cutoffProfile_le (o z : TorusSite N) (m : ℕ) : |cutoffProfile o m z| ≤ 1 := by
  have h0 : 0 ≤ cutoffProfile o m z := le_max_left _ _
  rw [abs_of_nonneg h0]
  exact max_le zero_le_one (min_le_left _ _)
private theorem lieFormCurl_cutoffCoords (ℓ : StepParameters) (W : TorusField N) (o x : TorusSite N) (m : ℕ) (μ ν : Fin 4) :
    lieFormCurl (cutoffCoords ℓ W o m) (x, μ, ν) = cutoffProfile o m x • lieFormCurl (axialCoords ℓ W o) (x, μ, ν) +
      (cutoffProfile o m (x + TorusFields.unitStep N μ) - cutoffProfile o m x) • axialCoords ℓ W o (x + TorusFields.unitStep N μ, ν) -
      (cutoffProfile o m (x + TorusFields.unitStep N ν) - cutoffProfile o m x) • axialCoords ℓ W o (x + TorusFields.unitStep N ν, μ) := by
  simp only [lieFormCurl, cutoffCoords]
  module
private theorem norm_cutoff_curl_le (hC : curlOverReferenceStatement) (hA : axialGaugePathBoundsStatement) (ℓ : StepParameters) (o : TorusSite N) (D m : ℕ)
    (W W₀ : TorusField N) (M Nf : TorusBond N → BlockAverages.imaginaryQuaternions) (e : TorusBond N → ℝ) (v ω κ ε : ℝ) (hR : IsNearReference o D W W₀ M Nf e v ω κ)
    (hκ : 1 ≤ κ) (hv : 0 ≤ v) (hω : 0 ≤ ω) (hε : 0 < ε) (hN : 2 * D + 2 < N) (hm : 2 ≤ m)
    (hsm : 10 ^ 4 * κ ^ 2 * ((D : ℝ) + 3) ^ 2 * (v + ω + 100 * ((D : ℝ) + 3) * ε) ≤ 1)
    (x : TorusSite N) (μ ν : Fin 4) (hμν : μ < ν) (hd : TorusFields.supDist x o + 3 ≤ D) :
    ‖lieFormCurl (cutoffCoords ℓ W o m) (x, μ, ν)‖ ≤
      2 * 10 ^ 5 * κ ^ 2 * (((TorusFields.supDist x o : ℝ) + 2) * (v + ω + plaquetteSum e x μ ν) + pathSum e (plaquettePathBonds o x μ ν)) ^ 2 + (4 * ω + v / 16) +
        124 / ((m : ℝ) - 1) * (((TorusFields.supDist x o : ℝ) + 2) * (v + ω + plaquetteSum e x μ ν) + pathSum e (plaquettePathBonds o x μ ν)) +
        plaquetteSum e x μ ν + 20 * pathSum (fun c => (e c / ε) ^ 20) (plaquettePathBonds o x μ ν) := by
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = ((TorusFields.supDist x o : ℝ) + 2) * (v + ω + plaquetteSum e x μ ν) + pathSum e (plaquettePathBonds o x μ ν) := ⟨_, rfl⟩
  rw [← hU]
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = plaquetteSum e x μ ν := ⟨_, rfl⟩
  rw [← hh]
  have hh0 : 0 ≤ h := by
    rw [hh, plaquetteSum_eq_four]
    have := hR.size_nonneg (x, μ)
    have := hR.size_nonneg (x + TorusFields.unitStep N μ, ν)
    have := hR.size_nonneg (x + TorusFields.unitStep N ν, μ)
    have := hR.size_nonneg (x, ν)
    linarith
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = pathSum (fun c => (e c / ε) ^ 20) (plaquettePathBonds o x μ ν) := ⟨_, rfl⟩
  rw [← hZ]
  have hZ0 : 0 ≤ Z := by
    rw [hZ]
    have : ∀ l' : List (TorusBond N), 0 ≤ pathSum (fun c => (e c / ε) ^ 20) l' := by
      intro l'
      induction l' with
      | nil => simp [pathSum]
      | cons a' r' ih' =>
        have h1 := hR.size_nonneg a'
        have h2 : 0 ≤ (e a' / ε) ^ 20 := by positivity
        simp only [pathSum, List.map_cons, List.sum_cons] at ih' ⊢
        linarith
    exact this _
  have hHnn : 0 ≤ pathSum e (plaquettePathBonds o x μ ν) := by
    have : ∀ l' : List (TorusBond N), 0 ≤ pathSum e l' := by
      intro l'
      induction l' with
      | nil => simp [pathSum]
      | cons a' r' ih' =>
        have h1 := hR.size_nonneg a'
        simp only [pathSum, List.map_cons, List.sum_cons] at ih' ⊢
        linarith
    exact this _
  have hU0 : 0 ≤ U := by
    rw [hU, ← hh]
    positivity
  have hK0 : 0 ≤ 2 * 10 ^ 5 * κ ^ 2 * U ^ 2 := by positivity
  have hL0 : 0 ≤ 124 / ((m : ℝ) - 1) * U := by positivity
  by_cases hG : ∀ c ∈ plaquettePathBonds o x μ ν, e c ≤ ε
  · obtain ⟨b1, b2⟩ := (hC ℓ N o D W W₀ M Nf e v ω κ ε hR hκ hv hω hε.le hN hsm).2 x μ ν hμν hd hG
    rw [← hU] at b1 b2
    have hNf : ‖lieFormCurl Nf (x, μ, ν)‖ ≤ h := by
      refine (norm_lieFormCurl_le_logSize Nf x μ ν).trans ?_
      unfold plaquetteLogSize
      rw [hh, plaquetteSum_eq_four]
      have a1 := hR.free_le (x, μ)
      have a2 := hR.free_le (x + TorusFields.unitStep N μ, ν)
      have a3 := hR.free_le (x + TorusFields.unitStep N ν, μ)
      have a4 := hR.free_le (x, ν)
      linarith
    have hMc := hR.curl_le x μ ν hμν
    have hcurl : ‖lieFormCurl (axialCoords ℓ W o) (x, μ, ν)‖ ≤ 2 * 10 ^ 5 * κ ^ 2 * U ^ 2 + 4 * ω + v / 16 + h := by
      have e1 : lieFormCurl (axialCoords ℓ W o) (x, μ, ν) =
          (lieFormCurl (axialCoords ℓ W o) (x, μ, ν) - lieFormCurl M (x, μ, ν) - lieFormCurl Nf (x, μ, ν)) +
            lieFormCurl M (x, μ, ν) + lieFormCurl Nf (x, μ, ν) := by
        abel
      rw [e1]
      refine (norm_add_le _ _).trans ?_
      have := norm_add_le (lieFormCurl (axialCoords ℓ W o) (x, μ, ν) - lieFormCurl M (x, μ, ν) - lieFormCurl Nf (x, μ, ν)) (lieFormCurl M (x, μ, ν))
      linarith
    have hA2 := b2 (x + TorusFields.unitStep N μ, ν) (by simp [plaquetteBonds])
    have hA3 := b2 (x + TorusFields.unitStep N ν, μ) (by simp [plaquetteBonds])
    rw [lieFormCurl_cutoffCoords]
    have t1 : ‖cutoffProfile o m x • lieFormCurl (axialCoords ℓ W o) (x, μ, ν)‖ ≤ ‖lieFormCurl (axialCoords ℓ W o) (x, μ, ν)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have := mul_le_mul_of_nonneg_right (abs_cutoffProfile_le o x m) (norm_nonneg (lieFormCurl (axialCoords ℓ W o) (x, μ, ν)))
      linarith
    have l2 := abs_cutoffProfile_sub_le o (x + TorusFields.unitStep N μ) x m hm (step_supDist_le_add_one x o μ) (supDist_le_step_add_one x o μ)
    have l3 := abs_cutoffProfile_sub_le o (x + TorusFields.unitStep N ν) x m hm (step_supDist_le_add_one x o ν) (supDist_le_step_add_one x o ν)
    have hLp : 0 ≤ 1 / ((m : ℝ) - 1) := by positivity
    have t2 : ‖(cutoffProfile o m (x + TorusFields.unitStep N μ) - cutoffProfile o m x) • axialCoords ℓ W o (x + TorusFields.unitStep N μ, ν)‖ ≤ 1 / ((m : ℝ) - 1) * (62 * U) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul l2 hA2 (norm_nonneg _) hLp
    have t3 : ‖(cutoffProfile o m (x + TorusFields.unitStep N ν) - cutoffProfile o m x) • axialCoords ℓ W o (x + TorusFields.unitStep N ν, μ)‖ ≤ 1 / ((m : ℝ) - 1) * (62 * U) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul l3 hA3 (norm_nonneg _) hLp
    have e2 : 124 / ((m : ℝ) - 1) * U = 1 / ((m : ℝ) - 1) * (62 * U) + 1 / ((m : ℝ) - 1) * (62 * U) := by ring
    rw [e2]
    refine (norm_sub_le _ _).trans ?_
    have := norm_add_le (cutoffProfile o m x • lieFormCurl (axialCoords ℓ W o) (x, μ, ν))
      ((cutoffProfile o m (x + TorusFields.unitStep N μ) - cutoffProfile o m x) • axialCoords ℓ W o (x + TorusFields.unitStep N μ, ν))
    linarith
  · have h1 : 1 ≤ Z := by
      rw [hZ]
      exact one_le_pathSum_pow e hR.size_nonneg hε _ hG
    have c1 : ‖lieFormCurl (cutoffCoords ℓ W o m) (x, μ, ν)‖ ≤ 4 * Real.pi := by
      refine (norm_lieFormCurl_le_logSize _ x μ ν).trans (le_trans ?_ (axial_logSize_le hA ℓ W o x μ ν))
      unfold plaquetteLogSize cutoffCoords
      have s : ∀ b : TorusBond N, ‖cutoffProfile o m b.1 • axialCoords ℓ W o b‖ ≤ ‖axialCoords ℓ W o b‖ := fun b => by
        rw [norm_smul, Real.norm_eq_abs]
        have := mul_le_mul_of_nonneg_right (abs_cutoffProfile_le o b.1 m) (norm_nonneg (axialCoords ℓ W o b))
        linarith
      have a1 := s (x, μ)
      have a2 := s (x + TorusFields.unitStep N μ, ν)
      have a3 := s (x + TorusFields.unitStep N ν, μ)
      have a4 := s (x, ν)
      linarith
    have hpi := Real.pi_lt_d2
    linarith
private theorem boxCurvature_le_of_small_sizes (hC : curlOverReferenceStatement) (ℓ : StepParameters) (o : TorusSite N) (D m : ℕ)
    (W W₀ : TorusField N) (M Nf : TorusBond N → BlockAverages.imaginaryQuaternions) (e : TorusBond N → ℝ) (v ω κ ε Xb : ℝ) (hR : IsNearReference o D W W₀ M Nf e v ω κ)
    (hκ : 1 ≤ κ) (hv : 0 ≤ v) (hω : 0 ≤ ω) (hε : 0 ≤ ε) (hN : 2 * D + 2 < N)
    (hsm : 10 ^ 4 * κ ^ 2 * ((D : ℝ) + 3) ^ 2 * (v + ω + 100 * ((D : ℝ) + 3) * ε) ≤ 1) (hD : 2 * m + 1 ≤ D)
    (hXb : v / 2 + 8 * ε + 5 * ω ≤ Xb) (hX0 : 0 ≤ Xb) (hnear : ∀ c : TorusBond N, TorusFields.supDist c.1 o ≤ 2 * m → e c < ε) :
    boxCurvature o (2 * m) W ≤ Xb := by
  refine Real.iSup_le (fun p => ?_) hX0
  obtain ⟨⟨x, μ, ν⟩, hμν, hcor⟩ := p
  have hx : TorusFields.supDist x o ≤ 2 * m := by
    have h1 := hcor x (by simp [TorusFields.plaquetteVertices])
    have h2 := (Finset.mem_filter.1 h1).2
    exact_mod_cast h2
  have hx₁ : TorusFields.supDist (x + TorusFields.unitStep N μ) o ≤ 2 * m := by
    have h1 := hcor (x + TorusFields.unitStep N μ) (by simp [TorusFields.plaquetteVertices])
    have h2 := (Finset.mem_filter.1 h1).2
    exact_mod_cast h2
  have hx₂ : TorusFields.supDist (x + TorusFields.unitStep N ν) o ≤ 2 * m := by
    have h1 := hcor (x + TorusFields.unitStep N ν) (by simp [TorusFields.plaquetteVertices])
    have h2 := (Finset.mem_filter.1 h1).2
    exact_mod_cast h2
  have hbonds : ∀ c ∈ plaquetteBonds x μ ν, e c ≤ ε := by
    intro c hc
    simp only [plaquetteBonds, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact (hnear _ hx).le
    · exact (hnear _ hx₁).le
    · exact (hnear _ hx₂).le
    · exact (hnear _ hx).le
  have h1 := (hC ℓ N o D W W₀ M Nf e v ω κ ε hR hκ hv hω hε hN hsm).1 x μ ν hμν (by omega) hbonds
  refine h1.trans ?_
  have h2 : plaquetteSum e x μ ν ≤ 4 * ε := by
    rw [plaquetteSum_eq_four]
    have a1 := hbonds (x, μ) (by simp [plaquetteBonds])
    have a2 := hbonds (x + TorusFields.unitStep N μ, ν) (by simp [plaquetteBonds])
    have a3 := hbonds (x + TorusFields.unitStep N ν, μ) (by simp [plaquetteBonds])
    have a4 := hbonds (x, ν) (by simp [plaquetteBonds])
    linarith
  linarith
end Pointwise
end CutoffCurlSteps
open CutoffCurlSteps in
theorem cutoffCurlOverReference (hC : curlOverReferenceStatement) (hA : axialGaugePathBoundsStatement) :
    cutoffCurlOverReferenceStatement :=
  ⟨fun ℓ N _ => norm_axial_curl_sub_le hC hA ℓ, fun ℓ N _ => norm_cutoff_curl_le hC hA ℓ, fun ℓ N _ => boxCurvature_le_of_small_sizes hC ℓ⟩
end YangMills.Construction.MomentLaw
end
