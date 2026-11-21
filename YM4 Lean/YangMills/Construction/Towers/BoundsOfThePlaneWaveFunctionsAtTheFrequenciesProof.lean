import YangMills.Construction.Towers.ActionOfTheDifferencesOnPlaneWavesProof
import YangMills.Construction.Towers.OddReciprocalWeightsAndTheirSum
import YangMills.Construction.Towers.ResponseNearZeroPropertyFacts
import Mathlib
import YangMills.Construction.Towers.ElementaryBoundsOfThePlaneWaveFunctions
import YangMills.Construction.Towers.TheMassiveJetsProof
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.Tower.FrequencyBounds
open ResponseProperties (InFundamentalStrip)
open PlaneWaves (edgeWeight forwardSymbol symbolSquare freqBox shiftedFreq)
open FreeStrip (halfSupRate)
structure BoundsAtFrequency (L k : ℕ) (p : Fin 4 → ℂ) (m : Fin 4 → ℤ) : Prop where
  symbolSquare_ge : 2 * (TorusMetric.supNormVec fun ν => (m ν : ℝ)) ^ 2 ≤
    ‖symbolSquare L k (shiftedFreq p m)‖
  vertexWeight_le : ‖PlaneWaves.vertexWeight L k (shiftedFreq p m)‖ ≤
    16 * ∏ ν, oddHarmonicWeight (m ν)
  vertexWeight_neg_le : ‖PlaneWaves.vertexWeight L k (-shiftedFreq p m)‖ ≤
    16 * ∏ ν, oddHarmonicWeight (m ν)
  edgeWeight_le : ∀ μ, ‖edgeWeight L k (shiftedFreq p m) μ‖ ≤
    40 * ∏ ν, oddHarmonicWeight (m ν)
  edgeWeight_neg_le : ∀ μ, ‖edgeWeight L k (-shiftedFreq p m) μ‖ ≤
    40 * ∏ ν, oddHarmonicWeight (m ν)
  forwardSymbol_le : ∀ μ, ‖forwardSymbol L k (shiftedFreq p m) μ‖ ≤
    12 * TorusMetric.supNormVec fun ν => (m ν : ℝ)
def FrequencyBoundsHold : Prop :=
  ∀ δ₀ ∈ halfSupRate, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ p : Fin 4 → ℂ, InFundamentalStrip δ₀ p → ∀ m ∈ freqBox L k, m ≠ 0 →
      BoundsAtFrequency L k p m
end YangMills.Construction.Tower.FrequencyBounds
end

noncomputable section
namespace YangMills.Construction.Tower.FrequencyBounds
open PlaneWaves
open PlaneWaves.PlaneWaveBounds (complexPoint realSymbolSquare SymbolBounds DirichletSumBounds)
open PeriodicOperators (toComplexVec)
open ResponseProperties (InFundamentalStrip)
open FreeStrip (halfSupRate)
theorem finestMesh_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (j : ℕ) :
    0 < finestMesh L j := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.finestMesh_pos <;> assumption
theorem finestMesh_le_one {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (j : ℕ) :
    finestMesh L j ≤ 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.MassJets.finestMesh_le_one <;> assumption
theorem exp_one_eighth_le_two : Real.exp (1 / 8) ≤ 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval (x := 1 / 8) (by norm_num) (by norm_num)
  linarith [show (1 : ℝ) / (1 - 1 / 8) ≤ 2 by norm_num]
theorem exp_one_sixteenth_le_two : Real.exp (1 / 16) ≤ 2 :=
  (Real.exp_le_exp.2 (by norm_num)).trans exp_one_eighth_le_two
theorem norm_exp_halfPhase_le {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) {τ : ℂ} (hτ : |τ.im| ≤ 1 / 8) :
    ‖Complex.exp (Complex.I * (1 - (η : ℂ)) * τ / 2)‖ ≤ Real.exp (1 / 16) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have e : Complex.I * (1 - (η : ℂ)) * τ / 2 = Complex.I * ((((1 - η) / 2 : ℝ) : ℂ) * τ) := by
    push_cast
    ring
  rw [e, Complex.I_mul_re, Complex.im_ofReal_mul]
  have hb := (abs_le.1 hτ).1
  have hc : 0 ≤ (1 - η) / 2 := by linarith
  have h2 : (1 - η) / 2 * (-(1 / 8)) ≤ (1 - η) / 2 * τ.im := mul_le_mul_of_nonneg_left hb hc
  linarith
theorem one_le_abs_intCast {a : ℤ} (ha : a ≠ 0) : (1 : ℝ) ≤ |(a : ℝ)| := by
  have h : (1 : ℤ) ≤ |a| := Int.one_le_abs ha
  rw [← Int.cast_abs]
  exact_mod_cast h
theorem oddHarmonicWeight_nonneg (a : ℤ) : 0 ≤ oddHarmonicWeight a := by
  have h : (0 : ℝ) ≤ max 1 (2 * |(a : ℝ)| - 1) := (zero_le_one).trans (le_max_left _ _)
  exact inv_nonneg.2 h
theorem oddHarmonicWeight_neg (a : ℤ) : oddHarmonicWeight (-a) = oddHarmonicWeight a := by
  simp [oddHarmonicWeight]
def realPart (p : Fin 4 → ℂ) (m : Fin 4 → ℤ) : Fin 4 → ℝ :=
  fun ν => (p ν).re + 2 * Real.pi * (m ν : ℝ)
def imagPart (p : Fin 4 → ℂ) : Fin 4 → ℝ := fun ν => (p ν).im
theorem complexPoint_realPart (p : Fin 4 → ℂ) (m : Fin 4 → ℤ) :
    complexPoint (realPart p m) (imagPart p) = shiftedFreq p m := by
  funext ν
  simp only [complexPoint, shiftedFreq, realPart, imagPart]
  push_cast
  linear_combination Complex.re_add_im (p ν)
theorem neg_shiftedFreq (p : Fin 4 → ℂ) (m : Fin 4 → ℤ) :
    -shiftedFreq p m = shiftedFreq (-p) (-m) := by apply _root_.YangMills.Construction.Tower.PlaneWaveCoboundaries.neg_shiftedFreq <;> assumption
theorem shiftedFreq_im (p : Fin 4 → ℂ) (m : Fin 4 → ℤ) (ν : Fin 4) :
    (shiftedFreq p m ν).im = (p ν).im := by
  simp [shiftedFreq]
theorem neg_mem_freqBox {L j : ℕ} {m : Fin 4 → ℤ} (hm : m ∈ freqBox L j) :
    -m ∈ freqBox L j := by apply _root_.YangMills.Construction.Tower.PeriodicMultiplierMatrices.neg_mem_freqBox <;> assumption
theorem abs_realPart_le {L j : ℕ} {p : Fin 4 → ℂ} {m : Fin 4 → ℤ}
    (hre : ∀ ν, |(p ν).re| ≤ Real.pi) (hm : m ∈ freqBox L j) (ν : Fin 4) :
    |realPart p m ν| ≤ Real.pi / finestMesh L j := by
  have hπ := Real.pi_pos
  obtain ⟨a1, a2⟩ := abs_le.1 (hre ν)
  obtain ⟨b1, b2⟩ := abs_le.1 ((mem_freqBox L j m).1 hm ν)
  have c1 := mul_le_mul_of_nonneg_left b1 hπ.le
  have c2 := mul_le_mul_of_nonneg_left b2 hπ.le
  rw [div_eq_mul_inv, abs_le]
  simp only [realPart]
  constructor <;> nlinarith
theorem planeWaveBounds_at (hE : PlaneWaves.PlaneWaveBounds.Claim) {L j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : 1 ≤ j) {p : Fin 4 → ℂ} {m : Fin 4 → ℤ}
    (hre : ∀ ν, |(p ν).re| ≤ Real.pi) (him : ∀ ν, |(p ν).im| ≤ 1 / 8) (hm : m ∈ freqBox L j) :
    SymbolBounds L j (realPart p m) (imagPart p) ∧
      DirichletSumBounds L j (realPart p m) (imagPart p) :=
  (hE.1 L j hL hj _ _ (abs_realPart_le hre hm) him).2
theorem norm_dirichletSum_le_exp (hE : PlaneWaves.PlaneWaveBounds.Claim) {L j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : 1 ≤ j) {p : Fin 4 → ℂ} {m : Fin 4 → ℤ}
    (hre : ∀ ν, |(p ν).re| ≤ Real.pi) (him : ∀ ν, |(p ν).im| ≤ 1 / 8) (hm : m ∈ freqBox L j)
    (ν : Fin 4) : ‖dirichletSum L j (shiftedFreq p m ν)‖ ≤ Real.exp (1 / 16) := by
  have h := (planeWaveBounds_at hE hL hj hre him hm).2 ν
  rw [complexPoint_realPart] at h
  exact h.1
theorem norm_dirichletSum_le_weight (hE : PlaneWaves.PlaneWaveBounds.Claim) {L j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : 1 ≤ j) {p : Fin 4 → ℂ} {m : Fin 4 → ℤ}
    (hre : ∀ ν, |(p ν).re| ≤ Real.pi) (him : ∀ ν, |(p ν).im| ≤ 1 / 8) (hm : m ∈ freqBox L j)
    (ν : Fin 4) : ‖dirichletSum L j (shiftedFreq p m ν)‖ ≤ 2 * oddHarmonicWeight (m ν) := by
  by_cases h0 : m ν = 0
  · have hw : oddHarmonicWeight (m ν) = 1 := by
      simp [oddHarmonicWeight, h0]
    rw [hw]
    linarith [norm_dirichletSum_le_exp hE hL hj hre him hm ν, exp_one_sixteenth_le_two]
  · have h := (planeWaveBounds_at hE hL hj hre him hm).2 ν
    rw [complexPoint_realPart] at h
    obtain ⟨h1, h2⟩ := h.2.2 (p ν) (m ν) rfl (hre ν) h0
    have hone := one_le_abs_intCast h0
    have hw : oddHarmonicWeight (m ν) = (2 * |(m ν : ℝ)| - 1)⁻¹ := by
      rw [oddHarmonicWeight, max_eq_right (by linarith)]
    rw [hw]
    exact h1.trans h2
theorem norm_vertexWeight_le (hE : PlaneWaves.PlaneWaveBounds.Claim) {L j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : 1 ≤ j) {p : Fin 4 → ℂ} {m : Fin 4 → ℤ}
    (hre : ∀ ν, |(p ν).re| ≤ Real.pi) (him : ∀ ν, |(p ν).im| ≤ 1 / 8) (hm : m ∈ freqBox L j) :
    ‖PlaneWaves.vertexWeight L j (shiftedFreq p m)‖ ≤ 16 * ∏ ν, oddHarmonicWeight (m ν) := by
  rw [PlaneWaves.vertexWeight, norm_prod]
  calc ∏ ν, ‖dirichletSum L j (shiftedFreq p m ν)‖
      ≤ ∏ ν, (2 * oddHarmonicWeight (m ν)) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun ν _ => norm_dirichletSum_le_weight hE hL hj hre him hm ν)
    _ = 16 * ∏ ν, oddHarmonicWeight (m ν) := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        norm_num
theorem norm_edgeWeight_le (hE : PlaneWaves.PlaneWaveBounds.Claim) {L j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : 1 ≤ j) {p : Fin 4 → ℂ} {m : Fin 4 → ℤ}
    (hre : ∀ ν, |(p ν).re| ≤ Real.pi) (him : ∀ ν, |(p ν).im| ≤ 1 / 8) (hm : m ∈ freqBox L j)
    (μ : Fin 4) :
    ‖edgeWeight L j (shiftedFreq p m) μ‖ ≤ 40 * ∏ ν, oddHarmonicWeight (m ν) := by
  have hw : 0 ≤ ∏ ν, oddHarmonicWeight (m ν) :=
    Finset.prod_nonneg fun ν _ => oddHarmonicWeight_nonneg _
  have hv := norm_vertexWeight_le hE hL hj hre him hm
  have hs := norm_dirichletSum_le_exp hE hL hj hre him hm μ
  have he : ‖Complex.exp (Complex.I * (1 - ((finestMesh L j : ℝ) : ℂ)) *
      shiftedFreq p m μ / 2)‖ ≤ Real.exp (1 / 16) :=
    norm_exp_halfPhase_le (finestMesh_pos hL j) (finestMesh_le_one hL j)
      (by rw [shiftedFreq_im]; exact him μ)
  have hexp : Real.exp (1 / 16) * Real.exp (1 / 16) ≤ 2 := by
    rw [← Real.exp_add]
    have : (1 / 16 + 1 / 16 : ℝ) = 1 / 8 := by norm_num
    rw [this]
    exact exp_one_eighth_le_two
  simp only [edgeWeight, norm_mul]
  calc _ ≤ Real.exp (1 / 16) * Real.exp (1 / 16) * (16 * ∏ ν, oddHarmonicWeight (m ν)) := by
        gcongr
    _ ≤ 2 * (16 * ∏ ν, oddHarmonicWeight (m ν)) := by gcongr
    _ ≤ 40 * ∏ ν, oddHarmonicWeight (m ν) := by linarith
theorem abs_le_supNormVec (m : Fin 4 → ℤ) (ν : Fin 4) :
    |(m ν : ℝ)| ≤ TorusMetric.supNormVec fun ν => (m ν : ℝ) :=
  Finset.le_sup' (fun μ => |(m μ : ℝ)|) (Finset.mem_univ ν)
theorem exists_abs_eq_supNormVec (m : Fin 4 → ℤ) :
    ∃ σ, TorusMetric.supNormVec (fun ν => (m ν : ℝ)) = |(m σ : ℝ)| := by
  obtain ⟨σ, -, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun μ => |(m μ : ℝ)|
  exact ⟨σ, h⟩
theorem one_le_supNormVec {m : Fin 4 → ℤ} (hm : m ≠ 0) :
    1 ≤ TorusMetric.supNormVec fun ν => (m ν : ℝ) := by
  obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hm
  exact (one_le_abs_intCast hτ).trans (abs_le_supNormVec m τ)
theorem symbolSquare_lower (hE : PlaneWaves.PlaneWaveBounds.Claim) {L j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : 1 ≤ j) {p : Fin 4 → ℂ} {m : Fin 4 → ℤ}
    (hre : ∀ ν, |(p ν).re| ≤ Real.pi) (him : ∀ ν, |(p ν).im| ≤ 1 / 8) (hm : m ∈ freqBox L j)
    (h0 : m ≠ 0) :
    2 * (TorusMetric.supNormVec fun ν => (m ν : ℝ)) ^ 2 ≤
      ‖symbolSquare L j (shiftedFreq p m)‖ := by
  have hπ := Real.pi_pos
  obtain ⟨σ, hσ⟩ := exists_abs_eq_supNormVec m
  have hM := one_le_supNormVec h0
  set M := TorusMetric.supNormVec fun ν => (m ν : ℝ) with hMdef
  have hB := (planeWaveBounds_at hE hL hj hre him hm).1
  have hq : Real.pi * (2 * M - 1) ≤ |realPart p m σ| := by
    have h1 := abs_sub_abs_le_abs_sub (2 * Real.pi * (m σ : ℝ)) (-(p σ).re)
    rw [abs_neg, sub_neg_eq_add, add_comm (2 * Real.pi * (m σ : ℝ)), abs_mul, abs_mul,
      abs_of_pos hπ, abs_of_pos (by norm_num : (0 : ℝ) < 2), ← hσ] at h1
    have h2 := hre σ
    have h3 : |realPart p m σ| = |(p σ).re + 2 * Real.pi * (m σ : ℝ)| := rfl
    rw [h3]
    nlinarith
  have hd : 2 * (2 * M - 1) ≤ ‖forwardSymbol L j (toComplexVec (realPart p m)) σ‖ := by
    have h1 := (hB.1 σ).1
    have h2 : 2 / Real.pi * (Real.pi * (2 * M - 1)) ≤ 2 / Real.pi * |realPart p m σ| :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    have h3 : 2 / Real.pi * (Real.pi * (2 * M - 1)) = 2 * (2 * M - 1) := by
      field_simp
    linarith
  have hD : (2 * (2 * M - 1)) ^ 2 ≤ realSymbolSquare L j (realPart p m) := by
    have h1 : ‖forwardSymbol L j (toComplexVec (realPart p m)) σ‖ ^ 2 ≤
        realSymbolSquare L j (realPart p m) :=
      Finset.single_le_sum (f := fun ν => ‖forwardSymbol L j (toComplexVec (realPart p m)) ν‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ σ)
    have h2 : (2 * (2 * M - 1)) ^ 2 ≤ ‖forwardSymbol L j (toComplexVec (realPart p m)) σ‖ ^ 2 :=
      pow_le_pow_left₀ (by linarith) hd 2
    linarith
  have hfour : 4 ≤ realSymbolSquare L j (realPart p m) := by nlinarith
  have hlow := hB.2.2.2.2.2 hfour
  rw [complexPoint_realPart] at hlow
  nlinarith
theorem forwardSymbol_upper (hE : PlaneWaves.PlaneWaveBounds.Claim) {L j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : 1 ≤ j) {p : Fin 4 → ℂ} {m : Fin 4 → ℤ}
    (hre : ∀ ν, |(p ν).re| ≤ Real.pi) (him : ∀ ν, |(p ν).im| ≤ 1 / 8) (hm : m ∈ freqBox L j)
    (h0 : m ≠ 0) (μ : Fin 4) :
    ‖forwardSymbol L j (shiftedFreq p m) μ‖ ≤ 12 * TorusMetric.supNormVec fun ν => (m ν : ℝ) := by
  have hπ := Real.pi_pos
  have hπ' := Real.pi_lt_d2
  have hM := one_le_supNormVec h0
  have hμ := abs_le_supNormVec m μ
  set M := TorusMetric.supNormVec fun ν => (m ν : ℝ) with hMdef
  have hB := (planeWaveBounds_at hE hL hj hre him hm).1
  have h1 := (hB.2.2.2.2.1 μ).1
  rw [complexPoint_realPart] at h1
  have h2 := (hB.1 μ).2
  have h3 : |realPart p m μ| ≤ Real.pi + 2 * Real.pi * M := by
    obtain ⟨a1, a2⟩ := abs_le.1 (hre μ)
    obtain ⟨b1, b2⟩ := abs_le.1 hμ
    have c1 := mul_le_mul_of_nonneg_left b1 hπ.le
    have c2 := mul_le_mul_of_nonneg_left b2 hπ.le
    rw [abs_le]
    simp only [realPart]
    constructor <;> nlinarith
  have h5 : Real.pi * M ≤ 3.15 * M := mul_le_mul_of_nonneg_right hπ'.le (by linarith)
  linarith
theorem boundsAtFrequency_of (hE : PlaneWaves.PlaneWaveBounds.Claim) {L j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : 1 ≤ j) {p : Fin 4 → ℂ} {m : Fin 4 → ℤ}
    (hre : ∀ ν, |(p ν).re| ≤ Real.pi) (him : ∀ ν, |(p ν).im| ≤ 1 / 8) (hm : m ∈ freqBox L j)
    (h0 : m ≠ 0) : BoundsAtFrequency L j p m := by
  have hre' : ∀ ν, |((-p) ν).re| ≤ Real.pi := fun ν => by simpa using hre ν
  have him' : ∀ ν, |((-p) ν).im| ≤ 1 / 8 := fun ν => by simpa using him ν
  have hm' := neg_mem_freqBox hm
  have hprod : ∏ ν, oddHarmonicWeight ((-m) ν) = ∏ ν, oddHarmonicWeight (m ν) :=
    Finset.prod_congr rfl fun ν _ => by rw [Pi.neg_apply, oddHarmonicWeight_neg]
  refine ⟨symbolSquare_lower hE hL hj hre him hm h0, norm_vertexWeight_le hE hL hj hre him hm, ?_,
    norm_edgeWeight_le hE hL hj hre him hm, ?_, forwardSymbol_upper hE hL hj hre him hm h0⟩
  · rw [neg_shiftedFreq, ← hprod]
    exact norm_vertexWeight_le hE hL hj hre' him' hm'
  · intro μ
    rw [neg_shiftedFreq, ← hprod]
    exact norm_edgeWeight_le hE hL hj hre' him' hm' μ
theorem frequencyBoundsHold_of (hE : PlaneWaves.PlaneWaveBounds.Claim)
    (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) : FrequencyBoundsHold := by
  intro δ₀ hδ L hL j hj p hp m hm h0
  obtain ⟨-, -, δ₁, hδ₁, C, -, hI, -⟩ := hN
  have hδ' : δ₀ ≤ 1 / 64 := by
    rw [Part.mem_unique hδ hδ₁]
    exact hI.2
  have him : ∀ ν, |(p ν).im| ≤ 1 / 8 := fun ν => by
    have h : |(p ν).im| ≤ 2 * δ₀ := hp.1 ν
    linarith
  exact boundsAtFrequency_of hE hL hj hp.2 him hm h0
end YangMills.Construction.Tower.FrequencyBounds
end
