import YangMills.Construction.Torus.FormOfACutOffAtTensorsProof
import YangMills.Construction.Torus.WeightedSumOfTheCoefficientsOfATestFunction
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
open YangMills.Construction.Torus.FourierBox
namespace YangMills.Construction.AmbientPoints.CutoffSeries
variable {s : Conventions.StandingParameters} {n : ℕ}
theorem mem_complexComponentSpace_of_single {O : Fin n → Set (Pt s .euclidean)} {i : Fin n}
    {g : Pt s .euclidean → ℂ}
    (hg : ofSinglePoint g ∈ testFns (singletonTuples (O i))) :
    g ∈ complexEntrySpace O i := by apply _root_.YangMills.Construction.AmbientPoints.CutoffSeriesAtTensorsProof.mem_complexComponentSpace_of_testFn <;> assumption
theorem cutoffSeriesBoundedLinear_holds (hCoef : FourierCoeffBounds)
    (hMode : CutoffTimesModeGradNorm)
    (hW : WeightedCoeffSumBound)
    (hS : GradientC1Bounds.Statement) : CutoffSeriesBoundedLinear := by
  intro s n ρ C O B χ hO hC hB hχ
  obtain ⟨hn, hρ, hOi⟩ := hO
  have hP : 0 < 4 * ρ := by positivity
  have hscale : 0 < bumpScale ρ := by
    unfold bumpScale
    have := Real.pi_pos
    positivity
  have hfac : ∀ (k : Fin (4 * n) → ℤ) (i : Fin n),
      0 ≤ 1 + euclidNormInt (blockOf k i) / bumpScale ρ := fun k i => by
    have h0 : 0 ≤ euclidNormInt (blockOf k i) := Real.sqrt_nonneg _
    positivity
  obtain ⟨w, hw⟩ : ∃ w : (Fin (4 * n) → ℤ) → ℝ, w = fun k =>
      ∏ i, (1 + euclidNormInt (blockOf k i) / bumpScale ρ) := ⟨_, rfl⟩
  have hw0 : ∀ k, 0 ≤ w k := fun k => by
    rw [hw]
    exact Finset.prod_nonneg fun i _ => hfac k i
  obtain ⟨M, hMeq⟩ : ∃ M : ℝ≥0∞, M = ∏ i, c1GradNorm fun x => (χ i x : ℂ) := ⟨_, rfl⟩
  have hM : M ≠ ⊤ := by
    rw [hMeq]
    refine ENNReal.prod_ne_top fun i _ => ?_
    have hi := hχ i
    have h1 : IsCnAtPoint 1 fun x => (χ i x : ℂ) := by
      have hs' : IsCnOn Set.univ ⊤
          (ofSinglePoint (fun x => (χ i x : ℂ)) ∘ tupleProj s .euclidean 1) := hi.1
      exact ⟨hs'.1, fun m _ => hs'.2 m le_top⟩
    exact ((hS s .euclidean).2 ⟨1, Set.mem_Ici.2 le_rfl⟩ (χ i) h1 hi.2.1).1.ne
  have hBk : ∀ k, ‖B (cutoffModeTuple (4 * ρ) χ k)‖ ≤ C * M.toReal * w k := by
    intro k
    have hm := fun i => hMode s ρ hρ (O i) (χ i) (blockOf k i) (hOi i).1 (hχ i)
    have hent : IsComplexComponentTuple O (cutoffModeTuple (4 * ρ) χ k) :=
      fun i => mem_complexComponentSpace_of_single (hm i).1
    have h1 := hB _ hent
    have h2 : ∏ i, c1GradNorm (cutoffModeTuple (4 * ρ) χ k i) ≤ M * ENNReal.ofReal (w k) := by
      rw [hw, hMeq]
      simp only
      rw [ENNReal.ofReal_prod_of_nonneg fun i _ => hfac k i, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod' fun i _ => (hm i).2.2
    have h3 : ENNReal.ofReal ‖B (cutoffModeTuple (4 * ρ) χ k)‖ ≤
        ENNReal.ofReal (C * M.toReal * w k) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC ENNReal.toReal_nonneg), ENNReal.ofReal_mul hC,
        ENNReal.ofReal_toReal hM, mul_assoc]
      exact h1.trans (mul_le_mul' le_rfl h2)
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg hC ENNReal.toReal_nonneg) (hw0 k))).1 h3
  have hterm : ∀ (F : Tuple s .euclidean n → ℂ) (k : Fin (4 * n) → ℤ),
      ‖fourierCoeff (4 * ρ) F k * B (cutoffModeTuple (4 * ρ) χ k)‖ ≤
        C * M.toReal * (‖fourierCoeff (4 * ρ) F k‖ * w k) := fun F k => by
    rw [norm_mul]
    calc ‖fourierCoeff (4 * ρ) F k‖ * ‖B (cutoffModeTuple (4 * ρ) χ k)‖
        ≤ ‖fourierCoeff (4 * ρ) F k‖ * (C * M.toReal * w k) :=
          mul_le_mul_of_nonneg_left (hBk k) (norm_nonneg _)
      _ = C * M.toReal * (‖fourierCoeff (4 * ρ) F k‖ * w k) := by ring
  have hWF : ∀ F ∈ testFns (fundamentalBoxPow s n (4 * ρ)),
      Summable (fun k : Fin (4 * n) → ℤ => ‖fourierCoeff (4 * ρ) F k‖ * w k) ∧
      ENNReal.ofReal (∑' k : Fin (4 * n) → ℤ, ‖fourierCoeff (4 * ρ) F k‖ * w k) ≤
        ENNReal.ofReal (bumpNumber n ρ) * cnNorm (5 * n + 1) F := by
    subst hw
    exact fun F hF => hW s n ρ hn hρ F hF
  have hsum : ∀ F ∈ testFns (fundamentalBoxPow s n (4 * ρ)), Summable
      (fun k : Fin (4 * n) → ℤ => fourierCoeff (4 * ρ) F k * B (cutoffModeTuple (4 * ρ) χ k)) :=
    fun F hF => Summable.of_norm_bounded ((hWF F hF).1.mul_left (C * M.toReal)) (hterm F)
  refine ⟨fun F hF => ⟨hsum F hF, ?_⟩, ?_⟩
  · have h1 : ‖cutoffSeries (4 * ρ) B χ F‖ ≤
        C * M.toReal * ∑' k, ‖fourierCoeff (4 * ρ) F k‖ * w k := by
      unfold cutoffSeries
      rw [← tsum_mul_left]
      exact tsum_of_norm_bounded ((hWF F hF).1.mul_left _).hasSum (hterm F)
    have h2 := (hWF F hF).2
    rw [← hMeq]
    calc ENNReal.ofReal ‖cutoffSeries (4 * ρ) B χ F‖
        ≤ ENNReal.ofReal (C * M.toReal * ∑' k, ‖fourierCoeff (4 * ρ) F k‖ * w k) :=
          ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal C * M *
            ENNReal.ofReal (∑' k, ‖fourierCoeff (4 * ρ) F k‖ * w k) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hC ENNReal.toReal_nonneg), ENNReal.ofReal_mul hC,
            ENNReal.ofReal_toReal hM]
      _ ≤ ENNReal.ofReal C * M *
            (ENNReal.ofReal (bumpNumber n ρ) * cnNorm (5 * n + 1) F) :=
          mul_le_mul' le_rfl h2
      _ = ENNReal.ofReal (C * bumpNumber n ρ) * M * cnNorm (5 * n + 1) F := by
          rw [ENNReal.ofReal_mul hC]
          ring
  · have hk := fun k => (hCoef s n (4 * ρ) hn hP).1 k
    constructor
    · intro F G H hH
      change cutoffSeries (4 * ρ) B χ H.1 =
        cutoffSeries (4 * ρ) B χ F.1 + cutoffSeries (4 * ρ) B χ G.1
      unfold cutoffSeries
      rw [← (hsum F.1 F.2).tsum_add (hsum G.1 G.2)]
      refine tsum_congr fun k => ?_
      have e : fourierCoeff (4 * ρ) H.1 k =
          fourierCoeff (4 * ρ) F.1 k + fourierCoeff (4 * ρ) G.1 k := (hk k).1 F G H hH
      rw [e, add_mul]
    · intro c F H hH
      change cutoffSeries (4 * ρ) B χ H.1 = c * cutoffSeries (4 * ρ) B χ F.1
      unfold cutoffSeries
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      have e : fourierCoeff (4 * ρ) H.1 k = c * fourierCoeff (4 * ρ) F.1 k := (hk k).2 c F H hH
      rw [e, mul_assoc]
end YangMills.Construction.AmbientPoints.CutoffSeries
