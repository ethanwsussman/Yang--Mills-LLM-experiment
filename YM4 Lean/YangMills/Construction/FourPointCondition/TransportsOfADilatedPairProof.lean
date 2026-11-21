import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrabilityProof
import YangMills.Construction.FourPointCondition.TransportsOfADilatedPair
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Torus.GeometryTransportLiftAndDilationOfTestPairs
import YangMills.Construction.Torus.OneBallIntegralsAndLiftOfATestPair
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace YangMills.Construction
open TorusMetric PeriodicLattice TestFunctions ResponseInTheExpansion TorusLumps
namespace FourPointCondition
private theorem euclidNormVec_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (v : Fin 4 → ℝ) :
    euclidNormVec (c • v) = c * euclidNormVec v := by apply _root_.YangMills.Construction.WightmanReconstruction.SmoothToolkit.euclidNormVec_smul_of_nonneg <;> assumption
private theorem euclidDistR4_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x y : Fin 4 → ℝ) :
    euclidDistR4 (c • x) (c • y) = c * euclidDistR4 x y := by
  simp only [euclidDistR4, ← smul_sub, euclidNormVec_smul_of_nonneg hc]
private def contractionHomeomorph (d : ℝ) (hd : 0 < d) : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) :=
  Homeomorph.smulOfNeZero d⁻¹ (inv_ne_zero hd.ne')
private theorem uniformNorm_comp_inv_smul {d : ℝ} (hd : 0 < d) (φ : (Fin 4 → ℝ) → ℝ) :
    uniformNorm (fun x => φ (d⁻¹ • x)) = uniformNorm φ := by
  unfold uniformNorm
  exact (contractionHomeomorph d hd).surjective.iSup_comp (fun y => ‖φ y‖)
private theorem tsupport_comp_inv_smul {d : ℝ} (hd : 0 < d) (φ : (Fin 4 → ℝ) → ℝ) :
    tsupport (fun x => φ (d⁻¹ • x)) = (fun x => d⁻¹ • x) ⁻¹' tsupport φ :=
  tsupport_comp_eq_preimage φ (contractionHomeomorph d hd)
private theorem isLipschitzFor_comp_inv_smul {d : ℝ} (hd : 0 < d) {φ : (Fin 4 → ℝ) → ℝ}
    (h : IsLipschitzFor euclidDistR4 φ) :
    IsLipschitzFor euclidDistR4 (fun x => φ (d⁻¹ • x)) := by
  obtain ⟨C, hC, hφ⟩ := h
  refine ⟨C * d⁻¹, by positivity, fun x y => ?_⟩
  have h' := hφ (d⁻¹ • x) (d⁻¹ • y)
  rw [euclidDistR4_smul_of_nonneg (inv_nonneg.2 hd.le)] at h'
  rw [mul_assoc]
  exact h'
private theorem bestLipschitzConstant_comp_inv_smul_le {d : ℝ} (hd : 0 < d)
    {φ : (Fin 4 → ℝ) → ℝ} (h : IsLipschitzFor euclidDistR4 φ) :
    bestLipschitzConstant euclidDistR4 (fun x => φ (d⁻¹ • x)) ≤
      bestLipschitzConstant euclidDistR4 φ / d := by
  rw [le_div_iff₀ hd]
  obtain ⟨C₀, hC₀, h₀⟩ := h
  refine le_csInf ⟨C₀, hC₀, h₀⟩ ?_
  rintro C ⟨hC, hφ⟩
  rw [← le_div_iff₀ hd]
  refine csInf_le ⟨0, fun _ h => h.1⟩ ⟨by positivity, fun x y => ?_⟩
  have h' := hφ (d⁻¹ • x) (d⁻¹ • y)
  rw [euclidDistR4_smul_of_nonneg (inv_nonneg.2 hd.le)] at h'
  calc _ ≤ C * (d⁻¹ * euclidDistR4 x y) := h'
    _ = C / d * euclidDistR4 x y := by rw [div_eq_mul_inv, mul_assoc]
private theorem ofReal_mul_setDistR4_le_preimage {c : ℝ} (hc : 0 < c) (A B : Set (Fin 4 → ℝ)) :
    ENNReal.ofReal c * setDistR4 A B ≤
      setDistR4 ((fun x => c⁻¹ • x) ⁻¹' A) ((fun x => c⁻¹ • x) ⁻¹' B) := by
  refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
  have h : setDistR4 A B ≤ ENNReal.ofReal (euclidNormVec (c⁻¹ • a - c⁻¹ • b)) :=
    iInf₂_le_of_le (c⁻¹ • a) ha (iInf₂_le_of_le (c⁻¹ • b) hb le_rfl)
  calc ENNReal.ofReal c * setDistR4 A B
      ≤ ENNReal.ofReal c * ENNReal.ofReal (euclidNormVec (c⁻¹ • a - c⁻¹ • b)) := by gcongr
    _ = ENNReal.ofReal (euclidNormVec (a - b)) := by
      rw [← ENNReal.ofReal_mul hc.le, ← smul_sub, euclidNormVec_smul_of_nonneg (inv_nonneg.2 hc.le),
        mul_inv_cancel_left₀ hc.ne']
private theorem setDistR4_preimage_inv_smul_bounds {d : ℝ} (hd : 0 < d) {A B : Set (Fin 4 → ℝ)}
    (h₁ : ENNReal.ofReal 1 ≤ setDistR4 A B)
    (h₂ : setDistR4 A B ≤ ENNReal.ofReal (6 * 1)) :
    ENNReal.ofReal d ≤ setDistR4 ((fun x => d⁻¹ • x) ⁻¹' A) ((fun x => d⁻¹ • x) ⁻¹' B) ∧
      setDistR4 ((fun x => d⁻¹ • x) ⁻¹' A) ((fun x => d⁻¹ • x) ⁻¹' B) ≤
        ENNReal.ofReal (6 * d) := by
  constructor
  · calc ENNReal.ofReal d = ENNReal.ofReal d * ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal d * setDistR4 A B := by gcongr
      _ ≤ _ := ofReal_mul_setDistR4_le_preimage hd A B
  · have h := ofReal_mul_setDistR4_le_preimage (inv_pos.2 hd) ((fun x => d⁻¹ • x) ⁻¹' A)
      ((fun x => d⁻¹ • x) ⁻¹' B)
    have hS : ∀ S : Set (Fin 4 → ℝ),
        (fun x => d⁻¹⁻¹ • x) ⁻¹' ((fun x => d⁻¹ • x) ⁻¹' S) = S := by
      intro S
      ext x
      simp only [mem_preimage, inv_inv, inv_smul_smul₀ hd.ne']
    rw [hS, hS] at h
    calc setDistR4 ((fun x => d⁻¹ • x) ⁻¹' A) ((fun x => d⁻¹ • x) ⁻¹' B)
        = ENNReal.ofReal d * (ENNReal.ofReal d⁻¹ *
            setDistR4 ((fun x => d⁻¹ • x) ⁻¹' A) ((fun x => d⁻¹ • x) ⁻¹' B)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hd.le, mul_inv_cancel₀ hd.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal d * ENNReal.ofReal (6 * 1) := by
          gcongr
          exact h.trans h₂
      _ = ENNReal.ofReal (6 * d) := by
          rw [← ENNReal.ofReal_mul hd.le]
          congr 1
          ring
private theorem isShapedBump_comp_inv_smul {d ϑ : ℝ} (hd : 0 < d) {x : Fin 4 → ℝ}
    {φ : (Fin 4 → ℝ) → ℝ}
    (h : IsShapedBump euclidDistR4 closedBallR4 (fun f => ∫ x, f x) 1 ϑ x φ) :
    IsShapedBump euclidDistR4 closedBallR4 (fun f => ∫ x, f x) d ϑ (d • x)
      (fun y => φ (d⁻¹ • y)) := by
  obtain ⟨hl, hn, ⟨y, hy⟩, hs, hi, hL⟩ := h
  refine ⟨isLipschitzFor_comp_inv_smul hd hl, fun y => hn _, ⟨d • y, ?_⟩, ?_, ?_, ?_⟩
  · simpa only [inv_smul_smul₀ hd.ne'] using hy
  · rw [tsupport_comp_inv_smul hd]
    intro u hu
    have hu' : euclidNormVec (d⁻¹ • u - x) ≤ 1 := hs hu
    have hdec : u - d • x = d • (d⁻¹ • u - x) := by rw [smul_sub, smul_inv_smul₀ hd.ne']
    show euclidNormVec (u - d • x) ≤ d
    rw [hdec, euclidNormVec_smul_of_nonneg hd.le]
    nlinarith
  · rw [uniformNorm_comp_inv_smul hd]
    have hI : ∫ y, φ (d⁻¹ • y) = d ^ 4 * ∫ y, φ y := by
      have h' := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Fin 4 → ℝ)) φ hd.le
      rw [h', Module.finrank_fin_fun, smul_eq_mul]
    show _ ≤ ∫ y, φ (d⁻¹ • y)
    rw [hI]
    have hi' : ϑ * uniformNorm φ * 1 ^ 4 ≤ ∫ y, φ y := hi
    have hd4 : 0 < d ^ 4 := by positivity
    rw [one_pow, mul_one] at hi'
    nlinarith
  · rw [uniformNorm_comp_inv_smul hd]
    refine (bestLipschitzConstant_comp_inv_smul_le hd hl).trans ?_
    have hL' : bestLipschitzConstant euclidDistR4 φ ≤ uniformNorm φ / (ϑ * 1) := hL
    rw [mul_one] at hL'
    calc bestLipschitzConstant euclidDistR4 φ / d ≤ uniformNorm φ / ϑ / d := by gcongr
      _ = uniformNorm φ / (ϑ * d) := by rw [div_div]
private theorem comp_inv_smul_mem_separatedPairsR4 {d ϑ : ℝ} (hd : 0 < d)
    {φ ψ : (Fin 4 → ℝ) → ℝ} (h : (φ, ψ) ∈ separatedPairsR4 1 ϑ) :
    ((fun y => φ (d⁻¹ • y)), (fun y => ψ (d⁻¹ • y))) ∈ separatedPairsR4 d ϑ := by
  obtain ⟨x₁, x₂, b₁, b₂, c₁, c₂⟩ := h
  refine ⟨d • x₁, d • x₂, isShapedBump_comp_inv_smul hd b₁, isShapedBump_comp_inv_smul hd b₂, ?_⟩
  show ENNReal.ofReal d ≤ setDistR4 (tsupport fun y => φ (d⁻¹ • y))
      (tsupport fun y => ψ (d⁻¹ • y)) ∧
    setDistR4 (tsupport fun y => φ (d⁻¹ • y)) (tsupport fun y => ψ (d⁻¹ • y)) ≤
      ENNReal.ofReal (6 * d)
  rw [tsupport_comp_inv_smul hd, tsupport_comp_inv_smul hd]
  exact setDistR4_preimage_inv_smul_bounds hd c₁ c₂
private theorem inverseEighthKernel_comp_inv_smul {d : ℝ} (hd : 0 < d) (φ ψ : (Fin 4 → ℝ) → ℝ) :
    inverseEighthKernel (fun y => φ (d⁻¹ • y)) (fun y => ψ (d⁻¹ • y)) = inverseEighthKernel φ ψ := by
  have hd8 : d ^ 8 ≠ 0 := by positivity
  have : (volume : Measure ((Fin 4 → ℝ) × (Fin 4 → ℝ))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod.instIsAddHaarMeasure _ _
  have key := Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure ((Fin 4 → ℝ) × (Fin 4 → ℝ)))
    (fun z => φ z.1 * ψ z.2 * euclidNormVec (z.1 - z.2) ^ (-8 : ℤ)) hd.le
  have hfin : Module.finrank ℝ ((Fin 4 → ℝ) × (Fin 4 → ℝ)) = 8 := by
    simp [Module.finrank_prod]
  rw [hfin, smul_eq_mul] at key
  have hinv : (d⁻¹) ^ (-8 : ℤ) = d ^ 8 := by
    rw [zpow_neg, inv_zpow, inv_inv]
    exact zpow_ofNat d 8
  have hpt : ∀ z : (Fin 4 → ℝ) × (Fin 4 → ℝ),
      φ (d⁻¹ • z).1 * ψ (d⁻¹ • z).2 * euclidNormVec ((d⁻¹ • z).1 - (d⁻¹ • z).2) ^ (-8 : ℤ) =
        d ^ 8 * (φ (d⁻¹ • z.1) * ψ (d⁻¹ • z.2) * euclidNormVec (z.1 - z.2) ^ (-8 : ℤ)) := by
    intro z
    simp only [Prod.smul_fst, Prod.smul_snd, ← smul_sub]
    rw [euclidNormVec_smul_of_nonneg (inv_nonneg.2 hd.le), mul_zpow, hinv]
    ring
  simp only [hpt] at key
  rw [integral_const_mul] at key
  simpa only [inverseEighthKernel, RCLike.ofReal_real_eq_id, id_eq] using mul_left_cancel₀ hd8 key
private theorem torusEuclidNorm_neg {s : ℝ} (x : Torus4 s) :
    torusEuclidNorm (-x) = torusEuclidNorm x := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.torusEuclidNorm_neg <;> assumption
private theorem torusEuclidNorm_add_le {s : ℝ} (u w : Torus4 s) :
    torusEuclidNorm (u + w) ≤ torusEuclidNorm u + torusEuclidNorm w := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_add_le <;> assumption
private theorem euclidDistTorus_comm {s : ℝ} (x y : Torus4 s) :
    euclidDistTorus x y = euclidDistTorus y x := by apply _root_.YangMills.Construction.TestPairs.euclidDistTorus_comm <;> assumption
private theorem euclidDistTorus_le_of_subset_closedBall {s d : ℝ} (hd : 0 < d) {c : Torus4 s}
    {S : Set (Torus4 s)} (hS : S ⊆ closedBallTorus c d) :
    ∀ x ∈ S, ∀ z ∈ S, euclidDistTorus x z ≤ 10 * d := by
  intro x hx z hz
  have h₁ : torusEuclidNorm (x - c) ≤ d := hS hx
  have h₂ : torusEuclidNorm (z - c) ≤ d := hS hz
  have h₃ : torusEuclidNorm ((x - c) + -(z - c)) ≤
      torusEuclidNorm (x - c) + torusEuclidNorm (z - c) := by
    rw [← torusEuclidNorm_neg (z - c)]
    exact torusEuclidNorm_add_le _ _
  have h₄ : (x - c) + -(z - c) = x - z := by abel
  rw [h₄] at h₃
  show torusEuclidNorm (x - z) ≤ 10 * d
  linarith
private theorem isSeparatedTestTuple_of_mem_separatedPairs (hB : SingleBallPairs.MainStatement)
    {ℓ : StepParameters} {m : ℕ} (hm : 0 < m) {d vt : ℝ} (hsep : IsSepShapePair d vt)
    (hside : 40 * d ≤ torusSide ℓ.side m) {F G : FourTorus ℓ.side m → ℝ}
    (hclass : (F, G) ∈ separatedPairsFourTorus ℓ.side m d vt)
    (hsF : uniformNorm F = 1) (hsG : uniformNorm G = 1) :
    IsSeparatedTestTuple ℓ m d vt ![F, G] := by
  have hd : 0 < d := hsep.1
  obtain ⟨⟨l₁, -, -⟩, ⟨l₂, -, -⟩, x₁, x₂, hcent⟩ :=
    (mem_separatedPairs_iff euclidDistTorus closedBallTorus setEuclidDist
      (torusVolumeIntegral (torusSide ℓ.side m)) d vt (F, G)).1 hclass
  have hapart : TestPairs.SupportsSeparated euclidDistTorus d F G :=
    (hB.2 ℓ.side (torusSide ℓ.side m) d vt hsep ⟨⟨m, hm, rfl⟩, hside⟩ x₁ x₂ F G hclass hcent).1.2.2.1
  have hballF : tsupport F ⊆ closedBallTorus x₁ d := hcent.1.1
  have hballG : tsupport G ⊆ closedBallTorus x₂ d := hcent.2.1.1
  have hlipF : bestLipschitzConstant euclidDistTorus F ≤ uniformNorm F / (vt * d) := hcent.1.2.2
  have hlipG : bestLipschitzConstant euclidDistTorus G ≤ uniformNorm G / (vt * d) := hcent.2.1.2.2
  rw [hsF] at hlipF
  rw [hsG] at hlipG
  have hFG : ENNReal.ofReal d ≤ setEuclidDist (tsupport F) (tsupport G) := hcent.2.2.1
  have hGF : ENNReal.ofReal d ≤ setEuclidDist (tsupport G) (tsupport F) := by
    refine le_iInf₂ fun b hb => le_iInf₂ fun a ha => ENNReal.ofReal_le_ofReal ?_
    have h := (hapart a ha b hb).1
    rw [euclidDistTorus_comm] at h
    exact h
  refine ⟨Fin.forall_fin_two.2 ⟨hsF, hsG⟩, Fin.forall_fin_two.2 ⟨l₁, l₂⟩,
    Fin.forall_fin_two.2 ⟨hlipF, hlipG⟩, ⟨hd, ?_⟩, ?_⟩
  · exact Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun h => absurd rfl h, fun _ => hFG⟩,
      Fin.forall_fin_two.2 ⟨fun _ => hGF, fun h => absurd rfl h⟩⟩
  · refine Fin.forall_fin_two.2
      ⟨Fin.forall_fin_two.2 ⟨euclidDistTorus_le_of_subset_closedBall hd hballF, ?_⟩,
      Fin.forall_fin_two.2 ⟨?_, euclidDistTorus_le_of_subset_closedBall hd hballG⟩⟩
    · exact fun x hx z hz => (hapart x hx z hz).2
    · intro x hx z hz
      rw [euclidDistTorus_comm]
      exact (hapart z hz x hx).2
theorem dilatedPairPeriodization (hG : PairTransport.PairTransportStatement)
    (hB : SingleBallPairs.MainStatement) : dilatedPairPeriodizationStatement := by
  intro ℓ vt d φ ψ hf hd hvt hvt1 hmem hφ hψ
  have hL2 : 2 ≤ ℓ.side := le_trans (by norm_num) hf.L_ge
  have hL : (1 : ℝ) < (ℓ.side : ℝ) := by exact_mod_cast hL2
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (40 * d) hL
  refine ⟨n + 1, fun m hm => ?_⟩
  have hmpos : 0 < m := by omega
  have hside : 40 * d ≤ torusSide ℓ.side m := by
    have h₁ : (ℓ.side : ℝ) ^ n ≤ (ℓ.side : ℝ) ^ m := pow_le_pow_right₀ hL.le (by omega)
    have h₀ : 0 ≤ (ℓ.side : ℝ) ^ m := by positivity
    simp only [torusSide]
    linarith
  have hsep : IsSepShapePair d vt := ⟨hd, hvt, hvt1⟩
  have hdil := comp_inv_smul_mem_separatedPairsR4 (d := d) hd hmem
  let s : Conventions.StandingParameters :=
    ⟨ℓ.side, ⟨hf.L_odd, le_trans (by norm_num) hf.L_ge⟩, 1, ⟨m, hmpos⟩⟩
  have T : PairTransport.PeriodizationOfPairR4 ℓ.side m d vt
      (fun x => φ (d⁻¹ • x)) (fun x => ψ (d⁻¹ • x)) :=
    (hG s d vt hsep).2.1 hside _ _ hdil
  obtain ⟨hclass, hs₁, hs₂, -, hker, -⟩ := T
  exact ⟨hclass,
    isSeparatedTestTuple_of_mem_separatedPairs hB hmpos hsep hside hclass
      (hs₁.trans ((uniformNorm_comp_inv_smul hd φ).trans hφ))
      (hs₂.trans ((uniformNorm_comp_inv_smul hd ψ).trans hψ)),
    hker.trans (inverseEighthKernel_comp_inv_smul hd φ ψ)⟩
end FourPointCondition
end YangMills.Construction
end
