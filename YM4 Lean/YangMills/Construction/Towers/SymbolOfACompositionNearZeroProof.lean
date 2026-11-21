import YangMills.Construction.Continuum.ChosenSmoothFunctionsPartitionsOfUnityRotationsAndIntegrabilityProof
import YangMills.Construction.PeriodicOperators.RiemannSumsAndShiftsProof
import YangMills.Construction.Towers.CoefficientOfTheFamilyOfTheTotalNormaliserProof
import YangMills.Construction.Towers.PropertiesOfTheSymbolOfOneStep
import YangMills.Construction.Towers.SymbolOfACompositionNearZero
import YangMills.Construction.Towers.TheRelationsOfTheResponseProof
import Mathlib
set_option autoImplicit false
open Asymptotics Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.CompositeSymbolNearZero
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (toComplexVec imStrip)
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.PeriodicOperators.Tempered
open YangMills.Construction.PeriodicOperators.Tempered.OneStep
open YangMills.Construction.OneLoopLaw.TemperedStiffness (HasTransverseForm transverseTensor)
open YangMills.Construction.Tower.ResponseProperties (euclidNorm)
open YangMills.Construction.Tower.StepEntryBounds (CongruentMod HoldsAt kroneckerEntry)
theorem euclidNormVec_nonneg (x : AmbientSpace) : 0 ≤ euclidNormVec x := Real.sqrt_nonneg _
theorem abs_apply_le_euclidNormVec (x : AmbientSpace) (k : Fin 4) : |x k| ≤ euclidNormVec x := by apply _root_.YangMills.SharedProofs.p10398 <;> assumption
theorem tendsto_euclidNormVec : Tendsto euclidNormVec (𝓝 (0 : AmbientSpace)) (𝓝 0) := by
  have hcont : Continuous euclidNormVec := by
    unfold euclidNormVec
    fun_prop
  have hzero : euclidNormVec (0 : AmbientSpace) = 0 := by simp [euclidNormVec]
  simpa [hzero] using hcont.tendsto (0 : AmbientSpace)
theorem euclidNormVec_smul {c : ℝ} (hc : 0 ≤ c) (x : AmbientSpace) :
    euclidNormVec (c • x) = c * euclidNormVec x := by apply _root_.YangMills.Construction.WightmanReconstruction.SmoothToolkit.euclidNormVec_smul_of_nonneg <;> assumption
theorem euclidNorm_toComplexVec (x : AmbientSpace) :
    euclidNorm (toComplexVec x) = euclidNormVec x := by
  simp [euclidNorm, euclidNormVec, toComplexVec]
theorem euclidNorm_neg_toComplexVec (x : AmbientSpace) :
    euclidNorm (-toComplexVec x) = euclidNormVec x := by
  simp [euclidNorm, euclidNormVec, toComplexVec]
theorem toComplexVec_mem_imStrip {s : ℝ} (hs : 0 ≤ s) (x : AmbientSpace) :
    toComplexVec x ∈ imStrip s := by apply _root_.YangMills.Construction.PeriodicOperators.RiemannSums.toComplexVec_mem_imStrip <;> assumption
theorem neg_toComplexVec_mem_imStrip {s : ℝ} (hs : 0 ≤ s) (x : AmbientSpace) :
    -toComplexVec x ∈ imStrip s := by
  intro k
  simpa [toComplexVec] using hs
theorem tendsto_toComplexVec : Tendsto toComplexVec (𝓝 (0 : AmbientSpace)) (𝓝 0) := by apply _root_.YangMills.Construction.Tower.NormaliserStiffness.tendsto_toComplexVec_zero <;> assumption
theorem euclidNormVec_pow_isBigO_pow {a b : ℕ} (hab : b ≤ a) :
    (fun x : AmbientSpace => euclidNormVec x ^ a) =O[𝓝 0] fun x => euclidNormVec x ^ b := by
  have hsmall : ∀ᶠ x : AmbientSpace in 𝓝 0, euclidNormVec x < 1 :=
    tendsto_euclidNormVec.eventually (gt_mem_nhds one_pos)
  refine IsBigO.of_bound 1 (hsmall.mono fun x hx => ?_)
  have hnn := euclidNormVec_nonneg x
  rw [Real.norm_of_nonneg (pow_nonneg hnn a), Real.norm_of_nonneg (pow_nonneg hnn b), one_mul]
  exact pow_le_pow_of_le_one hnn hx.le hab
theorem transverseTensor_isBigO (b : ℝ) (j k : Fin 4) :
    (fun x : AmbientSpace => (transverseTensor b j k x : ℂ)) =O[𝓝 0]
      fun x => euclidNormVec x ^ 2 := by
  refine IsBigO.of_bound (2 * |b|) (Eventually.of_forall fun x => ?_)
  have hj := abs_apply_le_euclidNormVec x j
  have hk := abs_apply_le_euclidNormVec x k
  have hnn := euclidNormVec_nonneg x
  rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (pow_nonneg hnn 2)]
  unfold transverseTensor
  rw [abs_mul]
  have hprod : |x j * x k| ≤ euclidNormVec x ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul hj hk (abs_nonneg _) hnn
  have hdiag : |euclidNormVec x ^ 2 * (if j = k then (1 : ℝ) else 0)| ≤ euclidNormVec x ^ 2 := by
    split_ifs
    · rw [mul_one, abs_of_nonneg (pow_nonneg hnn 2)]
    · simpa using pow_nonneg hnn 2
  have hdiff : |euclidNormVec x ^ 2 * (if j = k then (1 : ℝ) else 0) - x j * x k| ≤
      2 * euclidNormVec x ^ 2 := by
    obtain ⟨hpa, hpb⟩ := abs_le.mp hprod
    obtain ⟨hda, hdb⟩ := abs_le.mp hdiag
    rw [abs_le]
    constructor <;> linarith
  calc |b| * |euclidNormVec x ^ 2 * (if j = k then (1 : ℝ) else 0) - x j * x k|
      ≤ |b| * (2 * euclidNormVec x ^ 2) := mul_le_mul_of_nonneg_left hdiff (abs_nonneg b)
    _ = 2 * |b| * euclidNormVec x ^ 2 := by ring
theorem isBigO_sq_of_hasTransverseForm {P : SymbolArray} {b : ℝ} (hP : HasTransverseForm P b)
    (r s : Fin 4) :
    (fun y : AmbientSpace => P r s (toComplexVec y)) =O[𝓝 0] fun y => euclidNormVec y ^ 2 := by
  have h := ((hP r s).trans (euclidNormVec_pow_isBigO_pow (by norm_num : 2 ≤ 4))).add
    (transverseTensor_isBigO b r s)
  refine isBigO_norm_left.mp (h.norm_left.congr_left fun y => ?_)
  rw [sub_add_cancel, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
theorem stepEntry_isBigO {δ₀ : ℝ} (hδ : 0 ≤ δ₀) {L i : ℕ} (H : HoldsAt δ₀ L i) :
    (∀ (n : Fin 4 → ℤ) (r j : Fin 4), ¬ CongruentMod L n 0 →
      ((fun x : AmbientSpace => stepEntry L i n (toComplexVec x) r j) =O[𝓝 0]
          fun x => euclidNormVec x ^ 2) ∧
        (fun x : AmbientSpace => stepEntry L i n (-toComplexVec x) r j) =O[𝓝 0]
          fun x => euclidNormVec x ^ 2) ∧
    (∀ (n : Fin 4 → ℤ) (r j : Fin 4), CongruentMod L n 0 →
      ((fun x : AmbientSpace => stepEntry L i n (toComplexVec x) r j - kroneckerEntry r j) =O[𝓝 0]
          euclidNormVec) ∧
        (fun x : AmbientSpace => stepEntry L i n (-toComplexVec x) r j - kroneckerEntry r j) =O[𝓝 0]
          euclidNormVec) := by
  obtain ⟨A, U, hU, hA⟩ := H.near_zero
  have htwo : 0 ≤ 2 * δ₀ := by linarith
  have hin : ∀ᶠ x : AmbientSpace in 𝓝 0, toComplexVec x ∈ U := tendsto_toComplexVec hU
  have hin' : ∀ᶠ x : AmbientSpace in 𝓝 0, -toComplexVec x ∈ U :=
    (by simpa using tendsto_toComplexVec.neg : Tendsto (fun x => -toComplexVec x)
      (𝓝 (0 : AmbientSpace)) (𝓝 0)) hU
  refine ⟨fun n r j hn => ⟨?_, ?_⟩, fun n r j hn => ⟨?_, ?_⟩⟩
  · refine IsBigO.of_bound A (hin.mono fun x hx => ?_)
    have := (hA _ hx (toComplexVec_mem_imStrip htwo x) n r j).1 hn
    rwa [euclidNorm_toComplexVec, ← Real.norm_of_nonneg (pow_nonneg (euclidNormVec_nonneg x) 2)]
      at this
  · refine IsBigO.of_bound A (hin'.mono fun x hx => ?_)
    have := (hA _ hx (neg_toComplexVec_mem_imStrip htwo x) n r j).1 hn
    rwa [euclidNorm_neg_toComplexVec,
      ← Real.norm_of_nonneg (pow_nonneg (euclidNormVec_nonneg x) 2)] at this
  · refine IsBigO.of_bound A (hin.mono fun x hx => ?_)
    have := (hA _ hx (toComplexVec_mem_imStrip htwo x) n r j).2 hn
    rwa [euclidNorm_toComplexVec, ← Real.norm_of_nonneg (euclidNormVec_nonneg x)] at this
  · refine IsBigO.of_bound A (hin'.mono fun x hx => ?_)
    have := (hA _ hx (neg_toComplexVec_mem_imStrip htwo x) n r j).2 hn
    rwa [euclidNorm_neg_toComplexVec, ← Real.norm_of_nonneg (euclidNormVec_nonneg x)] at this
theorem not_congruentMod_of_mem_residueBox {L : ℕ} {n : Fin 4 → ℤ} (hn : n ∈ residueBox L)
    (hne : n ≠ 0) : ¬ CongruentMod L n 0 ∧ ¬ CongruentMod L (-n) 0 := by
  have hrange : ∀ k, 0 ≤ n k ∧ n k < (L : ℤ) := fun k => by
    simpa [residueBox, Fintype.mem_piFinset] using (Fintype.mem_piFinset.mp hn) k
  have hdvd : ∀ k, (L : ℤ) ∣ n k → n k = 0 := fun k hd =>
    Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_of_nonneg (hrange k).1]; exact (hrange k).2)
  constructor
  · intro hc
    exact hne (funext fun k => hdvd k (by simpa using hc k))
  · intro hc
    exact hne (funext fun k => hdvd k (by simpa using hc k))
theorem rescaledFreq_toComplexVec (L : ℕ) (x : AmbientSpace) (n : Fin 4 → ℤ) :
    rescaledFreq L (toComplexVec x) n = toComplexVec (rescaledMomentum L x n) := by
  funext r
  simp [rescaledFreq, rescaledMomentum, toComplexVec,
    YangMills.Construction.Tower.PlaneWaves.shiftedFreq]
theorem rescaledFreq_toComplexVec_zero (L : ℕ) (x : AmbientSpace) :
    rescaledFreq L (toComplexVec x) 0 = toComplexVec ((L : ℝ)⁻¹ • x) := by
  funext r
  simp [rescaledFreq, toComplexVec, YangMills.Construction.Tower.PlaneWaves.shiftedFreq,
    div_eq_inv_mul]
def classContribution (L i : ℕ) (P : SymbolArray) (j k : Fin 4) (n : Fin 4 → ℤ)
    (x : AmbientSpace) : ℂ :=
  ∑ r, ∑ s, stepEntry L i n (toComplexVec x) r j * P r s (rescaledFreq L (toComplexVec x) n) *
    stepEntry L i (-n) (-toComplexVec x) s k
theorem classContribution_isBigO {δ₀ : ℝ} (hδ : 0 ≤ δ₀) {L i : ℕ} (H : HoldsAt δ₀ L i)
    {P : SymbolArray} {C : ℝ} (hC : ∀ (r s : Fin 4) (y : AmbientSpace), ‖P r s (toComplexVec y)‖ ≤ C)
    (j k : Fin 4) {n : Fin 4 → ℤ} (hn : n ∈ residueBox L) (hne : n ≠ 0) :
    classContribution L i P j k n =O[𝓝 0] fun x => euclidNormVec x ^ 3 := by
  obtain ⟨hc, hc'⟩ := not_congruentMod_of_mem_residueBox hn hne
  have hB := (stepEntry_isBigO hδ H).1
  unfold classContribution
  refine IsBigO.fun_sum fun r _ => IsBigO.fun_sum fun s _ => ?_
  have hP : (fun x : AmbientSpace => P r s (rescaledFreq L (toComplexVec x) n)) =O[𝓝 0]
      fun _ => (1 : ℝ) := by
    refine IsBigO.of_bound C (Eventually.of_forall fun x => ?_)
    rw [rescaledFreq_toComplexVec, norm_one, mul_one]
    exact hC _ _ _
  have h := (((hB n r j hc).1).mul hP).mul ((hB (-n) s k hc').2)
  exact (h.congr_right fun x => by ring).trans (euclidNormVec_pow_isBigO_pow (by norm_num : 3 ≤ 4))
theorem classContribution_zero_sub_isBigO {δ₀ : ℝ} (hδ : 0 ≤ δ₀) {L i : ℕ} (H : HoldsAt δ₀ L i)
    {P : SymbolArray} {b : ℝ} (hP : HasTransverseForm P b) (j k : Fin 4) :
    (fun x : AmbientSpace => classContribution L i P j k 0 x -
        P j k (toComplexVec ((L : ℝ)⁻¹ • x))) =O[𝓝 0]
      fun x => euclidNormVec x ^ 3 := by
  have hB := (stepEntry_isBigO hδ H).2
  have hcong : CongruentMod L 0 0 := fun k => by simp
  have hscale : Tendsto (fun x : AmbientSpace => (L : ℝ)⁻¹ • x) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_const_smul ((L : ℝ)⁻¹)).tendsto (0 : AmbientSpace)
  have hsq : ∀ r s, (fun x : AmbientSpace => P r s (toComplexVec ((L : ℝ)⁻¹ • x))) =O[𝓝 0]
      fun x => euclidNormVec x ^ 2 := fun r s => by
    refine ((isBigO_sq_of_hasTransverseForm hP r s).comp_tendsto hscale).trans ?_
    refine IsBigO.of_bound (((L : ℝ)⁻¹) ^ 2) (Eventually.of_forall fun x => ?_)
    have hinv : (0 : ℝ) ≤ (L : ℝ)⁻¹ := by positivity
    have hnn := euclidNormVec_nonneg x
    simp only [Function.comp]
    rw [euclidNormVec_smul hinv, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (pow_nonneg hnn 2), mul_pow]
  have hone : euclidNormVec =O[𝓝 (0 : AmbientSpace)] fun _ => (1 : ℝ) :=
    tendsto_euclidNormVec.isBigO_one ℝ
  have hconst : ∀ r j : Fin 4, (fun _ : AmbientSpace => kroneckerEntry r j) =O[𝓝 0]
      fun _ => (1 : ℝ) :=
    fun r j => isBigO_const_const _ one_ne_zero _
  have hsplit : ∀ x : AmbientSpace, classContribution L i P j k 0 x -
        P j k (toComplexVec ((L : ℝ)⁻¹ • x)) =
      ∑ r, ∑ s, ((stepEntry L i 0 (toComplexVec x) r j - kroneckerEntry r j) *
            P r s (toComplexVec ((L : ℝ)⁻¹ • x)) * stepEntry L i 0 (-toComplexVec x) s k +
          kroneckerEntry r j * P r s (toComplexVec ((L : ℝ)⁻¹ • x)) *
            (stepEntry L i 0 (-toComplexVec x) s k - kroneckerEntry s k)) := by
    intro x
    have hdelta : P j k (toComplexVec ((L : ℝ)⁻¹ • x)) =
        ∑ r, ∑ s, kroneckerEntry r j * P r s (toComplexVec ((L : ℝ)⁻¹ • x)) *
          kroneckerEntry s k := by
      simp [kroneckerEntry]
    rw [hdelta]
    unfold classContribution
    rw [rescaledFreq_toComplexVec_zero, neg_zero, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  refine IsBigO.congr_left ?_ fun x => (hsplit x).symm
  refine IsBigO.fun_sum fun r _ => IsBigO.fun_sum fun s _ => ?_
  have hleft := (hB 0 r j hcong).1
  have hright := (hB 0 s k hcong).2
  have hbdd : (fun x : AmbientSpace => stepEntry L i 0 (-toComplexVec x) s k) =O[𝓝 0]
      fun _ => (1 : ℝ) :=
    ((hright.trans hone).add (hconst s k)).congr_left fun x => sub_add_cancel _ _
  have hfirst := (hleft.mul (hsq r s)).mul hbdd
  have hsecond := ((hconst r j).mul (hsq r s)).mul hright
  exact (hfirst.congr_right fun x => by ring).add (hsecond.congr_right fun x => by ring)
theorem halfSupRate_nonneg {δ₀ : ℝ}
    (hδ : δ₀ ∈ YangMills.Construction.Tower.FreeStrip.halfSupRate) : 0 ≤ δ₀ := by apply _root_.YangMills.Construction.Tower.ResponseRelationsAtAllHeights.nonneg_of_mem_halfSupRate <;> assumption
theorem stepSymbolNearZero (hEntries : YangMills.Construction.Tower.StepEntryBounds.Claim)
    (hResponse : YangMills.Construction.Tower.ResponseOperators.Claim) :
    YangMills.Construction.Tower.StepSymbolNearZero.Claim := by
  intro L hL P b i hbdd hP j k
  obtain ⟨δ₀, hδ, -⟩ := hResponse
  obtain ⟨C, hC⟩ := hbdd
  have hδ₀ := halfSupRate_nonneg hδ
  have H := hEntries δ₀ hδ L hL i
  have hLpos : 0 < L := by have := hL.2; omega
  have hzeroMem : (0 : Fin 4 → ℤ) ∈ residueBox L := by
    refine Fintype.mem_piFinset.mpr fun k => ?_
    simpa using hLpos
  have hrest : (fun x : AmbientSpace =>
      ∑ n ∈ (residueBox L).erase 0, classContribution L i P j k n x) =O[𝓝 0]
      fun x => euclidNormVec x ^ 3 :=
    IsBigO.fun_sum fun n hn => classContribution_isBigO hδ₀ H hC j k
      (Finset.mem_of_mem_erase hn) (Finset.ne_of_mem_erase hn)
  have hzero := classContribution_zero_sub_isBigO hδ₀ H hP j k
  refine (((hzero.const_mul_left ((L : ℂ) ^ 2)).add
    (hrest.const_mul_left ((L : ℂ) ^ 2))).congr_left fun x => ?_)
  have hsum : stepSymbolArray L i P j k (toComplexVec x) =
      (L : ℂ) ^ 2 * ∑ n ∈ residueBox L, classContribution L i P j k n x := rfl
  rw [hsum, ← Finset.add_sum_erase _ _ hzeroMem]
  ring
end YangMills.Construction.CompositeSymbolNearZero
end
