import YangMills.Construction.LawInAState.FromSixteenCopiesToOneBoxProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.PeriodicOperators.ProductOfPeriodicOperators
import YangMills.Construction.PeriodicOperators.SumsOfExponentials
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.Composition
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
variable {I I' I'' : PeriodicData}
theorem euclidNormVec_add_le (u v : Fin 4 → ℝ) :
    euclidNormVec (u + v) ≤ euclidNormVec u + euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem euclidNormVec_sub_comm (a b : AmbientSpace) :
    euclidNormVec (a - b) = euclidNormVec (b - a) := by apply _root_.YangMills.SharedProofs.p26380 <;> assumption
theorem norm_mul_kernel_le {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    {C₁ C₂ δ δ' : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hT : ExpDecay I I' T C₁ δ)
    (hS : ExpDecay I'' I S C₂ δ) (h₀ : 0 ≤ δ') (h₁ : δ' ≤ δ) (a : I'.Carrier) (b : I.Carrier)
    (c : I''.Carrier) :
    ‖T a b * S b c‖ ≤
      C₁ * C₂ * Real.exp (-δ' * euclidNormVec (I'.pos a - I''.pos c)) *
        Real.exp (-(δ - δ') * euclidNormVec (I.pos b - I'.pos a)) := by
  have hsplit : I'.pos a - I''.pos c = (I'.pos a - I.pos b) + (I.pos b - I''.pos c) := by
    abel
  have htri : euclidNormVec (I'.pos a - I''.pos c) ≤
      euclidNormVec (I'.pos a - I.pos b) + euclidNormVec (I.pos b - I''.pos c) := by
    rw [hsplit]
    exact euclidNormVec_add_le _ _
  rw [euclidNormVec_sub_comm (I.pos b) (I'.pos a)]
  have hnn : 0 ≤ euclidNormVec (I.pos b - I''.pos c) := Real.sqrt_nonneg _
  have hexp : -δ * euclidNormVec (I'.pos a - I.pos b) + -δ * euclidNormVec (I.pos b - I''.pos c) ≤
      -δ' * euclidNormVec (I'.pos a - I''.pos c) +
        -(δ - δ') * euclidNormVec (I'.pos a - I.pos b) := by
    nlinarith [mul_le_mul_of_nonneg_left htri h₀, mul_le_mul_of_nonneg_right h₁ hnn]
  rw [norm_mul]
  calc ‖T a b‖ * ‖S b c‖
      ≤ (C₁ * Real.exp (-δ * euclidNormVec (I'.pos a - I.pos b))) *
          (C₂ * Real.exp (-δ * euclidNormVec (I.pos b - I''.pos c))) :=
        mul_le_mul (hT a b) (hS b c) (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * Real.exp (-δ * euclidNormVec (I'.pos a - I.pos b) +
          -δ * euclidNormVec (I.pos b - I''.pos c)) := by
        rw [Real.exp_add]
        ring
    _ ≤ C₁ * C₂ * Real.exp (-δ' * euclidNormVec (I'.pos a - I''.pos c) +
          -(δ - δ') * euclidNormVec (I'.pos a - I.pos b)) := by
        have hCC : 0 ≤ C₁ * C₂ := by positivity
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hCC
    _ = C₁ * C₂ * Real.exp (-δ' * euclidNormVec (I'.pos a - I''.pos c)) *
          Real.exp (-(δ - δ') * euclidNormVec (I'.pos a - I.pos b)) := by
        rw [Real.exp_add]
        ring
theorem compSummableAt_of_expDecay (hsum : ExponentialSums.Bounds) (hI : IsPeriodic I)
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ} {C₁ C₂ δ δ' : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hT : ExpDecay I I' T C₁ δ) (hS : ExpDecay I'' I S C₂ δ)
    (h₀ : 0 ≤ δ') (h₁ : δ' < δ) (a : I'.Carrier) (c : I''.Carrier) :
    CompSummableAt T S a c :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun b => norm_mul_kernel_le hC₁ hC₂ hT hS h₀ h₁.le a b c)
    (((hsum (δ - δ') (sub_pos.mpr h₁)).2.2 I hI (I'.pos a)).1.mul_left _)
theorem compKernel_isDecayRate (hsum : ExponentialSums.Bounds) (hI : IsPeriodic I)
    {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ} {C₁ C₂ δ δ' : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hT : ExpDecay I I' T C₁ δ) (hS : ExpDecay I'' I S C₂ δ)
    (h₀ : 0 < δ') (h₁ : δ' < δ) : IsDecayRate I'' I' (compKernel T S) δ' := by
  have hc : 0 < δ - δ' := sub_pos.mpr h₁
  have hB : 0 ≤ (Nat.card I.UnitQuot : ℝ) *
      (Real.exp (2 * (δ - δ')) * expHalfSum (δ - δ') ^ 4) := by
    positivity
  obtain ⟨B, hBeq⟩ : ∃ B : ℝ, B = (Nat.card I.UnitQuot : ℝ) *
      (Real.exp (2 * (δ - δ')) * expHalfSum (δ - δ') ^ 4) := ⟨_, rfl⟩
  rw [← hBeq] at hB
  refine ⟨h₀, C₁ * C₂ * (B + 1), by positivity, fun a c => ?_⟩
  obtain ⟨hs, ht⟩ := (hsum (δ - δ') hc).2.2 I hI (I'.pos a)
  rw [← hBeq] at ht
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C₁ * C₂ *
      Real.exp (-δ' * euclidNormVec (I'.pos a - I''.pos c)) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    positivity
  have hle : ∀ b, ‖T a b * S b c‖ ≤
      K * Real.exp (-(δ - δ') * euclidNormVec (I.pos b - I'.pos a)) := fun b => by
    rw [hK]
    exact norm_mul_kernel_le hC₁ hC₂ hT hS h₀.le h₁.le a b c
  have hsm : Summable fun b => ‖T a b * S b c‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle (hs.mul_left K)
  calc ‖compKernel T S a c‖
      ≤ ∑' b, ‖T a b * S b c‖ := norm_tsum_le_tsum_norm hsm
    _ ≤ ∑' b, K * Real.exp (-(δ - δ') * euclidNormVec (I.pos b - I'.pos a)) :=
        hsm.tsum_le_tsum hle (hs.mul_left K)
    _ = K * ∑' b, Real.exp (-(δ - δ') * euclidNormVec (I.pos b - I'.pos a)) :=
        tsum_mul_left
    _ ≤ K * (B + 1) := mul_le_mul_of_nonneg_left (by linarith) hK0
    _ = C₁ * C₂ * (B + 1) * Real.exp (-δ' * euclidNormVec (I'.pos a - I''.pos c)) := by
        rw [hK]
        ring
def translateEquiv (hI : IsPeriodic I) (n : Fin 4 → ℤ) : I.Carrier ≃ I.Carrier where
  toFun := I.translate n
  invFun := I.translate (-n)
  left_inv := fun x => by
    rw [← hI.translate_add, add_neg_cancel, hI.translate_zero]
  right_inv := fun x => by
    rw [← hI.translate_add, neg_add_cancel, hI.translate_zero]
theorem compKernel_isShiftInvariant (hI : IsPeriodic I) {T : I'.Carrier → I.Carrier → ℂ}
    {S : I.Carrier → I''.Carrier → ℂ} (hT : IsShiftInvariant I I' T)
    (hS : IsShiftInvariant I'' I S) : IsShiftInvariant I'' I' (compKernel T S) := by
  intro n a c
  unfold compKernel
  rw [← (translateEquiv hI n).tsum_eq]
  refine tsum_congr fun b => ?_
  change T (I'.translate n a) (I.translate n b) * S (I.translate n b) (I''.translate n c) = _
  rw [hT, hS]
theorem compClaim_holds (hsum : ExponentialSums.Bounds) : CompClaim := by
  intro I I' I'' hI _ _ T S δ hTp hTr hSp hSr
  obtain ⟨hδ, C₁, hC₁, hT⟩ := hTr
  obtain ⟨-, C₂, hC₂, hS⟩ := hSr
  have hrate : ∀ δ', 0 < δ' → δ' < δ → IsDecayRate I'' I' (compKernel T S) δ' :=
    fun δ' h₀ h₁ => compKernel_isDecayRate hsum hI hC₁ hC₂ hT hS h₀ h₁
  obtain ⟨hhalf, C, hC, hb⟩ := hrate (δ / 2) (by linarith) (by linarith)
  exact ⟨⟨fun a c => compSummableAt_of_expDecay hsum hI hC₁ hC₂ hT hS le_rfl hδ a c,
    compKernel_isShiftInvariant hI hTp.1 hSp.1, C, δ / 2, hC, hhalf, hb⟩, hrate⟩
end YangMills.Construction.PeriodicOperators.Composition
end
