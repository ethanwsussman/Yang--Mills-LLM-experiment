import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernelsProof
import YangMills.Construction.LawInAState.FromSixteenCopiesToOneBoxProof
import YangMills.Construction.PeriodicOperators.AssociativityOfProductsOfPeriodicOperators
import YangMills.Construction.PeriodicOperators.CommonConstantAndCommonRate
import YangMills.Construction.PeriodicOperators.ProductOfPeriodicOperators
import YangMills.Construction.PeriodicOperators.SumsOfExponentials
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.CompAssoc
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
variable {I I' I'' I''' : PeriodicData}
theorem euclidNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_nonneg <;> assumption
theorem euclidNormVec_sub_comm (a b : AmbientSpace) :
    euclidNormVec (a - b) = euclidNormVec (b - a) := by apply _root_.YangMills.SharedProofs.p26380 <;> assumption
theorem summable_triple_product (hsum : ExponentialSums.Bounds) (hI : IsPeriodic I)
    (hI'' : IsPeriodic I'') {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    {S' : I''.Carrier → I'''.Carrier → ℂ} {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hT : ExpDecay I I' T C δ) (hS : ExpDecay I'' I S C δ) (hS' : ExpDecay I''' I'' S' C δ)
    (a : I'.Carrier) (d : I'''.Carrier) :
    Summable fun p : I.Carrier × I''.Carrier => T a p.1 * S p.1 p.2 * S' p.2 d := by
  have ha := ((hsum δ hδ).2.2 I hI (I'.pos a)).1
  have hb := ((hsum δ hδ).2.2 I'' hI'' (I'''.pos d)).1
  have hab := (Summable.mul_of_nonneg ha hb (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)).mul_left (C * C * C)
  refine Summable.of_norm_bounded hab fun p => ?_
  obtain ⟨b, c⟩ := p
  have h₁ : ‖T a b‖ ≤ C * Real.exp (-δ * euclidNormVec (I.pos b - I'.pos a)) := by
    rw [euclidNormVec_sub_comm (I.pos b) (I'.pos a)]
    exact hT a b
  have h₂ : ‖S b c‖ ≤ C := by
    have hd := euclidNormVec_nonneg (I.pos b - I''.pos c)
    have hexp : Real.exp (-δ * euclidNormVec (I.pos b - I''.pos c)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    calc ‖S b c‖ ≤ C * Real.exp (-δ * euclidNormVec (I.pos b - I''.pos c)) := hS b c
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hexp hC.le
      _ = C := mul_one C
  have h₃ := hS' c d
  rw [norm_mul, norm_mul]
  calc ‖T a b‖ * ‖S b c‖ * ‖S' c d‖
      ≤ (C * Real.exp (-δ * euclidNormVec (I.pos b - I'.pos a))) * C *
          (C * Real.exp (-δ * euclidNormVec (I''.pos c - I'''.pos d))) :=
        mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)) h₃ (norm_nonneg _)
          (by positivity)
    _ = C * C * C * (Real.exp (-δ * euclidNormVec (I.pos b - I'.pos a)) *
          Real.exp (-δ * euclidNormVec (I''.pos c - I'''.pos d))) := by
        ring
theorem compKernel_assoc {T : I'.Carrier → I.Carrier → ℂ} {S : I.Carrier → I''.Carrier → ℂ}
    {S' : I''.Carrier → I'''.Carrier → ℂ}
    (h : ∀ a d, Summable fun p : I.Carrier × I''.Carrier => T a p.1 * S p.1 p.2 * S' p.2 d) :
    compKernel (compKernel T S) S' = compKernel T (compKernel S S') := by
  funext a d
  change ∑' c, (∑' b, T a b * S b c) * S' c d =
    ∑' b, T a b * ∑' c, S b c * S' c d
  calc ∑' c, (∑' b, T a b * S b c) * S' c d
      = ∑' c, ∑' b, T a b * S b c * S' c d :=
        tsum_congr fun _ => tsum_mul_right.symm
    _ = ∑' b, ∑' c, T a b * S b c * S' c d :=
        Summable.tsum_comm (f := fun b c => T a b * S b c * S' c d) (h a d)
    _ = ∑' b, T a b * ∑' c, S b c * S' c d := tsum_congr fun b => by
        rw [← tsum_mul_left]
        exact tsum_congr fun _ => mul_assoc _ _ _
theorem claim_holds (hcommon : UniformDecay.Claim)
    (hprod : CompClaim) (hsum : ExponentialSums.Bounds) :
    Claim := by
  intro I I' I'' I''' hI hI' hI'' hI''' T S S' hT hS hS'
  obtain ⟨C₁, δ₁, hC₁, hδ₁, hb₁⟩ := hT.2
  obtain ⟨C₂, δ₂, hC₂, hδ₂, hb₂⟩ := hS.2
  obtain ⟨C₃, δ₃, hC₃, hδ₃, hb₃⟩ := hS'.2
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max C₁ (max C₂ C₃) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min δ₁ (min δ₂ δ₃) := ⟨_, rfl⟩
  have h₁C : C₁ ≤ C := hC ▸ le_max_left _ _
  have h₂C : C₂ ≤ C := hC ▸ (le_max_left _ _).trans (le_max_right _ _)
  have h₃C : C₃ ≤ C := hC ▸ (le_max_right _ _).trans (le_max_right _ _)
  have h₁δ : δ ≤ δ₁ := hδ ▸ min_le_left _ _
  have h₂δ : δ ≤ δ₂ := hδ ▸ (min_le_right _ _).trans (min_le_left _ _)
  have h₃δ : δ ≤ δ₃ := hδ ▸ (min_le_right _ _).trans (min_le_right _ _)
  have hCpos : 0 < C := hC₁.trans_le h₁C
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have hhalf : 0 < δ / 2 := half_pos hδpos
  have hhalfle : δ / 2 ≤ δ := half_le_self hδpos.le
  have bT : ExpDecay I I' T C δ :=
    hcommon.1 I I' hI hI' T C₁ δ₁ C δ hT hC₁ hδ₁ hb₁ h₁C hδpos h₁δ
  have bS : ExpDecay I'' I S C δ :=
    hcommon.1 I'' I hI'' hI S C₂ δ₂ C δ hS hC₂ hδ₂ hb₂ h₂C hδpos h₂δ
  have bS' : ExpDecay I''' I'' S' C δ :=
    hcommon.1 I''' I'' hI''' hI'' S' C₃ δ₃ C δ hS' hC₃ hδ₃ hb₃ h₃C hδpos h₃δ
  have rT : IsDecayRate I I' T δ := ⟨hδpos, C, hCpos, bT⟩
  have rS : IsDecayRate I'' I S δ := ⟨hδpos, C, hCpos, bS⟩
  have rS' : IsDecayRate I''' I'' S' δ := ⟨hδpos, C, hCpos, bS'⟩
  have rT₂ : IsDecayRate I I' T (δ / 2) :=
    ⟨hhalf, C, hCpos, hcommon.1 I I' hI hI' T C δ C (δ / 2) hT hCpos hδpos bT le_rfl hhalf hhalfle⟩
  have rS'₂ : IsDecayRate I''' I'' S' (δ / 2) :=
    ⟨hhalf, C, hCpos,
      hcommon.1 I''' I'' hI''' hI'' S' C δ C (δ / 2) hS' hCpos hδpos bS' le_rfl hhalf hhalfle⟩
  have hTS := hprod I I' I'' hI hI' hI'' T S δ hT rT hS rS
  have hSS := hprod I'' I I''' hI'' hI hI''' S S' δ hS rS hS' rS'
  have rTS := hTS.comp_decay (δ / 2) hhalf (by linarith)
  have rSS := hSS.comp_decay (δ / 2) hhalf (by linarith)
  have hL := hprod I'' I' I''' hI'' hI' hI''' (compKernel T S) S' (δ / 2)
    hTS.comp_periodic.2 rTS hS' rS'₂
  have hR := hprod I I' I''' hI hI' hI''' T (compKernel S S') (δ / 2)
    hT rT₂ hSS.comp_periodic.2 rSS
  exact ⟨hTS.comp_periodic.1, hTS.comp_periodic.2, hSS.comp_periodic.1,
    hSS.comp_periodic.2, hL.comp_periodic.1, hL.comp_periodic.2,
    hR.comp_periodic.1, hR.comp_periodic.2,
    compKernel_assoc (summable_triple_product hsum hI hI'' hCpos hδpos bT bS bS')⟩
end YangMills.Construction.PeriodicOperators.CompAssoc
end
