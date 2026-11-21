import YangMills.Construction.PeriodicOperators.ImaginaryShiftOfASymbol
import YangMills.Construction.PeriodicOperators.SeriesOfTheSymbol
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.SymbolImShift
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
variable {I I' : PeriodicData}
theorem norm_exp_bilinDot_le (θ y : AmbientSpace) :
    ‖Complex.exp (bilinDot (toComplexVec θ) (toComplexVec y))‖ ≤
      Real.exp (euclidNormVec θ * euclidNormVec y) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre : (bilinDot (toComplexVec θ) (toComplexVec y)).re = ∑ i, θ i * y i := by
    simp [bilinDot, toComplexVec]
  rw [hre]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ θ y
  simpa [euclidNormVec] using hcs
theorem isShiftInvariant_expConj (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {K : I'.Carrier → I.Carrier → ℂ} (hK : IsShiftInvariant I I' K) (θ : AmbientSpace) :
    IsShiftInvariant I I' (expConj I I' θ K) := by
  intro n a' a
  have hy : I'.pos (I'.translate n a') - I.pos (I.translate n a) =
      I'.pos a' - I.pos a := by
    rw [hI'.pos_translate, hI.pos_translate]
    abel
  simp only [expConj]
  rw [hy, hK n a' a]
theorem expDecay_expConj {K : I'.Carrier → I.Carrier → ℂ} {C δ : ℝ}
    (hK : ExpDecay I I' K C δ) (θ : AmbientSpace) :
    ExpDecay I I' (expConj I I' θ K) C (δ - euclidNormVec θ) := by
  intro a' a
  simp only [expConj]
  rw [norm_mul]
  calc ‖Complex.exp (bilinDot (toComplexVec θ) (toComplexVec (I'.pos a' - I.pos a)))‖ *
        ‖K a' a‖
      ≤ Real.exp (euclidNormVec θ * euclidNormVec (I'.pos a' - I.pos a)) *
          (C * Real.exp (-δ * euclidNormVec (I'.pos a' - I.pos a))) :=
        mul_le_mul (norm_exp_bilinDot_le θ _) (hK a' a) (norm_nonneg _) (Real.exp_pos _).le
    _ = C * Real.exp (-(δ - euclidNormVec θ) * euclidNormVec (I'.pos a' - I.pos a)) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
theorem symbolSummand_expConj (K : I'.Carrier → I.Carrier → ℂ) (θ : AmbientSpace)
    (z : Fin 4 → ℂ) (a' : I'.Carrier) (a : I.Carrier) (n : Fin 4 → ℤ) :
    symbolSummand I I' (expConj I I' θ K) z a' a n =
      symbolSummand I I' K (addIVec z θ) a' a n := by
  simp only [symbolSummand, expConj]
  generalize I'.pos a' = u
  generalize I.pos (I.translate n a) = v
  have h : bilinDot (toComplexVec θ) (toComplexVec (u - v)) +
      Complex.I * bilinDot z (toComplexVec (v - u)) =
      Complex.I * bilinDot (addIVec z θ) (toComplexVec (v - u)) := by
    simp only [bilinDot, toComplexVec, addIVec, Pi.sub_apply, Complex.ofReal_sub]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (-(θ i : ℂ) * ((v i : ℂ) - u i)) * Complex.I_sq
  rw [← h, Complex.exp_add]
  ring
theorem claim_holds (hS : SymbolSeriesClaim) : Claim := by
  intro I I' hI hI' K δ hK hrate θ hθ z hz
  obtain ⟨hcov, -⟩ := hK
  obtain ⟨-, C, hC, hb⟩ := hrate
  have hb' := expDecay_expConj hb θ
  have hpos : 0 < δ - euclidNormVec θ := sub_pos.mpr hθ
  have hrate' : IsDecayRate I I' (expConj I I' θ K) (δ - euclidNormVec θ) :=
    ⟨hpos, C, hC, hb'⟩
  refine ⟨⟨isShiftInvariant_expConj hI hI' hcov θ, C, δ - euclidNormVec θ, hC, hpos, hb'⟩,
    (hS I I' hI hI' _ _ hrate').summableOn_strip z hz, ?_⟩
  funext a' a
  simp only [fourierSymbol, symbolSummand_expConj]
end YangMills.Construction.PeriodicOperators.SymbolImShift
end
