import YangMills.Construction.OneLoopLaw.CoefficientFromALimitKernel
import YangMills.Construction.OneLoopLaw.CoefficientOfATemperedFunctional
import YangMills.Construction.OneLoopLaw.CovarianceOfASymbol
import YangMills.Construction.OneLoopLaw.DecayOfTheKernelsOfASymbol
import YangMills.Construction.OneLoopLaw.FirstDerivativeOfAMemberVanishes
import YangMills.Construction.OneLoopLaw.FourierSeriesOfASymbol
import YangMills.Construction.OneLoopLaw.KernelsOfATemperingChoice
import YangMills.Construction.OneLoopLaw.PeriodicityAndGaugeRelationOfASymbol
import YangMills.Construction.OneLoopLaw.SecondPartialsOfAFourierSeries
import YangMills.Construction.OneLoopLaw.TaylorFormOfACovariantSymbol
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.TemperedStiffness
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.Tempered YangMills.Construction.PeriodicOperators.RiemannSums
open YangMills.Construction.InfiniteLattice (AmbientSpace)
theorem hasSum_congr_terms {α : Type*} {f g : α → ℂ} {a : ℂ} (h : ∀ u, f u = g u)
    (hg : HasSum g a) : HasSum f a := by
  rwa [show f = g from funext h]
theorem bilinDot_neg_left (x y : AmbientSpace) :
    bilinDot (toComplexVec (-x)) (toComplexVec y) = -bilinDot (toComplexVec x) (toComplexVec y) := by
  simp [bilinDot, toComplexVec, Finset.sum_neg_distrib]
theorem conj_bilinDot (x y : AmbientSpace) :
    (starRingEnd ℂ) (bilinDot (toComplexVec x) (toComplexVec y)) =
      bilinDot (toComplexVec x) (toComplexVec y) := by
  simp [bilinDot, toComplexVec, map_sum]
theorem conj_eq_neg_of_real_coeffs {g : (Fin 4 → ℂ) → ℂ} {c : (Fin 4 → ℤ) → ℂ}
    (hc : ∀ u, (c u).im = 0)
    (hg : ∀ x : AmbientSpace, HasSum (fun u : Fin 4 → ℤ => c u *
      Complex.exp (-(Complex.I * bilinDot (toComplexVec x) (toComplexVec (castVec u)))))
      (g (toComplexVec x))) (x : AmbientSpace) :
    (starRingEnd ℂ) (g (toComplexVec x)) = g (toComplexVec (-x)) := by
  have hstar : HasSum (fun u : Fin 4 → ℤ => star (c u *
      Complex.exp (-(Complex.I * bilinDot (toComplexVec x) (toComplexVec (castVec u))))))
      (star (g (toComplexVec x))) := (hg x).star
  refine hstar.unique ?_
  refine hasSum_congr_terms (fun u => ?_) (hg (-x))
  rw [bilinDot_neg_left, star_mul', Complex.star_def, ← Complex.exp_conj,
    Complex.conj_eq_iff_im.2 (hc u)]
  congr 2
  simp [conj_bilinDot]
theorem temperedStiffnessClaim_holds (hFirst : MemberFirstDerivativeVanishes)
    (hKer : TemperedKernels.KernelLimitAndReality)
    (hPer : SymbolPeriodicity.PeriodicityAndWardClaim)
    (hCov : SymbolCovariance.SymbolCovarianceClaim)
    (hDec : SymbolKernelDecay.SymbolKernelDecayClaim)
    (hFou : SymbolFourierSeries.FourierExpansionOfSymbol)
    (hSec : FourierSecondDerivatives.TermwiseSecondDerivativeClaim)
    (hTay : CovariantSymbolTaylor.TaylorExpansionClaim)
    (hLim : KernelStiffness.StiffnessFromKernelLimit) : TemperedStiffnessClaim := by
  intro L hL hS F δ π e hF hc
  obtain ⟨hper, hward⟩ := hPer L hS F δ π e hF hc
  obtain ⟨hperm, hrefl⟩ := hCov L hS F δ π e hF hc
  obtain ⟨hker, hreal⟩ := hKer L hS F δ π e hF hc
  have hpos : 0 < δ := hc.delta_pos
  obtain ⟨O, hO, hO'⟩ := hc.analytic
  have hhol : ∀ μ ν, HolomorphicNearStrip δ (π μ ν) := fun μ ν => ⟨O, hO, (hO' μ ν).1⟩
  have hbdd : ∀ μ ν, BoundedOnStrip δ (π μ ν) := fun μ ν => by
    obtain ⟨C, hC⟩ := (hO' μ ν).2
    exact ⟨C, fun κ hκ => hC κ (hO hκ)⟩
  have hdecay := fun μ ν => hDec δ (π μ ν) hpos (hhol μ ν) (hper μ ν) (hbdd μ ν)
  have hfour := fun μ ν => hFou δ (π μ ν) hpos (hhol μ ν) (hper μ ν) (hbdd μ ν)
  have hconj : ∀ (μ ν : Fin 4) (x : AmbientSpace),
      (starRingEnd ℂ) (π μ ν (toComplexVec x)) = π μ ν (toComplexVec (-x)) :=
    fun μ ν x => conj_eq_neg_of_real_coeffs (hreal μ ν) (hfour μ ν) x
  obtain ⟨b, hb, htay⟩ := hTay δ π hpos hhol hward hperm hrefl hconj
  have hs := fun (μ ν ρ τ : Fin 4) =>
    hSec δ _ (symbolKernel (π μ ν)) (π μ ν) hpos (hdecay μ ν) (hfour μ ν) ρ τ
  have hmixed : ∀ μ ν : Fin 4, μ ≠ ν → HasSum (fun u : Fin 4 → ℤ =>
      symbolKernel (π μ ν) u * (u μ : ℂ) * (u ν : ℂ)) (b : ℂ) := by
    intro μ ν hne
    have h := hs μ ν μ ν
    rwa [(htay μ ν hne).1, neg_neg] at h
  let P : Fin 4 → Fin 4 → YangMills.Construction.EffectiveAction.IntPoint → ℝ :=
    fun μ ν u => (symbolKernel (π μ ν) u).re
  have hP : ∀ μ ν u, ((P μ ν u : ℝ) : ℂ) = symbolKernel (π μ ν) u := fun μ ν u =>
    Complex.ext (by simp [P]) (by simp [hreal μ ν u])
  have hlimit : ∀ (x y : YangMills.Construction.EffectiveAction.IntBond) (a a' : Fin 3),
      Filter.Tendsto (fun n => complexHessian F n
          (YangMills.Construction.OneLoopLaw.FunctionalStiffness.liftedPauliForm L n a x)
          (YangMills.Construction.OneLoopLaw.FunctionalStiffness.liftedPauliForm L n a' y))
        Filter.atTop
        (nhds (if a = a' then ((P x.2 y.2 (y.1 - x.1) : ℝ) : ℂ) else 0)) := by
    intro x y a a'
    rw [hP]
    exact hker x y a a'
  have hsum : ∀ μ ν : Fin 4, μ ≠ ν → HasSum (fun u : YangMills.Construction.EffectiveAction.IntPoint =>
      P μ ν u * (u μ : ℝ) * (u ν : ℝ)) b := by
    intro μ ν hne
    refine Complex.hasSum_ofReal.1 ?_
    refine hasSum_congr_terms (fun u => ?_) (hmixed μ ν hne)
    push_cast
    rw [hP]
  obtain ⟨hcoef, hval⟩ := hLim L hL hS F hF P b hlimit hsum
  refine ⟨?_, hker, fun μ ν u => ⟨hreal μ ν u, hdecay μ ν u⟩, b, hb, ?_, ?_⟩
  · obtain ⟨s₀, hs₀, h⟩ := hF
    exact ⟨s₀, hs₀, fun s hs' hle n hn hsn B hB =>
      hFirst L n hS hn (F n) (h s hs' hle n hn hsn) B hB⟩
  · rw [hval]
    exact hcoef
  · intro μ ν hne
    rw [hval]
    refine ⟨hmixed μ ν hne, ?_, rfl, ?_, ?_⟩
    · rw [(htay μ ν hne).1, neg_neg]
    · rw [(htay μ ν hne).2]
      ring
    · have h := (hs ν ν μ μ).mul_left (-(1 / 2 : ℂ))
      rw [(htay μ ν hne).2] at h
      have hval' : -(1 / 2 : ℂ) * -(2 * (b : ℂ)) = (b : ℂ) := by ring
      rw [hval'] at h
      refine hasSum_congr_terms (fun u => ?_) h
      ring
end YangMills.Construction.OneLoopLaw.TemperedStiffness
end
