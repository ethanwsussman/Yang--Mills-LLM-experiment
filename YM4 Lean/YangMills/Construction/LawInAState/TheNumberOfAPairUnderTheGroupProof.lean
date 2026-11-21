import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAndCopies
import YangMills.Construction.InfiniteLattice.SmearedDensityAndActionOfIsometries
import YangMills.Construction.LawInAState.TheLeastTorusLawUnderLatticeIsometries
import YangMills.Construction.LawInAState.TheNumberOfAPairUnderTheGroup
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.StateLaws
open ChessboardTori
open InfiniteLattice (AmbientSpace IsBoundedBorelCompactlySupported smearedEnergy faceEnergy)
private theorem covariance_comp_of_integral_comp_eq {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {T : Ω → Ω} (hT : Measurable T) {X Y : Ω → ℝ} (mX : Measurable X) (mY : Measurable Y) {CX CY : ℝ}
    (bX : ∀ U, |X U| ≤ CX) (bY : ∀ U, |Y U| ≤ CY)
    (hRe : ∀ F : Ω → ℝ, Measurable F → (∃ C : ℝ, ∀ U, |F U| ≤ C) → ∫ U, F (T U) ∂ν = ∫ U, F U ∂ν) :
    cov[fun U => X (T U), fun U => Y (T U); ν] = cov[X, Y; ν] := by
  have memX : MemLp X 2 ν := MemLp.of_bound mX.aestronglyMeasurable CX (Filter.Eventually.of_forall bX)
  have memY : MemLp Y 2 ν := MemLp.of_bound mY.aestronglyMeasurable CY (Filter.Eventually.of_forall bY)
  have memX' : MemLp (fun U => X (T U)) 2 ν :=
    MemLp.of_bound (mX.comp hT).aestronglyMeasurable CX (Filter.Eventually.of_forall fun U => bX _)
  have memY' : MemLp (fun U => Y (T U)) 2 ν :=
    MemLp.of_bound (mY.comp hT).aestronglyMeasurable CY (Filter.Eventually.of_forall fun U => bY _)
  rw [covariance_eq_sub memX' memY', covariance_eq_sub memX memY, hRe _ mX ⟨CX, bX⟩, hRe _ mY ⟨CY, bY⟩]
  have hXY := hRe (fun U => X U * Y U) (mX.mul mY)
    ⟨CX * CY, fun U => by
      rw [abs_mul]
      exact mul_le_mul (bX U) (bY U) (abs_nonneg _) ((abs_nonneg _).trans (bX U))⟩
  simp only [Pi.mul_def]
  rw [hXY]
theorem covarianceReflectionInvariant (hI : unitTorusMeasureSymmetricStatement)
    (hE : ChessboardTori.GridBasicProperties.Statement) (hO : InfiniteLattice.SmearedEnergyAndSymmetryAction.Main) :
    covarianceReflectionInvariantStatement := by
  intro D g r f h hf hh
  obtain ⟨hP, hinv⟩ := hI D
  have hinvs := hinv (g.toLatticeSym r)
  obtain ⟨⟨-, hreal⟩, hact, -, -⟩ := hO D.mesh D.mesh_pos
  obtain ⟨-, hsurjP, hcorners, hbary, hplaq⟩ := (hE D g).2.1 (g.toLatticeSym r)
  have hTm : Measurable (g.toLatticeSym r).pullbackField := ((hact (g.toLatticeSym r)).2.2.1).measurable
  have hinj : Function.Injective (D.imageFace (g.toLatticeSym r)) := by
    intro p q hpq
    have h1 := hcorners p
    rw [hpq, hcorners q] at h1
    have hsite : Function.Injective (g.toLatticeSym r).pointMap := by
      intro a b hab
      exact Subtype.ext (r.1.injective (congrArg Subtype.val hab))
    exact InfiniteLattice.ElementaryPlaquette.cornerSet_injective D.mesh_pos ((Set.image_injective.2 hsite h1).symm)
  have htrans : ∀ (w : AmbientSpace → ℝ) (U : D.GaugeField), smearedEnergy (fun x => w (r.1.symm x)) U =
      smearedEnergy w ((g.toLatticeSym r).pullbackField U) := by
    intro w U
    unfold smearedEnergy
    have e := finsum_comp_equiv (Equiv.ofBijective _ ⟨hinj, hsurjP⟩)
      (f := fun p : D.Plaquette => faceEnergy U p • w (r.1.symm p.center))
    rw [← e]
    refine finsum_congr fun p => ?_
    have e1 : (D.imageFace (g.toLatticeSym r) p).center = r.1 p.center := hbary p
    show faceEnergy U (D.imageFace (g.toLatticeSym r) p) •
        w (r.1.symm (D.imageFace (g.toLatticeSym r) p).center) =
      faceEnergy ((g.toLatticeSym r).pullbackField U) p • w p.center
    rw [e1, Equiv.symm_apply_apply, hplaq p U]
  have hRe : ∀ F : D.GaugeField → ℝ, Measurable F → (∃ C : ℝ, ∀ U, |F U| ≤ C) →
      ∫ U, F ((g.toLatticeSym r).pullbackField U) ∂unitTorusMeasure D.L D.K D.β =
        ∫ U, F U ∂unitTorusMeasure D.L D.K D.β := by
    intro F hF ⟨C, hC⟩
    have h1 := hinvs (fun U => (F U : ℂ)) ⟨Complex.measurable_ofReal.comp hF, C, fun U => by
      simpa [Complex.norm_real] using hC U⟩
    exact Complex.ofReal_injective (integral_complex_ofReal.symm.trans (h1.trans integral_complex_ofReal))
  have hobs : ∀ w : AmbientSpace → ℝ, IsBoundedBorelCompactlySupported w →
      Measurable (smearedObservable D.L D.K w) ∧ ∃ C : ℝ, ∀ U, |smearedObservable D.L D.K w U| ≤ C := by
    intro w hw
    obtain ⟨-, -, ⟨hm, C, hC⟩, -⟩ := hreal w hw
    refine ⟨?_, C, fun U => ?_⟩
    · have h1 := Complex.measurable_re.comp hm
      have e : (Complex.re ∘ fun U : D.GaugeField => ((smearedEnergy w U : ℝ) : ℂ)) = smearedObservable D.L D.K w := by
        funext U
        exact Complex.ofReal_re _
      rw [e] at h1
      exact h1
    · have h1 := hC U
      rw [Complex.norm_real] at h1
      exact h1
  obtain ⟨mX, CX, bX⟩ := hobs f hf
  obtain ⟨mY, CY, bY⟩ := hobs h hh
  have eX : smearedObservable D.L D.K (fun x => f (r.1.symm x)) =
      fun U => smearedObservable D.L D.K f ((g.toLatticeSym r).pullbackField U) := funext (htrans f)
  have eY : smearedObservable D.L D.K (fun x => h (r.1.symm x)) =
      fun U => smearedObservable D.L D.K h ((g.toLatticeSym r).pullbackField U) := funext (htrans h)
  unfold unitTorusCovariance
  rw [eX, eY]
  exact @covariance_comp_of_integral_comp_eq _ _ _ hP _ hTm _ _ mX mY CX CY bX bY hRe
end YangMills.Construction.StateLaws
end
