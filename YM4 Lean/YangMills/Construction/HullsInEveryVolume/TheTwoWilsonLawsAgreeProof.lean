import YangMills.Construction.HullsInEveryVolume.TheObservableReadsAWindowProof
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullsInEveryVolume
private theorem projectPoint_latticePointOfInt {L m K N : ℕ} [NeZero N]
    (hN : (N : ℝ) * PeriodicLattice.meshSize L (K : ℤ) = PeriodicLattice.torusSide L m) (h : Fin 4 → ℤ) :
    InfiniteLattice.projectPoint L m (K : ℤ) (TorusLimits.latticePointOfInt (PeriodicLattice.meshSize L (K : ℤ)) h) =
      ClusterExpansionOfAStep.periodicLatticeSite (n := N) L m (K : ℤ) (TorusFields.siteOfInt h) := by
  refine Subtype.ext (funext fun ν => ?_)
  have hr : (((ClusterExpansionOfAStep.periodicLatticeSite (n := N) L m (K : ℤ) (TorusFields.siteOfInt h) :
      PeriodicLattice.Site L m (K : ℤ)) : PeriodicLattice.FourTorus L m)) ν =
      ((((((TorusFields.siteOfInt h : TorusFields.TorusSite N) ν).cast : ℤ) : ℝ) *
          PeriodicLattice.meshSize L (K : ℤ) : ℝ) :
        AddCircle (PeriodicLattice.torusSide L m)) := by
    simp only [ClusterExpansionOfAStep.periodicLatticeSite, PeriodicLattice.offsetSite, zero_add]
    rw [show (((∑ μ, (((TorusFields.siteOfInt h : TorusFields.TorusSite N) μ).cast : ℤ) •
          PeriodicLattice.unitStep L m (K : ℤ) μ :
        PeriodicLattice.Site L m (K : ℤ)) : PeriodicLattice.FourTorus L m)) =
        ∑ μ, (((TorusFields.siteOfInt h : TorusFields.TorusSite N) μ).cast : ℤ) •
          ((PeriodicLattice.unitStep L m (K : ℤ) μ : PeriodicLattice.Site L m (K : ℤ)) :
            PeriodicLattice.FourTorus L m) by
      simp]
    rw [Finset.sum_apply, Finset.sum_eq_single ν]
    · simp only [Pi.smul_apply, PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_same]
      rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
    · intro μ _ hμ
      simp [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hμ.symm]
    · simp
  rw [hr]
  have hc : ((((TorusFields.siteOfInt h : TorusFields.TorusSite N) ν).cast : ℤ)) = h ν % (N : ℤ) :=
    ZMod.coe_intCast _
  have hv : (((((TorusFields.siteOfInt h : TorusFields.TorusSite N) ν).cast : ℤ)) : ℝ) =
      (h ν : ℝ) - (N : ℝ) * ((h ν / (N : ℤ) : ℤ) : ℝ) := by
    rw [hc, Int.emod_def]
    push_cast
    ring
  have e : (((((TorusFields.siteOfInt h : TorusFields.TorusSite N) ν).cast : ℤ)) : ℝ) *
        PeriodicLattice.meshSize L (K : ℤ) =
      (h ν : ℝ) * PeriodicLattice.meshSize L (K : ℤ) -
        ((h ν / (N : ℤ) : ℤ) : ℝ) * PeriodicLattice.torusSide L m := by
    rw [hv, ← hN]
    ring
  rw [e, AddCircle.coe_sub]
  have hzero : ((((h ν / (N : ℤ) : ℤ) : ℝ) * PeriodicLattice.torusSide L m : ℝ) :
      AddCircle (PeriodicLattice.torusSide L m)) = 0 :=
    (AddCircle.coe_eq_zero_iff _).mpr ⟨h ν / (N : ℤ), by simp⟩
  rw [hzero, sub_zero]
  rfl
private theorem projectLink_forwardFrom {L m K N : ℕ} [NeZero N]
    (hN : (N : ℝ) * PeriodicLattice.meshSize L (K : ℤ) = PeriodicLattice.torusSide L m) (h : Fin 4 → ℤ)
    (i : Fin 4) :
    InfiniteLattice.projectLink L m (K : ℤ)
        (InfiniteLattice.Link.forwardFrom
          (TorusLimits.latticePointOfInt (PeriodicLattice.meshSize L (K : ℤ)) h) i) =
      PeriodicLattice.Bond.forwardFrom
        (ClusterExpansionOfAStep.periodicLatticeSite (n := N) L m (K : ℤ) (TorusFields.siteOfInt h)) i := by
  refine PeriodicLattice.Bond.ext (projectPoint_latticePointOfInt hN h) ?_
  change InfiniteLattice.projectPoint L m (K : ℤ)
      (TorusLimits.latticePointOfInt (PeriodicLattice.meshSize L (K : ℤ)) h +
        InfiniteLattice.axisStep (PeriodicLattice.meshSize L (K : ℤ)) i) =
      _ + PeriodicLattice.unitStep L m (K : ℤ) i
  have e := InfiniteLattice.projectPoint_sub L m (K : ℤ)
    (TorusLimits.latticePointOfInt (PeriodicLattice.meshSize L (K : ℤ)) h +
      InfiniteLattice.axisStep (PeriodicLattice.meshSize L (K : ℤ)) i)
    (InfiniteLattice.axisStep (PeriodicLattice.meshSize L (K : ℤ)) i)
  rw [add_sub_cancel_right, InfiniteLattice.projectPoint_axisStep, projectPoint_latticePointOfInt hN h] at e
  rw [e]
  abel
private theorem evalOnField_liftField {L m K N R : ℕ} [NeZero N]
    (hN : (N : ℝ) * PeriodicLattice.meshSize L (K : ℤ) = PeriodicLattice.torusSide L m)
    (F : ClusterExpansionOfAStep.TorusFieldsAreGaugeFields L m K N) (G : TorusLimits.WindowValuation R → ℝ)
    (W : TorusFields.TorusField N) :
    TorusLimits.evalOnField G
        (InfiniteLattice.liftField L m (K : ℤ) (ClusterExpansionOfAStep.gaugeFieldOfTorusField L m (K : ℤ) W)) =
      TorusLimits.evalOnTorus G W := by
  have hcompact : ClusterExpansionOfAStep.gaugeFieldOfTorusField L m (K : ℤ) W ∈
      PeriodicLattice.compactGaugeFields L m (K : ℤ) := by
    rw [← F.range_gaugeField]
    exact Set.mem_range_self W
  have key : InfiniteLattice.liftField L m (K : ℤ) (ClusterExpansionOfAStep.gaugeFieldOfTorusField L m (K : ℤ) W) =
      ⟨fun b => ⟨ClusterExpansionOfAStep.gaugeFieldOfTorusField L m (K : ℤ) W (InfiniteLattice.projectLink L m (K : ℤ) b),
          hcompact.1 _ (Set.mem_univ _)⟩, fun b => Subtype.ext (by
        rw [InfiniteLattice.specialUnitary_coe_inv]
        exact hcompact.2 (InfiniteLattice.projectLink L m (K : ℤ) b) (Set.mem_univ _))⟩ :=
    dif_pos hcompact
  unfold TorusLimits.evalOnField TorusLimits.evalOnTorus
  rw [key]
  congr 1
  funext b
  change ClusterExpansionOfAStep.gaugeFieldOfTorusField L m (K : ℤ) W (InfiniteLattice.projectLink L m (K : ℤ) _) = _
  rw [projectLink_forwardFrom hN, F.gaugeField_forwardFrom]
private theorem measurable_evalOnField {R : ℕ} {a : ℝ} {G : TorusLimits.WindowValuation R → ℝ}
    (hG : TorusLimits.IsBoundedWindowObservable G) :
    Measurable (TorusLimits.evalOnField G : InfiniteLattice.GaugeField a → ℝ) := by apply _root_.YangMills.SharedProofs.p62357 <;> assumption
private theorem integral_wilsonLaw_eq_integral_liftedWilsonMeasure {L m K N R : ℕ} [NeZero N]
    (hN : (N : ℝ) * PeriodicLattice.meshSize L (K : ℤ) = PeriodicLattice.torusSide L m)
    (F : ClusterExpansionOfAStep.TorusFieldsAreGaugeFields L m K N) (β : ℝ) {G : TorusLimits.WindowValuation R → ℝ}
    (hG : TorusLimits.IsBoundedWindowObservable G) :
    ∫ W, TorusLimits.evalOnTorus G W ∂(WeightedResponses.wilsonLaw β N) =
      ∫ U, TorusLimits.evalOnField G U ∂(InfiniteLattice.liftedWilsonMeasure L m K β) := by
  have hlift := InfiniteLattice.measurable_liftField L m (K : ℤ)
  have heval : Measurable (TorusLimits.evalOnField G : TorusLimits.FineField L K → ℝ) :=
    measurable_evalOnField hG
  have hcomp : Measurable fun U => TorusLimits.evalOnField G (InfiniteLattice.liftField L m (K : ℤ) U) :=
    heval.comp hlift
  have hw : ∀ W : TorusFields.TorusField N,
      TorusLumps.wilsonWeight β N W = Real.exp (-β * TorusFields.wilsonAction Finset.univ W) := fun W => by
    simp [TorusLumps.wilsonWeight, NeZero.ne N]
  have hwn : ∀ W : TorusFields.TorusField N, 0 ≤ TorusLumps.wilsonWeight β N W := fun W => by
    rw [hw]
    exact (Real.exp_pos _).le
  have hρ : Continuous fun W : TorusFields.TorusField N =>
      Real.exp (-β * TorusFields.wilsonAction Finset.univ W) :=
    Real.continuous_exp.comp (continuous_const.mul (TorusFields.continuous_wilsonAction _))
  have : SecondCountableTopology BlockAverages.UnitQuaternion :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hρm : Measurable fun W : TorusFields.TorusField N => TorusLumps.wilsonWeight β N W := by
    have : (fun W : TorusFields.TorusField N => TorusLumps.wilsonWeight β N W) =
        fun W : TorusFields.TorusField N => Real.exp (-β * TorusFields.wilsonAction Finset.univ W) :=
      funext hw
    rw [this]
    exact hρ.measurable
  set Z : ℝ := ∫ W, TorusLumps.wilsonWeight β N W ∂(TorusFields.fieldHaar N) with hZdef
  have hZ0 : 0 ≤ Z := integral_nonneg hwn
  have hZ' : ∫ W', Real.exp (-β * TorusFields.wilsonAction Finset.univ W') ∂(TorusFields.fieldHaar N) = Z :=
    integral_congr_ae (ae_of_all _ fun W => (hw W).symm)
  have hd : AEMeasurable (fun W : TorusFields.TorusField N => ENNReal.ofReal (TorusLumps.wilsonWeight β N W))
      (TorusFields.fieldHaar N) :=
    (ENNReal.measurable_ofReal.comp hρm).aemeasurable
  have hright : ∫ U, TorusLimits.evalOnField G U ∂(InfiniteLattice.liftedWilsonMeasure L m K β) =
      Z⁻¹ • ∫ W, TorusLumps.wilsonWeight β N W • TorusLimits.evalOnTorus G W ∂(TorusFields.fieldHaar N) := by
    unfold InfiniteLattice.liftedWilsonMeasure
    rw [integral_map hlift.aemeasurable heval.aestronglyMeasurable, F.wilsonGibbsMeasure_eq β,
      integral_smul_measure,
      integral_map F.measurable_gaugeField.aemeasurable hcomp.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀ hd (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
      ENNReal.toReal_inv, ← hZdef, ENNReal.toReal_ofReal hZ0]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun W => ?_)
    simp only []
    rw [ENNReal.toReal_ofReal (hwn W), evalOnField_liftField hN F G W]
  have hleft : ∫ W, TorusLimits.evalOnTorus G W ∂(WeightedResponses.wilsonLaw β N) =
      Z⁻¹ • ∫ W, TorusLumps.wilsonWeight β N W • TorusLimits.evalOnTorus G W ∂(TorusFields.fieldHaar N) := by
    have hmeas : AEMeasurable (fun W : TorusFields.TorusField N => ENNReal.ofReal
        (Real.exp (-β * TorusFields.wilsonAction Finset.univ W) /
          ∫ W', Real.exp (-β * TorusFields.wilsonAction Finset.univ W') ∂(TorusFields.fieldHaar N)))
        (TorusFields.fieldHaar N) :=
      (ENNReal.measurable_ofReal.comp (hρ.measurable.div_const _)).aemeasurable
    unfold WeightedResponses.wilsonLaw
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
      ← integral_smul]
    refine integral_congr_ae (ae_of_all _ fun W => ?_)
    simp only []
    rw [hZ', ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ0), smul_smul, div_eq_inv_mul, hw W]
  rw [hleft, hright]
theorem wilsonLawsAgree_of_torusMeasure (hF : ClusterExpansionOfAStep.WilsonMeasureOnTorusFields) :
    HullsInEveryVolume.wilsonLawsAgreeStatement := by
  intro L K m R _ β G _ hL hm _ hG
  have hNe : WeightedResponses.fineSide L K (2 * L ^ m) = 2 * L ^ (m + K) := by
    rw [WeightedResponses.fineSide_eq, pow_add]
    ring
  have h2 : 2 < WeightedResponses.fineSide L K (2 * L ^ m) := by
    have : 1 < L ^ (m + K) := Nat.one_lt_pow (by omega) hL
    omega
  have hN : ((WeightedResponses.fineSide L K (2 * L ^ m) : ℕ) : ℝ) * PeriodicLattice.meshSize L (K : ℤ) =
      PeriodicLattice.torusSide L m := by
    rw [hNe, PeriodicLattice.meshSize, PeriodicLattice.torusSide, zpow_neg, zpow_natCast]
    push_cast
    rw [pow_add]
    field_simp
  exact integral_wilsonLaw_eq_integral_liftedWilsonMeasure hN (hF L m K _ hNe h2) β hG
end YangMills.Construction.HullsInEveryVolume
end
