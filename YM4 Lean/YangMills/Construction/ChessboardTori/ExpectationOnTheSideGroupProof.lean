import YangMills.Construction.ChessboardTori.ArithmeticOfMirrorGrids
import YangMills.Construction.ChessboardTori.ExpectationOnTheSideGroup
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori.PeriodExpectation
theorem holds (hProj : ProjOnEdgesAndFaces.Statement)
    (hArith : ReflectionGridArithmetic.Statement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) : Statement := by
  intro D P hP
  subst hP
  have hL1 : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  obtain ⟨-, -, -, hint, hZ, hprob, -, -, -, -⟩ := hW D.L D.m D.K D.β hL1 D.m.pos D.K.pos
  obtain ⟨⟨-, e, eL, eP, -, -, -, ⟨-, hmap⟩, ⟨-, hact⟩, ⟨-, hlift⟩⟩, -⟩ := hArith D
  obtain ⟨-, -, hconf, -, -⟩ := hProj D D.cubicPeriod
  have hfam : AEMeasurable (D.linkFamily eL) D.cubicPeriod.haarMeasure := by
    by_contra h
    have h0 := Measure.map_of_not_aemeasurable h
    rw [hmap] at h0
    have : (PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)) Set.univ = 1 :=
      measure_univ
    rw [h0] at this
    simp at this
  have hcover : ∀ U, D.cubicPeriod.liftGaugeField U = D.liftField (D.linkFamily eL U) := by
    intro U
    exact (dif_pos (hconf U)).trans (Subtype.ext (funext fun b => (hlift U b).symm))
  refine ⟨PeriodicLattice.partitionFunction D.L D.m D.K D.β, hZ, fun H hH => ?_⟩
  have hHm : Measurable H := hH.1
  have hm := InfiniteLattice.measurable_liftField D.L D.m ((D.K : ℕ) : ℤ)
  have hHl : Measurable fun W => H (D.liftField W) := hHm.comp hm
  have hd : AEMeasurable (fun W => ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β W))
      (PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hint.aestronglyMeasurable.aemeasurable
  have h1 : D.liftedExpectation H =
      ∫ W, H (D.liftField W) ∂(PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β) :=
    integral_map hm.aemeasurable hHm.aestronglyMeasurable
  have h2 : ∫ W, H (D.liftField W) ∂(PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β) =
      ((ENNReal.ofReal (PeriodicLattice.partitionFunction D.L D.m D.K D.β))⁻¹).toReal •
        ∫ W, (ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β W)).toReal • H (D.liftField W)
          ∂(PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)) := by
    unfold PeriodicLattice.wilsonGibbsMeasure
    rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul₀ hd
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hG : AEStronglyMeasurable
      (fun W => (ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β W)).toReal •
        H (D.liftField W))
      (D.cubicPeriod.haarMeasure.map (D.linkFamily eL)) := by
    rw [hmap]
    exact (hd.ennreal_toReal.aestronglyMeasurable).smul hHl.aestronglyMeasurable
  have h3 : ∫ W, (ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β W)).toReal •
      H (D.liftField W) ∂(PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)) =
      ∫ U, H (D.cubicPeriod.liftGaugeField U) *
        Complex.exp (-(D.β : ℂ) * (D.cubicPeriod.wilsonAction U : ℂ))
          ∂D.cubicPeriod.haarMeasure := by
    rw [← hmap, integral_map hfam hG]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    have hn : 0 ≤ PeriodicLattice.boltzmannWeight D.β (D.linkFamily eL U) := (Real.exp_pos _).le
    simp only []
    rw [ENNReal.toReal_ofReal hn, hcover U, Complex.real_smul, hact U, mul_comm]
    congr 1
    simp only [PeriodicLattice.boltzmannWeight]
    push_cast
    rfl
  rw [h1, h2, h3, ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le, Complex.real_smul,
    div_eq_mul_inv, mul_comm]
  push_cast
  rfl
end YangMills.Construction.ChessboardTori.PeriodExpectation
end
