import YangMills.Construction.ChessboardTori.MirrorGridsWithEvenCellsAsGridData
import YangMills.Construction.ChessboardTori.PeriodicRealizationOnARectangularTorus
import YangMills.Construction.InfiniteLattice.WeakLimitPointsAlongSides
import YangMills.Construction.Lattice.CellGridProperties
import YangMills.Construction.LawInAState.GridDataAtEveryExponent
import YangMills.Construction.LawInAState.MeanOnATorusByThePeriodGroup
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BoxTorus
namespace LawInAState.TorusMeanViaPeriods
open ChessboardTori ReflectedCopies CellGrid
variable {D : ChessboardSetup}
private theorem edgeEquivBond_projEdge {P : PeriodSubgroup D} {e : ℕ} {d : CellGrid D.L ((D.K : ℕ) : ℤ)}
    (hside : d.HasEqualSides e) (hlen : d.sideLengths = P.sideLengths) (hfwd : P.ProjCarriesEdgesAndFaces)
    (l : D.Link) :
    edgeEquivBond hside ((edgeEquivOfSidesEq hlen).symm (P.projEdge l)) =
      InfiniteLattice.projectLink D.L e ((D.K : ℕ) : ℤ) l := by
  have hpt : ∀ x : InfiniteLattice.LatticePoint D.mesh,
      (gridPointEquivSite hside ((gridPointEquivOfSidesEq hlen).symm (P.projPoint x)) : PeriodicLattice.FourTorus D.L e) =
        TorusMetric.torusProj (PeriodicLattice.torusSide D.L e) (x : InfiniteLattice.AmbientSpace) := by
    intro x
    have h₁ : (((gridPointEquivOfSidesEq hlen).symm (P.projPoint x) : d.GridPoint) : d.Space) =
        BoxTorus.projection d.sideLengths x := by
      apply (spaceEquivOfSidesEq hlen).injective
      rw [← coe_gridPointEquivOfSidesEq, Equiv.apply_symm_apply]
      rfl
    rw [coe_gridPointEquivSite, h₁, spaceEquivTorus_projection]
    rfl
  obtain ⟨-, hends, -⟩ := hfwd
  refine PeriodicLattice.Bond.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show (gridPointEquivSite hside ((gridPointEquivOfSidesEq hlen).symm (P.projEdge l).source) : PeriodicLattice.FourTorus D.L e) = _
    rw [(hends l).1, hpt]
    rfl
  · show (gridPointEquivSite hside ((gridPointEquivOfSidesEq hlen).symm (P.projEdge l).target) : PeriodicLattice.FourTorus D.L e) = _
    rw [(hends l).2.1, hpt]
    rfl
theorem holds (hG : EqualSideGrids.AtEveryExponent) (hl : GridLattice.Properties)
    (hM : ChessboardTori.ReflectionGridAsCellGrid.Statement) (hR : ChessboardTori.BoxTorusQuotient.Statement) :
    LawInAState.TorusMeanViaPeriods.Statement := by
  intro D g hq e
  set n := cubicCounts D e with hn
  have hcoarse : g.IsCoarse := by
    show 0 ≤ g.q
    omega
  set P : PeriodSubgroup D := gridPeriods g n with hP
  obtain ⟨⟨d, hd⟩, hall⟩ := hM D g n.coord n.two_le n.even
  obtain ⟨hsides, -, hlen, -, -, hconf, hface⟩ := hall d hd
  have hcell : g.cellSide = 1 := by simp [ReflectionGrid.cellSide, hq]
  have hside : d.HasEqualSides e := fun μ => by
    rw [hsides μ, hcell, mul_one]
    show (((2 * (D.L : ℤ) ^ e : ℤ)) : ℝ) = PeriodicLattice.torusSide D.L e
    push_cast
    rfl
  obtain ⟨hC, hA⟩ := hG D.L e (D.K : ℕ) d hside D.β
  obtain ⟨-, hwil, hnorm, -, hmean⟩ := hA
  have hR₁ := (hR ⟨D, g, hcoarse⟩).1 n.coord n.two_le
  obtain ⟨hfwd, -, -, -, -, hliftP, -⟩ := hR₁
  have hlift : ∀ U : d.GaugeConfig,
      InfiniteLattice.liftField D.L e ((D.K : ℕ) : ℤ) (toBondField hside U) =
        P.liftGaugeField (gaugeConfigOfSidesEq hlen U) := by
    intro U
    have hU : toBondField hside U ∈ PeriodicLattice.compactGaugeFields D.L e ((D.K : ℕ) : ℤ) :=
      hC.1.mapsTo (Set.mem_univ U)
    have h₁ : P.liftGaugeField (gaugeConfigOfSidesEq hlen U) =
        ⟨P.liftField (gaugeConfigOfSidesEq hlen U), hliftP.1 _⟩ := dif_pos (hliftP.1 _)
    rw [h₁]
    apply Subtype.ext
    funext l
    apply Subtype.ext
    have h₂ : InfiniteLattice.liftField D.L e ((D.K : ℕ) : ℤ) (toBondField hside U) = _ :=
      dif_pos hU
    rw [h₂]
    show toBondField hside U (InfiniteLattice.projectLink D.L e ((D.K : ℕ) : ℤ) l) =
      (edgeVariable (gaugeConfigOfSidesEq hlen U) (P.projEdge l) : Matrices.ComplexMatrix2)
    rw [← edgeEquivBond_projEdge hside hlen hfwd l]
    have h₃ := hconf.2.1 U ((edgeEquivOfSidesEq hlen).symm (P.projEdge l))
    rw [Equiv.apply_symm_apply] at h₃
    rw [h₃]
    simp only [toBondField, Equiv.symm_apply_apply]
    rfl
  have hemb : MeasurableEmbedding (gaugeConfigOfSidesEq (L := D.L) (κ := ((D.K : ℕ) : ℤ)) hlen) :=
    (hconf.1.homeomorph).measurableEmbedding
  have hpush := hconf.2.2
  have hact : ∀ U : d.GaugeConfig, P.wilsonAction (gaugeConfigOfSidesEq hlen U) = d.wilsonAction U := hface.2.2.2
  have hdens := (hl _ _ d).2.2.2.2.2 D.β D.beta_pos
  have hZ : torusPartition g n = d.normalizingIntegral D.β := by
    show ∫ U, Real.exp (-D.β * P.wilsonAction U) ∂P.haarMeasure = _
    show ∫ U, Real.exp (-D.β * P.wilsonAction U) ∂P.haarMeasure = ∫ U, Real.exp (-D.β * d.wilsonAction U) ∂_
    have : P.haarMeasure = (haarConfigMeasure D.L ((D.K : ℕ) : ℤ) d.sideLengths).map (gaugeConfigOfSidesEq hlen) :=
      hpush.symm
    rw [this, hemb.integral_map]
    simp only [hact]
  have hZpos : 0 < torusPartition g n := by
    rw [hZ]
    exact hdens.2.2.2
  refine ⟨hZpos, fun F hF => ?_⟩
  obtain ⟨hFm, C, hFC⟩ := hF
  have hm := InfiniteLattice.measurable_liftField D.L e ((D.K : ℕ) : ℤ)
  have h₁ : ∫ U, F U ∂InfiniteLattice.liftedWilsonMeasure D.L e D.K D.β =
      PeriodicLattice.gibbsExpectation D.L e (D.K : ℕ) D.β
        (fun W => F (InfiniteLattice.liftField D.L e ((D.K : ℕ) : ℤ) W)) :=
    InfiniteLattice.integral_liftedWilsonMeasure D.L e (D.K : ℕ) D.β ⟨hFm, C, hFC⟩
  have h₂ := hmean (fun W => F (InfiniteLattice.liftField D.L e ((D.K : ℕ) : ℤ) W))
    (hFm.comp hm) ⟨C, fun U _ => hFC _⟩
  have hdm : AEMeasurable (fun U : d.GaugeConfig => ENNReal.ofReal (d.boltzmannFactor D.β U))
      (haarConfigMeasure D.L ((D.K : ℕ) : ℤ) d.sideLengths) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hdens.2.2.1.aestronglyMeasurable.aemeasurable
  have h₃ : d.gibbsMean D.β (fun U => F (InfiniteLattice.liftField D.L e
        ((D.K : ℕ) : ℤ) (toBondField hside U))) =
      ((ENNReal.ofReal (d.normalizingIntegral D.β))⁻¹).toReal •
        ∫ U, (ENNReal.ofReal (d.boltzmannFactor D.β U)).toReal •
          F (InfiniteLattice.liftField D.L e ((D.K : ℕ) : ℤ) (toBondField hside U))
          ∂(haarConfigMeasure D.L ((D.K : ℕ) : ℤ) d.sideLengths) := by
    unfold CellGrid.gibbsMean CellGrid.gibbsMeasure
    rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul₀ hdm
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have h₄ : ∫ U, (ENNReal.ofReal (d.boltzmannFactor D.β U)).toReal •
        F (InfiniteLattice.liftField D.L e ((D.K : ℕ) : ℤ) (toBondField hside U))
        ∂(haarConfigMeasure D.L ((D.K : ℕ) : ℤ) d.sideLengths) =
      ∫ V, F (P.liftGaugeField V) *
        Complex.exp (-(D.β : ℂ) * (P.wilsonAction V : ℂ)) ∂P.haarMeasure := by
    have hH : P.haarMeasure = (haarConfigMeasure D.L ((D.K : ℕ) : ℤ) d.sideLengths).map
        (gaugeConfigOfSidesEq hlen) := hpush.symm
    rw [hH, hemb.integral_map]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    have hw : 0 ≤ d.boltzmannFactor D.β U := (Real.exp_pos _).le
    simp only [hlift U, hact U]
    rw [ENNReal.toReal_ofReal hw, Complex.real_smul, CellGrid.boltzmannFactor]
    push_cast
    ring
  rw [h₁, ← h₂, h₃, h₄, ENNReal.toReal_inv, ENNReal.toReal_ofReal (hZ ▸ hZpos.le), ← hZ,
    Complex.real_smul]
  have hZc : ((torusPartition g n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hZpos.ne'
  push_cast
  field_simp
end LawInAState.TorusMeanViaPeriods
end YangMills.Construction
end
