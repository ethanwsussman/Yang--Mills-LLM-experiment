import YangMills.Construction.SourcesOnAFlow.MeanInAPeriodicExtensionProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CutoffCoverLift
variable {L m K : ℕ}
theorem torusCover_eq_iff (x y : AmbientSpace) :
    CutoffLattice.torusCover L m x = CutoffLattice.torusCover L m y ↔
      x - y ∈ latticeSubgroup (PeriodicLattice.torusSide L m) := by apply _root_.YangMills.Construction.PeriodicExtension.torusCover_eq_iff <;> assumption
theorem pointsAndLinks (hp : Covering.PeriodLattice_le L m K) :
    PointsAndLinks L m K := by
  refine ⟨hp, ?_, ?_, fun b => ⟨rfl, ?_, rfl⟩⟩
  · rw [PeriodicLattice.sublattice_eq_map_latticeSubgroup]
    rfl
  · intro x
    constructor
    · intro hx
      rw [PeriodicLattice.sublattice_eq_map_latticeSubgroup]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [PeriodicLattice.sublattice_eq_map_latticeSubgroup] at hx
      obtain ⟨y, hy, e⟩ := hx
      have hd : x - y ∈ latticeSubgroup (PeriodicLattice.torusSide L m) :=
        (torusCover_eq_iff x y).mp e.symm
      simpa using add_mem (hp hd) hy
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    change projectPoint L m (K : ℤ) b.terminal - projectPoint L m (K : ℤ) b.initial = _
    rw [← projectPoint_sub, hμ, projectPoint_axisStep]
theorem facesCovered (hf : Covering.ProjectsPlaquetteEdges L m K) :
    FacesCovered L m K := by apply _root_.YangMills.Construction.PeriodicExtension.facesCovered_of <;> assumption
theorem liftOfField
    (hf : Covering.ProjectsPlaquetteEdges L m K)
    (ha : Covering.FaceEnergyOfLift L m K)
    (ht : Covering.ProjectInvariantUnderPeriods L m K)
    (U : PeriodicLattice.CompactGaugeField L m (K : ℤ)) :
    LiftOfField L m K U := by
  refine ⟨fun b => liftCompactField_apply U b, fun p => ⟨?_, ha p U⟩, fun t hmem => ?_⟩
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hf p
    have hr : ∀ b : PeriodicLattice.Bond L m (K : ℤ),
        (((U.linkValue b)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
          U.1 b.opposite := fun b => by
      rw [← U.linkValue_opposite b]
      rfl
    rw [PeriodicExtensions.faceHolonomy_eq_edges, liftCompactField_apply, liftCompactField_apply,
      liftCompactField_apply, liftCompactField_apply, h₁, h₂, h₃, h₄]
    simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
      PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, Submonoid.coe_mul, hr]
    simp only [mul_assoc]
    rfl
  · exact Subtype.ext (funext fun b => (ht b t hmem).2 U)
theorem pushforwardWilson {β : ℝ} (h : LiftFormation.MeasuresAndPushforward L m K β) :
    PushforwardWilson L m K β := by
  obtain ⟨-, -, -, hp, -, hc⟩ := h
  exact ⟨hp, fun F hF => (hc F hF.1 hF.2).2.2⟩
theorem holds (hcovering : Covering.CoveringProperties)
    (hformed : LiftFormation.Statement) : Statement := by
  intro s β hβ
  obtain ⟨hf, ha, hp, ht, -⟩ := hcovering s
  exact ⟨pointsAndLinks hp, facesCovered hf, liftOfField hf ha ht,
    continuous_liftCompactField, pushforwardWilson (hformed s β hβ).2.2⟩
end YangMills.Construction.InfiniteLattice.CutoffCoverLift
