import YangMills.Construction.InfiniteLattice.CoveringMapAndThePeriodicExtensionAtACutoff
import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLattice
import YangMills.Construction.InfiniteLattice.EquilibriumEquationOfThePeriodicExtensions
import YangMills.Construction.InfiniteLattice.InvarianceOfStatesUnderIsometriesOfACutoffLattice
import YangMills.Construction.InfiniteLattice.PeriodicExtensionInAWindow
import YangMills.Construction.InfiniteLattice.PropertiesOfTheWilsonKernelOnObservables
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace PeriodicLift
variable {a : ℝ}
def linkWindowOf {Λ : Finset (Link a)} (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) :
    LinkWindow a :=
  ⟨Λ, fun _ hb => mem_positiveLinks_iff.mp (hΛ hb)⟩
theorem glue_eq_splice (ha : 0 < a) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) (V : Λ → Matrices.ComplexMatrix2.specialUnitary)
    (U : GaugeField a) :
    (linkWindowOf hΛ).glue ha V U = WilsonOperator.splice ha hΛ V U := by
  refine WilsonOperator.eq_splice ha hΛ V U _ (fun b => dif_pos b.2) (fun b hb => ?_)
  have hopp : b.opposite ∉ Λ := fun h =>
    Link.opposite_not_isPositivelyOriented ha (mem_positiveLinks_iff.mp hb.1)
      (mem_positiveLinks_iff.mp (hΛ h))
  exact (dif_neg hb.2).trans (dif_neg hopp)
theorem boltzmannWeight_eq (ha : 0 < a) (β : ℝ) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) (V : Λ → Matrices.ComplexMatrix2.specialUnitary)
    (U : GaugeField a) :
    (linkWindowOf hΛ).boltzmannWeight ha β V U =
      WilsonOperator.localWeight β Λ (WilsonOperator.splice ha hΛ V U) := by
  unfold LinkWindow.boltzmannWeight
  rw [glue_eq_splice]
  rfl
theorem map_kernelOperator (ha : 0 < a) (β : ℝ) {Λ : Finset (Link a)}
    (hΛ : (Λ : Set (Link a)) ⊆ positiveLinkSet a) (φ : ℂ →L[ℝ] ℝ)
    (F : GaugeField a → ℂ) (U : GaugeField a)
    (hI : Integrable (fun V => F (WilsonOperator.splice ha hΛ V U) *
      (WilsonOperator.localWeight β Λ (WilsonOperator.splice ha hΛ V U) : ℂ))
      (Matrices.ComplexMatrix2.haarPi Λ)) :
    φ (WilsonOperator.kernelOperator ha β hΛ F U) =
      (linkWindowOf hΛ).realOperator ha β (fun U' => φ (F U')) U := by
  have hZ : WilsonOperator.localPartition ha β hΛ U =
      ∫ V', (linkWindowOf hΛ).boltzmannWeight ha β V' U ∂(linkWindowOf hΛ).haarProd := by
    unfold WilsonOperator.localPartition
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun V => (boltzmannWeight_eq ha β hΛ V U).symm)
  have hsmul : ∀ (r : ℝ) (z : ℂ), φ ((r : ℂ) * z) = r * φ z := fun r z => by
    rw [← Complex.real_smul, map_smul, smul_eq_mul]
  unfold LinkWindow.realOperator WilsonOperator.kernelOperator
  simp only [LinkWindow.rimKernel_restrictRim, LinkWindow.densityKernel]
  rw [← hZ, ← Complex.ofReal_inv, hsmul, ← φ.integral_comp_comm hI]
  simp only [mul_comm (F _), hsmul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  have e₁ := glue_eq_splice ha hΛ V U
  have e₂ := boltzmannWeight_eq ha β hΛ V U
  change (WilsonOperator.localPartition ha β hΛ U)⁻¹ *
      (WilsonOperator.localWeight β Λ (WilsonOperator.splice ha hΛ V U) *
        φ (F (WilsonOperator.splice ha hΛ V U))) =
    φ (F ((linkWindowOf hΛ).glue ha V U)) *
      ((linkWindowOf hΛ).boltzmannWeight ha β V U / WilsonOperator.localPartition ha β hΛ U)
  rw [e₁, e₂, div_eq_mul_inv]
  ring
theorem linkEndpoints_finite (S : Finset (Link a)) : (linkEndpoints S).Finite := by
  refine (S.finite_toSet.biUnion fun b _ =>
    (Set.toFinite ({b.initial, b.terminal} : Set (LatticePoint a)))).subset ?_
  rintro x ⟨b, hb, h⟩
  exact mem_biUnion hb (by simpa using h)
theorem le_endpointDiameter (S : Finset (Link a)) {x y : LatticePoint a}
    (hx : x ∈ linkEndpoints S) (hy : y ∈ linkEndpoints S) :
    GibbsAtFixedSpacing.linfNorm ((x : AmbientSpace) - (y : AmbientSpace)) ≤
      endpointDiameter S := by
  have hf := linkEndpoints_finite S
  refine le_csSup ?_ ⟨x, hx, y, hy, rfl⟩
  refine ((hf.image2 (fun x y : LatticePoint a =>
    GibbsAtFixedSpacing.linfNorm ((x : AmbientSpace) - (y : AmbientSpace))) hf).subset ?_).bddAbove
  rintro r ⟨x, hx, y, hy, rfl⟩
  exact ⟨x, hx, y, hy, rfl⟩
theorem projectLink_injOn (hC : LatticeCovering.CoveringStatement)
    (s : Conventions.StandingParameters) (β : ℝ) (hβ : 0 < β)
    (S : Finset (Link (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ))))
    (hw : endpointDiameter S < s.side) :
    InjOn (projectLink s.L s.m ((s.K : ℕ) : ℤ)) (S : Set _) := by
  have hinj := (hC ⟨s, β, hβ⟩).1.2.1
    ((fun x : LatticePoint _ => (x : AmbientSpace)) '' linkEndpoints S) (by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (le_endpointDiameter S hx hy).trans_lt hw)
  have hpt : ∀ {x y : LatticePoint (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ))},
      x ∈ linkEndpoints S → y ∈ linkEndpoints S →
      projectPoint s.L s.m ((s.K : ℕ) : ℤ) x = projectPoint s.L s.m ((s.K : ℕ) : ℤ) y →
      x = y := fun {x y} hx hy h =>
    Subtype.ext (hinj ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ (congrArg Subtype.val h))
  intro b hb b' hb' h
  exact Link.ext
    (hpt ⟨b, hb, Or.inl rfl⟩ ⟨b', hb', Or.inl rfl⟩ (congrArg PeriodicLattice.Bond.source h))
    (hpt ⟨b, hb, Or.inr rfl⟩ ⟨b', hb', Or.inr rfl⟩ (congrArg PeriodicLattice.Bond.target h))
theorem projectsPlaquettes_holds (hL : CutoffCoverLift.Statement)
    (s : Conventions.StandingParameters) : ProjectsPlaquettes s := by
  have h := hL s 1 one_pos
  intro p
  refine ⟨(h.2.1.1 p).1, fun U hU => ?_⟩
  exact (h.2.2.1 ⟨U, hU⟩).2.1 p
theorem shiftInvariant_holds
    (hI : CutoffLatticeStates.StatesInvariantUnderMotions)
    (s : Conventions.StandingParameters) (β : ℝ) (hβ : 0 < β) : ShiftInvariant s β := by
  obtain ⟨_, h⟩ := (hI s β hβ).1 s.m s.m.pos
  intro v A hA
  exact h ⟨fun x => x + (v : AmbientSpace), LinearMap.id, ⟨Equiv.refl _, fun _ => Or.inl rfl⟩,
    (v : AmbientSpace), v.2, fun _ => rfl⟩ A hA
theorem kernelInvariantInWindow_holds
    (hE : PeriodicExtensions.LiftedEquilibriumEquation.Statement)
    (hC : LatticeCovering.CoveringStatement)
    (hK : WilsonOperatorProperties)
    (s : Conventions.StandingParameters) (β : ℝ) (hβ : 0 < β) : KernelInvariantInWindow s β := by
  intro Λ S hΛ hS hplus hw F hF hFS
  have hprob : IsProbabilityMeasure (liftedWilsonMeasure s.L s.m s.K β) :=
    (hC ⟨s, β, hβ⟩).2.2.1.2.2.2.2.2
  have hk := ((hK s.L s.K s.isAdmissible.1 s.isAdmissible.2 s.K.pos
    (meshSize_pos s) β hβ).1 Λ (hΛ.trans hS)).1
  have hobs := hk.kernel_isBoundedObservable F hF
  have hint : ∀ {G : GaugeField (PeriodicLattice.meshSize s.L ((s.K : ℕ) : ℤ)) → ℂ},
      IsBoundedObservable G → Integrable G (liftedWilsonMeasure s.L s.m s.K β) := fun {G} hG => by
    obtain ⟨hm, C, hC'⟩ := hG
    exact Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC')
  have key : ∀ φ : ℂ →L[ℝ] ℝ,
      ∫ U, φ (WilsonOperator.kernelOperator (meshSize_pos s) β (hΛ.trans hS) F U)
          ∂liftedWilsonMeasure s.L s.m s.K β =
        ∫ U, φ (F U) ∂liftedWilsonMeasure s.L s.m s.K β := fun φ => by
    obtain ⟨hm, C, hC'⟩ := hF
    have h := hE ⟨s, β, hβ⟩ (linkWindowOf (hΛ.trans hS)) (S : Set _) S.finite_toSet hS hΛ
      (by
        rintro b ⟨⟨p, hp, hb⟩, -⟩
        exact hplus (Or.inr (mem_iUnion₂.mpr ⟨p, hp, hb⟩)))
      (projectLink_injOn hC s β hβ S hw) (fun U => φ (F U))
      (φ.continuous.measurable.comp hm)
      ⟨‖φ‖ * C, fun U => (φ.le_opNorm _).trans (by gcongr; exact hC' U)⟩
      ⟨hS, fun U U' h => congrArg φ (hFS U U' h)⟩
    simp only [CutoffLattice.integralAgainst] at h
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun U =>
      map_kernelOperator (meshSize_pos s) β (hΛ.trans hS) φ F U
        (hk.integrable_kernel F ⟨hm, C, hC'⟩ U))
  have hφ : ∀ φ : ℂ →L[ℝ] ℝ,
      φ (∫ U, WilsonOperator.kernelOperator (meshSize_pos s) β (hΛ.trans hS) F U
          ∂liftedWilsonMeasure s.L s.m s.K β) =
        φ (∫ U, F U ∂liftedWilsonMeasure s.L s.m s.K β) := fun φ => by
    rw [← φ.integral_comp_comm (hint hobs), ← φ.integral_comp_comm (hint hF)]
    exact key φ
  exact Complex.ext (hφ Complex.reCLM) (hφ Complex.imCLM)
end PeriodicLift
theorem PeriodicLift.holds
    (hL : CutoffCoverLift.Statement)
    (hC : LatticeCovering.CoveringStatement)
    (hE : PeriodicExtensions.LiftedEquilibriumEquation.Statement)
    (hI : CutoffLatticeStates.StatesInvariantUnderMotions)
    (hK : WilsonOperatorProperties) :
    PeriodicLift.Statement := fun s β hβ =>
  ⟨PeriodicLift.projectsPlaquettes_holds hL s,
    PeriodicLift.shiftInvariant_holds hI s β hβ,
    PeriodicLift.kernelInvariantInWindow_holds hE hC hK s β hβ⟩
end YangMills.Construction.InfiniteLattice
