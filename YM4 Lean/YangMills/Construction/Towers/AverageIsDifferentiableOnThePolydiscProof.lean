import YangMills.Construction.Lattice.HolonomyUnderReorderingProof
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.Towers.AverageIsDifferentiableOnThePolydisc
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
namespace PolydiscSmoothing
section Links
variable {a : ℝ}
theorem isPositivelyOriented_or_opposite (e : InfiniteLattice.Link a) :
    e.IsPositivelyOriented ∨ e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem not_opposite_isPositivelyOriented (ha : a ≠ 0) {e : InfiniteLattice.Link a}
    (h : e.IsPositivelyOriented) : ¬ e.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := h
  rintro ⟨ν, hν⟩
  have hν' : e.initial - e.terminal = InfiniteLattice.axisStep a ν := hν
  have hsum : InfiniteLattice.axisStep a μ + InfiniteLattice.axisStep a ν = 0 := by
    rw [← hμ, ← hν']
    abel
  have hval := congrArg
    (fun s : InfiniteLattice.LatticePoint a => (s : InfiniteLattice.AmbientSpace) μ) hsum
  by_cases hνμ : ν = μ
  · subst hνμ
    simp [InfiniteLattice.axisStep] at hval
    exact ha (by linarith)
  · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne (Ne.symm hνμ)] at hval
    exact ha hval
end Links
section Group
variable {U : Matrices.ComplexMatrix2}
theorem inv_eq_star_of_mem (hU : U ∈ PeriodicLattice.compactGaugeGroup) : U⁻¹ = star U := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.inv_eq_star_of_mem <;> assumption
theorem inv_inv_of_mem (hU : U ∈ PeriodicLattice.compactGaugeGroup) : (U⁻¹)⁻¹ = U := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
theorem mem_complexGaugeGroup (hU : U ∈ PeriodicLattice.compactGaugeGroup) :
    U ∈ PeriodicLattice.complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.mp hU).2
theorem inv_mem_complexGaugeGroup (hU : U ∈ PeriodicLattice.compactGaugeGroup) :
    U⁻¹ ∈ PeriodicLattice.complexGaugeGroup := by
  have hd : U.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp hU).2
  show (U⁻¹).det = 1
  rw [inv_eq_star_of_mem hU, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hd, star_one]
theorem operatorNorm_inv_sub_one (hU : U ∈ PeriodicLattice.compactGaugeGroup) :
    Matrices.ComplexMatrix2.operatorNorm (U⁻¹ - 1) = Matrices.ComplexMatrix2.operatorNorm (U - 1) := by apply _root_.YangMills.Construction.PeriodicLattice.HolonomyUnderReordering.norm_inv_sub_one_of_mem <;> assumption
end Group
section Values
variable {L k j : ℕ} {S : Set (Edge L k j)} {F : Finset (Edge L k j)}
theorem fieldOfValuesOn_of_mem (w : F → Matrices.ComplexMatrix2) {e : Edge L k j} (h : e ∈ F) :
    fieldOfValuesOn F w e = w ⟨e, h⟩ := by
  unfold fieldOfValuesOn
  exact dif_pos h
theorem fieldOfValuesOn_of_opposite_mem (w : F → Matrices.ComplexMatrix2) {e : Edge L k j}
    (h : e ∉ F) (h' : e.opposite ∈ F) :
    fieldOfValuesOn F w e = (w ⟨e.opposite, h'⟩)⁻¹ := by
  unfold fieldOfValuesOn
  rw [dif_neg h, dif_pos h']
def valuesOnPositiveEdges (hF : ∀ e, e ∈ F ↔ e ∈ S ∧ e.IsPositivelyOriented)
    (w : F → Matrices.ComplexMatrix2) : PositiveEdgeOf S → Matrices.ComplexMatrix2 :=
  fun e => w ⟨e.1, (hF e.1).2 e.2⟩
theorem extendFromPositive_valuesOnPositiveEdges
    (hF : ∀ e, e ∈ F ↔ e ∈ S ∧ e.IsPositivelyOriented) (w : F → Matrices.ComplexMatrix2) :
    extendFromPositive S (valuesOnPositiveEdges hF w) = fieldOfValuesOn F w := by
  funext e
  unfold extendFromPositive
  by_cases h : e ∈ F
  · rw [dif_pos ((hF e).1 h), fieldOfValuesOn_of_mem w h]
    rfl
  · rw [dif_neg (fun h' => h ((hF e).2 h'))]
    by_cases h' : e.opposite ∈ F
    · rw [dif_pos ((hF e.opposite).1 h'), fieldOfValuesOn_of_opposite_mem w h h']
      rfl
    · rw [dif_neg (fun h'' => h' ((hF e.opposite).2 h''))]
      unfold fieldOfValuesOn
      rw [dif_neg h, dif_neg h']
theorem restrictPositive_fieldOfValuesOn
    (hF : ∀ e, e ∈ F ↔ e ∈ S ∧ e.IsPositivelyOriented) (w : F → Matrices.ComplexMatrix2) :
    restrictPositive S (fieldOfValuesOn F w) = valuesOnPositiveEdges hF w := by
  funext e
  exact fieldOfValuesOn_of_mem w ((hF e.1).2 e.2)
theorem fieldOfValuesOn_mem_nearIdentityPolydisc (hL : L ≠ 0) {ρ : ℝ}
    {c : Edge L k (j + 1)} {F : Finset (Edge L k j)}
    (hF : ∀ e, e ∈ F ↔ e ∈ doubleCubeLinks L (meshAt L k j) c ∧ e.IsPositivelyOriented)
    {w : F → Matrices.ComplexMatrix2} (hw : w ∈ nearIdentityValues F ρ) :
    fieldOfValuesOn F w ∈ nearIdentityPolydisc L k j ρ c := by
  have ha : meshAt L k j ≠ 0 := by
    unfold meshAt
    exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr hL)
  have hG : ∀ e, w e ∈ PeriodicLattice.compactGaugeGroup := hw.1
  have hopp : ∀ e ∈ doubleCubeLinks L (meshAt L k j) c,
      e.opposite ∈ doubleCubeLinks L (meshAt L k j) c := fun e he => ⟨he.2, he.1⟩
  have hcase : ∀ e ∈ doubleCubeLinks L (meshAt L k j) c, e ∉ F → e.opposite ∈ F := by
    intro e he heF
    rcases isPositivelyOriented_or_opposite e with hp | hp
    · exact absurd ((hF e).2 ⟨he, hp⟩) heF
    · exact (hF _).2 ⟨hopp e he, hp⟩
  refine ⟨⟨fun e he => ?_, fun e he => ?_⟩, fun e he => ?_⟩
  · by_cases h : e ∈ F
    · rw [fieldOfValuesOn_of_mem w h]
      exact mem_complexGaugeGroup (hG _)
    · rw [fieldOfValuesOn_of_opposite_mem w h (hcase e he h)]
      exact inv_mem_complexGaugeGroup (hG _)
  · by_cases h : e ∈ F
    · have hoF : e.opposite ∉ F := fun h' =>
        not_opposite_isPositivelyOriented ha ((hF e).1 h).2 ((hF _).1 h').2
      rw [fieldOfValuesOn_of_mem w h, fieldOfValuesOn_of_opposite_mem w hoF h]
      rfl
    · have h' := hcase e he h
      rw [fieldOfValuesOn_of_opposite_mem w h h', fieldOfValuesOn_of_mem w h',
        inv_inv_of_mem (hG _)]
  · by_cases h : e ∈ F
    · rw [fieldOfValuesOn_of_mem w h]
      exact hw.2 _
    · rw [fieldOfValuesOn_of_opposite_mem w h (hcase e he h), operatorNorm_inv_sub_one (hG _)]
      exact hw.2 _
theorem isRelativelyOpen_nearIdentityValues (F : Finset (Edge L k j)) (ρ : ℝ) :
    Matrices.ComplexMatrix2.IsRelativelyOpen (Matrices.specialUnitaryPower F)
      (nearIdentityValues F ρ) := by
  refine ⟨{w | ∀ e, Matrices.ComplexMatrix2.operatorNorm (w e - 1) < ρ}, ?_, ?_⟩
  · simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun e =>
      isOpen_lt (continuous_norm.comp ((continuous_apply e).sub continuous_const)) continuous_const
  · ext w
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
end Values
end PolydiscSmoothing
open PolydiscSmoothing in
theorem complexSmoothing_differentiableOn_polydisc : ComplexSmoothingDifferentiableOnPolydisc := by
  intro L hL k j hj ρ hρ c hc F hF
  have hL0 : L ≠ 0 := by
    have := hL.2
    omega
  refine ⟨isRelativelyOpen_nearIdentityValues F ρ, fun χ => ?_⟩
  obtain ⟨inst, hhol⟩ := ((hρ.fullSpace k j hj c hc).holomorphic_smoothing).1
  have hdiffp : DifferentiableOn ℝ χ.param χ.source :=
    χ.contDiffOn_param.differentiableOn (by simp)
  intro u hu
  have hup : u ∈ χ.source := hu.1
  set T := valuesOnPositiveEdges hF with hT
  have hTd : Differentiable ℝ T := by
    refine differentiable_pi.2 fun e => ?_
    exact differentiable_apply _
  have hmaps : MapsTo (fun u' => T (χ.param u')) (χ.coords (nearIdentityValues F ρ))
      (restrictPositive (doubleCubeLinks L (meshAt L k j) c) ''
        nearIdentityPolydisc L k j ρ c) := by
    intro u' hu'
    exact ⟨_, fieldOfValuesOn_mem_nearIdentityPolydisc hL0 hF hu'.2,
      restrictPositive_fieldOfValuesOn hF _⟩
  obtain ⟨G, hGan, hGeq⟩ := hhol.2.2 _ (hmaps hu)
  have hdu : DifferentiableWithinAt ℝ χ.param (χ.coords (nearIdentityValues F ρ)) u :=
    (hdiffp u hup).mono inter_subset_left
  have hTp : DifferentiableWithinAt ℝ (fun u' => T (χ.param u'))
      (χ.coords (nearIdentityValues F ρ)) u :=
    (hTd _).comp_differentiableWithinAt u hdu
  have hGd : DifferentiableAt ℝ G (T (χ.param u)) :=
    hGan.differentiableAt.restrictScalars ℝ
  have hcomp : DifferentiableWithinAt ℝ (fun u' => G (T (χ.param u')) ())
      (χ.coords (nearIdentityValues F ρ)) u :=
    DifferentiableAt.comp_differentiableWithinAt (g := fun y : Unit → Matrices.ComplexMatrix2 => y ()) u
      (differentiableAt_apply () _) (hGd.comp_differentiableWithinAt u hTp)
  have htend := (hTp.continuousWithinAt).tendsto_nhdsWithin hmaps
  have hev := htend.eventually hGeq
  have hval : ∀ w, complexSmoothing L (fieldOfValuesOn F w) c =
      complexSmoothing L (extendFromPositive _ (T w)) c := by
    intro w
    rw [hT, extendFromPositive_valuesOnPositiveEdges hF w]
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hev] with u' hu'
    show complexSmoothing L (fieldOfValuesOn F (χ.param u')) c = _
    rw [hval]
    exact congrFun hu' ()
  · show complexSmoothing L (fieldOfValuesOn F (χ.param u)) c = _
    rw [hval]
    exact congrFun (hGeq.self_of_nhdsWithin (hmaps hu)) ()
end YangMills.Construction.Tower.FullSpace
end
