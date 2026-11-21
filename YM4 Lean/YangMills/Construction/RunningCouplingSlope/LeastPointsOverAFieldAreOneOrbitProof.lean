import YangMills.Construction.ClusterExpansionOfAStep.UnitQuaternionsAsSpecialUnitaryMatrices
import YangMills.Construction.RunningCouplingSlope.FibreFormIsASumOverTheStepsProof
import YangMills.Construction.RunningCouplingSlope.LeastPointsAreGaugeImagesOfSmallTangentsProof
import YangMills.Construction.SoftAverages.QuaternionsAsMatrices
import YangMills.Construction.ColdChainAtEveryLevel.CurlOfAGapOnAPatchProof
import YangMills.Construction.ColdStepAtMirrorFrames.SumsOverTheSitesOfATorus
import YangMills.Construction.Lattice.CovarianceOfTheAveragingMapsProof
import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreUnderAGaugeFunctionProof
import YangMills.Construction.RunningCouplingSlope.LeastFieldNearTheFlatField
import YangMills.Construction.RunningCouplingSlope.LeastPointReadsTheChain
import YangMills.Construction.RunningCouplingSlope.LeastPointsOverAFieldAreOneOrbit
import YangMills.Construction.RunningCouplingSlope.PlainMeanReadsAnyFrame
import YangMills.Construction.Matrices.UnitQuaternionsAsMatrices
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Matrices
open Tower BlockAverages ColdStepAtMirrorFrames
open TorusFields (TorusField TorusSite trivialField readAtLevel torusFrame)
namespace MinimizersFormOneGaugeOrbit
section Quaternions
private abbrev qmat (q : ℍ[ℝ]) : ComplexMatrix2 := SoftAverages.quaternionToMatrix q
private theorem quatMatrix_eq_qmat (q : ℍ[ℝ]) : UnitQuaternions.quatMatrix q = qmat q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UnitQuaternions.quatMatrix, SoftAverages.quaternionToMatrix, mul_comm]
abbrev _root_.YangMills.DeltaSharedProofs.p500685 := @quatMatrix_eq_qmat
private theorem qmat_one : qmat 1 = 1 := SoftAverages.quaternionToMatrix_one
private theorem qmat_mul (p q : ℍ[ℝ]) : qmat (p * q) = qmat p * qmat q := by apply _root_.YangMills.Construction.SoftAverages.quaternionToMatrix_mul <;> assumption
private theorem qmat_smul (r : ℝ) (q : ℍ[ℝ]) : qmat (r • q) = (r : ℂ) • qmat q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SoftAverages.quaternionToMatrix] <;> ring
abbrev _root_.YangMills.DeltaSharedProofs.p501227 := @qmat_smul
private theorem qmat_injective {p q : ℍ[ℝ]} (h : qmat p = qmat q) : p = q := by
  have e0 := congrFun (congrFun h 0) 0
  have e1 := congrFun (congrFun h 0) 1
  simp only [SoftAverages.quaternionToMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at e0 e1
  have r0 := congrArg Complex.re e0
  have i0 := congrArg Complex.im e0
  have r1 := congrArg Complex.re e1
  have i1 := congrArg Complex.im e1
  simp at r0 i0 r1 i1
  ext <;> assumption
abbrev _root_.YangMills.DeltaSharedProofs.p501191 := @qmat_injective
private theorem qmat_mem (g : UnitQuaternion) : qmat (g : ℍ[ℝ]) ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.quaternionToMatrix_mem_specialUnitary <;> assumption
private theorem exists_qmat_of_mem {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.specialUnitary) :
    ∃ g : UnitQuaternion, A = qmat (g : ℍ[ℝ]) := by
  obtain ⟨g, hg⟩ := UnitQuaternions.toSpecialUnitaryHom_surjective ⟨A, hA⟩
  refine ⟨g, ?_⟩
  have := congrArg Subtype.val hg
  rw [← quatMatrix_eq_qmat]
  exact this.symm
abbrev _root_.YangMills.DeltaSharedProofs.p500695 := @exists_qmat_of_mem
private theorem coe_unit_inv (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
private theorem qmat_inv (g : UnitQuaternion) :
    (qmat (g : ℍ[ℝ]))⁻¹ = qmat ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by apply _root_.YangMills.DeltaSharedProofs.p502200 <;> assumption
private theorem qmat_inv_mem {g : UnitQuaternion} :
    (qmat (g : ℍ[ℝ]))⁻¹ ∈ ComplexMatrix2.specialUnitary := by
  rw [qmat_inv]
  exact qmat_mem _
private theorem traceDefect_qmat (q : ℍ[ℝ]) : traceDefect (qmat q) = 1 - q.re := by apply _root_.YangMills.DeltaSharedProofs.p500863 <;> assumption
private theorem half_fullTrace_qmat (q : ℍ[ℝ]) : (1 / 2) * (ComplexMatrix2.fullTrace (qmat q)).re = q.re := by
  simp [ComplexMatrix2.fullTrace, Matrix.trace_fin_two, SoftAverages.quaternionToMatrix]
  ring
abbrev _root_.YangMills.DeltaSharedProofs.p501762 := @half_fullTrace_qmat
private theorem det_qmat (q : ℍ[ℝ]) : Matrix.det (qmat q) = ((Quaternion.normSq q : ℝ) : ℂ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.det_quaternionToMatrix <;> assumption
private theorem sqrt_det_qmat (m : ℍ[ℝ]) : (Matrix.det (qmat m)) ^ (1 / 2 : ℂ) = ((‖m‖ : ℝ) : ℂ) := by
  rw [det_qmat, Quaternion.normSq_eq_norm_mul_self]
  have h0 := norm_nonneg m
  have e : (((‖m‖ * ‖m‖ : ℝ)) : ℂ) ^ (1 / 2 : ℂ) = (((‖m‖ * ‖m‖) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    norm_num
  rw [e, ← Real.sqrt_eq_rpow, Real.sqrt_mul_self h0]
abbrev _root_.YangMills.DeltaSharedProofs.p501669 := @sqrt_det_qmat
private theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
private theorem plaquette_term_nonneg (g : UnitQuaternion) : 0 ≤ 1 - ((g : ℍ[ℝ])).re := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.one_sub_re_nonneg <;> assumption
end Quaternions
section Coordinates
variable {L n k : ℕ}
private def coordSite (j : ℕ) (z : Fin 4 → ℤ) : Vertex L n k j := PeriodicLattice.offsetSite 0 z
private theorem sublatticeCoords (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) :
    PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k j) :=
  (hC L n hL.1 hL.2 hn).1 _ (by simp only [PeriodicLattice.levelDepth]; omega)
private theorem two_mul_halfPeriod {j : ℕ} (hj : j ≤ k) :
    2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k j) = 2 * L ^ (n + (k - j)) := by
  simp only [PeriodicLattice.halfPeriod, PeriodicLattice.levelDepth]
  congr 2
  omega
abbrev _root_.YangMills.SharedProofs.p9710 := @two_mul_halfPeriod
private theorem coordSite_surjective (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) (x : Vertex L n k j) :
    ∃ z, x = coordSite j z :=
  (sublatticeCoords hC hL hn hj).2.2.2.1 0 x
private theorem coordSite_eq_iff (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) (z w : Fin 4 → ℤ) :
    coordSite (L := L) (n := n) (k := k) j z = coordSite j w ↔
      ∀ μ, ((2 * L ^ (n + (k - j)) : ℕ) : ℤ) ∣ w μ - z μ := by
  have h := (sublatticeCoords hC hL hn hj).2.2.2.2.1 0 z w
  rw [two_mul_halfPeriod hj] at h
  refine h.trans (forall_congr' fun μ => ?_)
  exact Int.modEq_iff_dvd
private theorem coordSite_add (j : ℕ) (z w : Fin 4 → ℤ) :
    coordSite (L := L) (n := n) (k := k) j (z + w) = coordSite j z + coordSite j w := by
  simp [coordSite, PeriodicLattice.offsetSite, add_smul, Finset.sum_add_distrib]
private theorem sum_single_smul {A : Type*} [AddCommGroup A] (f : Fin 4 → A) (μ : Fin 4) :
    ∑ ν, (Pi.single μ 1 : Fin 4 → ℤ) ν • f ν = f μ := by
  rw [Finset.sum_eq_single μ]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp
abbrev _root_.YangMills.SharedProofs.p19285 := @sum_single_smul
private theorem unitStep_eq_coordSite (j : ℕ) (μ : Fin 4) :
    PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ =
      coordSite (L := L) (n := n) (k := k) j (Pi.single μ 1) := by
  simp only [coordSite, PeriodicLattice.offsetSite, zero_add]
  rw [sum_single_smul]
private theorem two_lt_period (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (j : ℕ) :
    (2 : ℤ) < ((2 * L ^ (n + (k - j)) : ℕ) : ℤ) := by
  have h1 : L ^ 1 ≤ L ^ (n + (k - j)) := Nat.pow_le_pow_right (by have := hL.2; omega) (by omega)
  have h2 := hL.2
  rw [pow_one] at h1
  have : 2 < 2 * L ^ (n + (k - j)) := by omega
  exact_mod_cast this
private theorem exists_forwardFrom_of_pos {j : ℕ} (b : Edge L n k j) (hb : b.IsPositivelyOriented) :
    ∃ x μ, b = PeriodicLattice.Bond.forwardFrom x μ := by
  obtain ⟨μ, h⟩ := hb
  refine ⟨b.source, μ, PeriodicLattice.Bond.ext rfl ?_⟩
  show b.target = b.source + _
  rw [← h]
  abel
abbrev _root_.YangMills.SharedProofs.p50830 := @exists_forwardFrom_of_pos
private theorem forwardFrom_pos {j : ℕ} (x : Vertex L n k j) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
private theorem unitStep_injective (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) {μ ν : Fin 4}
    (h : PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) ν) :
    μ = ν := by
  by_contra hne
  rw [unitStep_eq_coordSite, unitStep_eq_coordSite, coordSite_eq_iff hC hL hn hj] at h
  have h1 := h μ
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h1
  have h3 : ((2 * L ^ (n + (k - j)) : ℕ) : ℤ) ∣ 1 := by
    have := dvd_neg.mpr h1
    simpa using this
  have h2 := Int.le_of_dvd one_pos h3
  have := two_lt_period (k := k) hL hn j
  omega
private theorem forwardFrom_injective (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    {x y : Vertex L n k j} {μ ν : Fin 4}
    (h : PeriodicLattice.Bond.forwardFrom x μ = PeriodicLattice.Bond.forwardFrom y ν) : x = y ∧ μ = ν := by
  have h1 : x = y := congrArg PeriodicLattice.Bond.source h
  refine ⟨h1, ?_⟩
  have h2 : x + _ = y + _ := congrArg PeriodicLattice.Bond.target h
  subst h1
  exact unitStep_injective hC hL hn hj (add_left_cancel h2)
abbrev _root_.YangMills.SharedProofs.p47369 := @forwardFrom_injective
private theorem not_opposite_pos (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) (b : Edge L n k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  rintro ⟨ν, hν⟩
  obtain ⟨μ, hμ⟩ := hb
  have e : PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ +
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) ν = 0 := by
    rw [← hμ, ← hν]
    show b.target - b.source + (b.source - b.target) = 0
    abel
  have e0 : coordSite (L := L) (n := n) (k := k) j 0 = 0 := by
    simp [coordSite, PeriodicLattice.offsetSite]
  rw [unitStep_eq_coordSite, unitStep_eq_coordSite, ← coordSite_add, ← e0, coordSite_eq_iff hC hL hn hj] at e
  have h1 := e μ
  have hp := two_lt_period (k := k) hL hn j
  simp only [Pi.zero_apply, zero_sub, Pi.add_apply, Pi.single_eq_same] at h1
  have h3 := dvd_neg.mp h1
  by_cases h : μ = ν
  · subst h
    simp only [Pi.single_eq_same] at h3
    have h2 := Int.le_of_dvd (by norm_num) h3
    omega
  · simp only [Pi.single_eq_of_ne h, add_zero] at h3
    have h2 := Int.le_of_dvd (by norm_num) h3
    omega
private theorem pos_or_opposite_pos {j : ℕ} (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem specialUnitary_inv_mem {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.specialUnitary) :
    A⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
private theorem specialUnitary_inv_inv {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.specialUnitary) :
    (A⁻¹)⁻¹ = A := by apply _root_.YangMills.SharedProofs.p318 <;> assumption
private theorem fieldOfPositiveValues_mem (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    (w : PositiveEdge L n k j → ComplexMatrix2) (hw : ∀ c, w c ∈ ComplexMatrix2.specialUnitary) :
    fieldOfPositiveValues w ∈ fieldSpace L n k j := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · show fieldOfPositiveValues w b ∈ ComplexMatrix2.specialUnitary
    unfold fieldOfPositiveValues
    split_ifs with h h'
    · exact hw _
    · exact specialUnitary_inv_mem (hw _)
    · exact one_mem _
  · rcases pos_or_opposite_pos b with h | h
    · have h2 := not_opposite_pos hC hL hn hj b h
      have h3 : (b.opposite.opposite).IsPositivelyOriented := h
      simp only [fieldOfPositiveValues, dif_pos h, dif_neg h2, dif_pos h3]
      rfl
    · have h2 : ¬ b.IsPositivelyOriented := fun h' => not_opposite_pos hC hL hn hj b h' h
      simp only [fieldOfPositiveValues, dif_pos h, dif_neg h2]
      exact (specialUnitary_inv_inv (hw _)).symm
abbrev _root_.YangMills.SharedProofs.p18687 := @fieldOfPositiveValues_mem
private theorem field_ext_of_forward (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    {A B : Edge L n k j → ComplexMatrix2} (hA : A ∈ fieldSpace L n k j) (hB : B ∈ fieldSpace L n k j)
    (h : ∀ z μ, A (PeriodicLattice.Bond.forwardFrom (coordSite j z) μ) =
      B (PeriodicLattice.Bond.forwardFrom (coordSite j z) μ)) :
    A = B := by
  have hp : ∀ b : Edge L n k j, b.IsPositivelyOriented → A b = B b := by
    intro b hb
    obtain ⟨x, μ, rfl⟩ := exists_forwardFrom_of_pos b hb
    obtain ⟨z, rfl⟩ := coordSite_surjective hC hL hn hj x
    exact h z μ
  funext b
  rcases pos_or_opposite_pos b with hb | hb
  · exact hp b hb
  · have h1 := hA.2 b.opposite (Set.mem_univ _)
    have h2 := hB.2 b.opposite (Set.mem_univ _)
    have e : b.opposite.opposite = b := rfl
    rw [e] at h1 h2
    rw [h1, h2, hp _ hb]
end Coordinates
section Compatible
variable {L n k : ℕ} {F : BlockFrame}
private structure Compatible (F : BlockFrame) (L n k J : ℕ) : Prop where
  blockSide_eq : F.blockSide = L
  le_top : J ≤ F.top
  le_levels : J ≤ k
  period_eq : ∀ j, j ≤ J → ∀ i, F.period j i = 2 * L ^ (n + (k - j))
  extent_pos : ∀ i, 0 < F.extent i
private def Represents (F : BlockFrame) (j : ℕ) (C : Edge L n k j → ComplexMatrix2) (Y : F.GaugeField j) : Prop :=
  ∀ (z : Fin 4 → ℤ) (μ : Fin 4),
    C (PeriodicLattice.Bond.forwardFrom (coordSite j z) μ) = qmat ((Y (siteOfCoords j z) μ : UnitQuaternion) : ℍ[ℝ])
private theorem coordSite_eq_iff_siteOfCoords (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Compatible F L n k J)
    {j : ℕ} (hj : j ≤ J) (z w : Fin 4 → ℤ) :
    coordSite (L := L) (n := n) (k := k) j z = coordSite j w ↔
      (siteOfCoords j z : F.Site j) = siteOfCoords j w := by
  rw [coordSite_eq_iff hC hL hn (hj.trans hT.le_levels), siteOfCoords_eq_iff]
  refine forall_congr' fun i => ?_
  rw [hT.period_eq j hj i]
private theorem exists_field_of_frame (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Compatible F L n k J)
    {j : ℕ} (hj : j ≤ J) (Y : F.GaugeField j) : ∃ C ∈ fieldSpace L n k j, Represents F j C Y := by
  have hjk := hj.trans hT.le_levels
  have hch : ∀ c : PositiveEdge L n k j, ∃ (z : Fin 4 → ℤ) (μ : Fin 4),
      c.1 = PeriodicLattice.Bond.forwardFrom (coordSite j z) μ := by
    intro c
    obtain ⟨x, μ, h⟩ := exists_forwardFrom_of_pos c.1 c.2
    obtain ⟨z, rfl⟩ := coordSite_surjective hC hL hn hjk x
    exact ⟨z, μ, h⟩
  choose zc μc hc using hch
  refine ⟨fieldOfPositiveValues fun c => qmat ((Y (siteOfCoords j (zc c)) (μc c) : UnitQuaternion) : ℍ[ℝ]),
    fieldOfPositiveValues_mem hC hL hn hjk _ fun c => qmat_mem _, ?_⟩
  intro z μ
  have hp := forwardFrom_pos (coordSite (L := L) (n := n) (k := k) j z) μ
  simp only [fieldOfPositiveValues, dif_pos hp]
  obtain ⟨e1, e2⟩ := forwardFrom_injective hC hL hn hjk (hc ⟨_, hp⟩)
  rw [← e2, ← (coordSite_eq_iff_siteOfCoords hC hL hn hT hj _ _).mp e1]
private theorem exists_frameField (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Compatible F L n k J)
    {j : ℕ} (hj : j ≤ J) {A : Edge L n k j → ComplexMatrix2} (hA : A ∈ fieldSpace L n k j) :
    ∃ Y : F.GaugeField j, Represents F j A Y := by
  have h : ∀ (x : F.Site j) (μ : Fin 4), ∃ g : UnitQuaternion,
      A (PeriodicLattice.Bond.forwardFrom (coordSite j (siteCoords x)) μ) = qmat (g : ℍ[ℝ]) :=
    fun x μ => exists_qmat_of_mem (hA.1 _ (Set.mem_univ _))
  choose Y hY using h
  refine ⟨Y, fun z μ => ?_⟩
  have e : coordSite (L := L) (n := n) (k := k) j z = coordSite j (siteCoords (siteOfCoords j z : F.Site j)) :=
    (coordSite_eq_iff_siteOfCoords hC hL hn hT hj _ _).mpr (_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords _).symm
  rw [e]
  exact hY _ _
private theorem cast_dvd (P : ℕ) (c : ℤ) : (P : ℤ) ∣ c - (((c : ZMod P)).cast : ℤ) :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (by rw [ZMod.intCast_zmod_cast])
private theorem readAtLevel_back {j M : ℕ} (hper : ∀ i, F.period j i = M) (Y : F.GaugeField j) :
    readAtLevel F j (fun x i => Y (siteOfCoords j fun l => (((x l : ZMod M)).cast : ℤ)) i : TorusField M) = Y := by
  funext x i
  show Y (siteOfCoords j fun l => ((((siteCoords x l : ℤ) : ZMod M)).cast : ℤ)) i = Y x i
  congr 1
  conv_rhs => rw [← _root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords x]
  rw [siteOfCoords_eq_iff]
  intro l
  rw [hper l]
  exact cast_dvd M _
abbrev _root_.YangMills.DeltaSharedProofs.p502190 := @readAtLevel_back
abbrev _root_.YangMills.SharedProofs.p81894 := @readAtLevel_back
private theorem contourMean_of_represents (hP : ContourMeanMatchesFrame)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Compatible F L n k J)
    {j : ℕ} (hj : j + 1 ≤ J)
    {A : Edge L n k j → ComplexMatrix2} (hA : A ∈ fieldSpace L n k j) {Y : F.GaugeField j}
    (hR : Represents F j A Y) (z : Fin 4 → ℤ) (μ : Fin 4) :
    contourMean A (PeriodicLattice.Bond.forwardFrom (coordSite (j + 1) z) μ) =
      qmat (_root_.YangMills.Construction.BlockAverages.contourAverage Y (siteOfCoords (j + 1) z, μ)) := by
  have hjk : j < k := lt_of_lt_of_le (Nat.lt_of_succ_le hj) hT.le_levels
  have hM : (2 * L ^ (n + (k - (j + 1)))) * L = 2 * L ^ (n + (k - j)) := by
    have : n + (k - j) = n + (k - (j + 1)) + 1 := by omega
    rw [this, pow_succ]
    ring
  have hper : ∀ i, F.period j i = (2 * L ^ (n + (k - (j + 1)))) * L := fun i => by
    rw [hT.period_eq j (by omega) i, hM]
  have h := hP L hL n k j (2 * L ^ (n + (k - (j + 1)))) hn hjk hM F hT.blockSide_eq hper
    (hT.period_eq (j + 1) hj)
    (fun x i => Y (siteOfCoords j fun l => (((x l : ZMod _)).cast : ℤ)) i) A
    ⟨hA, fun zz μ => hR _ μ⟩ z μ
  rw [readAtLevel_back hper] at h
  exact h
private theorem normalized_mem_unitary {m : ℍ[ℝ]} (h0 : m ≠ 0) : (‖m‖⁻¹ • m) ∈ unitary ℍ[ℝ] := by apply _root_.YangMills.Construction.BlockAverages.smul_inv_norm_mem_unitary <;> assumption
private theorem meanRadius_of_contourMean {j : ℕ} {A : Edge L n k j → ComplexMatrix2}
    {c : Edge L n k (j + 1)} {m : ℍ[ℝ]}
    (hm : contourMean A c = qmat m) : meanRadius A c = ((‖m‖ : ℝ) : ℂ) := by
  simp only [meanRadius, hm]
  exact sqrt_det_qmat m
abbrev _root_.YangMills.DeltaSharedProofs.p500717 := @meanRadius_of_contourMean
private theorem normalizedMean_of_contourMean {j : ℕ} {A : Edge L n k j → ComplexMatrix2}
    {c : Edge L n k (j + 1)} {m : ℍ[ℝ]}
    (hm : contourMean A c = qmat m) (h0 : m ≠ 0) :
    normalizedMean A c = qmat ((⟨‖m‖⁻¹ • m, normalized_mem_unitary h0⟩ : UnitQuaternion) : ℍ[ℝ]) := by
  show (meanRadius A c)⁻¹ • contourMean A c = qmat (‖m‖⁻¹ • m)
  rw [meanRadius_of_contourMean hm, hm, qmat_smul]
  push_cast
  rfl
abbrev _root_.YangMills.DeltaSharedProofs.p500417 := @normalizedMean_of_contourMean
private theorem re_mul_star_swap (m q : ℍ[ℝ]) : (m * star q).re = (q * star m).re := by
  have h : star (q * star m) = m * star q := by rw [star_mul, star_star]
  rw [← h]
  simp
  ring
abbrev _root_.YangMills.SharedProofs.p60130 := @re_mul_star_swap
private theorem cost_term_eq {j : ℕ} {A : Edge L n k j → ComplexMatrix2} {c : Edge L n k (j + 1)}
    {m : ℍ[ℝ]} (hm : contourMean A c = qmat m) (g : UnitQuaternion) :
    (meanRadius A c).re * traceDefect (qmat (g : ℍ[ℝ]) * (normalizedMean A c)⁻¹) =
      ‖m‖ - (m * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by
  rw [meanRadius_of_contourMean hm, Complex.ofReal_re]
  by_cases h0 : m = 0
  · subst h0
    simp
  · have hn0 : ‖m‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    rw [normalizedMean_of_contourMean hm h0, qmat_inv, ← qmat_mul, traceDefect_qmat, coe_unit_inv,
      coe_unit_inv, re_mul_star_swap m (g : ℍ[ℝ])]
    show ‖m‖ * (1 - ((g : ℍ[ℝ]) * star (‖m‖⁻¹ • m)).re) = _
    have hs : ∀ (r : ℝ) (p q : ℍ[ℝ]), (p * star (r • q)).re = r * (p * star q).re := by
      intro r p q
      simp
    rw [hs]
    field_simp
abbrev _root_.YangMills.DeltaSharedProofs.p502207 := @cost_term_eq
private theorem sum_eq_finsum {α β : Type*} (s : Finset α) (f : α → ℝ) (g : β → ℝ) (φ : ↥s → β)
    (hφ : Function.Bijective φ) (h : ∀ a : ↥s, f a = g (φ a)) :
    ∑ a ∈ s, f a = ∑ᶠ b, g b := by
  rw [← finsum_comp_equiv (Equiv.ofBijective φ hφ), finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort]
  exact Finset.sum_congr rfl fun a _ => h a
abbrev _root_.YangMills.SharedProofs.p64412 := @sum_eq_finsum
private def fitCost {j : ℕ} (A : Edge L n k j → ComplexMatrix2) (B : Edge L n k (j + 1) → ComplexMatrix2) : ℝ :=
  ∑ᶠ c : PositiveEdge L n k (j + 1),
    (meanRadius A c.1).re * traceDefect (B c.1 * (normalizedMean A c.1)⁻¹)
private theorem mem_innerBonds (hL : Conventions.IsAdmissibleBlockingFactor L) {J : ℕ} (hT : Compatible F L n k J)
    {j : ℕ} (hj : j ≤ J) (b : F.Site j × Fin 4) : b ∈ innerBonds (finiteCells F) j := by
  have hodd : Odd F.blockSide := hT.blockSide_eq ▸ hL.1
  have hs := fun x : F.Site j => mem_allSites hodd hT.extent_pos (hj.trans hT.le_top) x
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨hs _, hs _⟩
private theorem sum_blockFit_eq (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ}
    (hT : Compatible F L n k J) {j : ℕ} (hj : j + 1 ≤ J)
    {A : Edge L n k j → ComplexMatrix2} (hA : A ∈ fieldSpace L n k j) {B : Edge L n k (j + 1) → ComplexMatrix2}
    {Y : F.GaugeField j} {Y' : F.GaugeField (j + 1)} (hR : Represents F j A Y)
    (hR' : Represents F (j + 1) B Y') :
    ∑ c ∈ innerBonds (finiteCells F) (j + 1), blockFit Y Y' c = fitCost A B := by
  have hjk := hj.trans hT.le_levels
  refine sum_eq_finsum _ _ _ (fun p => ⟨PeriodicLattice.Bond.forwardFrom (coordSite (j + 1) (siteCoords p.1.1)) p.1.2,
    forwardFrom_pos _ _⟩) ⟨?_, ?_⟩ ?_
  · rintro ⟨⟨x, μ⟩, hp⟩ ⟨⟨y, ν⟩, hq⟩ h
    have h1 := congrArg Subtype.val h
    obtain ⟨e1, e2⟩ := forwardFrom_injective hC hL hn hjk h1
    have e3 := (coordSite_eq_iff_siteOfCoords hC hL hn hT hj _ _).mp e1
    rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords, _root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords] at e3
    simp only at e2 e3
    subst e2 e3
    rfl
  · rintro ⟨c, hc⟩
    obtain ⟨x, μ, rfl⟩ := exists_forwardFrom_of_pos c hc
    obtain ⟨z, rfl⟩ := coordSite_surjective hC hL hn hjk x
    refine ⟨⟨(siteOfCoords (j + 1) z, μ), mem_innerBonds hL hT hj _⟩, Subtype.ext ?_⟩
    show PeriodicLattice.Bond.forwardFrom
      (coordSite (j + 1) (siteCoords (siteOfCoords (j + 1) z : F.Site (j + 1)))) μ = _
    rw [(coordSite_eq_iff_siteOfCoords hC hL hn hT hj _ _).mpr (_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords _)]
  · rintro ⟨⟨x, μ⟩, hp⟩
    have h1 := contourMean_of_represents hP hL hn hT hj hA hR (siteCoords x) μ
    have h2 := hR' (siteCoords x) μ
    rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords] at h1 h2
    show blockFit Y Y' (x, μ) = _
    simp only
    rw [h2, cost_term_eq h1]
    rfl
end Compatible
section MinimalAction
variable {L n k : ℕ} {F G : BlockFrame}
private theorem Compatible.mono {J J' : ℕ} (hT : Compatible F L n k J) (h : J' ≤ J) : Compatible F L n k J' :=
  ⟨hT.blockSide_eq, h.trans hT.le_top, h.trans hT.le_levels, fun j hj => hT.period_eq j (hj.trans h),
    hT.extent_pos⟩
private theorem plaquetteHolonomy_eq (Y : F.GaugeField 0) (x : F.Site 0) (μ ν : Fin 4) :
    BlockAverages.plaquetteHolonomy Y (x, μ, ν) =
      Y x μ * Y (x + BlockAverages.unitStep 0 μ) ν * (Y (x + BlockAverages.unitStep 0 ν) μ)⁻¹ * (Y x ν)⁻¹ := by apply _root_.YangMills.Construction.PatchCurls.plaquetteHolonomy_eq <;> assumption
private theorem wilsonAction_of_represents (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Compatible F L n k J)
    {A : Edge L n k 0 → ComplexMatrix2} (hA : A ∈ fieldSpace L n k 0) {Y : F.GaugeField 0}
    (hR : Represents F 0 A Y) :
    BlockAverages.wilsonAction (finiteCells F) Y = Tower.plaquetteAction L n k A := by
  have hodd : Odd F.blockSide := hT.blockSide_eq ▸ hL.1
  have hs := fun x : F.Site 0 => mem_allSites hodd hT.extent_pos (Nat.zero_le _) x
  have hk0 : 0 ≤ k := Nat.zero_le _
  have hj0 : 0 ≤ J := Nat.zero_le _
  have hmem : ∀ q : F.Site 0 × Fin 4 × Fin 4, q.2.1 < q.2.2 → q ∈ innerPlaquettes (finiteCells F) 0 := by
    intro q hq
    simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hs _, hq, fun y _ => hs y⟩
  show ∑ p ∈ innerPlaquettes (finiteCells F) 0,
      (1 - ((BlockAverages.plaquetteHolonomy Y p : UnitQuaternion) : ℍ[ℝ]).re) =
    ∑ᶠ p : Face L n k 0, PeriodicLattice.plaquetteCost A p
  refine sum_eq_finsum _ _ _ (fun q => ⟨coordSite 0 (siteCoords q.1.1), q.1.2.1, q.1.2.2,
    (Finset.mem_filter.mp q.2).2.1⟩) ⟨?_, ?_⟩ ?_
  · rintro ⟨⟨x, μ, ν⟩, hp⟩ ⟨⟨y, μ', ν'⟩, hq⟩ h
    have e1 := congrArg PeriodicLattice.Plaquette.origin h
    have e2 := congrArg PeriodicLattice.Plaquette.firstAxis h
    have e3 := congrArg PeriodicLattice.Plaquette.secondAxis h
    have e4 := (coordSite_eq_iff_siteOfCoords hC hL hn hT hj0 _ _).mp e1
    rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords, _root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords] at e4
    simp only at e2 e3 e4
    subst e2 e3 e4
    rfl
  · rintro ⟨b, μ, ν, h⟩
    obtain ⟨z, rfl⟩ := coordSite_surjective hC hL hn hk0 b
    refine ⟨⟨(siteOfCoords 0 z, μ, ν), hmem _ h⟩, ?_⟩
    refine PeriodicLattice.Plaquette.ext ?_ rfl rfl
    exact (coordSite_eq_iff_siteOfCoords hC hL hn hT hj0 _ _).mpr (_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords _)
  · rintro ⟨⟨x, μ, ν⟩, hp⟩
    set z := siteCoords x with hz
    have hx : (siteOfCoords 0 z : F.Site 0) = x := _root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords x
    have hadd : ∀ ρ : Fin 4, (siteOfCoords 0 (z + Pi.single ρ 1) : F.Site 0) = x + BlockAverages.unitStep 0 ρ := by
      intro ρ
      rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_add, hx]
      rfl
    have hst : ∀ ρ : Fin 4, coordSite (L := L) (n := n) (k := k) 0 z +
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) ρ = coordSite 0 (z + Pi.single ρ 1) := by
      intro ρ
      rw [coordSite_add, unitStep_eq_coordSite]
    have r3 := hA.2 (PeriodicLattice.Bond.forwardFrom
      (coordSite 0 z + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) ν) μ) (Set.mem_univ _)
    have r4 := hA.2 (PeriodicLattice.Bond.forwardFrom (coordSite 0 z) ν) (Set.mem_univ _)
    show 1 - ((BlockAverages.plaquetteHolonomy Y (x, μ, ν) : UnitQuaternion) : ℍ[ℝ]).re =
      1 - (1 / 2) * (ComplexMatrix2.fullTrace (PeriodicLattice.pathHolonomy A
      [PeriodicLattice.Bond.forwardFrom (coordSite 0 z) μ,
       PeriodicLattice.Bond.forwardFrom (coordSite 0 z + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) μ) ν,
       (PeriodicLattice.Bond.forwardFrom
         (coordSite 0 z + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) ν) μ).opposite,
       (PeriodicLattice.Bond.forwardFrom (coordSite 0 z) ν).opposite])).re
    have hh : PeriodicLattice.pathHolonomy A
      [PeriodicLattice.Bond.forwardFrom (coordSite 0 z) μ,
       PeriodicLattice.Bond.forwardFrom (coordSite 0 z + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) μ) ν,
       (PeriodicLattice.Bond.forwardFrom
         (coordSite 0 z + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) ν) μ).opposite,
       (PeriodicLattice.Bond.forwardFrom (coordSite 0 z) ν).opposite] =
        qmat ((BlockAverages.plaquetteHolonomy Y (x, μ, ν) : UnitQuaternion) : ℍ[ℝ]) := by
      simp only [PeriodicLattice.pathHolonomy, List.map, List.prod_cons, List.prod_nil, mul_one]
      rw [r3, r4, hst, hst, hR, hR, hR, hR, hadd, hadd, hx, plaquetteHolonomy_eq, qmat_inv, qmat_inv]
      simp only [Submonoid.coe_mul, qmat_mul, mul_assoc]
    rw [hh, half_fullTrace_qmat]
private theorem blockFit_nonneg {j : ℕ} (X : F.GaugeField j) (X' : F.GaugeField (j + 1))
    (c : F.Site (j + 1) × Fin 4) : 0 ≤ blockFit X X' c := by apply _root_.YangMills.Construction.BlockAverages.MinimalChain.blockFit_nonneg <;> assumption
private theorem minimalAction_nonneg (a : ℝ) (ha : 0 < a) (S : Finset F.Cell) :
    ∀ (j : ℕ) (W : F.GaugeField j), 0 ≤ minimalAction a S j W
  | 0, U => Finset.sum_nonneg fun p _ => plaquette_term_nonneg _
  | j + 1, V => Real.iInf_nonneg fun W => add_nonneg (minimalAction_nonneg a ha S j W)
      (mul_nonneg ha.le (Finset.sum_nonneg fun c _ => blockFit_nonneg _ _ _))
private theorem bddBelow_energy (a : ℝ) (ha : 0 < a) (S : Finset F.Cell) (j : ℕ) (V : F.GaugeField (j + 1)) :
    BddBelow (Set.range fun W : F.GaugeField j =>
      minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W V c) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨W, rfl⟩
  exact add_nonneg (minimalAction_nonneg a ha S j W)
    (mul_nonneg ha.le (Finset.sum_nonneg fun c _ => blockFit_nonneg _ _ _))
abbrev _root_.YangMills.SharedProofs.p89849 := @bddBelow_energy
private theorem minimalAction_succ_le (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) {J : ℕ} (hF : Compatible F L n k J) (hG : Compatible G L n k J) {j : ℕ}
    (hj : j + 1 ≤ J)
    (ih : ∀ A ∈ fieldSpace L n k j, ∀ (Y : F.GaugeField j) (Y' : G.GaugeField j), Represents F j A Y →
      Represents G j A Y' → minimalAction a (finiteCells F) j Y = minimalAction a (finiteCells G) j Y')
    {B : Edge L n k (j + 1) → ComplexMatrix2} {Y : F.GaugeField (j + 1)} {Y' : G.GaugeField (j + 1)}
    (hR : Represents F (j + 1) B Y) (hR' : Represents G (j + 1) B Y') :
    minimalAction a (finiteCells G) (j + 1) Y' ≤ minimalAction a (finiteCells F) (j + 1) Y := by
  refine le_ciInf fun W => ?_
  obtain ⟨A, hA, hRA⟩ := exists_field_of_frame hC hL hn hF (Nat.le_of_succ_le hj) W
  obtain ⟨W', hW'⟩ := exists_frameField hC hL hn hG (Nat.le_of_succ_le hj) hA
  refine (ciInf_le (bddBelow_energy a ha _ j Y') W').trans_eq ?_
  rw [← ih A hA W W' hRA hW', sum_blockFit_eq hC hP hL hn hF hj hA hRA hR,
    sum_blockFit_eq hC hP hL hn hG hj hA hW' hR']
private theorem minimalAction_eq_of_represents (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) {J : ℕ} (hF : Compatible F L n k J) (hG : Compatible G L n k J) (j : ℕ)
    (hj : j ≤ J) :
    ∀ A ∈ fieldSpace L n k j, ∀ (Y : F.GaugeField j) (Y' : G.GaugeField j), Represents F j A Y →
      Represents G j A Y' → minimalAction a (finiteCells F) j Y = minimalAction a (finiteCells G) j Y' := by
  induction j with
  | zero =>
    intro A hA Y Y' hR hR'
    show BlockAverages.wilsonAction _ Y = BlockAverages.wilsonAction _ Y'
    rw [wilsonAction_of_represents hC hL hn hF hA hR, wilsonAction_of_represents hC hL hn hG hA hR']
  | succ j ih =>
    intro B hB Y Y' hR hR'
    have ih' := ih (Nat.le_of_succ_le hj)
    exact le_antisymm
      (minimalAction_succ_le hC hP hL hn ha hG hF hj (fun A hA Y Y' h h' => (ih' A hA Y' Y h' h).symm) hR' hR)
      (minimalAction_succ_le hC hP hL hn ha hF hG hj ih' hR hR')
private theorem minimizer_transport (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) {j : ℕ} (hF : Compatible F L n k (j + 1)) (hG : Compatible G L n k (j + 1))
    {A : Edge L n k j → ComplexMatrix2} (hA : A ∈ fieldSpace L n k j) {B : Edge L n k (j + 1) → ComplexMatrix2}
    {Z : F.GaugeField j} {Z' : F.GaugeField (j + 1)} {Y : G.GaugeField j} {Y' : G.GaugeField (j + 1)}
    (hZ : Represents F j A Z) (hZ' : Represents F (j + 1) B Z') (hY : Represents G j A Y)
    (hY' : Represents G (j + 1) B Y')
    (hmin : ∀ W, blockEnergy a (finiteCells F) j Z Z' ≤ blockEnergy a (finiteCells F) j W Z')
    (W : G.GaugeField j) :
    blockEnergy a (finiteCells G) j Y Y' ≤ blockEnergy a (finiteCells G) j W Y' := by
  obtain ⟨A', hA', hRW⟩ := exists_field_of_frame hC hL hn hG (Nat.le_succ j) W
  obtain ⟨W', hW'⟩ := exists_frameField hC hL hn hF (Nat.le_succ j) hA'
  have h := hmin W'
  simp only [blockEnergy] at h ⊢
  rw [sum_blockFit_eq hC hP hL hn hF le_rfl hA hZ hZ', sum_blockFit_eq hC hP hL hn hF le_rfl hA' hW' hZ',
    minimalAction_eq_of_represents hC hP hL hn ha hF hG j (Nat.le_succ j) A hA Z Y hZ hY,
    minimalAction_eq_of_represents hC hP hL hn ha hF hG j (Nat.le_succ j) A' hA' W' W hW' hRW] at h
  rw [sum_blockFit_eq hC hP hL hn hG le_rfl hA hY hY', sum_blockFit_eq hC hP hL hn hG le_rfl hA' hRW hY']
  exact h
private def partialAction (a : ℝ) (C : (j : ℕ) → Edge L n k j → ComplexMatrix2) (j : ℕ) : ℝ :=
  Tower.plaquetteAction L n k (C 0) + a * ∑ i ∈ Finset.range j, fitCost (C i) (C (i + 1))
private theorem minimalAction_le_partial (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) {J : ℕ} (hG : Compatible G L n k J) {C : (j : ℕ) → Edge L n k j → ComplexMatrix2}
    {Y : (j : ℕ) → G.GaugeField j} (hCm : ∀ j, j ≤ J → C j ∈ fieldSpace L n k j)
    (hR : ∀ j, j ≤ J → Represents G j (C j) (Y j)) (j : ℕ) (hj : j ≤ J) :
    minimalAction a (finiteCells G) j (Y j) ≤ partialAction a C j := by
  induction j with
  | zero =>
    show BlockAverages.wilsonAction _ _ ≤ Tower.plaquetteAction L n k (C 0) + a * ∑ i ∈ Finset.range 0, _
    rw [wilsonAction_of_represents hC hL hn hG (hCm 0 hj) (hR 0 hj)]
    simp
  | succ j ih =>
    have h1 := ih (Nat.le_of_succ_le hj)
    refine (ciInf_le (bddBelow_energy a ha _ j (Y (j + 1))) (Y j)).trans ?_
    rw [sum_blockFit_eq hC hP hL hn hG hj (hCm j (Nat.le_of_succ_le hj)) (hR j (Nat.le_of_succ_le hj))
      (hR _ hj)]
    simp only [partialAction, Finset.sum_range_succ, mul_add]
    simp only [partialAction] at h1
    linarith
private theorem minimalAction_eq_partial (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) {J : ℕ} (hG : Compatible G L n k J) {C : (j : ℕ) → Edge L n k j → ComplexMatrix2}
    {Y : (j : ℕ) → G.GaugeField j} (hCm : ∀ j, j ≤ J → C j ∈ fieldSpace L n k j)
    (hR : ∀ j, j ≤ J → Represents G j (C j) (Y j))
    (hmin : ∀ j, j < J → ∀ W, blockEnergy a (finiteCells G) j (Y j) (Y (j + 1)) ≤
      blockEnergy a (finiteCells G) j W (Y (j + 1))) (j : ℕ) (hj : j ≤ J) :
    minimalAction a (finiteCells G) j (Y j) = partialAction a C j := by
  induction j with
  | zero =>
    show BlockAverages.wilsonAction _ _ = Tower.plaquetteAction L n k (C 0) + a * ∑ i ∈ Finset.range 0, _
    rw [wilsonAction_of_represents hC hL hn hG (hCm 0 hj) (hR 0 hj)]
    simp
  | succ j ih =>
    have h1 := ih (Nat.le_of_succ_le hj)
    have h2 : minimalAction a (finiteCells G) (j + 1) (Y (j + 1)) =
        blockEnergy a (finiteCells G) j (Y j) (Y (j + 1)) :=
      le_antisymm (ciInf_le (bddBelow_energy a ha _ j (Y (j + 1))) (Y j)) (le_ciInf (hmin j hj))
    rw [h2]
    simp only [blockEnergy]
    rw [sum_blockFit_eq hC hP hL hn hG hj (hCm j (Nat.le_of_succ_le hj)) (hR j (Nat.le_of_succ_le hj))
      (hR _ hj), h1]
    simp only [partialAction, Finset.sum_range_succ, mul_add]
    ring
end MinimalAction
section ChainPoints
variable {L n k : ℕ} {G : BlockFrame}
private theorem levelField_succ_apply (X : ChainPoint L n k) {j : ℕ} (hj : j < k)
    (c : PositiveEdge L n k (j + 1)) :
    levelField X (j + 1) c.1 = X.noise ⟨j, hj⟩ c * normalizedMean (levelField X j) c.1 := by
  rw [levelField, dif_pos hj]
  simp only [fieldOfPositiveValues, dif_pos c.2]
private theorem chainCost_eq (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {J : ℕ} (hG : Compatible G L n k J) (hJ : J = k) {X : ChainPoint L n k} (hX : IsCompactValued X)
    {j : ℕ} (hj : j < k) :
    ∑ᶠ c : PositiveEdge L n k (j + 1),
        (meanRadius (levelField X j) c.1).re * traceDefect (X.noise ⟨j, hj⟩ c) =
      fitCost (levelField X j) (levelField X (j + 1)) := by
  subst hJ
  refine finsum_congr fun c => ?_
  have hA := hX.2 j hj.le
  have hB := hX.2 (j + 1) hj
  obtain ⟨Y, hY⟩ := exists_frameField hC hL hn hG hj.le hA
  obtain ⟨x, μ, hx⟩ := exists_forwardFrom_of_pos c.1 c.2
  obtain ⟨z, rfl⟩ := coordSite_surjective hC hL hn hj x
  have hm := contourMean_of_represents hP hL hn hG hj hA hY z μ
  rw [← hx] at hm
  set m := _root_.YangMills.Construction.BlockAverages.contourAverage Y (siteOfCoords (j + 1) z, μ)
  have hpos := levelField_succ_apply X hj c
  obtain ⟨g, hg⟩ := exists_qmat_of_mem (hB.1 c.1 (Set.mem_univ _))
  by_cases h0 : m = 0
  · exfalso
    have hz : normalizedMean (levelField X j) c.1 = 0 := by
      show (meanRadius (levelField X j) c.1)⁻¹ • contourMean (levelField X j) c.1 = 0
      rw [hm, h0]
      have : qmat 0 = 0 := by
        ext i l
        fin_cases i <;> fin_cases l <;> simp [SoftAverages.quaternionToMatrix]
      rw [this, smul_zero]
    rw [hz, mul_zero, hg] at hpos
    have h3 : qmat (g : ℍ[ℝ]) = qmat 0 := by
      rw [hpos]
      ext i l
      fin_cases i <;> fin_cases l <;> simp [SoftAverages.quaternionToMatrix]
    have h4 := qmat_injective h3
    have h5 := norm_unitQuaternion g
    rw [h4] at h5
    simp at h5
  · have hu := normalizedMean_of_contourMean hm h0
    set v : UnitQuaternion := ⟨‖m‖⁻¹ • m, normalized_mem_unitary h0⟩
    have : levelField X (j + 1) c.1 * (normalizedMean (levelField X j) c.1)⁻¹ = X.noise ⟨j, hj⟩ c := by
      rw [hpos, hu, mul_assoc, qmat_inv, ← qmat_mul, ← Submonoid.coe_mul, mul_inv_cancel]
      show _ * qmat 1 = _
      rw [qmat_one, mul_one]
    rw [this]
private theorem chainAction_eq_partial (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hG : Compatible G L n k k) {X : ChainPoint L n k} (hX : IsCompactValued X) (a : ℝ) :
    chainAction a X = partialAction a (levelField X) k := by
  simp only [chainAction, partialAction]
  rw [← Fin.sum_univ_eq_sum_range (fun i => fitCost (levelField X i) (levelField X (i + 1))) k]
  congr 2
  exact Finset.sum_congr rfl fun i _ => chainCost_eq hC hP hL hn hG rfl hX i.2
private theorem siteCoords_cast {F : BlockFrame} {j m : ℕ} (hper : ∀ i, F.period j i = m)
    (w : Fin 4 → ℤ) (l : Fin 4) :
    ((siteCoords (siteOfCoords j w : F.Site j) l : ℤ) : ZMod m) = (w l : ZMod m) := by
  rw [siteCoords_siteOfCoords, hper l, ZMod.intCast_mod]
private theorem represents_of_representsAtLevel {F : BlockFrame} (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Compatible F L n k J)
    {j m : ℕ} (hj : j ≤ J) (hm : m = 2 * L ^ (n + (k - j))) {A : Edge L n k j → ComplexMatrix2}
    {V : TorusField m} (h : RepresentsAtLevel j A V) :
    Represents F j A (readAtLevel F j V) := by
  intro z μ
  have hper : ∀ i, F.period j i = m := fun i => by rw [hT.period_eq j hj i, hm]
  have e : coordSite (L := L) (n := n) (k := k) j z = levelVertexOfTorusSite j (fun l => ((z l : ZMod m))) := by
    show coordSite j z = coordSite j _
    rw [coordSite_eq_iff_siteOfCoords hC hL hn hT hj]
    rw [siteOfCoords_eq_iff]
    intro l
    rw [hper l]
    exact (dvd_sub_comm).mp (cast_dvd m (z l))
  rw [e, h.2]
  show _ = qmat ((V (fun l => ((siteCoords (siteOfCoords j z : F.Site j) l : ℤ) : ZMod m)) μ :
    UnitQuaternion) : ℍ[ℝ])
  congr 3
  funext l
  rw [siteCoords_cast hper]
end ChainPoints
section Steps
private theorem minimizer_of_step {a ρ : ℝ} {L j m : ℕ} {V : TorusField m}
    (h : ∃ w, IsMinimizingChart a (finiteCells (torusFrame L j m))
      (readAtLevel (torusFrame L j m) (torusFrame L j m).top V) ρ w) :
    ∀ W : (torusFrame L j m).GaugeField j,
    blockEnergy a (finiteCells (torusFrame L j m)) j
        (readAtLevel (torusFrame L j m) j (SlopeCoefficient.minimizerOnFinerTorus a ρ L j m V))
        (readAtLevel (torusFrame L j m) (j + 1) V) ≤
      blockEnergy a (finiteCells (torusFrame L j m)) j W (readAtLevel (torusFrame L j m) (j + 1) V) := by
  set F := torusFrame L j m with hF
  set Vt : F.GaugeField F.top := readAtLevel F F.top V with hVt
  have hper : ∀ i, F.period j i = m * L := fun i => by
    simp [BlockFrame.period, hF, torusFrame, BlockFrame.top]
  have e : readAtLevel F j (SlopeCoefficient.minimizerOnFinerTorus a ρ L j m V) =
      chartedField (minimizingCoordinates a (finiteCells F) Vt ρ) Vt := by
    have e2 : coordsAboveFrame (F := F) true a ρ 0 Vt 0 = minimizingCoordinates a (finiteCells F) Vt ρ := by
      funext x i
      simp [coordsAboveFrame, stepFrame, minimizingBondCoordinate, stepCoordinates, toImaginary]
      exact fun _ => Subtype.ext (by ext <;> simp)
    funext x i
    show fieldAboveFrame (F := F) true a ρ 0 Vt 0
      (siteOfCoords j fun l => ((((siteCoords x l : ℤ) : ZMod (m * L))).cast : ℤ)) i = chartedField _ Vt x i
    have e3 : (siteOfCoords j fun l => ((((siteCoords x l : ℤ) : ZMod (m * L))).cast : ℤ) : F.Site j) = x := by
      conv_rhs => rw [← _root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords x]
      rw [siteOfCoords_eq_iff]
      intro l
      rw [hper l]
      exact cast_dvd _ _
    rw [e3]
    show chartedField (coordsAboveFrame (F := F) true a ρ 0 Vt 0) Vt x i = _
    rw [e2]
  rw [e]
  have hs : IsMinimizingChart a (finiteCells F) Vt ρ (minimizingCoordinates a (finiteCells F) Vt ρ) := by
    unfold minimizingCoordinates
    rw [dif_pos h]
    exact h.choose_spec
  exact fun W => hs.2.2 W
abbrev _root_.YangMills.SharedProofs.p16240 := @minimizer_of_step
end Steps
section Descent
variable {a ρ : ℝ} {L : ℕ}
private theorem torusSideBelow_eq (L : ℕ) : ∀ s N, torusSideBelow L s N = N * L ^ s
  | 0, N => by simp [torusSideBelow]
  | s + 1, N => by
    rw [torusSideBelow, torusSideBelow_eq L s]
    ring
private theorem minimizerBelow_succ (a ρ : ℝ) (L : ℕ) : ∀ (s k N : ℕ) (V : TorusField N),
    (⟨torusSideBelow L (s + 1) N, minimizerBelow a ρ L k (s + 1) N V⟩ : Σ m, TorusField m) =
      ⟨torusSideBelow L s N * L, SlopeCoefficient.minimizerOnFinerTorus a ρ L (k - 1 - s) (torusSideBelow L s N)
        (minimizerBelow a ρ L k s N V)⟩
  | 0, k, N, V => rfl
  | s + 1, k, N, V => by
    have h := minimizerBelow_succ a ρ L s (k - 1) (N * L)
      (SlopeCoefficient.minimizerOnFinerTorus a ρ L (k - 1) N V)
    have e : k - 1 - (s + 1) = k - 1 - 1 - s := by omega
    rw [e]
    exact h
private def chainAt (a ρ : ℝ) (L k N : ℕ) (V : TorusField N) (j : ℕ) : Σ m, TorusField m :=
  ⟨torusSideBelow L (k - j) N, minimizerBelow a ρ L k (k - j) N V⟩
private theorem chainAt_step (k N : ℕ) (V : TorusField N) {j : ℕ} (hj : j < k) :
    chainAt a ρ L k N V j = ⟨(chainAt a ρ L k N V (j + 1)).1 * L,
      SlopeCoefficient.minimizerOnFinerTorus a ρ L j (chainAt a ρ L k N V (j + 1)).1
        (chainAt a ρ L k N V (j + 1)).2⟩ := by
  obtain ⟨s, hs⟩ : ∃ s, k - j = s + 1 := ⟨k - j - 1, by omega⟩
  have h2 : k - (j + 1) = s := by omega
  have h3 : k - 1 - s = j := by omega
  have h := minimizerBelow_succ a ρ L s k N V
  rw [h3] at h
  simp only [chainAt]
  rw [hs, h2]
  exact h
abbrev _root_.YangMills.DeltaSharedProofs.p501514 := @chainAt_step
private theorem tendsto_minimizerBelow (hN : MinimizerNearTrivialField) (ha : 0 < a)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (h0 : 0 < ρ) (h1 : ρ ≤ 1) : ∀ (s k N : ℕ), 2 * L ≤ N →
    Tendsto (minimizerBelow a ρ L k s N) (𝓝 (trivialField N)) (𝓝 (trivialField (torusSideBelow L s N)))
  | 0, k, N, _ => tendsto_id
  | s + 1, k, N, hm => by
    have h := (hN a ha L hL (k - 1) N ρ hm h0 h1).1
    have hL1 : 1 ≤ L := by have := hL.2; omega
    exact (tendsto_minimizerBelow hN ha hL h0 h1 s (k - 1) (N * L)
      (hm.trans (Nat.le_mul_of_pos_right N hL1))).comp h
end Descent
private theorem compatible_torusFrame {L n k t m : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (h : t + 1 ≤ k) (hm : m = 2 * L ^ (n + (k - (t + 1)))) : Compatible (torusFrame L t m) L n k (t + 1) := by
  have hL0 : 0 < L := by have := hL.2; omega
  refine ⟨rfl, le_rfl, h, fun j hj i => ?_, fun i => ?_⟩
  · show m * L ^ (t + 1 - j) = _
    rw [hm, mul_assoc, ← pow_add]
    congr 2
    omega
  · show 0 < m
    rw [hm]
    positivity
section GaugeFunctions
variable {L n k : ℕ} [NeZero L]
private theorem compact_inv_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
private theorem compact_mul_mem {g h : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hh : h ∈ PeriodicLattice.compactGaugeGroup) : g * h ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.mul_mem_of_mem <;> assumption
private theorem isUnit_det_of_mem_compact {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit g.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
private theorem fieldOfPositiveValues_of_pos {j : ℕ} (w : PositiveEdge L n k j → ComplexMatrix2)
    {b : Edge L n k j} (h : b.IsPositivelyOriented) :
    fieldOfPositiveValues w b = w ⟨b, h⟩ := by
  simp [fieldOfPositiveValues, h]
private theorem levelField_succ (X : ChainPoint L n k) {j : ℕ} (h : j < k) :
    levelField X (j + 1) =
      fieldOfPositiveValues fun c => X.noise ⟨j, h⟩ c * normalizedMean (levelField X j) c.1 := by
  simp [levelField, h]
private theorem levelField_succ_of_pos (X : ChainPoint L n k) {j : ℕ} (h : j < k) {b : Edge L n k (j + 1)}
    (hb : b.IsPositivelyOriented) :
    levelField X (j + 1) b = X.noise ⟨j, h⟩ ⟨b, hb⟩ * normalizedMean (levelField X j) b := by
  rw [levelField_succ X h, fieldOfPositiveValues_of_pos _ hb]
private theorem coe_toSublattice {m : ℕ} {i i' : ℤ} (h : i ≤ i') (y : PeriodicLattice.Site L m i) :
    ((y.toSublattice i' : PeriodicLattice.Site L m i') : PeriodicLattice.FourTorus L m) = y := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.coe_toSublattice <;> assumption
private theorem levelDepth_anti {i j : ℕ} (h : i ≤ j) :
    PeriodicLattice.levelDepth k j ≤ PeriodicLattice.levelDepth k i := by apply _root_.YangMills.Construction.PeriodicLattice.EquivarianceProof.levelDepth_anti <;> assumption
private theorem restrictVertexFunction_through (v : Vertex L n k 0 → ComplexMatrix2) {i j : ℕ} (h : i ≤ j)
    (y : Vertex L n k j) :
    restrictVertexFunction i v (y.toSublattice (PeriodicLattice.levelDepth k i)) = restrictVertexFunction j v y := by
  simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap]
  congr 1
  refine Subtype.ext ?_
  have h1 : PeriodicLattice.levelDepth k j ≤ PeriodicLattice.levelDepth k i := levelDepth_anti h
  have h2 : PeriodicLattice.levelDepth k i ≤ PeriodicLattice.levelDepth k 0 := levelDepth_anti (Nat.zero_le _)
  have e1 := coe_toSublattice h2 (y.toSublattice (PeriodicLattice.levelDepth k i))
  have e2 := coe_toSublattice h1 y
  have e3 := coe_toSublattice (h1.trans h2) y
  exact (e1.trans e2).trans e3.symm
variable (hK : ContourMeanGaugeCovariant) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hn : 0 < n)
include hK hL hn in
private theorem levelField_gaugeTransformPoint {X' : ChainPoint L n k} (hX' : IsCompactValued X')
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    ∀ j, j ≤ k → levelField (gaugeTransformPoint v X') j =
      PeriodicLattice.gaugeTransform (restrictVertexFunction j v) (levelField X' j) := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.levelField_gaugeTransformPoint <;> assumption
include hK hL hn in
private theorem chainAction_gaugeTransformPoint
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (a : ℝ) {X' : ChainPoint L n k} (hX' : IsCompactValued X') {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    chainAction a (gaugeTransformPoint v X') = chainAction a X' := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.chainAction_gaugeTransformPoint <;> assumption
private theorem gaugeTransform_mem_fieldSpace {j : ℕ} {w : Vertex L n k j → ComplexMatrix2}
    {V : Edge L n k j → ComplexMatrix2}
    (hw : ∀ x, w x ∈ PeriodicLattice.compactGaugeGroup) (hV : V ∈ fieldSpace L n k j) :
    PeriodicLattice.gaugeTransform w V ∈ fieldSpace L n k j := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · exact compact_mul_mem (compact_mul_mem (hw _) (hV.1 b (Set.mem_univ b))) (compact_inv_mem (hw _))
  · simp only [PeriodicLattice.gaugeTransform]
    rw [hV.2 b (Set.mem_univ b), Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_compact (hw _))]
    simp only [PeriodicLattice.Bond.opposite, mul_assoc]
private theorem isCompactValued_gaugeTransformPoint (hK : ContourMeanGaugeCovariant)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {X : ChainPoint L n k}
    (hX : IsCompactValued X) {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    IsCompactValued (gaugeTransformPoint v X) := by
  refine ⟨fun i c => ?_, fun j hj => ?_⟩
  · exact compact_mul_mem (compact_mul_mem (hv _) (hX.1 i c)) (compact_inv_mem (hv _))
  · rw [levelField_gaugeTransformPoint hK hL hn hX hv j hj]
    exact gaugeTransform_mem_fieldSpace (fun x => hv _) (hX.2 j hj)
abbrev _root_.YangMills.SharedProofs.p17448 := @isCompactValued_gaugeTransformPoint
private theorem cancel_gauge {g h A : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hh : h ∈ PeriodicLattice.compactGaugeGroup) : g⁻¹ * (g * A * h⁻¹) * (h⁻¹)⁻¹ = A := by
  rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_compact hh)]
  calc g⁻¹ * (g * A * h⁻¹) * h = (g⁻¹ * g) * A * (h⁻¹ * h) := by simp only [mul_assoc]
    _ = A := by
      rw [Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_compact hg),
        Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_compact hh), one_mul, mul_one]
private theorem gaugeTransformPoint_inv {X : ChainPoint L n k} {v : Vertex L n k 0 → ComplexMatrix2}
    (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) :
    gaugeTransformPoint (fun x => (v x)⁻¹) (gaugeTransformPoint v X) = X := by
  obtain ⟨U, N⟩ := X
  simp only [gaugeTransformPoint]
  congr 1
  · funext b
    exact cancel_gauge (hv _) (hv _)
  · funext i c
    exact cancel_gauge (hv _) (hv _)
abbrev _root_.YangMills.SharedProofs.p6932 := @gaugeTransformPoint_inv
private theorem gaugeTransformPoint_comp (u v : Vertex L n k 0 → ComplexMatrix2) (X : ChainPoint L n k) :
    gaugeTransformPoint u (gaugeTransformPoint v X) = gaugeTransformPoint (fun x => u x * v x) X := by
  obtain ⟨U, N⟩ := X
  simp only [gaugeTransformPoint]
  congr 1
  · funext b
    show u b.source * (v b.source * U b * (v b.target)⁻¹) * (u b.target)⁻¹ =
      u b.source * v b.source * U b * (u b.target * v b.target)⁻¹
    rw [Matrix.mul_inv_rev]
    simp only [mul_assoc]
  · funext i c
    show restrictVertexFunction (i + 1) u c.1.source *
        (restrictVertexFunction (i + 1) v c.1.source * N i c * (restrictVertexFunction (i + 1) v c.1.source)⁻¹) *
        (restrictVertexFunction (i + 1) u c.1.source)⁻¹ =
      (restrictVertexFunction (i + 1) u c.1.source * restrictVertexFunction (i + 1) v c.1.source) * N i c *
        (restrictVertexFunction (i + 1) u c.1.source * restrictVertexFunction (i + 1) v c.1.source)⁻¹
    rw [Matrix.mul_inv_rev]
    simp only [mul_assoc]
private theorem gaugeTransformPoint_one (X : ChainPoint L n k) : gaugeTransformPoint (fun _ => 1) X = X := by
  obtain ⟨U, N⟩ := X
  simp only [gaugeTransformPoint]
  congr 1
  · funext b
    show 1 * U b * (1 : ComplexMatrix2)⁻¹ = U b
    simp
  · funext i c
    show (1 : ComplexMatrix2) * N i c * (1 : ComplexMatrix2)⁻¹ = N i c
    simp
include hK hL hn in
private theorem gaugeTransformPoint_minimizer
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy)
    {a : ℝ} {W : Edge L n k k → ComplexMatrix2} {X : ChainPoint L n k} (hX : IsMinimizerOver a W X)
    {v : Vertex L n k 0 → ComplexMatrix2} (hv : ∀ x, v x ∈ PeriodicLattice.compactGaugeGroup)
    (h1 : ∀ y : Vertex L n k k, restrictVertexFunction k v y = 1) :
    IsMinimizerOver a W (gaugeTransformPoint v X) := by
  refine ⟨isCompactValued_gaugeTransformPoint hK hL hn hX.compact hv, ?_, fun Y hY hYt => ?_⟩
  · rw [levelField_gaugeTransformPoint hK hL hn hX.compact hv k le_rfl, hX.top_eq]
    funext b
    simp [PeriodicLattice.gaugeTransform, h1]
  · rw [chainAction_gaugeTransformPoint hK hL hn hg a hX.compact hv]
    exact hX.le Y hY hYt
private theorem exists_extension {j : ℕ} (hj : j ≤ k) (w : Vertex L n k j → ComplexMatrix2)
    (hw : ∀ x, w x ∈ PeriodicLattice.compactGaugeGroup) :
    ∃ v : Vertex L n k 0 → ComplexMatrix2, (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) ∧
      restrictVertexFunction j v = w := by
  have h0 : PeriodicLattice.levelDepth k j ≤ PeriodicLattice.levelDepth k 0 := levelDepth_anti (Nat.zero_le _)
  let f : Vertex L n k j → Vertex L n k 0 := fun y => y.toSublattice (PeriodicLattice.levelDepth k 0)
  have hinj : Function.Injective f := by
    intro x y h
    refine Subtype.ext ?_
    have e1 := coe_toSublattice h0 x
    have e2 := coe_toSublattice h0 y
    rw [← e1, ← e2]
    exact congrArg Subtype.val h
  refine ⟨Function.extend f w 1, fun x => ?_, ?_⟩
  · by_cases h : ∃ y, f y = x
    · obtain ⟨y, rfl⟩ := h
      rw [hinj.extend_apply]
      exact hw y
    · rw [Function.extend_apply' _ _ _ h]
      exact one_mem _
  · funext y
    exact hinj.extend_apply _ _ _
private theorem chainPoint_ext {X Y : ChainPoint L n k} (hY : IsCompactValued Y)
    (h : ∀ j, j ≤ k → levelField X j = levelField Y j) : X = Y := by
  have hb : X.fine = Y.fine := h 0 (Nat.zero_le _)
  have hnz : ∀ i c, X.noise i c = Y.noise i c := by
    intro i c
    have e := congrFun (h (i + 1) i.2) c.1
    rw [levelField_succ_of_pos X i.2 c.2, levelField_succ_of_pos Y i.2 c.2, h i i.2.le] at e
    have hm : Y.noise i c * normalizedMean (levelField Y i) c.1 ∈ PeriodicLattice.compactGaugeGroup := by
      have h2 := (hY.2 (i + 1) i.2).1 c.1 (Set.mem_univ _)
      rwa [levelField_succ_of_pos Y i.2 c.2] at h2
    have hA : normalizedMean (levelField Y i) c.1 ∈ PeriodicLattice.compactGaugeGroup := by
      have h3 := compact_mul_mem (compact_inv_mem (hY.1 i c)) hm
      rwa [← mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_compact (hY.1 i c)), one_mul] at h3
    have hu : normalizedMean (levelField Y i) c.1 * (normalizedMean (levelField Y i) c.1)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_compact hA)
    calc X.noise i c = X.noise i c * normalizedMean (levelField Y i) c.1 *
          (normalizedMean (levelField Y i) c.1)⁻¹ := by rw [mul_assoc, hu, mul_one]
      _ = Y.noise i c * normalizedMean (levelField Y i) c.1 *
          (normalizedMean (levelField Y i) c.1)⁻¹ := by
        have e' : X.noise i c * normalizedMean (levelField Y i) c.1 =
            Y.noise i c * normalizedMean (levelField Y i) c.1 := e
        rw [e']
      _ = Y.noise i c := by rw [mul_assoc, hu, mul_one]
  obtain ⟨U, N⟩ := X
  obtain ⟨U', N'⟩ := Y
  simp only at hb hnz
  subst hb
  congr 1
  funext i c
  exact hnz i c
end GaugeFunctions
section CoarseLevels
variable {L n k : ℕ} [NeZero L]
private theorem qmat_cancel (g h s : UnitQuaternion) :
    (qmat ((g : UnitQuaternion) : ℍ[ℝ]))⁻¹ * qmat (((g * s * h⁻¹ : UnitQuaternion)) : ℍ[ℝ]) *
        ((qmat ((h : UnitQuaternion) : ℍ[ℝ]))⁻¹)⁻¹ =
      qmat ((s : UnitQuaternion) : ℍ[ℝ]) := by
  rw [specialUnitary_inv_inv (qmat_mem h), qmat_inv, ← qmat_mul, ← qmat_mul, ← Submonoid.coe_mul,
    ← Submonoid.coe_mul]
  have e : g⁻¹ * (g * s * h⁻¹) * h = s := by group
  rw [e]
private theorem coe_coordSite (j : ℕ) (z : Fin 4 → ℤ) (ν : Fin 4) :
    ((coordSite (L := L) (n := n) (k := k) j z : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j)) :
        PeriodicLattice.FourTorus L n) ν =
      (((z ν : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j) : ℝ) :
        AddCircle (PeriodicLattice.torusSide L n)) := by
  have h1 : ((coordSite (L := L) (n := n) (k := k) j z :
      PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j)) : PeriodicLattice.FourTorus L n) =
      ∑ μ, z μ • PeriodicLattice.pointOnAxis L n μ (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j)) := by
    show (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j)).subtype (coordSite j z) = _
    simp only [coordSite, PeriodicLattice.offsetSite, zero_add]
    rw [map_sum]
    exact Finset.sum_congr rfl fun μ _ => map_zsmul _ _ _
  rw [h1, Finset.sum_apply, Finset.sum_eq_single ν]
  · simp only [Pi.smul_apply, PeriodicLattice.pointOnAxis, Pi.single_eq_same]
    rw [← zsmul_eq_mul]
    exact (QuotientAddGroup.mk_zsmul _ _ _).symm
  · intro b _ hb
    simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hb.symm]
  · simp
private theorem meshSize_succ (hL : 0 < L) (j : ℕ) :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k (j + 1)) =
      L * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold PeriodicLattice.meshSize
  have e : -PeriodicLattice.levelDepth k (j + 1) = -PeriodicLattice.levelDepth k j + 1 := by
    simp only [PeriodicLattice.levelDepth]; push_cast; ring
  rw [e, zpow_add₀ hL', zpow_one]
  ring
private theorem coordSite_toSublattice (hL : 0 < L) (j : ℕ) (w : Fin 4 → ℤ) :
    (coordSite (L := L) (n := n) (k := k) (j + 1) w).toSublattice (PeriodicLattice.levelDepth k j) =
      coordSite j (fun ν => (L : ℤ) * w ν) := by
  have hc : ((coordSite (L := L) (n := n) (k := k) j (fun ν => (L : ℤ) * w ν) :
        PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j)) : PeriodicLattice.FourTorus L n) =
      (coordSite (L := L) (n := n) (k := k) (j + 1) w :
        PeriodicLattice.Site L n (PeriodicLattice.levelDepth k (j + 1))) := by
    funext ν
    rw [coe_coordSite, coe_coordSite, meshSize_succ hL]
    congr 1
    push_cast
    ring
  have hs : (((coordSite (L := L) (n := n) (k := k) (j + 1) w).toSublattice (PeriodicLattice.levelDepth k j) :
        PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j)) : PeriodicLattice.FourTorus L n) =
      (coordSite (L := L) (n := n) (k := k) (j + 1) w :
        PeriodicLattice.Site L n (PeriodicLattice.levelDepth k (j + 1))) :=
    coe_toSublattice (levelDepth_anti (Nat.le_succ j)) _
  exact Subtype.ext (hs.trans hc.symm)
private theorem exists_gauge_of_represents (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j m : ℕ} (hj : j < k)
    (hT : Compatible (torusFrame L j m) L n k (j + 1))
    {A A₀ : Edge L n k j → ComplexMatrix2} (hA : A ∈ fieldSpace L n k j)
    (hA₀ : A₀ ∈ fieldSpace L n k j)
    {γ : (torusFrame L j m).Site j → UnitQuaternion} {S : (torusFrame L j m).GaugeField j}
    (h1 : ∀ z : (torusFrame L j m).Cell, γ (cellCentre j z) = 1)
    (hR : Represents (torusFrame L j m) j A (BlockAverages.gaugeTransform γ S))
    (hR₀ : Represents (torusFrame L j m) j A₀ S) :
    ∃ v : Vertex L n k 0 → ComplexMatrix2, (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) ∧
      (∀ i, j + 1 ≤ i → ∀ y : Vertex L n k i, restrictVertexFunction i v y = 1) ∧
      PeriodicLattice.gaugeTransform (restrictVertexFunction j v) A = A₀ := by
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hsurj : ∀ x : Vertex L n k j, ∃ z, x = coordSite j z := coordSite_surjective hC hL hn hj.le
  choose zc hzc using hsurj
  let w : Vertex L n k j → ComplexMatrix2 := fun x => (qmat ((γ (siteOfCoords j (zc x)) : UnitQuaternion) : ℍ[ℝ]))⁻¹
  have hw : ∀ z, w (coordSite j z) = (qmat ((γ (siteOfCoords j z) : UnitQuaternion) : ℍ[ℝ]))⁻¹ := by
    intro z
    have e : (siteOfCoords j (zc (coordSite j z)) : (torusFrame L j m).Site j) = siteOfCoords j z :=
      (coordSite_eq_iff_siteOfCoords hC hL hn hT (Nat.le_succ j) _ _).1 (hzc _).symm
    show (qmat ((γ (siteOfCoords j (zc (coordSite j z))) : UnitQuaternion) : ℍ[ℝ]))⁻¹ = _
    rw [e]
  have hwr : ∀ x, w x ∈ PeriodicLattice.compactGaugeGroup := fun x => qmat_inv_mem
  obtain ⟨v, hv, hr⟩ := exists_extension hj.le w hwr
  refine ⟨v, hv, fun i hi y => ?_, ?_⟩
  · have e1 : restrictVertexFunction i v y =
        restrictVertexFunction j v ((y.toSublattice (PeriodicLattice.levelDepth k (j + 1))).toSublattice
          (PeriodicLattice.levelDepth k j)) := by
      rw [restrictVertexFunction_through v (Nat.le_succ j), restrictVertexFunction_through v hi]
    obtain ⟨u, hu⟩ := coordSite_surjective hC hL hn (Nat.succ_le_of_lt hj)
      (y.toSublattice (PeriodicLattice.levelDepth k (j + 1)))
    rw [e1, hu, coordSite_toSublattice hL0, hr, hw]
    let c : (torusFrame L j m).Cell := siteOfCoords (torusFrame L j m).top u
    have e3 : (siteOfCoords j (fun ν => (L : ℤ) * u ν) : (torusFrame L j m).Site j) = cellCentre j c := by
      show (siteOfCoords j _ : (torusFrame L j m).Site j) = siteOfCoords j _
      rw [siteOfCoords_eq_iff]
      intro l
      have hper : (torusFrame L j m).period j l = m * L := by
        simp [BlockFrame.period, torusFrame, BlockFrame.top]
      have hper1 : (torusFrame L j m).period (torusFrame L j m).top l = m := by
        simp [BlockFrame.period, torusFrame, BlockFrame.top]
      have hc : siteCoords c l = u l % (m : ℤ) := by
        have h2 := siteCoords_siteOfCoords (F := torusFrame L j m) (j := (torusFrame L j m).top) u l
        rw [hper1] at h2
        exact h2
      have hexp : (torusFrame L j m).top - j = 1 := by simp [BlockFrame.top, torusFrame]
      have hdiv := Int.emod_add_mul_ediv (u l) (m : ℤ)
      have hLe : (torusFrame L j m).blockSide = L := rfl
      rw [hexp, pow_one, hper, hc, hLe]
      refine ⟨-(u l / (m : ℤ)), ?_⟩
      push_cast
      linear_combination (L : ℤ) * hdiv
    rw [e3, h1 c]
    show (qmat 1)⁻¹ = 1
    rw [qmat_one]
    simp
  · refine field_ext_of_forward hC hL hn hj.le (gaugeTransform_mem_fieldSpace (fun x => hv _) hA) hA₀
      fun z μ => ?_
    have htarget : (PeriodicLattice.Bond.forwardFrom (coordSite (L := L) (n := n) (k := k) j z) μ).target =
        coordSite j (z + Pi.single μ 1) := by
      rw [coordSite_add, ← unitStep_eq_coordSite]
      rfl
    have hnext : (siteOfCoords j z + BlockAverages.unitStep j μ : (torusFrame L j m).Site j) =
        siteOfCoords j (z + Pi.single μ 1) := by
      funext l
      simp [siteOfCoords, BlockAverages.unitStep]
    show restrictVertexFunction j v (coordSite j z) * A (PeriodicLattice.Bond.forwardFrom (coordSite j z) μ) *
        (restrictVertexFunction j v (PeriodicLattice.Bond.forwardFrom (coordSite j z) μ).target)⁻¹ = _
    rw [htarget, hr, hw, hw, hR z μ, hR₀ z μ]
    simp only [BlockAverages.gaugeTransform]
    rw [hnext]
    exact qmat_cancel _ _ _
end CoarseLevels
section Orbit
variable {L n k : ℕ} {G : BlockFrame}
private theorem step_minimal_of_minimizer (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) (hG : Compatible G L n k k) {Y : ChainPoint L n k} (hY : IsCompactValued Y)
    {Z : (j : ℕ) → G.GaugeField j} (hR : ∀ j, j ≤ k → Represents G j (levelField Y j) (Z j))
    (hle : chainAction a Y ≤ minimalAction a (finiteCells G) k (Z k)) {j : ℕ} (hj : j < k)
    (W : G.GaugeField j) :
    blockEnergy a (finiteCells G) j (Z j) (Z (j + 1)) ≤ blockEnergy a (finiteCells G) j W (Z (j + 1)) := by
  have hcfg : ∀ i, i ≤ k → levelField Y i ∈ fieldSpace L n k i := fun i hi => hY.2 i hi
  have hen : ∀ i, i < k → blockEnergy a (finiteCells G) i (Z i) (Z (i + 1)) =
      minimalAction a (finiteCells G) i (Z i) + a * fitCost (levelField Y i) (levelField Y (i + 1)) := by
    intro i hi
    simp only [blockEnergy]
    rw [sum_blockFit_eq hC hP hL hn hG hi (hcfg i hi.le) (hR i hi.le) (hR _ hi)]
  have hdown : ∀ d, d ≤ k → partialAction a (levelField Y) (k - d) ≤
      minimalAction a (finiteCells G) (k - d) (Z (k - d)) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, ← chainAction_eq_partial hC hP hL hn hG hY a]
      exact hle
    | succ d ih =>
      intro hd
      have h1 := ih (Nat.le_of_succ_le hd)
      obtain ⟨i, hi⟩ : ∃ i, k - (d + 1) = i := ⟨_, rfl⟩
      have hi1 : k - d = i + 1 := by omega
      rw [hi]
      rw [hi1] at h1
      have hik : i < k := by omega
      have h2 : minimalAction a (finiteCells G) (i + 1) (Z (i + 1)) ≤
          blockEnergy a (finiteCells G) i (Z i) (Z (i + 1)) :=
        ciInf_le (bddBelow_energy a ha _ i (Z (i + 1))) (Z i)
      rw [hen i hik] at h2
      simp only [partialAction, Finset.sum_range_succ, mul_add] at h1 ⊢
      linarith
  have h1 := hdown (k - (j + 1)) (by omega)
  have e : k - (k - (j + 1)) = j + 1 := by omega
  rw [e] at h1
  have h2 := minimalAction_le_partial hC hP hL hn ha hG hcfg hR j hj.le
  have h3 : minimalAction a (finiteCells G) (j + 1) (Z (j + 1)) ≤
      blockEnergy a (finiteCells G) j W (Z (j + 1)) := ciInf_le (bddBelow_energy a ha _ j (Z (j + 1))) W
  rw [hen j hj]
  simp only [partialAction, Finset.sum_range_succ, mul_add] at h1 h2 ⊢
  linarith
private def StepNear (a ρ : ℝ) (L j m : ℕ) (V : TorusField m) : Prop :=
  (∃ w, IsMinimizingChart a (finiteCells (torusFrame L j m))
    (readAtLevel (torusFrame L j m) (torusFrame L j m).top V) ρ w) ∧
  ∀ W' : (torusFrame L j m).GaugeField (torusFrame L j m).depth,
    (∀ W'', blockEnergy a (finiteCells (torusFrame L j m)) (torusFrame L j m).depth W'
        (readAtLevel (torusFrame L j m) (torusFrame L j m).top V) ≤
      blockEnergy a (finiteCells (torusFrame L j m)) (torusFrame L j m).depth W''
        (readAtLevel (torusFrame L j m) (torusFrame L j m).top V)) →
    ∃ γ : (torusFrame L j m).Site (torusFrame L j m).depth → UnitQuaternion,
      (∀ z : (torusFrame L j m).Cell, γ (cellCentre _ z) = 1) ∧
      W' = BlockAverages.gaugeTransform γ (fieldAboveFrame (F := torusFrame L j m) true a ρ 0
        (readAtLevel (torusFrame L j m) (torusFrame L j m).top V) 0)
private theorem eventually_stepNear {a ρ : ℝ} {L : ℕ} (hN : MinimizerNearTrivialField) (ha : 0 < a)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (h0 : 0 < ρ) (h1 : ρ ≤ 1) (t M : ℕ) (hM : 2 * L ≤ M) :
    ∀ᶠ V in 𝓝 (trivialField M), StepNear a ρ L t M V :=
  (hN a ha L hL t M ρ hM h0 h1).2.mono fun V h => ⟨h.1, h.2.1⟩
private theorem readAtLevel_minimizerOnFinerTorus {a ρ : ℝ} {L j m : ℕ} (V : TorusField m) :
    readAtLevel (torusFrame L j m) j (SlopeCoefficient.minimizerOnFinerTorus a ρ L j m V) =
      fieldAboveFrame (F := torusFrame L j m) true a ρ 0
        (readAtLevel (torusFrame L j m) (torusFrame L j m).top V) 0 := by
  have hper : ∀ i, (torusFrame L j m).period j i = m * L := fun i => by
    simp [BlockFrame.period, torusFrame, BlockFrame.top]
  funext x i
  show fieldAboveFrame (F := torusFrame L j m) true a ρ 0
    (readAtLevel (torusFrame L j m) (torusFrame L j m).top V) 0
    (siteOfCoords j fun l => ((((siteCoords x l : ℤ) : ZMod (m * L))).cast : ℤ)) i = _
  have e3 : (siteOfCoords j fun l => ((((siteCoords x l : ℤ) : ZMod (m * L))).cast : ℤ) :
      (torusFrame L j m).Site j) = x := by
    conv_rhs => rw [← _root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords x]
    rw [siteOfCoords_eq_iff]
    intro l
    rw [hper l]
    exact cast_dvd _ _
  rw [e3]
end Orbit
end MinimizersFormOneGaugeOrbit
open MinimizersFormOneGaugeOrbit in
theorem MinimizersFormOneGaugeOrbit.proof (hN : MinimizerNearTrivialField)
    (hR : MinimizerRepresentsChainNearTrivial) (hP : ContourMeanMatchesFrame)
    (hC : PeriodicLattice.CoordinateDescription)
    (hK : ContourMeanGaugeCovariant)
    (hg : PeriodicLattice.GaugeCovarianceOfHolonomy) :
    MinimizersFormOneGaugeOrbit := by
  intro a ha L hL k n hk hn
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  have hL0 : 0 < L := by have := hL.2; omega
  have : NeZero L := ⟨hL0.ne'⟩
  have h0 : (0 : ℝ) < 1 := one_pos
  have h1 : (1 : ℝ) ≤ 1 := le_rfl
  have hside : ∀ j, j ≤ t + 1 → torusSideBelow L (t + 1 - j) (2 * L ^ n) = 2 * L ^ (n + (t + 1 - j)) := by
    intro j hj
    rw [torusSideBelow_eq, pow_add]
    ring
  have hbig : ∀ e, 0 < e → 2 * L ≤ 2 * L ^ e := fun e he =>
    Nat.mul_le_mul_left 2 (Nat.le_self_pow he.ne' L)
  have hGm : 2 * L ^ n = 2 * L ^ (n + (t + 1 - (t + 1))) := by simp
  have hG : Compatible (torusFrame L t (2 * L ^ n)) L n (t + 1) (t + 1) := compatible_torusFrame hL le_rfl hGm
  set G := torusFrame L t (2 * L ^ n) with hGdef
  have hE1 : ∀ᶠ V in 𝓝 (trivialField (2 * L ^ n)), ∀ j ∈ Finset.range (t + 1),
      StepNear a 1 L j (chainAt a 1 L (t + 1) _ V (j + 1)).1 (chainAt a 1 L (t + 1) _ V (j + 1)).2 := by
    refine (Filter.eventually_all_finset _).2 fun j hj => ?_
    have hj' : j + 1 ≤ t + 1 := Finset.mem_range.mp hj
    exact (tendsto_minimizerBelow hN ha hL h0 h1 (t + 1 - (j + 1)) (t + 1) _ (hbig n hn)).eventually
      (eventually_stepNear hN ha hL h0 h1 j _
        ((hbig (n + (t + 1 - (j + 1))) (by omega)).trans (hside _ hj').ge))
  filter_upwards [hE1, hR a ha L hL (t + 1) n hk hn 1 h0 h1] with V e1 eR W hW X X' hX hX'
  obtain ⟨X₀, hX₀, hread⟩ := eR W hW
  have hzs : ∀ j, j ≤ t + 1 → (chainAt a 1 L (t + 1) _ V j).1 = 2 * L ^ (n + (t + 1 - j)) := hside
  have hrd : ∀ j, j ≤ t + 1 → RepresentsAtLevel j (levelField X₀ j) (chainAt a 1 L (t + 1) _ V j).2 :=
    fun j hj => hread j hj
  let Y : (j : ℕ) → G.GaugeField j := fun j => readAtLevel G j (chainAt a 1 L (t + 1) _ V j).2
  have hCR : ∀ j, j ≤ t + 1 → Represents G j (levelField X₀ j) (Y j) := fun j hj =>
    represents_of_representsAtLevel hC hL hn hG hj (hzs j hj) (hrd j hj)
  have hcfg₀ : ∀ j, j ≤ t + 1 → levelField X₀ j ∈ fieldSpace L n (t + 1) j :=
    fun j hj => hX₀.compact.2 j hj
  have hmin₀ : ∀ j, j < t + 1 → ∀ W', blockEnergy a (finiteCells G) j (Y j) (Y (j + 1)) ≤
      blockEnergy a (finiteCells G) j W' (Y (j + 1)) := by
    intro j hj W'
    have hj1 : j + 1 ≤ t + 1 := hj
    have hF := compatible_torusFrame (n := n) (k := t + 1) (t := j) hL hj1 (hzs (j + 1) hj1)
    have hG' := hG.mono hj1
    have hZ' := represents_of_representsAtLevel hC hL hn hF le_rfl (hzs (j + 1) hj1) (hrd _ hj1)
    have hZ := represents_of_representsAtLevel hC hL hn hF (Nat.le_succ j) (hzs j hj.le) (hrd _ hj.le)
    rw [chainAt_step _ _ _ hj] at hZ
    exact minimizer_transport hC hP hL hn ha hF hG' (hcfg₀ _ hj.le) hZ hZ' (hCR _ hj.le) (hCR _ hj1)
      (minimizer_of_step (e1 j (Finset.mem_range.mpr hj)).1) W'
  have hval : chainAction a X₀ = minimalAction a (finiteCells G) (t + 1) (Y (t + 1)) := by
    rw [chainAction_eq_partial hC hP hL hn hG hX₀.compact a,
      minimalAction_eq_partial hC hP hL hn ha hG hcfg₀ hCR hmin₀ (t + 1) le_rfl]
  have key : ∀ X : ChainPoint L n (t + 1), IsMinimizerOver a W X →
      ∃ v : Vertex L n (t + 1) 0 → ComplexMatrix2, (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) ∧
        (∀ y : Vertex L n (t + 1) (t + 1), restrictVertexFunction (t + 1) v y = 1) ∧
        gaugeTransformPoint v X = X₀ := by
    intro X hX
    have hind : ∀ d, d ≤ t + 1 → ∃ v : Vertex L n (t + 1) 0 → ComplexMatrix2,
        (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) ∧
        (∀ y : Vertex L n (t + 1) (t + 1), restrictVertexFunction (t + 1) v y = 1) ∧
        ∀ l, t + 1 - d ≤ l → l ≤ t + 1 → levelField (gaugeTransformPoint v X) l = levelField X₀ l := by
      intro d
      induction d with
      | zero =>
        intro _
        refine ⟨fun _ => 1, fun _ => one_mem _, fun _ => rfl, fun l h2 h3 => ?_⟩
        have hl : l = t + 1 := by omega
        subst hl
        rw [gaugeTransformPoint_one, hX.top_eq, hX₀.top_eq]
      | succ d ih =>
        intro hd
        obtain ⟨v, hv, hv1, hvl⟩ := ih (Nat.le_of_succ_le hd)
        obtain ⟨j, hjd⟩ : ∃ j, t + 1 - (d + 1) = j := ⟨_, rfl⟩
        have hj : j < t + 1 := by omega
        have hj1 : j + 1 ≤ t + 1 := hj
        have hjj : t + 1 - d = j + 1 := by omega
        rw [hjd]
        rw [hjj] at hvl
        obtain ⟨Q, hQ⟩ : ∃ Q, Q = gaugeTransformPoint v X := ⟨_, rfl⟩
        rw [← hQ] at hvl
        have hQl : IsMinimizerOver a W Q := by
          rw [hQ]
          exact gaugeTransformPoint_minimizer hK hL hn hg hX hv hv1
        have hex : ∀ i, ∃ Zi : G.GaugeField i, i ≤ t + 1 → Represents G i (levelField Q i) Zi := by
          intro i
          by_cases hi : i ≤ t + 1
          · obtain ⟨Zi, hZi⟩ := exists_frameField hC hL hn hG hi (hQl.compact.2 i hi)
            exact ⟨Zi, fun _ => hZi⟩
          · exact ⟨fun _ _ => 1, fun h => absurd h hi⟩
        choose Z hZ using hex
        have hle : chainAction a Q ≤ minimalAction a (finiteCells G) (t + 1) (Z (t + 1)) := by
          have h3 := hQl.le X₀ hX₀.compact hX₀.top_eq
          have hZt : Represents G (t + 1) W (Z (t + 1)) := by
            have h4 := hZ (t + 1) le_rfl
            rwa [hQl.top_eq] at h4
          have hYt : Represents G (t + 1) W (Y (t + 1)) := by
            have h4 := hCR (t + 1) le_rfl
            rwa [hX₀.top_eq] at h4
          rw [minimalAction_eq_of_represents hC hP hL hn ha hG hG (t + 1) le_rfl W hW.1 (Z (t + 1)) (Y (t + 1))
            hZt hYt, ← hval]
          exact h3
        have hZmin := fun W' => step_minimal_of_minimizer hC hP hL hn ha hG hQl.compact hZ hle hj W'
        have hF := compatible_torusFrame (n := n) (k := t + 1) (t := j) hL hj1 (hzs (j + 1) hj1)
        have hG' := hG.mono hj1
        have hA : levelField Q j ∈ fieldSpace L n (t + 1) j := hQl.compact.2 j hj.le
        obtain ⟨Yf, hYf⟩ := exists_frameField hC hL hn hF (Nat.le_succ j) hA
        have hsame : levelField Q (j + 1) = levelField X₀ (j + 1) := hvl (j + 1) le_rfl hj1
        have hZ' := represents_of_representsAtLevel hC hL hn hF le_rfl (hzs (j + 1) hj1) (hrd _ hj1)
        rw [← hsame] at hZ'
        have hmF := minimizer_transport hC hP hL hn ha hG' hF hA (hZ j hj.le) (hZ (j + 1) hj1) hYf hZ' hZmin
        obtain ⟨γ, hγ1, hγ⟩ := (e1 j (Finset.mem_range.mpr hj)).2 Yf hmF
        have hS := represents_of_representsAtLevel hC hL hn hF (Nat.le_succ j) (hzs j hj.le) (hrd _ hj.le)
        rw [chainAt_step _ _ _ hj, readAtLevel_minimizerOnFinerTorus] at hS
        rw [hγ] at hYf
        obtain ⟨u, hu, hu1, hu2⟩ := exists_gauge_of_represents hC hL hn hj hF hA (hcfg₀ j hj.le) hγ1 hYf hS
        refine ⟨fun x => u x * v x, fun x => compact_mul_mem (hu x) (hv x), fun y => ?_, fun l hl hl' => ?_⟩
        · show restrictVertexFunction (t + 1) u y * restrictVertexFunction (t + 1) v y = 1
          rw [hu1 _ hj1, hv1, mul_one]
        · rw [← gaugeTransformPoint_comp u v X, ← hQ,
            levelField_gaugeTransformPoint hK hL hn hQl.compact hu l hl']
          rcases Nat.eq_or_lt_of_le hl with rfl | hlt
          · exact hu2
          · have e2 : restrictVertexFunction l u = fun _ => 1 := funext (hu1 l hlt)
            have e3 : PeriodicLattice.gaugeTransform (fun _ => 1) (levelField Q l) = levelField Q l := by
              funext b
              simp [PeriodicLattice.gaugeTransform]
            rw [e2, e3, hvl l hlt hl']
    obtain ⟨v, hv, hv1, hvl⟩ := hind (t + 1) le_rfl
    exact ⟨v, hv, hv1, chainPoint_ext hX₀.compact fun j hj => hvl j (by omega) hj⟩
  obtain ⟨v, hv, hv1, e⟩ := key X hX
  obtain ⟨v', hv', hv1', e'⟩ := key X' hX'
  refine ⟨fun x => (v' x)⁻¹ * v x, fun x => compact_mul_mem (compact_inv_mem (hv' x)) (hv x), fun y => ?_, ?_⟩
  · show (restrictVertexFunction (t + 1) v' y)⁻¹ * restrictVertexFunction (t + 1) v y = 1
    rw [hv1, hv1']
    simp
  · rw [← gaugeTransformPoint_comp (fun x => (v' x)⁻¹) v X, e, ← e', gaugeTransformPoint_inv hv']
end YangMills.Construction.RunningCouplingSlope
end
