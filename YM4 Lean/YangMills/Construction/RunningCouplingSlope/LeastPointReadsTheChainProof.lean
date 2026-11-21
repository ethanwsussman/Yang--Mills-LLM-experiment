import YangMills.Construction.ClusterExpansionOfAStep.UnitQuaternionsAsSpecialUnitaryMatrices
import YangMills.Construction.ColdChainAtEveryLevel.SizesAtAGoodCellProof
import YangMills.Construction.RunningCouplingSlope.FibreFormIsASumOverTheStepsProof
import YangMills.Construction.RunningCouplingSlope.LeastPointsAreGaugeImagesOfSmallTangentsProof
import YangMills.Construction.SoftAverages.QuaternionsAsMatrices
import YangMills.Construction.RunningCouplingSlope.LeastPointsOverAFieldAreOneOrbitProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.TorusFields (TorusField trivialField readAtLevel torusFrame)
open YangMills.Construction.SlopeCoefficient (minimizerOnFinerTorus)
open YangMills.Construction.Matrices (ComplexMatrix2)
open YangMills.Construction.Conventions (IsAdmissibleBlockingFactor)
namespace MinimizerChainLemmas
section QuaternionMatrices
private abbrev qmat (q : ℍ[ℝ]) : ComplexMatrix2 := SoftAverages.quaternionToMatrix q
private theorem quatMatrix_eq_qmat (q : ℍ[ℝ]) : UnitQuaternions.quatMatrix q = qmat q := by apply _root_.YangMills.DeltaSharedProofs.p500685 <;> assumption
private theorem qmat_one : qmat 1 = 1 := SoftAverages.quaternionToMatrix_one
private theorem qmat_mul (p q : ℍ[ℝ]) : qmat (p * q) = qmat p * qmat q := by apply _root_.YangMills.Construction.SoftAverages.quaternionToMatrix_mul <;> assumption
private theorem qmat_smul (r : ℝ) (q : ℍ[ℝ]) : qmat (r • q) = (r : ℂ) • qmat q := by apply _root_.YangMills.DeltaSharedProofs.p501227 <;> assumption
private theorem qmat_injective {p q : ℍ[ℝ]} (h : qmat p = qmat q) : p = q := by apply _root_.YangMills.DeltaSharedProofs.p501191 <;> assumption
private theorem qmat_mem (g : UnitQuaternion) : qmat (g : ℍ[ℝ]) ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.quaternionToMatrix_mem_specialUnitary <;> assumption
private theorem exists_unit_of_mem {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.specialUnitary) :
    ∃ g : UnitQuaternion, A = qmat (g : ℍ[ℝ]) := by apply _root_.YangMills.DeltaSharedProofs.p500695 <;> assumption
private theorem coe_unit_inv (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
private theorem qmat_inv (g : UnitQuaternion) :
    (qmat (g : ℍ[ℝ]))⁻¹ = qmat ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by apply _root_.YangMills.DeltaSharedProofs.p502200 <;> assumption
private theorem traceDefect_qmat (q : ℍ[ℝ]) : traceDefect (qmat q) = 1 - q.re := by apply _root_.YangMills.DeltaSharedProofs.p500863 <;> assumption
private theorem half_fullTrace_qmat (q : ℍ[ℝ]) : (1 / 2) * (ComplexMatrix2.fullTrace (qmat q)).re = q.re := by apply _root_.YangMills.DeltaSharedProofs.p501762 <;> assumption
private theorem det_qmat (q : ℍ[ℝ]) : Matrix.det (qmat q) = ((Quaternion.normSq q : ℝ) : ℂ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.det_quaternionToMatrix <;> assumption
private theorem sqrt_det_qmat (m : ℍ[ℝ]) : (Matrix.det (qmat m)) ^ (1 / 2 : ℂ) = ((‖m‖ : ℝ) : ℂ) := by apply _root_.YangMills.DeltaSharedProofs.p501669 <;> assumption
private theorem norm_coe_unit (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
end QuaternionMatrices
section LevelCoordinates
variable {L n k : ℕ}
private def vtx (j : ℕ) (z : Fin 4 → ℤ) : Vertex L n k j := PeriodicLattice.offsetSite 0 z
private theorem sublatticeCoords (hC : PeriodicLattice.CoordinateDescription)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) :
    PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k j) :=
  (hC L n hL.1 hL.2 hn).1 _ (by simp only [PeriodicLattice.levelDepth]; omega)
private theorem two_mul_halfPeriod {j : ℕ} (hj : j ≤ k) :
    2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k j) = 2 * L ^ (n + (k - j)) := by apply _root_.YangMills.SharedProofs.p9710 <;> assumption
private theorem vtx_surjective (hC : PeriodicLattice.CoordinateDescription)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) (x : Vertex L n k j) :
    ∃ z, x = vtx j z :=
  (sublatticeCoords hC hL hn hj).2.2.2.1 0 x
private theorem vtx_eq_iff (hC : PeriodicLattice.CoordinateDescription)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) (z w : Fin 4 → ℤ) :
    vtx (L := L) (n := n) (k := k) j z = vtx j w ↔
      ∀ μ, ((2 * L ^ (n + (k - j)) : ℕ) : ℤ) ∣ w μ - z μ := by
  have h := (sublatticeCoords hC hL hn hj).2.2.2.2.1 0 z w
  rw [two_mul_halfPeriod hj] at h
  refine h.trans (forall_congr' fun μ => ?_)
  exact Int.modEq_iff_dvd
private theorem vtx_add (j : ℕ) (z w : Fin 4 → ℤ) :
    vtx (L := L) (n := n) (k := k) j (z + w) = vtx j z + vtx j w := by
  simp [vtx, PeriodicLattice.offsetSite, add_smul, Finset.sum_add_distrib]
private theorem sum_single_smul {A : Type*} [AddCommGroup A] (f : Fin 4 → A) (μ : Fin 4) :
    ∑ ν, (Pi.single μ 1 : Fin 4 → ℤ) ν • f ν = f μ := by apply _root_.YangMills.SharedProofs.p19285 <;> assumption
private theorem unitStep_eq_vtx (j : ℕ) (μ : Fin 4) :
    PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ =
      vtx (L := L) (n := n) (k := k) j (Pi.single μ 1) := by
  simp only [vtx, PeriodicLattice.offsetSite, zero_add]
  rw [sum_single_smul]
private theorem exists_forwardFrom_of_pos {j : ℕ} (b : Edge L n k j) (hb : b.IsPositivelyOriented) :
    ∃ x μ, b = PeriodicLattice.Bond.forwardFrom x μ := by apply _root_.YangMills.SharedProofs.p50830 <;> assumption
private theorem forwardFrom_pos {j : ℕ} (x : Vertex L n k j) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
private theorem forwardFrom_injective (hC : PeriodicLattice.CoordinateDescription)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) {x y : Vertex L n k j}
    {μ ν : Fin 4}
    (h : PeriodicLattice.Bond.forwardFrom x μ = PeriodicLattice.Bond.forwardFrom y ν) : x = y ∧ μ = ν := by apply _root_.YangMills.SharedProofs.p47369 <;> assumption
private theorem pos_or_opposite_pos {j : ℕ} (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem inv_mem_specialUnitary {A : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.specialUnitary) :
    A⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
private theorem fieldOfPositiveValues_mem (hC : PeriodicLattice.CoordinateDescription)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    (w : PositiveEdge L n k j → ComplexMatrix2) (hw : ∀ c, w c ∈ ComplexMatrix2.specialUnitary) :
    fieldOfPositiveValues w ∈ fieldSpace L n k j := by apply _root_.YangMills.SharedProofs.p18687 <;> assumption
private theorem field_ext_of_forward (hC : PeriodicLattice.CoordinateDescription)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    {A B : Edge L n k j → ComplexMatrix2} (hA : A ∈ fieldSpace L n k j) (hB : B ∈ fieldSpace L n k j)
    (h : ∀ z μ, A (PeriodicLattice.Bond.forwardFrom (vtx j z) μ) =
      B (PeriodicLattice.Bond.forwardFrom (vtx j z) μ)) :
    A = B := by
  have hp : ∀ b : Edge L n k j, b.IsPositivelyOriented → A b = B b := by
    intro b hb
    obtain ⟨x, μ, rfl⟩ := exists_forwardFrom_of_pos b hb
    obtain ⟨z, rfl⟩ := vtx_surjective hC hL hn hj x
    exact h z μ
  funext b
  rcases pos_or_opposite_pos b with hb | hb
  · exact hp b hb
  · have h1 := hA.2 b.opposite (Set.mem_univ _)
    have h2 := hB.2 b.opposite (Set.mem_univ _)
    have e : b.opposite.opposite = b := rfl
    rw [e] at h1 h2
    rw [h1, h2, hp _ hb]
end LevelCoordinates
section MatchedFrames
variable {L n k : ℕ} {F : BlockFrame}
private structure Matched (F : BlockFrame) (L n k J : ℕ) : Prop where
  blockSide_eq : F.blockSide = L
  le_top : J ≤ F.top
  le_depth : J ≤ k
  period_eq : ∀ j, j ≤ J → ∀ i, F.period j i = 2 * L ^ (n + (k - j))
  extent_pos : ∀ i, 0 < F.extent i
private def Corresponds (F : BlockFrame) (j : ℕ) (C : Edge L n k j → ComplexMatrix2) (Y : F.GaugeField j) :
    Prop :=
  ∀ (z : Fin 4 → ℤ) (μ : Fin 4),
    C (PeriodicLattice.Bond.forwardFrom (vtx j z) μ) = qmat ((Y (siteOfCoords j z) μ : UnitQuaternion) : ℍ[ℝ])
private theorem vtx_eq_iff_siteOfCoords (hC : PeriodicLattice.CoordinateDescription)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Matched F L n k J) {j : ℕ} (hj : j ≤ J)
    (z w : Fin 4 → ℤ) :
    vtx (L := L) (n := n) (k := k) j z = vtx j w ↔ (siteOfCoords j z : F.Site j) = siteOfCoords j w := by
  rw [vtx_eq_iff hC hL hn (hj.trans hT.le_depth), siteOfCoords_eq_iff]
  refine forall_congr' fun i => ?_
  rw [hT.period_eq j hj i]
private theorem exists_latticeField (hC : PeriodicLattice.CoordinateDescription)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Matched F L n k J) {j : ℕ} (hj : j ≤ J)
    (Y : F.GaugeField j) : ∃ C ∈ fieldSpace L n k j, Corresponds F j C Y := by
  have hjk := hj.trans hT.le_depth
  have hch : ∀ c : PositiveEdge L n k j, ∃ (z : Fin 4 → ℤ) (μ : Fin 4),
      c.1 = PeriodicLattice.Bond.forwardFrom (vtx j z) μ := by
    intro c
    obtain ⟨x, μ, h⟩ := exists_forwardFrom_of_pos c.1 c.2
    obtain ⟨z, rfl⟩ := vtx_surjective hC hL hn hjk x
    exact ⟨z, μ, h⟩
  choose zc μc hc using hch
  refine ⟨fieldOfPositiveValues fun c => qmat ((Y (siteOfCoords j (zc c)) (μc c) : UnitQuaternion) : ℍ[ℝ]),
    fieldOfPositiveValues_mem hC hL hn hjk _ fun c => qmat_mem _, ?_⟩
  intro z μ
  have hp := forwardFrom_pos (vtx (L := L) (n := n) (k := k) j z) μ
  simp only [fieldOfPositiveValues, dif_pos hp]
  obtain ⟨e1, e2⟩ := forwardFrom_injective hC hL hn hjk (hc ⟨_, hp⟩)
  rw [← e2, ← (vtx_eq_iff_siteOfCoords hC hL hn hT hj _ _).mp e1]
private theorem exists_frameField (hC : PeriodicLattice.CoordinateDescription)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Matched F L n k J) {j : ℕ} (hj : j ≤ J)
    {A : Edge L n k j → ComplexMatrix2} (hA : A ∈ fieldSpace L n k j) :
    ∃ Y : F.GaugeField j, Corresponds F j A Y := by
  have h : ∀ (x : F.Site j) (μ : Fin 4), ∃ g : UnitQuaternion,
      A (PeriodicLattice.Bond.forwardFrom (vtx j (siteCoords x)) μ) = qmat (g : ℍ[ℝ]) :=
    fun x μ => exists_unit_of_mem (hA.1 _ (Set.mem_univ _))
  choose Y hY using h
  refine ⟨Y, fun z μ => ?_⟩
  have e : vtx (L := L) (n := n) (k := k) j z = vtx j (siteCoords (siteOfCoords j z : F.Site j)) :=
    (vtx_eq_iff_siteOfCoords hC hL hn hT hj _ _).mpr (_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords _).symm
  rw [e]
  exact hY _ _
private theorem dvd_sub_cast (P : ℕ) (c : ℤ) : (P : ℤ) ∣ c - (((c : ZMod P)).cast : ℤ) :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (by rw [ZMod.intCast_zmod_cast])
private theorem readAtLevel_recoords {j M : ℕ} (hper : ∀ i, F.period j i = M) (Y : F.GaugeField j) :
    readAtLevel F j
      (fun x i => Y (siteOfCoords j fun l => (((x l : ZMod M)).cast : ℤ)) i : TorusField M) = Y := by apply _root_.YangMills.SharedProofs.p81894 <;> assumption
private theorem contourMean_of_corresponds (hP : ContourMeanMatchesFrame)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Matched F L n k J) {j : ℕ}
    (hj : j + 1 ≤ J)
    {A : Edge L n k j → ComplexMatrix2} (hA : A ∈ fieldSpace L n k j) {Y : F.GaugeField j}
    (hR : Corresponds F j A Y) (z : Fin 4 → ℤ) (μ : Fin 4) :
    contourMean A (PeriodicLattice.Bond.forwardFrom (vtx (j + 1) z) μ) =
      qmat (_root_.YangMills.Construction.BlockAverages.contourAverage Y (siteOfCoords (j + 1) z, μ)) := by
  have hjk : j < k := lt_of_lt_of_le (Nat.lt_of_succ_le hj) hT.le_depth
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
  rw [readAtLevel_recoords hper] at h
  exact h
private theorem normalized_mem_unitary {m : ℍ[ℝ]} (h0 : m ≠ 0) : (‖m‖⁻¹ • m) ∈ unitary ℍ[ℝ] := by apply _root_.YangMills.Construction.BlockAverages.smul_inv_norm_mem_unitary <;> assumption
private theorem meanRadius_eq {j : ℕ} {A : Edge L n k j → ComplexMatrix2} {c : Edge L n k (j + 1)}
    {m : ℍ[ℝ]} (hm : contourMean A c = qmat m) : meanRadius A c = ((‖m‖ : ℝ) : ℂ) := by apply _root_.YangMills.DeltaSharedProofs.p500717 <;> assumption
private theorem normalizedMean_eq {j : ℕ} {A : Edge L n k j → ComplexMatrix2} {c : Edge L n k (j + 1)}
    {m : ℍ[ℝ]} (hm : contourMean A c = qmat m) (h0 : m ≠ 0) :
    normalizedMean A c = qmat ((⟨‖m‖⁻¹ • m, normalized_mem_unitary h0⟩ : UnitQuaternion) : ℍ[ℝ]) := by apply _root_.YangMills.DeltaSharedProofs.p500417 <;> assumption
private theorem cost_summand {j : ℕ} {A : Edge L n k j → ComplexMatrix2} {c : Edge L n k (j + 1)}
    {m : ℍ[ℝ]} (hm : contourMean A c = qmat m) (g : UnitQuaternion) :
    (meanRadius A c).re * traceDefect (qmat (g : ℍ[ℝ]) * (normalizedMean A c)⁻¹) =
      ‖m‖ - (m * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by apply _root_.YangMills.DeltaSharedProofs.p502207 <;> assumption
private theorem sum_eq_finsum {α β : Type*} (s : Finset α) (f : α → ℝ) (g : β → ℝ) (φ : ↥s → β)
    (hφ : Function.Bijective φ) (h : ∀ a : ↥s, f a = g (φ a)) :
    ∑ a ∈ s, f a = ∑ᶠ b, g b := by apply _root_.YangMills.SharedProofs.p64412 <;> assumption
private def fitCost {j : ℕ} (A : Edge L n k j → ComplexMatrix2) (B : Edge L n k (j + 1) → ComplexMatrix2) : ℝ :=
  ∑ᶠ c : PositiveEdge L n k (j + 1),
    (meanRadius A c.1).re * traceDefect (B c.1 * (normalizedMean A c.1)⁻¹)
private theorem mem_innerBonds (hL : IsAdmissibleBlockingFactor L) {J : ℕ} (hT : Matched F L n k J) {j : ℕ}
    (hj : j ≤ J) (b : F.Site j × Fin 4) : b ∈ innerBonds (finiteCells F) j := by
  have hodd : Odd F.blockSide := hT.blockSide_eq ▸ hL.1
  have hs := fun x : F.Site j => mem_allSites hodd hT.extent_pos (hj.trans hT.le_top) x
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨hs _, hs _⟩
private theorem sum_blockFit (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ}
    (hT : Matched F L n k J) {j : ℕ} (hj : j + 1 ≤ J)
    {A : Edge L n k j → ComplexMatrix2} (hA : A ∈ fieldSpace L n k j)
    {B : Edge L n k (j + 1) → ComplexMatrix2}
    {Y : F.GaugeField j} {Y' : F.GaugeField (j + 1)} (hR : Corresponds F j A Y)
    (hR' : Corresponds F (j + 1) B Y') :
    ∑ c ∈ innerBonds (finiteCells F) (j + 1), blockFit Y Y' c = fitCost A B := by
  have hjk := hj.trans hT.le_depth
  refine sum_eq_finsum _ _ _
    (fun p => ⟨PeriodicLattice.Bond.forwardFrom (vtx (j + 1) (siteCoords p.1.1)) p.1.2,
      forwardFrom_pos _ _⟩) ⟨?_, ?_⟩ ?_
  · rintro ⟨⟨x, μ⟩, hp⟩ ⟨⟨y, ν⟩, hq⟩ h
    have h1 := congrArg Subtype.val h
    obtain ⟨e1, e2⟩ := forwardFrom_injective hC hL hn hjk h1
    have e3 := (vtx_eq_iff_siteOfCoords hC hL hn hT hj _ _).mp e1
    rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords, _root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords] at e3
    simp only at e2 e3
    subst e2 e3
    rfl
  · rintro ⟨c, hc⟩
    obtain ⟨x, μ, rfl⟩ := exists_forwardFrom_of_pos c hc
    obtain ⟨z, rfl⟩ := vtx_surjective hC hL hn hjk x
    refine ⟨⟨(siteOfCoords (j + 1) z, μ), mem_innerBonds hL hT hj _⟩, Subtype.ext ?_⟩
    show PeriodicLattice.Bond.forwardFrom
      (vtx (j + 1) (siteCoords (siteOfCoords (j + 1) z : F.Site (j + 1)))) μ = _
    rw [(vtx_eq_iff_siteOfCoords hC hL hn hT hj _ _).mpr (_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords _)]
  · rintro ⟨⟨x, μ⟩, hp⟩
    have h1 := contourMean_of_corresponds hP hL hn hT hj hA hR (siteCoords x) μ
    have h2 := hR' (siteCoords x) μ
    rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords] at h1 h2
    show blockFit Y Y' (x, μ) = _
    simp only
    rw [h2, cost_summand h1]
    rfl
end MatchedFrames
section MinimalActions
variable {L n k : ℕ} {F G : BlockFrame}
private theorem Matched.mono {J J' : ℕ} (hT : Matched F L n k J) (h : J' ≤ J) : Matched F L n k J' :=
  ⟨hT.blockSide_eq, h.trans hT.le_top, h.trans hT.le_depth, fun j hj => hT.period_eq j (hj.trans h),
    hT.extent_pos⟩
private theorem plaquetteHolonomy_eq (Y : F.GaugeField 0) (x : F.Site 0) (μ ν : Fin 4) :
    plaquetteHolonomy Y (x, μ, ν) =
      Y x μ * Y (x + unitStep 0 μ) ν * (Y (x + unitStep 0 ν) μ)⁻¹ * (Y x ν)⁻¹ := by apply _root_.YangMills.Construction.PatchCurls.plaquetteHolonomy_eq <;> assumption
private theorem wilsonAction_eq (hC : PeriodicLattice.CoordinateDescription)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Matched F L n k J)
    {A : Edge L n k 0 → ComplexMatrix2} (hA : A ∈ fieldSpace L n k 0) {Y : F.GaugeField 0}
    (hR : Corresponds F 0 A Y) :
    wilsonAction (finiteCells F) Y = plaquetteAction L n k A := by
  have hodd : Odd F.blockSide := hT.blockSide_eq ▸ hL.1
  have hs := fun x : F.Site 0 => mem_allSites hodd hT.extent_pos (Nat.zero_le _) x
  have hk0 : 0 ≤ k := Nat.zero_le _
  have hj0 : 0 ≤ J := Nat.zero_le _
  have hmem : ∀ q : F.Site 0 × Fin 4 × Fin 4, q.2.1 < q.2.2 → q ∈ innerPlaquettes (finiteCells F) 0 := by
    intro q hq
    simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hs _, hq, fun y _ => hs y⟩
  show ∑ p ∈ innerPlaquettes (finiteCells F) 0, (1 - ((plaquetteHolonomy Y p : UnitQuaternion) : ℍ[ℝ]).re) =
    ∑ᶠ p : Face L n k 0, PeriodicLattice.plaquetteCost A p
  refine sum_eq_finsum _ _ _ (fun q => ⟨vtx 0 (siteCoords q.1.1), q.1.2.1, q.1.2.2,
    (Finset.mem_filter.mp q.2).2.1⟩) ⟨?_, ?_⟩ ?_
  · rintro ⟨⟨x, μ, ν⟩, hp⟩ ⟨⟨y, μ', ν'⟩, hq⟩ h
    have e1 := congrArg PeriodicLattice.Plaquette.origin h
    have e2 := congrArg PeriodicLattice.Plaquette.firstAxis h
    have e3 := congrArg PeriodicLattice.Plaquette.secondAxis h
    have e4 := (vtx_eq_iff_siteOfCoords hC hL hn hT hj0 _ _).mp e1
    rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords, _root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords] at e4
    simp only at e2 e3 e4
    subst e2 e3 e4
    rfl
  · rintro ⟨b, μ, ν, h⟩
    obtain ⟨z, rfl⟩ := vtx_surjective hC hL hn hk0 b
    refine ⟨⟨(siteOfCoords 0 z, μ, ν), hmem _ h⟩, ?_⟩
    refine PeriodicLattice.Plaquette.ext ?_ rfl rfl
    exact (vtx_eq_iff_siteOfCoords hC hL hn hT hj0 _ _).mpr (_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords _)
  · rintro ⟨⟨x, μ, ν⟩, hp⟩
    set z := siteCoords x with hz
    have hx : (siteOfCoords 0 z : F.Site 0) = x := _root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords x
    have hadd : ∀ ρ : Fin 4, (siteOfCoords 0 (z + Pi.single ρ 1) : F.Site 0) = x + unitStep 0 ρ := by
      intro ρ
      rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_add, hx]
      rfl
    have hst : ∀ ρ : Fin 4, vtx (L := L) (n := n) (k := k) 0 z +
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) ρ = vtx 0 (z + Pi.single ρ 1) := by
      intro ρ
      rw [vtx_add, unitStep_eq_vtx]
    have r3 := hA.2 (PeriodicLattice.Bond.forwardFrom
      (vtx 0 z + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) ν) μ) (Set.mem_univ _)
    have r4 := hA.2 (PeriodicLattice.Bond.forwardFrom (vtx 0 z) ν) (Set.mem_univ _)
    show 1 - ((plaquetteHolonomy Y (x, μ, ν) : UnitQuaternion) : ℍ[ℝ]).re =
      1 - (1 / 2) * (ComplexMatrix2.fullTrace (PeriodicLattice.pathHolonomy A
      [PeriodicLattice.Bond.forwardFrom (vtx 0 z) μ,
       PeriodicLattice.Bond.forwardFrom (vtx 0 z + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) μ) ν,
       (PeriodicLattice.Bond.forwardFrom
         (vtx 0 z + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) ν) μ).opposite,
       (PeriodicLattice.Bond.forwardFrom (vtx 0 z) ν).opposite])).re
    have hh : PeriodicLattice.pathHolonomy A
      [PeriodicLattice.Bond.forwardFrom (vtx 0 z) μ,
       PeriodicLattice.Bond.forwardFrom (vtx 0 z + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) μ) ν,
       (PeriodicLattice.Bond.forwardFrom
         (vtx 0 z + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) ν) μ).opposite,
       (PeriodicLattice.Bond.forwardFrom (vtx 0 z) ν).opposite] =
        qmat ((plaquetteHolonomy Y (x, μ, ν) : UnitQuaternion) : ℍ[ℝ]) := by
      simp only [PeriodicLattice.pathHolonomy, List.map, List.prod_cons, List.prod_nil, mul_one]
      rw [r3, r4, hst, hst, hR, hR, hR, hR, hadd, hadd, hx, plaquetteHolonomy_eq, qmat_inv, qmat_inv]
      simp only [Submonoid.coe_mul, qmat_mul, mul_assoc]
    rw [hh, half_fullTrace_qmat]
private theorem bddBelow_step (a : ℝ) (ha : 0 < a) (S : Finset F.Cell) (j : ℕ) (V : F.GaugeField (j + 1)) :
    BddBelow (Set.range fun W : F.GaugeField j =>
      minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W V c) := by apply _root_.YangMills.SharedProofs.p89849 <;> assumption
private theorem minimalAction_step_le (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) {J : ℕ} (hF : Matched F L n k J) (hG : Matched G L n k J) {j : ℕ} (hj : j + 1 ≤ J)
    (ih : ∀ A ∈ fieldSpace L n k j, ∀ (Y : F.GaugeField j) (Y' : G.GaugeField j),
      Corresponds F j A Y → Corresponds G j A Y' →
      minimalAction a (finiteCells F) j Y = minimalAction a (finiteCells G) j Y')
    {B : Edge L n k (j + 1) → ComplexMatrix2} {Y : F.GaugeField (j + 1)} {Y' : G.GaugeField (j + 1)}
    (hR : Corresponds F (j + 1) B Y) (hR' : Corresponds G (j + 1) B Y') :
    minimalAction a (finiteCells G) (j + 1) Y' ≤ minimalAction a (finiteCells F) (j + 1) Y := by
  refine le_ciInf fun W => ?_
  obtain ⟨A, hA, hRA⟩ := exists_latticeField hC hL hn hF (Nat.le_of_succ_le hj) W
  obtain ⟨W', hW'⟩ := exists_frameField hC hL hn hG (Nat.le_of_succ_le hj) hA
  refine (ciInf_le (bddBelow_step a ha _ j Y') W').trans_eq ?_
  rw [← ih A hA W W' hRA hW', sum_blockFit hC hP hL hn hF hj hA hRA hR,
    sum_blockFit hC hP hL hn hG hj hA hW' hR']
private theorem minimalAction_eq (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) {J : ℕ} (hF : Matched F L n k J) (hG : Matched G L n k J) (j : ℕ) (hj : j ≤ J) :
    ∀ A ∈ fieldSpace L n k j, ∀ (Y : F.GaugeField j) (Y' : G.GaugeField j),
      Corresponds F j A Y → Corresponds G j A Y' →
      minimalAction a (finiteCells F) j Y = minimalAction a (finiteCells G) j Y' := by
  induction j with
  | zero =>
    intro A hA Y Y' hR hR'
    show wilsonAction _ Y = wilsonAction _ Y'
    rw [wilsonAction_eq hC hL hn hF hA hR, wilsonAction_eq hC hL hn hG hA hR']
  | succ j ih =>
    intro B hB Y Y' hR hR'
    have ih' := ih (Nat.le_of_succ_le hj)
    exact le_antisymm
      (minimalAction_step_le hC hP hL hn ha hG hF hj (fun A hA Y Y' h h' => (ih' A hA Y' Y h' h).symm) hR' hR)
      (minimalAction_step_le hC hP hL hn ha hF hG hj ih' hR hR')
private theorem isMin_transport (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) {j : ℕ} (hF : Matched F L n k (j + 1)) (hG : Matched G L n k (j + 1))
    {A : Edge L n k j → ComplexMatrix2} (hA : A ∈ fieldSpace L n k j)
    {B : Edge L n k (j + 1) → ComplexMatrix2}
    {Z : F.GaugeField j} {Z' : F.GaugeField (j + 1)} {Y : G.GaugeField j} {Y' : G.GaugeField (j + 1)}
    (hZ : Corresponds F j A Z) (hZ' : Corresponds F (j + 1) B Z') (hY : Corresponds G j A Y)
    (hY' : Corresponds G (j + 1) B Y')
    (hmin : ∀ W, blockEnergy a (finiteCells F) j Z Z' ≤ blockEnergy a (finiteCells F) j W Z')
    (W : G.GaugeField j) :
    blockEnergy a (finiteCells G) j Y Y' ≤ blockEnergy a (finiteCells G) j W Y' := by
  obtain ⟨A', hA', hRW⟩ := exists_latticeField hC hL hn hG (Nat.le_succ j) W
  obtain ⟨W', hW'⟩ := exists_frameField hC hL hn hF (Nat.le_succ j) hA'
  have h := hmin W'
  simp only [blockEnergy] at h ⊢
  rw [sum_blockFit hC hP hL hn hF le_rfl hA hZ hZ', sum_blockFit hC hP hL hn hF le_rfl hA' hW' hZ',
    minimalAction_eq hC hP hL hn ha hF hG j (Nat.le_succ j) A hA Z Y hZ hY,
    minimalAction_eq hC hP hL hn ha hF hG j (Nat.le_succ j) A' hA' W' W hW' hRW] at h
  rw [sum_blockFit hC hP hL hn hG le_rfl hA hY hY', sum_blockFit hC hP hL hn hG le_rfl hA' hRW hY']
  exact h
private def partialAction (a : ℝ) (C : (j : ℕ) → Edge L n k j → ComplexMatrix2) (j : ℕ) : ℝ :=
  plaquetteAction L n k (C 0) + a * ∑ i ∈ Finset.range j, fitCost (C i) (C (i + 1))
private theorem minimalAction_le_partial (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) {J : ℕ} (hG : Matched G L n k J) {C : (j : ℕ) → Edge L n k j → ComplexMatrix2}
    {Y : (j : ℕ) → G.GaugeField j} (hCm : ∀ j, j ≤ J → C j ∈ fieldSpace L n k j)
    (hR : ∀ j, j ≤ J → Corresponds G j (C j) (Y j)) (j : ℕ) (hj : j ≤ J) :
    minimalAction a (finiteCells G) j (Y j) ≤ partialAction a C j := by
  induction j with
  | zero =>
    show wilsonAction _ _ ≤ plaquetteAction L n k (C 0) + a * ∑ i ∈ Finset.range 0, _
    rw [wilsonAction_eq hC hL hn hG (hCm 0 hj) (hR 0 hj)]
    simp
  | succ j ih =>
    have h1 := ih (Nat.le_of_succ_le hj)
    refine (ciInf_le (bddBelow_step a ha _ j (Y (j + 1))) (Y j)).trans ?_
    rw [sum_blockFit hC hP hL hn hG hj (hCm j (Nat.le_of_succ_le hj)) (hR j (Nat.le_of_succ_le hj)) (hR _ hj)]
    simp only [partialAction, Finset.sum_range_succ, mul_add]
    simp only [partialAction] at h1
    linarith
private theorem minimalAction_eq_partial (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) {J : ℕ} (hG : Matched G L n k J) {C : (j : ℕ) → Edge L n k j → ComplexMatrix2}
    {Y : (j : ℕ) → G.GaugeField j} (hCm : ∀ j, j ≤ J → C j ∈ fieldSpace L n k j)
    (hR : ∀ j, j ≤ J → Corresponds G j (C j) (Y j))
    (hmin : ∀ j, j < J → ∀ W, blockEnergy a (finiteCells G) j (Y j) (Y (j + 1)) ≤
      blockEnergy a (finiteCells G) j W (Y (j + 1))) (j : ℕ) (hj : j ≤ J) :
    minimalAction a (finiteCells G) j (Y j) = partialAction a C j := by
  induction j with
  | zero =>
    show wilsonAction _ _ = plaquetteAction L n k (C 0) + a * ∑ i ∈ Finset.range 0, _
    rw [wilsonAction_eq hC hL hn hG (hCm 0 hj) (hR 0 hj)]
    simp
  | succ j ih =>
    have h1 := ih (Nat.le_of_succ_le hj)
    have h2 : minimalAction a (finiteCells G) (j + 1) (Y (j + 1)) =
        blockEnergy a (finiteCells G) j (Y j) (Y (j + 1)) :=
      le_antisymm (ciInf_le (bddBelow_step a ha _ j (Y (j + 1))) (Y j)) (le_ciInf (hmin j hj))
    rw [h2]
    simp only [blockEnergy]
    rw [sum_blockFit hC hP hL hn hG hj (hCm j (Nat.le_of_succ_le hj)) (hR j (Nat.le_of_succ_le hj)) (hR _ hj),
      h1]
    simp only [partialAction, Finset.sum_range_succ, mul_add]
    ring
end MinimalActions
section ChainPoints
variable {L n k : ℕ} {G : BlockFrame}
private theorem levelField_pos (X : ChainPoint L n k) {j : ℕ} (hj : j < k) (c : PositiveEdge L n k (j + 1)) :
    levelField X (j + 1) c.1 = X.noise ⟨j, hj⟩ c * normalizedMean (levelField X j) c.1 := by
  rw [levelField, dif_pos hj]
  simp only [fieldOfPositiveValues, dif_pos c.2]
private theorem cost_chainPoint (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {J : ℕ} (hG : Matched G L n k J) (hJ : J = k) {X : ChainPoint L n k} (hX : IsCompactValued X) {j : ℕ}
    (hj : j < k) :
    ∑ᶠ c : PositiveEdge L n k (j + 1),
        (meanRadius (levelField X j) c.1).re * traceDefect (X.noise ⟨j, hj⟩ c) =
      fitCost (levelField X j) (levelField X (j + 1)) := by
  subst hJ
  refine finsum_congr fun c => ?_
  have hA := hX.2 j hj.le
  have hB := hX.2 (j + 1) hj
  obtain ⟨Y, hY⟩ := exists_frameField hC hL hn hG hj.le hA
  obtain ⟨x, μ, hx⟩ := exists_forwardFrom_of_pos c.1 c.2
  obtain ⟨z, rfl⟩ := vtx_surjective hC hL hn hj x
  have hm := contourMean_of_corresponds hP hL hn hG hj hA hY z μ
  rw [← hx] at hm
  set m := _root_.YangMills.Construction.BlockAverages.contourAverage Y (siteOfCoords (j + 1) z, μ)
  have hpos := levelField_pos X hj c
  obtain ⟨g, hg⟩ := exists_unit_of_mem (hB.1 c.1 (Set.mem_univ _))
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
    have h5 := norm_coe_unit g
    rw [h4] at h5
    simp at h5
  · have hu := normalizedMean_eq hm h0
    set v : UnitQuaternion := ⟨‖m‖⁻¹ • m, normalized_mem_unitary h0⟩
    have : levelField X (j + 1) c.1 * (normalizedMean (levelField X j) c.1)⁻¹ = X.noise ⟨j, hj⟩ c := by
      rw [hpos, hu, mul_assoc, qmat_inv, ← qmat_mul, ← Submonoid.coe_mul, mul_inv_cancel]
      show _ * qmat 1 = _
      rw [qmat_one, mul_one]
    rw [this]
private theorem chainAction_eq (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hG : Matched G L n k k) {X : ChainPoint L n k} (hX : IsCompactValued X) (a : ℝ) :
    chainAction a X = partialAction a (levelField X) k := by
  simp only [chainAction, partialAction]
  rw [← Fin.sum_univ_eq_sum_range (fun i => fitCost (levelField X i) (levelField X (i + 1))) k]
  congr 2
  exact Finset.sum_congr rfl fun i _ => cost_chainPoint hC hP hL hn hG rfl hX i.2
private theorem exists_chainPoint (hC : PeriodicLattice.CoordinateDescription)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {C : (j : ℕ) → Edge L n k j → ComplexMatrix2}
    (hCm : ∀ j, j ≤ k → C j ∈ fieldSpace L n k j)
    (hu : ∀ j, j < k → ∀ c : PositiveEdge L n k (j + 1),
      normalizedMean (C j) c.1 ∈ ComplexMatrix2.specialUnitary) :
    ∃ X : ChainPoint L n k, IsCompactValued X ∧ ∀ j, j ≤ k → levelField X j = C j := by
  let X : ChainPoint L n k := ⟨C 0, fun i c => C (i + 1) c.1 * (normalizedMean (C i) c.1)⁻¹⟩
  have hnoise : ∀ (j : ℕ) (h : j < k) (c : PositiveEdge L n k (j + 1)),
      X.noise ⟨j, h⟩ c ∈ ComplexMatrix2.specialUnitary :=
    fun j h c => mul_mem ((hCm (j + 1) h).1 c.1 (Set.mem_univ _)) (inv_mem_specialUnitary (hu j h c))
  have hs : ∀ j, j ≤ k → levelField X j = C j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hlt : j < k := hj
      rw [levelField, dif_pos hlt, ih hlt.le]
      have hvals : ∀ c : PositiveEdge L n k (j + 1),
          X.noise ⟨j, hlt⟩ c * normalizedMean (C j) c.1 = C (j + 1) c.1 := by
        intro c
        obtain ⟨g, hg⟩ := exists_unit_of_mem (hu j hlt c)
        show C (j + 1) c.1 * (normalizedMean (C j) c.1)⁻¹ * normalizedMean (C j) c.1 = _
        rw [hg, qmat_inv, mul_assoc, ← qmat_mul, ← Submonoid.coe_mul, inv_mul_cancel]
        show _ * qmat 1 = _
        rw [qmat_one, mul_one]
      refine field_ext_of_forward hC hL hn hj (fieldOfPositiveValues_mem hC hL hn hj _ fun c => ?_)
        (hCm _ hj) fun z μ => ?_
      · rw [hvals]
        exact (hCm (j + 1) hj).1 c.1 (Set.mem_univ _)
      · have hp := forwardFrom_pos (vtx (L := L) (n := n) (k := k) (j + 1) z) μ
        simp only [fieldOfPositiveValues, dif_pos hp]
        exact hvals ⟨_, hp⟩
  refine ⟨X, ⟨fun i c => ?_, fun j hj => ?_⟩, hs⟩
  · exact hnoise i.1 i.2 c
  · rw [hs j hj]
    exact hCm j hj
private theorem siteCoords_cast {F : BlockFrame} {j m : ℕ} (hper : ∀ i, F.period j i = m) (w : Fin 4 → ℤ)
    (l : Fin 4) :
    ((siteCoords (siteOfCoords j w : F.Site j) l : ℤ) : ZMod m) = (w l : ZMod m) := by
  rw [siteCoords_siteOfCoords, hper l, ZMod.intCast_mod]
private theorem corresponds_of_represents {F : BlockFrame} (hC : PeriodicLattice.CoordinateDescription)
    (hL : IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Matched F L n k J) {j m : ℕ} (hj : j ≤ J)
    (hm : m = 2 * L ^ (n + (k - j))) {A : Edge L n k j → ComplexMatrix2} {V : TorusField m}
    (h : RepresentsAtLevel j A V) :
    Corresponds F j A (readAtLevel F j V) := by
  intro z μ
  have hper : ∀ i, F.period j i = m := fun i => by rw [hT.period_eq j hj i, hm]
  have e : vtx (L := L) (n := n) (k := k) j z = levelVertexOfTorusSite j (fun l => ((z l : ZMod m))) := by
    show vtx j z = vtx j _
    rw [vtx_eq_iff_siteOfCoords hC hL hn hT hj]
    rw [siteOfCoords_eq_iff]
    intro l
    rw [hper l]
    exact (dvd_sub_comm).mp (dvd_sub_cast m (z l))
  rw [e, h.2]
  show _ = qmat ((V (fun l => ((siteCoords (siteOfCoords j z : F.Site j) l : ℤ) : ZMod m)) μ :
    UnitQuaternion) : ℍ[ℝ])
  congr 3
  funext l
  rw [siteCoords_cast hper]
private theorem represents_of_corresponds {F : BlockFrame} {J : ℕ} (hT : Matched F L n k J) {j m : ℕ}
    (hj : j ≤ J) (hm : m = 2 * L ^ (n + (k - j))) {A : Edge L n k j → ComplexMatrix2} {V : TorusField m}
    (hA : A ∈ fieldSpace L n k j) (h : Corresponds F j A (readAtLevel F j V)) : RepresentsAtLevel j A V := by
  refine ⟨hA, fun zz μ => ?_⟩
  have hper : ∀ i, F.period j i = m := fun i => by rw [hT.period_eq j hj i, hm]
  have h1 := h (fun l => ((zz l).cast : ℤ)) μ
  refine h1.trans ?_
  show qmat ((V (fun l => ((siteCoords (siteOfCoords j _ : F.Site j) l : ℤ) : ZMod m)) μ :
    UnitQuaternion) : ℍ[ℝ]) = _
  congr 3
  funext l
  rw [siteCoords_cast hper]
  exact ZMod.intCast_zmod_cast _
end ChainPoints
section Steps
private theorem step_isMin {a ρ : ℝ} {L j m : ℕ} {V : TorusField m}
    (h : ∃ w, IsMinimizingChart a (finiteCells (torusFrame L j m))
      (readAtLevel (torusFrame L j m) (torusFrame L j m).top V) ρ w) :
    ∀ W : (torusFrame L j m).GaugeField j,
    blockEnergy a (finiteCells (torusFrame L j m)) j
        (readAtLevel (torusFrame L j m) j (minimizerOnFinerTorus a ρ L j m V))
        (readAtLevel (torusFrame L j m) (j + 1) V) ≤
      blockEnergy a (finiteCells (torusFrame L j m)) j W (readAtLevel (torusFrame L j m) (j + 1) V) := by apply _root_.YangMills.SharedProofs.p16240 <;> assumption
end Steps
section FieldsBelow
variable {a ρ : ℝ} {L : ℕ}
private theorem torusSideBelow_eq (L : ℕ) : ∀ s N, torusSideBelow L s N = N * L ^ s
  | 0, N => by simp [torusSideBelow]
  | s + 1, N => by
    rw [torusSideBelow, torusSideBelow_eq L s]
    ring
private theorem minimizerBelow_succ (a ρ : ℝ) (L : ℕ) : ∀ (s k N : ℕ) (V : TorusField N),
    (⟨torusSideBelow L (s + 1) N, minimizerBelow a ρ L k (s + 1) N V⟩ : Σ m, TorusField m) =
      ⟨torusSideBelow L s N * L,
        minimizerOnFinerTorus a ρ L (k - 1 - s) (torusSideBelow L s N) (minimizerBelow a ρ L k s N V)⟩
  | 0, k, N, V => rfl
  | s + 1, k, N, V => by
    have h := minimizerBelow_succ a ρ L s (k - 1) (N * L) (minimizerOnFinerTorus a ρ L (k - 1) N V)
    have e : k - 1 - (s + 1) = k - 1 - 1 - s := by omega
    rw [e]
    exact h
private def levelAt (a ρ : ℝ) (L k N : ℕ) (V : TorusField N) (j : ℕ) : Σ m, TorusField m :=
  ⟨torusSideBelow L (k - j) N, minimizerBelow a ρ L k (k - j) N V⟩
private theorem levelAt_succ (k N : ℕ) (V : TorusField N) {j : ℕ} (hj : j < k) :
    levelAt a ρ L k N V j = ⟨(levelAt a ρ L k N V (j + 1)).1 * L,
      minimizerOnFinerTorus a ρ L j (levelAt a ρ L k N V (j + 1)).1 (levelAt a ρ L k N V (j + 1)).2⟩ := by apply _root_.YangMills.DeltaSharedProofs.p501514 <;> assumption
private theorem levelAt_top (k N : ℕ) (V : TorusField N) : levelAt a ρ L k N V k = ⟨N, V⟩ := by
  simp only [levelAt]
  rw [Nat.sub_self]
  rfl
private theorem tendsto_minimizerBelow (hN : MinimizerNearTrivialField) (ha : 0 < a)
    (hL : IsAdmissibleBlockingFactor L) (h0 : 0 < ρ) (h1 : ρ ≤ 1) : ∀ (s k N : ℕ), 2 * L ≤ N →
    Tendsto (minimizerBelow a ρ L k s N) (𝓝 (trivialField N)) (𝓝 (trivialField (torusSideBelow L s N)))
  | 0, k, N, _ => tendsto_id
  | s + 1, k, N, hm => by
    have h := (hN a ha L hL (k - 1) N ρ hm h0 h1).1
    have hL1 : 1 ≤ L := by have := hL.2; omega
    exact (tendsto_minimizerBelow hN ha hL h0 h1 s (k - 1) (N * L)
      (hm.trans (Nat.le_mul_of_pos_right N hL1))).comp h
private theorem eventually_minimizing (hN : MinimizerNearTrivialField) (ha : 0 < a)
    (hL : IsAdmissibleBlockingFactor L) (h0 : 0 < ρ) (h1 : ρ ≤ 1) (t M : ℕ) (hM : 2 * L ≤ M) :
    ∀ᶠ V in 𝓝 (trivialField M), ∃ w, IsMinimizingChart a (finiteCells (torusFrame L t M))
      (readAtLevel (torusFrame L t M) (torusFrame L t M).top V) ρ w :=
  (hN a ha L hL t M ρ hM h0 h1).2.mono fun V h => h.1
private theorem continuous_pathHolonomy {F : BlockFrame} {j m : ℕ} (x : F.Site j) (l : List PathStep) :
    Continuous fun V : TorusField m => pathHolonomy (readAtLevel F j V) x l := by
  induction l generalizing x with
  | nil => exact continuous_const
  | cons st r ih =>
    have h1 : Continuous fun V : TorusField m => linkValue (readAtLevel F j V) x st := by
      unfold linkValue
      by_cases hs : st.2 = true
      · simp only [hs, if_true, readAtLevel]
        fun_prop
      · simp only [hs, readAtLevel]
        simp only [Bool.false_eq_true, if_false]
        exact (by fun_prop : Continuous fun V : TorusField m => V _ st.1).inv
    exact h1.mul (ih _)
abbrev _root_.YangMills.SharedProofs.p11593 := @continuous_pathHolonomy
private theorem pathHolonomy_one {F : BlockFrame} {j : ℕ} (x : F.Site j) (l : List PathStep) :
    pathHolonomy (fun _ _ => (1 : UnitQuaternion) : F.GaugeField j) x l = 1 := by apply _root_.YangMills.Construction.BlockAverages.LowCostPatch.pathHolonomy_trivialField <;> assumption
abbrev _root_.YangMills.SharedProofs.p3325 := @pathHolonomy_one
private theorem eventually_contourAverage_ne_zero {F : BlockFrame} {j m : ℕ} (hL : 0 < F.blockSide)
    (hs : ∀ i, 0 < F.extent i) :
    ∀ᶠ V in 𝓝 (trivialField m), ∀ c : F.Site (j + 1) × Fin 4, _root_.YangMills.Construction.BlockAverages.contourAverage (readAtLevel F j V) c ≠ 0 := by
  have hfin : Finite (F.Site (j + 1) × Fin 4) := by
    have : ∀ i, Finite (ZMod (F.period (j + 1) i)) := fun i => by
      have : NeZero (F.period (j + 1) i) := ⟨(period_pos hL hs _ i).ne'⟩
      exact inferInstance
    have : Finite (F.Site (j + 1)) := Pi.finite
    exact inferInstance
  refine eventually_all.2 fun c => ?_
  have hcont : Continuous fun V : TorusField m => _root_.YangMills.Construction.BlockAverages.contourAverage (readAtLevel F j V) c := by
    have h1 : ∀ (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), Continuous fun V : TorusField m =>
        ((pathHolonomy (readAtLevel F j V) (refineSite c.1) (bondContour F.blockSide h π c.2) :
          UnitQuaternion) : ℍ[ℝ]) :=
      fun h π => continuous_subtype_val.comp (continuous_pathHolonomy _ _)
    unfold _root_.YangMills.Construction.BlockAverages.contourAverage
    exact Continuous.const_smul (c := (1 / (24 * (F.blockSide : ℝ) ^ 4)))
      (continuous_finsetSum _ fun h _ => continuous_finsetSum _ fun π _ => h1 h π)
  refine hcont.continuousAt.eventually_ne ?_
  have hflat : readAtLevel F j (trivialField m) = fun _ _ => (1 : UnitQuaternion) := rfl
  have hne : (centredCube F.blockSide).Nonempty := by
    refine ⟨0, ?_⟩
    unfold centredCube
    rw [Fintype.mem_piFinset]
    intro i
    simp only [Pi.zero_apply, Finset.mem_Icc]
    have : (0 : ℤ) ≤ ((F.blockSide : ℤ) - 1) / 2 := by
      have : (1 : ℤ) ≤ F.blockSide := by exact_mod_cast hL
      omega
    omega
  have hS : ∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), ((1 : UnitQuaternion) : ℍ[ℝ]) =
      (((centredCube F.blockSide).card : ℝ) * (24 : ℝ)) • (1 : ℍ[ℝ]) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [Nat.factorial]
  simp only [_root_.YangMills.Construction.BlockAverages.contourAverage, hflat, pathHolonomy_one]
  rw [hS, smul_smul]
  refine smul_ne_zero ?_ one_ne_zero
  positivity
end FieldsBelow
private theorem matched_torusFrame {L n k t m : ℕ} (hL : IsAdmissibleBlockingFactor L) (h : t + 1 ≤ k)
    (hm : m = 2 * L ^ (n + (k - (t + 1)))) : Matched (torusFrame L t m) L n k (t + 1) := by
  have hL0 : 0 < L := by have := hL.2; omega
  refine ⟨rfl, le_rfl, h, fun j hj i => ?_, fun i => ?_⟩
  · show m * L ^ (t + 1 - j) = _
    rw [hm, mul_assoc, ← pow_add]
    congr 2
    omega
  · show 0 < m
    rw [hm]
    positivity
end MinimizerChainLemmas
open MinimizerChainLemmas in
theorem minimizerRepresentsChainNearTrivial_holds (hN : MinimizerNearTrivialField)
    (hP : ContourMeanMatchesFrame)
    (hC : PeriodicLattice.CoordinateDescription) :
    MinimizerRepresentsChainNearTrivial := by
  intro a ha L hL k n hk hn ρ h0 h1
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  have hL0 : 0 < L := by have := hL.2; omega
  have hside : ∀ j, j ≤ t + 1 →
      torusSideBelow L (t + 1 - j) (2 * L ^ n) = 2 * L ^ (n + (t + 1 - j)) := by
    intro j hj
    rw [torusSideBelow_eq, pow_add]
    ring
  have hbig : ∀ e, 0 < e → 2 * L ≤ 2 * L ^ e := fun e he =>
    Nat.mul_le_mul_left 2 (Nat.le_self_pow he.ne' L)
  have hGm : 2 * L ^ n = 2 * L ^ (n + (t + 1 - (t + 1))) := by simp
  have hG : Matched (torusFrame L t (2 * L ^ n)) L n (t + 1) (t + 1) := matched_torusFrame hL le_rfl hGm
  set G := torusFrame L t (2 * L ^ n) with hGdef
  have hE1 : ∀ᶠ V in 𝓝 (trivialField (2 * L ^ n)), ∀ j ∈ Finset.range (t + 1),
      ∃ w, IsMinimizingChart a (finiteCells (torusFrame L j (levelAt a ρ L (t + 1) _ V (j + 1)).1))
        (readAtLevel (torusFrame L j (levelAt a ρ L (t + 1) _ V (j + 1)).1)
          (torusFrame L j (levelAt a ρ L (t + 1) _ V (j + 1)).1).top (levelAt a ρ L (t + 1) _ V (j + 1)).2)
        ρ w := by
    refine (Filter.eventually_all_finset _).2 fun j hj => ?_
    have hj' : j + 1 ≤ t + 1 := Finset.mem_range.mp hj
    exact (tendsto_minimizerBelow hN ha hL h0 h1 (t + 1 - (j + 1)) (t + 1) _ (hbig n hn)).eventually
      (eventually_minimizing hN ha hL h0 h1 j _
        ((hbig (n + (t + 1 - (j + 1))) (by omega)).trans (hside _ hj').ge))
  have hE2 : ∀ᶠ V in 𝓝 (trivialField (2 * L ^ n)), ∀ j ∈ Finset.range (t + 1),
      ∀ c : G.Site (j + 1) × Fin 4,
        _root_.YangMills.Construction.BlockAverages.contourAverage (readAtLevel G j (levelAt a ρ L (t + 1) _ V j).2) c ≠ 0 := by
    refine (Filter.eventually_all_finset _).2 fun j hj => ?_
    exact (tendsto_minimizerBelow hN ha hL h0 h1 (t + 1 - j) (t + 1) _ (hbig n hn)).eventually
      (eventually_contourAverage_ne_zero (F := G) hL0 hG.extent_pos)
  filter_upwards [hE1, hE2] with V e1 e2 W hW
  have hzs : ∀ j, j ≤ t + 1 → (levelAt a ρ L (t + 1) _ V j).1 = 2 * L ^ (n + (t + 1 - j)) := hside
  let Y : (j : ℕ) → G.GaugeField j := fun j => readAtLevel G j (levelAt a ρ L (t + 1) _ V j).2
  have hex : ∀ j, ∃ A : Edge L n (t + 1) j → ComplexMatrix2, j ≤ t + 1 →
      A ∈ fieldSpace L n (t + 1) j ∧ Corresponds G j A (Y j) := by
    intro j
    by_cases hj : j ≤ t + 1
    · obtain ⟨A, hA, hR⟩ := exists_latticeField hC hL hn hG hj (Y j)
      exact ⟨A, fun _ => ⟨hA, hR⟩⟩
    · exact ⟨fun _ => 1, fun h => absurd h hj⟩
  choose C hCC using hex
  have hCm := fun j hj => (hCC j hj).1
  have hCR := fun j hj => (hCC j hj).2
  have hmin : ∀ j, j < t + 1 → ∀ W', blockEnergy a (finiteCells G) j (Y j) (Y (j + 1)) ≤
      blockEnergy a (finiteCells G) j W' (Y (j + 1)) := by
    intro j hj W'
    have hj1 : j + 1 ≤ t + 1 := hj
    have hF := matched_torusFrame (n := n) (k := t + 1) (t := j) hL hj1 (hzs (j + 1) hj1)
    have hG' := hG.mono hj1
    have hZ' := corresponds_of_represents hC hL hn hF le_rfl (hzs (j + 1) hj1)
      (represents_of_corresponds hG hj1 (hzs (j + 1) hj1) (hCm _ hj1) (hCR _ hj1))
    have hZ := corresponds_of_represents hC hL hn hF (Nat.le_succ j) (hzs j hj.le)
      (represents_of_corresponds hG hj.le (hzs j hj.le) (hCm _ hj.le) (hCR _ hj.le))
    rw [levelAt_succ _ _ _ hj] at hZ
    exact isMin_transport hC hP hL hn ha hF hG' (hCm _ hj.le) hZ hZ' (hCR _ hj.le) (hCR _ hj1)
      (step_isMin (e1 j (Finset.mem_range.mpr hj))) W'
  have hu : ∀ j, j < t + 1 → ∀ c : PositiveEdge L n (t + 1) (j + 1),
      normalizedMean (C j) c.1 ∈ ComplexMatrix2.specialUnitary := by
    intro j hj c
    obtain ⟨x, μ, hx⟩ := exists_forwardFrom_of_pos c.1 c.2
    obtain ⟨z, rfl⟩ := vtx_surjective hC hL hn hj x
    have hm := contourMean_of_corresponds hP hL hn hG hj (hCm _ hj.le) (hCR _ hj.le) z μ
    rw [← hx] at hm
    rw [normalizedMean_eq hm (e2 j (Finset.mem_range.mpr hj) _)]
    exact qmat_mem _
  obtain ⟨X, hX, hXC⟩ := exists_chainPoint hC hL hn hCm hu
  have hWtop : Corresponds G (t + 1) W (Y (t + 1)) := by
    have h3 := corresponds_of_represents (j := t + 1) hC hL hn hG le_rfl hGm (A := W) (V := V) ⟨hW.1, hW.2⟩
    show Corresponds G (t + 1) W (readAtLevel G (t + 1) (levelAt a ρ L (t + 1) _ V (t + 1)).2)
    rw [levelAt_top]
    exact h3
  have hWC : W = C (t + 1) := field_ext_of_forward hC hL hn le_rfl hW.1 (hCm _ le_rfl) fun z μ => by
    rw [hWtop z μ, hCR _ le_rfl z μ]
  have hXR : ∀ j, j ≤ t + 1 → Corresponds G j (levelField X j) (Y j) := by
    intro j hj
    rw [hXC j hj]
    exact hCR j hj
  have hval : chainAction a X = minimalAction a (finiteCells G) (t + 1) (Y (t + 1)) := by
    rw [chainAction_eq hC hP hL hn hG hX a,
      minimalAction_eq_partial hC hP hL hn ha hG (fun j hj => hX.2 j hj) hXR hmin (t + 1) le_rfl]
  refine ⟨X, ⟨hX, ?_, fun X' hX' hX'W => ?_⟩, fun j hj => ?_⟩
  · rw [hXC _ le_rfl, hWC]
  · have hex' : ∀ j, ∃ Z : G.GaugeField j, j ≤ t + 1 → Corresponds G j (levelField X' j) Z := by
      intro j
      by_cases hj : j ≤ t + 1
      · obtain ⟨Z, hZ⟩ := exists_frameField hC hL hn hG hj (hX'.2 j hj)
        exact ⟨Z, fun _ => hZ⟩
      · exact ⟨fun _ _ => 1, fun h => absurd h hj⟩
    choose Z hZ using hex'
    have hle := minimalAction_le_partial hC hP hL hn ha hG (fun j hj => hX'.2 j hj) hZ (t + 1) le_rfl
    have hZt : Corresponds G (t + 1) W (Z (t + 1)) := by
      have := hZ (t + 1) le_rfl
      rwa [hX'W] at this
    have hsame := minimalAction_eq hC hP hL hn ha hG hG (t + 1) le_rfl W hW.1 (Y (t + 1)) (Z (t + 1))
      hWtop hZt
    rw [hval, hsame, chainAction_eq hC hP hL hn hG hX' a]
    exact hle
  · rw [hXC j hj]
    exact represents_of_corresponds hG hj (hzs j hj) (hCm j hj) (hCR j hj)
end YangMills.Construction.RunningCouplingSlope
end
