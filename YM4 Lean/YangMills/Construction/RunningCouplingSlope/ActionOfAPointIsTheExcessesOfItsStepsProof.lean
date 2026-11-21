import YangMills.Construction.ClusterExpansionOfAStep.UnitQuaternionsAsSpecialUnitaryMatrices
import YangMills.Construction.RunningCouplingSlope.FibreFormIsASumOverTheStepsProof
import YangMills.Construction.RunningCouplingSlope.LeastPointsAreGaugeImagesOfSmallTangentsProof
import YangMills.Construction.SoftAverages.QuaternionsAsMatrices
import YangMills.Construction.RunningCouplingSlope.ActionOfAPointIsTheExcessesOfItsSteps
import YangMills.Construction.RunningCouplingSlope.LeastPointsOverAFieldAreOneOrbitProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower BlockAverages ColdStepAtMirrorFrames
open TorusFields (TorusField TorusSite trivialField readAtLevel torusFrame)
namespace ExcessDecomposition
section Quat
private abbrev qmat (q : ℍ[ℝ]) : Matrices.ComplexMatrix2 := SoftAverages.quaternionToMatrix q
private theorem quatMatrix_eq_qmat (q : ℍ[ℝ]) : UnitQuaternions.quatMatrix q = qmat q := by apply _root_.YangMills.DeltaSharedProofs.p500685 <;> assumption
private theorem qmat_one : qmat 1 = 1 := SoftAverages.quaternionToMatrix_one
private theorem qmat_mul (p q : ℍ[ℝ]) : qmat (p * q) = qmat p * qmat q := by apply _root_.YangMills.Construction.SoftAverages.quaternionToMatrix_mul <;> assumption
private theorem qmat_smul (r : ℝ) (q : ℍ[ℝ]) : qmat (r • q) = (r : ℂ) • qmat q := by apply _root_.YangMills.DeltaSharedProofs.p501227 <;> assumption
private theorem qmat_injective {p q : ℍ[ℝ]} (h : qmat p = qmat q) : p = q := by apply _root_.YangMills.DeltaSharedProofs.p501191 <;> assumption
private theorem qmat_mem (g : UnitQuaternion) :
    qmat (g : ℍ[ℝ]) ∈ Matrices.ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.quaternionToMatrix_mem_specialUnitary <;> assumption
private theorem exists_qmat_of_mem {A : Matrices.ComplexMatrix2}
    (hA : A ∈ Matrices.ComplexMatrix2.specialUnitary) : ∃ g : UnitQuaternion, A = qmat (g : ℍ[ℝ]) := by apply _root_.YangMills.DeltaSharedProofs.p500695 <;> assumption
private theorem coe_inv_unit (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
private theorem qmat_inv (g : UnitQuaternion) :
    (qmat (g : ℍ[ℝ]))⁻¹ = qmat ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by apply _root_.YangMills.DeltaSharedProofs.p502200 <;> assumption
private theorem traceDefect_qmat (q : ℍ[ℝ]) : traceDefect (qmat q) = 1 - q.re := by apply _root_.YangMills.DeltaSharedProofs.p500863 <;> assumption
private theorem half_fullTrace_qmat (q : ℍ[ℝ]) :
    (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (qmat q)).re = q.re := by apply _root_.YangMills.DeltaSharedProofs.p501762 <;> assumption
private theorem det_qmat (q : ℍ[ℝ]) : Matrix.det (qmat q) = ((Quaternion.normSq q : ℝ) : ℂ) := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.det_quaternionToMatrix <;> assumption
private theorem norm_unitQuat (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
end Quat
section Coordinates
variable {L n k : ℕ}
private def coordSite (j : ℕ) (z : Fin 4 → ℤ) : Vertex L n k j := PeriodicLattice.offsetSite 0 z
private theorem sublattice_coords (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) :
    PeriodicLattice.SublatticeCoordinates L n (PeriodicLattice.levelDepth k j) :=
  (hC L n hL.1 hL.2 hn).1 _ (by simp only [PeriodicLattice.levelDepth]; omega)
private theorem two_mul_halfPeriod {j : ℕ} (hj : j ≤ k) :
    2 * PeriodicLattice.halfPeriod L n (PeriodicLattice.levelDepth k j) = 2 * L ^ (n + (k - j)) := by apply _root_.YangMills.SharedProofs.p9710 <;> assumption
private theorem coordSite_surjective (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    (x : Vertex L n k j) : ∃ z, x = coordSite j z :=
  (sublattice_coords hC hL hn hj).2.2.2.1 0 x
private theorem coordSite_eq_iff (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) (z w : Fin 4 → ℤ) :
    coordSite (L := L) (n := n) (k := k) j z = coordSite j w ↔
      ∀ μ, ((2 * L ^ (n + (k - j)) : ℕ) : ℤ) ∣ w μ - z μ := by
  have h := (sublattice_coords hC hL hn hj).2.2.2.2.1 0 z w
  rw [two_mul_halfPeriod hj] at h
  refine h.trans (forall_congr' fun μ => ?_)
  exact Int.modEq_iff_dvd
private theorem coordSite_add (j : ℕ) (z w : Fin 4 → ℤ) :
    coordSite (L := L) (n := n) (k := k) j (z + w) = coordSite j z + coordSite j w := by
  simp [coordSite, PeriodicLattice.offsetSite, add_smul, Finset.sum_add_distrib]
private theorem sum_piSingle_smul {A : Type*} [AddCommGroup A] (f : Fin 4 → A) (μ : Fin 4) :
    ∑ ν, (Pi.single μ 1 : Fin 4 → ℤ) ν • f ν = f μ := by apply _root_.YangMills.SharedProofs.p19285 <;> assumption
private theorem unitStep_eq (j : ℕ) (μ : Fin 4) :
    PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ =
      coordSite (L := L) (n := n) (k := k) j (Pi.single μ 1) := by
  simp only [coordSite, PeriodicLattice.offsetSite, zero_add]
  rw [sum_piSingle_smul]
private theorem exists_forward_of_pos {j : ℕ} (b : Edge L n k j) (hb : b.IsPositivelyOriented) :
    ∃ x μ, b = PeriodicLattice.Bond.forwardFrom x μ := by apply _root_.YangMills.SharedProofs.p50830 <;> assumption
private theorem forward_isPos {j : ℕ} (x : Vertex L n k j) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
private theorem forwardFrom_injective (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    {x y : Vertex L n k j} {μ ν : Fin 4}
    (h : PeriodicLattice.Bond.forwardFrom x μ = PeriodicLattice.Bond.forwardFrom y ν) : x = y ∧ μ = ν := by apply _root_.YangMills.SharedProofs.p47369 <;> assumption
private theorem fieldOfPositiveValues_mem (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    (w : PositiveEdge L n k j → Matrices.ComplexMatrix2)
    (hw : ∀ c, w c ∈ Matrices.ComplexMatrix2.specialUnitary) :
    fieldOfPositiveValues w ∈ fieldSpace L n k j := by apply _root_.YangMills.SharedProofs.p18687 <;> assumption
end Coordinates
section Compatible
variable {L n k : ℕ} {F : BlockFrame}
private structure Compatible (F : BlockFrame) (L n k J : ℕ) : Prop where
  side_eq : F.blockSide = L
  le_top : J ≤ F.top
  le_height : J ≤ k
  period_eq : ∀ j, j ≤ J → ∀ i, F.period j i = 2 * L ^ (n + (k - j))
  extent_pos : ∀ i, 0 < F.extent i
private def Represents (F : BlockFrame) (j : ℕ) (C : Edge L n k j → Matrices.ComplexMatrix2)
    (Y : F.GaugeField j) : Prop :=
  ∀ (z : Fin 4 → ℤ) (μ : Fin 4),
    C (PeriodicLattice.Bond.forwardFrom (coordSite j z) μ) = qmat ((Y (siteOfCoords j z) μ : UnitQuaternion) : ℍ[ℝ])
private theorem coordSite_iff_siteOfCoords (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Compatible F L n k J)
    {j : ℕ} (hj : j ≤ J) (z w : Fin 4 → ℤ) :
    coordSite (L := L) (n := n) (k := k) j z = coordSite j w ↔
      (siteOfCoords j z : F.Site j) = siteOfCoords j w := by
  rw [coordSite_eq_iff hC hL hn (hj.trans hT.le_height), siteOfCoords_eq_iff]
  refine forall_congr' fun i => ?_
  rw [hT.period_eq j hj i]
private theorem exists_field_of_frame (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Compatible F L n k J)
    {j : ℕ} (hj : j ≤ J) (Y : F.GaugeField j) : ∃ C ∈ fieldSpace L n k j, Represents F j C Y := by
  have hjk := hj.trans hT.le_height
  have hch : ∀ c : PositiveEdge L n k j, ∃ (z : Fin 4 → ℤ) (μ : Fin 4),
      c.1 = PeriodicLattice.Bond.forwardFrom (coordSite j z) μ := by
    intro c
    obtain ⟨x, μ, h⟩ := exists_forward_of_pos c.1 c.2
    obtain ⟨z, rfl⟩ := coordSite_surjective hC hL hn hjk x
    exact ⟨z, μ, h⟩
  choose zc μc hc using hch
  refine ⟨fieldOfPositiveValues fun c => qmat ((Y (siteOfCoords j (zc c)) (μc c) : UnitQuaternion) : ℍ[ℝ]),
    fieldOfPositiveValues_mem hC hL hn hjk _ fun c => qmat_mem _, ?_⟩
  intro z μ
  have hp := forward_isPos (coordSite (L := L) (n := n) (k := k) j z) μ
  simp only [fieldOfPositiveValues, dif_pos hp]
  obtain ⟨e1, e2⟩ := forwardFrom_injective hC hL hn hjk (hc ⟨_, hp⟩)
  rw [← e2, ← (coordSite_iff_siteOfCoords hC hL hn hT hj _ _).mp e1]
private theorem exists_frame_field (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Compatible F L n k J)
    {j : ℕ} (hj : j ≤ J) {A : Edge L n k j → Matrices.ComplexMatrix2} (hA : A ∈ fieldSpace L n k j) :
    ∃ Y : F.GaugeField j, Represents F j A Y := by
  have h : ∀ (x : F.Site j) (μ : Fin 4), ∃ g : UnitQuaternion,
      A (PeriodicLattice.Bond.forwardFrom (coordSite j (siteCoords x)) μ) = qmat (g : ℍ[ℝ]) :=
    fun x μ => exists_qmat_of_mem (hA.1 _ (Set.mem_univ _))
  choose Y hY using h
  refine ⟨Y, fun z μ => ?_⟩
  have e : coordSite (L := L) (n := n) (k := k) j z = coordSite j (siteCoords (siteOfCoords j z : F.Site j)) :=
    (coordSite_iff_siteOfCoords hC hL hn hT hj _ _).mpr (YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords _).symm
  rw [e]
  exact hY _ _
private theorem readAtLevel_back {j M : ℕ} (hper : ∀ i, F.period j i = M) (Y : F.GaugeField j) :
    readAtLevel F j (fun x i => Y (siteOfCoords j fun l => (((x l : ZMod M)).cast : ℤ)) i : TorusField M) = Y := by apply _root_.YangMills.SharedProofs.p81894 <;> assumption
private theorem contourMean_of_represents (hP : ContourMeanMatchesFrame)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Compatible F L n k J)
    {j : ℕ} (hj : j + 1 ≤ J) {A : Edge L n k j → Matrices.ComplexMatrix2} (hA : A ∈ fieldSpace L n k j)
    {Y : F.GaugeField j} (hR : Represents F j A Y) (z : Fin 4 → ℤ) (μ : Fin 4) :
    contourMean A (PeriodicLattice.Bond.forwardFrom (coordSite (j + 1) z) μ) =
      qmat (BlockAverages.contourAverage Y (siteOfCoords (j + 1) z, μ)) := by
  have hjk : j < k := lt_of_lt_of_le (Nat.lt_of_succ_le hj) hT.le_height
  have hM : (2 * L ^ (n + (k - (j + 1)))) * L = 2 * L ^ (n + (k - j)) := by
    have : n + (k - j) = n + (k - (j + 1)) + 1 := by omega
    rw [this, pow_succ]
    ring
  have hper : ∀ i, F.period j i = (2 * L ^ (n + (k - (j + 1)))) * L := fun i => by
    rw [hT.period_eq j (by omega) i, hM]
  have h := hP L hL n k j (2 * L ^ (n + (k - (j + 1)))) hn hjk hM F hT.side_eq hper (hT.period_eq (j + 1) hj)
    (fun x i => Y (siteOfCoords j fun l => (((x l : ZMod _)).cast : ℤ)) i) A
    ⟨hA, fun zz μ => hR _ μ⟩ z μ
  rw [readAtLevel_back hper] at h
  exact h
private theorem unit_of_mean {m : ℍ[ℝ]} (h0 : m ≠ 0) : (‖m‖⁻¹ • m) ∈ unitary ℍ[ℝ] := by apply _root_.YangMills.Construction.BlockAverages.smul_inv_norm_mem_unitary <;> assumption
private theorem meanRadius_eq {j : ℕ} {A : Edge L n k j → Matrices.ComplexMatrix2} {c : Edge L n k (j + 1)}
    {m : ℍ[ℝ]} (hm : contourMean A c = qmat m) : meanRadius A c = ((‖m‖ : ℝ) : ℂ) := by apply _root_.YangMills.DeltaSharedProofs.p500717 <;> assumption
private theorem normalizedMean_eq {j : ℕ} {A : Edge L n k j → Matrices.ComplexMatrix2} {c : Edge L n k (j + 1)}
    {m : ℍ[ℝ]} (hm : contourMean A c = qmat m) (h0 : m ≠ 0) :
    normalizedMean A c = qmat ((⟨‖m‖⁻¹ • m, unit_of_mean h0⟩ : UnitQuaternion) : ℍ[ℝ]) := by apply _root_.YangMills.DeltaSharedProofs.p500417 <;> assumption
private theorem re_mul_star_swap (m q : ℍ[ℝ]) : (m * star q).re = (q * star m).re := by apply _root_.YangMills.SharedProofs.p60130 <;> assumption
private theorem cost_term_eq {j : ℕ} {A : Edge L n k j → Matrices.ComplexMatrix2} {c : Edge L n k (j + 1)}
    {m : ℍ[ℝ]} (hm : contourMean A c = qmat m) (g : UnitQuaternion) :
    (meanRadius A c).re * traceDefect (qmat (g : ℍ[ℝ]) * (normalizedMean A c)⁻¹) =
      ‖m‖ - (m * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])).re := by apply _root_.YangMills.DeltaSharedProofs.p502207 <;> assumption
private theorem sum_eq_finsum {α β : Type*} (s : Finset α) (f : α → ℝ) (g : β → ℝ) (φ : ↥s → β)
    (hφ : Function.Bijective φ) (h : ∀ a : ↥s, f a = g (φ a)) :
    ∑ a ∈ s, f a = ∑ᶠ b, g b := by apply _root_.YangMills.SharedProofs.p64412 <;> assumption
private def fitCost {j : ℕ} (A : Edge L n k j → Matrices.ComplexMatrix2)
    (B : Edge L n k (j + 1) → Matrices.ComplexMatrix2) : ℝ :=
  ∑ᶠ c : PositiveEdge L n k (j + 1),
    (meanRadius A c.1).re * traceDefect (B c.1 * (normalizedMean A c.1)⁻¹)
private theorem mem_innerBonds (hL : Conventions.IsAdmissibleBlockingFactor L) {J : ℕ}
    (hT : Compatible F L n k J) {j : ℕ} (hj : j ≤ J) (b : F.Site j × Fin 4) :
    b ∈ innerBonds (finiteCells F) j := by
  have hodd : Odd F.blockSide := hT.side_eq ▸ hL.1
  have hs := fun x : F.Site j => mem_allSites hodd hT.extent_pos (hj.trans hT.le_top) x
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨hs _, hs _⟩
private theorem sum_blockFit (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ}
    (hT : Compatible F L n k J) {j : ℕ} (hj : j + 1 ≤ J)
    {A : Edge L n k j → Matrices.ComplexMatrix2} (hA : A ∈ fieldSpace L n k j)
    {B : Edge L n k (j + 1) → Matrices.ComplexMatrix2}
    {Y : F.GaugeField j} {Y' : F.GaugeField (j + 1)} (hR : Represents F j A Y) (hR' : Represents F (j + 1) B Y') :
    ∑ c ∈ innerBonds (finiteCells F) (j + 1), blockFit Y Y' c = fitCost A B := by
  have hjk := hj.trans hT.le_height
  refine sum_eq_finsum _ _ _ (fun p => ⟨PeriodicLattice.Bond.forwardFrom (coordSite (j + 1) (siteCoords p.1.1)) p.1.2,
    forward_isPos _ _⟩) ⟨?_, ?_⟩ ?_
  · rintro ⟨⟨x, μ⟩, hp⟩ ⟨⟨y, ν⟩, hq⟩ h
    have h1 := congrArg Subtype.val h
    obtain ⟨e1, e2⟩ := forwardFrom_injective hC hL hn hjk h1
    have e3 := (coordSite_iff_siteOfCoords hC hL hn hT hj _ _).mp e1
    rw [YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords, YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords] at e3
    simp only at e2 e3
    subst e2 e3
    rfl
  · rintro ⟨c, hc⟩
    obtain ⟨x, μ, rfl⟩ := exists_forward_of_pos c hc
    obtain ⟨z, rfl⟩ := coordSite_surjective hC hL hn hjk x
    refine ⟨⟨(siteOfCoords (j + 1) z, μ), mem_innerBonds hL hT hj _⟩, Subtype.ext ?_⟩
    show PeriodicLattice.Bond.forwardFrom
      (coordSite (j + 1) (siteCoords (siteOfCoords (j + 1) z : F.Site (j + 1)))) μ = _
    rw [(coordSite_iff_siteOfCoords hC hL hn hT hj _ _).mpr (YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords _)]
  · rintro ⟨⟨x, μ⟩, hp⟩
    have h1 := contourMean_of_represents hP hL hn hT hj hA hR (siteCoords x) μ
    have h2 := hR' (siteCoords x) μ
    rw [YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords] at h1 h2
    show blockFit Y Y' (x, μ) = _
    simp only
    rw [h2, cost_term_eq h1]
    rfl
end Compatible
section Minimal
variable {L n k : ℕ} {F G : BlockFrame}
private theorem Compatible.mono {J J' : ℕ} (hT : Compatible F L n k J) (h : J' ≤ J) : Compatible F L n k J' :=
  ⟨hT.side_eq, h.trans hT.le_top, h.trans hT.le_height, fun j hj => hT.period_eq j (hj.trans h), hT.extent_pos⟩
private theorem plaquetteHolonomy_eq (Y : F.GaugeField 0) (x : F.Site 0) (μ ν : Fin 4) :
    plaquetteHolonomy Y (x, μ, ν) =
      Y x μ * Y (x + unitStep 0 μ) ν * (Y (x + unitStep 0 ν) μ)⁻¹ * (Y x ν)⁻¹ := by apply _root_.YangMills.Construction.PatchCurls.plaquetteHolonomy_eq <;> assumption
private theorem wilsonAction_of_represents (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Compatible F L n k J)
    {A : Edge L n k 0 → Matrices.ComplexMatrix2} (hA : A ∈ fieldSpace L n k 0) {Y : F.GaugeField 0}
    (hR : Represents F 0 A Y) :
    wilsonAction (finiteCells F) Y = Tower.plaquetteAction L n k A := by
  have hodd : Odd F.blockSide := hT.side_eq ▸ hL.1
  have hs := fun x : F.Site 0 => mem_allSites hodd hT.extent_pos (Nat.zero_le _) x
  have hk0 : 0 ≤ k := Nat.zero_le _
  have hj0 : 0 ≤ J := Nat.zero_le _
  have hmem : ∀ q : F.Site 0 × Fin 4 × Fin 4, q.2.1 < q.2.2 → q ∈ innerPlaquettes (finiteCells F) 0 := by
    intro q hq
    simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hs _, hq, fun y _ => hs y⟩
  show ∑ p ∈ innerPlaquettes (finiteCells F) 0, (1 - ((plaquetteHolonomy Y p : UnitQuaternion) : ℍ[ℝ]).re) =
    ∑ᶠ p : Face L n k 0, PeriodicLattice.plaquetteCost A p
  refine sum_eq_finsum _ _ _ (fun q => ⟨coordSite 0 (siteCoords q.1.1), q.1.2.1, q.1.2.2,
    (Finset.mem_filter.mp q.2).2.1⟩) ⟨?_, ?_⟩ ?_
  · rintro ⟨⟨x, μ, ν⟩, hp⟩ ⟨⟨y, μ', ν'⟩, hq⟩ h
    have e1 := congrArg PeriodicLattice.Plaquette.origin h
    have e2 := congrArg PeriodicLattice.Plaquette.firstAxis h
    have e3 := congrArg PeriodicLattice.Plaquette.secondAxis h
    have e4 := (coordSite_iff_siteOfCoords hC hL hn hT hj0 _ _).mp e1
    rw [YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords, YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords] at e4
    simp only at e2 e3 e4
    subst e2 e3 e4
    rfl
  · rintro ⟨b, μ, ν, h⟩
    obtain ⟨z, rfl⟩ := coordSite_surjective hC hL hn hk0 b
    refine ⟨⟨(siteOfCoords 0 z, μ, ν), hmem _ h⟩, ?_⟩
    refine PeriodicLattice.Plaquette.ext ?_ rfl rfl
    exact (coordSite_iff_siteOfCoords hC hL hn hT hj0 _ _).mpr (YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords _)
  · rintro ⟨⟨x, μ, ν⟩, hp⟩
    set z := siteCoords x with hz
    have hx : (siteOfCoords 0 z : F.Site 0) = x := YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords x
    have hadd : ∀ ρ : Fin 4, (siteOfCoords 0 (z + Pi.single ρ 1) : F.Site 0) = x + unitStep 0 ρ := by
      intro ρ
      rw [_root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_add, hx]
      rfl
    have hst : ∀ ρ : Fin 4, coordSite (L := L) (n := n) (k := k) 0 z +
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) ρ = coordSite 0 (z + Pi.single ρ 1) := by
      intro ρ
      rw [coordSite_add, unitStep_eq]
    have r3 := hA.2 (PeriodicLattice.Bond.forwardFrom
      (coordSite 0 z + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) ν) μ) (Set.mem_univ _)
    have r4 := hA.2 (PeriodicLattice.Bond.forwardFrom (coordSite 0 z) ν) (Set.mem_univ _)
    show 1 - ((plaquetteHolonomy Y (x, μ, ν) : UnitQuaternion) : ℍ[ℝ]).re =
      1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (PeriodicLattice.pathHolonomy A
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
        qmat ((plaquetteHolonomy Y (x, μ, ν) : UnitQuaternion) : ℍ[ℝ]) := by
      simp only [PeriodicLattice.pathHolonomy, List.map, List.prod_cons, List.prod_nil, mul_one]
      rw [r3, r4, hst, hst, hR, hR, hR, hR, hadd, hadd, hx, plaquetteHolonomy_eq, qmat_inv, qmat_inv]
      simp only [Submonoid.coe_mul, qmat_mul, mul_assoc]
    rw [hh, half_fullTrace_qmat]
private theorem bddBelow_step (a : ℝ) (ha : 0 < a) (S : Finset F.Cell) (j : ℕ) (V : F.GaugeField (j + 1)) :
    BddBelow (Set.range fun W : F.GaugeField j =>
      minimalAction a S j W + a * ∑ c ∈ innerBonds S (j + 1), blockFit W V c) := by apply _root_.YangMills.SharedProofs.p89849 <;> assumption
private theorem minimalAction_step_le (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) {J : ℕ} (hF : Compatible F L n k J) (hG : Compatible G L n k J) {j : ℕ} (hj : j + 1 ≤ J)
    (ih : ∀ A ∈ fieldSpace L n k j, ∀ (Y : F.GaugeField j) (Y' : G.GaugeField j),
      Represents F j A Y → Represents G j A Y' →
      minimalAction a (finiteCells F) j Y = minimalAction a (finiteCells G) j Y')
    {B : Edge L n k (j + 1) → Matrices.ComplexMatrix2} {Y : F.GaugeField (j + 1)} {Y' : G.GaugeField (j + 1)}
    (hR : Represents F (j + 1) B Y) (hR' : Represents G (j + 1) B Y') :
    minimalAction a (finiteCells G) (j + 1) Y' ≤ minimalAction a (finiteCells F) (j + 1) Y := by
  refine le_ciInf fun W => ?_
  obtain ⟨A, hA, hRA⟩ := exists_field_of_frame hC hL hn hF (Nat.le_of_succ_le hj) W
  obtain ⟨W', hW'⟩ := exists_frame_field hC hL hn hG (Nat.le_of_succ_le hj) hA
  refine (ciInf_le (bddBelow_step a ha _ j Y') W').trans_eq ?_
  rw [← ih A hA W W' hRA hW', sum_blockFit hC hP hL hn hF hj hA hRA hR, sum_blockFit hC hP hL hn hG hj hA hW' hR']
private theorem minimalAction_congr (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) {J : ℕ} (hF : Compatible F L n k J) (hG : Compatible G L n k J) (j : ℕ) (hj : j ≤ J) :
    ∀ A ∈ fieldSpace L n k j, ∀ (Y : F.GaugeField j) (Y' : G.GaugeField j),
      Represents F j A Y → Represents G j A Y' →
      minimalAction a (finiteCells F) j Y = minimalAction a (finiteCells G) j Y' := by
  induction j with
  | zero =>
    intro A hA Y Y' hR hR'
    show wilsonAction _ Y = wilsonAction _ Y'
    rw [wilsonAction_of_represents hC hL hn hF hA hR, wilsonAction_of_represents hC hL hn hG hA hR']
  | succ j ih =>
    intro B hB Y Y' hR hR'
    have ih' := ih (Nat.le_of_succ_le hj)
    exact le_antisymm
      (minimalAction_step_le hC hP hL hn ha hG hF hj (fun A hA Y Y' h h' => (ih' A hA Y' Y h' h).symm) hR' hR)
      (minimalAction_step_le hC hP hL hn ha hF hG hj ih' hR hR')
private def totalUpTo (a : ℝ) (C : (j : ℕ) → Edge L n k j → Matrices.ComplexMatrix2) (j : ℕ) : ℝ :=
  Tower.plaquetteAction L n k (C 0) + a * ∑ i ∈ Finset.range j, fitCost (C i) (C (i + 1))
end Minimal
section Points
variable {L n k : ℕ} {G : BlockFrame}
private theorem levelField_pos (X : ChainPoint L n k) {j : ℕ} (hj : j < k) (c : PositiveEdge L n k (j + 1)) :
    levelField X (j + 1) c.1 = X.noise ⟨j, hj⟩ c * normalizedMean (levelField X j) c.1 := by
  rw [levelField, dif_pos hj]
  simp only [fieldOfPositiveValues, dif_pos c.2]
private theorem fitCost_of_point (hC : PeriodicLattice.CoordinateDescription)
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
  obtain ⟨Y, hY⟩ := exists_frame_field hC hL hn hG hj.le hA
  obtain ⟨x, μ, hx⟩ := exists_forward_of_pos c.1 c.2
  obtain ⟨z, rfl⟩ := coordSite_surjective hC hL hn hj x
  have hm := contourMean_of_represents hP hL hn hG hj hA hY z μ
  rw [← hx] at hm
  set m := BlockAverages.contourAverage Y (siteOfCoords (j + 1) z, μ)
  have hpos := levelField_pos X hj c
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
    have h5 := norm_unitQuat g
    rw [h4] at h5
    simp at h5
  · have hu := normalizedMean_eq hm h0
    set v : UnitQuaternion := ⟨‖m‖⁻¹ • m, unit_of_mean h0⟩
    have : levelField X (j + 1) c.1 * (normalizedMean (levelField X j) c.1)⁻¹ = X.noise ⟨j, hj⟩ c := by
      rw [hpos, hu, mul_assoc, qmat_inv, ← qmat_mul, ← Submonoid.coe_mul, mul_inv_cancel]
      show _ * qmat 1 = _
      rw [qmat_one, mul_one]
    rw [this]
private theorem chainAction_eq_total (hC : PeriodicLattice.CoordinateDescription)
    (hP : ContourMeanMatchesFrame) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hG : Compatible G L n k k) {X : ChainPoint L n k} (hX : IsCompactValued X) (a : ℝ) :
    chainAction a X = totalUpTo a (levelField X) k := by
  simp only [chainAction, totalUpTo]
  rw [← Fin.sum_univ_eq_sum_range (fun i => fitCost (levelField X i) (levelField X (i + 1))) k]
  congr 2
  exact Finset.sum_congr rfl fun i _ => fitCost_of_point hC hP hL hn hG rfl hX i.2
end Points
section Steps
variable {L n k : ℕ}
private theorem torusSideBelow_eq (L : ℕ) : ∀ s N, torusSideBelow L s N = N * L ^ s
  | 0, N => by simp [torusSideBelow]
  | s + 1, N => by
    rw [torusSideBelow, torusSideBelow_eq L s]
    ring
private theorem compatible_torusFrame {t m : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
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
private theorem compatible_frameAtStep (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ} (h : j + 1 ≤ k) :
    Compatible (frameAtStep L n k j) L n k (j + 1) :=
  compatible_torusFrame hL h (by rw [sideAtStep, torusSideBelow_eq, pow_add]; ring)
private theorem represents_of_values {F : BlockFrame} (hC : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {J : ℕ} (hT : Compatible F L n k J)
    {j : ℕ} (hj : j ≤ J) {A : Edge L n k j → Matrices.ComplexMatrix2} {Y : F.GaugeField j}
    (h : ∀ b : F.Site j × Fin 4, A (edgeOfCoords j b) = qmat ((Y b.1 b.2 : UnitQuaternion) : ℍ[ℝ])) :
    Represents F j A Y := by
  intro z μ
  have e : coordSite (L := L) (n := n) (k := k) j z = coordSite j (siteCoords (siteOfCoords j z : F.Site j)) :=
    (coordSite_iff_siteOfCoords hC hL hn hT hj _ _).mpr (YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_siteCoords _).symm
  rw [e]
  exact h (siteOfCoords j z, μ)
end Steps
end ExcessDecomposition
open ExcessDecomposition in
theorem chainAction_eq_sum_excessEnergy (hP : ContourMeanMatchesFrame)
    (hC : PeriodicLattice.CoordinateDescription) :
    ChainActionIsSumOfExcesses := by
  intro a ha L hL k n hn X hX Z Z' hZ hZ'
  have hT : ∀ j : Fin (k + 1), Compatible (frameAtStep L n (k + 1) j) L n (k + 1) (j + 1) :=
    fun j => compatible_frameAtStep hL j.2
  have hR : ∀ j : Fin (k + 1), Represents (frameAtStep L n (k + 1) j) j (levelField X j) (Z j) :=
    fun j => represents_of_values hC hL hn (hT j) (Nat.le_succ _) (hZ j)
  have hR' : ∀ j : Fin (k + 1), Represents (frameAtStep L n (k + 1) j) (j + 1) (levelField X (j + 1)) (Z' j) :=
    fun j => represents_of_values hC hL hn (hT j) le_rfl (hZ' j)
  set top : ℝ := minimalAction a (finiteCells (frameAtStep L n (k + 1) (Fin.last k)))
    (frameAtStep L n (k + 1) (Fin.last k)).top (Z' (Fin.last k)) with htop
  let f : ℕ → ℝ := fun i => if h : i < k + 1 then
    minimalAction a (finiteCells (frameAtStep L n (k + 1) (⟨i, h⟩ : Fin (k + 1))))
      (frameAtStep L n (k + 1) (⟨i, h⟩ : Fin (k + 1))).depth (Z ⟨i, h⟩) else top
  have hf : ∀ j : Fin (k + 1), f j = minimalAction a (finiteCells (frameAtStep L n (k + 1) j))
      (frameAtStep L n (k + 1) j).depth (Z j) := fun j => by
    simp only [f]
    rw [dif_pos j.2]
  have hnext : ∀ j : Fin (k + 1), f (j + 1) = minimalAction a (finiteCells (frameAtStep L n (k + 1) j))
      (frameAtStep L n (k + 1) j).top (Z' j) := by
    intro j
    by_cases h : (j : ℕ) + 1 < k + 1
    · have h1 := hf ⟨j + 1, h⟩
      refine h1.trans ?_
      exact minimalAction_congr hC hP hL hn ha ((hT ⟨j + 1, h⟩).mono (Nat.le_succ _)) (hT j) (j + 1) le_rfl
        (levelField X (j + 1)) (hX.2 _ h.le) _ _ (hR ⟨j + 1, h⟩) (hR' j)
    · have hj : j = Fin.last k := Fin.ext (by simp only [Fin.val_last]; omega)
      subst hj
      simp only [f]
      rw [dif_neg h]
  have hex : ∀ j : Fin (k + 1), excessEnergy a (Z j) (Z' j) =
      f j - f (j + 1) + a * fitCost (levelField X j) (levelField X (j + 1)) := by
    intro j
    have hs := sum_blockFit hC hP hL hn (hT j) le_rfl (hX.2 j (by have := j.2; omega)) (hR j) (hR' j)
    have e : excessEnergy a (Z j) (Z' j) =
        f j + a * fitCost (levelField X j) (levelField X (j + 1)) - f (j + 1) := by
      rw [hf, hnext, ← hs]
      rfl
    rw [e]
    ring
  have h0 : f 0 = Tower.plaquetteAction L n (k + 1) (levelField X 0) := by
    have h1 := hf ⟨0, Nat.succ_pos k⟩
    refine h1.trans ?_
    exact wilsonAction_of_represents hC hL hn (hT ⟨0, Nat.succ_pos k⟩) (hX.2 0 (Nat.zero_le _))
      (hR ⟨0, Nat.succ_pos k⟩)
  have hk : f (k + 1) = top := by
    simp only [f]
    rw [dif_neg (lt_irrefl _)]
  rw [chainAction_eq_total hC hP hL hn (hT (Fin.last k)) hX a, Finset.sum_congr rfl fun j _ => hex j,
    Fin.sum_univ_eq_sum_range
      (fun i => f i - f (i + 1) + a * fitCost (levelField X i) (levelField X (i + 1))) (k + 1),
    Finset.sum_add_distrib, Finset.sum_range_sub', ← Finset.mul_sum, h0, hk]
  simp only [totalUpTo]
  ring
end YangMills.Construction.RunningCouplingSlope
end
