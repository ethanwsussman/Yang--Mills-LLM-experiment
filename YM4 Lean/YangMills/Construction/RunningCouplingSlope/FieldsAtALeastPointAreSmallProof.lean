import YangMills.Construction.Lattice.BlocksBoxesAndPaths
import YangMills.Construction.Lattice.FlatConfigurationsOnBoxesAndTheirAverages
import YangMills.Construction.RunningCouplingSlope.ActionOnTheFibreUnderAGaugeFunctionProof
import YangMills.Construction.RunningCouplingSlope.FlatPointIsLeastProof
import YangMills.Construction.RunningCouplingSlope.LeastPointsAreGaugeImagesOfSmallTangentsProof
import YangMills.Construction.RunningCouplingSlope.LegsOfTheOrdersAreContours
import Mathlib
import YangMills.Construction.Matrices.SpecialUnitaryTwo
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MinimizerSmallness
open Filter Matrices
open scoped Topology
section Smooth
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
theorem contDiffAt_det {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀) :
    ContDiffAt ℝ 2 (fun y => (f y).det) y₀ := by apply _root_.YangMills.SharedProofs.p38879 <;> assumption
theorem contDiffAt_inv {f : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀) (hu : IsUnit (f y₀).det) :
    ContDiffAt ℝ 2 (fun y => (f y)⁻¹) y₀ := by apply _root_.YangMills.SharedProofs.p22704 <;> assumption
theorem contDiffAt_smul {f : Y → ℂ} {g : Y → ComplexMatrix2} (hf : ContDiffAt ℝ 2 f y₀)
    (hg : ContDiffAt ℝ 2 g y₀) : ContDiffAt ℝ 2 (fun y => f y • g y) y₀ := by apply _root_.YangMills.SharedProofs.p3257 <;> assumption
theorem contDiffAt_cpow_half {f : Y → ℂ} (hf : ContDiffAt ℝ 2 f y₀) (hs : f y₀ ∈ Complex.slitPlane) :
    ContDiffAt ℝ 2 (fun y => f y ^ (1 / 2 : ℂ)) y₀ := by apply _root_.YangMills.SharedProofs.p3856 <;> assumption
variable {L n k j : ℕ}
theorem contDiffAt_pathHolonomy {V : Y → Tower.Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (Γ : List (Tower.Edge L n k j)) :
    ContDiffAt ℝ 2 (fun y => PeriodicLattice.pathHolonomy (V y) Γ) y₀ := by apply _root_.YangMills.SharedProofs.p6652 <;> assumption
theorem contDiffAt_contourMean [NeZero L] {V : Y → Tower.Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Tower.Edge L n k (j + 1)) : ContDiffAt ℝ 2 (fun y => contourMean (V y) c) y₀ := by apply _root_.YangMills.SharedProofs.p1840 <;> assumption
theorem contDiffAt_meanRadius [NeZero L] {V : Y → Tower.Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Tower.Edge L n k (j + 1)) (hs : (contourMean (V y₀) c).det ∈ Complex.slitPlane) :
    ContDiffAt ℝ 2 (fun y => meanRadius (V y) c) y₀ :=
  contDiffAt_cpow_half (contDiffAt_det (contDiffAt_contourMean hV hu c)) hs
theorem contDiffAt_normalizedMean [NeZero L] {V : Y → Tower.Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, ContDiffAt ℝ 2 (fun y => V y b) y₀) (hu : ∀ b, IsUnit (V y₀ b).det)
    (c : Tower.Edge L n k (j + 1)) (hs : (contourMean (V y₀) c).det ∈ Complex.slitPlane)
    (hl : meanRadius (V y₀) c ≠ 0) :
    ContDiffAt ℝ 2 (fun y => normalizedMean (V y) c) y₀ :=
  contDiffAt_smul ((contDiffAt_meanRadius hV hu c hs).inv hl) (contDiffAt_contourMean hV hu c)
end Smooth
section Quaternions
def quaternionSubmodule : Submodule ℝ ComplexMatrix2 where
  carrier := {M | M 1 1 = star (M 0 0) ∧ M 1 0 = -star (M 0 1)}
  add_mem' := by
    rintro A B ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · simp [Matrix.add_apply, h1, h3]
    · simp only [Matrix.add_apply, h2, h4, star_add]; ring
  zero_mem' := by simp
  smul_mem' := by
    rintro c A ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · simp [Matrix.smul_apply, h1]
    · simp [Matrix.smul_apply, h2]
theorem mem_quaternionSubmodule_of_mem {g : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) : g ∈ quaternionSubmodule :=
  ComplexMatrix2.quaternion_entries_of_mem_specialUnitary hg
theorem det_eq_normSq_of_mem_quaternionSubmodule {M : ComplexMatrix2} (hM : M ∈ quaternionSubmodule) :
    M.det = ((Complex.normSq (M 0 0) + Complex.normSq (M 0 1) : ℝ) : ℂ) :=
  ComplexMatrix2.det_quaternionMatrix hM
theorem det_mem_slitPlane {M : ComplexMatrix2} (hM : M ∈ quaternionSubmodule) (h : M.det ≠ 0) :
    M.det ∈ Complex.slitPlane :=
  ComplexMatrix2.det_quaternionMatrix_mem_slitPlane hM h
variable {L n k j : ℕ}
theorem compact_mul_mem {g h : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup)
    (hh : h ∈ PeriodicLattice.compactGaugeGroup) :
    g * h ∈ PeriodicLattice.compactGaugeGroup := ComplexMatrix2.specialUnitary.mul_mem hg hh
theorem compact_inv_mem {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g⁻¹ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_mem_compactGaugeGroup <;> assumption
theorem det_eq_one_of_compact {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    g.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
theorem isUnit_det_of_compact {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    IsUnit g.det := by apply _root_.YangMills.Construction.PeriodicLattice.SingleStepEstimate.det_isUnit_of_mem <;> assumption
theorem pathHolonomy_mem_compact {V : Tower.Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) (Γ : List (Tower.Edge L n k j)) :
    PeriodicLattice.pathHolonomy V Γ ∈ PeriodicLattice.compactGaugeGroup := by apply _root_.YangMills.SharedProofs.p6330 <;> assumption
theorem contourMean_mem_quaternionSubmodule [NeZero L] {V : Tower.Edge L n k j → ComplexMatrix2}
    (hV : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) (c : Tower.Edge L n k (j + 1)) :
    contourMean V c ∈ quaternionSubmodule := by
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Tower.Vertex L n k j)).Finite := Set.toFinite _
  have hs : ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) =
      (((1 / 24 : ℝ) * ((L : ℝ) ^ (-4 : ℤ)) : ℝ) : ℂ) := by
    simp [PeriodicLattice.inverseFourthPowerWeight]
  rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin, hs, Complex.coe_smul]
  refine quaternionSubmodule.smul_mem _
    (quaternionSubmodule.sum_mem fun x _ => quaternionSubmodule.sum_mem fun π _ => ?_)
  exact mem_quaternionSubmodule_of_mem (compact_mul_mem
    (compact_mul_mem (pathHolonomy_mem_compact hV _) (pathHolonomy_mem_compact hV _))
    (compact_inv_mem (pathHolonomy_mem_compact hV _)))
end Quaternions
section Values
variable {L n k j : ℕ}
theorem fieldOfPositiveValues_pos (w : Tower.PositiveEdge L n k j → ComplexMatrix2)
    {b : Tower.Edge L n k j} (h : b.IsPositivelyOriented) :
    Tower.fieldOfPositiveValues w b = w ⟨b, h⟩ := by
  simp [Tower.fieldOfPositiveValues, h]
theorem fieldOfPositiveValues_neg (w : Tower.PositiveEdge L n k j → ComplexMatrix2)
    {b : Tower.Edge L n k j} (h : ¬b.IsPositivelyOriented) :
    Tower.fieldOfPositiveValues w b =
      (w ⟨b.opposite, PeriodicLattice.Bond.opposite_isPositivelyOriented h⟩)⁻¹ := by
  simp [Tower.fieldOfPositiveValues, h, PeriodicLattice.Bond.opposite_isPositivelyOriented h]
theorem fieldOfPositiveValues_mem_fieldSpace {w : Tower.PositiveEdge L n k j → ComplexMatrix2}
    (hw : ∀ c, w c ∈ PeriodicLattice.compactGaugeGroup)
    (hx : ∀ b : Tower.Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    Tower.fieldOfPositiveValues w ∈ Tower.fieldSpace L n k j := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.fieldOfPositiveValues_mem_fieldSpace <;> assumption
end Values
section Levels
variable {L n k : ℕ}
theorem levelField_succ (X : ChainPoint L n k) {j : ℕ} (h : j < k) :
    levelField X (j + 1) =
      Tower.fieldOfPositiveValues fun c => X.noise ⟨j, h⟩ c * normalizedMean (levelField X j) c.1 := by
  simp [levelField, h]
theorem det_contourMean_ne_zero {j : ℕ} {V : Tower.Edge L n k j → ComplexMatrix2}
    {c : Tower.Edge L n k (j + 1)} (h : meanRadius V c ≠ 0) :
    (contourMean V c).det ≠ 0 := by apply _root_.YangMills.SharedProofs.p15699 <;> assumption
end Levels
section Families
variable {L n k : ℕ} [NeZero L] {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {y₀ : Y}
  {Z : Y → ChainPoint L n k}
theorem isUnit_det_of_mem_fieldSpace {j : ℕ} {V : Tower.Edge L n k j → ComplexMatrix2}
    (hV : V ∈ Tower.fieldSpace L n k j) (b : Tower.Edge L n k j) :
    IsUnit (V b).det := isUnit_det_of_compact (hV.1 b (Set.mem_univ b))
theorem finite_face (j : ℕ) : Finite (Tower.Face L n k j) := by apply _root_.YangMills.SharedProofs.p23234 <;> assumption
end Families
section Sites
instance {L n k j : ℕ} [NeZero L] : Fintype (Tower.Edge L n k j) := Fintype.ofFinite _
variable {L : ℕ} [NeZero L]
theorem coe_toSublattice {m : ℕ} {i i' : ℤ} (h : i ≤ i') (y : PeriodicLattice.Site L m i) :
    ((y.toSublattice i' : PeriodicLattice.Site L m i') : PeriodicLattice.FourTorus L m) = y := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.coe_toSublattice <;> assumption
end Sites
section Paths
variable {L m : ℕ} {i : ℤ}
theorem isBondPathFromTo_append {Γ Γ' : List (PeriodicLattice.Bond L m i)}
    {x y z : PeriodicLattice.Site L m i}
    (h : PeriodicLattice.IsBondPathFromTo Γ x y) (h' : PeriodicLattice.IsBondPathFromTo Γ' y z) :
    PeriodicLattice.IsBondPathFromTo (Γ ++ Γ') x z := by
  obtain ⟨c, e, t, l⟩ := h
  obtain ⟨c', e', t', l'⟩ := h'
  rcases List.eq_nil_or_concat Γ with rfl | ⟨Γ₀, b, rfl⟩
  · have := e rfl
    subst this
    rw [List.nil_append]
    exact ⟨c', e', t', l'⟩
  simp only [List.concat_eq_append] at c e t l ⊢
  rcases Γ' with _ | ⟨b', Γ₁⟩
  · have := e' rfl
    subst this
    rw [List.append_nil]
    exact ⟨c, e, t, l⟩
  have hbh : b.target = y := l b (by simp)
  have hbt : b'.source = y := t' b' (by simp)
  refine ⟨?_, by simp, ?_, ?_⟩
  · refine List.IsChain.append c c' ?_
    intro p hp q hq
    have hp' : b = p := by simpa using hp
    have hq' : b' = q := by simpa using hq
    rw [← hp', ← hq', hbh, hbt]
  · intro p hp
    rcases Γ₀ with _ | ⟨a, Γ₀⟩
    · have : b = p := by simpa using hp
      rw [← this]
      exact t b (by simp)
    · have : a = p := by simpa using hp
      rw [← this]
      exact t a (by simp)
  · intro p hp
    refine l' p ?_
    simpa [List.getLast?_append] using hp
theorem pathHolonomy_append (U : PeriodicLattice.Bond L m i → ComplexMatrix2)
    (Γ Γ' : List (PeriodicLattice.Bond L m i)) :
    PeriodicLattice.pathHolonomy U (Γ ++ Γ') =
      PeriodicLattice.pathHolonomy U Γ * PeriodicLattice.pathHolonomy U Γ' := by
  simp [PeriodicLattice.pathHolonomy]
theorem pathHolonomy_eq_of_flat_box (hF : PeriodicLattice.FlatFieldsAndTheirAverages)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hi : 0 < i)
    {Y : Set (PeriodicLattice.Site L m i)} {U : PeriodicLattice.Bond L m i → ComplexMatrix2}
    (hbox : PeriodicLattice.IsSiteBox i Y) (hU : U ∈ PeriodicLattice.compactGaugeFields L m i)
    (hflat : ∀ p, PeriodicLattice.plaquetteHolonomy U p = 1)
    {Γ₁ Γ₂ : List (PeriodicLattice.Bond L m i)} {z z' : PeriodicLattice.Site L m i}
    (h₁ : PeriodicLattice.IsBondPathFromTo Γ₁ z z') (h₂ : PeriodicLattice.IsBondPathFromTo Γ₂ z z')
    (i₁ : ∀ b ∈ Γ₁, b.LiesIn Y) (i₂ : ∀ b ∈ Γ₂, b.LiesIn Y) :
    PeriodicLattice.pathHolonomy U Γ₁ = PeriodicLattice.pathHolonomy U Γ₂ := by
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, i = PeriodicLattice.levelDepth K 0 :=
    ⟨i.toNat, by simp only [PeriodicLattice.levelDepth]; omega⟩
  have hK : 0 < K := by
    simp only [PeriodicLattice.levelDepth] at hi
    omega
  exact (hF L m K hL hm hK).1 Y U hbox ⟨fun b _ => hU.1 b (Set.mem_univ _),
    fun b _ => hU.2 b (Set.mem_univ _)⟩ (fun p _ => hflat p) Γ₁ Γ₂ z z' h₁ h₂ i₁ i₂
end Paths
section FlatField
variable {L n k j : ℕ} [NeZero L]
  (hF : PeriodicLattice.FlatFieldsAndTheirAverages)
  (hlegs : AxisOrderLegsAreContours)
  (hcf : PeriodicLattice.BlockContoursAndCombs)
  (hbb : PeriodicLattice.BlocksBoxesPaths.Statement)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
abbrev sourceCrossing (c : Tower.Edge L n k (j + 1)) : List (Tower.Edge L n k j) :=
  PeriodicLattice.crossingPath c (c.source.toSublattice (PeriodicLattice.levelDepth k j))
theorem levelDepth_succ_le :
    PeriodicLattice.levelDepth k (j + 1) ≤ PeriodicLattice.levelDepth k j := by apply _root_.YangMills.Construction.Tower.ScalingPreservesStepsAtSide.levelDepth_succ_le <;> assumption
theorem shiftAcross_toSublattice_source (c : Tower.Edge L n k (j + 1)) :
    PeriodicLattice.shiftAcross c (c.source.toSublattice (PeriodicLattice.levelDepth k j)) =
      c.target.toSublattice (PeriodicLattice.levelDepth k j) := by
  refine Subtype.ext ?_
  have e1 := coe_toSublattice (levelDepth_succ_le (k := k) (j := j)) c.source
  have e2 := coe_toSublattice (levelDepth_succ_le (k := k) (j := j)) (c.target - c.source)
  have e3 := coe_toSublattice (levelDepth_succ_le (k := k) (j := j)) c.target
  change ((c.source.toSublattice (PeriodicLattice.levelDepth k j) : PeriodicLattice.FourTorus L n) +
    ((c.target - c.source).toSublattice (PeriodicLattice.levelDepth k j) :
      PeriodicLattice.FourTorus L n)) = _
  rw [e1, e2, e3]
  simp
include hbb hL hn in
theorem crossingPath_properties (hj : j < k) (c : Tower.Edge L n k (j + 1))
    (hc : c.IsPositivelyOriented) :
    (∀ x ∈ (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Tower.Vertex L n k j)),
      PeriodicLattice.shiftAcross c x ∈
        (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.target :
          Set (Tower.Vertex L n k j))) ∧
    ∀ x ∈ (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Tower.Vertex L n k j)),
      PeriodicLattice.IsBondPathFromTo (PeriodicLattice.crossingPath c x) x
        (PeriodicLattice.shiftAcross c x) ∧
      ∀ b ∈ PeriodicLattice.crossingPath c x, PeriodicLattice.Bond.LiesIn b
        (PeriodicLattice.sitesIn (PeriodicLattice.bondDoubleBlock c) : Set (Tower.Vertex L n k j)) := by
  have hK : 0 < k := by omega
  have hcross := (hbb L k n ⟨rfl, rfl, rfl, hL.1, hL.2, hK, hn⟩).2.2.2.2.2.2 j hj |>.2.1 c hc
  refine ⟨fun x hx => hcross.1.mapsTo hx, fun x hx => ⟨(hcross.2 x hx).1, fun b hb => ?_⟩⟩
  exact ((hcross.2 x hx).2.2 b hb).2
include hlegs hcf hL hn in
theorem contourLeg_properties (hj : j < k) (y : Tower.Vertex L n k (j + 1)) (x : Tower.Vertex L n k j)
    (hx : x ∈ (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y :
      Set (Tower.Vertex L n k j)))
    (π : Equiv.Perm (Fin 4)) :
    PeriodicLattice.IsBondPathFromTo (contourLeg y x π)
        (y.toSublattice (PeriodicLattice.levelDepth k j)) x ∧
      (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
      ∀ b ∈ contourLeg y x π, (b.source : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∧
        (b.target : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
  obtain ⟨σ, hσ⟩ := hlegs L n _ _ y x π
  have h := ((hcf L n k hL hn j hj y x hx).2.1 _ ⟨σ, rfl⟩)
  rw [← hσ] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩
include hF hlegs hcf hbb hL hn in
theorem contourHolonomy_of_flat (hj : j < k) {V : Tower.Edge L n k j → ComplexMatrix2}
    (hV : V ∈ Tower.fieldSpace L n k j)
    (hflat : ∀ p, PeriodicLattice.plaquetteHolonomy V p = 1) (c : Tower.Edge L n k (j + 1))
    (hc : c.IsPositivelyOriented) (x : Tower.Vertex L n k j)
    (hx : x ∈ (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Tower.Vertex L n k j)))
    (π : Equiv.Perm (Fin 4)) :
    contourHolonomy V c x π = PeriodicLattice.pathHolonomy V (sourceCrossing c) := by
  have hi : 0 < PeriodicLattice.levelDepth k j := by
    simp only [PeriodicLattice.levelDepth]; omega
  have hK : 0 < k := by omega
  have hbox : PeriodicLattice.IsSiteBox (PeriodicLattice.levelDepth k j)
      (PeriodicLattice.sitesIn (PeriodicLattice.bondDoubleBlock c) : Set (Tower.Vertex L n k j)) :=
    (((hbb L k n ⟨rfl, rfl, rfl, hL.1, hL.2, hK, hn⟩).2.2.2.2.2.2 j hj).1.2.1 c).1
  obtain ⟨hmaps, hcr⟩ := crossingPath_properties hbb hL hn hj c hc
  have hx' := hmaps x hx
  obtain ⟨l1, m1, i1⟩ := contourLeg_properties hlegs hcf hL hn hj c.source x hx π
  obtain ⟨l2, m2, i2⟩ := contourLeg_properties hlegs hcf hL hn hj c.target _ hx' π
  have hy₀ : c.source.toSublattice (PeriodicLattice.levelDepth k j) ∈
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Tower.Vertex L n k j)) := by
    change ((c.source.toSublattice (PeriodicLattice.levelDepth k j) :
      PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j)) : PeriodicLattice.FourTorus L n) ∈
        PeriodicLattice.unitBlock c.source
    rw [coe_toSublattice levelDepth_succ_le]
    exact m1
  obtain ⟨p₀, ins₀⟩ := hcr _ hy₀
  obtain ⟨p₁, ins₁⟩ := hcr x hx
  rw [shiftAcross_toSublattice_source] at p₀
  have hA := isBondPathFromTo_append l1 p₁
  have hB := isBondPathFromTo_append p₀ l2
  have h := pathHolonomy_eq_of_flat_box hF hL hn hi hbox hV hflat hA hB ?_ ?_
  · rw [pathHolonomy_append, pathHolonomy_append] at h
    have hu := isUnit_det_of_compact (pathHolonomy_mem_compact (fun b => hV.1 b (Set.mem_univ _))
      (contourLeg c.target (PeriodicLattice.shiftAcross c x) π))
    rw [contourHolonomy, h, mul_assoc, Matrix.mul_nonsing_inv _ hu, mul_one]
  · intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact ⟨Or.inl (i1 b hb).1, Or.inl (i1 b hb).2⟩
    · exact ins₁ b hb
  · intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact ins₀ b hb
    · exact ⟨Or.inr (i2 b hb).1, Or.inr (i2 b hb).2⟩
variable (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement)
include hb hL hn in
theorem card_sitesInBlock (hj : j < k) (c : Tower.Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) :
    Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Tower.Vertex L n k j)) = L ^ 4 := ((hb L hL n k hn).1 j hj c hc).1
include hb hlegs hcf hL hn in
theorem toSublattice_source_mem (hj : j < k) (c : Tower.Edge L n k (j + 1))
    (hc : c.IsPositivelyOriented) :
    c.source.toSublattice (PeriodicLattice.levelDepth k j) ∈
      (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
        Set (Tower.Vertex L n k j)) := by
  have hcard := card_sitesInBlock hL hn hb hj c hc
  have hpos : Nat.card ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Tower.Vertex L n k j)) ≠ 0 := by
    rw [hcard]
    have := hL.2
    positivity
  have hne : Nonempty ↥(PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Tower.Vertex L n k j)) := by
    have := Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hpos)
    exact this.1
  obtain ⟨x, hx⟩ := hne
  obtain ⟨-, m1, -⟩ := contourLeg_properties hlegs hcf hL hn hj c.source x hx 1
  change ((c.source.toSublattice (PeriodicLattice.levelDepth k j) :
    PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j)) : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.unitBlock c.source
  rw [coe_toSublattice levelDepth_succ_le]
  exact m1
include hF hlegs hcf hbb hL hn hb in
theorem normalizedMean_of_flat (hj : j < k) {V : Tower.Edge L n k j → ComplexMatrix2}
    (hV : V ∈ Tower.fieldSpace L n k j)
    (hflat : ∀ p, PeriodicLattice.plaquetteHolonomy V p = 1) (c : Tower.Edge L n k (j + 1))
    (hc : c.IsPositivelyOriented) :
    meanRadius V c = 1 ∧ normalizedMean V c = PeriodicLattice.pathHolonomy V (sourceCrossing c) := by
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source :
      Set (Tower.Vertex L n k j)).Finite := Set.toFinite _
  set T := PeriodicLattice.pathHolonomy V (sourceCrossing c) with hT
  have hTr : T ∈ PeriodicLattice.compactGaugeGroup :=
    pathHolonomy_mem_compact (fun b => hV.1 b (Set.mem_univ _)) _
  have hcard : hfin.toFinset.card = L ^ 4 := by
    rw [← Nat.card_eq_card_finite_toFinset hfin]
    exact card_sitesInBlock hL hn hb hj c hc
  have hLc : (L : ℂ) ≠ 0 := by
    have := hL.2
    exact_mod_cast (by omega : L ≠ 0)
  have hmean : contourMean V c = T := by
    rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin]
    have e : ∑ x ∈ hfin.toFinset, ∑ π : Equiv.Perm (Fin 4), contourHolonomy V c x π =
        ∑ x ∈ hfin.toFinset, ∑ π : Equiv.Perm (Fin 4), T := by
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun π _ => ?_
      exact contourHolonomy_of_flat hF hlegs hcf hbb hL hn hj hV hflat c hc x
        (hfin.mem_toFinset.1 hx) π
    rw [e]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, hcard]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    have hs : (1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L * (((L ^ 4 : ℕ) : ℂ) *
        (((Nat.factorial 4 : ℕ)) : ℂ)) = 1 := by
      simp only [PeriodicLattice.inverseFourthPowerWeight]
      have h4 : Nat.factorial 4 = 24 := rfl
      rw [h4]
      push_cast
      rw [zpow_neg]
      push_cast
      field_simp
    rw [← mul_assoc] at hs
    rw [hs, one_smul]
  have hlen : meanRadius V c = 1 := by
    rw [meanRadius, hmean, det_eq_one_of_compact hTr]
    simp
  refine ⟨hlen, ?_⟩
  rw [normalizedMean, hlen, hmean]
  simp
include hF hlegs hcf hbb hL hn hb in
theorem plaquetteHolonomy_normalizedMean_of_flat (hj : j < k)
    (hx : ∀ b : Tower.Edge L n k (j + 1), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {V : Tower.Edge L n k j → ComplexMatrix2} (hV : V ∈ Tower.fieldSpace L n k j)
    (hflat : ∀ p, PeriodicLattice.plaquetteHolonomy V p = 1)
    (p : Tower.Face L n k (j + 1)) :
    PeriodicLattice.plaquetteHolonomy
      (Tower.fieldOfPositiveValues fun c : Tower.PositiveEdge L n k (j + 1) =>
        normalizedMean V c.1) p = 1 := by
  have hi : 0 < PeriodicLattice.levelDepth k j := by
    simp only [PeriodicLattice.levelDepth]; omega
  have hK : 0 < k := by omega
  have hVr : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup := fun b => hV.1 b (Set.mem_univ _)
  set U : Tower.Edge L n k (j + 1) → ComplexMatrix2 :=
    Tower.fieldOfPositiveValues fun c : Tower.PositiveEdge L n k (j + 1) =>
      normalizedMean V c.1 with hU
  have hpos : ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
      U c = PeriodicLattice.pathHolonomy V (sourceCrossing c) := by
    intro c hc
    rw [hU, fieldOfPositiveValues_pos _ hc]
    exact (normalizedMean_of_flat hF hlegs hcf hbb hL hn hb hj hV hflat c hc).2
  have hUc : U ∈ Tower.fieldSpace L n k (j + 1) := by
    refine fieldOfPositiveValues_mem_fieldSpace (fun c => ?_) hx
    rw [(normalizedMean_of_flat hF hlegs hcf hbb hL hn hb hj hV hflat c.1 c.2).2]
    exact pathHolonomy_mem_compact hVr _
  have hf : ∀ (x : Tower.Vertex L n k (j + 1)) (μ : Fin 4),
      (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented :=
    fun x μ => ⟨μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
  set s₁ := PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k (j + 1)) p.firstAxis with hs₁
  set s₂ := PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k (j + 1)) p.secondAxis with hs₂
  set b₁ := PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis with hb₁
  set b₂ := PeriodicLattice.Bond.forwardFrom (p.origin + s₁) p.secondAxis with hb₂
  set b₃ := PeriodicLattice.Bond.forwardFrom (p.origin + s₂) p.firstAxis with hb₃
  set b₄ := PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis with hb₄
  have hbox : PeriodicLattice.IsSiteBox (PeriodicLattice.levelDepth k j)
      (PeriodicLattice.sitesIn (⋃ y ∈ p.vertices, PeriodicLattice.unitBlock y) :
        Set (Tower.Vertex L n k j)) :=
    (((hbb L k n ⟨rfl, rfl, rfl, hL.1, hL.2, hK, hn⟩).2.2.2.2.2.2 j hj).1.2.2 p).1
  have hcr : ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented → c.source ∈ p.vertices →
      c.target ∈ p.vertices →
      PeriodicLattice.IsBondPathFromTo (sourceCrossing c)
        (c.source.toSublattice (PeriodicLattice.levelDepth k j))
        (c.target.toSublattice (PeriodicLattice.levelDepth k j)) ∧
      ∀ b ∈ sourceCrossing c, PeriodicLattice.Bond.LiesIn b
        (PeriodicLattice.sitesIn (⋃ y ∈ p.vertices, PeriodicLattice.unitBlock y) :
          Set (Tower.Vertex L n k j)) := by
    intro c hc ht hh
    obtain ⟨-, h2⟩ := crossingPath_properties hbb hL hn hj c hc
    obtain ⟨p₀, ins₀⟩ := h2 _ (toSublattice_source_mem hlegs hcf hL hn hb hj c hc)
    rw [shiftAcross_toSublattice_source] at p₀
    refine ⟨p₀, fun b hb' => ?_⟩
    have hmem : ∀ z : PeriodicLattice.FourTorus L n, z ∈ PeriodicLattice.bondDoubleBlock c →
        z ∈ ⋃ y ∈ p.vertices, PeriodicLattice.unitBlock y := by
      intro z hz
      rcases hz with hz | hz
      · exact Set.mem_iUnion₂.2 ⟨_, ht, hz⟩
      · exact Set.mem_iUnion₂.2 ⟨_, hh, hz⟩
    exact ⟨hmem _ (ins₀ b hb').1, hmem _ (ins₀ b hb').2⟩
  have c₁ : p.origin ∈ p.vertices := by simp [PeriodicLattice.Plaquette.vertices]
  have c₂ : p.origin + s₁ ∈ p.vertices := by simp [PeriodicLattice.Plaquette.vertices, hs₁]
  have c₃ : p.origin + s₁ + s₂ ∈ p.vertices := by
    simp [PeriodicLattice.Plaquette.vertices, hs₁, hs₂]
  have c₄ : p.origin + s₂ ∈ p.vertices := by simp [PeriodicLattice.Plaquette.vertices, hs₂]
  have e₃ : p.origin + s₂ + s₁ = p.origin + s₁ + s₂ := by abel
  obtain ⟨q₁, i₁⟩ := hcr b₁ (hf _ _) c₁ c₂
  obtain ⟨q₂, i₂⟩ := hcr b₂ (hf _ _) c₂ c₃
  obtain ⟨q₃, i₃⟩ := hcr b₃ (hf _ _) c₄ (by
    change p.origin + s₂ + s₁ ∈ p.vertices
    rw [e₃]; exact c₃)
  obtain ⟨q₄, i₄⟩ := hcr b₄ (hf _ _) c₁ c₄
  have hA := isBondPathFromTo_append q₁ q₂
  have hB := isBondPathFromTo_append q₄ q₃
  have e₅ : b₃.target = b₂.target := e₃
  rw [e₅] at hB
  have h := pathHolonomy_eq_of_flat_box hF hL hn hi hbox hV hflat hA hB
    (fun b hb' => (List.mem_append.1 hb').elim (i₁ b) (i₂ b))
    (fun b hb' => (List.mem_append.1 hb').elim (i₄ b) (i₃ b))
  rw [pathHolonomy_append, pathHolonomy_append] at h
  have r₃ : U b₃.opposite = (U b₃)⁻¹ := hUc.2 b₃ (Set.mem_univ _)
  have r₄ : U b₄.opposite = (U b₄)⁻¹ := hUc.2 b₄ (Set.mem_univ _)
  have u₃ : IsUnit (U b₃).det := isUnit_det_of_mem_fieldSpace hUc b₃
  have u₄ : IsUnit (U b₄).det := isUnit_det_of_mem_fieldSpace hUc b₄
  have h' : U b₁ * U b₂ = U b₄ * U b₃ := by
    rw [hpos b₁ (hf _ _), hpos b₂ (hf _ _), hpos b₃ (hf _ _), hpos b₄ (hf _ _)]
    exact h
  have e₆ : PeriodicLattice.plaquetteHolonomy U p = U b₁ * (U b₂ * ((U b₃)⁻¹ * (U b₄)⁻¹)) := by
    simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
      PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    rw [r₃, r₄]
  rw [e₆, ← mul_assoc, h', mul_assoc, ← mul_assoc (U b₃), Matrix.mul_nonsing_inv _ u₃, one_mul,
    Matrix.mul_nonsing_inv _ u₄]
end FlatField
section Compact
theorem exists_pos_of_small_on_compact {α : Type*} [TopologicalSpace α] {K : Set α}
    (hK : IsCompact K) {E : α → ℝ}
    (hE : Continuous E) (hE0 : ∀ x, 0 ≤ E x) {G : Set α} (hG : ∀ x ∈ K, E x = 0 → G ∈ 𝓝 x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, E x < δ → x ∈ G := by
  have hK' : IsCompact (K \ interior G) := hK.diff isOpen_interior
  rcases (K \ interior G).eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, fun x hx _ => ?_⟩
    have : x ∈ interior G := by
      by_contra hn
      have : x ∈ K \ interior G := ⟨hx, hn⟩
      rw [h] at this
      exact this
    exact interior_subset this
  · obtain ⟨x₀, hx₀, hmin⟩ := hK'.exists_isMinOn h hE.continuousOn
    have hpos : 0 < E x₀ := by
      refine lt_of_le_of_ne (hE0 x₀) fun h0 => hx₀.2 ?_
      exact mem_interior_iff_mem_nhds.2 (hG x₀ hx₀.1 h0.symm)
    refine ⟨E x₀, hpos, fun x hx hlt => ?_⟩
    by_contra hn
    have hx' : x ∈ K \ interior G := ⟨hx, fun h' => hn (interior_subset h')⟩
    exact absurd (hmin hx') (not_le.2 hlt)
theorem isCompact_compactGaugeGroup :
    IsCompact (PeriodicLattice.compactGaugeGroup : Set ComplexMatrix2) := by
  have : CompactSpace ComplexMatrix2.specialUnitary := inferInstance
  exact isCompact_iff_compactSpace.2 this
end Compact
section Configs
variable {L n k j : ℕ} [NeZero L]
theorem isCompact_fieldSpace : IsCompact (Tower.fieldSpace L n k j) := by
  have h1 : IsCompact (Set.pi Set.univ fun _ : Tower.Edge L n k j =>
      (PeriodicLattice.compactGaugeGroup : Set ComplexMatrix2)) :=
    isCompact_univ_pi fun _ => isCompact_compactGaugeGroup
  have h2 : IsClosed {U : Tower.Edge L n k j → ComplexMatrix2 | ∀ b, U b.opposite * U b = 1} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun b => isClosed_eq ?_ continuous_const
    exact (continuous_apply _).mul (continuous_apply _)
  have e : Tower.fieldSpace L n k j =
      (Set.pi Set.univ fun _ : Tower.Edge L n k j =>
        (PeriodicLattice.compactGaugeGroup : Set ComplexMatrix2)) ∩
        {U | ∀ b, U b.opposite * U b = 1} := by
    ext U
    constructor
    · intro h
      refine ⟨fun b _ => h.1 b (Set.mem_univ _), fun b => ?_⟩
      rw [h.2 b (Set.mem_univ _)]
      exact Matrix.nonsing_inv_mul _ (isUnit_det_of_compact (h.1 b (Set.mem_univ _)))
    · rintro ⟨h1, h2⟩
      exact ⟨fun b _ => h1 b (Set.mem_univ _),
        fun b _ => Matrix.inv_eq_left_inv (h2 b) ▸ rfl⟩
  rw [e]
  exact h1.inter_right h2
end Configs
section Step
variable {L n k j : ℕ} [NeZero L]
  (hF : PeriodicLattice.FlatFieldsAndTheirAverages)
  (hlegs : AxisOrderLegsAreContours)
  (hcf : PeriodicLattice.BlockContoursAndCombs)
  (hbb : PeriodicLattice.BlocksBoxesPaths.Statement)
  (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
theorem continuous_plaquetteHolonomy (p : Tower.Face L n k j) :
    Continuous fun U : Tower.Edge L n k j → ComplexMatrix2 => PeriodicLattice.plaquetteHolonomy U p :=
  continuous_iff_continuousAt.2 fun U =>
    (contDiffAt_pathHolonomy (V := fun V : Tower.Edge L n k j → ComplexMatrix2 => V) (y₀ := U)
      (fun b => (contDiff_apply ℝ ComplexMatrix2 b).contDiffAt) _).continuousAt
instance {j : ℕ} : Finite (Tower.Face L n k j) := finite_face j
instance {j : ℕ} : Fintype (Tower.Face L n k j) := Fintype.ofFinite _
instance {j : ℕ} : Fintype (Tower.PositiveEdge L n k j) := Fintype.ofFinite _
abbrev StepPair (L n k j : ℕ) : Type :=
  (Tower.Edge L n k j → ComplexMatrix2) × (Tower.PositiveEdge L n k (j + 1) → ComplexMatrix2)
def compactStepPairs (L n k j : ℕ) : Set (StepPair L n k j) :=
  (Tower.fieldSpace L n k j) ×ˢ
    (Set.pi Set.univ fun _ : Tower.PositiveEdge L n k (j + 1) =>
      (PeriodicLattice.compactGaugeGroup : Set ComplexMatrix2))
theorem isCompact_compactStepPairs : IsCompact (compactStepPairs L n k j) :=
  isCompact_fieldSpace.prod (isCompact_univ_pi fun _ => isCompact_compactGaugeGroup)
def distanceFromFlat (x : StepPair L n k j) : ℝ :=
  (∑ p : Tower.Face L n k j, ‖PeriodicLattice.plaquetteHolonomy x.1 p - 1‖) +
    ∑ c : Tower.PositiveEdge L n k (j + 1), ‖x.2 c - 1‖
theorem continuous_distanceFromFlat :
    Continuous (distanceFromFlat (L := L) (n := n) (k := k) (j := j)) := by
  unfold distanceFromFlat
  refine Continuous.add (continuous_finsetSum _ fun p _ => ?_)
    (continuous_finsetSum _ fun c _ => ?_)
  · exact (((continuous_plaquetteHolonomy p).comp continuous_fst).sub continuous_const).norm
  · exact (((continuous_apply c).comp continuous_snd).sub continuous_const).norm
theorem distanceFromFlat_nonneg (x : StepPair L n k j) : 0 ≤ distanceFromFlat x :=
  add_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)
abbrev nextLevelField (x : StepPair L n k j) : Tower.Edge L n k (j + 1) → ComplexMatrix2 :=
  Tower.fieldOfPositiveValues fun c : Tower.PositiveEdge L n k (j + 1) =>
    x.2 c * normalizedMean x.1 c.1
def nearOneSet (L n k j : ℕ) (ε : ℝ) : Set (StepPair L n k j) :=
  {x | (∀ c : Tower.PositiveEdge L n k (j + 1), ‖meanRadius x.1 c.1 - 1‖ < ε) ∧
    ∀ p : Tower.Face L n k (j + 1),
      ‖PeriodicLattice.plaquetteHolonomy (nextLevelField x) p - 1‖ < ε}
include hF hlegs hcf hbb hb hL hn in
theorem nearOneSet_mem_nhds (hj : j < k)
    (hx : ∀ b : Tower.Edge L n k (j + 1), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {ε : ℝ} (hε : 0 < ε)
    {V : Tower.Edge L n k j → ComplexMatrix2} {w : Tower.PositiveEdge L n k (j + 1) → ComplexMatrix2}
    (hV : V ∈ Tower.fieldSpace L n k j) (h0 : distanceFromFlat ((V, w) : StepPair L n k j) = 0) :
    nearOneSet L n k j ε ∈ 𝓝 ((V, w) : StepPair L n k j) := by
  have h1 := (add_eq_zero_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)).1 h0
  have hflat : ∀ p, PeriodicLattice.plaquetteHolonomy V p = 1 := fun p => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => norm_nonneg _).1 h1.1 p (Finset.mem_univ _)
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  have hw1 : ∀ c, w c = 1 := fun c => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => norm_nonneg _).1 h1.2 c (Finset.mem_univ _)
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  have hVr : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup := fun b => hV.1 b (Set.mem_univ _)
  have hfa := fun (c : Tower.Edge L n k (j + 1)) (hc : c.IsPositivelyOriented) =>
    normalizedMean_of_flat hF hlegs hcf hbb hL hn hb hj hV hflat c hc
  have hone : ∀ b : Tower.Edge L n k j,
      ContDiffAt ℝ 2 (fun y : StepPair L n k j => y.1 b) (V, w) := fun b =>
    (contDiff_apply ℝ ComplexMatrix2 b).contDiffAt.comp _ contDiff_fst.contDiffAt
  have hl : ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented → meanRadius V c ≠ 0 :=
    fun c hc => by
      rw [(hfa c hc).1]; exact one_ne_zero
  have hsl : ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
      (contourMean V c).det ∈ Complex.slitPlane :=
    fun c hc => det_mem_slitPlane (contourMean_mem_quaternionSubmodule hVr c)
      (det_contourMean_ne_zero (hl c hc))
  have hlen : ∀ c : Tower.PositiveEdge L n k (j + 1), ∀ᶠ y in 𝓝 ((V, w) : StepPair L n k j),
      ‖meanRadius y.1 c.1 - 1‖ < ε := by
    intro c
    have hc := (contDiffAt_meanRadius (V := fun y : StepPair L n k j => y.1) (y₀ := (V, w)) hone
      (isUnit_det_of_mem_fieldSpace hV) c.1 (hsl c.1 c.2)).continuousAt
    have h2 := hc.tendsto.eventually (Metric.ball_mem_nhds _ hε)
    filter_upwards [h2] with y hy
    have h3 : meanRadius V c.1 = 1 := (hfa c.1 c.2).1
    simp only [Metric.mem_ball, dist_eq_norm] at hy
    rwa [h3] at hy
  have hval : ∀ c : Tower.PositiveEdge L n k (j + 1), ContDiffAt ℝ 2
      (fun y : StepPair L n k j => y.2 c * normalizedMean y.1 c.1) (V, w) := fun c =>
    (((contDiff_apply ℝ ComplexMatrix2 c).contDiffAt).comp _ contDiff_snd.contDiffAt).mul
      (contDiffAt_normalizedMean (V := fun y : StepPair L n k j => y.1) (y₀ := (V, w)) hone
        (isUnit_det_of_mem_fieldSpace hV) c.1 (hsl c.1 c.2) (hl c.1 c.2))
  have hvr : ∀ c : Tower.PositiveEdge L n k (j + 1), w c * normalizedMean V c.1 ∈
      PeriodicLattice.compactGaugeGroup := fun c => by
    rw [hw1 c, one_mul, (hfa c.1 c.2).2]
    exact pathHolonomy_mem_compact hVr _
  have hbond : ∀ b : Tower.Edge L n k (j + 1),
      ContDiffAt ℝ 2 (fun y : StepPair L n k j => nextLevelField y b) (V, w) := by
    intro b
    by_cases hbp : b.IsPositivelyOriented
    · simp only [nextLevelField, fieldOfPositiveValues_pos _ hbp]
      exact hval ⟨b, hbp⟩
    · simp only [nextLevelField, fieldOfPositiveValues_neg _ hbp]
      exact contDiffAt_inv (hval _) (isUnit_det_of_compact (hvr _))
  have hpl : ∀ p : Tower.Face L n k (j + 1), ∀ᶠ y in 𝓝 ((V, w) : StepPair L n k j),
      ‖PeriodicLattice.plaquetteHolonomy (nextLevelField y) p - 1‖ < ε := by
    intro p
    have hc : ContinuousAt (fun y : StepPair L n k j =>
        PeriodicLattice.plaquetteHolonomy (nextLevelField y) p) (V, w) :=
      (contDiffAt_pathHolonomy hbond _).continuousAt
    have h2 := hc.tendsto.eventually (Metric.ball_mem_nhds _ hε)
    filter_upwards [h2] with y hy
    have h3 : PeriodicLattice.plaquetteHolonomy (nextLevelField ((V, w) : StepPair L n k j)) p = 1 := by
      have e : (fun c : Tower.PositiveEdge L n k (j + 1) => w c * normalizedMean V c.1) =
          fun c => normalizedMean V c.1 := by
        funext c
        rw [hw1 c, one_mul]
      simp only [nextLevelField]
      rw [e]
      exact plaquetteHolonomy_normalizedMean_of_flat hF hlegs hcf hbb hL hn hb hj hx hV hflat p
    simp only [Metric.mem_ball, dist_eq_norm] at hy
    rwa [h3] at hy
  exact (eventually_all.2 hlen).and (eventually_all.2 hpl)
include hF hlegs hcf hbb hb hL hn in
theorem exists_near_one_of_small (hj : j < k)
    (hx : ∀ b : Tower.Edge L n k (j + 1), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ V ∈ Tower.fieldSpace L n k j,
      (∀ p, ComplexMatrix2.operatorNorm (PeriodicLattice.plaquetteHolonomy V p - 1) < δ) →
      ∀ w : Tower.PositiveEdge L n k (j + 1) → ComplexMatrix2,
      (∀ c, w c ∈ PeriodicLattice.compactGaugeGroup) →
      (∀ c, ComplexMatrix2.operatorNorm (w c - 1) < δ) →
      ((V, w) : StepPair L n k j) ∈ nearOneSet L n k j ε := by
  have hG : ∀ x ∈ compactStepPairs L n k j, distanceFromFlat x = 0 →
      nearOneSet L n k j ε ∈ 𝓝 x := by
    intro x hx' h0
    exact nearOneSet_mem_nhds hF hlegs hcf hbb hb hL hn hj hx hε hx'.1 h0
  obtain ⟨δ, hδ, hgood⟩ := exists_pos_of_small_on_compact isCompact_compactStepPairs
    continuous_distanceFromFlat distanceFromFlat_nonneg hG
  set N : ℝ := (Fintype.card (Tower.Face L n k j) : ℝ) +
    (Fintype.card (Tower.PositiveEdge L n k (j + 1)) : ℝ) + 1 with hN
  have hNp : 0 < N := by positivity
  refine ⟨δ / N, by positivity, fun V hV hp w hw hw' => ?_⟩
  have hmem : ((V, w) : StepPair L n k j) ∈ compactStepPairs L n k j := ⟨hV, fun c _ => hw c⟩
  have hlt : distanceFromFlat ((V, w) : StepPair L n k j) < δ := by
    have s1 : (∑ p : Tower.Face L n k j, ‖PeriodicLattice.plaquetteHolonomy V p - 1‖) ≤
        (Fintype.card (Tower.Face L n k j) : ℝ) * (δ / N) := by
      have := Finset.sum_le_card_nsmul Finset.univ
        (fun p : Tower.Face L n k j => ‖PeriodicLattice.plaquetteHolonomy V p - 1‖) (δ / N)
        (fun p _ => (hp p).le)
      simpa using this
    have s2 : (∑ c : Tower.PositiveEdge L n k (j + 1), ‖w c - 1‖) ≤
        (Fintype.card (Tower.PositiveEdge L n k (j + 1)) : ℝ) * (δ / N) := by
      have := Finset.sum_le_card_nsmul Finset.univ
        (fun c : Tower.PositiveEdge L n k (j + 1) => ‖w c - 1‖) (δ / N) (fun c _ => (hw' c).le)
      simpa using this
    have s3 : N * (δ / N) = δ := by field_simp
    have s4 : 0 < δ / N := by positivity
    have s5 : distanceFromFlat ((V, w) : StepPair L n k j) =
        (∑ p : Tower.Face L n k j, ‖PeriodicLattice.plaquetteHolonomy V p - 1‖) +
          ∑ c : Tower.PositiveEdge L n k (j + 1), ‖w c - 1‖ := rfl
    rw [s5]
    nlinarith
  exact hgood _ hmem hlt
end Step
section Defect
theorem norm_sub_one_sq {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    ‖g - 1‖ ^ 2 = 2 * traceDefect g := by apply _root_.YangMills.SharedProofs.p32894 <;> assumption
theorem traceDefect_nonneg {g : ComplexMatrix2} (hg : g ∈ PeriodicLattice.compactGaugeGroup) :
    0 ≤ traceDefect g := by apply _root_.YangMills.SharedProofs.p3544 <;> assumption
theorem traceDefect_one : traceDefect 1 = 0 := by
  simp [traceDefect, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
theorem re_cpow_half_nonneg (z : ℂ) : 0 ≤ (z ^ (1 / 2 : ℂ)).re := by apply _root_.YangMills.SharedProofs.p69172 <;> assumption
end Defect
section Parts
variable {L n k : ℕ} [NeZero L]
theorem plaquetteCost_eq_traceDefect (U : Tower.Edge L n k 0 → ComplexMatrix2)
    (p : Tower.Face L n k 0) :
    PeriodicLattice.plaquetteCost U p = traceDefect (PeriodicLattice.plaquetteHolonomy U p) := by apply _root_.YangMills.SharedProofs.p12545 <;> assumption
theorem plaquetteHolonomy_mem_compact {j : ℕ} {U : Tower.Edge L n k j → ComplexMatrix2}
    (hU : U ∈ Tower.fieldSpace L n k j) (p : Tower.Face L n k j) :
    PeriodicLattice.plaquetteHolonomy U p ∈ PeriodicLattice.compactGaugeGroup :=
  pathHolonomy_mem_compact (fun b => hU.1 b (Set.mem_univ _)) _
theorem plaquetteAction_eq_sum (U : Tower.Edge L n k 0 → ComplexMatrix2) :
    Tower.plaquetteAction L n k U =
      ∑ p : Tower.Face L n k 0, traceDefect (PeriodicLattice.plaquetteHolonomy U p) := by
  simp only [Tower.plaquetteAction, PeriodicLattice.wilsonAction, finsum_eq_sum_of_fintype,
    plaquetteCost_eq_traceDefect]
theorem plaquetteAction_nonneg {U : Tower.Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ Tower.fieldSpace L n k 0) :
    0 ≤ Tower.plaquetteAction L n k U := by
  rw [plaquetteAction_eq_sum]
  exact Finset.sum_nonneg fun p _ => traceDefect_nonneg (plaquetteHolonomy_mem_compact hU p)
theorem norm_plaquetteHolonomy_sub_one_sq_le {U : Tower.Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ Tower.fieldSpace L n k 0) (p : Tower.Face L n k 0) :
    ‖PeriodicLattice.plaquetteHolonomy U p - 1‖ ^ 2 ≤ 2 * Tower.plaquetteAction L n k U := by
  rw [norm_sub_one_sq (plaquetteHolonomy_mem_compact hU p), plaquetteAction_eq_sum]
  have := Finset.single_le_sum (f := fun p : Tower.Face L n k 0 =>
    traceDefect (PeriodicLattice.plaquetteHolonomy U p))
    (fun p _ => traceDefect_nonneg (plaquetteHolonomy_mem_compact hU p)) (Finset.mem_univ p)
  linarith
def noiseTerm (X : ChainPoint L n k) (i : Fin k) (c : Tower.PositiveEdge L n k (i + 1)) : ℝ :=
  (meanRadius (levelField X i) c.1).re * traceDefect (X.noise i c)
theorem noiseTerm_nonneg {X : ChainPoint L n k} (hX : IsCompactValued X) (i : Fin k)
    (c : Tower.PositiveEdge L n k (i + 1)) : 0 ≤ noiseTerm X i c :=
  mul_nonneg (re_cpow_half_nonneg _) (traceDefect_nonneg (hX.1 i c))
theorem chainAction_eq (a : ℝ) (X : ChainPoint L n k) :
    chainAction a X = Tower.plaquetteAction L n k X.fine +
      a * ∑ i : Fin k, ∑ c : Tower.PositiveEdge L n k (i + 1), noiseTerm X i c := by
  simp only [chainAction, noiseTerm, finsum_eq_sum_of_fintype]
theorem plaquetteAction_le_chainAction {a : ℝ} (ha : 0 < a) {X : ChainPoint L n k}
    (hX : IsCompactValued X) :
    Tower.plaquetteAction L n k X.fine ≤ chainAction a X := by
  rw [chainAction_eq]
  have : 0 ≤ a * ∑ i : Fin k, ∑ c : Tower.PositiveEdge L n k (i + 1), noiseTerm X i c :=
    mul_nonneg ha.le (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ =>
      noiseTerm_nonneg hX i c)
  linarith
theorem noiseTerm_le_chainAction {a : ℝ} (ha : 0 < a) {X : ChainPoint L n k}
    (hX : IsCompactValued X) (i : Fin k)
    (c : Tower.PositiveEdge L n k (i + 1)) : a * noiseTerm X i c ≤ chainAction a X := by
  rw [chainAction_eq]
  have h1 : noiseTerm X i c ≤ ∑ c : Tower.PositiveEdge L n k (i + 1), noiseTerm X i c :=
    Finset.single_le_sum (f := fun c => noiseTerm X i c) (fun c _ => noiseTerm_nonneg hX i c)
      (Finset.mem_univ c)
  have h2 : (∑ c : Tower.PositiveEdge L n k (i + 1), noiseTerm X i c) ≤
      ∑ i : Fin k, ∑ c : Tower.PositiveEdge L n k (i + 1), noiseTerm X i c :=
    Finset.single_le_sum
      (f := fun i : Fin k => ∑ c : Tower.PositiveEdge L n k (i + 1), noiseTerm X i c)
      (fun i _ => Finset.sum_nonneg fun c _ => noiseTerm_nonneg hX i c) (Finset.mem_univ i)
  have h3 := plaquetteAction_nonneg (hX.2 0 (Nat.zero_le _))
  have h3' : 0 ≤ Tower.plaquetteAction L n k X.fine := h3
  have h4 := mul_le_mul_of_nonneg_left (h1.trans h2) ha.le
  linarith
def SmallThroughLevel (X : ChainPoint L n k) (m : ℕ) (ε : ℝ) : Prop :=
  (∀ j, j ≤ m → ∀ p : Tower.Face L n k j,
    ‖PeriodicLattice.plaquetteHolonomy (levelField X j) p - 1‖ < ε) ∧
  ∀ i : Fin k, (i : ℕ) < m → ∀ c : Tower.PositiveEdge L n k (i + 1),
    ‖X.noise i c - 1‖ < ε ∧ ‖meanRadius (levelField X i) c.1 - 1‖ < ε
theorem exists_small_through_level (hF : PeriodicLattice.FlatFieldsAndTheirAverages)
    (hlegs : AxisOrderLegsAreContours)
    (hcf : PeriodicLattice.BlockContoursAndCombs)
    (hbb : PeriodicLattice.BlocksBoxesPaths.Statement)
    (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hxor : ∀ j, j ≤ k → ∀ b : Tower.Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {a : ℝ} (ha : 0 < a) :
    ∀ m, m ≤ k → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ChainPoint L n k, IsCompactValued X →
      chainAction a X < δ → SmallThroughLevel X m ε := by
  intro m
  induction m with
  | zero =>
    intro _ ε hε
    refine ⟨ε ^ 2 / 2, by positivity, fun X hX hlt =>
      ⟨fun j hj p => ?_, fun i hi => absurd hi (by omega)⟩⟩
    obtain rfl : j = 0 := by omega
    have hU : X.fine ∈ Tower.fieldSpace L n k 0 := hX.2 0 (Nat.zero_le _)
    have h1 := norm_plaquetteHolonomy_sub_one_sq_le hU p
    have h2 := plaquetteAction_le_chainAction ha hX
    have h3 : ‖PeriodicLattice.plaquetteHolonomy X.fine p - 1‖ ^ 2 < ε ^ 2 := by linarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  | succ m ih =>
    intro hm ε hε
    have h : m < k := hm
    obtain ⟨δ₁, hδ₁, hstep⟩ := exists_near_one_of_small hF hlegs hcf hbb hb hL hn h (hxor _ hm)
      (ε := min ε (1 / 2)) (by positivity)
    obtain ⟨δ₂, hδ₂, hlow⟩ := ih h.le (min ε δ₁) (by positivity)
    set d := min δ₁ ε with hd
    have hdp : 0 < d := by positivity
    refine ⟨min δ₂ (a * d ^ 2 / 4), by positivity, fun X hX hlt => ?_⟩
    have hlt₂ : chainAction a X < δ₂ := lt_of_lt_of_le hlt (min_le_left _ _)
    have hlt₃ : chainAction a X < a * d ^ 2 / 4 := lt_of_lt_of_le hlt (min_le_right _ _)
    obtain ⟨lp, ln⟩ := hlow X hX hlt₂
    have hV := hX.2 m h.le
    have hpl : ∀ p, ComplexMatrix2.operatorNorm
        (PeriodicLattice.plaquetteHolonomy (levelField X m) p - 1) < δ₁ :=
      fun p => lt_of_lt_of_le (lp m le_rfl p) (min_le_right _ _)
    have hone := hstep _ hV hpl (fun _ => 1) (fun _ => ComplexMatrix2.specialUnitary.one_mem)
      (fun _ => by simpa using hδ₁)
    have hlen : ∀ c : Tower.PositiveEdge L n k (m + 1),
        ‖meanRadius (levelField X m) c.1 - 1‖ < min ε (1 / 2) := hone.1
    have hnoise : ∀ c : Tower.PositiveEdge L n k (m + 1), ‖X.noise ⟨m, h⟩ c - 1‖ < d := by
      intro c
      have hr : 1 / 2 ≤ (meanRadius (levelField X m) c.1).re := by
        have h1 := lt_of_lt_of_le (hlen c) (min_le_right _ _)
        have h2 := Complex.abs_re_le_norm (meanRadius (levelField X m) c.1 - 1)
        have h3 := abs_le.1 (h2.trans h1.le)
        simp only [Complex.sub_re, Complex.one_re] at h3
        linarith [h3.1]
      have hnr : X.noise ⟨m, h⟩ c ∈ PeriodicLattice.compactGaugeGroup := hX.1 _ _
      have he := traceDefect_nonneg hnr
      have ht := noiseTerm_le_chainAction ha hX ⟨m, h⟩ c
      have ht' : a * ((meanRadius (levelField X m) c.1).re * traceDefect (X.noise ⟨m, h⟩ c)) ≤
          chainAction a X := ht
      have h5 : (1 / 2) * traceDefect (X.noise ⟨m, h⟩ c) ≤
          (meanRadius (levelField X m) c.1).re * traceDefect (X.noise ⟨m, h⟩ c) :=
        mul_le_mul_of_nonneg_right hr he
      have h6 : a * ((1 / 2) * traceDefect (X.noise ⟨m, h⟩ c)) ≤ chainAction a X :=
        (mul_le_mul_of_nonneg_left h5 ha.le).trans ht'
      have h7 : 2 * traceDefect (X.noise ⟨m, h⟩ c) < d ^ 2 := by
        have : a * (2 * traceDefect (X.noise ⟨m, h⟩ c)) < a * d ^ 2 := by linarith
        exact lt_of_mul_lt_mul_left this ha.le
      have h8 := norm_sub_one_sq hnr
      rw [← h8] at h7
      exact lt_of_pow_lt_pow_left₀ 2 hdp.le h7
    have hgood := hstep _ hV hpl (X.noise ⟨m, h⟩) (hX.1 ⟨m, h⟩) (fun c =>
      lt_of_lt_of_le (hnoise c) (min_le_left _ _))
    refine ⟨fun j hj p => ?_, fun i hi c => ?_⟩
    · rcases Nat.lt_or_ge j (m + 1) with h' | h'
      · exact lt_of_lt_of_le (lp j (by omega) p) (min_le_left _ _)
      · obtain rfl : j = m + 1 := by omega
        rw [levelField_succ X h]
        exact lt_of_lt_of_le (hgood.2 p) (min_le_left _ _)
    · rcases Nat.lt_or_ge (i : ℕ) m with h' | h'
      · have := ln i h' c
        exact ⟨lt_of_lt_of_le this.1 (min_le_left _ _), lt_of_lt_of_le this.2 (min_le_left _ _)⟩
      · obtain rfl : i = ⟨m, h⟩ := by
          ext
          simp only
          omega
        exact ⟨lt_of_lt_of_le (hnoise c) (min_le_right _ _),
          lt_of_lt_of_le (hlen c) (min_le_left _ _)⟩
end Parts
section TopNoise
variable {L n k' : ℕ} [NeZero L]
def topNoisePoint (W : Tower.Edge L n (k' + 1) (k' + 1) → ComplexMatrix2) : ChainPoint L n (k' + 1) :=
  ⟨fun _ => 1, fun i => 1 + Pi.single (M := fun i : Fin (k' + 1) =>
    Tower.PositiveEdge L n (k' + 1) (i + 1) → ComplexMatrix2) (Fin.last k') (fun c => W c.1 - 1) i⟩
theorem topNoisePoint_noise_of_ne (W : Tower.Edge L n (k' + 1) (k' + 1) → ComplexMatrix2)
    {i : Fin (k' + 1)} (hi : i ≠ Fin.last k') (c : Tower.PositiveEdge L n (k' + 1) (i + 1)) :
    (topNoisePoint W).noise i c = 1 := by
  simp [topNoisePoint, Pi.single_eq_of_ne hi]
theorem topNoisePoint_noise_last (W : Tower.Edge L n (k' + 1) (k' + 1) → ComplexMatrix2)
    (c : Tower.PositiveEdge L n (k' + 1) (k' + 1)) :
    (topNoisePoint W).noise (Fin.last k') c = W c.1 := by
  simp [topNoisePoint]
theorem fieldOfPositiveValues_one {j : ℕ} :
    Tower.fieldOfPositiveValues (fun _ : Tower.PositiveEdge L n (k' + 1) j => (1 : ComplexMatrix2)) =
      fun _ => 1 := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · rw [fieldOfPositiveValues_pos _ hb]
  · rw [fieldOfPositiveValues_neg _ hb]
    simp
variable (hD : NormalizedMeanAtOne) (hL : Conventions.IsAdmissibleBlockingFactor L)
  (hn : 0 < n)
include hD hL hn
theorem levelField_topNoisePoint_of_le (W : Tower.Edge L n (k' + 1) (k' + 1) → ComplexMatrix2) :
    ∀ j, j ≤ k' → levelField (topNoisePoint W) j = fun _ => 1 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have h : j < k' + 1 := by omega
    have hne : (⟨j, h⟩ : Fin (k' + 1)) ≠ Fin.last k' := by
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
    rw [levelField_succ _ h, ih (by omega)]
    have e : (fun c : Tower.PositiveEdge L n (k' + 1) (j + 1) => (topNoisePoint W).noise ⟨j, h⟩ c *
        normalizedMean (fun _ : Tower.Edge L n (k' + 1) j => (1 : ComplexMatrix2)) c.1) =
        fun _ => 1 := by
      funext c
      rw [topNoisePoint_noise_of_ne W hne,
        (hD L hL n (k' + 1) j hn h 0 (Submodule.zero_mem _) c.1 c.2).2.2.1, one_mul]
    rw [e, fieldOfPositiveValues_one]
theorem levelField_topNoisePoint_top {W : Tower.Edge L n (k' + 1) (k' + 1) → ComplexMatrix2}
    (hW : W ∈ Tower.fieldSpace L n (k' + 1) (k' + 1)) :
    levelField (topNoisePoint W) (k' + 1) = W := by
  have h : k' < k' + 1 := Nat.lt_succ_self k'
  rw [levelField_succ _ h, levelField_topNoisePoint_of_le hD hL hn W k' le_rfl]
  funext b
  have hav : ∀ c : Tower.PositiveEdge L n (k' + 1) (k' + 1), (topNoisePoint W).noise ⟨k', h⟩ c *
      normalizedMean (fun _ : Tower.Edge L n (k' + 1) k' => (1 : ComplexMatrix2)) c.1 = W c.1 := by
    intro c
    rw [(hD L hL n (k' + 1) k' hn h 0 (Submodule.zero_mem _) c.1 c.2).2.2.1, mul_one]
    exact topNoisePoint_noise_last W c
  by_cases hb : b.IsPositivelyOriented
  · rw [fieldOfPositiveValues_pos _ hb, hav ⟨b, hb⟩]
  · rw [fieldOfPositiveValues_neg _ hb, hav]
    exact (hW.2 b.opposite (Set.mem_univ _)).symm
theorem topNoisePoint_isCompactValued (hxor : ∀ j, j ≤ k' + 1 → ∀ b : Tower.Edge L n (k' + 1) j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {W : Tower.Edge L n (k' + 1) (k' + 1) → ComplexMatrix2}
    (hW : W ∈ Tower.fieldSpace L n (k' + 1) (k' + 1)) :
    IsCompactValued (topNoisePoint W) := by
  have hone : ∀ j, (fun _ => (1 : ComplexMatrix2)) ∈ Tower.fieldSpace L n (k' + 1) j := fun j =>
    ⟨fun _ _ => one_mem _, fun _ _ => by simp⟩
  refine ⟨fun i c => ?_, fun j hj => ?_⟩
  · by_cases hi : i = Fin.last k'
    · subst hi
      rw [topNoisePoint_noise_last]
      exact hW.1 _ (Set.mem_univ _)
    · rw [topNoisePoint_noise_of_ne W hi]
      exact one_mem _
  · rcases Nat.lt_or_ge j (k' + 1) with h' | h'
    · rw [levelField_topNoisePoint_of_le hD hL hn W j (by omega)]
      exact hone j
    · obtain rfl : j = k' + 1 := by omega
      rw [levelField_topNoisePoint_top hD hL hn hW]
      exact hW
theorem chainAction_topNoisePoint (a : ℝ) {W : Tower.Edge L n (k' + 1) (k' + 1) → ComplexMatrix2} :
    chainAction a (topNoisePoint W) =
      a * ∑ c : Tower.PositiveEdge L n (k' + 1) (k' + 1), traceDefect (W c.1) := by
  have h1 : Tower.plaquetteAction L n (k' + 1) (topNoisePoint W).fine = 0 := by
    rw [plaquetteAction_eq_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    have e : PeriodicLattice.plaquetteHolonomy (topNoisePoint W).fine p = 1 := by
      simp [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy, topNoisePoint]
    rw [e, traceDefect_one]
  rw [chainAction_eq, h1, zero_add]
  congr 1
  rw [Finset.sum_eq_single (Fin.last k')]
  · refine Finset.sum_congr rfl fun c _ => ?_
    have h : k' < k' + 1 := Nat.lt_succ_self k'
    have e1 : meanRadius (levelField (topNoisePoint W) k') c.1 = 1 := by
      rw [levelField_topNoisePoint_of_le hD hL hn W k' le_rfl]
      exact (hD L hL n (k' + 1) k' hn h 0 (Submodule.zero_mem _) c.1 c.2).2.1
    have e1' : meanRadius (levelField (topNoisePoint W) (Fin.last k' : Fin (k' + 1))) c.1 = 1 := e1
    simp only [noiseTerm]
    rw [e1', topNoisePoint_noise_last]
    simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun c _ => ?_
    simp only [noiseTerm]
    rw [topNoisePoint_noise_of_ne W hi, traceDefect_one, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end TopNoise
section Top
open scoped Quaternion
variable {L n k : ℕ}
theorem exists_top_vertex (hlat : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (c : Tower.PositiveEdge L n k k) :
    ∃ (z : TorusFields.TorusSite (2 * L ^ n)) (μ : Fin 4),
      c.1 = PeriodicLattice.Bond.forwardFrom (topVertexOf z) μ := by apply _root_.YangMills.SharedProofs.p10565 <;> assumption
theorem traceDefect_quaternionToMatrix (q : ℍ[ℝ]) :
    traceDefect (SoftAverages.quaternionToMatrix q) = 1 - q.re := by apply _root_.YangMills.SharedProofs.p14120 <;> assumption
end Top
theorem xor_isPositive_opposite (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    {L n k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    ∀ j, j ≤ k → ∀ b : Tower.Edge L n k j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.RunningCouplingSlope.FibreActionProof.xor_isPositivelyOriented_opposite <;> assumption
theorem minimizerFieldsNearOne_holds (hD : NormalizedMeanAtOne)
    (hF : PeriodicLattice.FlatFieldsAndTheirAverages)
    (hlegs : AxisOrderLegsAreContours)
    (hcf : PeriodicLattice.BlockContoursAndCombs)
    (hbb : PeriodicLattice.BlocksBoxesPaths.Statement)
    (hb : PeriodicLattice.CrossingsAndBareBlocks.Statement)
    (hor : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (hlat : PeriodicLattice.CoordinateDescription) :
    MinimizerFieldsNearOne := by
  intro a ha L hL k n hk hn ε hε
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  have hxor : ∀ j, j ≤ k' + 1 → ∀ b : Tower.Edge L n (k' + 1) j,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := xor_isPositive_opposite hor hL hn
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_small_through_level hF hlegs hcf hbb hb hL hn hxor ha (k' + 1) le_rfl ε hε
  set N : ℝ := (Fintype.card (Tower.PositiveEdge L n (k' + 1) (k' + 1)) : ℝ) + 1 with hN
  have hNp : 0 < N := by positivity
  set η : ℝ := δ / (a * N) with hη
  have hηp : 0 < η := by positivity
  haveI : NeZero (2 * L ^ n) := ⟨by
    have := hL.2
    positivity⟩
  have hev : ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
      ∀ (z : TorusFields.TorusSite (2 * L ^ n)) (μ : Fin 4),
        1 - ((V z μ : BlockAverages.UnitQuaternion) : Quaternion ℝ).re < η := by
    refine eventually_all.2 fun z => eventually_all.2 fun μ => ?_
    have hc : Continuous fun V : TorusFields.TorusField (2 * L ^ n) =>
        1 - ((V z μ : BlockAverages.UnitQuaternion) : Quaternion ℝ).re :=
      continuous_const.sub (Quaternion.continuous_re.comp (continuous_subtype_val.comp
        ((continuous_apply μ).comp (continuous_apply z))))
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    have h1 : ((TorusFields.trivialField (2 * L ^ n) z μ : BlockAverages.UnitQuaternion) :
        Quaternion ℝ) = 1 :=
      rfl
    have h2 : (1 : Quaternion ℝ).re = 1 := rfl
    simp only [h1, h2, sub_self]
    exact hηp
  filter_upwards [hev] with V hV W hW X hLeast
  have hX : IsCompactValued X := hLeast.compact
  have hcomp := hLeast.le (topNoisePoint W) (topNoisePoint_isCompactValued hD hL hn hxor hW.1)
    (levelField_topNoisePoint_top hD hL hn hW.1)
  rw [chainAction_topNoisePoint hD hL hn] at hcomp
  have hterm : ∀ c : Tower.PositiveEdge L n (k' + 1) (k' + 1), traceDefect (W c.1) ≤ η := by
    intro c
    obtain ⟨z, μ, hz⟩ := exists_top_vertex hlat hL hn c
    rw [hz, hW.2 z μ, traceDefect_quaternionToMatrix]
    exact (hV z μ).le
  have hsum : (∑ c : Tower.PositiveEdge L n (k' + 1) (k' + 1), traceDefect (W c.1)) ≤
      (Fintype.card (Tower.PositiveEdge L n (k' + 1) (k' + 1)) : ℝ) * η := by
    have := Finset.sum_le_card_nsmul Finset.univ
      (fun c : Tower.PositiveEdge L n (k' + 1) (k' + 1) => traceDefect (W c.1)) η
      (fun c _ => hterm c)
    simpa using this
  have hlt : chainAction a X < δ := by
    have h1 : a * (N * η) = δ := by
      rw [hη]
      field_simp
    have h2 : a * (∑ c : Tower.PositiveEdge L n (k' + 1) (k' + 1), traceDefect (W c.1)) ≤
        a * ((Fintype.card (Tower.PositiveEdge L n (k' + 1) (k' + 1)) : ℝ) * η) :=
      mul_le_mul_of_nonneg_left hsum ha.le
    have h3 : 0 < a * η := by positivity
    have h4 : a * (N * η) =
        a * ((Fintype.card (Tower.PositiveEdge L n (k' + 1) (k' + 1)) : ℝ) * η) + a * η := by
      rw [hN]
      ring
    linarith
  obtain ⟨s1, s2⟩ := hsmall X hX hlt
  exact ⟨s1, fun i c => (s2 i i.2 c).1, fun i c => (s2 i i.2 c).2⟩
end YangMills.Construction.RunningCouplingSlope.MinimizerSmallness
end
