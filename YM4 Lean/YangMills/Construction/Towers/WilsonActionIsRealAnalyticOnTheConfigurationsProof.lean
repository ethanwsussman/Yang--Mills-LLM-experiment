import YangMills.Construction.Lattice.QuotientLatticesAndNeighbours
import YangMills.Construction.Lattice.WeightsAsFunctionsOfTheConfigurationAndSourcedIntegrals
import YangMills.Construction.Matrices.MatrixOperationsKeepHolomorphy
import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSets
import YangMills.Construction.Towers.SpacesOfFormsAtAFiniteSide
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction
namespace Tower
def WilsonActionAnalytic : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n →
    IsAnalyticFieldFunction (fieldSpace L n k 0) (plaquetteAction L n k)
end Tower
end YangMills.Construction
end

open Set Filter
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices Matrices.GroupLieProduct Matrices.GroupLieProduct.Subspaces Coordinates
namespace Tower.WilsonAnalyticity
theorem inv_eq_conjTranspose_of_mem_specialUnitary {U : ComplexMatrix2}
    (hU : U ∈ ComplexMatrix2.specialUnitary) : U⁻¹ = U.conjTranspose := by
  have hu := (Matrix.mem_specialUnitaryGroup_iff.mp hU).1
  exact Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hu)
theorem det_eq_one_of_mem_specialUnitary {U : ComplexMatrix2}
    (hU : U ∈ ComplexMatrix2.specialUnitary) : U.det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.mp hU).2
theorem inv_mem_specialUnitary {U : ComplexMatrix2}
    (hU : U ∈ ComplexMatrix2.specialUnitary) : U⁻¹ ∈ ComplexMatrix2.specialUnitary := by
  rw [inv_eq_conjTranspose_of_mem_specialUnitary hU]
  have hu := (Matrix.mem_specialUnitaryGroup_iff.mp hU)
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · exact Unitary.star_mem hu.1
  · rw [Matrix.det_conjTranspose, hu.2, star_one]
theorem fullTrace_im_eq_zero {U : ComplexMatrix2}
    (hU : U ∈ ComplexMatrix2.specialUnitary) : (ComplexMatrix2.fullTrace U).im = 0 := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.fullTrace_im_eq_zero_of_mem_specialUnitary <;> assumption
theorem isHolomorphicToCoords_firstEntry {ι κ : Type} [Fintype ι] [Fintype κ]
    {e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {S : Set (ι ⊕ κ → ComplexMatrix2)}
    {F : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hF : IsHolomorphicToCoords e ComplexCoordinates.matrixEquiv S F) :
    IsHolomorphicToCoords e (Equiv.refl (ComplexCoordinates 1)) S
      fun x _ => ComplexCoordinates.matrixEquiv (F x) 0 := by
  have hproj : Continuous fun z : ComplexCoordinates 4 => (fun _ : Fin 1 => z 0) :=
    continuous_pi fun _ => continuous_apply _
  obtain ⟨hS, hcont, hloc⟩ := hF
  refine ⟨hS, hproj.comp_continuousOn hcont, fun x hx => ?_⟩
  obtain ⟨V, hV0, hVo, hVt, hchart⟩ := hloc x hx
  refine ⟨V, hV0, hVo, hVt, fun i => ?_⟩
  obtain ⟨hopen, hc, hdiff⟩ := hchart i
  refine ⟨hopen, hproj.comp_continuousOn hc, fun a ha j => ?_⟩
  filter_upwards [hdiff a ha j] with z hz
  exact differentiableAt_pi.2 fun _ => differentiableAt_pi.1 hz 0
theorem isHolomorphicToMatrixEntries_finsetSum {ι κ J : Type} [Fintype ι] [Fintype κ]
    {e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {S : Set (ι ⊕ κ → ComplexMatrix2)}
    (hzero : IsHolomorphicToMatrixEntries e S fun _ => (0 : ComplexMatrix2))
    (hadd : ∀ F G : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2,
      IsHolomorphicToMatrixEntries e S F → IsHolomorphicToMatrixEntries e S G →
      IsHolomorphicToMatrixEntries e S fun x => F x + G x)
    (s : Finset J) {f : J → (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hf : ∀ j, IsHolomorphicToMatrixEntries e S (f j)) :
    IsHolomorphicToMatrixEntries e S fun x => ∑ j ∈ s, f j x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hzero
  | insert a s ha ih =>
    have hins : (fun x => ∑ j ∈ insert a s, f j x) = fun x => f a x + ∑ j ∈ s, f j x :=
      funext fun x => Finset.sum_insert ha
    rw [hins]
    exact hadd _ _ (hf a) ih
section Edges
variable {L n k : ℕ}
theorem isPositivelyOriented_or_opposite (b : Edge L n k 0) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ | hμ⟩ := b.isNeighbour
  · exact Or.inl ⟨μ, hμ⟩
  · refine Or.inr ⟨μ, ?_⟩
    change b.source - b.target = _
    rw [← neg_sub, hμ, neg_neg]
theorem not_opposite_isPositivelyOriented
    (hlat : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (b : Edge L n k 0)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, hμ⟩ := hb
  rintro ⟨ν, hν⟩
  have hnb := (hlat L hL n 0 k hn (Nat.zero_le k)).2.2.2.2.2.1
  have hstep : QuotientLattices.IsSignedAxisStep
      (QuotientLattices.torusAxisSteps L n k 0)
      (b.source : PeriodicLattice.FourTorus L n) (b.target : PeriodicLattice.FourTorus L n) 1 μ := by
    have hval := congrArg Subtype.val hμ
    simpa [QuotientLattices.IsSignedAxisStep, QuotientLattices.torusAxisSteps] using hval
  have hstep' : QuotientLattices.IsSignedAxisStep
      (QuotientLattices.torusAxisSteps L n k 0)
      (b.target : PeriodicLattice.FourTorus L n) (b.source : PeriodicLattice.FourTorus L n) 1 ν := by
    have hval := congrArg Subtype.val hν
    simpa [QuotientLattices.IsSignedAxisStep, QuotientLattices.torusAxisSteps,
      PeriodicLattice.Bond.opposite] using hval
  have hexcl := ((hnb.2.2 _ b.source.2 _ b.target.2).2 1 μ hstep).2
  rcases hexcl with ⟨-, hno⟩ | ⟨-, hno⟩
  · exact hno ⟨ν, hstep'⟩
  · exact hno ⟨μ, hstep⟩
theorem opposite_opposite (b : Edge L n k 0) : b.opposite.opposite = b :=
  PeriodicLattice.Bond.ext rfl rfl
theorem fieldOfPositiveValues_mem_fieldSpace
    (hnot : ∀ b : Edge L n k 0, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    {v : PositiveEdge L n k 0 → ComplexMatrix2}
    (hv : ∀ b, v b ∈ ComplexMatrix2.specialUnitary) :
    fieldOfPositiveValues v ∈ fieldSpace L n k 0 := by
  have hpos : ∀ {b : Edge L n k 0} (hb : b.IsPositivelyOriented),
      fieldOfPositiveValues v b = v ⟨b, hb⟩ :=
    fun hb => by simp [fieldOfPositiveValues, hb]
  have hneg : ∀ {b : Edge L n k 0} (hb : ¬ b.IsPositivelyOriented)
      (hb' : b.opposite.IsPositivelyOriented),
      fieldOfPositiveValues v b = (v ⟨b.opposite, hb'⟩)⁻¹ :=
    fun hb hb' => by simp [fieldOfPositiveValues, hb, hb']
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [hpos hb]
      exact hv _
    · rw [hneg hb ((isPositivelyOriented_or_opposite b).resolve_left hb)]
      exact inv_mem_specialUnitary (hv _)
  · by_cases hb : b.IsPositivelyOriented
    · have hbb : b.opposite.opposite.IsPositivelyOriented := by rwa [opposite_opposite]
      rw [hneg (hnot b hb) hbb, hpos hb]
      congr 2
    · have hb' := (isPositivelyOriented_or_opposite b).resolve_left hb
      rw [hneg hb hb', hpos hb']
      have hunit : IsUnit (v ⟨b.opposite, hb'⟩).det := by
        rw [det_eq_one_of_mem_specialUnitary (hv _)]
        exact isUnit_one
      exact (Matrix.nonsing_inv_nonsing_inv _ hunit).symm
theorem restrictToPositiveEdges_fieldOfPositiveValues (v : PositiveEdge L n k 0 → ComplexMatrix2) :
    restrictToPositiveEdges (fieldOfPositiveValues v) = v := by
  funext ⟨c, hc⟩
  simp [fieldOfPositiveValues, restrictToPositiveEdges, hc]
theorem isOpenFieldSet_fieldSpace (hprod : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    IsOpenFieldSet PeriodicLattice.compactGaugeGroup (fieldSpace L n k 0) := by
  have hopen := ((hprod L hL k 0 (Nat.zero_le k)).1 n hn).2.2.2.2.2.2.2.2.1
  exact ⟨subset_rfl, (hopen _ subset_rfl).1 ⟨univ, isOpen_univ, by simp⟩⟩
end Edges
section Analyticity
variable {L n k : ℕ} [Fintype (PositiveEdge L n k 0)] [Fintype (Face L n k 0)]
def faceProductAt (f : Face L n k 0) (x : PositiveEdge L n k 0 ⊕ Empty → ComplexMatrix2) :
    ComplexMatrix2 :=
  (((PeriodicLattice.Plaquette.boundaryBonds f).map
    (fieldOfPositiveValues (groupComponent x))).prod)
def negHalfTraceScalar : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 :=
  (-(1 / 2 : ℂ)) • (Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight (1 : ComplexMatrix2)
def matrixActionAt (L n k : ℕ) [Fintype (Face L n k 0)]
    (x : PositiveEdge L n k 0 ⊕ Empty → ComplexMatrix2) : ComplexMatrix2 :=
  ∑ f : Face L n k 0, ((1 : ComplexMatrix2) + negHalfTraceScalar (faceProductAt f x))
theorem isHolomorphic_matrixActionAt (hclos : HolomorphyClosureStatement)
    (e : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    IsHolomorphicToMatrixEntries e (GroupLieProduct (PositiveEdge L n k 0) Empty)
      (matrixActionAt L n k) := by
  have hS : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveEdge L n k 0) Empty)
      (GroupLieProduct (PositiveEdge L n k 0) Empty) := ⟨univ, isOpen_univ, by simp⟩
  obtain ⟨hconst, hcoord, hadd, hmul, hlin, hinv, -, -, -, -, -⟩ := hclos _ _ e _ hS
  have hedge : ∀ c : Edge L n k 0, IsHolomorphicToMatrixEntries e
      (GroupLieProduct (PositiveEdge L n k 0) Empty)
      fun x => fieldOfPositiveValues (groupComponent x) c := by
    intro c
    by_cases hc : c.IsPositivelyOriented
    · have hfun : (fun x : PositiveEdge L n k 0 ⊕ Empty → ComplexMatrix2 =>
          fieldOfPositiveValues (groupComponent x) c) = fun x => x (.inl ⟨c, hc⟩) := by
        funext x
        simp [fieldOfPositiveValues, hc, groupComponent]
      rw [hfun]
      exact hcoord _
    · by_cases hc' : c.opposite.IsPositivelyOriented
      · have hfun : (fun x : PositiveEdge L n k 0 ⊕ Empty → ComplexMatrix2 =>
            fieldOfPositiveValues (groupComponent x) c) =
            fun x => (x (.inl ⟨c.opposite, hc'⟩))⁻¹ := by
          funext x
          simp [fieldOfPositiveValues, hc, hc', groupComponent]
        rw [hfun]
        refine hinv _ (hcoord _) fun x hx => ?_
        have hdet : (x (.inl ⟨c.opposite, hc'⟩)).det = 1 := hx (.inl ⟨c.opposite, hc'⟩)
        rw [hdet]
        exact isUnit_one
      · have hfun : (fun x : PositiveEdge L n k 0 ⊕ Empty → ComplexMatrix2 =>
            fieldOfPositiveValues (groupComponent x) c) = fun _ => 1 := by
          funext x
          simp [fieldOfPositiveValues, hc, hc']
        rw [hfun]
        exact hconst 1
  have hword : ∀ w : List (Edge L n k 0), IsHolomorphicToMatrixEntries e
      (GroupLieProduct (PositiveEdge L n k 0) Empty)
      fun x => (w.map (fieldOfPositiveValues (groupComponent x))).prod := by
    intro w
    induction w with
    | nil => simpa using hconst 1
    | cons c w ih => simpa only [List.map_cons, List.prod_cons] using hmul _ _ (hedge c) ih
  exact isHolomorphicToMatrixEntries_finsetSum (hconst 0) hadd Finset.univ
    fun f => hadd _ _ (hconst 1) (hlin negHalfTraceScalar _ (hword _))
omit [Fintype (PositiveEdge L n k 0)] in
theorem plaquetteAction_eq_finsetSum (A : Edge L n k 0 → ComplexMatrix2) :
    plaquetteAction L n k A = ∑ f : Face L n k 0,
      (1 - (1 / 2) * (ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy A f)).re) := by
  simp only [plaquetteAction, PeriodicLattice.wilsonAction, finsum_eq_sum_of_fintype,
    PeriodicLattice.plaquetteCost]
omit [Fintype (PositiveEdge L n k 0)] in
theorem matrixActionAt_firstEntry {x : PositiveEdge L n k 0 ⊕ Empty → ComplexMatrix2}
    (hx : fieldOfPositiveValues (groupComponent x) ∈ fieldSpace L n k 0) :
    ComplexCoordinates.matrixEquiv (matrixActionAt L n k x) 0 =
      (plaquetteAction L n k (fieldOfPositiveValues (groupComponent x)) : ℂ) := by
  have hidx : ComplexCoordinates.entryIndex.symm (0 : Fin 4) = ((0 : Fin 2), (0 : Fin 2)) := rfl
  have hterm : ∀ f : Face L n k 0,
      ((1 : ComplexMatrix2) + negHalfTraceScalar (faceProductAt f x)) 0 0 =
      ((1 - (1 / 2) * (ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy
        (fieldOfPositiveValues (groupComponent x)) f)).re : ℝ) : ℂ) := by
    intro f
    have hmem : PeriodicLattice.plaquetteHolonomy (fieldOfPositiveValues (groupComponent x)) f ∈
        ComplexMatrix2.specialUnitary := by
      refine Submonoid.list_prod_mem _ fun y hy => ?_
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hy
      exact hx.1 c (mem_univ c)
    have hre : ((ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy
        (fieldOfPositiveValues (groupComponent x)) f)).re : ℂ) =
        ComplexMatrix2.fullTrace (PeriodicLattice.plaquetteHolonomy
          (fieldOfPositiveValues (groupComponent x)) f) :=
      Complex.ext (by simp) (by simp [fullTrace_im_eq_zero hmem])
    have hprod : faceProductAt f x =
        PeriodicLattice.plaquetteHolonomy (fieldOfPositiveValues (groupComponent x)) f := rfl
    push_cast
    rw [hre, hprod]
    simp [negHalfTraceScalar, ComplexMatrix2.fullTrace]
    ring
  show (matrixActionAt L n k x) (ComplexCoordinates.entryIndex.symm 0).1
    (ComplexCoordinates.entryIndex.symm 0).2 = _
  rw [hidx, plaquetteAction_eq_finsetSum, matrixActionAt, Matrix.sum_apply]
  push_cast
  exact Finset.sum_congr rfl fun f _ => by simpa using hterm f
theorem isAnalyticFieldFunction_plaquetteAction (hclos : HolomorphyClosureStatement)
    (hopen : IsOpenFieldSet PeriodicLattice.compactGaugeGroup (fieldSpace L n k 0))
    (hnot : ∀ b : Edge L n k 0, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented) :
    IsAnalyticFieldFunction (fieldSpace L n k 0) (plaquetteAction L n k) := by
  refine ⟨hopen, inferInstance, ?_⟩
  have hsub : ∀ x : PositiveEdge L n k 0 ⊕ Empty → ComplexMatrix2, x ∈ subspaceTimesGroup ⊥ _ →
      fieldOfPositiveValues (groupComponent x) ∈ fieldSpace L n k 0 :=
    fun x hx => fieldOfPositiveValues_mem_fieldSpace hnot hx.2
  have hgrp : ∀ x : PositiveEdge L n k 0 ⊕ Empty → ComplexMatrix2,
      fieldOfPositiveValues (groupComponent x) ∈ fieldSpace L n k 0 →
      ∀ r, groupComponent x r ∈ ComplexMatrix2.specialUnitary := by
    intro x hx r
    have hr := hx.1 r.1 (mem_univ _)
    have hval : fieldOfPositiveValues (groupComponent x) r.1 = groupComponent x r :=
      congrFun (restrictToPositiveEdges_fieldOfPositiveValues (groupComponent x)) r
    rwa [hval] at hr
  refine ⟨⟨bot_le, univ, isOpen_univ, ?_⟩, fun y hy => ?_⟩
  · ext x
    exact ⟨fun hx => ⟨mem_univ _, Subsingleton.elim _ _, hgrp x hx⟩, fun hx => hsub x hx.2⟩
  · refine ⟨GroupLieProduct (PositiveEdge L n k 0) Empty, ?_, ⟨univ, isOpen_univ, by simp⟩,
      fun x hx => hsub x hx.2,
      fun x _ => ComplexCoordinates.matrixEquiv (matrixActionAt L n k x) 0, ?_, ?_⟩
    · rintro (r | z)
      · exact det_eq_one_of_mem_specialUnitary (hgrp y hy r)
      · exact z.elim
    · exact fun e => isHolomorphicToCoords_firstEntry (isHolomorphic_matrixActionAt hclos e)
    · intro x hx
      funext i
      exact matrixActionAt_firstEntry (hsub x hx.2)
end Analyticity
end Tower.WilsonAnalyticity
open Tower Tower.WilsonAnalyticity in
theorem Tower.wilsonActionAnalytic_holds
    (hforms : Tower.FiniteSideFormSpaces)
    (hlat : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hprod : Tower.BondSetFields.ProductStructureHolds)
    (hclos : Matrices.GroupLieProduct.HolomorphyClosureStatement) :
    Tower.WilsonActionAnalytic := by
  intro L n k hL hn
  obtain ⟨hfin, -⟩ := hforms L n k 0 hL hn (Nat.zero_le k)
  let _ : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
  have hfaces : Finite (Face L n k 0) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hf⟩ := (hlat L hL n 0 k hn (Nat.zero_le k)).2.1
    exact hf
  let _ : Fintype (Face L n k 0) := Fintype.ofFinite _
  exact isAnalyticFieldFunction_plaquetteAction hclos (isOpenFieldSet_fieldSpace hprod hL hn)
    (not_opposite_isPositivelyOriented (k := k) hlat hL hn)
end YangMills.Construction
end
