import YangMills.Construction.Towers.CommutatorTermAtAPeriodicExtensionDescendsProof
import YangMills.Construction.Towers.FunctionsOfTheCellsOfATowerAreReadAtTheirPlaces
import YangMills.Construction.Towers.IndexSetsArePeriodic
import YangMills.Construction.Towers.PeriodicExtensionsOfFunctionsOfCells
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.UnitScale.CellsReadAtPlaces
open OneStepChart
open LocalKernels
open LocalKernels.Periodisation
section AntisymmetricFunctions
variable {B : Type} (rev : B → B) (pos : B → Prop)
theorem exists_antisymm_extension (hrev : ∀ b, rev (rev b) = b) (hx : ∀ b, Xor (pos b) (pos (rev b)))
    (w : {b // pos b} → Matrices.ComplexMatrix2) :
    ∃ F : B → Matrices.ComplexMatrix2, (∀ b (h : pos b), F b = w ⟨b, h⟩) ∧ ∀ b, F (rev b) = -F b := by
  classical
  refine ⟨fun b => if h : pos b then w ⟨b, h⟩ else
    if h' : pos (rev b) then -w ⟨rev b, h'⟩ else 0, fun b h => dif_pos h, fun b => ?_⟩
  rcases hx b with ⟨hp, hn⟩ | ⟨hr, hn⟩
  · have hp' : pos (rev (rev b)) := by rwa [hrev]
    simp only [dif_pos hp, dif_neg hn, dif_pos hp']
    congr 2
    exact Subtype.ext (hrev b)
  · simp only [dif_pos hr, dif_neg hn, neg_neg]
theorem antisymm_eq_of_eqOn_pos (hx : ∀ b, Xor (pos b) (pos (rev b)))
    {f g : B → Matrices.ComplexMatrix2} (hf : ∀ b, f (rev b) = -f b) (hg : ∀ b, g (rev b) = -g b)
    (h : ∀ b, pos b → f b = g b) : f = g := by
  funext b
  rcases hx b with ⟨hp, _⟩ | ⟨hr, _⟩
  · exact h b hp
  · exact neg_injective (by rw [← hf, ← hg]; exact h _ hr)
end AntisymmetricFunctions
theorem isSlotEvaluation_pairedFunctions (ι : Type) :
    IsSlotEvaluation (Tower.pairedFunctions ι) ι (fun f => f) where
  eval_mem := fun _ hf p => Submodule.mem_pi.1 hf p (Set.mem_univ _)
  exists_eval_eq := fun w hw => ⟨w, Submodule.mem_pi.2 fun p _ => hw p, rfl⟩
  eq_of_eval_eq := fun _ _ _ _ h => h
  eval_add := fun _ _ _ _ => rfl
  eval_smul := fun _ _ _ => rfl
  isFinitelySupported_iff := fun _ _ => Iff.rfl
  pair_eq := fun _ _ => rfl
theorem xor_isPositivelyOriented_full {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
theorem xor_isPositivelyOriented_torus (hx : PeriodicLattice.LevelBondOrientationDichotomy) {L m k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k) (b : Tower.Edge L m k j) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p22685 <;> assumption
theorem isSlotEvaluation_fullForms {a : ℝ} (ha : 0 < a) :
    IsSlotEvaluation (FullSpace.edgePairedSpace a) (FullSpace.PositiveEdge a)
      FullSpace.restrictToPositiveEdges where
  eval_mem := fun _ hf p => hf.1 p.1 p.2
  exists_eval_eq := fun w hw => by
    obtain ⟨F, h₁, h₂⟩ := exists_antisymm_extension InfiniteLattice.Link.opposite
      InfiniteLattice.Link.IsPositivelyOriented (fun _ => rfl) (xor_isPositivelyOriented_full ha) w
    exact ⟨F, ⟨fun b hb => by rw [h₁ b hb]; exact hw _, h₂⟩, funext fun p => h₁ p.1 p.2⟩
  eq_of_eval_eq := fun f hf g hg h =>
    antisymm_eq_of_eqOn_pos InfiniteLattice.Link.opposite InfiniteLattice.Link.IsPositivelyOriented
      (xor_isPositivelyOriented_full ha) hf.2 hg.2 fun b hb => congrFun h ⟨b, hb⟩
  eval_add := fun _ _ _ _ => rfl
  eval_smul := fun _ _ _ => rfl
  isFinitelySupported_iff := fun _ _ => Iff.rfl
  pair_eq := fun _ _ => rfl
theorem isSlotEvaluation_torusForms (hx : PeriodicLattice.LevelBondOrientationDichotomy)
    {L m k j : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k) :
    IsSlotEvaluation (Tower.edgePairedSpace L m k j) (Tower.PositiveEdge L m k j)
      Tower.restrictToPositiveEdges where
  eval_mem := fun _ hf p => hf.1 p.1 p.2
  exists_eval_eq := fun w hw => by
    obtain ⟨F, h₁, h₂⟩ := exists_antisymm_extension
      (PeriodicLattice.Bond.opposite (j := PeriodicLattice.levelDepth k j))
      PeriodicLattice.Bond.IsPositivelyOriented (fun _ => rfl)
      (xor_isPositivelyOriented_torus hx hL hm hj) w
    exact ⟨F, ⟨fun b hb => by rw [h₁ b hb]; exact hw _, h₂⟩, funext fun p => h₁ p.1 p.2⟩
  eq_of_eval_eq := fun f hf g hg h =>
    antisymm_eq_of_eqOn_pos (PeriodicLattice.Bond.opposite (j := PeriodicLattice.levelDepth k j))
      PeriodicLattice.Bond.IsPositivelyOriented (xor_isPositivelyOriented_torus hx hL hm hj)
      hf.2 hg.2 fun b hb => congrFun h ⟨b, hb⟩
  eval_add := fun _ _ _ _ => rfl
  eval_smul := fun _ _ _ => rfl
  isFinitelySupported_iff := fun _ _ => Iff.rfl
  pair_eq := fun _ _ => rfl
section Translations
variable {L k j : ℕ}
theorem coe_integerPoint (hL : 0 < L) (hj : j ≤ k) (z : Fin 4 → ℤ) :
    ((integerPoint (Tower.meshAt L k j) z : InfiniteLattice.LatticePoint (Tower.meshAt L k j)) :
      InfiniteLattice.AmbientSpace) = PeriodicOperators.castVec z := by
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hex : ∃ x : InfiniteLattice.LatticePoint (Tower.meshAt L k j),
      (x : InfiniteLattice.AmbientSpace) = fun μ => (z μ : ℝ) := by
    refine ⟨⟨fun μ => (z μ : ℝ), fun μ => z μ * (L : ℤ) ^ (k - j), fun μ => ?_⟩, rfl⟩
    have e : (L : ℝ) ^ (k - j) * Tower.meshAt L k j = 1 := by
      rw [Tower.meshAt, ← zpow_natCast, ← zpow_add₀ hLr]
      simp [Nat.cast_sub hj]
    push_cast
    rw [mul_assoc, e, mul_one]
  exact Classical.epsilon_spec hex
theorem vertexImage_intShift (hL : 0 < L) (hj : j ≤ k) (z : Fin 4 → ℤ) (x : FullSpace.Vertex L k j) :
    FullSpace.vertexImage (PeriodicOperators.intShift z) x = x + integerPoint _ z := by
  have hex : ∃ x' : FullSpace.Vertex L k j,
      (x' : InfiniteLattice.AmbientSpace) = PeriodicOperators.intShift z x :=
    ⟨x + integerPoint _ z, by
      rw [AddSubgroup.coe_add, coe_integerPoint hL hj]; rfl⟩
  apply Subtype.ext
  refine (Classical.epsilon_spec hex).trans ?_
  rw [AddSubgroup.coe_add, coe_integerPoint hL hj]
  rfl
theorem linkTranslate_isPositivelyOriented {a : ℝ} {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) (z : InfiniteLattice.LatticePoint a) :
    (linkTranslate b z).IsPositivelyOriented := by
  obtain ⟨μ, h⟩ := hb
  exact ⟨μ, by simpa only [linkTranslate, add_sub_add_right_eq_sub] using h⟩
theorem coe_shiftEdge (hL : 0 < L) (hj : j ≤ k) (z : Fin 4 → ℤ)
    (b : PeriodicOperators.PosEdge L k j) :
    (PeriodicOperators.shiftEdge z b).1 = linkTranslate b.1 (integerPoint _ z) := by
  have h₁ : FullSpace.edgeImage (PeriodicOperators.intShift z) b.1 =
      linkTranslate b.1 (integerPoint _ z) := by
    have hex : ∃ c : FullSpace.Edge L k j,
        c.initial = FullSpace.vertexImage (PeriodicOperators.intShift z) b.1.initial ∧
        c.terminal = FullSpace.vertexImage (PeriodicOperators.intShift z) b.1.terminal :=
      ⟨linkTranslate b.1 (integerPoint _ z), (vertexImage_intShift hL hj z _).symm,
        (vertexImage_intShift hL hj z _).symm⟩
    have h := Classical.epsilon_spec hex
    exact InfiniteLattice.Link.ext (h.1.trans (vertexImage_intShift hL hj z _))
      (h.2.trans (vertexImage_intShift hL hj z _))
  have hex : ∃ c : PeriodicOperators.PosEdge L k j,
      c.1 = FullSpace.edgeImage (PeriodicOperators.intShift z) b.1 :=
    ⟨⟨_, linkTranslate_isPositivelyOriented b.2 (integerPoint _ z)⟩, h₁.symm⟩
  exact (Classical.epsilon_spec hex).trans h₁
end Translations
section CellTranslations
variable {L k j : ℕ}
theorem translate_isFreeAction (hI : LocalKernels.IndexSetPeriodicity.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) (c : LocalKernels.CellType) :
    (∀ p : LocalKernels.Cell L k j c, LocalKernels.Cell.translate 0 p = p) ∧
    (∀ (z z' : Fin 4 → ℤ) (p : LocalKernels.Cell L k j c),
      LocalKernels.Cell.translate (z + z') p =
        LocalKernels.Cell.translate z (LocalKernels.Cell.translate z' p)) ∧
    ∀ (z : Fin 4 → ℤ) (p : LocalKernels.Cell L k j c), LocalKernels.Cell.translate z p = p → z = 0 := by
  have hP := (hI L hL k).1 ⟨j, hj, c, false, 1, one_pos⟩
  refine ⟨fun p => hP.translate_zero p, fun z z' p => ?_, fun z p h => hP.free z p h⟩
  rw [add_comm]
  exact hP.translate_add z' z p
theorem finite_quotientCell (hc : LocalKernels.PeriodicLiftCells.CellsAndClassesHold) {m : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k)
    (c : LocalKernels.CellType) :
    Finite (LocalKernels.QuotientCell L m k j c) := by
  have h := ((hc L hL k m hm).2
    (LocalKernels.WeightedIndexSet.ofComponent ⟨j, hj, c, false, 1, one_pos⟩)).1
  have hs := (((hc L hL k m hm).1 j hj).1 c).1
  refine Finite.of_surjective (fun κ : (LocalKernels.WeightedIndexSet.ofComponent
    (⟨j, hj, c, false, 1, one_pos⟩ : LocalKernels.Component k)).ImageCarrier L m =>
      (κ.2.1 : LocalKernels.QuotientCell L m k j c)) ?_
  intro y
  obtain ⟨x, rfl⟩ := hs y
  exact ⟨⟨(), ⟨LocalKernels.Cell.proj m x, ⟨x, rfl⟩⟩⟩, rfl⟩
end CellTranslations
theorem vertex_cellEval (hc : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hE : LocalKernels.PeriodicLift.LiftProperties) (hI : LocalKernels.IndexSetPeriodicity.Statement)
    {L m k j : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k) :
    Nonempty (CellCoordinates (2 * L ^ m) (vertexFunctions L m k j)) := by
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨h0, h1, h2⟩ := translate_isFreeAction hI hL hj .vertex
  obtain ⟨hs, hq⟩ := ((hc L hL k m hm).1 j hj).1 .vertex
  obtain ⟨e1, e2⟩ := hE L hL k m hm ⟨j, hj, .vertex⟩
  exact ⟨{
    TorusSlot := Tower.Vertex L m k j
    torusEval := fun f => f
    proj := FullSpace.projVertex L m k j
    shiftSlot := fun z x => LocalKernels.Cell.translate (c := .vertex) z x
    full_basis := isSlotEvaluation_pairedFunctions _
    torus_coordinates := isSlotEvaluation_pairedFunctions _
    finite_torusSlot := finite_quotientCell hc hL hm hj .vertex
    extend_mem := e1
    eval_extend := fun f _ p => e2 f p
    proj_surjective := hs
    proj_eq_iff := hq
    shiftSlot_zero := h0
    shiftSlot_add := h1
    eq_zero_of_shiftSlot_eq := h2
    shift_mem := fun z f hf =>
      Submodule.mem_pi.2 fun x _ => Submodule.mem_pi.1 hf _ (Set.mem_univ _)
    eval_shift := fun z f _ p =>
      congrArg f (vertexImage_intShift hL0 hj (-z) p).symm }⟩
theorem edge_cellRepr (hc : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hE : LocalKernels.PeriodicLift.LiftProperties) (hI : LocalKernels.IndexSetPeriodicity.Statement)
    (hx : PeriodicLattice.LevelBondOrientationDichotomy)
    {L m k j : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k) :
    Nonempty (CellCoordinates (2 * L ^ m) (edgeForms L m k j)) := by
  have hL0 : 0 < L := by have := hL.2; omega
  have ha : 0 < Tower.meshAt L k j := zpow_pos (by exact_mod_cast hL0) _
  obtain ⟨h0, h1, h2⟩ := translate_isFreeAction hI hL hj .edge
  obtain ⟨hs, hq⟩ := ((hc L hL k m hm).1 j hj).1 .edge
  obtain ⟨e1, e2⟩ := hE L hL k m hm ⟨j, hj, .edge⟩
  exact ⟨{
    TorusSlot := Tower.PositiveEdge L m k j
    torusEval := Tower.restrictToPositiveEdges
    proj := LocalKernels.projPositiveEdge L m k j
    shiftSlot := fun z b => LocalKernels.Cell.translate (c := .edge) z b
    full_basis := isSlotEvaluation_fullForms ha
    torus_coordinates := isSlotEvaluation_torusForms hx hL hm hj
    finite_torusSlot := finite_quotientCell hc hL hm hj .edge
    extend_mem := e1
    eval_extend := fun f _ p => e2 f p
    proj_surjective := hs
    proj_eq_iff := hq
    shiftSlot_zero := h0
    shiftSlot_add := h1
    eq_zero_of_shiftSlot_eq := h2
    shift_mem := fun z f hf =>
      ⟨fun b hb => hf.1 _ (linkTranslate_isPositivelyOriented hb _), fun b => hf.2 (linkTranslate b _)⟩
    eval_shift := fun z f _ p =>
      congrArg f (coe_shiftEdge hL0 hj (-z) p).symm }⟩
theorem face_cellEval (hc : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hE : LocalKernels.PeriodicLift.LiftProperties) (hI : LocalKernels.IndexSetPeriodicity.Statement)
    {L m k j : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k) :
    Nonempty (CellCoordinates (2 * L ^ m) (faceFunctions L m k j)) := by
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨h0, h1, h2⟩ := translate_isFreeAction hI hL hj .face
  obtain ⟨hs, hq⟩ := ((hc L hL k m hm).1 j hj).1 .face
  obtain ⟨e1, e2⟩ := hE L hL k m hm ⟨j, hj, .face⟩
  exact ⟨{
    TorusSlot := Tower.Face L m k j
    torusEval := fun f => f
    proj := FullSpace.projFace L m k j
    shiftSlot := fun z p => LocalKernels.Cell.translate (c := .face) z p
    full_basis := isSlotEvaluation_pairedFunctions _
    torus_coordinates := isSlotEvaluation_pairedFunctions _
    finite_torusSlot := finite_quotientCell hc hL hm hj .face
    extend_mem := e1
    eval_extend := fun f _ p => e2 f p
    proj_surjective := hs
    proj_eq_iff := hq
    shiftSlot_zero := h0
    shiftSlot_add := h1
    eq_zero_of_shiftSlot_eq := h2
    shift_mem := fun z f hf =>
      Submodule.mem_pi.2 fun x _ => Submodule.mem_pi.1 hf _ (Set.mem_univ _)
    eval_shift := fun z f _ p =>
      congrArg f (InfiniteLattice.ElementaryPlaquette.ext
        (vertexImage_intShift hL0 hj (-z) (InfiniteLattice.ElementaryPlaquette.corner p)).symm
          rfl rfl) }⟩
theorem statement_holds (hc : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hE : LocalKernels.PeriodicLift.LiftProperties) (hI : LocalKernels.IndexSetPeriodicity.Statement)
    (hx : PeriodicLattice.LevelBondOrientationDichotomy) : Statement :=
  fun _ hL _ _ _ hm hj =>
    ⟨vertex_cellEval hc hE hI hL hm hj, edge_cellRepr hc hE hI hx hL hm hj,
      face_cellEval hc hE hI hL hm hj⟩
end YangMills.Construction.Tower.UnitScale.CellsReadAtPlaces
end
