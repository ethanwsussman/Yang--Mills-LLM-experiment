import YangMills.Construction.Torus.ProjectionsOfTheSequenceProof
import YangMills.Construction.Towers.CommutatorTermAtAPeriodicExtensionDescendsProof
import YangMills.Construction.Towers.CovariantDifferenceIsLocalWithACounterpart
import YangMills.Construction.Towers.TranslationsAndIsometriesOfATowerProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.CovDiffLocality
section EdgeFormula
variable {β σ : Type} (pos : β → Prop) (rev : β → β) (head tail : β → σ)
  (U : β → Matrices.ComplexMatrix2)
private def edgeDiff (l : σ → Matrices.ComplexMatrix2) : β → Matrices.ComplexMatrix2 :=
  open Classical in fun b =>
    if pos b then Matrices.ComplexMatrix2.conjugateBy (U b) (l (head b)) - l (tail b)
    else -(Matrices.ComplexMatrix2.conjugateBy (U (rev b)) (l (head (rev b))) - l (tail (rev b)))
private theorem conjugateBy_add (g X Y : Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.conjugateBy g (X + Y) =
      Matrices.ComplexMatrix2.conjugateBy g X + Matrices.ComplexMatrix2.conjugateBy g Y := by
  simp [Matrices.ComplexMatrix2.conjugateBy, mul_add, add_mul]
private theorem conjugateBy_smul (z : ℂ) (g X : Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.conjugateBy g (z • X) = z • Matrices.ComplexMatrix2.conjugateBy g X := by
  simp [Matrices.ComplexMatrix2.conjugateBy]
private theorem conjugateBy_mem_traceless (g : Matrices.ComplexMatrix2) {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    Matrices.ComplexMatrix2.conjugateBy g X ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.PeriodicLattice.conjugateBy_mem_traceless <;> assumption
private theorem edgeDiff_add (l l' : σ → Matrices.ComplexMatrix2) :
    edgeDiff pos rev head tail U (l + l') =
      edgeDiff pos rev head tail U l + edgeDiff pos rev head tail U l' := by
  funext b
  simp only [edgeDiff, Pi.add_apply, conjugateBy_add]
  split_ifs <;> abel
private theorem edgeDiff_smul (z : ℂ) (l : σ → Matrices.ComplexMatrix2) :
    edgeDiff pos rev head tail U (z • l) = z • edgeDiff pos rev head tail U l := by
  funext b
  simp only [edgeDiff, Pi.smul_apply, conjugateBy_smul]
  split_ifs <;> simp [smul_sub]
private theorem edgeDiff_of_pos (l : σ → Matrices.ComplexMatrix2) {b : β} (hb : pos b) :
    edgeDiff pos rev head tail U l b =
      Matrices.ComplexMatrix2.conjugateBy (U b) (l (head b)) - l (tail b) :=
  if_pos hb
private theorem edgeDiff_mem_traceless {l : σ → Matrices.ComplexMatrix2}
    (hl : ∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) {b : β} (hb : pos b) :
    edgeDiff pos rev head tail U l b ∈ Matrices.ComplexMatrix2.traceless := by
  rw [edgeDiff_of_pos pos rev head tail U l hb]
  exact Matrices.ComplexMatrix2.traceless.sub_mem (conjugateBy_mem_traceless _ (hl _)) (hl _)
private theorem edgeDiff_rev (hrr : ∀ b, rev (rev b) = b) (hx : ∀ b, Xor (pos b) (pos (rev b)))
    (l : σ → Matrices.ComplexMatrix2) (b : β) :
    edgeDiff pos rev head tail U l (rev b) = -edgeDiff pos rev head tail U l b := by
  unfold edgeDiff
  rcases hx b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [if_neg h₂, if_pos h₁, hrr]
  · rw [if_pos h₁, if_neg h₂, neg_neg]
end EdgeFormula
private theorem fullSpace_covDiff_of_pos {a : ℝ} (U : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) :
    Tower.FullSpace.covDiff U l b =
      Matrices.ComplexMatrix2.conjugateBy (U b) (l b.terminal) - l b.initial :=
  edgeDiff_of_pos (fun b : InfiniteLattice.Link a => b.IsPositivelyOriented) _ _ _ _ l hb
private theorem periodic_covDiff_of_pos {L n k j : ℕ} (U : Tower.Edge L n k j → Matrices.ComplexMatrix2)
    (l : Tower.Vertex L n k j → Matrices.ComplexMatrix2) {b : Tower.Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    Tower.covDiff U l b = Matrices.ComplexMatrix2.conjugateBy (U b) (l b.target) - l b.source := by apply _root_.YangMills.Construction.Tower.Translations.covDiff_of_pos <;> assumption
private theorem fullSpace_covDiff_congr {a : ℝ} (U : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (l l' : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented)
    (hHead : l b.terminal = l' b.terminal) (hTail : l b.initial = l' b.initial) :
    Tower.FullSpace.covDiff U l b = Tower.FullSpace.covDiff U l' b := by
  rw [fullSpace_covDiff_of_pos U l hb, fullSpace_covDiff_of_pos U l' hb, hHead, hTail]
private theorem covDiff_lift_eq {L n k j : ℕ} (hB : Periodisation.ProjEdgesCompatible L n k j)
    (V : Tower.Edge L n k j → Matrices.ComplexMatrix2) (l : Tower.Vertex L n k j → Matrices.ComplexMatrix2)
    (c : PeriodicOperators.PosEdge L k j) :
    Tower.FullSpace.covDiff (liftGaugeField L n k j V)
        (fun x => l (Tower.FullSpace.projVertex L n k j x)) c.1 =
      Tower.covDiff V l (projPositiveEdge L n k j c).1 := by
  have hEnds := hB.1 c.1
  rw [fullSpace_covDiff_of_pos _ _ c.2, periodic_covDiff_of_pos _ _ (projPositiveEdge L n k j c).2,
    hB.2.1 c, hEnds.1, hEnds.2]
  rfl
private theorem link_xor_opposite {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
private theorem edge_xor_opposite (hXor : PeriodicLattice.LevelBondOrientationDichotomy)
    {L n : ℕ} (k j : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (h : j ≤ k) :
    ∀ b : Tower.Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p22685 <;> assumption
private theorem supNormVec_single_le {a : ℝ} (ha : 0 ≤ a) (μ : Fin 4) :
    TorusMetric.supNormVec (Pi.single μ a) ≤ a := by apply _root_.YangMills.Construction.Weighted.ProjectionProof.supNormVec_single_le <;> assumption
private theorem supNormVec_zero_le {a : ℝ} (ha : 0 ≤ a) :
    TorusMetric.supNormVec (0 : Fin 4 → ℝ) ≤ a :=
  Finset.sup'_le _ _ fun ν _ => by simpa using ha
theorem covDiffIsLocal_holds (hCells : PeriodicLiftCells.CellsAndClassesHold)
    (hXor : PeriodicLattice.LevelBondOrientationDichotomy) : CovDiffIsLocal := by
  intro L hL k n hn j h V _
  have hB : Periodisation.ProjEdgesCompatible L n k j := ((hCells L hL k n hn).1 j h).2
  have hx := edge_xor_opposite (L := L) (n := n) hXor k j hL hn h
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  have ha : 0 < Tower.meshAt L k j := zpow_pos (by linarith) _
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    refine ⟨fun b hb => ?_, fun b => ?_⟩
    · exact edgeDiff_mem_traceless (fun b : InfiniteLattice.Link _ => b.IsPositivelyOriented) _ _ _ _
        (fun x => hf x trivial) hb
    · exact edgeDiff_rev (fun b : InfiniteLattice.Link _ => b.IsPositivelyOriented) _ _ _ _
        (fun _ => rfl) (link_xor_opposite ha) _ b
  · intro f _ g _
    exact edgeDiff_add _ _ _ _ _ f g
  · intro z f _
    exact edgeDiff_smul _ _ _ _ _ z f
  · intro f _ g _ c' hc
    let c : PeriodicOperators.PosEdge L k j := c'
    have hHead : f c.1.terminal = g c.1.terminal := by
      refine hc c.1.terminal ?_
      obtain ⟨μ, hμ⟩ := c.2
      have e : (c.1.terminal.1 - c.1.initial.1 : Fin 4 → ℝ) = Pi.single μ (Tower.meshAt L k j) :=
        congrArg Subtype.val hμ
      show TorusMetric.supNormVec (c.1.terminal.1 - c.1.initial.1) ≤ _
      rw [e]
      exact supNormVec_single_le ha.le μ
    have hTail : f c.1.initial = g c.1.initial := by
      refine hc c.1.initial ?_
      show TorusMetric.supNormVec (c.1.initial.1 - c.1.initial.1) ≤ _
      rw [sub_self]
      exact supNormVec_zero_le ha.le
    exact fullSpace_covDiff_congr _ f g c.2 hHead hTail
  · intro f hf
    refine ⟨fun b hb => ?_, fun b => ?_⟩
    · exact edgeDiff_mem_traceless (fun b : Tower.Edge L n k j => b.IsPositivelyOriented) _ _ _ _
        (fun x => hf x trivial) hb
    · exact edgeDiff_rev (fun b : Tower.Edge L n k j => b.IsPositivelyOriented) _ _ _ _
        (fun _ => rfl) hx _ b
  · intro f _ g _
    exact edgeDiff_add _ _ _ _ _ f g
  · intro z f _
    exact edgeDiff_smul _ _ _ _ _ z f
  · intro f _ c'
    exact covDiff_lift_eq hB V f c'
end YangMills.Construction.LocalKernels.CovDiffLocality
end
