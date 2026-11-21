import YangMills.Construction.Towers.BlocksOfATowerProof
import YangMills.Construction.Towers.CovariantAveragesAtAPeriodicExtensionDescendProof
import YangMills.Construction.DirichletOperator.FactsOfTheSettingInLevelUnitsProof
import YangMills.Construction.Towers.AverageDifferentialIsLocalWithACounterpart
import YangMills.Construction.Towers.ChainOfTheComplexIterateDifferentials
import YangMills.Construction.Towers.ChainOfTheComplexIteratesAtTheSideInfinity
import YangMills.Construction.Towers.IterateDifferentialIsLocalWithACounterpart
import YangMills.Construction.Towers.IteratedAveragesOfAPeriodicExtension
import YangMills.Construction.Towers.PeriodicExtensionsOfFunctionsOfCells
import YangMills.Construction.Towers.ReverseOfAStraightPathOfATowerProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.IterDerivLocality
open YangMills.Construction.LocalKernels.Periodisation YangMills.Construction.Tower
theorem supNormVec_eq_norm (v : Fin 4 → ℝ) : TorusMetric.supNormVec v = ‖v‖ := by apply _root_.YangMills.Construction.LevelUnitFacts.supNormVec_eq_norm <;> assumption
theorem supNormVec_sub_le (a b c : Fin 4 → ℝ) :
    TorusMetric.supNormVec (a - c) ≤
      TorusMetric.supNormVec (a - b) + TorusMetric.supNormVec (b - c) := by apply _root_.YangMills.Construction.LocalKernels.PeriodicLiftDescent.supNormVec_sub_le <;> assumption
theorem meshAt_pos {L : ℕ} (hL : 0 < L) (k j : ℕ) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.meshAt_pos <;> assumption
theorem meshAt_succ {L : ℕ} (hL : 0 < L) (k j : ℕ) :
    meshAt L k (j + 1) = L * meshAt L k j := by apply _root_.YangMills.Construction.Tower.AxisPathReversal.meshAt_succ <;> assumption
section Composition
variable {k L n : ℕ} {A A' A'' : CellClass k}
theorem localWithCounterpart_comp {R R' R'' : ℝ} (hR : R + R' ≤ R'')
    {m₁ : ((CellClass.fullSpace L A).index → Matrices.ComplexMatrix2) →
      (CellClass.fullSpace L A').index → Matrices.ComplexMatrix2}
    {t₁ : ((CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2) →
      (CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2}
    {m₂ : ((CellClass.fullSpace L A').index → Matrices.ComplexMatrix2) →
      (CellClass.fullSpace L A'').index → Matrices.ComplexMatrix2}
    {t₂ : ((CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2) →
      (CellClass.quotSpace L n A'').index → Matrices.ComplexMatrix2}
    {m : ((CellClass.fullSpace L A).index → Matrices.ComplexMatrix2) →
      (CellClass.fullSpace L A'').index → Matrices.ComplexMatrix2}
    {t : ((CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2) →
      (CellClass.quotSpace L n A'').index → Matrices.ComplexMatrix2}
    (h₁ : IsLocalWithPeriodicCounterpart L n A A' R m₁ t₁)
    (h₂ : IsLocalWithPeriodicCounterpart L n A' A'' R' m₂ t₂)
    (hm : ∀ f ∈ (CellClass.fullSpace L A).complexSubmodule, m f = m₂ (m₁ f))
    (ht : ∀ f ∈ (CellClass.quotSpace L n A).complexSubmodule, t f = t₂ (t₁ f))
    (he : ∀ f ∈ (CellClass.quotSpace L n A).complexSubmodule,
      CellClass.periodicExtension L n A f ∈ (CellClass.fullSpace L A).complexSubmodule)
    (he' : ∀ f ∈ (CellClass.quotSpace L n A').complexSubmodule,
      CellClass.periodicExtension L n A' f ∈ (CellClass.fullSpace L A').complexSubmodule)
    (hv : ∀ (f : (CellClass.quotSpace L n A').index → Matrices.ComplexMatrix2)
      (c : Cell L k A'.level A'.cellType),
      CellClass.cellFn L A' (CellClass.periodicExtension L n A' f) c =
        CellClass.quotCellFn L n A' f (Cell.proj n c)) :
    IsLocalWithPeriodicCounterpart L n A A'' R'' m t := by
  refine ⟨⟨fun f hf => ?_, fun f hf g hg => ?_, fun z f hf => ?_, fun f hf g hg c'' H => ?_⟩,
    ⟨fun f hf => ?_, fun f hf g hg => ?_, fun z f hf => ?_⟩, fun f hf c'' => ?_⟩
  · rw [hm f hf]
    exact h₂.full.map_mem _ (h₁.full.map_mem f hf)
  · rw [hm _ (add_mem hf hg), hm f hf, hm g hg, h₁.full.map_add f hf g hg]
    exact h₂.full.map_add _ (h₁.full.map_mem f hf) _ (h₁.full.map_mem g hg)
  · rw [hm _ (Submodule.smul_mem _ z hf), hm f hf, h₁.full.map_smul z f hf]
    exact h₂.full.map_smul z _ (h₁.full.map_mem f hf)
  · rw [hm f hf, hm g hg]
    refine h₂.full.local_dependence _ (h₁.full.map_mem f hf) _ (h₁.full.map_mem g hg) c''
      fun c' hc' => ?_
    refine h₁.full.local_dependence f hf g hg c' fun c hc => H c ?_
    exact (supNormVec_sub_le _ (Cell.anchor c') _).trans ((add_le_add hc hc').trans hR)
  · rw [ht f hf]
    exact h₂.periodic.map_mem _ (h₁.periodic.map_mem f hf)
  · rw [ht _ (add_mem hf hg), ht f hf, ht g hg, h₁.periodic.map_add f hf g hg]
    exact h₂.periodic.map_add _ (h₁.periodic.map_mem f hf) _ (h₁.periodic.map_mem g hg)
  · rw [ht _ (Submodule.smul_mem _ z hf), ht f hf, h₁.periodic.map_smul z f hf]
    exact h₂.periodic.map_smul z _ (h₁.periodic.map_mem f hf)
  · have hE := he f hf
    have hT := h₁.periodic.map_mem f hf
    rw [hm _ hE, ht f hf, ← h₂.commutes (t₁ f) hT c'']
    refine h₂.full.local_dependence _ (h₁.full.map_mem _ hE) _ (he' _ hT) c'' fun c _ => ?_
    rw [h₁.commutes f hf c, hv]
end Composition
theorem iterDerivIsLocal_holds (h₁ : SmoothingDerivLocality.SmoothingDerivIsLocalWithCounterpart)
    (h₂ : Tower.ComplexIterDerivChain)
    (h₃ : Tower.FullSpace.ComplexIterChain)
    (h₄ : IterMeansOfLift.Claim)
    (h₅ : PeriodicLift.LiftProperties) : IterDerivIsLocal := by
  intro L hL k n hn hk U hU j
  have hLpos : 0 < L := by have := hL.2; omega
  have hW := (h₄ L hL k n hn hk U hU.1).1.1 hU
  have hF := (h₄ L hL k n hn hk U hU.1).2 hU
  induction j with
  | zero =>
    intro h
    have hid : ∀ f ∈ FullSpace.complexEdgeForms (meshAt L k 0),
        FullSpace.complexIterDeriv L k 0 (liftGaugeField L n k 0 U) f = f :=
      fun f hf => (h₃ L hL k _ hW f hf).1
    have hid' : ∀ f ∈ complexEdgeForms L n k 0, complexIterDeriv L n k 0 U f = f :=
      fun f hf => (h₂ L hL n k hn U hU f hf).1
    refine ⟨⟨fun f hf => ?_, fun f hf g hg => ?_, fun z f hf => ?_, fun f hf g hg c' H => ?_⟩,
      ⟨fun f hf => ?_, fun f hf g hg => ?_, fun z f hf => ?_⟩, fun f hf c' => ?_⟩
    · have e := hid f hf
      rw [e]
      exact hf
    · exact (hid _ (add_mem hf hg)).trans (congrArg₂ (· + ·) (hid f hf).symm (hid g hg).symm)
    · exact (hid _ (Submodule.smul_mem _ z hf)).trans (congrArg (z • ·) (hid f hf).symm)
    · rw [hid f hf, hid g hg]
      refine H c' ?_
      rw [sub_self, supNormVec_eq_norm, norm_zero]
      have := meshAt_pos hLpos k 0
      positivity
    · have e := hid' f hf
      rw [e]
      exact hf
    · exact (hid' _ (add_mem hf hg)).trans (congrArg₂ (· + ·) (hid' f hf).symm (hid' g hg).symm)
    · exact (hid' _ (Submodule.smul_mem _ z hf)).trans (congrArg (z • ·) (hid' f hf).symm)
    · have hE := (h₅ L hL k n hn (CellClass.edgeClass k 0 h)).1 f hf
      rw [hid _ hE, hid' f hf]
      exact (h₅ L hL k n hn (CellClass.edgeClass k 0 h)).2 f c'
  | succ j ih =>
    intro h
    have hj : j ≤ k := Nat.le_of_succ_le h
    have hR : 3 * meshAt L k j + 3 * meshAt L k (j + 1) / 2 ≤
        3 * meshAt L k (j + 1) := by
      have hp := meshAt_pos hLpos k j
      have h13 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
      rw [meshAt_succ hLpos]
      nlinarith
    refine localWithCounterpart_comp hR (ih hj) (h₁ L hL k n hn U hU j h) (fun f hf => ?_)
      (fun f hf => ?_) (h₅ L hL k n hn _).1 (h₅ L hL k n hn _).1 (h₅ L hL k n hn _).2
    · have e := (h₃ L hL k _ hW f hf).2.1 j h
      rw [e, hF j hj]
    · exact (h₂ L hL n k hn U hU f hf).2.1 j h
end YangMills.Construction.LocalKernels.IterDerivLocality
end
