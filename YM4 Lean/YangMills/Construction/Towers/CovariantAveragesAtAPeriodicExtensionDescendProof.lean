import YangMills.Construction.RunningCouplingSlope.NormsOfThePlainProductsProof
import YangMills.Construction.Towers.AdjointBlockAverageIsLocalWithACounterpart
import YangMills.Construction.Towers.AverageDifferentialIsLocalWithACounterpart
import YangMills.Construction.Towers.ContourDriftIsLocalWithACounterpart
import YangMills.Construction.Towers.CovariantAveragesAtAPeriodicExtensionDescend
import YangMills.Construction.Towers.CovariantDifferenceIsLocalWithACounterpart
import YangMills.Construction.Towers.IterateDifferentialIsLocalWithACounterpart
import YangMills.Construction.Towers.IteratedAveragesOfAPeriodicExtension
import YangMills.Construction.Towers.IteratesOfSmallConfigurationsAreInTheComplexGroup
import YangMills.Construction.Towers.PeriodicExtensionsOfFunctionsOfCells
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels.PeriodicLiftDescent
open Periodisation Tower
section Calculus
variable {k : ℕ} {L n : ℕ} {A A' A'' : CellClass k}
theorem cellFn_add (f g : (CellClass.fullSpace L A).index → Matrices.ComplexMatrix2)
    (c : Cell L k A.level A.cellType) :
    CellClass.cellFn L A (f + g) c =
      CellClass.cellFn L A f c + CellClass.cellFn L A g c := by
  obtain ⟨j, h, _ | _ | _⟩ := A <;> rfl
theorem cellFn_zero (c : Cell L k A.level A.cellType) :
    CellClass.cellFn L A (0 : (CellClass.fullSpace L A).index → Matrices.ComplexMatrix2) c = 0 := by
  obtain ⟨j, h, _ | _ | _⟩ := A <;> rfl
theorem quotCellFn_add (f g : (CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2)
    (c : QuotientCell L n k A.level A.cellType) :
    CellClass.quotCellFn L n A (f + g) c =
      CellClass.quotCellFn L n A f c + CellClass.quotCellFn L n A g c := by
  obtain ⟨j, h, _ | _ | _⟩ := A <;> rfl
theorem quotCellFn_zero (c : QuotientCell L n k A.level A.cellType) :
    CellClass.quotCellFn L n A (0 : (CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2) c = 0 := by
  obtain ⟨j, h, _ | _ | _⟩ := A <;> rfl
theorem supNormVec_sub_le (x y z : InfiniteLattice.AmbientSpace) :
    TorusMetric.supNormVec (x - z) ≤
      TorusMetric.supNormVec (x - y) + TorusMetric.supNormVec (y - z) := by
  have e : ∀ v : InfiniteLattice.AmbientSpace, TorusMetric.supNormVec v = ‖v‖ := fun v => by
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun μ _ => ?_
      simpa [Real.norm_eq_abs] using norm_le_pi_norm v μ
    · refine (pi_norm_le_iff_of_nonneg ?_).mpr fun μ => ?_
      · exact (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
      · rw [Real.norm_eq_abs]
        exact Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ)
  rw [e, e, e]
  calc ‖x - z‖ = ‖(x - y) + (y - z)‖ := by rw [sub_add_sub_cancel]
    _ ≤ _ := norm_add_le _ _
theorem local_mono {R R' : ℝ} {m t} (h : IsLocalWithPeriodicCounterpart L n A A' R m t) (hR : R ≤ R') :
    IsLocalWithPeriodicCounterpart L n A A' R' m t :=
  ⟨⟨h.full.map_mem, h.full.map_add, h.full.map_smul, fun f hf g hg c' hc =>
      h.full.local_dependence f hf g hg c' fun c hd => hc c (hd.trans hR)⟩, h.periodic, h.commutes⟩
def ExtensionsCompatible (L n : ℕ) (A : CellClass k) : Prop :=
  (∀ f ∈ (CellClass.quotSpace L n A).complexSubmodule,
    CellClass.periodicExtension L n A f ∈ (CellClass.fullSpace L A).complexSubmodule) ∧
  ∀ (f : (CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2) (c : Cell L k A.level A.cellType),
    CellClass.cellFn L A (CellClass.periodicExtension L n A f) c =
      CellClass.quotCellFn L n A f (Cell.proj n c)
theorem local_comp {R₁ R₂ : ℝ} {m₁ t₁ m₂ t₂} (hE : ExtensionsCompatible L n A)
    (hE' : ExtensionsCompatible L n A')
    (h₁ : IsLocalWithPeriodicCounterpart L n A A' R₁ m₁ t₁)
    (h₂ : IsLocalWithPeriodicCounterpart L n A' A'' R₂ m₂ t₂) :
    IsLocalWithPeriodicCounterpart L n A A'' (R₁ + R₂) (fun f => m₂ (m₁ f)) (fun f => t₂ (t₁ f)) := by
  refine ⟨⟨fun f hf => h₂.full.map_mem _ (h₁.full.map_mem f hf), fun f hf g hg => ?_,
      fun z f hf => ?_, fun f hf g hg c'' hc => ?_⟩,
    ⟨fun f hf => h₂.periodic.map_mem _ (h₁.periodic.map_mem f hf), fun f hf g hg => ?_,
      fun z f hf => ?_⟩,
    fun f hf c'' => ?_⟩
  · rw [h₁.full.map_add f hf g hg,
      h₂.full.map_add _ (h₁.full.map_mem f hf) _ (h₁.full.map_mem g hg)]
  · rw [h₁.full.map_smul z f hf, h₂.full.map_smul z _ (h₁.full.map_mem f hf)]
  · refine h₂.full.local_dependence _ (h₁.full.map_mem f hf) _ (h₁.full.map_mem g hg) c''
      fun c' hc' => ?_
    refine h₁.full.local_dependence f hf g hg c' fun c hd => hc c ?_
    exact (supNormVec_sub_le _ (Cell.anchor c') _).trans (add_le_add hd hc')
  · rw [h₁.periodic.map_add f hf g hg,
      h₂.periodic.map_add _ (h₁.periodic.map_mem f hf) _ (h₁.periodic.map_mem g hg)]
  · rw [h₁.periodic.map_smul z f hf, h₂.periodic.map_smul z _ (h₁.periodic.map_mem f hf)]
  · have hm := h₁.periodic.map_mem f hf
    have e : CellClass.cellFn L A'' (m₂ (m₁ (CellClass.periodicExtension L n A f))) c'' =
        CellClass.cellFn L A'' (m₂ (CellClass.periodicExtension L n A' (t₁ f))) c'' := by
      refine h₂.full.local_dependence _ (h₁.full.map_mem _ (hE.1 f hf)) _ (hE'.1 _ hm) c''
        fun c' _ => ?_
      rw [h₁.commutes f hf c', hE'.2]
    exact e.trans (h₂.commutes _ hm c'')
theorem local_add {R : ℝ} {m₁ t₁ m₂ t₂} (h₁ : IsLocalWithPeriodicCounterpart L n A A' R m₁ t₁)
    (h₂ : IsLocalWithPeriodicCounterpart L n A A' R m₂ t₂) :
    IsLocalWithPeriodicCounterpart L n A A' R (fun f => m₁ f + m₂ f) (fun f => t₁ f + t₂ f) := by
  refine ⟨⟨fun f hf => Submodule.add_mem _ (h₁.full.map_mem f hf) (h₂.full.map_mem f hf),
      fun f hf g hg => ?_, fun z f hf => ?_, fun f hf g hg c' hc => ?_⟩,
    ⟨fun f hf => Submodule.add_mem _ (h₁.periodic.map_mem f hf) (h₂.periodic.map_mem f hf),
      fun f hf g hg => ?_, fun z f hf => ?_⟩, fun f hf c' => ?_⟩
  · simp only [h₁.full.map_add f hf g hg, h₂.full.map_add f hf g hg]; abel
  · simp only [h₁.full.map_smul z f hf, h₂.full.map_smul z f hf, smul_add]
  · rw [cellFn_add, cellFn_add, h₁.full.local_dependence f hf g hg c' hc,
      h₂.full.local_dependence f hf g hg c' hc]
  · simp only [h₁.periodic.map_add f hf g hg, h₂.periodic.map_add f hf g hg]; abel
  · simp only [h₁.periodic.map_smul z f hf, h₂.periodic.map_smul z f hf, smul_add]
  · rw [cellFn_add, quotCellFn_add, h₁.commutes f hf c', h₂.commutes f hf c']
theorem local_zero {R : ℝ} : IsLocalWithPeriodicCounterpart L n A A' R (fun _ => 0) (fun _ => 0) := by
  refine ⟨⟨fun _ _ => Submodule.zero_mem _, fun _ _ _ _ => (add_zero 0).symm,
      fun z _ _ => (smul_zero z).symm, fun _ _ _ _ _ _ => rfl⟩,
    ⟨fun _ _ => Submodule.zero_mem _, fun _ _ _ _ => (add_zero 0).symm,
      fun z _ _ => (smul_zero z).symm⟩, fun _ _ c' => ?_⟩
  rw [cellFn_zero, quotCellFn_zero]
theorem local_id (hE : ExtensionsCompatible L n A) :
    IsLocalWithPeriodicCounterpart L n A A 0 (fun f => f) (fun f => f) := by
  refine ⟨⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun f _ g _ c' hc => hc c' ?_⟩,
    ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩, fun f _ c' => hE.2 f c'⟩
  simp [TorusMetric.supNormVec]
end Calculus
section Spacing
theorem meshAt_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < Tower.meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem meshAt_succ {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    Tower.meshAt L k (j + 1) = L * Tower.meshAt L k j := by apply _root_.YangMills.SharedProofs.p23229 <;> assumption
theorem thirteen_mul_meshAt_le {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    13 * Tower.meshAt L k j ≤ Tower.meshAt L k (j + 1) := by
  rw [meshAt_succ hL]
  have : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  exact mul_le_mul_of_nonneg_right this (meshAt_pos hL k j).le
theorem meshAt_le_one {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {k j : ℕ} (h : j ≤ k) :
    Tower.meshAt L k j ≤ 1 := by
  have h1 : (1 : ℝ) ≤ L := by
    have : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
    linarith
  exact zpow_le_one_of_nonpos₀ h1 (by omega)
theorem twelve_lt_periodSide {L n : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    2 * (6 : ℝ) < (periodSide L n : ℝ) := by
  have h13 : 13 ≤ L := hL.2
  have : L ≤ L ^ n := Nat.le_self_pow (by omega) L
  have h : 13 ≤ L ^ n := h13.trans this
  have h' : (13 : ℝ) ≤ ((L ^ n : ℕ) : ℝ) := by exact_mod_cast h
  unfold periodSide
  push_cast at h' ⊢
  linarith
end Spacing
section Main
theorem covariantMeansDescend_holds (h₀ : Periodisation.LocalLinearMapsPeriodize)
    (hE : PeriodicLift.LiftProperties)
    (hit : IterMeansOfLift.Claim)
    (hD : CovDiffLocality.CovDiffIsLocal)
    (hG : SmallIterates.SmallIteratesInComplexGaugeGroup)
    (ha : AdjointCubeAverageIsLocalPeriodic)
    (hc : ContourDriftLocality.ContourLogDriftIsLocal)
    (hQ : SmoothingDerivLocality.SmoothingDerivIsLocalWithCounterpart)
    (hI : IterDerivLocality.IterDerivIsLocal) : CovariantMeansDescend := by
  intro L hL k n hn hk U hU hs
  have hX : ∀ A : CellClass k, ExtensionsCompatible L n A := fun A => hE L hL k n hn A
  have hB : ComplexIterLift L n k U := (hit L hL k n hn hk U hU).2 hs
  have hpos := meshAt_pos hL k
  have hstep := thirteen_mul_meshAt_le hL k
  have hblock : ∀ (j : ℕ) (h : j + 1 ≤ k),
      IsLocalWithPeriodicCounterpart L n (CellClass.vertexClass k j (Nat.le_of_succ_le h))
        (CellClass.vertexClass k (j + 1) h) (Tower.meshAt L k (j + 1) / 2)
        (Tower.FullSpace.adjointCubeAverage
          (Tower.FullSpace.complexIter L k j (liftGaugeField L n k 0 U)))
        (Tower.adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j U)) := by
    intro j h
    rw [hB j (Nat.le_of_succ_le h)]
    exact ha L hL k n hn U hs j h
  have hdrift : ∀ (j : ℕ) (h : j + 1 ≤ k),
      IsLocalWithPeriodicCounterpart L n (CellClass.edgeClass k j (Nat.le_of_succ_le h))
        (CellClass.vertexClass k (j + 1) h) (3 * Tower.meshAt L k (j + 1) / 2)
        (Tower.FullSpace.contourLogDrift
          (Tower.FullSpace.complexIter L k j (liftGaugeField L n k 0 U)))
        (Tower.contourLogDrift (PeriodicLattice.complexBlockFieldAtLevel j U)) := by
    intro j h
    rw [hB j (Nat.le_of_succ_le h)]
    exact hc L hL k n hn U hs j h
  have hcirc : ∀ (j : ℕ) (h : j + 1 ≤ k),
      IsLocalWithPeriodicCounterpart L n (CellClass.edgeClass k j (Nat.le_of_succ_le h))
        (CellClass.edgeClass k (j + 1) h) (5 * Tower.meshAt L k (j + 1) / 2)
        (Tower.FullSpace.covariantSmoothingDeriv
          (Tower.FullSpace.complexIter L k j (liftGaugeField L n k 0 U)))
        (Tower.covariantSmoothingDeriv (PeriodicLattice.complexBlockFieldAtLevel j U)) := by
    intro j h
    have hj := hB j (Nat.le_of_succ_le h)
    have hj' := hB (j + 1) h
    have hsm : Tower.FullSpace.smoothingMap L k j (liftGaugeField L n k j
        (PeriodicLattice.complexBlockFieldAtLevel j U)) = liftGaugeField L n k (j + 1)
          (PeriodicLattice.complexBlockFieldAtLevel (j + 1) U) := by
      rw [← hj, ← hj']
      rfl
    have hp := hpos (j + 1)
    have hsum := local_add
      (local_mono (hQ L hL k n hn U hs j h)
        (show 3 * Tower.meshAt L k (j + 1) / 2 ≤ 5 * Tower.meshAt L k (j + 1) / 2 by linarith))
      (local_mono (local_comp (hX _) (hX _) (hc L hL k n hn U hs j h)
          (hD L hL k n hn (j + 1) h _ (hG L hL k n hn hk U hs (j + 1) h)))
        (show 3 * Tower.meshAt L k (j + 1) / 2 + Tower.meshAt L k (j + 1) ≤
          5 * Tower.meshAt L k (j + 1) / 2 by linarith))
    rw [hj]
    have e₁ : Tower.FullSpace.covariantSmoothingDeriv (liftGaugeField L n k j
        (PeriodicLattice.complexBlockFieldAtLevel j U)) = fun B =>
          Tower.FullSpace.complexSmoothingDeriv (liftGaugeField L n k j
            (PeriodicLattice.complexBlockFieldAtLevel j U)) B +
          Tower.FullSpace.covDiff (liftGaugeField L n k (j + 1)
            (PeriodicLattice.complexBlockFieldAtLevel (j + 1) U))
            (Tower.FullSpace.contourLogDrift (liftGaugeField L n k j
              (PeriodicLattice.complexBlockFieldAtLevel j U)) B) := by
      funext B
      simp only [Tower.FullSpace.covariantSmoothingDeriv, hsm]
    rw [e₁]
    exact hsum
  have hcov : ∀ (j : ℕ) (h : j ≤ k),
      IsLocalWithPeriodicCounterpart L n (CellClass.edgeClass k 0 (Nat.zero_le k))
        (CellClass.edgeClass k j h) (5 * Tower.meshAt L k j)
        (Tower.FullSpace.iterCovariantDeriv L k (liftGaugeField L n k 0 U) j)
        (Tower.iterCovariantDeriv L n k U j) := by
    intro j
    induction j with
    | zero =>
      intro h
      have hp := hpos 0
      exact local_mono (local_id (hX _)) (by linarith)
    | succ j ih =>
      intro h
      have h₁ := hstep j
      have hp := hpos j
      have hcmp := local_comp (hX _) (hX _) (ih (Nat.le_of_succ_le h)) (hcirc j h)
      exact local_mono hcmp (by linarith)
  have hav : ∀ (j : ℕ) (h : j ≤ k),
      IsLocalWithPeriodicCounterpart L n (CellClass.vertexClass k 0 (Nat.zero_le k))
        (CellClass.vertexClass k j h) (Tower.meshAt L k j)
        (Tower.FullSpace.iterAdjointCubeAverage L k (liftGaugeField L n k 0 U) j)
        (Tower.iterAdjointCubeAverage L n k U j) := by
    intro j
    induction j with
    | zero =>
      intro h
      have hp := hpos 0
      exact local_mono (local_id (hX _)) hp.le
    | succ j ih =>
      intro h
      have h₁ := hstep j
      have hp := hpos j
      have hcmp := local_comp (hX _) (hX _) (ih (Nat.le_of_succ_le h)) (hblock j h)
      exact local_mono hcmp (by linarith)
  have hit' : ∀ (j : ℕ) (h : j ≤ k),
      IsLocalWithPeriodicCounterpart L n (CellClass.edgeClass k 0 (Nat.zero_le k))
        (CellClass.edgeClass k j h) (3 * Tower.meshAt L k j)
        (Tower.FullSpace.complexIterDeriv L k j (liftGaugeField L n k 0 U))
        (Tower.complexIterDeriv L n k j U) := hI L hL k n hn hk U hs
  have hdr : ∀ (j : ℕ) (h : j ≤ k),
      IsLocalWithPeriodicCounterpart L n (CellClass.edgeClass k 0 (Nat.zero_le k))
        (CellClass.vertexClass k j h) (5 * Tower.meshAt L k j)
        (Tower.FullSpace.iterContourLogDrift L k (liftGaugeField L n k 0 U) j)
        (Tower.iterContourLogDrift L n k U j) := by
    intro j
    induction j with
    | zero =>
      intro h
      exact local_zero
    | succ j ih =>
      intro h
      have h₁ := hstep j
      have hp := hpos j
      have hcmp₁ := local_comp (hX _) (hX _) (ih (Nat.le_of_succ_le h)) (hblock j h)
      have hcmp₂ := local_comp (hX _) (hX _) (hit' j (Nat.le_of_succ_le h)) (hdrift j h)
      have hsum := local_add
        (local_mono hcmp₁ (show _ ≤ 5 * Tower.meshAt L k (j + 1) by linarith))
        (local_mono hcmp₂ (show _ ≤ 5 * Tower.meshAt L k (j + 1) by linarith))
      exact hsum
  have h6 := twelve_lt_periodSide hL hn
  intro j h _
  have hone := meshAt_le_one hL h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h₀ L hL k n hn _ _ (by simp [edgesAtZero, CellClass.edgeClass])
      (by simp [CellClass.edgeClass]) 6 (by norm_num) h6 _ _
      (local_mono (hit' j h) (by linarith))
  · exact h₀ L hL k n hn _ _ (by simp [edgesAtZero, CellClass.edgeClass])
      (by simp [CellClass.edgeClass]) 6 (by norm_num) h6 _ _
      (local_mono (hcov j h) (by linarith))
  · exact h₀ L hL k n hn _ _ (by simp [verticesAtZero, CellClass.vertexClass])
      (by simp [CellClass.vertexClass]) 6 (by norm_num) h6 _ _
      (local_mono (hav j h) (by linarith))
  · exact h₀ L hL k n hn _ _ (by simp [edgesAtZero, CellClass.edgeClass])
      (by simp [CellClass.vertexClass]) 6 (by norm_num) h6 _ _
      (local_mono (hdr j h) (by linarith))
end Main
end YangMills.Construction.LocalKernels.PeriodicLiftDescent
end
