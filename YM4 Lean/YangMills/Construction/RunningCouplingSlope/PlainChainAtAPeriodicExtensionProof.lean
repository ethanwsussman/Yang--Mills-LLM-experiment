import YangMills.Construction.RunningCouplingSlope.AdjointBlockAverageAtASmallConfiguration
import YangMills.Construction.RunningCouplingSlope.ContourDriftAtASmallConfiguration
import YangMills.Construction.RunningCouplingSlope.PlainChainAtAPeriodicExtension
import YangMills.Construction.RunningCouplingSlope.PlainDifferentialIsLocalWithACounterpart
import YangMills.Construction.RunningCouplingSlope.PlainMeanAlongTheQuotient
import YangMills.Construction.Towers.CovariantAveragesAtAPeriodicExtensionDescendProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.MeanChainAtLift
open Tower LocalKernels LocalKernels.Periodisation
section Calculus
variable {k : ℕ} {L n : ℕ} {A A' A'' : CellClass k}
private theorem cellFn_smul (z : ℂ) (f : (CellClass.fullSpace L A).index → Matrices.ComplexMatrix2)
    (c : Cell L k A.level A.cellType) :
    CellClass.cellFn L A (z • f) c = z • CellClass.cellFn L A f c := by
  obtain ⟨j, h, _ | _ | _⟩ := A <;> rfl
private theorem quotCellFn_smul (z : ℂ) (f : (CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2)
    (c : QuotientCell L n k A.level A.cellType) :
    CellClass.quotCellFn L n A (z • f) c = z • CellClass.quotCellFn L n A f c := by
  obtain ⟨j, h, _ | _ | _⟩ := A <;> rfl
private theorem supNormVec_sub_le (x y z : InfiniteLattice.AmbientSpace) :
    TorusMetric.supNormVec (x - z) ≤
      TorusMetric.supNormVec (x - y) + TorusMetric.supNormVec (y - z) := by apply _root_.YangMills.Construction.LocalKernels.PeriodicLiftDescent.supNormVec_sub_le <;> assumption
private theorem local_mono {R R' : ℝ} {m t} (h : IsLocalWithPeriodicCounterpart L n A A' R m t)
    (hR : R ≤ R') : IsLocalWithPeriodicCounterpart L n A A' R' m t := by apply _root_.YangMills.Construction.LocalKernels.PeriodicLiftDescent.local_mono <;> assumption
private def LiftsAgree (L n : ℕ) (A : CellClass k) : Prop :=
  (∀ f ∈ (CellClass.quotSpace L n A).complexSubmodule,
    CellClass.periodicExtension L n A f ∈ (CellClass.fullSpace L A).complexSubmodule) ∧
  ∀ (f : (CellClass.quotSpace L n A).index → Matrices.ComplexMatrix2) (c : Cell L k A.level A.cellType),
    CellClass.cellFn L A (CellClass.periodicExtension L n A f) c =
      CellClass.quotCellFn L n A f (Cell.proj n c)
private theorem local_comp {R₁ R₂ : ℝ} {m₁ t₁ m₂ t₂} (hE : LiftsAgree L n A)
    (hE' : LiftsAgree L n A')
    (h₁ : IsLocalWithPeriodicCounterpart L n A A' R₁ m₁ t₁)
    (h₂ : IsLocalWithPeriodicCounterpart L n A' A'' R₂ m₂ t₂) :
    IsLocalWithPeriodicCounterpart L n A A'' (R₁ + R₂) (fun f => m₂ (m₁ f)) (fun f => t₂ (t₁ f)) := by
  refine ⟨⟨fun f hf => h₂.1.map_mem _ (h₁.1.map_mem f hf), fun f hf g hg => ?_,
      fun z f hf => ?_, fun f hf g hg c'' hc => ?_⟩,
    ⟨fun f hf => h₂.periodic.map_mem _ (h₁.periodic.map_mem f hf), fun f hf g hg => ?_, fun z f hf => ?_⟩,
    fun f hf c'' => ?_⟩
  · rw [h₁.1.map_add f hf g hg,
      h₂.1.map_add _ (h₁.1.map_mem f hf) _ (h₁.1.map_mem g hg)]
  · rw [h₁.1.map_smul z f hf, h₂.1.map_smul z _ (h₁.1.map_mem f hf)]
  · refine h₂.1.local_dependence _ (h₁.1.map_mem f hf) _ (h₁.1.map_mem g hg) c'' fun c' hc' => ?_
    refine h₁.1.local_dependence f hf g hg c' fun c hd => hc c ?_
    exact (supNormVec_sub_le _ (Cell.anchor c') _).trans (add_le_add hd hc')
  · rw [h₁.periodic.map_add f hf g hg, h₂.periodic.map_add _ (h₁.periodic.map_mem f hf) _ (h₁.periodic.map_mem g hg)]
  · rw [h₁.periodic.map_smul z f hf, h₂.periodic.map_smul z _ (h₁.periodic.map_mem f hf)]
  · have hm := h₁.periodic.map_mem f hf
    have e : CellClass.cellFn L A'' (m₂ (m₁ (CellClass.periodicExtension L n A f))) c'' =
        CellClass.cellFn L A'' (m₂ (CellClass.periodicExtension L n A' (t₁ f))) c'' := by
      refine h₂.1.local_dependence _ (h₁.1.map_mem _ (hE.1 f hf)) _ (hE'.1 _ hm) c'' fun c' _ => ?_
      rw [h₁.commutes f hf c', hE'.2]
    exact e.trans (h₂.commutes _ hm c'')
private theorem local_add {R : ℝ} {m₁ t₁ m₂ t₂} (h₁ : IsLocalWithPeriodicCounterpart L n A A' R m₁ t₁)
    (h₂ : IsLocalWithPeriodicCounterpart L n A A' R m₂ t₂) :
    IsLocalWithPeriodicCounterpart L n A A' R (fun f => m₁ f + m₂ f) (fun f => t₁ f + t₂ f) := by apply _root_.YangMills.Construction.LocalKernels.PeriodicLiftDescent.local_add <;> assumption
private theorem local_smul {R : ℝ} {m t} (w : ℂ) (h : IsLocalWithPeriodicCounterpart L n A A' R m t) :
    IsLocalWithPeriodicCounterpart L n A A' R (fun f => w • m f) (fun f => w • t f) := by
  refine ⟨⟨fun f hf => Submodule.smul_mem _ w (h.1.map_mem f hf),
      fun f hf g hg => ?_, fun z f hf => ?_, fun f hf g hg c' hc => ?_⟩,
    ⟨fun f hf => Submodule.smul_mem _ w (h.periodic.map_mem f hf),
      fun f hf g hg => ?_, fun z f hf => ?_⟩, fun f hf c' => ?_⟩
  · simp only [h.1.map_add f hf g hg, smul_add]
  · simp only [h.1.map_smul z f hf]
    exact smul_comm w z _
  · rw [cellFn_smul, cellFn_smul, h.1.local_dependence f hf g hg c' hc]
  · simp only [h.periodic.map_add f hf g hg, smul_add]
  · simp only [h.periodic.map_smul z f hf]
    exact smul_comm w z _
  · rw [cellFn_smul, quotCellFn_smul, h.commutes f hf c']
private theorem real_smul_eq {ι : Type} (r : ℝ) (x : ι → Matrices.ComplexMatrix2) : r • x = (r : ℂ) • x := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
private theorem local_real_smul {R : ℝ} {m t} (r : ℝ) (h : IsLocalWithPeriodicCounterpart L n A A' R m t) :
    IsLocalWithPeriodicCounterpart L n A A' R (fun f => r • m f) (fun f => r • t f) := by
  have e₁ : (fun f => r • m f) = fun f => (r : ℂ) • m f := funext fun f => real_smul_eq r _
  have e₂ : (fun f => r • t f) = fun f => (r : ℂ) • t f := funext fun f => real_smul_eq r _
  rw [e₁, e₂]
  exact local_smul _ h
private theorem local_id (hE : LiftsAgree L n A) :
    IsLocalWithPeriodicCounterpart L n A A 0 (fun f => f) (fun f => f) := by
  refine ⟨⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun f _ g _ c' hc => hc c' ?_⟩,
    ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩, fun f _ c' => hE.2 f c'⟩
  simp [TorusMetric.supNormVec]
end Calculus
section Spacing
private theorem meshAt_pos {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
private theorem thirteen_mul_meshAt_le {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    13 * meshAt L k j ≤ meshAt L k (j + 1) := by apply _root_.YangMills.Construction.LocalKernels.PeriodicLiftDescent.thirteen_mul_meshAt_le <;> assumption
private theorem meshAt_le_one {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {k j : ℕ} (h : j ≤ k) :
    meshAt L k j ≤ 1 := by apply _root_.YangMills.Construction.LocalKernels.PeriodicLiftDescent.meshAt_le_one <;> assumption
private theorem twelve_lt_periodSide {L n : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    2 * (6 : ℝ) < (periodSide L n : ℝ) := by apply _root_.YangMills.Construction.LocalKernels.PeriodicLiftDescent.twelve_lt_periodSide <;> assumption
end Spacing
section Iterates
variable {L n k : ℕ}
private theorem link_pos_or_opposite_pos {a : ℝ} (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
private theorem normalizedMean_lift (hA : ContourMeanAlongProjection)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    (V : Edge L n k j → Matrices.ComplexMatrix2) {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented) :
    FullLattice.contourMean (liftGaugeField L n k j V) c =
        contourMean V (FullSpace.projEdge L n k (j + 1) c) ∧
      FullLattice.meanRadius (liftGaugeField L n k j V) c =
        meanRadius V (FullSpace.projEdge L n k (j + 1) c) ∧
      FullLattice.normalizedMean (liftGaugeField L n k j V) c =
        normalizedMean V (FullSpace.projEdge L n k (j + 1) c) := by
  have e := hA L hL n k j hn hj c hc (liftGaugeField L n k j V) V fun _ _ => rfl
  refine ⟨e, ?_, ?_⟩
  · unfold FullLattice.meanRadius meanRadius
    rw [e]
  · unfold FullLattice.normalizedMean normalizedMean FullLattice.meanRadius meanRadius
    rw [e]
private theorem meanIterate_succ (U : Edge L n k 0 → Matrices.ComplexMatrix2) {j : ℕ} (hj : j < k)
    (hP : ∀ b : Edge L n k (j + 1), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (b : Edge L n k (j + 1)) :
    meanIterate U (j + 1) b = open Classical in
      if b.IsPositivelyOriented then normalizedMean (meanIterate U j) b
      else (normalizedMean (meanIterate U j) b.opposite)⁻¹ := by
  classical
  show levelField (quietPoint U) (j + 1) b = _
  rw [levelField, dif_pos hj]
  unfold fieldOfPositiveValues
  by_cases hb : b.IsPositivelyOriented
  · simp [hb, quietPoint]
    rfl
  · have hr : b.opposite.IsPositivelyOriented := by
      rcases hP b with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hb
      · exact h
    simp [hb, hr, quietPoint]
    rfl
private theorem meanIterate_lift (hA : ContourMeanAlongProjection)
    (hQ : EdgeProjectionProperties)
    (hP : PeriodicLattice.LevelBondOrientationDichotomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (U : Edge L n k 0 → Matrices.ComplexMatrix2) :
    ∀ j ≤ k, FullLattice.meanIterate (liftGaugeField L n k 0 U) j =
      liftGaugeField L n k j (meanIterate U j) := by
  classical
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    have hj : j < k := h
    have hq := (hQ L n k (j + 1) hL hn h).1
    have hx : ∀ b : Edge L n k (j + 1), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun b => by
      rcases hP L n k hL hn (by omega) (j + 1) h b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨h₁, h₂⟩
      · exact Or.inr ⟨h₁, h₂⟩
    funext c
    show (if c.IsPositivelyOriented then FullLattice.normalizedMean (FullLattice.meanIterate _ j) c
      else (FullLattice.normalizedMean (FullLattice.meanIterate _ j) c.opposite)⁻¹) =
      meanIterate U (j + 1) (FullSpace.projEdge L n k (j + 1) c)
    rw [ih hj.le, meanIterate_succ U hj hx]
    by_cases hc : c.IsPositivelyOriented
    · have hcq := (hq c).2.2.1 hc
      rw [if_pos hc, if_pos hcq]
      exact (normalizedMean_lift hA hL hn hj _ hc).2.2
    · have hr := (link_pos_or_opposite_pos c).resolve_left hc
      have hrq : (FullSpace.projEdge L n k (j + 1) c).opposite.IsPositivelyOriented := by
        rw [(hq c).2.2.2]
        exact (hq c.opposite).2.2.1 hr
      have hnq : ¬(FullSpace.projEdge L n k (j + 1) c).IsPositivelyOriented := by
        rcases hx (FullSpace.projEdge L n k (j + 1) c) with ⟨-, h₂⟩ | ⟨-, h₂⟩
        · exact absurd hrq h₂
        · exact h₂
      rw [if_neg hc, if_neg hnq, (hq c).2.2.2, (normalizedMean_lift hA hL hn hj _ hr).2.2]
end Iterates
section Main
variable {L n k : ℕ}
private theorem fullCovDiff_congr {a : ℝ} {W W' : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → W b = W' b) :
    FullSpace.covDiff W = FullSpace.covDiff W' := by
  classical
  funext l b
  unfold FullSpace.covDiff FullSpace.extendOddly
  by_cases hb : b.IsPositivelyOriented
  · simp only [if_pos hb, h b hb]
  · simp only [if_neg hb, h b.opposite ((link_pos_or_opposite_pos b).resolve_left hb)]
private theorem covDiff_congr {j : ℕ} {W W' : Edge L n k j → Matrices.ComplexMatrix2}
    (hP : ∀ b : Edge L n k j, ¬ b.IsPositivelyOriented → b.opposite.IsPositivelyOriented)
    (h : ∀ b : Edge L n k j, b.IsPositivelyOriented → W b = W' b) :
    covDiff W = covDiff W' := by
  classical
  funext l b
  unfold covDiff extendOddly
  by_cases hb : b.IsPositivelyOriented
  · simp only [if_pos hb, h b hb]
  · simp only [if_neg hb, h b.opposite (hP b hb)]
theorem meanChainLiftsNearIdentity (h₀ : LocalLinearMapsPeriodize)
    (hE : PeriodicLift.LiftProperties)
    (hA : ContourMeanAlongProjection)
    (hQ : EdgeProjectionProperties)
    (hP : PeriodicLattice.LevelBondOrientationDichotomy)
    (hD : CovDiffLocality.CovDiffIsLocal)
    (ha : AdjointCubeAverageIsLocal)
    (hc : ContourLogDriftIsLocal)
    (hU : NormalizedMeanDifferentialPeriodizes) : MeanChainLiftsNearIdentity := by
  intro L hL
  obtain ⟨ρ, hρ, hdiff⟩ := hU L hL
  refine ⟨ρ, hρ, fun k n hk hn U hs => ?_⟩
  have hX : ∀ A : CellClass k, LiftsAgree L n A := fun A => hE L hL k n hn A
  have hit := meanIterate_lift hA hQ hP hL hn U
  have hpos := meshAt_pos hL k
  have hstep := thirteen_mul_meshAt_le hL k
  have hnext : ∀ (j : ℕ) (h : j + 1 ≤ k) (b : Edge L n k (j + 1)), b.IsPositivelyOriented →
      meanIterate U (j + 1) b = normalizedMean (meanIterate U j) b := by
    intro j h b hb
    have hx : ∀ b : Edge L n k (j + 1), Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := fun b => by
      rcases hP L n k hL hn (by omega) (j + 1) h b with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨h₁, h₂⟩
      · exact Or.inr ⟨h₁, h₂⟩
    rw [meanIterate_succ U h hx, if_pos hb]
  have hrev : ∀ (j : ℕ), j ≤ k → ∀ b : Edge L n k j, ¬ b.IsPositivelyOriented → b.opposite.IsPositivelyOriented := by
    intro j h b hb
    rcases hP L n k hL hn (by omega) j h b with ⟨h₁, -⟩ | ⟨h₁, -⟩
    · exact absurd h₁ hb
    · exact h₁
  have hcirc : ∀ (j : ℕ) (h : j + 1 ≤ k),
      IsLocalWithPeriodicCounterpart L n (CellClass.edgeClass k j (Nat.le_of_succ_le h))
        (CellClass.edgeClass k (j + 1) h) (5 * meshAt L k (j + 1) / 2)
        (FullLattice.meanCovariantStep (liftGaugeField L n k j (meanIterate U j)))
        (meanCovariantStep (meanIterate U j)) := by
    intro j h
    have hj : j < k := h
    have hp := hpos (j + 1)
    have h₁ := hdiff k n hn j h _ (hs.mem_complexGroup j hj.le) (hs.norm_sub_one_lt j hj)
    have h₂ := hc L hL k n hn U hs.mem_smallIterate j h _ (hs.mem_smallComplex j hj)
    have h₃ := hD L hL k n hn (j + 1) h _ (hs.mem_complexGroup (j + 1) h)
    have hsum := local_add
      (local_mono h₁
        (show 3 * meshAt L k (j + 1) / 2 ≤ 5 * meshAt L k (j + 1) / 2 by linarith))
      (local_mono (local_comp (hX _) (hX _) h₂ h₃)
        (show 3 * meshAt L k (j + 1) / 2 + meshAt L k (j + 1) ≤
          5 * meshAt L k (j + 1) / 2 by linarith))
    have e₁ : FullLattice.meanCovariantStep (liftGaugeField L n k j (meanIterate U j)) =
        fun B => FullLattice.normalizedMeanDifferential
            (liftGaugeField L n k j (meanIterate U j)) B +
          FullSpace.covDiff (liftGaugeField L n k (j + 1)
            (meanIterate U (j + 1)))
            (FullSpace.contourLogDrift (liftGaugeField L n k j (meanIterate U j)) B) := by
      funext B
      have e : FullSpace.covDiff (FullLattice.normalizedMean
            (liftGaugeField L n k j (meanIterate U j))) =
          FullSpace.covDiff (liftGaugeField L n k (j + 1)
            (meanIterate U (j + 1))) := by
        refine fullCovDiff_congr fun b hb => ?_
        rw [(normalizedMean_lift hA hL hn hj _ hb).2.2]
        exact (hnext j h _ (((hQ L n k (j + 1) hL hn h).1 b).2.2.1 hb)).symm
      show FullLattice.normalizedMeanDifferential _ B + FullSpace.covDiff (FullLattice.normalizedMean _) _ = _
      rw [e]
    have e₂ : meanCovariantStep (meanIterate U j) = fun B =>
        holLeftDifferential normalizedMean (meanIterate U j) B +
          covDiff (meanIterate U (j + 1)) (contourLogDrift (meanIterate U j) B) := by
      funext B
      have e : covDiff (normalizedMean (meanIterate U j)) =
          covDiff (meanIterate U (j + 1)) :=
        covDiff_congr (hrev (j + 1) h) fun b hb => (hnext j h b hb).symm
      show _ + covDiff (normalizedMean _) _ = _
      rw [e]
    rw [e₁, e₂]
    exact hsum
  have hcov : ∀ (j : ℕ) (h : j ≤ k),
      IsLocalWithPeriodicCounterpart L n (CellClass.edgeClass k 0 (Nat.zero_le k))
        (CellClass.edgeClass k j h) (5 * meshAt L k j)
        (FullLattice.meanCovariant (liftGaugeField L n k 0 U) j)
        (meanCovariant U j) := by
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
      have e : FullLattice.meanCovariant (liftGaugeField L n k 0 U) (j + 1) =
          fun B => FullLattice.meanCovariantStep
            (liftGaugeField L n k j (meanIterate U j))
            (FullLattice.meanCovariant (liftGaugeField L n k 0 U) j B) := by
        funext B
        show FullLattice.meanCovariantStep (FullLattice.meanIterate _ j) _ = _
        rw [hit j (Nat.le_of_succ_le h)]
      rw [e]
      exact local_mono hcmp (by linarith)
  have hav : ∀ (j : ℕ) (h : j ≤ k),
      IsLocalWithPeriodicCounterpart L n (CellClass.vertexClass k 0 (Nat.zero_le k))
        (CellClass.vertexClass k j h) (meshAt L k j)
        (FullLattice.meanCubeAverage (liftGaugeField L n k 0 U) j)
        (composedCubeAverage (quietPoint U) j) := by
    intro j
    induction j with
    | zero =>
      intro h
      have hp := hpos 0
      exact local_mono (local_id (hX _)) hp.le
    | succ j ih =>
      intro h
      have hj : j < k := h
      have h₁ := hstep j
      have hp := hpos j
      have hcmp := local_comp (hX _) (hX _) (ih (Nat.le_of_succ_le h))
        (ha L hL k n hn j h _ (hs.mem_smallComplex j hj))
      have e : FullLattice.meanCubeAverage (liftGaugeField L n k 0 U) (j + 1) =
          fun l => FullSpace.adjointCubeAverage
            (liftGaugeField L n k j (meanIterate U j))
            (FullLattice.meanCubeAverage (liftGaugeField L n k 0 U) j l) := by
        funext l
        show FullSpace.adjointCubeAverage (FullLattice.meanIterate _ j) _ = _
        rw [hit j (Nat.le_of_succ_le h)]
      rw [e]
      exact local_mono hcmp (by linarith)
  have h6 := twelve_lt_periodSide hL hn
  refine ⟨hit, fun j hj c hcp => ?_, fun j h => ?_, ?_, ?_⟩
  · rw [hit j hj.le]
    exact (normalizedMean_lift hA hL hn hj _ hcp).2.1
  · have hone := meshAt_le_one hL h
    rw [hit j (Nat.le_of_succ_le h)]
    exact h₀ L hL k n hn _ _ (by simp [CellClass.edgeClass]) (by simp [CellClass.edgeClass]) 6
      (by norm_num) h6 _ _ (local_mono (local_real_smul _ (hcirc j h)) (by linarith))
  · have hone := meshAt_le_one hL (le_refl k)
    exact h₀ L hL k n hn _ _ (by simp [edgesAtZero, CellClass.edgeClass])
      (by simp [CellClass.edgeClass]) 6 (by norm_num) h6 _ _
      (local_mono (local_real_smul _ (hcov k le_rfl)) (by linarith))
  · have hone := meshAt_le_one hL (le_refl k)
    exact h₀ L hL k n hn _ _ (by simp [verticesAtZero, CellClass.vertexClass])
      (by simp [CellClass.vertexClass]) 6 (by norm_num) h6 _ _
      (local_mono (hav k le_rfl) (by linarith))
end Main
end YangMills.Construction.RunningCouplingSlope.MeanChainAtLift
end
