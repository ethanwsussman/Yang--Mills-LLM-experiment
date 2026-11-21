import YangMills.Construction.Lattice.ActionOfABareGaugeTransformation
import YangMills.Construction.Towers.EntriesOfTheActionAndOfTheCovariantDifferenceProof
import YangMills.Construction.RunningCouplingSlope.TheCommutatorOfTheChainReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TheOtherConstraintReadsNearCellsProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.ChainBracketLocality
open Tower
open Matrices
section RowColumnBound
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq b]
private theorem norm_le_sqrt_of_row_col (A : Matrix a b ℂ) {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hrow : ∀ p, ∑ q, ‖A p q‖ ≤ R) (hcol : ∀ q, ∑ p, ‖A p q‖ ≤ S) :
    ‖A‖ ≤ Real.sqrt (R * S) := by apply _root_.YangMills.SharedProofs.p34885 <;> assumption
private theorem sum_le_card_mul_of_injOn {α β : Type} [Fintype α] [Fintype β] {f : α → ℝ}
    {T : α → Prop} {M : ℝ} (hM : 0 ≤ M) (label : α → β) (hf : ∀ x, ¬T x → f x = 0)
    (hb : ∀ x, f x ≤ M) (hinj : ∀ x y, T x → T y → label x = label y → x = y) :
    ∑ x, f x ≤ Fintype.card β * M := by
  classical
  have e : ∑ x, f x = ∑ x ∈ Finset.univ.filter T, f x := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun x _ => by
      by_cases h : T x
      · simp [h]
      · simp [h, hf x h]
  have c : (Finset.univ.filter T).card ≤ Fintype.card β := by
    refine Finset.card_le_card_of_injOn label (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
    intro x hx y hy h
    exact hinj x y (by simpa using hx) (by simpa using hy) h
  rw [e]
  calc ∑ x ∈ Finset.univ.filter T, f x ≤ (Finset.univ.filter T).card • M :=
        Finset.sum_le_card_nsmul _ _ _ fun x _ => hb x
    _ = ((Finset.univ.filter T).card : ℝ) * M := by simp
    _ ≤ Fintype.card β * M :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast c) hM
abbrev _root_.YangMills.SharedProofs.p48454 := @sum_le_card_mul_of_injOn
end RowColumnBound
private def pauliCombo (u : Fin 3 → ℂ) : ComplexMatrix2 :=
  ∑ a, u a • ComplexMatrix2.pauliFamily a
private def conjExp (A T : ComplexMatrix2) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (Complex.I • A) * T * ComplexMatrix2.matExp (-(Complex.I • A))
private def bracketEntry (J T D : ComplexMatrix2) : ℂ :=
  ComplexMatrix2.halfTrace (J * ((Complex.I / 2) • (T * D - D * T)))
private lemma bracketEntry_add_left (J T T' D : ComplexMatrix2) :
    bracketEntry J (T + T') D = bracketEntry J T D + bracketEntry J T' D := by
  have e : J * ((Complex.I / 2) • ((T + T') * D - D * (T + T'))) =
      J * ((Complex.I / 2) • (T * D - D * T)) + J * ((Complex.I / 2) • (T' * D - D * T')) := by
    rw [← mul_add, ← smul_add]
    congr 2
    noncomm_ring
  simp only [bracketEntry, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, e, Matrix.trace_add]
  ring
private lemma bracketEntry_add_right (J T D D' : ComplexMatrix2) :
    bracketEntry J T (D + D') = bracketEntry J T D + bracketEntry J T D' := by
  have e : J * ((Complex.I / 2) • (T * (D + D') - (D + D') * T)) =
      J * ((Complex.I / 2) • (T * D - D * T)) + J * ((Complex.I / 2) • (T * D' - D' * T)) := by
    rw [← mul_add, ← smul_add]
    congr 2
    noncomm_ring
  simp only [bracketEntry, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, e, Matrix.trace_add]
  ring
private lemma bracketEntry_smul_left (c : ℂ) (J T D : ComplexMatrix2) :
    bracketEntry J (c • T) D = c * bracketEntry J T D := by
  have e : J * ((Complex.I / 2) • ((c • T) * D - D * (c • T))) =
      c • (J * ((Complex.I / 2) • (T * D - D * T))) := by
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_comm c]
  simp only [bracketEntry, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, e, Matrix.trace_smul,
    smul_eq_mul]
  ring
private lemma bracketEntry_smul_right (c : ℂ) (J T D : ComplexMatrix2) :
    bracketEntry J T (c • D) = c * bracketEntry J T D := by
  have e : J * ((Complex.I / 2) • (T * (c • D) - (c • D) * T)) =
      c • (J * ((Complex.I / 2) • (T * D - D * T))) := by
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_comm c]
  simp only [bracketEntry, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, e, Matrix.trace_smul,
    smul_eq_mul]
  ring
private def bracketEntryLeft (J D : ComplexMatrix2) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun T := bracketEntry J T D
  map_add' := fun T T' => bracketEntry_add_left J T T' D
  map_smul' := fun c T => by simpa using bracketEntry_smul_left c J T D
private def bracketEntryRight (J T : ComplexMatrix2) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun D := bracketEntry J T D
  map_add' := fun D D' => bracketEntry_add_right J T D D'
  map_smul' := fun c D => by simpa using bracketEntry_smul_right c J T D
private def conjExpLinear (A : ComplexMatrix2) : ComplexMatrix2 →ₗ[ℂ] ComplexMatrix2 where
  toFun T := conjExp A T
  map_add' := fun T T' => by simp only [conjExp, mul_add, add_mul]
  map_smul' := fun c T => by simp only [conjExp, mul_smul_comm, smul_mul_assoc, RingHom.id_apply]
private lemma bracketEntry_pauliCombo (J D : ComplexMatrix2) (u : Fin 3 → ℂ) :
    bracketEntry J (pauliCombo u) D = ∑ a, u a * bracketEntry J (ComplexMatrix2.pauliFamily a) D := by
  change bracketEntryLeft J D (pauliCombo u) = _
  simp only [pauliCombo, map_sum, map_smul, smul_eq_mul]
  rfl
private lemma bracketEntry_conjExp_pauliCombo (J A D : ComplexMatrix2) (u : Fin 3 → ℂ) :
    bracketEntry J (conjExp A (pauliCombo u)) D =
      ∑ a, u a * bracketEntry J (conjExp A (ComplexMatrix2.pauliFamily a)) D := by
  change bracketEntryLeft J D (conjExpLinear A (pauliCombo u)) = _
  simp only [pauliCombo, map_sum, map_smul, smul_eq_mul]
  rfl
private lemma bracketEntry_pauliCombo_right (J T : ComplexMatrix2) (v : Fin 3 → ℂ) :
    bracketEntry J T (pauliCombo v) = ∑ d, v d * bracketEntry J T (ComplexMatrix2.pauliFamily d) := by
  change bracketEntryRight J T (pauliCombo v) = _
  simp only [pauliCombo, map_sum, map_smul, smul_eq_mul]
  rfl
private lemma bracketEntry_im_eq_zero {J T D : ComplexMatrix2} (hJ : J.conjTranspose = J)
    (hT : T.conjTranspose = T) (hD : D.conjTranspose = D) : (bracketEntry J T D).im = 0 := by
  set Y : ComplexMatrix2 := (Complex.I / 2) • (T * D - D * T) with hY
  have eY : Y.conjTranspose = Y := by
    rw [hY, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hT, hD]
    have : star (Complex.I / 2) = -(Complex.I / 2) := by
      simp [Complex.conj_I]
      ring
    rw [this, neg_smul, ← smul_neg, neg_sub]
  have e : star (Matrix.trace (J * Y)) = Matrix.trace (J * Y) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, eY, hJ, Matrix.trace_mul_comm]
  have h : (Matrix.trace (J * Y)).im = 0 := Complex.conj_eq_iff_im.1 e
  simp only [bracketEntry, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, ← hY]
  simp [Complex.mul_im, h]
private lemma conjTranspose_matExp {A : ComplexMatrix2} (hA : A.conjTranspose = A) :
    (ComplexMatrix2.matExp (Complex.I • A)).conjTranspose =
      ComplexMatrix2.matExp (-(Complex.I • A)) := by
  rw [ComplexMatrix2.matExp, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hA]
  simp [Complex.conj_I]
private lemma conjTranspose_conjExp {A T : ComplexMatrix2} (hA : A.conjTranspose = A)
    (hT : T.conjTranspose = T) : (conjExp A T).conjTranspose = conjExp A T := by
  have h : (ComplexMatrix2.matExp (-(Complex.I • A))).conjTranspose =
      ComplexMatrix2.matExp (Complex.I • A) := by
    rw [← conjTranspose_matExp hA, Matrix.conjTranspose_conjTranspose]
  rw [conjExp, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, h, conjTranspose_matExp hA, hT,
    mul_assoc]
private lemma conjugateBy_matExp (A T : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy (ComplexMatrix2.matExp (Complex.I • A)) T = conjExp A T := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValueFunctions.LocalComponents.conjugateBy_expI <;> assumption
private lemma eq_pauliCombo {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.hermitianTraceless)
    {u : Fin 3 → ℂ} (h : ∀ a, pauliCoeff a X = u a) : X = pauliCombo u := by
  have hs : X ∈ ComplexMatrix2.traceless := hX.2
  have s : ∀ c : Fin 3 → ℂ,
      ((OneLoop.pauliCoordinateEquiv.symm c : ComplexMatrix2.traceless) : ComplexMatrix2) =
      ∑ a, c a • ComplexMatrix2.pauliFamily a := fun c => by
    rw [Fin.sum_univ_three]
    rfl
  have e : ∀ a, pauliCoeff a X = OneLoop.pauliCoordinateEquiv ⟨X, hs⟩ a := fun a => by
    rw [pauliCoeff, dif_pos hs]
  have k : ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by
    simp only [e]
    rw [← s, LinearEquiv.symm_apply_apply]
  rw [pauliCombo, ← k]
  exact Finset.sum_congr rfl fun a _ => by rw [h a]
private def pauliComboCLM : (Fin 3 → ℂ) →L[ℂ] ComplexMatrix2 :=
  ∑ a, (ContinuousLinearMap.proj a : (Fin 3 → ℂ) →L[ℂ] ℂ).smulRight (ComplexMatrix2.pauliFamily a)
private lemma pauliComboCLM_apply (u : Fin 3 → ℂ) : pauliComboCLM u = pauliCombo u := by
  simp [pauliComboCLM, pauliCombo]
private def halfTraceCLM : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((1 / 2 : ℂ) • Matrix.traceLinearMap (Fin 2) ℂ ℂ)
private lemma halfTraceCLM_apply (X : ComplexMatrix2) :
    halfTraceCLM X = ComplexMatrix2.halfTrace X := by
  simp [halfTraceCLM, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
private abbrev CoeffPair : Type := (Fin 3 → ℂ) × (Fin 3 → ℂ)
private def sourceEntry (a d : Fin 3) (w : CoeffPair) : ℂ :=
  bracketEntry (pauliCombo w.1) (ComplexMatrix2.pauliFamily a) (ComplexMatrix2.pauliFamily d)
private def targetEntry (a d : Fin 3) (w : CoeffPair) : ℂ :=
  bracketEntry (pauliCombo w.1) (conjExp (pauliCombo w.2) (ComplexMatrix2.pauliFamily a))
    (ComplexMatrix2.pauliFamily d)
private lemma analyticAt_bracketEntry {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {J T D : E → ComplexMatrix2} {x : E} (hJ : AnalyticAt ℂ J x) (hT : AnalyticAt ℂ T x)
    (hD : AnalyticAt ℂ D x) : AnalyticAt ℂ (fun w => bracketEntry (J w) (T w) (D w)) x := by
  have h1 : AnalyticAt ℂ (fun w => J w * ((Complex.I / 2) • (T w * D w - D w * T w))) x :=
    hJ.mul (show AnalyticAt ℂ ((Complex.I / 2 : ℂ) • fun w => T w * D w - D w * T w) x from
      ((hT.mul hD).sub (hD.mul hT)).const_smul)
  have h2 := (halfTraceCLM.analyticAt _).comp h1
  exact h2.congr (Eventually.of_forall fun w => halfTraceCLM_apply _)
private lemma analyticAt_pauliCombo_fst (w : CoeffPair) :
    AnalyticAt ℂ (fun w : CoeffPair => pauliCombo w.1) w := by
  have h := (pauliComboCLM.comp (ContinuousLinearMap.fst ℂ (Fin 3 → ℂ) (Fin 3 → ℂ))).analyticAt w
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp [pauliComboCLM_apply]
private lemma analyticAt_pauliCombo_snd (w : CoeffPair) :
    AnalyticAt ℂ (fun w : CoeffPair => pauliCombo w.2) w := by
  have h := (pauliComboCLM.comp (ContinuousLinearMap.snd ℂ (Fin 3 → ℂ) (Fin 3 → ℂ))).analyticAt w
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp [pauliComboCLM_apply]
private lemma analyticAt_sourceEntry (a d : Fin 3) (w : CoeffPair) :
    AnalyticAt ℂ (sourceEntry a d) w :=
  analyticAt_bracketEntry (analyticAt_pauliCombo_fst w) analyticAt_const analyticAt_const
private lemma analyticAt_targetEntry (a d : Fin 3) (w : CoeffPair) :
    AnalyticAt ℂ (targetEntry a d) w := by
  have hs : AnalyticAt ℂ (fun w : CoeffPair => Complex.I • pauliCombo w.2) w :=
    show AnalyticAt ℂ ((Complex.I : ℂ) • fun w : CoeffPair => pauliCombo w.2) w from
      (analyticAt_pauliCombo_snd w).const_smul
  have e1 : AnalyticAt ℂ (fun w : CoeffPair => ComplexMatrix2.matExp (Complex.I • pauliCombo w.2)) w :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) (𝔸 := ComplexMatrix2) _).comp_of_eq hs rfl
  have e2 : AnalyticAt ℂ
      (fun w : CoeffPair => ComplexMatrix2.matExp (-(Complex.I • pauliCombo w.2))) w :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) (𝔸 := ComplexMatrix2) _).comp_of_eq hs.neg rfl
  exact analyticAt_bracketEntry (analyticAt_pauliCombo_fst w) ((e1.mul analyticAt_const).mul e2)
    analyticAt_const
private lemma exists_entry_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a d : Fin 3) (w : CoeffPair), ‖w‖ ≤ 1 →
    ‖sourceEntry a d w‖ ≤ K ∧ ‖targetEntry a d w‖ ≤ K := by
  let F : CoeffPair → (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ) := fun w =>
    (fun p => sourceEntry p.1 p.2 w, fun p => targetEntry p.1 p.2 w)
  have c1 : ∀ p : Fin 3 × Fin 3, Continuous (sourceEntry p.1 p.2) := fun p =>
    continuous_iff_continuousAt.2 fun w => (analyticAt_sourceEntry p.1 p.2 w).continuousAt
  have c2 : ∀ p : Fin 3 × Fin 3, Continuous (targetEntry p.1 p.2) := fun p =>
    continuous_iff_continuousAt.2 fun w => (analyticAt_targetEntry p.1 p.2 w).continuousAt
  have hF : Continuous F := (continuous_pi c1).prodMk (continuous_pi c2)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : CoeffPair) 1).exists_bound_of_continuousOn
    hF.continuousOn
  have h0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (by simp))
  refine ⟨K, h0, fun a d w hw => ?_⟩
  have h := hK w (by simpa using hw)
  have h1 : ‖(F w).1‖ ≤ K := (norm_fst_le _).trans h
  have h2 : ‖(F w).2‖ ≤ K := (norm_snd_le _).trans h
  exact ⟨(norm_le_pi_norm (F w).1 (a, d)).trans h1, (norm_le_pi_norm (F w).2 (a, d)).trans h2⟩
section Kernel
variable {L n k : ℕ}
private abbrev toFine {j : ℕ} (y : Vertex L n k j) : Vertex L n k 0 :=
  y.toSublattice (PeriodicLattice.levelDepth k 0)
private lemma toFine_self (x : Vertex L n k 0) : toFine x = x := by
  have h : ∃ y : Vertex L n k 0, (y : PeriodicLattice.FourTorus L n) = x := ⟨x, rfl⟩
  exact Subtype.ext (Classical.epsilon_spec h)
abbrev _root_.YangMills.DeltaSharedProofs.p39288 := @toFine_self
private lemma toFine_coe (hL : 0 < L) {j : ℕ} (y : Vertex L n k j) :
    ((toFine y : Vertex L n k 0) : PeriodicLattice.FourTorus L n) = y := by apply _root_.YangMills.Construction.PeriodicLattice.coe_toSublattice_finest <;> assumption
private lemma toFine_injective (hL : 0 < L) {j : ℕ} {y y' : Vertex L n k j}
    (h : toFine y = toFine y') : y = y' := by
  apply Subtype.ext
  rw [← toFine_coe hL y, ← toFine_coe hL y', h]
private def axisOf {j : ℕ} (b : PositiveEdge L n k j) : Fin 4 := b.2.choose
private lemma target_eq {j : ℕ} (b : PositiveEdge L n k j) :
    b.1.target = b.1.source + PeriodicLattice.unitStep L n _ (axisOf b) := by
  have h : b.1.target - b.1.source = PeriodicLattice.unitStep L n _ (axisOf b) := b.2.choose_spec
  rw [← h]
  abel
private lemma edge_ext_source {j : ℕ} {b b' : PositiveEdge L n k j}
    (h : b.1.source = b'.1.source) (hd : axisOf b = axisOf b') : b = b' := by
  apply Subtype.ext
  apply PeriodicLattice.Bond.ext h
  rw [target_eq b, target_eq b', h, hd]
private lemma edge_ext_target {j : ℕ} {b b' : PositiveEdge L n k j}
    (h : b.1.target = b'.1.target) (hd : axisOf b = axisOf b') : b = b' := by
  apply Subtype.ext
  refine PeriodicLattice.Bond.ext ?_ h
  have e := target_eq b
  have e' := target_eq b'
  rw [h, hd] at e
  exact add_right_cancel (e.symm.trans e')
private def IsIncident (s : Vertex L n k 0) : LevelFormIndex L n k → Prop
  | .inl p => s = p.2.1.source ∨ s = p.2.1.target
  | .inr p => s = toFine p.2.2.1.source
private def sourceVertex : LevelFormIndex L n k → Vertex L n k 0
  | .inl p => p.2.1.source
  | .inr p => toFine p.2.2.1.source
private def readPair {I : Type} (z : I → ℂ) (σ σ' : Fin 3 → I) : CoeffPair :=
  (fun e => z (σ e), fun e => z (σ' e))
private def baseCurrent (b : PositiveEdge L n k 0) : Fin 3 → TripleCoordIndex L n k :=
  fun e => .inr (.inl (.inl (e, b)))
private def baseField (b : PositiveEdge L n k 0) : Fin 3 → TripleCoordIndex L n k :=
  fun e => .inl (.inl (e, b))
private def levelCurrent (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    Fin 3 → TripleCoordIndex L n k :=
  fun e => .inr (.inl (.inr ⟨i, (e, c)⟩))
private def levelField (i : Fin k) (c : PositiveEdge L n k (i + 1)) :
    Fin 3 → TripleCoordIndex L n k :=
  fun e => .inl (.inr ⟨i, (e, c)⟩)
private def bracketKernel (z : TripleCoordIndex L n k → ℂ) :
    Matrix (Fin 3 × Vertex L n k 0) (LevelFormIndex L n k) ℂ :=
  open Classical in
  fun p q => match q with
    | .inl r =>
      (if p.2 = r.2.1.source then
          sourceEntry p.1 r.1 (readPair z (baseCurrent r.2) (baseField r.2)) else 0) +
        (if p.2 = r.2.1.target then
          targetEntry p.1 r.1 (readPair z (baseCurrent r.2) (baseField r.2)) else 0)
    | .inr r =>
      if p.2 = toFine r.2.2.1.source then
        sourceEntry p.1 r.2.1 (readPair z (levelCurrent r.1 r.2.2) (levelField r.1 r.2.2)) +
          targetEntry p.1 r.2.1 (readPair z (levelCurrent r.1 r.2.2) (levelField r.1 r.2.2))
      else 0
private lemma bracketKernel_eq_zero (z : TripleCoordIndex L n k → ℂ) (p : Fin 3 × Vertex L n k 0)
    (q : LevelFormIndex L n k) (h : ¬IsIncident p.2 q) : bracketKernel z p q = 0 := by
  rcases q with r | r
  · simp only [IsIncident, not_or] at h
    simp [bracketKernel, h.1, h.2]
  · simp only [IsIncident] at h
    simp [bracketKernel, h]
private lemma norm_readPair_le {I : Type} [Fintype I] (z : I → ℂ) (σ σ' : Fin 3 → I) :
    ‖readPair z σ σ'‖ ≤ ‖z‖ := by
  refine max_le ?_ ?_
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun e => norm_le_pi_norm z (σ e)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun e => norm_le_pi_norm z (σ' e)
private lemma norm_ite_zero_le {c : Prop} [Decidable c] {x : ℂ} {K : ℝ} (hK : 0 ≤ K)
    (h : ‖x‖ ≤ K) : ‖(if c then x else 0 : ℂ)‖ ≤ K := by
  split_ifs
  · exact h
  · simpa using hK
private lemma norm_bracketKernel_le [Fintype (LevelFormIndex L n k)]
    [Fintype (Fin 3 × PositiveEdge L n k k)] {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ (a d : Fin 3) (w : CoeffPair), ‖w‖ ≤ 1 →
      ‖sourceEntry a d w‖ ≤ K ∧ ‖targetEntry a d w‖ ≤ K)
    {z : TripleCoordIndex L n k → ℂ} (hz : ‖z‖ ≤ 1) (p : Fin 3 × Vertex L n k 0)
    (q : LevelFormIndex L n k) : ‖bracketKernel z p q‖ ≤ 2 * K := by
  rcases q with r | r
  · have h := hb p.1 r.1 (readPair z (baseCurrent r.2) (baseField r.2))
      ((norm_readPair_le _ _ _).trans hz)
    have h1 := norm_ite_zero_le (c := p.2 = r.2.1.source) hK h.1
    have h2 := norm_ite_zero_le (c := p.2 = r.2.1.target) hK h.2
    calc ‖bracketKernel z p (.inl r)‖ ≤ _ := norm_add_le _ _
      _ ≤ 2 * K := by linarith
  · have h := hb p.1 r.2.1 (readPair z (levelCurrent r.1 r.2.2) (levelField r.1 r.2.2))
      ((norm_readPair_le _ _ _).trans hz)
    have h3 : ‖sourceEntry p.1 r.2.1 (readPair z (levelCurrent r.1 r.2.2) (levelField r.1 r.2.2)) +
        targetEntry p.1 r.2.1 (readPair z (levelCurrent r.1 r.2.2) (levelField r.1 r.2.2))‖ ≤
          2 * K :=
      (norm_add_le _ _).trans (by linarith [h.1, h.2])
    exact norm_ite_zero_le (by positivity) h3
private def rowLabel (s : Vertex L n k 0) :
    LevelFormIndex L n k → Fin 3 × (Bool × Fin 4 ⊕ Fin k × Fin 4) :=
  open Classical in fun q => match q with
    | .inl r => (r.1, .inl (decide (s = r.2.1.source), axisOf r.2))
    | .inr r => (r.2.1, .inr (r.1, axisOf r.2.2))
private lemma rowLabel_injective (hL : 0 < L) (s : Vertex L n k 0) (q q' : LevelFormIndex L n k)
    (h : IsIncident s q) (h' : IsIncident s q') (e : rowLabel s q = rowLabel s q') : q = q' := by
  rcases q with ⟨d, b⟩ | ⟨i, d, c⟩ <;> rcases q' with ⟨d', b'⟩ | ⟨i', d', c'⟩
  · simp only [rowLabel, Prod.mk.injEq, Sum.inl.injEq, decide_eq_decide] at e
    obtain ⟨rfl, e1, e2⟩ := e
    simp only [IsIncident] at h h'
    have : b = b' := by
      by_cases ht : s = b.1.source
      · exact edge_ext_source (ht.symm.trans (e1.1 ht)) e2
      · have ht' : ¬s = b'.1.source := fun x => ht (e1.2 x)
        exact edge_ext_target ((h.resolve_left ht).symm.trans (h'.resolve_left ht')) e2
    rw [this]
  · simp [rowLabel] at e
  · simp [rowLabel] at e
  · simp only [rowLabel, Prod.mk.injEq, Sum.inr.injEq] at e
    obtain ⟨rfl, rfl, e2⟩ := e
    simp only [IsIncident] at h h'
    have : c = c' :=
      edge_ext_source (toFine_injective hL (h.symm.trans h')) e2
    rw [this]
private def colLabel (q : LevelFormIndex L n k) (p : Fin 3 × Vertex L n k 0) : Fin 3 × Bool :=
  open Classical in (p.1, decide (p.2 = sourceVertex q))
private lemma colLabel_injective (q : LevelFormIndex L n k) (p p' : Fin 3 × Vertex L n k 0)
    (h : IsIncident p.2 q) (h' : IsIncident p'.2 q) (e : colLabel q p = colLabel q p') :
    p = p' := by
  simp only [colLabel, Prod.mk.injEq, decide_eq_decide] at e
  refine Prod.ext e.1 ?_
  by_cases ht : p.2 = sourceVertex q
  · exact ht.trans (e.2.1 ht).symm
  · have ht' : ¬p'.2 = sourceVertex q := fun x => ht (e.2.2 x)
    rcases q with r | r
    · simp only [IsIncident, sourceVertex] at h h' ht ht'
      exact (h.resolve_left ht).trans (h'.resolve_left ht').symm
    · exact absurd h ht
private lemma cellDist_le_of_incident
    (hc : (∀ y y' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k),
      cellDist y y' = cellDist y' y) ∧
    (∀ y y' y'' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k),
      cellDist y y'' ≤ cellDist y y' + cellDist y' y'') ∧
    (∀ (x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0)) (μ : Fin 4),
      cellDist (fineVertexCell (L := L) (n := n) (k := k) x)
        (fineVertexCell (L := L) (n := n) (k := k) (x + PeriodicLattice.unitStep L n _ μ)) ≤ 4))
    {s : Vertex L n k 0} {q : LevelFormIndex L n k} (h : IsIncident s q) :
    cellDist (levelFormIndexCell q) (levelVertexCell s) ≤ 8 ∧
      cellDist (levelVertexCell s) (levelFormIndexCell q) ≤ 8 := by
  obtain ⟨sym, tri, near⟩ := hc
  have self_near : ∀ x : Vertex L n k 0,
      cellDist (fineVertexCell (L := L) (n := n) (k := k) x) (fineVertexCell x) ≤ 8 := by
    intro x
    have h1 := near x 0
    have h2 := tri (fineVertexCell x) (fineVertexCell (x + PeriodicLattice.unitStep L n _ 0))
      (fineVertexCell x)
    rw [sym (fineVertexCell (x + PeriodicLattice.unitStep L n _ 0))] at h2
    linarith
  have cell0 : ∀ x : Vertex L n k 0, levelVertexCell x = fineVertexCell x := fun x => by
    rw [levelVertexCell]
    exact congrArg _ (toFine_self x)
  suffices H : cellDist (levelFormIndexCell q) (levelVertexCell s) ≤ 8 from
    ⟨H, by rw [sym]; exact H⟩
  rcases q with r | r
  · change cellDist (levelVertexCell r.2.1.source) (levelVertexCell s) ≤ 8
    rw [cell0, cell0]
    rcases h with rfl | rfl
    · exact self_near _
    · rw [target_eq r.2]
      exact (near _ _).trans (by norm_num)
  · change s = toFine r.2.2.1.source at h
    change cellDist (fineVertexCell (toFine r.2.2.1.source)) (levelVertexCell s) ≤ 8
    rw [cell0, ← h]
    exact self_near s
private def readPairCLM {I : Type} [Fintype I] (σ σ' : Fin 3 → I) : (I → ℂ) →L[ℂ] CoeffPair :=
  (ContinuousLinearMap.pi fun e => ContinuousLinearMap.proj (σ e)).prod
    (ContinuousLinearMap.pi fun e => ContinuousLinearMap.proj (σ' e))
private lemma analyticAt_comp_readPair {I : Type} [Fintype I] (σ σ' : Fin 3 → I)
    {f : CoeffPair → ℂ} (hf : ∀ w, AnalyticAt ℂ f w) (z : I → ℂ) :
    AnalyticAt ℂ (fun z : I → ℂ => f (readPair z σ σ')) z :=
  (hf _).comp_of_eq ((readPairCLM σ σ').analyticAt z) rfl
private lemma analyticAt_ite_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : Prop}
    [Decidable c] {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun w => if c then f w else 0) x := by
  by_cases h : c
  · simpa [h] using hf
  · simpa [h] using analyticAt_const
private theorem bracketKernel_isLocallyHolomorphic (hL : 0 < L)
    (hc : (∀ y y' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k),
      cellDist y y' = cellDist y' y) ∧
    (∀ y y' y'' : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k),
      cellDist y y'' ≤ cellDist y y' + cellDist y' y'') ∧
    (∀ (x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0)) (μ : Fin 4),
      cellDist (fineVertexCell (L := L) (n := n) (k := k) x)
        (fineVertexCell (L := L) (n := n) (k := k) (x + PeriodicLattice.unitStep L n _ μ)) ≤ 4))
    {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ (a d : Fin 3) (w : CoeffPair), ‖w‖ ≤ 1 →
      ‖sourceEntry a d w‖ ≤ K ∧ ‖targetEntry a d w‖ ≤ K)
    [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
    [Fintype (Fin 3 × PositiveEdge L n k k)] [Fintype (Fin 3 × Vertex L n k 0)] :
    IsLocallyHolomorphicFamily tripleCoordIndexCell levelFormIndexCell fineIndexCell
      (bracketKernel (L := L) (n := n) (k := k)) 1
      (Real.sqrt ((Fintype.card (Fin 3 × (Bool × Fin 4 ⊕ Fin k × Fin 4)) * (2 * K)) *
        (Fintype.card (Fin 3 × Bool) * (2 * K)))) 8 where
  holomorphic := by
    intro p q z _
    rcases q with r | r
    · exact (analyticAt_ite_zero (analyticAt_comp_readPair _ _ (analyticAt_sourceEntry _ _) z)).add
        (analyticAt_ite_zero (analyticAt_comp_readPair _ _ (analyticAt_targetEntry _ _) z))
    · exact analyticAt_ite_zero ((analyticAt_comp_readPair _ _ (analyticAt_sourceEntry _ _) z).add
        (analyticAt_comp_readPair _ _ (analyticAt_targetEntry _ _) z))
  norm_le := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by
      have := mem_ball_zero_iff.1 hz
      exact this.le
    refine norm_le_sqrt_of_row_col _ (by positivity) (by positivity) (fun p => ?_) (fun q => ?_)
    · exact sum_le_card_mul_of_injOn (by positivity) (rowLabel p.2) (T := IsIncident p.2)
        (fun q h => by rw [bracketKernel_eq_zero z p q h, norm_zero])
        (fun q => norm_bracketKernel_le hK hb hz1 p q) (rowLabel_injective hL p.2)
    · exact sum_le_card_mul_of_injOn (by positivity) (colLabel q) (T := fun p => IsIncident p.2 q)
        (fun p h => by rw [bracketKernel_eq_zero z p q h, norm_zero])
        (fun p => norm_bracketKernel_le hK hb hz1 p q) (colLabel_injective q)
  depends_near := by
    intro p q z _ z' _ hz
    by_cases h : IsIncident p.2 q
    · have near := (cellDist_le_of_incident hc h).1
      rcases q with r | r
      · have e : readPair z (baseCurrent r.2) (baseField r.2) =
            readPair z' (baseCurrent r.2) (baseField r.2) := by
          refine Prod.ext (funext fun e => hz _ near) (funext fun e => hz _ near)
        simp only [bracketKernel, e]
      · have e : readPair z (levelCurrent r.1 r.2.2) (levelField r.1 r.2.2) =
            readPair z' (levelCurrent r.1 r.2.2) (levelField r.1 r.2.2) := by
          refine Prod.ext (funext fun e => hz _ near) (funext fun e => hz _ near)
        simp only [bracketKernel, e]
    · rw [bracketKernel_eq_zero z p q h, bracketKernel_eq_zero z' p q h]
  eq_zero_of_far := by
    intro z _ p q h
    refine bracketKernel_eq_zero z p q fun ht => ?_
    exact absurd (cellDist_le_of_incident hc ht).2 (not_le.2 h)
private lemma finsum_levelFormIndex [Fintype (PositiveEdge L n k 0)]
    [∀ i : Fin k, Fintype (PositiveEdge L n k (i + 1))] (f : LevelFormIndex L n k → ℂ) :
    ∑ᶠ q, f q = ∑ b : PositiveEdge L n k 0, ∑ d : Fin 3, f (.inl (d, b)) +
      ∑ i : Fin k, ∑ c : PositiveEdge L n k (i + 1), ∑ d : Fin 3, f (.inr ⟨i, (d, c)⟩) := by
  rw [finsum_eq_sum_of_fintype, Fintype.sum_sum_type, Fintype.sum_prod_type_right,
    Fintype.sum_sigma]
  congr 1
  exact Finset.sum_congr rfl fun i _ => Fintype.sum_prod_type_right _
private lemma sum_levelFormIndex [Fintype (LevelFormIndex L n k)] [Fintype (PositiveEdge L n k 0)]
    [∀ i : Fin k, Fintype (PositiveEdge L n k (i + 1))] (f : LevelFormIndex L n k → ℂ) :
    ∑ q, f q = ∑ b : PositiveEdge L n k 0, ∑ d : Fin 3, f (.inl (d, b)) +
      ∑ i : Fin k, ∑ c : PositiveEdge L n k (i + 1), ∑ d : Fin 3, f (.inr ⟨i, (d, c)⟩) := by
  rw [← finsum_eq_sum_of_fintype f]
  exact finsum_levelFormIndex f
private lemma finsum_colourVertex [Fintype (Vertex L n k 0)] (f : Fin 3 × Vertex L n k 0 → ℂ) :
    ∑ᶠ p, f p = ∑ a : Fin 3, ∑ s : Vertex L n k 0, f (a, s) := by
  rw [finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
private lemma sum_colourVertex [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Vertex L n k 0)]
    (f : Fin 3 × Vertex L n k 0 → ℂ) : ∑ p, f p = ∑ a : Fin 3, ∑ s : Vertex L n k 0, f (a, s) := by
  rw [← finsum_eq_sum_of_fintype f]
  exact finsum_colourVertex f
private lemma column_base [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Vertex L n k 0)]
    (z : TripleCoordIndex L n k → ℂ) (v : Fin 3 × Vertex L n k 0 → ℂ) (d : Fin 3)
    (b : PositiveEdge L n k 0) :
    ∑ p, v p * bracketKernel z p (.inl (d, b)) =
      bracketEntry (pauliCombo (readPair z (baseCurrent b) (baseField b)).1)
        (pauliCombo fun a => v (a, b.1.source)) (ComplexMatrix2.pauliFamily d) +
      bracketEntry (pauliCombo (readPair z (baseCurrent b) (baseField b)).1)
        (conjExp (pauliCombo (readPair z (baseCurrent b) (baseField b)).2)
          (pauliCombo fun a => v (a, b.1.target)))
        (ComplexMatrix2.pauliFamily d) := by
  classical
  rw [sum_colourVertex, bracketEntry_pauliCombo, bracketEntry_conjExp_pauliCombo,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [bracketKernel, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rfl
private lemma column_level [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Vertex L n k 0)]
    (z : TripleCoordIndex L n k → ℂ) (v : Fin 3 × Vertex L n k 0 → ℂ) (d : Fin 3) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    ∑ p, v p * bracketKernel z p (.inr ⟨i, (d, c)⟩) =
      bracketEntry (pauliCombo (readPair z (levelCurrent i c) (levelField i c)).1)
        (pauliCombo fun a => v (a, toFine c.1.source)) (ComplexMatrix2.pauliFamily d) +
      bracketEntry (pauliCombo (readPair z (levelCurrent i c) (levelField i c)).1)
        (conjExp (pauliCombo (readPair z (levelCurrent i c) (levelField i c)).2)
          (pauliCombo fun a => v (a, toFine c.1.source))) (ComplexMatrix2.pauliFamily d) := by
  classical
  rw [sum_colourVertex, bracketEntry_pauliCombo, bracketEntry_conjExp_pauliCombo,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [bracketKernel, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_add]
  rfl
private lemma edgeForm_hermitian {j : ℕ} (ξ : edgeFormSpace L n k j) (b : PositiveEdge L n k j) :
    ((ξ : Edge L n k j → ComplexMatrix2) b.1).conjTranspose = (ξ : Edge L n k j → ComplexMatrix2) b.1 :=
  (ξ.2.1 b.1 b.2).1.symm
private lemma vertexForm_hermitian (l : vertexFunctionSpace L n k 0) (s : Vertex L n k 0) :
    ((l : Vertex L n k 0 → ComplexMatrix2) s).conjTranspose = (l : Vertex L n k 0 → ComplexMatrix2) s :=
  (l.2 s (Set.mem_univ _)).1.symm
section Values
variable [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [Fintype (Fin 3 × Vertex L n k 0)]
  [Fintype (Fin 3 × Vertex L n k k)]
private lemma baseForm_eq (P : PauliCoordinates L n k) (ξ : LevelForms L n k)
    (b : PositiveEdge L n k 0) :
    (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1 =
      pauliCombo fun d => ((P.formCoords ξ (.inl (d, b)) : ℝ) : ℂ) :=
  eq_pauliCombo (ξ.1.2.1 b.1 b.2) fun a => P.formCoords_base ξ (a, b)
private lemma levelForm_eq (P : PauliCoordinates L n k) (ξ : LevelForms L n k) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
      pauliCombo fun d => ((P.formCoords ξ (.inr ⟨i, (d, c)⟩) : ℝ) : ℂ) :=
  eq_pauliCombo ((ξ.2 i).2.1 c.1 c.2) fun a => P.formCoords_level ξ i (a, c)
private lemma vertexForm_eq (P : PauliCoordinates L n k) (l : vertexFunctionSpace L n k 0)
    (s : Vertex L n k 0) :
    (l : Vertex L n k 0 → ComplexMatrix2) s =
      pauliCombo fun a => complexifyCoords (fineVertexCoords P l) (a, s) :=
  eq_pauliCombo (l.2 s (Set.mem_univ _)) fun a => P.ghostCoords_fst (l, 0) (a, s)
private lemma fine_eq (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ)
    (b : PositiveEdge L n k 0) :
    (pointOfCoords P x).fine b.1 =
      ComplexMatrix2.matExp
        (Complex.I • ((tripleOfCoords P x).1.1 : Edge L n k 0 → ComplexMatrix2) b.1) := by
  simp only [pointOfCoords, expMove, unitPoint, PeriodicLattice.expTwist, if_pos b.2, mul_one]
private lemma noise_eq (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    (pointOfCoords P x).noise i c =
      ComplexMatrix2.matExp
        (Complex.I • ((tripleOfCoords P x).1.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1) := by
  simp only [pointOfCoords, expMove, unitPoint, mul_one]
end Values
private lemma edgeFormPairing_bracketTerm [Fintype (PositiveEdge L n k 0)]
    (J : Edge L n k 0 → ComplexMatrix2) (U : Edge L n k 0 → ComplexMatrix2)
    (l : Vertex L n k 0 → ComplexMatrix2) (B : Edge L n k 0 → ComplexMatrix2) :
    edgeFormPairing J (bracketTerm U l B) = ∑ b : PositiveEdge L n k 0,
      bracketEntry (J b.1) (l b.1.source + ComplexMatrix2.conjugateBy (U b.1) (l b.1.target))
        (B b.1) := by
  rw [edgeFormPairing, traceFinsumPairing, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [restrictToPositiveEdges, bracketTerm, extendOddly, if_pos b.2, bracketEntry,
    Ring.lie_def]
private lemma edgeFormPairing_level {j : ℕ} [Fintype (PositiveEdge L n k j)]
    (J : Edge L n k j → ComplexMatrix2) (N : PositiveEdge L n k j → ComplexMatrix2)
    (l : Vertex L n k j → ComplexMatrix2) (B : Edge L n k j → ComplexMatrix2) :
    edgeFormPairing J (extendOddly fun c =>
      open Classical in
      if hc : c.IsPositivelyOriented then
        (Complex.I / 2) • ⁅l c.source + ComplexMatrix2.conjugateBy (N ⟨c, hc⟩) (l c.source), B c⁆
      else 0) = ∑ c : PositiveEdge L n k j,
      bracketEntry (J c.1) (l c.1.source + ComplexMatrix2.conjugateBy (N c) (l c.1.source))
        (B c.1) := by
  rw [edgeFormPairing, traceFinsumPairing, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [restrictToPositiveEdges, extendOddly, if_pos b.2, dif_pos b.2, bracketEntry,
    Ring.lie_def]
private lemma ofReal_re_of_im_eq_zero {w : ℂ} (h : w.im = 0) : ((w.re : ℝ) : ℂ) = w :=
  Complex.ext rfl (by simp [h])
private lemma im_sum_eq_zero {α : Type} (s : Finset α) (f : α → ℂ) (h : ∀ x, (f x).im = 0) :
    (∑ x ∈ s, f x).im = 0 := by
  rw [Complex.im_sum]
  exact Finset.sum_eq_zero fun x _ => h x
private theorem bracketKernel_real [Fintype (LevelFormIndex L n k)]
    [Fintype (Fin 3 × PositiveEdge L n k k)] [Fintype (GhostCoordIndex L n k)]
    [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
    (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ) (l : vertexFunctionSpace L n k 0)
    (ξ : LevelForms L n k) :
    ((levelPairing (formValues (tripleOfCoords P x).2.1)
        (chainBracket (pointOfCoords P x) (l : Vertex L n k 0 → ComplexMatrix2) (formValues ξ)) :
          ℝ) : ℂ) =
      complexifyCoords (fineVertexCoords P l) ⬝ᵥ
        (bracketKernel (complexifyCoords x)).mulVec (complexifyCoords (P.formCoords ξ)) := by
  classical
  have : Finite (PositiveEdge L n k 0) :=
    Finite.of_injective (fun b => (Sum.inl ((0 : Fin 3), b) : LevelFormIndex L n k))
      fun b b' h => by simpa using h
  have : ∀ i : Fin k, Finite (PositiveEdge L n k (i + 1)) := fun i =>
    Finite.of_injective
      (fun b => (Sum.inr ⟨i, ((0 : Fin 3), b)⟩ : LevelFormIndex L n k))
      fun b b' h => by simpa using h
  have : Finite (Vertex L n k 0) :=
    Finite.of_injective (fun s => ((0 : Fin 3), s)) fun s s' h => by simpa using h
  let _ : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
  let _ : ∀ i : Fin k, Fintype (PositiveEdge L n k (i + 1)) := fun i => Fintype.ofFinite _
  let _ : Fintype (Vertex L n k 0) := Fintype.ofFinite _
  set z := complexifyCoords x with hz
  set v := complexifyCoords (fineVertexCoords P l) with hv
  set w := complexifyCoords (P.formCoords ξ) with hw
  set τ := tripleOfCoords P x with hτ
  have t1 : P.formCoords τ.1 = fun p => x (.inl p) := P.formCoords.apply_symm_apply _
  have t2 : P.formCoords τ.2.1 = fun p => x (.inr (.inl p)) := P.formCoords.apply_symm_apply _
  have a0 : ∀ b : PositiveEdge L n k 0, (τ.1.1 : Edge L n k 0 → ComplexMatrix2) b.1 =
      pauliCombo (readPair z (baseCurrent b) (baseField b)).2 := fun b => by
    rw [baseForm_eq P τ.1 b, t1]
    rfl
  have j0 : ∀ b : PositiveEdge L n k 0, (τ.2.1.1 : Edge L n k 0 → ComplexMatrix2) b.1 =
      pauliCombo (readPair z (baseCurrent b) (baseField b)).1 := fun b => by
    rw [baseForm_eq P τ.2.1 b, t2]
    rfl
  have ai : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (τ.1.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
      pauliCombo (readPair z (levelCurrent i c) (levelField i c)).2 := fun i c => by
    rw [levelForm_eq P τ.1 i c, t1]
    rfl
  have ji : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (τ.2.1.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
      pauliCombo (readPair z (levelCurrent i c) (levelField i c)).1 := fun i c => by
    rw [levelForm_eq P τ.2.1 i c, t2]
    rfl
  have e0 : edgeFormPairing (τ.2.1.1 : Edge L n k 0 → ComplexMatrix2)
      (bracketTerm (pointOfCoords P x).fine (l : Vertex L n k 0 → ComplexMatrix2)
        (ξ.1 : Edge L n k 0 → ComplexMatrix2)) = ∑ b : PositiveEdge L n k 0,
      bracketEntry ((τ.2.1.1 : Edge L n k 0 → ComplexMatrix2) b.1)
        ((l : Vertex L n k 0 → ComplexMatrix2) b.1.source +
          conjExp ((τ.1.1 : Edge L n k 0 → ComplexMatrix2) b.1)
            ((l : Vertex L n k 0 → ComplexMatrix2) b.1.target))
        ((ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1) := by
    rw [edgeFormPairing_bracketTerm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [fine_eq, conjugateBy_matExp]
  have ei : ∀ i : Fin k, edgeFormPairing (τ.2.1.2 i : Edge L n k (i + 1) → ComplexMatrix2)
      ((chainBracket (pointOfCoords P x) (l : Vertex L n k 0 → ComplexMatrix2)
        (formValues ξ)).2 i) =
      ∑ c : PositiveEdge L n k (i + 1),
      bracketEntry ((τ.2.1.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1)
        ((l : Vertex L n k 0 → ComplexMatrix2) (toFine c.1.source) +
          conjExp ((τ.1.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1)
            ((l : Vertex L n k 0 → ComplexMatrix2) (toFine c.1.source)))
        ((ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1) := by
    intro i
    have h := edgeFormPairing_level (τ.2.1.2 i : Edge L n k (i + 1) → ComplexMatrix2)
      ((pointOfCoords P x).noise i)
      (restrictVertexFunction (i + 1) (l : Vertex L n k 0 → ComplexMatrix2))
      (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2)
    refine h.trans (Finset.sum_congr rfl fun c _ => ?_)
    rw [noise_eq, conjugateBy_matExp]
    rfl
  have im0 : ∀ b : PositiveEdge L n k 0,
      (bracketEntry ((τ.2.1.1 : Edge L n k 0 → ComplexMatrix2) b.1)
        ((l : Vertex L n k 0 → ComplexMatrix2) b.1.source +
          conjExp ((τ.1.1 : Edge L n k 0 → ComplexMatrix2) b.1)
            ((l : Vertex L n k 0 → ComplexMatrix2) b.1.target))
        ((ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1)).im = 0 := fun b =>
    bracketEntry_im_eq_zero (edgeForm_hermitian _ b)
      (by rw [Matrix.conjTranspose_add, vertexForm_hermitian,
        conjTranspose_conjExp (edgeForm_hermitian _ b) (vertexForm_hermitian _ _)])
      (edgeForm_hermitian _ b)
  have imi : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (bracketEntry ((τ.2.1.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1)
        ((l : Vertex L n k 0 → ComplexMatrix2) (toFine c.1.source) +
          conjExp ((τ.1.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1)
            ((l : Vertex L n k 0 → ComplexMatrix2) (toFine c.1.source)))
        ((ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1)).im = 0 := fun i c =>
    bracketEntry_im_eq_zero (edgeForm_hermitian _ c)
      (by rw [Matrix.conjTranspose_add, vertexForm_hermitian,
        conjTranspose_conjExp (edgeForm_hermitian _ c) (vertexForm_hermitian _ _)])
      (edgeForm_hermitian _ c)
  have lhs : ((levelPairing (formValues τ.2.1)
        (chainBracket (pointOfCoords P x) (l : Vertex L n k 0 → ComplexMatrix2)
          (formValues ξ)) : ℝ) : ℂ) =
      (∑ b : PositiveEdge L n k 0,
        bracketEntry ((τ.2.1.1 : Edge L n k 0 → ComplexMatrix2) b.1)
          ((l : Vertex L n k 0 → ComplexMatrix2) b.1.source +
            conjExp ((τ.1.1 : Edge L n k 0 → ComplexMatrix2) b.1)
              ((l : Vertex L n k 0 → ComplexMatrix2) b.1.target))
          ((ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1)) +
      ∑ i : Fin k, ∑ c : PositiveEdge L n k (i + 1),
        bracketEntry ((τ.2.1.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1)
          ((l : Vertex L n k 0 → ComplexMatrix2) (toFine c.1.source) +
            conjExp ((τ.1.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1)
              ((l : Vertex L n k 0 → ComplexMatrix2) (toFine c.1.source)))
          ((ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1) := by
    rw [levelPairing]
    change (((edgeFormPairing (τ.2.1.1 : Edge L n k 0 → ComplexMatrix2)
        (bracketTerm (pointOfCoords P x).fine (l : Vertex L n k 0 → ComplexMatrix2)
          (ξ.1 : Edge L n k 0 → ComplexMatrix2))).re +
      ∑ i : Fin k, (edgeFormPairing (τ.2.1.2 i : Edge L n k (i + 1) → ComplexMatrix2)
        ((chainBracket (pointOfCoords P x) (l : Vertex L n k 0 → ComplexMatrix2)
          (formValues ξ)).2 i)).re : ℝ) : ℂ) = _
    rw [e0]
    simp only [ei]
    push_cast
    rw [ofReal_re_of_im_eq_zero (im_sum_eq_zero _ _ im0)]
    congr 1
    exact Finset.sum_congr rfl fun i _ => ofReal_re_of_im_eq_zero (im_sum_eq_zero _ _ (imi i))
  rw [lhs]
  have rhs : v ⬝ᵥ (bracketKernel z).mulVec w = ∑ q, (∑ p, v p * bracketKernel z p q) * w q := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring
  rw [rhs, sum_levelFormIndex]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [j0 b, a0 b, vertexForm_eq P l b.1.source, vertexForm_eq P l b.1.target, baseForm_eq P ξ b,
      bracketEntry_pauliCombo_right]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [column_base, bracketEntry_add_left, mul_comm]
    rfl
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
    rw [ji i c, ai i c, vertexForm_eq P l (toFine c.1.source), levelForm_eq P ξ i c,
      bracketEntry_pauliCombo_right]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [column_level, bracketEntry_add_left, mul_comm]
    rfl
end Kernel
theorem chainBracket_isLocallyHolomorphic (hcells : NeighbouringFineVertexCells) :
    ChainBracketIsLocallyHolomorphic := by
  intro L hL k _
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨K, hK, hb⟩ := exists_entry_bound
  refine ⟨1, Real.sqrt ((Fintype.card (Fin 3 × (Bool × Fin 4 ⊕ Fin k × Fin 4)) * (2 * K)) *
    (Fintype.card (Fin 3 × Bool) * (2 * K))), 8, one_pos, Real.sqrt_nonneg _, by norm_num,
    Eventually.of_forall fun n => ?_⟩
  intro _ _ _ _ _ _ _ _ _ P
  obtain ⟨sym, tri, _, near⟩ := hcells L hL n k
  refine ⟨bracketKernel, bracketKernel_isLocallyHolomorphic hL0 ⟨sym, tri, near⟩ hK hb,
    Eventually.of_forall fun x l ξ => ?_⟩
  exact bracketKernel_real P x l ξ
end YangMills.Construction.RunningCouplingSlope.ChainBracketLocality
end
