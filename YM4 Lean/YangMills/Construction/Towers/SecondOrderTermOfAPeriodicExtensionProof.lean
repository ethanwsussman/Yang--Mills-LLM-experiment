import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyProof
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Towers.CovariantAveragesAsDifferentialsProof
import YangMills.Construction.Towers.IteratedAveragesOfAPeriodicExtension
import YangMills.Construction.Towers.SecondOrderTermOfAPeriodicExtension
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.LocalKernels.LiftQuadraticTerm
open YangMills.Construction.LocalKernels.Periodisation YangMills.Construction.Matrices
open YangMills.Construction.Tower.AsDifferentials (boundedSubmodule quadraticTermAt)
theorem deriv_deriv_congr_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℂ → ℂ → E}
    (h : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0), f p.1 p.2 = g p.1 p.2) :
    deriv (fun s => deriv (fun t => f s t) 0) 0 = deriv (fun s => deriv (fun t => g s t) 0) 0 := by
  have h₁ : ∀ᶠ s : ℂ in 𝓝 0, ∀ᶠ t : ℂ in 𝓝 0, f s t = g s t := h.curry_nhds
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [h₁] with s hs
  exact Filter.EventuallyEq.deriv_eq hs
theorem matExp_smul_mul_mem (hEL : ComplexMatrix2.ExpLogEstimates) {X g : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    ComplexMatrix2.matExp (Complex.I • X) * g ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.Construction.Tower.AsDifferentials.expChart_mem_unitDeterminant <;> assumption
theorem inv_mem_unitDeterminant {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    g⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem inv_inv_of_mem_unitDeterminant {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.unitDeterminant) : (g⁻¹)⁻¹ = g := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
theorem eventually_matExp_mul_sub_lt (hEL : ComplexMatrix2.ExpLogEstimates)
    (X Y g : ComplexMatrix2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0),
      ComplexMatrix2.operatorNorm
        (ComplexMatrix2.matExp (Complex.I • (p.1 • X + p.2 • Y)) * g - g) < ε := by
  have hbound : ∀ p : ℂ × ℂ, ComplexMatrix2.operatorNorm
      (ComplexMatrix2.matExp (Complex.I • (p.1 • X + p.2 • Y)) * g - g) ≤
      (Real.exp ‖Complex.I • (p.1 • X + p.2 • Y)‖ - 1) * ‖g‖ := fun p => by
    have e : ComplexMatrix2.matExp (Complex.I • (p.1 • X + p.2 • Y)) * g - g =
        (ComplexMatrix2.matExp (Complex.I • (p.1 • X + p.2 • Y)) - 1) * g := by
      rw [sub_mul, one_mul]
    rw [e]
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hEL.1 (Complex.I • (p.1 • X + p.2 • Y))).2 (norm_nonneg _))
  have hc : Continuous fun p : ℂ × ℂ =>
      (Real.exp ‖Complex.I • (p.1 • X + p.2 • Y)‖ - 1) * ‖g‖ := by fun_prop
  have h0 := hc.tendsto (0, 0)
  simp only [zero_smul, add_zero, smul_zero, norm_zero, Real.exp_zero, sub_self, zero_mul] at h0
  filter_upwards [h0.eventually (gt_mem_nhds hε)] with p hp
  exact (hbound p).trans_lt hp
section Torus
variable {L n k : ℕ}
open YangMills.Construction.Tower.MeanStableFields in
theorem isMeanSequenceFrom_of_mem_smallIterateFields
    (hO : Tower.IteratedMeans.TorusConditions L n k)
    {U : Tower.Edge L n k 0 → ComplexMatrix2} (hU : U ∈ Tower.smallIterateFields L n k) :
    IsMeanSequenceFrom k U fun i => PeriodicLattice.complexBlockFieldAtLevel i U := by apply _root_.YangMills.Construction.Tower.AsDifferentials.isMeanSequenceFrom_of_small <;> assumption
theorem mem_smallIterateFields_of_mem_meanStableFields
    (hO : Tower.IteratedMeans.TorusConditions L n k)
    {W : Tower.Edge L n k 0 → ComplexMatrix2}
    (hW : W ∈ Tower.MeanStableFields.meanStableFields L n k k) :
    W ∈ Tower.smallIterateFields L n k := by apply _root_.YangMills.Construction.Tower.AsDifferentials.small_of_meanStable <;> assumption
theorem expTwist_mem_fieldsIn (hEL : ComplexMatrix2.ExpLogEstimates)
    (hx : ∀ b : Tower.Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {U C : Tower.Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ Tower.fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup)
    (hC : C ∈ Tower.complexEdgeForms L n k 0) :
    PeriodicLattice.expTwist C U ∈ Tower.fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup := by
  classical
  have hval : ∀ b : Tower.Edge L n k 0, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • C b) * U b ∈ ComplexMatrix2.unitDeterminant :=
    fun b hb => matExp_smul_mul_mem hEL (hC.1 b hb) (hU.1 b (mem_univ b))
  have hrr : ∀ b : Tower.Edge L n k 0, b.opposite.opposite = b :=
    fun b => PeriodicLattice.Bond.ext rfl rfl
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · simp only [PeriodicLattice.expTwist, if_pos hb]
      exact hval b hb
    · have hr : b.opposite.IsPositivelyOriented := by
        rcases hx b with h | h
        exacts [absurd h.1 hb, h.1]
      simp only [PeriodicLattice.expTwist, if_neg hb]
      exact inv_mem_unitDeterminant (hval _ hr)
  · by_cases hb : b.IsPositivelyOriented
    · have hr : ¬ b.opposite.IsPositivelyOriented := by
        rcases hx b with h | h
        exacts [h.2, absurd hb h.2]
      simp only [PeriodicLattice.expTwist, if_pos hb, if_neg hr, hrr b]
    · have hr : b.opposite.IsPositivelyOriented := by
        rcases hx b with h | h
        exacts [absurd h.1 hb, h.1]
      simp only [PeriodicLattice.expTwist, if_neg hb, if_pos hr]
      exact (inv_inv_of_mem_unitDeterminant (hval _ hr)).symm
theorem eventually_expTwist_mem_smallIterateFields (hEL : ComplexMatrix2.ExpLogEstimates)
    (hP : Tower.MeanStableFields.MeanStableConditions L n k)
    (hO : Tower.IteratedMeans.TorusConditions L n k)
    (hfin : (univ : Set (Tower.Edge L n k 0)).Finite)
    (hx : ∀ b : Tower.Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {U B B' : Tower.Edge L n k 0 → ComplexMatrix2} (hU : U ∈ Tower.smallIterateFields L n k)
    (hB : B ∈ Tower.complexEdgeForms L n k 0) (hB' : B' ∈ Tower.complexEdgeForms L n k 0) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0),
      PeriodicLattice.expTwist (p.1 • B + p.2 • B') U ∈ Tower.smallIterateFields L n k := by
  classical
  have hS : U ∈ Tower.MeanStableFields.meanStableFields L n k k :=
    ⟨_, isMeanSequenceFrom_of_mem_smallIterateFields hO hU⟩
  let F : Finset (Tower.Edge L n k 0) := hfin.toFinset.filter (·.IsPositivelyOriented)
  obtain ⟨ε, hε, hmv⟩ := hP.small_perturbation U hS F (fun b hb => (Finset.mem_filter.1 hb).2)
  have hall : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0), ∀ b ∈ F,
      ComplexMatrix2.operatorNorm
        (ComplexMatrix2.matExp (Complex.I • (p.1 • B b + p.2 • B' b)) * U b - U b) < ε :=
    (Finset.eventually_all F).2 fun b _ => eventually_matExp_mul_sub_lt hEL (B b) (B' b) (U b) hε
  filter_upwards [hall] with p hp
  refine mem_smallIterateFields_of_mem_meanStableFields hO (hmv _ (expTwist_mem_fieldsIn hEL hx hU.1
    ((Tower.complexEdgeForms L n k 0).add_mem ((Tower.complexEdgeForms L n k 0).smul_mem p.1 hB)
      ((Tower.complexEdgeForms L n k 0).smul_mem p.2 hB'))) (fun b hb hbF => ?_) (fun b hb => ?_))
  · exact absurd (Finset.mem_filter.2 ⟨by simp, hb⟩) hbF
  · have hp' : b.IsPositivelyOriented := (Finset.mem_filter.1 hb).2
    simpa [PeriodicLattice.expTwist, if_pos hp'] using hp b hb
theorem iterMean_eq_complexBlockFieldAtLevel
    (hP : Tower.MeanStableFields.MeanStableConditions L n k)
    (hO : Tower.IteratedMeans.TorusConditions L n k)
    {U : Tower.Edge L n k 0 → ComplexMatrix2} (hU : U ∈ Tower.smallIterateFields L n k)
    (c : Tower.Edge L n k k) :
    Tower.AsDifferentials.iterMean U k c = PeriodicLattice.complexBlockFieldAtLevel k U c := by
  simp [Tower.AsDifferentials.iterMean, Tower.LevelwiseMeans.valuesOrOne,
    hP.eq_levelwiseMean k le_rfl U _ (isMeanSequenceFrom_of_mem_smallIterateFields hO hU) k le_rfl c]
end Torus
section FullSpace
variable {L k : ℕ}
open YangMills.Construction.Tower.MeanStableFields.Infinite in
theorem fullSpace_isMeanSequenceFrom_of_mem_smallIterateFields
    (hO : Tower.IteratedMeans.Unbounded.SpaceConditions L k)
    {U : Tower.FullSpace.Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ Tower.FullSpace.smallIterateFields L k) :
    IsMeanSequenceFrom k U fun i => Tower.FullSpace.complexIter L k i U := by
  refine ⟨⟨fun i hi => ?_, fun i hi b => (hU.2 i hi).2 b, fun i hi c hc => rfl⟩, rfl⟩
  cases i with
  | zero => exact hU.1
  | succ i => exact hO.meanStep_mem i (by omega) _ (hU.2 i (by omega))
theorem fullSpace_iterMean_eq_complexIter
    (hP : Tower.MeanStableFields.Infinite.MeanStableConditions L k)
    (hO : Tower.IteratedMeans.Unbounded.SpaceConditions L k)
    {U : Tower.FullSpace.Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ Tower.FullSpace.smallIterateFields L k)
    (c : Tower.FullSpace.Edge L k k) :
    Tower.FullSpace.AsDifferentials.iterMean U k c = Tower.FullSpace.complexIter L k k U c := by
  simp [Tower.FullSpace.AsDifferentials.iterMean, Tower.LevelwiseMeans.valuesOrOne,
    hP.eq_levelwiseMean k le_rfl U _
      (fullSpace_isMeanSequenceFrom_of_mem_smallIterateFields hO hU) k le_rfl c]
end FullSpace
section Lift
variable {L n k : ℕ}
theorem link_isPositivelyOriented_or_opposite {a : ℝ} (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem expTwist_liftGaugeField
    (hq : ∀ b : Tower.FullSpace.Edge L k 0,
      (b.IsPositivelyOriented → (Tower.FullSpace.projEdge L n k 0 b).IsPositivelyOriented) ∧
      (Tower.FullSpace.projEdge L n k 0 b).opposite = Tower.FullSpace.projEdge L n k 0 b.opposite)
    (hx : ∀ b : Tower.Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (C U : Tower.Edge L n k 0 → ComplexMatrix2) :
    Tower.FullSpace.expTwist (liftGaugeField L n k 0 C) (liftGaugeField L n k 0 U) =
      liftGaugeField L n k 0 (PeriodicLattice.expTwist C U) := by
  classical
  funext b
  by_cases hb : b.IsPositivelyOriented
  · have h' := (hq b).1 hb
    simp only [Tower.FullSpace.expTwist, if_pos hb, liftGaugeField,
      PeriodicLattice.expTwist, if_pos h']
  · have hr : b.opposite.IsPositivelyOriented :=
      (link_isPositivelyOriented_or_opposite b).resolve_left hb
    have h' : ¬ (Tower.FullSpace.projEdge L n k 0 b).IsPositivelyOriented := by
      have hp := (hq b.opposite).1 hr
      have e : (Tower.FullSpace.projEdge L n k 0 b).opposite =
          Tower.FullSpace.projEdge L n k 0 b.opposite := (hq b).2
      rw [← e] at hp
      rcases hx (Tower.FullSpace.projEdge L n k 0 b) with h | h
      exacts [absurd hp h.2, h.2]
    simp only [Tower.FullSpace.expTwist, if_neg hb, liftGaugeField,
      PeriodicLattice.expTwist, if_neg h', (hq b).2]
theorem liftGaugeField_mem_complexEdgeForms
    (hq : ∀ b : Tower.FullSpace.Edge L k 0,
      (b.IsPositivelyOriented → (Tower.FullSpace.projEdge L n k 0 b).IsPositivelyOriented) ∧
      (Tower.FullSpace.projEdge L n k 0 b).opposite = Tower.FullSpace.projEdge L n k 0 b.opposite)
    {B : Tower.Edge L n k 0 → ComplexMatrix2} (hB : B ∈ Tower.complexEdgeForms L n k 0) :
    liftGaugeField L n k 0 B ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0) := by
  refine ⟨fun b hb => hB.1 _ ((hq b).1 hb), fun b => ?_⟩
  show B (Tower.FullSpace.projEdge L n k 0 b.opposite) = -B (Tower.FullSpace.projEdge L n k 0 b)
  rw [← (hq b).2]
  exact hB.2 _
end Lift
theorem quadraticTermOfLift_holds
    (h₁ : Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (h₂ : LocalKernels.IterMeansOfLift.Claim)
    (h₃ : Tower.MeanStableFields.MeanStableFieldsHold)
    (h₄ : Tower.IteratedMeans.IteratedMeansHold)
    (h₅ : Tower.BondSetFields.ProductStructureHolds)
    (h₆ : Tower.EdgeProjectionProperties)
    (h₇ : PeriodicLattice.LevelBondOrientationDichotomy)
    (h₈ : ComplexMatrix2.ExpLogEstimates) :
    LocalKernels.QuadraticTermOfLift := by
  classical
  intro L hL k n hn hk U hU hS B hB B' hB' c
  have hD := h₁ L hL k hk
  have hq := (hD.1 n hn).2.1 U hS
  have hW : liftGaugeField L n k 0 U ∈ Tower.FullSpace.smallIterateFields L k :=
    (h₂ L hL k n hn hk U hU).1.1 hS
  have hq' := hD.2.2 _ hW
  have hPs := (h₃ L hL k hk).1 n hn
  have hPw := (h₃ L hL k hk).2
  have hOs := (h₄ L hL k hk).1 n hn
  have hOw := (h₄ L hL k hk).2
  have hfin : (univ : Set (Tower.Edge L n k 0)).Finite :=
    ((h₅ L hL k 0 (Nat.zero_le k)).1 n hn).2.1
  have hx : ∀ b : Tower.Edge L n k 0, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    h₇ L n k hL hn hk 0 (Nat.zero_le k)
  have hQ : ∀ b : Tower.FullSpace.Edge L k 0,
      (b.IsPositivelyOriented → (Tower.FullSpace.projEdge L n k 0 b).IsPositivelyOriented) ∧
      (Tower.FullSpace.projEdge L n k 0 b).opposite =
        Tower.FullSpace.projEdge L n k 0 b.opposite :=
    fun b => ⟨((h₆ L n k 0 hL hn (Nat.zero_le k)).1 b).2.2.1,
      ((h₆ L n k 0 hL hn (Nat.zero_le k)).1 b).2.2.2⟩
  have hbd : ∀ {A : Tower.Edge L n k 0 → ComplexMatrix2},
      ∃ C : ℝ, ∀ b, ComplexMatrix2.operatorNorm (A b) ≤ C := by
    intro A
    have : Finite (Tower.Edge L n k 0) := Set.finite_univ_iff.1 hfin
    exact Finite.exists_le fun b => ComplexMatrix2.operatorNorm (A b)
  have hBb : ∀ {A : Tower.Edge L n k 0 → ComplexMatrix2}, A ∈ Tower.complexEdgeForms L n k 0 →
      A ∈ boundedSubmodule (Tower.complexEdgeForms L n k 0) := fun hA => ⟨hA, hbd⟩
  have hEb : ∀ {A : Tower.Edge L n k 0 → ComplexMatrix2}, A ∈ Tower.complexEdgeForms L n k 0 →
      liftGaugeField L n k 0 A ∈
        boundedSubmodule (Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0)) := fun {A} hA => by
    obtain ⟨C, hC⟩ := hbd (A := A)
    exact ⟨liftGaugeField_mem_complexEdgeForms hQ hA, C, fun b => hC _⟩
  have hc : (projPositiveEdge L n k k c).1 = Tower.FullSpace.projEdge L n k k c.1 :=
    Classical.epsilon_spec (p := fun d : Tower.PositiveEdge L n k k =>
      d.1 = Tower.FullSpace.projEdge L n k k c.1)
      ⟨⟨_, ((h₆ L n k k hL hn le_rfl).1 c.1).2.2.1 c.2⟩, rfl⟩
  have hval : ∀ {V : Tower.Edge L n k 0 → ComplexMatrix2}, V ∈ Tower.smallIterateFields L n k →
      Tower.FullSpace.AsDifferentials.iterMean (liftGaugeField L n k 0 V) k c.1 =
        Tower.AsDifferentials.iterMean V k (projPositiveEdge L n k k c).1 := by
    intro V hV
    have hVw := (h₂ L hL k n hn hk V hV.1).1.1 hV
    have hVe := (h₂ L hL k n hn hk V hV.1).2 hV k le_rfl
    rw [fullSpace_iterMean_eq_complexIter hPw hOw hVw,
      iterMean_eq_complexBlockFieldAtLevel hPs hOs hV, hVe, hc]
    rfl
  have hnear : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0),
      Tower.FullSpace.AsDifferentials.topLogRatio L k (liftGaugeField L n k 0 U) c
          (p.1 • liftGaugeField L n k 0 B + p.2 • liftGaugeField L n k 0 B') =
        Tower.AsDifferentials.topLogRatio L n k U (projPositiveEdge L n k k c)
          (p.1 • B + p.2 • B') := by
    filter_upwards [eventually_expTwist_mem_smallIterateFields h₈ hPs hOs hfin hx hS hB hB']
      with p hp
    have e : p.1 • liftGaugeField L n k 0 B + p.2 • liftGaugeField L n k 0 B' =
        liftGaugeField L n k 0 (p.1 • B + p.2 • B') := rfl
    rw [e]
    simp only [Tower.FullSpace.AsDifferentials.topLogRatio, Tower.AsDifferentials.topLogRatio,
      Tower.FullSpace.AsDifferentials.iterLogRatio, Tower.AsDifferentials.iterLogRatio,
      Tower.FullSpace.AsDifferentials.iterRatio, Tower.AsDifferentials.iterRatio]
    rw [expTwist_liftGaugeField hQ hx, hval hp, hval hS]
  simp only [Tower.FullSpace.AsDifferentials.complexQuadraticTerm,
    Tower.AsDifferentials.complexQuadraticTerm,
    quadraticTermAt, dif_pos (And.intro (hEb hB) (hEb hB')),
    dif_pos (And.intro (hBb hB) (hBb hB'))]
  rw [← (hq'.2.2 ⟨_, hEb hB⟩ ⟨_, hEb hB'⟩ c).1,
    ← (hq.2.2 ⟨B, hBb hB⟩ ⟨B', hBb hB'⟩ (projPositiveEdge L n k k c)).1]
  simp only [Tower.mixedDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
  exact deriv_deriv_congr_of_eventuallyEq
    (f := fun s t => Tower.FullSpace.AsDifferentials.topLogRatio L k (liftGaugeField L n k 0 U) c
      (s • liftGaugeField L n k 0 B + t • liftGaugeField L n k 0 B'))
    (g := fun s t => Tower.AsDifferentials.topLogRatio L n k U
      (projPositiveEdge L n k k c) (s • B + t • B')) hnear
end YangMills.Construction.LocalKernels.LiftQuadraticTerm
end
