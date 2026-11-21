import YangMills.Construction.Lattice.BlocksInTheCoordinatesOfAFinerLatticeProof
import YangMills.Construction.Towers.KernelsOfPeriodicLocalBilinearMapsProof
import YangMills.Construction.Towers.LatticesOfSideInfinityOverAFiniteSide
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.MatricesOfLinearMaps
open Periodisation Tower
open PeriodicOperators (KernelMatrix applyKernel HasFiniteSupport wTranspose)
open InfiniteLattice (AmbientSpace)
open TorusMetric (supNormVec)
open FullLatticeOverTorus (LocallyFiniteCells)
theorem abs_le_supNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ supNormVec v := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.abs_le_supNormVec <;> assumption
theorem supNormVec_sub_comm (x y : Fin 4 → ℝ) : supNormVec (x - y) = supNormVec (y - x) := by apply _root_.YangMills.Construction.LocalKernels.LocalBilinearKernels.supNormVec_sub_comm <;> assumption
theorem isBounded_supNormVec_sub_le (y : AmbientSpace) (R : ℝ) :
    Bornology.IsBounded {x : AmbientSpace | supNormVec (x - y) ≤ R} := by
  refine (Metric.isBounded_closedBall (x := y) (r := max R 0)).subset ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff (le_max_right _ _)]
  intro μ
  rw [Real.dist_eq]
  exact ((abs_le_supNormVec (x - y) μ).trans hx).trans (le_max_left _ _)
theorem finite_cells_near {L k j : ℕ} (h : LocallyFiniteCells L k j) (c : CellType)
    (y : AmbientSpace) (R : ℝ) :
    {x : Cell L k j c | supNormVec (Cell.anchor x - y) ≤ R}.Finite := by
  obtain ⟨h₁, h₂, h₃⟩ := h _ (isBounded_supNormVec_sub_le y R)
  cases c
  · exact h₁
  · exact h₂
  · exact h₃
theorem finite_forget_mem {A : Type} {S : Set A} (hS : S.Finite) (c : Bool) :
    {e : WithColour A c | WithColour.forget e ∈ S}.Finite := by
  cases c
  · exact hS
  · refine ((finite_univ (α := Fin 3)).prod hS).subset ?_
    rintro ⟨a, x⟩ hx
    exact ⟨mem_univ _, hx⟩
theorem finite_indices_near {L k : ℕ} (h : ∀ j ≤ k, LocallyFiniteCells L k j)
    (I : WeightedIndexSet k) (y : AmbientSpace) (R : ℝ) :
    {ι : (I.toPeriodicData L).Carrier | supNormVec ((I.toPeriodicData L).pos ι - y) ≤ R}.Finite := by
  have := I.finite_slot
  have hp : ∀ p : I.Slot,
      {e : (I.comp p).Elem L |
        supNormVec (Cell.anchor (WithColour.forget e) - y) ≤ R}.Finite := fun p =>
    finite_forget_mem (finite_cells_near (h _ (I.comp p).level_le) (I.comp p).cellType y R) _
  refine (finite_iUnion fun p => (hp p).image (Sigma.mk p)).subset ?_
  rintro ⟨p, e⟩ hι
  exact mem_iUnion.2 ⟨p, e, hι, rfl⟩
theorem wPairing_wTranspose {N N' : Type} (w : N → ℝ) (w' : N' → ℝ) (hw : ∀ i, w i ≠ 0)
    (T : N' → N → ℂ) (hcol : ∀ i, {i' | T i' i ≠ 0}.Finite) (g : N' → ℂ) (f : N → ℂ)
    (hf : (Function.support f).Finite) :
    PeriodicOperators.wPairing w (applyKernel (wTranspose w w' T) g) f =
      PeriodicOperators.wPairing w' g (applyKernel T f) := by
  classical
  set F : Finset N := hf.toFinset with hFdef
  set G : Finset N' := (hf.biUnion fun i _ => hcol i).toFinset with hGdef
  have hF : ∀ i, i ∉ F → f i = 0 := fun i hi => by
    by_contra h0
    exact hi (hf.mem_toFinset.2 h0)
  have hG : ∀ i', i' ∉ G → ∀ i ∈ F, T i' i = 0 := fun i' hi' i hi => by
    by_contra h0
    exact hi' ((hf.biUnion fun i _ => hcol i).mem_toFinset.2
      (mem_iUnion₂.2 ⟨i, hf.mem_toFinset.1 hi, h0⟩))
  have actT : ∀ i', applyKernel T f i' = ∑ i ∈ F, T i' i * f i := fun i' =>
    tsum_eq_sum fun i hi => by simp [hF i hi]
  have actTt : ∀ i ∈ F, applyKernel (wTranspose w w' T) g i =
      ∑ i' ∈ G, wTranspose w w' T i i' * g i' := fun i hi =>
    tsum_eq_sum fun i' hi' => by simp [wTranspose, hG i' hi' i hi]
  have hzero : ∀ i', i' ∉ G → applyKernel T f i' = 0 := fun i' hi' => by
    rw [actT]
    exact Finset.sum_eq_zero fun i hi => by simp [hG i' hi' i hi]
  unfold PeriodicOperators.wPairing
  rw [tsum_eq_sum (s := F) (fun i hi => by simp [hF i hi]),
    tsum_eq_sum (s := G) (fun i' hi' => by simp [hzero i' hi'])]
  calc ∑ i ∈ F, (w i : ℂ) * (applyKernel (wTranspose w w' T) g i * f i)
      = ∑ i ∈ F, ∑ i' ∈ G, (w' i' : ℂ) * (g i' * (T i' i * f i)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [actTt i hi, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i' _ => ?_
        have h0 : (w i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hw i)
        simp only [wTranspose]
        push_cast
        field_simp
    _ = ∑ i' ∈ G, ∑ i ∈ F, (w' i' : ℂ) * (g i' * (T i' i * f i)) := Finset.sum_comm
    _ = ∑ i' ∈ G, (w' i' : ℂ) * (g i' * applyKernel T f i') := by
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [actT, Finset.mul_sum, Finset.mul_sum]
theorem localKernelFacts_of_locallyFinite {L k : ℕ} (h : ∀ j ≤ k, LocallyFiniteCells L k j) :
    LocalKernelFacts (k := k) L := by
  intro I I' R _ T hT
  have rowFin : ∀ ι', {ι | T ι' ι ≠ 0}.Finite := fun ι' =>
    (finite_indices_near h I ((I'.toPeriodicData L).pos ι') R).subset fun ι hι => by
      by_contra hn
      exact hι (hT ι' ι hn)
  have colFin : ∀ ι, {ι' | T ι' ι ≠ 0}.Finite := fun ι =>
    (finite_indices_near h I' ((I.toPeriodicData L).pos ι) R).subset fun ι' hι' => by
      by_contra hn
      refine hι' (hT ι' ι fun hle => hn ?_)
      show supNormVec ((I'.toPeriodicData L).pos ι' - (I.toPeriodicData L).pos ι) ≤ R
      rw [supNormVec_sub_comm]
      exact hle
  have hw : ∀ ι, (I.toPeriodicData L).weightOf ι ≠ 0 := fun ι => (I.comp ι.1).weight_pos.ne'
  refine ⟨fun f ι' => (rowFin ι').subset fun ι hι => left_ne_zero_of_mul hι, fun f hf => ?_,
    fun ι ι' hn => ?_, fun g f hf => wPairing_wTranspose _ _ hw T colFin g f hf⟩
  · refine (hf.biUnion fun ι _ => colFin ι).subset fun ι' hι' => ?_
    by_contra hn
    refine hι' ?_
    have hz : ∀ ι, T ι' ι * f ι = 0 := fun ι => by
      by_contra h0
      exact hn (mem_iUnion₂.2 ⟨ι, right_ne_zero_of_mul h0, left_ne_zero_of_mul h0⟩)
    simp [applyKernel, hz]
  · have hz : T ι' ι = 0 := hT ι' ι fun hle => hn (by
      rw [supNormVec_sub_comm]
      exact hle)
    simp [kernelT, wTranspose, hz]
theorem existsUnique_matrix {N N' : Type} [Finite N] (m : (N → ℂ) →ₗ[ℂ] (N' → ℂ)) :
    ∃! M : KernelMatrix N N', IsRepresentedBy univ m M := by
  classical
  have := Fintype.ofFinite N
  have act : ∀ (M : KernelMatrix N N') (f : N → ℂ) (i' : N'),
      applyKernel M f i' = ∑ i, M i' i * f i := fun M f i' => tsum_fintype _
  refine ⟨fun i' i => m (fun j => if i = j then 1 else 0) i', fun f _ => ?_, fun M' hM' => ?_⟩
  · funext i'
    rw [act, LinearMap.pi_apply_eq_sum_univ m f]
    simp [Finset.sum_apply, mul_comm]
  · funext i' i
    have h := congrFun (hM' (fun j => if i = j then 1 else 0) (mem_univ _)) i'
    rw [act] at h
    simpa using h.symm
theorem kernelsAndLinearMapMatrices_holds (hCells : PeriodicLiftCells.CellsAndClassesHold)
    (hLattices : FullLatticeOverTorus.FullLatticeOverTorusClaim) :
    KernelsAndLinearMapMatrices := by
  intro L hL k m hm
  refine ⟨localKernelFacts_of_locallyFinite fun j hj => (hLattices L hL k j hj m hm).2.2.2.1,
    fun I I' f => ?_⟩
  have : Finite (I.ImageCarrier L m) := ((hCells L hL k m hm).2 I).1
  exact existsUnique_matrix f
end YangMills.Construction.LocalKernels.MatricesOfLinearMaps
end
