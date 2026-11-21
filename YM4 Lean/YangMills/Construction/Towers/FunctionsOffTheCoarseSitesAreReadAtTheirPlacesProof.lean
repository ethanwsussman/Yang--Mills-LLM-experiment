import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtensionProof
import YangMills.Construction.Towers.FunctionsOffTheCoarseSitesAreReadAtTheirPlaces
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.UnitScale.FineOnlyVertexCoordinates
open OneStepChart FullLatticeOverTorus
open InfiniteLattice (AmbientSpace)
variable {L m k j : ℕ}
theorem isSlotEvaluation_self (ι : Type) :
    IsSlotEvaluation (Tower.pairedFunctions ι) ι (fun f => f) where
  eval_mem := fun _ hf p => hf p (mem_univ p)
  exists_eval_eq := fun w hw => ⟨w, fun p _ => hw p, rfl⟩
  eq_of_eval_eq := fun _ _ _ _ h => h
  eval_add := fun _ _ _ _ => rfl
  eval_smul := fun _ _ _ => rfl
  isFinitelySupported_iff := fun _ _ => Iff.rfl
  pair_eq := fun _ _ => rfl
theorem dite_mem_traceless {c : Prop} (d : Decidable c) (a : c → Matrices.ComplexMatrix2)
    (h : ∀ hc, a hc ∈ Matrices.ComplexMatrix2.traceless) :
    @dite _ c d a (fun _ => 0) ∈ Matrices.ComplexMatrix2.traceless := by
  by_cases hc : c
  · rw [dif_pos hc]
    exact h hc
  · rw [dif_neg hc]
    exact Submodule.zero_mem _
theorem torusProj_eq_iff (S : ℝ) (x y : AmbientSpace) :
    TorusMetric.torusProj S x = TorusMetric.torusProj S y ↔
      ∃ n : Fin 4 → ℤ, ∀ μ, y μ = x μ + (n μ : ℝ) * S := by apply _root_.YangMills.Construction.LocalKernels.PeriodicLiftCells.torusProj_eq_iff <;> assumption
theorem integerPoint_coe_apply {a : ℝ}
    (h : InfiniteLattice.latticeSubgroup 1 ≤ InfiniteLattice.latticeSubgroup a)
    (z : Fin 4 → ℤ) (μ : Fin 4) : (integerPoint a z : AmbientSpace) μ = (z μ : ℝ) := by
  let y : InfiniteLattice.LatticePoint 1 := ⟨fun μ => (z μ : ℝ), z, fun μ => by simp⟩
  have e : ((FullSpace.toFiner a y : InfiniteLattice.LatticePoint a) : AmbientSpace) = y :=
    Classical.epsilon_spec (p := fun x : InfiniteLattice.LatticePoint a => (x : AmbientSpace) = y)
      ⟨⟨y, h y.2⟩, rfl⟩
  exact congrFun e μ
theorem intCast_mem_latticeSubgroup {a : ℝ}
    (h : InfiniteLattice.latticeSubgroup 1 ≤ InfiniteLattice.latticeSubgroup a)
    (z : Fin 4 → ℤ) : (fun μ => (z μ : ℝ) : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a :=
  h ⟨z, fun μ => by simp⟩
theorem mem_of_projVertex_mem (hc : PeriodsInSublattice L m k (j + 1))
    (hq : TorusQuotientMapsVerticesAndEdges L m k (j + 1)) (x : FullSpace.Vertex L k j)
    (h : ((FullSpace.projVertex L m k j x : Tower.Vertex L m k j) : PeriodicLattice.FourTorus L m) ∈
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k (j + 1))) :
    (x : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (Tower.meshAt L k (j + 1)) := by
  have h' : ((FullSpace.projVertex L m k j x : Tower.Vertex L m k j) :
      PeriodicLattice.FourTorus L m) ∈
      torusQuotient L m '' (InfiniteLattice.latticeSubgroup (Tower.meshAt L k (j + 1)) :
        Set AmbientSpace) := by
    rw [hq.1]
    exact h
  obtain ⟨y, hy, e⟩ := h'
  obtain ⟨n, hn⟩ := (torusProj_eq_iff _ _ _).1 e
  have hw : (fun μ => (n μ : ℝ) * PeriodicLattice.torusSide L m : AmbientSpace) ∈
      InfiniteLattice.latticeSubgroup (Tower.meshAt L k (j + 1)) := hc.2 ⟨n, fun _ => rfl⟩
  have e' : (x : AmbientSpace) =
      y + (fun μ => (n μ : ℝ) * PeriodicLattice.torusSide L m : AmbientSpace) :=
    funext fun μ => hn μ
  rw [e']
  exact add_mem hy hw
theorem projVertex_mem_of_mem (hq : TorusQuotientMapsVerticesAndEdges L m k (j + 1))
    (x : FullSpace.Vertex L k j)
    (h : (x : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup (Tower.meshAt L k (j + 1))) :
    ((FullSpace.projVertex L m k j x : Tower.Vertex L m k j) : PeriodicLattice.FourTorus L m) ∈
      PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k (j + 1)) := by
  have h' : ((FullSpace.projVertex L m k j x : Tower.Vertex L m k j) :
      PeriodicLattice.FourTorus L m) ∈
      torusQuotient L m '' (InfiniteLattice.latticeSubgroup (Tower.meshAt L k (j + 1)) :
        Set AmbientSpace) :=
    ⟨x, h, rfl⟩
  rw [hq.1] at h'
  exact h'
theorem fundamentalCube_isBounded : Bornology.IsBounded (fundamentalCube L m) := by apply _root_.YangMills.Construction.LocalKernels.PeriodicLiftCells.fundamentalCube_isBounded <;> assumption
theorem finite_vertex (hq : TorusQuotientMapsVerticesAndEdges L m k j)
    (hT : ∀ N : Fin 4 → ℤ, ShiftSurjectiveOnVertices L k j N)
    (hF : LocallyFiniteCells L k j) (hA : ShiftedFromFundamentalCube L m k j)
    (hP : TorusQuotientPeriodic L m) : Finite (Tower.Vertex L m k j) := by
  have hfin := (hF _ (fundamentalCube_isBounded (L := L) (m := m))).1
  have := hfin.to_subtype
  refine Finite.of_surjective
    (fun y : {x : FullSpace.Vertex L k j | (x : AmbientSpace) ∈ fundamentalCube L m} =>
      FullSpace.projVertex L m k j y.1) ?_
  intro t
  have ht : (t : PeriodicLattice.FourTorus L m) ∈
      torusQuotient L m '' (InfiniteLattice.latticeSubgroup (Tower.meshAt L k j) :
        Set AmbientSpace) := by
    rw [hq.1]
    exact t.2
  obtain ⟨x, hx, e⟩ := ht
  obtain ⟨y, N, hy, hN, ey⟩ := hA.1 ⟨x, hx⟩
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  have e₁ : x = (y : AmbientSpace) + PeriodicOperators.castVec N := by
    rw [← (hT N).2 y, ey]
  change torusQuotient L m (y : AmbientSpace) = t
  rw [← e, e₁, hP _ _ hN]
theorem statement_holds (h₁ : FullLatticeOverTorusClaim) : Statement := by
  intro L hL m k j hm hj
  obtain ⟨hc, -, hT, hF, -, hA, hP⟩ := h₁ L hL k j hj.le m hm
  have hqj := (h₁ L hL k j hj.le m hm).2.1
  obtain ⟨hc', hq', -⟩ := h₁ L hL k (j + 1) hj m hm
  have hval : ∀ (x : FullSpace.Vertex L k j) (z : Fin 4 → ℤ) (μ : Fin 4),
      ((x + integerPoint _ z : FullSpace.Vertex L k j) : AmbientSpace) μ =
        (x : AmbientSpace) μ + (z μ : ℝ) :=
    fun x z μ => by
      change (x : AmbientSpace) μ + (integerPoint _ z : AmbientSpace) μ = _
      rw [integerPoint_coe_apply hc.1]
  have hshift : ∀ (z : Fin 4 → ℤ)
      (x : FullSpace.FineOnlyVertex (Tower.meshAt L k (j + 1)) (Tower.meshAt L k j)),
      ((x.1 + integerPoint _ z : FullSpace.Vertex L k j) : AmbientSpace) ∉
        InfiniteLattice.latticeSubgroup (Tower.meshAt L k (j + 1)) := by
    intro z x h
    apply x.2
    have e : (x.1 : AmbientSpace) =
        ((x.1 + integerPoint _ z : FullSpace.Vertex L k j) : AmbientSpace) -
          (fun μ => (z μ : ℝ) : AmbientSpace) := funext fun μ => by
      rw [Pi.sub_apply, hval]
      ring
    rw [e]
    exact sub_mem h (intCast_mem_latticeSubgroup hc'.1 z)
  have hquot : ∀ x : FullSpace.FineOnlyVertex (Tower.meshAt L k (j + 1)) (Tower.meshAt L k j),
      ((FullSpace.projVertex L m k j x.1 : Tower.Vertex L m k j) :
        PeriodicLattice.FourTorus L m) ∉
        PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth k (j + 1)) :=
    fun x h => x.2 (mem_of_projVertex_mem hc' hq' x.1 h)
  have hfin : Finite (Tower.Vertex L m k j) := finite_vertex hqj (fun N => (hT N).1) hF hA hP
  have hside : ∀ (n : Fin 4 → ℤ) (μ : Fin 4),
      ((((2 * L ^ m) • n) μ : ℤ) : ℝ) = (n μ : ℝ) * PeriodicLattice.torusSide L m := by
    intro n μ
    simp [PeriodicLattice.torusSide]
    ring
  refine ⟨{
    TorusSlot := Tower.FineOnlyVertex L m k j
    torusEval := fun f => f
    proj := fun x => ⟨FullSpace.projVertex L m k j x.1, hquot x⟩
    shiftSlot := fun z x => ⟨x.1 + integerPoint _ z, hshift z x⟩
    full_basis := isSlotEvaluation_self _
    torus_coordinates := isSlotEvaluation_self _
    finite_torusSlot := Subtype.finite
    extend_mem := fun f hf x _ => dite_mem_traceless _ _ fun _ => hf _ (mem_univ _)
    eval_extend := fun f _ p => dif_pos (hquot p)
    proj_surjective := ?_
    proj_eq_iff := ?_
    shiftSlot_zero := ?_
    shiftSlot_add := ?_
    eq_zero_of_shiftSlot_eq := ?_
    shift_mem := fun z f hf x _ => dite_mem_traceless _ _ fun _ => hf _ (mem_univ _)
    eval_shift := fun z f _ p => dif_pos (hshift (-z) p) }⟩
  · rintro ⟨t, ht⟩
    have h' : (t : PeriodicLattice.FourTorus L m) ∈
        torusQuotient L m '' (InfiniteLattice.latticeSubgroup (Tower.meshAt L k j) :
          Set AmbientSpace) := by
      rw [hqj.1]
      exact t.2
    obtain ⟨x, hx, e⟩ := h'
    have et : FullSpace.projVertex L m k j ⟨x, hx⟩ = t := Subtype.ext e
    refine ⟨⟨⟨x, hx⟩, fun h => ht ?_⟩, Subtype.ext et⟩
    rw [← et]
    exact projVertex_mem_of_mem hq' _ h
  · intro p p'
    constructor
    · intro e
      have e₁ : TorusMetric.torusProj (PeriodicLattice.torusSide L m) (p.1 : AmbientSpace) =
          TorusMetric.torusProj (PeriodicLattice.torusSide L m) (p'.1 : AmbientSpace) :=
        congrArg (fun t : Tower.FineOnlyVertex L m k j =>
          ((t.1 : Tower.Vertex L m k j) : PeriodicLattice.FourTorus L m)) e
      obtain ⟨n, hn⟩ := (torusProj_eq_iff _ _ _).1 e₁
      refine ⟨n, Subtype.ext (Subtype.ext (funext fun μ => ?_))⟩
      change (p'.1 : AmbientSpace) μ =
        ((p.1 + integerPoint _ _ : FullSpace.Vertex L k j) : AmbientSpace) μ
      rw [hval, hn μ, hside]
    · rintro ⟨v, rfl⟩
      apply Subtype.ext
      apply Subtype.ext
      refine (torusProj_eq_iff _ _ _).2 ⟨v, fun μ => ?_⟩
      change ((p.1 + integerPoint _ _ : FullSpace.Vertex L k j) : AmbientSpace) μ = _
      rw [hval, hside]
  · intro p
    refine Subtype.ext (Subtype.ext (funext fun μ => ?_))
    change ((p.1 + integerPoint _ _ : FullSpace.Vertex L k j) : AmbientSpace) μ = _
    rw [hval]
    simp
  · intro z z' p
    refine Subtype.ext (Subtype.ext (funext fun μ => ?_))
    change ((p.1 + integerPoint _ _ : FullSpace.Vertex L k j) : AmbientSpace) μ =
      (((p.1 + integerPoint _ z' : FullSpace.Vertex L k j) + integerPoint _ z :
        FullSpace.Vertex L k j) : AmbientSpace) μ
    rw [hval, hval, hval, Pi.add_apply]
    push_cast
    ring
  · intro z p e
    funext μ
    have e₁ := congrFun (congrArg (fun t : FullSpace.FineOnlyVertex
      (Tower.meshAt L k (j + 1)) (Tower.meshAt L k j) =>
        ((t.1 : FullSpace.Vertex L k j) : AmbientSpace)) e) μ
    change ((p.1 + integerPoint _ z : FullSpace.Vertex L k j) : AmbientSpace) μ = _ at e₁
    rw [hval] at e₁
    have : (z μ : ℝ) = 0 := by linarith
    exact_mod_cast this
end YangMills.Construction.Tower.UnitScale.FineOnlyVertexCoordinates
end
