import YangMills.Construction.PeriodicOperators.IndexSetsOfATowerProof
import YangMills.Construction.PeriodicOperators.TranslationsOnTheIndexSetsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TowerTranslations
open YangMills.Construction.Tower
section OneLattice
variable {a : ℝ} {N : ℕ}
theorem castVec_mem_latticeSubgroup (h : a * N = 1) (n : Fin 4 → ℤ) :
    castVec n ∈ InfiniteLattice.latticeSubgroup a := by apply _root_.YangMills.Construction.PeriodicOperators.TowerIndexSets.castVec_mem_latticeSubgroup <;> assumption
theorem intShift_mapsSublatticeOnto (h : a * N = 1) (n : Fin 4 → ℤ) :
    FullSpace.MapsSublatticeOnto a (intShift n) := by
  have hn := castVec_mem_latticeSubgroup h n
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact add_mem hx hn
  · intro hy
    exact ⟨y - castVec n, sub_mem hy hn, by simp [intShift]⟩
theorem vertexImage_intShift (h : a * N = 1) (n : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint a) :
    FullSpace.vertexImage (intShift n) x = x + ⟨castVec n, castVec_mem_latticeSubgroup h n⟩ :=
  Subtype.ext (Classical.epsilon_spec
    (p := fun x' : InfiniteLattice.LatticePoint a =>
      (x' : InfiniteLattice.AmbientSpace) = intShift n x)
    ⟨x + ⟨castVec n, castVec_mem_latticeSubgroup h n⟩, rfl⟩)
theorem edgeImage_intShift_forwardFrom (h : a * N = 1) (n : Fin 4 → ℤ)
    (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    FullSpace.edgeImage (intShift n) (InfiniteLattice.Link.forwardFrom x μ) =
      InfiniteLattice.Link.forwardFrom (FullSpace.vertexImage (intShift n) x) μ := by
  have hstep : FullSpace.vertexImage (intShift n) (x + InfiniteLattice.axisStep a μ) =
      FullSpace.vertexImage (intShift n) x + InfiniteLattice.axisStep a μ := by
    rw [vertexImage_intShift h, vertexImage_intShift h]
    abel
  have spec := Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link a =>
      b'.initial = FullSpace.vertexImage (intShift n)
          (InfiniteLattice.Link.forwardFrom x μ).initial ∧
        b'.terminal = FullSpace.vertexImage (intShift n)
          (InfiniteLattice.Link.forwardFrom x μ).terminal)
    ⟨InfiniteLattice.Link.forwardFrom (FullSpace.vertexImage (intShift n) x) μ, rfl, hstep.symm⟩
  have spec' : (FullSpace.edgeImage (intShift n) (InfiniteLattice.Link.forwardFrom x μ)).initial =
        FullSpace.vertexImage (intShift n) x ∧
      (FullSpace.edgeImage (intShift n) (InfiniteLattice.Link.forwardFrom x μ)).terminal =
        FullSpace.vertexImage (intShift n) (x + InfiniteLattice.axisStep a μ) := spec
  exact InfiniteLattice.Link.ext spec'.1 (spec'.2.trans hstep)
end OneLattice
theorem meshAt_mul_pow {L k j : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) :
    meshAt L k j * ((L ^ (k - j) : ℕ) : ℝ) = 1 := by
  have hL0 : (L : ℝ) ≠ 0 := by
    have : 0 < L := by
      have := hL.2
      omega
    exact_mod_cast this.ne'
  have he : (j : ℤ) - (k : ℤ) + ((k - j : ℕ) : ℤ) = 0 := by omega
  unfold meshAt
  rw [Nat.cast_pow, ← zpow_natCast, ← zpow_add₀ hL0, he, zpow_zero]
theorem shiftEdge_eq {L k j N : ℕ} (h : meshAt L k j * N = 1) (n : Fin 4 → ℤ)
    (b : PosEdge L k j) (μ : Fin 4)
    (hb : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L k j) μ) :
    shiftEdge n b = posEdgeForward (FullSpace.vertexImage (intShift n) b.1.initial) μ := by
  have hf : b.1 = InfiniteLattice.Link.forwardFrom b.1.initial μ :=
    InfiniteLattice.Link.ext rfl (by
      show b.1.terminal = b.1.initial + InfiniteLattice.axisStep (meshAt L k j) μ
      rw [← hb]
      abel)
  have hm : FullSpace.edgeImage (intShift n) b.1 =
      InfiniteLattice.Link.forwardFrom (FullSpace.vertexImage (intShift n) b.1.initial) μ :=
    (congrArg (FullSpace.edgeImage (intShift n)) hf).trans (edgeImage_intShift_forwardFrom h n _ μ)
  have spec := Classical.epsilon_spec
    (p := fun b' : PosEdge L k j => b'.1 = FullSpace.edgeImage (intShift n) b.1)
    ⟨posEdgeForward (FullSpace.vertexImage (intShift n) b.1.initial) μ, hm.symm⟩
  exact Subtype.ext (spec.trans hm)
theorem claim_holds : Claim := by
  intro L hL k j _ hj n
  have h := meshAt_mul_pow (k := k) (j := j) hL hj
  have hm := vertexImage_intShift h n
  refine ⟨intShift_mapsSublatticeOnto h n,
    fun x => ⟨?_, fun μ => edgeImage_intShift_forwardFrom h n x μ, fun μ ν hμν => ?_⟩,
    fun c x => rfl, fun c b μ hb => ?_, fun c x μ ν hμν => rfl⟩
  · rw [hm]
    rfl
  · simp only [FullSpace.faceCorners, Set.image_insert_eq, Set.image_singleton, hm]
    rw [add_right_comm (x + InfiniteLattice.axisStep _ μ) (InfiniteLattice.axisStep _ ν),
      add_right_comm x (InfiniteLattice.axisStep _ μ), add_right_comm x (InfiniteLattice.axisStep _ ν)]
  · exact congrArg (Prod.mk c) (shiftEdge_eq h n b μ hb)
end YangMills.Construction.PeriodicOperators.TowerTranslations
end
