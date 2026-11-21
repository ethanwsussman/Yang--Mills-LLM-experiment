import YangMills.Construction.Towers.BlocksOfATowerProof
import YangMills.Construction.InfiniteLattice.MeasurabilityIsDependenceOnVariablesAtEverySpacingProof
import YangMills.Construction.Lattice.LatticeIsometriesAsMapsOfPairsProof
import YangMills.Construction.Towers.LatticesOfSideInfinityOverAFiniteSide
import YangMills.Construction.Towers.SymbolsOfTheAveragesOnPlaneWavesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.FullLatticeOverTorus
open InfiniteLattice (AmbientSpace)
open Tower
open PeriodicOperators (castVec intShift shiftEdge shiftFace PosEdge)
theorem latticeSubgroup_le_of_eq_zmul {a b : ℝ} (M : ℤ) (h : b = (M : ℝ) * a) :
    InfiniteLattice.latticeSubgroup b ≤ InfiniteLattice.latticeSubgroup a := by
  rintro x ⟨N, hN⟩
  refine ⟨fun μ => N μ * M, fun μ => ?_⟩
  rw [hN μ, h]
  push_cast
  ring
theorem meshAt_pos {L : ℕ} (hL : 0 < L) (k j : ℕ) : 0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.meshAt_pos <;> assumption
theorem one_eq_intCast_mul_meshAt {L k j : ℕ} (hL : 0 < L) (h : j ≤ k) :
    (1 : ℝ) = (((L : ℤ) ^ (k - j) : ℤ) : ℝ) * meshAt L k j := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : (j : ℤ) - (k : ℤ) = -((k - j : ℕ) : ℤ) := by
    rw [Nat.cast_sub h]
    ring
  rw [meshAt, e, zpow_neg, zpow_natCast]
  push_cast
  rw [mul_inv_cancel₀ (pow_ne_zero _ hL')]
theorem torusSide_eq_intCast (L n : ℕ) :
    PeriodicLattice.torusSide L n = ((2 * (L : ℤ) ^ n : ℤ) : ℝ) := by
  simp [PeriodicLattice.torusSide]
theorem torusSide_pos {L : ℕ} (hL : 0 < L) (n : ℕ) : 0 < PeriodicLattice.torusSide L n := by apply _root_.YangMills.SharedProofs.p34445 <;> assumption
theorem unitLattice_le_meshLattice {L k j : ℕ} (hL : 0 < L) (h : j ≤ k) :
    InfiniteLattice.latticeSubgroup 1 ≤ InfiniteLattice.latticeSubgroup (meshAt L k j) :=
  latticeSubgroup_le_of_eq_zmul _ (one_eq_intCast_mul_meshAt hL h)
theorem periodLattice_le_unitLattice (L n : ℕ) :
    periodLattice L n ≤ InfiniteLattice.latticeSubgroup 1 :=
  latticeSubgroup_le_of_eq_zmul (2 * (L : ℤ) ^ n) (by rw [mul_one]; exact torusSide_eq_intCast L n)
theorem castVec_mem_unitLattice (N : Fin 4 → ℤ) : castVec N ∈ InfiniteLattice.latticeSubgroup 1 :=
  ⟨N, fun μ => by simp [castVec]⟩
theorem castVec_mem_meshLattice {L k j : ℕ} (hL : 0 < L) (h : j ≤ k) (N : Fin 4 → ℤ) :
    castVec N ∈ InfiniteLattice.latticeSubgroup (meshAt L k j) :=
  unitLattice_le_meshLattice hL h (castVec_mem_unitLattice N)
theorem castVec_neg (N : Fin 4 → ℤ) : castVec (-N) = -castVec N := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.castVec_neg <;> assumption
theorem torusProj_add (S : ℝ) (x y : AmbientSpace) :
    TorusMetric.torusProj S (x + y) = TorusMetric.torusProj S x + TorusMetric.torusProj S y := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_add' <;> assumption
theorem torusProj_sub (S : ℝ) (x y : AmbientSpace) :
    TorusMetric.torusProj S (x - y) = TorusMetric.torusProj S x - TorusMetric.torusProj S y := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_sub' <;> assumption
theorem torusProj_neg (S : ℝ) (x : AmbientSpace) :
    TorusMetric.torusProj S (-x) = -TorusMetric.torusProj S x := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_neg' <;> assumption
theorem torusProj_axisStep (L n k j : ℕ) (μ : Fin 4) :
    TorusMetric.torusProj (PeriodicLattice.torusSide L n)
        ((InfiniteLattice.axisStep (meshAt L k j) μ : FullSpace.Vertex L k j) : AmbientSpace) =
      (PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ :
        PeriodicLattice.FourTorus L n) := by
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp [TorusMetric.torusProj, InfiniteLattice.axisStep, PeriodicLattice.unitStep,
      PeriodicLattice.pointOnAxis, meshSize_levelDepth]
  · simp [TorusMetric.torusProj, InfiniteLattice.axisStep, PeriodicLattice.unitStep,
      PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hν]
theorem torusQuotient_image_latticeSubgroup (L n k j : ℕ) :
    torusQuotient L n '' (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) =
      (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) :
        Set (PeriodicLattice.FourTorus L n)) := by
  ext y
  constructor
  · rintro ⟨x, ⟨N, hN⟩, rfl⟩
    refine ⟨N, fun μ => ?_⟩
    rw [meshSize_levelDepth, ← hN μ]
    rfl
  · rintro ⟨N, hN⟩
    refine ⟨fun μ => (N μ : ℝ) * meshAt L k j, ⟨N, fun μ => rfl⟩, ?_⟩
    funext μ
    rw [hN μ, meshSize_levelDepth]
    rfl
def vertexOnTorus (L n k j : ℕ) (x : FullSpace.Vertex L k j) : Vertex L n k j :=
  ⟨torusQuotient L n x, by
    have h := torusQuotient_image_latticeSubgroup L n k j
    have h' : torusQuotient L n x ∈
        torusQuotient L n '' (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) :=
      ⟨x, x.2, rfl⟩
    rw [h] at h'
    exact h'⟩
theorem vertexOnTorus_sub_of_eq_axisStep {L n k j : ℕ} {x y : FullSpace.Vertex L k j} {μ : Fin 4}
    (h : y - x = InfiniteLattice.axisStep (meshAt L k j) μ) :
    vertexOnTorus L n k j y - vertexOnTorus L n k j x =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ := by
  apply Subtype.ext
  rw [← torusProj_axisStep L n k j μ, ← h]
  exact (torusProj_sub _ _ _).symm
theorem vertexOnTorus_sub_of_eq_neg_axisStep {L n k j : ℕ} {x y : FullSpace.Vertex L k j}
    {μ : Fin 4} (h : y - x = -InfiniteLattice.axisStep (meshAt L k j) μ) :
    vertexOnTorus L n k j y - vertexOnTorus L n k j x =
      -PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ := by
  apply Subtype.ext
  have e := congrArg (fun z : FullSpace.Vertex L k j => (z : AmbientSpace)) h
  simp only [AddSubgroup.coe_sub, AddSubgroup.coe_neg] at e
  simp only [AddSubgroup.coe_sub, AddSubgroup.coe_neg]
  rw [← torusProj_axisStep L n k j μ, ← torusProj_neg, ← e]
  exact (torusProj_sub _ _ _).symm
theorem torusQuotientMapsVerticesAndEdges_holds (L n k j : ℕ) :
    TorusQuotientMapsVerticesAndEdges L n k j := by
  refine ⟨torusQuotient_image_latticeSubgroup L n k j, fun b => ?_⟩
  refine ⟨⟨vertexOnTorus L n k j b.initial, vertexOnTorus L n k j b.terminal, ?_⟩, rfl, rfl, ?_⟩
  · obtain ⟨μ, h | h⟩ := b.isAdjacent
    · exact ⟨μ, Or.inl (vertexOnTorus_sub_of_eq_axisStep h)⟩
    · exact ⟨μ, Or.inr (vertexOnTorus_sub_of_eq_neg_axisStep h)⟩
  · rintro ⟨μ, h⟩
    exact ⟨μ, vertexOnTorus_sub_of_eq_axisStep h⟩
theorem torusQuotientPeriodic_holds (L n : ℕ) : TorusQuotientPeriodic L n := by
  rintro x v ⟨N, hN⟩
  rw [torusQuotient, torusProj_add]
  have : TorusMetric.torusProj (PeriodicLattice.torusSide L n) v = 0 := by
    funext μ
    refine (AddCircle.coe_eq_zero_iff _).2 ⟨N μ, ?_⟩
    rw [hN μ, zsmul_eq_mul]
  rw [this, add_zero]
section Shifts
variable {L k j : ℕ}
theorem coe_vertexImage_intShift (hL : 0 < L) (h : j ≤ k) (N : Fin 4 → ℤ)
    (x : FullSpace.Vertex L k j) :
    ((FullSpace.vertexImage (intShift N) x : FullSpace.Vertex L k j) : AmbientSpace) =
      x + castVec N := by
  have hex : ∃ x' : FullSpace.Vertex L k j, (x' : AmbientSpace) = intShift N x :=
    ⟨⟨x + castVec N, add_mem x.2 (castVec_mem_meshLattice hL h N)⟩, rfl⟩
  exact Classical.epsilon_spec hex
theorem vertexImage_intShift_sub (hL : 0 < L) (h : j ≤ k) (N : Fin 4 → ℤ)
    (x y : FullSpace.Vertex L k j) :
    (FullSpace.vertexImage (intShift N) y : FullSpace.Vertex L k j) -
        FullSpace.vertexImage (intShift N) x = y - x := by
  apply Subtype.ext
  rw [AddSubgroup.coe_sub, coe_vertexImage_intShift hL h, coe_vertexImage_intShift hL h,
    AddSubgroup.coe_sub]
  abel
theorem vertexImage_intShift_neg_cancel (hL : 0 < L) (h : j ≤ k) (N : Fin 4 → ℤ)
    (x : FullSpace.Vertex L k j) :
    (FullSpace.vertexImage (intShift N) (FullSpace.vertexImage (intShift (-N)) x) :
      FullSpace.Vertex L k j) = x := by
  apply Subtype.ext
  rw [coe_vertexImage_intShift hL h, coe_vertexImage_intShift hL h, castVec_neg]
  abel
theorem edgeImage_intShift_endpoints (hL : 0 < L) (h : j ≤ k) (N : Fin 4 → ℤ)
    (b : FullSpace.Edge L k j) :
    (FullSpace.edgeImage (intShift N) b).initial = FullSpace.vertexImage (intShift N) b.initial ∧
      (FullSpace.edgeImage (intShift N) b).terminal =
        FullSpace.vertexImage (intShift N) b.terminal := by
  have hex : ∃ b' : FullSpace.Edge L k j,
      b'.initial = FullSpace.vertexImage (intShift N) b.initial ∧
      b'.terminal = FullSpace.vertexImage (intShift N) b.terminal :=
    ⟨⟨FullSpace.vertexImage (intShift N) b.initial,
      FullSpace.vertexImage (intShift N) b.terminal, by
      rw [vertexImage_intShift_sub hL h]
      exact b.isAdjacent⟩, rfl, rfl⟩
  exact Classical.epsilon_spec hex
theorem shiftEdge_val (hL : 0 < L) (h : j ≤ k) (N : Fin 4 → ℤ) (b : PosEdge L k j) :
    (shiftEdge N b).1 = FullSpace.edgeImage (intShift N) b.1 := by
  have hex : ∃ b' : PosEdge L k j, b'.1 = FullSpace.edgeImage (intShift N) b.1 := by
    refine ⟨⟨FullSpace.edgeImage (intShift N) b.1, ?_⟩, rfl⟩
    obtain ⟨μ, hμ⟩ := b.2
    refine ⟨μ, ?_⟩
    obtain ⟨e₁, e₂⟩ := edgeImage_intShift_endpoints hL h N b.1
    rw [e₁, e₂, vertexImage_intShift_sub hL h]
    exact hμ
  exact Classical.epsilon_spec hex
theorem shiftEdge_initial (hL : 0 < L) (h : j ≤ k) (N : Fin 4 → ℤ) (b : PosEdge L k j) :
    (shiftEdge N b).1.initial = FullSpace.vertexImage (intShift N) b.1.initial := by
  rw [shiftEdge_val hL h]
  exact (edgeImage_intShift_endpoints hL h N b.1).1
theorem shiftEdge_terminal (hL : 0 < L) (h : j ≤ k) (N : Fin 4 → ℤ) (b : PosEdge L k j) :
    (shiftEdge N b).1.terminal = FullSpace.vertexImage (intShift N) b.1.terminal := by
  rw [shiftEdge_val hL h]
  exact (edgeImage_intShift_endpoints hL h N b.1).2
theorem shiftEdge_neg_cancel (hL : 0 < L) (h : j ≤ k) (N : Fin 4 → ℤ)
    (b : PosEdge L k j) : shiftEdge N (shiftEdge (-N) b) = b := by
  apply Subtype.ext
  apply InfiniteLattice.Link.ext
  · rw [shiftEdge_initial hL h, shiftEdge_initial hL h, vertexImage_intShift_neg_cancel hL h]
  · rw [shiftEdge_terminal hL h, shiftEdge_terminal hL h, vertexImage_intShift_neg_cancel hL h]
theorem shiftFace_neg_cancel (hL : 0 < L) (h : j ≤ k) (N : Fin 4 → ℤ)
    (p : FullSpace.Face L k j) : shiftFace N (shiftFace (-N) p) = p := by
  apply InfiniteLattice.ElementaryPlaquette.ext
  · exact vertexImage_intShift_neg_cancel hL h N p.corner
  · rfl
  · rfl
theorem shiftSurjectiveOnVertices_holds (hL : 0 < L) (h : j ≤ k) (N : Fin 4 → ℤ) :
    ShiftSurjectiveOnVertices L k j N := by
  refine ⟨?_, coe_vertexImage_intShift hL h N⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact add_mem hx (castVec_mem_meshLattice hL h N)
  · intro hy
    refine ⟨y - castVec N, sub_mem hy (castVec_mem_meshLattice hL h N), ?_⟩
    change y - castVec N + castVec N = y
    abel
theorem shiftSurjectiveOnEdges_holds (hL : 0 < L) (h : j ≤ k) (N : Fin 4 → ℤ) :
    ShiftSurjectiveOnEdges L k j N := by
  refine ⟨fun c => ⟨shiftEdge (-N) c, shiftEdge_neg_cancel hL h N c⟩, fun b => ?_⟩
  rw [shiftEdge_initial hL h, shiftEdge_terminal hL h, coe_vertexImage_intShift hL h,
    coe_vertexImage_intShift hL h]
  exact ⟨rfl, rfl⟩
theorem shiftSurjectiveOnFaces_holds (hL : 0 < L) (h : j ≤ k) (N : Fin 4 → ℤ) :
    ShiftSurjectiveOnFaces L k j N := by
  refine ⟨fun c => ⟨shiftFace (-N) c, shiftFace_neg_cancel hL h N c⟩,
    fun p => ⟨coe_vertexImage_intShift hL h N p.corner, rfl, rfl, ?_⟩⟩
  have hb : (shiftFace N p).corner = FullSpace.vertexImage (intShift N) p.corner := rfl
  have hf : (shiftFace N p).lowAxis = p.lowAxis := rfl
  have hs : (shiftFace N p).highAxis = p.highAxis := rfl
  simp only [FullSpace.faceCorners, hb, hf, hs, Set.image_insert_eq, Set.image_singleton]
  simp only [AddSubgroup.coe_add, coe_vertexImage_intShift hL h, intShift]
  have e₁ : ∀ u : AmbientSpace,
      (p.corner : AmbientSpace) + u + castVec N = (p.corner : AmbientSpace) + castVec N + u :=
    fun u => by abel
  have e₂ : ∀ u v : AmbientSpace, (p.corner : AmbientSpace) + u + v + castVec N =
      (p.corner : AmbientSpace) + castVec N + u + v := fun u v => by abel
  simp only [e₁, e₂]
end Shifts
theorem finite_latticePoints_of_isBounded {a : ℝ} (ha : 0 < a) {B : Set AmbientSpace}
    (hB : Bornology.IsBounded B) :
    {x : InfiniteLattice.LatticePoint a | (x : AmbientSpace) ∈ B}.Finite := by apply _root_.YangMills.Construction.InfiniteLattice.MeasurableIffDependsOnlyProof.finite_latticePoints_of_isBounded <;> assumption
theorem locallyFiniteCells_holds {L : ℕ} (hL : 0 < L) (k j : ℕ) :
    LocallyFiniteCells L k j := by
  intro B hB
  have hT := finite_latticePoints_of_isBounded (meshAt_pos hL k j) hB
  refine ⟨hT, ?_, ?_⟩
  · refine ((hT.prod (finite_univ (α := Fin 4))).image
      fun q : FullSpace.Vertex L k j × Fin 4 =>
        (⟨InfiniteLattice.Link.forwardFrom q.1 q.2, q.2, add_sub_cancel_left _ _⟩ :
          PosEdge L k j)).subset ?_
    rintro ⟨b, μ, hμ⟩ hb
    refine ⟨(b.initial, μ), ⟨hb, mem_univ _⟩, ?_⟩
    apply Subtype.ext
    apply InfiniteLattice.Link.ext
    · rfl
    · change b.initial + _ = b.terminal
      rw [← hμ]
      abel
  · refine Set.Finite.of_finite_image (f := fun p : FullSpace.Face L k j =>
      (p.corner, p.lowAxis, p.highAxis)) ?_ ?_
    · refine (hT.prod (finite_univ (α := Fin 4 × Fin 4))).subset ?_
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨hp, mem_univ _⟩
    · intro p _ q _ e
      have e' : (p.corner, p.lowAxis, p.highAxis) = (q.corner, q.lowAxis, q.highAxis) := e
      simp only [Prod.mk.injEq] at e'
      exact InfiniteLattice.ElementaryPlaquette.ext e'.1 e'.2.1 e'.2.2
theorem locallyFiniteEdgesAtVertex_holds (L k j : ℕ) : LocallyFiniteEdgesAtVertex L k j := by
  intro x
  let nbr : Set (FullSpace.Vertex L k j) := range fun q : Fin 4 × Bool =>
    if q.2 then x + InfiniteLattice.axisStep (meshAt L k j) q.1
    else x - InfiniteLattice.axisStep (meshAt L k j) q.1
  have hnbr : nbr.Finite := Set.finite_range _
  refine Set.Finite.of_finite_image
    (f := fun b : FullSpace.Edge L k j => (b.initial, b.terminal)) ?_ ?_
  · refine (((Set.finite_singleton x).prod hnbr).union (hnbr.prod (Set.finite_singleton x))).subset
      ?_
    rintro _ ⟨b, hb | hb, rfl⟩
    · refine Or.inl ⟨hb, ?_⟩
      obtain ⟨μ, h | h⟩ := b.isAdjacent
      · exact ⟨(μ, true), by simp only [if_true]; rw [← hb, ← h]; abel⟩
      · exact ⟨(μ, false), by
          simp only [Bool.false_eq_true, if_false]
          rw [← hb, sub_eq_add_neg, ← h]
          abel⟩
    · refine Or.inr ⟨?_, hb⟩
      obtain ⟨μ, h | h⟩ := b.isAdjacent
      · exact ⟨(μ, false), by
          simp only [Bool.false_eq_true, if_false]
          rw [← hb, ← h]
          abel⟩
      · exact ⟨(μ, true), by
          simp only [if_true]
          rw [← hb, ← neg_eq_iff_eq_neg.mpr h]
          abel⟩
  · intro b _ c _ e
    have e' : (b.initial, b.terminal) = (c.initial, c.terminal) := e
    simp only [Prod.mk.injEq] at e'
    exact InfiniteLattice.Link.ext e'.1 e'.2
theorem exists_period_sub_mem_fundamentalCube {L : ℕ} (hL : 0 < L) (n : ℕ) (z : AmbientSpace) :
    ∃ N : Fin 4 → ℤ, castVec N ∈ periodLattice L n ∧ z - castVec N ∈ fundamentalCube L n := by
  have hS := torusSide_pos hL n
  refine ⟨fun μ => 2 * (L : ℤ) ^ n * ⌊z μ / PeriodicLattice.torusSide L n⌋,
    ⟨fun μ => ⌊z μ / PeriodicLattice.torusSide L n⌋, fun μ => ?_⟩, fun μ => ?_⟩
  · simp only [castVec]
    rw [Int.cast_mul, ← torusSide_eq_intCast]
    ring
  · have e : (z - castVec fun μ => 2 * (L : ℤ) ^ n * ⌊z μ / PeriodicLattice.torusSide L n⌋) μ =
        z μ - PeriodicLattice.torusSide L n * (⌊z μ / PeriodicLattice.torusSide L n⌋ : ℝ) := by
      simp only [Pi.sub_apply, castVec]
      rw [Int.cast_mul, ← torusSide_eq_intCast]
    rw [e]
    have h₁ := Int.floor_le (z μ / PeriodicLattice.torusSide L n)
    have h₂ := Int.lt_floor_add_one (z μ / PeriodicLattice.torusSide L n)
    rw [le_div_iff₀ hS] at h₁
    rw [div_lt_iff₀ hS] at h₂
    constructor <;> nlinarith
theorem shiftedFromFundamentalCube_holds {L k j : ℕ} (hL : 0 < L) (h : j ≤ k) (n : ℕ) :
    ShiftedFromFundamentalCube L n k j := by
  refine ⟨fun x => ?_, fun b => ?_, fun p => ?_⟩
  · obtain ⟨N, hN, hc⟩ := exists_period_sub_mem_fundamentalCube hL n (x : AmbientSpace)
    refine ⟨FullSpace.vertexImage (intShift (-N)) x, N, ?_, hN,
      vertexImage_intShift_neg_cancel hL h N x⟩
    rw [coe_vertexImage_intShift hL h, castVec_neg, ← sub_eq_add_neg]
    exact hc
  · obtain ⟨N, hN, hc⟩ := exists_period_sub_mem_fundamentalCube hL n (b.1.initial : AmbientSpace)
    refine ⟨shiftEdge (-N) b, N, ?_, hN, shiftEdge_neg_cancel hL h N b⟩
    rw [shiftEdge_initial hL h, coe_vertexImage_intShift hL h, castVec_neg, ← sub_eq_add_neg]
    exact hc
  · obtain ⟨N, hN, hc⟩ := exists_period_sub_mem_fundamentalCube hL n (p.corner : AmbientSpace)
    refine ⟨shiftFace (-N) p, N, ?_, hN, shiftFace_neg_cancel hL h N p⟩
    change ((FullSpace.vertexImage (intShift (-N)) p.corner : FullSpace.Vertex L k j) :
      AmbientSpace) ∈ _
    rw [coe_vertexImage_intShift hL h, castVec_neg, ← sub_eq_add_neg]
    exact hc
theorem fullLatticeOverTorusClaim_holds : FullLatticeOverTorusClaim := by
  intro L hst k j h n _
  have hL : 0 < L := by
    have := hst.2
    omega
  exact ⟨⟨unitLattice_le_meshLattice hL h,
      (periodLattice_le_unitLattice L n).trans (unitLattice_le_meshLattice hL h)⟩,
    torusQuotientMapsVerticesAndEdges_holds L n k j,
    fun N => ⟨shiftSurjectiveOnVertices_holds hL h N, shiftSurjectiveOnEdges_holds hL h N,
      shiftSurjectiveOnFaces_holds hL h N⟩,
    locallyFiniteCells_holds hL k j, locallyFiniteEdgesAtVertex_holds L k j,
    shiftedFromFundamentalCube_holds hL h n,
    torusQuotientPeriodic_holds L n⟩
end YangMills.Construction.FullLatticeOverTorus
end
