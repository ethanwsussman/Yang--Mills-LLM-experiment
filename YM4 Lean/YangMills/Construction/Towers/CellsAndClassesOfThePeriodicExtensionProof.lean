import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import YangMills.Construction.Towers.LatticesOfSideInfinityOverAFiniteSide
import YangMills.Construction.Towers.QuotientOfATowerCarriesConfigurationsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.PeriodicLiftCells
open Periodisation Tower
open FullLatticeOverTorus
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (castVec intShift shiftEdge shiftFace)
variable {L n k j : ℕ}
theorem castVec_periodSide_smul (m : Fin 4 → ℤ) (μ : Fin 4) :
    castVec (periodSide L n • m) μ = (m μ : ℝ) * PeriodicLattice.torusSide L n := by
  simp [castVec, periodSide, PeriodicLattice.torusSide]
  ring
theorem torusProj_eq_iff (S : ℝ) (x y : AmbientSpace) :
    TorusMetric.torusProj S x = TorusMetric.torusProj S y ↔
      ∃ m : Fin 4 → ℤ, ∀ μ, y μ = x μ + (m μ : ℝ) * S := by
  constructor
  · intro h
    have key : ∀ μ, ∃ z : ℤ, y μ = x μ + (z : ℝ) * S := by
      intro μ
      have e : ((x μ : ℝ) : AddCircle S) = ((y μ : ℝ) : AddCircle S) := congrFun h μ
      have e' : ((y μ - x μ : ℝ) : AddCircle S) = 0 := by
        rw [AddCircle.coe_sub, e, sub_self]
      obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff S).1 e'
      refine ⟨z, ?_⟩
      rw [zsmul_eq_mul] at hz
      rw [hz]
      ring
    choose m hm using key
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩
    funext μ
    have e : ((y μ - x μ : ℝ) : AddCircle S) = 0 :=
      (AddCircle.coe_eq_zero_iff S).2 ⟨m μ, by rw [zsmul_eq_mul, hm μ]; ring⟩
    rw [AddCircle.coe_sub, sub_eq_zero] at e
    exact e.symm
theorem projVertex_eq_iff (x y : FullSpace.Vertex L k j) :
    FullSpace.projVertex L n k j x = FullSpace.projVertex L n k j y ↔
      ∃ m : Fin 4 → ℤ, (y : AmbientSpace) = x + castVec (periodSide L n • m) := by
  constructor
  · intro h
    have h' : TorusMetric.torusProj (PeriodicLattice.torusSide L n) (x : AmbientSpace) =
        TorusMetric.torusProj (PeriodicLattice.torusSide L n) (y : AmbientSpace) :=
      congrArg Subtype.val h
    obtain ⟨m, hm⟩ := (torusProj_eq_iff _ _ _).1 h'
    refine ⟨m, ?_⟩
    funext μ
    rw [Pi.add_apply, castVec_periodSide_smul, hm μ]
  · rintro ⟨m, hm⟩
    apply Subtype.ext
    refine (torusProj_eq_iff _ _ _).2 ⟨m, fun μ => ?_⟩
    rw [hm, Pi.add_apply, castVec_periodSide_smul]
theorem projVertex_add_axisStep (x : FullSpace.Vertex L k j) (μ : Fin 4) :
    FullSpace.projVertex L n k j (x + InfiniteLattice.axisStep (meshAt L k j) μ) =
      FullSpace.projVertex L n k j x +
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ := by apply _root_.YangMills.Construction.Tower.FieldProjection.projVertex_add_axisStep <;> assumption
theorem projVertex_surjective (hC : TorusQuotientMapsVerticesAndEdges L n k j)
    (c : Tower.Vertex L n k j) : ∃ x, FullSpace.projVertex L n k j x = c := by
  have hc : (c : PeriodicLattice.FourTorus L n) ∈
      torusQuotient L n ''
        (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) := by
    rw [hC.1]
    exact c.2
  obtain ⟨x, hx, e⟩ := hc
  exact ⟨⟨x, hx⟩, Subtype.ext e⟩
theorem meshAt_pos_and_lt_torusSide (hL : 0 < L) (h : j ≤ k) :
    0 < meshAt L k j ∧ meshAt L k j < PeriodicLattice.torusSide L n := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h₁ : 0 < meshAt L k j := zpow_pos (by linarith) _
  have h₂ : meshAt L k j ≤ 1 :=
    zpow_le_one_of_nonpos₀ hL' (by omega)
  have h₃ : (1 : ℝ) ≤ (L : ℝ) ^ n := one_le_pow₀ hL'
  refine ⟨h₁, ?_⟩
  rw [PeriodicLattice.torusSide]
  linarith
theorem unitStep_injective (hL : 0 < L) (h : j ≤ k) {μ ν : Fin 4}
    (e : PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) ν) : μ = ν := by
  by_contra hne
  have e₁ := congrFun (congrArg Subtype.val e) μ
  have e₂ : ((meshAt L k j : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) = 0 := by
    simpa [PeriodicLattice.unitStep, PeriodicLattice.pointOnAxis, meshSize_levelDepth,
      Pi.single_eq_of_ne hne] using e₁
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff _).1 e₂
  obtain ⟨h₁, h₂⟩ := meshAt_pos_and_lt_torusSide (n := n) hL h
  rw [zsmul_eq_mul] at hz
  have hS : 0 < PeriodicLattice.torusSide L n := h₁.trans h₂
  have hz₁ : (0 : ℝ) < z := by
    by_contra hc
    have : (z : ℝ) * PeriodicLattice.torusSide L n ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) hS.le
    linarith
  have hz₂ : (z : ℝ) < 1 := by
    by_contra hc
    have : PeriodicLattice.torusSide L n ≤ (z : ℝ) * PeriodicLattice.torusSide L n :=
      le_mul_of_one_le_left hS.le (not_lt.1 hc)
    linarith
  have a₁ : (0 : ℤ) < z := by exact_mod_cast hz₁
  have a₂ : z < (1 : ℤ) := by exact_mod_cast hz₂
  omega
section Edges
variable (hq : ∀ b : FullSpace.Edge L k j,
  (FullSpace.projEdge L n k j b).source = FullSpace.projVertex L n k j b.initial ∧
  (FullSpace.projEdge L n k j b).target = FullSpace.projVertex L n k j b.terminal ∧
  (b.IsPositivelyOriented → (FullSpace.projEdge L n k j b).IsPositivelyOriented))
include hq
theorem projPositiveEdge_val (b : PeriodicOperators.PosEdge L k j) :
    (projPositiveEdge L n k j b).1 = FullSpace.projEdge L n k j b.1 :=
  Classical.epsilon_spec (p := fun c : Tower.PositiveEdge L n k j =>
    c.1 = FullSpace.projEdge L n k j b.1) ⟨⟨_, (hq b.1).2.2 b.2⟩, rfl⟩
theorem projPositiveEdge_source (b : PeriodicOperators.PosEdge L k j) :
    (projPositiveEdge L n k j b).1.source = FullSpace.projVertex L n k j b.1.initial := by
  rw [projPositiveEdge_val hq, (hq b.1).1]
theorem projPositiveEdge_target (b : PeriodicOperators.PosEdge L k j) :
    (projPositiveEdge L n k j b).1.target = FullSpace.projVertex L n k j b.1.terminal := by
  rw [projPositiveEdge_val hq, (hq b.1).2.1]
theorem projEdge_forwardFrom (x : FullSpace.Vertex L k j) (μ : Fin 4) :
    FullSpace.projEdge L n k j (InfiniteLattice.Link.forwardFrom x μ) =
      PeriodicLattice.Bond.forwardFrom (FullSpace.projVertex L n k j x) μ := by
  apply PeriodicLattice.Bond.ext
  · exact (hq _).1
  · rw [(hq _).2.1]
    exact projVertex_add_axisStep x μ
theorem projPositiveEdge_eq_iff (hL : 0 < L) (h : j ≤ k)
    (hB : ∀ N, ShiftSurjectiveOnEdges L k j N)
    (x y : PeriodicOperators.PosEdge L k j) :
    projPositiveEdge L n k j x = projPositiveEdge L n k j y ↔
      ∃ m : Fin 4 → ℤ, y = shiftEdge (periodSide L n • m) x := by
  constructor
  · intro e
    have et : FullSpace.projVertex L n k j x.1.initial =
        FullSpace.projVertex L n k j y.1.initial := by
      rw [← projPositiveEdge_source hq, ← projPositiveEdge_source hq, e]
    have eh : FullSpace.projVertex L n k j x.1.terminal =
        FullSpace.projVertex L n k j y.1.terminal := by
      rw [← projPositiveEdge_target hq, ← projPositiveEdge_target hq, e]
    obtain ⟨m, hm⟩ := (projVertex_eq_iff x.1.initial y.1.initial).1 et
    obtain ⟨μ, hμ⟩ := x.2
    obtain ⟨ν, hν⟩ := y.2
    have hx : x.1.terminal = x.1.initial + InfiniteLattice.axisStep (meshAt L k j) μ := by
      rw [← hμ]
      abel
    have hy : y.1.terminal = y.1.initial + InfiniteLattice.axisStep (meshAt L k j) ν := by
      rw [← hν]
      abel
    have est : PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ =
        PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) ν := by
      rw [hx, hy, projVertex_add_axisStep, projVertex_add_axisStep, et] at eh
      exact add_left_cancel eh
    obtain rfl := unitStep_injective hL h est
    refine ⟨m, Subtype.ext (InfiniteLattice.Link.ext (Subtype.ext ?_) (Subtype.ext ?_))⟩
    · rw [((hB _).2 x).1, hm]
    · rw [((hB _).2 x).2, hx, hy]
      simp only [AddSubgroup.coe_add]
      rw [hm]
      abel
  · rintro ⟨m, rfl⟩
    apply Subtype.ext
    apply PeriodicLattice.Bond.ext
    · rw [projPositiveEdge_source hq, projPositiveEdge_source hq]
      exact (projVertex_eq_iff _ _).2 ⟨m, ((hB _).2 x).1⟩
    · rw [projPositiveEdge_target hq, projPositiveEdge_target hq]
      exact (projVertex_eq_iff _ _).2 ⟨m, ((hB _).2 x).2⟩
theorem projPositiveEdge_surjective (hC : TorusQuotientMapsVerticesAndEdges L n k j) :
    Function.Surjective (projPositiveEdge L n k j) := by
  rintro ⟨c, μ, hμ⟩
  obtain ⟨x, hx⟩ := projVertex_surjective hC c.source
  have hpos : (InfiniteLattice.Link.forwardFrom x μ : FullSpace.Edge L k j).IsPositivelyOriented :=
    ⟨μ, add_sub_cancel_left _ _⟩
  refine ⟨⟨InfiniteLattice.Link.forwardFrom x μ, hpos⟩, Subtype.ext ?_⟩
  rw [projPositiveEdge_val hq, projEdge_forwardFrom hq, hx]
  apply PeriodicLattice.Bond.ext
  · rfl
  · change c.source + _ = c.target
    rw [← hμ]
    abel
end Edges
theorem projFace_eq_iff (hP : ∀ N, ShiftSurjectiveOnFaces L k j N)
    (p q : FullSpace.Face L k j) :
    FullSpace.projFace L n k j p = FullSpace.projFace L n k j q ↔
      ∃ m : Fin 4 → ℤ, q = shiftFace (periodSide L n • m) p := by
  constructor
  · intro e
    have e₁ : FullSpace.projVertex L n k j p.corner = FullSpace.projVertex L n k j q.corner :=
      congrArg PeriodicLattice.Plaquette.origin e
    have e₂ : p.lowAxis = q.lowAxis := congrArg PeriodicLattice.Plaquette.firstAxis e
    have e₃ : p.highAxis = q.highAxis := congrArg PeriodicLattice.Plaquette.secondAxis e
    obtain ⟨m, hm⟩ := (projVertex_eq_iff _ _).1 e₁
    refine ⟨m, InfiniteLattice.ElementaryPlaquette.ext (Subtype.ext ?_) e₂.symm e₃.symm⟩
    rw [((hP _).2 p).1, hm]
  · rintro ⟨m, rfl⟩
    apply PeriodicLattice.Plaquette.ext
    · exact (projVertex_eq_iff _ _).2 ⟨m, ((hP _).2 p).1⟩
    · rfl
    · rfl
theorem projFace_surjective (hC : TorusQuotientMapsVerticesAndEdges L n k j) :
    Function.Surjective (FullSpace.projFace L n k j) := by
  intro c
  obtain ⟨x, hx⟩ := projVertex_surjective hC c.origin
  refine ⟨⟨x, c.firstAxis, c.secondAxis, c.firstAxis_lt_secondAxis⟩, ?_⟩
  apply PeriodicLattice.Plaquette.ext
  · exact hx
  · rfl
  · rfl
theorem projVertex_eq_iff_vertexImage (hS : ∀ N, ShiftSurjectiveOnVertices L k j N)
    (x y : FullSpace.Vertex L k j) :
    FullSpace.projVertex L n k j x = FullSpace.projVertex L n k j y ↔
      ∃ m : Fin 4 → ℤ, y = FullSpace.vertexImage (intShift (periodSide L n • m)) x := by
  rw [projVertex_eq_iff]
  refine exists_congr fun m => ⟨fun e => Subtype.ext ?_, fun e => ?_⟩
  · rw [(hS _).2 x]
    exact e
  · rw [e, (hS _).2 x]
theorem projCellsClassified_of (hL : 0 < L) (h : j ≤ k)
    (hq : ∀ b : FullSpace.Edge L k j,
      (FullSpace.projEdge L n k j b).source = FullSpace.projVertex L n k j b.initial ∧
      (FullSpace.projEdge L n k j b).target = FullSpace.projVertex L n k j b.terminal ∧
      (b.IsPositivelyOriented → (FullSpace.projEdge L n k j b).IsPositivelyOriented))
    (hC : TorusQuotientMapsVerticesAndEdges L n k j)
    (hT : ∀ N, ShiftSurjectiveOnVertices L k j N ∧ ShiftSurjectiveOnEdges L k j N ∧
      ShiftSurjectiveOnFaces L k j N) :
    ProjCellsClassified L n k j := by
  intro c
  cases c
  · exact ⟨projVertex_surjective hC, projVertex_eq_iff_vertexImage fun N => (hT N).1⟩
  · exact ⟨projPositiveEdge_surjective hq hC,
      projPositiveEdge_eq_iff hq hL h fun N => (hT N).2.1⟩
  · exact ⟨projFace_surjective hC, projFace_eq_iff fun N => (hT N).2.2⟩
theorem projEdgesCompatible_of
    (hq : ∀ b : FullSpace.Edge L k j,
      (FullSpace.projEdge L n k j b).source = FullSpace.projVertex L n k j b.initial ∧
      (FullSpace.projEdge L n k j b).target = FullSpace.projVertex L n k j b.terminal ∧
      (b.IsPositivelyOriented → (FullSpace.projEdge L n k j b).IsPositivelyOriented)) :
    ProjEdgesCompatible L n k j := by
  refine ⟨fun b => ⟨(hq b).1, (hq b).2.1⟩, projPositiveEdge_val hq, fun p => ?_⟩
  simp only [Tower.faceEdges, FullSpace.faceEdges, List.map_cons, List.map_nil,
    projEdge_forwardFrom hq, projVertex_add_axisStep]
  rfl
theorem fundamentalCube_isBounded : Bornology.IsBounded (fundamentalCube L n) := by
  refine (Metric.isBounded_closedBall (x := (0 : AmbientSpace))
    (r := |PeriodicLattice.torusSide L n|)).subset fun y hy => ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg _)]
  intro μ
  rw [Real.norm_eq_abs, abs_of_nonneg (hy μ).1]
  exact (hy μ).2.le.trans (le_abs_self _)
theorem exists_smul_of_mem_periodLattice {N : Fin 4 → ℤ} (hN : castVec N ∈ periodLattice L n) :
    ∃ m : Fin 4 → ℤ, N = periodSide L n • m := by
  obtain ⟨m, hm⟩ := hN
  refine ⟨m, funext fun μ => ?_⟩
  have e : (N μ : ℝ) = (((periodSide L n • m) μ : ℤ) : ℝ) := by
    change castVec N μ = castVec (periodSide L n • m) μ
    rw [hm μ, castVec_periodSide_smul]
  exact_mod_cast e
theorem finite_quotientCell (hc : ProjCellsClassified L n k j)
    (hF : LocallyFiniteCells L k j) (hA : ShiftedFromFundamentalCube L n k j)
    (c : CellType) : Finite (QuotientCell L n k j c) := by
  have hB := fundamentalCube_isBounded (L := L) (n := n)
  have hfin : {x : Cell L k j c | Cell.anchor x ∈ fundamentalCube L n}.Finite := by
    cases c
    · exact (hF _ hB).1
    · exact (hF _ hB).2.1
    · exact (hF _ hB).2.2
  have harise : ∀ x : Cell L k j c, ∃ y : Cell L k j c,
      Cell.anchor y ∈ fundamentalCube L n ∧ Cell.proj n y = Cell.proj n x := by
    cases c
    · intro x
      obtain ⟨y, N, hy, hN, e⟩ := hA.1 x
      obtain ⟨m, rfl⟩ := exists_smul_of_mem_periodLattice hN
      exact ⟨y, hy, ((hc .vertex).2 y x).2 ⟨m, e.symm⟩⟩
    · intro x
      obtain ⟨y, N, hy, hN, e⟩ := hA.2.1 x
      obtain ⟨m, rfl⟩ := exists_smul_of_mem_periodLattice hN
      exact ⟨y, hy, ((hc .edge).2 y x).2 ⟨m, e.symm⟩⟩
    · intro x
      obtain ⟨y, N, hy, hN, e⟩ := hA.2.2 x
      obtain ⟨m, rfl⟩ := exists_smul_of_mem_periodLattice hN
      exact ⟨y, hy, ((hc .face).2 y x).2 ⟨m, e.symm⟩⟩
  have := hfin.to_subtype
  refine Finite.of_surjective
    (fun y : {x : Cell L k j c | Cell.anchor x ∈ fundamentalCube L n} => Cell.proj n y.1) ?_
  intro t
  obtain ⟨x, rfl⟩ := (hc c).1 t
  obtain ⟨y, hy, e⟩ := harise x
  exact ⟨⟨y, hy⟩, e⟩
theorem finite_withColour {A : Type} [Finite A] (c : Bool) : Finite (WithColour A c) := by
  cases c
  · exact (inferInstance : Finite A)
  · exact (inferInstance : Finite (Fin 3 × A))
theorem component_proj_eq_iff (hc : ∀ j ≤ k, ProjCellsClassified L n k j) (P : Component k)
    (ι ι' : P.Elem L) :
    P.proj L n ι = P.proj L n ι' ↔
      ∃ m : Fin 4 → ℤ, ι' = WithColour.map (Cell.translate (periodSide L n • m)) ι := by
  obtain ⟨lv, hlv, kd, col, w, hw⟩ := P
  have H := (hc lv hlv kd).2
  cases col
  · exact H ι ι'
  · obtain ⟨a, x⟩ := ι
    obtain ⟨b, y⟩ := ι'
    constructor
    · intro e
      have e₁ : a = b := congrArg Prod.fst e
      have e₂ : Cell.proj n x = Cell.proj n y := congrArg Prod.snd e
      obtain ⟨m, hm⟩ := (H x y).1 e₂
      exact ⟨m, Prod.ext e₁.symm hm⟩
    · rintro ⟨m, e⟩
      have e₁ : b = a := congrArg Prod.fst e
      have e₂ : y = Cell.translate (periodSide L n • m) x := congrArg Prod.snd e
      exact Prod.ext e₁.symm ((H x y).2 ⟨m, e₂⟩)
theorem proj_eq_iff (hc : ∀ j ≤ k, ProjCellsClassified L n k j) (I : WeightedIndexSet k)
    (ι ι' : Idx L I) :
    I.proj L n ι = I.proj L n ι' ↔
      ∃ m : Fin 4 → ℤ, ι' = (I.toPeriodicData L).translate (periodSide L n • m) ι := by
  obtain ⟨p, e⟩ := ι
  obtain ⟨p', e'⟩ := ι'
  constructor
  · intro h
    have h' : (⟨p, ⟨(I.comp p).proj L n e, mem_range_self _⟩⟩ :
        Σ p : I.Slot, ↥((I.comp p).image L n)) =
        ⟨p', ⟨(I.comp p').proj L n e', mem_range_self _⟩⟩ := h
    obtain ⟨rfl, h₂⟩ := Sigma.mk.inj h'
    have h₃ := congrArg Subtype.val (eq_of_heq h₂)
    obtain ⟨m, hm⟩ := (component_proj_eq_iff hc _ e e').1 h₃
    exact ⟨m, by rw [hm]; rfl⟩
  · rintro ⟨m, e₀⟩
    have e₁ : (⟨p', e'⟩ : Σ p : I.Slot, (I.comp p).Elem L) =
        ⟨p, WithColour.map (Cell.translate (periodSide L n • m)) e⟩ := e₀
    obtain ⟨rfl, h₂⟩ := Sigma.mk.inj e₁
    obtain rfl := eq_of_heq h₂
    have h₃ := (component_proj_eq_iff hc _ e _).2 ⟨m, rfl⟩
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext h₃))
theorem quotientClassesPeriodic_of (hc : ∀ j ≤ k, ProjCellsClassified L n k j)
    (hfin : ∀ j ≤ k, ∀ c : CellType, Finite (QuotientCell L n k j c)) (I : WeightedIndexSet k) :
    QuotientClassesPeriodic L n I := by
  have hsurj : Function.Surjective (I.proj L n) := by
    rintro ⟨p, _, e, rfl⟩
    exact ⟨⟨p, e⟩, rfl⟩
  have hiff := proj_eq_iff hc I
  refine ⟨?_, ⟨Quot.lift (I.proj L n) ?_, ⟨?_, ?_⟩, fun ι => rfl⟩, ?_, ?_, ?_⟩
  · have := I.finite_slot
    have hp : ∀ p, Finite ((I.comp p).QuotElem L n) := fun p => by
      have := hfin _ (I.comp p).level_le (I.comp p).cellType
      exact finite_withColour _
    have hi : ∀ p, Finite ↥((I.comp p).image L n) := fun p => by
      have := hp p
      exact Subtype.finite
    unfold WeightedIndexSet.ImageCarrier
    infer_instance
  · rintro ι _ ⟨m, rfl⟩
    exact (hiff ι _).2 ⟨m, rfl⟩
  · intro a b h
    obtain ⟨ι, rfl⟩ := Quot.exists_rep a
    obtain ⟨ι', rfl⟩ := Quot.exists_rep b
    obtain ⟨m, hm⟩ := (hiff ι ι').1 h
    exact Quot.sound ⟨m, hm⟩
  · intro κ
    obtain ⟨ι, rfl⟩ := hsurj κ
    exact ⟨Quot.mk _ ι, rfl⟩
  · intro f _ m ι
    show f (I.proj L n _) = f (I.proj L n ι)
    rw [(hiff ι _).2 ⟨m, rfl⟩]
  · intro f _ f' _ e
    funext κ
    obtain ⟨ι, rfl⟩ := hsurj κ
    exact congrFun e ι
  · intro g hg
    refine ⟨fun κ => g (Function.surjInv hsurj κ), mem_univ _, funext fun ι => ?_⟩
    obtain ⟨m, hm⟩ := (hiff _ _).1 (Function.surjInv_eq hsurj (I.proj L n ι))
    exact (hg m _).symm.trans (congrArg g hm.symm)
theorem cellsAndClassesHold_of (h₁ : FullLatticeOverTorus.FullLatticeOverTorusClaim)
    (h₂ : Tower.EdgeProjectionProperties) :
    LocalKernels.PeriodicLiftCells.CellsAndClassesHold := by
  intro L hL k n hn
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hq : ∀ j ≤ k, ∀ b : FullSpace.Edge L k j,
      (FullSpace.projEdge L n k j b).source = FullSpace.projVertex L n k j b.initial ∧
      (FullSpace.projEdge L n k j b).target = FullSpace.projVertex L n k j b.terminal ∧
      (b.IsPositivelyOriented → (FullSpace.projEdge L n k j b).IsPositivelyOriented) :=
    fun j hj b =>
      let e := (h₂ L n k j hL hn hj).1 b
      ⟨e.1, e.2.1, e.2.2.1⟩
  have hcells : ∀ j ≤ k, ProjCellsClassified L n k j := fun j hj =>
    let F := h₁ L hL k j hj n hn
    projCellsClassified_of hL0 hj (hq j hj) F.2.1 F.2.2.1
  have hfin : ∀ j ≤ k, ∀ c : CellType, Finite (QuotientCell L n k j c) := fun j hj c =>
    let F := h₁ L hL k j hj n hn
    finite_quotientCell (hcells j hj) F.2.2.2.1 F.2.2.2.2.2.1 c
  exact ⟨fun j hj => ⟨hcells j hj, projEdgesCompatible_of (hq j hj)⟩,
    quotientClassesPeriodic_of hcells hfin⟩
end YangMills.Construction.LocalKernels.PeriodicLiftCells
end
