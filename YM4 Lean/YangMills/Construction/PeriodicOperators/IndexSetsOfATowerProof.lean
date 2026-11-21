import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TowerIndexSets
open Tower
section SingleLattice
variable {a : ℝ} {N : ℕ}
theorem castVec_mem_latticeSubgroup (h : a * N = 1) (n : Fin 4 → ℤ) :
    castVec n ∈ InfiniteLattice.latticeSubgroup a :=
  ⟨fun μ => n μ * (N : ℤ), fun μ => by
    show (n μ : ℝ) = ((n μ * (N : ℤ) : ℤ) : ℝ) * a
    push_cast
    rw [mul_assoc, mul_comm (N : ℝ) a, h, mul_one]⟩
def intPoint (h : a * N = 1) (n : Fin 4 → ℤ) : InfiniteLattice.LatticePoint a :=
  ⟨castVec n, castVec_mem_latticeSubgroup h n⟩
theorem intPoint_zero (h : a * N = 1) : intPoint h 0 = 0 :=
  Subtype.ext (funext fun μ => by simp [intPoint, castVec])
theorem intPoint_add (h : a * N = 1) (m n : Fin 4 → ℤ) :
    intPoint h (m + n) = intPoint h m + intPoint h n :=
  Subtype.ext (funext fun μ => by simp [intPoint, castVec])
theorem eq_zero_of_intPoint_eq_zero (h : a * N = 1) {n : Fin 4 → ℤ} (e : intPoint h n = 0) :
    n = 0 :=
  funext fun μ => by
    have e' : (n μ : ℝ) = 0 := congrFun (congrArg Subtype.val e) μ
    exact_mod_cast e'
theorem vertexImage_intShift (h : a * N = 1) (n : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint a) :
    FullSpace.vertexImage (intShift n) x = x + intPoint h n :=
  Subtype.ext (Classical.epsilon_spec
    (p := fun x' : InfiniteLattice.LatticePoint a =>
      (x' : InfiniteLattice.AmbientSpace) = intShift n x)
    ⟨x + intPoint h n, rfl⟩ |>.trans rfl)
theorem edgeImage_intShift_ends (h : a * N = 1) (n : Fin 4 → ℤ) (b : InfiniteLattice.Link a) :
    (FullSpace.edgeImage (intShift n) b).initial = b.initial + intPoint h n ∧
      (FullSpace.edgeImage (intShift n) b).terminal = b.terminal + intPoint h n := by
  have spec := Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link a =>
      b'.initial = FullSpace.vertexImage (intShift n) b.initial ∧
        b'.terminal = FullSpace.vertexImage (intShift n) b.terminal)
    ⟨⟨FullSpace.vertexImage (intShift n) b.initial, FullSpace.vertexImage (intShift n) b.terminal, by
      obtain ⟨μ, hμ⟩ := b.isAdjacent
      refine ⟨μ, ?_⟩
      rw [vertexImage_intShift h, vertexImage_intShift h, add_sub_add_right_eq_sub]
      exact hμ⟩, rfl, rfl⟩
  have spec' : (FullSpace.edgeImage (intShift n) b).initial =
        FullSpace.vertexImage (intShift n) b.initial ∧
      (FullSpace.edgeImage (intShift n) b).terminal =
        FullSpace.vertexImage (intShift n) b.terminal := spec
  rw [vertexImage_intShift h, vertexImage_intShift h] at spec'
  exact spec'
def residuePoint (a : ℝ) (r : Fin 4 → Fin N) : InfiniteLattice.LatticePoint a :=
  ⟨fun μ => ((r μ : ℕ) : ℝ) * a, fun μ => ((r μ : ℕ) : ℤ), fun μ => by simp⟩
theorem exists_residuePoint_add_intPoint (h : a * N = 1) (hN : 0 < N)
    (x : InfiniteLattice.LatticePoint a) :
    ∃ (r : Fin 4 → Fin N) (q : Fin 4 → ℤ), x = residuePoint a r + intPoint h q := by
  obtain ⟨x, m, hm⟩ := x
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlt : ∀ μ, (m μ % (N : ℤ)).toNat < N := fun μ => by
    have h1 := Int.emod_nonneg (m μ) hN'
    have h2 := Int.emod_lt_of_pos (m μ) (by exact_mod_cast hN : (0 : ℤ) < N)
    omega
  refine ⟨fun μ => ⟨(m μ % (N : ℤ)).toNat, hlt μ⟩, fun μ => m μ / (N : ℤ), ?_⟩
  refine Subtype.ext (funext fun μ => ?_)
  show x μ = (((m μ % (N : ℤ)).toNat : ℕ) : ℝ) * a + ((m μ / (N : ℤ) : ℤ) : ℝ)
  have hr : (((m μ % (N : ℤ)).toNat : ℕ) : ℤ) = m μ % (N : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hN')
  have hr' : (((m μ % (N : ℤ)).toNat : ℕ) : ℝ) = ((m μ % (N : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast hr
  have hd : ((m μ : ℤ) : ℝ) = ((m μ % (N : ℤ) : ℤ) : ℝ) + (N : ℝ) * ((m μ / (N : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv (m μ) (N : ℤ)).symm
  rw [hm μ, hr', hd, add_mul]
  congr 1
  calc (N : ℝ) * ((m μ / (N : ℤ) : ℤ) : ℝ) * a
      = (a * N) * ((m μ / (N : ℤ) : ℤ) : ℝ) := by ring
    _ = ((m μ / (N : ℤ) : ℤ) : ℝ) := by rw [h, one_mul]
end SingleLattice
theorem finite_unitQuot_of_cover (I : PeriodicData) {F : Type} [Finite F] (g : F → I.Carrier)
    (hg : ∀ ι, ∃ (f : F) (n : Fin 4 → ℤ), ι = I.translate n (g f)) : Finite I.UnitQuot :=
  Finite.of_surjective (fun f => I.mkQuot 1 (g f)) fun c => by
    induction c using Quot.ind with
    | mk ι =>
      obtain ⟨f, n, rfl⟩ := hg ι
      exact ⟨f, Quot.sound ⟨n, by simp⟩⟩
section TowerLevels
variable {L k j N : ℕ}
theorem shiftEdge_ends (h : meshAt L k j * N = 1) (n : Fin 4 → ℤ) (b : PosEdge L k j) :
    (shiftEdge n b).1.initial = b.1.initial + intPoint h n ∧
      (shiftEdge n b).1.terminal = b.1.terminal + intPoint h n := by
  have spec := Classical.epsilon_spec
    (p := fun b' : PosEdge L k j => b'.1 = FullSpace.edgeImage (intShift n) b.1)
    ⟨⟨FullSpace.edgeImage (intShift n) b.1, by
      obtain ⟨μ, hμ⟩ := b.2
      refine ⟨μ, ?_⟩
      rw [(edgeImage_intShift_ends h n b.1).1, (edgeImage_intShift_ends h n b.1).2,
        add_sub_add_right_eq_sub]
      exact hμ⟩, rfl⟩
  have spec' : (shiftEdge n b).1 = FullSpace.edgeImage (intShift n) b.1 := spec
  rw [spec']
  exact edgeImage_intShift_ends h n b.1
theorem posEdge_ext {b b' : PosEdge L k j} (ht : b.1.initial = b'.1.initial)
    (hh : b.1.terminal = b'.1.terminal) : b = b' :=
  Subtype.ext (InfiniteLattice.Link.ext ht hh)
theorem shiftFace_corner (h : meshAt L k j * N = 1) (n : Fin 4 → ℤ) (p : FullSpace.Face L k j) :
    (shiftFace n p).corner = p.corner + intPoint h n :=
  vertexImage_intShift h n p.corner
theorem colourVertices_isPeriodic (h : meshAt L k j * N = 1) (hN : 0 < N)
    (hw : 0 < meshAt L k j) : IsPeriodic (colourVertices L k j) where
  translate_zero := fun (ι : Fin 3 × FullSpace.Vertex L k j) => by
    show (ι.1, FullSpace.vertexImage (intShift 0) ι.2) = ι
    rw [vertexImage_intShift h, intPoint_zero, add_zero]
  translate_add := fun m n (ι : Fin 3 × FullSpace.Vertex L k j) => by
    show (ι.1, FullSpace.vertexImage (intShift (m + n)) ι.2) =
      (ι.1, FullSpace.vertexImage (intShift n) (FullSpace.vertexImage (intShift m) ι.2))
    simp only [vertexImage_intShift h, intPoint_add, add_assoc]
  free := fun n (ι : Fin 3 × FullSpace.Vertex L k j) e => by
    have e' : FullSpace.vertexImage (intShift n) ι.2 = ι.2 := congrArg Prod.snd e
    rw [vertexImage_intShift h] at e'
    exact eq_zero_of_intPoint_eq_zero h (add_eq_left.mp e')
  finite_quot := by
    refine finite_unitQuot_of_cover (colourVertices L k j)
      (F := Fin 3 × (Fin 4 → Fin N)) (fun f => (f.1, residuePoint _ f.2)) ?_
    intro (ι : Fin 3 × FullSpace.Vertex L k j)
    obtain ⟨r, q, hx⟩ := exists_residuePoint_add_intPoint h hN ι.2
    refine ⟨(ι.1, r), q, ?_⟩
    show ι = (ι.1, FullSpace.vertexImage (intShift q) (residuePoint _ r))
    rw [vertexImage_intShift h, ← hx]
  pos_translate := fun n (ι : Fin 3 × FullSpace.Vertex L k j) => by
    show ((FullSpace.vertexImage (intShift n) ι.2 : FullSpace.Vertex L k j) :
      InfiniteLattice.AmbientSpace) = _
    rw [vertexImage_intShift h]
    rfl
  finite_components := inferInstanceAs (Finite Unit)
  componentOf_translate := fun _ _ => rfl
  weight_pos := fun _ => pow_pos hw 4
theorem colourEdges_isPeriodic (h : meshAt L k j * N = 1) (hN : 0 < N)
    (hw : 0 < meshAt L k j) : IsPeriodic (colourEdges L k j) where
  translate_zero := fun (ι : Fin 3 × PosEdge L k j) => by
    show (ι.1, shiftEdge 0 ι.2) = ι
    refine Prod.ext rfl (posEdge_ext ?_ ?_)
    · rw [(shiftEdge_ends h 0 ι.2).1, intPoint_zero, add_zero]
    · rw [(shiftEdge_ends h 0 ι.2).2, intPoint_zero, add_zero]
  translate_add := fun m n (ι : Fin 3 × PosEdge L k j) => by
    show (ι.1, shiftEdge (m + n) ι.2) = (ι.1, shiftEdge n (shiftEdge m ι.2))
    refine Prod.ext rfl (posEdge_ext ?_ ?_)
    · rw [(shiftEdge_ends h _ ι.2).1, (shiftEdge_ends h n _).1,
        (shiftEdge_ends h m _).1, intPoint_add, add_assoc]
    · rw [(shiftEdge_ends h _ ι.2).2, (shiftEdge_ends h n _).2,
        (shiftEdge_ends h m _).2, intPoint_add, add_assoc]
  free := fun n (ι : Fin 3 × PosEdge L k j) e => by
    have e' : shiftEdge n ι.2 = ι.2 := congrArg Prod.snd e
    have e'' := (shiftEdge_ends h n ι.2).1
    rw [e'] at e''
    exact eq_zero_of_intPoint_eq_zero h (add_eq_left.mp e''.symm)
  finite_quot := by
    refine finite_unitQuot_of_cover (colourEdges L k j)
      (F := Fin 3 × (Fin 4 → Fin N) × Fin 4)
      (fun f => (f.1, (⟨InfiniteLattice.Link.forwardFrom (residuePoint _ f.2.1) f.2.2, f.2.2,
        add_sub_cancel_left _ _⟩ : PosEdge L k j))) ?_
    intro (ι : Fin 3 × PosEdge L k j)
    obtain ⟨μ, hμ⟩ := ι.2.2
    obtain ⟨r, q, hx⟩ := exists_residuePoint_add_intPoint h hN ι.2.1.initial
    refine ⟨(ι.1, r, μ), q, ?_⟩
    show ι = (ι.1, shiftEdge q ⟨InfiniteLattice.Link.forwardFrom (residuePoint _ r) μ, μ,
      add_sub_cancel_left _ _⟩)
    refine Prod.ext rfl (posEdge_ext ?_ ?_)
    · rw [(shiftEdge_ends h q _).1]
      exact hx
    · rw [(shiftEdge_ends h q _).2]
      show ι.2.1.terminal = residuePoint _ r + InfiniteLattice.axisStep _ μ + intPoint h q
      rw [← sub_add_cancel ι.2.1.terminal ι.2.1.initial, hμ, hx]
      abel
  pos_translate := fun n (ι : Fin 3 × PosEdge L k j) => by
    show ((shiftEdge n ι.2).1.initial : InfiniteLattice.AmbientSpace) = _
    rw [(shiftEdge_ends h n ι.2).1]
    rfl
  finite_components := inferInstanceAs (Finite Unit)
  componentOf_translate := fun _ _ => rfl
  weight_pos := fun _ => pow_pos hw 4
theorem colourFaces_isPeriodic (h : meshAt L k j * N = 1) (hN : 0 < N)
    (hw : 0 < meshAt L k j) : IsPeriodic (colourFaces L k j) where
  translate_zero := fun (ι : Fin 3 × FullSpace.Face L k j) => by
    show (ι.1, shiftFace 0 ι.2) = ι
    refine Prod.ext rfl (InfiniteLattice.ElementaryPlaquette.ext ?_ rfl rfl)
    rw [shiftFace_corner h, intPoint_zero, add_zero]
  translate_add := fun m n (ι : Fin 3 × FullSpace.Face L k j) => by
    show (ι.1, shiftFace (m + n) ι.2) = (ι.1, shiftFace n (shiftFace m ι.2))
    refine Prod.ext rfl (InfiniteLattice.ElementaryPlaquette.ext ?_ rfl rfl)
    rw [shiftFace_corner h, shiftFace_corner h, shiftFace_corner h, intPoint_add, add_assoc]
  free := fun n (ι : Fin 3 × FullSpace.Face L k j) e => by
    have e' : shiftFace n ι.2 = ι.2 := congrArg Prod.snd e
    have e'' := shiftFace_corner h n ι.2
    rw [e'] at e''
    exact eq_zero_of_intPoint_eq_zero h (add_eq_left.mp e''.symm)
  finite_quot := by
    refine finite_unitQuot_of_cover (colourFaces L k j)
      (F := Fin 3 × (Fin 4 → Fin N) × {d : Fin 4 × Fin 4 // d.1 < d.2})
      (fun f => (f.1, (⟨residuePoint _ f.2.1, f.2.2.1.1, f.2.2.1.2, f.2.2.2⟩ :
        FullSpace.Face L k j))) ?_
    intro (ι : Fin 3 × FullSpace.Face L k j)
    obtain ⟨r, q, hx⟩ := exists_residuePoint_add_intPoint h hN ι.2.corner
    refine ⟨(ι.1, r, ⟨(ι.2.lowAxis, ι.2.highAxis), ι.2.lowAxis_lt_highAxis⟩), q, ?_⟩
    show ι = (ι.1, shiftFace q
      ⟨residuePoint _ r, ι.2.lowAxis, ι.2.highAxis, ι.2.lowAxis_lt_highAxis⟩)
    refine Prod.ext rfl (InfiniteLattice.ElementaryPlaquette.ext ?_ rfl rfl)
    rw [shiftFace_corner h]
    exact hx
  pos_translate := fun n (ι : Fin 3 × FullSpace.Face L k j) => by
    show ((shiftFace n ι.2).corner : InfiniteLattice.AmbientSpace) = _
    rw [shiftFace_corner h]
    rfl
  finite_components := inferInstanceAs (Finite Unit)
  componentOf_translate := fun _ _ => rfl
  weight_pos := fun _ => pow_pos hw 4
end TowerLevels
theorem claim_holds : Claim := by
  intro L hL k j hj
  have hL0 : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  have hw : 0 < meshAt L k j := zpow_pos hL0 _
  have hN : 0 < L ^ (k - j) := pow_pos (by have := hL.2; omega) _
  have h : meshAt L k j * ((L ^ (k - j) : ℕ) : ℝ) = 1 := by
    have e : (j : ℤ) - (k : ℤ) = -((k - j : ℕ) : ℤ) := by omega
    rw [meshAt, e, zpow_neg, zpow_natCast]
    push_cast
    exact inv_mul_cancel₀ (pow_ne_zero _ hL0.ne')
  exact ⟨colourVertices_isPeriodic h hN hw, colourEdges_isPeriodic h hN hw,
    colourFaces_isPeriodic h hN hw⟩
end YangMills.Construction.PeriodicOperators.TowerIndexSets
end
