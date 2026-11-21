import YangMills.Construction.PeriodicOperators.TheFibresAtTheTopOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TopFibreDimension
section UnitMesh
variable {a : ℝ}
def latticePointOfInt (h : a = 1) (n : Fin 4 → ℤ) : InfiniteLattice.LatticePoint a :=
  ⟨castVec n, n, fun μ => by simp [castVec, h]⟩
theorem exists_eq_latticePointOfInt (h : a = 1) (x : InfiniteLattice.LatticePoint a) :
    ∃ n, x = latticePointOfInt h n := by
  obtain ⟨x, m, hm⟩ := x
  exact ⟨m, Subtype.ext (funext fun μ => by simp [latticePointOfInt, castVec, hm μ, h])⟩
theorem vertexImage_intShift (h : a = 1) (n : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint a) :
    Tower.FullSpace.vertexImage (intShift n) x = x + latticePointOfInt h n :=
  Subtype.ext (Classical.epsilon_spec
    (p := fun y : InfiniteLattice.LatticePoint a => (y : InfiniteLattice.AmbientSpace) = intShift n x)
    ⟨x + latticePointOfInt h n, rfl⟩ |>.trans rfl)
theorem edgeImage_intShift_ends (h : a = 1) (n : Fin 4 → ℤ) (l : InfiniteLattice.Link a) :
    (Tower.FullSpace.edgeImage (intShift n) l).initial = l.initial + latticePointOfInt h n ∧
      (Tower.FullSpace.edgeImage (intShift n) l).terminal = l.terminal + latticePointOfInt h n := by
  have hspec := Classical.epsilon_spec
    (p := fun l' : InfiniteLattice.Link a =>
      l'.initial = Tower.FullSpace.vertexImage (intShift n) l.initial ∧
        l'.terminal = Tower.FullSpace.vertexImage (intShift n) l.terminal)
    ⟨⟨Tower.FullSpace.vertexImage (intShift n) l.initial,
      Tower.FullSpace.vertexImage (intShift n) l.terminal, by
      obtain ⟨μ, hμ⟩ := l.isAdjacent
      refine ⟨μ, ?_⟩
      rw [vertexImage_intShift h, vertexImage_intShift h, add_sub_add_right_eq_sub]
      exact hμ⟩, rfl, rfl⟩
  have hends : (Tower.FullSpace.edgeImage (intShift n) l).initial =
        Tower.FullSpace.vertexImage (intShift n) l.initial ∧
      (Tower.FullSpace.edgeImage (intShift n) l).terminal =
        Tower.FullSpace.vertexImage (intShift n) l.terminal := hspec
  rw [vertexImage_intShift h, vertexImage_intShift h] at hends
  exact hends
theorem axisStep_injective (h : a = 1) {μ ν : Fin 4}
    (e : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a ν) : μ = ν := by
  by_contra hne
  have e' : (Pi.single μ a : InfiniteLattice.AmbientSpace) μ =
      (Pi.single ν a : InfiniteLattice.AmbientSpace) μ :=
    congrFun (congrArg Subtype.val e) μ
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne, h] at e'
  exact one_ne_zero e'
end UnitMesh
theorem finrank_fun_of_equiv {C F : Type} [Fintype F] (e : C ≃ F) :
    Module.finrank ℂ (C → ℂ) = Fintype.card F := by
  let _ : Fintype C := Fintype.ofEquiv F e.symm
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_congr e]
section Levels
variable {L k j : ℕ}
theorem shiftEdge_ends (h : Tower.meshAt L k j = 1) (n : Fin 4 → ℤ) (b : PosEdge L k j) :
    (shiftEdge n b).1.initial = b.1.initial + latticePointOfInt h n ∧
      (shiftEdge n b).1.terminal = b.1.terminal + latticePointOfInt h n := by
  have hspec := Classical.epsilon_spec
    (p := fun b' : PosEdge L k j => b'.1 = Tower.FullSpace.edgeImage (intShift n) b.1)
    ⟨⟨Tower.FullSpace.edgeImage (intShift n) b.1, by
      obtain ⟨μ, hμ⟩ := b.2
      refine ⟨μ, ?_⟩
      rw [(edgeImage_intShift_ends h n b.1).1, (edgeImage_intShift_ends h n b.1).2,
        add_sub_add_right_eq_sub]
      exact hμ⟩, rfl⟩
  have hb : (shiftEdge n b).1 = Tower.FullSpace.edgeImage (intShift n) b.1 := hspec
  rw [hb]
  exact edgeImage_intShift_ends h n b.1
def edgeAxis (b : PosEdge L k j) : Fin 4 := Classical.choose b.2
theorem edgeAxis_spec (b : PosEdge L k j) :
    b.1.terminal - b.1.initial = InfiniteLattice.axisStep _ (edgeAxis b) :=
  Classical.choose_spec b.2
theorem edgeAxis_eq (h : Tower.meshAt L k j = 1) {b : PosEdge L k j} {μ : Fin 4}
    (e : b.1.terminal - b.1.initial = InfiniteLattice.axisStep _ μ) : edgeAxis b = μ :=
  axisStep_injective h ((edgeAxis_spec b).symm.trans e)
theorem edgeAxis_shiftEdge (h : Tower.meshAt L k j = 1) (n : Fin 4 → ℤ) (b : PosEdge L k j) :
    edgeAxis (shiftEdge n b) = edgeAxis b :=
  edgeAxis_eq h (by
    rw [(shiftEdge_ends h n b).1, (shiftEdge_ends h n b).2, add_sub_add_right_eq_sub]
    exact edgeAxis_spec b)
def vertexColour : (colourVertices L k j).UnitQuot → Fin 3 :=
  Quot.lift (fun p : Fin 3 × Tower.FullSpace.Vertex L k j => p.1) (by
    rintro _ _ ⟨n, rfl⟩
    rfl)
theorem mkQuot_vertex_eq (h : Tower.meshAt L k j = 1) (c : Fin 3)
    (x x' : Tower.FullSpace.Vertex L k j) :
    (colourVertices L k j).mkQuot 1 (c, x) = (colourVertices L k j).mkQuot 1 (c, x') := by
  obtain ⟨n, hn⟩ := exists_eq_latticePointOfInt h (x' - x)
  refine Quot.sound ⟨n, ?_⟩
  show ((c, x') : Fin 3 × Tower.FullSpace.Vertex L k j) =
    (c, Tower.FullSpace.vertexImage (intShift (1 • n)) x)
  rw [one_smul, vertexImage_intShift h, ← hn, add_sub_cancel]
theorem vertexColour_bijective (h : Tower.meshAt L k j = 1) :
    Function.Bijective (vertexColour (L := L) (k := k) (j := j)) := by
  constructor
  · intro c c' e
    induction c using Quot.ind with
    | mk p =>
      induction c' using Quot.ind with
      | mk p' =>
        obtain ⟨col, x⟩ := p
        obtain ⟨col', x'⟩ := p'
        have e' : col = col' := e
        subst e'
        exact mkQuot_vertex_eq h col x x'
  · intro c
    exact ⟨(colourVertices L k j).mkQuot 1 (c, 0), rfl⟩
def edgeLabel (h : Tower.meshAt L k j = 1) : (colourEdges L k j).UnitQuot → Fin 3 × Fin 4 :=
  Quot.lift (fun p : Fin 3 × PosEdge L k j => (p.1, edgeAxis p.2)) (by
    rintro ⟨c, b⟩ _ ⟨n, rfl⟩
    show (c, edgeAxis b) = (c, edgeAxis (shiftEdge (1 • n) b))
    rw [edgeAxis_shiftEdge h])
theorem mkQuot_edge_eq (h : Tower.meshAt L k j = 1) (c : Fin 3) (b b' : PosEdge L k j)
    (e : edgeAxis b = edgeAxis b') :
    (colourEdges L k j).mkQuot 1 (c, b) = (colourEdges L k j).mkQuot 1 (c, b') := by
  obtain ⟨n, hn⟩ := exists_eq_latticePointOfInt h (b'.1.initial - b.1.initial)
  refine Quot.sound ⟨n, ?_⟩
  show ((c, b') : Fin 3 × PosEdge L k j) = (c, shiftEdge (1 • n) b)
  rw [one_smul]
  have hends := shiftEdge_ends h n b
  have hd : b.1.terminal - b.1.initial = b'.1.terminal - b'.1.initial := by
    rw [edgeAxis_spec b, edgeAxis_spec b', e]
  have hb : b' = shiftEdge n b := by
    refine Subtype.ext (InfiniteLattice.Link.ext ?_ ?_)
    · rw [hends.1, ← hn, add_sub_cancel]
    · rw [hends.2, ← hn]
      calc b'.1.terminal = (b'.1.terminal - b'.1.initial) + b'.1.initial := by abel
        _ = (b.1.terminal - b.1.initial) + b'.1.initial := by rw [hd]
        _ = b.1.terminal + (b'.1.initial - b.1.initial) := by abel
  rw [← hb]
def edgeAtOrigin (L k j : ℕ) (μ : Fin 4) : PosEdge L k j :=
  ⟨InfiniteLattice.Link.forwardFrom 0 μ, μ, by simp [InfiniteLattice.Link.forwardFrom]⟩
theorem edgeLabel_bijective (h : Tower.meshAt L k j = 1) :
    Function.Bijective (edgeLabel h) := by
  constructor
  · intro c c' e
    induction c using Quot.ind with
    | mk p =>
      induction c' using Quot.ind with
      | mk p' =>
        obtain ⟨col, b⟩ := p
        obtain ⟨col', b'⟩ := p'
        have e' : (col, edgeAxis b) = (col', edgeAxis b') := e
        obtain ⟨rfl, hd⟩ := Prod.mk.inj e'
        exact mkQuot_edge_eq h col b b' hd
  · rintro ⟨c, μ⟩
    refine ⟨(colourEdges L k j).mkQuot 1 (c, edgeAtOrigin L k j μ), ?_⟩
    show (c, edgeAxis (edgeAtOrigin L k j μ)) = (c, μ)
    rw [edgeAxis_eq h (μ := μ) (by simp [edgeAtOrigin, InfiniteLattice.Link.forwardFrom])]
end Levels
theorem claim_holds : Claim := by
  intro L _ k _
  have h : Tower.meshAt L k k = 1 := by simp [Tower.meshAt]
  refine ⟨?_, ?_⟩
  · rw [finrank_fun_of_equiv (Equiv.ofBijective _ (edgeLabel_bijective h))]
    simp
  · rw [finrank_fun_of_equiv (Equiv.ofBijective _ (vertexColour_bijective h))]
    simp
end YangMills.Construction.PeriodicOperators.TopFibreDimension
end
