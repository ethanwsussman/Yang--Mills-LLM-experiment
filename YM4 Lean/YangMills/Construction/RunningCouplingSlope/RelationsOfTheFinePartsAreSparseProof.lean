import YangMills.Construction.RunningCouplingSlope.CellsOfNeighbouringFineSites
import YangMills.Construction.RunningCouplingSlope.RelationsOfTheFinePartsAreSparse
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
variable {L n k : ℕ}
private theorem face_eq_of_axes_of_edge (p p' : Tower.Face L n k 0) (h1 : p.firstAxis = p'.firstAxis)
    (h2 : p.secondAxis = p'.secondAxis) (i : Fin 4) (h : Tower.faceEdge p i = Tower.faceEdge p' i) :
    p = p' := by
  have ht := congrArg PeriodicLattice.Bond.source h
  refine PeriodicLattice.Plaquette.ext ?_ h1 h2
  fin_cases i
  · exact ht
  · change p.origin + PeriodicLattice.unitStep L n _ p.firstAxis =
      p'.origin + PeriodicLattice.unitStep L n _ p'.firstAxis at ht
    rw [h1] at ht
    exact add_right_cancel ht
  · change p.origin + PeriodicLattice.unitStep L n _ p.secondAxis =
      p'.origin + PeriodicLattice.unitStep L n _ p'.secondAxis at ht
    rw [h2] at ht
    exact add_right_cancel ht
  · exact ht
private theorem natCard_le_of_injective {α β : Type} [Finite β] (f : α → β)
    (hf : Function.Injective f) (N : ℕ) (hN : Nat.card β ≤ N) : Nat.card α ≤ N :=
  (Nat.card_le_card_of_injective f hf).trans hN
private theorem card_faces_through_le (q : Tower.PositiveEdge L n k 0) :
    Nat.card {p : Tower.Face L n k 0 // ∃ i, facePositiveEdge p i = q} ≤ 64 := by
  choose I hI using fun x : {p : Tower.Face L n k 0 // ∃ i, facePositiveEdge p i = q} => x.2
  refine natCard_le_of_injective (β := Fin 4 × Fin 4 × Fin 4)
    (fun x => (x.1.firstAxis, x.1.secondAxis, I x)) ?_ 64 (by simp)
  intro x y hxy
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨h1, h2, h3⟩ := hxy
  refine Subtype.ext (face_eq_of_axes_of_edge _ _ h1 h2 (I x) ?_)
  have e1 := congrArg Subtype.val (hI x)
  have e2 := congrArg Subtype.val (hI y)
  rw [← h3] at e2
  exact e1.trans e2.symm
private theorem cellDist_self (y : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k k)) :
    cellDist y y = 0 := by
  simp [cellDist, AmbientPoints.torusEuclidNorm_eq_sqrt]
theorem finePartRelationsSparse_of_cells (hC : NeighbouringFineVertexCells) :
    FinePartRelationsSparse := by
  intro L hL n k _ _ _
  obtain ⟨hsym, htri, -, hnear⟩ := hC L hL n k
  have hbond : ∀ (p : Tower.Face L n k 0) (i : Fin 4),
      cellDist (fineVertexCell (k := k) (Tower.faceEdge p i).source)
        (fineVertexCell (k := k) p.origin) ≤ 4 := by
    intro p i
    fin_cases i
    · change cellDist (fineVertexCell (k := k) p.origin) (fineVertexCell (k := k) p.origin) ≤ 4
      rw [cellDist_self]
      norm_num
    · rw [hsym]
      exact hnear p.origin p.firstAxis
    · rw [hsym]
      exact hnear p.origin p.secondAxis
    · change cellDist (fineVertexCell (k := k) p.origin) (fineVertexCell (k := k) p.origin) ≤ 4
      rw [cellDist_self]
      norm_num
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, card_faces_through_le, hbond⟩
  · rintro ⟨a', b⟩
    refine natCard_le_of_injective (β := Fin 3) (fun x => x.1.1) ?_ 768 (by simp)
    intro x y hxy
    exact Subtype.ext (Prod.ext hxy (x.2.trans y.2.symm))
  · rintro ⟨a, s⟩
    choose μ hμ using fun y : {p : Fin 3 × Tower.PositiveEdge L n k 0 //
      vertexEdgeIncidence p (a, s)} => y.1.2.2
    refine natCard_le_of_injective (β := Fin 3 × Fin 4) (fun y => (y.1.1, μ y)) ?_ 768 (by simp)
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have hh : x.1.2.1.target = y.1.2.1.target := x.2.symm.trans y.2
    have ht : x.1.2.1.source = y.1.2.1.source := by
      have e1 := hμ x
      have e2 := hμ y
      rw [h2, ← e2, hh] at e1
      exact sub_right_injective e1
    exact Subtype.ext (Prod.ext h1 (Subtype.ext (PeriodicLattice.Bond.ext ht hh)))
  · rintro ⟨a', b⟩ ⟨a, s⟩ h
    obtain ⟨μ, hμ⟩ := b.2
    have e : s = b.1.source + PeriodicLattice.unitStep L n _ μ := by
      rw [show s = b.1.target from h, ← hμ]
      abel
    have := hnear b.1.source μ
    change cellDist (fineVertexCell (k := k) b.1.source) (fineVertexCell (k := k) s) ≤ 8
    rw [e]
    linarith
  · rintro ⟨a', p⟩
    choose I hI using fun x : {q : Fin 3 × Tower.PositiveEdge L n k 0 //
      faceEdgeIncidence (a', p) q} => x.2
    refine natCard_le_of_injective (β := Fin 3 × Fin 4) (fun x => (x.1.1, I x)) ?_ 768 (by simp)
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    refine Subtype.ext (Prod.ext h1 ?_)
    rw [hI x, hI y, h2]
  · rintro ⟨a, b⟩
    choose I hI using fun x : {p : Fin 3 × Tower.Face L n k 0 // faceEdgeIncidence p (a, b)} => x.2
    refine natCard_le_of_injective (β := Fin 3 × Fin 4 × Fin 4 × Fin 4)
      (fun x => (x.1.1, x.1.2.firstAxis, x.1.2.secondAxis, I x)) ?_ 768 (by simp)
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3, h4⟩ := hxy
    refine Subtype.ext (Prod.ext h1 (face_eq_of_axes_of_edge _ _ h2 h3 (I x) ?_))
    have e1 := congrArg Subtype.val (hI x)
    have e2 := congrArg Subtype.val (hI y)
    rw [← h4] at e2
    exact e1.symm.trans e2
  · rintro ⟨a', p⟩ ⟨a, q⟩ ⟨i, hi⟩
    have e : q = facePositiveEdge p i := hi
    subst e
    have := hbond p i
    change cellDist (fineVertexCell (k := k) p.origin)
      (fineVertexCell (k := k) (Tower.faceEdge p i).source) ≤ 8
    rw [hsym]
    linarith
  · intro p
    have : Subsingleton {q : Fin 3 × Tower.Face L n k 0 // faceDiagonal p q} :=
      ⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩
    exact (Finite.card_le_one_iff_subsingleton.2 this).trans (by norm_num)
  · intro q
    have : Subsingleton {p : Fin 3 × Tower.Face L n k 0 // faceDiagonal p q} :=
      ⟨fun x y => Subtype.ext (x.2.symm.trans y.2)⟩
    exact (Finite.card_le_one_iff_subsingleton.2 this).trans (by norm_num)
  · intro p q h
    have e : q = p := h
    subst e
    rw [cellDist_self]
    norm_num
  · intro p
    choose P I J hI hJ using fun x : {q : Fin 3 × Tower.PositiveEdge L n k 0 //
      edgesShareFace p q} => x.2
    refine natCard_le_of_injective (β := Fin 3 × Fin 4 × Fin 4 × Fin 4 × Fin 4)
      (fun x => (x.1.1, (P x).firstAxis, (P x).secondAxis, I x, J x)) ?_ 768 (by simp)
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3, h4, h5⟩ := hxy
    have hP : P x = P y := by
      refine face_eq_of_axes_of_edge _ _ h2 h3 (I x) ?_
      have e1 := congrArg Subtype.val (hI x)
      have e2 := congrArg Subtype.val (hI y)
      rw [← h4] at e2
      exact e1.trans e2.symm
    refine Subtype.ext (Prod.ext h1 ?_)
    rw [← hJ x, ← hJ y, hP, h5]
  · intro q
    choose P I J hI hJ using fun x : {p : Fin 3 × Tower.PositiveEdge L n k 0 //
      edgesShareFace p q} => x.2
    refine natCard_le_of_injective (β := Fin 3 × Fin 4 × Fin 4 × Fin 4 × Fin 4)
      (fun x => (x.1.1, (P x).firstAxis, (P x).secondAxis, J x, I x)) ?_ 768 (by simp)
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3, h4, h5⟩ := hxy
    have hP : P x = P y := by
      refine face_eq_of_axes_of_edge _ _ h2 h3 (J x) ?_
      have e1 := congrArg Subtype.val (hJ x)
      have e2 := congrArg Subtype.val (hJ y)
      rw [← h4] at e2
      exact e1.trans e2.symm
    refine Subtype.ext (Prod.ext h1 ?_)
    rw [← hI x, ← hI y, hP, h5]
  · rintro ⟨a', b'⟩ ⟨a, b⟩ ⟨p, i, j, hi, hj⟩
    have e1 := hbond p i
    have e2 := hbond p j
    have e3 : (facePositiveEdge p i).1 = b'.1 := congrArg Subtype.val hi
    have e4 : (facePositiveEdge p j).1 = b.1 := congrArg Subtype.val hj
    change Tower.faceEdge p i = b'.1 at e3
    change Tower.faceEdge p j = b.1 at e4
    rw [e3] at e1
    rw [e4] at e2
    change cellDist (fineVertexCell (k := k) b'.1.source) (fineVertexCell (k := k) b.1.source) ≤ 8
    have := htri (fineVertexCell (k := k) b'.1.source) (fineVertexCell (k := k) p.origin)
      (fineVertexCell (k := k) b.1.source)
    rw [hsym (fineVertexCell (k := k) p.origin)] at this
    linarith
end YangMills.Construction.RunningCouplingSlope
end
