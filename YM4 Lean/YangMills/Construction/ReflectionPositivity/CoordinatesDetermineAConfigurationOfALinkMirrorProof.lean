import YangMills.Construction.Lattice.OppositeBondsAndPositiveValues
import YangMills.Construction.ReflectionPositivity.CoordinatesDetermineAConfigurationOfALinkMirror
import YangMills.Construction.ReflectionPositivity.HeightOverALinkPosition
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkCoordinates
variable {D : MirrorData}
theorem coe_inv_specialUnitary (g : Matrices.ComplexMatrix2.specialUnitary) :
    ((g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      (g : Matrices.ComplexMatrix2)⁻¹ := by apply _root_.YangMills.Construction.InfiniteLattice.specialUnitary_coe_inv <;> assumption
theorem not_mem_openSlab_pos_and_neg (C : LinkLevel D) {x : D.Torus} (hx : x ∈ C.openSlab .pos)
    (hx' : x ∈ C.openSlab .neg) : False := by
  obtain ⟨y, ⟨h₁, h₂⟩, rfl⟩ := hx
  obtain ⟨y', ⟨h₃, h₄⟩, e⟩ := hx'
  have hs : 0 < PeriodicLattice.torusSide D.L D.m := LinkLevel.side_pos (D := D)
  have : Fact (0 < PeriodicLattice.torusSide D.L D.m) := ⟨hs⟩
  simp only [SlabSide.toReal, one_mul, neg_mul] at h₁ h₂ h₃ h₄
  have hside : D.side = PeriodicLattice.torusSide D.L D.m := rfl
  rw [hside] at h₂ h₄
  have e' : ((y' D.dir : ℝ) : AddCircle (PeriodicLattice.torusSide D.L D.m)) = (y D.dir : ℝ) :=
    congrFun e D.dir
  have m₁ : y D.dir ∈ Ico (C.pos - PeriodicLattice.torusSide D.L D.m / 2)
      (C.pos - PeriodicLattice.torusSide D.L D.m / 2 + PeriodicLattice.torusSide D.L D.m) :=
    ⟨by linarith, by linarith⟩
  have m₂ : y' D.dir ∈ Ico (C.pos - PeriodicLattice.torusSide D.L D.m / 2)
      (C.pos - PeriodicLattice.torusSide D.L D.m / 2 + PeriodicLattice.torusSide D.L D.m) :=
    ⟨by linarith, by linarith⟩
  have := (AddCircle.coe_eq_coe_iff_of_mem_Ico m₂ m₁).1 e'
  linarith
theorem not_mem_halfEdges_pos_and_neg (C : LinkLevel D) {b : D.Edge}
    (hb : b ∈ C.halfEdges .pos) (hb' : b ∈ C.halfEdges .neg) : False :=
  not_mem_openSlab_pos_and_neg C hb.2.1.2 hb'.2.1.2
def tripleValue (C : LinkLevel D) (uPos : C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary)
    (uNeg : C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary)
    (w : C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary)
    (b : D.Edge) : Matrices.ComplexMatrix2.specialUnitary :=
  open Classical in
  if hp : b ∈ C.halfEdges .pos then uPos ⟨b, hp⟩
  else if hn : b ∈ C.halfEdges .neg then uNeg ⟨b, hn⟩
  else if ht : b ∈ C.transversalEdges then
    (if C.orientedAcross b = b then w ⟨b, ht⟩ else (w ⟨b, ht⟩)⁻¹)
  else 1
def extendInv (g : D.Edge → Matrices.ComplexMatrix2.specialUnitary) (b : D.Edge) :
    Matrices.ComplexMatrix2.specialUnitary :=
  open Classical in
  if b.IsPositivelyOriented then g b else (g b.opposite)⁻¹
theorem opposite_opposite_and_xor
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (b : D.Edge) : b.opposite.opposite = b ∧
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
  have hj : -((D.m : ℕ) : ℤ) < (((D.K : ℕ) : ℤ)) := by
    have h₁ := D.K.pos
    have h₂ := D.m.pos
    omega
  obtain ⟨-, -, h₃, -, -, h₄⟩ := (hb D.toStandingParameters ((D.K : ℕ) : ℤ) hj).1 b
  exact ⟨h₃, h₄⟩
theorem extendInv_opposite
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (g : D.Edge → Matrices.ComplexMatrix2.specialUnitary) (b : D.Edge) :
    extendInv g b.opposite = (extendInv g b)⁻¹ := by
  obtain ⟨hr, hx⟩ := opposite_opposite_and_xor hb b
  rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [extendInv, extendInv, if_neg h₂, if_pos h₁, hr]
  · rw [extendInv, extendInv, if_pos h₁, if_neg h₂, inv_inv]
def fieldOfValues
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (g : D.Edge → Matrices.ComplexMatrix2.specialUnitary) : D.FieldSpace :=
  ⟨fun b => (extendInv g b : Matrices.ComplexMatrix2), fun b _ => (extendInv g b).2, fun b _ => by
    change ((extendInv g b.opposite : Matrices.ComplexMatrix2.specialUnitary) :
        Matrices.ComplexMatrix2) =
      ((extendInv g b : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)⁻¹
    rw [extendInv_opposite hb, coe_inv_specialUnitary]⟩
theorem hasCoords_fieldOfValues
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (C : LinkLevel D) (uPos : C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary)
    (uNeg : C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary)
    (w : C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary) :
    C.HasCoords (fieldOfValues hb (tripleValue C uPos uNeg w)) uPos uNeg w := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · funext b
    apply Subtype.ext
    change ((extendInv (tripleValue C uPos uNeg w) b.1 : Matrices.ComplexMatrix2.specialUnitary) :
      Matrices.ComplexMatrix2) = _
    rw [extendInv, if_pos b.2.1, tripleValue, dif_pos b.2]
  · funext b
    apply Subtype.ext
    change ((extendInv (tripleValue C uPos uNeg w) b.1 : Matrices.ComplexMatrix2.specialUnitary) :
      Matrices.ComplexMatrix2) = _
    have hn : b.1 ∉ C.halfEdges .pos := fun h => not_mem_halfEdges_pos_and_neg C h b.2
    rw [extendInv, if_pos b.2.1, tripleValue, dif_neg hn, dif_pos b.2]
  · funext b
    apply Subtype.ext
    change ((extendInv (tripleValue C uPos uNeg w) (C.orientedAcross b.1) :
      Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) = _
    have hval : tripleValue C uPos uNeg w b.1 =
        if C.orientedAcross b.1 = b.1 then w b else (w b)⁻¹ := by
      rw [tripleValue, dif_neg b.2.2.1, dif_neg b.2.2.2, dif_pos b.2]
    have hpos : extendInv (tripleValue C uPos uNeg w) b.1 =
        tripleValue C uPos uNeg w b.1 := if_pos b.2.1
    by_cases h : C.orientedAcross b.1 = b.1
    · rw [h, hpos, hval, h, if_pos rfl]
    · have h' : C.orientedAcross b.1 = b.1.opposite :=
        (C.orientedAcross_eq_or b.1).resolve_left h
      rw [h', extendInv_opposite hb, hpos, hval, if_neg h, inv_inv]
theorem val_eq_inv_opposite
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (U : D.FieldSpace) (b : D.Edge) : U.1 b = (U.1 b.opposite)⁻¹ := by
  have h := U.2.2 b.opposite (mem_univ _)
  rwa [(opposite_opposite_and_xor hb b).1] at h
theorem eq_of_hasCoords
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (C : LinkLevel D) {U U' : D.FieldSpace}
    {uPos : C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary}
    {uNeg : C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary}
    {w : C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary}
    (h : C.HasCoords U uPos uNeg w) (h' : C.HasCoords U' uPos uNeg w) :
    U = U' := by
  have hpos : ∀ b : D.Edge, b.IsPositivelyOriented → U.1 b = U'.1 b := by
    intro b hbp
    by_cases hp : b ∈ C.halfEdges .pos
    · exact congrArg Subtype.val (congrFun (h.1.trans h'.1.symm) ⟨b, hp⟩)
    by_cases hn : b ∈ C.halfEdges .neg
    · exact congrArg Subtype.val (congrFun (h.2.1.trans h'.2.1.symm) ⟨b, hn⟩)
    have ht : b ∈ C.transversalEdges := ⟨hbp, hp, hn⟩
    have e : U.1 (C.orientedAcross b) = U'.1 (C.orientedAcross b) :=
      congrArg Subtype.val (congrFun (h.2.2.trans h'.2.2.symm) ⟨b, ht⟩)
    rcases C.orientedAcross_eq_or b with r | r
    · rwa [r] at e
    · rw [r] at e
      rw [val_eq_inv_opposite hb U b, val_eq_inv_opposite hb U' b, e]
  apply Subtype.ext
  funext b
  rcases (opposite_opposite_and_xor hb b).2 with ⟨h₁, -⟩ | ⟨h₁, -⟩
  · exact hpos b h₁
  · rw [val_eq_inv_opposite hb U b, val_eq_inv_opposite hb U' b, hpos _ h₁]
theorem coordinatesDetermineField_of_opposite
    (hb : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction) :
    CoordinatesDetermineField := by
  intro D C
  have hex : ∀ (uPos : C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary)
      (uNeg : C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary)
      (w : C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary),
      ∃ U : D.FieldSpace, C.HasCoords U uPos uNeg w :=
    fun uPos uNeg w => ⟨_, hasCoords_fieldOfValues hb C uPos uNeg w⟩
  refine ⟨fun uPos uNeg w => ⟨?_, ?_⟩, fun σ u => ?_⟩
  · obtain ⟨U, hU⟩ := hex uPos uNeg w
    exact ⟨U, hU, fun U' hU' => eq_of_hasCoords hb C hU' hU⟩
  · exact Classical.epsilon_spec (hex uPos uNeg w)
  · cases σ
    · obtain ⟨U, hU⟩ := hex u (fun _ => 1) (fun _ => 1)
      exact ⟨U, hU.1⟩
    · obtain ⟨U, hU⟩ := hex (fun _ => 1) u (fun _ => 1)
      exact ⟨U, hU.2.1⟩
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkCoordinates
end
