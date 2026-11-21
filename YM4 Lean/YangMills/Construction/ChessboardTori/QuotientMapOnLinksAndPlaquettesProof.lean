import YangMills.Construction.ChessboardTori.InducedMapsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ProjOnEdgesAndFaces
variable {D : ChessboardSetup} (P : PeriodSubgroup D)
def pointHom : InfiniteLattice.LatticePoint D.mesh →+ P.GridPoint where
  toFun := P.projPoint
  map_zero' := Subtype.ext P.proj.map_zero
  map_add' x y := Subtype.ext (P.proj.map_add x y)
theorem pointHom_apply (x : InfiniteLattice.LatticePoint D.mesh) : pointHom P x = P.projPoint x := rfl
theorem pointHom_axisStep (μ : Fin 4) :
    pointHom P (InfiniteLattice.axisStep D.mesh μ) =
      BoxTorus.gridStep D.L ((D.K : ℕ) : ℤ) P.sideLengths μ := by
  apply Subtype.ext
  change BoxTorus.projection P.sideLengths (Pi.single μ D.mesh) =
    BoxTorus.projection P.sideLengths (D.mesh • BoxTorus.basisVector μ)
  congr 1
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp [BoxTorus.basisVector]
  · simp [BoxTorus.basisVector, Pi.single_eq_of_ne hν]
theorem projPoint_add_axisStep (x : InfiniteLattice.LatticePoint D.mesh) (μ : Fin 4) :
    P.projPoint (x + InfiniteLattice.axisStep D.mesh μ) =
      P.projPoint x + BoxTorus.gridStep D.L ((D.K : ℕ) : ℤ) P.sideLengths μ := by
  rw [← pointHom_apply, map_add, pointHom_axisStep]
  rfl
theorem pointHom_surjective : Function.Surjective (pointHom P) := by
  rintro ⟨x, n, rfl⟩
  exact ⟨D.gridVector n, Subtype.ext rfl⟩
theorem pointHom_ker : (pointHom P).ker = D.periodSubgroupOfGrid P.mult := by
  ext x
  have hx : (x : AmbientSpace) ∈ D.periodGroup P.mult ↔
      (x : AmbientSpace) ∈ (BoxTorus.projection P.sideLengths).ker := by
    rw [BoxTorus.projection_ker]
    rfl
  rw [AddMonoidHom.mem_ker]
  change _ ↔ (x : AmbientSpace) ∈ D.periodGroup P.mult
  rw [hx, AddMonoidHom.mem_ker]
  exact ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩
theorem quotientRegularity (hQ : LatticeQuotients.Statement) :
    D.QuotientRegularity (pointHom P) :=
  (hQ D P.mult P.four_le_mult).1 P.GridPoint (pointHom P) (pointHom_surjective P)
    (Or.inl (pointHom_ker P))
theorem signedAxisStep_one (ν : Fin 4) :
    D.signedAxisStep (pointHom P) 1 ν = BoxTorus.gridStep D.L ((D.K : ℕ) : ℤ) P.sideLengths ν := by
  simp [ChessboardSetup.signedAxisStep, pointHom_axisStep]
theorem isNeighbourStep_one_iff (x x' : P.GridPoint) (ν : Fin 4) :
    BoxTorus.IsNeighbourStep x x' ν 1 ↔ x' - x = D.signedAxisStep (pointHom P) 1 ν := by
  rw [signedAxisStep_one, sub_eq_iff_eq_add']
  constructor
  · rintro ⟨-, hx⟩
    apply Subtype.ext
    rw [hx]
    simp [BoxTorus.translate, BoxTorus.gridStep]
  · intro hx
    refine ⟨Or.inl rfl, ?_⟩
    rw [hx]
    simp [BoxTorus.translate, BoxTorus.gridStep]
theorem projEdge_opposite (b : D.Link) : P.projEdge b.opposite = (P.projEdge b).flip :=
  BoxTorus.DirectedEdge.ext rfl rfl
theorem projEdge_forwardFrom (x : InfiniteLattice.LatticePoint D.mesh) (μ : Fin 4) :
    P.projEdge (InfiniteLattice.Link.forwardFrom x μ) =
      BoxTorus.edgeFrom (P.projPoint x) μ :=
  BoxTorus.DirectedEdge.ext rfl (projPoint_add_axisStep P x μ)
theorem exists_positive_preimage (c : P.DirectedEdge) (ν : Fin 4)
    (hc : BoxTorus.IsNeighbourStep c.source c.target ν 1) :
    ∃ b : D.Link, b.IsPositivelyOriented ∧ P.projEdge b = c := by
  obtain ⟨x, hx⟩ := pointHom_surjective P c.source
  refine ⟨InfiniteLattice.Link.forwardFrom x ν, ⟨ν, add_sub_cancel_left _ _⟩, ?_⟩
  refine BoxTorus.DirectedEdge.ext hx ?_
  have hc' := (isNeighbourStep_one_iff P _ _ _).mp hc
  rw [signedAxisStep_one, sub_eq_iff_eq_add'] at hc'
  rw [hc', ← hx]
  exact projPoint_add_axisStep P x ν
theorem projEdge_surjective : Function.Surjective P.projEdge := by
  intro c
  obtain ⟨ν, σ, hs⟩ := c.isNeighbour
  rcases hs.1 with e | e
  · subst e
    obtain ⟨b, -, hb⟩ := exists_positive_preimage P c ν hs
    exact ⟨b, hb⟩
  · subst e
    have hs' := hs.symm
    rw [neg_neg] at hs'
    obtain ⟨b, -, hb⟩ := exists_positive_preimage P c.flip ν hs'
    refine ⟨b.opposite, ?_⟩
    rw [projEdge_opposite, hb]
    rfl
theorem projEdge_image_positive :
    P.projEdge '' {b : D.Link | b.IsPositivelyOriented} = {c : P.DirectedEdge | c.IsForward} := by
  apply Subset.antisymm
  · rintro _ ⟨b, ⟨μ, hμ⟩, rfl⟩
    refine ⟨μ, (isNeighbourStep_one_iff P _ _ _).mpr ?_⟩
    change pointHom P b.terminal - pointHom P b.initial = _
    rw [← map_sub, hμ]
    simp [ChessboardSetup.signedAxisStep]
  · rintro c ⟨ν, hc⟩
    obtain ⟨b, hb, e⟩ := exists_positive_preimage P c ν hc
    exact ⟨b, hb, e⟩
theorem projFace_surjective : Function.Surjective P.projFace := by
  intro p
  obtain ⟨x, hx⟩ := pointHom_surjective P p.corner
  exact ⟨⟨x, p.dir₁, p.dir₂, p.dir₁_lt_dir₂⟩, BoxTorus.Face.ext hx rfl rfl⟩
theorem vertexSet_projFace (p : D.Plaquette) :
    (P.projFace p).vertexSet = P.projPoint '' D.faceCorners p := by
  simp only [BoxTorus.Face.vertexSet, ChessboardSetup.faceCorners, image_insert_eq,
    image_singleton, projPoint_add_axisStep]
  rfl
theorem faceCenter_projFace (p : D.Plaquette) :
    P.faceCenter (P.projFace p) = P.proj p.center := by
  change BoxTorus.projection P.sideLengths p.corner +
      BoxTorus.projection P.sideLengths
        ((D.mesh / 2) • (BoxTorus.basisVector p.lowAxis + BoxTorus.basisVector p.highAxis)) =
    BoxTorus.projection P.sideLengths p.center
  rw [← map_add]
  congr 1
  funext ν
  simp only [InfiniteLattice.ElementaryPlaquette.center, Pi.add_apply, Pi.smul_apply,
    BoxTorus.basisVector, smul_eq_mul, Pi.single_apply]
  split_ifs <;> ring
theorem projPoint_eq_iff (x y : InfiniteLattice.LatticePoint D.mesh) :
    P.projPoint x = P.projPoint y ↔ ∃ v ∈ D.periodSubgroupOfGrid P.mult, y = x + v := by
  constructor
  · intro hxy
    refine ⟨y - x, ?_, by abel⟩
    rw [← pointHom_ker, AddMonoidHom.mem_ker, map_sub, pointHom_apply, pointHom_apply, hxy,
      sub_self]
  · rintro ⟨v, hv, rfl⟩
    rw [← pointHom_ker, AddMonoidHom.mem_ker] at hv
    rw [← pointHom_apply, ← pointHom_apply, map_add, hv, add_zero]
theorem exists_terminal_sub_initial (b : D.Link) :
    ∃ (ε : ℤˣ) (μ : Fin 4), b.terminal - b.initial = (ε : ℤ) • InfiniteLattice.axisStep D.mesh μ := by
  obtain ⟨μ, hb | hb⟩ := b.isAdjacent
  · exact ⟨1, μ, by simpa using hb⟩
  · exact ⟨-1, μ, by simpa using hb⟩
theorem projEdge_eq_iff (hQ : LatticeQuotients.Statement) (b b' : D.Link) :
    P.projEdge b = P.projEdge b' ↔ ∃ v ∈ D.periodSubgroupOfGrid P.mult, b' = D.shiftLink b v := by
  constructor
  · intro hbb
    have hs : P.projPoint b.initial = P.projPoint b'.initial :=
      congrArg BoxTorus.DirectedEdge.source hbb
    have ht : P.projPoint b.terminal = P.projPoint b'.terminal :=
      congrArg BoxTorus.DirectedEdge.target hbb
    obtain ⟨v, hv, hvs⟩ := (projPoint_eq_iff P _ _).mp hs
    obtain ⟨ε, μ, hb⟩ := exists_terminal_sub_initial b
    obtain ⟨ε', μ', hb'⟩ := exists_terminal_sub_initial b'
    have e₁ : pointHom P b.terminal - pointHom P b.initial = D.signedAxisStep (pointHom P) ε μ := by
      rw [← map_sub, hb, map_zsmul]
      rfl
    have e₂ : pointHom P b.terminal - pointHom P b.initial =
        D.signedAxisStep (pointHom P) ε' μ' := by
      rw [pointHom_apply, pointHom_apply, hs, ht, ← pointHom_apply, ← pointHom_apply, ← map_sub,
        hb', map_zsmul]
      rfl
    obtain ⟨rfl, rfl⟩ := (quotientRegularity P hQ).2.1.2.1 _ _ _ _ _ _ e₁ e₂
    refine ⟨v, hv, InfiniteLattice.Link.ext hvs ?_⟩
    have h₁ : b'.terminal = b'.initial + (b'.terminal - b'.initial) := by abel
    change b'.terminal = b.terminal + v
    rw [h₁, hb', hvs, ← hb]
    abel
  · rintro ⟨v, hv, rfl⟩
    exact BoxTorus.DirectedEdge.ext ((projPoint_eq_iff P _ _).mpr ⟨v, hv, rfl⟩)
      ((projPoint_eq_iff P _ _).mpr ⟨v, hv, rfl⟩)
theorem projFace_eq_iff (p p' : D.Plaquette) :
    P.projFace p = P.projFace p' ↔
      ∃ v ∈ D.periodSubgroupOfGrid P.mult, p' = D.shiftPlaquette p v := by
  constructor
  · intro hpp
    have hc : P.projPoint p.corner = P.projPoint p'.corner :=
      congrArg BoxTorus.Face.corner hpp
    have h₁ : p.lowAxis = p'.lowAxis := congrArg BoxTorus.Face.dir₁ hpp
    have h₂ : p.highAxis = p'.highAxis := congrArg BoxTorus.Face.dir₂ hpp
    obtain ⟨v, hv, hvc⟩ := (projPoint_eq_iff P _ _).mp hc
    exact ⟨v, hv, InfiniteLattice.ElementaryPlaquette.ext hvc h₁.symm h₂.symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact BoxTorus.Face.ext ((projPoint_eq_iff P _ _).mpr ⟨v, hv, rfl⟩) rfl rfl
theorem edgeVariable_flip (hQ : LatticeQuotients.Statement) (U : P.GaugeConfig)
    (c : P.DirectedEdge) :
    BoxTorus.edgeVariable U c.flip = (BoxTorus.edgeVariable U c)⁻¹ := by apply _root_.YangMills.Construction.ChessboardTori.InducedQuotientMaps.OnQuotient.edgeVariable_flip <;> assumption
theorem liftIsGaugeField (hQ : LatticeQuotients.Statement) (U : P.GaugeConfig) :
    P.LiftIsGaugeField U := by
  intro b
  change BoxTorus.edgeVariable U (P.projEdge b.opposite) =
    (BoxTorus.edgeVariable U (P.projEdge b))⁻¹
  rw [projEdge_opposite, edgeVariable_flip P hQ]
theorem liftGaugeField_eq (hQ : LatticeQuotients.Statement) :
    P.liftGaugeField =
      fun U => ⟨P.liftField U, liftIsGaugeField P hQ U⟩ :=
  funext fun U => dif_pos (liftIsGaugeField P hQ U)
theorem continuous_edgeVariable (c : P.DirectedEdge) :
    Continuous fun U : P.GaugeConfig => BoxTorus.edgeVariable U c := by apply _root_.YangMills.Construction.ChessboardTori.InducedQuotientMaps.OnQuotient.continuous_edgeVariable <;> assumption
theorem continuous_liftGaugeField (hQ : LatticeQuotients.Statement) :
    Continuous P.liftGaugeField := by
  rw [liftGaugeField_eq P hQ]
  exact Continuous.subtype_mk (continuous_pi fun b => continuous_edgeVariable P _) _
theorem liftGaugeField_apply (hQ : LatticeQuotients.Statement) (U : P.GaugeConfig)
    (b : D.Link) :
    (P.liftGaugeField U) b = BoxTorus.edgeVariable U (P.projEdge b) := by
  rw [liftGaugeField_eq P hQ]
  rfl
theorem faceHolonomy_lift (hQ : LatticeQuotients.Statement) (U : P.GaugeConfig)
    (p : D.Plaquette) :
    InfiniteLattice.faceHolonomy (P.liftGaugeField U) p =
      BoxTorus.faceHolonomy U (P.projFace p) := by
  simp only [InfiniteLattice.faceHolonomy, BoxTorus.faceHolonomy,
    liftGaugeField_apply P hQ, projEdge_forwardFrom, projPoint_add_axisStep]
  rfl
theorem faceEnergy_lift (hQ : LatticeQuotients.Statement) (U : P.GaugeConfig)
    (p : D.Plaquette) :
    InfiniteLattice.faceEnergy (P.liftGaugeField U) p =
      P.faceEnergy U (P.projFace p) := by
  simp only [InfiniteLattice.faceEnergy, PeriodSubgroup.faceEnergy,
    BoxTorus.faceEnergy, faceHolonomy_lift P hQ]
end ProjOnEdgesAndFaces
open ProjOnEdgesAndFaces in
theorem ProjOnEdgesAndFaces.holds (hQ : LatticeQuotients.Statement) :
    ProjOnEdgesAndFaces.Statement := by
  intro D P
  refine ⟨⟨pointHom_surjective P, projEdge_surjective P, projEdge_image_positive P,
      projFace_surjective P, projEdge_opposite P, vertexSet_projFace P,
      faceCenter_projFace P⟩,
    ⟨projPoint_eq_iff P, projEdge_eq_iff P hQ, projFace_eq_iff P⟩,
    ⟨liftIsGaugeField P hQ, continuous_liftGaugeField P hQ, fun U p =>
      ⟨faceHolonomy_lift P hQ U p, faceEnergy_lift P hQ U p⟩⟩⟩
end YangMills.Construction.ChessboardTori
end
