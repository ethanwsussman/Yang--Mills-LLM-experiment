import YangMills.Construction.ChessboardTori.ElementaryPropertiesOfAGrid
import YangMills.Construction.ChessboardTori.PeriodicRealizationOnARectangularTorus
import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import YangMills.Construction.Lattice.CubesBlocksDistancesAndTraces
import YangMills.Construction.Lattice.SiteAndPlaquetteCounts
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace BoxTorusQuotient
section Quotient
variable {D : ChessboardSetup} (P : PeriodSubgroup D)
def pointHom : InfiniteLattice.LatticePoint D.mesh →+ P.GridPoint where
  toFun := P.projPoint
  map_zero' := Subtype.ext P.proj.map_zero
  map_add' x y := Subtype.ext (P.proj.map_add x y)
theorem pointHom_axisStep (μ : Fin 4) :
    pointHom P (InfiniteLattice.axisStep D.mesh μ) =
      BoxTorus.gridStep D.L ((D.K : ℕ) : ℤ) P.sideLengths μ := by
  apply Subtype.ext
  change BoxTorus.projection P.sideLengths (Pi.single μ D.mesh) =
    BoxTorus.projection P.sideLengths (D.mesh • BoxTorus.basisVector μ)
  congr 1
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [BoxTorus.basisVector]
  · simp [BoxTorus.basisVector, Pi.single_eq_of_ne h]
theorem pointHom_surjective : Function.Surjective (pointHom P) := by
  rintro ⟨x, n, rfl⟩
  exact ⟨D.gridVector n, Subtype.ext rfl⟩
theorem mem_subgroup_of_proj_eq_zero {z : AmbientSpace} (hz : P.proj z = 0) :
    z ∈ P.subgroup := by
  have h : z ∈ (BoxTorus.projection P.sideLengths).ker := hz
  rw [BoxTorus.projection_ker] at h
  exact h
theorem proj_eq_zero_of_mem_subgroup {z : AmbientSpace} (hz : z ∈ P.subgroup) :
    P.proj z = 0 := by
  have h : z ∈ BoxTorus.periods P.sideLengths := hz
  rw [← BoxTorus.projection_ker] at h
  exact h
theorem pointHom_ker : (pointHom P).ker = D.periodSubgroupOfGrid P.mult := by
  ext x
  rw [AddMonoidHom.mem_ker]
  change _ ↔ (x : AmbientSpace) ∈ P.subgroup
  constructor
  · intro e
    exact mem_subgroup_of_proj_eq_zero P (congrArg Subtype.val e)
  · intro e
    exact Subtype.ext (proj_eq_zero_of_mem_subgroup P e)
theorem quotientRegularity (hQ : LatticeQuotients.Statement) : D.QuotientRegularity (pointHom P) :=
  (hQ D P.mult P.four_le_mult).1 P.GridPoint (pointHom P) (pointHom_surjective P) (Or.inl (pointHom_ker P))
theorem signedAxisStep_one (ν : Fin 4) :
    D.signedAxisStep (pointHom P) 1 ν = BoxTorus.gridStep D.L ((D.K : ℕ) : ℤ) P.sideLengths ν := by
  simp [ChessboardSetup.signedAxisStep, pointHom_axisStep]
theorem isNeighbourStep_one_iff (x x' : P.GridPoint) (ν : Fin 4) :
    BoxTorus.IsNeighbourStep x x' ν 1 ↔ x' - x = D.signedAxisStep (pointHom P) 1 ν := by
  rw [signedAxisStep_one, sub_eq_iff_eq_add']
  constructor
  · rintro ⟨-, h⟩
    apply Subtype.ext
    rw [h]
    simp [BoxTorus.translate, BoxTorus.gridStep]
  · intro h
    refine ⟨Or.inl rfl, ?_⟩
    rw [h]
    simp [BoxTorus.translate, BoxTorus.gridStep]
theorem not_isForward_flip (hQ : LatticeQuotients.Statement) {c : P.DirectedEdge}
    (h : c.IsForward) : ¬ c.flip.IsForward := by
  rintro ⟨ν', h'⟩
  obtain ⟨ν, h⟩ := h
  have h₁ := (isNeighbourStep_one_iff P _ _ _).mp h
  have h₂ := (isNeighbourStep_one_iff P _ _ _).mp h'
  rcases ((quotientRegularity P hQ).2.1.2.2 c.source c.target 1 ν h₁).2 with ⟨-, hn⟩ | ⟨-, hn⟩
  · exact hn ⟨ν', h₂⟩
  · exact hn ⟨ν, h₁⟩
theorem opposite_isPositivelyOriented {b : D.Link} (h : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h₁ | h₁⟩ := b.isAdjacent
  · exact absurd ⟨μ, h₁⟩ h
  · refine ⟨μ, ?_⟩
    change b.initial - b.terminal = _
    rw [← neg_sub, h₁, neg_neg]
theorem projEdge_isForward_iff (hQ : LatticeQuotients.Statement)
    (hQF : ProjOnEdgesAndFaces.Statement) (b : D.Link) :
    (P.projEdge b).IsForward ↔ b.IsPositivelyOriented := by
  have hImg := (hQF D P).1.2.2.1
  have hpos : ∀ b : D.Link, b.IsPositivelyOriented → (P.projEdge b).IsForward := fun b hb => by
    exact show P.projEdge b ∈ {c : P.DirectedEdge | c.IsForward} from by
      rw [← hImg]
      exact ⟨b, hb, rfl⟩
  refine ⟨fun hc => ?_, hpos b⟩
  by_contra hb
  have h₁ := hpos _ (opposite_isPositivelyOriented hb)
  rw [(hQF D P).1.2.2.2.2.1 b] at h₁
  exact not_isForward_flip P hQ hc h₁
end Quotient
section Centers
variable {D : ChessboardSetup}
def axisPairIndicator (κ ι ν : Fin 4) : ℤ := (if ν = κ then 1 else 0) + (if ν = ι then 1 else 0)
set_option maxRecDepth 100000 in
theorem axes_eq_of_parity : ∀ κ ι κ' ι' : Fin 4, κ < ι → κ' < ι' →
    (∀ ν, (axisPairIndicator κ ι ν - axisPairIndicator κ' ι' ν) % 2 = 0) → κ = κ' ∧ ι = ι' := by
  decide
theorem center_apply (p : D.Plaquette) {n : Fin 4 → ℤ}
    (hn : ∀ μ, (p.corner : AmbientSpace) μ = (n μ : ℝ) * D.mesh) (ν : Fin 4) :
    p.center ν = ((2 * n ν + axisPairIndicator p.lowAxis p.highAxis ν : ℤ) : ℝ) * (D.mesh / 2) := by
  simp only [InfiniteLattice.ElementaryPlaquette.center, Pi.add_apply, hn, Pi.single_apply,
    axisPairIndicator]
  push_cast
  split_ifs <;> ring
theorem axes_eq_of_center {p p' : D.Plaquette} (s : Fin 4 → ℤ)
    (h : ∀ ν, ∃ k : ℤ, p.center ν - p'.center ν = (k : ℝ) * ((s ν : ℝ) * D.mesh)) :
    p.lowAxis = p'.lowAxis ∧ p.highAxis = p'.highAxis := by
  obtain ⟨n, hn⟩ := p.corner.2
  obtain ⟨n', hn'⟩ := p'.corner.2
  refine axes_eq_of_parity _ _ _ _ p.lowAxis_lt_highAxis p'.lowAxis_lt_highAxis fun ν => ?_
  obtain ⟨k, hk⟩ := h ν
  rw [center_apply p hn, center_apply p' hn'] at hk
  have ha : D.mesh / 2 ≠ 0 := div_ne_zero D.mesh_pos.ne' two_ne_zero
  have h1 : ((2 * n ν + axisPairIndicator p.lowAxis p.highAxis ν : ℤ) : ℝ) -
      ((2 * n' ν + axisPairIndicator p'.lowAxis p'.highAxis ν : ℤ) : ℝ) =
        2 * ((k : ℝ) * (s ν : ℝ)) := by
    refine mul_right_cancel₀ ha ?_
    rw [sub_mul, hk]
    ring
  have h2 : (2 * n ν + axisPairIndicator p.lowAxis p.highAxis ν) -
      (2 * n' ν + axisPairIndicator p'.lowAxis p'.highAxis ν) = 2 * (k * s ν) := by
    exact_mod_cast h1
  generalize k * s ν = t at h2
  omega
theorem edgesAndCenters_plane (hQ : LatticeQuotients.Statement) (D : ChessboardSetup) :
    D.EdgesAndCentersDetermine := by
  refine ⟨fun x x' κ κ' h => ?_, fun p p' h => ?_⟩
  · have ht : x = x' := congrArg InfiniteLattice.Link.initial h
    subst ht
    have hh : x + InfiniteLattice.axisStep D.mesh κ = x + InfiniteLattice.axisStep D.mesh κ' :=
      congrArg InfiniteLattice.Link.terminal h
    have e := add_left_cancel hh
    let q : InfiniteLattice.LatticePoint D.mesh →+ InfiniteLattice.LatticePoint D.mesh :=
      AddMonoidHom.id _
    have hr : D.QuotientRegularity q :=
      (hQ D (fun _ => 4) (fun _ => le_refl _)).1 _ q Function.surjective_id
        (Or.inr ((AddMonoidHom.ker_eq_bot_iff q).mpr Function.injective_id))
    have e₁ : InfiniteLattice.axisStep D.mesh κ - 0 = D.signedAxisStep q 1 κ := by
      simp [ChessboardSetup.signedAxisStep, q]
    have e₂ : InfiniteLattice.axisStep D.mesh κ - 0 = D.signedAxisStep q 1 κ' := by
      simp [ChessboardSetup.signedAxisStep, q, e]
    exact ⟨rfl, (hr.2.1.2.1 _ _ _ _ _ _ e₁ e₂).2⟩
  · obtain ⟨hf, hs⟩ := axes_eq_of_center (p := p) (p' := p') 0
      fun ν => ⟨0, by simp [h]⟩
    have hb : p.corner = p'.corner := by
      apply Subtype.ext
      funext ν
      have h' := congrFun h ν
      simp only [InfiniteLattice.ElementaryPlaquette.center, Pi.add_apply] at h'
      rw [hf, hs] at h'
      linarith
    exact ⟨hb, hf, hs, InfiniteLattice.ElementaryPlaquette.ext hb hf hs⟩
theorem edgesAndCenters_torus (hQ : LatticeQuotients.Statement)
    (hQF : ProjOnEdgesAndFaces.Statement) (P : PeriodSubgroup D) :
    P.EdgesAndCentersDetermine := by
  refine ⟨fun x x' κ κ' h => ?_, fun p p' h => ?_⟩
  · have ht : x = x' := congrArg BoxTorus.DirectedEdge.source h
    subst ht
    have hh : x + BoxTorus.gridStep D.L ((D.K : ℕ) : ℤ) P.sideLengths κ =
        x + BoxTorus.gridStep D.L ((D.K : ℕ) : ℤ) P.sideLengths κ' :=
      congrArg BoxTorus.DirectedEdge.target h
    have e := add_left_cancel hh
    have e₁ : BoxTorus.gridStep D.L ((D.K : ℕ) : ℤ) P.sideLengths κ - 0 =
        D.signedAxisStep (pointHom P) 1 κ := by
      rw [signedAxisStep_one, sub_zero]
    have e₂ : BoxTorus.gridStep D.L ((D.K : ℕ) : ℤ) P.sideLengths κ - 0 =
        D.signedAxisStep (pointHom P) 1 κ' := by
      rw [signedAxisStep_one, sub_zero, e]
    exact ⟨rfl, ((quotientRegularity P hQ).2.1.2.1 _ _ _ _ _ _ e₁ e₂).2⟩
  · obtain ⟨x, hx⟩ := pointHom_surjective P p.corner
    obtain ⟨x', hx'⟩ := pointHom_surjective P p'.corner
    let p₀ : D.Plaquette := ⟨x, p.dir₁, p.dir₂, p.dir₁_lt_dir₂⟩
    let p₀' : D.Plaquette := ⟨x', p'.dir₁, p'.dir₂, p'.dir₁_lt_dir₂⟩
    have c₀ : P.projFace p₀ = p := BoxTorus.Face.ext hx rfl rfl
    have c₀' : P.projFace p₀' = p' := BoxTorus.Face.ext hx' rfl rfl
    have hbar := (hQF D P).1.2.2.2.2.2.2
    have e : P.proj p₀.center = P.proj p₀'.center := by
      rw [← hbar, ← hbar, c₀, c₀', h]
    have hd : p₀.center - p₀'.center ∈ P.subgroup :=
      mem_subgroup_of_proj_eq_zero P (by rw [map_sub, e, sub_self])
    obtain ⟨hf, hs⟩ : p.dir₁ = p'.dir₁ ∧ p.dir₂ = p'.dir₂ :=
      axes_eq_of_center (p := p₀) (p' := p₀') P.mult fun ν => by
        obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
          ((AddSubgroup.mem_pi _).mp hd ν (mem_univ ν))
        refine ⟨k, ?_⟩
        rw [zsmul_eq_mul] at hk
        exact hk.symm
    have hb : p.corner = p'.corner := by
      rw [← hx, ← hx']
      apply Subtype.ext
      change P.proj x = P.proj x'
      have e' : P.proj ((x : AmbientSpace) + (Pi.single p.dir₁ (D.mesh / 2) +
            Pi.single p.dir₂ (D.mesh / 2))) =
          P.proj ((x' : AmbientSpace) + (Pi.single p.dir₁ (D.mesh / 2) +
            Pi.single p.dir₂ (D.mesh / 2))) := by
        have h1 : p₀.center = (x : AmbientSpace) + (Pi.single p.dir₁ (D.mesh / 2) +
            Pi.single p.dir₂ (D.mesh / 2)) := by
          simp only [InfiniteLattice.ElementaryPlaquette.center, p₀, add_assoc]
        have h2 : p₀'.center = (x' : AmbientSpace) + (Pi.single p.dir₁ (D.mesh / 2) +
            Pi.single p.dir₂ (D.mesh / 2)) := by
          simp only [InfiniteLattice.ElementaryPlaquette.center, p₀', add_assoc, hf, hs]
        rw [← h1, ← h2, e]
      rw [map_add, map_add] at e'
      exact add_right_cancel e'
    exact ⟨hb, hf, hs, BoxTorus.Face.ext hb hf hs⟩
end Centers
section Lift
variable {D : ChessboardSetup} (P : PeriodSubgroup D)
theorem liftGaugeField_apply (hQF : ProjOnEdgesAndFaces.Statement)
    (U : P.GaugeConfig) (b : D.Link) :
    (P.liftGaugeField U) b = BoxTorus.edgeVariable U (P.projEdge b) := by
  have h : P.liftGaugeField U = ⟨P.liftField U, (hQF D P).2.2.1 U⟩ :=
    dif_pos ((hQF D P).2.2.1 U)
  rw [h]
  rfl
theorem shift_liftGaugeField (hQF : ProjOnEdgesAndFaces.Statement)
    (U : P.GaugeConfig) {v : InfiniteLattice.LatticePoint D.mesh}
    (hv : v ∈ D.periodSubgroupOfGrid P.mult) :
    (InfiniteLattice.shift v).pullbackField (P.liftGaugeField U) = P.liftGaugeField U := by
  apply Subtype.ext
  funext b
  change (P.liftGaugeField U) ((InfiniteLattice.shift v).linkMap b) = (P.liftGaugeField U) b
  rw [liftGaugeField_apply P hQF, liftGaugeField_apply P hQF]
  have h : D.shiftLink b v = (InfiniteLattice.shift v).linkMap b :=
    InfiniteLattice.Link.ext (Subtype.ext rfl) (Subtype.ext rfl)
  rw [((hQF D P).2.1.2.1 b ((InfiniteLattice.shift v).linkMap b)).mpr ⟨v, hv, h.symm⟩]
end Lift
section Descended
variable {D : ChessboardSetup}
theorem linearComponent_eq {r : AmbientSpace → AmbientSpace} {R : AmbientSpace →ₗ[ℝ] AmbientSpace}
    (h : HasLinearComponent r R) : linearComponent r = R := by
  have h' : HasLinearComponent r (linearComponent r) := Classical.epsilon_spec ⟨R, h⟩
  obtain ⟨v, hv⟩ := h
  obtain ⟨v', hv'⟩ := h'
  have h0 : v' = v := by
    have := (hv' 0).symm.trans (hv 0)
    simpa using this
  subst h0
  exact LinearMap.ext fun x => add_right_cancel ((hv' x).symm.trans (hv x))
theorem isCoordDiagonal_of_mem (hE : GridBasicProperties.Statement) (g : ReflectionGrid D)
    (r : g.reflectionGroup) : IsCoordDiagonal (linearComponent (g.toLatticeSym r).toFun) := by
  have hcw := (hE D g).2.2.2.1.1 r.1 r.2
  have h : ∀ μ, ∃ c w : ℝ, ∀ x : AmbientSpace, r.1 x μ = c * x μ + w := by
    intro μ
    rcases hcw μ with ⟨t, ht⟩ | ⟨k, hk⟩
    · refine ⟨1, 2 * t * g.cellSide, fun x => ?_⟩
      have h1 := ht x
      simp only [ReflectionGrid.coordShift] at h1
      linarith
    · refine ⟨-1, 2 * k * g.cellSide + 2 * g.origin μ, fun x => ?_⟩
      have h1 := hk x
      simp only [ReflectionGrid.coordReflect] at h1
      linarith
  choose c w hc using h
  let R : AmbientSpace →ₗ[ℝ] AmbientSpace := LinearMap.pi fun μ => c μ • LinearMap.proj μ
  have hR : HasLinearComponent (g.toLatticeSym r).toFun R :=
    ⟨w, fun x => funext fun μ => by
      change r.1 x μ = (R x + w) μ
      rw [hc μ x]
      simp [R]⟩
  rw [linearComponent_eq hR]
  intro μ
  refine ⟨c μ, funext fun ν => ?_⟩
  by_cases hν : ν = μ
  · subst hν
    simp [R, coordVec]
  · simp [R, coordVec, Pi.single_eq_of_ne hν]
variable {P : PeriodSubgroup D}
theorem range_faceVertices (p : P.Face) :
    range (D.faceVertices (pointHom P) p.corner p.dir₁ p.dir₂) = p.vertexSet := by
  have h : ∀ ν, D.signedAxisStep (pointHom P) 1 ν =
      BoxTorus.gridStep D.L ((D.K : ℕ) : ℤ) P.sideLengths ν := fun ν => signedAxisStep_one P ν
  ext y
  simp only [ChessboardSetup.faceVertices, h, BoxTorus.Face.vertexSet, mem_range,
    Fin.exists_fin_succ, mem_insert_iff, mem_singleton_iff]
  simp [eq_comm]
theorem face_eq_of_vertexSet (hQ : LatticeQuotients.Statement) {p q : P.Face}
    (h : p.vertexSet = q.vertexSet) : p = q := by
  obtain ⟨h1, h2, h3⟩ := (quotientRegularity P hQ).2.2.2 p.corner q.corner p.dir₁ p.dir₂
    q.dir₁ q.dir₂ p.dir₁_lt_dir₂ q.dir₁_lt_dir₂
    (by rw [range_faceVertices, range_faceVertices, h])
  exact BoxTorus.Face.ext h1 h2 h3
def vertexImage (p : P.Face) : Set P.TorusSpace :=
  (fun x : P.GridPoint => (x : P.TorusSpace)) '' p.vertexSet
theorem mapFace_eq_of (hQ : LatticeQuotients.Statement) {s : P.TorusSpace → P.TorusSpace}
    {p c : P.Face} (h : vertexImage c = s '' vertexImage p) : P.mapFace s p = c := by
  have h' : vertexImage (P.mapFace s p) = s '' vertexImage p :=
    Classical.epsilon_spec (p := fun p' : P.Face =>
      (fun x : P.GridPoint => (x : P.TorusSpace)) '' p'.vertexSet =
        s '' ((fun x : P.GridPoint => (x : P.TorusSpace)) '' p.vertexSet)) ⟨c, h⟩
  refine face_eq_of_vertexSet hQ (image_injective.mpr Subtype.val_injective ?_)
  exact h'.trans h.symm
theorem vertexImage_projFace (hQF : ProjOnEdgesAndFaces.Statement) (p : D.Plaquette) :
    vertexImage (P.projFace p) =
      (fun x : InfiniteLattice.LatticePoint D.mesh => P.proj x) '' D.faceCorners p := by
  rw [vertexImage, (hQF D P).1.2.2.2.2.2.1 p, image_image]
  rfl
theorem mapFace_projFace (hQ : LatticeQuotients.Statement)
    (hQF : ProjOnEdgesAndFaces.Statement)
    (hL : D.LatticeSymMapsLinksFaces) {r : D.LatticeSym}
    {f : P.TorusSpace → P.TorusSpace} (hf : P.InducesMap r f) (p : D.Plaquette) :
    P.mapFace f (P.projFace p) = P.projFace (D.imageFace r p) := by
  refine mapFace_eq_of hQ ?_
  rw [vertexImage_projFace hQF, vertexImage_projFace hQF, (hL r).2.2.1 p,
    image_image, image_image]
  exact image_congr fun x _ => congrFun hf x
theorem inducesUniqueQuotientMap (hQ : LatticeQuotients.Statement)
    (hQF : ProjOnEdgesAndFaces.Statement) (hI : QuotientMapsStatement)
    (hE : GridBasicProperties.Statement) (g : ReflectionGrid D) (P : PeriodSubgroup D)
    (r : g.reflectionGroup) : P.InducesUniqueQuotientMap (g.toLatticeSym r) := by
  have hP : P.IsStableUnder (g.toLatticeSym r) :=
    (hI D).2.2.1 P _ (isCoordDiagonal_of_mem hE g r)
  obtain ⟨⟨hInd, r₁, -, -, -, hc₁, hc₂⟩, hAct, -, hPull, -⟩ := (hI D).1 P _ hP
  have hsurj : Function.Surjective P.proj :=
    BoxTorus.projection_surjective P.sideLengths
  refine ⟨⟨_, hInd, fun s hs => ?_⟩,
    Function.bijective_iff_has_inverse.mpr ⟨P.quotientMap r₁, congrFun hc₂, congrFun hc₁⟩,
    hAct.2.1, hAct.2.2.2.2.2.1, hAct.2.2.2.2.2.2.1.2,
    mapFace_projFace hQ hQF (hE D g).2.1 hInd, fun U => ⟨?_, (hPull U).2.2⟩⟩
  · funext u
    obtain ⟨z, rfl⟩ := hsurj u
    exact (congrFun hs z).symm.trans (congrFun hInd z)
  · apply Subtype.ext
    funext b
    change (P.liftGaugeField U) ((g.toLatticeSym r).linkMap b) =
      (P.liftGaugeField (P.pullback (P.quotientMap (g.toLatticeSym r)) U)) b
    rw [liftGaugeField_apply P hQF, liftGaugeField_apply P hQF]
    exact (hPull U).2.1 b
end Descended
section Transport
variable {D : ChessboardSetup}
theorem latticeSymmetry_ext {a : ℝ} {r s : InfiniteLattice.LatticeSymmetry a}
    (h : r.toFun = s.toFun) : r = s := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem mover_eq {g : ReflectionGrid D} (hEx : g.UniqueElementMapsCell)
    {S S' : Set AmbientSpace} (hS : S ∈ g.cellSet) (hS' : S' ∈ g.cellSet) (r : g.reflectionGroup)
    (h : r.1 '' S = S') : g.mover S S' = r := by
  have hspec : (g.mover S S').1 '' S = S' :=
    Classical.epsilon_spec (p := fun r : g.reflectionGroup => r.1 '' S = S') ⟨r, h⟩
  exact (hEx S hS S' hS').unique hspec h
theorem transportIsPeriodic (hQF : ProjOnEdgesAndFaces.Statement)
    (hA : ReflectionGridArithmetic.Statement) (hE : GridBasicProperties.Statement)
    (hG : ReflectionGroupAndTransport.Statement) (g : ReflectionGrid D) (hg : g.IsCoarse)
    (n : Fin 4 → ℤ) (hn : ∀ μ, 2 ≤ n μ) (hev : ∀ κ, Even (n κ)) :
    g.TransportIsPeriodic (g.boxPeriods n hn) := by
  obtain ⟨-, hEx, hSign, hCopies, -, -⟩ := hG D g hg
  have hcells := (hE D g).2.2.2.1.2.2.2.2.2.1
  have hvec := (((hA D).2.2.2 g).1.2.2.2.2 n hn).1
  have heven : ∀ x ∈ (g.boxPeriods n hn).subgroup,
      ∃ t : Fin 4 → ℤ, x = fun μ => 2 * g.cellSide * t μ := by
    intro x hx
    rw [hvec] at hx
    have h : ∀ μ, ∃ t : ℤ, x μ = 2 * g.cellSide * t := fun μ => by
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
        ((AddSubgroup.mem_pi _).mp hx μ (mem_univ μ))
      obtain ⟨c, hc⟩ := hev μ
      have hk' : (k : ℝ) * ((n μ : ℝ) * g.cellSide) = x μ := by
        simpa [zsmul_eq_mul] using hk
      refine ⟨k * c, ?_⟩
      rw [← hk', hc]
      push_cast
      ring
    choose t ht using h
    exact ⟨t, funext ht⟩
  refine ⟨fun x hx => ?_, fun S hS S' hS' F hF v hv => ?_⟩
  · obtain ⟨t, rfl⟩ := heven x hx
    exact (AddSubgroup.mem_pi _).mpr fun μ _ =>
      AddSubgroup.mem_zmultiples_iff.mpr ⟨t μ, by rw [zsmul_eq_mul]; ring⟩
  have hvv : (v : AmbientSpace) ∈ (g.boxPeriods n hn).subgroup := hv
  obtain ⟨t, ht⟩ := heven _ hvv
  obtain ⟨r, hr, hrt, hsg⟩ := hSign.2.2 t
  have hrv : (r : AmbientSpace → AmbientSpace) = fun x => x + (v : AmbientSpace) := by
    rw [hrt, ← ht]
    rfl
  let τ : g.reflectionGroup := ⟨r, hr⟩
  have himg : τ.1 '' S' = (fun x : AmbientSpace => x + (v : AmbientSpace)) '' S' := by
    change (r : AmbientSpace → AmbientSpace) '' S' = _
    rw [hrv]
  have hcell : (fun x : AmbientSpace => x + (v : AmbientSpace)) '' S' ∈ g.cellSet := by
    rw [← himg]
    exact hcells r hr S' hS'
  have hcar := mover_eq hEx hS' hcell τ himg
  have hτ : g.toLatticeSym τ = InfiniteLattice.shift v := latticeSymmetry_ext hrv
  have hsg' : orientationSign τ.1 = 1 := hsg
  have hcopy : ∀ G : D.GaugeField → ℂ,
      g.transportTo S' ((fun x : AmbientSpace => x + (v : AmbientSpace)) '' S') G =
        (InfiniteLattice.shift v).actOn G := by
    intro G
    unfold ReflectionGrid.transportTo
    rw [hcar]
    unfold ReflectionGrid.transport
    rw [hτ, hsg']
    funext U
    simp [Conventions.signedConjFun, Conventions.signedConj]
  have hmain : g.transportTo S ((fun x : AmbientSpace => x + (v : AmbientSpace)) '' S') F =
      (InfiniteLattice.shift v).actOn (g.transportTo S S' F) := by
    rw [← hcopy]
    exact ((hCopies.1 S hS S' hS' _ hcell F hF F hF).2.2.1).symm
  refine ⟨hcell, hmain, fun U => ?_⟩
  rw [hmain]
  change (g.transportTo S S' F) ((InfiniteLattice.shift v).pullbackField
    ((g.boxPeriods n hn).liftGaugeField U)) = _
  rw [shift_liftGaugeField _ hQF U hv]
theorem transportThroughReflections (hQ : LatticeQuotients.Statement)
    (hQF : ProjOnEdgesAndFaces.Statement) (hI : QuotientMapsStatement)
    (hE : GridBasicProperties.Statement) (hG : ReflectionGroupAndTransport.Statement)
    (g : ReflectionGrid D) (hg : g.IsCoarse) (P : PeriodSubgroup D) :
    g.TransportThroughReflections P := by
  obtain ⟨-, hEx, hSign, -, -, -⟩ := hG D g hg
  have hcells := (hE D g).2.2.2.1.2.2.2.2.2.1
  intro S hS F hF μ k
  have hcell : g.reflect μ k '' S ∈ g.cellSet :=
    hcells _ (g.reflectElem μ k).2 S hS
  have hcar := mover_eq hEx hS hcell (g.reflectElem μ k) rfl
  have hsgn : orientationSign (g.reflectElem μ k).1 = -1 := hSign.2.1 μ k
  have hcopy : g.transportTo S (g.reflect μ k '' S) F = fun U : D.GaugeField =>
      starRingEnd ℂ ((g.toLatticeSym (g.reflectElem μ k)).actOn F U) := by
    unfold ReflectionGrid.transportTo
    rw [hcar]
    unfold ReflectionGrid.transport
    rw [hsgn]
    funext U
    simp [Conventions.signedConjFun, Conventions.signedConj]
  refine ⟨hcopy, fun U => ?_⟩
  rw [hcopy]
  have hcfg :=
    ((inducesUniqueQuotientMap hQ hQF hI hE g P (g.reflectElem μ k)).2.2.2.2.2.2 U).1
  change starRingEnd ℂ (F ((g.toLatticeSym (g.reflectElem μ k)).pullbackField
    (P.liftGaugeField U))) = _
  rw [hcfg]
end Transport
section Expectation
theorem sourcedBoltzmannWeight_eq {L m : ℕ} {j : ℤ} [Finite (PeriodicLattice.Plaquette L m j)]
    {β : ℝ} (w : PeriodicLattice.FourTorus L m → ℂ)
    {U : PeriodicLattice.Bond L m j → Matrices.ComplexMatrix2}
    (hp : ∀ p : PeriodicLattice.Plaquette L m j,
      ((PeriodicLattice.plaquetteCost U p : ℝ) : ℂ) = PeriodicLattice.plaquetteEnergy U p) :
    PeriodicLattice.sourcedBoltzmannWeight β w U =
      (PeriodicLattice.boltzmannWeight β U : ℂ) *
        Complex.exp (PeriodicLattice.smearedObservable w U) := by
  have := Fintype.ofFinite (PeriodicLattice.Plaquette L m j)
  unfold PeriodicLattice.sourcedBoltzmannWeight PeriodicLattice.boltzmannWeight
    PeriodicLattice.barycenterWeightedEnergy PeriodicLattice.plaquetteWeightedEnergy
    PeriodicLattice.smearedObservable PeriodicLattice.wilsonAction
  simp only [finsum_eq_sum_of_fintype, ← hp, Complex.real_smul]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [mul_comm]
  ring
theorem liftedExpectationFormula_holds
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (hT : PeriodicLattice.CubeGeometry.ElementaryLatticeFacts)
    (D : ChessboardSetup) : D.LiftedExpectationFormula := by
  intro F hF
  have hL1 : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  have hL : 0 < D.L := by omega
  obtain ⟨-, -, -, hint, hZ, -, hreal, -⟩ := hW D.L D.m D.K D.β hL1 D.m.pos D.K.pos
  have hae : ∀ᵐ U ∂(PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)),
      U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) := mem_ae_iff.mpr hreal
  have hfin : Finite D.PeriodicPlaquette := by
    have hm : -((D.m : ℕ) : ℤ) ≤ ((D.K : ℕ) : ℤ) := by omega
    obtain ⟨-, -, -, hc, -⟩ := hC D.L D.m ((D.K : ℕ) : ℤ) hL hm
    apply Nat.finite_of_card_ne_zero
    rw [hc]
    have : 0 < 6 * (2 * D.L ^ (((D.m : ℕ) : ℤ) + ((D.K : ℕ) : ℤ)).toNat) ^ 4 := by positivity
    omega
  have hZ0 : D.partitionFunction 0 =
      ((PeriodicLattice.partitionFunction D.L D.m D.K D.β : ℝ) : ℂ) := by
    change ∫ U, PeriodicLattice.sourcedBoltzmannWeight D.β 0 U
      ∂(PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)) = _
    rw [PeriodicLattice.partitionFunction, ← integral_complex_ofReal]
    refine integral_congr_ae (hae.mono fun U hU => ?_)
    rw [sourcedBoltzmannWeight_eq 0 ((hT D.toStandingParameters).2.2 U hU).1]
    simp [PeriodicLattice.smearedObservable]
  have hm := InfiniteLattice.measurable_liftField D.L D.m ((D.K : ℕ) : ℤ)
  have hd : AEMeasurable (fun W => ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β W))
      (PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hint.aestronglyMeasurable.aemeasurable
  have h1 : D.liftedExpectation F =
      ∫ W, F (D.liftField W) ∂(PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β) :=
    integral_map hm.aemeasurable hF.1.aestronglyMeasurable
  have h2 : ∫ W, F (D.liftField W) ∂(PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β) =
      ((ENNReal.ofReal (PeriodicLattice.partitionFunction D.L D.m D.K D.β))⁻¹).toReal •
        ∫ W, (ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β W)).toReal • F (D.liftField W)
          ∂(PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)) := by
    unfold PeriodicLattice.wilsonGibbsMeasure
    rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul₀ hd
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have h3 : ∫ W, (ENNReal.ofReal (PeriodicLattice.boltzmannWeight D.β W)).toReal •
      F (D.liftField W) ∂(PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)) =
      ∫ U, F (D.liftField U) *
        Complex.exp (-(D.β : ℂ) * (PeriodicLattice.wilsonAction U : ℂ))
        ∂PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ) := by
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    have hn : 0 ≤ PeriodicLattice.boltzmannWeight D.β U := (Real.exp_pos _).le
    simp only []
    rw [ENNReal.toReal_ofReal hn, Complex.real_smul, PeriodicLattice.boltzmannWeight, mul_comm]
    push_cast
    rfl
  rw [h1, h2, h3, hZ0, ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le, Complex.real_smul]
  push_cast
  rfl
end Expectation
theorem statement_holds (hQ : LatticeQuotients.Statement)
    (hQF : ProjOnEdgesAndFaces.Statement) (hI : QuotientMapsStatement)
    (hA : ReflectionGridArithmetic.Statement) (hE : GridBasicProperties.Statement)
    (hG : ReflectionGroupAndTransport.Statement)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement)
    (hC : PeriodicLattice.SiteAndPlaquetteCounts)
    (hT : PeriodicLattice.CubeGeometry.ElementaryLatticeFacts) :
    Statement := by
  intro O
  refine ⟨fun n hn => ?_, fun hside => ?_⟩
  · have hc := hQF O.toChessboardSetup (O.grid.boxPeriods n hn)
    refine ⟨⟨fun x hx => O.toChessboardSetup.periodGroup_le_gridPoints _ hx,
        fun b => ⟨rfl, rfl, projEdge_isForward_iff _ hQ hQF b⟩,
        fun p => ⟨hc.1.2.2.2.2.2.1 p, hc.1.2.2.2.2.2.2 p⟩⟩,
      ⟨hc.1.1, fun c hc' => ?_, hc.1.2.2.2.1⟩,
      ⟨hc.2.1.1, fun b b' _ _ => hc.2.1.2.1 b b', hc.2.1.2.2⟩,
      edgesAndCenters_plane hQ O.toChessboardSetup, edgesAndCenters_torus hQ hQF _,
      ⟨hc.2.2.1, hc.2.2.2.1, fun U p => (hc.2.2.2.2 U p).2,
        fun U v hv => shift_liftGaugeField _ hQF U hv⟩,
      fun r => inducesUniqueQuotientMap hQ hQF hI hE O.grid _ r,
      fun hev => transportIsPeriodic hQF hA hE hG O.grid O.isCoarse n hn hev,
      transportThroughReflections hQ hQF hI hE hG O.grid O.isCoarse _⟩
    have h : c ∈ (O.grid.boxPeriods n hn).projEdge ''
        {b : O.toChessboardSetup.Link | b.IsPositivelyOriented} := by
      rw [hc.1.2.2.1]
      exact hc'
    obtain ⟨b, hb, e⟩ := h
    exact ⟨b, hb, e⟩
  · obtain ⟨hreads, -, -, hg⟩ := hA O.toChessboardSetup
    exact ⟨((hg O.grid).2 hside).1, hreads,
      liftedExpectationFormula_holds hW hC hT O.toChessboardSetup⟩
end BoxTorusQuotient
end YangMills.Construction.ChessboardTori
end
