import YangMills.Construction.ChessboardTori.PeriodicRealizationOnARectangularTorusProof
import YangMills.Construction.ChessboardTori.ElementsCarryingLayersOfCells
import YangMills.Construction.ChessboardTori.GroupCoordinateByCoordinate
import YangMills.Construction.ChessboardTori.GroupOfAGridAndCopiesProof
import YangMills.Construction.ChessboardTori.InducedMaps
import YangMills.Construction.ChessboardTori.ReflectionsOfSlabsProof
import YangMills.Construction.InequalityOnMirroredCopies.ArrayMeanIsTheMeanOnTheTorusProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace LayerCarryingElements
variable {D : ChessboardSetup}
theorem periodSubgroup_ext {P Q : PeriodSubgroup D} (h : P.mult = Q.mult) : P = Q := by apply _root_.YangMills.SharedProofs.p50270 <;> assumption
theorem reflect_apply_axis (g : ReflectionGrid D) (μ : Fin 4) (κ : ℤ) (x : AmbientSpace) :
    g.reflect μ κ x μ = 2 * (g.origin μ + κ * g.cellSide) - x μ := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGroupAndTransport.reflect_apply_self <;> assumption
theorem reflect_apply_of_ne (g : ReflectionGrid D) (μ : Fin 4) (κ : ℤ) (x : AmbientSpace)
    {ν : Fin 4} (hν : ν ≠ μ) : g.reflect μ κ x ν = x ν := by
  simp [ReflectionGrid.reflect, coordVec, Pi.single_eq_of_ne hν]
def reflectElem (g : ReflectionGrid D) (μ : Fin 4) (κ : ℤ) : g.reflectionGroup :=
  ⟨g.reflectPerm μ κ, Subgroup.subset_closure ⟨(μ, κ), rfl⟩⟩
theorem reflect_mem_cell (g : ReflectionGrid D) (μ : Fin 4) (κ c : ℤ) (k : Fin 4 → ℤ)
    {x : AmbientSpace} (hx : x ∈ g.cell (Function.update k μ c)) :
    g.reflect μ κ x ∈ g.cell (Function.update k μ (2 * κ - 1 - c)) := by
  intro ν
  by_cases hνμ : ν = μ
  · subst hνμ
    have h1 := hx ν
    rw [Function.update_self] at h1
    rw [Function.update_self, reflect_apply_axis]
    obtain ⟨h2, h3⟩ := Set.mem_Icc.mp h1
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · push_cast
      linarith
    · push_cast
      linarith
  · have h1 := hx ν
    rw [Function.update_of_ne hνμ] at h1
    rw [Function.update_of_ne hνμ, reflect_apply_of_ne g μ κ x hνμ]
    exact h1
theorem image_reflect_cell (g : ReflectionGrid D) (μ : Fin 4) (κ c : ℤ) (k : Fin 4 → ℤ) :
    (reflectElem g μ κ).1 '' g.cell (Function.update k μ c) =
      g.cell (Function.update k μ (2 * κ - 1 - c)) := by
  refine Subset.antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact reflect_mem_cell g μ κ c k hx
  · refine ⟨g.reflect μ κ y, ?_, g.reflect_involutive μ κ y⟩
    have h := reflect_mem_cell g μ κ (2 * κ - 1 - c) k hy
    rwa [show 2 * κ - 1 - (2 * κ - 1 - c) = c by ring] at h
theorem orientationSign_reflect (g : ReflectionGrid D) (hG : g.ReflectionGroupCoordForm)
    (μ : Fin 4) (κ : ℤ) : orientationSign (reflectElem g μ κ).1 = -1 := by
  have hflip : g.numReflectedCoords (reflectElem g μ κ).1 = 1 := by
    unfold ReflectionGrid.numReflectedCoords
    rw [Finset.card_eq_one]
    refine ⟨μ, ?_⟩
    ext ν
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨z, hz⟩
      by_contra hν
      have h0 : g.reflect μ κ (fun _ => g.origin ν) ν - g.origin ν =
          g.coordReflect z (g.origin ν - g.origin ν) := hz (fun _ => g.origin ν)
      have h1 : g.reflect μ κ (fun _ => g.origin ν + 1) ν - g.origin ν =
          g.coordReflect z (g.origin ν + 1 - g.origin ν) := hz (fun _ => g.origin ν + 1)
      rw [reflect_apply_of_ne g μ κ _ hν] at h0 h1
      simp only [ReflectionGrid.coordReflect] at h0 h1
      simp only [sub_self] at h0
      simp only [add_sub_cancel_left] at h1
      linarith
    · rintro rfl
      refine ⟨κ, fun x => ?_⟩
      change g.reflect ν κ x ν - g.origin ν = g.coordReflect κ (x ν - g.origin ν)
      rw [reflect_apply_axis]
      simp only [ReflectionGrid.coordReflect]
      ring
  rw [hG.2.2.1 _ (reflectElem g μ κ).2, hflip, pow_one]
namespace OnTorus
variable (P : PeriodSubgroup D)
theorem inducesMap_apply {P : PeriodSubgroup D} {r : D.LatticeSym}
    {f : P.TorusSpace → P.TorusSpace} (hf : P.InducesMap r f) (w : AmbientSpace) :
    f (P.proj w) = P.proj (r.toFun w) :=
  (congrFun hf w).symm
theorem exists_proj_eq (u : P.TorusSpace) : ∃ w : AmbientSpace, P.proj w = u :=
  BoxTorus.projection_surjective P.sideLengths u
theorem inducesMap_unique {P : PeriodSubgroup D} {r : D.LatticeSym}
    {f f' : P.TorusSpace → P.TorusSpace} (hf : P.InducesMap r f) (hf' : P.InducesMap r f') :
    f = f' := by apply _root_.YangMills.Construction.ChessboardTori.SlabReflections.inducesMap_unique <;> assumption
theorem mapEdge_id (e : P.DirectedEdge) : P.mapEdge id e = e := by
  have h : ∃ e' : P.DirectedEdge, (e'.source : P.TorusSpace) = id e.source ∧
      (e'.target : P.TorusSpace) = id e.target :=
    ⟨e, rfl, rfl⟩
  have hs := Classical.epsilon_spec h
  exact BoxTorus.DirectedEdge.ext (Subtype.ext hs.1) (Subtype.ext hs.2)
theorem pullback_id (U : P.GaugeConfig) : P.pullback id U = U := by
  funext e
  change BoxTorus.edgeVariable U (P.mapEdge id e.1) = U e
  rw [mapEdge_id]
  unfold BoxTorus.edgeVariable
  rw [dif_pos e.2]
theorem liftGaugeField_apply (hQ : ProjOnEdgesAndFaces.Statement) (U : P.GaugeConfig)
    (e : D.Link) : (P.liftGaugeField U).1 e = P.liftField U e := by apply _root_.YangMills.Construction.ChessboardTori.BoxTorusQuotient.liftGaugeField_apply <;> assumption
end OnTorus
variable (T : TransferSetup D) (m : SlabCount)
theorem slabReverse_slabReverse (η : T.SlabConfig) : T.slabReverse (T.slabReverse η) = η := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => funext fun y => ?_)
  · simp [TransferSetup.slabReverse]
  · simp [TransferSetup.slabReverse]
def MovesLayer (a b : ℤ) (r : T.grid.reflectionGroup)
    (f : (T.torusPeriods m).GaugeConfig → (T.torusPeriods m).GaugeConfig) : Prop :=
  (∀ k : Fin 4 → ℤ, r.1 '' T.grid.cell (Function.update k T.axis a) =
    T.grid.cell (Function.update k T.axis b)) ∧
  orientationSign r.1 = (b - a).negOnePow ∧
  (∀ U, (T.grid.toLatticeSym r).pullbackField
      ((T.torusPeriods m).liftGaugeField U) =
    (T.torusPeriods m).liftGaugeField (f U)) ∧
  ∀ U, T.slabRestriction m ((a : ℤ) : ZMod (m : ℕ)) (f U) =
    if Even (b - a) then T.slabRestriction m ((b : ℤ) : ZMod (m : ℕ)) U
    else T.slabReverse (T.slabRestriction m ((b : ℤ) : ZMod (m : ℕ)) U)
variable {T m}
theorem movesLayer_refl (hG : T.grid.ReflectionGroupCoordForm) (a : ℤ) :
    MovesLayer T m a a 1 id := by
  refine ⟨fun k => ?_, ?_, fun U => ?_, fun U => ?_⟩
  · simp
  · have h := hG.2.2.2.1 _ (one_mem T.grid.reflectionGroup) _ (one_mem T.grid.reflectionGroup)
    rw [one_mul] at h
    have h1 : orientationSign ((1 : T.grid.reflectionGroup) : Equiv.Perm AmbientSpace) = 1 := by
      simpa using h
    simpa using h1
  · rfl
  · simp
theorem MovesLayer.reflectStep (hG : T.grid.ReflectionGroupCoordForm)
    (hQ : ProjOnEdgesAndFaces.Statement) {a b κ : ℤ} {r : T.grid.reflectionGroup}
    {f : (T.torusPeriods m).GaugeConfig → (T.torusPeriods m).GaugeConfig}
    (h : MovesLayer T m a b r f)
    {θ : (T.torusPeriods m).TorusSpace → (T.torusPeriods m).TorusSpace}
    (hlift : ∀ (U : (T.torusPeriods m).GaugeConfig) (e : D.Link),
      (T.torusPeriods m).liftField U ((T.planeReflection κ).linkMap e) =
        (T.torusPeriods m).liftField ((T.torusPeriods m).pullback θ U) e)
    (hη : ∀ U, T.slabRestriction m ((b : ℤ) : ZMod (m : ℕ)) ((T.torusPeriods m).pullback θ U) =
      T.slabReverse (T.slabRestriction m ((2 * κ - 1 - b : ℤ) : ZMod (m : ℕ)) U)) :
    MovesLayer T m a (2 * κ - 1 - b) (reflectElem T.grid T.axis κ * r)
      (f ∘ (T.torusPeriods m).pullback θ) := by
  obtain ⟨hc, hs, hr, hp⟩ := h
  have hodd : Odd (2 * (κ - b) - 1) := ⟨κ - b - 1, by ring⟩
  have hpar : Even (2 * κ - 1 - b - a) ↔ ¬ Even (b - a) := by
    rw [show 2 * κ - 1 - b - a = (b - a) + (2 * (κ - b) - 1) by ring, Int.even_add]
    have : ¬ Even (2 * (κ - b) - 1) := Int.not_even_iff_odd.mpr hodd
    tauto
  refine ⟨fun k => ?_, ?_, fun U => ?_, fun U => ?_⟩
  · have he : (reflectElem T.grid T.axis κ * r).1 ''
        T.grid.cell (Function.update k T.axis a) =
        (reflectElem T.grid T.axis κ).1 ''
          (r.1 '' T.grid.cell (Function.update k T.axis a)) := by
      rw [← image_comp]
      rfl
    rw [he, hc k]
    exact image_reflect_cell T.grid T.axis κ b k
  · change orientationSign (((reflectElem T.grid T.axis κ).1 * r.1 : Equiv.Perm AmbientSpace)) = _
    rw [hG.2.2.2.1 _ (reflectElem T.grid T.axis κ).2 _ r.2, orientationSign_reflect _ hG, hs,
      show 2 * κ - 1 - b - a = (b - a) + (2 * (κ - b) - 1) by ring, Int.negOnePow_add,
      Int.negOnePow_odd _ hodd, mul_comm]
  · have hB : ∀ V : D.GaugeField,
        (T.grid.toLatticeSym (reflectElem T.grid T.axis κ * r)).pullbackField V =
          (T.grid.toLatticeSym r).pullbackField
            ((T.planeReflection κ).pullbackField V) :=
      fun V => Subtype.ext (funext fun e => rfl)
    have hA : (T.planeReflection κ).pullbackField ((T.torusPeriods m).liftGaugeField U) =
        (T.torusPeriods m).liftGaugeField ((T.torusPeriods m).pullback θ U) := by
      refine Subtype.ext (funext fun e => ?_)
      change ((T.torusPeriods m).liftGaugeField U).1 ((T.planeReflection κ).linkMap e) = _
      rw [OnTorus.liftGaugeField_apply _ hQ, OnTorus.liftGaugeField_apply _ hQ, hlift]
    rw [hB, hA, hr]
    rfl
  · change T.slabRestriction m ((a : ℤ) : ZMod (m : ℕ)) (f ((T.torusPeriods m).pullback θ U)) = _
    rw [hp, hη U]
    by_cases he : Even (b - a)
    · rw [if_pos he, if_neg (fun h => hpar.mp h he)]
    · rw [if_neg he, if_pos (hpar.mpr he), slabReverse_slabReverse]
end LayerCarryingElements
open LayerCarryingElements in
theorem LayerCarryingElements.holds
    (hArith : ReflectionGridArithmetic.Statement)
    (hCoord : ReflectionGroupCoordinates.Statement)
    (hInd : QuotientMapsStatement)
    (hQ : ProjOnEdgesAndFaces.Statement)
    (hSlabs : SlabSymmetries.Statement) :
    LayerCarryingElements.Statement := by
  intro D T m hside hn hcross a b
  obtain ⟨_, hcp, heven, _, hgrp, _⟩ := ((hArith D).2.2.2 T.grid).2 hside |>.1
  have hnc : (((m : ℕ) : ℤ)) = T.grid.cellsPerTorusSide := by
    have : ((m : ℕ) : ℝ) = (T.grid.cellsPerTorusSide : ℝ) := hn.trans hcp
    exact_mod_cast this
  have hEven : Even (m : ℕ) := by
    rw [← Int.even_coe_nat, hnc]
    exact heven
  have hP : T.torusPeriods m = D.cubicPeriod := by
    rw [← hgrp]
    refine periodSubgroup_ext (funext fun ν => ?_)
    change T.cellCounts m ν * T.grid.cellRatio = T.grid.cellsPerTorusSide * T.grid.cellRatio
    rw [TransferSetup.cellCounts]
    split_ifs with h
    · rw [hnc]
    · rw [hcross, hnc]
  have hG := hCoord D T.grid
  have hstab : ∀ κ : ℤ, (T.torusPeriods m).IsStableUnder (T.planeReflection κ) := fun κ => by
    rw [hP]
    exact (hInd D).2.2.2.1 _
  have hquot : ∀ (k : ZMod (m : ℕ)) (κ : ℤ), (κ : ZMod (m : ℕ)) = k →
      (T.torusPeriods m).quotientMap (T.planeReflection (κ + 1)) = T.slabFlip m k :=
    fun k κ h => OnTorus.inducesMap_unique ((hInd D).1 _ _ (hstab (κ + 1))).1.1
      ((hSlabs D T m hEven k).1 κ h)
  have hlift : ∀ (k : ZMod (m : ℕ)) (κ : ℤ), (κ : ZMod (m : ℕ)) = k →
      ∀ (U : (T.torusPeriods m).GaugeConfig) (e : D.Link),
        (T.torusPeriods m).liftField U ((T.planeReflection (κ + 1)).linkMap e) =
          (T.torusPeriods m).liftField
            ((T.torusPeriods m).pullback (T.slabFlip m k) U) e := by
    intro k κ h U e
    have h1 := (((hInd D).1 _ _ (hstab (κ + 1))).2.2.2.1 U).2.1 e
    rwa [hquot k κ h] at h1
  have hinv : ∀ (k : ZMod (m : ℕ)) (κ : ℤ), (κ : ZMod (m : ℕ)) = k →
      ∀ U : (T.torusPeriods m).GaugeConfig,
        (T.torusPeriods m).pullback (T.slabFlip m k)
          ((T.torusPeriods m).pullback (T.slabFlip m k) U) = U := by
    intro k κ h U
    have h1 := (((hInd D).1 _ _ (hstab (κ + 1))).2.2.1 _ (hstab (κ + 1))).2.1 U
    rw [hquot k κ h] at h1
    have hi := (hSlabs D T m hEven k).1 κ h
    have h2 : T.slabFlip m k ∘ T.slabFlip m k = id := by
      funext u
      obtain ⟨w, rfl⟩ := OnTorus.exists_proj_eq _ u
      change T.slabFlip m k (T.slabFlip m k _) = _
      rw [OnTorus.inducesMap_apply hi, OnTorus.inducesMap_apply hi]
      exact congrArg _ (T.grid.reflect_involutive T.axis (κ + 1) w)
    rw [h1, h2, OnTorus.pullback_id]
  have main : ∃ (r : T.grid.reflectionGroup)
      (f : (T.torusPeriods m).GaugeConfig → (T.torusPeriods m).GaugeConfig),
      MovesLayer T m a b r f := by
    refine Int.inductionOn' b a ⟨1, id, movesLayer_refl hG a⟩ ?_ ?_
    · rintro c _ ⟨r, f, h⟩
      have e : 2 * (c + 1) - 1 - c = c + 1 := by ring
      have h1 := h.reflectStep hG hQ (κ := c + 1) (θ := T.slabFlip m ((c : ℤ) : ZMod (m : ℕ)))
        (hlift _ c rfl) (fun U => by
          rw [e, (hSlabs D T m hEven _).2.2.2.2.2.2.1 U]
          push_cast
          rfl)
      rw [e] at h1
      exact ⟨_, _, h1⟩
    · rintro c _ ⟨r, f, h⟩
      have e : 2 * c - 1 - c = c - 1 := by ring
      have e' : c - 1 + 1 = c := by ring
      have hk : (((c - 1 : ℤ) : ZMod (m : ℕ)) + 1) = ((c : ℤ) : ZMod (m : ℕ)) := by
        push_cast
        ring
      have hx := hlift ((c - 1 : ℤ) : ZMod (m : ℕ)) (c - 1) rfl
      rw [e'] at hx
      have h1 := h.reflectStep hG hQ (κ := c)
        (θ := T.slabFlip m ((c - 1 : ℤ) : ZMod (m : ℕ))) hx (fun U => by
          have h7 := (hSlabs D T m hEven ((c - 1 : ℤ) : ZMod (m : ℕ))).2.2.2.2.2.2.1
            ((T.torusPeriods m).pullback (T.slabFlip m ((c - 1 : ℤ) : ZMod (m : ℕ))) U)
          rw [hinv _ (c - 1) rfl U, hk] at h7
          rw [e, h7, slabReverse_slabReverse])
      rw [e] at h1
      exact ⟨_, _, h1⟩
  obtain ⟨r, f, h⟩ := main
  exact ⟨r, f, h⟩
end YangMills.Construction.ChessboardTori
end
