import YangMills.Construction.InfiniteLattice.ArrayOfAMirrorGridOnTheTorus
import YangMills.Construction.InfiniteLattice.ChessboardObjectsOfAMirrorGrid
import YangMills.Construction.InfiniteLattice.ChessboardValueOfTheSourcesPart
import YangMills.Construction.InfiniteLattice.GroupCopiesAndCellsOfTheBoxOfAMirrorGrid
import YangMills.Construction.InfiniteLattice.InducedGroupOfAMirrorGridOnTheTorus
import YangMills.Construction.InfiniteLattice.LatticeIsometriesAndPeriodicRealizationOnATorus
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.MultipleReflections
open InfiniteLattice (AmbientSpace)
namespace GluingNorm
open Setup.Grid
variable {D : Setup} (G : D.Grid)
theorem exists_torusSymmetry
    (hTiles : GridGroupAndBoxTiles)
    (hPull : SymmetriesAndTorusPullback)
    (r : _root_.YangMills.Construction.InfiniteLattice.ReflectionGrid.reflectionGroup G)
    {r' : D.Torus → D.Torus}
    (hr : D.coveringMap ∘ (r.1 : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) = r' ∘ D.coveringMap) :
    ∃ t : D.TorusSymmetry, t.toFun = r' := by
  obtain ⟨s, hs⟩ := ((hTiles D G G.edgeExp G.edge_eq_zpow_edgeExp).1 r).1
  obtain ⟨⟨t, ht⟩, -⟩ := (hPull D).2.2.2.2.1 s
  refine ⟨t, funext fun u => ?_⟩
  obtain ⟨x, rfl⟩ := TestFunctions.torusProj_surjective _ u
  have h1 := ht x
  have h2 := congrFun hr x
  rw [hs] at h1
  exact h1.symm.trans h2
theorem image_reflectionGroup_eq_inducedTorusMaps
    (hGrp : TorusGroupInducedHolds)
    (hCh : ChessboardObjectsHold)
    (hTiles : GridGroupAndBoxTiles)
    (hPull : SymmetriesAndTorusPullback)
    (i : ℕ) (h : 2 * G.edge ≤ D.side) :
    (fun r : Equiv.Perm D.Torus => (r : D.Torus → D.Torus)) ''
        ((G.toCubicGrid i h).reflectionGroup : Set _) = G.toChessboardGrid.inducedTorusMaps := by
  rw [(hGrp D G h i).1]
  have hI := (hCh D G).2.2.2.1
  ext r'
  constructor
  · rintro ⟨-, r, hr, hc⟩
    have hm : ((r : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) ∈
        (fun r : Equiv.Perm AmbientSpace => (r : AmbientSpace → AmbientSpace)) ''
          (G.toChessboardGrid.reflectionGroup : Set _) := by
      rw [hI]
      exact ⟨r, hr, rfl⟩
    obtain ⟨ρ, hρ, e⟩ := hm
    refine ⟨ρ, hρ, ?_⟩
    have e' : (ρ : AmbientSpace → AmbientSpace) = r := e
    rw [e']
    exact hc
  · rintro ⟨ρ, hρ, hc⟩
    have hm : (ρ : AmbientSpace → AmbientSpace) ∈
        (fun r : AmbientSpace ≃ᵃ[ℝ] AmbientSpace => (r : AmbientSpace → AmbientSpace)) ''
          (_root_.YangMills.Construction.InfiniteLattice.ReflectionGrid.reflectionGroup G : Set _) := by
      rw [← hI]
      exact ⟨ρ, hρ, rfl⟩
    obtain ⟨r, hr, e⟩ := hm
    have e' : (r : AmbientSpace → AmbientSpace) = ρ := e
    have hc' : D.coveringMap ∘ (r : AmbientSpace → AmbientSpace) = r' ∘ D.coveringMap := by
      rw [e']
      exact hc
    obtain ⟨t, rfl⟩ := exists_torusSymmetry G hTiles hPull ⟨r, hr⟩ hc'
    exact ⟨t.dist_eq, r, hr, hc'⟩
theorem torusSign_eq_orientationSign
    (hGrp : TorusGroupInducedHolds)
    (hCh : ChessboardObjectsHold)
    (hTiles : GridGroupAndBoxTiles)
    (hPull : SymmetriesAndTorusPullback)
    (i : ℕ) (h : 2 * G.edge ≤ D.side) (r : (G.toCubicGrid i h).reflectionGroup) :
    G.toChessboardGrid.torusSign (r.1 : D.Torus → D.Torus) =
      SourcesAndGluing.orientationSign (D := D.toGluingSetup i) (r.1 : D.Torus → D.Torus) := by
  have hm : (r.1 : D.Torus → D.Torus) ∈ G.toChessboardGrid.inducedTorusMaps := by
    rw [← image_reflectionGroup_eq_inducedTorusMaps G hGrp hCh hTiles hPull i h]
    exact ⟨r.1, r.2, rfl⟩
  obtain ⟨ρ₀, hρ₀, hc₀⟩ := hm
  have hs : D.coveringMap ∘
        ((G.toChessboardGrid.inducingElement (r.1 : D.Torus → D.Torus)).1 : AmbientSpace → AmbientSpace) =
      (r.1 : D.Torus → D.Torus) ∘ D.coveringMap :=
    Classical.epsilon_spec (p := fun ρ : G.toChessboardGrid.reflectionGroup =>
      D.toChessboardSetup.proj ∘ ρ.1 = (r.1 : D.Torus → D.Torus) ∘ D.toChessboardSetup.proj)
      ⟨⟨ρ₀, hρ₀⟩, hc₀⟩
  set ρ := G.toChessboardGrid.inducingElement (r.1 : D.Torus → D.Torus) with hρdef
  have hm2 : (ρ.1 : AmbientSpace → AmbientSpace) ∈
      (fun r : AmbientSpace ≃ᵃ[ℝ] AmbientSpace => (r : AmbientSpace → AmbientSpace)) ''
        (_root_.YangMills.Construction.InfiniteLattice.ReflectionGrid.reflectionGroup G : Set _) := by
    rw [← (hCh D G).2.2.2.1]
    exact ⟨ρ.1, ρ.2, rfl⟩
  obtain ⟨r₂, hr₂, e⟩ := hm2
  have e' : (r₂ : AmbientSpace → AmbientSpace) = ρ.1 := e
  have hSign := (hCh D G).2.2.2.2.1 ρ ⟨r₂, hr₂⟩ e'.symm
  have hPar := (hGrp D G h i).2 r.1 r.2 ⟨r₂, hr₂⟩ (by
    change D.coveringMap ∘ (r₂ : AmbientSpace → AmbientSpace) = _
    rw [e']
    exact hs)
  have hE : (((ChessboardTori.orientationSign ρ.1 : ℤˣ) : ℤ) : ℝ) =
      (((SourcesAndGluing.orientationSign (D := D.toGluingSetup i)
        (r.1 : D.Torus → D.Torus) : ℤˣ) : ℤ) : ℝ) :=
    hSign.trans hPar.symm
  exact Units.ext (Int.cast_injective hE)
theorem signedCopy_eq_torusTransport
    (hGrp : TorusGroupInducedHolds)
    (hCh : ChessboardObjectsHold)
    (hTiles : GridGroupAndBoxTiles)
    (hPull : SymmetriesAndTorusPullback)
    (i : ℕ) (h : 2 * G.edge ≤ D.side) (r : (G.toCubicGrid i h).reflectionGroup)
    (F : D.GaugeField → ℂ) :
    SourcesAndGluing.signedCopy (D := D.toGluingSetup i) r.1 F =
      G.toChessboardGrid.torusTransport (r.1 : D.Torus → D.Torus) (D.liftToLinks F) := by
  have hmem : (r.1 : D.Torus → D.Torus) ∈ (fun r : Equiv.Perm D.Torus => (r : D.Torus → D.Torus)) ''
      ((G.toCubicGrid i h).reflectionGroup : Set _) := ⟨r.1, r.2, rfl⟩
  rw [(hGrp D G h i).1] at hmem
  obtain ⟨hiso, r₂, hr₂, hc⟩ := hmem
  obtain ⟨t, ht⟩ := exists_torusSymmetry G hTiles hPull ⟨r₂, hr₂⟩ hc
  let rr : (D.toGluingSetup i).TorusLatticeIsometry :=
    ⟨(r.1 : D.Torus → D.Torus), ⟨r.1.bijective, hiso⟩, by
      have h1 := t.image_eq
      rw [ht] at h1
      exact h1⟩
  have hEq : rr.toEquiv = r.1 := Equiv.ext fun _ => rfl
  have hPb : ∀ U, rr.pullbackField U = D.toChessboardSetup.pullbackField (r.1 : D.Torus → D.Torus) U := by
    intro U
    funext b
    have hs := Classical.epsilon_spec (p := fun b' : D.toChessboardSetup.PeriodicLink =>
      (b'.source : D.Torus) = (r.1 : D.Torus → D.Torus) b.source ∧
        (b'.target : D.Torus) = (r.1 : D.Torus → D.Torus) b.target) ⟨rr.linkMap b, rfl, rfl⟩
    have hb : D.toChessboardSetup.imageLink (r.1 : D.Torus → D.Torus) b = rr.linkMap b :=
      PeriodicLattice.Bond.ext (Subtype.ext hs.1) (Subtype.ext hs.2)
    change U (rr.linkMap b) = U (D.toChessboardSetup.imageLink (r.1 : D.Torus → D.Torus) b)
    rw [hb]
  have hc2 := SourcesAndGluing.signedCopy_eq_actOn rr F
  rw [hEq] at hc2
  rw [hc2]
  change Conventions.signedConjFun _ _ = Conventions.signedConjFun (G.toChessboardGrid.torusSign _)
    (D.toChessboardSetup.pullbackObservable _ _)
  rw [torusSign_eq_orientationSign G hGrp hCh hTiles hPull i h r]
  congr 1
  funext U
  exact congrArg (D.liftToLinks F) (hPb U)
end GluingNorm
open GluingNorm Setup.Grid in
theorem gluingNormHolds_of_parts
    (hArr : ProductOnTorusHolds)
    (hGrp : TorusGroupInducedHolds)
    (hCh : ChessboardObjectsHold)
    (hTiles : GridGroupAndBoxTiles)
    (hPull : SymmetriesAndTorusPullback)
    (hW : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    GluingNormHolds := by
  intro D G h i k F hF
  have hprod : ∀ U : PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ),
      (G.toCubicGrid i h).reflectionProduct F U.1 = D.liftToLinks (G.reflectedProduct k F) U.1 := by
    intro U
    rw [(hArr D G h k F hF).1 U]
    change (∏ᶠ r : (G.toCubicGrid i h).reflectionGroup,
        SourcesAndGluing.signedCopy (D := D.toGluingSetup i) r.1 F U.1) =
      ∏ᶠ r' ∈ G.toChessboardGrid.inducedTorusMaps,
        G.toChessboardGrid.torusTransport r' (D.liftToLinks F) U.1
    rw [← image_reflectionGroup_eq_inducedTorusMaps G hGrp hCh hTiles hPull i h,
      finprod_mem_image DFunLike.coe_injective.injOn]
    rw [← finprod_set_coe_eq_finprod_mem]
    refine finprod_congr fun r => ?_
    rw [signedCopy_eq_torusTransport G hGrp hCh hTiles hPull i h r F]
  refine ⟨rfl, hprod, ?_⟩
  have hae : ∀ᵐ U ∂PeriodicLattice.wilsonGibbsMeasure D.L D.m D.K D.β,
      U ∈ PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ) := by
    have h1 := (hW D.L D.m D.K D.β (by have := D.isAdmissible.2; omega) D.m.pos
      D.K.pos).2.2.2.2.2.2.2.2.1
    exact mem_ae_iff.2 h1
  have he : (D.toGluingSetup i).expectation ((G.toCubicGrid i h).reflectionProduct F) =
      D.torusExpectation (G.reflectedProduct k F) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with U hU
    exact hprod ⟨U, hU⟩
  change ‖(D.toGluingSetup i).expectation ((G.toCubicGrid i h).reflectionProduct F)‖ ^ _ = _
  rw [he]
  rfl
end YangMills.Construction.MultipleReflections
end
