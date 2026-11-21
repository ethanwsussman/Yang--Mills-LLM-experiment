import YangMills.Construction.ChessboardTori.SidesCentresAndTheChessboardFunctional
import YangMills.Construction.MirrorGridsOfEverySide.MirrorGridOrientationsAndReflectionProducts
import YangMills.Construction.ReflectionPositivity.SpaceOfConfigurationsAndPlaquetteEnergiesAtOneCutoff
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
open InfiniteLattice (AmbientSpace)
open ChessboardTori (ReflectionGrid orientationSign)
structure ScalingMap (D : GridSetup) where
  power : ℕ
  power_lt : power < (D.K : ℕ)
  shift : AmbientSpace
  shift_mem : shift ∈ D.gridPoints
namespace ScalingMap
variable {D : GridSetup} (S : ScalingMap D)
def coarseCutoff : ℕ+ := ⟨(D.K : ℕ) - S.power, Nat.sub_pos_of_lt S.power_lt⟩
def fineExponent : ℕ+ := ⟨(D.m : ℕ) + S.power, Nat.add_pos_left D.m.pos _⟩
def image : GridSetup := D.withIndices S.coarseCutoff S.fineExponent
def scale : ℝ := (D.L : ℝ) ^ S.power
theorem scale_pos : 0 < S.scale :=
  pow_pos (by linarith [D.one_lt_factor]) _
def toFun (x : AmbientSpace) : AmbientSpace := fun μ => S.scale * (x μ - S.shift μ)
def toPerm : Equiv.Perm AmbientSpace where
  toFun := S.toFun
  invFun y := fun μ => S.scale⁻¹ * y μ + S.shift μ
  left_inv x := by
    have hne := S.scale_pos.ne'
    funext μ
    simp only [toFun]
    field_simp
    ring
  right_inv y := by
    have hne := S.scale_pos.ne'
    funext μ
    simp only [toFun]
    field_simp
    ring
theorem image_mesh : S.image.mesh = S.scale * D.mesh := by
  have hL : (D.L : ℝ) ≠ 0 := by linarith [D.one_lt_factor]
  have hle : S.power ≤ (D.K : ℕ) := S.power_lt.le
  change (D.L : ℝ) ^ (-(((((D.K : ℕ) - S.power : ℕ)) : ℕ) : ℤ)) =
    (D.L : ℝ) ^ S.power * (D.L : ℝ) ^ (-(((D.K : ℕ) : ℕ) : ℤ))
  rw [← zpow_natCast (D.L : ℝ) S.power, ← zpow_add₀ hL]
  congr 1
  omega
theorem toFun_mem {x : AmbientSpace} (hx : x ∈ D.gridPoints) :
    S.toFun x ∈ S.image.gridPoints := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨u, hu⟩ := S.shift_mem
  refine ⟨n - u, fun μ => ?_⟩
  simp only [toFun, hn μ, hu μ, S.image_mesh, Pi.sub_apply, Int.cast_sub]
  ring
def pointMap (x : InfiniteLattice.LatticePoint D.mesh) : InfiniteLattice.LatticePoint S.image.mesh :=
  ⟨S.toFun x, S.toFun_mem x.2⟩
theorem pointMap_sub_pointMap {x y : InfiniteLattice.LatticePoint D.mesh} {μ : Fin 4}
    (h : y - x = InfiniteLattice.axisStep D.mesh μ) :
    S.pointMap y - S.pointMap x = InfiniteLattice.axisStep S.image.mesh μ := by
  apply Subtype.ext
  funext ν
  have h' := congrFun (congrArg Subtype.val h) ν
  change (y : AmbientSpace) ν - (x : AmbientSpace) ν = (Pi.single μ D.mesh : AmbientSpace) ν at h'
  change S.scale * ((y : AmbientSpace) ν - S.shift ν) - S.scale * ((x : AmbientSpace) ν - S.shift ν) =
    (Pi.single μ S.image.mesh : AmbientSpace) ν
  have h2 : S.scale * ((y : AmbientSpace) ν - S.shift ν) - S.scale * ((x : AmbientSpace) ν - S.shift ν) =
      S.scale * ((y : AmbientSpace) ν - (x : AmbientSpace) ν) := by ring
  rw [h2, h', S.image_mesh]
  by_cases hν : ν = μ
  · subst hν
    simp
  · simp [Pi.single_eq_of_ne hν]
def linkMap (e : D.Link) : S.image.Link where
  initial := S.pointMap e.initial
  terminal := S.pointMap e.terminal
  isAdjacent := by
    obtain ⟨μ, h | h⟩ := e.isAdjacent
    · exact ⟨μ, Or.inl (S.pointMap_sub_pointMap h)⟩
    · refine ⟨μ, Or.inr ?_⟩
      have h' : e.initial - e.terminal = InfiniteLattice.axisStep D.mesh μ := by
        rw [← neg_sub, h, neg_neg]
      rw [← S.pointMap_sub_pointMap h', neg_sub]
theorem linkMap_opposite (e : D.Link) : S.linkMap e.opposite = (S.linkMap e).opposite := rfl
def pullback (U' : S.image.GaugeField) : D.GaugeField :=
  ⟨fun e => U' (S.linkMap e), fun e => U'.2 (S.linkMap e)⟩
def faceMap (p : D.Plaquette) : S.image.Plaquette :=
  ⟨S.pointMap p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
def IsTorusLift (T : D.Torus → S.image.Torus) : Prop :=
  T ∘ D.proj = S.image.proj ∘ S.toFun
def torusMap (y : D.Torus) : S.image.Torus :=
  S.image.proj (S.toFun (TestFunctions.liftPoint (ℓ := PeriodicLattice.torusSide D.L D.m) y))
def torusInv : S.image.Torus → D.Torus := Function.invFun S.torusMap
def IsLinkImage (e : D.PeriodicLink) (e' : S.image.PeriodicLink) : Prop :=
  (e'.source : S.image.Torus) = S.torusMap e.source ∧
    (e'.target : S.image.Torus) = S.torusMap e.target
def torusLinkMap (e : D.PeriodicLink) : S.image.PeriodicLink :=
  Classical.epsilon (S.IsLinkImage e)
def torusPullback (U' : S.image.PeriodicLink → Matrices.ComplexMatrix2) :
    D.PeriodicLink → Matrices.ComplexMatrix2 :=
  fun e => U' (S.torusLinkMap e)
def IsFaceImage (p : D.TorusFace) (p' : S.image.TorusFace) : Prop :=
  p'.firstAxis = p.firstAxis ∧ p'.secondAxis = p.secondAxis ∧
    (p'.origin : S.image.Torus) = S.torusMap p.origin
instance : Nonempty S.image.TorusFace := ⟨⟨0, 0, 1, by decide⟩⟩
def torusFaceMap (p : D.TorusFace) : S.image.TorusFace :=
  Classical.epsilon (S.IsFaceImage p)
theorem toFun_halfInteger {c : AmbientSpace}
    (hc : ∀ μ, ∃ i : ℤ, c μ = D.mesh * ((i : ℝ) + 1 / 2)) (μ : Fin 4) :
    ∃ i : ℤ, S.toFun c μ = S.image.mesh * ((i : ℝ) + 1 / 2) := by
  obtain ⟨i, hi⟩ := hc μ
  obtain ⟨u, hu⟩ := S.shift_mem
  refine ⟨i - u μ, ?_⟩
  simp only [toFun, hi, hu μ, S.image_mesh, Int.cast_sub]
  ring
def gridImage (g : ReflectionGrid D) : ReflectionGrid S.image where
  q := g.q + S.power
  one_sub_K_le_q := by
    have hq := g.one_sub_K_le_q
    have hp := S.power_lt
    change 1 - ((((D.K : ℕ) - S.power : ℕ)) : ℤ) ≤ g.q + S.power
    omega
  origin := S.toFun g.origin
  origin_mem := S.toFun_halfInteger g.origin_mem
def conjTorus (r : D.Torus → D.Torus) : S.image.Torus → S.image.Torus :=
  S.torusMap ∘ r ∘ S.torusInv
def PreservesGridPoints : Prop :=
  S.toFun '' (D.gridPoints : Set AmbientSpace) = (S.image.gridPoints : Set AmbientSpace) ∧
    Function.Bijective S.linkMap ∧
    (∀ e : D.Link, e.IsPositivelyOriented ↔ (S.linkMap e).IsPositivelyOriented) ∧
    (∀ p : D.Plaquette,
      S.toFun '' (Subtype.val '' D.faceCorners p) =
        Subtype.val '' S.image.faceCorners (S.faceMap p)) ∧
    Function.Bijective S.faceMap ∧
    ∀ p : D.Plaquette, (S.faceMap p).center = S.toFun p.center
def PreservesTorus : Prop :=
  (∃! T : D.Torus → S.image.Torus, S.IsTorusLift T) ∧
    S.IsTorusLift S.torusMap ∧
    Function.Bijective S.torusMap ∧
    (∀ x y : D.Torus, TorusMetric.torusEuclidNorm (S.torusMap x - S.torusMap y) =
      S.scale * TorusMetric.torusEuclidNorm (x - y)) ∧
    S.torusMap '' (PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ) : Set D.Torus) =
      (PeriodicLattice.sublattice S.image.L S.image.m ((S.image.K : ℕ) : ℤ) :
        Set S.image.Torus) ∧
    (∀ e : D.PeriodicLink, S.IsLinkImage e (S.torusLinkMap e)) ∧
    Function.Bijective S.torusLinkMap ∧
    (∀ e : D.PeriodicLink, e.IsPositivelyOriented ↔ (S.torusLinkMap e).IsPositivelyOriented) ∧
    (∀ p : D.TorusFace, S.IsFaceImage p (S.torusFaceMap p)) ∧
    (∀ p : D.TorusFace,
      S.torusMap '' (Subtype.val '' p.vertices) =
        Subtype.val '' (S.torusFaceMap p).vertices) ∧
    Function.Bijective S.torusFaceMap ∧
    ∀ p : D.TorusFace, (S.torusFaceMap p).barycenter = S.torusMap p.barycenter
def PreservesExpect (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] :
    Prop :=
  ∀ F : (D.PeriodicLink → Matrices.ComplexMatrix2) → E,
    ReflectionPositivity.CutoffMirrors.IsBoundedBorel (fun U : D.torusFields => F U.1) →
      D.expect F = S.image.expect (F ∘ S.torusPullback)
def PreservesObservables (E : Type*) [AddCommMonoid E] [Module ℝ E] : Prop :=
  ∀ (f : D.Torus → E), ∀ U' ∈ S.image.torusFields,
    PeriodicLattice.smearedObservable f (S.torusPullback U') =
      PeriodicLattice.smearedObservable (f ∘ S.torusInv) U'
def SharpNormNonincreasing (E : Type*) [NormedAddCommGroup E] (f : D.Torus → E) : Prop :=
  TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus f → ∀ M : ℝ, 1 ≤ M →
    TestFunctions.sharpNormTorus M (f ∘ S.torusInv) ≤ TestFunctions.sharpNormTorus M f
def PreservesMeasures : Prop :=
  (∃ h : S.image.torusFields ≃ₜ D.torusFields,
      ∀ U', (h U' : D.PeriodicLink → Matrices.ComplexMatrix2) = S.torusPullback U'.1) ∧
    IsHomeomorph S.pullback ∧
    (∀ (U' : S.image.GaugeField) (p : D.Plaquette),
      InfiniteLattice.faceEnergy (S.pullback U') p =
        InfiniteLattice.faceEnergy U' (S.faceMap p)) ∧
    (∀ U' ∈ S.image.torusFields, ∀ p : D.TorusFace,
      PeriodicLattice.plaquetteCost (S.torusPullback U') p =
        PeriodicLattice.plaquetteCost U' (S.torusFaceMap p)) ∧
    S.PreservesExpect ℝ ∧ S.PreservesExpect ℂ ∧
    S.PreservesObservables ℝ ∧ S.PreservesObservables ℂ ∧
    (∀ f : D.Torus → ℝ, S.SharpNormNonincreasing ℝ f) ∧
    (∀ f : D.Torus → ℂ, (∀ x, (f x).im = 0) → S.SharpNormNonincreasing ℂ f) ∧
    D.partition = S.image.partition
def PreservesCellsAndGroup (g : ReflectionGrid D) : Prop :=
  (∀ k, S.toFun '' g.cell k = (S.gridImage g).cell k) ∧
    (∀ k, S.toFun '' interior (g.cell k) = interior ((S.gridImage g).cell k)) ∧
    (∀ k, S.toFun (g.cellCentre k) = (S.gridImage g).cellCentre k) ∧
    (fun P : Set AmbientSpace => S.toFun '' P) '' g.wallSet = (S.gridImage g).wallSet ∧
    (∃ φ : g.reflectionGroup ≃* (S.gridImage g).reflectionGroup, ∀ r : g.reflectionGroup,
      ((φ r : Equiv.Perm AmbientSpace) = S.toPerm * r.1 * S.toPerm⁻¹) ∧
        orientationSign (φ r).1 = orientationSign r.1)
def PreservesCellObservables (g : ReflectionGrid D) : Prop :=
  (∀ C ∈ g.cellSet,
      (fun F : D.GaugeField → ℂ => F ∘ S.pullback) '' ReflectionGrid.cellObservables (D := D) C =
        ReflectionGrid.cellObservables (D := S.image) (S.toFun '' C)) ∧
    ∀ C ∈ g.cellSet, ∀ C' ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) C,
      g.transportTo C C' F ∘ S.pullback =
        (S.gridImage g).transportTo (S.toFun '' C) (S.toFun '' C') (F ∘ S.pullback)
def PreservesGrid (g : ReflectionGrid D) : Prop :=
  S.PreservesCellsAndGroup g ∧ S.PreservesCellObservables g
def PreservesCellsAndGroupTorus (g : ReflectionGrid D) : Prop :=
  2 * (S.scale * g.cellSide) ≤ S.scale * PeriodicLattice.torusSide D.L D.m ∧
    (S.gridImage g).cellsAcross = g.cellsAcross ∧
    (S.gridImage g).cellNumber = g.cellNumber ∧
    (fun C : Set D.Torus => S.torusMap '' C) '' g.torusCellSet = (S.gridImage g).torusCellSet ∧
    BijOn S.conjTorus g.inducedTorusMaps (S.gridImage g).inducedTorusMaps ∧
    (∀ r ∈ g.inducedTorusMaps, ∀ s ∈ g.inducedTorusMaps,
      S.conjTorus (r ∘ s) = S.conjTorus r ∘ S.conjTorus s) ∧
    ∀ r ∈ g.inducedTorusMaps, (S.gridImage g).torusSign (S.conjTorus r) = g.torusSign r
def PreservesCellObservablesTorus (g : ReflectionGrid D) : Prop :=
  (∀ C ∈ g.torusCellSet,
      (fun F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ => F ∘ S.torusPullback) ''
          g.torusCellObservables C =
        (S.gridImage g).torusCellObservables (S.torusMap '' C)) ∧
    (∀ C ∈ g.torusCellSet, ∀ C' ∈ g.torusCellSet, ∀ F ∈ g.torusCellObservables C,
      ∀ U' ∈ S.image.torusFields,
        g.torusTransportTo C C' F (S.torusPullback U') =
          (S.gridImage g).torusTransportTo (S.torusMap '' C) (S.torusMap '' C')
            (F ∘ S.torusPullback) U') ∧
    (∀ C ∈ g.torusCellSet, ∀ F ∈ g.torusCellObservables C, ∀ U' ∈ S.image.torusFields,
      g.cellProduct C F (S.torusPullback U') =
        (S.gridImage g).cellProduct (S.torusMap '' C) (F ∘ S.torusPullback) U') ∧
    ∀ C ∈ g.torusCellSet, ∀ F ∈ g.torusCellObservables C,
      g.cellChessboardSeminorm C F =
        (S.gridImage g).cellChessboardSeminorm (S.torusMap '' C) (F ∘ S.torusPullback)
def PreservesGridTorus (g : ReflectionGrid D) : Prop :=
  S.PreservesCellsAndGroupTorus g ∧ S.PreservesCellObservablesTorus g
def PreservesSidesAndCentres : Prop :=
  (∀ l : ℝ, D.IsAdmissibleSide l →
    S.image.IsAdmissibleSide (S.scale * l) ∧
      ∀ g' : ReflectionGrid S.image, g'.cellSide = S.scale * l →
        ∃! G : Set (Set AmbientSpace), ∃ g : ReflectionGrid D,
          g.cellSide = l ∧ g.cellSet = G ∧ (S.gridImage g).cellSet = g'.cellSet) ∧
    (∀ c : AmbientSpace, (∀ μ, ∃ i : ℤ, c μ = D.mesh * ((i : ℝ) + 1 / 2)) →
      ∀ μ, ∃ i : ℤ, S.toFun c μ = S.image.mesh * ((i : ℝ) + 1 / 2))
def PreservesReflectionGrids : Prop :=
  S.PreservesSidesAndCentres ∧
    ∀ g : ReflectionGrid D, g.HasAdmissibleSide →
      (S.gridImage g).cellSide = S.scale * g.cellSide ∧
        (S.gridImage g).origin = S.toFun g.origin ∧
        S.PreservesGrid g ∧
        (2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m → S.PreservesGridTorus g)
end ScalingMap
end YangMills.Construction.MirrorGridsAllSides
end
