import YangMills.Construction.PassageToTheLimit.SeparatedTuplesMultilinearFunctionalsCentredFunctionalTensors
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflections
import YangMills.Construction.ReflectionPositivity.SupportsTranslationsSeparationAndTransportOfTuples
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.Sides
variable (D : MirrorData)
theorem euclidReflect_eq_reflectR4 (μ : Fin 4) (c : ℝ) :
    euclidReflect μ c = LimitSpaces.reflectR4 μ c := by
  funext y ν
  by_cases h : ν = μ
  · subst h
    simp [euclidReflect, LimitSpaces.reflectR4, LimitSpaces.stdBasisVec,
      PeriodicLattice.coordVec]
  · simp [euclidReflect, LimitSpaces.reflectR4, LimitSpaces.stdBasisVec,
      PeriodicLattice.coordVec, h]
theorem reflect_euclidean (μ : Fin 4) (c : ℝ) :
    CoordMirror.reflect D ⟨μ, c⟩ .euclidean =
      LimitSpaces.Ambient.euclidean.reflect D.toStandingParameters μ c := by
  funext y
  exact (congrFun (euclidReflect_eq_reflectR4 μ c) y).trans
    (LimitSpaces.Ambient.reflect_euclidean D.toStandingParameters μ c y).symm
theorem reflect_torus (μ : Fin 4) (c : ℝ) :
    CoordMirror.reflect D ⟨μ, c⟩ .torus =
      LimitSpaces.Ambient.periodic.reflect D.toStandingParameters μ c := by
  have hθ : D.Induces (euclidReflect μ c)
      (LimitSpaces.Ambient.periodic.reflect D.toStandingParameters μ c) := by
    rw [euclidReflect_eq_reflectR4]
    exact LimitSpaces.Ambient.periodic.reflect_comp_proj D.toStandingParameters μ c
  have hε : D.Induces (euclidReflect μ c) (D.descended (euclidReflect μ c)) :=
    Classical.epsilon_spec (p := D.Induces (euclidReflect μ c)) ⟨_, hθ⟩
  funext x
  obtain ⟨y, rfl⟩ := LimitSpaces.Ambient.periodic.proj_surjective D.toStandingParameters x
  exact (congrFun hε y).trans (congrFun hθ y).symm
variable (P : LimitSpaces.Ambient)
def hyperplane : (P : LimitSpaces.Ambient) → Fin 4 → ℝ → Set (P.Carrier D.toStandingParameters)
  | .euclidean, μ, c => CoordMirror.carrier D ⟨μ, c⟩ .euclidean
  | .periodic, μ, c => CoordMirror.carrier D ⟨μ, c⟩ .torus
def openHalf : (P : LimitSpaces.Ambient) → Fin 4 → ℝ → Set (P.Carrier D.toStandingParameters)
  | .euclidean, μ, c => CoordMirror.upperSide D ⟨μ, c⟩ .euclidean
  | .periodic, μ, c => CoordMirror.upperSide D ⟨μ, c⟩ .torus
def distToHyperplane (μ : Fin 4) (c : ℝ) (x : P.Carrier D.toStandingParameters) : ℝ≥0∞ :=
  P.infSetDist D.toStandingParameters {x} (hyperplane D P μ c)
def IsLipschitzMap {𝕜 : Type} [RCLike 𝕜] (f : P.Carrier D.toStandingParameters → 𝕜) : Prop :=
  TestFunctions.IsLipschitzFor (P.pointDist D.toStandingParameters) f
theorem isLipschitzMap_iff_isLip (f : P.Carrier D.toStandingParameters → ℝ) :
    IsLipschitzMap D P f ↔ P.IsLip D.toStandingParameters f := by
  cases P <;> exact Iff.rfl
def MetricAndSymmetries (μ : Fin 4) (c : ℝ) : Prop :=
  FamilyTopology.IsMetricFunction (P.pointDist D.toStandingParameters) ∧
  (∀ x y : Fin 4 → ℝ,
    LimitSpaces.Ambient.periodic.pointDist D.toStandingParameters
        (LimitSpaces.Ambient.periodic.proj D.toStandingParameters x)
        (LimitSpaces.Ambient.periodic.proj D.toStandingParameters y) ≤
      TorusMetric.euclidNormVec (x - y)) ∧
  (∀ v : P.Carrier D.toStandingParameters,
    LimitSpaces.AmbientMetric.IsDistPreserving D.toStandingParameters P fun x => x + v) ∧
  LimitSpaces.AmbientMetric.IsDistPreserving D.toStandingParameters P
    (P.reflect D.toStandingParameters μ c) ∧
  P.reflect D.toStandingParameters μ c ∘ P.reflect D.toStandingParameters μ c = id ∧
  (∀ (Z : Type) [Zero Z] (f : P.Carrier D.toStandingParameters → Z)
      (v : P.Carrier D.toStandingParameters),
    P.closedSupport D.toStandingParameters (P.reflectFun D.toStandingParameters μ c f) =
        P.reflect D.toStandingParameters μ c '' P.closedSupport D.toStandingParameters f ∧
      P.closedSupport D.toStandingParameters (P.translateFun D.toStandingParameters v f) =
        P.translateSet D.toStandingParameters (P.closedSupport D.toStandingParameters f) v) ∧
  (∀ (𝕜 : Type) [RCLike 𝕜] (f : P.Carrier D.toStandingParameters → 𝕜), IsLipschitzMap D P f →
    IsLipschitzMap D P (P.reflectFun D.toStandingParameters μ c f)) ∧
  ∀ f ∈ P.c1Compact D.toStandingParameters,
    P.reflectFun D.toStandingParameters μ c f ∈ P.c1Compact D.toStandingParameters ∧
    (∀ v : P.Carrier D.toStandingParameters,
      P.translateFun D.toStandingParameters v f ∈ P.c1Compact D.toStandingParameters) ∧
    P.IsLip D.toStandingParameters f
def EuclidDistToHyperplane (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ x : Fin 4 → ℝ, distToHyperplane D .euclidean μ c x = ENNReal.ofReal |x μ - c|
def TorusDistToHyperplane (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ x : Fin 4 → ℝ,
    distToHyperplane D .periodic μ c (LimitSpaces.Ambient.periodic.proj D.toStandingParameters x) =
        LimitSpaces.realInfDist (x μ)
          (translateSet (LimitSpaces.multiplesOf (D.side / 2)) c) ∧
      (0 < x μ - c → x μ - c < D.side / 2 →
        distToHyperplane D .periodic μ c
            (LimitSpaces.Ambient.periodic.proj D.toStandingParameters x) =
          ENNReal.ofReal (min (x μ - c) (D.side / 2 - (x μ - c))))
def OpenHalfOffHyperplane (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ x ∈ openHalf D P μ c, 0 < distToHyperplane D P μ c x
def ReflectedPointsFar (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ x ∈ openHalf D P μ c, ∀ y ∈ openHalf D P μ c,
    distToHyperplane D P μ c x + distToHyperplane D P μ c y ≤
      ENNReal.ofReal (P.pointDist D.toStandingParameters x (P.reflect D.toStandingParameters μ c y))
def CompactInOpenHalfStable (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ K : Set (P.Carrier D.toStandingParameters), P.IsCompactSubset D.toStandingParameters K →
    K ⊆ openHalf D P μ c →
      0 < P.infSetDist D.toStandingParameters K (hyperplane D P μ c) ∧
      ∀ c' : ℝ, ENNReal.ofReal |c' - c| < P.infSetDist D.toStandingParameters K (hyperplane D P μ c) →
        K ⊆ openHalf D P μ c'
def CompactInOpenHalfLowerLevels (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ K : Set (LimitSpaces.Ambient.euclidean.Carrier D.toStandingParameters),
    LimitSpaces.Ambient.euclidean.IsCompactSubset D.toStandingParameters K →
    K ⊆ openHalf D .euclidean μ c →
      ∀ c' : ℝ, c' ≤ c → K ⊆ openHalf D .euclidean μ c'
def IsSepLipList (X : List (P.Carrier D.toStandingParameters → ℝ)) : Prop :=
  P.IsSepLipTuple D.toStandingParameters Set.univ X.get
def GapsPositive : Prop :=
  (∀ A B : Set (P.Carrier D.toStandingParameters), P.IsCompactSubset D.toStandingParameters A →
    P.IsCompactSubset D.toStandingParameters B → Disjoint A B →
      P.PositivelySeparated D.toStandingParameters A B) ∧
  ∀ X : List (P.Carrier D.toStandingParameters → ℝ), IsSepLipList D P X →
    0 < P.listGap D.toStandingParameters X
def ReflectAppendSeparated (E : Ambient) (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ X Y : Ambient.FnList D E,
    X ∈ Ambient.separatedWithin D E (CoordMirror.upperSide D ⟨μ, c⟩ E) →
    Y ∈ Ambient.separatedWithin D E (CoordMirror.upperSide D ⟨μ, c⟩ E) →
      CoordMirror.reflectAppend D ⟨μ, c⟩ E X Y ∈ Ambient.separatedAll D E
def ReflectAppendSepLip (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ X Y : List (P.Carrier D.toStandingParameters → ℝ),
    IsSepLipList D P X → IsSepLipList D P Y →
    (∀ f ∈ X, P.SupportedWithin D.toStandingParameters (openHalf D P μ c) f) →
    (∀ f ∈ Y, P.SupportedWithin D.toStandingParameters (openHalf D P μ c) f) →
      IsSepLipList D P (X.map (P.reflectFun D.toStandingParameters μ c) ++ Y)
def TranslateOpenHalf (μ : Fin 4) (c : ℝ) : Prop :=
  ∀ t : ℝ,
    P.translateSetVec D.toStandingParameters (openHalf D P μ c)
        (t • LimitSpaces.stdBasisVec μ) =
      openHalf D P μ (c + t)
def HyperplaneSidesClaim : Prop :=
  ∀ (D : MirrorData) (μ : Fin 4) (c : ℝ),
    (∀ P : LimitSpaces.Ambient,
      MetricAndSymmetries D P μ c ∧
      OpenHalfOffHyperplane D P μ c ∧
      ReflectedPointsFar D P μ c ∧
      CompactInOpenHalfStable D P μ c ∧
      GapsPositive D P ∧
      ReflectAppendSepLip D P μ c ∧
      TranslateOpenHalf D P μ c) ∧
    EuclidDistToHyperplane D μ c ∧
    TorusDistToHyperplane D μ c ∧
    CompactInOpenHalfLowerLevels D μ c ∧
    ∀ E : Ambient, ReflectAppendSeparated D E μ c
end YangMills.Construction.ReflectionPositivity.AxisMirror.Sides
end
