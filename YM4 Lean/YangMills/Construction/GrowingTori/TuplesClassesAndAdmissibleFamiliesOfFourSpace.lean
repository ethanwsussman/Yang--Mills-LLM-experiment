import YangMills.Construction.SourcesAndGluing.SeparatedLipschitzTuplesAndTheirClasses
import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriLimits
abbrev RealFn : Type := (Fin 4 → ℝ) → ℝ
section Supports
variable {N : ℕ} {Z : Type*} [Zero Z]
def fnSupport (f : (Fin N → ℝ) → Z) : Set (Fin N → ℝ) := closure {x | f x ≠ 0}
def SupportedIn (f : (Fin N → ℝ) → Z) (A : Set (Fin N → ℝ)) : Prop :=
  IsCompact (fnSupport f) ∧ fnSupport f ⊆ A
end Supports
def infDist (S T : Set (Fin 4 → ℝ)) : ℝ≥0∞ := TestFunctions.setDistR4 S T
theorem infDist_empty_right (S : Set (Fin 4 → ℝ)) : infDist S ∅ = ∞ := by
  simp [infDist, TestFunctions.setDistR4]
def PosSeparated (S T : Set (Fin 4 → ℝ)) : Prop := infDist S T ≠ 0
def ptInfDist (x : Fin 4 → ℝ) (S : Set (Fin 4 → ℝ)) : ℝ≥0∞ := infDist {x} S
abbrev LipschitzR4 (f : RealFn) : Prop :=
  TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f
abbrev lipConst (f : RealFn) : ℝ :=
  TestFunctions.bestLipschitzConstant TestFunctions.euclidDistR4 f
def IsSepLipTuple {n : ℕ} (f : Fin n → RealFn) : Prop :=
  (∀ i, LipschitzR4 (f i)) ∧ (∀ i, IsCompact (fnSupport (f i))) ∧
    ∀ i j, i ≠ j → Disjoint (fnSupport (f i)) (fnSupport (f j))
def SuppsWithin {n : ℕ} (f : Fin n → RealFn) (U : Set (Fin 4 → ℝ)) : Prop :=
  ∀ i, fnSupport (f i) ⊆ U
def sepTuplesR4 (s : Conventions.StandingParameters) (n : ℕ) : Set (Fin n → RealFn) :=
  AmbientPoints.separatedTuples s .euclidean n
theorem mem_sepTuplesR4_iff (s : Conventions.StandingParameters) {n : ℕ} (f : Fin n → RealFn) :
    f ∈ sepTuplesR4 s n ↔
      (∀ i, ContDiff ℝ 1 (f i)) ∧ (∀ i, IsCompact (fnSupport (f i))) ∧
        ∀ i j, i ≠ j → Disjoint (fnSupport (f i)) (fnSupport (f j)) := by
  have hSupp : ∀ g : RealFn,
      @tsupport (AmbientPoints.Pt s .euclidean) ℝ _ _ g = fnSupport g := fun g =>
    AmbientPoints.tsupport_eq_of_r4 g
  have hId : ∀ S : Set (AmbientPoints.Pt s .euclidean),
      (AmbientPoints.homeomorphR4 s) '' S = S := fun S => by
    ext x
    exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hCpt : ∀ S : Set (AmbientPoints.Pt s .euclidean),
      IsCompact S ↔ IsCompact (X := Fin 4 → ℝ) S := fun S => by
    have hImg := (AmbientPoints.homeomorphR4 s).isCompact_image (s := S)
    rw [hId] at hImg
    exact hImg.symm
  constructor
  · rintro ⟨hC1, hDisj⟩
    refine ⟨fun i => (hC1 i).1, fun i => ?_, fun i j hij => ?_⟩
    · have hK := (hCpt _).1 (hC1 i).2
      rwa [hSupp] at hK
    · have hD : Disjoint (@tsupport (AmbientPoints.Pt s .euclidean) ℝ _ _ (f i))
          (@tsupport (AmbientPoints.Pt s .euclidean) ℝ _ _ (f j)) := hDisj hij
      rwa [hSupp, hSupp] at hD
  · rintro ⟨hC1, hK, hDisj⟩
    refine ⟨fun i => ⟨hC1 i, ?_⟩, fun i j hij => ?_⟩
    · refine (hCpt _).2 ?_
      rw [hSupp]
      exact hK i
    · change Disjoint (@tsupport (AmbientPoints.Pt s .euclidean) ℝ _ _ (f i))
        (@tsupport (AmbientPoints.Pt s .euclidean) ℝ _ _ (f j))
      rw [hSupp, hSupp]
      exact hDisj i j hij
abbrev subfamily {X : Type*} {n : ℕ} (f : Fin n → X) (B : Finset (Fin n)) : Fin B.card → X :=
  AmbientPoints.restrictTuple f B
def minSuppGap {n : ℕ} (_hn : 2 ≤ n) (f : Fin n → RealFn) (_hf : IsSepLipTuple f) : ℝ≥0∞ :=
  ⨅ i, ⨅ j, ⨅ _ : i ≠ j, infDist (fnSupport (f i)) (fnSupport (f j))
abbrev ballOrigin (ρ : ℝ) : Set (Fin 4 → ℝ) := SourcesAndGluing.ballR4 ρ
abbrev closedBallR4 (x : Fin 4 → ℝ) (R : ℝ) : Set (Fin 4 → ℝ) :=
  SourcesAndGluing.closedBallAt x R
def BallSupported {n : ℕ} (R : ℝ) (_hR : 0 < R) (f : Fin n → RealFn) : Prop :=
  ∀ i, ∃ x, fnSupport (f i) ⊆ closedBallR4 x R
def lipTuples (n : ℕ) (hn : 2 ≤ n) (d R : ℝ) (_hd : 0 < d) (hR : 0 < R) :
    Set (Fin n → RealFn) :=
  {f | ∃ hf : IsSepLipTuple f, BallSupported R hR f ∧ ENNReal.ofReal d ≤ minSuppGap hn f hf}
def lipTuplesTorus (G : SourcesAndGluing.GluingSetup) (m : ℕ+) (n : ℕ) (hn : 2 ≤ n) (d R : ℝ)
    (_hd : 0 < d) (_hR : 0 < R) (_hRm : R < (G.L : ℝ) ^ (m : ℕ) / 2) :
    Set (Fin n → G.torusAt m → ℝ) :=
  (SourcesAndGluing.Ambient.torus m).lipClass G ⟨n, by omega⟩ d R
def AdmissibleSets {q : ℕ} (_hq : 1 ≤ q) (d R : ℝ) (_hd : 0 < d) (_hR : 0 < R)
    (S : Fin q → Set (Fin 4 → ℝ)) : Prop :=
  (∀ l, ∃ x, S l ⊆ closedBallR4 x R) ∧
    ∀ l j, l ≠ j → ENNReal.ofReal d ≤ infDist (S l) (S j)
def c1SuppIn (s : Conventions.StandingParameters) (S : Set (Fin 4 → ℝ)) : Set RealFn :=
  AmbientPoints.c1CompactlySupportedIn (s := s) (E := .euclidean) S
theorem mem_c1SuppIn_iff (s : Conventions.StandingParameters) (S : Set (Fin 4 → ℝ))
    (f : RealFn) :
    f ∈ c1SuppIn s S ↔ ContDiff ℝ 1 f ∧ SupportedIn f S := by
  have hSupp : @tsupport (AmbientPoints.Pt s .euclidean) ℝ _ _ f = fnSupport f :=
    AmbientPoints.tsupport_eq_of_r4 f
  have hId : ∀ Z : Set (AmbientPoints.Pt s .euclidean),
      (AmbientPoints.homeomorphR4 s) '' Z = Z := fun Z => by
    ext x
    exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hCpt : ∀ Z : Set (AmbientPoints.Pt s .euclidean),
      IsCompact Z ↔ IsCompact (X := Fin 4 → ℝ) Z := fun Z => by
    have hImg := (AmbientPoints.homeomorphR4 s).isCompact_image (s := Z)
    rw [hId] at hImg
    exact hImg.symm
  constructor
  · rintro ⟨hC1, hK, hSub⟩
    refine ⟨hC1, ?_, ?_⟩
    · have hK' := (hCpt _).1 hK
      rwa [hSupp] at hK'
    · rwa [hSupp] at hSub
  · rintro ⟨hC1, hK, hSub⟩
    refine ⟨hC1, (hCpt _).2 ?_, ?_⟩
    · rw [hSupp]
      exact hK
    · rw [hSupp]
      exact hSub
def lipSuppIn (S : Set (Fin 4 → ℝ)) : Set RealFn :=
  {f | LipschitzR4 f ∧ SupportedIn f S}
def closedThick (S : Set (Fin 4 → ℝ)) (_hS : IsCompact S) (η : ℝ) (_hη : 0 < η) :
    Set (Fin 4 → ℝ) :=
  {x | ptInfDist x S ≤ ENNReal.ofReal η}
end YangMills.Construction.ToriLimits
end
