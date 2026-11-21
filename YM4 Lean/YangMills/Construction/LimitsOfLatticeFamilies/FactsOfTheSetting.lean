import YangMills.Construction.LimitsOfLatticeFamilies.IsometriesTranslationsAndEnlargedSupports
import YangMills.Construction.LimitsOfLatticeFamilies.ReferenceRadiusPriceAndEffectiveConstants
import YangMills.Construction.LimitsOfLatticeFamilies.TensorsOfSeparatedTuplesAndCentredFunctionals
import YangMills.Construction.LimitsOfLatticeFamilies.TranslationModulusInTheSharpNorm
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
namespace ModelSpace.SettingFacts
variable (s : Conventions.StandingParameters) (M : BlockScale s) (Y : ModelSpace)
def NormTranslationInvariantMetric : Prop :=
  (∀ u v : Y.Carrier s, ModelSpace.norm s Y (u + v) ≤ ModelSpace.norm s Y u + ModelSpace.norm s Y v) ∧
  (∀ u : Y.Carrier s, ModelSpace.norm s Y (-u) = ModelSpace.norm s Y u) ∧
  (∀ x y : Y.Carrier s, 0 ≤ ModelSpace.dist s Y x y) ∧
  (∀ x y : Y.Carrier s, ModelSpace.dist s Y x y = 0 ↔ x = y) ∧
  (∀ x y : Y.Carrier s, ModelSpace.dist s Y x y = ModelSpace.dist s Y y x) ∧
  (∀ x y w : Y.Carrier s, ModelSpace.dist s Y x y ≤ ModelSpace.dist s Y x w + ModelSpace.dist s Y w y) ∧
  ∀ x y a : Y.Carrier s, ModelSpace.dist s Y (x + a) (y + a) = ModelSpace.dist s Y x y
def ClosedBallsCompact : Prop :=
  ∀ (x : Y.Carrier s) (R : ℝ), 0 < R → IsCompactIn s Y (closedBall s Y x R)
def TorusCompactBoundedBySide : Prop :=
  (∀ u : torus.Carrier s, ∃ v : Fin 4 → ℝ, IsLiftOf s torus u v ∧
    ∀ μ, v μ ∈ Icc (-(s.side / 2)) (s.side / 2)) ∧
  (∀ u : torus.Carrier s, ModelSpace.norm s torus u ≤ s.side) ∧
  IsCompactIn s torus univ ∧
  ∀ (x : torus.Carrier s) (R : ℝ), s.side ≤ R → closedBall s torus x R = univ
def CompactSubsetsBounded : Prop :=
  ∀ K : Set (Y.Carrier s), IsCompactIn s Y K →
    (∃ r : ℝ, 0 < r ∧ K ⊆ ballAtBase s Y (ENNReal.ofReal r)) ∧
    ∃ (x : Y.Carrier s) (R : ℝ), 0 < R ∧ K ⊆ closedBall s Y x R
def EventuallyInFiniteConj : Prop :=
  ∀ J : Set ℕ, J.Infinite → ∀ (k : ℕ) (p : Fin k → ℕ → Prop),
    (∀ i, EventuallyIn J (p i)) → EventuallyIn J fun j => ∀ i, p i j
variable {s Y} in
def DifferAtOneIndex {n : ℕ} (g g' : FunTuple s Y n) : Prop :=
  ∃ i, g i ≠ g' i ∧ ∀ l, l ≠ i → g l = g' l
def InCommonProduct {n : ℕ} (V : Set (Y.Carrier s) → Set (Y.Carrier s → ℝ)) (r : ℝ≥0∞)
    (g g' : FunTuple s Y n) : Prop :=
  ∃ A : Fin n → Set (Y.Carrier s), (∀ l, A l ⊆ ballAtBase s Y r) ∧
    (∀ l k, l ≠ k → Disjoint (A l) (A k)) ∧ (∀ l, g l ∈ V (A l)) ∧ ∀ l, g' l ∈ V (A l)
def CommonProductAndZeroComponent : Prop :=
  ∀ n, 1 ≤ n → ∀ r : ℝ≥0∞, 0 < r →
    (∀ g ∈ sepTuplesIn s Y n r, ∀ g' ∈ sepTuplesIn s Y n r, DifferAtOneIndex g g' →
      InCommonProduct s Y (c1CompactSupp s Y) r g g') ∧
    (∀ Φ : TupleFunctional (sepTuplesIn s Y n r), IsMultilinearSep Φ →
      ∀ h ∈ sepTuplesIn s Y n r, ∀ i, h i = 0 → Φ.extend h = 0) ∧
    (∀ g ∈ lipSepTuplesIn s Y n r, ∀ g' ∈ lipSepTuplesIn s Y n r, DifferAtOneIndex g g' →
      InCommonProduct s Y (lipCompactSupp s Y) r g g') ∧
    ∀ Φ : TupleFunctional (lipSepTuplesIn s Y n r), IsMultilinearLip Φ →
      ∀ h ∈ lipSepTuplesIn s Y n r, ∀ i, h i = 0 → Φ.extend h = 0
def MinSeparationPos : Prop :=
  ∀ n, 2 ≤ n → ∀ f ∈ sepTuples s Y n,
    0 < minSeparation s Y f ∧
    (minSeparation s Y f = ⊤ ↔
      ∀ i k, (supportIn s Y (f i)).Nonempty → (supportIn s Y (f k)).Nonempty → i = k) ∧
    (minSeparation s Y f = ⊤ → (∃ i, f i = 0) ∧
      ∀ (a : Y.Carrier s) (r : ℝ≥0∞), 0 < r → ∀ Φ : TupleFunctional (sepTuplesIn s Y n r),
        IsMultilinearSep Φ → shiftTuple a f ∈ sepTuplesIn s Y n r →
          Φ.extend (shiftTuple a f) = 0)
def AtAdmissibleRadius (C : SeparationBound) (n : ℕ) (d R R' C' θ : ℝ) : Prop :=
  R' ∈ admissibleRadii s Y ∧ 0 ≤ C' ∧
  (R ∈ admissibleRadii s Y → C' = C.val n d R') ∧
  (R ∉ admissibleRadii s Y → C' = θ ^ n * C.val n d R') ∧
  (Y = euclidean → R' = R ∧ C' = C.val n d R)
def EffConstAdmissible : Prop :=
  refRadius s Y ∈ admissibleRadii s Y ∧ 1 ≤ costFactor M.1 Y ∧
  ∀ (C : SeparationBound) (n : ℕ), 2 ≤ n → ∀ d R : ℝ, 0 < d → 0 < R →
    AtAdmissibleRadius s Y C n d R (flatRadius s Y R) (effConst s Y M.1 C n d R)
      (costFactor M.1 Y) ∧
    ∀ r ∈ admissibleRadii s Y, ∀ θ : ℝ, 1 ≤ θ →
      AtAdmissibleRadius s Y C n d R (flatRadiusOf s Y r R)
        (effConstOf s Y r θ C n d R) θ
def TorusFactorFormula : Prop :=
  ∀ M : ℕ, costFactor M torus = 16 ^ 4 * (1 + 320 * Real.pi * M)
def SepTensorsBounded : Prop :=
  ∀ q, 1 ≤ q →
    (∀ F ∈ sepTensorsTop s Y q,
      ∃ r : ℝ, 0 < r ∧ F ∈ sepTensors s Y q (ENNReal.ofReal r)) ∧
    ∀ r r' : ℝ≥0∞, 0 < r → r ≤ r' → sepTensors s Y q r ≤ sepTensors s Y q r'
def ShiftIsometric : Prop :=
  ∀ a : Y.Carrier s,
    (∃ t : SpaceIsometry s Y, (∀ y, t y = y + a) ∧
      ∀ f : Y.Carrier s → ℝ, t.pushFun f = shift a f) ∧
    (∀ f ∈ c1CompactSupp s Y univ,
      shift a f ∈ c1CompactSupp s Y univ ∧
      supportIn s Y (shift a f) = shiftSet (supportIn s Y f) a ∧
      grad s Y (shift a f) = shift a (grad s Y f) ∧
      sharpNorm s M Y (shift a f) = sharpNorm s M Y f) ∧
    (∀ n, 1 ≤ n → ∀ f ∈ sepTuples s Y n, shiftTuple a f ∈ sepTuples s Y n) ∧
    ∀ K : Set (Y.Carrier s), IsCompactIn s Y K → IsCompactIn s Y (shiftSet K a)
def ShiftDifferenceBounds : Prop :=
  ∀ (f : c1CompactSupp s Y univ) (a b : Y.Carrier s),
    ENNReal.ofReal (TestFunctions.uniformNorm (shift a f.1 - shift b f.1)) ≤
      gradSup f * ((ModelSpace.norm s Y (a - b)).toNNReal : ℝ≥0∞) ∧
    ENNReal.ofReal (lipNumber s Y (shift a f.1 - shift b f.1)) ≤
      gradOscillation f (ModelSpace.norm s Y (a - b)).toNNReal ∧
    ENNReal.ofReal (sharpNorm s M Y (shift a f.1 - shift b f.1)) ≤
      sharpTranslationModulus M f (ModelSpace.norm s Y (a - b)).toNNReal
def ProjKernels : Prop :=
  {x | proj s euclidean x = 0} = {0} ∧
  {x | proj s torus x = 0} = {x | ∃ k : Fin 4 → ℤ, x = fun μ => s.side * k μ}
def ProjLiftProperties : Prop :=
  (∀ x x', proj s Y (x + x') = proj s Y x + proj s Y x') ∧
  Function.Surjective (proj s Y) ∧
  (∀ u : Y.Carrier s, ∃ v, IsMinimalLiftOf s Y u v) ∧
  (∀ x, ModelSpace.norm s Y (proj s Y x) ≤ TorusMetric.euclidNormVec x) ∧
  (∀ x x', ModelSpace.norm s Y (proj s Y x - proj s Y x') ≤
    TorusMetric.euclidNormVec (x - x')) ∧
  ∀ x, (Y = euclidean ∨ Y = torus ∧ TorusMetric.euclidNormVec x < s.side / 2) →
    ModelSpace.norm s Y (proj s Y x) = TorusMetric.euclidNormVec x
def IsC1IffLift : Prop :=
  (∀ f : Y.Carrier s → ℝ, IsC1 s Y f ↔ TestFunctions.IsC1R4 (f ∘ proj s Y)) ∧
  (∀ f : Y.Carrier s → ℝ, IsC1 s Y f →
    grad s Y f ∘ proj s Y = gradR4 (f ∘ proj s Y) ∧
    ∀ g : Y.Carrier s → Fin 4 → ℝ,
      g ∘ proj s Y = gradR4 (f ∘ proj s Y) → g = grad s Y f) ∧
  ∀ f g : Y.Carrier s → ℝ, IsC1 s Y f → IsC1 s Y g →
    (∀ α β : ℝ, IsC1 s Y (α • f + β • g)) ∧ IsC1 s Y (f * g)
def C1CompactSuppLipschitz : Prop :=
  (∀ f : c1CompactSupp s Y univ, gradSup f < ⊤ ∧
    (∀ x y, |f.1 x - f.1 y| ≤ (gradSup f).toReal * ModelSpace.dist s Y x y) ∧
    IsLipschitzReal s Y f.1 ∧
    lipNumber s Y f.1 ≤ (gradSup f).toReal) ∧
  ∀ A : Set (Y.Carrier s), c1CompactSupp s Y A ⊆ lipCompactSupp s Y A
def TorusSupportCompact : Prop :=
  (∀ f : torus.Carrier s → ℝ, IsCompactIn s torus (supportIn s torus f)) ∧
  ∀ f : torus.Carrier s → ℝ, IsC1 s torus f → f ∈ c1CompactSupp s torus univ
def IsSeminormOnSet (p : (Y.Carrier s → ℝ) → ℝ) (V : Set (Y.Carrier s → ℝ)) : Prop :=
  (∀ h ∈ V, 0 ≤ p h) ∧ (∀ (α : ℝ), ∀ h ∈ V, p (α • h) = |α| * p h) ∧
  ∀ h ∈ V, ∀ h' ∈ V, p (h + h') ≤ p h + p h'
def SubmodulesAndSharpSeminorm : Prop :=
  (∀ A : Set (Y.Carrier s), ∃ V : Submodule ℝ (Y.Carrier s → ℝ), (V : Set _) = lipCompactSupp s Y A) ∧
  (∀ A : Set (Y.Carrier s), ∃ V : Submodule ℝ (Y.Carrier s → ℝ), (V : Set _) = c1CompactSupp s Y A) ∧
  (∀ h ∈ lipCompactSupp s Y univ, TestFunctions.IsBoundedFun h ∧ IsLipschitzReal s Y h) ∧
  IsSeminormOnSet s Y (sharpNorm s M Y) (lipCompactSupp s Y univ)
def ProductPermRestrictClosed : Prop :=
  ∀ n, 1 ≤ n → ∀ r : ℝ≥0∞, 0 < r →
    (∀ A : Fin n → Set (Y.Carrier s), (∀ l, A l ⊆ ballAtBase s Y r) →
      (∀ l k, l ≠ k → Disjoint (A l) (A k)) →
        (∀ h : FunTuple s Y n, (∀ l, h l ∈ c1CompactSupp s Y (A l)) → h ∈ sepTuplesIn s Y n r) ∧
        ∀ h : FunTuple s Y n, (∀ l, h l ∈ lipCompactSupp s Y (A l)) →
          h ∈ lipSepTuplesIn s Y n r) ∧
    (∀ h ∈ sepTuplesIn s Y n r,
      (∀ σ : Equiv.Perm (Fin n), (fun l => h (σ l)) ∈ sepTuplesIn s Y n r) ∧
      ∀ B : Finset (Fin n), B.Nonempty → restrictTuple h B ∈ sepTuplesIn s Y B.card r) ∧
    ∀ h ∈ lipSepTuplesIn s Y n r,
      (∀ σ : Equiv.Perm (Fin n), (fun l => h (σ l)) ∈ lipSepTuplesIn s Y n r) ∧
      ∀ B : Finset (Fin n), B.Nonempty → restrictTuple h B ∈ lipSepTuplesIn s Y B.card r
def CentredSumWellDefined : Prop :=
  ∀ r : ℝ≥0∞, 0 < r →
    (∀ q, ∀ h ∈ sepTuplesIn s Y q r, ∀ P ∈ SetPartition.nonSingletonPartitions q,
      ∀ B ∈ P.parts, 2 ≤ B.card ∧ restrictTuple h B ∈ sepTuplesIn s Y B.card r) ∧
    ∀ Φ : FunctionalSeq s Y r, IsMultilinearSeq Φ →
      (∀ h : sepTuplesIn s Y 0 r, centredSum Φ 0 h = 1) ∧
      ∀ h : sepTuplesIn s Y 1 r, centredSum Φ 1 h = 0
def HierarchyOnSepTuples : Prop :=
  ∀ H : HierarchySequence s Y, ∀ n, 2 ≤ n →
    (∀ j ∈ H.indices,
      sepTuplesIn s Y n (H.rad j) ⊆ lipSepTuplesIn s Y n (H.rad j) ∧
      (H.restrictSeq j n).IsSymm ∧
      IsMultilinearSep (H.restrictSeq j n) ∧
      ∀ d R : ℝ, 0 < d → 0 < R → ∀ f ∈ lipTuplesApart s Y n d R,
        (∀ i, supportIn s Y (f i) ⊆ ballAtBase s Y (H.rad j)) →
          f ∈ lipSepTuplesIn s Y n (H.rad j)) ∧
    (∀ K : Set (Y.Carrier s), IsCompactIn s Y K →
      EventuallyIn H.indices fun j => K ⊆ ballAtBase s Y (H.rad j)) ∧
    ∀ f ∈ sepTuples s Y n,
      EventuallyIn H.indices fun j => f ∈ sepTuplesIn s Y n (H.rad j) ∧ j ∈ H.definedAt f
end ModelSpace.SettingFacts
open ModelSpace ModelSpace.SettingFacts
structure SettingFactsHold (s : Conventions.StandingParameters) (M : BlockScale s) (Y : ModelSpace) :
    Prop where
  dist_invariant : NormTranslationInvariantMetric s Y
  closedBall_compact : ClosedBallsCompact s Y
  torus_compact : TorusCompactBoundedBySide s
  compact_bounded : CompactSubsetsBounded s Y
  eventually_conj : EventuallyInFiniteConj
  commonProduct : CommonProductAndZeroComponent s Y
  minSeparation_pos : MinSeparationPos s Y
  effConst_admissible : EffConstAdmissible s M Y
  torusFactor_eq : TorusFactorFormula
  sepTensors_bounded : SepTensorsBounded s Y
  shift_isometric : ShiftIsometric s M Y
  shift_diff : ShiftDifferenceBounds s M Y
  proj_kernels : ProjKernels s
  proj_lifts : ProjLiftProperties s Y
  isC1_iff : IsC1IffLift s Y
  c1_lipschitz : C1CompactSuppLipschitz s Y
  torus_support : TorusSupportCompact s
  submodules : SubmodulesAndSharpSeminorm s M Y
  product_closed : ProductPermRestrictClosed s Y
  centred_defined : CentredSumWellDefined s Y
  hierarchy_sepTuples : HierarchyOnSepTuples s Y
def SettingFactsHold.statement : Prop :=
  ∀ (s : Conventions.StandingParameters) (M : BlockScale s) (Y : ModelSpace), SettingFactsHold s M Y
end YangMills.Construction.LatticeLimits
end
