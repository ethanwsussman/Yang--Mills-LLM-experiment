import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.AxialGauges
import YangMills.Construction.Lattice.GaugeFixingFactor
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Matrices
namespace Tower
abbrev sideSet (L : ℕ) : Set ℝ := PeriodicLattice.torusSides L
def meshAt (L k j : ℕ) : ℝ := (L : ℝ) ^ ((j : ℤ) - (k : ℤ))
def finestMesh (L k : ℕ) : ℝ := meshAt L k 0
theorem meshSize_levelDepth (L k j : ℕ) :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j) = meshAt L k j := by
  simp [PeriodicLattice.meshSize, meshAt, PeriodicLattice.levelDepth]
section FiniteSide
variable {L n k : ℕ}
abbrev Vertex (L n k j : ℕ) : Type := PeriodicLattice.SiteAtLevel L n k j
abbrev Edge (L n k j : ℕ) : Type := PeriodicLattice.BondAtLevel L n k j
abbrev Face (L n k j : ℕ) : Type := PeriodicLattice.PlaquetteAtLevel L n k j
abbrev fieldSpace (L n k j : ℕ) : Set (Edge L n k j → ComplexMatrix2) :=
  PeriodicLattice.gaugeFieldsAtLevel L n k j
def gaugeGroupAt (L n k j : ℕ) : Set (Vertex L n k j → ComplexMatrix2) :=
  {u | PeriodicLattice.IsGaugeMap PeriodicLattice.compactGaugeGroup u}
def smoothingStep (L n k j : ℕ) :
    (Edge L n k j → ComplexMatrix2) → Edge L n k (j + 1) → ComplexMatrix2 :=
  PeriodicLattice.blockAverageStep (Averaging.smoothingRadius L) j
def smoothingIter (L n k j : ℕ) :
    (Edge L n k 0 → ComplexMatrix2) → Edge L n k j → ComplexMatrix2 :=
  PeriodicLattice.blockFieldAtLevel (Averaging.smoothingRadius L) j
def linearSmoothing (L n k j : ℕ) :
    (Edge L n k j → ComplexMatrix2) → Edge L n k (j + 1) → ComplexMatrix2 :=
  PeriodicLattice.scaledLinearBlockStep j
def axialFunction (L n k j : ℕ) (V : Edge L n k j → ComplexMatrix2) : ℝ :=
  PeriodicLattice.axialGaugeFunction k j univ V
def IsAxialGaugeAt (L n k j : ℕ) (V : Edge L n k j → ComplexMatrix2) : Prop :=
  PeriodicLattice.IsBlockAxialGauge k j univ V
def plaquetteAction (L n k : ℕ) (U : Edge L n k 0 → ComplexMatrix2) : ℝ :=
  PeriodicLattice.wilsonAction U
def IsDistancePreserving (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n) :
    Prop :=
  ∀ p q, TorusMetric.torusEuclidNorm (f p - f q) = TorusMetric.torusEuclidNorm (p - q)
def MapsSublatticeOnto (k j : ℕ)
    (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n) : Prop :=
  f '' (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) :
      Set (PeriodicLattice.FourTorus L n)) =
    PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j)
variable {j : ℕ}
def vertexImage (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (v : Vertex L n k j) : Vertex L n k j :=
  Classical.epsilon fun w => (w : PeriodicLattice.FourTorus L n) = f v
def vertexPreimage (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (v : Vertex L n k j) : Vertex L n k j :=
  Classical.epsilon fun w => f w = v
def edgeImage (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (e : Edge L n k j) : Edge L n k j :=
  Classical.epsilon fun e' => e'.source = vertexImage f e.source ∧ e'.target = vertexImage f e.target
def edgePreimage (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (e : Edge L n k j) : Edge L n k j :=
  Classical.epsilon fun e' =>
    e'.source = vertexPreimage f e.source ∧ e'.target = vertexPreimage f e.target
def pathImage (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (γ : List (Edge L n k j)) : List (Edge L n k j) :=
  γ.map (edgeImage f)
def pushField (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (V : Edge L n k j → ComplexMatrix2) : Edge L n k j → ComplexMatrix2 :=
  fun e => V (edgePreimage f e)
def pushSiteFunction {E : Type*} (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n)
    (g : Vertex L n k j → E) : Vertex L n k j → E :=
  fun v => g (vertexPreimage f v)
end FiniteSide
def EventuallyNearIdentity {ι : Type*} (D : Set (ι → ComplexMatrix2))
    (P : (ι → ComplexMatrix2) → Prop) : Prop :=
  ∀ᶠ V in 𝓝[D] (fun _ => (1 : ComplexMatrix2)), P V
namespace FullSpace
open InfiniteLattice (AmbientSpace)
abbrev Vertex (L k j : ℕ) : Type := InfiniteLattice.LatticePoint (meshAt L k j)
abbrev Edge (L k j : ℕ) : Type := InfiniteLattice.Link (meshAt L k j)
abbrev Face (L k j : ℕ) : Type := InfiniteLattice.ElementaryPlaquette (meshAt L k j)
section OneLattice
variable {a : ℝ}
instance : Nonempty (InfiniteLattice.Link a) :=
  ⟨InfiniteLattice.Link.forwardFrom 0 0⟩
def backwardLink (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) : InfiniteLattice.Link a :=
  ⟨x, x - InfiniteLattice.axisStep a μ, μ, Or.inr (by abel)⟩
def faceCorners (p : InfiniteLattice.ElementaryPlaquette a) : Set (InfiniteLattice.LatticePoint a) :=
  {p.corner, p.corner + InfiniteLattice.axisStep a p.lowAxis,
    p.corner + InfiniteLattice.axisStep a p.lowAxis + InfiniteLattice.axisStep a p.highAxis,
    p.corner + InfiniteLattice.axisStep a p.highAxis}
def faceBoundary (p : InfiniteLattice.ElementaryPlaquette a) : List (InfiniteLattice.Link a) :=
  [InfiniteLattice.Link.forwardFrom p.corner p.lowAxis,
    InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.lowAxis) p.highAxis,
    (InfiniteLattice.Link.forwardFrom (p.corner + InfiniteLattice.axisStep a p.highAxis)
      p.lowAxis).opposite,
    (InfiniteLattice.Link.forwardFrom p.corner p.highAxis).opposite]
def linkHolonomy (U : InfiniteLattice.Link a → ComplexMatrix2) (γ : List (InfiniteLattice.Link a)) :
    ComplexMatrix2 :=
  (γ.map U).prod
def faceVariable (U : InfiniteLattice.Link a → ComplexMatrix2)
    (p : InfiniteLattice.ElementaryPlaquette a) : ComplexMatrix2 :=
  linkHolonomy U (faceBoundary p)
def IsLinkPath (γ : List (InfiniteLattice.Link a)) : Prop :=
  γ.IsChain fun e e' => e.terminal = e'.initial
def sumAlong (A : InfiniteLattice.Link a → ComplexMatrix2) (γ : List (InfiniteLattice.Link a)) :
    ComplexMatrix2 :=
  (γ.map A).sum
def forwardSteps (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    ℕ → List (InfiniteLattice.Link a)
  | 0 => []
  | m + 1 => InfiniteLattice.Link.forwardFrom x μ ::
      forwardSteps (x + InfiniteLattice.axisStep a μ) μ m
def backwardSteps (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) :
    ℕ → List (InfiniteLattice.Link a)
  | 0 => []
  | m + 1 => backwardLink x μ :: backwardSteps (x - InfiniteLattice.axisStep a μ) μ m
def signedSteps (x : InfiniteLattice.LatticePoint a) (μ : Fin 4) (m : ℤ) :
    List (InfiniteLattice.Link a) :=
  if 0 ≤ m then forwardSteps x μ m.toNat else backwardSteps x μ (-m).toNat
def IsAxisDisplacement (x x' : InfiniteLattice.LatticePoint a) (μ : Fin 4) (m : ℤ) : Prop :=
  x' - x = m • InfiniteLattice.axisStep a μ
def axisPath (x x' : InfiniteLattice.LatticePoint a) : List (InfiniteLattice.Link a) :=
  open Classical in
  if h : ∃ q : Fin 4 × ℤ, IsAxisDisplacement x x' q.1 q.2 then
    signedSteps x h.choose.1 h.choose.2
  else []
def IsFieldIn (G : Set ComplexMatrix2) (U : InfiniteLattice.Link a → ComplexMatrix2) : Prop :=
  (∀ e, U e ∈ G) ∧ ∀ e, U e.opposite = (U e)⁻¹
def IsFieldOn (G : Set ComplexMatrix2) (S : Set (InfiniteLattice.Link a))
    (U : InfiniteLattice.Link a → ComplexMatrix2) : Prop :=
  (∀ e ∈ S, U e ∈ G) ∧ ∀ e ∈ S, U e.opposite = (U e)⁻¹
def gaugeAct (u : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (U : InfiniteLattice.Link a → ComplexMatrix2) : InfiniteLattice.Link a → ComplexMatrix2 :=
  fun e => u e.initial * U e * (u e.terminal)⁻¹
end OneLattice
def fieldSpace (L k j : ℕ) : Set (Edge L k j → ComplexMatrix2) :=
  {U | IsFieldIn PeriodicLattice.compactGaugeGroup U}
def gaugeGroupAt (L k j : ℕ) : Set (Vertex L k j → ComplexMatrix2) :=
  {u | ∀ x, u x ∈ PeriodicLattice.compactGaugeGroup}
section Blocks
variable (L : ℕ) {a : ℝ} (a' : ℝ)
def cubeOfOrder (m : ℕ) (y : InfiniteLattice.LatticePoint a) : Set AmbientSpace :=
  {x | ∃ ν : Fin 4 → ℤ, (∀ μ, 2 * |ν μ| ≤ (L : ℤ) ^ m - 1) ∧
    x = (y : AmbientSpace) + ∑ μ, Pi.single μ ((ν μ : ℝ) * a')}
abbrev cube (y : InfiniteLattice.LatticePoint a) : Set AmbientSpace := cubeOfOrder L a' 1 y
def doubleCube (c : InfiniteLattice.Link a) : Set AmbientSpace :=
  cube L a' c.initial ∪ cube L a' c.terminal
def linkCorridor (c : InfiniteLattice.Link a) : Set (InfiniteLattice.Link a') :=
  {e | (e.initial : AmbientSpace) ∈ cube L a' c.initial ∧
    (e.terminal : AmbientSpace) ∈ cube L a' c.terminal}
def toFiner (y : InfiniteLattice.LatticePoint a) : InfiniteLattice.LatticePoint a' :=
  Classical.epsilon fun x : InfiniteLattice.LatticePoint a' => (x : AmbientSpace) = y
def IsPivotLink (c : InfiniteLattice.Link a) (e : InfiniteLattice.Link a') : Prop :=
  e ∈ linkCorridor L a' c ∧ e ∈ axisPath (toFiner a' c.initial) (toFiner a' c.terminal)
def pivotLink (c : InfiniteLattice.Link a) : InfiniteLattice.Link a' :=
  Classical.epsilon (IsPivotLink L a' c)
def cubeVertices (y : InfiniteLattice.LatticePoint a) : Set (InfiniteLattice.LatticePoint a') :=
  {x | (x : AmbientSpace) ∈ cube L a' y}
def doubleCubeLinks (c : InfiniteLattice.Link a) : Set (InfiniteLattice.Link a') :=
  {e | (e.initial : AmbientSpace) ∈ doubleCube L a' c ∧
    (e.terminal : AmbientSpace) ∈ doubleCube L a' c}
end Blocks
section Contours
variable (L : ℕ) {a a' : ℝ}
def IsCubeOffset (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a')
    (ν : Fin 4 → ℤ) : Prop :=
  (x : AmbientSpace) - (y : AmbientSpace) = ∑ μ, Pi.single μ ((ν μ : ℝ) * a') ∧
    ∀ μ, 2 * |ν μ| ≤ (L : ℤ) - 1
def cubeOffset (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    Fin 4 → ℤ :=
  Classical.epsilon (IsCubeOffset L y x)
def offsetSupport (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    Finset (Fin 4) :=
  Finset.univ.filter fun μ => cubeOffset L y x μ ≠ 0
abbrev ContourOrder (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    Type :=
  Fin (offsetSupport L y x).card ≃ offsetSupport L y x
def stepsInOrder (ν : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint a') :
    List (Fin 4) → List (InfiniteLattice.Link a')
  | [] => []
  | μ :: l => signedSteps x μ (ν μ) ++ stepsInOrder ν (x + ν μ • InfiniteLattice.axisStep a' μ) l
def contour (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a')
    (σ : ContourOrder L y x) : List (InfiniteLattice.Link a') :=
  stepsInOrder (cubeOffset L y x) (toFiner a' y)
    ((List.finRange _).map fun i => ((σ i : offsetSupport L y x) : Fin 4))
def contourSet (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    Set (List (InfiniteLattice.Link a')) :=
  Set.range (contour L y x)
def shifted (c : InfiniteLattice.Link a) (x : InfiniteLattice.LatticePoint a') :
    InfiniteLattice.LatticePoint a' :=
  x + toFiner a' (c.terminal - c.initial)
def crossingPath (c : InfiniteLattice.Link a) (x : InfiniteLattice.LatticePoint a') :
    List (InfiniteLattice.Link a') :=
  axisPath x (shifted c x)
def transportAlong (U : InfiniteLattice.Link a' → ComplexMatrix2) (c : InfiniteLattice.Link a) :
    ComplexMatrix2 :=
  linkHolonomy U (axisPath (toFiner a' c.initial) (toFiner a' c.terminal))
def contourHolonomies (U : InfiniteLattice.Link a' → ComplexMatrix2)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') :
    ContourOrder L y x → ComplexMatrix2 :=
  fun σ => linkHolonomy U (contour L y x σ)
def contourAverage (B : InfiniteLattice.Link a' → ComplexMatrix2)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') : ComplexMatrix2 :=
  (((Fintype.card (ContourOrder L y x) : ℝ)⁻¹ : ℝ) : ℂ) •
    ∑ σ : ContourOrder L y x, sumAlong B (contour L y x σ)
def linearSmoothing (B : InfiniteLattice.Link a' → ComplexMatrix2) :
    InfiniteLattice.Link a → ComplexMatrix2 :=
  fun c => PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ cubeVertices L a' c.initial,
    (contourAverage L B c.initial x + sumAlong B (crossingPath c x) -
      contourAverage L B c.terminal (shifted c x))
def complexContourMean (U : InfiniteLattice.Link a' → ComplexMatrix2)
    (y : InfiniteLattice.LatticePoint a) (x : InfiniteLattice.LatticePoint a') : ComplexMatrix2 :=
  PeriodicLattice.complexLogMean (contourHolonomies L U y x)
def complexDomain (c : InfiniteLattice.Link a) : Set (InfiniteLattice.Link a' → ComplexMatrix2) :=
  {U | IsFieldOn PeriodicLattice.complexGaugeGroup (doubleCubeLinks L a' c) U ∧
    (∀ x ∈ cubeVertices L a' c.initial,
      ComplexMatrix2.familyDiameter (contourHolonomies L U c.initial x) <
        Averaging.centreOfMassDiameter) ∧
    ∀ x ∈ cubeVertices L a' c.terminal,
      ComplexMatrix2.familyDiameter (contourHolonomies L U c.terminal x) <
        Averaging.centreOfMassDiameter}
def crossingDefect (U : InfiniteLattice.Link a' → ComplexMatrix2) (c : InfiniteLattice.Link a)
    (x : InfiniteLattice.LatticePoint a') : ComplexMatrix2 :=
  complexContourMean L U c.initial x * linkHolonomy U (crossingPath c x) *
    (complexContourMean L U c.terminal (shifted c x))⁻¹ * (transportAlong U c)⁻¹
def complexDomainNearOne (c : InfiniteLattice.Link a) :
    Set (InfiniteLattice.Link a' → ComplexMatrix2) :=
  {U | U ∈ complexDomain L c ∧
    ∀ x ∈ cubeVertices L a' c.initial,
      ComplexMatrix2.operatorNorm (crossingDefect L U c x - 1) < 1}
def complexSmoothingPositive (U : InfiniteLattice.Link a' → ComplexMatrix2)
    (c : InfiniteLattice.Link a) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (PeriodicLattice.inverseFourthPowerWeight L •
    ∑ᶠ x ∈ cubeVertices L a' c.initial, ComplexMatrix2.logSeries (crossingDefect L U c x)) *
      transportAlong U c
def complexSmoothing (U : InfiniteLattice.Link a' → ComplexMatrix2) :
    InfiniteLattice.Link a → ComplexMatrix2 :=
  open Classical in
  fun c => if c.IsPositivelyOriented then complexSmoothingPositive L U c
    else (complexSmoothingPositive L U c.opposite)⁻¹
end Contours
section Isometries
variable {a : ℝ}
def IsDistancePreserving (f : AmbientSpace → AmbientSpace) : Prop :=
  ∀ p q, TorusMetric.euclidNormVec (f p - f q) = TorusMetric.euclidNormVec (p - q)
def MapsSublatticeOnto (a : ℝ) (f : AmbientSpace → AmbientSpace) : Prop :=
  f '' (InfiniteLattice.latticeSubgroup a : Set AmbientSpace) = InfiniteLattice.latticeSubgroup a
def vertexImage (f : AmbientSpace → AmbientSpace) (v : InfiniteLattice.LatticePoint a) :
    InfiniteLattice.LatticePoint a :=
  Classical.epsilon fun w => (w : AmbientSpace) = f v
def vertexPreimage (f : AmbientSpace → AmbientSpace) (v : InfiniteLattice.LatticePoint a) :
    InfiniteLattice.LatticePoint a :=
  Classical.epsilon fun w => f w = v
def edgeImage (f : AmbientSpace → AmbientSpace) (e : InfiniteLattice.Link a) :
    InfiniteLattice.Link a :=
  Classical.epsilon fun e' =>
    e'.initial = vertexImage f e.initial ∧ e'.terminal = vertexImage f e.terminal
def edgePreimage (f : AmbientSpace → AmbientSpace) (e : InfiniteLattice.Link a) :
    InfiniteLattice.Link a :=
  Classical.epsilon fun e' =>
    e'.initial = vertexPreimage f e.initial ∧ e'.terminal = vertexPreimage f e.terminal
def pathImage (f : AmbientSpace → AmbientSpace) (γ : List (InfiniteLattice.Link a)) :
    List (InfiniteLattice.Link a) :=
  γ.map (edgeImage f)
def pushField (f : AmbientSpace → AmbientSpace) (V : InfiniteLattice.Link a → ComplexMatrix2) :
    InfiniteLattice.Link a → ComplexMatrix2 :=
  fun e => V (edgePreimage f e)
def pushSiteFunction {E : Type*} (f : AmbientSpace → AmbientSpace)
    (g : InfiniteLattice.LatticePoint a → E) : InfiniteLattice.LatticePoint a → E :=
  fun v => g (vertexPreimage f v)
end Isometries
def supDistOne {ι : Type*} (V : ι → ComplexMatrix2) : ℝ≥0∞ :=
  ⨆ i, ENNReal.ofReal (ComplexMatrix2.operatorNorm (V i - 1))
def EventuallyNearIdentity {ι : Type*} (D : Set (ι → ComplexMatrix2))
    (P : (ι → ComplexMatrix2) → Prop) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ V ∈ D, supDistOne V < ENNReal.ofReal ε → P V
def IsAnalyticInFinitelyManyLinks {a : ℝ} (D : Set (InfiniteLattice.Link a → ComplexMatrix2))
    (f : (InfiniteLattice.Link a → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  ∃ (F : Finset (InfiniteLattice.Link a)) (O : Set (F → ComplexMatrix2))
    (g : (F → ComplexMatrix2) → Unit → ComplexMatrix2),
    ComplexMatrix2.IsRealAnalyticBetween (fun _ => ComplexMatrix2.FactorKind.group)
        (fun _ => ComplexMatrix2.FactorKind.group) O g ∧
      ∀ V ∈ D, (fun e : F => V e) ∈ O ∧ f V = g (fun e : F => V e) ()
def IsAnalyticMap {a : ℝ} {ι : Type*} (D : Set (InfiniteLattice.Link a → ComplexMatrix2))
    (m : (InfiniteLattice.Link a → ComplexMatrix2) → ι → ComplexMatrix2) : Prop :=
  ∀ i, IsAnalyticInFinitelyManyLinks D fun V => m V i
end FullSpace
def EventuallyIn {α : Type*} [Preorder α] (S : Set α) (P : α → Prop) : Prop :=
  ∃ s₀ ∈ S, ∀ s ∈ S, s₀ ≤ s → P s
end Tower
end YangMills.Construction
end
