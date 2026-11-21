import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Tower.SelectedObjects
structure ImagesOnSide (L n k j : ℕ)
    (f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n) : Prop where
  vertexImage_coe : ∀ x : Vertex L n k j,
    ((vertexImage (k := k) (j := j) f x : Vertex L n k j) : PeriodicLattice.FourTorus L n) = f x
  vertexImage_unique : ∀ x x' : Vertex L n k j,
    (x' : PeriodicLattice.FourTorus L n) = f x → x' = vertexImage (k := k) (j := j) f x
  apply_vertexPreimage : ∀ x : Vertex L n k j,
    f (vertexPreimage (k := k) (j := j) f x : Vertex L n k j) = x
  vertexPreimage_unique : ∀ x x' : Vertex L n k j,
    f x' = x → x' = vertexPreimage (k := k) (j := j) f x
  edgeImage_endpoints : ∀ b : Edge L n k j,
    (edgeImage (k := k) (j := j) f b).source = vertexImage (k := k) (j := j) f b.source ∧
      (edgeImage (k := k) (j := j) f b).target = vertexImage (k := k) (j := j) f b.target
  edgeImage_unique : ∀ b b' : Edge L n k j,
    b'.source = vertexImage (k := k) (j := j) f b.source →
      b'.target = vertexImage (k := k) (j := j) f b.target → b' = edgeImage (k := k) (j := j) f b
  edgePreimage_endpoints : ∀ b : Edge L n k j,
    (edgePreimage (k := k) (j := j) f b).source = vertexPreimage (k := k) (j := j) f b.source ∧
      (edgePreimage (k := k) (j := j) f b).target = vertexPreimage (k := k) (j := j) f b.target
  edgePreimage_unique : ∀ b b' : Edge L n k j,
    b'.source = vertexPreimage (k := k) (j := j) f b.source →
      b'.target = vertexPreimage (k := k) (j := j) f b.target →
        b' = edgePreimage (k := k) (j := j) f b
structure OnSide (L n k j : ℕ) : Prop where
  one_mem_fieldSpace : (fun _ => (1 : ComplexMatrix2)) ∈ fieldSpace L n k j
  one_mem_gaugeGroupAt : (fun _ => (1 : ComplexMatrix2)) ∈ gaugeGroupAt L n k j
  images : ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
    IsDistancePreserving f → MapsSublatticeOnto k j f → ImagesOnSide L n k j f
structure ImagesAtInfinity (L k j : ℕ) (f : AmbientSpace → AmbientSpace) : Prop where
  vertexImage_coe : ∀ x : FullSpace.Vertex L k j,
    ((FullSpace.vertexImage f x : FullSpace.Vertex L k j) : AmbientSpace) = f x
  vertexImage_unique : ∀ x x' : FullSpace.Vertex L k j,
    (x' : AmbientSpace) = f x → x' = FullSpace.vertexImage f x
  apply_vertexPreimage : ∀ x : FullSpace.Vertex L k j,
    f (FullSpace.vertexPreimage f x : FullSpace.Vertex L k j) = x
  vertexPreimage_unique : ∀ x x' : FullSpace.Vertex L k j,
    f x' = x → x' = FullSpace.vertexPreimage f x
  edgeImage_endpoints : ∀ b : FullSpace.Edge L k j,
    (FullSpace.edgeImage f b).initial = FullSpace.vertexImage f b.initial ∧
      (FullSpace.edgeImage f b).terminal = FullSpace.vertexImage f b.terminal
  edgeImage_unique : ∀ b b' : FullSpace.Edge L k j,
    b'.initial = FullSpace.vertexImage f b.initial → b'.terminal = FullSpace.vertexImage f b.terminal →
      b' = FullSpace.edgeImage f b
  edgePreimage_endpoints : ∀ b : FullSpace.Edge L k j,
    (FullSpace.edgePreimage f b).initial = FullSpace.vertexPreimage f b.initial ∧
      (FullSpace.edgePreimage f b).terminal = FullSpace.vertexPreimage f b.terminal
  edgePreimage_unique : ∀ b b' : FullSpace.Edge L k j,
    b'.initial = FullSpace.vertexPreimage f b.initial →
      b'.terminal = FullSpace.vertexPreimage f b.terminal →
      b' = FullSpace.edgePreimage f b
structure AtInfinity (L k j : ℕ) : Prop where
  one_mem_fieldSpace : (fun _ => (1 : ComplexMatrix2)) ∈ FullSpace.fieldSpace L k j
  one_mem_gaugeGroupAt : (fun _ => (1 : ComplexMatrix2)) ∈ FullSpace.gaugeGroupAt L k j
  images : ∀ f : AmbientSpace → AmbientSpace, FullSpace.IsDistancePreserving f →
    FullSpace.MapsSublatticeOnto (meshAt L k j) f → ImagesAtInfinity L k j f
def IsNearLogMean {ι : Type*} [Fintype ι] (V : ι → ComplexMatrix2) (W : ComplexMatrix2) : Prop :=
  ComplexMatrix2.IsLogMean PeriodicLattice.complexGaugeGroup V W ∧
    ∃ i, ComplexMatrix2.operatorNorm (V i * W⁻¹ - 1) ≤ PeriodicLattice.complexMeanTolerance
structure CubesAtInfinity (L k j : ℕ) : Prop where
  toFiner_coe : ∀ y : FullSpace.Vertex L k j,
    ((FullSpace.toFiner (meshAt L k (j - 1)) y : FullSpace.Vertex L k (j - 1)) : AmbientSpace) = y
  axis_endpoints : ∀ c : FullSpace.Edge L k j, ∃ q : Fin 4 × ℤ,
    FullSpace.IsAxisDisplacement (FullSpace.toFiner (meshAt L k (j - 1)) c.initial)
      (FullSpace.toFiner (meshAt L k (j - 1)) c.terminal) q.1 q.2
  axis_shifted : ∀ (c : FullSpace.Edge L k j) (x : FullSpace.Vertex L k (j - 1)),
    x ∈ FullSpace.cubeVertices L (meshAt L k (j - 1)) c.initial →
      ∃ q : Fin 4 × ℤ, FullSpace.IsAxisDisplacement x (FullSpace.shifted c x) q.1 q.2
  shifted_mem : ∀ (c : FullSpace.Edge L k j) (x : FullSpace.Vertex L k (j - 1)),
    x ∈ FullSpace.cubeVertices L (meshAt L k (j - 1)) c.initial →
      FullSpace.shifted c x ∈ FullSpace.cubeVertices L (meshAt L k (j - 1)) c.terminal
  existsUnique_pivotLink : ∀ c : FullSpace.Edge L k j,
    ∃! b : FullSpace.Edge L k (j - 1), FullSpace.IsPivotLink L (meshAt L k (j - 1)) c b
  existsUnique_cubeOffset : ∀ (y : FullSpace.Vertex L k j)
      (x : FullSpace.Vertex L k (j - 1)), x ∈ FullSpace.cubeVertices L (meshAt L k (j - 1)) y →
    ∃! ν : Fin 4 → ℤ, FullSpace.IsCubeOffset L y x ν
  cubeVertices_finite : ∀ y : FullSpace.Vertex L k j,
    (FullSpace.cubeVertices L (meshAt L k (j - 1)) y).Finite
  cubeVertices_ncard : ∀ y : FullSpace.Vertex L k j,
    (FullSpace.cubeVertices L (meshAt L k (j - 1)) y).ncard = L ^ 4
  complexContourMean_isNearLogMean : ∀ (c : FullSpace.Edge L k j)
      (U : FullSpace.Edge L k (j - 1) → ComplexMatrix2), U ∈ FullSpace.complexDomain L c →
    ∀ y ∈ ({c.initial, c.terminal} : Set (FullSpace.Vertex L k j)),
      ∀ x ∈ FullSpace.cubeVertices L (meshAt L k (j - 1)) y,
        IsNearLogMean (FullSpace.contourHolonomies L U y x) (FullSpace.complexContourMean L U y x) ∧
          ∀ W, IsNearLogMean (FullSpace.contourHolonomies L U y x) W →
            W = FullSpace.complexContourMean L U y x
  complexContourMean_mem : ∀ (c : FullSpace.Edge L k j)
      (U : FullSpace.Edge L k (j - 1) → ComplexMatrix2), U ∈ FullSpace.complexDomain L c →
    ∀ y ∈ ({c.initial, c.terminal} : Set (FullSpace.Vertex L k j)),
      ∀ x ∈ FullSpace.cubeVertices L (meshAt L k (j - 1)) y,
        FullSpace.complexContourMean L U y x ∈ PeriodicLattice.complexGaugeGroup
  transportAlong_mem : ∀ (c : FullSpace.Edge L k j)
      (U : FullSpace.Edge L k (j - 1) → ComplexMatrix2), U ∈ FullSpace.complexDomain L c →
    FullSpace.transportAlong U c ∈ PeriodicLattice.complexGaugeGroup
def Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ k j : ℕ, j ≤ k → (∀ n : ℕ, 0 < n → OnSide L n k j) ∧ AtInfinity L k j) ∧
    ∀ k j : ℕ, 1 ≤ j → j ≤ k → CubesAtInfinity L k j
end YangMills.Construction.Tower.SelectedObjects
end
