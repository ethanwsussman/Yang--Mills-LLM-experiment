import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
namespace TorusLumps
open BlockAverages LumpContours TorusFields
structure StepParameters where
  coupling : ℝ
  side : ℕ
  [side_ne : NeZero side]
  grid : LumpGrid side
  baseDepth : ℕ
  threshold : ℝ
  κ : ℝ
  κ₁ : ℝ
  rt : ℝ
  n₁ : ℝ
  E : ℝ
  E₃ : ℝ
  derivBound : ℝ
  n₀ : ℕ
  y₁ : ℝ
  B : ℝ
attribute [instance] StepParameters.side_ne
def stepBlockFrame (L m : ℕ) : BlockFrame := ⟨L, 0, fun _ => m⟩
instance (L m j : ℕ) (i : Fin 4) [NeZero L] [NeZero m] : NeZero ((stepBlockFrame L m).period j i) :=
  ⟨by
    simp only [stepBlockFrame, BlockFrame.period]
    exact mul_ne_zero (NeZero.ne m) (pow_ne_zero _ (NeZero.ne L))⟩
variable {m : ℕ}
def parentBlock (L : ℕ) (x : TorusSite (m * L)) : TorusSite m :=
  fun i => ((((x i).cast : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) : ℤ)
open Classical in
def sitesInBlocks [NeZero m] (L : ℕ) [NeZero L] (S : Finset (TorusSite m)) : Finset (TorusSite (m * L)) :=
  Finset.univ.filter fun x => parentBlock L x ∈ S
def levelSites (F : BlockFrame) (j : ℕ) : Finset (F.Site j) := boxSites j 0 fun i => (F.period j i : ℤ) - 1
def toTorusSite {F : BlockFrame} {j : ℕ} (m : ℕ) (x : F.Site j) : TorusSite m :=
  fun k => ((siteCoords x k : ℤ) : ZMod m)
open Classical in
def torusHotLumps (p : StepParameters) (W : TorusField m) : Finset (Finset (TorusSite m)) :=
  (hotLumps p.grid p.threshold (levelSites (stepBlockFrame p.side (m / p.side)) 0)
    (readAtLevel (stepBlockFrame p.side (m / p.side)) 0 W)).image fun l => l.image (toTorusSite m)
def torusHotSites (p : StepParameters) (W : TorusField m) : Finset (TorusSite m) :=
  (torusHotLumps p W).biUnion id
open Classical in
def lumpCenter [NeZero m] (l : Finset (TorusSite m)) : TorusSite m :=
  if h : ∃ z, ∀ x ∈ l, supDist x z ≤ 2 ^ 14 then h.choose else 0
def partitionFn (s : ℝ) : ℝ :=
  ∫ g : UnitQuaternion, Real.exp (s * ((g : UnitQuaternion) : ℍ[ℝ]).re) ∂haarUnit
def logPartitionGap (s : ℝ) : ℝ := s - Real.log (partitionFn s)
def baseChoices (p : StepParameters) [NeZero m] (W : (stepBlockFrame p.side m).GaugeField 0) :
    Finset ((stepBlockFrame p.side m).Cell → (stepBlockFrame p.side m).Site 0) :=
  open Classical in
  Finset.univ.filter fun b =>
    IsBaseChoice p.baseDepth (hotLumps p.grid p.threshold (levelSites (stepBlockFrame p.side m) 0) W) b
def bondKernel (p : StepParameters) (x : ℝ) {m : ℕ} (W : (stepBlockFrame p.side m).GaugeField 0)
    (V : (stepBlockFrame p.side m).GaugeField 1)
    (b : (stepBlockFrame p.side m).Cell → (stepBlockFrame p.side m).Site 0)
    (c : (stepBlockFrame p.side m).Cell × Fin 4) : ℝ :=
  let Wbar := contourMean p.baseDepth
    (hotLumps p.grid p.threshold (levelSites (stepBlockFrame p.side m) 0) W) b W c
  Real.exp (p.coupling * x * (Wbar * ((V c.1 c.2)⁻¹ : UnitQuaternion)).re) /
    partitionFn (p.coupling * x * ‖Wbar‖)
def averagedKernel (p : StepParameters) (x : ℝ) [NeZero m] (W : (stepBlockFrame p.side m).GaugeField 0)
    (V : (stepBlockFrame p.side m).GaugeField 1) : ℝ :=
  (1 / ((baseChoices p W).card : ℝ)) * ∑ b ∈ baseChoices p W, ∏ c : (stepBlockFrame p.side m).Cell × Fin 4,
    bondKernel p x W V b c
abbrev TorusFunctional : Type := (m : ℕ) → TorusField m → ℝ
def kernelImage (p : StepParameters) (x : ℝ) (D : TorusFunctional) : TorusFunctional := fun m V =>
  if h : m = 0 then 0 else
    haveI : NeZero m := ⟨h⟩
    ∫ W : TorusField (m * p.side), D (m * p.side) W *
      averagedKernel p x (readAtLevel (stepBlockFrame p.side m) 0 W)
        (readAtLevel (stepBlockFrame p.side m) 1 V) ∂(fieldHaar (m * p.side))
end TorusLumps
end YangMills.Construction
end
