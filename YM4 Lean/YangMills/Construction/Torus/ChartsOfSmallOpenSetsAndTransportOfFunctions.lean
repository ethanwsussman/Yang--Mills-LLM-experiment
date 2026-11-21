import YangMills.Construction.Torus.SeparatedTuplesFormsAndDistinctPointsOfTorusOrFourSpace
import YangMills.Construction.Torus.TestFunctionsAndDistributionsOnOpenSetsOfTuples
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open YangMills.Construction.Conventions (StandingParameters)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints
variable {s : StandingParameters} {E : Ambient} {n : ℕ}
def boxSet (V : Fin n → Set (Pt s E)) : Set (Tuple s E n) := pi univ V
def IsSmallOpenTuple (V : Fin n → Set (Pt s E)) : Prop :=
  1 ≤ n ∧ ∀ i, IsOpen (V i) ∧ (V i).Nonempty ∧ setDiam s E (V i) < injRadius s E
def maxDiam (V : Fin n → Set (Pt s E)) : ℝ≥0∞ := ⨆ i, setDiam s E (V i)
theorem isGreatest_maxDiam (hn : 1 ≤ n) (V : Fin n → Set (Pt s E)) :
    IsGreatest (range fun i => setDiam s E (V i)) (maxDiam V) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨exists_eq_ciSup_of_finite, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact le_iSup (fun i => setDiam s E (V i)) i
def IsBasePoint (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) : Prop :=
  ∀ i, proj s E (z i) ∈ V i
def localChartDomain (A : Set (Pt s E)) (b : Fin 4 → ℝ) : Set (Pt s .euclidean) :=
  {u : Fin 4 → ℝ |
    ENNReal.ofReal (euclidNormVec u) < injRadius s E ∧ proj s E (b + u) ∈ A}
variable (s E) in
def localChart (b : Fin 4 → ℝ) (u : Fin 4 → ℝ) : Pt s E := proj s E (b + u)
theorem mapsTo_localChart (A : Set (Pt s E)) (b : Fin 4 → ℝ) :
    MapsTo (localChart s E b) (localChartDomain A b) A :=
  fun _ hu => hu.2
def boxChartDomain (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) :
    Set (Tuple s .euclidean n) :=
  boxSet fun i => localChartDomain (V i) (z i)
variable (s E) in
def boxChart (z : Fin n → Fin 4 → ℝ) (u : Tuple s .euclidean n) : Tuple s E n :=
  fun i => localChart s E (z i) (u i)
theorem mapsTo_boxChart (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) :
    MapsTo (boxChart s E z) (boxChartDomain V z) (boxSet V) :=
  fun _ hu i hi => mapsTo_localChart (V i) (z i) (hu i hi)
theorem boxChart_eq_tupleProj (z u : Fin n → Fin 4 → ℝ) :
    boxChart s E z u = tupleProj s E n (flattenCoords n (z + u)) := by
  funext i
  rw [tupleProj_flattenCoords]
  rfl
section Transport
variable {R : Type*} [Zero R]
def chartPullback (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) (F : Tuple s E n → R) :
    Tuple s .euclidean n → R :=
  (boxChartDomain V z).indicator (F ∘ boxChart s E z)
def chartPushforward (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ)
    (H : Tuple s .euclidean n → R) : Tuple s E n → R := fun y =>
  open Classical in
  if h : ∃ u ∈ boxChartDomain V z, boxChart s E z u = y then H h.choose else 0
variable {V : Fin n → Set (Pt s E)} {z : Fin n → Fin 4 → ℝ}
theorem chartPullback_of_mem (F : Tuple s E n → R) {u : Tuple s .euclidean n}
    (hu : u ∈ boxChartDomain V z) : chartPullback V z F u = F (boxChart s E z u) :=
  indicator_of_mem hu _
theorem chartPullback_of_notMem (F : Tuple s E n → R) {u : Tuple s .euclidean n}
    (hu : u ∉ boxChartDomain V z) : chartPullback V z F u = 0 :=
  indicator_of_notMem hu _
theorem chartPushforward_boxChart (hinj : InjOn (boxChart s E z) (boxChartDomain V z))
    (H : Tuple s .euclidean n → R) {u : Tuple s .euclidean n} (hu : u ∈ boxChartDomain V z) :
    chartPushforward V z H (boxChart s E z u) = H u := by
  have h : ∃ v ∈ boxChartDomain V z, boxChart s E z v = boxChart s E z u := ⟨u, hu, rfl⟩
  rw [chartPushforward, dif_pos h, hinj h.choose_spec.1 hu h.choose_spec.2]
theorem chartPushforward_of_notMem (H : Tuple s .euclidean n → R) {y : Tuple s E n}
    (hy : y ∉ boxChart s E z '' boxChartDomain V z) : chartPushforward V z H y = 0 := by
  rw [chartPushforward, dif_neg]
  rintro ⟨u, hu, rfl⟩
  exact hy ⟨u, hu, rfl⟩
theorem chartPullback_ofReal (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ)
    (F : Tuple s E n → ℝ) :
    chartPullback V z (fun y => (F y : ℂ)) = fun u => ((chartPullback V z F u : ℝ) : ℂ) := by
  funext u
  by_cases hu : u ∈ boxChartDomain V z
  · rw [chartPullback_of_mem _ hu, chartPullback_of_mem _ hu]
  · rw [chartPullback_of_notMem _ hu, chartPullback_of_notMem _ hu, Complex.ofReal_zero]
theorem chartPushforward_ofReal (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ)
    (H : Tuple s .euclidean n → ℝ) :
    chartPushforward V z (fun u => (H u : ℂ)) = fun y => ((chartPushforward V z H y : ℝ) : ℂ) := by
  funext y
  by_cases h : ∃ u ∈ boxChartDomain V z, boxChart s E z u = y
  · simp only [chartPushforward, dif_pos h]
  · simp only [chartPushforward, dif_neg h, Complex.ofReal_zero]
variable (V z) in
def coordPullback (i : Fin n) (F : Tuple s E 1 → R) : Tuple s .euclidean 1 → R :=
  chartPullback (fun _ => V i) (fun _ => z i) F
variable (V z) in
def coordPushforward (i : Fin n) (H : Tuple s .euclidean 1 → R) : Tuple s E 1 → R :=
  chartPushforward (fun _ => V i) (fun _ => z i) H
variable (V z) in
def singlePullback (i : Fin n) (φ : Pt s E → R) : Pt s .euclidean → R :=
  fun u => coordPullback V z i (fun y => φ (y 0)) fun _ => u
variable (V z) in
def singlePushforward (i : Fin n) (g : Pt s .euclidean → R) : Pt s E → R :=
  fun y => coordPushforward V z i (fun v => g (v 0)) fun _ => y
theorem mem_boxChartDomain_single {i : Fin n} {v : Tuple s .euclidean 1} :
    v ∈ boxChartDomain (fun _ : Fin 1 => V i) (fun _ => z i) ↔
      v 0 ∈ localChartDomain (V i) (z i) := by
  constructor
  · exact fun h => h 0 (mem_univ _)
  · intro h j _
    rwa [Subsingleton.elim j 0]
theorem singlePullback_of_mem {i : Fin n} (φ : Pt s E → R) {u : Pt s .euclidean}
    (hu : u ∈ localChartDomain (V i) (z i)) :
    singlePullback V z i φ u = φ (localChart s E (z i) u) :=
  chartPullback_of_mem _ (mem_boxChartDomain_single.mpr hu)
theorem singlePullback_of_notMem {i : Fin n} (φ : Pt s E → R) {u : Pt s .euclidean}
    (hu : u ∉ localChartDomain (V i) (z i)) : singlePullback V z i φ u = 0 :=
  chartPullback_of_notMem _ fun h => hu (mem_boxChartDomain_single.mp h)
end Transport
def coordTestFns (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) (i : Fin n) :
    Set (Tuple s .euclidean 1 → ℂ) :=
  testFns (boxSet fun _ : Fin 1 => localChartDomain (V i) (z i))
def boxTestFns (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) :
    Set (Tuple s .euclidean n → ℂ) :=
  testFns (boxChartDomain V z)
def coordC1CompactSupport (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ)
    (i : Fin n) : Set (Pt s .euclidean → ℝ) :=
  c1CompactSupportIn (localChartDomain (V i) (z i))
def boxDistribs (V : Fin n → Set (Pt s E)) (z : Fin n → Fin 4 → ℝ) :
    Set (testFns (boxChartDomain V z) → ℂ) :=
  distribs (boxChartDomain V z)
end YangMills.Construction.AmbientPoints
