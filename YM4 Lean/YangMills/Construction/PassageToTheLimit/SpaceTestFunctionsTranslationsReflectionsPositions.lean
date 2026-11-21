import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.EuclideanIsometries
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
abbrev SharpParameter : Type := Set.Ici (1 : ℝ)
def multiplesOf (a : ℝ) : Set ℝ := {x | ∃ n : ℤ, x = a * (n : ℝ)}
def halfShiftedMultiplesOf (a : ℝ) : Set ℝ := {x | ∃ n : ℤ, x = a * ((n : ℝ) + 1 / 2)}
def realInfDist (c : ℝ) (S : Set ℝ) : ℝ≥0∞ := ⨅ t ∈ S, ENNReal.ofReal |c - t|
def stdBasisVec (μ : Fin 4) : Fin 4 → ℝ := Pi.single μ 1
inductive Ambient where
  | euclidean
  | periodic
namespace Ambient
variable (s : Conventions.StandingParameters)
def Carrier : Ambient → Type
  | euclidean => Fin 4 → ℝ
  | periodic => s.Torus
instance instAddCommGroupCarrier : (E : Ambient) → AddCommGroup (E.Carrier s)
  | euclidean => inferInstanceAs (AddCommGroup (Fin 4 → ℝ))
  | periodic => inferInstanceAs (AddCommGroup s.Torus)
def proj : (E : Ambient) → (Fin 4 → ℝ) → E.Carrier s
  | euclidean, x => x
  | periodic, x => TorusMetric.torusProj s.side x
def periodGroup : Ambient → AddSubgroup (Fin 4 → ℝ)
  | euclidean => ⊥
  | periodic => InfiniteLattice.latticeSubgroup s.side
variable (E : Ambient)
theorem proj_add (x y : Fin 4 → ℝ) :
    E.proj s (x + y) = E.proj s x + E.proj s y := by
  cases E with
  | euclidean => rfl
  | periodic => funext μ; exact AddCircle.coe_add _ _ _ |>.trans rfl
theorem proj_neg (x : Fin 4 → ℝ) : E.proj s (-x) = -E.proj s x := by
  cases E with
  | euclidean => rfl
  | periodic => funext μ; exact AddCircle.coe_neg _ |>.trans rfl
theorem proj_surjective : Function.Surjective (E.proj s) := by
  cases E with
  | euclidean => exact fun x => ⟨x, rfl⟩
  | periodic => exact TestFunctions.torusProj_surjective _
theorem mem_periodGroup_iff (γ : Fin 4 → ℝ) : γ ∈ E.periodGroup s ↔ E.proj s γ = 0 := by
  cases E with
  | euclidean => exact Iff.rfl
  | periodic =>
    constructor
    · rintro ⟨n, hn⟩
      funext μ
      refine (AddCircle.coe_eq_zero_iff _).mpr ⟨n μ, ?_⟩
      simp [hn μ]
    · intro h
      have hμ : ∀ μ, ∃ n : ℤ, n • s.side = γ μ := fun μ =>
        (AddCircle.coe_eq_zero_iff _).mp (congrFun h μ)
      choose n hn using hμ
      exact ⟨n, fun μ => by simp [← hn μ]⟩
theorem sub_mem_periodGroup {x y : Fin 4 → ℝ} (h : E.proj s x = E.proj s y) :
    x - y ∈ E.periodGroup s := by
  rw [mem_periodGroup_iff, sub_eq_add_neg, proj_add, proj_neg, h, add_neg_cancel]
def IsLiftOf (x : E.Carrier s) (y : Fin 4 → ℝ) : Prop := E.proj s y = x
def someLift (x : E.Carrier s) : Fin 4 → ℝ := Classical.epsilon fun y => E.IsLiftOf s x y
theorem proj_someLift (x : E.Carrier s) : E.proj s (E.someLift s x) = x :=
  Classical.epsilon_spec (p := fun y => E.IsLiftOf s x y) (E.proj_surjective s x)
theorem isLiftOf_iff {x : E.Carrier s} {y : Fin 4 → ℝ} (hy : E.IsLiftOf s x y) (z : Fin 4 → ℝ) :
    E.IsLiftOf s x z ↔ ∃ γ ∈ E.periodGroup s, z = y + γ := by
  constructor
  · intro hz
    exact ⟨z - y, E.sub_mem_periodGroup s (hz.trans hy.symm), by abel⟩
  · rintro ⟨γ, hγ, rfl⟩
    have h0 := (E.mem_periodGroup_iff s γ).mp hγ
    simpa [IsLiftOf, proj_add, h0] using hy
def addVec (x : E.Carrier s) (v : Fin 4 → ℝ) : E.Carrier s := x + E.proj s v
def translateSet (S : Set (E.Carrier s)) (v : E.Carrier s) : Set (E.Carrier s) := (fun x => x + v) '' S
def translateSetVec (S : Set (E.Carrier s)) (v : Fin 4 → ℝ) : Set (E.Carrier s) :=
  (fun x => E.addVec s x v) '' S
def euclidLength : (E : Ambient) → E.Carrier s → ℝ
  | euclidean, x => TorusMetric.euclidNormVec x
  | periodic, x => TorusMetric.torusEuclidNorm x
def pointDist (x y : E.Carrier s) : ℝ := E.euclidLength s (x - y)
def infSetDist (S S' : Set (E.Carrier s)) : ℝ≥0∞ :=
  ⨅ x ∈ S, ⨅ y ∈ S', ENNReal.ofReal (E.pointDist s x y)
def PositivelySeparated (S S' : Set (E.Carrier s)) : Prop := 0 < E.infSetDist s S S'
def setDiam (S : Set (E.Carrier s)) : ℝ≥0∞ :=
  ⨆ x ∈ S, ⨆ y ∈ S, ENNReal.ofReal (E.pointDist s x y)
abbrev closureSet (S : Set (E.Carrier s)) : Set (E.Carrier s) :=
  MetricNotions.closureWrt (E.pointDist s) S
abbrev IsOpenSubset (S : Set (E.Carrier s)) : Prop := MetricNotions.IsOpenWrt (E.pointDist s) S
abbrev IsClosedSubset (S : Set (E.Carrier s)) : Prop := MetricNotions.IsClosedWrt (E.pointDist s) S
abbrev IsCompactSubset (S : Set (E.Carrier s)) : Prop := MetricNotions.IsCompactWrt (E.pointDist s) S
abbrev IsContinuousSelf (g : E.Carrier s → E.Carrier s) : Prop :=
  MetricNotions.IsContinuousWrt (E.pointDist s) (E.pointDist s) g
abbrev IsContinuousInto {Z : Type*} [PseudoMetricSpace Z] (g : E.Carrier s → Z) : Prop :=
  MetricNotions.IsContinuousWrt (E.pointDist s) dist g
def closedSupport {Z : Type*} [Zero Z] (f : E.Carrier s → Z) : Set (E.Carrier s) :=
  E.closureSet s {x | f x ≠ 0}
def liftFun {Z : Type*} (f : E.Carrier s → Z) : (Fin 4 → ℝ) → Z := f ∘ E.proj s
theorem liftFun_add_of_mem {Z : Type*} (f : E.Carrier s → Z) (x : Fin 4 → ℝ)
    {γ : Fin 4 → ℝ} (hγ : γ ∈ E.periodGroup s) : E.liftFun s f (x + γ) = E.liftFun s f x := by
  have h0 := (E.mem_periodGroup_iff s γ).mp hγ
  simp [liftFun, proj_add, h0]
def IsC1 (f : E.Carrier s → ℝ) : Prop := TestFunctions.IsC1R4 (E.liftFun s f)
def gradR4 (F : (Fin 4 → ℝ) → ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun μ => TestFunctions.partialDerivR4 μ F y
def grad (f : E.Carrier s → ℝ) (x : E.Carrier s) : Fin 4 → ℝ :=
  gradR4 (E.liftFun s f) (E.someLift s x)
theorem grad_comp_proj (f : E.Carrier s → ℝ) :
    E.grad s f ∘ E.proj s = gradR4 (E.liftFun s f) := by
  funext y
  obtain ⟨γ, hγ, hy⟩ := (E.isLiftOf_iff s (x := E.proj s y) (y := y) rfl
    (E.someLift s (E.proj s y))).mp (E.proj_someLift s _)
  funext μ
  simp only [Function.comp_apply, grad, gradR4, TestFunctions.partialDerivR4, hy]
  congr 1
  funext t
  have : y + γ + t • Pi.single μ (1 : ℝ) = y + t • Pi.single μ (1 : ℝ) + γ := by abel
  rw [this, E.liftFun_add_of_mem s f _ hγ]
def partialDeriv (μ : Fin 4) (f : E.Carrier s → ℝ) (x : E.Carrier s) : ℝ := E.grad s f x μ
def gradSup (f : E.Carrier s → ℝ) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal (TorusMetric.euclidNormVec (E.grad s f x))
def normC1 (f : E.Carrier s → ℝ) : ℝ :=
  max (TestFunctions.uniformNorm f) (⨆ μ : Fin 4, TestFunctions.uniformNorm (E.partialDeriv s μ f))
def IsLip : (E : Ambient) → (E.Carrier s → ℝ) → Prop
  | euclidean, f => TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 f
  | periodic, f => TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus f
def lipConst : (E : Ambient) → (E.Carrier s → ℝ) → ℝ
  | euclidean, f => TestFunctions.lipConstR4 f
  | periodic, f => TestFunctions.lipConstTorus f
def normSharp (M : SharpParameter) : (E : Ambient) → (E.Carrier s → ℝ) → ℝ
  | euclidean, f => TestFunctions.sharpNormR4 (M : ℝ) f
  | periodic, f => TestFunctions.sharpNormTorus (M : ℝ) f
def c1Compact : Set (E.Carrier s → ℝ) :=
  {f | E.IsC1 s f ∧ E.IsCompactSubset s (E.closedSupport s f)}
def translateFun {Z : Type*} (v : E.Carrier s) (f : E.Carrier s → Z) (x : E.Carrier s) : Z := f (x - v)
def translateFunVec {Z : Type*} (v : Fin 4 → ℝ) (f : E.Carrier s → Z) : E.Carrier s → Z :=
  E.translateFun s (E.proj s v) f
end Ambient
def coordFlipMatrix (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal fun ν => if ν = μ then -1 else 1
def reflectR4 (μ : Fin 4) (c : ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  y - (2 * (y μ - c)) • stdBasisVec μ
theorem reflectR4_eq (μ : Fin 4) (c : ℝ) (y : Fin 4 → ℝ) :
    reflectR4 μ c y = (coordFlipMatrix μ).mulVec y + (2 * c) • stdBasisVec μ := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [reflectR4, coordFlipMatrix, stdBasisVec, Matrix.mulVec_diagonal]
    ring
  · simp [reflectR4, coordFlipMatrix, stdBasisVec, Matrix.mulVec_diagonal, h]
namespace Ambient
variable (s : Conventions.StandingParameters) (E : Ambient)
def reflect (μ : Fin 4) (c : ℝ) (x : E.Carrier s) : E.Carrier s :=
  E.proj s (reflectR4 μ c (E.someLift s x))
theorem coordFlipMatrix_mulVec_mem (μ : Fin 4) {γ : Fin 4 → ℝ} (hγ : γ ∈ E.periodGroup s) :
    (coordFlipMatrix μ).mulVec γ ∈ E.periodGroup s := by
  cases E with
  | euclidean =>
    have h0 : γ = 0 := hγ
    subst h0
    simp [periodGroup]
  | periodic =>
    obtain ⟨n, hn⟩ := hγ
    refine ⟨fun ν => if ν = μ then -n ν else n ν, fun ν => ?_⟩
    by_cases h : ν = μ
    · simp [coordFlipMatrix, Matrix.mulVec_diagonal, h, hn]
    · simp [coordFlipMatrix, Matrix.mulVec_diagonal, h, hn]
theorem reflect_comp_proj (μ : Fin 4) (c : ℝ) :
    E.reflect s μ c ∘ E.proj s = E.proj s ∘ reflectR4 μ c := by
  funext y
  obtain ⟨γ, hγ, hy⟩ := (E.isLiftOf_iff s (x := E.proj s y) (y := y) rfl
    (E.someLift s (E.proj s y))).mp (E.proj_someLift s _)
  have h0 := (E.mem_periodGroup_iff s _).mp (E.coordFlipMatrix_mulVec_mem s μ hγ)
  have hsplit : reflectR4 μ c (y + γ) =
      reflectR4 μ c y + (coordFlipMatrix μ).mulVec γ := by
    rw [reflectR4_eq, reflectR4_eq, Matrix.mulVec_add]
    abel
  simp only [Function.comp_apply, reflect, hy, hsplit, proj_add, h0, add_zero]
theorem reflect_euclidean (μ : Fin 4) (c : ℝ) (y : Fin 4 → ℝ) :
    euclidean.reflect s μ c y = reflectR4 μ c y :=
  congrFun (euclidean.reflect_comp_proj s μ c) y
def reflectFun {Z : Type*} (μ : Fin 4) (c : ℝ) (f : E.Carrier s → Z) : E.Carrier s → Z :=
  f ∘ E.reflect s μ c
end Ambient
section Positions
variable (s : Conventions.StandingParameters)
def latticeScale (i : ℤ) : ℝ := PeriodicLattice.meshSize s.L i
def vertexCoords (i : ℕ+) : Set ℝ := multiplesOf (latticeScale s (i : ℕ))
def edgeMidCoords (i : ℕ+) : Set ℝ := halfShiftedMultiplesOf (latticeScale s (i : ℕ))
def axisMirror : (E : Ambient) → Fin 4 → ℝ → Set (E.Carrier s)
  | .euclidean, μ, c => {x | x μ = c}
  | .periodic, μ, c => TorusMetric.torusProj s.side '' ({x | x μ = c} ∪ {x | x μ = c + s.side / 2})
def IsVertexMirror (E : Ambient) (i : ℕ+) (P : Set (E.Carrier s)) : Prop :=
  ∃ (μ : Fin 4) (c : ℝ), c ∈ vertexCoords s i ∧ P = axisMirror s E μ c
def IsEdgeMirror (E : Ambient) (i : ℕ+) (P : Set (E.Carrier s)) : Prop :=
  ∃ (μ : Fin 4) (c : ℝ), c ∈ edgeMidCoords s i ∧ P = axisMirror s E μ c
def edgeMidCoordsAll : Set ℝ := ⋃ i : ℕ+, edgeMidCoords s i
end Positions
end LimitSpaces
end YangMills.Construction
