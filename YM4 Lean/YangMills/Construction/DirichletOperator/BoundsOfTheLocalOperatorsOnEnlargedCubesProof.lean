import YangMills.Construction.DirichletOperator.BoundsOfACubeTermOnADivergenceProof
import YangMills.Construction.Torus.ProjSmallCubes
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.CubeTorus (torusSetting levelSpacing tensorModulusAt TensorAnchorSupported)
open YangMills.Construction.CubeOperators (RegularityConstants cubeDivOne cubeDivTwo IsCubeScale
  cutoffSize sourceSize chosenConstants)
noncomputable section
namespace YangMills.Construction.EnlargedCubeBounds.Assembly
structure SubadditiveNorm {V : Type} [AddCommMonoid V] (N : V → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ N v
  map_zero_le : N 0 ≤ 0
  map_add_le : ∀ v w, N (v + w) ≤ N v + N w
theorem SubadditiveNorm.comp {V W : Type} [AddCommMonoid V] [AddCommMonoid W] {N : W → ℝ}
    (h : SubadditiveNorm N) {T : V → W} (h₀ : T 0 = 0) (ha : ∀ v w, T (v + w) = T v + T w) :
    SubadditiveNorm fun v => N (T v) :=
  ⟨fun _ => h.nonneg _, by simpa [h₀] using h.map_zero_le, fun v w => by
    rw [ha]
    exact h.map_add_le _ _⟩
theorem SubadditiveNorm.const_mul {V : Type} [AddCommMonoid V] {N : V → ℝ} (h : SubadditiveNorm N)
    {a : ℝ} (ha : 0 ≤ a) : SubadditiveNorm fun v => a * N v :=
  ⟨fun v => mul_nonneg ha (h.nonneg v), mul_nonpos_of_nonneg_of_nonpos ha h.map_zero_le, fun v w => by
    have := mul_le_mul_of_nonneg_left (h.map_add_le v w) ha
    linarith⟩
section Lattice
variable {𝒯 : YangMills.Construction.RegionSequence.NestedRegions}
theorem finite_fineBond (hl : TorusLengthsStatement)
    (𝒯 : YangMills.Construction.RegionSequence.NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem bondInner_comm (A B : 𝒯.FineBond → ℝ) : bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem bondInner_add_left [Finite 𝒯.FineBond] (A B g : 𝒯.FineBond → ℝ) :
    bondInner (A + B) g = bondInner A g + bondInner B g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.bondInner_add_left <;> assumption
theorem eq_of_bondInner_eq [Finite 𝒯.FineBond] (F : Submodule ℝ (𝒯.FineBond → ℝ))
    {X Y : 𝒯.FineBond → ℝ} (hX : X ∈ F) (hY : Y ∈ F)
    (h : ∀ v ∈ F, bondInner X v = bondInner Y v) : X = Y := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.eq_of_bondInner_eq <;> assumption
theorem nablaOne_add (A B : 𝒯.FineBond → ℝ) : nablaOne (A + B) = nablaOne A + nablaOne B := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.nablaOne_add <;> assumption
theorem nablaTwo_add (J K : 𝒯.Tensor 1) : nablaTwo (J + K) = nablaTwo J + nablaTwo K := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.nablaTwo_add <;> assumption
theorem bondLap_add (A B : 𝒯.FineBond → ℝ) : bondLap (A + B) = bondLap A + bondLap B := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.bondLap_add <;> assumption
theorem divOne_add (J J' : 𝒯.Tensor 1) : divOne (J + J') = divOne J + divOne J' := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.divOne_add <;> assumption
theorem le_holderBond [Finite 𝒯.FineBond] (α lam : ℝ) (f : 𝒯.FineBond → ℝ) {b b' : 𝒯.FineBond}
    (hd : b.dir = b'.dir) (h₀ : 0 < siteLOneDist b.source b'.source)
    (h₁ : siteLOneDist b.source b'.source ≤ lam) :
    (lam / siteLOneDist b.source b'.source) ^ α * ‖f b' - f b‖ ≤ holderBond α lam f := by apply _root_.YangMills.Construction.CubeTermBounds.le_holderBond <;> assumption
theorem holderBond_nonneg (α lam : ℝ) (f : 𝒯.FineBond → ℝ) : 0 ≤ holderBond α lam f := by apply _root_.YangMills.Construction.FirstTypeGreenRegularity.holderBond_nonneg <;> assumption
theorem supSite_nonneg (f : 𝒯.FineSite → ℝ) : 0 ≤ supSite f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem ltwoBond_eq_sqrt [Fintype 𝒯.FineBond] (f : 𝒯.FineBond → ℝ) :
    ltwoBond f = √(∑ b, (𝒯.ξ ^ 2 * f b) * (𝒯.ξ ^ 2 * f b)) := by
  simp only [ltwoBond, bondL2, bondInner]
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by ring
theorem ltwoTensor_eq_sqrt [Fintype 𝒯.FineBond] {r : ℕ} (J : 𝒯.Tensor r) :
    ltwoTensor J =
      √(∑ i : (Fin r → Fin 4) × 𝒯.FineBond, (𝒯.ξ ^ 2 * J i.1 i.2) * (𝒯.ξ ^ 2 * J i.1 i.2)) := by
  simp only [ltwoTensor, tensorL2, tensorInner, bondInner]
  rw [Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring
def cornerShift (lam : ℝ) (i : Fin 4 → Fin 4) : Fin 4 → ℝ :=
  fun μ => (2 * ((i μ : ℕ) : ℝ) - 3) * lam
def shiftedCenter (o : 𝒯.Point) (lam : ℝ) (i : Fin 4 → Fin 4) : 𝒯.Point :=
  o + torusProj 4 𝒯.side (cornerShift lam i)
open Classical in
def cellIndex (o : 𝒯.Point) (lam : ℝ) (b : 𝒯.FineBond) : Fin 4 → Fin 4 :=
  if h : ∃ i, AnchoredIn (cubeHalfSide (shiftedCenter o lam i) lam) b then h.choose else 0
def cellRestrict (o : 𝒯.Point) (lam : ℝ) (k : Fin 4 → Fin 4) (f : 𝒯.FineBond → ℝ) :
    𝒯.FineBond → ℝ :=
  indicator {b | cellIndex o lam b = k} f
end Lattice
section Operators
variable {𝒮 : YangMills.Construction.RegionSequence.NestedRegions} {M : ℕ}
theorem levelSpacing_pos (Q : LevelCube 𝒮 M) : 0 < levelSpacing Q := by
  have hL : (0 : ℝ) < 𝒮.L := by
    have := 𝒮.thirteen_le_L
    exact_mod_cast (by omega : 0 < 𝒮.L)
  simp only [levelSpacing, YangMills.Construction.RegionSequence.NestedRegions.scale, scaleSpacing,
    zpow_natCast]
  exact mul_pos (pow_pos hL _) 𝒮.ξ_pos
structure PieceData (c : RegularityConstants) (Q : LevelCube 𝒮 M) : Prop where
  finite : Finite Q.system.setting.FineBond
  holds : c.CubeHolds Q
  restrict_mem : ∀ (o : Q.system.setting.Point) (lam : ℝ) (k : Fin 4 → Fin 4)
    {A : Q.system.setting.FineBond → ℝ}, A ∈ Q.system.forms → cellRestrict o lam k A ∈ Q.system.forms
  divOne_mem : ∀ J, cubeDivOne Q J ∈ Q.system.forms
  divOne_add : ∀ J J', cubeDivOne Q (J + J') = cubeDivOne Q J + cubeDivOne Q J'
  divTwo_mem : ∀ J, cubeDivTwo Q J ∈ Q.system.forms
  divTwo_add : ∀ J J', cubeDivTwo Q (J + J') = cubeDivTwo Q J + cubeDivTwo Q J'
namespace PieceData
variable {c : RegularityConstants} {Q : LevelCube 𝒮 M}
theorem inv_mem_forms (R : PieceData c Q) {u : Q.system.setting.FineBond → ℝ}
    (hu : u ∈ Q.system.forms) : Q.system.inv u ∈ Q.system.forms := by
  obtain ⟨g, hg, rfl⟩ := R.holds.invertible.surjOn hu
  exact (Classical.epsilon_spec
    (p := fun g' => g' ∈ (Q.system.forms : Set (Q.system.setting.FineBond → ℝ)) ∧
      Q.system.op g' = Q.system.op g) ⟨g, hg, rfl⟩).1
end PieceData
section Members
variable {𝒯 : YangMills.Construction.RegionSequence.NestedRegions}
end Members
end Operators
end YangMills.Construction.EnlargedCubeBounds.Assembly
