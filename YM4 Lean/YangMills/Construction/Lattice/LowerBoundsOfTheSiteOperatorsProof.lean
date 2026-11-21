import YangMills.Construction.Lattice.ClosedFormsWithVanishingAveragesAreDifferencesProof
import YangMills.Construction.Lattice.BoxLaplacianSpectralGap
import YangMills.Construction.Lattice.GeometryOfASeparatedSequenceProof
import YangMills.Construction.Lattice.LowerBoundsOfTheSiteOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators SeparatedSequences
  SeparatedSequences.BaseParameters
namespace SiteOperatorBounds
section Parameters
variable (E : BaseParameters)
theorem cast_L_pos : 0 < (E.L : ℝ) := by apply _root_.YangMills.Construction.SeparatedSequences.LevelWeightMinimum.side_pos <;> assumption
theorem levelMeshRatio_pos (n : ℕ) : 0 < E.levelMeshRatio n := zpow_pos (cast_L_pos E) _
instance instFintypeLatticeSite (n : ℕ) : Fintype (E.LatticeSite n) := Fintype.ofFinite _
variable {E}
def toBareSite {n : ℕ} (y : E.LatticeSite n) : BareSite E.L E.m E.K :=
  ⟨y, sublattice_mono (by have := E.three_le_L; omega) E.m
    (by simp only [levelDepth]; push_cast; omega) y.2⟩
def offsetSite {n : ℕ} (y : E.LatticeSite n) (a : Fin 4 → ℤ) : BareSite E.L E.m E.K :=
  toBareSite y + ∑ ν, a ν • unitStep E.L E.m (levelDepth E.K 0) ν
theorem coe_offsetSite {n : ℕ} (y : E.LatticeSite n) (a : Fin 4 → ℤ) :
    ((offsetSite y a : BareSite E.L E.m E.K) : E.Torus) =
      (y : E.Torus) +
        ∑ ν, a ν • ((unitStep E.L E.m (levelDepth E.K 0) ν : BareSite E.L E.m E.K) : E.Torus) := by
  simp [offsetSite, toBareSite]
theorem shiftedPoint_zero_eq (p : E.Torus) (a : Fin 4 → ℤ) :
    E.shiftedPoint 0 p a =
      p + ∑ ν, a ν • ((unitStep E.L E.m (levelDepth E.K 0) ν : BareSite E.L E.m E.K) : E.Torus) := by apply _root_.YangMills.Construction.SequenceGeometryProof.shiftedPoint_eq <;> assumption
variable (E) in
def halfSide (n : ℕ) : ℕ := E.L ^ n / 2
variable (E) in
theorem two_mul_halfSide_add_one (n : ℕ) : 2 * halfSide E n + 1 = E.L ^ n := by apply _root_.YangMills.Construction.PeriodicLattice.VanishingAverageGradients.two_mul_halfWidth_add_one <;> assumption
variable (E) in
def InCentredBox (n : ℕ) (a : Fin 4 → ℤ) : Prop :=
  ∀ ν, -(halfSide E n : ℤ) ≤ a ν ∧ a ν ≤ halfSide E n
theorem mem_boundedOffsets_iff {n : ℕ} (a : Fin 4 → ℤ) :
    a ∈ boundedOffsets (E.L ^ n) ↔ InCentredBox E n a := by apply _root_.YangMills.Construction.SequenceGeometryProof.mem_boundedOffsets_iff <;> assumption
theorem offsetSite_add_single {n : ℕ} (y : E.LatticeSite n) (a : Fin 4 → ℤ) (μ : Fin 4) (k : ℤ) :
    offsetSite y (a + Pi.single μ k) =
      offsetSite y a + k • unitStep E.L E.m (levelDepth E.K 0) μ := by
  unfold offsetSite
  rw [add_assoc]
  congr 1
  simp [add_smul, Finset.sum_add_distrib, Pi.single_apply, ite_smul]
variable (E) in
def centredOffset (n : ℕ) (k : Fin 4 → Fin (E.L ^ n)) : Fin 4 → ℤ :=
  fun ν => ((k ν : ℕ) : ℤ) - (halfSide E n : ℤ)
theorem centredOffset_injective {n : ℕ} : Function.Injective (centredOffset E n) := by
  intro k k' h
  funext ν
  have h1 := congrFun h ν
  simp only [centredOffset] at h1
  exact Fin.ext (by omega)
def forwardBondEnergy (f : ZeroForms E.L E.m E.K) (x : BareSite E.L E.m E.K) : ℝ :=
  ∑ μ, (f (x + unitStep E.L E.m (levelDepth E.K 0) μ) - f x) ^ 2
theorem latticeInner_eq_sum (f g : ZeroForms E.L E.m E.K) :
    latticeInner E.L E.t f g = E.levelMeshRatio 0 ^ 4 * ∑ x, f x * g x := by
  rw [latticeInner, finsum_eq_sum_of_fintype, E.levelMeshRatio_zero]
theorem latticeInner_comm (f g : ZeroForms E.L E.m E.K) :
    latticeInner E.L E.t f g = latticeInner E.L E.t g f := by
  simp only [latticeInner_eq_sum, mul_comm (f _)]
theorem latticeInner_sum (f : ZeroForms E.L E.m E.K) (g : Fin 4 → ZeroForms E.L E.m E.K) :
    latticeInner E.L E.t f (∑ μ, g μ) = ∑ μ, latticeInner E.L E.t f (g μ) := by
  simp only [latticeInner_eq_sum, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
theorem latticeInner_forwardDifference_self (μ : Fin 4) (f : ZeroForms E.L E.m E.K) :
    latticeInner E.L E.t (forwardDifference E.t μ f) (forwardDifference E.t μ f) =
      E.levelMeshRatio 0 ^ 2 *
        ∑ x, (f (x + unitStep E.L E.m (levelDepth E.K 0) μ) - f x) ^ 2 := by
  have hξ := (levelMeshRatio_pos E 0).ne'
  rw [latticeInner_eq_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [forwardDifference, ← E.levelMeshRatio_zero]
  field_simp
theorem latticeInner_scalarLaplacian (hDO : BareLatticeOperators.Statement)
    (f : ZeroForms E.L E.m E.K) :
    latticeInner E.L E.t f (scalarLaplacian E.L E.m E.K E.t f) =
      E.levelMeshRatio 0 ^ 2 * ∑ x, forwardBondEnergy f x := by
  obtain ⟨hadj, hform, -⟩ := hDO E
  rw [hform.2.2.1 f, latticeInner_sum]
  have h1 : ∀ μ, latticeInner E.L E.t f (forwardDifferenceAdjoint E.t μ (forwardDifference E.t μ f)) =
      E.levelMeshRatio 0 ^ 2 *
        ∑ x, (f (x + unitStep E.L E.m (levelDepth E.K 0) μ) - f x) ^ 2 := by
    intro μ
    rw [latticeInner_comm, ← hadj.1 μ f (forwardDifference E.t μ f),
      latticeInner_forwardDifference_self]
  simp only [h1, forwardBondEnergy]
  rw [← Finset.mul_sum, Finset.sum_comm]
end Parameters
section Blocks
def boxSite {E : BaseParameters} {n : ℕ} (y : E.LatticeSite n)
    (k : Fin 4 → Fin (E.L ^ n)) : BareSite E.L E.m E.K :=
  offsetSite y (centredOffset E n k)
variable (D : SequenceDatum) (H : LatticeCubeStatement)
include H in
theorem fineBlock_eq_image {n : ℕ} (hn : n ≤ D.t) (y : D.LatticeSite n) :
    fineBlock (D := D.toBaseParameters) y =
        D.shiftedPoint 0 (y : D.Torus) '' boundedOffsets (D.L ^ n) ∧
      InjOn (D.shiftedPoint 0 (y : D.Torus)) (boundedOffsets (D.L ^ n)) := by apply _root_.YangMills.Construction.SequenceGeometryProof.fineBlock_eq_image <;> assumption
include H in
theorem mem_fineBlock_iff {n : ℕ} (hn : n ≤ D.t) (y : D.LatticeSite n)
    (x : BareSite D.L D.m D.K) :
    (x : D.Torus) ∈ fineBlock (D := D.toBaseParameters) y ↔
      ∃ a, InCentredBox D.toBaseParameters n a ∧ x = offsetSite y a := by
  rw [(fineBlock_eq_image D H hn y).1]
  constructor
  · rintro ⟨a, ha, hx⟩
    refine ⟨a, (mem_boundedOffsets_iff a).1 ha, Subtype.ext ?_⟩
    rw [coe_offsetSite, ← hx, shiftedPoint_zero_eq]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (mem_boundedOffsets_iff a).2 ha, by rw [shiftedPoint_zero_eq, coe_offsetSite]⟩
variable {D}
variable (D)
include H in
theorem mem_fineBlock_self {n : ℕ} (hn : n ≤ D.t) (y : D.LatticeSite n) :
    (y : D.Torus) ∈ fineBlock (D := D.toBaseParameters) y := by
  have h := (mem_fineBlock_iff D H hn y (toBareSite y)).2
    ⟨0, fun ν => by simp, by simp [offsetSite]⟩
  exact h
variable {D}
end Blocks
section Numbers
variable (E : BaseParameters)
theorem blockSpectralGap_eq_cast (n : ℕ) :
    blockSpectralGap E n =
      4 * ((E.L ^ n : ℕ) : ℝ) ^ 2 * Real.sin (Real.pi / (2 * ((E.L ^ n : ℕ) : ℝ))) ^ 2 := by
  simp only [blockSpectralGap]
  push_cast
  rw [pow_mul']
theorem four_le_blockSpectralGap (hGap : Lattice.BoxLaplacianGap.BoxLaplacianSpectralGap)
    (n : ℕ) : 4 ≤ blockSpectralGap E n := by
  rw [blockSpectralGap_eq_cast]
  exact (hGap (E.L ^ n) (Nat.one_le_pow _ _ (by have := E.three_le_L; omega))).2.1
end Numbers
section Bounds
variable (D : SequenceDatum) (H : LatticeCubeStatement)
  (hGap : Lattice.BoxLaplacianGap.BoxLaplacianSpectralGap)
end Bounds
end SiteOperatorBounds
end YangMills.Construction
end
