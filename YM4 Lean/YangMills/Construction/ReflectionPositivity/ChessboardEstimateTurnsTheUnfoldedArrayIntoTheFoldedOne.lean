import YangMills.Construction.InfiniteLattice.FrameOfAMirrorVectorAndAdaptedPeriodGroups
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.ReflectionPositivity.CopiesOnTheSlabsAndTheFold
import YangMills.Construction.ReflectionPositivity.ParallelPartOfASplitPeriodLattice
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open InfiniteLattice
theorem mem_latticeSubgroup_of_mem_parallelPeriodLattice {n x : AmbientSpace}
    (hx : x ∈ parallelPeriodLattice n) : x ∈ latticeSubgroup 1 := by
  obtain ⟨m, hm⟩ := (AddSubgroup.mem_inf.mp hx).1
  refine ⟨fun μ => m μ * 2, fun μ => ?_⟩
  rw [hm μ]
  push_cast
  ring
namespace MirrorLadder
variable (L : MirrorLadder)
def parallelPoint (x : parallelPeriodLattice L.normal) : LatticePoint 1 :=
  ⟨x, mem_latticeSubgroup_of_mem_parallelPeriodLattice x.2⟩
def levelShift (k : ℤ) : LatticePoint 1 :=
  ⟨((k : ℝ) * (L.spacing : ℝ)) • firstNonzeroBasisVec L.normal, by
    have hk := zsmul_mem (firstNonzeroBasisVec_mem_latticeSubgroup L.normal) (k * L.spacing)
    rwa [← Int.cast_smul_eq_zsmul ℝ, Int.cast_mul] at hk⟩
def dualShift (i : ℤ) : LatticePoint 1 :=
  ⟨(2 * (i : ℝ) * (L.spacing : ℝ)) • dualVector L.normal, by
    have hi := zsmul_mem (two_smul_dualVector_mem_latticeSubgroup L.normal_mem) (i * L.spacing)
    rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_mul] at hi
    rwa [show 2 * (i : ℝ) * (L.spacing : ℝ) = (i : ℝ) * (L.spacing : ℝ) * 2 by ring]⟩
def axialPoint (x : parallelPeriodLattice L.normal) (k : ℤ) : LatticePoint 1 :=
  L.parallelPoint x + L.levelShift k
def normalPoint (x : parallelPeriodLattice L.normal) (i : ℤ) : LatticePoint 1 :=
  L.parallelPoint x + L.dualShift i
theorem axialPoint_mem_axialSublattice (x : parallelPeriodLattice L.normal) (k : ℤ) :
    L.axialPoint x k ∈ L.axialSublattice := by
  refine AddSubgroup.mem_addSubgroupOf.mpr (mem_axialPeriodLattice_iff.mpr ⟨x, x.2, k, ?_⟩)
  change _ = (x : AmbientSpace) + ((k : ℝ) * (L.spacing : ℝ)) • firstNonzeroBasisVec L.normal
  rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
theorem normalPoint_mem_normalSublattice (x : parallelPeriodLattice L.normal) (i : ℤ) :
    L.normalPoint x i ∈ L.normalSublattice := by
  refine AddSubgroup.mem_addSubgroupOf.mpr (mem_normalPeriodLattice_iff.mpr ⟨x, x.2, i, ?_⟩)
  change _ = (x : AmbientSpace) + (2 * (i : ℝ) * (L.spacing : ℝ)) • dualVector L.normal
  rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
  congr 2
  ring
variable (Γ : PeriodSublattice 1) (J : ℕ)
def transverseSubgroup : AddSubgroup (parallelPeriodLattice L.normal) :=
  (Γ.transversePart L.normal ((J : ℤ) * L.spacing)).addSubgroupOf (parallelPeriodLattice L.normal)
abbrev TransverseQuotient : Type := parallelPeriodLattice L.normal ⧸ L.transverseSubgroup Γ J
def UniqueRepresentation {I C : Type*} (point : parallelPeriodLattice L.normal → I → C) : Prop :=
  ∀ c : C, ∃! p : L.TransverseQuotient Γ J × I, ∀ x : parallelPeriodLattice L.normal,
    (x : L.TransverseQuotient Γ J) = p.1 → point x p.2 = c
variable {L}
variable (A : L.SlabZeroGenerator)
def SlabZeroGenerator.periodicTerm (x : parallelPeriodLattice L.normal) (k : ℤ) :
    Γ.QuotientField → ℂ :=
  Γ.periodize ((shift (L.axialPoint x k)).actOn A.toFun)
def SlabZeroGenerator.slabExp (t : ℝ) (k : ℤ) (U : Γ.QuotientField) : ℂ :=
  Complex.exp ((t : ℂ) * ∑ᶠ c : L.TransverseQuotient Γ J, A.periodicTerm Γ (Quotient.out c) k U)
def SlabZeroGenerator.axialClass (x : parallelPeriodLattice L.normal) (k : ℤ) :
    A.unfoldedArray.Cosets Γ :=
  ((⟨L.axialPoint x k, L.axialPoint_mem_axialSublattice x k⟩ : A.unfoldedArray.sublattice) :
    A.unfoldedArray.Cosets Γ)
def SlabZeroGenerator.normalClass (x : parallelPeriodLattice L.normal) (i : ℤ) :
    A.foldedArray.Cosets Γ :=
  ((⟨L.normalPoint x i, L.normalPoint_mem_normalSublattice x i⟩ : A.foldedArray.sublattice) :
    A.foldedArray.Cosets Γ)
variable (L)
structure IsAdaptedSlabDecomposition (w : ℤ) (S : SlabDecomposition) : Prop where
  normal_eq : S.normal = L.normal
  baseLevel_eq : S.baseLevel = L.offset
  width_eq : S.width = L.spacing
  admissible : AdmissibleParams L.spacing (S.count : ℤ) w
  three_le : 3 ≤ min ((S.count : ℤ) * L.spacing) w
  toAmbient_eq :
    S.period.toAmbient = adaptedLattice L.normal L.normal_mem L.spacing (S.count : ℤ) w
end MirrorLadder
def ChessboardFoldingEstimate : Prop :=
  ∀ (β : ℝ), 0 < β → ∀ (L : MirrorLadder) (A : L.SlabZeroGenerator) (w : ℤ)
    (S : SlabDecomposition), L.IsAdaptedSlabDecomposition w S →
    Finite (L.TransverseQuotient S.period S.count) ∧
    (∀ (k : ℤ) (x y : parallelPeriodLattice L.normal),
      (x : L.TransverseQuotient S.period S.count) = y →
        A.periodicTerm S.period x k = A.periodicTerm S.period y k) ∧
    ∀ t : ℝ, 0 ≤ t →
      let f : ℤ → S.period.QuotientField → ℂ := A.slabExp S.period S.count t
      let bound : ℝ := Real.exp (-(t * (Nat.card (L.TransverseQuotient S.period S.count) : ℝ) *
        TestFunctions.uniformNorm A.toFun))
      (∀ k : ℤ, f (k + 2 * (S.count : ℤ)) = f k) ∧
      (∀ k : ℤ, f k ∈ S.slabAlgebra k ∧ (∀ U, (f k U).im = 0) ∧
        bound ≤ ⨅ U, (f k U).re) ∧
      0 < bound ∧
      L.UniqueRepresentation S.period S.count
        (fun x (k : Fin (2 * S.count)) => A.axialClass S.period x ((k : ℕ) : ℤ)) ∧
      (fun U => ∏ k : ZMod (2 * S.count), f (k.val : ℤ) U) =
        (fun U => ((Real.exp (t * A.unfoldedArray.periodicSum S.period U) : ℝ) : ℂ)) ∧
      (∀ k : ℤ,
        f k = S.period.compPullback (shift (L.levelShift k)) (f 0) ∧
        (∀ j : ZMod (2 * S.count),
          S.slabCopy (k : ZMod (2 * S.count)) (j + (k : ZMod (2 * S.count))) (f k) =
            S.period.compPullback (shift (L.levelShift k)) (S.slabCopy 0 j (f 0))) ∧
        S.fold β (k : ZMod (2 * S.count)) (f k) = S.fold β 0 (f 0)) ∧
      L.UniqueRepresentation S.period S.count
        (fun x (i : Fin S.count) => A.normalClass S.period x ((i : ℕ) : ℤ)) ∧
      (fun U => ∏ j : ZMod (2 * S.count), S.slabCopy 0 j (f 0) U) =
        (fun U => ((Real.exp (t * A.foldedArray.periodicSum S.period U) : ℝ) : ℂ)) ∧
      A.unfoldedArray.tiltedPartition S.period β t ≤
        A.foldedArray.tiltedPartition S.period β t
end YangMills.Construction.NormalFamilies
