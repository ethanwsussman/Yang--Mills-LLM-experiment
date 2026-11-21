import YangMills.Construction.Lattice.LowerBoundsOfTheSiteOperators
import YangMills.Construction.Lattice.MinimumOverTheWeightsOfConsecutiveLevelsProof
import YangMills.Construction.Lattice.SymmetryOfTheDirichletSiteOperatorsProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators FiniteDimReal SeparatedSequences
noncomputable section
namespace SiteOperatorPositivity
section Abstract
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
end Abstract
section Inner
variable {L t : ℕ} {ι : Type}
theorem latticeInner_comm (f g : ι → ℝ) : latticeInner L t f g = latticeInner L t g f := by apply _root_.YangMills.Construction.SeparatedSequences.MassiveRelation.latticeInner_comm <;> assumption
end Inner
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus)
theorem L_pos_real : (0 : ℝ) < D.L := by apply _root_.YangMills.Construction.SeparatedSequences.LevelWeightMinimum.side_pos <;> assumption
theorem finestMesh_pos : 0 < finestMeshInLevelUnits D.L D.t := by apply _root_.YangMills.Construction.SeparatedSequences.OneExtensionProof.finestMesh_pos <;> assumption
theorem levelMeshRatio_pos (n : ℕ) : 0 < D.levelMeshRatio n := by apply _root_.YangMills.Construction.SeparatedSequences.OneExtensionProof.levelMeshRatio_pos <;> assumption
theorem finite_bareSite : Finite (BareSite D.L D.m D.K) :=
  BaseParameters.instFiniteLatticeSite D 0
theorem restrictedZeroInner_comm (f g : ↥(zeroFormsOn D.K (Ω 0))) :
    D.restrictedZeroInner Ω f g = D.restrictedZeroInner Ω g f :=
  latticeInner_comm _ _
theorem mem_cube_self {n : ℕ} (y : D.LatticeSite n) :
    (y : D.Torus) ∈ BaseParameters.cube (D := D) y := by
  change TorusMetric.torusSupNorm ((y : D.Torus) - (y : D.Torus)) ≤
    meshSize D.L (levelDepth D.K n) / 2
  rw [sub_self]
  have hsp : 0 < meshSize D.L (levelDepth D.K n) := zpow_pos (L_pos_real D) _
  have h0 : TorusMetric.torusSupNorm (0 : D.Torus) ≤ 0 := by
    refine csInf_le ⟨0, ?_⟩ ⟨0, ?_, ?_⟩
    · rintro _ ⟨v, -, rfl⟩
      exact (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
    · funext μ
      simp [TorusMetric.torusProj]
    · simp [TorusMetric.supNormVec]
  linarith
end SiteOperatorPositivity
end
end YangMills.Construction
