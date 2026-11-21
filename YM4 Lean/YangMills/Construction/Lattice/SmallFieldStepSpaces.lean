import YangMills.Construction.Lattice.LieValuedBondFunctions
import Mathlib
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m K : ℕ} {j : ℤ}
abbrev bareSiteInner (k : ℕ) (f g : SiteAtLevel L m K 0 → ComplexMatrix2) : ℂ :=
  siteInner (finestMeshInLevelUnits L k) f g
abbrev bareBondFormInner (k : ℕ) (A B : BondAtLevel L m K 0 → ComplexMatrix2) : ℂ :=
  bondFormInner (finestMeshInLevelUnits L k) A B
def lieBondFunctionInner (β γ : LieBondFunction L m j) : ℂ :=
  ∑ᶠ c : PositivelyOrientedBond L m j, halfTracePairing (β c) (γ c)
def compactBondForms (L m : ℕ) (j : ℤ) : Submodule ℝ (Bond L m j → ComplexMatrix2) where
  carrier := {A | IsBondForm compactLieAlgebra A}
  add_mem' := by
    rintro A B ⟨hA, hAr⟩ ⟨hB, hBr⟩
    refine ⟨fun b hb => ComplexMatrix2.hermitianTraceless.add_mem (hA b hb) (hB b hb), fun b => ?_⟩
    simp only [Pi.add_apply, hAr, hBr, neg_add]
  zero_mem' := ⟨fun _ _ => ComplexMatrix2.hermitianTraceless.zero_mem, fun _ => by simp⟩
  smul_mem' := by
    rintro r A ⟨hA, hAr⟩
    refine ⟨fun b hb => ComplexMatrix2.hermitianTraceless.smul_mem r (hA b hb), fun b => ?_⟩
    simp only [Pi.smul_apply, hAr, smul_neg]
def compactSiteFields (L m : ℕ) (j : ℤ) : Submodule ℝ (Site L m j → ComplexMatrix2) where
  carrier := {f | IsSiteField compactLieAlgebra f}
  add_mem' := fun hf hg x => ComplexMatrix2.hermitianTraceless.add_mem (hf x) (hg x)
  zero_mem' := fun _ => ComplexMatrix2.hermitianTraceless.zero_mem
  smul_mem' := fun r _ hf x => ComplexMatrix2.hermitianTraceless.smul_mem r (hf x)
def compactLieBondFunctions (L m : ℕ) (j : ℤ) : Submodule ℝ (LieBondFunction L m j) where
  carrier := {a | a.IsCompactValued}
  add_mem' := fun ha hb b => ComplexMatrix2.hermitianTraceless.add_mem (ha b) (hb b)
  zero_mem' := fun _ => ComplexMatrix2.hermitianTraceless.zero_mem
  smul_mem' := fun r a ha b => by
    have h : (((r • a) b : ↥ComplexMatrix2.traceless) : ComplexMatrix2) =
        r • (a b : ComplexMatrix2) := by
      ext i l
      simp
    change (((r • a) b : ↥ComplexMatrix2.traceless) : ComplexMatrix2) ∈
      ComplexMatrix2.hermitianTraceless
    rw [h]
    exact ComplexMatrix2.hermitianTraceless.smul_mem r (ha b)
abbrev bareBondFormSpace (L m K : ℕ) : Submodule ℝ (BondAtLevel L m K 0 → ComplexMatrix2) :=
  compactBondForms L m (levelDepth K 0)
abbrev bareSiteFieldSpace (L m K : ℕ) : Submodule ℝ (SiteAtLevel L m K 0 → ComplexMatrix2) :=
  compactSiteFields L m (levelDepth K 0)
abbrev lieBondSpaceAtLevel (L m K k : ℕ) :
    Submodule ℝ (LieBondFunction L m (levelDepth K k)) :=
  compactLieBondFunctions L m (levelDepth K k)
abbrev siteFieldSpaceAtLevel (L m K k : ℕ) :
    Submodule ℝ (SiteAtLevel L m K k → ComplexMatrix2) :=
  compactSiteFields L m (levelDepth K k)
abbrev lieBondSpaceAtNextLevel (L m K k : ℕ) :
    Submodule ℝ (LieBondFunction L m (levelDepth K (k + 1))) :=
  compactLieBondFunctions L m (levelDepth K (k + 1))
abbrev bareBondFormSpaceInner (k : ℕ) (A B : bareBondFormSpace L m K) : ℂ :=
  bareBondFormInner k A.1 B.1
abbrev bareSiteFieldSpaceInner (k : ℕ) (f g : bareSiteFieldSpace L m K) : ℂ :=
  bareSiteInner k f.1 g.1
abbrev lieBondSpaceInner {k : ℕ} (β γ : lieBondSpaceAtLevel L m K k) : ℂ :=
  lieBondFunctionInner β.1 γ.1
section Calculus
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable [TopologicalSpace E] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
def IsC2Between (D : Set E) (D' : Set F) (h : E → F) : Prop :=
  IsOpen D ∧ IsOpen D' ∧ MapsTo h D D' ∧ DifferentiableOn ℝ h D ∧
    DifferentiableOn ℝ (fderiv ℝ h) D ∧ ContinuousOn (fderiv ℝ (fderiv ℝ h)) D
abbrev firstFDeriv (h : E → F) (x : E) : E →L[ℝ] F := fderiv ℝ h x
abbrev secondFDeriv (h : E → F) (x : E) : E →L[ℝ] E →L[ℝ] F := fderiv ℝ (fderiv ℝ h) x
def IsOpenIntervalAroundZero (I : Set ℝ) : Prop := IsOpen I ∧ I.OrdConnected ∧ (0 : ℝ) ∈ I
def IsTwiceDiffCurve (I : Set ℝ) (c : ℝ → F) : Prop :=
  IsOpenIntervalAroundZero I ∧ DifferentiableOn ℝ c I ∧ DifferentiableAt ℝ (deriv c) 0
end Calculus
end YangMills.Construction.PeriodicLattice
