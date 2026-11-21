import YangMills.Construction.Towers.ConfigurationsFormedLevelByLevelOnThePolydiscs
import YangMills.Construction.Towers.KernelsOfTheScaledOperatorsAtEveryComplexConfiguration
import YangMills.Construction.Towers.RelationsAtEveryComplexConfigurationOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.RelationsOfTheCovariantIteratesOfTheWholeLattice
import YangMills.Construction.Towers.RelationsOfTheIteratedAveragesOfTheScaledPictureOnASideProof
import YangMills.Construction.Towers.RelationsOfTheIteratedAveragesOfTheScaledPictureOnTheWhole
import YangMills.Construction.Towers.TheBackgroundKernelAtZero
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IterRelations
open YangMills.Construction.Matrices (ComplexMatrix2)
open YangMills.Construction.PeriodicOperators (KernelMatrix applyKernel compKernel unitKernel Represents
  RowFinite ColumnFinite ApplySummable CompSummable KernelUnique swapKernel HasFiniteSupport)
open YangMills.Construction.Tower.RescaledConditions (CoreRelations complementProj gaugeFixedKernel)
section Kernels
variable {N N' : Type}
theorem applyKernel_smul (T : KernelMatrix N N') (z : ℂ) (f : N → ℂ) :
    applyKernel T (z • f) = z • applyKernel T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_smul <;> assumption
theorem smul_applyKernel (T : KernelMatrix N N') (z : ℂ) (f : N → ℂ) :
    applyKernel (z • T) f = z • applyKernel T f := by apply _root_.YangMills.Construction.Tower.FullSpace.ComplexFieldRescaledRelations.applyKernel_smul_kernel <;> assumption
theorem applyKernel_hasFiniteSupport {T : KernelMatrix N N'} (hT : ColumnFinite T) {v : N → ℂ}
    (hv : HasFiniteSupport v) : HasFiniteSupport (applyKernel T v) := by
  refine (Set.Finite.biUnion hv fun i _ => hT i).subset ?_
  intro i' h
  by_contra hn
  apply h
  have hzero : ∀ i, T i' i * v i = 0 := by
    intro i
    by_cases hvi : v i = 0
    · simp [hvi]
    · have hT0 : T i' i = 0 := by
        by_contra h'
        exact hn (mem_biUnion (show i ∈ Function.support v from hvi) h')
      simp [hT0]
  show ∑' i, T i' i * v i = 0
  simp [hzero]
theorem unitKernel_apply (f : N → ℂ) : applyKernel (unitKernel N) f = f := by apply _root_.YangMills.Construction.Tower.IterRelationsOnTorus.applyKernel_unit <;> assumption
theorem sub_applyKernel {T S : KernelMatrix N N'} {f : N → ℂ} (hT : ApplySummable T f)
    (hS : ApplySummable S f) :
    applyKernel (T - S) f = applyKernel T f - applyKernel S f := by
  funext i'
  have h₁ : Summable fun i => T i' i * f i := Summable.of_norm (hT i')
  have h₂ : Summable fun i => S i' i * f i := Summable.of_norm (hS i')
  show ∑' i, (T i' i - S i' i) * f i = ∑' i, T i' i * f i - ∑' i, S i' i * f i
  rw [← h₁.tsum_sub h₂]
  exact tsum_congr fun i => sub_mul _ _ _
end Kernels
section Values
theorem real_smul_eq_complex_smul {ι : Type} (z : ℝ) (f : ι → ComplexMatrix2) :
    z • f = (z : ℂ) • f := by apply _root_.YangMills.SharedProofs.p7664 <;> assumption
variable {S S' : PairedFunctionSpace} {m : (S.index → ComplexMatrix2) → S'.index → ComplexMatrix2}
theorem transposeOfValues_mem {g : S'.index → ComplexMatrix2} (hg : g ∈ S'.complexSubmodule) :
    PairedFunctionSpace.transposeOfValues S S' m g ∈ S.complexSubmodule := by apply _root_.YangMills.Construction.Tower.CovDiffTransposes.transposeOfValues_mem <;> assumption
theorem transposeOfValues_smul (z : ℂ) {g : S'.index → ComplexMatrix2}
    (hg : g ∈ S'.complexSubmodule) :
    PairedFunctionSpace.transposeOfValues S S' m (z • g) =
      z • PairedFunctionSpace.transposeOfValues S S' m g := by apply _root_.YangMills.Construction.Tower.IterRelationsOnTorus.transposeOfValues_smul <;> assumption
theorem transposeOfValues_real_smul (z : ℝ) {g : S'.index → ComplexMatrix2}
    (hg : g ∈ S'.complexSubmodule) :
    PairedFunctionSpace.transposeOfValues S S' m (z • g) =
      z • PairedFunctionSpace.transposeOfValues S S' m g := by
  rw [real_smul_eq_complex_smul, real_smul_eq_complex_smul, transposeOfValues_smul _ hg]
theorem mem_of_transposeExists (h : KernelAtZeroSources.TransposeExists S S' m)
    {l : S.index → ComplexMatrix2} (hl : l ∈ S.complexSubmodule) : m l ∈ S'.complexSubmodule := by
  have e : m l = _ := (h.1 ⟨l, hl⟩).symm
  rw [e]
  exact Subtype.coe_prop _
theorem real_smul_of_transposeExists (h : KernelAtZeroSources.TransposeExists S S' m) (z : ℝ)
    {l : S.index → ComplexMatrix2} (hl : l ∈ S.complexSubmodule) : m (z • l) = z • m l := by
  have hz : (z : ℂ) • l ∈ S.complexSubmodule := S.complexSubmodule.smul_mem _ hl
  have e₁ : m ((z : ℂ) • l) = _ := (h.1 ⟨(z : ℂ) • l, hz⟩).symm
  have e₂ : (⟨(z : ℂ) • l, hz⟩ : S.complexSubmodule) = (z : ℂ) • ⟨l, hl⟩ := rfl
  rw [e₂, map_smul] at e₁
  have e₃ : (PairedFunctionSpace.linearOfValues S S' m ⟨l, hl⟩ : S'.index → ComplexMatrix2) = m l :=
    h.1 ⟨l, hl⟩
  rw [real_smul_eq_complex_smul, real_smul_eq_complex_smul, e₁]
  exact congrArg (fun x => (z : ℂ) • x) e₃
end Values
structure IsPauliCoordinate (r : PauliComponentsOfSymmetricKernel) : Prop where
  ofCoeffs_mem : ∀ c, r.ofCoeffs c ∈ r.space.complexSubmodule
  coeffs_ofCoeffs : ∀ c, r.coeffs (r.ofCoeffs c) = c
  ofCoeffs_coeffs : ∀ f ∈ r.space.complexSubmodule, r.ofCoeffs (r.coeffs f) = f
  real_homogeneous : ScalarMultipleKernels.CoeffsRealHomogeneous r
theorem IsPauliCoordinate.real_smul_mem {r : PauliComponentsOfSymmetricKernel} (z : ℝ)
    {f : r.space.index → ComplexMatrix2} (hf : f ∈ r.space.complexSubmodule) :
    z • f ∈ r.space.complexSubmodule := by
  rw [real_smul_eq_complex_smul]
  exact r.space.complexSubmodule.smul_mem _ hf
def gaugeFixingMap (r₀ b₀ r : PauliComponentsOfSymmetricKernel) (lam : ℝ)
    (Dm : (r₀.space.index → ComplexMatrix2) → b₀.space.index → ComplexMatrix2)
    (Rm : (r₀.space.index → ComplexMatrix2) → r.space.index → ComplexMatrix2)
    (B : b₀.space.index → ComplexMatrix2) : r₀.space.index → ComplexMatrix2 :=
  PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm B -
    lam • PairedFunctionSpace.transposeOfValues r₀.space r.space Rm
      (Rm (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm B))
structure RelationData (r₀ b₀ r b : PauliComponentsOfSymmetricKernel)
    (p : RescaledOperators r₀.Place b₀.Place r.Place b.Place)
    (Dm : (r₀.space.index → ComplexMatrix2) → b₀.space.index → ComplexMatrix2)
    (Qm : (b₀.space.index → ComplexMatrix2) → b.space.index → ComplexMatrix2)
    (Rm : (r₀.space.index → ComplexMatrix2) → r.space.index → ComplexMatrix2)
    (Wm : (r.space.index → ComplexMatrix2) → b.space.index → ComplexMatrix2)
    (DW : KernelMatrix (Fin 3 × r.Place) (Fin 3 × b.Place))
    (background : (b₀.space.index → ComplexMatrix2) → (b₀.space.index → ComplexMatrix2) → ℂ)
    (w : ℝ) : Prop where
  algebra : RescaledKernelAlgebra.Claim
  multiples : ScalarMultipleKernels.Statement
  products : PeriodicOperators.RowFiniteKernels.Claim
  hr₀ : IsPauliCoordinate r₀
  hb₀ : IsPauliCoordinate b₀
  hr : IsPauliCoordinate r
  hb : IsPauliCoordinate b
  eta_pos : 0 < p.eta
  coarse_pos : 0 < p.coarse
  D_eq : p.D = r₀.kernel b₀ fun l => p.eta⁻¹ • Dm l
  Q_eq : p.Q = b₀.kernel b fun B => p.eta • Qm B
  R_eq : p.R = r₀.kernel r Rm
  DW_eq : DW = r.kernel b Wm
  hD : PauliComponentsOfSymmetricKernel.HasLocalKernel r₀ b₀ Dm
  hQ : PauliComponentsOfSymmetricKernel.HasLocalKernel b₀ b Qm
  hR : PauliComponentsOfSymmetricKernel.HasLocalKernel r₀ r Rm
  hW : PauliComponentsOfSymmetricKernel.HasLocalKernel r b Wm
  one_D : KernelUnique r₀.Index b₀.Index
  one_Q : KernelUnique b₀.Index b.Index
  one_R : KernelUnique r₀.Index r.Index
  one_QD : KernelUnique r₀.Index b.Index
  one_RR : KernelUnique r.Index r.Index
  H_rowFinite : RowFinite p.H
  D_mem : ∀ l ∈ r₀.space.complexSubmodule, Dm l ∈ b₀.space.complexSubmodule
  R_mem : ∀ l ∈ r₀.space.complexSubmodule, Rm l ∈ r.space.complexSubmodule
  R_smul : ∀ (z : ℝ), ∀ l ∈ r₀.space.complexSubmodule, Rm (z • l) = z • Rm l
  comm : ∀ l ∈ r₀.space.complexSubmodule, Qm (Dm l) = Wm (Rm l)
  R_unit : ∀ g ∈ r.space.complexSubmodule,
    Rm (PairedFunctionSpace.transposeOfValues r₀.space r.space Rm g) = w • g
  unit_scale : p.coarse ^ 4 * (p.eta ^ 4)⁻¹ * w = 1
  site_sub : ∀ c c', r₀.ofCoeffs (c - c') = r₀.ofCoeffs c - r₀.ofCoeffs c'
  site_pairing : ∀ c c', HasFiniteSupport c' →
    r₀.space.pair (r₀.ofCoeffs c) (r₀.ofCoeffs c') = ∑ᶠ i, c i * c' i
  bond_finite : ∀ f ∈ b₀.space.complexSubmodule, b₀.space.IsFinitelySupported f →
    HasFiniteSupport (b₀.coeffs f)
  background_formula : ∀ b' ∈ b₀.space.complexSubmodule, b₀.space.IsFinitelySupported b' →
    background (p.eta • b') (p.eta • b') =
      PeriodicOperators.wPairing (meshWeight p.eta) (b₀.coeffs b')
          (applyKernel p.H (b₀.coeffs b')) +
        r₀.space.pair (gaugeFixingMap r₀ b₀ r (p.coarse ^ 4 * (p.eta ^ 4)⁻¹) Dm Rm (p.eta • b'))
          (gaugeFixingMap r₀ b₀ r (p.coarse ^ 4 * (p.eta ^ 4)⁻¹) Dm Rm (p.eta • b'))
namespace RelationData
variable {r₀ b₀ r b : PauliComponentsOfSymmetricKernel} {p : RescaledOperators r₀.Place b₀.Place r.Place b.Place}
  {Dm : (r₀.space.index → ComplexMatrix2) → b₀.space.index → ComplexMatrix2}
  {Qm : (b₀.space.index → ComplexMatrix2) → b.space.index → ComplexMatrix2}
  {Rm : (r₀.space.index → ComplexMatrix2) → r.space.index → ComplexMatrix2}
  {Wm : (r.space.index → ComplexMatrix2) → b.space.index → ComplexMatrix2}
  {DW : KernelMatrix (Fin 3 × r.Place) (Fin 3 × b.Place)}
  {background : (b₀.space.index → ComplexMatrix2) → (b₀.space.index → ComplexMatrix2) → ℂ}
  {w : ℝ} (S : RelationData r₀ b₀ r b p Dm Qm Rm Wm DW background w)
include S
theorem Q_eq_smul_kernel : p.Q = (p.eta : ℂ) • b₀.kernel b Qm := by
  rw [S.Q_eq]
  exact (S.multiples b₀ b Qm S.hb.real_homogeneous S.hQ S.one_Q p.eta 1 1).1
theorem D_eq_smul_kernel : p.D = ((p.eta⁻¹ : ℝ) : ℂ) • r₀.kernel b₀ Dm := by
  rw [S.D_eq]
  exact (S.multiples r₀ b₀ Dm S.hb₀.real_homogeneous S.hD S.one_D p.eta⁻¹ 1 1).1
theorem Dt_eq_smul_swap : p.Dt = ((p.eta⁻¹ : ℝ) : ℂ) • swapKernel (r₀.kernel b₀ Dm) := by
  have h := (S.multiples r₀ b₀ Dm S.hb₀.real_homogeneous S.hD S.one_D p.eta⁻¹ p.eta p.eta).2
  have e : p.eta⁻¹ * (p.eta ^ 4 * (p.eta ^ 4)⁻¹) = p.eta⁻¹ := by
    have := S.eta_pos.ne'
    field_simp
  rw [e] at h
  show meshTranspose p.eta p.eta p.D = _
  rw [S.D_eq]
  exact h
theorem Rt_eq_smul_swap :
    p.Rt = ((p.coarse ^ 4 * (p.eta ^ 4)⁻¹ : ℝ) : ℂ) • swapKernel (r₀.kernel r Rm) := by
  have h := (S.multiples r₀ r Rm S.hr.real_homogeneous S.hR S.one_R (1 : ℝ) p.eta p.coarse).2
  simp only [one_smul, one_mul] at h
  show meshTranspose p.eta p.coarse p.R = _
  rw [S.R_eq]
  exact h
theorem D_rowFinite : RowFinite p.D := by
  rw [S.D_eq_smul_kernel]
  exact S.hD.smul_row_finite _
theorem Q_rowFinite : RowFinite p.Q := by
  rw [S.Q_eq_smul_kernel]
  exact S.hQ.smul_row_finite _
theorem R_rowFinite : RowFinite p.R := by
  rw [S.R_eq]
  exact S.hR.row_finite
theorem DW_rowFinite : RowFinite DW := by
  rw [S.DW_eq]
  exact S.hW.row_finite
theorem Dt_rowFinite : RowFinite p.Dt := by
  rw [S.Dt_eq_smul_swap]
  exact S.hD.smul_swap_row_finite _
theorem Rt_rowFinite : RowFinite p.Rt := by
  rw [S.Rt_eq_smul_swap]
  exact S.hR.smul_swap_row_finite _
theorem R_columnFinite : ColumnFinite p.R := by
  rw [S.R_eq]
  exact S.hR.column_finite
theorem Dt_columnFinite : ColumnFinite p.Dt := by
  rw [S.Dt_eq_smul_swap]
  exact S.hD.smul_swap_column_finite _
theorem Rt_columnFinite : ColumnFinite p.Rt := by
  rw [S.Rt_eq_smul_swap]
  exact S.hR.smul_swap_column_finite _
theorem apply_R (f : r₀.Index → ℂ) :
    applyKernel p.R f = r.coeffs (Rm (r₀.ofCoeffs f)) := by
  rw [S.R_eq]
  exact (S.hR.represents f).2
theorem apply_Dt (f : b₀.Index → ℂ) :
    applyKernel p.Dt f = ((p.eta⁻¹ : ℝ) : ℂ) • r₀.coeffs
      (PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm (b₀.ofCoeffs f)) := by
  rw [S.Dt_eq_smul_swap]
  exact (S.hD.smul_swap_represents _ f).2
theorem apply_Rt (f : r.Index → ℂ) :
    applyKernel p.Rt f = ((p.coarse ^ 4 * (p.eta ^ 4)⁻¹ : ℝ) : ℂ) • r₀.coeffs
      (PairedFunctionSpace.transposeOfValues r₀.space r.space Rm (r.ofCoeffs f)) := by
  rw [S.Rt_eq_smul_swap]
  exact (S.hR.smul_swap_represents _ f).2
theorem R_comp_Rt : compKernel p.R p.Rt = unitKernel (Fin 3 × r.Place) := by
  have hprod := (S.products.1 _ _ p.Rt S.Rt_rowFinite).2 _ p.R S.R_rowFinite
  have hU := S.products.2.2.1 (Fin 3 × r.Place)
  refine S.one_RR (fun f => f) _ _ (fun f => ⟨(hprod.2.2 f).1, ?_⟩)
    (fun f => ⟨(S.products.1 _ _ _ hU.1).1 f, unitKernel_apply f⟩)
  have hg := S.hr.ofCoeffs_mem f
  have hm := transposeOfValues_mem (S := r₀.space) (m := Rm) hg
  rw [(hprod.2.2 f).2.2, S.apply_Rt, applyKernel_smul, S.apply_R, S.hr₀.ofCoeffs_coeffs _ hm,
    S.R_unit _ hg, S.hr.real_homogeneous, S.hr.coeffs_ofCoeffs, smul_smul, ← Complex.ofReal_mul,
    S.unit_scale]
  simp
theorem Q_comp_D : compKernel p.Q p.D = compKernel DW p.R := by
  have h₁ := (S.products.1 _ _ p.D S.D_rowFinite).2 _ p.Q S.Q_rowFinite
  have h₂ := (S.products.1 _ _ p.R S.R_rowFinite).2 _ DW S.DW_rowFinite
  refine S.one_QD (r₀.mapOnCoeffs b fun l => Qm (Dm l)) _ _
    (fun f => ⟨(h₁.2.2 f).1, ?_⟩) (fun f => ⟨(h₂.2.2 f).1, ?_⟩)
  · have hl := S.hr₀.ofCoeffs_mem f
    have e : (p.eta : ℂ) * ((p.eta⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ S.eta_pos.ne']
      simp
    rw [(h₁.2.2 f).2.2, S.Q_eq_smul_kernel, S.D_eq_smul_kernel, smul_applyKernel,
      smul_applyKernel, applyKernel_smul, smul_smul, e, one_smul, (S.hD.represents f).2,
      (S.hQ.represents _).2]
    show b.coeffs (Qm (b₀.ofCoeffs (b₀.coeffs (Dm (r₀.ofCoeffs f))))) = _
    rw [S.hb₀.ofCoeffs_coeffs _ (S.D_mem _ hl)]
    rfl
  · have hl := S.hr₀.ofCoeffs_mem f
    rw [(h₂.2.2 f).2.2, S.apply_R, S.DW_eq, (S.hW.represents _).2]
    show b.coeffs (Wm (r.ofCoeffs (r.coeffs (Rm (r₀.ofCoeffs f))))) =
      b.coeffs (Qm (Dm (r₀.ofCoeffs f)))
    rw [S.hr.ofCoeffs_coeffs _ (S.R_mem _ hl), S.comm _ hl]
theorem projectionConsequences : RescaledKernelAlgebra.ProjectionConsequences p :=
  S.algebra _ _ _ _ p S.eta_pos S.coarse_pos
    ⟨S.D_rowFinite, S.Dt_rowFinite, S.R_rowFinite, S.Rt_rowFinite, S.H_rowFinite⟩ S.R_comp_Rt
theorem gaugeFixingMap_smul_eq {b' : b₀.space.index → ComplexMatrix2}
    (hb' : b' ∈ b₀.space.complexSubmodule) :
    gaugeFixingMap r₀ b₀ r (p.coarse ^ 4 * (p.eta ^ 4)⁻¹) Dm Rm (p.eta • b') =
      r₀.ofCoeffs (((p.eta ^ 2 : ℝ) : ℂ) • applyKernel (complementProj p)
        (applyKernel p.Dt (b₀.coeffs b'))) := by
  have hη := S.eta_pos.ne'
  set lam : ℝ := p.coarse ^ 4 * (p.eta ^ 4)⁻¹ with hlam
  set s := PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm b' with hs
  have hsm : s ∈ r₀.space.complexSubmodule := transposeOfValues_mem hb'
  set v := applyKernel p.Dt (b₀.coeffs b') with hv
  have hv' : v = ((p.eta⁻¹ : ℝ) : ℂ) • r₀.coeffs s := by
    rw [hv, S.apply_Dt, S.hb₀.ofCoeffs_coeffs _ hb']
  set l : r₀.space.index → ComplexMatrix2 := p.eta⁻¹ • s with hl
  have hlm : l ∈ r₀.space.complexSubmodule := IsPauliCoordinate.real_smul_mem _ hsm
  have hvl : r₀.coeffs l = v := by
    rw [hv', hl]
    exact S.hr₀.real_homogeneous _ _
  have hlv : r₀.ofCoeffs v = l := by
    rw [← hvl]
    exact S.hr₀.ofCoeffs_coeffs _ hlm
  have hRl := S.R_mem l hlm
  set y := PairedFunctionSpace.transposeOfValues r₀.space r.space Rm (Rm l) with hy
  have hym : y ∈ r₀.space.complexSubmodule := transposeOfValues_mem hRl
  have hRv : applyKernel p.R v = r.coeffs (Rm l) := by
    rw [S.apply_R, hlv]
  have hprod := (S.products.1 _ _ p.R S.R_rowFinite).2 _ p.Rt S.Rt_rowFinite
  have hPv : applyKernel (compKernel p.Rt p.R) v = (lam : ℂ) • r₀.coeffs y := by
    rw [(hprod.2.2 v).2.2, hRv, S.apply_Rt, S.hr.ofCoeffs_coeffs _ hRl]
  have hU := S.products.2.2.1 (Fin 3 × r₀.Place)
  have hu : applyKernel (complementProj p) v = v - (lam : ℂ) • r₀.coeffs y := by
    show applyKernel (unitKernel (Fin 3 × r₀.Place) - compKernel p.Rt p.R) v = _
    rw [sub_applyKernel ((S.products.1 _ _ _ hU.1).1 v) (hprod.2.2 v).1, unitKernel_apply, hPv]
  have hly : l - lam • y ∈ r₀.space.complexSubmodule :=
    r₀.space.complexSubmodule.sub_mem hlm (IsPauliCoordinate.real_smul_mem _ hym)
  have hm : r₀.ofCoeffs (applyKernel (complementProj p) v) = l - lam • y := by
    have e : (lam : ℂ) • r₀.coeffs y = r₀.coeffs (lam • y) := (S.hr₀.real_homogeneous _ _).symm
    rw [hu, S.site_sub, hlv, e, S.hr₀.ofCoeffs_coeffs _ (IsPauliCoordinate.real_smul_mem _ hym)]
  have hcol : r₀.coeffs (l - lam • y) = applyKernel (complementProj p) v := by
    rw [← hm, S.hr₀.coeffs_ofCoeffs]
  have hfinal : r₀.ofCoeffs (((p.eta ^ 2 : ℝ) : ℂ) • applyKernel (complementProj p) v) =
      (p.eta ^ 2) • (l - lam • y) := by
    rw [← hcol, ← S.hr₀.real_homogeneous]
    exact S.hr₀.ofCoeffs_coeffs _ (IsPauliCoordinate.real_smul_mem _ hly)
  rw [hfinal]
  have hDT : PairedFunctionSpace.transposeOfValues r₀.space b₀.space Dm (p.eta • b') =
      (p.eta ^ 2) • l := by
    rw [transposeOfValues_real_smul _ hb', hl, smul_smul]
    congr 1
    field_simp
  unfold gaugeFixingMap
  rw [hDT, S.R_smul _ _ hlm, transposeOfValues_real_smul _ hRl, smul_sub, smul_comm lam]
theorem background_smul_eq {b' : b₀.space.index → ComplexMatrix2}
    (hb' : b' ∈ b₀.space.complexSubmodule) (hf : b₀.space.IsFinitelySupported b') :
    background (p.eta • b') (p.eta • b') =
      PeriodicOperators.wPairing (meshWeight p.eta) (b₀.coeffs b')
        (applyKernel (gaugeFixedKernel p) (b₀.coeffs b')) := by
  have C := S.projectionConsequences
  have hc := S.bond_finite _ hb' hf
  set v := applyKernel p.Dt (b₀.coeffs b') with hv
  have hvf : HasFiniteSupport v := applyKernel_hasFiniteSupport S.Dt_columnFinite hc
  have hprod := (S.products.1 _ _ p.R S.R_rowFinite).2 _ p.Rt S.Rt_rowFinite
  have hU := S.products.2.2.1 (Fin 3 × r₀.Place)
  have hu : applyKernel (complementProj p) v = v - applyKernel p.Rt (applyKernel p.R v) := by
    show applyKernel (unitKernel (Fin 3 × r₀.Place) - compKernel p.Rt p.R) v = _
    rw [sub_applyKernel ((S.products.1 _ _ _ hU.1).1 v) (hprod.2.2 v).1, unitKernel_apply,
      (hprod.2.2 v).2.2]
  have hPf : HasFiniteSupport (applyKernel p.Rt (applyKernel p.R v)) :=
    applyKernel_hasFiniteSupport S.Rt_columnFinite
      (applyKernel_hasFiniteSupport S.R_columnFinite hvf)
  set u := applyKernel (complementProj p) v with hudef
  have huf : HasFiniteSupport u := by
    rw [hu]
    exact (hvf.union hPf).subset (Function.support_sub _ _)
  have hzf : HasFiniteSupport (((p.eta ^ 2 : ℝ) : ℂ) • u) :=
    huf.subset fun i h h0 => h (by simp [show u i = 0 from h0])
  rw [S.background_formula _ hb' hf, S.gaugeFixingMap_smul_eq hb', S.site_pairing _ _ hzf,
    C.pairing_eq _ hc]
  congr 1
  have hs : (Function.support fun i => ((meshWeight p.eta i : ℝ) : ℂ) * (u i * u i)).Finite :=
    huf.subset fun i h h0 => h (by simp [show u i = 0 from h0])
  unfold PeriodicOperators.wPairing
  rw [tsum_eq_finsum hs]
  refine finsum_congr fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul, meshWeight]
  push_cast
  ring
theorem coreRelations : CoreRelations r₀ b₀ r b p Dm Qm Rm Wm DW background := by
  have C := S.projectionConsequences
  have hprod₁ := (S.products.1 _ _ p.Rt S.Rt_rowFinite).2 _ p.R S.R_rowFinite
  have hprod₂ := (S.products.1 _ _ p.D S.D_rowFinite).2 _ p.Q S.Q_rowFinite
  have hprod₃ := (S.products.1 _ _ p.R S.R_rowFinite).2 _ DW S.DW_rowFinite
  refine ⟨S.R_comp_Rt, S.Q_comp_D, fun b' hb' hf => S.background_smul_eq hb' hf, ?_, ?_, ?_, ?_,
    ⟨S.R_rowFinite, S.Q_rowFinite, S.D_rowFinite, S.DW_rowFinite, S.Rt_rowFinite,
      S.Dt_rowFinite⟩,
    ⟨hprod₁.1, hprod₂.1, hprod₃.1, C.proj_summable⟩, C.complementProj_row_finite,
    C.comp_assoc⟩
  · rw [S.R_eq]
    exact S.hR.represents
  · have e : (b₀.mapOnCoeffs b fun B' => p.eta • Qm B') =
        (p.eta : ℂ) • b₀.mapOnCoeffs b Qm :=
      funext fun f => S.hb.real_homogeneous _ _
    rw [e, S.Q_eq_smul_kernel]
    exact S.hQ.smul_represents _
  · have e : (r₀.mapOnCoeffs b₀ fun l => (p.eta)⁻¹ • Dm l) =
        ((p.eta⁻¹ : ℝ) : ℂ) • r₀.mapOnCoeffs b₀ Dm :=
      funext fun f => S.hb₀.real_homogeneous _ _
    rw [e, S.D_eq_smul_kernel]
    exact S.hD.smul_represents _
  · rw [S.DW_eq]
    exact S.hW.represents
end RelationData
section Coefficients
theorem sum_smul_pauli_mem_traceless (x : Fin 3 → ℂ) :
    ∑ a, x a • ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem pauliCoeff_real_smul (z : ℝ) (a : Fin 3) (X : ComplexMatrix2) :
    pauliCoeff a (z • X) = (z : ℂ) * pauliCoeff a X := by apply _root_.YangMills.Construction.Tower.IterTransposesOnTorus.pauliCoeff_real_smul <;> assumption
theorem toPauliCoeffs_real_smul {σ : Type} (z : ℝ) (f : σ → ComplexMatrix2) :
    toPauliCoeffs (z • f) = (z : ℂ) • toPauliCoeffs f :=
  funext fun i => pauliCoeff_real_smul z i.1 (f i.2)
theorem halfTrace_mul_sums (hP : OneLoop.PauliMatrixRelations) (x y : Fin 3 → ℂ) :
    ComplexMatrix2.halfTrace
        ((∑ a, x a • ComplexMatrix2.pauliFamily a) * ∑ a, y a • ComplexMatrix2.pauliFamily a) =
      ∑ a, x a * y a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.halfTrace_mul_sums <;> assumption
variable {σ : Type}
theorem toPauliCoeffs_ofPauliCoeffs (c : Fin 3 × σ → ℂ) :
    toPauliCoeffs (ofPauliCoeffs c) = c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.toPauliCoeffs_ofPauliCoeffs <;> assumption
theorem ofPauliCoeffs_sub (c c' : Fin 3 × σ → ℂ) :
    ofPauliCoeffs (c - c') = ofPauliCoeffs c - ofPauliCoeffs c' :=
  funext fun i => by
    simp [ofPauliCoeffs, sub_smul, Finset.sum_sub_distrib]
theorem traceFinsumPairing_ofPauliCoeffs (hP : OneLoop.PauliMatrixRelations)
    (a b : Fin 3 × σ → ℂ) (hs : (Function.support fun i => a i * b i).Finite) :
    traceFinsumPairing (ofPauliCoeffs a) (ofPauliCoeffs b) = ∑ᶠ i, a i * b i := by
  unfold traceFinsumPairing
  have e : ∀ i, ComplexMatrix2.halfTrace (ofPauliCoeffs a i * ofPauliCoeffs b i) =
      ∑ c, a (c, i) * b (c, i) := fun i =>
    halfTrace_mul_sums hP (fun c => a (c, i)) (fun c => b (c, i))
  simp only [e]
  have e₂ : ∑ᶠ i, a i * b i = ∑ c : Fin 3, ∑ᶠ i, a (c, i) * b (c, i) := by
    rw [finsum_curry _ hs]
    exact finsum_eq_sum_of_fintype _
  rw [e₂]
  refine finsum_sum_comm _ _ fun c _ => ?_
  have hinj : Function.Injective fun i : σ => (c, i) := fun i i' h => (Prod.ext_iff.1 h).2
  exact hs.preimage hinj.injOn
theorem vertexCoordinate_isCoordinateProjection (σ : Type) : IsPauliCoordinate (vertexCoordinate σ) where
  ofCoeffs_mem c := fun i _ => sum_smul_pauli_mem_traceless fun a => c (a, i)
  coeffs_ofCoeffs c := toPauliCoeffs_ofPauliCoeffs c
  ofCoeffs_coeffs _ hf := funext fun i => sum_pauliCoeff_smul (hf i (mem_univ i))
  real_homogeneous z f := toPauliCoeffs_real_smul z f
end Coefficients
section Forms
variable {L k j : ℕ}
def extendByZero (c : Fin 3 × PositiveEdge (meshAt L k j) → ℂ) :
    InfiniteLattice.Link (meshAt L k j) → ComplexMatrix2 :=
  open Classical in fun e => if h : e.IsPositivelyOriented then ofPauliCoeffs c ⟨e, h⟩ else 0
theorem edgePauliCoordinates_ofCoeffs_eq (c : Fin 3 × PositiveEdge (meshAt L k j) → ℂ) :
    (edgePauliCoordinates L k j).ofCoeffs c = extendOddly (extendByZero (L := L) (k := k) (j := j) c) :=
  rfl
theorem restrict_edgeEval_ofCoeffs (c : Fin 3 × PositiveEdge (meshAt L k j) → ℂ) :
    restrictToPositiveEdges ((edgePauliCoordinates L k j).ofCoeffs c) = ofPauliCoeffs c := by
  funext e
  have he : e.1.IsPositivelyOriented := e.2
  rw [edgePauliCoordinates_ofCoeffs_eq]
  show extendOddly (extendByZero (L := L) (k := k) (j := j) c) e.1 = _
  simp only [extendOddly, extendByZero, if_pos he, dif_pos he]
theorem edgePauliCoordinates_ofCoeffs_mem (hL : 0 < meshAt L k j)
    (c : Fin 3 × PositiveEdge (meshAt L k j) → ℂ) :
    (edgePauliCoordinates L k j).ofCoeffs c ∈ (edgePauliCoordinates L k j).space.complexSubmodule := by
  rw [edgePauliCoordinates_ofCoeffs_eq]
  refine ⟨fun e he => ?_, fun e => ?_⟩
  · have h := congrFun (restrict_edgeEval_ofCoeffs (L := L) (k := k) (j := j) c) ⟨e, he⟩
    have h' : extendOddly (extendByZero (L := L) (k := k) (j := j) c) e =
        ofPauliCoeffs c ⟨e, he⟩ := h
    rw [h']
    exact sum_smul_pauli_mem_traceless fun a => c (a, ⟨e, he⟩)
  · have hx := InfiniteLattice.xor_mem_positiveLinks hL e
    rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have p₁ : e.IsPositivelyOriented := InfiniteLattice.mem_positiveLinks_iff.1 h₁
      have p₂ : ¬ e.opposite.IsPositivelyOriented :=
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)
      simp only [extendOddly, if_pos p₁, if_neg p₂]
      rfl
    · have p₁ : e.opposite.IsPositivelyOriented := InfiniteLattice.mem_positiveLinks_iff.1 h₁
      have p₂ : ¬ e.IsPositivelyOriented :=
        fun h => h₂ (InfiniteLattice.mem_positiveLinks_iff.2 h)
      simp only [extendOddly, if_pos p₁, if_neg p₂, neg_neg]
theorem edgePauliCoordinates_isCoordinateRepr (hL : 0 < meshAt L k j) :
    IsPauliCoordinate (edgePauliCoordinates L k j) where
  ofCoeffs_mem c := edgePauliCoordinates_ofCoeffs_mem hL c
  coeffs_ofCoeffs c :=
    (congrArg toPauliCoeffs (restrict_edgeEval_ofCoeffs c)).trans (toPauliCoeffs_ofPauliCoeffs c)
  ofCoeffs_coeffs B hB := by
    have hpos : ∀ e (he : e.IsPositivelyOriented),
        (edgePauliCoordinates L k j).ofCoeffs ((edgePauliCoordinates L k j).coeffs B) e = B e := by
      intro e he
      have h := congrFun (restrict_edgeEval_ofCoeffs ((edgePauliCoordinates L k j).coeffs B)) ⟨e, he⟩
      have h' : (edgePauliCoordinates L k j).ofCoeffs ((edgePauliCoordinates L k j).coeffs B) e =
          ofPauliCoeffs (toPauliCoeffs (restrictToPositiveEdges B)) ⟨e, he⟩ := h
      rw [h']
      exact sum_pauliCoeff_smul (hB.1 e he)
    funext e
    by_cases he : e.IsPositivelyOriented
    · exact hpos e he
    · have hx := InfiniteLattice.xor_mem_positiveLinks hL e
      have hr : e.opposite.IsPositivelyOriented := by
        rcases hx with ⟨h₁, _⟩ | ⟨h₁, _⟩
        · exact absurd (InfiniteLattice.mem_positiveLinks_iff.1 h₁) he
        · exact InfiniteLattice.mem_positiveLinks_iff.1 h₁
      have e₁ := (edgePauliCoordinates_ofCoeffs_mem hL ((edgePauliCoordinates L k j).coeffs B)).2 e
      have e₂ : B e.opposite = -B e := hB.2 e
      rw [hpos _ hr, e₂] at e₁
      exact (neg_injective e₁).symm
  real_homogeneous z f := toPauliCoeffs_real_smul z (restrictToPositiveEdges f)
end Forms
section TowerLevels
variable {L k : ℕ}
open YangMills.Construction.Tower.HessianKernel (IsSymmBilinearOn finiteSupportComplexForms)
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
theorem bilinear_smul_smul {α : Type} {𝒮 : Set (α → ComplexMatrix2)}
    {Q : (α → ComplexMatrix2) → (α → ComplexMatrix2) → ℂ}
    (hQ : IsSymmBilinearOn 𝒮 Q) (h0 : (0 : α → ComplexMatrix2) ∈ 𝒮) (z : ℂ)
    {E : α → ComplexMatrix2} (hE : E ∈ 𝒮) (hz : z • E ∈ 𝒮) :
    Q (z • E) (z • E) = z ^ 2 * Q E E := by
  have l0 : ∀ X ∈ 𝒮, Q 0 X = 0 := fun X hX => by
    have h := (hQ 1 0 h0 0 h0 X hX).1
    simpa using h
  have r0 : ∀ X ∈ 𝒮, Q X 0 = 0 := fun X hX => by
    have h := (hQ 1 0 h0 0 h0 X hX).2.1
    simpa using h
  have e₁ := (hQ z E hE 0 h0 (z • E) hz).1
  have e₂ := (hQ z E hE 0 h0 E hE).2.1
  rw [add_zero, l0 _ hz, add_zero] at e₁
  rw [add_zero, r0 _ hE, add_zero] at e₂
  rw [e₁, e₂]
  ring
theorem edgePauliCoordinates_coeffs_finite {b' : Edge L k 0 → ComplexMatrix2}
    (hf : HasFiniteSupp (restrictToPositiveEdges b')) :
    HasFiniteSupport ((edgePauliCoordinates L k 0).coeffs b') := by
  refine (Set.Finite.prod (Set.finite_univ (α := Fin 3)) hf).subset ?_
  rintro ⟨a, i⟩ h
  refine ⟨mem_univ a, fun h0 => h ?_⟩
  show pauliCoeff a (restrictToPositiveEdges b' i) = 0
  rw [show restrictToPositiveEdges b' i = 0 from h0, pauliCoeff_zero]
theorem hessian_smul_eq (hP : OneLoop.PauliMatrixRelations)
    (hη : 0 < meshAt L k 0) {U : Edge L k 0 → ComplexMatrix2}
    (hbil : IsSymmBilinearOn (finiteSupportComplexForms L k 0) (complexActionHessian U))
    (hop : ∀ B ∈ finiteSupportComplexForms L k 0, ∀ B' ∈ finiteSupportComplexForms L k 0,
      finiteEdgePairing B (complexHessianOperator U B') = complexActionHessian U B B')
    (hH : Represents (rescaledOperators L k U).H (((finestMesh L k : ℂ) ^ 2)⁻¹ •
      (edgePauliCoordinates L k 0).mapOnCoeffs (edgePauliCoordinates L k 0) (complexHessianOperator U)))
    {b' : Edge L k 0 → ComplexMatrix2} (hb' : b' ∈ complexEdgeForms (meshAt L k 0))
    (hf : HasFiniteSupp (restrictToPositiveEdges b')) :
    complexActionHessian U (finestMesh L k • b') (finestMesh L k • b') =
      PeriodicOperators.wPairing (meshWeight (finestMesh L k)) ((edgePauliCoordinates L k 0).coeffs b')
        (applyKernel (rescaledOperators L k U).H ((edgePauliCoordinates L k 0).coeffs b')) := by
  have hB : IsPauliCoordinate (edgePauliCoordinates L k 0) := edgePauliCoordinates_isCoordinateRepr hη
  have hc := edgePauliCoordinates_coeffs_finite hf
  set c := (edgePauliCoordinates L k 0).coeffs b' with hcdef
  have hbc : (edgePauliCoordinates L k 0).ofCoeffs c = b' := hB.ofCoeffs_coeffs _ hb'
  have hpc : restrictToPositiveEdges b' = ofPauliCoeffs c := by
    conv_lhs => rw [← hbc]
    exact restrict_edgeEval_ofCoeffs c
  have hmem : b' ∈ finiteSupportComplexForms L k 0 :=
    ⟨hb', (hf.image Subtype.val).subset fun e h => ⟨⟨e, h.1⟩, h.2, rfl⟩⟩
  have h0 : (0 : Edge L k 0 → ComplexMatrix2) ∈ finiteSupportComplexForms L k 0 :=
    ⟨(complexEdgeForms (meshAt L k 0)).zero_mem,
      Set.finite_empty.subset fun e h => absurd rfl h.2⟩
  have hz : (finestMesh L k : ℂ) • b' ∈ finiteSupportComplexForms L k 0 :=
    ⟨(complexEdgeForms (meshAt L k 0)).smul_mem _ hb',
      hmem.2.subset fun e h => ⟨h.1, fun h' => h.2 (by simp [h'])⟩⟩
  have hz0 : (finestMesh L k : ℂ) ≠ 0 := by
    have : finestMesh L k ≠ 0 := hη.ne'
    exact_mod_cast this
  set y := applyKernel (complexHessianKernel U) c with hy
  have hA : complexHessianOperator U b' = (edgePauliCoordinates L k 0).ofCoeffs y := rfl
  have hx : applyKernel (rescaledOperators L k U).H c = ((finestMesh L k : ℂ) ^ 2)⁻¹ • y := by
    rw [(hH c).2]
    show ((finestMesh L k : ℂ) ^ 2)⁻¹ • (edgePauliCoordinates L k 0).coeffs
      (complexHessianOperator U ((edgePauliCoordinates L k 0).ofCoeffs c)) = _
    rw [hbc, hA]
    exact congrArg _ (hB.coeffs_ofCoeffs y)
  have hs : (Function.support fun i => c i * y i).Finite :=
    hc.subset fun i h h' => h (by simp [show c i = 0 from h'])
  have hpair : finiteEdgePairing b' (complexHessianOperator U b') = ∑ᶠ i, c i * y i := by
    show traceFinsumPairing (restrictToPositiveEdges b')
      (restrictToPositiveEdges (complexHessianOperator U b')) = _
    have hy' : restrictToPositiveEdges (complexHessianOperator U b') = ofPauliCoeffs y :=
      restrict_edgeEval_ofCoeffs (L := L) (k := k) (j := 0) y
    rw [hy', hpc]
    exact traceFinsumPairing_ofPauliCoeffs hP c y hs
  rw [real_smul_eq_complex_smul, bilinear_smul_smul hbil h0 _ hmem hz, ← hop _ hmem _ hmem, hpair]
  refine Eq.trans ?_
    (congrArg (PeriodicOperators.wPairing (meshWeight (finestMesh L k)) c) hx).symm
  have hs₂ : (Function.support fun i => ((meshWeight (finestMesh L k) i : ℝ) : ℂ) *
      (c i * (((finestMesh L k : ℂ) ^ 2)⁻¹ • y) i)).Finite :=
    hc.subset fun i h h' => h (by simp [show c i = 0 from h'])
  unfold PeriodicOperators.wPairing
  rw [tsum_eq_finsum hs₂, mul_finsum]
  refine finsum_congr fun i => ?_
  have e : (((finestMesh L k : ℂ) ^ 2)⁻¹ • y) i = ((finestMesh L k : ℂ) ^ 2)⁻¹ * y i := rfl
  have hw : ((meshWeight (finestMesh L k) i : ℝ) : ℂ) = (finestMesh L k : ℂ) ^ 4 := by
    simp [meshWeight]
  have key : ∀ z w u v v' : ℂ, z ≠ 0 → w = z ^ 4 → v' = (z ^ 2)⁻¹ * v →
      z ^ 2 * (u * v) = w * (u * v') := by
    intro z w u v v' hz h₁ h₂
    subst h₁ h₂
    field_simp
  exact key _ _ _ _ _ hz0 hw e
end TowerLevels
section Assembly
variable {L k : ℕ}
theorem coarse_pow_div_finest_pow (L k : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) :
    meshAt L k k ^ 4 * (finestMesh L k ^ 4)⁻¹ = (L : ℝ) ^ (4 * k) := by
  have e₁ : meshAt L k k = 1 := by simp [meshAt]
  have e₂ : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := by
    simp [finestMesh, meshAt, zpow_neg, zpow_natCast]
  rw [e₁, e₂, one_pow, one_mul, inv_pow, inv_inv, ← pow_mul, mul_comm]
theorem pow_mul_inv_pow_eq_one (L k : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) :
    (L : ℝ) ^ (4 * k) * ((L : ℝ) ^ (-4 : ℤ)) ^ k = 1 := by
  have h0 : (L : ℝ) ≠ 0 := by
    have := hL.2
    have : 0 < L := by omega
    exact_mod_cast this.ne'
  have e : ((L : ℝ) ^ (-4 : ℤ)) = ((L : ℝ) ^ 4)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  rw [e, inv_pow, ← pow_mul]
  exact mul_inv_cancel₀ (pow_ne_zero _ h0)
theorem inverseFourthPowerWeight_pow (L k : ℕ) :
    PeriodicLattice.inverseFourthPowerWeight L ^ k = ((((L : ℝ) ^ (-4 : ℤ)) ^ k : ℝ) : ℂ) := by
  unfold PeriodicLattice.inverseFourthPowerWeight
  push_cast
  rfl
theorem relationData (hAlg : RescaledKernelAlgebra.Claim)
    (hMul : ScalarMultipleKernels.Statement)
    (hProd : PeriodicOperators.RowFiniteKernels.Claim)
    (hKer : ThreeMapKernels.Claim)
    (hCov : CovariantIterRelations)
    (hEvery : ComplexFieldRescaledRelations.Statement)
    (hScaled : RescaledKernels.KernelsWellFormedEverywhere)
    (hSecond : HessianKernel.KernelProperties)
    (hBack : KernelAtZeroSources.ZeroSourceKernel)
    (hForm : IteratedMeans.IteratedMeansHold)
    (hP : OneLoop.PauliMatrixRelations)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {U : Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ smallIterateFields L k) :
    RelationData (vertexCoordinate (Vertex L k 0)) (edgePauliCoordinates L k 0) (vertexCoordinate (Vertex L k k))
      (edgePauliCoordinates L k k) (rescaledOperators L k U) (covDiff U)
      (iterCovariantDeriv L k U k) (iterAdjointCubeAverage L k U k)
      (covDiff (complexIter L k k U))
      (covDiffKernel L k k (complexIter L k k U))
      (backgroundForm L k U) (((L : ℝ) ^ (-4 : ℤ)) ^ k) := by
  have hWc : complexIter L k k U ∈ fieldsValuedIn L k k PeriodicLattice.complexGaugeGroup := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact (hForm L hL (m + 1) hk).2.meanStep_mem m (Nat.lt_succ_self m) _
      (hU.2 m (Nat.lt_succ_self m))
  have hK := (hKer L hL k hk).2
  have hTF := hBack L hL k hk U hU
  have hTD := hTF.1
  have hTR := hTF.2.1
  have hC := hCov L hL k k le_rfl U hU
  have hpairs := hK.1 0 k (Nat.zero_le k) le_rfl
  have hS := hSecond L hL k 0 (Nat.zero_le k)
  have hE := hEvery L hL k hk U hU.1
  have hlam : (rescaledOperators L k U).coarse ^ 4 * ((rescaledOperators L k U).eta ^ 4)⁻¹ =
      (L : ℝ) ^ (4 * k) := coarse_pow_div_finest_pow L k hL
  have hgauge : ∀ B, gaugeFixingMap (vertexCoordinate (Vertex L k 0)) (edgePauliCoordinates L k 0)
      (vertexCoordinate (Vertex L k k))
      ((rescaledOperators L k U).coarse ^ 4 * ((rescaledOperators L k U).eta ^ 4)⁻¹)
      (covDiff U) (iterAdjointCubeAverage L k U k) B = gaugeFixingTerm L k U B := by
    intro B
    rw [hlam]
    rfl
  refine
    { algebra := hAlg
      multiples := hMul
      products := hProd
      hr₀ := vertexCoordinate_isCoordinateProjection _
      hb₀ := edgePauliCoordinates_isCoordinateRepr (meshAt_pos hL k 0)
      hr := vertexCoordinate_isCoordinateProjection _
      hb := edgePauliCoordinates_isCoordinateRepr (meshAt_pos hL k k)
      eta_pos := meshAt_pos hL k 0
      coarse_pos := meshAt_pos hL k k
      D_eq := rfl
      Q_eq := rfl
      R_eq := rfl
      DW_eq := rfl
      hD := hK.2.1 U hU.1
      hQ := (hK.2.2.2 U hU).1
      hR := (hK.2.2.2 U hU).2
      hW := hK.2.2.1 _ hWc
      one_D := (hK.1 0 0 (Nat.zero_le k) (Nat.zero_le k)).2.1
      one_Q := hpairs.2.2.2
      one_R := hpairs.1
      one_QD := hpairs.2.1
      one_RR := (hK.1 k k le_rfl le_rfl).1
      H_rowFinite := ((hScaled L hL k hk).2 U hU.1).H_rowFinite
      D_mem := fun l hl => mem_of_transposeExists hTD hl
      R_mem := fun l hl => mem_of_transposeExists hTR hl
      R_smul := fun z l hl => real_smul_of_transposeExists hTR z hl
      comm := ?_
      R_unit := ?_
      unit_scale := ?_
      site_sub := fun c c' => ofPauliCoeffs_sub c c'
      site_pairing := fun c c' hf => traceFinsumPairing_ofPauliCoeffs hP c c'
        (hf.subset fun i h h' => h (by simp [show c' i = 0 from h']))
      bond_finite := fun f _ hf => edgePauliCoordinates_coeffs_finite hf
      background_formula := ?_ }
  · intro l hl
    exact (hC.2.1 l fun x => hl x (mem_univ x)).2 |>.trans rfl
  · intro g hg
    obtain ⟨T, hT₁, _, hT₃⟩ := hC.2.2
    have hTe : T = PairedFunctionSpace.linearOfValues (pairedFunctions (Vertex L k 0))
        (pairedFunctions (Vertex L k k)) (iterAdjointCubeAverage L k U k) :=
      LinearMap.ext fun f => Subtype.ext ((hT₁ f).trans (hTR.1 f).symm)
    have h₃ := hT₃ ⟨g, hg⟩
    rw [hT₁, hTe] at h₃
    unfold PairedFunctionSpace.transposeOfValues
    rw [dif_pos hg]
    refine h₃.trans ?_
    rw [inverseFourthPowerWeight_pow, real_smul_eq_complex_smul]
    rfl
  · rw [hlam]
    exact pow_mul_inv_pow_eq_one L k hL
  · intro b' hb' hf
    have hh := hS.2 U hU.1
    have h₁ := hessian_smul_eq hP (meshAt_pos hL k 0) hh.1 hh.2.2.2.2.1 hE.2.1 hb' hf
    rw [hgauge]
    show complexActionHessian U (finestMesh L k • b') (finestMesh L k • b') +
      traceFinsumPairing (gaugeFixingTerm L k U (finestMesh L k • b'))
        (gaugeFixingTerm L k U (finestMesh L k • b')) = _
    exact congrArg (· + _) h₁
theorem rescaledIterRelations_holds (hAlg : RescaledKernelAlgebra.Claim)
    (hMul : ScalarMultipleKernels.Statement)
    (hProd : PeriodicOperators.RowFiniteKernels.Claim)
    (hKer : ThreeMapKernels.Claim)
    (hCov : CovariantIterRelations)
    (hEvery : ComplexFieldRescaledRelations.Statement)
    (hScaled : RescaledKernels.KernelsWellFormedEverywhere)
    (hSecond : HessianKernel.KernelProperties)
    (hBack : KernelAtZeroSources.ZeroSourceKernel)
    (hForm : IteratedMeans.IteratedMeansHold)
    (hP : OneLoop.PauliMatrixRelations) : RescaledIterRelations := by
  intro L hL k hk U hU
  exact (relationData hAlg hMul hProd hKer hCov hEvery hScaled hSecond hBack hForm hP hL hk
    hU).coreRelations
end Assembly
end YangMills.Construction.Tower.FullSpace.IterRelations
end
