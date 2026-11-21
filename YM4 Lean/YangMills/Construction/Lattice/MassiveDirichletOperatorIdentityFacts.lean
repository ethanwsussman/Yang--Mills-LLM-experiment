import YangMills.Construction.Lattice.CollarOfTheInnerMember
import YangMills.Construction.Lattice.ScalarMinimiserOfASequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set MeasureTheory PeriodicLattice PeriodicLattice.DirichletOperators
namespace PeriodicLattice.DirichletOperators
variable {L m K : ℕ}
def zeroMul (h : ZeroForms L m K) : Module.End ℝ (ZeroForms L m K) where
  toFun f x := h x * f x
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def oneMul (h : ZeroForms L m K) : Module.End ℝ (OneForms L m K) where
  toFun A b := h b.1.source * A b
  map_add' A B := by
    funext b
    simp only [Pi.add_apply]
    ring
  map_smul' c A := by
    funext b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def frontierOpKOuter (K t : ℕ) (Ω₀ : Set (FourTorus L m)) (φ : BondFrame) :
    ZeroForms L m K →ₗ[ℝ] OneForms L m K :=
  bondProjection K Ω₀ φ ∘ₗ grad t ∘ₗ (1 - siteProjection K Ω₀) ∘ₗ scalarLaplacian L m K t ∘ₗ
    siteProjection K Ω₀
def frontierOpKCut (K t : ℕ) (Ω₀ : Set (FourTorus L m)) (φ : BondFrame) :
    ZeroForms L m K →ₗ[ℝ] OneForms L m K :=
  bondProjection K Ω₀ φ ∘ₗ hodgeLaplacian L m K t ∘ₗ frontierProjection K Ω₀ φ ∘ₗ grad t ∘ₗ
    siteProjection K Ω₀
end PeriodicLattice.DirichletOperators
namespace RealInnerForms
def IsUniqueMinimizerOn {V : Type*} (F : V → ℝ) (C : Set V) (v : V) : Prop :=
  v ∈ C ∧ ∀ u ∈ C, u ≠ v → F v < F u
end RealInnerForms
namespace SeparatedSequences.BaseParameters
variable (D : BaseParameters) (Ω : ℕ → Set D.Torus) (φ : BondFrame)
abbrev withParameterA (b : ℝ) (hb : 0 < b) : BaseParameters := { D with a := b, a_pos := hb }
abbrev RegionZeroForms : Type := ↥(zeroFormsOn D.K (Ω 0))
abbrev RegionOneForms : Type := ↥(oneFormsOn D.K (Ω 0) φ)
abbrev regionGrad : D.RegionZeroForms Ω →ₗ[ℝ] D.RegionOneForms Ω φ :=
  dirichletGrad D.K D.t (Ω 0) φ
abbrev regionGradAdjoint : D.RegionOneForms Ω φ →ₗ[ℝ] D.RegionZeroForms Ω :=
  dirichletGradAdjoint D.K D.t (Ω 0) φ
abbrev regionScalarLaplacian : Module.End ℝ (D.RegionZeroForms Ω) :=
  dirichletLaplacian D.K D.t (Ω 0)
abbrev regionHodgeLaplacian : Module.End ℝ (D.RegionOneForms Ω φ) :=
  dirichletHodgeLaplacian D.K D.t (Ω 0) φ
abbrev regionCurlCurl : Module.End ℝ (D.RegionOneForms Ω φ) := dirichletCurlCurl D.K D.t (Ω 0) φ
abbrev fullLaplacian : Module.End ℝ (ZeroForms D.L D.m D.K) := scalarLaplacian D.L D.m D.K D.t
abbrev fullGradAdjoint : OneForms D.L D.m D.K →ₗ[ℝ] ZeroForms D.L D.m D.K :=
  gradAdjoint D.L D.m D.K D.t
abbrev fullGrad : ZeroForms D.L D.m D.K →ₗ[ℝ] OneForms D.L D.m D.K := grad D.t
abbrev fullCurl : OneForms D.L D.m D.K →ₗ[ℝ] TwoForms D.L D.m D.K := curl D.t
def normSq {ι : Type} (g : ι → ℝ) : ℝ := latticeInner D.L D.t g g
abbrev regionZeroMul (h : ZeroForms D.L D.m D.K) : Module.End ℝ (D.RegionZeroForms Ω) :=
  compress (siteProjection D.K (Ω 0)) (zeroMul h)
abbrev regionOneMul (h : ZeroForms D.L D.m D.K) : Module.End ℝ (D.RegionOneForms Ω φ) :=
  compress (bondProjection D.K (Ω 0) φ) (oneMul h)
def severedBondCount (x : BareSite D.L D.m D.K) : ℕ :=
  Nat.card {b : BareBond D.L D.m D.K //
    b ∈ starBonds D.K (Ω 0) \ framedBonds D.K (Ω 0) φ ∧ (b.1.source = x ∨ b.1.target = x)}
def starGradSum (h g : ZeroForms D.L D.m D.K) (x : BareSite D.L D.m D.K) : ℝ :=
  ∑ᶠ b : {b : BareOrientedBond D.L D.m D.K // b ∈ outgoingBonds x},
    orientedValue (D.fullGrad h) b.1 * orientedValue (D.fullGrad g) b.1
def mulCommutatorRemainder (h : ZeroForms D.L D.m D.K) (f : D.RegionZeroForms Ω) (n : ℕ)
    (y : D.LatticeSite n) (x : BareSite D.L D.m D.K) : ℝ :=
  D.starGradSum h f.1 x - D.fullLaplacian h x * f.1 x -
    D.levelWeight n * (D.levelMeshRatio n ^ 2)⁻¹ * ((D.L : ℝ) ^ (n * dimension))⁻¹ *
      ∑ᶠ x' : {x' : BareSite D.L D.m D.K // (x' : D.Torus) ∈ fineBlock (D := D) y},
        (h x'.1 - h x) * f.1 x'.1
def blockConstants : Submodule ℝ (D.RegionZeroForms Ω) where
  carrier := {f | ∀ n ≤ D.t, ∀ y ∈ D.layerSites Ω n, ∀ x x' : BareSite D.L D.m D.K,
    (x : D.Torus) ∈ fineBlock (D := D) y → (x' : D.Torus) ∈ fineBlock (D := D) y → f.1 x = f.1 x'}
  add_mem' := fun hf hg n hn y hy x x' hx hx' => by
    simp only [Submodule.coe_add, Pi.add_apply, hf n hn y hy x x' hx hx', hg n hn y hy x x' hx hx']
  zero_mem' := fun _ _ _ _ _ _ _ _ => rfl
  smul_mem' := fun c _ hf n hn y hy x x' hx hx' => by
    simp only [Submodule.coe_smul, Pi.smul_apply, hf n hn y hy x x' hx hx']
def averageFormula (X : Module.End ℝ (D.RegionZeroForms Ω)) :
    Module.End ℝ (D.RegionZeroForms Ω) :=
  Ring.inverse X ∘ₗ D.averageZeroAdjoint Ω ∘ₗ
    Ring.inverse (D.averageZero Ω ∘ₗ (Ring.inverse X ^ 2) ∘ₗ D.averageZeroAdjoint Ω) ∘ₗ
      D.averageZero Ω ∘ₗ Ring.inverse X
def zeroFormExtensionAdjoint : D.RegionZeroForms Ω →ₗ[ℝ] D.CoarseZeroForms Ω :=
  FiniteDimReal.adjointFor (D.coarseZeroInner Ω) (D.restrictedZeroInner Ω) (D.zeroFormExtension Ω)
def oneExtensionAdjoint : D.RegionOneForms Ω φ →ₗ[ℝ] D.CoarseOneForms Ω φ :=
  FiniteDimReal.adjointFor (D.coarseOneInner Ω φ) (D.restrictedOneInner Ω φ) (D.oneExtension Ω φ)
def gaugePart : Module.End ℝ (D.RegionOneForms Ω φ) :=
  D.oneGreen Ω φ ∘ₗ D.gaugeFixingTerm Ω φ
def averagePart : Module.End ℝ (D.RegionOneForms Ω φ) :=
  D.oneExtension Ω φ ∘ₗ D.averageOne Ω φ
def constrainedOneGreen : Module.End ℝ (D.RegionOneForms Ω φ) :=
  D.oneProjection Ω φ ∘ₗ D.oneGreen Ω φ
def pureGaugeCovariance : Module.End ℝ (D.RegionOneForms Ω φ) :=
  D.regionGrad Ω φ ∘ₗ D.constrainedZeroGreen Ω ∘ₗ D.regionGradAdjoint Ω φ
def massiveOneInner (u v : D.RegionOneForms Ω φ) : ℝ :=
  D.restrictedOneInner Ω φ u (D.massiveOneOperator Ω φ v)
def levelCombination (α β : ℝ) : ℝ := α * β / (α * (D.L : ℝ) ^ (-2 : ℤ) + β)
def coarseBlockMean {n : ℕ} (y : D.LatticeSite (n + 1))
    (g : ↥(coarseBlock (D := D) y) → ℝ) : ℝ :=
  (Nat.card ↥(coarseBlock (D := D) y) : ℝ)⁻¹ * ∑ᶠ z, g z
structure GradCurlIdentities : Prop where
  split : ∀ f : D.RegionZeroForms Ω, D.fullGrad f.1 =
    (D.regionGrad Ω φ f).1 + frontierProjection D.K (Ω 0) φ (D.fullGrad f.1)
  curl_grad : ∀ f : D.RegionZeroForms Ω, D.fullCurl (D.regionGrad Ω φ f).1 =
    -D.fullCurl (frontierProjection D.K (Ω 0) φ (D.fullGrad f.1))
  of_star : φ = BondFrame.star → ∀ f : D.RegionZeroForms Ω,
    (D.regionGrad Ω φ f).1 = D.fullGrad f.1 ∧ D.fullCurl (D.regionGrad Ω φ f).1 = 0
  interior_fails : φ = BondFrame.interior →
    ∀ (x : BareSite D.L D.m D.K) (b b' : BareBond D.L D.m D.K) (p : BarePlaquette D.L D.m D.K)
      (f : D.RegionZeroForms Ω),
      x ∈ sitesOfRegion D.K (Ω 0) →
      ((b.1.source = x ∧ b.1.target ∉ sitesOfRegion D.K (Ω 0)) ∨
        (b.1.target = x ∧ b.1.source ∉ sitesOfRegion D.K (Ω 0))) →
      ((b'.1.source = x ∧ b'.1.target ∈ sitesOfRegion D.K (Ω 0)) ∨
        (b'.1.target = x ∧ b'.1.source ∈ sitesOfRegion D.K (Ω 0))) →
      bondAxis b ≠ bondAxis b' →
      b ∈ edgesOf p → b' ∈ edgesOf p →
      f.1 = ({x} : Set (BareSite D.L D.m D.K)).indicator 1 →
      |D.fullCurl (D.regionGrad Ω φ f).1 p| = (D.levelMeshRatio 0 ^ 2)⁻¹
  of_vanishing_on_frontier : ∀ f : D.RegionZeroForms Ω,
    (∀ x ∈ frontierSites D.K (Ω 0), f.1 x = 0) →
      (D.regionGrad Ω φ f).1 = D.fullGrad f.1 ∧
        D.fullCurl (D.regionGrad Ω φ f).1 = 0
structure DirichletLaplacianSplitting : Prop where
  eq_add : ∀ f : D.RegionZeroForms Ω, (D.regionScalarLaplacian Ω f).1 =
    (D.regionGradAdjoint Ω φ (D.regionGrad Ω φ f)).1 + frontierOpN D.K D.t (Ω 0) φ f.1
  frontier_apply : ∀ (f : D.RegionZeroForms Ω) (x : BareSite D.L D.m D.K),
    frontierOpN D.K D.t (Ω 0) φ f.1 x =
      (D.levelMeshRatio 0 ^ 2)⁻¹ * (D.severedBondCount Ω φ x : ℝ) * f.1 x
  of_star : φ = BondFrame.star → frontierOpN D.K D.t (Ω 0) φ = 0
  frontier_supported : ∀ (f : D.RegionZeroForms Ω) (x : BareSite D.L D.m D.K),
    x ∉ frontierSites D.K (Ω 0) → frontierOpN D.K D.t (Ω 0) φ f.1 x = 0
structure HodgeLaplacianSplitting : Prop where
  axisComponent_hodge : ∀ (A : OneForms D.L D.m D.K) (ν : Fin 4),
    DirichletOperators.axisComponent (hodgeLaplacian D.L D.m D.K D.t A) ν =
      D.fullLaplacian (DirichletOperators.axisComponent A ν)
  eq_add : ∀ A : D.RegionOneForms Ω φ, (D.regionHodgeLaplacian Ω φ A).1 =
    (D.regionCurlCurl Ω φ A).1 +
      (D.regionGrad Ω φ (D.regionGradAdjoint Ω φ A)).1 + frontierOpE D.K D.t (Ω 0) φ A.1
  frontier_inner : ∀ A : D.RegionOneForms Ω φ,
    latticeInner D.L D.t A.1 (frontierOpE D.K D.t (Ω 0) φ A.1) =
      D.levelMeshRatio 0 ^ dimension * ∑ᶠ x : {x : BareSite D.L D.m D.K // x ∉ sitesOfRegion D.K (Ω 0)},
        |D.fullGradAdjoint A.1 x.1| ^ 2
  of_interior : φ = BondFrame.interior → frontierOpE D.K D.t (Ω 0) φ = 0
  of_star_nonneg : φ = BondFrame.star → ∀ A : D.RegionOneForms Ω φ,
    0 ≤ latticeInner D.L D.t A.1 (frontierOpE D.K D.t (Ω 0) φ A.1)
  of_star_depends_on_frontier : φ = BondFrame.star → ∀ A A' : D.RegionOneForms Ω φ,
    (∀ b ∈ frontierBonds D.K (Ω 0), A.1 b = A'.1 b) →
      frontierOpE D.K D.t (Ω 0) φ A.1 = frontierOpE D.K D.t (Ω 0) φ A'.1
structure GradLaplacianCommutation : Prop where
  full : ∀ f : ZeroForms D.L D.m D.K, hodgeLaplacian D.L D.m D.K D.t (D.fullGrad f) =
    D.fullGrad (D.fullLaplacian f)
  grad : ∀ f : D.RegionZeroForms Ω,
    (D.regionHodgeLaplacian Ω φ (D.regionGrad Ω φ f)).1 =
      (D.regionGrad Ω φ (D.regionScalarLaplacian Ω f)).1 + frontierOpK D.K D.t (Ω 0) φ f.1
  grad_adjoint : ∀ A : D.RegionOneForms Ω φ,
    (D.regionGradAdjoint Ω φ (D.regionHodgeLaplacian Ω φ A)).1 =
      (D.regionScalarLaplacian Ω (D.regionGradAdjoint Ω φ A)).1 +
        formalAdjoint D.L D.t (frontierOpK D.K D.t (Ω 0) φ) A.1
  of_star : φ = BondFrame.star → frontierOpKCut D.K D.t (Ω 0) φ = 0
  of_interior : φ = BondFrame.interior → frontierOpKOuter D.K D.t (Ω 0) φ = 0
  of_vanishing_on_frontier : ∀ f : D.RegionZeroForms Ω,
    (∀ x ∈ frontierSites D.K (Ω 0), f.1 x = 0) → frontierOpK D.K D.t (Ω 0) φ f.1 = 0
structure MulCommutators : Prop where
  zeroMul_comm_siteProjection : ∀ h : ZeroForms D.L D.m D.K,
    zeroMul h * siteProjection D.K (Ω 0) = siteProjection D.K (Ω 0) * zeroMul h
  oneMul_comm_bondProjection : ∀ h : ZeroForms D.L D.m D.K,
    oneMul h * bondProjection D.K (Ω 0) φ = bondProjection D.K (Ω 0) φ * oneMul h
  oneMul_comm_frontierProjection : ∀ h : ZeroForms D.L D.m D.K,
    oneMul h * frontierProjection D.K (Ω 0) φ = frontierProjection D.K (Ω 0) φ * oneMul h
  compress_zero : ∀ (h : ZeroForms D.L D.m D.K) (X : Module.End ℝ (ZeroForms D.L D.m D.K)),
    compress (siteProjection D.K (Ω 0)) X * D.regionZeroMul Ω h -
        D.regionZeroMul Ω h * compress (siteProjection D.K (Ω 0)) X =
      compress (siteProjection D.K (Ω 0)) (X * zeroMul h - zeroMul h * X)
  compress_one : ∀ (h : ZeroForms D.L D.m D.K) (X : Module.End ℝ (OneForms D.L D.m D.K)),
    compress (bondProjection D.K (Ω 0) φ) X * D.regionOneMul Ω φ h -
        D.regionOneMul Ω φ h * compress (bondProjection D.K (Ω 0) φ) X =
      compress (bondProjection D.K (Ω 0) φ) (X * oneMul h - oneMul h * X)
  massive_zero : ∀ (h : ZeroForms D.L D.m D.K) (f : D.RegionZeroForms Ω) (n : ℕ), n ≤ D.t →
    ∀ y ∈ D.layerSites Ω n, ∀ x : BareSite D.L D.m D.K, (x : D.Torus) ∈ fineBlock (D := D) y →
      (D.massiveZeroOperator Ω (D.regionZeroMul Ω h f)).1 x =
        h x * (D.massiveZeroOperator Ω f).1 x - D.mulCommutatorRemainder Ω h f n y x
  sub_eq_lineSum : ∀ (h : ZeroForms D.L D.m D.K) (x x' : BareSite D.L D.m D.K)
    (Γ : List (BareOrientedBond D.L D.m D.K)), IsBondPathFromTo Γ x x' →
      h x' - h x = D.levelMeshRatio 0 * lineSum (D.fullGrad h) Γ
  hodge_one : ∀ (h : ZeroForms D.L D.m D.K) (A : D.RegionOneForms Ω φ) (x : BareSite D.L D.m D.K)
    (μ : Fin 4), bondFrom x μ ∈ framedBonds D.K (Ω 0) φ →
      axisComponent (D.regionHodgeLaplacian Ω φ (D.regionOneMul Ω φ h A)).1 μ x =
        h x * axisComponent (D.regionHodgeLaplacian Ω φ A).1 μ x -
          D.starGradSum h (axisComponent A.1 μ) x + D.fullLaplacian h x * axisComponent A.1 μ x
structure ZeroFormSymmetries : Prop where
  laplacian_symm : FiniteDimReal.IsSymmetricFor (D.restrictedZeroInner Ω) (D.regionScalarLaplacian Ω)
  massive_symm : FiniteDimReal.IsSymmetricFor (D.restrictedZeroInner Ω) (D.massiveZeroOperator Ω)
  green_symm : FiniteDimReal.IsSymmetricFor (D.restrictedZeroInner Ω) (D.zeroGreen Ω)
  gaugeRange_symm :
    FiniteDimReal.IsSymmetricFor (D.restrictedZeroInner Ω) (D.gaugeRangeProjection Ω)
  gaugeComplement_symm :
    FiniteDimReal.IsSymmetricFor (D.restrictedZeroInner Ω) (D.gaugeComplementProjection Ω)
  constrainedGreen_symm :
    FiniteDimReal.IsSymmetricFor (D.restrictedZeroInner Ω) (D.constrainedZeroGreen Ω)
  averagedGreenSq_symm :
    FiniteDimReal.IsSymmetricFor (D.coarseZeroInner Ω) (D.averagedZeroGreenSq Ω)
  averagedGreenSq_inverse_symm :
    FiniteDimReal.IsSymmetricFor (D.coarseZeroInner Ω) (Ring.inverse (D.averagedZeroGreenSq Ω))
  blockConstants_projection : RealInnerForms.IsOrthogonalProjectionFor (D.restrictedZeroInner Ω)
    (D.blockConstants Ω) (D.averageZeroAdjoint Ω ∘ₗ D.averageZero Ω)
structure AverageKernelProperties : Prop where
  supported : ∀ f ∈ D.averageZeroKernel Ω, ∀ x : BareSite D.L D.m D.K,
    (x : D.Torus) ∉ D.memberAt Ω 1 → f.1 x = 0
  grad_supported : ∀ f ∈ D.averageZeroKernel Ω, ∀ b ∉ interiorBonds D.K (Ω 0),
    D.fullGrad f.1 b = 0
  laplacian_supported : ∀ f ∈ D.averageZeroKernel Ω, ∀ x ∉ D.collarOfFirstMember Ω 1,
    D.fullLaplacian f.1 x = 0
  grad_laplacian_supported : ∀ f ∈ D.averageZeroKernel Ω, ∀ b ∉ interiorBonds D.K (Ω 0),
    D.fullGrad (D.fullLaplacian f.1) b = 0
  regionGrad_eq : ∀ f ∈ D.averageZeroKernel Ω, (D.regionGrad Ω φ f).1 = D.fullGrad f.1
  gradAdjoint_grad_eq : ∀ f ∈ D.averageZeroKernel Ω,
    (D.regionGradAdjoint Ω φ (D.regionGrad Ω φ f)).1 = D.fullLaplacian f.1
  regionLaplacian_eq : ∀ f ∈ D.averageZeroKernel Ω,
    (D.regionScalarLaplacian Ω f).1 = D.fullLaplacian f.1
  massive_eq : ∀ f ∈ D.averageZeroKernel Ω, (D.massiveZeroOperator Ω f).1 = D.fullLaplacian f.1
  grad_laplacian_eq : ∀ f ∈ D.averageZeroKernel Ω,
    (D.regionGrad Ω φ (D.regionScalarLaplacian Ω f)).1 = D.fullGrad (D.fullLaplacian f.1)
  bijOn : BijOn (D.regionScalarLaplacian Ω) (D.averageZeroKernel Ω : Set (D.RegionZeroForms Ω))
    (LinearMap.range (D.gaugeRangeProjection Ω) : Set (D.RegionZeroForms Ω))
structure GaugeProjectionFormulas : Prop where
  of_posDef : ∀ X : Module.End ℝ (D.RegionZeroForms Ω),
    FiniteDimReal.IsPosDefFor (D.restrictedZeroInner Ω) X →
      (∀ f ∈ D.averageZeroKernel Ω, X f = D.regionScalarLaplacian Ω f) →
        D.gaugeComplementProjection Ω = D.averageFormula Ω X ∧
          D.gaugeRangeProjection Ω = 1 - D.averageFormula Ω X
  of_massive : D.gaugeComplementProjection Ω =
    D.zeroGreen Ω ∘ₗ D.averageZeroAdjoint Ω ∘ₗ Ring.inverse (D.averagedZeroGreenSq Ω) ∘ₗ
      D.averageZero Ω ∘ₗ D.zeroGreen Ω
  gaugeRange_withParameterA : ∀ (b : ℝ) (hb : 0 < b),
    (D.withParameterA b hb).gaugeRangeProjection Ω = D.gaugeRangeProjection Ω
  gaugeComplement_withParameterA : ∀ (b : ℝ) (hb : 0 < b),
    (D.withParameterA b hb).gaugeComplementProjection Ω = D.gaugeComplementProjection Ω
  laplacian_posDef : Ω 0 ≠ univ →
    FiniteDimReal.IsPosDefFor (D.restrictedZeroInner Ω) (D.regionScalarLaplacian Ω)
  of_laplacian : Ω 0 ≠ univ →
    D.gaugeComplementProjection Ω = D.averageFormula Ω (D.regionScalarLaplacian Ω) ∧
      D.gaugeRangeProjection Ω = 1 - D.averageFormula Ω (D.regionScalarLaplacian Ω)
  range_green_averageAdjoint :
    D.gaugeRangeProjection Ω ∘ₗ D.zeroGreen Ω ∘ₗ D.averageZeroAdjoint Ω = 0
  average_green_range :
    D.averageZero Ω ∘ₗ D.zeroGreen Ω ∘ₗ D.gaugeRangeProjection Ω = 0
  range_green_comp_range :
    LinearMap.range (D.zeroGreen Ω ∘ₗ D.gaugeRangeProjection Ω) = D.averageZeroKernel Ω
structure ConstrainedGreenProperties : Prop where
  eq_comp : D.constrainedZeroGreen Ω =
    D.zeroGreen Ω ∘ₗ D.gaugeRangeProjection Ω ∘ₗ D.zeroGreen Ω
  average_comp : D.averageZero Ω ∘ₗ D.constrainedZeroGreen Ω = 0
  comp_averageAdjoint : D.constrainedZeroGreen Ω ∘ₗ D.averageZeroAdjoint Ω = 0
  range_eq_laplacian : D.gaugeRangeProjection Ω =
    D.regionScalarLaplacian Ω ∘ₗ D.constrainedZeroGreen Ω ∘ₗ D.regionScalarLaplacian Ω
  range_eq_massive : D.gaugeRangeProjection Ω =
    D.massiveZeroOperator Ω ∘ₗ D.constrainedZeroGreen Ω ∘ₗ D.massiveZeroOperator Ω
  comp_laplacian : D.constrainedZeroGreen Ω ∘ₗ D.regionScalarLaplacian Ω =
    D.zeroGreen Ω ∘ₗ D.gaugeRangeProjection Ω
  apply_mem_kernel : ∀ f, D.constrainedZeroGreen Ω f ∈ D.averageZeroKernel Ω
  weak_form : ∀ f, ∀ g ∈ D.averageZeroKernel Ω,
    latticeInner D.L D.t (D.fullLaplacian g.1) (D.fullLaplacian (D.constrainedZeroGreen Ω f).1) =
      D.restrictedZeroInner Ω g f
  weak_form_unique : ∀ f, ∀ u ∈ D.averageZeroKernel Ω,
    (∀ g ∈ D.averageZeroKernel Ω,
      latticeInner D.L D.t (D.fullLaplacian g.1) (D.fullLaplacian u.1) =
        D.restrictedZeroInner Ω g f) → u = D.constrainedZeroGreen Ω f
structure VariationalAndGaussianForms : Prop where
  normSq_sub : ∀ f, ∀ g ∈ D.averageZeroKernel Ω,
    D.normSq (f - D.regionScalarLaplacian Ω g).1 =
      D.restrictedZeroInner Ω f (D.gaugeComplementProjection Ω f) +
        D.normSq (D.regionScalarLaplacian Ω (g - D.zeroGreen Ω (D.gaugeRangeProjection Ω f))).1
  integrable_gaussian : ∀ (μ : Measure ↥(D.averageZeroKernel Ω)) [μ.IsAddHaarMeasure],
    Integrable (fun g : ↥(D.averageZeroKernel Ω) =>
      Real.exp (-(1 / 2) * D.normSq (D.regionScalarLaplacian Ω g.1).1)) μ
  integrable_gaussian_shift : ∀ (μ : Measure ↥(D.averageZeroKernel Ω)) [μ.IsAddHaarMeasure]
    (f : D.RegionZeroForms Ω),
    Integrable (fun g : ↥(D.averageZeroKernel Ω) =>
      Real.exp (-(1 / 2) * D.normSq (f - D.regionScalarLaplacian Ω g.1).1)) μ
  integrable_gaussian_linear : ∀ (μ : Measure ↥(D.averageZeroKernel Ω)) [μ.IsAddHaarMeasure]
    (f : D.RegionZeroForms Ω),
    Integrable (fun g : ↥(D.averageZeroKernel Ω) =>
      Real.exp (-(1 / 2) * D.normSq (D.regionScalarLaplacian Ω g.1).1 +
        D.restrictedZeroInner Ω (D.regionScalarLaplacian Ω f) g.1)) μ
  integral_gaussian_shift : ∀ (μ : Measure ↥(D.averageZeroKernel Ω)) [μ.IsAddHaarMeasure]
    (f : D.RegionZeroForms Ω),
    ∫ g : ↥(D.averageZeroKernel Ω),
        Real.exp (-(1 / 2) * D.normSq (f - D.regionScalarLaplacian Ω g.1).1) ∂μ =
      (∫ g : ↥(D.averageZeroKernel Ω),
        Real.exp (-(1 / 2) * D.normSq (D.regionScalarLaplacian Ω g.1).1) ∂μ) *
        Real.exp (-(1 / 2) * D.restrictedZeroInner Ω f (D.gaugeComplementProjection Ω f))
  integral_gaussian_linear : ∀ (μ : Measure ↥(D.averageZeroKernel Ω)) [μ.IsAddHaarMeasure]
    (f : D.RegionZeroForms Ω),
    ∫ g : ↥(D.averageZeroKernel Ω),
        Real.exp (-(1 / 2) * D.normSq (D.regionScalarLaplacian Ω g.1).1 +
          D.restrictedZeroInner Ω (D.regionScalarLaplacian Ω f) g.1) ∂μ =
      (∫ g : ↥(D.averageZeroKernel Ω),
        Real.exp (-(1 / 2) * D.normSq (D.regionScalarLaplacian Ω g.1).1) ∂μ) *
        Real.exp ((1 / 2) * D.restrictedZeroInner Ω f (D.gaugeRangeProjection Ω f))
structure ZeroFormMinimizer : Prop where
  average_comp_extension : D.averageZero Ω ∘ₗ D.zeroFormExtension Ω = LinearMap.id
  isUniqueMinimizerOn : ∀ ω : D.CoarseZeroForms Ω,
    RealInnerForms.IsUniqueMinimizerOn (fun f : D.RegionZeroForms Ω => D.normSq (D.fullGrad f.1))
      {f | D.averageZero Ω f = ω} (D.zeroFormExtension Ω ω)
  inverse_averagedGreen : Ring.inverse (D.averagedZeroGreen Ω) =
    D.weightMulZero Ω + D.zeroFormExtensionAdjoint Ω ∘ₗ D.regionScalarLaplacian Ω ∘ₗ
      D.zeroFormExtension Ω
  green_eq_add : ∃ C' : Module.End ℝ (D.RegionZeroForms Ω),
    (∀ f, C' f ∈ D.averageZeroKernel Ω ∧
      (∀ g ∈ D.averageZeroKernel Ω,
        latticeInner D.L D.t (D.fullGrad g.1) (D.fullGrad (C' f).1) =
          D.restrictedZeroInner Ω g f) ∧
      ∀ u ∈ D.averageZeroKernel Ω,
        (∀ g ∈ D.averageZeroKernel Ω,
          latticeInner D.L D.t (D.fullGrad g.1) (D.fullGrad u.1) =
            D.restrictedZeroInner Ω g f) → u = C' f) ∧
    D.zeroGreen Ω =
      C' + D.zeroFormExtension Ω ∘ₗ D.averagedZeroGreen Ω ∘ₗ D.zeroFormExtensionAdjoint Ω
  inverse_averagedGreenSq_isLeast : ∀ ω : D.CoarseZeroForms Ω,
    IsLeast {r : ℝ | ∃ f : D.RegionZeroForms Ω, D.averageZero Ω f = ω ∧
        r = D.normSq (D.massiveZeroOperator Ω f).1}
      (D.coarseZeroInner Ω ω (Ring.inverse (D.averagedZeroGreenSq Ω) ω))
structure ConsecutiveLevelWeights : Prop where
  isLeast : ∀ (n : ℕ), n < D.t → ∀ (y : D.LatticeSite (n + 1)) (α β : ℝ), 0 < α → 0 < β →
    ∀ g : ↥(coarseBlock (D := D) y) → ℝ,
      IsLeast (range fun w : ↥(coarseBlock (D := D) y) → ℝ =>
          α * D.levelMeshRatio (n + 1) ^ (dimension - 2) * |D.coarseBlockMean y w| ^ 2 +
            β * D.levelMeshRatio n ^ (dimension - 2) * ∑ᶠ z, |w z - g z| ^ 2)
        (D.levelCombination α β * D.levelMeshRatio (n + 1) ^ (dimension - 2) *
          |D.coarseBlockMean y g| ^ 2)
  levelWeight_succ : ∀ j : ℕ, 1 ≤ j → D.levelCombination D.a (D.levelWeight j) = D.levelWeight (j + 1)
  levelWeight_one : D.levelWeight 1 = D.a
  levelCombination_lt : ∀ a₀ : ℝ, 0 < a₀ → D.levelCombination D.a a₀ < D.a
  levelCombination_self : D.levelCombination D.a D.a = D.a / (1 + (D.L : ℝ) ^ (-2 : ℤ))
  levelCombination_shifted : D.levelCombination (D.a / (1 - (D.L : ℝ) ^ (-2 : ℤ))) D.a = D.a
def AverageGradIntertwining : Prop :=
  D.averageOne Ω φ ∘ₗ D.regionGrad Ω φ = D.coarseDifference Ω φ ∘ₗ D.averageZero Ω
structure GaugeFixingProperties : Prop where
  average_grad : ∀ f ∈ D.averageZeroKernel Ω, D.averageOne Ω φ (D.regionGrad Ω φ f) = 0
  curl_grad : ∀ f ∈ D.averageZeroKernel Ω, D.fullCurl (D.regionGrad Ω φ f).1 = 0
  gaugeSolution_mem : ∀ A : D.RegionOneForms Ω φ,
    D.zeroGreen Ω (D.gaugeRangeProjection Ω (D.regionGradAdjoint Ω φ A)) ∈ D.averageZeroKernel Ω
  gaugeSolution_spec : ∀ A : D.RegionOneForms Ω φ, D.gaugeRangeProjection Ω (D.regionGradAdjoint Ω φ
    (A - D.regionGrad Ω φ
      (D.zeroGreen Ω (D.gaugeRangeProjection Ω (D.regionGradAdjoint Ω φ A))))) = 0
  gaugeSolution_unique : ∀ (A : D.RegionOneForms Ω φ), ∀ f ∈ D.averageZeroKernel Ω,
    D.gaugeRangeProjection Ω (D.regionGradAdjoint Ω φ (A - D.regionGrad Ω φ f)) = 0 →
      f = D.zeroGreen Ω (D.gaugeRangeProjection Ω (D.regionGradAdjoint Ω φ A))
  gaugeSolution_isUniqueMinimizerOn : ∀ A : D.RegionOneForms Ω φ,
    RealInnerForms.IsUniqueMinimizerOn
      (fun f : D.RegionZeroForms Ω =>
        D.normSq (D.fullGradAdjoint (A.1 - D.fullGrad f.1)))
      (D.averageZeroKernel Ω : Set (D.RegionZeroForms Ω))
      (D.zeroGreen Ω (D.gaugeRangeProjection Ω (D.regionGradAdjoint Ω φ A)))
structure MassiveOneOperatorForms : Prop where
  eq_hodge_form : ∀ A : D.RegionOneForms Ω φ, (D.massiveOneOperator Ω φ A).1 =
    (D.regionHodgeLaplacian Ω φ A).1 -
      (D.regionGrad Ω φ (D.gaugeComplementProjection Ω
        (D.regionGradAdjoint Ω φ A))).1 -
      frontierOpE D.K D.t (Ω 0) φ A.1 + (D.weightedAverageOne Ω φ A).1
  massive_symm : FiniteDimReal.IsSymmetricFor (D.restrictedOneInner Ω φ) (D.massiveOneOperator Ω φ)
  green_symm : FiniteDimReal.IsSymmetricFor (D.restrictedOneInner Ω φ) (D.oneGreen Ω φ)
  averagedGreen_symm :
    FiniteDimReal.IsSymmetricFor (D.coarseOneInner Ω φ) (D.averagedOneGreen Ω φ)
  averagedGreen_inverse_symm :
    FiniteDimReal.IsSymmetricFor (D.coarseOneInner Ω φ) (Ring.inverse (D.averagedOneGreen Ω φ))
structure MassiveOperatorsRelation : Prop where
  massive_grad : ∀ f ∈ D.averageZeroKernel Ω,
    D.massiveOneOperator Ω φ (D.regionGrad Ω φ f) =
      D.regionGrad Ω φ (D.massiveZeroOperator Ω f)
  green_grad_range : D.oneGreen Ω φ ∘ₗ D.regionGrad Ω φ ∘ₗ D.gaugeRangeProjection Ω =
    D.regionGrad Ω φ ∘ₗ D.zeroGreen Ω ∘ₗ D.gaugeRangeProjection Ω
  range_gradAdjoint_green :
    D.gaugeRangeProjection Ω ∘ₗ D.regionGradAdjoint Ω φ ∘ₗ D.oneGreen Ω φ =
      D.gaugeRangeProjection Ω ∘ₗ D.zeroGreen Ω ∘ₗ D.regionGradAdjoint Ω φ
  green_gaugeFixing_green : D.oneGreen Ω φ ∘ₗ D.gaugeFixingTerm Ω φ ∘ₗ D.oneGreen Ω φ =
    D.pureGaugeCovariance Ω φ
structure OneGreenProducts : Prop where
  left : D.gaugeRangeProjection Ω ∘ₗ D.regionGradAdjoint Ω φ ∘ₗ D.oneGreen Ω φ ∘ₗ
    D.regionGrad Ω φ = D.gaugeRangeProjection Ω
  right : D.regionGradAdjoint Ω φ ∘ₗ D.oneGreen Ω φ ∘ₗ D.regionGrad Ω φ ∘ₗ
    D.gaugeRangeProjection Ω = D.gaugeRangeProjection Ω
  with_averageAdjoint : D.gaugeRangeProjection Ω ∘ₗ D.regionGradAdjoint Ω φ ∘ₗ D.oneGreen Ω φ ∘ₗ
    D.averageOneAdjoint Ω φ = 0
  with_average : D.averageOne Ω φ ∘ₗ D.oneGreen Ω φ ∘ₗ D.regionGrad Ω φ ∘ₗ
    D.gaugeRangeProjection Ω = 0
structure OneExtensionProperties : Prop where
  average_comp_extension : D.averageOne Ω φ ∘ₗ D.oneExtension Ω φ = LinearMap.id
  gauge_condition : D.gaugeRangeProjection Ω ∘ₗ D.regionGradAdjoint Ω φ ∘ₗ D.oneExtension Ω φ = 0
  isUniqueMinimizerOn : ∀ B : D.CoarseOneForms Ω φ,
    RealInnerForms.IsUniqueMinimizerOn (fun A : D.RegionOneForms Ω φ => D.normSq (D.fullCurl A.1))
      {A | D.averageOne Ω φ A = B ∧ D.gaugeRangeProjection Ω (D.regionGradAdjoint Ω φ A) = 0}
      (D.oneExtension Ω φ B)
  minimizers_eq : ∀ B : D.CoarseOneForms Ω φ,
    {A : D.RegionOneForms Ω φ | D.averageOne Ω φ A = B ∧
      ∀ A' : D.RegionOneForms Ω φ, D.averageOne Ω φ A' = B →
        D.normSq (D.fullCurl A.1) ≤ D.normSq (D.fullCurl A'.1)} =
      {A | ∃ f ∈ D.averageZeroKernel Ω, A = D.oneExtension Ω φ B + D.regionGrad Ω φ f}
  withParameterA_eq : ∀ (b : ℝ) (hb : 0 < b),
    (D.withParameterA b hb).oneExtension Ω φ = D.oneExtension Ω φ
  inverse_averagedGreen : Ring.inverse (D.averagedOneGreen Ω φ) =
    D.weightMulOne Ω φ +
      D.oneExtensionAdjoint Ω φ ∘ₗ D.regionCurlCurl Ω φ ∘ₗ D.oneExtension Ω φ
  inverse_averagedGreen_inner : ∀ B : D.CoarseOneForms Ω φ,
    D.coarseOneInner Ω φ B (Ring.inverse (D.averagedOneGreen Ω φ) B) =
      D.coarseOneInner Ω φ B (D.weightMulOne Ω φ B) +
        D.normSq (D.fullCurl (D.oneExtension Ω φ B).1)
structure OneFormProjections : Prop where
  gauge_idem : D.gaugePart Ω φ * D.gaugePart Ω φ = D.gaugePart Ω φ
  average_idem : D.averagePart Ω φ * D.averagePart Ω φ = D.averagePart Ω φ
  rest_idem : D.oneProjection Ω φ * D.oneProjection Ω φ = D.oneProjection Ω φ
  gauge_symm : FiniteDimReal.IsSymmetricFor (D.massiveOneInner Ω φ) (D.gaugePart Ω φ)
  average_symm : FiniteDimReal.IsSymmetricFor (D.massiveOneInner Ω φ) (D.averagePart Ω φ)
  rest_symm : FiniteDimReal.IsSymmetricFor (D.massiveOneInner Ω φ) (D.oneProjection Ω φ)
  gauge_mul_average : D.gaugePart Ω φ * D.averagePart Ω φ = 0
  average_mul_gauge : D.averagePart Ω φ * D.gaugePart Ω φ = 0
  gauge_mul_rest : D.gaugePart Ω φ * D.oneProjection Ω φ = 0
  rest_mul_gauge : D.oneProjection Ω φ * D.gaugePart Ω φ = 0
  average_mul_rest : D.averagePart Ω φ * D.oneProjection Ω φ = 0
  rest_mul_average : D.oneProjection Ω φ * D.averagePart Ω φ = 0
  sum_eq_one : D.gaugePart Ω φ + D.averagePart Ω φ + D.oneProjection Ω φ = 1
  gauge_range : LinearMap.range (D.gaugePart Ω φ) =
    (D.averageZeroKernel Ω).map (D.regionGrad Ω φ)
  average_range : LinearMap.range (D.averagePart Ω φ) = LinearMap.range (D.oneExtension Ω φ)
  rest_range : LinearMap.range (D.oneProjection Ω φ) = D.constrainedOneForms Ω φ
  gauge_withParameterA : ∀ (b : ℝ) (hb : 0 < b),
    (D.withParameterA b hb).gaugePart Ω φ = D.gaugePart Ω φ
  average_withParameterA : ∀ (b : ℝ) (hb : 0 < b),
    (D.withParameterA b hb).averagePart Ω φ = D.averagePart Ω φ
  rest_withParameterA : ∀ (b : ℝ) (hb : 0 < b),
    (D.withParameterA b hb).oneProjection Ω φ = D.oneProjection Ω φ
structure OneGreenDecomposition : Prop where
  eq_add : D.oneGreen Ω φ = D.constrainedOneGreen Ω φ + D.pureGaugeCovariance Ω φ +
    D.oneExtension Ω φ ∘ₗ D.averagedOneGreen Ω φ ∘ₗ D.oneExtensionAdjoint Ω φ
  constrained_symm : FiniteDimReal.IsSymmetricFor (D.restrictedOneInner Ω φ) (D.constrainedOneGreen Ω φ)
  constrained_mem : ∀ J, D.constrainedOneGreen Ω φ J ∈ D.constrainedOneForms Ω φ
  weak_form : ∀ J, ∀ Z ∈ D.constrainedOneForms Ω φ,
    latticeInner D.L D.t (D.fullCurl Z.1) (D.fullCurl (D.constrainedOneGreen Ω φ J).1) =
      D.restrictedOneInner Ω φ Z J
  weak_form_unique : ∀ J, ∀ U ∈ D.constrainedOneForms Ω φ,
    (∀ Z ∈ D.constrainedOneForms Ω φ,
      latticeInner D.L D.t (D.fullCurl Z.1) (D.fullCurl U.1) = D.restrictedOneInner Ω φ Z J) →
        U = D.constrainedOneGreen Ω φ J
  vanishes_on_first_layer : ∀ Z ∈ D.constrainedOneForms Ω φ, ∀ c ∈ D.layerBondSet Ω φ 0, Z.1 c = 0
  conditioned_green : D.oneGreen Ω φ -
      D.oneGreen Ω φ ∘ₗ D.averageOneAdjoint Ω φ ∘ₗ Ring.inverse (D.averagedOneGreen Ω φ) ∘ₗ
        D.averageOne Ω φ ∘ₗ D.oneGreen Ω φ =
    D.constrainedOneGreen Ω φ + D.pureGaugeCovariance Ω φ
end SeparatedSequences.BaseParameters
end YangMills.Construction
end
