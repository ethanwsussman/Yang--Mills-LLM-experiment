import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace DirichletOperators
variable {L m K : ℕ}
abbrev BareSite (L m K : ℕ) : Type := SiteAtLevel L m K 0
abbrev BareOrientedBond (L m K : ℕ) : Type := BondAtLevel L m K 0
abbrev BareBond (L m K : ℕ) : Type := PositivelyOrientedBond L m (levelDepth K 0)
abbrev BarePlaquette (L m K : ℕ) : Type := PlaquetteAtLevel L m K 0
abbrev ZeroForms (L m K : ℕ) : Type := BareSite L m K → ℝ
abbrev OneForms (L m K : ℕ) : Type := BareBond L m K → ℝ
abbrev TwoForms (L m K : ℕ) : Type := BarePlaquette L m K → ℝ
def latticeInner (L t : ℕ) {ι : Type} (f g : ι → ℝ) : ℝ :=
  finestMeshInLevelUnits L t ^ 4 * ∑ᶠ i, f i * g i
def formalAdjoint (L t : ℕ) {ι κ : Type} (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    (κ → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  Classical.epsilon fun T' => ∀ f g, latticeInner L t g (T f) = latticeInner L t (T' g) f
def bondFrom (x : BareSite L m K) (μ : Fin 4) : BareBond L m K :=
  ⟨Bond.forwardFrom x μ, μ, by simp [Bond.forwardFrom]⟩
def axisComponent (A : OneForms L m K) (μ : Fin 4) : ZeroForms L m K :=
  fun x => A (bondFrom x μ)
open Classical in
def orientedValue (A : OneForms L m K) (b : BareOrientedBond L m K) : ℝ :=
  if h : b.IsPositivelyOriented then A ⟨b, h⟩
  else if h' : b.opposite.IsPositivelyOriented then -A ⟨b.opposite, h'⟩
  else 0
def lineSum (A : OneForms L m K) (Γ : List (BareOrientedBond L m K)) : ℝ :=
  (Γ.map (orientedValue A)).sum
def forwardDifference (t : ℕ) (μ : Fin 4) (f : ZeroForms L m K) : ZeroForms L m K :=
  fun x => (finestMeshInLevelUnits L t)⁻¹ * (f (x + unitStep L m (levelDepth K 0) μ) - f x)
def grad (t : ℕ) : ZeroForms L m K →ₗ[ℝ] OneForms L m K where
  toFun f b := (finestMeshInLevelUnits L t)⁻¹ * (f b.1.target - f b.1.source)
  map_add' f g := by
    funext b
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem axisComponent_grad (t : ℕ) (f : ZeroForms L m K) (μ : Fin 4) :
    axisComponent (grad t f) μ = forwardDifference t μ f := rfl
def curlAxes (t : ℕ) (A : OneForms L m K) (μ ν : Fin 4) : ZeroForms L m K :=
  forwardDifference t μ (axisComponent A ν) - forwardDifference t ν (axisComponent A μ)
def curl (t : ℕ) : OneForms L m K →ₗ[ℝ] TwoForms L m K where
  toFun A p := curlAxes t A p.firstAxis p.secondAxis p.origin
  map_add' A B := by
    funext p
    simp only [curlAxes, forwardDifference, axisComponent, Pi.add_apply, Pi.sub_apply]
    ring
  map_smul' c A := by
    funext p
    simp only [curlAxes, forwardDifference, axisComponent, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, RingHom.id_apply]
    ring
def gradAdjoint (L m K t : ℕ) : OneForms L m K →ₗ[ℝ] ZeroForms L m K :=
  formalAdjoint L t (grad t)
def curlAdjoint (L m K t : ℕ) : TwoForms L m K →ₗ[ℝ] OneForms L m K :=
  formalAdjoint L t (curl t)
def scalarLaplacian (L m K t : ℕ) : ZeroForms L m K →ₗ[ℝ] ZeroForms L m K :=
  gradAdjoint L m K t ∘ₗ grad t
def curlCurl (L m K t : ℕ) : OneForms L m K →ₗ[ℝ] OneForms L m K :=
  curlAdjoint L m K t ∘ₗ curl t
def hodgeLaplacian (L m K t : ℕ) : OneForms L m K →ₗ[ℝ] OneForms L m K :=
  curlCurl L m K t + grad t ∘ₗ gradAdjoint L m K t
def outgoingBonds (x : BareSite L m K) : Set (BareOrientedBond L m K) := {b | b.source = x}
def edgesOf (p : BarePlaquette L m K) : Set (BareBond L m K) :=
  {bondFrom p.origin p.firstAxis,
    bondFrom (p.origin + unitStep L m (levelDepth K 0) p.firstAxis) p.secondAxis,
    bondFrom (p.origin + unitStep L m (levelDepth K 0) p.secondAxis) p.firstAxis,
    bondFrom p.origin p.secondAxis}
def sitesOfRegion (K : ℕ) (Ω : Set (FourTorus L m)) : Set (BareSite L m K) := sitesIn Ω
def interiorBonds (K : ℕ) (Ω : Set (FourTorus L m)) : Set (BareBond L m K) :=
  {b | b.1.source ∈ sitesOfRegion K Ω ∧ b.1.target ∈ sitesOfRegion K Ω}
def starBonds (K : ℕ) (Ω : Set (FourTorus L m)) : Set (BareBond L m K) :=
  {b | b.1.source ∈ sitesOfRegion K Ω ∨ b.1.target ∈ sitesOfRegion K Ω}
def frontierBonds (K : ℕ) (Ω : Set (FourTorus L m)) : Set (BareBond L m K) :=
  starBonds K Ω \ interiorBonds K Ω
inductive BondFrame
  | interior
  | star
def framedBonds (K : ℕ) (Ω : Set (FourTorus L m)) : BondFrame → Set (BareBond L m K)
  | BondFrame.interior => interiorBonds K Ω
  | BondFrame.star => starBonds K Ω
def framedPlaquettes (K : ℕ) (Ω : Set (FourTorus L m)) (φ : BondFrame) :
    Set (BarePlaquette L m K) :=
  {p | ∃ b ∈ edgesOf p, b ∈ framedBonds K Ω φ}
def frontierSites (K : ℕ) (Ω : Set (FourTorus L m)) : Set (BareSite L m K) :=
  {x | x ∈ sitesOfRegion K Ω ∧ ∃ b ∈ frontierBonds K Ω, x = b.1.source ∨ x = b.1.target}
def indicatorMul {ι : Type} (X : Set ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := X.indicator
  map_add' f g := by
    funext i
    by_cases h : i ∈ X <;> simp [h]
  map_smul' c f := by
    funext i
    by_cases h : i ∈ X <;> simp [h]
def siteProjection (K : ℕ) (Ω : Set (FourTorus L m)) : ZeroForms L m K →ₗ[ℝ] ZeroForms L m K :=
  indicatorMul (sitesOfRegion K Ω)
def bondProjection (K : ℕ) (Ω : Set (FourTorus L m)) (φ : BondFrame) :
    OneForms L m K →ₗ[ℝ] OneForms L m K :=
  indicatorMul (framedBonds K Ω φ)
def frontierProjection (K : ℕ) (Ω : Set (FourTorus L m)) (φ : BondFrame) :
    OneForms L m K →ₗ[ℝ] OneForms L m K :=
  indicatorMul (starBonds K Ω \ framedBonds K Ω φ)
abbrev zeroFormsOn (K : ℕ) (Ω : Set (FourTorus L m)) : Submodule ℝ (ZeroForms L m K) :=
  LinearMap.range (siteProjection K Ω)
abbrev oneFormsOn (K : ℕ) (Ω : Set (FourTorus L m)) (φ : BondFrame) :
    Submodule ℝ (OneForms L m K) :=
  LinearMap.range (bondProjection K Ω φ)
def compress {V : Type} [AddCommGroup V] [Module ℝ V] (χ X : V →ₗ[ℝ] V) :
    LinearMap.range χ →ₗ[ℝ] LinearMap.range χ :=
  ((χ ∘ₗ X ∘ₗ χ).domRestrict (LinearMap.range χ)).codRestrict (LinearMap.range χ)
    fun f => LinearMap.mem_range_self χ (X (χ f))
def dirichletGrad (K t : ℕ) (Ω : Set (FourTorus L m)) (φ : BondFrame) :
    zeroFormsOn K Ω →ₗ[ℝ] oneFormsOn K Ω φ :=
  ((bondProjection K Ω φ ∘ₗ grad t).domRestrict (zeroFormsOn K Ω)).codRestrict
    (oneFormsOn K Ω φ)
    fun f => LinearMap.mem_range_self (bondProjection K Ω φ) (grad t f.1)
def dirichletGradAdjoint (K t : ℕ) (Ω : Set (FourTorus L m)) (φ : BondFrame) :
    oneFormsOn K Ω φ →ₗ[ℝ] zeroFormsOn K Ω :=
  ((siteProjection K Ω ∘ₗ gradAdjoint L m K t).domRestrict (oneFormsOn K Ω φ)).codRestrict
    (zeroFormsOn K Ω)
    fun A => LinearMap.mem_range_self (siteProjection K Ω) (gradAdjoint L m K t A.1)
def dirichletLaplacian (K t : ℕ) (Ω : Set (FourTorus L m)) :
    zeroFormsOn K Ω →ₗ[ℝ] zeroFormsOn K Ω :=
  compress (siteProjection K Ω) (scalarLaplacian L m K t)
def dirichletHodgeLaplacian (K t : ℕ) (Ω : Set (FourTorus L m)) (φ : BondFrame) :
    oneFormsOn K Ω φ →ₗ[ℝ] oneFormsOn K Ω φ :=
  compress (bondProjection K Ω φ) (hodgeLaplacian L m K t)
def dirichletCurlCurl (K t : ℕ) (Ω : Set (FourTorus L m)) (φ : BondFrame) :
    oneFormsOn K Ω φ →ₗ[ℝ] oneFormsOn K Ω φ :=
  compress (bondProjection K Ω φ) (curlCurl L m K t)
def frontierOpN (K t : ℕ) (Ω : Set (FourTorus L m)) (φ : BondFrame) :
    ZeroForms L m K →ₗ[ℝ] ZeroForms L m K :=
  siteProjection K Ω ∘ₗ gradAdjoint L m K t ∘ₗ frontierProjection K Ω φ ∘ₗ grad t ∘ₗ
    siteProjection K Ω
def frontierOpE (K t : ℕ) (Ω : Set (FourTorus L m)) (φ : BondFrame) :
    OneForms L m K →ₗ[ℝ] OneForms L m K :=
  bondProjection K Ω φ ∘ₗ grad t ∘ₗ (1 - siteProjection K Ω) ∘ₗ gradAdjoint L m K t ∘ₗ
    bondProjection K Ω φ
def frontierOpK (K t : ℕ) (Ω : Set (FourTorus L m)) (φ : BondFrame) :
    ZeroForms L m K →ₗ[ℝ] OneForms L m K :=
  bondProjection K Ω φ ∘ₗ grad t ∘ₗ (1 - siteProjection K Ω) ∘ₗ scalarLaplacian L m K t ∘ₗ
      siteProjection K Ω -
    bondProjection K Ω φ ∘ₗ hodgeLaplacian L m K t ∘ₗ frontierProjection K Ω φ ∘ₗ grad t ∘ₗ
      siteProjection K Ω
end DirichletOperators
end PeriodicLattice
end YangMills.Construction
