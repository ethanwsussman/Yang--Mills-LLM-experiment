import YangMills.Construction.Geometry.ToriGeneralSide
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TorusMetric
noncomputable section
namespace GeneralTorus
section Generic
variable {V U : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup U] [Module ℝ U]
def IsAdjointFor (p : V → V → ℝ) (q : U → U → ℝ) (K : V →ₗ[ℝ] U) (T : U →ₗ[ℝ] V) : Prop :=
  ∀ v u, q (K v) u = p v (T u)
def adjointFor (p : V → V → ℝ) (q : U → U → ℝ) (K : V →ₗ[ℝ] U) : U →ₗ[ℝ] V :=
  Classical.epsilon (IsAdjointFor p q K)
def IsOrthProjFor (p : V → V → ℝ) (E : Submodule ℝ V) (P : V →ₗ[ℝ] ↥E) : Prop :=
  (∀ e : ↥E, P e = e) ∧ ∀ v, ∀ e ∈ E, p (v - P v) e = 0
def orthProjFor (p : V → V → ℝ) (E : Submodule ℝ V) : V →ₗ[ℝ] ↥E :=
  Classical.epsilon (IsOrthProjFor p E)
end Generic
def halfSpan (N : ℕ) : ℝ := ((N : ℝ) - 1) / 2
open Classical in
def tentMultiplicity (N : ℕ) (s : ℤ) : ℕ :=
  ((Finset.range N).filter fun i : ℕ => |(s : ℝ) - (i : ℝ)| ≤ halfSpan N).card
def MemBondWindow (N : ℕ) (μ : Fin 4) (k : Fin 4 → ℤ) : Prop :=
  -halfSpan N ≤ (k μ : ℝ) ∧ (k μ : ℝ) ≤ 3 * halfSpan N + 1 ∧
    ∀ ν, ν ≠ μ → |(k ν : ℝ)| ≤ halfSpan N
open Classical in
def tentKernel {S : ℝ} (N : ℕ) (σ : ℝ) (y : Torus4 S) (μ : Fin 4) (x : Torus4 S) : ℝ :=
  if h : ∃ k : Fin 4 → ℤ, MemBondWindow N μ k ∧ x = y + torusProj S fun ν => σ * (k ν : ℝ) then
    ((N : ℝ) ^ 5)⁻¹ * (tentMultiplicity N (h.choose μ) : ℝ)
  else 0
theorem finite_latticeSite {S σ : ℝ} (h : IsEvenMultipleOf S σ) : Finite (LatticeSite S σ) := by
  obtain ⟨k, hk, hS⟩ := h
  have hNpos : 0 < 2 * k := by omega
  set N : ℕ := 2 * k with hN
  have hSN : S = (N : ℝ) * σ := by
    rw [hS, hN]
    push_cast
    ring
  have hsub : (spacingLattice S σ : Set (Torus4 S)) ⊆
      range fun j : Fin 4 → Fin N => torusProj S fun μ => σ * ((j μ : ℕ) : ℝ) := by
    rintro x ⟨m, rfl⟩
    have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hNpos.ne'
    have hNi : 0 < (N : ℤ) := by exact_mod_cast hNpos
    refine ⟨fun μ => ⟨(m μ % N).toNat, ?_⟩, ?_⟩
    · have h1 := Int.emod_lt_of_pos (m μ) hNi
      have h2 := Int.emod_nonneg (m μ) hNz
      omega
    · funext μ
      have h2 := Int.emod_nonneg (m μ) hNz
      have hcast : (((m μ % N).toNat : ℕ) : ℝ) = ((m μ % N : ℤ) : ℝ) := by
        have : (((m μ % N).toNat : ℕ) : ℤ) = m μ % N := Int.toNat_of_nonneg h2
        exact_mod_cast this
      have hdiv : σ * (m μ : ℝ) = σ * ((m μ % N : ℤ) : ℝ) + ((m μ / N : ℤ) : ℝ) * S := by
        have h3 : (m μ : ℝ) = ((m μ % N : ℤ) : ℝ) + (N : ℝ) * ((m μ / N : ℤ) : ℝ) := by
          have := Int.emod_add_mul_ediv (m μ) N
          exact_mod_cast this.symm
        rw [hSN]
        nth_rewrite 1 [h3]
        ring
      have hzero : (((((m μ / N : ℤ) : ℝ) * S : ℝ)) : AddCircle S) = 0 :=
        (AddCircle.coe_eq_zero_iff S).2 ⟨m μ / N, by simp⟩
      simp only [torusProj]
      rw [hcast, hdiv, AddCircle.coe_add, hzero, add_zero]
  exact ((finite_range _).subset hsub).to_subtype
namespace ScaleData
variable (D : ScaleData)
abbrev PosBond (n : ℕ) : Type := {c : D.BondAt n // c.IsPositivelyOriented}
abbrev BaseSite : Type := D.SiteAt 0
abbrev BaseBond : Type := D.PosBond 0
abbrev BasePlaquette : Type := D.PlaquetteAt 0
abbrev SiteField : Type := D.BaseSite → ℝ
abbrev BondField : Type := D.BaseBond → ℝ
abbrev PlaquetteField : Type := D.BasePlaquette → ℝ
def blockSize (n : ℕ) : ℕ := D.L ^ n
theorem isEvenMultipleOf_baseSpacing : IsEvenMultipleOf D.torusSide (D.levelSpacing 0) := by
  obtain ⟨k, hk, hS⟩ := D.torusSide_evenMultiple
  have hL : 0 < D.L := by
    have := D.blocking.thirteen_le
    omega
  refine ⟨k * D.L ^ D.lastLevel, Nat.mul_pos hk (pow_pos hL _), ?_⟩
  rw [hS, levelSpacing]
  push_cast
  ring
instance : Finite D.BaseSite := finite_latticeSite D.isEvenMultipleOf_baseSpacing
variable {D}
def bondFrom {n : ℕ} (x : D.SiteAt n) (μ : Fin 4) : D.PosBond n :=
  ⟨LatticeBond.plus x μ, μ, by simp [LatticeBond.plus]⟩
def posBondDir {n : ℕ} (c : D.PosBond n) : Fin 4 := c.2.choose
def bondSupport {n : ℕ} (c : D.PosBond n) : Set D.Space :=
  D.cubeAt n (c.1.src : D.Space) ∪ D.cubeAt n (c.1.tgt : D.Space)
variable (D)
def siteInner (f f' : D.SiteField) : ℝ := D.levelSpacing 0 ^ 4 * ∑ᶠ x, f x * f' x
def bondInner (A A' : D.BondField) : ℝ := D.levelSpacing 0 ^ 4 * ∑ᶠ b, A b * A' b
def plaquetteInner (F F' : D.PlaquetteField) : ℝ := D.levelSpacing 0 ^ 4 * ∑ᶠ p, F p * F' p
def siteL2Norm (f : D.SiteField) : ℝ := Real.sqrt (D.siteInner f f)
def plaquetteL2Norm (F : D.PlaquetteField) : ℝ := Real.sqrt (D.plaquetteInner F F)
def bondSupNorm (A : D.BondField) : ℝ := ⨆ b, |A b|
def formComponent (μ : Fin 4) : D.BondField →ₗ[ℝ] D.SiteField where
  toFun A x := A (bondFrom x μ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def forwardDiff (μ : Fin 4) : D.SiteField →ₗ[ℝ] D.SiteField where
  toFun f x := (D.levelSpacing 0)⁻¹ * (f (x + unitStep D.torusSide (D.levelSpacing 0) μ) - f x)
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def grad : D.SiteField →ₗ[ℝ] D.BondField where
  toFun f c := D.forwardDiff (posBondDir c) f c.1.src
  map_add' f g := by
    funext c
    simp only [map_add, Pi.add_apply]
  map_smul' a f := by
    funext c
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
def plaquetteCurl : D.BondField →ₗ[ℝ] D.PlaquetteField where
  toFun A p := D.forwardDiff p.dir₁ (D.formComponent p.dir₂ A) p.basePoint -
    D.forwardDiff p.dir₂ (D.formComponent p.dir₁ A) p.basePoint
  map_add' A A' := by
    funext p
    simp only [map_add, Pi.add_apply]
    ring
  map_smul' a A := by
    funext p
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def gradAdjoint : D.BondField →ₗ[ℝ] D.SiteField :=
  adjointFor D.siteInner D.bondInner D.grad
def plaquetteCurlAdjoint : D.PlaquetteField →ₗ[ℝ] D.BondField :=
  adjointFor D.bondInner D.plaquetteInner D.plaquetteCurl
def blockSiteMean (n : ℕ) : D.SiteField →ₗ[ℝ] (D.Space → ℝ) where
  toFun f y := ((D.blockSize n : ℝ) ^ 4)⁻¹ *
    ∑ᶠ x ∈ sitesIn (S := D.torusSide) (D.levelSpacing 0) (D.baseBlock n y), f x
  map_add' f g := by
    funext y
    simp only [Pi.add_apply]
    rw [finsum_mem_add_distrib (toFinite _), mul_add]
  map_smul' c f := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← mul_finsum_mem]
    ring
def blockBondMean (n : ℕ) : D.BondField →ₗ[ℝ] (D.PosBond n → ℝ) where
  toFun A c := ((D.blockSize n : ℝ) ^ 5)⁻¹ *
    ∑ᶠ x ∈ sitesIn (S := D.torusSide) (D.levelSpacing 0) (D.baseBlock n (c.1.src : D.Space)),
      ∑ i ∈ Finset.range (D.blockSize n), D.formComponent (posBondDir c) A
        (x + i • unitStep D.torusSide (D.levelSpacing 0) (posBondDir c))
  map_add' A A' := by
    funext c
    simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]
    rw [finsum_mem_add_distrib (toFinite _), mul_add]
  map_smul' a A := by
    funext c
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    rw [← mul_finsum_mem]
    ring
def meanWeight {n : ℕ} (c : D.PosBond n) (x : D.Space) : ℝ :=
  tentKernel (D.blockSize n) (D.levelSpacing 0) (c.1.src : D.Space) (posBondDir c) x
open Classical in
def oneStepWeight {n : ℕ} (c' : D.PosBond (n + 1)) (c'' : D.PosBond n) : ℝ :=
  if posBondDir c'' = posBondDir c' then
    tentKernel D.L (D.levelSpacing n) (c'.1.src : D.Space) (posBondDir c') (c''.1.src : D.Space)
  else 0
end ScaleData
namespace SeparatedChain
variable {D : ScaleData} (B : SeparatedChain D)
def dirichletSites : Submodule ℝ D.SiteField where
  carrier := {f | ∀ x : D.BaseSite, (x : D.Space) ∉ B.set 0 → f x = 0}
  add_mem' := by
    intro f g hf hg x hx
    simp [hf x hx, hg x hx]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c f hf x hx
    simp [hf x hx]
def meetingBonds : Set D.BaseBond :=
  {b | (b.1.src : D.Space) ∈ B.set 0 ∨ (b.1.tgt : D.Space) ∈ B.set 0}
def interiorBonds : Set D.BaseBond :=
  {b | (b.1.src : D.Space) ∈ B.set 0 ∧ (b.1.tgt : D.Space) ∈ B.set 0}
open Classical in
def anchor (b : D.BaseBond) : D.BaseSite :=
  if (b.1.src : D.Space) ∈ B.set 0 then b.1.src else b.1.tgt
def LiesInCell (b : D.BaseBond) (y : D.Space) : Prop := (B.anchor b : D.Space) ∈ B.localCube y
def siteProj : D.SiteField →ₗ[ℝ] ↥B.dirichletSites := orthProjFor D.siteInner B.dirichletSites
def dirichletLap : Module.End ℝ ↥B.dirichletSites :=
  B.siteProj ∘ₗ D.gradAdjoint ∘ₗ D.grad ∘ₗ B.dirichletSites.subtype
def shellIndex (y : D.Space) : ℕ := sInf {n | y ∈ B.shellSites n}
def siteMeans : ↥B.dirichletSites →ₗ[ℝ] (↥B.shellSitesUnion → ℝ) where
  toFun f y := D.blockSiteMean (B.shellIndex y) f y
  map_add' f g := by
    funext y
    simp only [Submodule.coe_add, map_add, Pi.add_apply]
  map_smul' c f := by
    funext y
    simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, RingHom.id_apply]
def siteMeansKer : Submodule ℝ ↥B.dirichletSites := LinearMap.ker B.siteMeans
def dirichletInner (f f' : ↥B.dirichletSites) : ℝ := D.siteInner f f'
def lapImageProj : Module.End ℝ ↥B.dirichletSites :=
  (B.siteMeansKer.map B.dirichletLap).subtype ∘ₗ
    orthProjFor B.dirichletInner (B.siteMeansKer.map B.dirichletLap)
end SeparatedChain
inductive BondSetChoice
  | meeting
  | interior
structure GaugeSetting where
  data : ScaleData
  chain : SeparatedChain data
  L_le_gapCount : data.L ≤ data.gapCount
  choice : BondSetChoice
  mass : ℝ
  mass_pos : 0 < mass
namespace GaugeSetting
variable (W : GaugeSetting)
def bondSet : Set W.data.BaseBond :=
  match W.choice with
  | .meeting => W.chain.meetingBonds
  | .interior => W.chain.interiorBonds
def formSubspace : Submodule ℝ W.data.BondField where
  carrier := {A | ∀ b, b ∉ W.bondSet → A b = 0}
  add_mem' := by
    intro f g hf hg x hx
    simp [hf x hx, hg x hx]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c f hf x hx
    simp [hf x hx]
def SupportedInCell (J : W.data.BondField) (y : W.data.Space) : Prop :=
  ∀ b ∈ W.bondSet, ¬W.chain.LiesInCell b y → J b = 0
def formProj : W.data.BondField →ₗ[ℝ] ↥W.formSubspace :=
  orthProjFor W.data.bondInner W.formSubspace
def formInner (A A' : ↥W.formSubspace) : ℝ := W.data.bondInner A A'
def coarseBondsAt : (n : ℕ) → Set (W.data.PosBond n)
  | 0 => {c | c ∈ W.bondSet ∧ (c.1.src : W.data.Space) ∉ W.chain.set 1 ∧
      (c.1.tgt : W.data.Space) ∉ W.chain.set 1}
  | n + 1 => {c | ((c.1.src : W.data.Space) ∈ W.chain.set (n + 1) ∨
        (c.1.tgt : W.data.Space) ∈ W.chain.set (n + 1)) ∧
      (c.1.src : W.data.Space) ∉ W.chain.set (n + 2) ∧
      (c.1.tgt : W.data.Space) ∉ W.chain.set (n + 2)}
abbrev CoarseBond : Type := Σ n : Fin (W.data.lastLevel + 1), ↥(W.coarseBondsAt n)
abbrev CoarseField : Type := W.CoarseBond → ℝ
variable {W}
def coarseLevel (c : W.CoarseBond) : ℕ := c.1
def coarseSpacing (c : W.CoarseBond) : ℝ := W.data.levelSpacing c.1
def coarseSrc (c : W.CoarseBond) : W.data.Space := (c.2.1.1.src : W.data.Space)
def coarseTgt (c : W.CoarseBond) : W.data.Space := (c.2.1.1.tgt : W.data.Space)
open Classical in
def coarseAnchor (c : W.CoarseBond) : W.data.Space :=
  if coarseSrc c ∈ W.chain.set c.1 then coarseSrc c else coarseTgt c
def coarseDist (c c' : W.CoarseBond) : ℝ := W.chain.scaledDist (coarseAnchor c) (coarseAnchor c')
def siteCoarseDist (y : W.data.Space) (c : W.CoarseBond) : ℝ :=
  W.chain.scaledDist y (coarseAnchor c)
variable (W)
def coarseInner (f f' : W.CoarseField) : ℝ := ∑ᶠ c, coarseSpacing c ^ 4 * (f c * f' c)
def coarseL2Norm (f : W.CoarseField) : ℝ := Real.sqrt (W.coarseInner f f)
def spacingMul : Module.End ℝ W.CoarseField where
  toFun f c := coarseSpacing c * f c
  map_add' f g := by
    funext c
    simp only [Pi.add_apply]
    ring
  map_smul' r f := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def massMul : Module.End ℝ W.CoarseField where
  toFun f c := W.mass * (coarseSpacing c ^ 2)⁻¹ * f c
  map_add' f g := by
    funext c
    simp only [Pi.add_apply]
    ring
  map_smul' r f := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def meanOp : ↥W.formSubspace →ₗ[ℝ] W.CoarseField where
  toFun A c := W.data.blockBondMean c.1 A c.2.1
  map_add' A A' := by
    funext c
    simp only [Submodule.coe_add, map_add, Pi.add_apply]
  map_smul' r A := by
    funext c
    simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, RingHom.id_apply]
def meanOpAdjoint : W.CoarseField →ₗ[ℝ] ↥W.formSubspace :=
  adjointFor W.formInner W.coarseInner W.meanOp
def massPart : Module.End ℝ ↥W.formSubspace :=
  W.meanOpAdjoint ∘ₗ W.massMul ∘ₗ W.meanOp
def gaugeLap : Module.End ℝ ↥W.formSubspace :=
  W.formProj ∘ₗ
      (W.data.plaquetteCurlAdjoint ∘ₗ W.data.plaquetteCurl +
        W.data.grad ∘ₗ W.chain.dirichletSites.subtype ∘ₗ
          W.chain.lapImageProj ∘ₗ W.chain.siteProj ∘ₗ
            W.data.gradAdjoint) ∘ₗ W.formSubspace.subtype +
    W.massPart
def curlLap : Module.End ℝ ↥W.formSubspace :=
  W.formProj ∘ₗ (W.data.plaquetteCurlAdjoint ∘ₗ W.data.plaquetteCurl) ∘ₗ W.formSubspace.subtype +
    W.massPart
def greenOp : Module.End ℝ ↥W.formSubspace := Ring.inverse W.gaugeLap
def coarseGreen : Module.End ℝ W.CoarseField :=
  W.meanOp ∘ₗ W.greenOp ∘ₗ W.meanOpAdjoint
def WellPosed : Prop :=
  (∀ A : ↥W.formSubspace, A ≠ 0 → 0 < W.formInner A (W.gaugeLap A)) ∧ IsUnit W.coarseGreen
def harmonicExt : W.CoarseField →ₗ[ℝ] ↥W.formSubspace :=
  W.greenOp ∘ₗ W.meanOpAdjoint ∘ₗ Ring.inverse W.coarseGreen
def coarseLap : Module.End ℝ W.CoarseField :=
  Ring.inverse W.coarseGreen - W.massMul
open Classical in
def coarseDelta (c : W.CoarseBond) : W.CoarseField := Pi.single c 1
def coarseUnit (c : W.CoarseBond) : W.CoarseField := (coarseSpacing c ^ 2)⁻¹ • W.coarseDelta c
def matrixEntry (K : Module.End ℝ W.CoarseField) (c c' : W.CoarseBond) : ℝ :=
  W.coarseInner (W.coarseUnit c) (K (W.coarseUnit c'))
def kernelEntry (K : Module.End ℝ W.CoarseField) (c c' : W.CoarseBond) : ℝ :=
  K (W.coarseDelta c') c
def harmonicExtKernel (b : ↥W.bondSet) (c : W.CoarseBond) : ℝ :=
  (W.harmonicExt (W.coarseDelta c) : W.data.BondField) b
def supportedOn (Y : Set W.CoarseBond) : Submodule ℝ W.CoarseField where
  carrier := {f | ∀ c, c ∉ Y → f c = 0}
  add_mem' := by
    intro f g hf hg x hx
    simp [hf x hx, hg x hx]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro r f hf x hx
    simp [hf x hx]
def restrictTo (Y : Set W.CoarseBond) : W.CoarseField →ₗ[ℝ] ↥(W.supportedOn Y) where
  toFun f := ⟨Y.indicator f, fun _ hc => indicator_of_notMem hc f⟩
  map_add' f g := Subtype.ext (indicator_add Y f g)
  map_smul' r f := Subtype.ext (indicator_const_smul Y r f)
def indicatorMul (Y : Set W.CoarseBond) : Module.End ℝ W.CoarseField :=
  (W.supportedOn Y).subtype ∘ₗ W.restrictTo Y
def compress (Y : Set W.CoarseBond) (K : Module.End ℝ W.CoarseField) :
    Module.End ℝ ↥(W.supportedOn Y) :=
  W.restrictTo Y ∘ₗ K ∘ₗ (W.supportedOn Y).subtype
def compressInverse (Y : Set W.CoarseBond) (K : Module.End ℝ W.CoarseField) :
    Module.End ℝ W.CoarseField :=
  (W.supportedOn Y).subtype ∘ₗ Ring.inverse (W.compress Y K) ∘ₗ W.restrictTo Y
end GaugeSetting
end GeneralTorus
end
end YangMills.Construction
