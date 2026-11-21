import Mathlib
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Lattice
structure LatticeParameters where
  d : ℕ
  L : ℕ
  offset : ℕ
  two_le_d : 2 ≤ d
  two_le_L : 2 ≤ L
  offset_lt : offset < L
variable {d : ℕ}
def basisVector (μ : Fin d) : Fin d → ℝ := Pi.single μ 1
def periodLattice (ℓ : Fin d → ℝ) : AddSubgroup (Fin d → ℝ) :=
  AddSubgroup.pi Set.univ fun μ => AddSubgroup.zmultiples (ℓ μ)
def PeriodicTorus (ℓ : Fin d → ℝ) : Type := (Fin d → ℝ) ⧸ periodLattice ℓ
instance (ℓ : Fin d → ℝ) : AddCommGroup (PeriodicTorus ℓ) :=
  inferInstanceAs (AddCommGroup ((Fin d → ℝ) ⧸ periodLattice ℓ))
def torusMk (ℓ : Fin d → ℝ) : (Fin d → ℝ) →+ PeriodicTorus ℓ := QuotientAddGroup.mk' (periodLattice ℓ)
theorem torusMk_surjective (ℓ : Fin d → ℝ) : Function.Surjective (torusMk ℓ) :=
  QuotientAddGroup.mk'_surjective _
theorem torusMk_eq_torusMk_iff (ℓ : Fin d → ℝ) (u v : Fin d → ℝ) :
    torusMk ℓ u = torusMk ℓ v ↔ u - v ∈ periodLattice ℓ := by
  rw [← sub_eq_zero, ← map_sub]
  exact QuotientAddGroup.eq_zero_iff (u - v)
def scaledIntegerLattice (d : ℕ) (ε : ℝ) : AddSubgroup (Fin d → ℝ) :=
  AddSubgroup.pi Set.univ fun _ => AddSubgroup.zmultiples ε
def latticeSubgroup (ℓ : Fin d → ℝ) (ε : ℝ) : AddSubgroup (PeriodicTorus ℓ) :=
  (scaledIntegerLattice d ε).map (torusMk ℓ)
class IsCommensurateSpacing (ℓ : Fin d → ℝ) (ε : ℝ) : Prop where
  periods_pos : ∀ μ, 0 < ℓ μ
  spacing_pos : 0 < ε
  ratio_mem : ∀ μ, ∃ n : ℕ, 0 < n ∧ ℓ μ / ε = n
abbrev LatticeSite (ℓ : Fin d → ℝ) (ε : ℝ) : Type := latticeSubgroup ℓ ε
instance finite_latticeSite (ℓ : Fin d → ℝ) (ε : ℝ) [h : IsCommensurateSpacing ℓ ε] :
    Finite (LatticeSite ℓ ε) := by
  have hε : ε ≠ 0 := h.spacing_pos.ne'
  choose n hn hr using h.ratio_mem
  have hℓ : ∀ μ, ℓ μ = n μ * ε := fun μ => by
    have := hr μ
    field_simp at this
    linarith
  have hmem : ∀ k : (μ : Fin d) → Fin (n μ),
      (fun μ => ((k μ : ℕ) : ℤ) • ε) ∈ scaledIntegerLattice d ε := fun k =>
    (AddSubgroup.mem_pi _).mpr fun μ _ => AddSubgroup.mem_zmultiples_iff.mpr ⟨(k μ : ℕ), rfl⟩
  let φ : ((μ : Fin d) → Fin (n μ)) → LatticeSite ℓ ε := fun k =>
    ⟨torusMk ℓ fun μ => ((k μ : ℕ) : ℤ) • ε, AddSubgroup.mem_map_of_mem _ (hmem k)⟩
  refine Finite.of_surjective φ ?_
  rintro ⟨x, u, hu, rfl⟩
  have hm : ∀ μ, ∃ m : ℤ, m • ε = u μ := fun μ =>
    AddSubgroup.mem_zmultiples_iff.mp ((AddSubgroup.mem_pi _).mp hu μ (Set.mem_univ μ))
  choose m hm using hm
  have hnz : ∀ μ, ((n μ : ℕ) : ℤ) ≠ 0 := fun μ => by exact_mod_cast (hn μ).ne'
  have hlt : ∀ μ, (m μ % (n μ : ℤ)).toNat < n μ := fun μ => by
    have h0 := Int.emod_nonneg (m μ) (hnz μ)
    have h1 := Int.emod_lt_of_pos (m μ) (by exact_mod_cast hn μ : (0 : ℤ) < (n μ : ℤ))
    omega
  refine ⟨fun μ => ⟨_, hlt μ⟩, Subtype.ext ?_⟩
  show torusMk ℓ _ = torusMk ℓ u
  rw [torusMk_eq_torusMk_iff]
  refine (AddSubgroup.mem_pi _).mpr fun μ _ =>
    AddSubgroup.mem_zmultiples_iff.mpr ⟨-(m μ / (n μ : ℤ)), ?_⟩
  have h0 := Int.emod_nonneg (m μ) (hnz μ)
  have hcast : (((m μ % (n μ : ℤ)).toNat : ℕ) : ℤ) = m μ % (n μ : ℤ) := Int.toNat_of_nonneg h0
  have hdiv : m μ % (n μ : ℤ) = m μ - (n μ : ℤ) * (m μ / (n μ : ℤ)) := by
    have := Int.mul_ediv_add_emod (m μ) (n μ : ℤ)
    omega
  have hval := hcast.trans hdiv
  simp only [Pi.sub_apply, ← hm μ, hval, zsmul_eq_mul, hℓ μ]
  push_cast
  ring
noncomputable instance (ℓ : Fin d → ℝ) (ε : ℝ) [IsCommensurateSpacing ℓ ε] :
    Fintype (LatticeSite ℓ ε) :=
  Fintype.ofFinite _
def latticeStep (ℓ : Fin d → ℝ) (ε : ℝ) (μ : Fin d) : LatticeSite ℓ ε :=
  ⟨torusMk ℓ (ε • basisVector μ), AddSubgroup.mem_map_of_mem _ <| (AddSubgroup.mem_pi _).mpr fun ν _ =>
    AddSubgroup.mem_zmultiples_iff.mpr ⟨if ν = μ then 1 else 0, by
      by_cases h : ν = μ <;> simp [basisVector, h]⟩⟩
abbrev Link (ℓ : Fin d → ℝ) (ε : ℝ) : Type := LatticeSite ℓ ε × Fin d
def Link.head {ℓ : Fin d → ℝ} {ε : ℝ} (b : Link ℓ ε) : LatticeSite ℓ ε := b.1 + latticeStep ℓ ε b.2
def Link.ends {ℓ : Fin d → ℝ} {ε : ℝ} (b : Link ℓ ε) : Set (LatticeSite ℓ ε) := {b.1, b.head}
@[ext]
structure LatticePlaquette (ℓ : Fin d → ℝ) (ε : ℝ) where
  base : LatticeSite ℓ ε
  first : Fin d
  second : Fin d
  lt : first < second
instance (ℓ : Fin d → ℝ) (ε : ℝ) [IsCommensurateSpacing ℓ ε] : Finite (LatticePlaquette ℓ ε) :=
  Finite.of_injective (fun p : LatticePlaquette ℓ ε => (p.base, p.first, p.second)) fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact LatticePlaquette.ext h.1 h.2.1 h.2.2
noncomputable instance (ℓ : Fin d → ℝ) (ε : ℝ) [IsCommensurateSpacing ℓ ε] :
    Fintype (LatticePlaquette ℓ ε) :=
  Fintype.ofFinite _
def LatticePlaquette.vertices {ℓ : Fin d → ℝ} {ε : ℝ} (p : LatticePlaquette ℓ ε) :
    Set (LatticeSite ℓ ε) :=
  {p.base, p.base + latticeStep ℓ ε p.first,
    p.base + latticeStep ℓ ε p.first + latticeStep ℓ ε p.second,
    p.base + latticeStep ℓ ε p.second}
def LatticePlaquette.boundaryLinks {ℓ : Fin d → ℝ} {ε : ℝ} (p : LatticePlaquette ℓ ε) :
    Set (Link ℓ ε) :=
  {(p.base, p.first), (p.base + latticeStep ℓ ε p.first, p.second),
    (p.base + latticeStep ℓ ε p.second, p.first), (p.base, p.second)}
abbrev Cochain0 (ℓ : Fin d → ℝ) (ε : ℝ) : Type := LatticeSite ℓ ε → ℝ
abbrev Cochain1 (ℓ : Fin d → ℝ) (ε : ℝ) : Type := Link ℓ ε → ℝ
abbrev Cochain2 (ℓ : Fin d → ℝ) (ε : ℝ) : Type := LatticePlaquette ℓ ε → ℝ
def latticeInner (d : ℕ) (ε : ℝ) {ι : Type*} [Fintype ι] (f g : ι → ℝ) : ℝ :=
  ε ^ d * ∑ i, f i * g i
def latticeNorm (d : ℕ) (ε : ℝ) {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ :=
  Real.sqrt (latticeInner d ε f f)
def linkComponent {ℓ : Fin d → ℝ} {ε : ℝ} (A : Cochain1 ℓ ε) (μ : Fin d) : Cochain0 ℓ ε :=
  fun x => A (x, μ)
structure LinkStep (ℓ : Fin d → ℝ) (ε : ℝ) where
  link : Link ℓ ε
  forward : Bool
def LinkStep.source {ℓ : Fin d → ℝ} {ε : ℝ} (t : LinkStep ℓ ε) : LatticeSite ℓ ε :=
  if t.forward then t.link.1 else t.link.head
def LinkStep.target {ℓ : Fin d → ℝ} {ε : ℝ} (t : LinkStep ℓ ε) : LatticeSite ℓ ε :=
  if t.forward then t.link.head else t.link.1
def IsWalkFrom {ℓ : Fin d → ℝ} {ε : ℝ} : LatticeSite ℓ ε → List (LinkStep ℓ ε) → Prop
  | _, [] => True
  | x, t :: ts => t.source = x ∧ IsWalkFrom t.target ts
structure LatticePath (ℓ : Fin d → ℝ) (ε : ℝ) where
  origin : LatticeSite ℓ ε
  steps : List (LinkStep ℓ ε)
  walk : IsWalkFrom origin steps
def pathIntegral {ℓ : Fin d → ℝ} {ε : ℝ} (A : Cochain1 ℓ ε) (Γ : LatticePath ℓ ε) : ℝ :=
  (Γ.steps.map fun t => if t.forward then A t.link else -A t.link).sum
def latticeGradient (ℓ : Fin d → ℝ) (ε : ℝ) : Cochain0 ℓ ε →ₗ[ℝ] Cochain1 ℓ ε where
  toFun lam b := ε⁻¹ * (lam (b.1 + latticeStep ℓ ε b.2) - lam b.1)
  map_add' f g := by
    funext b
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def latticeCurl (ℓ : Fin d → ℝ) (ε : ℝ) : Cochain1 ℓ ε →ₗ[ℝ] Cochain2 ℓ ε where
  toFun A p := ε⁻¹ * (A (p.base, p.first) + A (p.base + latticeStep ℓ ε p.first, p.second)
    - A (p.base + latticeStep ℓ ε p.second, p.first) - A (p.base, p.second))
  map_add' A B := by
    funext p
    simp only [Pi.add_apply]
    ring
  map_smul' c A := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
open Classical in
def latticeAdjoint {ι κ : Type*} [Fintype ι] [Fintype κ] (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    (κ → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun g i := ∑ j, T (Pi.single i 1) j * g j
  map_add' f g := by
    funext i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
def latticeDivergence (ℓ : Fin d → ℝ) (ε : ℝ) [IsCommensurateSpacing ℓ ε] :
    Cochain1 ℓ ε →ₗ[ℝ] Cochain0 ℓ ε :=
  latticeAdjoint (latticeGradient ℓ ε)
def latticeCurlAdjoint (ℓ : Fin d → ℝ) (ε : ℝ) [IsCommensurateSpacing ℓ ε] :
    Cochain2 ℓ ε →ₗ[ℝ] Cochain1 ℓ ε :=
  latticeAdjoint (latticeCurl ℓ ε)
def latticeLaplacian0 (ℓ : Fin d → ℝ) (ε : ℝ) [IsCommensurateSpacing ℓ ε] :
    Cochain0 ℓ ε →ₗ[ℝ] Cochain0 ℓ ε :=
  latticeDivergence ℓ ε ∘ₗ latticeGradient ℓ ε
def linksTouching {ℓ : Fin d → ℝ} {ε : ℝ} (X : Set (LatticeSite ℓ ε)) : Set (Link ℓ ε) :=
  {b | b.1 ∈ X ∨ b.head ∈ X}
def linksWithin {ℓ : Fin d → ℝ} {ε : ℝ} (X : Set (LatticeSite ℓ ε)) : Set (Link ℓ ε) :=
  {b | b.1 ∈ X ∧ b.head ∈ X}
def supportedIn {ι : Type*} (S : Set ι) : Submodule ℝ (ι → ℝ) where
  carrier := {f | ∀ i, i ∉ S → f i = 0}
  add_mem' hf hg i hi := by simp [hf i hi, hg i hi]
  zero_mem' _ _ := rfl
  smul_mem' c _ hf i hi := by simp [hf i hi]
end YangMills.Construction.Lattice
