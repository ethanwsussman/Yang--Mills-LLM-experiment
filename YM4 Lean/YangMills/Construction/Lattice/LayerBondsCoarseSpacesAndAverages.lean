import YangMills.Construction.Lattice.DirichletDifferenceOperators
import YangMills.Construction.Lattice.SeparatedSequenceData
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators
noncomputable section
namespace SeparatedSequences.BaseParameters
theorem site_finite {L : ℕ} (hL : 0 < L) (m : ℕ) (j : ℤ) : Finite (Site L m j) := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  set N : ℕ := 2 * L ^ (m + j.natAbs) with hN_def
  have hN : 0 < N := by positivity
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = (j.natAbs : ℤ) - j :=
    ⟨((j.natAbs : ℤ) - j).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hper : (N : ℝ) * meshSize L j = ((L ^ e : ℕ) : ℝ) * torusSide L m := by
    have h : (L : ℝ) ^ (j.natAbs : ℤ) * (L : ℝ) ^ (-j) = (L : ℝ) ^ (e : ℤ) := by
      rw [← zpow_add₀ hL0, he]
      congr 1
    simp only [zpow_natCast] at h
    simp only [hN_def, meshSize, torusSide]
    push_cast
    rw [pow_add, ← h]
    ring
  let f : (Fin 4 → Fin N) → Site L m j := fun k =>
    ⟨fun μ => ((((k μ : ℕ) : ℤ) : ℝ) * meshSize L j : ℝ), ⟨fun μ => ((k μ : ℕ) : ℤ), fun _ => rfl⟩⟩
  refine Finite.of_surjective f ?_
  rintro ⟨x, n, hn⟩
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  refine ⟨fun μ => ⟨(n μ % (N : ℤ)).toNat, ?_⟩, Subtype.ext (funext fun μ => ?_)⟩
  · have h1 := Int.emod_nonneg (n μ) hNpos.ne'
    have h2 := Int.emod_lt_of_pos (n μ) hNpos
    omega
  · have h1 := Int.emod_nonneg (n μ) hNpos.ne'
    have hcast : (((n μ % (N : ℤ)).toNat : ℕ) : ℤ) = n μ % (N : ℤ) := Int.toNat_of_nonneg h1
    change (((((((n μ % (N : ℤ)).toNat : ℕ) : ℤ) : ℝ) * meshSize L j : ℝ)) : AddCircle (torusSide L m)) = x μ
    rw [hcast, hn μ, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨-(n μ / (N : ℤ)) * ((L ^ e : ℕ) : ℤ), ?_⟩
    have hmod : n μ % (N : ℤ) = n μ - (N : ℤ) * (n μ / (N : ℤ)) := by
      have := Int.emod_add_mul_ediv (n μ) (N : ℤ)
      omega
    rw [hmod, zsmul_eq_mul]
    push_cast
    have hp := hper
    push_cast at hp
    linear_combination (-((n μ / (N : ℤ) : ℤ) : ℝ)) * hp * (-1)
variable (D : BaseParameters)
abbrev LevelBond (n : ℕ) : Type := PositivelyOrientedBond D.L D.m (levelDepth D.K n)
instance instFiniteLatticeSite (n : ℕ) : Finite (D.LatticeSite n) :=
  site_finite (by have := D.three_le_L; omega) _ _
instance instFiniteLevelBond (n : ℕ) : Finite (D.LevelBond n) :=
  Finite.of_injective (fun c : D.LevelBond n => (c.1.source, c.1.target)) fun _ _ h =>
    Subtype.ext (Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
def bondAxis {L m : ℕ} {j : ℤ} (c : PositivelyOrientedBond L m j) : Fin 4 := c.2.choose
variable (Ω : ℕ → Set D.Torus) (φ : BondFrame)
def layerBondSet : (n : ℕ) → Set (D.LevelBond n)
  | 0 => {c | c ∈ framedBonds D.K (Ω 0) φ ∧ c.1 ∉ bondsMeeting (D.memberAt Ω 1)}
  | n + 1 => {c | c.1 ∈ bondsMeeting (D.memberAt Ω (n + 1)) ∧ c.1 ∉ bondsMeeting (D.memberAt Ω (n + 2))}
def principalBonds : Set (Σ n : ℕ, D.LevelBond n) :=
  {c | c.1 ≤ D.t ∧ c.2 ∈ D.layerBondSet Ω φ c.1}
def bondMesh (c : Σ n : ℕ, D.LevelBond n) : ℝ := D.levelMeshRatio c.1
def IsInnerBond {n : ℕ} (c : D.LevelBond n) : Prop :=
  c.1.source ∈ D.layerSites Ω n ∧ c.1.target ∈ D.layerSites Ω n
def IsOuterEndpoint {n : ℕ} (c : D.LevelBond n) (y : D.LatticeSite n) : Prop :=
  1 ≤ n ∧ (y = c.1.source ∨ y = c.1.target) ∧ (y : D.Torus) ∉ D.memberAt Ω n
def IsOutgoingBond {n : ℕ} (c : D.LevelBond n) : Prop := ∃ y, D.IsOuterEndpoint Ω c y
abbrev CoarseZeroForms : Type := ↥(D.allLayerPoints Ω) → ℝ
abbrev CoarseOneForms : Type := ↥(D.principalBonds Ω φ) → ℝ
instance instFiniteAllLayerPoints : Finite ↥(D.allLayerPoints Ω) :=
  Set.Finite.to_subtype (Set.Finite.biUnion (Set.finite_Iic _) fun _ _ =>
    (Set.toFinite _).image _)
instance instFinitePrincipalBonds : Finite ↥(D.principalBonds Ω φ) := by
  refine Set.Finite.to_subtype (Set.Finite.subset
    (Set.Finite.biUnion (Set.finite_Iic D.t) fun n _ =>
      (Set.finite_univ (α := D.LevelBond n)).image (Sigma.mk n)) ?_)
  rintro ⟨n, c⟩ hc
  exact mem_biUnion (show n ∈ Iic D.t from hc.1) ⟨c, mem_univ _, rfl⟩
variable {D Ω φ}
open Classical in
def pointValue (ω : D.CoarseZeroForms Ω) (y : D.Torus) : ℝ :=
  if h : y ∈ D.allLayerPoints Ω then ω ⟨y, h⟩ else 0
open Classical in
def principalBondValue (B : D.CoarseOneForms Ω φ) (c : Σ n : ℕ, D.LevelBond n) : ℝ :=
  if h : c ∈ D.principalBonds Ω φ then B ⟨c, h⟩ else 0
variable (D Ω φ)
def coarseZeroInner (ω ω' : D.CoarseZeroForms Ω) : ℝ :=
  ∑ n ∈ Finset.range (D.t + 1), D.levelMeshRatio n ^ dimension *
    ∑ᶠ y : ↥(D.layerSites Ω n), pointValue ω (y.1 : D.Torus) * pointValue ω' (y.1 : D.Torus)
def coarseOneInner (B B' : D.CoarseOneForms Ω φ) : ℝ :=
  ∑ n ∈ Finset.range (D.t + 1), D.levelMeshRatio n ^ dimension *
    ∑ᶠ c : ↥(D.layerBondSet Ω φ n), principalBondValue B ⟨n, c.1⟩ * principalBondValue B' ⟨n, c.1⟩
theorem finsum_add_finite {ι : Type} [Finite ι] (f g : ι → ℝ) :
    ∑ᶠ i, (f i + g i) = ∑ᶠ i, f i + ∑ᶠ i, g i :=
  finsum_add_distrib (Set.toFinite _) (Set.toFinite _)
theorem finsum_const_mul_finite {ι : Type} [Finite ι] (c : ℝ) (f : ι → ℝ) :
    ∑ᶠ i, c * f i = c * ∑ᶠ i, f i :=
  (mul_finsum f c).symm
def blockAverageZero (n : ℕ) : ZeroForms D.L D.m D.K →ₗ[ℝ] (D.LatticeSite n → ℝ) where
  toFun f y := ((D.L : ℝ) ^ (n * dimension))⁻¹ *
    ∑ᶠ x : {x : BareSite D.L D.m D.K // (x : D.Torus) ∈ fineBlock (D := D) y}, f x.1
  map_add' f g := by
    funext y
    simp only [Pi.add_apply, finsum_add_finite, mul_add]
  map_smul' c f := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, finsum_const_mul_finite]
    ring
theorem lineSum_add {L m K : ℕ} (A B : OneForms L m K) (Γ : List (BareOrientedBond L m K)) :
    lineSum (A + B) Γ = lineSum A Γ + lineSum B Γ := by
  induction Γ with
  | nil => simp [lineSum]
  | cons b Γ ih =>
    simp only [lineSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    have : orientedValue (A + B) b = orientedValue A b + orientedValue B b := by
      simp only [orientedValue]
      split_ifs <;> simp
      ring
    rw [this]
    ring
theorem lineSum_smul {L m K : ℕ} (c : ℝ) (A : OneForms L m K) (Γ : List (BareOrientedBond L m K)) :
    lineSum (c • A) Γ = c * lineSum A Γ := by
  induction Γ with
  | nil => simp [lineSum]
  | cons b Γ ih =>
    simp only [lineSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    have : orientedValue (c • A) b = c * orientedValue A b := by
      simp only [orientedValue]
      split_ifs <;> simp
    rw [this]
    ring
def blockAverageOne (n : ℕ) : OneForms D.L D.m D.K →ₗ[ℝ] (D.LevelBond n → ℝ) where
  toFun A c := ((D.L : ℝ) ^ (n * (dimension + 1)))⁻¹ *
    ∑ᶠ x : {x : BareSite D.L D.m D.K // (x : D.Torus) ∈ fineBlock (D := D) c.1.source},
      lineSum A (forwardAxisPath x.1 (bondAxis c) (D.L ^ n))
  map_add' A B := by
    funext c
    simp only [Pi.add_apply, lineSum_add, finsum_add_finite, mul_add]
  map_smul' r A := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, lineSum_smul, finsum_const_mul_finite]
    ring
theorem exists_levelSite (y : ↥(D.allLayerPoints Ω)) :
    ∃ p : Σ n : ℕ, D.LatticeSite n,
      p.1 ≤ D.t ∧ p.2 ∈ D.layerSites Ω p.1 ∧ (p.2 : D.Torus) = y := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨n, hn, z, hz, rfl⟩ := mem_iUnion₂.mp hy
  exact ⟨⟨n, z⟩, hn, hz, rfl⟩
def levelSite (y : ↥(D.allLayerPoints Ω)) : Σ n : ℕ, D.LatticeSite n :=
  (D.exists_levelSite Ω y).choose
def averageZero : ↥(zeroFormsOn D.K (Ω 0)) →ₗ[ℝ] D.CoarseZeroForms Ω where
  toFun f y := D.blockAverageZero (D.levelSite Ω y).1 f.1 (D.levelSite Ω y).2
  map_add' f g := by
    funext y
    simp
  map_smul' c f := by
    funext y
    simp
def averageOne : ↥(oneFormsOn D.K (Ω 0) φ) →ₗ[ℝ] D.CoarseOneForms Ω φ where
  toFun A c := D.blockAverageOne c.1.1 A.1 c.1.2
  map_add' A B := by
    funext c
    simp
  map_smul' r A := by
    funext c
    simp
def levelWeight : ℕ → ℝ
  | 0 => D.a
  | n + 1 => D.a * (1 - (D.L : ℝ) ^ (-2 : ℤ)) / (1 - (D.L : ℝ) ^ (-(2 * ((n + 1 : ℕ) : ℤ))))
def weightMulZero : D.CoarseZeroForms Ω →ₗ[ℝ] D.CoarseZeroForms Ω where
  toFun ω y := D.levelWeight (D.levelSite Ω y).1 * (D.levelMeshRatio (D.levelSite Ω y).1 ^ 2)⁻¹ * ω y
  map_add' ω ω' := by
    funext y
    simp only [Pi.add_apply]
    ring
  map_smul' c ω := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def weightMulOne : D.CoarseOneForms Ω φ →ₗ[ℝ] D.CoarseOneForms Ω φ where
  toFun B c := D.a * (D.bondMesh c.1 ^ 2)⁻¹ * B c
  map_add' B B' := by
    funext c
    simp only [Pi.add_apply]
    ring
  map_smul' r B := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
def restrictedZeroInner (f g : ↥(zeroFormsOn D.K (Ω 0))) : ℝ := latticeInner D.L D.t f.1 g.1
def restrictedOneInner (A B : ↥(oneFormsOn D.K (Ω 0) φ)) : ℝ := latticeInner D.L D.t A.1 B.1
def averageZeroAdjoint : D.CoarseZeroForms Ω →ₗ[ℝ] ↥(zeroFormsOn D.K (Ω 0)) :=
  FiniteDimReal.adjointFor (D.restrictedZeroInner Ω) (D.coarseZeroInner Ω)
    (D.averageZero Ω)
def averageOneAdjoint : D.CoarseOneForms Ω φ →ₗ[ℝ] ↥(oneFormsOn D.K (Ω 0) φ) :=
  FiniteDimReal.adjointFor (D.restrictedOneInner Ω φ) (D.coarseOneInner Ω φ)
    (D.averageOne Ω φ)
def weightedAverageZero : ↥(zeroFormsOn D.K (Ω 0)) →ₗ[ℝ] ↥(zeroFormsOn D.K (Ω 0)) :=
  D.averageZeroAdjoint Ω ∘ₗ D.weightMulZero Ω ∘ₗ D.averageZero Ω
def weightedAverageOne : ↥(oneFormsOn D.K (Ω 0) φ) →ₗ[ℝ] ↥(oneFormsOn D.K (Ω 0) φ) :=
  D.averageOneAdjoint Ω φ ∘ₗ D.weightMulOne Ω φ ∘ₗ D.averageOne Ω φ
open Classical in
def levelValue (ω : D.CoarseZeroForms Ω) : (n : ℕ) → D.LatticeSite n → ℝ
  | 0, y => if y ∈ D.layerSites Ω 0 then pointValue ω (y : D.Torus) else 0
  | n + 1, y =>
    if y ∈ D.layerSites Ω (n + 1) then pointValue ω (y : D.Torus)
    else if ∃ c ∈ D.layerBondSet Ω φ (n + 1), D.IsOuterEndpoint Ω c y then
      ((D.L : ℝ) ^ dimension)⁻¹ *
        ∑ᶠ z : {z : D.LatticeSite n // z ∈ D.layerSites Ω n ∧ (z : D.Torus) ∈ coarseBlock (D := D) y},
          pointValue ω (z.1 : D.Torus)
    else 0
variable {D Ω} in
theorem pointValue_add (ω ω' : D.CoarseZeroForms Ω) (y : D.Torus) :
    pointValue (ω + ω') y = pointValue ω y + pointValue ω' y := by
  simp only [pointValue]
  split_ifs <;> simp
variable {D Ω} in
theorem pointValue_smul (c : ℝ) (ω : D.CoarseZeroForms Ω) (y : D.Torus) :
    pointValue (c • ω) y = c * pointValue ω y := by
  simp only [pointValue]
  split_ifs <;> simp
theorem levelValue_add (ω ω' : D.CoarseZeroForms Ω) (n : ℕ) (y : D.LatticeSite n) :
    D.levelValue Ω φ (ω + ω') n y = D.levelValue Ω φ ω n y + D.levelValue Ω φ ω' n y := by
  cases n with
  | zero =>
    simp only [levelValue]
    split_ifs <;> simp [pointValue_add]
  | succ n =>
    simp only [levelValue]
    split_ifs <;> simp [pointValue_add, finsum_add_finite, mul_add]
theorem levelValue_smul (c : ℝ) (ω : D.CoarseZeroForms Ω) (n : ℕ) (y : D.LatticeSite n) :
    D.levelValue Ω φ (c • ω) n y = c * D.levelValue Ω φ ω n y := by
  cases n with
  | zero =>
    simp only [levelValue]
    split_ifs <;> simp [pointValue_smul]
  | succ n =>
    simp only [levelValue]
    split_ifs
    · simp [pointValue_smul]
    · simp only [pointValue_smul, finsum_const_mul_finite]
      ring
    · simp
def coarseDifference : D.CoarseZeroForms Ω →ₗ[ℝ] D.CoarseOneForms Ω φ where
  toFun ω c := (D.levelMeshRatio c.1.1)⁻¹ *
    (D.levelValue Ω φ ω c.1.1 c.1.2.1.target - D.levelValue Ω φ ω c.1.1 c.1.2.1.source)
  map_add' ω ω' := by
    funext c
    simp only [Pi.add_apply, levelValue_add]
    ring
  map_smul' r ω := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, levelValue_smul]
    ring
end SeparatedSequences.BaseParameters
end
end YangMills.Construction
