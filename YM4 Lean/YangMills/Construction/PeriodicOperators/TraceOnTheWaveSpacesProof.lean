import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.PeriodicOperators.ExponentialSumsTorusWavesAndComponentSets
import Mathlib
import YangMills.Construction.PeriodicOperators.WaveSpacesOnATorus
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.PeriodicOperators.WaveSpaceTrace
def Claim : Prop :=
  ∀ I : PeriodicData, IsPeriodic I → ∀ s : ℕ, 0 < s →
    ∀ (A : Module.End ℂ (I.QuotMod s → ℂ)) (B : (Fin 4 → ℂ) → Module.End ℂ (I.UnitQuot → ℂ)),
      (∀ κ ∈ dualLattice s, ∀ (φ : I.UnitQuot → ℂ) (g : I.QuotMod s → ℂ),
        JetDomains.IsLiftOf I s g (blochWave I (toComplexVec κ) φ) →
          JetDomains.IsLiftOf I s (A g) (blochWave I (toComplexVec κ) (B (toComplexVec κ) φ))) →
      LinearMap.trace ℂ (I.QuotMod s → ℂ) A =
        RiemannSums.classSum s fun κ => LinearMap.trace ℂ (I.UnitQuot → ℂ) (B κ)
end YangMills.Construction.PeriodicOperators.WaveSpaceTrace
end

noncomputable section
namespace YangMills.Construction.PeriodicOperators.WaveSpaceTrace
open InfiniteLattice (AmbientSpace)
open JetDomains (IsLiftOf)
open RiemannSums (DualClasses classSum)
theorem mkQuot_surjective (I : PeriodicData) (s : ℕ) : Function.Surjective (I.mkQuot s) :=
  fun c => Quot.exists_rep c
theorem eq_of_isLiftOf {I : PeriodicData} {s : ℕ} {u u' : I.QuotMod s → ℂ} {f : I.Carrier → ℂ}
    (hu : IsLiftOf I s u f) (hu' : IsLiftOf I s u' f) : u = u' := by
  funext c
  obtain ⟨i, rfl⟩ := mkQuot_surjective I s c
  rw [hu i, hu' i]
def blochWaveOnQuot (I : PeriodicData) (s : ℕ) (k : AmbientSpace) :
    (I.UnitQuot → ℂ) →ₗ[ℂ] (I.QuotMod s → ℂ) where
  toFun ψ c := blochWave I (toComplexVec k) ψ (Function.surjInv (mkQuot_surjective I s) c)
  map_add' ψ ψ' := by
    funext c
    simp [blochWave, mul_add]
  map_smul' a ψ := by
    funext c
    simp only [blochWave, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem blochWaveOnQuot_isLiftOf {I : PeriodicData} (F : BlochDecomposition.Facts I) {s : ℕ}
    (hs : 0 < s) {k : AmbientSpace} (hk : k ∈ dualLattice s) (ψ : I.UnitQuot → ℂ) :
    IsLiftOf I s (blochWaveOnQuot I s k ψ) (blochWave I (toComplexVec k) ψ) := by
  intro i
  obtain ⟨u, hu⟩ := F.blochWave_descends s hs k hk ψ
  change blochWave I (toComplexVec k) ψ
    (Function.surjInv (mkQuot_surjective I s) (I.mkQuot s i)) = _
  rw [← hu, ← hu, Function.surjInv_eq (mkQuot_surjective I s) (I.mkQuot s i)]
def blochWaveEquiv {I : PeriodicData} (F : BlochDecomposition.Facts I) {s : ℕ} (hs : 0 < s)
    {k : AmbientSpace} (hk : k ∈ dualLattice s) :
    (I.UnitQuot → ℂ) ≃ₗ[ℂ] blochWaveSubspace I s k :=
  LinearEquiv.ofBijective
    ((blochWaveOnQuot I s k).codRestrict (blochWaveSubspace I s k)
      fun ψ => ⟨ψ, blochWaveOnQuot_isLiftOf F hs hk ψ⟩)
    (by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro ψ hψ
        refine F.blochWave_injective (toComplexVec k) ψ fun i => ?_
        rw [← blochWaveOnQuot_isLiftOf F hs hk ψ i]
        have : blochWaveOnQuot I s k ψ = 0 := congrArg Subtype.val hψ
        rw [this]
        rfl
      · rintro ⟨u, ψ, hψ⟩
        exact ⟨ψ, Subtype.ext (eq_of_isLiftOf (blochWaveOnQuot_isLiftOf F hs hk ψ) hψ)⟩)
theorem blochWaveEquiv_isLiftOf {I : PeriodicData} (F : BlochDecomposition.Facts I) {s : ℕ}
    (hs : 0 < s) {k : AmbientSpace} (hk : k ∈ dualLattice s) (ψ : I.UnitQuot → ℂ) :
    IsLiftOf I s (blochWaveEquiv F hs hk ψ : I.QuotMod s → ℂ) (blochWave I (toComplexVec k) ψ) :=
  blochWaveOnQuot_isLiftOf F hs hk ψ
theorem trace_restrict_eq_trace {I : PeriodicData} [Finite I.UnitQuot]
    (F : BlochDecomposition.Facts I) {s : ℕ} (hs : 0 < s) {k : AmbientSpace}
    (hk : k ∈ dualLattice s)
    (T : Module.End ℂ (I.QuotMod s → ℂ)) (M : Module.End ℂ (I.UnitQuot → ℂ))
    (hT : ∀ (ψ : I.UnitQuot → ℂ) (u : I.QuotMod s → ℂ),
      IsLiftOf I s u (blochWave I (toComplexVec k) ψ) →
        IsLiftOf I s (T u) (blochWave I (toComplexVec k) (M ψ)))
    (hmaps : Set.MapsTo T (blochWaveSubspace I s k) (blochWaveSubspace I s k)) :
    LinearMap.trace ℂ (blochWaveSubspace I s k) (T.restrict hmaps) =
      LinearMap.trace ℂ (I.UnitQuot → ℂ) M := by
  have hconj : T.restrict hmaps = (blochWaveEquiv F hs hk).conj M := by
    apply LinearMap.ext
    intro x
    obtain ⟨ψ, rfl⟩ := (blochWaveEquiv F hs hk).surjective x
    apply Subtype.ext
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact eq_of_isLiftOf (hT ψ _ (blochWaveEquiv_isLiftOf F hs hk ψ))
      (blochWaveEquiv_isLiftOf F hs hk (M ψ))
  rw [hconj, LinearMap.trace_conj']
theorem claim_holds (hBloch : BlochDecomposition.Claim)
    (hQuot : Quotients.QuotientTransposeNorm) : Claim := by
  intro I hI s hs T N hT
  classical
  have F := hBloch I hI
  obtain ⟨hC, hCs, -⟩ := (hQuot I I hI hI s hs).1
  have := F.dualClasses_finite s hs
  let _ : Fintype (DualClasses s) := Fintype.ofFinite _
  let r : DualClasses s → dualLattice s := Quotient.out
  have hr : IsDualSection s r := fun q => Quotient.out_eq q
  obtain ⟨hind, htop⟩ := F.internal_sum s hs r hr
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have hmaps : ∀ q, Set.MapsTo T (blochWaveSubspace I s (r q)) (blochWaveSubspace I s (r q)) := by
    rintro q u ⟨ψ, hψ⟩
    exact ⟨N (toComplexVec (r q)) ψ, hT (r q) (r q).2 ψ u hψ⟩
  rw [LinearMap.trace_eq_sum_trace_restrict hint hmaps, classSum,
    finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun q _ =>
    trace_restrict_eq_trace F hs (r q).2 T (N (toComplexVec (r q)))
      (fun ψ u hu => hT (r q) (r q).2 ψ u hu) (hmaps q)
end YangMills.Construction.PeriodicOperators.WaveSpaceTrace
end
