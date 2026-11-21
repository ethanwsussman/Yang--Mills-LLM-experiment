import YangMills.Construction.Lattice.ActionOfABareGaugeTransformation
import YangMills.Construction.Lattice.ContinuationOfTheMinimiserUnderIsometries
import YangMills.Construction.Lattice.ContinuationsUnderIsometriesLieInOneComplexOrbit
import YangMills.Construction.Lattice.GaugeActionsAtComplexConfigurationsUnderIsometries
import YangMills.Construction.Lattice.GaugeOnBlocksUnderIsometries
import YangMills.Construction.Lattice.HolomorphyOfTheContinuationsUnderIsometries
import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegions
import YangMills.Construction.Lattice.TranslationsCarryTheContinuationOfTheMinimiser
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace MinimizerContinuationIsometry
variable {L m : ℕ} {j : ℤ}
theorem bondPreimage_bondImage {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : ∀ e : Bond L m j, ((bondImage σ e).source : FourTorus L m) = σ e.source ∧
      ((bondImage σ e).target : FourTorus L m) = σ e.target) (e : Bond L m j) :
    bondPreimage σ (bondImage σ e) = e := by
  obtain ⟨hs, ht⟩ := hσ e
  have he : ∃ e' : Bond L m j, (e'.source : FourTorus L m) = σ.symm (bondImage σ e).source ∧
      (e'.target : FourTorus L m) = σ.symm (bondImage σ e).target := ⟨e, by simp [hs], by simp [ht]⟩
  rw [bondPreimage, dif_pos he]
  obtain ⟨h₁, h₂⟩ := he.choose_spec
  exact Bond.ext (Subtype.ext (by simpa [hs] using h₁)) (Subtype.ext (by simpa [ht] using h₂))
theorem bondImage_mem_bondsInside_iff {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : ∀ e : Bond L m j, ((bondImage σ e).source : FourTorus L m) = σ e.source ∧
      ((bondImage σ e).target : FourTorus L m) = σ e.target) (X : Set (FourTorus L m))
    (e : Bond L m j) :
    bondImage σ e ∈ (bondsInside (σ '' X) : Set (Bond L m j)) ↔
      e ∈ (bondsInside X : Set (Bond L m j)) := by
  obtain ⟨hs, ht⟩ := hσ e
  simp only [bondsInside, mem_ofPred_eq, hs, ht, σ.injective.mem_set_image]
theorem conj_mul_mul_inv {a d p q C : Matrices.ComplexMatrix2}
    (ha : a ∈ Matrices.ComplexMatrix2.unitDeterminant)
    (hd : d ∈ Matrices.ComplexMatrix2.unitDeterminant)
    (hq : q ∈ Matrices.ComplexMatrix2.unitDeterminant) :
    a * (p * C * q⁻¹) * d⁻¹ = (a * p * a⁻¹) * (a * C * d⁻¹) * (d * q * d⁻¹)⁻¹ := by
  have hau : IsUnit a.det := by rw [show a.det = 1 from ha]; exact isUnit_one
  have hdu : IsUnit d.det := by rw [show d.det = 1 from hd]; exact isUnit_one
  have hqu : IsUnit q.det := by rw [show q.det = 1 from hq]; exact isUnit_one
  have e₁ : (d * q * d⁻¹)⁻¹ = d * q⁻¹ * d⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdu, mul_assoc]
  have e₂ : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul _ hau
  have e₃ : d⁻¹ * d = 1 := Matrix.nonsing_inv_mul _ hdu
  rw [e₁]
  calc a * (p * C * q⁻¹) * d⁻¹ = a * p * (C * 1) * (q⁻¹ * d⁻¹) := by
        simp only [mul_one, mul_assoc]
    _ = a * p * (C * (d⁻¹ * d)) * (q⁻¹ * d⁻¹) := by rw [e₃]
    _ = a * p * 1 * (C * d⁻¹) * (d * q⁻¹ * d⁻¹) := by simp only [mul_one, mul_assoc]
    _ = a * p * (a⁻¹ * a) * (C * d⁻¹) * (d * q⁻¹ * d⁻¹) := by rw [e₂]
    _ = _ := by simp only [mul_assoc]
theorem blockwiseGauge_mem {K k : ℕ} (hL : 0 < L) {Ω : ℕ → Set (FourTorus L m)}
    {v : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2}
    (hv : IsComplexSiteMap (constraintSites K k Ω) v) (x : SiteAtLevel L m K 0) :
    blockwiseGauge K k Ω v x ∈ Matrices.ComplexMatrix2.unitDeterminant := by
  classical
  unfold blockwiseGauge
  split_ifs with h
  · apply hv
    exact ⟨h.choose, h.choose_spec.1, _, h.choose_spec.2.choose_spec.1, coe_toSublattice_finest hL _⟩
  · simp [Matrices.ComplexMatrix2.unitDeterminant]
theorem conj_mem_unitDeterminant {a p : Matrices.ComplexMatrix2}
    (ha : a ∈ Matrices.ComplexMatrix2.unitDeterminant)
    (hp : p ∈ Matrices.ComplexMatrix2.unitDeterminant) :
    a * p * a⁻¹ ∈ Matrices.ComplexMatrix2.unitDeterminant := by
  have ha' : a.det = 1 := ha
  have hp' : p.det = 1 := hp
  show (a * p * a⁻¹).det = 1
  simp [Matrix.det_mul, Matrix.det_nonsing_inv, ha', hp']
theorem conj_one {a : Matrices.ComplexMatrix2}
    (ha : a ∈ Matrices.ComplexMatrix2.unitDeterminant) : a * 1 * a⁻¹ = 1 := by
  have hau : IsUnit a.det := by rw [show a.det = 1 from ha]; exact isUnit_one
  rw [mul_one]
  exact Matrix.mul_nonsing_inv _ hau
theorem extendByOne_of_mem {S : Set (Bond L m j)} {W : Bond L m j → Matrices.ComplexMatrix2}
    {e : Bond L m j} (h : e ∈ S) : extendByOne S W e = W e := by
  simp [extendByOne, h]
theorem extendByOne_of_not_mem {S : Set (Bond L m j)} {W : Bond L m j → Matrices.ComplexMatrix2}
    {e : Bond L m j} (h : e ∉ S) : extendByOne S W e = 1 := by
  simp [extendByOne, h]
end MinimizerContinuationIsometry
open MinimizerContinuationIsometry in
theorem isometriesPreserveMinimizerContinuation
    (hHol : ContinuationsUnderIsometriesHolomorphic)
    (hOrb : IsometricContinuationsInOneComplexOrbit)
    (hTr : TranslationPreservesUniqueContinuation)
    (hGB : BlockwiseGaugeEquivariance)
    (hCG : ComplexGaugeCovarianceUnderIsometries.Statement)
    (hIso : LatticeIsometryGroupActionStatement) :
    IsometriesPreserveMinimizerContinuation := by
  intro L m hL hm i hi σ hσ ε εBar rB hε hεBar hrB K k e r Ω hF hS V₀
  refine ⟨fun h₁ h₂ => ?_, hTr L m hL hm i hi σ hσ ε εBar rB hε hεBar hrB K k e r Ω hF hS V₀⟩
  obtain ⟨hh, hball⟩ :=
    hHol L m hL hm i hi σ hσ ε εBar rB hε hεBar hrB K k e r Ω hF hS V₀ h₁ h₂
  have hLpos : 0 < L := by
    have := hL.2
    omega
  have hiK : i ≤ levelDepth K 0 := by
    obtain ⟨c, hic, hcK, -⟩ := hF.2.2.2.2 0 (Nat.zero_le _)
    exact hic.trans hcK
  have hG := hIso L m i hL hm hi
  have hends : ∀ c : BondAtLevel L m K 0, ((bondImage σ c).source : FourTorus L m) = σ c.source ∧
      ((bondImage σ c).target : FourTorus L m) = σ c.target :=
    (hG.2.2.2.2 σ hσ _ hiK).1.2.2.2.1
  have hσs : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨⟨H, hH⟩, -⟩ := hG.1
    have h₀ : σ ∈ H := by
      have : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := hH ▸ hσ
      exact this
    have h₁' : σ⁻¹ ∈ H := H.inv_mem h₀
    have : σ⁻¹ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := h₁'
    rw [hH] at this
    exact this
  have hends' : ∀ c : BondAtLevel L m K 0,
      ((bondImage σ.symm c).source : FourTorus L m) = σ.symm c.source ∧
      ((bondImage σ.symm c).target : FourTorus L m) = σ.symm c.target :=
    (hG.2.2.2.2 σ.symm hσs _ hiK).1.2.2.2.1
  have himage : ∀ c : BondAtLevel L m K 0, bondImage σ (bondPreimage σ c) = c :=
    fun c => bondPreimage_bondImage hends' c
  have hpull : ∀ (F : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) (c : BondAtLevel L m K 0),
      transportGaugeField σ F (bondImage σ c) = F c := by
    intro F c
    simp only [transportGaugeField, bondPreimage_bondImage hends c]
  have hmem : ∀ c : BondAtLevel L m K 0,
      bondImage σ c ∈ (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0)) ↔
        c ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) :=
    fun c => bondImage_mem_bondsInside_iff hends (Ω 0) c
  obtain ⟨hgauge, hall⟩ := hCG L m hL hm i hi σ hσ
  have hres := (hall K k Ω hF).2
  refine ⟨hh, fun B hB => ⟨hball B hB,
    hOrb L m hL hm i hi σ hσ ε εBar rB hε hεBar hrB K k e r Ω hF hS V₀ h₁ h₂ B hB, ?_, ?_⟩⟩
  all_goals
    obtain ⟨Φ, hΦ, -⟩ := id h₁
    have hspec : IsMinimizerContinuation ε εBar rB K k Ω V₀
        (minimizerContinuation ε εBar rB K k Ω V₀) := Classical.epsilon_spec ⟨Φ, hΦ⟩
    have hW : continuedMinimalField ε εBar rB K k Ω V₀ B ∈
        complexGaugeFields (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) :=
      (hspec.2.2.1 B hB).1
    obtain ⟨u, hu, hW'⟩ :=
      hOrb L m hL hm i hi σ hσ ε εBar rB hε hεBar hrB K k e r Ω hF hS V₀ h₁ h₂ B hB
    rw [hres] at hu
    obtain ⟨u₀, hu₀, rfl⟩ := hu
    have hu₀g : IsGaugeMap complexGaugeGroup u₀ := by
      intro x
      by_cases hx : x ∈ (sitesIn (Ω 0) : Set (SiteAtLevel L m K 0))
      · exact hu₀.1 x hx
      · rw [hu₀.2.1 x hx]
        simp [Matrices.ComplexMatrix2.unitDeterminant]
    have hcarry : ∀ (g : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2), IsGaugeMap complexGaugeGroup g →
        ∀ c ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)),
          gaugeTransform g (continuedMinimalField ε εBar rB K k Ω V₀ B) c =
            gaugeTransform (transportSiteFunction σ g) (transportGaugeField σ
              (continuedMinimalField ε εBar rB K k Ω V₀ B)) (bondImage σ c) := by
      intro g hg c hc
      rw [← (hgauge _ hiK (bondsInside (Ω 0)) c hc).2.2 _ hW g hg, hpull]
    try simp only [continuedGaugeExtendedField]
    generalize continuedMinimalField ε εBar rB K k Ω V₀ B = W at *
  · intro E f hf
    have hback : transportGaugeField σ.symm
        (continuedMinimalField ε εBar rB K k (imageChain σ Ω)
          (datumImage σ V₀) (twistedActiveFamily σ V₀ B)) =
        extendByOne (bondsInside (Ω 0)) (gaugeTransform u₀ W) := by
      funext c
      change continuedMinimalField ε εBar rB K k (imageChain σ Ω)
          (datumImage σ V₀) (twistedActiveFamily σ V₀ B) (bondImage σ c) = _
      rw [hW']
      by_cases hc : c ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0))
      · rw [extendByOne_of_mem ((hmem c).2 hc),
          extendByOne_of_mem hc, hcarry u₀ hu₀g c hc]
      · rw [extendByOne_of_not_mem (fun h => hc ((hmem c).1 h)),
          extendByOne_of_not_mem hc]
    change f (transportGaugeField σ.symm _) = f W
    rw [hback]
    exact hf u₀ hu₀
  · intro v hv
    have hvb : ∀ x, blockwiseGauge K k Ω v x ∈ Matrices.ComplexMatrix2.unitDeterminant :=
      blockwiseGauge_mem hLpos hv
    have hg : ∀ x, transportSiteFunction σ (blockwiseGauge K k Ω v) x ∈
        Matrices.ComplexMatrix2.unitDeterminant :=
      fun x => hvb _
    have hσu : ∀ x, transportSiteFunction σ u₀ x ∈ Matrices.ComplexMatrix2.unitDeterminant :=
      fun x => hu₀g _
    refine ⟨fun x => transportSiteFunction σ (blockwiseGauge K k Ω v) x *
        transportSiteFunction σ u₀ x *
        (transportSiteFunction σ (blockwiseGauge K k Ω v) x)⁻¹, ?_, ?_⟩
    · obtain ⟨u', hu', hu'e⟩ : ∃ u' ∈ complexStabilizerGroup (imageChain σ Ω)
          (activeBondSet K k (imageChain σ Ω)), u' = transportSiteFunction σ u₀ := by
        refine ⟨_, ?_, rfl⟩
        rw [hres]
        exact ⟨u₀, hu₀, rfl⟩
      subst hu'e
      refine ⟨fun x _ => conj_mem_unitDeterminant (hg x) (hσu x), fun x hx => ?_, fun x hx => ?_⟩
      · change _ * transportSiteFunction σ u₀ x * _ = 1
        rw [hu'.2.1 x hx]
        exact conj_one (hg x)
      · change _ * transportSiteFunction σ u₀ x * _ = 1
        rw [hu'.2.2 x hx]
        exact conj_one (hg x)
    · rw [hGB L m hL hm i hi σ hσ K k e r Ω hF hS v]
      funext c
      by_cases hc : c ∈ (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0))
      · rw [extendByOne_of_mem hc, extendByOne_of_mem hc]
        have hb : bondPreimage σ c ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)) := by
          have := himage c
          rw [← this] at hc
          exact (hmem _).1 hc
        have hcb : transportGaugeField σ (extendByOne (bondsInside (Ω 0))
            (gaugeTransform (blockwiseGauge K k Ω v) W)) c =
            gaugeTransform (transportSiteFunction σ (blockwiseGauge K k Ω v))
              (transportGaugeField σ W) c := by
          have h₃ := hcarry _ hvb _ hb
          rw [himage c] at h₃
          rw [← h₃]
          change extendByOne _ _ (bondPreimage σ c) = _
          rw [extendByOne_of_mem hb]
        rw [gaugeTransform, gaugeTransform, hcb, hW', extendByOne_of_mem hc, gaugeTransform,
          gaugeTransform]
        exact conj_mul_mul_inv (hg _) (hg _) (hσu _)
      · rw [extendByOne_of_not_mem hc, extendByOne_of_not_mem hc]
end YangMills.Construction.PeriodicLattice
