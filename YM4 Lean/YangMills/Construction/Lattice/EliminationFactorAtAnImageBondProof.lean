import YangMills.Construction.Lattice.BlocksAndLinearSizesUnderIsometries
import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.EliminationFactorAtAnImageBond
import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegions
import YangMills.Construction.Lattice.IteratesOfAComplexConfiguration
import YangMills.Construction.Lattice.OneStepIdentitiesAtAnImageBond
import YangMills.Construction.Lattice.PivotOfBond
import YangMills.Construction.Lattice.PropertiesOfTheTwoSchemes
import YangMills.Construction.Lattice.SeriesLogarithmOnTheComplexGroup
import YangMills.Construction.Matrices.ConjugationDeterminantProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
namespace ImageWeight
theorem restrictEndomorphism_eq {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    {S : Submodule 𝕜 E} {f : E → E} (A : Module.End 𝕜 S) (hA : ∀ x : S, (A x : E) = f x) :
    restrictEndomorphism S f = A := by
  have hex : ∃ T : Module.End 𝕜 S, ∀ x : S, (T x : E) = f x := ⟨A, hA⟩
  rw [restrictEndomorphism, dif_pos hex]
  refine LinearMap.ext fun x => Subtype.ext ?_
  exact (hex.choose_spec x).trans (hA x).symm
theorem restrictEndomorphism_eq_zero {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    {S : Submodule 𝕜 E} {f : E → E} (hne : ¬∃ T : Module.End 𝕜 S, ∀ x : S, (T x : E) = f x) :
    restrictEndomorphism S f = 0 := by
  rw [restrictEndomorphism, dif_neg hne]
theorem norm_det_restrictEndomorphism_conj {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E]
    [Module 𝕜 E] {S : Submodule 𝕜 E} {f g τ : E → E} (P Q : S ≃ₗ[𝕜] S)
    (hτ : Function.Injective τ) (hQ : ∀ x : S, (Q x : E) = τ x)
    (hconj : ∀ x : S, g (P x) = τ (f x))
    (hP : ‖LinearMap.det (P : S →ₗ[𝕜] S)‖ = 1) (hQd : ‖LinearMap.det (Q : S →ₗ[𝕜] S)‖ = 1) :
    ‖LinearMap.det (restrictEndomorphism S g)‖ = ‖LinearMap.det (restrictEndomorphism S f)‖ := by
  by_cases hex : ∃ A : Module.End 𝕜 S, ∀ x : S, (A x : E) = f x
  · obtain ⟨A, hA⟩ := hex
    have hB : ∀ x : S, (((Q : S →ₗ[𝕜] S) ∘ₗ A ∘ₗ (P.symm : S →ₗ[𝕜] S)) x : E) = g x := by
      intro x
      have hx := hconj (P.symm x)
      rw [LinearEquiv.apply_symm_apply] at hx
      rw [hx, ← hA]
      exact hQ _
    have hid : (P : S →ₗ[𝕜] S) ∘ₗ (P.symm : S →ₗ[𝕜] S) = LinearMap.id := by
      ext x
      simp
    have hd := LinearMap.det_comp (P : S →ₗ[𝕜] S) (P.symm : S →ₗ[𝕜] S)
    rw [hid, LinearMap.det_id] at hd
    have hn := congrArg norm hd
    rw [norm_one, norm_mul, hP, one_mul] at hn
    rw [restrictEndomorphism_eq A hA, restrictEndomorphism_eq _ hB, LinearMap.det_comp,
      LinearMap.det_comp, norm_mul, norm_mul, hQd, ← hn, one_mul, mul_one]
  · have hne : ¬∃ A : Module.End 𝕜 S, ∀ x : S, (A x : E) = g x := by
      rintro ⟨A, hA⟩
      refine hex ⟨(Q.symm : S →ₗ[𝕜] S) ∘ₗ A ∘ₗ (P : S →ₗ[𝕜] S), fun x => hτ ?_⟩
      rw [← hQ, ← hconj, ← hA]
      simp
    rw [restrictEndomorphism_eq_zero hex, restrictEndomorphism_eq_zero hne]
section Twists
variable {L m : ℕ} {j : ℤ}
def orientationTwist (σ : FourTorus L m ≃ FourTorus L m) (U : Bond L m j → ComplexMatrix2)
    (b : Bond L m j) : ComplexMatrix2 → ComplexMatrix2 :=
  open Classical in
  if (bondImage σ b).IsPositivelyOriented then id
  else fun X => -ComplexMatrix2.conjugateBy (U b)⁻¹ X
theorem coe_twistedLinkMap (σ : FourTorus L m ≃ FourTorus L m) (U : Bond L m j → ComplexMatrix2)
    (b : Bond L m j) (X : ↥ComplexMatrix2.traceless) :
    (twistedLinkMap σ U b X : ComplexMatrix2) = orientationTwist σ U b X := by
  by_cases hpos : (bondImage σ b).IsPositivelyOriented
  · simp [twistedLinkMap, orientationTwist, hpos]
  · simp [twistedLinkMap, orientationTwist, hpos, conjugationLinearMap]
theorem conjugateBy_conjugateBy_inv {u : ComplexMatrix2} (hu : IsUnit u.det) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy u (ComplexMatrix2.conjugateBy u⁻¹ X) = X := by apply _root_.YangMills.SharedProofs.p1183 <;> assumption
theorem conjugateBy_inv_conjugateBy {u : ComplexMatrix2} (hu : IsUnit u.det) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy u⁻¹ (ComplexMatrix2.conjugateBy u X) = X := by apply _root_.YangMills.SharedProofs.p32697 <;> assumption
theorem orientationTwist_injective (σ : FourTorus L m ≃ FourTorus L m)
    (U : Bond L m j → ComplexMatrix2) (b : Bond L m j) (hU : IsUnit (U b).det) :
    Function.Injective (orientationTwist σ U b) := by
  have hu : IsUnit ((U b)⁻¹).det := by
    rw [Matrix.det_nonsing_inv]
    exact hU.ringInverse
  by_cases hpos : (bondImage σ b).IsPositivelyOriented
  · simpa [orientationTwist, hpos] using Function.injective_id
  · intro X Y hXY
    simp only [orientationTwist, if_neg hpos] at hXY
    have hXY' := congrArg (ComplexMatrix2.conjugateBy ((U b)⁻¹)⁻¹) (neg_injective hXY)
    rwa [conjugateBy_inv_conjugateBy hu, conjugateBy_inv_conjugateBy hu] at hXY'
theorem norm_det_neg {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (f : E →ₗ[𝕜] E) : ‖LinearMap.det (-f)‖ = ‖LinearMap.det f‖ := by
  have hf : -f = (-1 : 𝕜) • f := by simp
  rw [hf, LinearMap.det_smul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
theorem conjugationLinearMap_eq (g : ComplexMatrix2) :
    conjugationLinearMap g = ComplexMatrix2.conjugateOnTraceless g :=
  LinearMap.ext fun _ => Subtype.ext rfl
theorem exists_traceless_equiv (hD : ComplexMatrix2.ConjugationDeterminant)
    (σ : FourTorus L m ≃ FourTorus L m) (U : Bond L m j → ComplexMatrix2) (b : Bond L m j)
    (hU : IsUnit (U b).det) :
    ∃ T : ↥ComplexMatrix2.traceless ≃ₗ[ℂ] ↥ComplexMatrix2.traceless,
      (∀ x : ↥ComplexMatrix2.traceless, (T x : ComplexMatrix2) = orientationTwist σ U b x) ∧
      ‖LinearMap.det (T : ↥ComplexMatrix2.traceless →ₗ[ℂ] ↥ComplexMatrix2.traceless)‖ = 1 := by
  have hu : IsUnit ((U b)⁻¹).det := by
    rw [Matrix.det_nonsing_inv]
    exact hU.ringInverse
  by_cases hpos : (bondImage σ b).IsPositivelyOriented
  · refine ⟨LinearEquiv.refl ℂ _, fun x => ?_, ?_⟩
    · simp [orientationTwist, hpos]
    · simp
  · refine ⟨LinearEquiv.ofLinearMap (-conjugationLinearMap (U b)⁻¹)
      (-conjugationLinearMap ((U b)⁻¹)⁻¹) ?_ ?_, fun x => ?_, ?_⟩
    · refine LinearMap.ext fun x => Subtype.ext ?_
      simpa [conjugationLinearMap] using conjugateBy_conjugateBy_inv hu x
    · refine LinearMap.ext fun x => Subtype.ext ?_
      simpa [conjugationLinearMap] using conjugateBy_inv_conjugateBy hu x
    · simp [orientationTwist, hpos, conjugationLinearMap]
    · rw [LinearEquiv.toLinearMap_ofLinearMap, norm_det_neg, conjugationLinearMap_eq]
      rcases (hD _ hu).2.1 with hd | hd <;> simp [hd]
theorem exists_hermitianTraceless_equiv (hD : ComplexMatrix2.ConjugationDeterminant)
    (σ : FourTorus L m ≃ FourTorus L m) (U : Bond L m j → ComplexMatrix2) (b : Bond L m j)
    (hU : U b ∈ compactGaugeGroup) :
    ∃ T : ↥ComplexMatrix2.hermitianTraceless ≃ₗ[ℝ] ↥ComplexMatrix2.hermitianTraceless,
      (∀ x : ↥ComplexMatrix2.hermitianTraceless,
        (T x : ComplexMatrix2) = orientationTwist σ U b x) ∧
      ‖LinearMap.det (T : ↥ComplexMatrix2.hermitianTraceless →ₗ[ℝ]
        ↥ComplexMatrix2.hermitianTraceless)‖ = 1 := by
  have hU' : U b ∈ ComplexMatrix2.specialUnitary := hU
  have hinv : ∀ {g : ComplexMatrix2}, g ∈ ComplexMatrix2.specialUnitary →
      g⁻¹ ∈ ComplexMatrix2.specialUnitary := by
    intro g hg
    rw [ComplexMatrix2.inv_eq_star_of_mem_specialUnitary hg]
    obtain ⟨hg₁, hg₂⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hg
    refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Unitary.star_mem hg₁, ?_⟩
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hg₂, star_one]
  have hu₁ : (U b)⁻¹ ∈ ComplexMatrix2.specialUnitary := hinv hU'
  have hu₂ : ((U b)⁻¹)⁻¹ ∈ ComplexMatrix2.specialUnitary := hinv hu₁
  have hu : IsUnit ((U b)⁻¹).det := by
    rw [(Matrix.mem_specialUnitaryGroup_iff.mp hu₁).2]
    exact isUnit_one
  by_cases hpos : (bondImage σ b).IsPositivelyOriented
  · refine ⟨LinearEquiv.refl ℝ _, fun x => ?_, ?_⟩
    · simp [orientationTwist, hpos]
    · simp
  · refine ⟨LinearEquiv.ofLinearMap (-ComplexMatrix2.conjugateOnHermitianTraceless ⟨_, hu₁⟩)
      (-ComplexMatrix2.conjugateOnHermitianTraceless ⟨_, hu₂⟩) ?_ ?_, fun x => ?_, ?_⟩
    · refine LinearMap.ext fun x => Subtype.ext ?_
      simp only [LinearMap.comp_apply, LinearMap.neg_apply, map_neg, neg_neg, LinearMap.id_apply]
      exact conjugateBy_conjugateBy_inv hu x
    · refine LinearMap.ext fun x => Subtype.ext ?_
      simp only [LinearMap.comp_apply, LinearMap.neg_apply, map_neg, neg_neg, LinearMap.id_apply]
      exact conjugateBy_inv_conjugateBy hu x
    · simp [orientationTwist, hpos, ComplexMatrix2.conjugateOnHermitianTraceless,
        ComplexMatrix2.conjugateByLinear]
      rfl
    · rw [LinearEquiv.toLinearMap_ofLinearMap, norm_det_neg]
      have hre := ((hD _ hu).2.2 hu₁).2
      have hn := congrArg norm hre
      rw [Complex.norm_real] at hn
      rw [hn]
      rcases (hD _ hu).2.1 with hd | hd <;> simp [hd]
end Twists
section Links
variable {L m : ℕ} {j j' : ℤ}
theorem bondsInDoubleBlock_opposite (c : Bond L m j) :
    (bondsInDoubleBlock c.opposite : Set (Bond L m j')) = bondsInDoubleBlock c := by apply _root_.YangMills.Construction.PeriodicLattice.bondsInDoubleBlock_opposite <;> assumption
theorem bondsInDoubleBlock_positivelyOriented (c : Bond L m j) :
    (bondsInDoubleBlock c.positivelyOriented : Set (Bond L m j')) = bondsInDoubleBlock c := by
  by_cases hpos : c.IsPositivelyOriented
  · simp [Bond.positivelyOriented, hpos]
  · simp only [Bond.positivelyOriented, if_neg hpos, bondsInDoubleBlock_opposite]
theorem isGaugeField_image_iff {σ : FourTorus L m ≃ FourTorus L m}
    (hpre : ∀ b : Bond L m j, bondPreimage σ (bondImage σ b) = b)
    (hopp : ∀ b : Bond L m j, bondPreimage σ b.opposite = (bondPreimage σ b).opposite)
    (𝒢 : Set ComplexMatrix2) (ℬ : Set (Bond L m j)) (U : Bond L m j → ComplexMatrix2) :
    IsGaugeField 𝒢 (bondImage σ '' ℬ) (transportGaugeField σ U) ↔ IsGaugeField 𝒢 ℬ U := by
  have hval : ∀ b, transportGaugeField σ U (bondImage σ b) = U b :=
    fun b => congrArg U (hpre b)
  have hval' : ∀ b, transportGaugeField σ U (bondImage σ b).opposite = U b.opposite := by
    intro b
    show U (bondPreimage σ (bondImage σ b).opposite) = _
    rw [hopp, hpre]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · rw [← hval]
      exact h₁ _ (mem_image_of_mem _ hb)
    · rw [← hval', ← hval]
      exact h₂ _ (mem_image_of_mem _ hb)
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      rw [hval]
      exact h₁ b hb
    · rintro _ ⟨b, hb, rfl⟩
      rw [hval', hval]
      exact h₂ b hb
end Links
end ImageWeight
open ImageWeight in
theorem eliminationWeightAtImageBond_holds
    (hI : TransportIdentitiesAtImageBond)
    (hB : IsometryInvariance.InvariantUnderIsometries)
    (hG : LatticeIsometryGroupActionStatement)
    (hP : PivotOfEveryBond)
    (hD : ComplexMatrix2.ConjugationDeterminant)
    (hT : AveragingSchemeProperties)
    (hS : LogSeriesInComplexGroupStatement) :
    EliminationWeightAtImageBond := by
  intro L m K k i σ hL hm hi hσ hk hik V c c' hc hc' hcc' hV hV'
  have hK : 0 < K := by omega
  have hId := hI L m K k i σ hL hm hi hσ hk hik V (fun _ => complexBlockAverage V c) c c' hc hc'
    hcc' hV hV' rfl
  have hik' : i ≤ levelDepth K k := hik.trans (by simp only [levelDepth]; omega)
  have hGr := hG L m i hL hm hi
  have hsym : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨H, hH⟩ := hGr.1.1
    have h1 : σ ∈ H := by
      have : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
      exact this
    have h3 : σ⁻¹ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := H.inv_mem h1
    rw [hH] at h3
    exact h3
  have hC := (hGr.2.2.2.2 σ hσ (levelDepth K k) hik').1
  have hC' := (hGr.2.2.2.2 σ.symm hsym (levelDepth K k) hik').1
  have hends : ∀ b : BondAtLevel L m K k,
      ((bondPreimage σ b).source : FourTorus L m) = σ.symm b.source ∧
        ((bondPreimage σ b).target : FourTorus L m) = σ.symm b.target := fun b => hC'.2.2.2.1 b
  have hpull : ∀ b : BondAtLevel L m K k, bondPreimage σ (bondImage σ b) = b := by
    intro b
    have hb := hC.2.2.2.1 b
    have p := hends (bondImage σ b)
    apply Bond.ext <;> apply Subtype.ext
    · rw [p.1, hb.1]; simp
    · rw [p.2, hb.2]; simp
  have hopp : ∀ b : BondAtLevel L m K k,
      bondPreimage σ b.opposite = (bondPreimage σ b).opposite := by
    intro b
    have p := hends b
    have q := hends b.opposite
    apply Bond.ext <;> apply Subtype.ext
    · exact q.1.trans p.2.symm
    · exact q.2.trans p.1.symm
  have hbonds : bondImage σ '' (bondsInDoubleBlock c : Set (BondAtLevel L m K k)) =
      bondsInDoubleBlock c' := by
    have hb := ((hB L m hL hm i hi σ hσ).2.1 K k hk hik c).2.2.2
    rw [bondsInDoubleBlock_positivelyOriented, bondsInDoubleBlock_positivelyOriented] at hb
    rcases hcc' with h | h
    · rw [hb, h]
    · rw [hb, h, bondsInDoubleBlock_opposite]
  have hreal : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c' : Set (BondAtLevel L m K k))
      (transportGaugeField σ V) ↔
      IsGaugeField compactGaugeGroup (bondsInDoubleBlock c : Set (BondAtLevel L m K k)) V := by
    rw [← hbonds]
    exact isGaugeField_image_iff hpull hopp _ _ V
  have hb₀ : (pivot c : BondAtLevel L m K k) ∈
      (bondsInDoubleBlock c : Set (BondAtLevel L m K k)) := by
    have h := (hP ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩ k hk c).isPivot.1
    exact ⟨Or.inl h.1, Or.inr h.2⟩
  have hunit : ∀ {g : ComplexMatrix2}, g ∈ complexGaugeGroup → IsUnit g.det := by
    intro g hg
    have hg1 : g.det = 1 := hg
    rw [hg1]
    exact isUnit_one
  have hg₀ : IsUnit (V (pivot c : BondAtLevel L m K k)).det := hunit (hV.1.1.1 _ hb₀)
  have hgW : IsUnit (complexBlockAverage V c : ComplexMatrix2).det :=
    hunit ((hS.2 L hL m K k hm hk c hc).1 V hV)
  have hcomm : ∀ X ∈ ComplexMatrix2.traceless,
      pivotCoeff (transportGaugeField σ V) c'
          (orientationTwist σ V (pivot c : BondAtLevel L m K k) X) =
        orientationTwist σ (fun _ => complexBlockAverage V c) c (pivotCoeff V c X) := by
    intro X hX
    obtain ⟨Y, hY, hXY⟩ := hId.pivotCoeff_conj ⟨X, hX⟩
    have hY' : (Y : ComplexMatrix2) = pivotCoeff V c X := hY
    rw [coe_twistedLinkMap, coe_twistedLinkMap, hY'] at hXY
    exact hXY
  have hinj := orientationTwist_injective σ (fun _ => complexBlockAverage V c) c hgW
  unfold eliminationWeight
  by_cases hr : IsGaugeField compactGaugeGroup (bondsInDoubleBlock c : Set (BondAtLevel L m K k)) V
  · rw [if_pos hr, if_pos (hreal.2 hr)]
    have hW : complexBlockAverage V c ∈ compactGaugeGroup := by
      obtain ⟨-, -, hM, hVal, -⟩ := (hT L hL m K k hm hk AveragingScheme.centred).2.1 c hc
      have hdom : V ∈ (schemeHolomorphyDomain AveragingScheme.centred c :
          Set (BondAtLevel L m K k → ComplexMatrix2)) := by
        rw [hM.domain_eq]
        exact hV
      have hmem := (hVal V hdom hr).average_mem
      rwa [hM.average_eq V hdom] at hmem
    obtain ⟨T, hT₁, hT₂⟩ :=
      exists_hermitianTraceless_equiv hD σ V (pivot c : BondAtLevel L m K k) (hr.1 _ hb₀)
    obtain ⟨T', hT₁', hT₂'⟩ :=
      exists_hermitianTraceless_equiv hD σ (fun _ => complexBlockAverage V c) c hW
    have hn := norm_det_restrictEndomorphism_conj (f := pivotCoeff V c)
      (g := pivotCoeff (transportGaugeField σ V) c') T T' hinj hT₁'
      (fun x => by rw [hT₁]; exact hcomm x x.2.2) hT₂ hT₂'
    simp only [Real.norm_eq_abs] at hn
    rw [hn]
  · rw [if_neg hr, if_neg (fun h => hr (hreal.1 h))]
    obtain ⟨T, hT₁, hT₂⟩ := exists_traceless_equiv hD σ V (pivot c : BondAtLevel L m K k) hg₀
    obtain ⟨T', hT₁', hT₂'⟩ :=
      exists_traceless_equiv hD σ (fun _ => complexBlockAverage V c) c hgW
    have hn := norm_det_restrictEndomorphism_conj (f := pivotCoeff V c)
      (g := pivotCoeff (transportGaugeField σ V) c') T T' hinj hT₁'
      (fun x => by rw [hT₁]; exact hcomm x x.2) hT₂ hT₂'
    rw [hn]
end YangMills.Construction.PeriodicLattice
