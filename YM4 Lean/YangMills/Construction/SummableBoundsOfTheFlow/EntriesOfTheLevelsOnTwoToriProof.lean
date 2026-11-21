import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import YangMills.Construction.HoleBesideASecondHole.CarriedSitesAndPaths
import YangMills.Construction.ResponseInTheExpansion.FieldsOfOneColour
import YangMills.Construction.SummableBoundsOfTheFlow.EntriesOfTheLevelsOnTwoTori
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongATiltProof
import YangMills.Construction.SummableBoundsOfTheFlow.SquaresOfLocalFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction.WeightedResponses
section Upper
variable {L t m : ℕ} [NeZero m]
private def framedBonds {k : ℕ} (c : Fin k → TorusFields.TorusBond m) :
    Fin k → (TorusFields.torusFrame L t m).Site (TorusFields.torusFrame L t m).top × Fin 4 :=
  fun l => (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t m) (TorusFields.torusFrame L t m).top (c l).1, (c l).2)
private theorem maxwellKernel_succ_eq_mixedDeriv (a : ℝ) (b b' : TorusFields.TorusBond m) :
    WeightedResponses.maxwellKernel a L (t + 1) b b' =
      BlockAverages.mixedBondDerivative
        (BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t m)) (TorusFields.torusFrame L t m).top)
        (ColdStepAtMirrorFrames.uniformField (TorusFields.torusFrame L t m) (TorusFields.torusFrame L t m).top)
        (framedBonds (L := L) (t := t) ![b, b']) ![WeightedResponses.unitGenerator, WeightedResponses.unitGenerator] := by
  classical
  unfold WeightedResponses.maxwellKernel TorusFields.mixedDeriv BlockAverages.mixedBondDerivative
  congr 2
  funext σ
  show BlockAverages.minimalAction a (TorusFields.cellsOfSites (TorusFields.torusFrame L t m) Finset.univ) (t + 1)
      (TorusFields.readAtLevel (TorusFields.torusFrame L t m) (t + 1) _) =
    BlockAverages.minimalAction a (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t m)) (t + 1) _
  rw [TopLevelSites.cellsOfSites_univ (F := TorusFields.torusFrame L t m) (n := m) fun _ => rfl]
  congr 1
  funext y i
  show TorusFields.perturb ![b, b'] ![WeightedResponses.unitGenerator, WeightedResponses.unitGenerator] σ
      (TorusFields.trivialField m) (TorusFrame.siteOfCell y) i = _
  simp only [TorusFields.perturb, TorusFields.trivialField, BlockAverages.rotatedField,
    ColdStepAtMirrorFrames.uniformField, BlockAverages.bondSpread, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  have hiff : (![b, b'] : Fin 2 → TorusFields.TorusBond m) l = (TorusFrame.siteOfCell y, i) ↔
      framedBonds (L := L) (t := t) ![b, b'] l = (y, i) := by
    unfold framedBonds
    constructor
    · intro h
      rw [h]
      exact Prod.ext (TorusFrame.torusSiteInFrame_siteOfCell y) rfl
    · intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      refine Prod.ext ?_ h2
      simp only at h1
      rw [← h1, TorusFrame.siteOfCell_torusSiteInFrame]
  exact if_congr hiff rfl rfl
end Upper
section Units
private theorem norm_unitGenerator : ‖(WeightedResponses.unitGenerator : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.ResponseInTheExpansion.SingleColourFields.norm_unitGenerator <;> assumption
private theorem unitGenerator_pair_units :
    BlockAverages.AreUnitVectors
      (![WeightedResponses.unitGenerator, WeightedResponses.unitGenerator] : Fin 2 → BlockAverages.imaginaryQuaternions) := by
  intro l
  have : ‖WeightedResponses.unitGenerator‖ = 1 := norm_unitGenerator
  fin_cases l <;> simpa using this
private theorem re_expUnit_smul_unitGenerator (s : ℝ) :
    ((BlockAverages.expUnit (s • WeightedResponses.unitGenerator) : BlockAverages.UnitQuaternion) : ℍ[ℝ]).re = Real.cos s := by
  rw [TopLevelSites.re_expUnit]
  have : ‖((s • WeightedResponses.unitGenerator : BlockAverages.imaginaryQuaternions) : ℍ[ℝ])‖ = |s| := by
    simp [norm_smul, norm_unitGenerator]
  rw [this, Real.cos_abs]
abbrev _root_.YangMills.SharedProofs.p36152 := @re_expUnit_smul_unitGenerator
private theorem expUnit_smul_unitGenerator_inv (s : ℝ) :
    (BlockAverages.expUnit (s • WeightedResponses.unitGenerator))⁻¹ =
      BlockAverages.expUnit ((-s) • WeightedResponses.unitGenerator) := by
  apply inv_eq_of_mul_eq_one_right
  rw [TorusFrame.expUnit_smul_mul]
  simp [TorusFields.expUnit_zero]
abbrev _root_.YangMills.SharedProofs.p1618 := @expUnit_smul_unitGenerator_inv
end Units
section Wilson
variable {m : ℕ}
private def abelianField (σ : TorusFields.TorusBond m → ℝ) : TorusFields.TorusField m :=
  fun x i => BlockAverages.expUnit (σ (x, i) • WeightedResponses.unitGenerator)
private theorem holonomy_abelianField (σ : TorusFields.TorusBond m → ℝ) (x : TorusFields.TorusSite m) (μ ν : Fin 4) :
    TorusFields.holonomy (abelianField σ) x μ ν =
      BlockAverages.expUnit (WeightedResponses.curl σ (x, μ, ν) • WeightedResponses.unitGenerator) := by
  simp only [TorusFields.holonomy, abelianField, WeightedResponses.curl]
  rw [expUnit_smul_unitGenerator_inv, expUnit_smul_unitGenerator_inv, TorusFrame.expUnit_smul_mul,
    TorusFrame.expUnit_smul_mul, TorusFrame.expUnit_smul_mul]
  congr 2
private theorem plaquetteEnergy_abelianField (σ : TorusFields.TorusBond m → ℝ) (x : TorusFields.TorusSite m) (μ ν : Fin 4) :
    TorusFields.plaquetteEnergy (abelianField σ) x μ ν = 1 - Real.cos (WeightedResponses.curl σ (x, μ, ν)) := by
  rw [TorusFields.plaquetteEnergy, holonomy_abelianField, re_expUnit_smul_unitGenerator]
private theorem iteratedFDeriv_two_sum_one_sub_cos {ι : Type} (P : Finset ι) (α β : ι → ℝ) :
    iteratedFDeriv ℝ 2 (fun σ : Fin 2 → ℝ => ∑ p ∈ P, (1 - Real.cos (σ 0 * α p + σ 1 * β p))) 0
      (fun l => Pi.single l 1) = ∑ p ∈ P, α p * β p := by
  set ℓ : ι → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun p =>
    α p • ContinuousLinearMap.proj 0 + β p • ContinuousLinearMap.proj 1 with hℓ
  have hℓa : ∀ p σ, ℓ p σ = σ 0 * α p + σ 1 * β p := by
    intro p σ
    simp [hℓ]
    ring
  have h1 : ∀ σ : Fin 2 → ℝ, HasFDerivAt (fun σ : Fin 2 → ℝ => ∑ p ∈ P, (1 - Real.cos (σ 0 * α p + σ 1 * β p)))
      (∑ p ∈ P, Real.sin (ℓ p σ) • ℓ p) σ := by
    intro σ
    refine (HasFDerivAt.fun_sum fun p _ => ?_)
    have h := ((ℓ p).hasFDerivAt (x := σ)).cos.const_sub 1
    have e : (fun σ : Fin 2 → ℝ => 1 - Real.cos (σ 0 * α p + σ 1 * β p)) = fun σ => 1 - Real.cos (ℓ p σ) := by
      funext σ
      rw [hℓa]
    rw [e]
    refine h.congr_fderiv ?_
    ext v
    simp
  have h2 : fderiv ℝ (fun σ : Fin 2 → ℝ => ∑ p ∈ P, (1 - Real.cos (σ 0 * α p + σ 1 * β p))) =
      fun σ => ∑ p ∈ P, Real.sin (ℓ p σ) • ℓ p := funext fun σ => (h1 σ).fderiv
  have h3 : HasFDerivAt (fun σ : Fin 2 → ℝ => ∑ p ∈ P, Real.sin (ℓ p σ) • ℓ p)
      (∑ p ∈ P, ((Real.cos (ℓ p 0) • ℓ p).smulRight (ℓ p))) (0 : Fin 2 → ℝ) := by
    refine (HasFDerivAt.fun_sum fun p _ => ?_)
    exact ((ℓ p).hasFDerivAt (x := 0)).sin.smul_const (ℓ p)
  rw [iteratedFDeriv_two_apply, h2, h3.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, map_zero,
    Real.cos_zero, one_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hℓa, hℓa]
  simp
private theorem curl_linear_comb (s s' : ℝ) (A A' : TorusFields.TorusBond m → ℝ) (p : TorusFields.TorusPlaquette m) :
    WeightedResponses.curl (fun d => s * A d + s' * A' d) p =
      s * WeightedResponses.curl A p + s' * WeightedResponses.curl A' p := by
  simp only [WeightedResponses.curl]
  ring
private theorem maxwellKernel_zero_eq_sum [NeZero m] (a : ℝ) (L : ℕ) (b b' : TorusFields.TorusBond m) :
    WeightedResponses.maxwellKernel a L 0 b b' = ∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite m)),
      WeightedResponses.curl (LocalFunctionals.bondIndicator b) p * WeightedResponses.curl (LocalFunctionals.bondIndicator b') p := by
  classical
  have hfun : (fun σ : Fin 2 → ℝ => TorusFields.actionAtLevel a L 0 Finset.univ
      (TorusFields.perturb ![b, b'] ![WeightedResponses.unitGenerator, WeightedResponses.unitGenerator] σ (TorusFields.trivialField m))) =
      fun σ => ∑ p ∈ TorusFields.plaquettesIn (Finset.univ : Finset (TorusFields.TorusSite m)),
        (1 - Real.cos (σ 0 * WeightedResponses.curl (LocalFunctionals.bondIndicator b) p +
          σ 1 * WeightedResponses.curl (LocalFunctionals.bondIndicator b') p)) := by
    funext σ
    have hf : TorusFields.perturb ![b, b'] ![WeightedResponses.unitGenerator, WeightedResponses.unitGenerator] σ
        (TorusFields.trivialField m) =
        abelianField fun d => σ 0 * LocalFunctionals.bondIndicator b d + σ 1 * LocalFunctionals.bondIndicator b' d := by
      funext x i
      simp only [TorusFields.perturb, TorusFields.trivialField, abelianField, mul_one, LocalFunctionals.bondIndicator]
      congr 1
      rw [Fin.sum_univ_two]
      show (if b = (x, i) then σ 0 • WeightedResponses.unitGenerator else (0 : BlockAverages.imaginaryQuaternions)) +
        (if b' = (x, i) then σ 1 • WeightedResponses.unitGenerator else (0 : BlockAverages.imaginaryQuaternions)) = _
      have e1 : ∀ (d : TorusFields.TorusBond m) (s : ℝ),
          (if d = (x, i) then s • WeightedResponses.unitGenerator else (0 : BlockAverages.imaginaryQuaternions)) =
          (s * (if (x, i) = d then 1 else 0)) • WeightedResponses.unitGenerator := by
        intro d s
        by_cases h : d = (x, i)
        · rw [if_pos h, if_pos h.symm, mul_one]
        · rw [if_neg h, if_neg (fun h' => h h'.symm), mul_zero, zero_smul]
      rw [e1, e1, ← add_smul]
    show TorusFields.wilsonAction Finset.univ _ = _
    rw [hf]
    unfold TorusFields.wilsonAction
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [plaquetteEnergy_abelianField]
    have : (p.1, p.2.1, p.2.2) = p := rfl
    rw [this, curl_linear_comb]
  unfold WeightedResponses.maxwellKernel TorusFields.mixedDeriv
  rw [hfun]
  exact iteratedFDeriv_two_sum_one_sub_cos _ _ _
abbrev _root_.YangMills.SharedProofs.p29646 := @maxwellKernel_zero_eq_sum
end Wilson
section Curls
private def latticeCurl (k : Fin 4 × Fin 4) (f : TorusLumps.LatticeBond → ℝ) : ℝ :=
  if k.1 < k.2 then f (0, k.1) + f (Pi.single k.1 1, k.2) - f (Pi.single k.2 1, k.1) - f (0, k.2) else 0
private theorem bondOffsetInBox_zero (μ : Fin 4) : TorusFields.BondOffsetInBox 1 ((0 : Fin 4 → ℤ), μ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · simp
  · show |((0 : Fin 4 → ℤ) + (Pi.single μ 1 : Fin 4 → ℤ)) i| ≤ ((1 : ℕ) : ℤ)
    simp only [zero_add, Pi.single_apply]
    split_ifs <;> simp
private theorem bondOffsetInBox_single {μ ν : Fin 4} (h : μ ≠ ν) :
    TorusFields.BondOffsetInBox 1 ((Pi.single μ 1 : Fin 4 → ℤ), ν) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · show |(Pi.single μ 1 : Fin 4 → ℤ) i| ≤ ((1 : ℕ) : ℤ)
    simp only [Pi.single_apply]
    split_ifs <;> simp
  · show |((Pi.single μ 1 : Fin 4 → ℤ) + (Pi.single ν 1 : Fin 4 → ℤ)) i| ≤ ((1 : ℕ) : ℤ)
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs with h1 h2 h2
    · exact absurd (h1.symm.trans h2) h
    · simp
    · simp
    · simp
private theorem latticeCurl_isLocal (k : Fin 4 × Fin 4) : LocalFunctionals.IsLocalFunctional 1 (latticeCurl k) := by
  constructor
  · simp [latticeCurl]
  · intro f f' hf
    unfold latticeCurl
    by_cases h : k.1 < k.2
    · rw [if_pos h, if_pos h, hf _ (bondOffsetInBox_zero _), hf _ (bondOffsetInBox_zero _),
        hf _ (bondOffsetInBox_single h.ne), hf _ (bondOffsetInBox_single h.ne')]
    · rw [if_neg h, if_neg h]
variable {m : ℕ} [NeZero m]
private theorem curl_eq_latticeCurl (A : TorusFields.TorusBond m → ℝ) (y : TorusFields.TorusSite m) (k : Fin 4 × Fin 4)
    (h : k.1 < k.2) :
    WeightedResponses.curl A (y, k.1, k.2) = latticeCurl k fun u => A (TorusLumps.bondFrom y u) := by
  have e0 : (TorusFields.siteOfInt (0 : Fin 4 → ℤ) : TorusFields.TorusSite m) = 0 := by
    funext i
    simp [TorusFields.siteOfInt]
  unfold WeightedResponses.curl latticeCurl
  rw [if_pos h]
  simp only [TorusLumps.bondFrom, e0, add_zero]
  rw [TorusLumps.unitStep_eq_siteOfInt, TorusLumps.unitStep_eq_siteOfInt]
private theorem maxwellKernel_zero_eq_gramEntry (a : ℝ) (L : ℕ) (b b' : TorusFields.TorusBond m) :
    WeightedResponses.maxwellKernel a L 0 b b' = LocalFunctionals.gramEntry (N := m) (m := m) id latticeCurl b b' := by
  classical
  rw [maxwellKernel_zero_eq_sum]
  unfold LocalFunctionals.gramEntry TorusFields.plaquettesIn
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : k.1 < k.2
  · have e : (k.1 < k.2 ∧ ∀ z ∈ TorusFields.plaquetteVertices y k.1 k.2, z ∈ (Finset.univ : Finset (TorusFields.TorusSite m))) := ⟨h, fun z _ => Finset.mem_univ z⟩
    show (if (k.1 < k.2 ∧ ∀ z ∈ TorusFields.plaquetteVertices y k.1 k.2, z ∈ (Finset.univ : Finset (TorusFields.TorusSite m))) then
      WeightedResponses.curl (LocalFunctionals.bondIndicator b) (y, k.1, k.2) *
        WeightedResponses.curl (LocalFunctionals.bondIndicator b') (y, k.1, k.2) else 0) = _
    rw [if_pos e, curl_eq_latticeCurl _ _ _ h, curl_eq_latticeCurl _ _ _ h]
    rfl
  · have e : ¬ (k.1 < k.2 ∧ ∀ z ∈ TorusFields.plaquetteVertices y k.1 k.2, z ∈ (Finset.univ : Finset (TorusFields.TorusSite m))) :=
      fun h' => h h'.1
    show (if (k.1 < k.2 ∧ ∀ z ∈ TorusFields.plaquetteVertices y k.1 k.2, z ∈ (Finset.univ : Finset (TorusFields.TorusSite m))) then
      WeightedResponses.curl (LocalFunctionals.bondIndicator b) (y, k.1, k.2) *
        WeightedResponses.curl (LocalFunctionals.bondIndicator b') (y, k.1, k.2) else 0) = _
    rw [if_neg e]
    simp [latticeCurl, h]
end Curls
private theorem uniformField_isSmallCurvature {F : BlockAverages.BlockFrame} {s : ℝ} (hs : 0 < s) :
    ColdStepAtMirrorFrames.IsSmallCurvature s (ColdStepAtMirrorFrames.uniformField F F.top) := by apply _root_.YangMills.Construction.BlockMeans.SegmentMean.isSmallCurvature_uniformField <;> assumption
private theorem bondOffsetInBox_mono {ρ r : ℕ} (h : ρ ≤ r) {e : TorusLumps.LatticeBond}
    (he : TorusFields.BondOffsetInBox ρ e) : TorusFields.BondOffsetInBox r e := by
  have hz : (ρ : ℤ) ≤ r := by exact_mod_cast h
  exact ⟨fun i => (he.1 i).trans hz, fun i => (he.2 i).trans hz⟩
theorem maxwellKernelDecayAndLocality_of_gramEntries (hSq : LocalFunctionals.GramEntriesTranslationInvariant) :
    WeightedResponses.MaxwellKernelDecayAndLocality := by
  classical
  intro a L c hc
  obtain ⟨Γ, C₀, hC₀, hsq⟩ := hSq (Fin 4 × Fin 4) 1 1 latticeCurl le_rfl latticeCurl_isLocal
  obtain ⟨⟨-, -, hs₀, hδ₂, -, -, -, hKk⟩, hest⟩ := hc.classical
  have hδ₁ : 0 < c.δ₁ := hc.positivity.1
  have hσ : 0 < c.σA := hc.positivity.2.2.2.1
  have hN2 : 0 < c.N 2 := hc.positivity.2.2.2.2.2.1 2
  set μ : ℝ := min c.δ₁ (c.δ₂ / 2) with hμ
  have hμ0 : 0 < μ := lt_min hδ₁ (by linarith)
  have hμ1 : μ ≤ c.δ₁ := min_le_left _ _
  have hμ2 : μ ≤ c.δ₂ / 2 := min_le_right _ _
  have hKk2 := hKk 2
  have hexp : 0 ≤ C₀ * Real.exp (2 * μ) := by positivity
  set C : ℝ := c.N 2 + c.Kk 2 + C₀ * Real.exp (2 * μ) + 1 with hC
  have hCpos : 0 < C := by positivity
  refine ⟨C, μ, hCpos, hμ0, ?_⟩
  intro u m m' _ _ h64 h64'
  have hsq₁ := hsq m m (id : TorusFields.TorusSite m → TorusFields.TorusSite m) (by simp) (by intro y v; simp)
  have hsq₂ := hsq m' m' (id : TorusFields.TorusSite m' → TorusFields.TorusSite m') (by simp) (by intro y v; simp)
  cases u with
  | zero =>
    refine ⟨fun b b' => ?_, fun y y' ρ r e e' hr hr' hρ he he' => ?_⟩
    · rw [maxwellKernel_zero_eq_gramEntry]
      by_cases hd : 2 * 1 < TorusFields.supDist b.1 b'.1
      · rw [hsq₁.2.1 b b' hd, abs_zero]
        positivity
      · have h1 : |LocalFunctionals.gramEntry (N := m) (m := m) id latticeCurl b b'| ≤ C₀ := by
          refine hsq₁.2.2 (fun x => ⟨x, 0, ?_, fun i => by simp⟩) (by omega) b b'
          funext i
          simp [TorusFields.siteOfInt]
        have hdn : (TorusFields.supDist b.1 b'.1 : ℝ) ≤ 2 := by
          have : TorusFields.supDist b.1 b'.1 ≤ 2 := by omega
          exact_mod_cast this
        have h2 : 1 ≤ Real.exp (2 * μ) * Real.exp (-(μ * TorusFields.supDist b.1 b'.1)) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by nlinarith)
        have h3 : C₀ ≤ C₀ * Real.exp (2 * μ) * Real.exp (-(μ * TorusFields.supDist b.1 b'.1)) := by
          rw [mul_assoc]
          exact le_mul_of_one_le_right hC₀ h2
        have h4 : C₀ * Real.exp (2 * μ) ≤ C := by
          rw [hC]
          linarith
        exact h1.trans (h3.trans (mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le))
    · rw [maxwellKernel_zero_eq_gramEntry, maxwellKernel_zero_eq_gramEntry]
      have e1 := hsq₁.1 y r e e' (by omega) (bondOffsetInBox_mono hρ he) he'
      have e2 := hsq₂.1 y' r e e' (by omega) (bondOffsetInBox_mono hρ he) he'
      simp only [id] at e1 e2
      rw [e1, e2, sub_self, abs_zero]
      positivity
  | succ t =>
    have hs : 0 < c.s₀ := hs₀
    refine ⟨fun b b' => ?_, fun y y' ρ r e e' hr hr' hρ he he' => ?_⟩
    · rw [maxwellKernel_succ_eq_mixedDeriv]
      have hF : ColdStepAtMirrorFrames.IsBlockTorus L (TorusFields.torusFrame L t m) := ⟨rfl, m, h64, fun _ => rfl⟩
      have hcl := hc.estimates (TorusFields.torusFrame L t m) c.σA (ColdStepAtMirrorFrames.uniformField _ _) hF hσ le_rfl
        (uniformField_isSmallCurvature hσ)
      have h1 := hcl.cellShares.2.2.2.2.2.1 2 (framedBonds (L := L) (t := t) ![b, b'])
        ![WeightedResponses.unitGenerator, WeightedResponses.unitGenerator] le_rfl unitGenerator_pair_units
      have h2 : TorusFields.supDist b.1 b'.1 ≤ BlockAverages.bondListDiameter (framedBonds (L := L) (t := t) ![b, b']) := by
        have e1 : BlockAverages.cellSupDist (framedBonds (L := L) (t := t) ![b, b'] 0).1
            (framedBonds (L := L) (t := t) ![b, b'] 1).1 = TorusFields.supDist b.1 b'.1 := by
          rw [TorusFrame.cellSupDist_torusFrame]
          show TorusFields.supDist (TorusFrame.siteOfCell (StepCosts.torusSiteInFrame _ _ b.1))
            (TorusFrame.siteOfCell (StepCosts.torusSiteInFrame _ _ b'.1)) = _
          rw [TorusFrame.siteOfCell_torusSiteInFrame, TorusFrame.siteOfCell_torusSiteInFrame]
        rw [← e1]
        exact (Finset.le_sup (f := fun l' => BlockAverages.cellSupDist (framedBonds (L := L) (t := t) ![b, b'] 0).1
            (framedBonds (L := L) (t := t) ![b, b'] l').1) (Finset.mem_univ 1)).trans
          (Finset.le_sup (f := fun l => Finset.univ.sup fun l' =>
            BlockAverages.cellSupDist (framedBonds (L := L) (t := t) ![b, b'] l).1 (framedBonds (L := L) (t := t) ![b, b'] l').1)
            (Finset.mem_univ 0))
      have h2' : (TorusFields.supDist b.1 b'.1 : ℝ) ≤
          BlockAverages.bondListDiameter (framedBonds (L := L) (t := t) ![b, b']) := by exact_mod_cast h2
      have h3 : Real.exp (-c.δ₁ * BlockAverages.bondListDiameter (framedBonds (L := L) (t := t) ![b, b'])) ≤
          Real.exp (-(μ * TorusFields.supDist b.1 b'.1)) := by
        refine Real.exp_le_exp.2 ?_
        have : (0 : ℝ) ≤ TorusFields.supDist b.1 b'.1 := by positivity
        nlinarith
      have h4 : c.N 2 ≤ C := by
        rw [hC]
        linarith
      exact h1.trans (mul_le_mul h4 h3 (Real.exp_pos _).le hCpos.le)
    · rw [maxwellKernel_succ_eq_mixedDeriv, maxwellKernel_succ_eq_mixedDeriv]
      have hF : ColdStepAtMirrorFrames.IsBlockTorus L (TorusFields.torusFrame L t m) := ⟨rfl, m, h64, fun _ => rfl⟩
      have hF' : ColdStepAtMirrorFrames.IsBlockTorus L (TorusFields.torusFrame L t m') := ⟨rfl, m', h64', fun _ => rfl⟩
      have hw : ∀ (n : ℕ) [NeZero n] (z : (TorusFields.torusFrame L t n).Cell),
          z ∈ ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t n) := by
        intro n _ z
        exact TopLevelSites.mem_finiteCells (fun _ => Nat.pos_of_ne_zero (NeZero.ne n)) z
      have hagree : BlockAverages.AgreeOnBall (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t m))
          (ColdStepAtMirrorFrames.uniformField (TorusFields.torusFrame L t m) (TorusFields.torusFrame L t m).top)
          (ColdStepAtMirrorFrames.finiteCells (TorusFields.torusFrame L t m'))
          (ColdStepAtMirrorFrames.uniformField (TorusFields.torusFrame L t m') (TorusFields.torusFrame L t m').top)
          (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t m) (TorusFields.torusFrame L t m).top y)
          (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t m') (TorusFields.torusFrame L t m').top y') r :=
        ⟨fun _ => Or.inr (by show 2 * r + 2 < m; omega), fun _ => Or.inr (by show 2 * r + 2 < m'; omega),
          fun h _ => ⟨fun _ => hw _ _, fun _ => hw _ _⟩, fun _ _ => rfl⟩
      have hcomp := (hest (TorusFields.torusFrame L t m) c.s₀ (ColdStepAtMirrorFrames.uniformField _ _) hF hs le_rfl
        (uniformField_isSmallCurvature hs)).2.2.2
        (TorusFields.torusFrame L t m') (ColdStepAtMirrorFrames.uniformField _ _) _ _ r hF' rfl
        (uniformField_isSmallCurvature hs) hagree
      have hboxes : ∀ l, BlockAverages.BondWithinRadius r ((![e, e'] : Fin 2 → TorusLumps.LatticeBond) l) := by
        intro l
        fin_cases l
        · exact bondOffsetInBox_mono hρ he
        · exact he'
      have hact := hcomp.action 1 ![e, e'] ![WeightedResponses.unitGenerator, WeightedResponses.unitGenerator] hboxes
        unitGenerator_pair_units
      have hbonds : ∀ (n : ℕ) [NeZero n] (z : TorusFields.TorusSite n),
          framedBonds (L := L) (t := t) ![TorusLumps.bondFrom z e, TorusLumps.bondFrom z e'] =
          ColdStepAtMirrorFrames.bondsAt (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top z)
            ![e, e'] := by
        intro n _ z
        have hk : ∀ w : TorusLumps.LatticeBond,
            StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top (TorusLumps.bondFrom z w).1 =
            StepCosts.torusSiteInFrame (TorusFields.torusFrame L t n) (TorusFields.torusFrame L t n).top z +
              BlockAverages.siteOfCoords (TorusFields.torusFrame L t n).top w.1 := by
          intro w
          have hm : ∀ k, (TorusFields.torusFrame L t n).period (TorusFields.torusFrame L t n).top k = n :=
            fun k => TorusFrame.period_torusFrame k
          have h1 := FrameTransfer.torusToFrame_add (F := TorusFields.torusFrame L t n) (j := (TorusFields.torusFrame L t n).top)
            hm z (TorusFields.siteOfInt w.1)
          rw [FrameTransfer.torusToFrame_siteOfInt hm] at h1
          exact h1
        funext l
        fin_cases l
        · exact Prod.ext (hk e) rfl
        · exact Prod.ext (hk e') rfl
      rw [hbonds m y, hbonds m' y']
      have hcd : (BlockAverages.cellSupDist (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t m) (TorusFields.torusFrame L t m).top y)
          (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t m) (TorusFields.torusFrame L t m).top y +
            BlockAverages.siteOfCoords (TorusFields.torusFrame L t m).top e.1) : ℝ) ≤ ρ := by
        have : BlockAverages.cellSupDist (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t m) (TorusFields.torusFrame L t m).top y)
            (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t m) (TorusFields.torusFrame L t m).top y +
              BlockAverages.siteOfCoords (TorusFields.torusFrame L t m).top e.1) ≤ ρ := by
          rw [TorusFrame.cellSupDist_torusFrame, TorusFrame.siteOfCell_add, TorusFrame.siteOfCell_siteOfCoords,
            TorusFrame.siteOfCell_torusSiteInFrame]
          refine TorusFields.supDist_add_siteOfInt_le y e.1 ρ fun i => ?_
          have := he.1 i
          rw [Int.abs_eq_natAbs] at this
          exact_mod_cast this
        exact_mod_cast this
      have hρr : (ρ : ℝ) ≤ r := by exact_mod_cast hρ
      have h5 : Real.exp (-(c.δ₂ / 2 * ((r : ℝ) -
          (BlockAverages.cellSupDist (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t m) (TorusFields.torusFrame L t m).top y)
            (StepCosts.torusSiteInFrame (TorusFields.torusFrame L t m) (TorusFields.torusFrame L t m).top y +
              BlockAverages.siteOfCoords (TorusFields.torusFrame L t m).top e.1) : ℝ)))) ≤
          Real.exp (-(μ * ((r : ℝ) - ρ))) := by
        refine Real.exp_le_exp.2 ?_
        have g1 : (0 : ℝ) ≤ (r : ℝ) - ρ := by linarith
        nlinarith
      have h6 : c.Kk 2 ≤ C := by
        rw [hC]
        linarith
      exact hact.trans (mul_le_mul h6 h5 (Real.exp_pos _).le hCpos.le)
end YangMills.Construction.WeightedResponses
end
