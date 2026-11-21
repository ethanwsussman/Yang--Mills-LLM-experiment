import YangMills.Construction.ColdStepAtMirrorFrames.EmbeddedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.EnergyAboutAChartPointProof
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionAlongTheChart
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsCompareOnEqualCharts
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionsCompareOnPairedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.GradientOfANearFunction
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsOfATorus
import YangMills.Construction.ColdStepAtMirrorFrames.SumsAgainstFlatResponsesProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace PairedExpansions
theorem one_le_torusDecayFactor (L : ℕ) {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) : 1 ≤ torusDecayFactor L δ x := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatResponseSums.one_le_decayWeight <;> assumption
theorem one_div_torusDecayFactor_le_exp (L : ℕ) (δ x : ℝ) : 1 / torusDecayFactor L δ x ≤ Real.exp (-(δ * x)) := by
  unfold torusDecayFactor
  have h1 : (1 : ℝ) ≤ max 1 ((x / (L : ℝ) ^ (1 / 640 : ℝ)) ^ 16000) := le_max_left _ _
  have h2 := Real.exp_pos (δ * x)
  rw [Real.exp_neg, div_le_iff₀ (by positivity)]
  have : (Real.exp (δ * x))⁻¹ * Real.exp (δ * x) = 1 := inv_mul_cancel₀ h2.ne'
  have h3 : 0 < (Real.exp (δ * x))⁻¹ := inv_pos.2 h2
  nlinarith [mul_le_mul_of_nonneg_right h1 (mul_pos h3 h2).le]
section Translation
variable {ι : Type} [Fintype ι]
theorem fderiv_eq_of_comp_add_left {A G : BondField ι → ℝ} {η : BondField ι} (h : ∀ ζ, A ζ = G (η + ζ))
    (ζ : BondField ι) : fderiv ℝ A ζ = fderiv ℝ G (η + ζ) := by
  have e : A = fun ζ => G (η + ζ) := funext h
  rw [e]
  exact fderiv_comp_add_left η
theorem secondDerivAlong_eq_of_comp_add_left {A G : BondField ι → ℝ} {η : BondField ι}
    (h : ∀ ζ, A ζ = G (η + ζ)) (ζ u v : BondField ι) :
    secondDerivAlong A ζ u v = secondDerivAlong G (η + ζ) u v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.ChartedEnergyLocal.secondDerivAlong_shift <;> assumption
theorem contDiffAt_of_comp_add_left {A G : BondField ι → ℝ} {η : BondField ι} (h : ∀ ζ, A ζ = G (η + ζ))
    {n : WithTop ℕ∞} (hA : ContDiffAt ℝ n A 0) : ContDiffAt ℝ n G η := by
  have e : G = fun y => A (y - η) := by
    funext y
    rw [h]
    congr 1
    abel
  rw [e]
  refine ContDiffAt.comp η (g := A) (f := fun y => y - η) ?_ (by fun_prop)
  simpa using hA
end Translation
theorem abs_sub_le_two_mul {a b A : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ A) : |a - b| ≤ 2 * A := by
  have := abs_sub a b
  linarith
theorem le_siteSupDist_of_not_withinRadius (hO : TorusOffsetsAboutCell) {F : BlockFrame} {Y : F.Cell} {q s : ℕ}
    {g h o u : Fin 4 → ℤ} {i : Fin 4}
    (hodd : Odd F.blockSide) (hs : ∀ i, 2 * q + 2 < F.extent i) (hh : WithinRadius s h) (hsq : s ≤ q)
    (hg : WithinRadius q g) (hfar : ¬ WithinRadius (q / 2) g) (ho : o ∈ centredCube F.blockSide)
    (hu : u ∈ centredCube F.blockSide) :
    (F.blockSide : ℝ) * (((q / 2 : ℕ) : ℝ) - s) ≤ siteSupDist (fineBondAt Y h o 0).1 (fineBondAt Y g u i).1 := by
  have hhq : WithinRadius q h := fun l => (hh l).trans (by exact_mod_cast hsq)
  obtain ⟨c1, _, d1, _, _, _, hcomm, _, hsite⟩ := hO F q Y hodd hs
  have htri := (hO F q (Y + siteOfCoords F.top h) hodd hs).2.2.2.2.2.2.2.1
  have e1 := (c1 h o 0 ho).1
  have e2 := (c1 g u i hu).1
  have hb := hsite (fineBondAt Y g u i).1 (fineBondAt Y h o 0).1
  rw [e1, e2] at hb
  have t1 := htri (Y + siteOfCoords F.top g) Y
  have dh : cellSupDist Y (Y + siteOfCoords F.top h) ≤ s := by
    rw [(d1 h hhq).2]
    refine Finset.sup_le fun l _ => ?_
    have := hh l
    rw [Int.abs_eq_natAbs] at this
    omega
  have dg : q / 2 + 1 ≤ cellSupDist (Y + siteOfCoords F.top g) Y := by
    rw [(d1 g hg).1]
    unfold WithinRadius at hfar
    rw [not_forall] at hfar
    obtain ⟨l, hl⟩ := hfar
    rw [not_le, Int.abs_eq_natAbs] at hl
    have h1 : (q / 2) < (g l).natAbs := by exact_mod_cast hl
    have h2 : (g l).natAbs ≤ Finset.univ.sup fun i => (g i).natAbs :=
      Finset.le_sup (f := fun i => (g i).natAbs) (Finset.mem_univ l)
    omega
  have hc2 := hcomm (Y + siteOfCoords F.top h) (Y + siteOfCoords F.top g)
  have h3 : q / 2 + 1 ≤ cellSupDist (Y + siteOfCoords F.top h) (Y + siteOfCoords F.top g) + s := by omega
  have h4 : F.blockSide * (q / 2 + 1) ≤
      F.blockSide * (cellSupDist (Y + siteOfCoords F.top h) (Y + siteOfCoords F.top g) + s) :=
    Nat.mul_le_mul_left _ h3
  have h5 : (F.blockSide : ℝ) * (((q / 2 : ℕ) : ℝ) + 1) ≤
      (F.blockSide : ℝ) * ((cellSupDist (Y + siteOfCoords F.top h) (Y + siteOfCoords F.top g) : ℝ) + s) := by
    exact_mod_cast h4
  have h6 : (F.blockSide : ℝ) * (cellSupDist (Y + siteOfCoords F.top h) (Y + siteOfCoords F.top g) : ℝ) ≤
      (siteSupDist (fineBondAt Y h o 0).1 (fineBondAt Y g u i).1 : ℝ) + F.blockSide := by exact_mod_cast hb
  nlinarith
end PairedExpansions
open PairedExpansions in
theorem pairedExpansionsComparison_holds (hAl : CentredFamilyInChartBounds) (hEq : ExpansionDifferenceBoundOnAgreeingCharts)
    (hO : TorusOffsetsAboutCell) (hEm : PushforwardFieldProperties) (hGr : BondPartialDiffBound)
    (hPV : PairedCoordinatesAgree) (hLC : ImaginaryCoordinatesIsometric) :
    PairedExpansionsComparison := by
  classical
  obtain ⟨C₁, hC₁, hA⟩ := hAl
  obtain ⟨C₂, hC₂, hE⟩ := hEq
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro L t n₀ σ δ ε ε₃ f hodd hδ hε hfam F F' w w' V V' Y Y' q r₂ s θ ρ hh Δ ι _ _ j j' h o
    hTF hTF' hθ hρ hh0 hhρ hr₂ hs hs' inj inj' hp hΔ hoff heq hgood hgood' hag hin hq ho
  obtain ⟨hFL, hFt, n, hside, hn⟩ := id hTF
  obtain ⟨hFL', hFt', n', hside', hn'⟩ := id hTF'
  have hLpos : 0 < L := hodd.pos
  have hLT := hTF
  have hLT' := hTF'
  have hoddF : Odd F.blockSide := hFL ▸ hodd
  have hoddF' : Odd F'.blockSide := hFL' ▸ hodd
  have hLL : F.blockSide = F'.blockSide := hFL.trans hFL'.symm
  have hmv := hLC.2.2.2.2.1
  set y := (fineBondAt Y h o 0).1 with hy
  set y' := (fineBondAt Y' h o 0).1 with hy'
  set Γ := readInChart (subtractTrivial f F y) w V with hΓ
  set Γ' := readInChart (subtractTrivial f F' y') w' V' with hΓ'
  have sh : ∀ (η ζ : StepVariable (finiteCells F)),
      readInChart (subtractTrivial f F y) (shiftCoordinates w η) V ζ = Γ (η + ζ) := fun η ζ => by
    show subtractTrivial f F y (chartedField (shiftCoordinates (shiftCoordinates w η) ζ) V) =
      subtractTrivial f F y (chartedField (shiftCoordinates w (η + ζ)) V)
    rw [hmv]
  have sh' : ∀ (η ζ : StepVariable (finiteCells F')),
      readInChart (subtractTrivial f F' y') (shiftCoordinates w' η) V' ζ = Γ' (η + ζ) :=
    fun η ζ => by
    show subtractTrivial f F' y' (chartedField (shiftCoordinates (shiftCoordinates w' η) ζ) V') =
      subtractTrivial f F' y' (chartedField (shiftCoordinates w' (η + ζ)) V')
    rw [hmv]
  have A := fun (η : StepVariable (finiteCells F)) (hc : IsSmallCurvature σ (chartedField (shiftCoordinates w η) V))
      (hw : ∀ b ∈ chordBonds (finiteCells F), ‖shiftCoordinates w η b.1 b.2‖ ≤ 1) =>
    hA L t n₀ σ δ ε ε₃ f hδ hε hfam F (shiftCoordinates w η) V y hLT hc hw
  have A' := fun (η : StepVariable (finiteCells F'))
      (hc : IsSmallCurvature σ (chartedField (shiftCoordinates w' η) V'))
      (hw : ∀ b ∈ chordBonds (finiteCells F'), ‖shiftCoordinates w' η b.1 b.2‖ ≤ 1) =>
    hA L t n₀ σ δ ε ε₃ f hδ hε hfam F' (shiftCoordinates w' η) V' y' hLT' hc hw
  obtain ⟨_, _, ea, va, _, _, hemb⟩ := hEm _ _ j inj
  obtain ⟨_, _, ea', va', _, _, hemb'⟩ := hEm _ _ j' inj'
  have s0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.2 zero_le_one
  have s1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.2 zero_le_one
  have g0 : ∀ ξ ∈ openPolyball ι (2 * ρ), IsSmallCurvature σ (chartedField (shiftCoordinates w (pushforwardField j ξ)) V) ∧
      ∀ b ∈ chordBonds (finiteCells F), ‖shiftCoordinates w (pushforwardField j ξ) b.1 b.2‖ ≤ 1 := fun ξ hξ => by
    have := hgood ξ hξ 0 s0
    rw [zero_smul, add_zero] at this
    exact this
  have g1 : ∀ ξ ∈ openPolyball ι (2 * ρ),
      IsSmallCurvature σ (chartedField (shiftCoordinates w (Δ + pushforwardField j ξ)) V) ∧
      ∀ b ∈ chordBonds (finiteCells F), ‖shiftCoordinates w (Δ + pushforwardField j ξ) b.1 b.2‖ ≤ 1 :=
    fun ξ hξ => by
    have := hgood ξ hξ 1 s1
    rw [one_smul, add_comm] at this
    exact this
  have cΓ : ∀ η, IsSmallCurvature σ (chartedField (shiftCoordinates w η) V) →
      (∀ b ∈ chordBonds (finiteCells F), ‖shiftCoordinates w η b.1 b.2‖ ≤ 1) → ContDiffAt ℝ 3 Γ η :=
    fun η hc hw => contDiffAt_of_comp_add_left (sh η) (A η hc hw).1
  have cΓ' : ∀ η, IsSmallCurvature σ (chartedField (shiftCoordinates w' η) V') →
      (∀ b ∈ chordBonds (finiteCells F'), ‖shiftCoordinates w' η b.1 b.2‖ ≤ 1) → ContDiffAt ℝ 3 Γ' η :=
    fun η hc hw => contDiffAt_of_comp_add_left (sh' η) (A' η hc hw).1
  have sΓ := fun (η : StepVariable (finiteCells F)) (u v : StepVariable (finiteCells F)) =>
    (secondDerivAlong_eq_of_comp_add_left (sh η) 0 u v)
  have fΓ := fun (η : StepVariable (finiteCells F)) => fderiv_eq_of_comp_add_left (sh η) 0
  have fΓ' := fun (η : StepVariable (finiteCells F')) => fderiv_eq_of_comp_add_left (sh' η) 0
  set R₂ : BondField ι → ℝ := fun ξ => Γ (Δ + pushforwardField j ξ) with hR₂
  set Γ₂ : StepVariable (finiteCells F) → ℝ := fun η => Γ (Δ + η) with hΓ₂
  have cΓ₂ : ∀ ξ ∈ openPolyball ι (2 * ρ), ContDiffAt ℝ 3 Γ₂ (pushforwardField j ξ) := fun ξ hξ => by
    have h1 := cΓ _ (g1 ξ hξ).1 (g1 ξ hξ).2
    have e : Γ₂ = Γ ∘ fun η => Δ + η := rfl
    rw [e]
    exact ContDiffAt.comp _ h1 (by fun_prop)
  have e3 : (3 : WithTop ℕ∞) ≠ 0 := by norm_num
  have cR : ∀ ξ ∈ openPolyball ι (2 * ρ), ContDiffAt ℝ 3 (fun z => Γ (pushforwardField j z)) ξ := fun ξ hξ =>
    (hemb 3 Γ ξ (cΓ _ (g0 ξ hξ).1 (g0 ξ hξ).2)).1
  have cR' : ∀ ξ ∈ openPolyball ι (2 * ρ), ContDiffAt ℝ 3 (fun z => Γ' (pushforwardField j' z)) ξ := fun ξ hξ =>
    (hemb' 3 Γ' ξ (cΓ' _ (hgood' ξ hξ).1 (hgood' ξ hξ).2)).1
  have cR₂ : ∀ ξ ∈ openPolyball ι (2 * ρ), ContDiffAt ℝ 3 R₂ ξ := fun ξ hξ => (hemb 3 Γ₂ ξ (cΓ₂ ξ hξ)).1
  have hC1 : C₁ ≤ C₁ + C₂ := by linarith
  have hN : (0 : ℝ) ≤ (ballChordBonds F Y r₂).card := Nat.cast_nonneg _
  have hmove : ∀ ξ ∈ openPolyball ι (2 * ρ),
      |R₂ ξ - Γ (pushforwardField j ξ)| ≤ (C₁ + C₂) * ε * θ * (ballChordBonds F Y r₂).card := by
    intro ξ hξ
    have hpt : ∀ v ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 3 Γ (pushforwardField j ξ + v • Δ) := fun v hv =>
      cΓ _ (hgood ξ hξ v hv).1 (hgood ξ hξ v hv).2
    have hd : ∀ v ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun v : ℝ => Γ (pushforwardField j ξ + v • Δ))
        (fderiv ℝ Γ (pushforwardField j ξ + v • Δ) Δ) (Set.Icc 0 1) v := fun v hv => by
      have h1 : HasDerivAt (fun v : ℝ => pushforwardField j ξ + v • Δ) Δ v := by
        simpa using ((hasDerivAt_id v).smul_const Δ).const_add (pushforwardField j ξ)
      have h2 := ((hpt v hv).differentiableAt (by norm_num)).hasFDerivAt
      exact (h2.comp_hasDerivAt v h1).hasDerivWithinAt
    have hb : ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ Γ (pushforwardField j ξ + v • Δ) Δ‖ ≤
        (C₁ + C₂) * ε * θ * (ballChordBonds F Y r₂).card := fun v hv => by
      have hgv := hgood ξ hξ v hv
      have e1 : fderiv ℝ Γ (pushforwardField j ξ + v • Δ) Δ =
          ∑ b : ↥(chordBonds (finiteCells F)),
            fderiv ℝ Γ (pushforwardField j ξ + v • Δ) (bondVariation b (Δ b)) := by
        unfold bondVariation
        rw [← map_sum, Finset.univ_sum_single]
      rw [e1, Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ b : ↥(chordBonds (finiteCells F)),
          |fderiv ℝ Γ (pushforwardField j ξ + v • Δ) (bondVariation b (Δ b))| ≤ (C₁ + C₂) * ε * ‖Δ b‖ :=
        fun b => by
        have h1 := (A _ hgv.1 hgv.2).2.1 b (Δ b)
        rw [fΓ (pushforwardField j ξ + v • Δ), add_zero] at h1
        refine h1.trans ?_
        have hw1 := one_le_torusDecayFactor L (x := siteSupDist y b.1.1) hδ (by positivity)
        have hnum : 0 ≤ C₁ * ε * ‖Δ b‖ := by positivity
        refine (div_le_self hnum hw1).trans ?_
        have : 0 ≤ ε * ‖Δ b‖ := by positivity
        nlinarith
      refine (Finset.sum_le_sum fun b _ => hterm b).trans ?_
      have e2 : ∑ b : ↥(chordBonds (finiteCells F)), (C₁ + C₂) * ε * ‖Δ b‖ =
          ∑ b ∈ ballChordBonds F Y r₂, (C₁ + C₂) * ε * ‖Δ b‖ := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun b _ hb' => ?_).symm
        simp [hoff b hb']
      rw [e2]
      have hcε : 0 ≤ (C₁ + C₂) * ε := by positivity
      calc ∑ b ∈ ballChordBonds F Y r₂, (C₁ + C₂) * ε * ‖Δ b‖ ≤
            ∑ _b ∈ ballChordBonds F Y r₂, (C₁ + C₂) * ε * θ :=
            Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hΔ b) hcε
        _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
    have hm := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb s0 s1
    simp only [zero_smul, add_zero, one_smul, sub_zero, norm_one, mul_one, Real.norm_eq_abs] at hm
    rw [hR₂]
    simp only
    rw [add_comm Δ]
    exact hm
  have sec1 : ∀ ξ ∈ openPolyball ι (2 * ρ), ∀ (k : ι) (u : BondVector), ‖u‖ = 1 →
      |secondDerivAlong (fun z => Γ (pushforwardField j z)) ξ (bondVariation k u) (bondVariation k u)| ≤
        (C₁ + C₂) * ε := fun ξ hξ k u hu => by
    have h1 := (hemb 3 Γ ξ (cΓ _ (g0 ξ hξ).1 (g0 ξ hξ).2)).2.2.1 (by norm_num) (bondVariation k u)
      (bondVariation k u)
    rw [h1, ea]
    have h2 := (A _ (g0 ξ hξ).1 (g0 ξ hξ).2).2.2 (j k) u
    rw [sΓ (pushforwardField j ξ), add_zero, hu] at h2
    refine h2.trans ?_
    nlinarith
  have sec2 : ∀ ξ ∈ openPolyball ι (2 * ρ), ∀ (k : ι) (u : BondVector), ‖u‖ = 1 →
      |secondDerivAlong R₂ ξ (bondVariation k u) (bondVariation k u)| ≤ (C₁ + C₂) * ε := fun ξ hξ k u hu => by
    have h1 := (hemb 3 Γ₂ ξ (cΓ₂ ξ hξ)).2.2.1 (by norm_num) (bondVariation k u) (bondVariation k u)
    have h1' : secondDerivAlong R₂ ξ (bondVariation k u) (bondVariation k u) =
        secondDerivAlong Γ₂ (pushforwardField j ξ) (pushforwardField j (bondVariation k u))
          (pushforwardField j (bondVariation k u)) := h1
    rw [h1', ea]
    have h3 : secondDerivAlong Γ₂ (pushforwardField j ξ) (bondVariation (j k) u) (bondVariation (j k) u) =
        secondDerivAlong Γ (Δ + pushforwardField j ξ) (bondVariation (j k) u) (bondVariation (j k) u) :=
      secondDerivAlong_eq_of_comp_add_left (fun _ => rfl) _ _ _
    rw [h3]
    have h2 := (A _ (g1 ξ hξ).1 (g1 ξ hξ).2).2.2 (j k) u
    rw [sΓ (Δ + pushforwardField j ξ), add_zero, hu] at h2
    refine h2.trans ?_
    nlinarith
  have hgrad := hGr ι ρ (2 * ρ) hh ((C₁ + C₂) * ε * θ * (ballChordBonds F Y r₂).card) ((C₁ + C₂) * ε) R₂
    (fun z => Γ (pushforwardField j z)) hh0 hρ (by linarith)
    (fun ξ hξ => ((cR₂ ξ hξ).of_le (by norm_num)).contDiffWithinAt)
    (fun ξ hξ => ((cR ξ hξ).of_le (by norm_num)).contDiffWithinAt) hmove sec2 sec1
  refine ⟨fun ξ hξ => ((cR ξ hξ).of_le (by norm_num)).contDiffWithinAt,
    fun ξ hξ => ((cR' ξ hξ).of_le (by norm_num)).contDiffWithinAt, fun ξ hξ => ?_⟩
  have hξ2 : ξ ∈ openPolyball ι (2 * ρ) := fun b => by have := hξ b; linarith
  have hs₂ : ∀ i, 2 * r₂ + 2 < F.extent i := fun i => by have := hs i; omega
  have hs₂' : ∀ i, 2 * r₂ + 2 < F'.extent i := fun i => by have := hs' i; omega
  have heq₂ : ∀ (h₁ o₁ : Fin 4 → ℤ) (i : Fin 4), WithinRadius r₂ h₁ → o₁ ∈ centredCube L →
      fineBondAt Y h₁ o₁ i ∈ chordBonds (finiteCells F) →
      shiftCoordinates w (Δ + pushforwardField j ξ) (fineBondAt Y h₁ o₁ i).1 i =
        shiftCoordinates w' (pushforwardField j' ξ) (fineBondAt Y' h₁ o₁ i).1 i := fun h₁ o₁ i hb ho₁ hc => by
    have hbq : WithinRadius q h₁ := fun l => (hb l).trans (by exact_mod_cast hr₂)
    have hco := (hPV F F' Y Y' q ι j j' ξ h₁ o₁ i hLL hoddF hs hs' inj inj' hp hbq (by rw [hFL]; exact ho₁)).2
    have h1 := heq h₁ o₁ i hb ho₁ hc
    have e1 : shiftCoordinates w (Δ + pushforwardField j ξ) =
        shiftCoordinates (shiftCoordinates w Δ) (pushforwardField j ξ) := (hmv F w Δ _).symm
    rw [e1]
    show shiftCoordinates w Δ _ i + stepCoordinates (pushforwardField j ξ) _ i =
      w' _ i + stepCoordinates (pushforwardField j' ξ) _ i
    rw [h1, hco]
  have hE' := hE L t n₀ σ δ ε ε₃ f hodd hε hfam F F' (shiftCoordinates w (Δ + pushforwardField j ξ))
    (shiftCoordinates w' (pushforwardField j' ξ)) V V'
    Y Y' r₂ s (q / 2) h o hTF hTF' hs₂ hs₂' (g1 ξ hξ2).1 (hgood' ξ hξ2).1 (g1 ξ hξ2).2 (hgood' ξ hξ2).2 hag heq₂ hin
    (by omega) ho
  obtain ⟨hval, hgr2⟩ := hE'
  have hRe : R₂ ξ = subtractTrivial f F y (chartedField (shiftCoordinates w (Δ + pushforwardField j ξ)) V) := rfl
  have hCε0 : 0 ≤ (C₁ + C₂) * ε := mul_nonneg (add_pos hC₁ hC₂).le hε
  have hNθ : 0 ≤ (C₁ + C₂) * ε * θ * (ballChordBonds F Y r₂).card := mul_nonneg (mul_nonneg hCε0 hθ) hN
  refine ⟨?_, fun k u hu => ?_⟩
  · have h1 := hmove ξ hξ2
    have htri := abs_sub_le
      (subtractTrivial f F' y' (chartedField (shiftCoordinates w' (pushforwardField j' ξ)) V')) (R₂ ξ)
      (Γ (pushforwardField j ξ))
    rw [hRe] at htri h1
    exact htri.trans (add_le_add hval h1)
  · have hDpos : 0 ≤ ε / torusDecayFactor L δ ((L : ℝ) * ((r₂ : ℝ) - s - 2)) := (abs_nonneg _).trans hval
    have hpart : bondPartialDeriv (fun ξ => Γ' (pushforwardField j' ξ)) k ξ u =
        fderiv ℝ (readInChart (subtractTrivial f F' y') (shiftCoordinates w' (pushforwardField j' ξ)) V') 0
          (bondVariation (j' k) u) := by
      have h1 := (hemb' 3 Γ' ξ (cΓ' _ (hgood' ξ hξ2).1 (hgood' ξ hξ2).2)).2.1 (by norm_num) (bondVariation k u)
      unfold bondPartialDeriv
      rw [h1, ea', fΓ' (pushforwardField j' ξ), add_zero]
    have hpart0 : bondPartialDeriv (fun ξ => Γ (pushforwardField j ξ)) k ξ u =
        fderiv ℝ (readInChart (subtractTrivial f F y) (shiftCoordinates w (pushforwardField j ξ)) V) 0
          (bondVariation (j k) u) := by
      have h1 := (hemb 3 Γ ξ (cΓ _ (g0 ξ hξ2).1 (g0 ξ hξ2).2)).2.1 (by norm_num) (bondVariation k u)
      unfold bondPartialDeriv
      rw [h1, ea, fΓ (pushforwardField j ξ), add_zero]
    have hpart2 : bondPartialDeriv R₂ k ξ u =
        fderiv ℝ (readInChart (subtractTrivial f F y) (shiftCoordinates w (Δ + pushforwardField j ξ)) V) 0
          (bondVariation (j k) u) := by
      have h1 := (hemb 3 Γ₂ ξ (cΓ₂ ξ hξ2)).2.1 (by norm_num) (bondVariation k u)
      have h1' : fderiv ℝ R₂ ξ (bondVariation k u) =
          fderiv ℝ Γ₂ (pushforwardField j ξ) (pushforwardField j (bondVariation k u)) := h1
      unfold bondPartialDeriv
      rw [h1', ea, fderiv_eq_of_comp_add_left (A := Γ₂) (G := Γ) (η := Δ) (fun _ => rfl),
        fΓ (Δ + pushforwardField j ξ), add_zero]
    show |bondPartialDeriv (fun ξ => Γ' (pushforwardField j' ξ)) k ξ u -
      bondPartialDeriv (fun ξ => Γ (pushforwardField j ξ)) k ξ u| ≤ _
    have hexp0 := Real.exp_pos (-(δ * L * (((q / 2 : ℕ) : ℝ) - s)))
    have hCε : 0 ≤ (C₁ + C₂) * ε := by positivity
    obtain ⟨g, u₁, k₁, hu₁, hg, e1, e2⟩ := hp k
    by_cases hnear : WithinRadius (q / 2) g
    · have hnr := hgr2 g u₁ k₁ (j k) (j' k) u hnear (by rw [← hFL]; exact hu₁) (by omega) e1 e2
      rw [hu, mul_one] at hnr
      have hg1 := hgrad ξ hξ k u hu
      have htri := abs_sub_le (bondPartialDeriv (fun ξ => Γ' (pushforwardField j' ξ)) k ξ u)
        (bondPartialDeriv R₂ k ξ u) (bondPartialDeriv (fun ξ => Γ (pushforwardField j ξ)) k ξ u)
      rw [hpart, hpart2] at htri
      rw [hpart]
      have hnr' : |fderiv ℝ (readInChart (subtractTrivial f F' y') (shiftCoordinates w' (pushforwardField j' ξ)) V') 0
            (bondVariation (j' k) u) -
          fderiv ℝ (readInChart (subtractTrivial f F y) (shiftCoordinates w (Δ + pushforwardField j ξ)) V) 0
            (bondVariation (j k) u)| ≤
          (C₁ + C₂) * ε / torusDecayFactor L δ ((L : ℝ) * ((r₂ : ℝ) - s - 2)) := by
        refine hnr.trans ?_
        have e3 : C₂ * ε / torusDecayFactor L δ ((L : ℝ) * ((r₂ : ℝ) - s - 2)) =
            C₂ * (ε / torusDecayFactor L δ ((L : ℝ) * ((r₂ : ℝ) - s - 2))) := by ring
        have e4 : (C₁ + C₂) * ε / torusDecayFactor L δ ((L : ℝ) * ((r₂ : ℝ) - s - 2)) =
            (C₁ + C₂) * (ε / torusDecayFactor L δ ((L : ℝ) * ((r₂ : ℝ) - s - 2))) := by ring
        rw [e3, e4]
        exact mul_le_mul_of_nonneg_right (by linarith) hDpos
      have hg1' : |fderiv ℝ (readInChart (subtractTrivial f F y) (shiftCoordinates w (Δ + pushforwardField j ξ)) V) 0
            (bondVariation (j k) u) -
          bondPartialDeriv (fun ξ => Γ (pushforwardField j ξ)) k ξ u| ≤
          2 * ((C₁ + C₂) * ε * θ * (ballChordBonds F Y r₂).card) / hh + 2 * ((C₁ + C₂) * ε) * hh := by
        rw [← hpart2]
        exact hg1
      have h20 := mul_nonneg hCε hexp0.le
      have e6 : 0 ≤ 2 * ((C₁ + C₂) * ε) * Real.exp (-(δ * L * (((q / 2 : ℕ) : ℝ) - s))) := by
        linarith only [h20]
      exact htri.trans (by linarith only [hnr', hg1', e6])
    · have hsq : s ≤ q := by omega
      have far1 := le_siteSupDist_of_not_withinRadius hO (i := k₁) (Y := Y) hoddF hs hin hsq hg hnear
        (by rw [hFL]; exact ho) hu₁
      have far2 := le_siteSupDist_of_not_withinRadius hO (i := k₁) (Y := Y') hoddF' hs' hin hsq hg
        (fun hh' => hnear hh') (by rw [hFL']; exact ho) (by rw [← hLL]; exact hu₁)
      rw [hFL] at far1
      rw [hFL'] at far2
      have bound1 : |fderiv ℝ (readInChart (subtractTrivial f F y) (shiftCoordinates w (pushforwardField j ξ)) V) 0
            (bondVariation (j k) u)| ≤
          C₁ * ε * Real.exp (-(δ * L * (((q / 2 : ℕ) : ℝ) - s))) := by
        have h1 := (A _ (g0 ξ hξ2).1 (g0 ξ hξ2).2).2.1 (j k) u
        rw [hu, mul_one] at h1
        refine h1.trans ?_
        have hx : (L : ℝ) * (((q / 2 : ℕ) : ℝ) - s) ≤ siteSupDist y (j k).1.1 := by
          rw [e1]
          exact far1
        have h2 := one_div_torusDecayFactor_le_exp L δ (siteSupDist y (j k).1.1)
        have h3 : Real.exp (-(δ * (siteSupDist y (j k).1.1 : ℝ))) ≤
            Real.exp (-(δ * L * (((q / 2 : ℕ) : ℝ) - s))) :=
          Real.exp_le_exp.2 (neg_le_neg (by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left hx hδ))
        have e5 : C₁ * ε / torusDecayFactor L δ (siteSupDist y (j k).1.1) =
            C₁ * ε * (1 / torusDecayFactor L δ (siteSupDist y (j k).1.1)) := by ring
        rw [e5]
        exact mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
      have bound2 : |fderiv ℝ (readInChart (subtractTrivial f F' y') (shiftCoordinates w' (pushforwardField j' ξ)) V') 0
            (bondVariation (j' k) u)| ≤
          C₁ * ε * Real.exp (-(δ * L * (((q / 2 : ℕ) : ℝ) - s))) := by
        have h1 := (A' _ (hgood' ξ hξ2).1 (hgood' ξ hξ2).2).2.1 (j' k) u
        rw [hu, mul_one] at h1
        refine h1.trans ?_
        have hx : (L : ℝ) * (((q / 2 : ℕ) : ℝ) - s) ≤ siteSupDist y' (j' k).1.1 := by
          rw [e2]
          exact far2
        have h2 := one_div_torusDecayFactor_le_exp L δ (siteSupDist y' (j' k).1.1)
        have h3 : Real.exp (-(δ * (siteSupDist y' (j' k).1.1 : ℝ))) ≤
            Real.exp (-(δ * L * (((q / 2 : ℕ) : ℝ) - s))) :=
          Real.exp_le_exp.2 (neg_le_neg (by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left hx hδ))
        have e5 : C₁ * ε / torusDecayFactor L δ (siteSupDist y' (j' k).1.1) =
            C₁ * ε * (1 / torusDecayFactor L δ (siteSupDist y' (j' k).1.1)) := by ring
        rw [e5]
        exact mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
      rw [hpart, hpart0]
      have htri := abs_sub_le_two_mul bound2 bound1
      have h10 : 0 ≤ (C₁ + C₂) * ε / torusDecayFactor L δ ((L : ℝ) * ((r₂ : ℝ) - s - 2)) := by
        have e4 : (C₁ + C₂) * ε / torusDecayFactor L δ ((L : ℝ) * ((r₂ : ℝ) - s - 2)) =
            (C₁ + C₂) * (ε / torusDecayFactor L δ ((L : ℝ) * ((r₂ : ℝ) - s - 2))) := by ring
        rw [e4]
        exact mul_nonneg (by positivity) hDpos
      have h11 : 0 ≤ 2 * ((C₁ + C₂) * ε * θ * (ballChordBonds F Y r₂).card) / hh :=
        div_nonneg (mul_nonneg (by norm_num) hNθ) hh0.le
      have h12 : 0 ≤ 2 * ((C₁ + C₂) * ε) * hh := mul_nonneg (mul_nonneg (by norm_num) hCε0) hh0.le
      have h13 : C₁ * ε * Real.exp (-(δ * L * (((q / 2 : ℕ) : ℝ) - s))) ≤
          (C₁ + C₂) * ε * Real.exp (-(δ * L * (((q / 2 : ℕ) : ℝ) - s))) := by
        have h14 : 0 ≤ ε * Real.exp (-(δ * L * (((q / 2 : ℕ) : ℝ) - s))) := mul_nonneg hε hexp0.le
        have h15 := mul_nonneg hC₂.le h14
        linarith only [h15]
      exact htri.trans (by linarith only [h10, h11, h12, h13])
end YangMills.Construction.ColdStepAtMirrorFrames
end
