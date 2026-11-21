import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHom
import YangMills.Construction.PeriodicOperators.StripsAndFiniteNormsOfJetsProof
import YangMills.Construction.Towers.PropertiesOfTheBackgrounds
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheScaledPictureAndTheirJets
import YangMills.Construction.Towers.TheBackgroundsAndTheBasicJets
import Mathlib
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.OperatorJetBounds
open PeriodicOperators
def JetsBoundedAtLevel : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ μPlus μMinus : Fin 4,
    ∃ C : ℝ, ∀ q ∈ momentumPolydisc stripHalfWidth,
      JetQuad.jetNorm stripHalfWidth q (covDerivJet L k q μPlus μMinus) ≤ ENNReal.ofReal C ∧
        JetQuad.jetNorm stripHalfWidth q (edgeOperatorJet L k q μPlus μMinus) ≤ ENNReal.ofReal C ∧
        JetQuad.jetNorm stripHalfWidth q (vertexOperatorJet L k q μPlus μMinus) ≤ ENNReal.ofReal C
end YangMills.Construction.Tower.FullSpace.BackgroundJets.OperatorJetBounds
end

open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.JetBoundsAtLevel
open YangMills.Construction.Coordinates
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetDomains (fstMomentum sndMomentum)
open YangMills.Construction.Tower.FullSpace.BackgroundProperties
section PhaseConjugation
variable {I I' : PeriodicData}
theorem quotHomNorm_le_one_of_wNorm_eq {A : QuotHom I I}
    (hA : ∀ f, wNorm (I.quotWeight 1) (A f) = wNorm (I.quotWeight 1) f) :
    quotHomNorm A ≤ 1 := by
  refine iSup₂_le fun f hf => ?_
  rw [hA f, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hf.2.2
theorem quotHomNorm_conj_phaseMul_le (hNorm : HomNorm.Claim)
    (hSym : SymbolCalculus.Claim) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (A : QuotHom I I') (n : Fin 4 → ℤ) :
    quotHomNorm ((quotHomInverse (phaseMul I' n)).comp
      (A.comp (phaseMul I n))) ≤ quotHomNorm A := by
  have hIso : ∀ {J : PeriodicData}, IsPeriodic J →
      ∀ f, wNorm (J.quotWeight 1) (phaseMul J n f) =
        wNorm (J.quotWeight 1) f := fun {J} hJ =>
    (hSym J J hJ hJ).2.2.2.1 n |>.2.2.2
  have hInv : IsInvertibleQuotHom (phaseMul I' n : QuotHom I' I') :=
    ((hSym I' I' hI' hI').2.2.2.2.2.2.1 1 one_pos).1 n
  have hPhase : quotHomNorm (phaseMul I n : QuotHom I I) ≤ 1 :=
    quotHomNorm_le_one_of_wNorm_eq (hIso hI)
  have hPhaseInv : quotHomNorm (quotHomInverse (phaseMul I' n) : QuotHom I' I') ≤ 1 := by
    refine quotHomNorm_le_one_of_wNorm_eq fun f => ?_
    rw [← hIso hI' (quotHomInverse (phaseMul I' n) f), hInv.apply_quotHomInverse]
  have hComp₁ := ((hNorm I I' hI hI').2.2.2.2.2.2.1 I hI).2 A (phaseMul I n)
  have hComp₂ := ((hNorm I' I' hI' hI').2.2.2.2.2.2.1 I hI).2
    (quotHomInverse (phaseMul I' n)) (A.comp (phaseMul I n))
  calc quotHomNorm ((quotHomInverse (phaseMul I' n)).comp
        (A.comp (phaseMul I n)))
      ≤ quotHomNorm (quotHomInverse (phaseMul I' n) : QuotHom I' I') *
          quotHomNorm (A.comp (phaseMul I n)) := hComp₂
    _ ≤ 1 * (quotHomNorm A * 1) :=
        mul_le_mul' hPhaseInv (hComp₁.trans (mul_le_mul' le_rfl hPhase))
    _ = quotHomNorm A := by simp
end PhaseConjugation
section Regions
theorem im_add_two_pi_mul_int (z : ℂ) (m : ℤ) : (z + 2 * Real.pi * (m : ℂ)).im = z.im := by apply _root_.YangMills.Construction.PeriodicOperators.ZeroFieldInvertibility.im_add_two_pi_mul_int <;> assumption
theorem exists_addTwoPiInt_abs_re_le_pi (κ : Fin 4 → ℂ) :
    ∃ n : Fin 4 → ℤ, ∀ μ, |(addTwoPiInt κ n μ).re| ≤ Real.pi := by apply _root_.YangMills.Construction.PeriodicOperators.ZeroFieldInvertibility.exists_abs_re_addTwoPiInt_le <;> assumption
def boxPolydisc (b δ : ℝ) : Set (ComplexCoordinates (4 + 4)) :=
  (⋂ μ, {z | |(fstMomentum z μ).re| ≤ Real.pi}) ∩ (⋂ μ, {z | |(fstMomentum z μ).im| ≤ b}) ∩
    ⋂ μ, {z | ‖sndMomentum z μ‖ ≤ δ}
theorem isCompact_boxPolydisc (b δ : ℝ) : IsCompact (boxPolydisc b δ) := by
  have hfst : ∀ μ : Fin 4, Continuous fun z : ComplexCoordinates (4 + 4) => fstMomentum z μ :=
    fun μ => continuous_apply _
  have hsnd : ∀ μ : Fin 4, Continuous fun z : ComplexCoordinates (4 + 4) => sndMomentum z μ :=
    fun μ => continuous_apply _
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine ((isClosed_iInter fun μ => isClosed_le ?_ continuous_const).inter
      (isClosed_iInter fun μ => isClosed_le ?_ continuous_const)).inter
      (isClosed_iInter fun μ => isClosed_le ?_ continuous_const)
    · exact continuous_abs.comp (Complex.continuous_re.comp (hfst μ))
    · exact continuous_abs.comp (Complex.continuous_im.comp (hfst μ))
    · exact (hsnd μ).norm
  · refine (Metric.isBounded_closedBall (x := (0 : ComplexCoordinates (4 + 4)))
      (r := Real.pi + |b| + |δ|)).subset ?_
    rintro z ⟨⟨hre, him⟩, hrad⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    refine Fin.addCases (fun μ => ?_) (fun μ => ?_) i
    · have hreμ := mem_iInter.1 hre μ
      have himμ := mem_iInter.1 him μ
      have hreμ' : |(fstMomentum z μ).re| ≤ Real.pi := hreμ
      have himμ' : |(fstMomentum z μ).im| ≤ b := himμ
      calc ‖z (Fin.castAdd 4 μ)‖ = ‖fstMomentum z μ‖ := rfl
        _ ≤ |(fstMomentum z μ).re| + |(fstMomentum z μ).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ Real.pi + |b| + |δ| := by
            have := le_abs_self b
            have := abs_nonneg δ
            linarith
    · have hradμ : ‖sndMomentum z μ‖ ≤ δ := mem_iInter.1 hrad μ
      calc ‖z (Fin.natAdd 4 μ)‖ = ‖sndMomentum z μ‖ := rfl
        _ ≤ Real.pi + |b| + |δ| := by
            have := le_abs_self δ
            have := abs_nonneg b
            have := Real.pi_pos
            linarith
theorem jetWidth_eq_of_mem {p : Fin 4 → ℂ} (hp : p ∈ momentumPolydisc stripHalfWidth) :
    jetWidth p = stripHalfWidth := by
  have h : ∀ μ, |(p μ).im| ≤ stripHalfWidth := fun μ => (Complex.abs_im_le_norm _).trans (hp μ)
  exact max_eq_left (max_le (h 0) (max_le (h 1) (max_le (h 2) (h 3))))
theorem addTwoPiInt_mem_imStrip {r : ℝ} {κ : Fin 4 → ℂ} (h : κ ∈ imStrip r) (n : Fin 4 → ℤ) :
    addTwoPiInt κ n ∈ imStrip r := by apply _root_.YangMills.SharedProofs.p29809 <;> assumption
theorem addTwoPiInt_add_mem_imStrip {r : ℝ} {κ q : Fin 4 → ℂ} (h : κ + q ∈ imStrip r)
    (n : Fin 4 → ℤ) : addTwoPiInt κ n + q ∈ imStrip r := by apply _root_.YangMills.Construction.PeriodicOperators.StripJetNorms.addTwoPiInt_add_mem_imStrip <;> assumption
end Regions
section ComponentBounds
variable {I I' : PeriodicData}
theorem exists_bound_quotHomNorm_of_quasiPeriodic (hNorm : HomNorm.Claim)
    (hSym : SymbolCalculus.Claim) (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {O : Set (Fin 4 → ℂ)} {δ b : ℝ} (hPO : momentumPolydisc δ ⊆ O)
    (A : (Fin 4 → ℂ) → (Fin 4 → ℂ) → QuotHom I I')
    (hA : ∀ (c' : I'.UnitQuot) (c : I.UnitQuot),
      ComplexCoordinates.IsHolomorphicIn (N := 4 + 4) (N' := 1) (productOver O) fun z _ =>
        linearMapEntry (A (sndMomentum z) (fstMomentum z)) c' c)
    (D : (Fin 4 → ℂ) → Set (Fin 4 → ℂ))
    (hb : ∀ p ∈ momentumPolydisc δ, ∀ κ ∈ D p, ∀ μ, |(κ μ).im| ≤ b)
    (hT : ∀ p ∈ momentumPolydisc δ, ∀ κ ∈ D p, ∀ n, addTwoPiInt κ n ∈ D p)
    (hQ : ∀ p ∈ momentumPolydisc δ, IsQuasiPeriodic (D p) (A p)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ momentumPolydisc δ,
      (⨆ κ ∈ D p, quotHomNorm (A p κ)) ≤ ENNReal.ofReal C := by
  have hsub : boxPolydisc b δ ⊆ productOver O := fun z hz =>
    hPO fun μ => mem_iInter.1 hz.2 μ
  have hbdd : QuotHomFamilyBoundedOn (boxPolydisc b δ)
      fun z => A (sndMomentum z) (fstMomentum z) := by
    rintro ⟨c', c⟩
    have hcont := (hA c' c).2.1.mono hsub
    have hentry : ContinuousOn (fun z : ComplexCoordinates (4 + 4) =>
        linearMapEntry (A (sndMomentum z) (fstMomentum z)) c' c) (boxPolydisc b δ) :=
      (continuous_apply (0 : Fin 1)).comp_continuousOn hcont
    exact (isCompact_boxPolydisc b δ).exists_bound_of_continuousOn hentry
  obtain ⟨C, hC⟩ := ((hNorm I I' hI hI').2.2.2.2.1 _ (boxPolydisc b δ)
    fun z => A (sndMomentum z) (fstMomentum z)).2 hbdd
  have hfin : ∀ B : QuotHom I I', quotHomNorm B < ∞ := fun B =>
    ((hNorm I I' hI hI').1 B).2
  refine ⟨|C|, abs_nonneg C, fun p hp => iSup₂_le fun κ hκ => ?_⟩
  obtain ⟨n, hn⟩ := exists_addTwoPiInt_abs_re_le_pi κ
  have hκn := hT p hp κ hκ n
  have hback : addTwoPiInt (addTwoPiInt κ n) (-n) = κ := by
    ext μ
    simp [addTwoPiInt]
  have hqp := hQ p hp (-n) _ hκn
  rw [hback] at hqp
  rw [hqp]
  refine (quotHomNorm_conj_phaseMul_le hNorm hSym hI hI' _ _).trans ?_
  have hmem : appendCoords (addTwoPiInt κ n) p ∈ boxPolydisc b δ := by
    have hfst : fstMomentum (appendCoords (addTwoPiInt κ n) p) = addTwoPiInt κ n :=
      funext fun μ => Fin.append_left _ _ μ
    have hsnd : sndMomentum (appendCoords (addTwoPiInt κ n) p) = p :=
      funext fun μ => Fin.append_right _ _ μ
    refine ⟨⟨mem_iInter.2 fun μ => ?_, mem_iInter.2 fun μ => ?_⟩, mem_iInter.2 fun μ => ?_⟩
    · show |(fstMomentum _ μ).re| ≤ _
      rw [hfst]
      exact hn μ
    · show |(fstMomentum _ μ).im| ≤ _
      rw [hfst]
      exact hb p hp _ hκn μ
    · show ‖sndMomentum _ μ‖ ≤ _
      rw [hsnd]
      exact hp μ
  have hle := hC _ hmem
  have hfst : fstMomentum (appendCoords (addTwoPiInt κ n) p) = addTwoPiInt κ n :=
    funext fun μ => Fin.append_left _ _ μ
  have hsnd : sndMomentum (appendCoords (addTwoPiInt κ n) p) = p :=
    funext fun μ => Fin.append_right _ _ μ
  simp only [hfst, hsnd] at hle
  rw [ENNReal.le_ofReal_iff_toReal_le (hfin _).ne (abs_nonneg C)]
  exact (le_abs_self _).trans (hle.trans (le_abs_self C))
theorem exists_bound_jetNorm (hNorm : HomNorm.Claim) (hSym : SymbolCalculus.Claim)
    {L k : ℕ} {μPlus μMinus : Fin 4} (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {O : Set (Fin 4 → ℂ)} (hPO : momentumPolydisc stripHalfWidth ⊆ O)
    (hO : ∀ p ∈ O, ResponseSymbolSummableAt L k p)
    {T : ((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
    (hF : JetWellDefined L k μPlus μMinus I I' T)
    (hHol : ComponentsHolomorphicOn L k μPlus μMinus O I I' T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ momentumPolydisc stripHalfWidth,
      JetQuad.jetNorm stripHalfWidth p (jetAlongResponse L k T p μPlus μMinus) ≤
        ENNReal.ofReal C := by
  have hjet : ∀ p ∈ momentumPolydisc stripHalfWidth,
      JetQuad.IsJet stripHalfWidth p (axisJet L k T p μPlus μMinus) := fun p hp => by
    have h := hF.isJet p (hO p (hPO hp))
    rwa [jetWidth_eq_of_mem hp] at h
  obtain ⟨C₀, h₀, b₀⟩ := exists_bound_quotHomNorm_of_quasiPeriodic hNorm hSym hI hI'
    (b := 2 * stripHalfWidth) hPO
    (fun p => (axisJet L k T p μPlus μMinus).f00) hHol.holo_f00
    (fun _ => imStrip (2 * stripHalfWidth))
    (fun _ _ κ hκ => hκ) (fun _ _ κ hκ n => addTwoPiInt_mem_imStrip hκ n)
    (fun p hp => (hjet p hp).quasiPeriodic_f00)
  obtain ⟨C₁, h₁, b₁⟩ := exists_bound_quotHomNorm_of_quasiPeriodic hNorm hSym hI hI'
    (b := 2 * stripHalfWidth) hPO
    (fun p => (axisJet L k T p μPlus μMinus).f10) hHol.holo_f10
    (fun p => stripAddShift stripHalfWidth p) (fun _ _ κ hκ => hκ.1)
    (fun _ _ κ hκ n => ⟨addTwoPiInt_mem_imStrip hκ.1 n, addTwoPiInt_add_mem_imStrip hκ.2 n⟩)
    (fun p hp => (hjet p hp).quasiPeriodic_f10)
  obtain ⟨C₂, h₂, b₂⟩ := exists_bound_quotHomNorm_of_quasiPeriodic hNorm hSym hI hI'
    (b := 2 * stripHalfWidth) hPO
    (fun p => (axisJet L k T p μPlus μMinus).f01) hHol.holo_f01
    (fun p => stripSubShift stripHalfWidth p) (fun _ _ κ hκ => hκ.1)
    (fun p _ κ hκ n => ⟨addTwoPiInt_mem_imStrip hκ.1 n, by
      have h := addTwoPiInt_add_mem_imStrip (q := -p) (κ := κ)
        (by simpa [sub_eq_add_neg] using hκ.2) n
      simpa [sub_eq_add_neg] using h⟩)
    (fun p hp => (hjet p hp).quasiPeriodic_f01)
  obtain ⟨C₃, h₃, b₃⟩ := exists_bound_quotHomNorm_of_quasiPeriodic hNorm hSym hI hI'
    (b := 0) hPO
    (fun p => (axisJet L k T p μPlus μMinus).f11) hHol.holo_f11 (fun _ => realDualPoints)
    (fun _ _ κ hκ μ => by rw [hκ μ, abs_zero])
    (fun _ _ κ hκ n μ => by
      show (κ μ + 2 * Real.pi * (n μ : ℂ)).im = 0
      rw [im_add_two_pi_mul_int]
      exact hκ μ)
    (fun p hp => (hjet p hp).quasiPeriodic_f11)
  refine ⟨C₀ + C₁ + C₂ + C₃, by positivity, fun p hp => ?_⟩
  rw [← axisJet_of_mem T hp μPlus μMinus, ENNReal.ofReal_add (by positivity) h₃,
    ENNReal.ofReal_add (by positivity) h₂, ENNReal.ofReal_add h₀ h₁]
  exact add_le_add (add_le_add (add_le_add (b₀ p hp) (b₁ p hp)) (b₂ p hp)) (b₃ p hp)
end ComponentBounds
theorem jetsBoundedAtLevel_holds (hBg : BackgroundPropertiesHold)
    (hOp : ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hNorm : HomNorm.Claim) (hSym : SymbolCalculus.Claim) :
    OperatorJetBounds.JetsBoundedAtLevel := by
  intro L hL k hk μPlus μMinus
  obtain ⟨O, -, hPO, hOn⟩ := (hBg L hL k hk).exists_nhds μPlus μMinus
  obtain ⟨hSi, hBo, -⟩ := (hOp.1 L hL k hk).1.periodic
  obtain ⟨fD, -, -, -, fK, fΔ, -, -⟩ := (hBg L hL k hk).jets_wellDefined μPlus μMinus
  obtain ⟨cD, -, -, -, cK, cΔ, -, -⟩ := hOn.components
  obtain ⟨C₁, -, b₁⟩ := exists_bound_jetNorm hNorm hSym hSi hBo hPO hOn.response_summable fD cD
  obtain ⟨C₂, -, b₂⟩ := exists_bound_jetNorm hNorm hSym hBo hBo hPO hOn.response_summable fK cK
  obtain ⟨C₃, -, b₃⟩ := exists_bound_jetNorm hNorm hSym hSi hSi hPO hOn.response_summable fΔ cΔ
  have m₁ : ENNReal.ofReal C₁ ≤ ENNReal.ofReal (max C₁ (max C₂ C₃)) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have m₂ : ENNReal.ofReal C₂ ≤ ENNReal.ofReal (max C₁ (max C₂ C₃)) :=
    ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_right _ _))
  have m₃ : ENNReal.ofReal C₃ ≤ ENNReal.ofReal (max C₁ (max C₂ C₃)) :=
    ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_right _ _))
  exact ⟨max C₁ (max C₂ C₃), fun p hp =>
    ⟨(b₁ p hp).trans m₁, (b₂ p hp).trans m₂, (b₃ p hp).trans m₃⟩⟩
end YangMills.Construction.Tower.FullSpace.BackgroundJets.JetBoundsAtLevel
end
