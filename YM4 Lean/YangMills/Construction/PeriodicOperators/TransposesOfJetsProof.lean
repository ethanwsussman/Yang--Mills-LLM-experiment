import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJetsProof
import YangMills.Construction.PeriodicOperators.IntegrandOfTheLogarithmicNumberOfAFunctionProof
import YangMills.Construction.PeriodicOperators.TransposesOfJets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetTranspose
open JetDomains
open JetQuad (IsJet)
section Entries
variable {J J' : Type}
theorem linearMapEntry_linearMapOfEntries [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
theorem linearMap_eq_of_linearMapEntry_eq [Finite J] {M M' : (J → ℂ) →ₗ[ℂ] (J' → ℂ)}
    (h : linearMapEntry M = linearMapEntry M') : M = M' := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMap_ext_of_entry <;> assumption
end Entries
section Phases
variable {I I' : PeriodicData}
theorem quotHomInverse_phaseMul (hI : IsPeriodic I) (e : Fin 4 → ℤ) :
    quotHomInverse (phaseMul I e) = phaseMul I (-e) := by apply _root_.YangMills.Construction.PeriodicOperators.LogDensityBounds.quotHomInverse_phaseMul <;> assumption
theorem linearMapEntry_phaseMul_comp (e e' : Fin 4 → ℤ) (M : QuotHom I I') (c' : I'.UnitQuot)
    (c : I.UnitQuot) :
    linearMapEntry ((phaseMul I' e').comp (M.comp (phaseMul I e))) c' c =
      phaseOn I' e' c' * linearMapEntry M c' c * phaseOn I e c := by
  classical
  have hs : phaseMul I e (Pi.single c 1) = phaseOn I e c • Pi.single c 1 := by
    funext d
    change phaseOn I e d * (Pi.single c 1 : I.UnitQuot → ℂ) d = _
    by_cases hd : d = c
    · subst hd
      simp
    · simp [Pi.single_eq_of_ne hd]
  unfold linearMapEntry
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hs, map_smul]
  change phaseOn I' e' c' * (phaseOn I e c • M (Pi.single c 1)) c' = _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
theorem linearMapEntry_quotHomTranspose_eq [Finite I'.UnitQuot] (M : QuotHom I I')
    (c : I.UnitQuot) (c' : I'.UnitQuot) :
    linearMapEntry (quotHomTranspose M) c c' =
      ((I'.quotWeight 1 c' / I.quotWeight 1 c : ℝ) : ℂ) * linearMapEntry M c' c :=
  congrFun (congrFun (linearMapEntry_linearMapOfEntries _) c) c'
theorem isQuasiPeriodic_quotHomTranspose (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {D D' : Set (Fin 4 → ℂ)} {A : (Fin 4 → ℂ) → QuotHom I I'} (hA : IsQuasiPeriodic D A)
    (L : (Fin 4 → ℂ) → Fin 4 → ℂ) (hL : ∀ κ ∈ D', L κ ∈ D)
    (hT : ∀ κ e, L (addTwoPiInt κ e) = addTwoPiInt (L κ) (-e)) :
    IsQuasiPeriodic D' fun κ => quotHomTranspose (A (L κ)) := by
  intro e κ hκ
  have := hI.finite_quot
  have := hI'.finite_quot
  have h1 := hA (-e) (L κ) (hL κ hκ)
  rw [quotHomInverse_phaseMul hI' (-e), neg_neg] at h1
  change quotHomTranspose (A (L (addTwoPiInt κ e))) =
    (quotHomInverse (phaseMul I e)).comp
      ((quotHomTranspose (A (L κ))).comp (phaseMul I' e))
  rw [hT, h1, quotHomInverse_phaseMul hI e]
  apply linearMap_eq_of_linearMapEntry_eq
  funext c c'
  rw [linearMapEntry_quotHomTranspose_eq, linearMapEntry_phaseMul_comp,
    linearMapEntry_phaseMul_comp, linearMapEntry_quotHomTranspose_eq]
  ring
end Phases
section Holomorphy
variable {I I' : PeriodicData}
theorem entriesHolomorphicOn_quotHomTranspose [Finite I'.UnitQuot] {O : Set (Fin 4 → ℂ)}
    {A : (Fin 4 → ℂ) → QuotHom I I'} (hA : EntriesHolomorphicOn O A)
    (L : (Fin 4 → ℂ) → Fin 4 → ℂ) (b : Fin 4 → ℂ) (hL : ∀ κ, L κ = -κ + b) :
    EntriesHolomorphicOn (L ⁻¹' O) fun κ => quotHomTranspose (A (L κ)) := by
  have hLc : Continuous L := by
    have : L = fun κ => -κ + b := funext hL
    rw [this]
    fun_prop
  intro c d
  obtain ⟨ho, hc, hd⟩ := hA d c
  set a : ℂ := ((I'.quotWeight 1 d / I.quotWeight 1 c : ℝ) : ℂ) with ha
  set F : Coordinates.ComplexCoordinates 4 → Coordinates.ComplexCoordinates 1 :=
    fun κ _ => linearMapEntry (A κ) d c with hF
  have hfun : (fun (κ : Coordinates.ComplexCoordinates 4) (_ : Fin 1) =>
      linearMapEntry (quotHomTranspose (A (L κ))) c d) = fun κ => a • F (L κ) := by
    funext κ i
    rw [linearMapEntry_quotHomTranspose_eq]
    rfl
  rw [hfun]
  refine ⟨ho.preimage hLc, ?_, ?_⟩
  · exact (hc.comp hLc.continuousOn (fun κ hκ => hκ)).const_smul a
  · intro x hx j
    have h0 := hd (L x) hx j
    have hneg : Filter.Tendsto (fun ζ : ℂ => -ζ) (nhds 0) (nhds 0) := by
      have := (continuous_neg (G := ℂ)).tendsto 0
      simpa using this
    filter_upwards [hneg.eventually h0] with ζ hζ
    have hcomp : (fun ζ : ℂ =>
        a • F (L (x + ζ • Coordinates.ComplexCoordinates.stdBasisVector j))) =
        fun ζ : ℂ => a • (fun ξ : ℂ =>
          F (L x + ξ • Coordinates.ComplexCoordinates.stdBasisVector j)) (-ζ) := by
      funext ξ
      simp only [hL]
      congr 2
      simp only [neg_add, neg_smul]
      abel
    rw [hcomp]
    have hd1 : DifferentiableAt ℂ (fun ζ : ℂ => -ζ) ζ := differentiable_neg.differentiableAt
    exact (DifferentiableAt.comp ζ hζ hd1).const_smul a
theorem isHolomorphicNbhd_quotHomTranspose [Finite I'.UnitQuot] {D D' : Set (Fin 4 → ℂ)}
    {A : (Fin 4 → ℂ) → QuotHom I I'} (hA : IsHolomorphicNbhd D A)
    (L : (Fin 4 → ℂ) → Fin 4 → ℂ) (b : Fin 4 → ℂ) (hL : ∀ κ, L κ = -κ + b)
    (hD : ∀ κ ∈ D', L κ ∈ D) :
    IsHolomorphicNbhd D' fun κ => quotHomTranspose (A (L κ)) := by
  obtain ⟨O, ho, hs, hh⟩ := hA
  have hLc : Continuous L := by
    have : L = fun κ => -κ + b := funext hL
    rw [this]
    fun_prop
  exact ⟨L ⁻¹' O, ho.preimage hLc, fun κ hκ => hs (hD κ hκ),
    entriesHolomorphicOn_quotHomTranspose (I := I) (I' := I') (fun c' c => hh c' c) L b hL⟩
end Holomorphy
section Sets
theorem neg_mem_imStrip {r : ℝ} {κ : Fin 4 → ℂ} (h : κ ∈ imStrip r) : -κ ∈ imStrip r := by
  intro μ
  simpa using h μ
theorem neg_sub_mem_stripAddShift {δ : ℝ} {p κ : Fin 4 → ℂ} (h : κ ∈ stripAddShift δ p) :
    -κ - p ∈ stripAddShift δ p := by apply _root_.YangMills.Construction.PeriodicOperators.JetArgumentLemmas.neg_sub_mem_stripAddShift <;> assumption
theorem neg_add_mem_stripSubShift {δ : ℝ} {p κ : Fin 4 → ℂ} (h : κ ∈ stripSubShift δ p) :
    -κ + p ∈ stripSubShift δ p := by apply _root_.YangMills.Construction.PeriodicOperators.JetArgumentLemmas.neg_add_mem_stripSubShift <;> assumption
theorem neg_mem_realDualPoints {κ : Fin 4 → ℂ} (h : κ ∈ realDualPoints) :
    -κ ∈ realDualPoints := by
  intro j
  simpa using h j
def negDomains (p : Fin 4 → ℂ) (O : Domains) : Domains where
  dom00 := (fun κ => -κ) ⁻¹' O.dom00
  dom10 := (fun κ => -κ - p) ⁻¹' O.dom10
  dom01 := (fun κ => -κ + p) ⁻¹' O.dom01
  dom11 := (fun κ => -κ) ⁻¹' O.dom11
theorem negDomains_areNhds {δ : ℝ} {p : Fin 4 → ℂ} {O : Domains}
    (hO : AreNhds δ p O) : AreNhds δ p (negDomains p O) where
  isOpen00 := hO.isOpen00.preimage (by fun_prop)
  isOpen10 := hO.isOpen10.preimage (by fun_prop)
  isOpen01 := hO.isOpen01.preimage (by fun_prop)
  isOpen11 := hO.isOpen11.preimage (by fun_prop)
  strip_subset := fun _ h => hO.strip_subset (neg_mem_imStrip h)
  addShift_subset := fun _ h => hO.addShift_subset (neg_sub_mem_stripAddShift h)
  subShift_subset := fun _ h => hO.subShift_subset (neg_add_mem_stripSubShift h)
  real_subset := fun _ h => hO.real_subset (neg_mem_realDualPoints h)
theorem neg_addTwoPiInt (κ : Fin 4 → ℂ) (e : Fin 4 → ℤ) :
    -addTwoPiInt κ e = addTwoPiInt (-κ) (-e) := by
  funext μ
  simp only [addTwoPiInt, Pi.neg_apply, Int.cast_neg]
  ring
theorem neg_sub_addTwoPiInt (p κ : Fin 4 → ℂ) (e : Fin 4 → ℤ) :
    -addTwoPiInt κ e - p = addTwoPiInt (-κ - p) (-e) := by
  funext μ
  simp only [addTwoPiInt, Pi.neg_apply, Pi.sub_apply, Int.cast_neg]
  ring
theorem neg_add_addTwoPiInt (p κ : Fin 4 → ℂ) (e : Fin 4 → ℤ) :
    -addTwoPiInt κ e + p = addTwoPiInt (-κ + p) (-e) := by
  funext μ
  simp only [addTwoPiInt, Pi.neg_apply, Pi.add_apply, Int.cast_neg]
  ring
end Sets
theorem jetTransposition_holds : JetTransposition.Holds := by
  intro I I' hI hI' δ p _ _
  have := hI'.finite_quot
  refine ⟨fun T _ O hO hT => ⟨negDomains p O, negDomains_areNhds hO,
    ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩, ?_⟩, fun T hT => ?_⟩
  · obtain ⟨h00, h10, h01, h11⟩ := hT
    exact ⟨entriesHolomorphicOn_quotHomTranspose h00 (fun κ => -κ) 0 (fun κ => by simp),
      entriesHolomorphicOn_quotHomTranspose h10 (fun κ => -κ - p) (-p)
        (fun κ => sub_eq_add_neg _ _),
      entriesHolomorphicOn_quotHomTranspose h01 (fun κ => -κ + p) p (fun _ => rfl),
      entriesHolomorphicOn_quotHomTranspose h11 (fun κ => -κ) 0 (fun κ => by simp)⟩
  · exact
      { pos_width := hT.pos_width
        mem_imStrip := hT.mem_imStrip
        holo_f00 := isHolomorphicNbhd_quotHomTranspose hT.holo_f00 (fun κ => -κ) 0
          (fun κ => by simp) fun _ h => neg_mem_imStrip h
        holo_f10 := isHolomorphicNbhd_quotHomTranspose hT.holo_f10 (fun κ => -κ - p) (-p)
          (fun κ => sub_eq_add_neg _ _) fun _ h => neg_sub_mem_stripAddShift h
        holo_f01 := isHolomorphicNbhd_quotHomTranspose hT.holo_f01 (fun κ => -κ + p) p
          (fun _ => rfl) fun _ h => neg_add_mem_stripSubShift h
        holo_f11 := isHolomorphicNbhd_quotHomTranspose hT.holo_f11 (fun κ => -κ) 0
          (fun κ => by simp) fun _ h => neg_mem_realDualPoints h
        quasiPeriodic_f00 := isQuasiPeriodic_quotHomTranspose hI hI' hT.quasiPeriodic_f00
          (fun κ => -κ) (fun _ h => neg_mem_imStrip h) neg_addTwoPiInt
        quasiPeriodic_f10 := isQuasiPeriodic_quotHomTranspose hI hI' hT.quasiPeriodic_f10
          (fun κ => -κ - p) (fun _ h => neg_sub_mem_stripAddShift h) (neg_sub_addTwoPiInt p)
        quasiPeriodic_f01 := isQuasiPeriodic_quotHomTranspose hI hI' hT.quasiPeriodic_f01
          (fun κ => -κ + p) (fun _ h => neg_add_mem_stripSubShift h) (neg_add_addTwoPiInt p)
        quasiPeriodic_f11 := isQuasiPeriodic_quotHomTranspose hI hI' hT.quasiPeriodic_f11
          (fun κ => -κ) (fun _ h => neg_mem_realDualPoints h) neg_addTwoPiInt }
end YangMills.Construction.PeriodicOperators.JetTranspose
end
