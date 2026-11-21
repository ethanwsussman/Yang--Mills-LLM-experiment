import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsOfSeveralVariables
import YangMills.Construction.Towers.TheRemainderOfTheFreePolarisationProof
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.SeveralComplexVariables
open ComplexVariables Coordinates TorusBoundNotation
variable {n : ℕ}
abbrev toUnitCoords (F : ComplexCoordinates n → ℂ) : ComplexCoordinates n → ComplexCoordinates 1 :=
  (Equiv.funUnique (Fin 1) ℂ).symm ∘ F
theorem toUnitCoords_apply (F : ComplexCoordinates n → ℂ) (z : ComplexCoordinates n) (i : Fin 1) :
    toUnitCoords F z i = F z := by
  simp [toUnitCoords]
theorem isHolomorphicScalar_iff {O : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ} :
    IsHolomorphicScalar O F ↔ IsOpen O ∧ ContinuousOn F O ∧ ∀ a ∈ O, ∀ j : Fin n, ∀ᶠ ζ in 𝓝 (0 : ℂ),
      DifferentiableAt ℂ (fun ζ : ℂ => F (a + ζ • ComplexCoordinates.stdBasisVector j)) ζ := by apply _root_.YangMills.Construction.ComplexVariables.HolomorphicFacts.isHolomorphicScalar_iff_lines <;> assumption
theorem eventually_add_smul_stdBasisVector_mem {O : Set (ComplexCoordinates n)} (hO : IsOpen O)
    {a : ComplexCoordinates n} (ha : a ∈ O) (j : Fin n) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • ComplexCoordinates.stdBasisVector j ∈ O := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundJets.FreePolarizationRemainder.eventually_line_mem_of_isOpen <;> assumption
theorem isHolomorphicScalar_of_eqOn {O : Set (ComplexCoordinates n)} {F G : ComplexCoordinates n → ℂ}
    (hF : IsHolomorphicScalar O F) (h : EqOn F G O) : IsHolomorphicScalar O G := by
  obtain ⟨hO, hc, hd⟩ := isHolomorphicScalar_iff.mp hF
  refine isHolomorphicScalar_iff.mpr ⟨hO, hc.congr h.symm, fun a ha j => ?_⟩
  filter_upwards [hd a ha j, (eventually_add_smul_stdBasisVector_mem hO ha j).eventually_nhds]
    with ζ hζ hnear
  refine hζ.congr_of_eventuallyEq ?_
  filter_upwards [hnear] with w hw
  exact (h hw).symm
theorem closedUnderAlgebra {O : Set (ComplexCoordinates n)} {F H : ComplexCoordinates n → ℂ}
    (hF : IsHolomorphicScalar O F) (hH : IsHolomorphicScalar O H) : ClosedUnderAlgebra O F H := by
  obtain ⟨hO, cF, dF⟩ := isHolomorphicScalar_iff.mp hF
  obtain ⟨-, cH, dH⟩ := isHolomorphicScalar_iff.mp hH
  refine ⟨fun c => isHolomorphicScalar_iff.mpr ⟨hO, cF.add (continuousOn_const.mul cH), fun a ha j => ?_⟩,
    isHolomorphicScalar_iff.mpr ⟨hO, cF.mul cH, fun a ha j => ?_⟩,
    isHolomorphicScalar_iff.mpr ⟨hO, ?_, fun a ha j => ?_⟩⟩
  · filter_upwards [dF a ha j, dH a ha j] with ζ h₁ h₂
    exact h₁.add (h₂.const_mul c)
  · filter_upwards [dF a ha j, dH a ha j] with ζ h₁ h₂
    exact h₁.mul h₂
  · exact Complex.continuous_exp.comp_continuousOn cF
  · filter_upwards [dF a ha j] with ζ h₁
    exact h₁.cexp
theorem holomorphicOnOpenSubsets {O : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ}
    (hF : IsHolomorphicScalar O F) : HolomorphicOnOpenSubsets O F := by
  intro O₁ hO₁ hsub
  obtain ⟨-, c, d⟩ := isHolomorphicScalar_iff.mp hF
  exact isHolomorphicScalar_iff.mpr ⟨hO₁, c.mono hsub, fun a ha j => d a (hsub ha) j⟩
theorem holomorphicGluing (O : Set (ComplexCoordinates n)) : HolomorphicGluing O := by
  intro G 𝒰 hopen hunion hG
  have hO : IsOpen O := hunion ▸ isOpen_sUnion hopen
  refine isHolomorphicScalar_iff.mpr ⟨hO, fun a ha => ?_, fun a ha j => ?_⟩
  · rw [← hunion] at ha
    obtain ⟨U, hU, haU⟩ := ha
    obtain ⟨-, c, -⟩ := isHolomorphicScalar_iff.mp (hG U hU)
    exact ((c a haU).continuousAt ((hopen U hU).mem_nhds haU)).continuousWithinAt
  · rw [← hunion] at ha
    obtain ⟨U, hU, haU⟩ := ha
    obtain ⟨-, -, d⟩ := isHolomorphicScalar_iff.mp (hG U hU)
    exact d a haU j
theorem holomorphicPostcomp {O : Set (ComplexCoordinates n)}
    {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar O F) :
    HolomorphicPostcomp O F := by
  intro O' g hO' hg hmaps
  obtain ⟨hO, c, d⟩ := isHolomorphicScalar_iff.mp hF
  refine isHolomorphicScalar_iff.mpr ⟨hO, hg.continuousOn.comp c hmaps, fun a ha j => ?_⟩
  filter_upwards [d a ha j, eventually_add_smul_stdBasisVector_mem hO ha j] with ζ hζ hmem
  have hgat : DifferentiableAt ℂ g (F (a + ζ • ComplexCoordinates.stdBasisVector j)) :=
    hg.differentiableAt (hO'.mem_nhds (hmaps hmem))
  exact hgat.comp ζ hζ
theorem continuous_affineParam {k : ℕ} (a : ComplexCoordinates n) (b : Fin k → ComplexCoordinates n) :
    Continuous (affineParam a b) := by
  unfold affineParam
  fun_prop
theorem isHolomorphicIn_affineParam {k : ℕ} (a : ComplexCoordinates n)
    (b : Fin k → ComplexCoordinates n) {U : Set (ComplexCoordinates k)} (hU : IsOpen U) :
    ComplexCoordinates.IsHolomorphicIn U (affineParam a b) := by
  refine ⟨hU, (continuous_affineParam a b).continuousOn,
    fun t _ j => Eventually.of_forall fun ζ => ?_⟩
  unfold affineParam
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop
theorem holomorphicAffinePrecomp (hA : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {O : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar O F) :
    HolomorphicAffinePrecomp O F := by
  intro k _ a b
  have hO : IsOpen O := hF.1
  have hopen : IsOpen (affineParam a b ⁻¹' O) := hO.preimage (continuous_affineParam a b)
  refine ⟨hopen, ?_⟩
  have h := (((hA.1 n O hO).1 1 (toUnitCoords F) hF).2.2.2.1) k (affineParam a b ⁻¹' O)
    (affineParam a b) (isHolomorphicIn_affineParam a b hopen) (fun t ht => ht)
  exact h
theorem exists_complex_hasFDerivAt (hA : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {O : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar O F)
    {z : ComplexCoordinates n} (hz : z ∈ O) :
    ∃ L : ComplexCoordinates n →L[ℂ] ComplexCoordinates 1, HasFDerivAt (toUnitCoords F) L z ∧
      fderiv ℝ (toUnitCoords F) z = L.restrictScalars ℝ := by
  obtain ⟨L, hL⟩ := ((hA.1 n O hF.1).1 1 (toUnitCoords F) hF).2.2.1 z hz
  exact ⟨L, hasFDerivAt_of_restrictScalars ℝ hL rfl, hL.fderiv⟩
theorem coordDeriv_eq_fderiv
    (hA : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {O : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar O F)
    {z : ComplexCoordinates n} (hz : z ∈ O) (i : Fin n) :
    coordDeriv i F z =
      fderiv ℝ (toUnitCoords F) z (ComplexCoordinates.stdBasisVector i) 0 := by
  obtain ⟨L, hL, hfd⟩ := exists_complex_hasFDerivAt hA hF hz
  have hline : HasDerivAt (fun ζ : ℂ => z + ζ • ComplexCoordinates.stdBasisVector i)
      (ComplexCoordinates.stdBasisVector i) 0 := by
    simpa using
      ((hasDerivAt_id (0 : ℂ)).smul_const (ComplexCoordinates.stdBasisVector i)).const_add z
  have hcomp : HasDerivAt (toUnitCoords F ∘ fun ζ : ℂ => z + ζ • ComplexCoordinates.stdBasisVector i)
      (L (ComplexCoordinates.stdBasisVector i)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hL hline (by simp)
  have hcoord := (hasDerivAt_pi.mp hcomp) 0
  have hval : (fun ζ : ℂ =>
      (toUnitCoords F ∘ fun ζ : ℂ => z + ζ • ComplexCoordinates.stdBasisVector i) ζ 0) =
      fun ζ : ℂ => F (z + ζ • ComplexCoordinates.stdBasisVector i) := by
    funext ζ
    simp [toUnitCoords_apply]
  rw [hval] at hcoord
  rw [hfd]
  exact hcoord.deriv
theorem isHolomorphicScalar_coordDeriv
    (hA : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hB : SeparatedFrame.HolomorphicDerivatives.Claim)
    {O : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar O F)
    (i : Fin n) : IsHolomorphicScalar O (coordDeriv i F) := by
  have h := (hB n 1 O (toUnitCoords F) hF).1 (ComplexCoordinates.stdBasisVector i)
  have h' : IsHolomorphicScalar O
      fun z => fderiv ℝ (toUnitCoords F) z (ComplexCoordinates.stdBasisVector i) 0 := by
    have he : (toUnitCoords fun z =>
        fderiv ℝ (toUnitCoords F) z (ComplexCoordinates.stdBasisVector i) 0) =
        fun z => fderiv ℝ (toUnitCoords F) z (ComplexCoordinates.stdBasisVector i) := by
      funext z
      funext j
      rw [Subsingleton.elim j 0, toUnitCoords_apply]
    change ComplexCoordinates.IsHolomorphicIn O
      (toUnitCoords fun z => fderiv ℝ (toUnitCoords F) z (ComplexCoordinates.stdBasisVector i) 0)
    rw [he]
    exact h
  exact isHolomorphicScalar_of_eqOn h' fun z hz => (coordDeriv_eq_fderiv hA hF hz i).symm
theorem coordDeriv_coordDeriv_eq_secondDeriv
    (hA : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hB : SeparatedFrame.HolomorphicDerivatives.Claim)
    {O : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar O F)
    {z : ComplexCoordinates n} (hz : z ∈ O) (l i : Fin n) :
    coordDeriv l (coordDeriv i F) z =
      ComplexCoordinates.secondDeriv (toUnitCoords F) z (ComplexCoordinates.stdBasisVector l)
        (ComplexCoordinates.stdBasisVector i) 0 := by
  have hΨ := isHolomorphicScalar_coordDeriv hA hB hF i
  obtain ⟨hO, -, dΨ⟩ := isHolomorphicScalar_iff.mp hΨ
  have hd : DifferentiableAt ℂ
      (fun ζ : ℂ => coordDeriv i F (z + ζ • ComplexCoordinates.stdBasisVector l)) 0 :=
    (dΨ z hz l).self_of_nhds
  have hreal := HasDerivAt.comp_ofReal (z := (0 : ℝ))
    (e := fun ζ : ℂ => coordDeriv i F (z + ζ • ComplexCoordinates.stdBasisVector l))
    (e' := deriv (fun ζ : ℂ => coordDeriv i F (z + ζ • ComplexCoordinates.stdBasisVector l)) 0)
    (by simpa using hd.hasDerivAt)
  have hdiff := ((hB n 1 O (toUnitCoords F) hF).2 z hz).1 (ComplexCoordinates.stdBasisVector l)
    (ComplexCoordinates.stdBasisVector i)
  have hline := (hasDerivAt_pi.mp hdiff.hasDerivAt) 0
  have hnear : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), z + s • ComplexCoordinates.stdBasisVector l ∈ O := by
    have hcont : Continuous fun s : ℝ => z + s • ComplexCoordinates.stdBasisVector l := by fun_prop
    exact hcont.continuousAt.eventually_mem (by simpa using hO.mem_nhds hz)
  have heq : (fun s : ℝ => coordDeriv i F
        (z + ((s : ℂ)) • ComplexCoordinates.stdBasisVector l)) =ᶠ[𝓝 (0 : ℝ)]
      fun s : ℝ => ComplexCoordinates.derivAlongLine (toUnitCoords F) z
        (ComplexCoordinates.stdBasisVector l) (ComplexCoordinates.stdBasisVector i) s 0 := by
    filter_upwards [hnear] with s hs
    have hcast : ((s : ℂ)) • ComplexCoordinates.stdBasisVector l =
        s • (ComplexCoordinates.stdBasisVector l : ComplexCoordinates n) := by
      funext t
      simp
    rw [hcast, coordDeriv_eq_fderiv hA hF hs i]
    rfl
  exact (hreal.congr_of_eventuallyEq heq.symm).unique hline
theorem coordDeriv_comm
    (hA : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hB : SeparatedFrame.HolomorphicDerivatives.Claim)
    {O : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar O F)
    (i l : Fin n) :
    EqOn (coordDeriv i (coordDeriv l F)) (coordDeriv l (coordDeriv i F)) O := by
  intro z hz
  rw [coordDeriv_coordDeriv_eq_secondDeriv hA hB hF hz,
    coordDeriv_coordDeriv_eq_secondDeriv hA hB hF hz,
    ((hB n 1 O (toUnitCoords F) hF).2 z hz).2.2]
theorem coordDeriv_eqOn_of_eqOn {O₁ : Set (ComplexCoordinates n)} (h₁ : IsOpen O₁)
    {F H : ComplexCoordinates n → ℂ} (h : EqOn F H O₁) (i : Fin n) :
    EqOn (coordDeriv i F) (coordDeriv i H) O₁ := by
  intro z hz
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [eventually_add_smul_stdBasisVector_mem h₁ hz i] with ζ hζ
  exact h hζ
theorem foldr_coordDeriv_eqOn_of_eqOn {O₁ : Set (ComplexCoordinates n)} (h₁ : IsOpen O₁)
    {F H : ComplexCoordinates n → ℂ} (h : EqOn F H O₁) (l : List (Fin n)) :
    EqOn (l.foldr coordDeriv F) (l.foldr coordDeriv H) O₁ := by
  induction l with
  | nil => exact h
  | cons i l ih => exact coordDeriv_eqOn_of_eqOn h₁ ih i
theorem isHolomorphicScalar_foldr_coordDeriv
    (hA : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hB : SeparatedFrame.HolomorphicDerivatives.Claim)
    {O : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar O F)
    (l : List (Fin n)) : IsHolomorphicScalar O (l.foldr coordDeriv F) := by
  induction l with
  | nil => exact hF
  | cons i l ih => exact isHolomorphicScalar_coordDeriv hA hB ih i
theorem formedSuccessively
    (hA : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hB : SeparatedFrame.HolomorphicDerivatives.Claim)
    {O : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar O F)
    (l : List (Fin n)) : FormedSuccessively O F l := by
  induction l with
  | nil => trivial
  | cons i l ih => exact ⟨ih, isHolomorphicScalar_foldr_coordDeriv hA hB hF l⟩
theorem foldr_coordDeriv_perm
    (hA : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hB : SeparatedFrame.HolomorphicDerivatives.Claim)
    {O : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar O F)
    {l l' : List (Fin n)} (h : l.Perm l') :
    EqOn (l.foldr coordDeriv F) (l'.foldr coordDeriv F) O := by
  have hO : IsOpen O := hF.1
  induction h with
  | nil => exact fun _ _ => rfl
  | cons i _ ih => exact coordDeriv_eqOn_of_eqOn hO ih i
  | swap i j l => exact coordDeriv_comm hA hB (isHolomorphicScalar_foldr_coordDeriv hA hB hF l) j i
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
theorem coordDeriv_add_const_mul {O : Set (ComplexCoordinates n)} {F H : ComplexCoordinates n → ℂ}
    (hF : IsHolomorphicScalar O F) (hH : IsHolomorphicScalar O H) (c : ℂ) (i : Fin n) :
    EqOn (coordDeriv i fun z => F z + c * H z)
      (fun z => coordDeriv i F z + c * coordDeriv i H z) O := by
  intro z hz
  obtain ⟨-, -, dF⟩ := isHolomorphicScalar_iff.mp hF
  obtain ⟨-, -, dH⟩ := isHolomorphicScalar_iff.mp hH
  have h₁ := (dF z hz i).self_of_nhds
  have h₂ := (dH z hz i).self_of_nhds
  have hadd := (h₁.hasDerivAt.add (h₂.hasDerivAt.const_mul c)).deriv
  exact hadd
theorem foldr_coordDeriv_add_const_mul
    (hA : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hB : SeparatedFrame.HolomorphicDerivatives.Claim)
    {O : Set (ComplexCoordinates n)} {F H : ComplexCoordinates n → ℂ}
    (hF : IsHolomorphicScalar O F) (hH : IsHolomorphicScalar O H) (c : ℂ) (l : List (Fin n)) :
    EqOn (l.foldr coordDeriv fun z => F z + c * H z)
      (fun z => l.foldr coordDeriv F z + c * l.foldr coordDeriv H z) O := by
  have hO : IsOpen O := hF.1
  induction l with
  | nil => exact fun _ _ => rfl
  | cons i l ih =>
    exact (coordDeriv_eqOn_of_eqOn hO ih i).trans
      (coordDeriv_add_const_mul (isHolomorphicScalar_foldr_coordDeriv hA hB hF l)
        (isHolomorphicScalar_foldr_coordDeriv hA hB hH l) c i)
theorem foldr_coordDeriv_zero (l : List (Fin n)) :
    l.foldr coordDeriv (0 : ComplexCoordinates n → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext z
    simp only [List.foldr_cons, ih]
    simp [coordDeriv]
theorem derivsVanishOfIndependent
    (hA : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hB : SeparatedFrame.HolomorphicDerivatives.Claim)
    {O : Set (ComplexCoordinates n)} {F : ComplexCoordinates n → ℂ} (hF : IsHolomorphicScalar O F) :
    DerivsVanishOfIndependent O F := by
  intro i hconst
  have hO : IsOpen O := hF.1
  have hzero : EqOn (coordDeriv i F) 0 O := by
    intro z hz
    have heq : (fun ζ : ℂ => F (z + ζ • ComplexCoordinates.stdBasisVector i)) =ᶠ[𝓝 (0 : ℂ)]
        fun _ => F z := by
      filter_upwards [eventually_add_smul_stdBasisVector_mem hO hz i] with ζ hζ
      refine hconst _ hζ z hz fun j hj => ?_
      simp [ComplexCoordinates.stdBasisVector, Pi.single_eq_of_ne hj]
    have := heq.deriv_eq
    simpa [coordDeriv] using this
  refine ⟨hzero, ?_⟩
  have hperm : (((List.finRange n).erase i) ++ [i]).Perm (List.finRange n) :=
    (List.perm_append_singleton _ _).trans (List.perm_cons_erase (List.mem_finRange i)).symm
  intro z hz
  have h₁ := foldr_coordDeriv_perm hA hB hF hperm hz
  have h₂ : EqOn (((List.finRange n).erase i ++ [i]).foldr coordDeriv F) 0 O := by
    simp only [List.foldr_append, List.foldr_cons, List.foldr_nil]
    have := foldr_coordDeriv_eqOn_of_eqOn hO hzero ((List.finRange n).erase i)
    rwa [foldr_coordDeriv_zero] at this
  exact h₁.symm.trans (h₂ hz)
theorem hasSum_principalLog_series {u : ℂ} (hu : ‖u - 1‖ < 1) :
    HasSum (fun k : ℕ+ => (-1 : ℂ) ^ ((k : ℕ) - 1) / ((k : ℕ) : ℂ) * (u - 1) ^ (k : ℕ))
      (Complex.log u) := by
  have h := Complex.hasSum_taylorSeries_log hu
  rw [add_sub_cancel] at h
  have hinj : Function.Injective ((↑) : ℕ+ → ℕ) := PNat.coe_injective
  have hsupp : ∀ x ∉ Set.range ((↑) : ℕ+ → ℕ),
      (-1 : ℂ) ^ (x + 1) * (u - 1) ^ x / (x : ℂ) = 0 := by
    intro x hx
    have hx0 : x = 0 := by
      by_contra hne
      exact hx ⟨⟨x, Nat.pos_of_ne_zero hne⟩, rfl⟩
    simp [hx0]
  have hs := (hinj.hasSum_iff hsupp).mpr h
  have hterm : (fun k : ℕ+ => (-1 : ℂ) ^ ((k : ℕ) - 1) / ((k : ℕ) : ℂ) * (u - 1) ^ (k : ℕ)) =
      (fun x : ℕ => (-1 : ℂ) ^ (x + 1) * (u - 1) ^ x / (x : ℂ)) ∘ ((↑) : ℕ+ → ℕ) := by
    funext k
    obtain ⟨m, hm⟩ : ∃ m, (k : ℕ) = m + 1 := ⟨(k : ℕ) - 1, (Nat.sub_add_cancel k.pos).symm⟩
    simp only [Function.comp_apply, hm, Nat.add_sub_cancel]
    ring
  rw [hterm]
  exact hs
theorem principalLog_eq_log {u : ℂ} (hu : ‖u - 1‖ < 1) : principalLog u = Complex.log u :=
  (hasSum_principalLog_series hu).tsum_eq
theorem principalLogProperties : PrincipalLogProperties := by
  have hslit : ∀ u ∈ discAtOne, u ∈ Complex.slitPlane := fun u hu => by
    have h := Complex.mem_slitPlane_of_norm_lt_one (z := u - 1) hu
    simpa using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hd : DifferentiableOn ℂ Complex.log discAtOne := fun u hu =>
      (Complex.differentiableAt_log (hslit u hu)).differentiableWithinAt
    exact hd.congr fun u hu => principalLog_eq_log hu
  · intro u hu
    rw [principalLog_eq_log hu]
    exact Complex.exp_log (Complex.slitPlane_ne_zero (hslit u hu))
  · rw [principalLog_eq_log (by simp)]
    simp
  · intro u hu
    have hu1 : ‖u - 1‖ < 1 := by linarith
    have hhalf : |(1 / 2 : ℝ)| < 1 := by
      rw [abs_of_pos (by norm_num)]
      norm_num
    have hg := Real.hasSum_pow_div_log_of_abs_lt_one hhalf
    have hlog : -Real.log (1 - 1 / 2) = Real.log 2 := by
      rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv, neg_neg]
    rw [hlog] at hg
    have hg' := (Equiv.pnatEquivNat.hasSum_iff).mpr hg
    rw [principalLog_eq_log hu1]
    refine (hasSum_principalLog_series hu1).norm_le_of_bounded hg' fun k => ?_
    have hp : PNat.natPred k + 1 = (k : ℕ) := PNat.natPred_add_one k
    have hc : ((PNat.natPred k : ℕ) : ℝ) + 1 = ((k : ℕ) : ℝ) := by exact_mod_cast hp
    simp only [Function.comp_apply, Equiv.pnatEquivNat_apply]
    rw [hp, hc, norm_mul, norm_div, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
      Complex.norm_natCast, one_div, inv_mul_eq_div]
    gcongr
theorem holomorphicCalculusRules_holds (hA : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hB : SeparatedFrame.HolomorphicDerivatives.Claim) : HolomorphicCalculusRules := by
  intro n _ O _ F H hF hH
  exact ⟨closedUnderAlgebra hF hH, holomorphicOnOpenSubsets hF, holomorphicGluing O,
    holomorphicPostcomp hF, holomorphicAffinePrecomp hA hF,
    ⟨fun i => isHolomorphicScalar_coordDeriv hA hB hF i, coordDeriv_comm hA hB hF⟩,
    ⟨formedSuccessively hA hB hF _, isHolomorphicScalar_foldr_coordDeriv hA hB hF _,
      fun l hl => ⟨formedSuccessively hA hB hF l, foldr_coordDeriv_perm hA hB hF hl⟩⟩,
    ⟨fun c => foldr_coordDeriv_add_const_mul hA hB hF hH c _,
      fun O₁ h₁ _ h => foldr_coordDeriv_eqOn_of_eqOn h₁ h _⟩,
    derivsVanishOfIndependent hA hB hF, principalLogProperties⟩
end YangMills.Construction.SeveralComplexVariables
end
