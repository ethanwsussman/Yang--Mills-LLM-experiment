import YangMills.Construction.PeriodicOperators.TemperedFunctionals
import YangMills.Construction.Towers.TheDilationOfTheMassiveFields
import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
import YangMills.Construction.Towers.TheMassiveFamilyIsTemperedProof
import YangMills.Construction.Towers.TranslatedConfigurationOfAFieldProof
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.ThirdColourScaling
def ScaledThirdColourWaveIsFourierMode : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ n : ℕ, 0 < n →
    ∀ q ∈ PeriodicOperators.dualLattice (2 * L ^ n), ∀ ρ : Fin 4,
      Scaling.scaledQuotField hL k n
          (PeriodicOperators.LogDetSecondDerivs.descendField (PeriodicOperators.colourEdges L k 0)
            (2 * L ^ n) (Scaling.thirdColourWave L k q ρ)) =
        Tower.remainderQuotField (k := 0)
          (PeriodicOperators.Tempered.fourierModeForm L (n + k) 2 (Tower.finestMesh L k • q) ρ)
end YangMills.Construction.Tower.MassiveOpFunctions.ThirdColourScaling
end

noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions
namespace ThirdColourScaling
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs (descendField)
open YangMills.Construction.Tower.MassiveOpFunctions.Scaling
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.LocalKernels (projPositiveEdge)
open YangMills.Construction.LocalKernels.Periodisation
theorem descendField_mkQuot (F : PeriodicData) (s : ℕ) (f : F.Carrier → ℂ)
    (hf : ∀ (m : Fin 4 → ℤ) (ι : F.Carrier), f (F.translate (s • m) ι) = f ι) (κ : F.Carrier) :
    descendField F s f (F.mkQuot s κ) = f κ := by
  let g : F.QuotMod s → ℂ := Quot.lift f (by
    rintro ι _ ⟨m, rfl⟩
    exact (hf m ι).symm)
  have key : ∃ z : ℂ, ∀ κ' : F.Carrier, F.mkQuot s κ' = F.mkQuot s κ → f κ' = z :=
    ⟨f κ, fun κ' h => congrArg g h⟩
  exact (Classical.epsilon_spec key κ rfl).symm
theorem exp_bilinDot_shift {s : ℕ} (hs : (s : ℝ) ≠ 0) {p : AmbientSpace} (hp : p ∈ dualLattice s)
    {y y' : AmbientSpace} {t : Fin 4 → ℤ} (ht : ∀ μ, y' μ = y μ + (t μ : ℝ) * (s : ℝ)) :
    Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec y')) =
      Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec y)) := by
  obtain ⟨m, hm⟩ := hp
  have h2 : bilinDot (toComplexVec p) (toComplexVec y') =
      bilinDot (toComplexVec p) (toComplexVec y) + ((∑ μ, m μ * t μ : ℤ) : ℂ) * (2 * Real.pi) := by
    simp only [bilinDot, toComplexVec]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have h3 : p μ * y' μ = p μ * y μ + (m μ : ℝ) * (t μ : ℝ) * (2 * Real.pi) := by
      rw [ht μ, hm μ]
      field_simp
    have h4 := congrArg (fun r : ℝ => (r : ℂ)) h3
    push_cast at h4
    exact h4
  have h5 : Complex.I * (((∑ μ, m μ * t μ : ℤ) : ℂ) * (2 * Real.pi)) =
      ((∑ μ, m μ * t μ : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    ring
  rw [h2, mul_add, Complex.exp_add, h5, Complex.exp_int_mul_two_pi_mul_I, mul_one]
variable {L n k : ℕ}
theorem phase_of_coe (hL : 0 < L) {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n))
    (y : AmbientSpace) :
    Tempered.phase (L := L) (n := n) p
        (fun μ => ((y μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n))) =
      Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec y)) := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.phase_coe <;> assumption
theorem pauliFamily_two_mem_traceless :
    Matrices.ComplexMatrix2.pauliFamily 2 ∈ Matrices.ComplexMatrix2.traceless := by
  change Matrix.trace _ = 0
  simp [Matrices.ComplexMatrix2.pauliFamily, OneLoop.pauliZ, Matrix.trace_fin_two]
theorem pauliCoeff_smul_pauliFamily_two (c : ℂ) (a : Fin 3) :
    pauliCoeff a (c • Matrices.ComplexMatrix2.pauliFamily 2) = if a = 2 then c else 0 := by
  have h : c • Matrices.ComplexMatrix2.pauliFamily 2 ∈ Matrices.ComplexMatrix2.traceless :=
    Matrices.ComplexMatrix2.traceless.smul_mem c pauliFamily_two_mem_traceless
  simp only [pauliCoeff, dif_pos h]
  fin_cases a <;>
    simp [OneLoop.pauliCoordinateEquiv, Matrices.ComplexMatrix2.pauliFamily, OneLoop.pauliZ]
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a 0 = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem meshAt_zero_mul_pow (hL : 0 < L) : meshAt L k 0 * ((L ^ k : ℕ) : ℝ) = 1 := by
  have h : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [meshAt]
  push_cast
  rw [zpow_sub₀ h]
  simp
  field_simp
theorem castVec_mem_latticeSubgroup (hL : 0 < L) (v : Fin 4 → ℤ) :
    castVec v ∈ InfiniteLattice.latticeSubgroup (meshAt L k 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.ShiftedFieldGauge.castVec_mem <;> assumption
def intVertex (hL : 0 < L) (v : Fin 4 → ℤ) : FullSpace.Vertex L k 0 :=
  ⟨castVec v, castVec_mem_latticeSubgroup hL v⟩
theorem vertexImage_intShift (hL : 0 < L) (v : Fin 4 → ℤ) (x : FullSpace.Vertex L k 0) :
    FullSpace.vertexImage (intShift v) x = x + intVertex hL v :=
  Subtype.ext (Classical.epsilon_spec
    (p := fun x' : FullSpace.Vertex L k 0 => (x' : AmbientSpace) = intShift v x)
    ⟨x + intVertex hL v, rfl⟩)
theorem edgeImage_intShift_ends (hL : 0 < L) (v : Fin 4 → ℤ) (b : FullSpace.Edge L k 0) :
    (FullSpace.edgeImage (intShift v) b).initial = b.initial + intVertex hL v ∧
      (FullSpace.edgeImage (intShift v) b).terminal = b.terminal + intVertex hL v := by
  have spec := Classical.epsilon_spec
    (p := fun b' : FullSpace.Edge L k 0 =>
      b'.initial = FullSpace.vertexImage (intShift v) b.initial ∧
        b'.terminal = FullSpace.vertexImage (intShift v) b.terminal)
    ⟨⟨FullSpace.vertexImage (intShift v) b.initial, FullSpace.vertexImage (intShift v) b.terminal, by
      obtain ⟨μ, hμ⟩ := b.isAdjacent
      refine ⟨μ, ?_⟩
      rw [vertexImage_intShift hL, vertexImage_intShift hL, add_sub_add_right_eq_sub]
      exact hμ⟩, rfl, rfl⟩
  have spec' : (FullSpace.edgeImage (intShift v) b).initial =
        FullSpace.vertexImage (intShift v) b.initial ∧
      (FullSpace.edgeImage (intShift v) b).terminal =
        FullSpace.vertexImage (intShift v) b.terminal := spec
  rw [vertexImage_intShift hL, vertexImage_intShift hL] at spec'
  exact spec'
theorem shiftEdge_ends (hL : 0 < L) (v : Fin 4 → ℤ) (b : PeriodicOperators.PosEdge L k 0) :
    (shiftEdge v b).1.initial = b.1.initial + intVertex hL v ∧
      (shiftEdge v b).1.terminal = b.1.terminal + intVertex hL v := by
  have spec := Classical.epsilon_spec
    (p := fun b' : PeriodicOperators.PosEdge L k 0 =>
      b'.1 = FullSpace.edgeImage (intShift v) b.1)
    ⟨⟨FullSpace.edgeImage (intShift v) b.1, by
      obtain ⟨μ, hμ⟩ := b.2
      refine ⟨μ, ?_⟩
      rw [(edgeImage_intShift_ends hL v b.1).1, (edgeImage_intShift_ends hL v b.1).2,
        add_sub_add_right_eq_sub]
      exact hμ⟩, rfl⟩
  have spec' : (shiftEdge v b).1 = FullSpace.edgeImage (intShift v) b.1 := spec
  rw [spec']
  exact edgeImage_intShift_ends hL v b.1
theorem thirdColourWave_translate (hL : 0 < L) {q : AmbientSpace} (hq : q ∈ dualLattice (2 * L ^ n))
    (ρ : Fin 4) (m : Fin 4 → ℤ) (ι : (colourEdges L k 0).Carrier) :
    thirdColourWave L k q ρ ((colourEdges L k 0).translate ((2 * L ^ n) • m) ι) =
      thirdColourWave L k q ρ ι := by
  obtain ⟨a, b⟩ := ι
  obtain ⟨ht, hh⟩ := shiftEdge_ends hL ((2 * L ^ n) • m) b
  have hs : ((2 * L ^ n : ℕ) : ℝ) ≠ 0 := by
    have : 0 < 2 * L ^ n := by positivity
    exact_mod_cast this.ne'
  have hd : (shiftEdge ((2 * L ^ n) • m) b).1.terminal -
      (shiftEdge ((2 * L ^ n) • m) b).1.initial = b.1.terminal - b.1.initial := by
    rw [ht, hh, add_sub_add_right_eq_sub]
  have hphase : Complex.exp (Complex.I * bilinDot (toComplexVec q)
        (toComplexVec ((shiftEdge ((2 * L ^ n) • m) b).1.initial : AmbientSpace))) =
      Complex.exp (Complex.I * bilinDot (toComplexVec q)
        (toComplexVec (b.1.initial : AmbientSpace))) := by
    refine exp_bilinDot_shift hs hq (t := m) fun μ => ?_
    rw [ht]
    simp [intVertex, castVec, mul_comm]
  show (if a = 2 ∧ (shiftEdge ((2 * L ^ n) • m) b).1.terminal -
        (shiftEdge ((2 * L ^ n) • m) b).1.initial = _ then
      Complex.exp (Complex.I * bilinDot (toComplexVec q)
        (toComplexVec ((shiftEdge ((2 * L ^ n) • m) b).1.initial : AmbientSpace))) else 0) =
    (if a = 2 ∧ b.1.terminal - b.1.initial = _ then
      Complex.exp (Complex.I * bilinDot (toComplexVec q)
        (toComplexVec (b.1.initial : AmbientSpace))) else 0)
  rw [hd, hphase]
theorem projPositiveEdge_sub (hb : ProjEdgesCompatible L n 0 0)
    (b : PeriodicOperators.PosEdge L 0 0) (ν : Fin 4)
    (hν : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L 0 0) ν) :
    (projPositiveEdge L n 0 0 b).1.target - (projPositiveEdge L n 0 0 b).1.source =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth 0 0) ν := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.projPositiveEdge_target_sub_source <;> assumption
theorem unitStep_ne {ν μ : Fin 4} (h : ν ≠ μ) :
    PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth 0 0) ν ≠
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth 0 0) μ := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.unitStep_ne <;> assumption
theorem axisStep_injective (hL : 0 < L) {μ ν : Fin 4}
    (h : InfiniteLattice.axisStep (meshAt L k 0) μ = InfiniteLattice.axisStep (meshAt L k 0) ν) :
    μ = ν := by
  have hs : meshAt L k 0 ≠ 0 := by
    have : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    exact zpow_ne_zero _ this
  by_contra hne
  have h1 := congrArg (fun s : FullSpace.Vertex L k 0 => (s : AmbientSpace) μ) h
  simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne hne] at h1
  exact hs h1
theorem finestMesh_smul_mem_dualLattice (hL : 0 < L) {q : AmbientSpace}
    (hq : q ∈ dualLattice (2 * L ^ n)) :
    finestMesh L k • q ∈ dualLattice (2 * L ^ (n + k)) := by
  obtain ⟨c, hc⟩ := hq
  refine ⟨c, fun μ => ?_⟩
  have e : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := by
    simp [finestMesh, meshAt, zpow_neg]
  rw [Pi.smul_apply, hc μ, e, smul_eq_mul, pow_add]
  push_cast
  field_simp
theorem remainderCoeffs_fourierModeForm (hL : 0 < L) (hb : ProjEdgesCompatible L n 0 0)
    {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n)) (ρ ν : Fin 4) (a : Fin 3)
    (b : PeriodicOperators.PosEdge L 0 0)
    (hν : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L 0 0) ν) :
    remainderCoeffs (k := 0) (Tempered.fourierModeForm L n 2 p ρ) (a, b) =
      if a = 2 ∧ ν = ρ then
        Complex.exp (Complex.I * bilinDot (toComplexVec p)
          (toComplexVec (b.1.initial : AmbientSpace)))
      else 0 := by
  have e : remainderCoeffs (k := 0) (Tempered.fourierModeForm L n 2 p ρ) (a, b) =
      pauliCoeff a (Tempered.fourierModeForm L n 2 p ρ (projPositiveEdge L n 0 0 b).1) := rfl
  have hd := projPositiveEdge_sub hb b ν hν
  have hv : Tempered.fourierModeForm L n 2 p ρ (projPositiveEdge L n 0 0 b).1 =
      if (projPositiveEdge L n 0 0 b).1.target - (projPositiveEdge L n 0 0 b).1.source =
          PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth 0 0) ρ then
        Tempered.phase p
            ((projPositiveEdge L n 0 0 b).1.source : PeriodicLattice.FourTorus L n) •
          Matrices.ComplexMatrix2.pauliFamily 2
      else 0 := by
    simp only [Tempered.fourierModeForm, extendOddly]
    rw [if_pos (projPositiveEdge L n 0 0 b).2]
  have ht : ((projPositiveEdge L n 0 0 b).1.source : PeriodicLattice.FourTorus L n) =
      fun μ => (((b.1.initial : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
    rw [hb.2.1 b, (hb.1 b.1).1]
    rfl
  rw [e, hv, hd]
  by_cases hνρ : ν = ρ
  · subst hνρ
    rw [if_pos rfl, ht, phase_of_coe hL hp, pauliCoeff_smul_pauliFamily_two]
    simp
  · rw [if_neg (unitStep_ne hνρ), pauliCoeff_zero, if_neg fun h => hνρ h.2]
theorem scaledField_thirdColourWave (hL : 0 < L) (hb : ProjEdgesCompatible L (n + k) 0 0)
    {q : AmbientSpace} (hq : q ∈ dualLattice (2 * L ^ n)) (ρ : Fin 4)
    (κ : (colourEdges L 0 0).Carrier) :
    scaledField hL k (thirdColourWave L k q ρ) κ =
      remainderCoeffs (k := 0)
        (Tempered.fourierModeForm L (n + k) 2 (finestMesh L k • q) ρ) κ := by
  obtain ⟨ι, rfl⟩ := (scaleEdgeIndex hL k).surjective κ
  obtain ⟨a, b⟩ := ι
  obtain ⟨ν, hν⟩ := b.2
  have hl : scaledField hL k (thirdColourWave L k q ρ) (scaleEdgeIndex hL k (a, b)) =
      thirdColourWave L k q ρ (a, b) :=
    congrArg (thirdColourWave L k q ρ) ((scaleEdgeIndex hL k).symm_apply_apply (a, b))
  have hd : (scalePosEdge hL k b).1.terminal - (scalePosEdge hL k b).1.initial =
      InfiniteLattice.axisStep (meshAt L 0 0) ν := by
    change FullSpace.scaleVertex hL (Nat.zero_le k) 0 b.1.terminal -
      FullSpace.scaleVertex hL (Nat.zero_le k) 0 b.1.initial = _
    rw [← map_sub, hν, FullSpace.scaleVertex_axisStep]
  have hr := remainderCoeffs_fourierModeForm (n := n + k) hL hb
    (finestMesh_smul_mem_dualLattice hL hq) ρ ν a (scalePosEdge hL k b) hd
  have e : scaleEdgeIndex hL k (a, b) = (a, scalePosEdge hL k b) := rfl
  rw [hl, e, hr]
  have hdot : bilinDot (toComplexVec (finestMesh L k • q))
        (toComplexVec ((scalePosEdge hL k b).1.initial : AmbientSpace)) =
      bilinDot (toComplexVec q) (toComplexVec (b.1.initial : AmbientSpace)) := by
    have ht : ((scalePosEdge hL k b).1.initial : AmbientSpace) =
        (L : ℝ) ^ (k - 0) • (b.1.initial : AmbientSpace) := rfl
    have hc : finestMesh L k * (L : ℝ) ^ k = 1 := by
      have := meshAt_zero_mul_pow (k := k) hL
      push_cast at this
      exact this
    have hcc : ((finestMesh L k : ℝ) : ℂ) * ((L : ℂ)) ^ k = 1 := by
      exact_mod_cast hc
    simp only [bilinDot, toComplexVec, ht]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, Nat.sub_zero]
    push_cast
    linear_combination ((q μ : ℂ) * ((b.1.initial : AmbientSpace) μ : ℂ)) * hcc
  rw [hdot]
  unfold thirdColourWave
  have hiff : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L k 0) ρ ↔ ν = ρ := by
    rw [hν]
    exact ⟨fun h => axisStep_injective hL h, fun h => by rw [h]⟩
  by_cases h : a = 2 ∧ ν = ρ
  · rw [if_pos h, if_pos ⟨h.1, hiff.2 h.2⟩]
    rfl
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1, hiff.1 h'.2⟩]
end ThirdColourScaling
open ThirdColourScaling in
theorem ThirdColourScaling.scaledThirdColourWave_isFourierMode
    (hCells : LocalKernels.PeriodicLiftCells.CellsAndClassesHold) :
    ThirdColourScaling.ScaledThirdColourWaveIsFourierMode := by
  intro L hL hS k _ n hn q hq ρ
  have hn' : 0 < n + k := by omega
  obtain ⟨hC, hB⟩ := (hCells L hS 0 (n + k) hn').1 0 le_rfl
  have hc := (hC .edge).2
  set B := PeriodicOperators.Tempered.fourierModeForm L (n + k) 2 (finestMesh L k • q) ρ with hBdef
  set w := Scaling.thirdColourWave L k q ρ with hw
  have h1 : PeriodicOperators.liftQuotField
      (PeriodicOperators.colourEdges L k 0) (2 * L ^ n)
      (PeriodicOperators.LogDetSecondDerivs.descendField
        (PeriodicOperators.colourEdges L k 0) (2 * L ^ n) w) = w := by
    funext κ
    exact descendField_mkQuot _ _ w (fun m ι => thirdColourWave_translate hL hq ρ m ι) κ
  have hW : ∀ κ, Scaling.scaledField hL k w κ =
      remainderCoeffs (k := 0) B κ := fun κ => scaledField_thirdColourWave hL hB hq ρ κ
  have hinv : ∀ (m : Fin 4 → ℤ) (ι : (PeriodicOperators.colourEdges L 0 0).Carrier),
      Scaling.scaledField hL k w
          ((PeriodicOperators.colourEdges L 0 0).translate ((2 * L ^ (n + k)) • m) ι) =
        Scaling.scaledField hL k w ι := by
    intro m ι
    refine (hW _).trans (Eq.trans ?_ (hW ι).symm)
    have e : LocalKernels.projPositiveEdge L (n + k) 0 0 ι.2 =
        LocalKernels.projPositiveEdge L (n + k) 0 0
          (PeriodicOperators.shiftEdge ((2 * L ^ (n + k)) • m) ι.2) :=
      (hc ι.2 _).2 ⟨m, rfl⟩
    show pauliCoeff ι.1 (B (LocalKernels.projPositiveEdge L (n + k) 0 0
        (PeriodicOperators.shiftEdge ((2 * L ^ (n + k)) • m) ι.2)).1) =
      pauliCoeff ι.1 (B (LocalKernels.projPositiveEdge L (n + k) 0 0 ι.2).1)
    rw [← e]
  have hl : ∀ κ : (remainderIndex L 0).Carrier,
      Scaling.scaledQuotField hL k n
          (PeriodicOperators.LogDetSecondDerivs.descendField
            (PeriodicOperators.colourEdges L k 0) (2 * L ^ n) w)
          ((remainderIndex L 0).mkQuot (2 * L ^ (n + k)) κ) =
        remainderCoeffs (k := 0) B κ := fun κ => by
    unfold Scaling.scaledQuotField
    rw [h1]
    exact (descendField_mkQuot _ _ _ hinv κ).trans (hW κ)
  have spec := Classical.epsilon_spec
    (p := fun f : (remainderIndex L 0).QuotMod (2 * L ^ (n + k)) → ℂ =>
      ∀ κ : (remainderIndex L 0).Carrier,
        f ((remainderIndex L 0).mkQuot (2 * L ^ (n + k)) κ) =
          remainderCoeffs (k := 0) B κ) ⟨_, hl⟩
  funext c
  induction c using Quot.ind with
  | mk κ => exact (hl κ).trans (spec κ).symm
end YangMills.Construction.Tower.MassiveOpFunctions
end
