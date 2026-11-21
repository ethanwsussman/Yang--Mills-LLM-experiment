import YangMills.Construction.Towers.GaugeTransformationsInTheLeftChartProof
import YangMills.Construction.Lattice.DerivativeOfAHolomorphicMapAndOpenBalls
import YangMills.Construction.Matrices.CalculusOfHolomorphicMapsProof
import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLatticeProof
import YangMills.Construction.Towers.AveragedContourOfAPairDoesNotDependOnTheBond
import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Towers.StepKernelsAreHolomorphicOnASide
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.StepKernelHolomorphy
open YangMills.Construction.Matrices
open YangMills.Construction.Coordinates
open YangMills.Construction.Matrices.GroupLieProduct
section Coordinates
theorem isHolomorphicIn_iff_differentiableOn
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {N N' : ℕ} {O : Set (ComplexCoordinates N)} {f : ComplexCoordinates N → ComplexCoordinates N'} :
    ComplexCoordinates.IsHolomorphicIn O f ↔ IsOpen O ∧ DifferentiableOn ℂ f O := by apply _root_.YangMills.SharedProofs.p123 <;> assumption
end Coordinates
section Near
variable {ι κ : Type} [Fintype ι] [Fintype κ]
theorem isSupOpen_inter {σ : Type} {O O' : Set (σ → ComplexMatrix2)} (h : IsSupOpen O)
    (h' : IsSupOpen O') : IsSupOpen (O ∩ O') := by apply _root_.YangMills.SharedProofs.p44648 <;> assumption
theorem isSupOpen_expChartAt_preimage (hE : ExpChartHolomorphy.ExpChartTheory)
    {p : ι ⊕ κ → ComplexMatrix2} (hp : p ∈ GroupLieProduct ι κ) {W : Set (ι ⊕ κ → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) :
    IsSupOpen {A ∈ tracelessPi (ι ⊕ κ) | expChartAt p A ∈ W} := by
  obtain ⟨S, hS, rfl⟩ := hW
  have hχ := ((hE.2.2.2.1 ι κ).1 p hp)
  refine (((hE.2.1 (ι ⊕ κ)).1 _ (sep_subset _ _)).1).2 ?_
  obtain ⟨u, hu, hue⟩ := continuousOn_iff'.1 hχ.2.1 S hS
  refine ⟨u, hu, ?_⟩
  ext A
  constructor
  · rintro ⟨hA, hAS, -⟩
    have : A ∈ expChartAt p ⁻¹' S ∩ tracelessPi (ι ⊕ κ) := ⟨hAS, hA⟩
    rw [hue] at this
    exact ⟨this.1, hA⟩
  · rintro ⟨hAu, hA⟩
    have : A ∈ u ∩ tracelessPi (ι ⊕ κ) := ⟨hAu, hA⟩
    rw [← hue] at this
    exact ⟨hA, this.1, hχ.2.2.1 hA⟩
theorem zero_mem_tracelessPi {σ : Type} : (0 : σ → ComplexMatrix2) ∈ tracelessPi σ :=
  fun _ => ComplexMatrix2.traceless.zero_mem
omit [Fintype ι] [Fintype κ] in
theorem expChartAt_zero (p : ι ⊕ κ → ComplexMatrix2) : expChartAt p 0 = p := by apply _root_.YangMills.SharedProofs.p39871 <;> assumption
theorem continuousOn_of_tupleOfCoords (hE : ExpChartHolomorphy.ExpChartTheory) {σ : Type}
    [Fintype σ] {F : Type} [TopologicalSpace F] {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {ν : σ ≃ Fin (Fintype.card σ)} {O : Set (σ → ComplexMatrix2)} (hO : IsSupOpen O)
    {h : (σ → ComplexMatrix2) → F} (hc : ContinuousOn (h ∘ tupleOfCoords b ν)
      (tupleOfCoords b ν ⁻¹' O)) : ContinuousOn h O := by
  have hT := (hE.2.1 σ).1
  have hpre : IsOpen (tupleOfCoords b ν ⁻¹' O) := ((hT O hO.1).2 b ν).1 hO
  rw [continuousOn_iff']
  intro t ht
  have hU := hc.isOpen_inter_preimage hpre ht
  have hsub : O ∩ h ⁻¹' t ⊆ tracelessPi σ := fun A hA => hO.1 hA.1
  have hD : IsSupOpen (O ∩ h ⁻¹' t) := ((hT _ hsub).2 b ν).2 hU
  obtain ⟨u, hu, hue⟩ := ((hT _ hsub).1).1 hD
  refine ⟨u, hu, ?_⟩
  ext A
  constructor
  · rintro ⟨hAt, hAO⟩
    have : A ∈ O ∩ h ⁻¹' t := ⟨hAO, hAt⟩
    rw [hue] at this
    exact ⟨this.1, hAO⟩
  · rintro ⟨hAu, hAO⟩
    have : A ∈ u ∩ tracelessPi σ := ⟨hAu, hO.1 hAO⟩
    rw [← hue] at this
    exact ⟨this.2, hAO⟩
theorem real_exp_le_of_le_half {s : ℝ} (hs : s ≤ 1 / 2) : Real.exp s ≤ 19 / 10 := by
  have h1 : Real.exp s ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 hs
  have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h3 := Real.exp_one_lt_d9
  have h4 := Real.exp_pos (1 / 2 : ℝ)
  nlinarith
theorem supNorm_zero {σ : Type} : supNorm (0 : σ → ComplexMatrix2) = 0 := by
  simp [supNorm, ComplexMatrix2.operatorNorm]
theorem continuousOn_of_expCharts (hE : ExpChartHolomorphy.ExpChartTheory) {E : Type}
    {l : ℕ} {e : E ≃ ComplexCoordinates l} {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {W : Set (ι ⊕ κ → ComplexMatrix2)} (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    {Φ : (ι ⊕ κ → ComplexMatrix2) → E}
    (h : ∀ p ∈ W, ∃ O : Set (ι ⊕ κ → ComplexMatrix2), 0 ∈ O ∧ (∀ A ∈ O, expChartAt p A ∈ W) ∧
      IsHolomorphicOnTraceless b e O (Φ ∘ expChartAt p)) :
    ContinuousOn (e ∘ Φ) W := by
  intro p hp
  obtain ⟨O, h0, -, hO, hf⟩ := h p hp
  have hWP : W ⊆ GroupLieProduct ι κ := by
    obtain ⟨S, -, rfl⟩ := hW
    exact inter_subset_right
  have hg : ContinuousOn (e ∘ Φ ∘ expChartAt p) O :=
    continuousOn_of_tupleOfCoords hE (b := b) (ν := Fintype.equivFin _) hO (hf _).2.1
  obtain ⟨s, hs, hball⟩ := hO.2 0 h0
  set s' := min s (1 / 2) with hs'
  have hs'0 : 0 < s' := lt_min hs (by norm_num)
  have hχ := ((hE.2.2.2.1 ι κ).1 p (hWP hp)).2.2.2.2 s' hs'0
    (real_exp_le_of_le_half (min_le_right _ _))
  obtain ⟨-, ⟨S, hS, hI⟩, hinv, hlog⟩ := hχ
  have hpI : p ∈ expChartAt p '' supBall (ι ⊕ κ) s' :=
    ⟨0, ⟨zero_mem_tracelessPi, by rw [supNorm_zero]; exact hs'0⟩, expChartAt_zero p⟩
  have hmap : MapsTo (ExpChartHolomorphy.logChart p)
      (expChartAt p '' supBall (ι ⊕ κ) s') O := by
    rintro _ ⟨A, hA, rfl⟩
    rw [hinv.1 hA]
    refine hball A hA.1 ?_
    rw [sub_zero]
    exact hA.2.trans_le (min_le_left _ _)
  have hcI : ContinuousOn (e ∘ Φ) (expChartAt p '' supBall (ι ⊕ κ) s') := by
    refine (hg.comp hlog hmap).congr fun q hq => ?_
    simp only [Function.comp]
    rw [hinv.2 hq]
  have hpS : p ∈ S := by
    have := hpI
    rw [hI] at this
    exact this.1
  refine (continuousWithinAt_inter (hS.mem_nhds hpS)).1 ?_
  refine (hcI p hpI).mono fun q hq => ?_
  rw [hI]
  exact ⟨hq.2, hWP hq.1⟩
def ChartHolomorphicOn (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (ι ⊕ κ → ComplexMatrix2)) (φ : (ι ⊕ κ → ComplexMatrix2) → ℂ) : Prop :=
  ∀ p ∈ W, ∃ O : Set (ι ⊕ κ → ComplexMatrix2), 0 ∈ O ∧ (∀ A ∈ O, expChartAt p A ∈ W) ∧
    IsHolomorphicOnTraceless b (Equiv.funUnique (Fin 1) ℂ).symm O (φ ∘ expChartAt p)
variable {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W W' : Set (ι ⊕ κ → ComplexMatrix2)}
  {φ ψ : (ι ⊕ κ → ComplexMatrix2) → ℂ}
theorem ChartHolomorphicOn.toCoords (hE : ExpChartHolomorphy.ExpChartTheory)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) (h : ChartHolomorphicOn b W φ) :
    IsHolomorphicToCoords b (Equiv.funUnique (Fin 1) ℂ).symm W φ :=
  ⟨hW, continuousOn_of_expCharts hE hW h, h⟩
theorem funUnique_symm_apply_fin_one (z : ℂ) (i : Fin 1) :
    (Equiv.funUnique (Fin 1) ℂ).symm z i = z := by apply _root_.YangMills.DeltaSharedProofs.p23888 <;> assumption
theorem ChartHolomorphicOn.congr (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (h : ChartHolomorphicOn b W φ) (he : EqOn φ ψ W) : ChartHolomorphicOn b W ψ := by
  intro p hp
  obtain ⟨O, h0, hin, hO, hf⟩ := h p hp
  refine ⟨O, h0, hin, hO, fun ν => ?_⟩
  obtain ⟨ho, hd⟩ := (isHolomorphicIn_iff_differentiableOn hM).1 (hf ν)
  refine (isHolomorphicIn_iff_differentiableOn hM).2 ⟨ho, hd.congr fun w hw => ?_⟩
  simp only [Function.comp]
  rw [← he (hin _ hw)]
theorem ChartHolomorphicOn.mono (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (hW' : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W') (hsub : W' ⊆ W)
    (h : ChartHolomorphicOn b W φ) : ChartHolomorphicOn b W' φ := by
  intro p hp
  have hpP : p ∈ GroupLieProduct ι κ := by
    obtain ⟨S, -, rfl⟩ := hW'
    exact hp.2
  obtain ⟨O, h0, -, hO, hf⟩ := h p (hsub hp)
  have hT := isSupOpen_expChartAt_preimage hE hpP hW'
  have hO' := isSupOpen_inter hO hT
  have hz : expChartAt p 0 ∈ W' := by
    rw [expChartAt_zero]
    exact hp
  refine ⟨O ∩ {A ∈ tracelessPi (ι ⊕ κ) | expChartAt p A ∈ W'},
    ⟨h0, zero_mem_tracelessPi, hz⟩, fun A hA => hA.2.2, hO', fun ν => ?_⟩
  obtain ⟨-, hd⟩ := (isHolomorphicIn_iff_differentiableOn hM).1 (hf ν)
  exact (isHolomorphicIn_iff_differentiableOn hM).2 ⟨(((hE.2.1 _).1 _ hO'.1).2 b ν).1 hO',
    hd.mono (preimage_mono inter_subset_left)⟩
theorem ChartHolomorphicOn.const (hE : ExpChartHolomorphy.ExpChartTheory)
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) (z : ℂ) :
    ChartHolomorphicOn b W fun _ => z := by
  intro p hp
  have hpP : p ∈ GroupLieProduct ι κ := by
    obtain ⟨S, -, rfl⟩ := hW
    exact hp.2
  have hT := isSupOpen_expChartAt_preimage hE hpP hW
  have hz : expChartAt p 0 ∈ W := by
    rw [expChartAt_zero]
    exact hp
  refine ⟨{A ∈ tracelessPi (ι ⊕ κ) | expChartAt p A ∈ W},
    ⟨zero_mem_tracelessPi, hz⟩, fun A hA => hA.2, hT, fun ν => ?_⟩
  exact (isHolomorphicIn_iff_differentiableOn hM).2 ⟨(((hE.2.1 _).1 _ hT.1).2 b ν).1 hT,
    differentiableOn_const ((Equiv.funUnique (Fin 1) ℂ).symm z)⟩
theorem ChartHolomorphicOn.map₂ (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {f : ℂ × ℂ → ℂ} (hf : Differentiable ℂ f) (hφ : ChartHolomorphicOn b W φ)
    (hψ : ChartHolomorphicOn b W ψ) : ChartHolomorphicOn b W fun p => f (φ p, ψ p) := by
  intro p hp
  obtain ⟨O₁, h₁, hin₁, hO₁, hf₁⟩ := hφ p hp
  obtain ⟨O₂, h₂, -, hO₂, hf₂⟩ := hψ p hp
  refine ⟨O₁ ∩ O₂, ⟨h₁, h₂⟩, fun A hA => hin₁ A hA.1, isSupOpen_inter hO₁ hO₂, fun ν => ?_⟩
  obtain ⟨ho₁, hd₁⟩ := (isHolomorphicIn_iff_differentiableOn hM).1 (hf₁ ν)
  obtain ⟨ho₂, hd₂⟩ := (isHolomorphicIn_iff_differentiableOn hM).1 (hf₂ ν)
  have g₁ : DifferentiableOn ℂ (fun w => φ (expChartAt p (tupleOfCoords b ν w)))
      (tupleOfCoords b ν ⁻¹' (O₁ ∩ O₂)) := by
    have := (differentiableOn_pi.1 hd₁ 0).mono (preimage_mono (inter_subset_left (t := O₂)))
    refine this.congr fun w _ => ?_
    simp [Function.comp]
  have g₂ : DifferentiableOn ℂ (fun w => ψ (expChartAt p (tupleOfCoords b ν w)))
      (tupleOfCoords b ν ⁻¹' (O₁ ∩ O₂)) := by
    have := (differentiableOn_pi.1 hd₂ 0).mono (preimage_mono (inter_subset_right (s := O₁)))
    refine this.congr fun w _ => ?_
    simp [Function.comp]
  refine (isHolomorphicIn_iff_differentiableOn hM).2 ⟨?_, differentiableOn_pi.2 fun i => ?_⟩
  · rw [preimage_inter]
    exact ho₁.inter ho₂
  · have := hf.comp_differentiableOn (g₁.prodMk g₂)
    refine this.congr fun w _ => ?_
    simp [Function.comp]
theorem ChartHolomorphicOn.add (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hφ : ChartHolomorphicOn b W φ) (hψ : ChartHolomorphicOn b W ψ) :
    ChartHolomorphicOn b W fun p => φ p + ψ p :=
  ChartHolomorphicOn.map₂ hM (f := fun z => z.1 + z.2) (by fun_prop) hφ hψ
theorem ChartHolomorphicOn.mul (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hφ : ChartHolomorphicOn b W φ) (hψ : ChartHolomorphicOn b W ψ) :
    ChartHolomorphicOn b W fun p => φ p * ψ p :=
  ChartHolomorphicOn.map₂ hM (f := fun z => z.1 * z.2) (by fun_prop) hφ hψ
theorem ChartHolomorphicOn.const_mul (hE : ExpChartHolomorphy.ExpChartTheory)
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) (z : ℂ)
    (hφ : ChartHolomorphicOn b W φ) :
    ChartHolomorphicOn b W fun p => z * φ p :=
  (ChartHolomorphicOn.const hE hM hW z).mul hM hφ
def EntriesHolomorphicOn (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (ι ⊕ κ → ComplexMatrix2)) (F : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  ∀ r s, ChartHolomorphicOn b W fun p => F p r s
variable {F G : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
theorem EntriesHolomorphicOn.add (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hF : EntriesHolomorphicOn b W F) (hG : EntriesHolomorphicOn b W G) :
    EntriesHolomorphicOn b W fun p => F p + G p :=
  fun r s => (hF r s).add hM (hG r s)
theorem EntriesHolomorphicOn.sub (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hF : EntriesHolomorphicOn b W F) (hG : EntriesHolomorphicOn b W G) :
    EntriesHolomorphicOn b W fun p => F p - G p :=
  fun r s => ChartHolomorphicOn.map₂ hM (f := fun z => z.1 - z.2) (by fun_prop) (hF r s) (hG r s)
theorem EntriesHolomorphicOn.mul (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hF : EntriesHolomorphicOn b W F) (hG : EntriesHolomorphicOn b W G) :
    EntriesHolomorphicOn b W fun p => F p * G p := by
  intro r s
  have e : (fun p => (F p * G p) r s) =
      fun p => F p r 0 * G p 0 s + F p r 1 * G p 1 s := by
    funext p
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e]
  exact ((hF r 0).mul hM (hG 0 s)).add hM ((hF r 1).mul hM (hG 1 s))
theorem EntriesHolomorphicOn.smul (hE : ExpChartHolomorphy.ExpChartTheory)
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) (z : ℂ)
    (hF : EntriesHolomorphicOn b W F) : EntriesHolomorphicOn b W fun p => z • F p := by
  intro r s
  simpa using (hF r s).const_mul hE hM hW z
theorem EntriesHolomorphicOn.const (hE : ExpChartHolomorphy.ExpChartTheory)
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) (X : ComplexMatrix2) :
    EntriesHolomorphicOn b W fun _ => X :=
  fun r s => ChartHolomorphicOn.const hE hM hW (X r s)
theorem EntriesHolomorphicOn.sum (hE : ExpChartHolomorphy.ExpChartTheory)
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) {α : Type} (S : Finset α)
    {f : α → (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2} (h : ∀ x ∈ S, EntriesHolomorphicOn b W (f x)) :
    EntriesHolomorphicOn b W fun p => ∑ x ∈ S, f x p := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa using EntriesHolomorphicOn.const hE hM hW (b := b) (0 : ComplexMatrix2)
  | insert a S ha ih =>
    have e : (fun p => ∑ x ∈ insert a S, f x p) = fun p => f a p + ∑ x ∈ S, f x p := by
      funext p
      rw [Finset.sum_insert ha]
    rw [e]
    exact (h a (Finset.mem_insert_self a S)).add hM
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))
theorem inv_apply_of_det_eq_one {X : ComplexMatrix2} (hX : X.det = 1) (r s : Fin 2) :
    X⁻¹ r s = Matrix.adjugate X r s := by
  rw [Matrix.inv_def, hX]
  simp
theorem EntriesHolomorphicOn.inv (hE : ExpChartHolomorphy.ExpChartTheory)
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) (hF : EntriesHolomorphicOn b W F)
    (hdet : ∀ p ∈ W, (F p).det = 1) : EntriesHolomorphicOn b W fun p => (F p)⁻¹ := by
  intro r s
  have hneg : ∀ r s, ChartHolomorphicOn b W fun p => -1 * F p r s := fun r s =>
    (hF r s).const_mul hE hM hW (-1)
  have hadj : ChartHolomorphicOn b W fun p => Matrix.adjugate (F p) r s := by
    fin_cases r <;> fin_cases s
    · simpa [Matrix.adjugate_fin_two] using hF 1 1
    · simpa [Matrix.adjugate_fin_two] using hneg 0 1
    · simpa [Matrix.adjugate_fin_two] using hneg 1 0
    · simpa [Matrix.adjugate_fin_two] using hF 0 0
  exact hadj.congr hM fun p hp => (inv_apply_of_det_eq_one (hdet p hp) r s).symm
end Near
section MatrixCoordinates
def matrixLinearEquiv : ComplexMatrix2 ≃ₗ[ℂ] ComplexCoordinates 4 :=
  { ComplexCoordinates.matrixEquiv with
    map_add' := fun X Y => by
      funext k
      rfl
    map_smul' := fun z X => by
      funext k
      rfl }
def matrixCLE : ComplexMatrix2 ≃L[ℂ] ComplexCoordinates 4 := matrixLinearEquiv.toContinuousLinearEquiv
theorem matrixCLE_symm_apply (z : ComplexCoordinates 4) (r s : Fin 2) :
    matrixCLE.symm z r s = z (ComplexCoordinates.entryIndex (r, s)) := rfl
theorem differentiable_matrixPiEquiv_symm_apply {σ : Type} {k : ℕ} (ν : σ ≃ Fin k) (q : σ) :
    Differentiable ℂ fun z => (matrixPiEquiv ν).symm z q := by
  have e : (fun z => (matrixPiEquiv ν).symm z q) =
      fun z => matrixCLE.symm (fun i : Fin 4 => z (finSigmaFinEquiv ⟨ν q, i⟩)) := by
    funext z
    rfl
  rw [e]
  exact matrixCLE.symm.differentiable.comp
    (differentiable_pi.2 fun i => differentiable_apply _)
end MatrixCoordinates
section Factor
variable {ι : Type} [Fintype ι]
open Classical in
def leftMulExpAt (s₀ : ι) (q : ι ⊕ Unit → ComplexMatrix2) : ι ⊕ Empty → ComplexMatrix2
  | .inl i => if i = s₀ then ComplexMatrix2.matExp (q (.inr ())) * q (.inl i) else q (.inl i)
  | .inr k => k.elim
def appendTraceless (p : ι ⊕ Empty → ComplexMatrix2) (Z : ComplexMatrix2) : ι ⊕ Unit → ComplexMatrix2 :=
  Sum.elim (fun i => p (.inl i)) fun _ => Z
omit [Fintype ι] in
theorem leftMulExpAt_append_zero (s₀ : ι) (p : ι ⊕ Empty → ComplexMatrix2) :
    leftMulExpAt s₀ (appendTraceless p 0) = p := by
  funext i
  rcases i with i | i
  · by_cases h : i = s₀ <;> simp [leftMulExpAt, appendTraceless, h, ComplexMatrix2.matExp]
  · exact i.elim
omit [Fintype ι] in
theorem expChartAt_appendTraceless (p A : ι ⊕ Empty → ComplexMatrix2) (Z : ComplexMatrix2) :
    expChartAt (appendTraceless p 0) (appendTraceless A Z) =
      appendTraceless (expChartAt p A) Z := by
  funext i
  rcases i with i | i
  · rfl
  · simp [expChartAt, appendTraceless]
theorem leftMulExpAt_isHolomorphic (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ExpChartHolomorphy.ExpChartTheory) (hX : ComplexMatrix2.ExpLogEstimates)
    (s₀ : ι) (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    IsHolomorphicToProduct b (GroupLieProduct ι Unit) (leftMulExpAt s₀) := by
  classical
  have hopen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι Unit) (GroupLieProduct ι Unit) :=
    ⟨univ, isOpen_univ, (univ_inter _).symm⟩
  refine ⟨hopen, fun i => ?_, fun k => k.elim⟩
  have hval : MapsTo (fun q => leftMulExpAt s₀ q (.inl i)) (GroupLieProduct ι Unit)
      ComplexMatrix2.unitDeterminant := by
    intro q hq
    have hg : (q (.inl i)).det = 1 := hq (.inl i)
    have hZ : ComplexMatrix2.fullTrace (q (.inr ())) = 0 := hq (.inr ())
    by_cases h : i = s₀
    · show (leftMulExpAt s₀ q (.inl i)).det = 1
      simp only [leftMulExpAt, if_pos h]
      rw [Matrix.det_mul, hg, mul_one, hX.2.2.2.2.2.1, hZ]
      simp
    · show (leftMulExpAt s₀ q (.inl i)).det = 1
      simp only [leftMulExpAt, if_neg h]
      exact hg
  refine ((hE.2.2.2.1 ι Unit).2.1 b _ _ hopen hval).2 ?_
  have ν := Fintype.equivFin (ι ⊕ Unit)
  have hth : ComplexCoordinates.IsHolomorphicVia (matrixPiEquiv ν)
      ComplexCoordinates.matrixEquiv univ (fun q => leftMulExpAt s₀ q (.inl i)) := by
    unfold ComplexCoordinates.IsHolomorphicVia
    rw [image_univ, (matrixPiEquiv ν).surjective.range_eq]
    refine (isHolomorphicIn_iff_differentiableOn hM).2
      ⟨isOpen_univ, Differentiable.differentiableOn ?_⟩
    have h₁ := differentiable_matrixPiEquiv_symm_apply ν (.inl i)
    have h₂ := differentiable_matrixPiEquiv_symm_apply ν (.inr ())
    have hm : Differentiable ℂ fun z => leftMulExpAt s₀ ((matrixPiEquiv ν).symm z) (.inl i) := by
      by_cases h : i = s₀
      · simp only [leftMulExpAt, if_pos h]
        have hexp : Differentiable ℂ (ComplexMatrix2.matExp) := fun X =>
          (NormedSpace.exp_analytic X).differentiableAt
        exact (hexp.comp h₂).mul h₁
      · simp only [leftMulExpAt, if_neg h]
        exact h₁
    exact matrixCLE.differentiable.comp hm
  have := (((hE.2.2.2.1 ι Unit).2.2 ComplexMatrix2 4 _ ComplexCoordinates.matrixEquiv ν univ _ hth).2 b)
  rwa [univ_inter] at this
end Factor
section Differential
variable {ι : Type} [Fintype ι] {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
def liftCoords (ν' : ι ⊕ Unit ≃ Fin (Fintype.card (ι ⊕ Unit)))
    (ν : ι ⊕ Empty ≃ Fin (Fintype.card (ι ⊕ Empty)))
    (w : ComplexCoordinates (Fintype.card (ι ⊕ Empty) * 3)) :
    ComplexCoordinates (Fintype.card (ι ⊕ Unit) * 3) :=
  fun m => Sum.elim (fun i => w (finProdFinEquiv (ν (.inl i), (finProdFinEquiv.symm m).2)))
    (fun _ => 0) (ν'.symm (finProdFinEquiv.symm m).1)
def directionCoords (ν' : ι ⊕ Unit ≃ Fin (Fintype.card (ι ⊕ Unit)))
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (Z : ComplexMatrix2.traceless) :
    ComplexCoordinates (Fintype.card (ι ⊕ Unit) * 3) :=
  fun m => Sum.elim (fun _ => 0) (fun _ => b.repr Z (finProdFinEquiv.symm m).2)
    (ν'.symm (finProdFinEquiv.symm m).1)
theorem tupleOfCoords_liftCoords (ν' : ι ⊕ Unit ≃ Fin (Fintype.card (ι ⊕ Unit)))
    (ν : ι ⊕ Empty ≃ Fin (Fintype.card (ι ⊕ Empty)))
    (w : ComplexCoordinates (Fintype.card (ι ⊕ Empty) * 3)) :
    tupleOfCoords b ν' (liftCoords ν' ν w) =
      appendTraceless (tupleOfCoords b ν w) 0 := by
  funext q
  rcases q with i | u
  · simp [tupleOfCoords, ComplexCoordinates.tracelessTuple, liftCoords, appendTraceless]
  · simp [tupleOfCoords, ComplexCoordinates.tracelessTuple, liftCoords, appendTraceless]
theorem tupleOfCoords_directionCoords (ν' : ι ⊕ Unit ≃ Fin (Fintype.card (ι ⊕ Unit)))
    (Z : ComplexMatrix2.traceless) :
    tupleOfCoords b ν' (directionCoords ν' b Z) = appendTraceless 0 (Z : ComplexMatrix2) := by
  funext q
  rcases q with i | u
  · simp [tupleOfCoords, ComplexCoordinates.tracelessTuple, directionCoords, appendTraceless]
  · have h : ∑ x, (b.repr Z) x • ((b x : ComplexMatrix2.traceless) : ComplexMatrix2) =
        (Z : ComplexMatrix2) := by
      have h' := congrArg Subtype.val (b.sum_repr Z)
      simpa only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul] using h'
    simp only [tupleOfCoords, ComplexCoordinates.tracelessTuple, directionCoords, appendTraceless]
    simpa using h
theorem tupleOfCoords_add_smul {σ : Type} [Fintype σ] (ν : σ ≃ Fin (Fintype.card σ))
    (w w' : ComplexCoordinates (Fintype.card σ * 3)) (t : ℂ) :
    tupleOfCoords b ν (w + t • w') =
      tupleOfCoords b ν w + t • tupleOfCoords b ν w' := by
  funext q
  simp [tupleOfCoords, ComplexCoordinates.tracelessTuple, add_smul, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul]
theorem tupleOfCoords_zero {σ : Type} [Fintype σ] (ν : σ ≃ Fin (Fintype.card σ)) :
    tupleOfCoords b ν 0 = 0 := by
  funext q
  simp [tupleOfCoords, ComplexCoordinates.tracelessTuple]
theorem differentiable_liftCoords (ν' : ι ⊕ Unit ≃ Fin (Fintype.card (ι ⊕ Unit)))
    (ν : ι ⊕ Empty ≃ Fin (Fintype.card (ι ⊕ Empty))) :
    Differentiable ℂ (liftCoords ν' ν) := by
  refine differentiable_pi.2 fun m => ?_
  unfold liftCoords
  rcases ν'.symm (finProdFinEquiv.symm m).1 with i | u
  · exact differentiable_apply _
  · exact differentiable_const _
theorem supNorm_nonneg {σ : Type} (A : σ → ComplexMatrix2) : 0 ≤ supNorm A :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem supNorm_appendTraceless_sub_le (A B : ι ⊕ Empty → ComplexMatrix2) :
    supNorm (appendTraceless B 0 - appendTraceless A 0) ≤ supNorm (B - A) := by
  refine Real.iSup_le (fun i => ?_) (supNorm_nonneg _)
  rcases i with i | u
  · exact le_ciSup (f := fun i => ComplexMatrix2.operatorNorm ((B - A) i))
      (Set.finite_range _).bddAbove (.inl i)
  · simpa [appendTraceless, ComplexMatrix2.operatorNorm] using supNorm_nonneg (B - A)
def expCurveAt (s₀ : ι) (Z : ComplexMatrix2.traceless) (p : ι ⊕ Empty → ComplexMatrix2) (t : ℂ) :
    ι ⊕ Empty → ComplexMatrix2 :=
  leftMulExpAt s₀ (appendTraceless p (t • (Z : ComplexMatrix2)))
omit [Fintype ι] in
theorem appendTraceless_add_smul (A : ι ⊕ Empty → ComplexMatrix2) (Z : ComplexMatrix2) (t : ℂ) :
    appendTraceless A 0 + t • appendTraceless 0 Z = appendTraceless A (t • Z) := by
  funext q
  rcases q with i | u <;> simp [appendTraceless]
theorem expCurveAt_deriv_local
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hX : ComplexMatrix2.ExpLogEstimates) (s₀ : ι) (Z : ComplexMatrix2.traceless)
    {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι Empty) W)
    {Φ : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToCoords b ComplexCoordinates.matrixEquiv W Φ)
    {p : ι ⊕ Empty → ComplexMatrix2} (hp : p ∈ W) :
    (∀ᶠ t in 𝓝 (0 : ℂ), expCurveAt s₀ Z p t ∈ W) ∧
    DifferentiableAt ℂ (fun t => Φ (expCurveAt s₀ Z p t)) 0 ∧
    ∃ O : Set (ι ⊕ Empty → ComplexMatrix2), 0 ∈ O ∧ (∀ A ∈ O, expChartAt p A ∈ W) ∧
      ∀ r s : Fin 2, IsHolomorphicOnTraceless b (Equiv.funUnique (Fin 1) ℂ).symm O
        ((fun p' => deriv (fun t => Φ (expCurveAt s₀ Z p' t)) 0 r s) ∘ expChartAt p) := by
  have hWP : W ⊆ GroupLieProduct ι Empty := by
    obtain ⟨S, -, rfl⟩ := hW
    exact inter_subset_right
  have hopen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι Unit) (GroupLieProduct ι Unit) :=
    ⟨univ, isOpen_univ, (univ_inter _).symm⟩
  obtain ⟨-, -, hcomp⟩ := (hE.2.2.2.2.1 ι Unit ι Empty) b _ _ hopen
    (leftMulExpAt_isHolomorphic hM hE hX s₀ b) ComplexMatrix2 4 ComplexCoordinates.matrixEquiv W Φ hΦ
  have hp' : appendTraceless p 0 ∈ GroupLieProduct ι Unit ∩ leftMulExpAt s₀ ⁻¹' W := by
    refine ⟨fun q => ?_, ?_⟩
    · rcases q with i | u
      · exact hWP hp (.inl i)
      · exact ComplexMatrix2.traceless.zero_mem
    · show leftMulExpAt s₀ (appendTraceless p 0) ∈ W
      rw [leftMulExpAt_append_zero]
      exact hp
  obtain ⟨O₁, h₀, hin, hO₁, hH⟩ := hcomp.2.2 _ hp'
  let ν' := Fintype.equivFin (ι ⊕ Unit)
  let H := ComplexCoordinates.matrixEquiv ∘ ((Φ ∘ leftMulExpAt s₀) ∘
    expChartAt (appendTraceless p 0)) ∘ tupleOfCoords b ν'
  have hHol : ComplexCoordinates.IsHolomorphicIn (tupleOfCoords b ν' ⁻¹' O₁) H := hH ν'
  obtain ⟨hopenM, hdiff⟩ := (isHolomorphicIn_iff_differentiableOn hM).1 hHol
  let d := directionCoords ν' b Z
  have hchart : ∀ (ν : ι ⊕ Empty ≃ Fin (Fintype.card (ι ⊕ Empty)))
      (w : ComplexCoordinates (Fintype.card (ι ⊕ Empty) * 3)) (t : ℂ),
      expChartAt (appendTraceless p 0)
        (tupleOfCoords b ν' (liftCoords ν' ν w + t • d)) =
      appendTraceless (expChartAt p (tupleOfCoords b ν w)) (t • (Z : ComplexMatrix2)) := by
    intro ν w t
    rw [tupleOfCoords_add_smul, tupleOfCoords_liftCoords, tupleOfCoords_directionCoords,
      appendTraceless_add_smul, expChartAt_appendTraceless]
  have hstar : ∀ (ν : ι ⊕ Empty ≃ Fin (Fintype.card (ι ⊕ Empty)))
      (w : ComplexCoordinates (Fintype.card (ι ⊕ Empty) * 3)) (t : ℂ),
      H (liftCoords ν' ν w + t • d) = matrixCLE
        (Φ (expCurveAt s₀ Z (expChartAt p (tupleOfCoords b ν w)) t)) := by
    intro ν w t
    simp only [H, Function.comp, hchart]
    rfl
  have hderiv : ∀ (ν : ι ⊕ Empty ≃ Fin (Fintype.card (ι ⊕ Empty)))
      (w : ComplexCoordinates (Fintype.card (ι ⊕ Empty) * 3)),
      liftCoords ν' ν w ∈ tupleOfCoords b ν' ⁻¹' O₁ →
      HasDerivAt (fun t => Φ (expCurveAt s₀ Z (expChartAt p (tupleOfCoords b ν w)) t))
        (matrixCLE.symm (fderiv ℝ H (liftCoords ν' ν w) d)) 0 := by
    intro ν w hz
    have hd := hdiff.differentiableAt (hopenM.mem_nhds hz)
    have h1 := hd.hasFDerivAt
    have h2 : HasDerivAt (fun t : ℂ => liftCoords ν' ν w + t • d) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const d).const_add (liftCoords ν' ν w)
    have h1' : HasFDerivAt H (fderiv ℂ H (liftCoords ν' ν w))
        (liftCoords ν' ν w + (0 : ℂ) • d) := by
      rw [zero_smul, add_zero]
      exact h1
    have h3 : HasDerivAt (fun t : ℂ => H (liftCoords ν' ν w + t • d))
        (fderiv ℂ H (liftCoords ν' ν w) d) 0 :=
      HasFDerivAt.comp_hasDerivAt (x := (0 : ℂ)) (f := fun t : ℂ => liftCoords ν' ν w + t • d)
        h1' h2
    have h4 := matrixCLE.symm.hasFDerivAt.comp_hasDerivAt (0 : ℂ) h3
    have e : fderiv ℝ H (liftCoords ν' ν w) d = fderiv ℂ H (liftCoords ν' ν w) d := by
      rw [hd.fderiv_restrictScalars ℝ]
      rfl
    rw [e]
    refine h4.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [Function.comp, hstar, ContinuousLinearEquiv.symm_apply_apply]
  let ν₀ := Fintype.equivFin (ι ⊕ Empty)
  have hz0 : liftCoords ν' ν₀ 0 ∈ tupleOfCoords b ν' ⁻¹' O₁ := by
    show tupleOfCoords b ν' (liftCoords ν' ν₀ 0) ∈ O₁
    rw [tupleOfCoords_liftCoords, tupleOfCoords_zero]
    have : appendTraceless (0 : ι ⊕ Empty → ComplexMatrix2) 0 = 0 := by
      funext q
      rcases q with i | u <;> rfl
    rw [this]
    exact h₀
  have hbase : expChartAt p (tupleOfCoords b ν₀ 0) = p := by
    rw [tupleOfCoords_zero, expChartAt_zero]
  refine ⟨?_, ?_, ?_⟩
  · have hc : Continuous fun t : ℂ => liftCoords ν' ν₀ 0 + t • d := by fun_prop
    have h0' : liftCoords ν' ν₀ 0 + (0 : ℂ) • d ∈ tupleOfCoords b ν' ⁻¹' O₁ := by
      simpa using hz0
    filter_upwards [hc.continuousAt.eventually (hopenM.mem_nhds h0')] with t ht
    have h := (hin _ ht).2
    rw [mem_preimage, hchart, hbase] at h
    exact h
  · have h := hderiv ν₀ 0 hz0
    rw [hbase] at h
    exact h.differentiableAt
  · have hOt : IsSupOpen {A ∈ tracelessPi (ι ⊕ Empty) | appendTraceless A 0 ∈ O₁} := by
      refine ⟨fun A hA => hA.1, fun A hA => ?_⟩
      obtain ⟨s, hs, hB⟩ := hO₁.2 _ hA.2
      refine ⟨s, hs, fun B hBm hn => ⟨hBm, hB _ ?_ ?_⟩⟩
      · intro q
        rcases q with i | u
        · exact hBm (.inl i)
        · exact ComplexMatrix2.traceless.zero_mem
      · exact (supNorm_appendTraceless_sub_le A B).trans_lt hn
    refine ⟨{A ∈ tracelessPi (ι ⊕ Empty) | appendTraceless A 0 ∈ O₁},
      ⟨zero_mem_tracelessPi, ?_⟩, fun A hA => ?_, fun r s => ⟨hOt, fun ν => ?_⟩⟩
    · have : appendTraceless (0 : ι ⊕ Empty → ComplexMatrix2) 0 = 0 := by
        funext q
        rcases q with i | u <;> rfl
      show appendTraceless (0 : ι ⊕ Empty → ComplexMatrix2) 0 ∈ O₁
      rw [this]
      exact h₀
    · have h := (hin _ hA.2).2
      rw [mem_preimage, expChartAt_appendTraceless, leftMulExpAt_append_zero] at h
      exact h
    · obtain ⟨-, hDd⟩ := (isHolomorphicIn_iff_differentiableOn hM).1 ((hD _ 4 _ H hHol).1 d)
      have hmaps : MapsTo (liftCoords ν' ν)
          (tupleOfCoords b ν ⁻¹' {A ∈ tracelessPi (ι ⊕ Empty) | appendTraceless A 0 ∈ O₁})
          (tupleOfCoords b ν' ⁻¹' O₁) := by
        intro w hw
        show tupleOfCoords b ν' (liftCoords ν' ν w) ∈ O₁
        rw [tupleOfCoords_liftCoords]
        exact hw.2
      have hc2 := hDd.comp (differentiable_liftCoords ν' ν).differentiableOn hmaps
      refine (isHolomorphicIn_iff_differentiableOn hM).2 ⟨(((hE.2.1 _).1 _ hOt.1).2 b ν).1 hOt,
        differentiableOn_pi.2 fun i => ?_⟩
      refine (differentiableOn_pi.1 hc2 (ComplexCoordinates.entryIndex (r, s))).congr
        fun w hw => ?_
      have h := (hderiv ν w (hmaps hw)).deriv
      simp only [Function.comp, funUnique_symm_apply_fin_one, h, matrixCLE_symm_apply]
theorem entriesHolomorphicOn_deriv_expCurveAt
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hX : ComplexMatrix2.ExpLogEstimates) (s₀ : ι) (Z : ComplexMatrix2.traceless)
    {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι Empty) W)
    {Φ : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToCoords b ComplexCoordinates.matrixEquiv W Φ) :
    EntriesHolomorphicOn b W fun p => deriv (fun t => Φ (expCurveAt s₀ Z p t)) 0 := by
  intro r s p hp
  obtain ⟨-, -, O, h0, hin, h⟩ := expCurveAt_deriv_local hM hE hD hX s₀ Z hW hΦ hp
  exact ⟨O, h0, hin, h r s⟩
end Differential
section Lattice
open YangMills.Construction.Tower.DoubleBlockPolydisc (doubleBlockBonds positiveDoubleBlockBonds
  polydiscPositive leftComponents IsHolomorphicWithEntries)
variable {L n k j : ℕ} {c : Edge L n k (j + 1)}
structure OrientationFacts (c : Edge L n k (j + 1)) : Prop where
  xor : ∀ b : Edge L n k j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
  opposite_opposite : ∀ b : Edge L n k j, b.opposite.opposite = b
  opposite_mem : ∀ b ∈ doubleBlockBonds c, b.opposite ∈ doubleBlockBonds c
theorem OrientationFacts.opposite_positive_of_not (F : OrientationFacts c) {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  rcases F.xor b with h | h
  exacts [absurd h.1 hb, h.1]
theorem OrientationFacts.not_opposite_positive (F : OrientationFacts c) {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  rcases F.xor b with h | h
  exacts [h.2, absurd hb h.2]
abbrev fieldOf (c : Edge L n k (j + 1)) (v : positiveDoubleBlockBonds c → ComplexMatrix2) :
    Edge L n k j → ComplexMatrix2 :=
  DoubleBlockPolydisc.fieldOfValues c v
theorem fieldOf_of_positive {v : positiveDoubleBlockBonds c → ComplexMatrix2} {b : Edge L n k j}
    (hb : b ∈ doubleBlockBonds c) (hp : b.IsPositivelyOriented) : fieldOf c v b = v ⟨b, hb, hp⟩ := by
  unfold fieldOf DoubleBlockPolydisc.fieldOfValues PeriodicLattice.extendFromPositive
  rw [dif_pos (show b ∈ doubleBlockBonds c ∧ b.IsPositivelyOriented from ⟨hb, hp⟩)]
  rfl
theorem fieldOf_opposite (F : OrientationFacts c) {v : positiveDoubleBlockBonds c → ComplexMatrix2}
    {b : Edge L n k j} (hb : b ∈ doubleBlockBonds c) (hp : b.IsPositivelyOriented) :
    fieldOf c v b.opposite = (v ⟨b, hb, hp⟩)⁻¹ := by
  have hr := F.not_opposite_positive hp
  have h' : b.opposite.opposite ∈ doubleBlockBonds c ∧ b.opposite.opposite.IsPositivelyOriented := by
    rw [F.opposite_opposite b]
    exact ⟨hb, hp⟩
  unfold fieldOf DoubleBlockPolydisc.fieldOfValues PeriodicLattice.extendFromPositive
  rw [dif_neg (show ¬ (b.opposite ∈ doubleBlockBonds c ∧ b.opposite.IsPositivelyOriented) from
    fun h => hr h.2), dif_pos h']
  congr 2
theorem fieldOf_of_not_mem (F : OrientationFacts c) {v : positiveDoubleBlockBonds c → ComplexMatrix2}
    {b : Edge L n k j} (hb : b ∉ doubleBlockBonds c) : fieldOf c v b = 1 := by
  have h' : ¬ (b.opposite ∈ doubleBlockBonds c ∧ b.opposite.IsPositivelyOriented) := fun h => by
    have := F.opposite_mem _ h.1
    rw [F.opposite_opposite b] at this
    exact hb this
  unfold fieldOf DoubleBlockPolydisc.fieldOfValues PeriodicLattice.extendFromPositive
  rw [dif_neg (show ¬ (b ∈ doubleBlockBonds c ∧ b.IsPositivelyOriented) from fun h => hb h.1),
    dif_neg h']
theorem inv_mem_unitDeterminant {g : ComplexMatrix2} (hg : g ∈ ComplexMatrix2.unitDeterminant) :
    g⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem inv_inv_of_mem_unitDeterminant {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.unitDeterminant) : (g⁻¹)⁻¹ = g := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
theorem fieldOf_mem_fieldsIn (F : OrientationFacts c)
    {v : positiveDoubleBlockBonds c → ComplexMatrix2}
    (hv : ∀ s, v s ∈ PeriodicLattice.complexGaugeGroup) :
    fieldOf c v ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  have hval : ∀ b, fieldOf c v b ∈ PeriodicLattice.complexGaugeGroup := by
    intro b
    by_cases hb : b ∈ doubleBlockBonds c
    · by_cases hp : b.IsPositivelyOriented
      · rw [fieldOf_of_positive hb hp]
        exact hv _
      · have hr := F.opposite_positive_of_not hp
        have hrb := F.opposite_mem b hb
        have h := fieldOf_opposite F (v := v) hrb hr
        rw [F.opposite_opposite b] at h
        rw [h]
        exact inv_mem_unitDeterminant (hv _)
    · rw [fieldOf_of_not_mem F hb]
      show (1 : ComplexMatrix2).det = 1
      simp
  refine ⟨fun b _ => hval b, fun b _ => ?_⟩
  by_cases hb : b ∈ doubleBlockBonds c
  · by_cases hp : b.IsPositivelyOriented
    · rw [fieldOf_opposite F hb hp, fieldOf_of_positive hb hp]
    · have hr := F.opposite_positive_of_not hp
      have hrb := F.opposite_mem b hb
      have h := fieldOf_opposite F (v := v) hrb hr
      rw [F.opposite_opposite b] at h
      rw [h, fieldOf_of_positive hrb hr, inv_inv_of_mem_unitDeterminant (hv _)]
  · have hr : b.opposite ∉ doubleBlockBonds c := fun h => by
      have := F.opposite_mem _ h
      rw [F.opposite_opposite b] at this
      exact hb this
    rw [fieldOf_of_not_mem F hb, fieldOf_of_not_mem F hr]
    simp
theorem exists_field_of_mem_polydisc {ρ : ℝ} {v : positiveDoubleBlockBonds c → ComplexMatrix2}
    (hv : v ∈ polydiscPositive ρ c) :
    ∃ V ∈ nearIdentityPolydisc ρ c, ∀ s : positiveDoubleBlockBonds c, v s = V s.1 := by
  obtain ⟨_, ⟨V, hV, rfl⟩, rfl⟩ := hv
  exact ⟨V, hV, fun s => rfl⟩
theorem fieldOf_eqOn (F : OrientationFacts c) {ρ : ℝ}
    {v : positiveDoubleBlockBonds c → ComplexMatrix2}
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ nearIdentityPolydisc ρ c)
    (hv : ∀ s : positiveDoubleBlockBonds c, v s = V s.1) :
    ∀ b ∈ doubleBlockBonds c, fieldOf c v b = V b := by
  intro b hb
  by_cases hp : b.IsPositivelyOriented
  · rw [fieldOf_of_positive hb hp, hv]
  · have hr := F.opposite_positive_of_not hp
    have hrb := F.opposite_mem b hb
    have h := fieldOf_opposite F (v := v) hrb hr
    rw [F.opposite_opposite b] at h
    have h₂ := hV.1.2 _ hrb
    rw [F.opposite_opposite b] at h₂
    rw [h, hv, h₂]
theorem value_mem_complexGaugeGroup {ρ : ℝ} {v : positiveDoubleBlockBonds c → ComplexMatrix2}
    (hv : v ∈ polydiscPositive ρ c) : ∀ s, v s ∈ PeriodicLattice.complexGaugeGroup := by
  obtain ⟨V, hV, he⟩ := exists_field_of_mem_polydisc hv
  intro s
  rw [he]
  exact hV.1.1 _ s.2.1
theorem fieldOf_mem_polydisc (F : OrientationFacts c) {ρ : ℝ}
    {v : positiveDoubleBlockBonds c → ComplexMatrix2}
    (hv : v ∈ polydiscPositive ρ c) : fieldOf c v ∈ nearIdentityPolydisc ρ c := by
  obtain ⟨V, hV, he⟩ := exists_field_of_mem_polydisc hv
  have h := fieldOf_mem_fieldsIn F (value_mem_complexGaugeGroup hv)
  refine ⟨⟨fun b _ => h.1 b (mem_univ b), fun b _ => h.2 b (mem_univ b)⟩, fun b hb => ?_⟩
  rw [fieldOf_eqOn F hV he b hb]
  exact hV.2 b hb
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
def iPauli (a : Fin 3) : ComplexMatrix2.traceless :=
  ⟨Complex.I • ComplexMatrix2.pauliFamily a,
    ComplexMatrix2.traceless.smul_mem _ (pauliFamily_mem_traceless a)⟩
theorem expTwist_of_positive {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_positive <;> assumption
theorem expTwist_of_not_positive {A U : Edge L n k j → ComplexMatrix2} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := by apply _root_.YangMills.Construction.Tower.LeftChartGauge.expTwist_of_not_positive <;> assumption
def pointOfValues (v : positiveDoubleBlockBonds c → ComplexMatrix2) :
    positiveDoubleBlockBonds c ⊕ Empty → ComplexMatrix2 :=
  Sum.elim v fun e => e.elim
theorem expTwist_basisForm_eq_fieldOf (F : OrientationFacts c) {s₀ : positiveDoubleBlockBonds c}
    {a : Fin 3} {b : PositiveEdge L n k j} (hs : s₀.1 = b.1)
    {p : positiveDoubleBlockBonds c ⊕ Empty → ComplexMatrix2}
    {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b' ∈ doubleBlockBonds c, V b' = fieldOf c (leftComponents p) b')
    (t : ℂ) : ∀ b' ∈ doubleBlockBonds c, PeriodicLattice.expTwist (t • basisForm a b) V b' =
      fieldOf c (leftComponents (expCurveAt s₀ (iPauli a) p t)) b' := by
  classical
  have hpos : ∀ b' ∈ doubleBlockBonds c, b'.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • (t • basisForm a b) b') * V b' =
      fieldOf c (leftComponents (expCurveAt s₀ (iPauli a) p t)) b' := by
    intro b' hb' hp
    rw [hV b' hb', fieldOf_of_positive hb' hp, fieldOf_of_positive hb' hp]
    by_cases h : (⟨b', hb', hp⟩ : positiveDoubleBlockBonds c) = s₀
    · have hb : b' = b.1 := by rw [← hs, ← h]
      have e : Complex.I • (t • basisForm a b) b' = t • (iPauli a : ComplexMatrix2) := by
        have : basisForm a b b' = ComplexMatrix2.pauliFamily a := by
          have hp' : (b.1).IsPositivelyOriented := hb ▸ hp
          simp [basisForm, extendOddly, hb, hp']
        simp only [Pi.smul_apply, this, iPauli]
        exact smul_comm _ _ _
      rw [e]
      simp only [leftComponents, expCurveAt, leftMulExpAt, if_pos h, appendTraceless, Sum.elim_inr,
        Sum.elim_inl]
    · have hb : b' ≠ b.1 := fun hb => h (Subtype.ext (hb.trans hs.symm))
      have e : Complex.I • (t • basisForm a b) b' = 0 := by
        have : basisForm a b b' = 0 := by
          simp [basisForm, extendOddly, hp, hb]
        simp [this]
      rw [e]
      simp [leftComponents, expCurveAt, leftMulExpAt, if_neg h, appendTraceless,
        ComplexMatrix2.matExp]
  intro b' hb'
  by_cases hp : b'.IsPositivelyOriented
  · rw [expTwist_of_positive hp]
    exact hpos b' hb' hp
  · have hr := F.opposite_positive_of_not hp
    have hrb := F.opposite_mem b' hb'
    rw [expTwist_of_not_positive hp, hpos _ hrb hr]
    have h := fieldOf_opposite F (v := leftComponents (expCurveAt s₀ (iPauli a) p t)) hrb hr
    rw [F.opposite_opposite b'] at h
    rw [h, fieldOf_of_positive hrb hr]
theorem expCurveAt_zero {ι : Type} (s₀ : ι) (Z : ComplexMatrix2.traceless)
    (p : ι ⊕ Empty → ComplexMatrix2) : expCurveAt s₀ Z p 0 = p := by
  simp only [expCurveAt, zero_smul]
  exact leftMulExpAt_append_zero s₀ p
theorem isRelativelyOpen_leftComponents_preimage {σ : Type} {W : Set (σ → ComplexMatrix2)}
    (h : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) W) :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct σ Empty) (leftComponents ⁻¹' W) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isRelativelyOpen_preimage_leftComponents <;> assumption
theorem conjugateBy_mem_traceless_of_det {g X : ComplexMatrix2} (hg : g.det = 1)
    (hX : X ∈ ComplexMatrix2.traceless) : ComplexMatrix2.conjugateBy g X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.conjugateBy_mem_traceless_of_det <;> assumption
end Lattice
section Values
open YangMills.Construction.Tower.LeftChartFields (CurveLogDerivative)
open YangMills.Construction.Tower.DoubleBlockPolydisc (doubleBlockBonds positiveDoubleBlockBonds
  polydiscPositive leftComponents IsHolomorphicWithEntries)
variable {L n k j : ℕ} {c : Edge L n k (j + 1)}
structure KernelSetting (ρ : ℝ) (c : Edge L n k (j + 1)) : Prop where
  facts : OrientationFacts c
  positive : c.IsPositivelyOriented
  curves : ∀ r : ℝ, 0 < r →
    CurveLogDerivative ℂ (Metric.ball 0 r) PeriodicLattice.complexGaugeGroup
      PeriodicLattice.complexLieAlgebra
  smoothing_local : ∀ W W' : Edge L n k j → ComplexMatrix2,
    (∀ b ∈ doubleBlockBonds c, W b = W' b) →
    PeriodicLattice.complexBlockAverage W c = PeriodicLattice.complexBlockAverage W' c
  contour_local : ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
    ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
    ∀ W ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup, W ∈ nearIdentityPolydisc ρ c →
    ∀ W' : Edge L n k j → ComplexMatrix2, (∀ b ∈ doubleBlockBonds c, W' b = W b) →
      PeriodicLattice.complexMeanContourHolonomy W' y x =
        PeriodicLattice.complexMeanContourHolonomy W y x
  block_finite : ∀ y : Vertex L n k (j + 1),
    (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y : Set (Vertex L n k j)).Finite
def smoothingOf (c : Edge L n k (j + 1)) (v : positiveDoubleBlockBonds c → ComplexMatrix2) :
    ComplexMatrix2 :=
  PeriodicLattice.complexBlockAverage (fieldOf c v) c
def contourMeanOf (c : Edge L n k (j + 1)) (y : Vertex L n k (j + 1)) (x : Vertex L n k j)
    (v : positiveDoubleBlockBonds c → ComplexMatrix2) : ComplexMatrix2 :=
  PeriodicLattice.complexMeanContourHolonomy (fieldOf c v) y x
def logPart (s₀ : positiveDoubleBlockBonds c) (Z : ComplexMatrix2.traceless)
    (Φ : (positiveDoubleBlockBonds c → ComplexMatrix2) → ComplexMatrix2)
    (p : positiveDoubleBlockBonds c ⊕ Empty → ComplexMatrix2) : ComplexMatrix2 :=
  Complex.I⁻¹ • (deriv (fun t => (Φ ∘ leftComponents) (expCurveAt s₀ Z p t)) 0 *
    (Φ (leftComponents p))⁻¹)
def driftOf (s₀ : positiveDoubleBlockBonds c) (Z : ComplexMatrix2.traceless)
    (T : Finset (Vertex L n k j)) (y : Vertex L n k (j + 1))
    (p : positiveDoubleBlockBonds c ⊕ Empty → ComplexMatrix2) : ComplexMatrix2 :=
  PeriodicLattice.inverseFourthPowerWeight L • ∑ x ∈ T, logPart s₀ Z (contourMeanOf c y x) p
def stepMap (s₀ : positiveDoubleBlockBonds c) (Z : ComplexMatrix2.traceless)
    (T T' : Finset (Vertex L n k j))
    (p : positiveDoubleBlockBonds c ⊕ Empty → ComplexMatrix2) : ComplexMatrix2 :=
  logPart s₀ Z (smoothingOf c) p +
    (ComplexMatrix2.conjugateBy (smoothingOf c (leftComponents p)) (driftOf s₀ Z T c.target p) -
      driftOf s₀ Z T' c.source p)
theorem complexSmoothingDeriv_apply (hc : c.IsPositivelyOriented) (V B : Edge L n k j → ComplexMatrix2) :
    complexSmoothingDeriv V B c = logDirectionalDeriv ℂ
      (fun X => PeriodicLattice.complexBlockAverage (PeriodicLattice.expTwist X V) c)
      (PeriodicLattice.complexBlockAverage V c) B := by
  simp only [complexSmoothingDeriv, holLeftDifferential, extendOddly, if_pos hc]
  rfl
theorem covariantSmoothingDeriv_apply (hc : c.IsPositivelyOriented)
    (V B : Edge L n k j → ComplexMatrix2) :
    covariantSmoothingDeriv V B c = complexSmoothingDeriv V B c +
      (ComplexMatrix2.conjugateBy (PeriodicLattice.complexBlockAverage V c)
        (contourLogDrift V B c.target) - contourLogDrift V B c.source) := by
  simp only [covariantSmoothingDeriv, Pi.add_apply, covDiff, extendOddly, if_pos hc]
  rfl
variable [Fintype (positiveDoubleBlockBonds c)]
theorem logDirectionalDeriv_eq_logPart
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hX : ComplexMatrix2.ExpLogEstimates) {ρ : ℝ} (S : KernelSetting ρ c)
    {Φ : (positiveDoubleBlockBonds c → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicWithEntries (polydiscPositive ρ c) Φ) (s₀ : positiveDoubleBlockBonds c)
    (Z : ComplexMatrix2.traceless) {p : positiveDoubleBlockBonds c ⊕ Empty → ComplexMatrix2}
    (hp : leftComponents p ∈ polydiscPositive ρ c)
    {m : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2} {E V : Edge L n k j → ComplexMatrix2}
    (hm₀ : m V = Φ (leftComponents p))
    (hm : ∀ t : ℂ, leftComponents (expCurveAt s₀ Z p t) ∈ polydiscPositive ρ c →
      m (PeriodicLattice.expTwist (t • E) V) = Φ (leftComponents (expCurveAt s₀ Z p t))) :
    logDirectionalDeriv ℂ (fun X => m (PeriodicLattice.expTwist X V)) (m V) E =
      logPart s₀ Z Φ p ∧ logPart s₀ Z Φ p ∈ ComplexMatrix2.traceless := by
  have hi := hΦ.toMatrices OneLoop.pauliBasis
  have hg := hΦ.toUnimodular OneLoop.pauliBasis
  obtain ⟨hev, hdiff, -⟩ := expCurveAt_deriv_local hM hE hD hX s₀ Z hi.1 hi (p := p) hp
  let w : ℂ → ComplexMatrix2 := fun t => (Φ ∘ leftComponents) (expCurveAt s₀ Z p t)
  have hw0 : w 0 = Φ (leftComponents p) := by
    simp only [w, Function.comp, expCurveAt_zero]
  have hgroup : ∀ᶠ t in 𝓝 (0 : ℂ), w t ∈ PeriodicLattice.complexGaugeGroup :=
    hev.mono fun t ht => hg.2.1 ht
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hgroup
  obtain ⟨-, -, heq, hmem⟩ := S.curves r hr w (fun t ht => hball t ht) hdiff
  have e : (fun t : ℂ => ComplexMatrix2.logSeries
      (m (PeriodicLattice.expTwist (t • E) V) * (m V)⁻¹)) =ᶠ[𝓝 0]
      fun t => ComplexMatrix2.logSeries (w t * (w 0)⁻¹) := by
    filter_upwards [hev] with t h₁
    rw [hm t h₁, hm₀, hw0]
    rfl
  have hpart : logPart s₀ Z Φ p = Complex.I⁻¹ • (deriv w 0 * (w 0)⁻¹) := by
    rw [hw0]
    rfl
  constructor
  · simp only [logDirectionalDeriv, Algebra.algebraMap_self, RingHom.id_apply]
    rw [e.deriv_eq, heq, hpart]
  · rw [hpart]
    exact hmem
omit [Fintype (positiveDoubleBlockBonds c)] in
theorem contourMean_eq_contourMeanOf {ρ : ℝ} (S : KernelSetting ρ c)
    {p : positiveDoubleBlockBonds c ⊕ Empty → ComplexMatrix2}
    (hp : leftComponents p ∈ polydiscPositive ρ c)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b' ∈ doubleBlockBonds c, V b' = fieldOf c (leftComponents p) b')
    {y : Vertex L n k (j + 1)} (hy : y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))))
    {x : Vertex L n k j} (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    PeriodicLattice.complexMeanContourHolonomy V y x = contourMeanOf c y x (leftComponents p) :=
  S.contour_local y hy x hx _ (fieldOf_mem_fieldsIn S.facts (value_mem_complexGaugeGroup hp))
    (fieldOf_mem_polydisc S.facts hp) V hV
theorem covariantSmoothingDeriv_eq_stepMap
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hX : ComplexMatrix2.ExpLogEstimates) {ρ : ℝ} (S : KernelSetting ρ c)
    (hA : IsHolomorphicWithEntries (polydiscPositive ρ c) (smoothingOf c))
    (hC : ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        IsHolomorphicWithEntries (polydiscPositive ρ c) (contourMeanOf c y x))
    {s₀ : positiveDoubleBlockBonds c} {a : Fin 3} {b : PositiveEdge L n k j} (hs : s₀.1 = b.1)
    {p : positiveDoubleBlockBonds c ⊕ Empty → ComplexMatrix2}
    (hp : leftComponents p ∈ polydiscPositive ρ c)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : ∀ b' ∈ doubleBlockBonds c, V b' = fieldOf c (leftComponents p) b') :
    covariantSmoothingDeriv V (basisForm a b) c =
      stepMap s₀ (iPauli a) (S.block_finite c.target).toFinset
        (S.block_finite c.source).toFinset p ∧
    stepMap s₀ (iPauli a) (S.block_finite c.target).toFinset
        (S.block_finite c.source).toFinset p ∈ ComplexMatrix2.traceless := by
  have hcurve := expTwist_basisForm_eq_fieldOf S.facts (a := a) hs hV
  have hav : PeriodicLattice.complexBlockAverage V c = smoothingOf c (leftComponents p) :=
    S.smoothing_local _ _ hV
  have h₁ := logDirectionalDeriv_eq_logPart hM hE hD hX S hA s₀ (iPauli a) hp
    (m := fun W => PeriodicLattice.complexBlockAverage W c) (E := basisForm a b) (V := V) hav
    fun t _ => S.smoothing_local _ _ (hcurve t)
  have h₂ : ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y, _ := fun y hy x hx =>
    logDirectionalDeriv_eq_logPart hM hE hD hX S (hC y hy x hx) s₀ (iPauli a) hp
      (m := fun W => PeriodicLattice.complexMeanContourHolonomy W y x) (E := basisForm a b) (V := V)
      (contourMean_eq_contourMeanOf S hp hV hy hx)
      fun t ht => S.contour_local y hy x hx _
        (fieldOf_mem_fieldsIn S.facts (value_mem_complexGaugeGroup ht))
        (fieldOf_mem_polydisc S.facts ht) _ (hcurve t)
  have hdrift : ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
      contourLogDrift V (basisForm a b) y =
        driftOf s₀ (iPauli a) (S.block_finite y).toFinset y p ∧
      driftOf s₀ (iPauli a) (S.block_finite y).toFinset y p ∈ ComplexMatrix2.traceless := by
    intro y hy
    constructor
    · simp only [contourLogDrift, driftOf]
      rw [finsum_mem_eq_finite_toFinset_sum _ (S.block_finite y)]
      exact congrArg (PeriodicLattice.inverseFourthPowerWeight L • ·) (Finset.sum_congr rfl fun x hx =>
        (h₂ y hy x ((S.block_finite y).mem_toFinset.1 hx)).1)
    · exact ComplexMatrix2.traceless.smul_mem _ (ComplexMatrix2.traceless.sum_mem fun x hx =>
        (h₂ y hy x ((S.block_finite y).mem_toFinset.1 hx)).2)
  have hdet : (smoothingOf c (leftComponents p)).det = 1 :=
    (hA.toUnimodular OneLoop.pauliBasis).2.1 hp
  constructor
  · rw [covariantSmoothingDeriv_apply S.positive, complexSmoothingDeriv_apply S.positive, h₁.1, hav,
      (hdrift c.target (Or.inr rfl)).1, (hdrift c.source (Or.inl rfl)).1]
    rfl
  · exact ComplexMatrix2.traceless.add_mem h₁.2 (ComplexMatrix2.traceless.sub_mem
      (conjugateBy_mem_traceless_of_det hdet (hdrift c.target (Or.inr rfl)).2)
      (hdrift c.source (Or.inl rfl)).2)
end Values
section Entries
open YangMills.Construction.Tower.DoubleBlockPolydisc (doubleBlockBonds positiveDoubleBlockBonds
  polydiscPositive leftComponents IsHolomorphicWithEntries)
def pauliCoeffFormula (a : Fin 3) (X : ComplexMatrix2) : ℂ :=
  ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
theorem pauliCoeff_eq_formula {a : Fin 3} {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a X = pauliCoeffFormula a X := by
  simp only [pauliCoeff, dif_pos hX]
  rfl
theorem chartHolomorphicOn_pauliCoeffFormula {ι κ : Type} [Fintype ι] [Fintype κ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {F : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W)
    (hF : EntriesHolomorphicOn b W F) (a : Fin 3) :
    ChartHolomorphicOn b W fun p => pauliCoeffFormula a (F p) := by
  fin_cases a
  · refine (((hF 0 1).add hM (hF 1 0)).const_mul hE hM hW (1 / 2)).congr hM fun p _ => ?_
    simp only [pauliCoeffFormula, Fin.zero_eta, Matrix.cons_val_zero]
    ring
  · refine ((((hF 1 0).add hM ((hF 0 1).const_mul hE hM hW (-1)))).const_mul hE hM hW
      (1 / (2 * Complex.I))).congr hM fun p _ => ?_
    simp only [pauliCoeffFormula, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  · refine (hF 0 0).congr hM fun p _ => ?_
    rfl
variable {L n k j : ℕ} {c : Edge L n k (j + 1)} [Fintype (positiveDoubleBlockBonds c)]
theorem entriesHolomorphicOn_logPart
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hX : ComplexMatrix2.ExpLogEstimates) (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {ρ : ℝ} {Φ : (positiveDoubleBlockBonds c → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicWithEntries (polydiscPositive ρ c) Φ) (s₀ : positiveDoubleBlockBonds c)
    (Z : ComplexMatrix2.traceless) :
    EntriesHolomorphicOn β (leftComponents ⁻¹' polydiscPositive ρ c) (logPart s₀ Z Φ) := by
  have hopen := (hΦ.toMatrices β).1
  have hd := entriesHolomorphicOn_deriv_expCurveAt hM hE hD hX s₀ Z hopen (hΦ.toMatrices β)
  have hent : EntriesHolomorphicOn β (leftComponents ⁻¹' polydiscPositive ρ c)
      fun p => Φ (leftComponents p) := fun r s => (hΦ.entries β r s).2.2
  have hinv := hent.inv hE hM hopen fun p hp => (hΦ.toUnimodular β).2.1 hp
  exact (hd.mul hM hinv).smul hE hM hopen _
theorem entriesHolomorphicOn_driftOf (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hX : ComplexMatrix2.ExpLogEstimates) (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {ρ : ℝ}
    (hopen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (positiveDoubleBlockBonds c) Empty)
      (leftComponents ⁻¹' polydiscPositive ρ c))
    {T : Finset (Vertex L n k j)} {y : Vertex L n k (j + 1)}
    (hT : ∀ x ∈ T, IsHolomorphicWithEntries (polydiscPositive ρ c) (contourMeanOf c y x))
    (s₀ : positiveDoubleBlockBonds c) (Z : ComplexMatrix2.traceless) :
    EntriesHolomorphicOn β (leftComponents ⁻¹' polydiscPositive ρ c) (driftOf s₀ Z T y) :=
  EntriesHolomorphicOn.smul hE hM hopen _ (EntriesHolomorphicOn.sum hE hM hopen T fun x hx =>
    entriesHolomorphicOn_logPart hM hE hD hX β (hT x hx) s₀ Z)
theorem entriesHolomorphicOn_conjugateBy {ι κ : Type} [Fintype ι] [Fintype κ]
    {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless} {W : Set (ι ⊕ κ → ComplexMatrix2)}
    {F G : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2}
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W) (hF : EntriesHolomorphicOn b W F)
    (hG : EntriesHolomorphicOn b W G) (hdet : ∀ p ∈ W, (F p).det = 1) :
    EntriesHolomorphicOn b W fun p => ComplexMatrix2.conjugateBy (F p) (G p) :=
  (hF.mul hM hG).mul hM (hF.inv hE hM hW hdet)
theorem entriesHolomorphicOn_stepMap (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hX : ComplexMatrix2.ExpLogEstimates) (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {ρ : ℝ}
    (hA : IsHolomorphicWithEntries (polydiscPositive ρ c) (smoothingOf c))
    {T T' : Finset (Vertex L n k j)}
    (hT : ∀ x ∈ T, IsHolomorphicWithEntries (polydiscPositive ρ c) (contourMeanOf c c.target x))
    (hT' : ∀ x ∈ T', IsHolomorphicWithEntries (polydiscPositive ρ c) (contourMeanOf c c.source x))
    (s₀ : positiveDoubleBlockBonds c) (Z : ComplexMatrix2.traceless) :
    EntriesHolomorphicOn β (leftComponents ⁻¹' polydiscPositive ρ c) (stepMap s₀ Z T T') := by
  have hopen := (hA.toMatrices β).1
  have hent : EntriesHolomorphicOn β (leftComponents ⁻¹' polydiscPositive ρ c)
      fun p => smoothingOf c (leftComponents p) := fun r s => (hA.entries β r s).2.2
  exact (entriesHolomorphicOn_logPart hM hE hD hX β hA s₀ Z).add hM
    ((entriesHolomorphicOn_conjugateBy hE hM hopen hent
      (entriesHolomorphicOn_driftOf hM hE hD hX β hopen hT s₀ Z)
      fun p hp => (hA.toUnimodular β).2.1 hp).sub hM
        (entriesHolomorphicOn_driftOf hM hE hD hX β hopen hT' s₀ Z))
omit [Fintype (positiveDoubleBlockBonds c)] in
theorem positiveValues_mem_polydiscPositive {ρ : ℝ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc ρ c) :
    (fun s : positiveDoubleBlockBonds c => V s.1) ∈ polydiscPositive ρ c :=
  ⟨_, ⟨V, hV, rfl⟩, rfl⟩
omit [Fintype (positiveDoubleBlockBonds c)] in
theorem nearIdentityPolydisc_mono {ρ ρ' : ℝ} (h : ρ ≤ ρ') :
    nearIdentityPolydisc ρ c ⊆ nearIdentityPolydisc ρ' c :=
  fun _ hV => ⟨hV.1, fun b hb => (hV.2 b hb).trans_le h⟩
theorem kernelHolomorphyAt_of_setting (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hX : ComplexMatrix2.ExpLogEstimates) {ρ : ℝ} (hρ : 0 < ρ) (S : KernelSetting ρ c)
    (hA : IsHolomorphicWithEntries (polydiscPositive ρ c) (smoothingOf c))
    (hC : ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        IsHolomorphicWithEntries (polydiscPositive ρ c) (contourMeanOf c y x))
    (hopen : ComplexMatrix2.IsRelativelyOpen (unimodularPi (positiveDoubleBlockBonds c))
      (polydiscPositive (3 / 4 * ρ) c)) :
    KernelHolomorphyAt (3 / 4 * ρ) c := by
  have hle : 3 / 4 * ρ ≤ ρ := by linarith
  have hsub : polydiscPositive (3 / 4 * ρ) c ⊆ polydiscPositive ρ c :=
    image_mono (image_mono (nearIdentityPolydisc_mono hle))
  have hopen' := isRelativelyOpen_leftComponents_preimage hopen
  have hC₁ := fun x hx => hC c.target (Or.inr rfl) x ((S.block_finite c.target).mem_toFinset.1 hx)
  have hC₂ := fun x hx => hC c.source (Or.inl rfl) x ((S.block_finite c.source).mem_toFinset.1 hx)
  refine ⟨hopen, ?_, ?_, ?_, ?_⟩
  · intro V hV V' _ he b hb a' a
    have hV₀ := nearIdentityPolydisc_mono hle hV
    have hv := positiveValues_mem_polydiscPositive hV₀
    have hV₁ : ∀ b' ∈ doubleBlockBonds c,
        V b' = fieldOf c (leftComponents
          (pointOfValues fun s : positiveDoubleBlockBonds c => V s.1)) b' :=
      fun b' h' => (fieldOf_eqOn S.facts hV₀ (fun _ => rfl) b' h').symm
    have hV₂ : ∀ b' ∈ doubleBlockBonds c,
        V' b' = fieldOf c (leftComponents
          (pointOfValues fun s : positiveDoubleBlockBonds c => V s.1)) b' :=
      fun b' h' => by rw [← he h']; exact hV₁ b' h'
    unfold smoothingDerivCoeff
    rw [(covariantSmoothingDeriv_eq_stepMap hM hE hD hX S hA hC (s₀ := ⟨b.1, hb, b.2⟩) (a := a)
        (b := b) rfl (p := pointOfValues fun s : positiveDoubleBlockBonds c => V s.1) hv hV₁).1,
      (covariantSmoothingDeriv_eq_stepMap hM hE hD hX S hA hC (s₀ := ⟨b.1, hb, b.2⟩) (a := a)
        (b := b) rfl (p := pointOfValues fun s : positiveDoubleBlockBonds c => V s.1) hv hV₂).1]
  · intro V hV V' _ he y hy x hx a' a
    have hV₀ := nearIdentityPolydisc_mono hle hV
    have hv := positiveValues_mem_polydiscPositive hV₀
    have hV₁ : ∀ b' ∈ doubleBlockBonds c,
        V b' = fieldOf c (leftComponents
          (pointOfValues fun s : positiveDoubleBlockBonds c => V s.1)) b' :=
      fun b' h' => (fieldOf_eqOn S.facts hV₀ (fun _ => rfl) b' h').symm
    have hV₂ : ∀ b' ∈ doubleBlockBonds c,
        V' b' = fieldOf c (leftComponents
          (pointOfValues fun s : positiveDoubleBlockBonds c => V s.1)) b' :=
      fun b' h' => by rw [← he h']; exact hV₁ b' h'
    unfold conjugationCoeff
    rw [contourMean_eq_contourMeanOf S (p := pointOfValues fun s : positiveDoubleBlockBonds c => V s.1)
        hv hV₁ hy hx,
      contourMean_eq_contourMeanOf S (p := pointOfValues fun s : positiveDoubleBlockBonds c => V s.1)
        hv hV₂ hy hx]
  · intro b hb a' a
    refine ⟨inferInstance, fun β => ?_⟩
    have h₁ := chartHolomorphicOn_pauliCoeffFormula hE hM (hA.toMatrices β).1
      (entriesHolomorphicOn_stepMap hM hE hD hX β hA hC₁ hC₂
        (⟨b.1, hb, b.2⟩ : positiveDoubleBlockBonds c) (iPauli a)) a'
    have h₂ := h₁.mono hM hE hopen' (preimage_mono hsub)
    refine (h₂.congr hM (ψ := (fun v => smoothingDerivCoeff
      (DoubleBlockPolydisc.fieldOfValues c v) c b a' a) ∘ leftComponents)
      fun p hp => ?_).toCoords hE hopen'
    have h := covariantSmoothingDeriv_eq_stepMap hM hE hD hX S hA hC (s₀ := ⟨b.1, hb, b.2⟩)
      (a := a) (b := b) rfl (p := p) (hsub hp) (V := fieldOf c (leftComponents p)) fun _ _ => rfl
    show _ = pauliCoeff a' (covariantSmoothingDeriv _ (basisForm a b) c)
    rw [h.1, pauliCoeff_eq_formula h.2]
  · intro y hy x hx a' a
    refine ⟨inferInstance, fun β => ?_⟩
    have hΦ := hC y hy x hx
    have hopen₀ := (hΦ.toMatrices β).1
    have hent : EntriesHolomorphicOn β (leftComponents ⁻¹' polydiscPositive ρ c)
        fun p => contourMeanOf c y x (leftComponents p) := fun r s => (hΦ.entries β r s).2.2
    have hdet : ∀ p ∈ leftComponents ⁻¹' polydiscPositive ρ c,
        (contourMeanOf c y x (leftComponents p)).det = 1 := fun p hp => (hΦ.toUnimodular β).2.1 hp
    have h₁ := chartHolomorphicOn_pauliCoeffFormula hE hM hopen₀
      (entriesHolomorphicOn_conjugateBy hE hM hopen₀ hent
        (EntriesHolomorphicOn.const hE hM hopen₀ (ComplexMatrix2.pauliFamily a)) hdet) a'
    have h₂ := h₁.mono hM hE hopen' (preimage_mono hsub)
    refine (h₂.congr hM (ψ := (fun v => conjugationCoeff
      (DoubleBlockPolydisc.fieldOfValues c v) y x a' a) ∘ leftComponents)
      fun p hp => ?_).toCoords hE hopen'
    show _ = pauliCoeff a'
      (ComplexMatrix2.conjugateBy (contourMeanOf c y x (leftComponents p)) (ComplexMatrix2.pauliFamily a))
    rw [pauliCoeff_eq_formula (conjugateBy_mem_traceless_of_det (hdet p (hsub hp))
      (pauliFamily_mem_traceless a))]
end Entries
open YangMills.Construction.Tower.BondSetFields in
theorem polydiscPositive_isRelativelyOpen {L n k j : ℕ} {c : Edge L n k (j + 1)} {ρ : ℝ} (hρ : 0 < ρ)
    (hP : BondSetFields.ProductStructureAt PeriodicLattice.Bond.opposite
      PeriodicLattice.Bond.IsPositivelyOriented PeriodicLattice.IsGaugeField
      (DoubleBlockPolydisc.doubleBlockBonds c)) :
    ComplexMatrix2.IsRelativelyOpen (unimodularPi (DoubleBlockPolydisc.positiveDoubleBlockBonds c))
      (DoubleBlockPolydisc.polydiscPositive ρ c) := by
  have hC : restrictTo (DoubleBlockPolydisc.doubleBlockBonds c) '' nearIdentityPolydisc ρ c =
      nearIdentity (fieldsOn (PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup)
        (DoubleBlockPolydisc.doubleBlockBonds c)) ρ := by
    ext w
    constructor
    · rintro ⟨V, ⟨hV, hn⟩, rfl⟩
      exact ⟨⟨V, hV, rfl⟩, fun b => hn b.1 b.2⟩
    · rintro ⟨⟨U, hU, rfl⟩, hn⟩
      exact ⟨U, ⟨hU, fun b hb => hn ⟨b, hb⟩⟩, rfl⟩
  show ComplexMatrix2.IsRelativelyOpen _ (readPositive _ _ '' (restrictTo _ '' _))
  rw [hC]
  exact (hP.2.1.2.2.2.2 ρ hρ).2
theorem stepKernelsHolomorphic
    (hM : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : ExpChartHolomorphy.ExpChartTheory)
    (hD : SeparatedFrame.HolomorphicDerivatives.Claim)
    (hX : ComplexMatrix2.ExpLogEstimates)
    (hlc : LeftChartFields.Claim)
    (hS : SmoothingNearIdentity)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hO : BondSetFields.ProductStructureHolds)
    (hEnd : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hR : PeriodicLattice.ComplexAverageIsLocal)
    (hB : PairContourIndependence.Statement)
    (hZ : BlockStructure) :
    StepKernelsHolomorphic := by
  classical
  intro L hL n k j hn hj c hc
  have hk : 1 ≤ k := by omega
  have hρ := (hS.1 L hL).2.2
  have hd := (hP L hL k j hj).1 n hn c hc
  have hfo := hd.finite_open
  have hblock : ∀ y : Vertex L n k (j + 1), (PeriodicLattice.unitBlock y).Finite := fun y => by
    have hb := ((hZ L k (j + 1) hL hk (by omega) (by omega)).1 n hn).1 y
    have hcard : (PeriodicLattice.unitBlock y).ncard = L ^ 4 := hb.2.2.1
    have hLpos : 0 < L := by have := hL.2; omega
    exact Set.finite_of_ncard_pos (by rw [hcard]; positivity)
  have S : KernelSetting (polydiscRadius L) c :=
    { facts :=
        { xor := fun b => ((hEnd ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj.le).2.2.2 b).2.2.2.2.2
          opposite_opposite := fun b => ((hEnd ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ j hj.le).2.2.2 b).2.2.2.1
          opposite_mem := hfo.opposite_mem }
      positive := hc
      curves := hlc.2.1
      smoothing_local := fun W W' he => by
        unfold PeriodicLattice.complexBlockAverage
        simp only [if_pos hc]
        exact (hR L n k j hL.1 hL.2 hn hj c hc).average_eq _ _ he
      contour_local := fun y hy x hx W hW hWp W' hr =>
        ((hB L hL k j hj).1 n hn y x hx c c hc hc hy hy W hW hWp.2 hWp.2 W' W hr
          (fun _ _ => rfl)).2.2
      block_finite := fun y =>
        Set.Finite.preimage (f := Subtype.val) Subtype.val_injective.injOn (hblock y) }
  let inst : Fintype (DoubleBlockPolydisc.positiveDoubleBlockBonds c) := hfo.positive_finite.fintype
  have hA : DoubleBlockPolydisc.IsHolomorphicWithEntries
      (DoubleBlockPolydisc.polydiscPositive (polydiscRadius L) c) (smoothingOf c) := by
    obtain ⟨i, h⟩ := hd.holomorphic_smoothing
    rw [Subsingleton.elim inst i]
    exact h
  have hC : ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        DoubleBlockPolydisc.IsHolomorphicWithEntries
          (DoubleBlockPolydisc.polydiscPositive (polydiscRadius L) c)
          (contourMeanOf c y x) := by
    intro y hy x hx
    obtain ⟨i, h⟩ := hd.holomorphic_contourMean y hy x hx
    rw [Subsingleton.elim inst i]
    exact h
  have hne : (DoubleBlockPolydisc.doubleBlockBonds c).Nonempty := by
    obtain ⟨b, hb⟩ := hfo.positive_nonempty
    exact ⟨b, hb.1⟩
  have hPd := ((hO L hL k j hj.le).1 n hn).1 _ hfo.finite hne hfo.opposite_mem
  have hpos : 0 < 3 / 4 * polydiscRadius L := by
    have := hρ.pos
    positivity
  exact kernelHolomorphyAt_of_setting hM hE hD hX hρ.pos S hA hC
    (polydiscPositive_isRelativelyOpen hpos hPd)
end YangMills.Construction.Tower.StepKernelHolomorphy
end
