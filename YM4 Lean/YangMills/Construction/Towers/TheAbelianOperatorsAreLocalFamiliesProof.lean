import YangMills.Construction.Towers.EntriesOfTheAbelianKernelsProof
import YangMills.Construction.Towers.TheAbelianOperatorsAreLocalFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies.AbelianLocality
section Derivatives
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]
def C3Bounded (f : V → ℂ) (c : ℝ) : Prop :=
  ContDiff ℝ 3 f ∧ ∀ k : ℕ, k ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ c
theorem C3Bounded.mono {f : V → ℂ} {c d : ℝ} (h : C3Bounded f c)
    (hcd : c ≤ d) : C3Bounded f d :=
  ⟨h.1, fun k hk x => (h.2 k hk x).trans hcd⟩
theorem C3Bounded.nonneg {f : V → ℂ} {c : ℝ} (h : C3Bounded f c) :
    0 ≤ c :=
  (norm_nonneg _).trans (h.2 0 (by norm_num) 0)
theorem c3Bounded_zero : C3Bounded (fun _ : V => (0 : ℂ)) 0 := by
  refine ⟨contDiff_const, fun k _ x => ?_⟩
  rw [iteratedFDeriv_fun_zero]
  simp
theorem C3Bounded.add {f g : V → ℂ} {c d : ℝ} (hf : C3Bounded f c)
    (hg : C3Bounded g d) : C3Bounded (fun x => f x + g x) (c + d) := by
  refine ⟨hf.1.add hg.1, fun k hk x => ?_⟩
  have hk' : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have e : iteratedFDeriv ℝ k (fun x => f x + g x) x =
      iteratedFDeriv ℝ k f x + iteratedFDeriv ℝ k g x :=
    iteratedFDeriv_add_apply (hf.1.of_le hk').contDiffAt (hg.1.of_le hk').contDiffAt
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (hf.2 k hk x) (hg.2 k hk x))
theorem C3Bounded.const_mul {f : V → ℂ} {c : ℝ} (hf : C3Bounded f c)
    (γ : ℂ) : C3Bounded (fun x => γ * f x) (‖γ‖ * c) := by
  refine ⟨contDiff_const.mul hf.1, fun k hk x => ?_⟩
  have hk' : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  have e : iteratedFDeriv ℝ k (γ • f) x = γ • iteratedFDeriv ℝ k f x :=
    iteratedFDeriv_const_smul_apply (hf.1.of_le hk').contDiffAt
  have e' : (fun x => γ * f x) = γ • f := rfl
  rw [e', e, norm_smul]
  exact mul_le_mul_of_nonneg_left (hf.2 k hk x) (norm_nonneg _)
theorem c3Bounded_finsetSum {α : Type} (s : Finset α) (f : α → V → ℂ) (c : α → ℝ)
    (h : ∀ i ∈ s, C3Bounded (f i) (c i)) :
    C3Bounded (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using c3Bounded_zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
theorem C3Bounded.comp_clm {f : V → ℂ} {c : ℝ} (hf : C3Bounded f c)
    (R : W →L[ℝ] V) : C3Bounded (f ∘ R) (c * (1 + ‖R‖) ^ 3) := by
  refine ⟨hf.1.comp R.contDiff, fun k hk x => ?_⟩
  have hk' : (k : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  rw [R.iteratedFDeriv_comp_right (hf.1.of_le hk') x le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hc := hf.nonneg
  have hR : (1 : ℝ) ≤ 1 + ‖R‖ := by linarith [norm_nonneg R]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc ‖iteratedFDeriv ℝ k f (R x)‖ * ‖R‖ ^ k ≤ c * (1 + ‖R‖) ^ 3 := by
        refine mul_le_mul (hf.2 k hk _) ?_ (by positivity) hc
        calc ‖R‖ ^ k ≤ (1 + ‖R‖) ^ k := by
              exact pow_le_pow_left₀ (norm_nonneg R) (by linarith) k
          _ ≤ (1 + ‖R‖) ^ 3 := pow_le_pow_right₀ hR hk
def expI : ℝ → ℂ := fun t => Complex.exp (Complex.I * t)
theorem iteratedDeriv_expI (k : ℕ) :
    iteratedDeriv k expI = fun t => Complex.I ^ k * expI t := by
  induction k with
  | zero =>
    funext t
    simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h : HasDerivAt expI (expI t * Complex.I) t := by
      have h₁ : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ)) (Complex.I * 1) t :=
        (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I
      have h₂ := h₁.cexp
      rw [mul_one] at h₂
      exact h₂
    rw [(h.const_mul (Complex.I ^ k)).deriv, pow_succ]
    ring
theorem c3Bounded_expI : C3Bounded expI 1 := by
  have hc : ContDiff ℝ 3 expI := by
    unfold expI
    exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨hc, fun k _ t => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expI]
  simp [expI, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
theorem exists_c3Bounded_of_fourier {S : Type} [Fintype S] {P : (S → ℝ) → ℂ}
    {γ : (S → ℤ) → ℂ} (h : Tower.AbelianFieldFacts.HasFourierCoeffs P γ) :
    ∃ c, C3Bounded P c := by
  obtain ⟨hfin, hP⟩ := h
  let ℓ : (S → ℤ) → (S → ℝ) →L[ℝ] ℝ :=
    fun m => ∑ β, (m β : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) β
  have hℓ : ∀ (m : S → ℤ) (x : S → ℝ), ℓ m x = ∑ᶠ β, (m β : ℝ) * x β := fun m x => by
    rw [finsum_eq_sum_of_fintype]
    simp [ℓ]
  have hterm : ∀ m, C3Bounded (fun x => γ m * Tower.AbelianFieldFacts.fourierMode m x)
      (‖γ m‖ * (1 * (1 + ‖ℓ m‖) ^ 3)) := fun m => by
    have := (c3Bounded_expI.comp_clm (ℓ m)).const_mul (γ m)
    have e : (fun x => γ m * (expI ∘ ℓ m) x) =
        fun x => γ m * Tower.AbelianFieldFacts.fourierMode m x := by
      funext x
      simp only [Function.comp, expI, Tower.AbelianFieldFacts.fourierMode, hℓ]
    rwa [e] at this
  have hs := c3Bounded_finsetSum hfin.toFinset _ _ fun m _ => hterm m
  have e : (fun x => ∑ m ∈ hfin.toFinset, γ m * Tower.AbelianFieldFacts.fourierMode m x) = P := by
    funext x
    rw [hP]
    refine (finsum_eq_sum_of_support_subset _ ?_).symm
    intro m hm
    simp only [Function.mem_support] at hm
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    exact fun h0 => hm (by simp [h0])
  rw [e] at hs
  exact ⟨_, hs⟩
end Derivatives
section Entries
variable {L : ℕ} {a : ℝ}
def DependsNear (y : InfiniteLattice.AmbientSpace)
    (F : (Tower.FullSpace.PositiveEdge a → ℝ) → ℂ) (c : ℝ) : Prop :=
  ∃ (E : Finset (Tower.FullSpace.PositiveEdge a)) (Q : (E → ℝ) → ℂ),
    (∀ b ∈ E, TorusMetric.euclidNormVec ((b.1.initial : InfiniteLattice.AmbientSpace) - y) ≤ 2) ∧
    C3Bounded Q c ∧ ∀ θ, F θ = Q fun b => θ b.1
def IsNearKernel {N : Type} (pos : N → InfiniteLattice.AmbientSpace)
    (T : (Tower.FullSpace.PositiveEdge a → ℝ) → N → N → ℂ) (C : ℝ) : Prop :=
  ∀ ι' ι, DependsNear (pos ι') (fun θ => T θ ι' ι) C
theorem IsNearKernel.mono {N : Type} {pos : N → InfiniteLattice.AmbientSpace}
    {T : (Tower.FullSpace.PositiveEdge a → ℝ) → N → N → ℂ} {C D : ℝ}
    (h : IsNearKernel pos T C) (hCD : C ≤ D) : IsNearKernel pos T D := fun ι' ι => by
  obtain ⟨E, Q, h₁, h₂, h₃⟩ := h ι' ι
  exact ⟨E, Q, h₁, h₂.mono hCD, h₃⟩
theorem translates_dependNear {I : PeriodicOperators.PeriodicData}
    (hI : PeriodicOperators.IsPeriodic I)
    (hB : ∀ (ζ : Fin 4 → ℤ) (b : PeriodicOperators.PosEdge L 0 0),
      (((PeriodicOperators.shiftEdge ζ b).1.initial : InfiniteLattice.AmbientSpace)) =
        (b.1.initial : InfiniteLattice.AmbientSpace) + PeriodicOperators.castVec ζ)
    (T : (Tower.FullSpace.PositiveEdge (Tower.meshAt L 0 0) → ℝ) → I.Carrier → I.Carrier → ℂ)
    (hT : Tower.AbelianFieldFacts.KernelEntriesTrigPoly L I T) (ι' ι : I.Carrier) :
    ∃ c : ℝ, ∀ ζ : Fin 4 → ℤ, DependsNear (I.pos (I.translate ζ ι'))
      (fun θ => T θ (I.translate ζ ι') (I.translate ζ ι)) c := by
  classical
  obtain ⟨P, ⟨hfin, -, γ, hγ⟩, hval⟩ := hT ι' ι
  have := Fintype.ofFinite (Tower.AbelianFieldFacts.edgesNear L (I.pos ι'))
  obtain ⟨c, hc⟩ := exists_c3Bounded_of_fourier hγ
  refine ⟨c * 2 ^ 3, fun ζ => ?_⟩
  let E : Finset (Tower.FullSpace.PositiveEdge (Tower.meshAt L 0 0)) :=
    Finset.univ.image fun b : Tower.AbelianFieldFacts.edgesNear L (I.pos ι') =>
      PeriodicOperators.shiftEdge ζ b.1
  have hE : ∀ b : Tower.AbelianFieldFacts.edgesNear L (I.pos ι'),
      PeriodicOperators.shiftEdge ζ b.1 ∈ E :=
    fun b => Finset.mem_image_of_mem _ (Finset.mem_univ b)
  let R : (E → ℝ) →L[ℝ] (Tower.AbelianFieldFacts.edgesNear L (I.pos ι') → ℝ) :=
    ContinuousLinearMap.pi fun b =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : E => ℝ)
        ⟨PeriodicOperators.shiftEdge ζ b.1, hE b⟩
  have hR : ‖R‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun b => norm_le_pi_norm x _
  refine ⟨E, P ∘ R, ?_, (hc.comp_clm R).mono ?_, fun θ => ?_⟩
  · intro b hb
    obtain ⟨b₀, -, rfl⟩ := Finset.mem_image.1 hb
    rw [hI.pos_translate, hB, add_sub_add_right_eq_sub]
    exact b₀.2
  · refine mul_le_mul_of_nonneg_left ?_ hc.nonneg
    exact pow_le_pow_left₀ (by positivity) (by linarith) 3
  · exact hval θ ζ
theorem exists_translate_eq_out {I : PeriodicOperators.PeriodicData}
    (hI : PeriodicOperators.IsPeriodic I) (ι : I.Carrier) :
    ∃ m : Fin 4 → ℤ, ι = I.translate m (Quot.out (I.mkQuot 1 ι)) := by apply _root_.YangMills.Construction.Tower.AbelianOperatorsLocalSelfAdjointProof.exists_translate_out <;> assumption
theorem euclidNormVec_neg (v : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (-v) = TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_neg <;> assumption
theorem isNearKernel_of_trigPoly {I : PeriodicOperators.PeriodicData}
    (hI : PeriodicOperators.IsPeriodic I)
    (hFin : ∀ ι : I.Carrier,
      {κ : I.Carrier | TorusMetric.euclidNormVec (I.pos κ - I.pos ι) ≤ 2}.Finite)
    (hB : ∀ (ζ : Fin 4 → ℤ) (b : PeriodicOperators.PosEdge L 0 0),
      (((PeriodicOperators.shiftEdge ζ b).1.initial : InfiniteLattice.AmbientSpace)) =
        (b.1.initial : InfiniteLattice.AmbientSpace) + PeriodicOperators.castVec ζ)
    (T : (Tower.FullSpace.PositiveEdge (Tower.meshAt L 0 0) → ℝ) → I.Carrier → I.Carrier → ℂ)
    (hT : Tower.AbelianFieldFacts.KernelEntriesTrigPoly L I T)
    (hR : ∀ θ, Tower.AbelianFieldFacts.HasRangeLeTwo I.pos (T θ)) :
    ∃ C : ℝ, 0 < C ∧ IsNearKernel I.pos T C := by
  classical
  choose c hc using translates_dependNear hI hB T hT
  have : Finite I.UnitQuot := hI.finite_quot
  let S : Set (I.Carrier × I.Carrier) := ⋃ q : I.UnitQuot,
    (fun κ => (Quot.out q, κ)) ''
      {κ : I.Carrier | TorusMetric.euclidNormVec (I.pos κ - I.pos (Quot.out q)) ≤ 2}
  have hS : S.Finite := Set.finite_iUnion fun q => (hFin _).image _
  obtain ⟨C, hC⟩ := (hS.image fun p => c p.1 p.2).bddAbove
  refine ⟨max C 0 + 1, by positivity, fun ι' ι => ?_⟩
  by_cases hd : TorusMetric.euclidNormVec (I.pos ι' - I.pos ι) ≤ 2
  · obtain ⟨m, hm⟩ := exists_translate_eq_out hI ι'
    set r := Quot.out (I.mkQuot 1 ι') with hr
    set κ := I.translate (-m) ι with hκ
    have hι : ι = I.translate m κ := by
      rw [hκ, ← hI.translate_add, neg_add_cancel, hI.translate_zero]
    have hmem : (r, κ) ∈ S := by
      refine Set.mem_iUnion.2 ⟨I.mkQuot 1 ι', κ, ?_, rfl⟩
      show TorusMetric.euclidNormVec (I.pos κ - I.pos r) ≤ 2
      have hk : I.pos κ = I.pos ι - PeriodicOperators.castVec m := by
        rw [hκ, hI.pos_translate, sub_eq_add_neg]
        congr 1
        funext μ
        simp [PeriodicOperators.castVec]
      have hp : I.pos ι' = I.pos r + PeriodicOperators.castVec m := by
        conv_lhs => rw [hm]
        exact hI.pos_translate m r
      have e : I.pos κ - I.pos r = -(I.pos ι' - I.pos ι) := by
        rw [hk, hp]
        abel
      rw [e, euclidNormVec_neg]
      exact hd
    have h₁ : c r κ ≤ C := hC ⟨(r, κ), hmem, rfl⟩
    obtain ⟨E, Q, q₁, q₂, q₃⟩ := hc r κ m
    rw [← hι, ← hm] at q₃
    rw [← hm] at q₁
    exact ⟨E, Q, q₁, q₂.mono (by linarith [le_max_left C 0]), q₃⟩
  · refine ⟨∅, fun _ => 0, by simp, c3Bounded_zero.mono (by positivity),
      fun θ => hR θ ι' ι hd⟩
end Entries
section Spacing
variable {a : ℝ}
def vertexPos : Fin 3 × InfiniteLattice.LatticePoint a → InfiniteLattice.AmbientSpace :=
  fun ι => ι.2
def edgePos : Fin 3 × Tower.FullSpace.PositiveEdge a → InfiniteLattice.AmbientSpace :=
  fun ι => ι.2.1.initial
def covDiffAdj (U B : InfiniteLattice.Link a → Matrices.ComplexMatrix2) :
    InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2 :=
  Tower.PairedFunctionSpace.transposeOfValues (Tower.pairedFunctions (InfiniteLattice.LatticePoint a))
    (Tower.FullSpace.edgePairedSpace a) (Tower.FullSpace.covDiff U) B
def laplacianOf (θ : Tower.FullSpace.PositiveEdge a → ℝ)
    (l : InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2) :
    InfiniteLattice.LatticePoint a → Matrices.ComplexMatrix2 :=
  covDiffAdj (Tower.FullSpace.abelianLinkField θ)
    (Tower.FullSpace.covDiff (Tower.FullSpace.abelianLinkField θ) l)
def unitForm (ι : Fin 3 × Tower.FullSpace.PositiveEdge a) :
    InfiniteLattice.Link a → Matrices.ComplexMatrix2 :=
  open Classical in Tower.FullSpace.extendOddly fun b' =>
    if b' = ι.2.1 then Matrices.ComplexMatrix2.pauliFamily ι.1 else 0
def faceQuadratic (U B : InfiniteLattice.Link a → Matrices.ComplexMatrix2) : ℂ :=
  ∑ᶠ p : InfiniteLattice.ElementaryPlaquette a,
    Tower.FaceTermDerivatives.secondDerivExpr (Tower.FullSpace.transportedForm U B p)
      (Tower.FullSpace.faceVariable U p)
def polarKernel (U : InfiniteLattice.Link a → Matrices.ComplexMatrix2) :
    PeriodicOperators.KernelMatrix (Fin 3 × Tower.FullSpace.PositiveEdge a)
      (Fin 3 × Tower.FullSpace.PositiveEdge a) := fun ι' ι =>
  (1 / 2) * (faceQuadratic U (unitForm ι' + unitForm ι) -
    faceQuadratic U (unitForm ι') - faceQuadratic U (unitForm ι))
def ofPositiveValues (g : Tower.FullSpace.PositiveEdge a → Matrices.ComplexMatrix2) :
    InfiniteLattice.Link a → Matrices.ComplexMatrix2 :=
  open Classical in Tower.FullSpace.extendOddly fun b =>
    if h : b.IsPositivelyOriented then g ⟨b, h⟩ else 0
def hessianOf (U B : InfiniteLattice.Link a → Matrices.ComplexMatrix2) :
    InfiniteLattice.Link a → Matrices.ComplexMatrix2 :=
  ofPositiveValues (Tower.ofPauliCoeffs (PeriodicOperators.applyKernel (polarKernel U)
      (Tower.toPauliCoeffs (Tower.FullSpace.restrictToPositiveEdges B)))) +
    Tower.FullSpace.covDiff U (covDiffAdj U B)
def vertexEntry (θ : Tower.FullSpace.PositiveEdge a → ℝ)
    (ι' ι : Fin 3 × InfiniteLattice.LatticePoint a) : ℂ :=
  Tower.pauliCoeff ι'.1
    (laplacianOf θ (Tower.ofPauliCoeffs (Tower.UnitGaugeDirections.basisFunction ι)) ι'.2)
def edgeEntry (θ : Tower.FullSpace.PositiveEdge a → ℝ)
    (ι' ι : Fin 3 × Tower.FullSpace.PositiveEdge a) : ℂ :=
  Tower.pauliCoeff ι'.1 (hessianOf (Tower.FullSpace.abelianLinkField θ)
    (ofPositiveValues (Tower.ofPauliCoeffs (Tower.UnitGaugeDirections.basisFunction ι))) ι'.2.1)
theorem pauliFamily_mem_traceless (c : Fin 3) :
    Matrices.ComplexMatrix2.pauliFamily c ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliCoeff_sum_smul (x : Fin 3 → ℂ) (c : Fin 3) :
    Tower.pauliCoeff c (∑ b, x b • Matrices.ComplexMatrix2.pauliFamily b) = x c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem matrixEntry_eq_of_apply {σ : Type}
    (M : (σ → Matrices.ComplexMatrix2) → σ → Matrices.ComplexMatrix2)
    (T : Tower.UnitLatticeL2.L2Field σ →L[ℂ] Tower.UnitLatticeL2.L2Field σ)
    (h : ∀ v : Tower.UnitLatticeL2.L2Field σ,
      Tower.UnitLatticeL2.ofCoords (T v) = M (Tower.UnitLatticeL2.ofCoords v))
    (ι' ι : Fin 3 × σ) :
    Tower.UnitLatticeL2.matrixEntry T ι' ι =
      Tower.pauliCoeff ι'.1 (M (Tower.ofPauliCoeffs (Tower.UnitGaugeDirections.basisFunction ι)) ι'.2) := by
  classical
  have hv : ((Tower.UnitLatticeL2.basisVec ι : Tower.UnitLatticeL2.L2Field σ) : Fin 3 × σ → ℂ) =
      Tower.UnitGaugeDirections.basisFunction ι := by
    funext κ
    by_cases hκ : κ = ι
    · subst hκ
      simp [Tower.UnitLatticeL2.basisVec, Tower.UnitGaugeDirections.basisFunction]
    · simp [Tower.UnitLatticeL2.basisVec, Tower.UnitGaugeDirections.basisFunction, hκ,
        lp.single_apply]
  have e : Tower.UnitLatticeL2.ofCoords
      (Tower.UnitLatticeL2.basisVec ι : Tower.UnitLatticeL2.L2Field σ) =
      Tower.ofPauliCoeffs (Tower.UnitGaugeDirections.basisFunction ι) := by
    rw [← hv]
    rfl
  have hs := congrFun (h (Tower.UnitLatticeL2.basisVec ι)) ι'.2
  rw [e] at hs
  rw [← hs]
  exact (pauliCoeff_sum_smul (fun c => T (Tower.UnitLatticeL2.basisVec ι) (c, ι'.2)) ι'.1).symm
theorem kernelOfMap_apply {N : Type} {M : (N → ℂ) → N → ℂ}
    (h : Tower.UnitGaugeDirections.IsUniqueRowFiniteKernelAction M) (ι' ι : N) :
    PeriodicOperators.kernelOfMap M ι' ι = M (Tower.UnitGaugeDirections.basisFunction ι) ι' := by apply _root_.YangMills.Construction.Tower.AbelianKernelEntries.kernelOfMap_apply <;> assumption
theorem extendOddly_of_positive (f : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    Tower.FullSpace.extendOddly f b = f b := if_pos hb
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → Matrices.ComplexMatrix2)
    (b : InfiniteLattice.Link a) :
    Tower.FullSpace.extendOddly f b.opposite = -Tower.FullSpace.extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
variable {L : ℕ}
theorem meshAt_pos (L : ℕ) : 0 < Tower.meshAt L 0 0 := by apply _root_.YangMills.Construction.Tower.TwoOperatorKernelProducts.meshAt_zero_pos <;> assumption
theorem unitForm_mem (ι : Fin 3 × Tower.FullSpace.PositiveEdge (Tower.meshAt L 0 0)) :
    (unitForm ι : Tower.FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2) ∈
      Tower.HessianKernel.finiteSupportComplexForms L 0 0 := by
  classical
  have hp : ∀ c : Tower.FullSpace.Edge L 0 0, c.IsPositivelyOriented →
      unitForm ι c = if c = ι.2.1 then Matrices.ComplexMatrix2.pauliFamily ι.1 else 0 :=
    fun c hc => extendOddly_of_positive _ hc
  refine ⟨⟨fun c hc => ?_, fun c => extendOddly_opposite (meshAt_pos L) _ c⟩, ?_⟩
  · rw [hp c hc]
    split_ifs
    · exact pauliFamily_mem_traceless _
    · exact Matrices.ComplexMatrix2.traceless.zero_mem
  · refine (Set.finite_singleton ι.2.1).subset ?_
    rintro c ⟨hc, hne⟩
    by_contra h
    apply hne
    rw [hp c hc, if_neg fun e => h (Set.mem_singleton_iff.mpr e)]
theorem add_mem_finiteSupport {B B' : Tower.FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2}
    (h : B ∈ Tower.HessianKernel.finiteSupportComplexForms L 0 0)
    (h' : B' ∈ Tower.HessianKernel.finiteSupportComplexForms L 0 0) :
    B + B' ∈ Tower.HessianKernel.finiteSupportComplexForms L 0 0 := by apply _root_.YangMills.Construction.Tower.AbelianKernelEntries.add_mem_finiteSupportComplexForms <;> assumption
theorem complexHessianKernel_eq_polar {U : Tower.FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2}
    (hB : Tower.HessianKernel.IsSymmBilinearOn (Tower.HessianKernel.finiteSupportComplexForms L 0 0)
      (Tower.FullSpace.complexActionHessian U))
    (hS : ∀ C ∈ Tower.HessianKernel.finiteSupportComplexForms L 0 0,
      faceQuadratic U C = Tower.FullSpace.complexActionHessian U C C) :
    Tower.FullSpace.complexHessianKernel U = polarKernel U := by
  funext ι' ι
  have m' := unitForm_mem ι'
  have m := unitForm_mem ι
  have ms := add_mem_finiteSupport m' m
  have h₁ := (hB 1 _ m' _ m _ ms).1
  have h₂ := (hB 1 _ m' _ m _ m').2.1
  have h₃ := (hB 1 _ m' _ m _ m).2.1
  have h₄ := (hB 1 _ m' _ m _ m).2.2
  rw [one_smul] at h₁ h₂ h₃
  show Tower.FullSpace.complexActionHessian U (unitForm ι') (unitForm ι) = _
  unfold polarKernel
  rw [hS _ ms, hS _ m', hS _ m, h₁, h₂, h₃, ← h₄]
  ring
theorem massiveHessian_eq_hessianOf {U : Tower.FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2}
    (h : Tower.FullSpace.complexHessianKernel U = polarKernel U)
    (B : Tower.FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2) :
    Tower.FullSpace.massiveHessian U B = hessianOf U B := by
  unfold Tower.FullSpace.massiveHessian hessianOf Tower.FullSpace.complexHessianOperator
  rw [h]
  rfl
end Spacing
theorem entries_eq (hOps : Tower.AbelianOperatorsLocalSelfAdjoint)
    (hPlaquettes : Tower.AbelianFieldPlaquettes.Claim)
    (hGauge : Tower.UnitGaugeDirections.Claim)
    (hSecond : Tower.HessianKernel.KernelProperties)
    (hDerivatives : Tower.FaceTermDerivatives.Statement)
    (L : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (θ : Tower.FullSpace.PositiveEdge (Tower.meshAt L 0 0) → ℝ) :
    (∀ ι' ι, Tower.AbelianFieldFacts.abelianLaplacianKernel θ ι' ι = vertexEntry θ ι' ι) ∧
    (∀ ι' ι, Tower.AbelianFieldFacts.abelianHessianKernel θ ι' ι = edgeEntry θ ι' ι) ∧
    (∀ ι' ι, Tower.UnitLatticeL2.matrixEntry (Tower.AbelianFieldDensity.laplacianOp θ) ι' ι =
      vertexEntry θ ι' ι) ∧
    (∀ ι' ι, Tower.UnitLatticeL2.matrixEntry (Tower.AbelianFieldDensity.massiveOp θ) ι' ι =
      edgeEntry θ ι' ι) := by
  have hU : Tower.FullSpace.abelianLinkField θ ∈
      Tower.FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup := by
    have h := (hPlaquettes L hL θ).abelianLinkField_mem
    exact ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.1 (h.1 b)).2, h.2⟩
  have hK := ((hGauge L hL).2 _ hU).2.2.2
  have hA : Tower.FullSpace.complexHessianKernel (Tower.FullSpace.abelianLinkField θ) =
      polarKernel (Tower.FullSpace.abelianLinkField θ) :=
    complexHessianKernel_eq_polar ((hSecond L hL 0 0 le_rfl).2 _ hU).1 fun C hC =>
      ((((hDerivatives L hL 0 0 le_rfl).2 C hC.1).2 hC.2).1 _ hU).1
  have hM := massiveHessian_eq_hessianOf hA
  have hO := hOps L hL θ
  refine ⟨fun ι' ι => kernelOfMap_apply hK.1 ι' ι, fun ι' ι => ?_, fun ι' ι => ?_, fun ι' ι => ?_⟩
  · refine (kernelOfMap_apply hK.2 ι' ι).trans ?_
    exact congrArg (fun X : Tower.FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2 =>
      Tower.pauliCoeff ι'.1 (X ι'.2.1)) (hM _)
  · exact matrixEntry_eq_of_apply _ _ hO.laplacian_apply ι' ι
  · refine (matrixEntry_eq_of_apply (fun g b => Tower.FullSpace.abelianMassiveHessian θ
      (Tower.AbelianFieldDensity.formOfPositiveValues g) b.1) _ hO.hessian_apply ι' ι).trans ?_
    exact congrArg (fun X : Tower.FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2 =>
      Tower.pauliCoeff ι'.1 (X ι'.2.1)) (hM _)
theorem abelianOperatorsLocallySmooth (hOps : Tower.AbelianOperatorsLocalSelfAdjoint)
    (hEntries : Tower.AbelianKernelEntries.EntriesAreTrigPolynomials)
    (hPlaquettes : Tower.AbelianFieldPlaquettes.Claim)
    (hGauge : Tower.UnitGaugeDirections.Claim)
    (hSecond : Tower.HessianKernel.KernelProperties)
    (hDerivatives : Tower.FaceTermDerivatives.Statement)
    (hSquare : Tower.UnitLatticeL2Statement)
    (hIndex : PeriodicOperators.TowerIndexSets.Claim) :
    Tower.LocalFamilies.AbelianOperatorsLocallySmooth := by
  have h₀ : Conventions.IsAdmissibleBlockingFactor 13 := ⟨by decide, le_rfl⟩
  have hE := entries_eq hOps hPlaquettes hGauge hSecond hDerivatives
  obtain ⟨-, ⟨-, -, -, hiS, -, -⟩, ⟨-, -, -, hiB, -, -⟩⟩ := hSquare.2 13
  have hSets := hIndex 13 h₀ 0 0 le_rfl
  have hTail : ∀ (ζ : Fin 4 → ℤ) (b : PeriodicOperators.PosEdge 13 0 0),
      (((PeriodicOperators.shiftEdge ζ b).1.initial : InfiniteLattice.AmbientSpace)) =
        (b.1.initial : InfiniteLattice.AmbientSpace) + PeriodicOperators.castVec ζ :=
    fun ζ b => hSets.2.1.pos_translate ζ ((0 : Fin 3), b)
  obtain ⟨C₁, hC₁, hl₁⟩ := isNearKernel_of_trigPoly hSets.1 (fun ι => (hiS.2 ι.2).1) hTail
    Tower.AbelianFieldFacts.abelianLaplacianKernel (hEntries 13 h₀).laplacian
    fun θ => (hOps 13 h₀ θ).laplacian_range
  obtain ⟨C₂, hC₂, hl₂⟩ := isNearKernel_of_trigPoly hSets.2.1
    (fun ι => (hiB.2 ι.2.1.initial).1) hTail
    Tower.AbelianFieldFacts.abelianHessianKernel (hEntries 13 h₀).hessian
    fun θ => (hOps 13 h₀ θ).hessian_range
  have s₀ : IsNearKernel vertexPos (vertexEntry (a := Tower.meshAt 13 0 0)) C₁ := fun ι' ι => by
    obtain ⟨E, Q, q₁, q₂, q₃⟩ := hl₁ ι' ι
    exact ⟨E, Q, q₁, q₂, fun θ => ((hE 13 h₀ θ).1 ι' ι).symm.trans (q₃ θ)⟩
  have b₀ : IsNearKernel edgePos (edgeEntry (a := Tower.meshAt 13 0 0)) C₂ := fun ι' ι => by
    obtain ⟨E, Q, q₁, q₂, q₃⟩ := hl₂ ι' ι
    exact ⟨E, Q, q₁, q₂, fun θ => ((hE 13 h₀ θ).2.1 ι' ι).symm.trans (q₃ θ)⟩
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, fun L hL => ?_⟩
  have hs : Tower.meshAt L 0 0 = Tower.meshAt 13 0 0 := by simp [Tower.meshAt]
  have s₁ : IsNearKernel vertexPos (vertexEntry (a := Tower.meshAt L 0 0)) (max C₁ C₂) := by
    rw [hs]
    exact s₀.mono (le_max_left _ _)
  have b₁ : IsNearKernel edgePos (edgeEntry (a := Tower.meshAt L 0 0)) (max C₁ C₂) := by
    rw [hs]
    exact b₀.mono (le_max_right _ _)
  refine ⟨⟨fun θ => (hOps L hL θ).laplacian_isSelfAdjoint, fun θ ι' ι h => ?_, fun ι' ι => ?_⟩,
    ⟨fun θ => (hOps L hL θ).hessian_isSelfAdjoint, fun θ ι' ι h => ?_, fun ι' ι => ?_⟩⟩
  · rw [(hE L hL θ).2.2.1, ← (hE L hL θ).1]
    exact (hOps L hL θ).laplacian_range ι' ι h
  · obtain ⟨E, Q, q₁, q₂, q₃⟩ := s₁ ι' ι
    exact ⟨E, Q, q₁, q₂.1, q₂.2, fun θ => ((hE L hL θ).2.2.1 ι' ι).trans (q₃ θ)⟩
  · rw [(hE L hL θ).2.2.2, ← (hE L hL θ).2.1]
    exact (hOps L hL θ).hessian_range ι' ι h
  · obtain ⟨E, Q, q₁, q₂, q₃⟩ := b₁ ι' ι
    exact ⟨E, Q, q₁, q₂.1, q₂.2, fun θ => ((hE L hL θ).2.2.2 ι' ι).trans (q₃ θ)⟩
end YangMills.Construction.Tower.LocalFamilies.AbelianLocality
end
