import YangMills.Construction.TorusOrFourSpace.CoefficientsOfTestFunctionsOnThePeriodBoxProof
import YangMills.Construction.TorusOrFourSpace.ModesOfACutOffOnThePeriodBox
import YangMills.Construction.TorusOrFourSpace.PartialsOfSumsAndProducts
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PeriodCell
namespace CutoffModeLemmas
variable (D : Params)
def asFourPoint (x : Coords 1) : Kind.euclidean.Pt D := x
theorem singleRead_apply {Z : Type*} (φ : Kind.euclidean.Pt D → Z) (x : Coords 1) :
    (Kind.Tuple.ofSingle D Kind.euclidean φ ∘ Kind.Tuple.proj D Kind.euclidean) x =
      φ (asFourPoint D x) := by
  have h : Coords.block x ⟨0, (1 : ℕ+).pos⟩ = x := by
    funext μ
    show x ⟨4 * 0 + (μ : ℕ), _⟩ = x μ
    congr 1
    apply Fin.ext
    simp
  show φ (Kind.quotMap D Kind.euclidean (Coords.block x ⟨0, (1 : ℕ+).pos⟩)) = _
  rw [h]
  rfl
theorem fin_one_index_eq (i : Fin ((1 : ℕ+) : ℕ)) : i = ⟨0, (1 : ℕ+).pos⟩ :=
  Fin.ext (Nat.lt_one_iff.mp (by simpa using i.2))
theorem iterPartial_zero {p : ℕ+} (G : Coords p → ℂ) :
    Coords.iterPartial (0 : CoordIndex p) G = G := by apply _root_.YangMills.Construction.ToriLimits.GrowingVolumeLimits.ProofSteps.MirrorStep.FlatReading.iterPartial_zero <;> assumption
theorem degree_le_one_cases {p : ℕ+} (α : CoordIndex p) (h : α.degree ≤ 1) :
    α = 0 ∨ ∃ j, α = Pi.single j 1 := by
  by_cases h0 : ∀ j, α j = 0
  · exact Or.inl (funext h0)
  · obtain ⟨j, hj⟩ := not_forall.mp h0
    refine Or.inr ⟨j, ?_⟩
    have hsum : α j + ∑ i ∈ Finset.univ.erase j, α i ≤ 1 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      exact h
    funext i
    by_cases hij : i = j
    · subst hij
      simp only [Pi.single_eq_same]
      omega
    · have hle : α i ≤ ∑ i ∈ Finset.univ.erase j, α i :=
        Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _)
          (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
      rw [Pi.single_eq_of_ne hij]
      omega
def phaseRate (P : ℝ) : ℂ := 2 * Real.pi * Complex.I / (P : ℂ)
theorem fourierChar_eq_exp {p : ℕ+} (P : ℝ) (k : IntCoords p) (x : Coords p) :
    fourierChar P k x = Complex.exp (phaseRate P * ((k.pairing x : ℝ) : ℂ)) := by
  unfold fourierChar phaseRate
  congr 1
  ring
theorem pairing_add_smul_single {p : ℕ+} (k : IntCoords p) (x : Coords p)
    (j : Fin (4 * (p : ℕ))) (t : ℝ) :
    k.pairing (x + t • Pi.single j 1) = k.pairing x + t * (k j : ℝ) := by apply _root_.YangMills.Construction.PeriodicSpace.PeriodCell.Fourier.pairing_add_smul_single <;> assumption
theorem fourierChar_contDiff {p : ℕ+} (P : ℝ) (k : IntCoords p) :
    ContDiff ℝ ⊤ (fourierChar P k) := by
  have h1 : ContDiff ℝ ⊤ fun x : Coords p => k.pairing x := by
    unfold IntCoords.pairing
    fun_prop
  have h2 : ContDiff ℝ ⊤ fun x : Coords p => ((k.pairing x : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp h1
  have h3 : ContDiff ℝ ⊤ fun x : Coords p =>
      Complex.exp (phaseRate P * ((k.pairing x : ℝ) : ℂ)) :=
    (contDiff_const.mul h2).cexp
  have h4 : fourierChar P k = fun x : Coords p =>
      Complex.exp (phaseRate P * ((k.pairing x : ℝ) : ℂ)) := by
    funext x
    exact fourierChar_eq_exp P k x
  rw [h4]
  exact h3
theorem partialAlong_fourierChar {p : ℕ+} (P : ℝ) (k : IntCoords p)
    (j : Fin (4 * (p : ℕ))) :
    Coords.partialAlong j (fourierChar P k) =
      fun x => (phaseRate P * ((k j : ℝ) : ℂ)) * fourierChar P k x := by
  funext x
  have hline : HasLineDerivAt ℝ (fourierChar P k)
      ((phaseRate P * ((k j : ℝ) : ℂ)) * fourierChar P k x) x (Pi.single j 1) := by
    unfold HasLineDerivAt
    have hfun : (fun t : ℝ => fourierChar P k (x + t • Pi.single j 1)) =
        fun t : ℝ => (fun z : ℂ => Complex.exp (phaseRate P * ((k.pairing x : ℝ) : ℂ) +
          phaseRate P * ((k j : ℝ) : ℂ) * z)) (t : ℂ) := by
      funext t
      rw [fourierChar_eq_exp, pairing_add_smul_single]
      congr 1
      push_cast
      ring
    rw [hfun]
    have hc : HasDerivAt (fun z : ℂ => Complex.exp (phaseRate P * ((k.pairing x : ℝ) : ℂ) +
        phaseRate P * ((k j : ℝ) : ℂ) * z))
        ((phaseRate P * ((k j : ℝ) : ℂ)) * fourierChar P k x) ((0 : ℝ) : ℂ) := by
      have hlin : HasDerivAt (fun z : ℂ => phaseRate P * ((k.pairing x : ℝ) : ℂ) +
          phaseRate P * ((k j : ℝ) : ℂ) * z) (phaseRate P * ((k j : ℝ) : ℂ)) ((0 : ℝ) : ℂ) := by
        simpa using ((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul
          (phaseRate P * ((k j : ℝ) : ℂ))).const_add (phaseRate P * ((k.pairing x : ℝ) : ℂ))
      have hexp := hlin.cexp
      have hval : Complex.exp (phaseRate P * ((k.pairing x : ℝ) : ℂ) +
          phaseRate P * ((k j : ℝ) : ℂ) * ((0 : ℝ) : ℂ)) = fourierChar P k x := by
        rw [fourierChar_eq_exp]
        simp
      rw [hval] at hexp
      exact hexp.congr_deriv (mul_comm _ _)
    exact hc.comp_ofReal
  exact hline.lineDeriv
theorem norm_fourierChar {p : ℕ+} (P : ℝ) (k : IntCoords p) (x : Coords p) :
    ‖fourierChar P k x‖ = 1 := by apply _root_.YangMills.Construction.PeriodicSpace.PeriodCell.Fourier.norm_fourierChar <;> assumption
theorem abs_coord_le_intVecNorm (κ : Fin 4 → ℤ) (μ : Fin 4) :
    |(κ μ : ℝ)| ≤ intVecNorm κ := by
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun μ => (κ μ : ℝ) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ μ)
theorem norm_phaseRate_mul_le {ρ : ℝ} (hρ : 0 < ρ) (κ : Fin 4 → ℤ) (μ : Fin 4) :
    ‖phaseRate (4 * ρ) * ((κ μ : ℝ) : ℂ)‖ ≤ intVecNorm κ / cutoffScale ρ := by
  have hπ := Real.pi_pos
  have hval : ‖phaseRate (4 * ρ) * ((κ μ : ℝ) : ℂ)‖ = |(κ μ : ℝ)| / cutoffScale ρ := by
    unfold phaseRate cutoffScale
    rw [norm_mul, norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hπ, abs_of_pos (by positivity : (0 : ℝ) < 4 * ρ)]
    simp only [Complex.norm_ofNat]
    field_simp
    ring
  rw [hval]
  exact div_le_div_of_nonneg_right (abs_coord_le_intVecNorm κ μ)
    (by unfold cutoffScale; positivity)
theorem ofReal_add_mul_le_mul {N : ℝ≥0∞} {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (haN : ENNReal.ofReal a ≤ N) (hbN : ENNReal.ofReal b ≤ N) :
    ENNReal.ofReal (a + b * c) ≤ N * ENNReal.ofReal (1 + c) := by
  have hm : ENNReal.ofReal (max a b) ≤ N := by
    rcases le_total a b with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  have hle : a + b * c ≤ max a b * (1 + c) := by
    have h1 := le_max_left a b
    have h2 := le_max_right a b
    nlinarith
  calc ENNReal.ofReal (a + b * c) ≤ ENNReal.ofReal (max a b * (1 + c)) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal (max a b) * ENNReal.ofReal (1 + c) :=
        ENNReal.ofReal_mul (le_max_of_le_left ha)
    _ ≤ N * ENNReal.ofReal (1 + c) := by gcongr
end CutoffModeLemmas
open CutoffModeLemmas in
theorem cutoffModeBounds_holds (hPartials : SumsProductsPartials.LeibnizRules)
    (hPoints : TupleFacts.AllFacts)
    (hContDiff : ContPartialsIffContDiff) :
    CutoffModeBounds := by
  intro D ρ hρ O hO hOB
  obtain ⟨hOnto, -, -, -, -, -, -, -, -, -, -, hProd, -, -, hDer, -, -, -, -, hStable, -, -, -, -⟩ :=
    hPoints D Kind.euclidean 1
  have hOpen : Kind.Tuple.IsOpenT D Kind.euclidean (Kind.Tuple.singleSet D Kind.euclidean O) := by
    have h := ((hProd fun _ => O).1) fun _ => hO
    have he : Kind.Tuple.boxSet D Kind.euclidean (fun _ : Fin ((1 : ℕ+) : ℕ) => O) =
        Kind.Tuple.singleSet D Kind.euclidean O := by
      ext y
      constructor
      · intro hy
        exact hy _
      · intro hy i
        rw [fin_one_index_eq i]
        exact hy
    rwa [he] at h
  have hChar : ∀ κ : Fin 4 → ℤ, ∀ ν, Coords.ContPartialsUpTo ν
      (Kind.Tuple.ofSingle D Kind.euclidean (fourierCharR4 (4 * ρ) κ) ∘
        Kind.Tuple.proj D Kind.euclidean) := by
    intro κ ν
    have he : Kind.Tuple.ofSingle D Kind.euclidean (fourierCharR4 (4 * ρ) κ) ∘
        Kind.Tuple.proj D Kind.euclidean = fourierChar (p := 1) (4 * ρ) κ := by
      funext x
      exact singleRead_apply D _ x
    rw [he]
    exact (hContDiff 1 ν _).2
      ((fourierChar_contDiff (p := 1) _ κ).of_le (by exact_mod_cast le_top))
  refine ⟨?_, fun κ ν => hChar κ ν, ?_⟩
  · intro φ hφ
    exact ⟨hφ.1, hφ.2.1, hφ.2.2.trans fun y hy => hOB hy⟩
  intro χ hχ
  refine ⟨?_, ?_⟩
  · intro G hG
    refine ⟨?_, ?_⟩
    · have h := ((hStable _ hOpen).2 _ hχ).2.2.2.1 _ hG
      have he : Kind.Tuple.ofSingle D Kind.euclidean (fun y => (χ y : ℂ) * G y) =
          Kind.Tuple.ofSingle D Kind.euclidean G *
            Kind.Tuple.ofSingle D Kind.euclidean fun y => (χ y : ℂ) := by
        funext y
        exact mul_comm _ _
      show Kind.Tuple.ofSingle D Kind.euclidean (fun y => (χ y : ℂ) * G y) ∈
        Kind.Tuple.testFns D Kind.euclidean (Kind.Tuple.singleSet D Kind.euclidean O)
      rw [he]
      exact h
    · intro y hy r hr
      obtain ⟨z, hz, hd⟩ := hy r hr
      refine ⟨z, ?_, hd⟩
      intro h0
      apply hz
      simp [show χ z = 0 from h0]
  intro κ
  set X : Coords 1 → ℂ :=
    Kind.Tuple.ofSingle D Kind.euclidean (fun y => (χ y : ℂ)) ∘ Kind.Tuple.proj D Kind.euclidean
    with hXdef
  set C : Coords 1 → ℂ := fourierChar (p := 1) (4 * ρ) κ with hCdef
  have hCread : Kind.Tuple.ofSingle D Kind.euclidean (fourierCharR4 (4 * ρ) κ) ∘
      Kind.Tuple.proj D Kind.euclidean = C := by
    funext x
    exact singleRead_apply D _ x
  have hXall : Coords.HasSmoothPartials X := hχ.1
  have hCall : Coords.HasSmoothPartials C := fun ν => hCread ▸ hChar κ ν
  have hMread : Kind.Tuple.ofSingle D Kind.euclidean (cutoffMode D (4 * ρ) χ κ) ∘
      Kind.Tuple.proj D Kind.euclidean = X * C := by
    funext x
    rw [singleRead_apply, Pi.mul_apply, hXdef, singleRead_apply, hCdef]
    rfl
  obtain ⟨-, hXCall, -, -, -, -, hRule, -⟩ := hPartials 1 X C hXall hCall
  have hMclass : Kind.Tuple.IsClassC D Kind.euclidean 1
      (Kind.Tuple.ofSingle D Kind.euclidean (cutoffMode D (4 * ρ) χ κ)) := by
    show Coords.ContPartialsUpTo 1 _
    rw [hMread]
    exact hXCall 1
  have hXclass : Kind.Tuple.IsClassC D Kind.euclidean 1
      (Kind.Tuple.ofSingle D Kind.euclidean fun y => (χ y : ℂ)) := hχ.1 1
  set N : ℝ≥0∞ := Kind.Tuple.c1NormSingleReal D Kind.euclidean χ with hNdef
  have hc : 0 ≤ intVecNorm κ / cutoffScale ρ := by
    unfold intVecNorm cutoffScale
    have := Real.pi_pos
    positivity
  unfold Kind.Tuple.c1NormSingle Kind.Tuple.cNorm
  refine iSup_le fun α => iSup_le fun hα => iSup_le fun y => ?_
  obtain ⟨x, rfl⟩ := hOnto.1 y
  have hM : Kind.Tuple.partialDeriv D Kind.euclidean α
      (Kind.Tuple.ofSingle D Kind.euclidean (cutoffMode D (4 * ρ) χ κ))
      (Kind.Tuple.proj D Kind.euclidean x) = Coords.iterPartial α (X * C) x := by
    have h := congrFun (hDer 1 _ hMclass α hα).2.1 x
    rw [hMread] at h
    exact h
  have hXN : ∀ β : CoordIndex 1, β.degree ≤ 1 →
      ENNReal.ofReal ‖Coords.iterPartial β X x‖ ≤ N := by
    intro β hβ
    have h := congrFun (hDer 1 _ hXclass β hβ).2.1 x
    have h' : Coords.iterPartial β X x = Kind.Tuple.partialDeriv D Kind.euclidean β
        (Kind.Tuple.ofSingle D Kind.euclidean fun y => (χ y : ℂ))
        (Kind.Tuple.proj D Kind.euclidean x) :=
      h.symm
    rw [h']
    exact le_iSup_of_le β
      (le_iSup_of_le hβ (le_iSup_of_le (Kind.Tuple.proj D Kind.euclidean x) le_rfl))
  have hX0 : ENNReal.ofReal ‖X x‖ ≤ N := by
    have h0 : (0 : CoordIndex 1).degree = 0 := Finset.sum_eq_zero fun _ _ => rfl
    have h := hXN 0 (by omega)
    rwa [iterPartial_zero] at h
  rw [hM]
  rcases degree_le_one_cases α hα with rfl | ⟨j, rfl⟩
  · have hCx : ‖C x‖ = 1 := norm_fourierChar (p := 1) _ κ x
    rw [iterPartial_zero, Pi.mul_apply, norm_mul, hCx, mul_one]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (ofReal_add_mul_le_mul (norm_nonneg _) hc hX0 hX0)
    have := mul_nonneg (norm_nonneg (X x)) hc
    linarith
  · have hXj : ENNReal.ofReal ‖Coords.partialAlong j X x‖ ≤ N := by
      have h := hXN (Pi.single j 1) hα
      have he := (hPartials 1 X C hXall hCall).2.2.2.2.2.1 j
      rwa [he] at h
    have hCj := partialAlong_fourierChar (p := 1) (4 * ρ) κ j
    have hnorm : ‖(Coords.partialAlong j X * C + X * Coords.partialAlong j C) x‖ ≤
        ‖Coords.partialAlong j X x‖ + ‖X x‖ * (intVecNorm κ / cutoffScale ρ) := by
      have hCx : ‖C x‖ = 1 := norm_fourierChar (p := 1) _ κ x
      have hCjx : Coords.partialAlong j C x = (phaseRate (4 * ρ) * ((κ j : ℝ) : ℂ)) * C x :=
        congrFun hCj x
      rw [Pi.add_apply, Pi.mul_apply, Pi.mul_apply, hCjx]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, hCx, mul_one, mul_one]
      gcongr
      exact norm_phaseRate_mul_le hρ κ j
    rw [(hPartials 1 (X * C) C hXCall hCall).2.2.2.2.2.1 j, hRule j]
    exact (ENNReal.ofReal_le_ofReal hnorm).trans
      (ofReal_add_mul_le_mul (norm_nonneg _) hc hXj hX0)
end YangMills.Construction.PeriodicSpace.PeriodCell
