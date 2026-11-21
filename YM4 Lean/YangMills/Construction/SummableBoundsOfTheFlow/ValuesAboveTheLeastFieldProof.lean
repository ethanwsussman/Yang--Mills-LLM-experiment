import YangMills.Construction.SummableBoundsOfTheFlow.HaarTermIsBoundedProof
import YangMills.Construction.SummableBoundsOfTheFlow.BondsAtACell
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesAlongParametersOfAFamilyProofForm
import YangMills.Construction.SummableBoundsOfTheFlow.LeastChartEnergyIsSmoothProof
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesInTheLawsBetweenProof
import YangMills.Construction.SummableBoundsOfTheFlow.ValuesAboveTheLeastField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ValuesAboveMinimizer
section
open Set Filter Topology
section
variable {E G H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
theorem iteratedFDeriv_succ_cons_apply {n : ℕ} {f : E → H} {x : E} (hf : ContDiffAt ℝ (n + 1 : ℕ) f x)
    (a : E) (u : Fin n → E) :
    iteratedFDeriv ℝ (n + 1) f x (Fin.cons a u) =
      fderiv ℝ (fun y => iteratedFDeriv ℝ n f y u) x a := by apply _root_.YangMills.Construction.ParameterListDerivatives.iteratedFDeriv_succ_cons_eq_fderiv <;> assumption
theorem contDiffAt_iteratedFDeriv_apply {n m i : ℕ} {f : E → H} {x : E} (hf : ContDiffAt ℝ n f x)
    (hmn : m + i ≤ n) (u : Fin i → E) :
    ContDiffAt ℝ m (fun y => iteratedFDeriv ℝ i f y u) x := by apply _root_.YangMills.Construction.ParameterListDerivatives.contDiffAt_iteratedFDeriv_eval <;> assumption
theorem iteratedFDeriv_comp_add_const {n : ℕ} {f : E → H} (L : G →L[ℝ] E) (a : E) {x : G}
    (hf : ContDiffAt ℝ n f (L x + a)) {i : ℕ} (hi : i ≤ n) (v : Fin i → G) :
    iteratedFDeriv ℝ i (fun z => f (L z + a)) x v = iteratedFDeriv ℝ i f (L x + a) fun j => L (v j) := by apply _root_.YangMills.SharedProofs.p13665 <;> assumption
end
section
variable {E₁ E₂ H : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂] [NormedAddCommGroup H] [NormedSpace ℝ H]
def partialJetSnd (f : E₁ × E₂ → H) (y : E₂) {k : ℕ} (w : Fin k → E₂) (x : E₁) : H :=
  iteratedFDeriv ℝ k (fun y' => f (x, y')) y w
theorem partialJetSnd_eq {n k : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂} (hf : ContDiffAt ℝ n f (x, y))
    (hk : k ≤ n) (w : Fin k → E₂) :
    partialJetSnd f y w x = iteratedFDeriv ℝ k f (x, y) fun j => (0, w j) := by
  have h := iteratedFDeriv_comp_add_const (ContinuousLinearMap.inr ℝ E₁ E₂) (x, 0) (x := y) (f := f)
    (by simpa using hf) hk w
  have e1 : (fun z => f ((ContinuousLinearMap.inr ℝ E₁ E₂) z + (x, 0))) = fun y' => f (x, y') := by
    funext z; simp
  rw [e1] at h
  simp only [partialJetSnd]
  rw [h]
  simp
theorem contDiffAt_eventually_fst {n : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂} (hf : ContDiffAt ℝ n f (x, y)) :
    ∀ᶠ x' in 𝓝 x, ContDiffAt ℝ n f (x', y) := by apply _root_.YangMills.Construction.ParameterListDerivatives.eventually_contDiffAt_left <;> assumption
theorem contDiffAt_partialJetSnd {n m k : ℕ} {f : E₁ × E₂ → H} {x : E₁} {y : E₂}
    (hf : ContDiffAt ℝ n f (x, y)) (hmn : m + k ≤ n) (w : Fin k → E₂) :
    ContDiffAt ℝ m (partialJetSnd f y w) x := by
  have h1 : ContDiffAt ℝ m (fun z => iteratedFDeriv ℝ k f z fun j => (0, w j)) (x, y) :=
    contDiffAt_iteratedFDeriv_apply hf hmn _
  have h2 : ContDiffAt ℝ m (fun x' : E₁ => (x', y)) x := by fun_prop
  have h3 : ContDiffAt ℝ m (fun x' => iteratedFDeriv ℝ k f (x', y) fun j => (0, w j)) x :=
    ContDiffAt.comp x (g := fun z => iteratedFDeriv ℝ k f z fun j => (0, w j)) h1 h2
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [contDiffAt_eventually_fst hf] with x' hx'
  exact partialJetSnd_eq hx' (by omega) w
def IsConcatVectors {m p k : ℕ} (v : Fin p → E₁) (w : Fin k → E₂) (u : Fin m → E₁ × E₂) : Prop :=
  m = p + k ∧ (∀ (i : Fin m) (hi : i.val < p), u i = (v ⟨i.val, hi⟩, 0)) ∧
    ∀ (i : Fin m) (hi : p ≤ i.val) (hk : i.val - p < k), u i = (0, w ⟨i.val - p, hk⟩)
theorem iteratedFDeriv_partialJetSnd {k : ℕ} (w : Fin k → E₂) {n : ℕ} {f : E₁ × E₂ → H} {y : E₂} :
    ∀ (p m : ℕ) (v : Fin p → E₁) (u : Fin m → E₁ × E₂) (x : E₁), IsConcatVectors v w u →
      ContDiffAt ℝ n f (x, y) → m ≤ n →
      iteratedFDeriv ℝ p (partialJetSnd f y w) x v = iteratedFDeriv ℝ m f (x, y) u := by
  intro p
  induction p with
  | zero =>
    intro m v u x hu hf hm
    obtain ⟨h0, -, h2⟩ := hu
    have : m = k := by omega
    subst this
    have hu' : u = fun j => (0, w j) := by
      funext j
      have := h2 j (Nat.zero_le _) (by simp)
      simpa using this
    rw [hu', ← partialJetSnd_eq hf hm w]
    simp
  | succ p ih =>
    intro m v u x hu hf hm
    obtain ⟨h0, h1, h2⟩ := hu
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hR : ContDiffAt ℝ (p + 1 : ℕ) (partialJetSnd f y w) x :=
      contDiffAt_partialJetSnd hf (by omega) w
    have hf' : ContDiffAt ℝ (m' + 1 : ℕ) f (x, y) := hf.of_le (by exact_mod_cast hm)
    have hu0 : u 0 = (v 0, 0) := h1 0 (by simp)
    have ht : IsConcatVectors (Fin.tail v) w (Fin.tail u) := by
      refine ⟨by omega, fun i hi => ?_, fun i hi hk => ?_⟩
      · have := h1 i.succ (by simpa using hi)
        simpa [Fin.tail_def] using this
      · have := h2 i.succ (by simp; omega) (by simp; omega)
        simp only [Fin.tail_def]
        rw [this]
        congr 2
        apply Fin.ext
        simp
    have e1 := iteratedFDeriv_succ_cons_apply hR (v 0) (Fin.tail v)
    have e2 := iteratedFDeriv_succ_cons_apply hf' (u 0) (Fin.tail u)
    rw [Fin.cons_self_tail] at e1 e2
    rw [e1, e2]
    have hev : (fun x' => iteratedFDeriv ℝ p (partialJetSnd f y w) x' (Fin.tail v)) =ᶠ[𝓝 x]
        fun x' => iteratedFDeriv ℝ m' f (x', y) (Fin.tail u) := by
      filter_upwards [contDiffAt_eventually_fst hf] with x' hx'
      exact ih m' _ _ x' ht hx' (by omega)
    rw [hev.fderiv_eq, hu0]
    have hd : DifferentiableAt ℝ (fun z => iteratedFDeriv ℝ m' f z (Fin.tail u)) (x, y) :=
      (contDiffAt_iteratedFDeriv_apply (m := 1) hf (by omega) _).differentiableAt (by norm_num)
    have hc : HasFDerivAt (fun x' : E₁ => (x', y)) (ContinuousLinearMap.inl ℝ E₁ E₂) x :=
      hasFDerivAt_prodMk_left x y
    have := (hd.hasFDerivAt.comp x hc).fderiv
    have e3 : (fun x' => iteratedFDeriv ℝ m' f (x', y) (Fin.tail u)) =
      (fun z => iteratedFDeriv ℝ m' f z (Fin.tail u)) ∘ fun x' : E₁ => (x', y) := rfl
    rw [e3, this]
    simp
end
end
section
open Set Filter Topology
open BlockAverages ColdStepAtMirrorFrames Interpolation
variable {F : BlockFrame}
def translatedTop {Zp : Type} (G : Zp → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (p : Zp × (Fin k → ℝ)) : ℝ :=
  G p.1 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X p.2) V)
abbrev basisVectors (k : ℕ) : Fin k → Fin k → ℝ := fun l => Pi.single l 1
def jointMoveMap {l : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F))) (e : Fin l → EuclideanSpace ℝ (Fin 3))
    (k : ℕ) : (Fin (l + k) → ℝ) →L[ℝ] StepVariable (finiteCells F) × (Fin k → ℝ) :=
  ContinuousLinearMap.prod
    (∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (l + k) => ℝ) (Fin.castAdd k i)).smulRight
      (bondVariation (b i) (e i)))
    (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.natAdd l j))
theorem jointDisplacement_eq {l k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (e : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) :
    jointDisplacement G η V b e c X = fun τ => translatedTop G V c X (jointMoveMap b e k τ + (η, 0)) := by
  funext τ
  simp only [jointDisplacement, translatedTop, jointMoveMap, displacedPoint]
  congr 1
  · simp only [ContinuousLinearMap.prod_apply, Prod.fst_add, sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [bondVariation]
    rw [Pi.single_smul]
  · congr 2
    funext j
    simp
theorem jointMoveMap_castAdd {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (e : Fin l → EuclideanSpace ℝ (Fin 3)) (i : Fin l) :
    jointMoveMap b e k (Pi.single (Fin.castAdd k i) 1) = (bondVariation (b i) (e i), 0) := by
  simp only [jointMoveMap, ContinuousLinearMap.prod_apply, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  refine Prod.ext ?_ ?_
  · simp only
    rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hne
      have : Fin.castAdd k i' ≠ Fin.castAdd k i := fun h => hne (Fin.castAdd_injective _ _ h)
      simp [Pi.single_apply, this]
    · simp
  · funext j
    have : Fin.natAdd l j ≠ Fin.castAdd k i := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [Pi.single_apply, this]
theorem jointMoveMap_natAdd {l k : ℕ} (b : Fin l → ↥(chordBonds (finiteCells F)))
    (e : Fin l → EuclideanSpace ℝ (Fin 3)) (j : Fin k) :
    jointMoveMap b e k (Pi.single (Fin.natAdd l j) 1) = (0, Pi.single j 1) := by
  simp only [jointMoveMap, ContinuousLinearMap.prod_apply, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  refine Prod.ext ?_ ?_
  · simp only
    refine Finset.sum_eq_zero fun i _ => ?_
    have : Fin.castAdd k i ≠ Fin.natAdd l j := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [Pi.single_apply, this]
  · funext j'
    by_cases h : j' = j
    · subst h; simp
    · have : Fin.natAdd l j' ≠ Fin.natAdd l j := fun h' => h (Fin.natAdd_injective _ _ h')
      simp [this, h]
theorem jointMixedDeriv_eq_partialJetSnd {l k : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) (b : Fin l → ↥(chordBonds (finiteCells F)))
    (e : Fin l → EuclideanSpace ℝ (Fin 3)) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (hf : ContDiffAt ℝ (l + k : ℕ) (translatedTop G V c X) (η, 0)) :
    jointMixedDeriv G η V b e c X =
      iteratedFDeriv ℝ l (partialJetSnd (translatedTop G V c X) 0 (basisVectors k)) η
        fun i => bondVariation (b i) (e i) := by
  have h := iteratedFDeriv_comp_add_const (jointMoveMap b e k) (η, 0) (x := 0) (f := translatedTop G V c X)
    (by simpa using hf) le_rfl (fun i => Pi.single i 1)
  simp only [jointMixedDeriv]
  rw [jointDisplacement_eq, h]
  simp only [map_zero, zero_add]
  refine (iteratedFDeriv_partialJetSnd (basisVectors k) l (l + k) _ _ η ⟨rfl, fun i hi => ?_, fun i hi hk => ?_⟩ hf le_rfl).symm
  · have this : i = Fin.castAdd k ⟨i.val, hi⟩ := Fin.ext rfl
    have h2 := jointMoveMap_castAdd (k := k) b e ⟨i.val, hi⟩
    rwa [← this] at h2
  · have this : i = Fin.natAdd l ⟨i.val - l, hk⟩ := Fin.ext (by simp; omega)
    have h2 := jointMoveMap_natAdd (l := l) b e ⟨i.val - l, hk⟩
    rwa [← this] at h2
abbrev ChordCoord (F : BlockFrame) : Type := ↥(chordBonds (finiteCells F)) × Fin 3
def chordBasis (α : ChordCoord F) : StepVariable (finiteCells F) :=
  bondVariation α.1 (EuclideanSpace.single α.2 1)
def chordCoord (α : ChordCoord F) : StepVariable (finiteCells F) →L[ℝ] ℝ :=
  (EuclideanSpace.proj α.2).comp (ContinuousLinearMap.proj α.1)
theorem chordCoord_apply (α : ChordCoord F) (ζ : StepVariable (finiteCells F)) :
    chordCoord α ζ = ζ α.1 α.2 := rfl
theorem chord_expand (ζ : StepVariable (finiteCells F)) :
    ζ = ∑ α : ChordCoord F, chordCoord α ζ • chordBasis α := by
  funext b
  ext a
  have h1 : ∀ (b' : ↥(chordBonds (finiteCells F))) (a' : Fin 3),
      ((chordCoord (b', a') ζ • chordBasis (b', a') : StepVariable (finiteCells F)) b) a =
        if b' = b then (if a' = a then ζ b' a' else 0) else 0 := by
    intro b' a'
    simp only [chordCoord_apply, chordBasis, bondVariation, Pi.smul_apply, Pi.single_apply]
    by_cases hb : b = b'
    · subst hb
      by_cases ha : a' = a
      · subst ha; simp
      · simp [ha, Ne.symm ha]
    · simp [hb, Ne.symm hb]
  have h2 : (∑ α : ChordCoord F, chordCoord α ζ • chordBasis α) b a =
      ∑ α : ChordCoord F, ((chordCoord α ζ • chordBasis α : StepVariable (finiteCells F)) b) a := by
    simp [Finset.sum_apply]
  rw [h2, Fintype.sum_prod_type]
  simp only [h1]
  simp
def unitImaginary : imaginaryQuaternions := ⟨⟨0, 1, 0, 0⟩, rfl⟩
theorem norm_coe_unitImaginary : ‖(unitImaginary : Quaternion ℝ)‖ = 1 := by apply _root_.YangMills.Construction.ChartedEnergyRegularity.norm_coe_imaginaryUnit <;> assumption
theorem norm_unitImaginary : ‖unitImaginary‖ = 1 := norm_coe_unitImaginary
def doubledIndex (F : BlockFrame) (i : Fin (Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F))) : ChordCoord F :=
  (Fintype.equivFin (ChordCoord F)).symm
    (Fin.addCases (motive := fun _ => Fin (Fintype.card (ChordCoord F))) (fun j => j) (fun j => j) i)
def doubledBond (F : BlockFrame) (i : Fin (Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F))) :
    ↥(chordBonds (finiteCells F)) := (doubledIndex F i).1
def doubledUnit (F : BlockFrame) (i : Fin (Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F))) :
    EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (doubledIndex F i).2 1
theorem norm_doubledUnit (F : BlockFrame) (i) : ‖doubledUnit F i‖ = 1 := by
  simp [doubledUnit]
def doubledParams (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) :
    Fin ((Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F)) + (k + n)) → ℝ :=
  Fin.addCases
    (fun a => Fin.addCases (motive := fun _ => ℝ)
      (fun a₁ => chordCoord ((Fintype.equivFin (ChordCoord F)).symm a₁) (p.1 - η)) (fun _ => 0) a)
    (fun d => Fin.addCases (motive := fun _ => ℝ) (fun j => s j * p.2 j) (fun _ => 0) d)
theorem doubledParams_left (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (a : Fin (Fintype.card (ChordCoord F))) :
    doubledParams F η s n p (Fin.castAdd (k + n) (Fin.castAdd _ a)) =
      chordCoord ((Fintype.equivFin (ChordCoord F)).symm a) (p.1 - η) := by
  simp only [doubledParams, Fin.addCases_left]
theorem doubledParams_mid (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (a : Fin (Fintype.card (ChordCoord F))) :
    doubledParams F η s n p (Fin.castAdd (k + n) (Fin.natAdd _ a)) = 0 := by
  simp only [doubledParams, Fin.addCases_left, Fin.addCases_right]
theorem doubledParams_top (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (j : Fin k) :
    doubledParams F η s n p (Fin.natAdd _ (Fin.castAdd n j)) = s j * p.2 j := by
  simp only [doubledParams, Fin.addCases_left, Fin.addCases_right]
theorem doubledParams_pad (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (j : Fin n) :
    doubledParams F η s n p (Fin.natAdd _ (Fin.natAdd k j)) = 0 := by
  simp only [doubledParams, Fin.addCases_right]
theorem doubledParams_contDiff (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (doubledParams F η s n) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.addCases (fun a => ?_) (fun d => ?_) i
  · refine Fin.addCases (fun a₁ => ?_) (fun a₂ => ?_) a
    · simp only [doubledParams_left]
      exact (chordCoord _).contDiff.comp (contDiff_fst.sub contDiff_const)
    · simp only [doubledParams_mid]
      exact contDiff_const
  · refine Fin.addCases (fun j => ?_) (fun a₂ => ?_) d
    · simp only [doubledParams_top]
      exact contDiff_const.mul ((contDiff_apply ℝ ℝ j).comp contDiff_snd)
    · simp only [doubledParams_pad]
      exact contDiff_const
theorem doubledParams_base (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ) :
    doubledParams F η s n (η, 0) = 0 := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun d => ?_) i
  · refine Fin.addCases (fun a₁ => ?_) (fun a₂ => ?_) a
    · rw [doubledParams_left]; simp
    · rw [doubledParams_mid]; rfl
  · refine Fin.addCases (fun j => ?_) (fun a₂ => ?_) d
    · rw [doubledParams_top]; simp
    · rw [doubledParams_pad]; rfl
theorem displacedPoint_doubledParams (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) :
    displacedPoint η (doubledBond F) (doubledUnit F)
      (fun i => doubledParams F η s n p (Fin.castAdd (k + n) i)) = p.1 := by
  simp only [displacedPoint]
  rw [Fin.sum_univ_add]
  have h2 : ∑ i, (Pi.single (doubledBond F (Fin.natAdd _ i))
      (doubledParams F η s n p (Fin.castAdd (k + n) (Fin.natAdd _ i)) • doubledUnit F (Fin.natAdd _ i)) :
        StepVariable (finiteCells F)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [doubledParams_mid]
    simp
  rw [h2, add_zero]
  have h1 : ∀ a : Fin (Fintype.card (ChordCoord F)),
      (Pi.single (doubledBond F (Fin.castAdd _ a))
        (doubledParams F η s n p (Fin.castAdd (k + n) (Fin.castAdd _ a)) • doubledUnit F (Fin.castAdd _ a)) :
          StepVariable (finiteCells F)) =
      chordCoord ((Fintype.equivFin (ChordCoord F)).symm a) (p.1 - η) •
        chordBasis ((Fintype.equivFin (ChordCoord F)).symm a) := by
    intro a
    rw [doubledParams_left]
    simp only [doubledBond, doubledUnit, doubledIndex, Fin.addCases_left, chordBasis, bondVariation]
    rw [Pi.single_smul]
  simp only [h1]
  rw [Equiv.sum_comp (Fintype.equivFin (ChordCoord F)).symm
    (fun α => chordCoord α (p.1 - η) • chordBasis α), ← chord_expand]
  abel
theorem bondSpread_doubledParams (F : BlockFrame) (η : StepVariable (finiteCells F)) {k : ℕ} (s : Fin k → ℝ) (n : ℕ)
    (p : StepVariable (finiteCells F) × (Fin k → ℝ)) (c : Fin k → F.Site F.top × Fin 4)
    (X X' : Fin k → imaginaryQuaternions)
    (hX : ∀ j, s j • X' j = X j) (c₀ : F.Site F.top × Fin 4) (X₀ : imaginaryQuaternions) :
    ColdStepAtMirrorFrames.bondSpread
      (Fin.addCases (motive := fun _ => F.Site F.top × Fin 4) c fun _ : Fin n => c₀)
      (Fin.addCases (motive := fun _ => imaginaryQuaternions) X' fun _ : Fin n => X₀)
      (fun i => doubledParams F η s n p (Fin.natAdd _ i)) =
      ColdStepAtMirrorFrames.bondSpread c X p.2 := by
  funext y i
  simp only [ColdStepAtMirrorFrames.bondSpread]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_right, doubledParams_pad, zero_smul, ite_self, Finset.sum_const_zero, add_zero,
    Fin.addCases_left, doubledParams_top]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hX j, smul_smul, mul_comm]
theorem translatedTop_contDiffAt {n : ℕ} (G : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) {k : ℕ} (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions)
    (hG : ∀ (p : ℕ) (c' : Fin p → F.Site F.top × Fin 4) (X' : Fin p → imaginaryQuaternions), AreUnitVectors X' → n ≤ p →
      ContDiffAt ℝ n (jointDisplacement G η V (doubledBond F) (doubledUnit F) c' X') 0) :
    ContDiffAt ℝ n (translatedTop G V c X) (η, 0) := by
  classical
  set X' : Fin k → imaginaryQuaternions := fun j => if X j = 0 then unitImaginary else (‖X j‖⁻¹ : ℝ) • X j with hX'
  set s : Fin k → ℝ := fun j => ‖X j‖ with hs
  have hsX : ∀ j, s j • X' j = X j := by
    intro j
    by_cases h : X j = 0
    · simp [hs, hX', h]
    · have h0 : ‖X j‖ ≠ 0 := norm_ne_zero_iff.2 h
      simp only [hs, hX', h, if_false, smul_smul, mul_inv_cancel₀ h0, one_smul]
  have hunit : ∀ j, ‖X' j‖ = 1 := by
    intro j
    by_cases h : X j = 0
    · simp only [hX', h, if_true, norm_unitImaginary]
    · have h0 : ‖X j‖ ≠ 0 := norm_ne_zero_iff.2 h
      simp only [hX', h, if_false, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h0]
  set c₀ : F.Site F.top × Fin 4 := (0, 0)
  set cc := Fin.addCases (motive := fun _ => F.Site F.top × Fin 4) c fun _ : Fin n => c₀ with hcc
  set XX := Fin.addCases (motive := fun _ => imaginaryQuaternions) X' fun _ : Fin n => unitImaginary with hXX
  have hu : AreUnitVectors XX := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [hXX, Fin.addCases_left, hunit]
    · simp only [hXX, Fin.addCases_right, norm_unitImaginary]
  have h1 := hG (k + n) cc XX hu (by omega)
  have h2 : ContDiffAt ℝ n (doubledParams F η s n) (η, 0) :=
    ((doubledParams_contDiff F η s n).of_le (by exact_mod_cast le_top)).contDiffAt
  have h3 : ContDiffAt ℝ n (jointDisplacement G η V (doubledBond F) (doubledUnit F) cc XX) (doubledParams F η s n (η, 0)) := by
    rw [doubledParams_base]; exact h1
  have h4 := ContDiffAt.comp (η, (0 : Fin k → ℝ)) h3 h2
  refine h4.congr_of_eventuallyEq (Eventually.of_forall fun p => ?_)
  simp only [Function.comp, jointDisplacement, translatedTop]
  rw [displacedPoint_doubledParams, bondSpread_doubledParams F η s n p c X X' hsX c₀ unitImaginary]
end
section
open Set Filter Topology MeasureTheory
open scoped Quaternion
open BlockAverages ColdStepAtMirrorFrames Interpolation
variable {F : BlockFrame} {V : F.GaugeField F.top}
theorem bondSpread_zero {k j : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    ColdStepAtMirrorFrames.bondSpread c X 0 = 0 := by apply _root_.YangMills.Construction.ChartedEnergyRegularity.bondSpread_zero <;> assumption
theorem leftTranslate_zero {j : ℕ} (W : F.GaugeField j) :
    leftTranslate (0 : F.Site j → Fin 4 → imaginaryQuaternions) W = W := by apply _root_.YangMills.Construction.ChartedEnergyRegularity.leftTranslate_zero <;> assumption
theorem cellSupDist_le_diameter {P : Finset F.Cell} {u v : F.Cell} (hu : u ∈ P) (hv : v ∈ P) :
    cellSupDist u v ≤ cellSetDiameter P := by apply _root_.YangMills.Construction.Interpolation.ObservableSizes.cellSupDist_le_cellSetDiameter <;> assumption
def bondBalls (F : BlockFrame) (ρ : ℝ) : Set (StepVariable (finiteCells F)) := {η | ∀ b, ‖η b‖ ≤ ρ}
theorem convex_bondBalls (ρ : ℝ) : Convex ℝ (bondBalls F ρ) := by
  intro x hx y hy s r hs hr hsr b
  calc ‖(s • x + r • y) b‖ ≤ s * ‖x b‖ + r * ‖y b‖ := by
        have := norm_add_le (s • x b) (r • y b)
        simpa [norm_smul, abs_of_nonneg hs, abs_of_nonneg hr] using this
    _ ≤ s * ρ + r * ρ := add_le_add (mul_le_mul_of_nonneg_left (hx b) hs)
        (mul_le_mul_of_nonneg_left (hy b) hr)
    _ = ρ := by rw [← add_mul, hsr, one_mul]
def logContourAverage (a ρ : ℝ) (c₀ : F.Site F.top × Fin 4) :
    StepVariable (finiteCells F) → F.GaugeField F.top → ℝ :=
  fun η V' => Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true a ρ 0 V' η) c₀‖
theorem interpolatedCoords_zero (a ρ : ℝ) (m : ℕ) (V' : F.GaugeField F.top) (η : StepVariable (finiteCells F)) :
    interpolatedCoords 0 a ρ m V' η = coordsAboveFrame true a ρ 0 V' η := by apply _root_.YangMills.SharedProofs.p718 <;> assumption
theorem logContourNorm_zero (a ρ : ℝ) (m : ℕ) (c₀ : F.Site F.top × Fin 4) :
    (logContourNorm 0 a ρ m c₀ : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) =
      logContourAverage a ρ c₀ := by apply _root_.YangMills.Construction.ChartedEnergyRegularity.logContourNorm_zero <;> assumption
theorem logContourAverage_sub_le {a ρA κ κ₂ δ₂ x ρ W : ℝ} {m : ℕ} {K : ℕ → ℝ} {D : ℕ → ℕ → ℝ}
    (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    (hD : 0 ≤ D 1 0) (hK : ∀ η ∈ bondBalls F ρ, HasInterpolationKernels 0 a ρA κ κ₂ δ₂ x m K D V η)
    (c₀ : F.Site F.top × Fin 4)
    (hW : ∑ b : ↥(chordBonds (finiteCells F)),
      Real.exp (-(2 ^ 8 * κ * (cellSupDist (enclosingCell b.1.1) c₀.1 : ℝ))) ≤ W)
    {η : StepVariable (finiteCells F)} (hη : η ∈ bondBalls F ρ) :
    |logContourAverage a ρA c₀ η V - logContourAverage a ρA c₀ 0 V| ≤ D 1 0 * W * ρ := by
  classical
  set R : StepVariable (finiteCells F) → ℝ := fun η => logContourAverage a ρA c₀ η V with hR
  have hW0 : 0 ≤ W := (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le).trans hW
  have h1 : ∀ y ∈ bondBalls F ρ, ContDiffAt ℝ (1 : ℕ)
      (translatedTop (logContourAverage a ρA c₀) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions)) (y, 0) := by
    intro y hy
    refine translatedTop_contDiffAt _ y V _ _ fun p c' X' hX' hp => ?_
    have h2 := ((hK y hy).logContour c₀ _ p (doubledBond F) (doubledUnit F) c' X' (by omega) (norm_doubledUnit F) hX').1
    rw [logContourNorm_zero] at h2
    exact h2.of_le (by exact_mod_cast (by omega : 1 ≤ Fintype.card (ChordCoord F) + Fintype.card (ChordCoord F) + p))
  have hRe : R = fun y => translatedTop (logContourAverage a ρA c₀) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
      (Fin.elim0 : Fin 0 → imaginaryQuaternions) (y, 0) := by
    funext y
    show logContourAverage a ρA c₀ y V =
      logContourAverage a ρA c₀ y (leftTranslate (ColdStepAtMirrorFrames.bondSpread _ _ 0) V)
    rw [bondSpread_zero, leftTranslate_zero]
  have hRc : ∀ y ∈ bondBalls F ρ, ContDiffAt ℝ (1 : ℕ) R y := by
    intro y hy
    rw [hRe]
    exact ContDiffAt.comp y (g := translatedTop (logContourAverage a ρA c₀) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
      (Fin.elim0 : Fin 0 → imaginaryQuaternions)) (h1 y hy) (by fun_prop)
  have hder : ∀ y ∈ bondBalls F ρ, ∀ (b : ↥(chordBonds (finiteCells F))) (e : EuclideanSpace ℝ (Fin 3)), ‖e‖ = 1 →
      |fderiv ℝ R y (bondVariation b e)| ≤
        D 1 0 * Real.exp (-(2 ^ 8 * κ * (cellSupDist (enclosingCell b.1.1) c₀.1 : ℝ))) := by
    intro y hy b e he
    have hs : ContDiffAt ℝ ((1 + 0 : ℕ)) (translatedTop (logContourAverage a ρA c₀) V
        (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) (Fin.elim0 : Fin 0 → imaginaryQuaternions)) (y, 0) := h1 y hy
    have e1 := jointMixedDeriv_eq_partialJetSnd (logContourAverage a ρA c₀) y V (fun _ : Fin 1 => b) (fun _ => e)
      Fin.elim0 Fin.elim0 hs
    have hj : partialJetSnd (translatedTop (logContourAverage a ρA c₀) V (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4)
        (Fin.elim0 : Fin 0 → imaginaryQuaternions)) 0 (basisVectors 0) = R := by
      funext z
      simp only [partialJetSnd, iteratedFDeriv_zero_apply]
      show logContourAverage a ρA c₀ z (leftTranslate (ColdStepAtMirrorFrames.bondSpread _ _ 0) V) =
        logContourAverage a ρA c₀ z V
      rw [bondSpread_zero, leftTranslate_zero]
    rw [hj, iteratedFDeriv_one_apply] at e1
    have e2 : fderiv ℝ R y (bondVariation b e) =
        jointMixedDeriv (logContourAverage a ρA c₀) y V (fun _ : Fin 1 => b) (fun _ => e)
        Fin.elim0 Fin.elim0 := e1.symm
    have h3 := ((hK y hy).logContour c₀ 1 0 (fun _ : Fin 1 => b) (fun _ => e) Fin.elim0 Fin.elim0 (by norm_num)
      (fun _ => he) (fun l => l.elim0)).2
    rw [logContourNorm_zero] at h3
    rw [e2]
    refine h3.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg ?_)) hD)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hm : enclosingCell b.1.1 ∈ ({c₀.1} ∪ chordBondCells (fun _ : Fin 1 => b) ∪
        topBondCells (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : Finset F.Cell) := by
      simp [chordBondCells]
    have hz : c₀.1 ∈ ({c₀.1} ∪ chordBondCells (fun _ : Fin 1 => b) ∪
        topBondCells (Fin.elim0 : Fin 0 → F.Site F.top × Fin 4) : Finset F.Cell) := by
      simp
    exact_mod_cast cellSupDist_le_diameter hm hz
  have hop : ∀ y ∈ bondBalls F ρ, ‖fderiv ℝ R y‖ ≤ D 1 0 * W := by
    intro y hy
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun δ => ?_
    have hδ : δ = ∑ b, (bondVariation b (δ b) : StepVariable (finiteCells F)) := by
      simpa [bondVariation] using (Finset.univ_sum_single δ).symm
    have hb : ∀ b : ↥(chordBonds (finiteCells F)), |fderiv ℝ R y (bondVariation b (δ b))| ≤
        D 1 0 * Real.exp (-(2 ^ 8 * κ * (cellSupDist (enclosingCell b.1.1) c₀.1 : ℝ))) * ‖δ‖ := by
      intro b
      by_cases h0 : δ b = 0
      · have : (bondVariation b (δ b) : StepVariable (finiteCells F)) = 0 := by simp [bondVariation, h0]
        rw [this, map_zero, abs_zero]
        positivity
      · have hn : ‖δ b‖ ≠ 0 := norm_ne_zero_iff.2 h0
        have he : ‖(‖δ b‖⁻¹ • δ b : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
          rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
        have hs : (bondVariation b (δ b) : StepVariable (finiteCells F)) =
            ‖δ b‖ • bondVariation b (‖δ b‖⁻¹ • δ b) := by
          simp only [bondVariation]
          rw [← Pi.single_smul, smul_smul, mul_inv_cancel₀ hn, one_smul]
        rw [hs, map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (norm_nonneg _), mul_comm]
        exact mul_le_mul (hder y hy b _ he) (norm_le_pi_norm δ b) (norm_nonneg _) (by positivity)
    rw [Real.norm_eq_abs]
    conv_lhs => rw [hδ]
    rw [map_sum]
    calc |∑ b, fderiv ℝ R y (bondVariation b (δ b))| ≤ ∑ b, |fderiv ℝ R y (bondVariation b (δ b))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b : ↥(chordBonds (finiteCells F)),
            D 1 0 * Real.exp (-(2 ^ 8 * κ * (cellSupDist (enclosingCell b.1.1) c₀.1 : ℝ))) * ‖δ‖ :=
          Finset.sum_le_sum fun b _ => hb b
      _ = D 1 0 * (∑ b : ↥(chordBonds (finiteCells F)),
            Real.exp (-(2 ^ 8 * κ * (cellSupDist (enclosingCell b.1.1) c₀.1 : ℝ)))) * ‖δ‖ := by
          rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ D 1 0 * W * ‖δ‖ := by gcongr
  have h0S : (0 : StepVariable (finiteCells F)) ∈ bondBalls F ρ := fun b => by simpa using hρ
  have hmv := (convex_bondBalls ρ).norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => (hRc y hy).differentiableAt (by norm_num)) hop h0S hη
  rw [Real.norm_eq_abs, sub_zero] at hmv
  refine hmv.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact (pi_norm_le_iff_of_nonneg hρ).2 hη
theorem norm_contourAverage_le (hL : Odd F.blockSide) {j : ℕ} (X : F.GaugeField j) (c : F.Site (j + 1) × Fin 4) :
    ‖_root_.YangMills.Construction.BlockAverages.contourAverage X c‖ ≤ 1 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.norm_contourAverage_le_one <;> assumption
theorem abs_log_le_one_of_half_le {r : ℝ} (h1 : 1 / 2 ≤ r) (h2 : r ≤ 1) : |Real.log r| ≤ 1 := by apply _root_.YangMills.SharedProofs.p60921 <;> assumption
theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : ‖toImaginary v‖ = ‖v‖ := by apply _root_.YangMills.Construction.Interpolation.ExponentBoundSteps.norm_toImaginary <;> assumption
theorem abs_haarLogRatio_le_one {w : imaginaryQuaternions} (hw : ‖w‖ ≤ 1) : |haarLogRatio w| ≤ 1 := by apply _root_.YangMills.Construction.Estimates.haarLogRatio_bound <;> assumption
theorem fieldAboveFrame_zero (a ρ : ℝ) (V' : F.GaugeField F.top) :
    fieldAboveFrame true a ρ 0 V' (0 : StepVariable (finiteCells F)) = torusMinimizingField a ρ V' := by apply _root_.YangMills.Construction.ChartedEnergyRegularity.fieldAboveFrame_zero <;> assumption
end
section
open Set Filter Topology MeasureTheory
open BlockAverages ColdStepAtMirrorFrames Interpolation
theorem values_bounded_of_parameters (T : _root_.YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) (hT : T.IsOrdered) (h64 : 64 ≤ T.n₀)
    (hσs : 5 / 4 * T.σ ≤ T.chainParams.s₀)
    {Cq Cz : ℕ → ℝ} {Cr : ℕ → ℕ → ℕ → ℝ}
    (hFB : ∀ (t : ℕ) (x : ℝ), T.coupling ≤ x → InterpolatedFrameBoundsAt T Cq Cz Cr t x)
    {Kf : ℕ → ℝ} {D : ℕ → ℕ → ℝ} (hD : ∀ l j, 0 < D l j) (hKe : interpolationKernelBoundsAt T Kf D)
    (N : ℕ) (hN : ∀ F : BlockFrame, F.blockSide = T.L → ∀ (ι : Type) [Fintype ι] (j : ι → F.Site F.depth × Fin 4),
      Function.Injective j → ∀ z : F.Cell, (Finset.univ.filter fun b => enclosingCell (j b).1 = z).card ≤ N)
    (W : ℝ) (hW0 : 0 ≤ W) (hW : ∀ (F : BlockFrame) (ι : Type) [Fintype ι] (y : ι → F.Cell),
      (∀ z, (Finset.univ.filter fun b => y b = z).card ≤ N) →
      ∀ z : F.Cell, ∑ b, Real.exp (-(2 ^ 8 * T.κ * (cellSupDist (y b) z : ℝ))) ≤ W) :
    ∃ R₀ : ℝ, 0 ≤ R₀ ∧
      ∀ (t : ℕ) (F : BlockFrame) (V : F.GaugeField F.top) (η : StepVariable (finiteCells F)),
        IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V → (∀ b, ‖η b‖ ≤ T.ballRadius) →
        IsSmallCurvature T.σ (fieldAboveFrame true T.a T.ρA 0 V η) ∧
        (∀ c ∈ innerBonds (finiteCells F) F.top,
          |Real.log ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true T.a T.ρA 0 V η) c‖| ≤ R₀) ∧
        ∀ b : ↥(chordBonds (finiteCells F)),
          |haarLogRatio (coordsAboveFrame true T.a T.ρA 0 V η b.1.1 b.1.2)| ≤ R₀ := by
  have hκ : 0 < T.κ := hT.κ_pos
  have hσ : 0 < T.σ := hT.σ_pos
  have hρ : 0 ≤ T.ballRadius := by
    show 0 ≤ T.σ / 64
    positivity
  have hD1 : 0 ≤ D 1 0 := (hD 1 0).le
  have hDW : 0 ≤ D 1 0 * W * T.ballRadius := by positivity
  refine ⟨2 + D 1 0 * W * T.ballRadius, by positivity, fun t F V η hF hV hη => ?_⟩
  obtain ⟨hFL, hFt, n, hside, hnn⟩ := id hF
  have hsm := ((hFB t T.coupling le_rfl).one_torus F V 0 hF hV le_rfl zero_le_one).small
  have hc := hT.chain_admissible
  obtain ⟨⟨hρ0, hρ1, hs₀, hδ, -, -, hC1, -⟩, hcl⟩ := hc.classical
  have hL := hc.inequalities
  refine ⟨?_, fun c hc' => ?_, fun b => ?_⟩
  · have h1 := hsm.small_curvature_nearby η hη
    have e : interpolatedField 0 T.a T.chainParams.ρA (frameRadius T.coupling) V η =
        fieldAboveFrame true T.a T.ρA 0 V η := by
      simp only [interpolatedField, fieldAboveFrame, interpolatedCoords_zero]
      rfl
    rw [e] at h1
    intro p hp
    have := h1 p hp
    linarith
  · have hWc : ∑ b : ↥(chordBonds (finiteCells F)),
        Real.exp (-(2 ^ 8 * T.κ * (cellSupDist (enclosingCell b.1.1) c.1 : ℝ))) ≤ W :=
      hW F ↥(chordBonds (finiteCells F)) (fun b => enclosingCell b.1.1)
        (fun z => hN F hFL ↥(chordBonds (finiteCells F)) (fun b => b.1) Subtype.val_injective z) c.1
    have hKst : ∀ η ∈ bondBalls F T.ballRadius, HasInterpolationKernels 0 T.a T.ρA T.κ T.chainParams.κ₂
        T.chainParams.δ₂ T.coupling (frameRadius T.coupling) Kf D V η :=
      fun η hη => hKe T.coupling t F V 0 η le_rfl hF hV le_rfl zero_le_one hη
    have h1 := logContourAverage_sub_le hκ hρ hD1 hKst c hWc hη
    have hs0 : 0 < 5 / 4 * T.σ := by positivity
    obtain ⟨-, hsc, -, -⟩ := hcl F (5 / 4 * T.σ) V ⟨hFL, n, by omega, hside⟩ hs0 hσs hV
    have hLp : 1 ≤ (F.blockSide : ℤ) := by
      have := hT.odd_L.pos
      rw [hFL]
      exact_mod_cast this
    have h0c : (0 : Fin 4 → ℤ) ∈ centredCube F.blockSide := by
      simp only [centredCube, Fintype.mem_piFinset, Pi.zero_apply, Finset.mem_Icc]
      intro _
      constructor <;> omega
    have h2' := (hsc.2 c 0 1 h0c).2
    rw [← fieldAboveFrame_zero] at h2'
    have h2 : 1 - T.chainParams.C * (5 / 4 * T.σ) ≤
        ‖_root_.YangMills.Construction.BlockAverages.contourAverage (fieldAboveFrame true T.a T.ρA 0 V 0) c‖ := h2'
    have hCs : T.chainParams.C * (5 / 4 * T.σ) ≤ 1 / 2 := by
      have h3 : T.chainParams.C * (5 / 4 * T.σ) ≤ T.chainParams.C * T.chainParams.s₀ :=
        mul_le_mul_of_nonneg_left hσs (by linarith)
      have h4 := hL.2.2.2.2.1
      linarith
    have hOdd : Odd F.blockSide := by
      rw [hFL]
      exact hT.odd_L
    have h5 : |logContourAverage T.a T.ρA c 0 V| ≤ 1 :=
      abs_log_le_one_of_half_le (by linarith) (norm_contourAverage_le hOdd _ c)
    have h6 : |logContourAverage T.a T.ρA c η V| ≤
        |logContourAverage T.a T.ρA c η V - logContourAverage T.a T.ρA c 0 V| +
        |logContourAverage T.a T.ρA c 0 V| := by
      have := abs_add_le (logContourAverage T.a T.ρA c η V - logContourAverage T.a T.ρA c 0 V)
        (logContourAverage T.a T.ρA c 0 V)
      simpa using this
    show |logContourAverage T.a T.ρA c η V| ≤ _
    linarith
  · have hw : ‖coordsAboveFrame true T.a T.ρA 0 V η b.1.1 b.1.2‖ ≤ 1 := by
      have h1 := hsm.norm_add_le b.1 b.2
      have e1 : interpolatedFrame 0 T.a T.chainParams.ρA (frameRadius T.coupling) b.1 V =
          ColdStepAtMirrorFrames.stepFrame true T.a T.ρA 0 b.1 V := by
        simp [interpolatedFrame, ColdStepAtMirrorFrames.stepFrame]
        rfl
      rw [e1] at h1
      have e2 : stepCoordinates η b.1.1 b.1.2 = toImaginary (η b) := by
        simp only [stepCoordinates]
        rw [dif_pos (show (b.1.1, b.1.2) ∈ chordBonds (finiteCells F) from b.2)]
      have e3 : coordsAboveFrame true T.a T.ρA 0 V η b.1.1 b.1.2 =
          ColdStepAtMirrorFrames.stepFrame true T.a T.ρA 0 b.1 V + toImaginary (η b) := by
        simp only [coordsAboveFrame, e2]
      rw [e3]
      have h2 : ‖toImaginary (η b)‖ ≤ T.σ / 64 := by
        rw [norm_toImaginary]
        exact hη b
      have h3 := norm_add_le (ColdStepAtMirrorFrames.stepFrame true T.a T.ρA 0 b.1 V) (toImaginary (η b))
      have h4 : T.chainParams.ρA ≤ 1 := hρ1
      linarith
    have := abs_haarLogRatio_le_one hw
    linarith
theorem eventually_lower_bounds :
    EventuallyInParameters fun T => 64 ≤ T.n₀ ∧ 5 / 4 * T.σ ≤ T.chainParams.s₀ := by apply _root_.YangMills.Construction.ChartedEnergyRegularity.eventually_parameter_floors <;> assumption
theorem valuesAboveFrameBounded (hFB : Interpolation.interpolatedFramesStatement)
    (hKe : Interpolation.interpolationKernelBoundsStatement)
    (hBonds : CellCounting.BondsPerCellBounded)
    (hSum : CellCounting.ExpDecaySumBounded) :
    StepDensities.valuesAboveFrameBoundedStatement := by
  obtain ⟨Cq, Cz, Cr, h1⟩ := hFB
  obtain ⟨Kf, D, -, hD, h2⟩ := hKe
  have A := EventuallyInParameters.and (EventuallyInParameters.and h1 h2) eventually_lower_bounds
  have Bt : EventuallyOrdered _ := EventuallyInParameters.mono A fun T g _ _ => g
  refine EventuallyOrdered.mono Bt fun T hT hn g => ?_
  obtain ⟨⟨g1, g2⟩, g3, g4⟩ := g
  have hL0 : 0 < T.L := hT.odd_L.pos
  obtain ⟨N, hN⟩ := hBonds T.L hL0
  have hκ' : 0 < 2 ^ 8 * T.κ := by have := hT.κ_pos; positivity
  obtain ⟨W, hW0, hW⟩ := hSum N _ hκ'
  exact values_bounded_of_parameters T hT g3 g4 g1 (hD _) g2 N hN W hW0 fun F ι _ y h z => hW F ι y h z
end
end YangMills.Construction.ValuesAboveMinimizer
end
