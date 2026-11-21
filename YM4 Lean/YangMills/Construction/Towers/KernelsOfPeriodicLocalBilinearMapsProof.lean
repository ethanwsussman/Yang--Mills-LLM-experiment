import YangMills.Construction.Towers.KernelDeterminedByABilinearFormProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.CellsAndClassesOfThePeriodicExtension
import YangMills.Construction.Towers.KernelsOfPeriodicLocalBilinearMaps
import YangMills.Construction.Towers.LocalKernelsAndMatricesOfLinearMaps
import YangMills.Construction.Towers.SumsProductsAndTransposesOfDescendingKernels
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.LocalKernels.LocalBilinearKernels
open PeriodicOperators (PeriodicData KernelMatrix applyKernel wPairing HasFiniteSupport)
open Periodisation
open TorusMetric (supNormVec)
theorem supNormVec_le_iff (v : Fin 4 → ℝ) (r : ℝ) : supNormVec v ≤ r ↔ ∀ μ, |v μ| ≤ r := by
  unfold supNormVec
  rw [Finset.sup'_le_iff]
  simp
theorem supNormVec_sub_le_add {a b c : Fin 4 → ℝ} {r s : ℝ} (h : supNormVec (a - c) ≤ r)
    (h' : supNormVec (b - c) ≤ s) : supNormVec (a - b) ≤ r + s := by
  rw [supNormVec_le_iff] at h h' ⊢
  intro μ
  have h1 := abs_le.1 (h μ)
  have h2 := abs_le.1 (h' μ)
  simp only [Pi.sub_apply] at h1 h2 ⊢
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
theorem supNormVec_sub_comm (a b : Fin 4 → ℝ) : supNormVec (a - b) = supNormVec (b - a) := by
  unfold supNormVec
  refine Finset.sup'_congr _ rfl fun μ _ => ?_
  exact abs_sub_comm _ _
section Functions
variable {J J' : Type}
def pointIndicator (ι : J) : J → ℂ := open Classical in fun x => if x = ι then 1 else 0
theorem pointIndicator_self (ι : J) : pointIndicator ι ι = 1 := by simp [pointIndicator]
theorem pointIndicator_of_ne {ι x : J} (h : x ≠ ι) : pointIndicator ι x = 0 := by apply _root_.YangMills.Construction.Tower.PolarisedKernel.basisFunction_of_ne <;> assumption
def restrictOn (D : Set J) (g : J → ℂ) : J → ℂ := open Classical in fun x => if x ∈ D then g x else 0
theorem restrictOn_of_mem {D : Set J} {g : J → ℂ} {x : J} (h : x ∈ D) : restrictOn D g x = g x := by
  simp [restrictOn, h]
theorem restrictOn_of_notMem {D : Set J} {g : J → ℂ} {x : J} (h : x ∉ D) : restrictOn D g x = 0 := by
  simp [restrictOn, h]
theorem restrictOn_hasFiniteSupport {D : Set J} (hD : D.Finite) (g : J → ℂ) :
    HasFiniteSupport (restrictOn D g) := by
  refine hD.subset fun x hx => ?_
  by_contra h
  exact (Function.mem_support.1 hx) (restrictOn_of_notMem h)
theorem pointIndicator_hasFiniteSupport (ι : J) : HasFiniteSupport (pointIndicator ι) := by apply _root_.YangMills.Construction.Tower.PolarisedKernel.basisFunction_hasFiniteSupport <;> assumption
theorem hasFiniteSupport_add {f g : J → ℂ} (hf : HasFiniteSupport f) (hg : HasFiniteSupport g) :
    HasFiniteSupport (f + g) :=
  (hf.union hg).subset (Function.support_add f g)
theorem hasFiniteSupport_smul (c : ℂ) {f : J → ℂ} (hf : HasFiniteSupport f) :
    HasFiniteSupport (c • f) := by
  refine Set.Finite.subset hf fun x hx => ?_
  rw [Function.mem_support] at hx ⊢
  intro h0
  exact hx (by simp [h0])
theorem isBoundedFn_zero : IsBoundedFn (0 : J → ℂ) := ⟨0, fun _ => by simp⟩
theorem isBoundedFn_of_hasFiniteSupport {f : J → ℂ} (hf : HasFiniteSupport f) : IsBoundedFn f := by
  obtain ⟨C, hC⟩ := (Set.Finite.image (fun i => ‖f i‖) hf).bddAbove
  refine ⟨max C 0, fun i => ?_⟩
  by_cases h : f i = 0
  · simp [h]
  · exact (hC ⟨i, Function.mem_support.2 h, rfl⟩).trans (le_max_left _ _)
theorem hasFiniteSupport_induction {P : (J → ℂ) → Prop} (h0 : P 0)
    (hs : ∀ (f : J → ℂ) (c : ℂ) (ι : J), HasFiniteSupport f → P f → P (f + c • pointIndicator ι))
    (f : J → ℂ) (hf : HasFiniteSupport f) : P f := by
  classical
  obtain ⟨s, hs'⟩ : ∃ s : Finset J, Function.support f ⊆ s :=
    ⟨hf.toFinset, fun x hx => Finset.mem_coe.2 (hf.mem_toFinset.2 hx)⟩
  induction s using Finset.induction_on generalizing f with
  | empty =>
    have : f = 0 := by
      funext x
      by_contra h
      simpa using hs' (Function.mem_support.2 h)
    rw [this]
    exact h0
  | insert a s _ ih =>
    have hg : HasFiniteSupport (f - f a • pointIndicator a) := by
      have := hasFiniteSupport_add hf (hasFiniteSupport_smul (-(f a)) (pointIndicator_hasFiniteSupport a))
      simpa [sub_eq_add_neg] using this
    have hsub : Function.support (f - f a • pointIndicator a) ⊆ s := by
      intro x hx
      rw [Function.mem_support] at hx
      by_cases hxa : x = a
      · subst hxa
        exact absurd (by simp [pointIndicator_self]) hx
      · have hfx : f x ≠ 0 := by
          intro h
          exact hx (by simp [pointIndicator_of_ne hxa, h])
        have := hs' (Function.mem_support.2 hfx)
        simpa [hxa] using this
    have := hs _ (f a) a hg (ih _ hg hsub)
    simpa using this
theorem summable_of_finite_support {F : J → ℂ} (h : (Function.support F).Finite) : Summable F :=
  summable_of_hasFiniteSupport h
variable (w : J → ℝ)
theorem summable_weighted_left {f : J → ℂ} (hf : HasFiniteSupport f) (g : J → ℂ) :
    Summable fun i => (w i : ℂ) * (f i * g i) := by
  refine summable_of_finite_support (Set.Finite.subset hf fun x hx => ?_)
  rw [Function.mem_support] at hx ⊢
  intro h0
  exact hx (by simp [h0])
theorem summable_weighted_right (f : J → ℂ) {g : J → ℂ} (hg : HasFiniteSupport g) :
    Summable fun i => (w i : ℂ) * (f i * g i) := by
  refine summable_of_finite_support (Set.Finite.subset hg fun x hx => ?_)
  rw [Function.mem_support] at hx ⊢
  intro h0
  exact hx (by simp [h0])
theorem wPairing_add_left {f g : J → ℂ} (hf : HasFiniteSupport f) (hg : HasFiniteSupport g)
    (h : J → ℂ) : wPairing w (f + g) h = wPairing w f h + wPairing w g h := by
  unfold wPairing
  rw [← (summable_weighted_left w hf h).tsum_add (summable_weighted_left w hg h)]
  refine tsum_congr fun i => ?_
  simp only [Pi.add_apply]
  ring
theorem wPairing_add_right {f g g' : J → ℂ} (h : Summable fun i => (w i : ℂ) * (f i * g i))
    (h' : Summable fun i => (w i : ℂ) * (f i * g' i)) :
    wPairing w f (g + g') = wPairing w f g + wPairing w f g' := by
  unfold wPairing
  rw [← h.tsum_add h']
  refine tsum_congr fun i => ?_
  simp only [Pi.add_apply]
  ring
theorem wPairing_smul_left (c : ℂ) (f h : J → ℂ) : wPairing w (c • f) h = c * wPairing w f h := by
  unfold wPairing
  rw [← tsum_mul_left]
  refine tsum_congr fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
theorem wPairing_smul_right (c : ℂ) (f h : J → ℂ) : wPairing w f (c • h) = c * wPairing w f h := by
  unfold wPairing
  rw [← tsum_mul_left]
  refine tsum_congr fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
theorem wPairing_comm (f g : J → ℂ) : wPairing w f g = wPairing w g f := by
  unfold wPairing
  refine tsum_congr fun i => ?_
  ring
theorem wPairing_zero_right (f : J → ℂ) : wPairing w f 0 = 0 := by
  simp [wPairing]
theorem wPairing_pointIndicator (ι : J) (g : J → ℂ) :
    wPairing w (pointIndicator ι) g = (w ι : ℂ) * g ι := by
  unfold wPairing
  rw [tsum_eq_single ι fun x hx => by simp [pointIndicator_of_ne hx]]
  simp [pointIndicator_self]
theorem applyKernel_summable (T : J' → J → ℂ) {f : J → ℂ} (hf : HasFiniteSupport f) (ι' : J') :
    Summable fun ι => T ι' ι * f ι := by
  refine summable_of_finite_support (Set.Finite.subset hf fun x hx => ?_)
  rw [Function.mem_support] at hx ⊢
  intro h0
  exact hx (by simp [h0])
theorem applyKernel_add (T : J' → J → ℂ) {f g : J → ℂ} (hf : HasFiniteSupport f)
    (hg : HasFiniteSupport g) :
    applyKernel T (f + g) = applyKernel T f + applyKernel T g := by
  funext ι'
  simp only [applyKernel, Pi.add_apply]
  rw [← (applyKernel_summable T hf ι').tsum_add (applyKernel_summable T hg ι')]
  refine tsum_congr fun i => ?_
  ring
theorem applyKernel_smul (T : J' → J → ℂ) (c : ℂ) (f : J → ℂ) :
    applyKernel T (c • f) = c • applyKernel T f := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.applyKernel_smul <;> assumption
theorem applyKernel_pointIndicator (T : J' → J → ℂ) (ι : J) (ι' : J') :
    applyKernel T (pointIndicator ι) ι' = T ι' ι := by
  unfold applyKernel
  rw [tsum_eq_single ι fun x hx => by simp [pointIndicator_of_ne hx]]
  simp [pointIndicator_self]
structure IsFinSuppBilinear (B : (J → ℂ) → (J' → ℂ) → ℂ) : Prop where
  map_add_left : ∀ f g f', HasFiniteSupport f → HasFiniteSupport g → HasFiniteSupport f' →
    B (f + g) f' = B f f' + B g f'
  map_smul_left : ∀ (c : ℂ) f f', HasFiniteSupport f → HasFiniteSupport f' →
    B (c • f) f' = c * B f f'
  map_add_right : ∀ f f' g', HasFiniteSupport f → HasFiniteSupport f' →
    HasFiniteSupport g' → B f (f' + g') = B f f' + B f g'
  map_smul_right : ∀ (c : ℂ) f f', HasFiniteSupport f → HasFiniteSupport f' →
    B f (c • f') = c * B f f'
theorem hasFiniteSupport_zero : HasFiniteSupport (0 : J → ℂ) := by
  simp [HasFiniteSupport]
theorem IsFinSuppBilinear.apply_zero_left {B : (J → ℂ) → (J' → ℂ) → ℂ} (hB : IsFinSuppBilinear B)
    {f' : J' → ℂ} (hf' : HasFiniteSupport f') : B 0 f' = 0 := by
  simpa using hB.map_smul_left 0 0 f' hasFiniteSupport_zero hf'
theorem IsFinSuppBilinear.apply_zero_right {B : (J → ℂ) → (J' → ℂ) → ℂ} (hB : IsFinSuppBilinear B)
    {f : J → ℂ} (hf : HasFiniteSupport f) : B f 0 = 0 := by
  simpa using hB.map_smul_right 0 f 0 hf hasFiniteSupport_zero
theorem finSuppBilinear_ext {X Y : (J → ℂ) → (J' → ℂ) → ℂ} (hX : IsFinSuppBilinear X)
    (hY : IsFinSuppBilinear Y)
    (h : ∀ ι ι', X (pointIndicator ι) (pointIndicator ι') = Y (pointIndicator ι) (pointIndicator ι'))
    {f : J → ℂ} {f' : J' → ℂ} (hf : HasFiniteSupport f) (hf' : HasFiniteSupport f') :
    X f f' = Y f f' := by
  have first : ∀ ι', X f (pointIndicator ι') = Y f (pointIndicator ι') := by
    intro ι'
    have hι' := pointIndicator_hasFiniteSupport ι'
    refine hasFiniteSupport_induction (P := fun u => X u (pointIndicator ι') = Y u (pointIndicator ι'))
      (by rw [hX.apply_zero_left hι', hY.apply_zero_left hι']) ?_ f hf
    intro u c ι hu ih
    have hi := pointIndicator_hasFiniteSupport ι
    have hci := hasFiniteSupport_smul c hi
    rw [hX.map_add_left _ _ _ hu hci hι', hY.map_add_left _ _ _ hu hci hι',
      hX.map_smul_left _ _ _ hi hι', hY.map_smul_left _ _ _ hi hι', ih, h]
  refine hasFiniteSupport_induction (P := fun u => X f u = Y f u)
    (by rw [hX.apply_zero_right hf, hY.apply_zero_right hf]) ?_ f' hf'
  intro u c ι' hu ih
  have hi := pointIndicator_hasFiniteSupport ι'
  have hci := hasFiniteSupport_smul c hi
  rw [hX.map_add_right _ _ _ hf hu hci, hY.map_add_right _ _ _ hf hu hci,
    hX.map_smul_right _ _ _ hf hi, hY.map_smul_right _ _ _ hf hi, ih, first]
theorem isFinSuppBilinear_wPairing_applyKernel (T : J → J' → ℂ) :
    IsFinSuppBilinear fun f f' => wPairing w f (applyKernel T f') where
  map_add_left f g f' hf hg _ := wPairing_add_left w hf hg _
  map_smul_left c f f' _ _ := wPairing_smul_left w c f _
  map_add_right f f' g' hf hf' hg' := by
    rw [applyKernel_add T hf' hg']
    exact wPairing_add_right w (summable_weighted_left w hf _) (summable_weighted_left w hf _)
  map_smul_right c f f' _ _ := by
    rw [applyKernel_smul T c f']
    exact wPairing_smul_right w c f _
variable {w}
theorem kernel_eq_inv_weight_mul (hw : ∀ i, (w i : ℂ) ≠ 0) {B : (J → ℂ) → (J' → ℂ) → ℂ}
    {T : J → J' → ℂ}
    (hT : ∀ f f', HasFiniteSupport f → HasFiniteSupport f' →
      wPairing w f (applyKernel T f') = B f f') (ι : J) (ι' : J') :
    T ι ι' = (w ι : ℂ)⁻¹ * B (pointIndicator ι) (pointIndicator ι') := by
  have h := hT _ _ (pointIndicator_hasFiniteSupport ι) (pointIndicator_hasFiniteSupport ι')
  rw [wPairing_pointIndicator, applyKernel_pointIndicator] at h
  rw [← h, inv_mul_cancel_left₀ (hw ι)]
theorem existsUnique_kernel_of_bilinear (hw : ∀ i, (w i : ℂ) ≠ 0) {B : (J → ℂ) → (J' → ℂ) → ℂ}
    (hB : IsFinSuppBilinear B) :
    ∃! T : J → J' → ℂ, ∀ f f', HasFiniteSupport f → HasFiniteSupport f' →
      wPairing w f (applyKernel T f') = B f f' := by
  refine ⟨fun ι ι' => (w ι : ℂ)⁻¹ * B (pointIndicator ι) (pointIndicator ι'), ?_, ?_⟩
  · intro f f' hf hf'
    refine finSuppBilinear_ext (isFinSuppBilinear_wPairing_applyKernel w _) hB (fun ι ι' => ?_) hf hf'
    rw [wPairing_pointIndicator, applyKernel_pointIndicator, mul_inv_cancel_left₀ (hw ι)]
  · intro T hT
    funext ι ι'
    exact kernel_eq_inv_weight_mul hw hT ι ι'
end Functions
section Local
variable {A B C : PeriodicData} {R : ℝ} {H : (A.Carrier → ℂ) → (B.Carrier → ℂ) → C.Carrier → ℂ}
theorem localBilinear_zero_left (hH : IsLocalBilinear A B C R H) {f' : B.Carrier → ℂ}
    (hf' : IsBoundedFn f') : H 0 f' = 0 := by
  simpa using hH.1.smul_left 0 0 f' isBoundedFn_zero hf'
theorem localBilinear_zero_right (hH : IsLocalBilinear A B C R H) {f : A.Carrier → ℂ}
    (hf : IsBoundedFn f) : H f 0 = 0 := by
  simpa using hH.1.smul_right 0 f 0 hf isBoundedFn_zero
theorem localBilinear_eq_zero_of_left (hH : IsLocalBilinear A B C R H) {f : A.Carrier → ℂ}
    {f' : B.Carrier → ℂ} (hf : IsBoundedFn f) (hf' : IsBoundedFn f') (c : C.Carrier)
    (h : ∀ a, supNormVec (A.pos a - C.pos c) ≤ R → f a = 0) : H f f' c = 0 := by
  rw [hH.2 f 0 f' f' hf isBoundedFn_zero hf' hf' c h fun _ _ => rfl, localBilinear_zero_left hH hf']
  rfl
theorem localBilinear_eq_zero_of_right (hH : IsLocalBilinear A B C R H) {f : A.Carrier → ℂ}
    {f' : B.Carrier → ℂ} (hf : IsBoundedFn f) (hf' : IsBoundedFn f') (c : C.Carrier)
    (h : ∀ b, supNormVec (B.pos b - C.pos c) ≤ R → f' b = 0) : H f f' c = 0 := by
  rw [hH.2 f f f' 0 hf hf hf' isBoundedFn_zero c (fun _ _ => rfl) h, localBilinear_zero_right hH hf]
  rfl
theorem pointIndicator_eq_zero_of_not {J : Type} {P : J → Prop} {ι : J} (h : ¬ P ι) (x : J)
    (hx : P x) : pointIndicator ι x = 0 :=
  pointIndicator_of_ne fun e => h (e ▸ hx)
theorem hasFiniteSupport_localBilinear (hH : IsLocalBilinear A B C R H)
    (hCA : ∀ a : A.Carrier, {c : C.Carrier | supNormVec (C.pos c - A.pos a) ≤ R}.Finite)
    {f : A.Carrier → ℂ} {f' : B.Carrier → ℂ} (hf : HasFiniteSupport f)
    (hf' : IsBoundedFn f') : HasFiniteSupport (H f f') := by
  refine (Set.Finite.biUnion hf fun a _ => hCA a).subset fun c hc => ?_
  rw [Function.mem_support] at hc
  by_contra hno
  refine hc (localBilinear_eq_zero_of_left hH (isBoundedFn_of_hasFiniteSupport hf) hf' c fun a ha => ?_)
  by_contra hfa
  refine hno (Set.mem_biUnion (Function.mem_support.2 hfa) ?_)
  show supNormVec (C.pos c - A.pos a) ≤ R
  rwa [supNormVec_sub_comm]
theorem isFinSuppBilinear_wPairing_localBilinear (hH : IsLocalBilinear A B C R H)
    (hCA : ∀ a : A.Carrier, {c : C.Carrier | supNormVec (C.pos c - A.pos a) ≤ R}.Finite)
    (w : C.Carrier → ℝ) (g : C.Carrier → ℂ) :
    IsFinSuppBilinear fun (f : A.Carrier → ℂ) (f' : B.Carrier → ℂ) => wPairing w g (H f f') where
  map_add_left f h f' hf hh hf' := by
    have bf' := isBoundedFn_of_hasFiniteSupport hf'
    rw [hH.1.add_left f h f' (isBoundedFn_of_hasFiniteSupport hf) (isBoundedFn_of_hasFiniteSupport hh) bf']
    exact wPairing_add_right w (summable_weighted_right w g (hasFiniteSupport_localBilinear hH hCA hf bf'))
      (summable_weighted_right w g (hasFiniteSupport_localBilinear hH hCA hh bf'))
  map_smul_left c f f' hf hf' := by
    rw [hH.1.smul_left c f f' (isBoundedFn_of_hasFiniteSupport hf) (isBoundedFn_of_hasFiniteSupport hf')]
    exact wPairing_smul_right w c g _
  map_add_right f f' h' hf hf' hh' := by
    have bf := isBoundedFn_of_hasFiniteSupport hf
    rw [hH.1.add_right f f' h' bf (isBoundedFn_of_hasFiniteSupport hf') (isBoundedFn_of_hasFiniteSupport hh')]
    exact wPairing_add_right w
      (summable_weighted_right w g
        (hasFiniteSupport_localBilinear hH hCA hf (isBoundedFn_of_hasFiniteSupport hf')))
      (summable_weighted_right w g
        (hasFiniteSupport_localBilinear hH hCA hf (isBoundedFn_of_hasFiniteSupport hh')))
  map_smul_right c f f' hf hf' := by
    rw [hH.1.smul_right c f f' (isBoundedFn_of_hasFiniteSupport hf) (isBoundedFn_of_hasFiniteSupport hf')]
    exact wPairing_smul_right w c g _
theorem localBilinear_pointIndicator_far (hH : IsLocalBilinear A B C R H) {a : A.Carrier}
    {b : B.Carrier} (h : ¬ supNormVec (B.pos b - A.pos a) ≤ 2 * R) :
    H (pointIndicator a) (pointIndicator b) = 0 := by
  funext c
  have ba := isBoundedFn_of_hasFiniteSupport (pointIndicator_hasFiniteSupport a)
  have bb := isBoundedFn_of_hasFiniteSupport (pointIndicator_hasFiniteSupport b)
  by_cases h1 : supNormVec (A.pos a - C.pos c) ≤ R
  · by_cases h2 : supNormVec (B.pos b - C.pos c) ≤ R
    · exact absurd (by simpa [two_mul] using supNormVec_sub_le_add h2 h1) h
    · exact localBilinear_eq_zero_of_right hH ba bb c
        (pointIndicator_eq_zero_of_not (P := fun x => supNormVec (B.pos x - C.pos c) ≤ R) h2)
  · exact localBilinear_eq_zero_of_left hH ba bb c
      (pointIndicator_eq_zero_of_not (P := fun x => supNormVec (A.pos x - C.pos c) ≤ R) h1)
theorem isLocalKernel_of_relation (hH : IsLocalBilinear A B C R H) {w : A.Carrier → ℝ}
    {w'' : C.Carrier → ℝ} (hw : ∀ i, (w i : ℂ) ≠ 0) {g : C.Carrier → ℂ}
    {T : A.Carrier → B.Carrier → ℂ}
    (hT : ∀ f f', HasFiniteSupport f → HasFiniteSupport f' →
      wPairing w f (applyKernel T f') = wPairing w'' g (H f f')) :
    IsLocalKernel B A (2 * R) T := by
  intro a b h
  rw [kernel_eq_inv_weight_mul (B := fun f f' => wPairing w'' g (H f f')) hw hT a b]
  rw [localBilinear_pointIndicator_far hH h, wPairing_zero_right, mul_zero]
theorem weight_mul_applyKernel_of_bounded (hH : IsLocalBilinear A B C R H)
    (hBA : ∀ a : A.Carrier,
      {b : B.Carrier | supNormVec (B.pos b - A.pos a) ≤ 2 * R}.Finite)
    {w : A.Carrier → ℝ} {w'' : C.Carrier → ℝ} {g'' : C.Carrier → ℂ}
    {T : A.Carrier → B.Carrier → ℂ}
    (hT : ∀ f f', HasFiniteSupport f → HasFiniteSupport f' →
      wPairing w f (applyKernel T f') = wPairing w'' g'' (H f f'))
    (hloc : IsLocalKernel B A (2 * R) T) {g : B.Carrier → ℂ} (hg : IsBoundedFn g)
    (a : A.Carrier) :
    (w a : ℂ) * applyKernel T g a = wPairing w'' g'' (H (pointIndicator a) g) := by
  set D : Set B.Carrier := {b | supNormVec (B.pos b - A.pos a) ≤ 2 * R} with hD
  have hfin := restrictOn_hasFiniteSupport (hBA a) g
  have ba := isBoundedFn_of_hasFiniteSupport (pointIndicator_hasFiniteSupport a)
  have h1 := hT _ _ (pointIndicator_hasFiniteSupport a) hfin
  rw [wPairing_pointIndicator] at h1
  have h2 : applyKernel T (restrictOn D g) a = applyKernel T g a := by
    refine tsum_congr fun b => ?_
    by_cases hb : b ∈ D
    · rw [restrictOn_of_mem hb]
    · rw [hloc a b hb]
      simp
  have h3 : H (pointIndicator a) (restrictOn D g) = H (pointIndicator a) g := by
    funext c
    by_cases hc : supNormVec (A.pos a - C.pos c) ≤ R
    · refine hH.2 _ _ _ _ ba ba (isBoundedFn_of_hasFiniteSupport hfin) hg c (fun _ _ => rfl)
        fun b hb => ?_
      refine restrictOn_of_mem ?_
      show supNormVec (B.pos b - A.pos a) ≤ 2 * R
      simpa [two_mul] using supNormVec_sub_le_add hb hc
    · have hfar :=
        pointIndicator_eq_zero_of_not (P := fun x => supNormVec (A.pos x - C.pos c) ≤ R) hc
      rw [localBilinear_eq_zero_of_left hH ba (isBoundedFn_of_hasFiniteSupport hfin) c hfar,
        localBilinear_eq_zero_of_left hH ba hg c hfar]
  rw [← h2, h1, h3]
def partialKernel (H : (A.Carrier → ℂ) → (B.Carrier → ℂ) → C.Carrier → ℂ) (g : B.Carrier → ℂ) :
    KernelMatrix A.Carrier C.Carrier :=
  fun c a => H (pointIndicator a) g c
theorem partialKernel_isLocalKernel (hH : IsLocalBilinear A B C R H) {g : B.Carrier → ℂ}
    (hg : IsBoundedFn g) : IsLocalKernel A C R (partialKernel H g) := by
  intro c a h
  exact localBilinear_eq_zero_of_left hH
    (isBoundedFn_of_hasFiniteSupport (pointIndicator_hasFiniteSupport a)) hg c
    (pointIndicator_eq_zero_of_not (P := fun x => supNormVec (A.pos x - C.pos c) ≤ R) h)
theorem applyKernel_partialKernel (hH : IsLocalBilinear A B C R H)
    (hAC : ∀ c : C.Carrier, {a : A.Carrier | supNormVec (A.pos a - C.pos c) ≤ R}.Finite)
    {g : B.Carrier → ℂ} (hg : IsBoundedFn g) {f : A.Carrier → ℂ} (hf : IsBoundedFn f) :
    applyKernel (partialKernel H g) f = H f g := by
  funext c
  set D : Set A.Carrier := {a | supNormVec (A.pos a - C.pos c) ≤ R} with hD
  have hfin := restrictOn_hasFiniteSupport (hAC c) f
  have hfinite : ∀ u : A.Carrier → ℂ, HasFiniteSupport u →
      H u g c = applyKernel (partialKernel H g) u c := by
    refine hasFiniteSupport_induction ?_ ?_
    · rw [localBilinear_zero_left hH hg]
      simp [applyKernel]
    · intro u d a hu ih
      have hi := pointIndicator_hasFiniteSupport a
      have hci := hasFiniteSupport_smul d hi
      rw [hH.1.add_left _ _ _ (isBoundedFn_of_hasFiniteSupport hu)
          (isBoundedFn_of_hasFiniteSupport hci) hg,
        hH.1.smul_left _ _ _ (isBoundedFn_of_hasFiniteSupport hi) hg, applyKernel_add _ hu hci,
        applyKernel_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [ih, applyKernel_pointIndicator]
      rfl
  have h1 : H f g c = H (restrictOn D f) g c :=
    hH.2 _ _ _ _ hf (isBoundedFn_of_hasFiniteSupport hfin) hg hg c
      (fun a ha => (restrictOn_of_mem (D := D) ha).symm) fun _ _ => rfl
  have h2 : applyKernel (partialKernel H g) f c =
      applyKernel (partialKernel H g) (restrictOn D f) c := by
    refine tsum_congr fun a => ?_
    by_cases ha : a ∈ D
    · rw [restrictOn_of_mem ha]
    · rw [partialKernel_isLocalKernel hH hg c a ha]
      simp
  rw [h2, h1, hfinite _ hfin]
end Local
section Tower
variable {k : ℕ} (L n : ℕ)
theorem weightOf_ofReal_ne_zero (I : WeightedIndexSet k) (ι : Idx L I) :
    (((I.toPeriodicData L).weightOf ι : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (I.comp ι.1).weight_pos.ne'
theorem imageWeight_ofReal_ne_zero (I : WeightedIndexSet k) (κ : I.ImageCarrier L n) :
    ((I.imageWeight L n κ : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (I.comp κ.1).weight_pos.ne'
theorem lift_isBoundedFn {I : WeightedIndexSet k} [Finite (I.ImageCarrier L n)]
    (f : I.ImageCarrier L n → ℂ) : IsBoundedFn (I.lift L n f) := by
  obtain ⟨C, hC⟩ := (Set.finite_range fun κ => ‖f κ‖).bddAbove
  exact ⟨C, fun ι => hC ⟨_, rfl⟩⟩
theorem finite_near (hE : LocalKernelFacts (k := k) L) (I I' : WeightedIndexSet k) {R : ℝ}
    (hR : 0 ≤ R) (ι' : Idx L I') :
    {ι : Idx L I | supNormVec ((I.toPeriodicData L).pos ι - (I'.toPeriodicData L).pos ι') ≤ R}.Finite := by
  classical
  let T : KernelMatrix (Idx L I) (Idx L I') := fun b a =>
    if supNormVec ((I.toPeriodicData L).pos a - (I'.toPeriodicData L).pos b) ≤ R then 1 else 0
  have hT : IsRLocal L I I' R T := fun b a h => if_neg h
  refine ((hE I I' R hR T hT).1 (fun _ => 1) ι').subset fun a ha => ?_
  rw [Function.mem_support]
  have ha' : supNormVec ((I.toPeriodicData L).pos a - (I'.toPeriodicData L).pos ι') ≤ R := ha
  simp [T, ha']
theorem kernelDescends_zero (I I' : WeightedIndexSet k) : KernelDescends L n I I' 0 0 := by
  refine ⟨⟨0, le_rfl, fun _ _ _ => rfl⟩, fun f => ?_⟩
  funext ι
  simp [applyKernel, WeightedIndexSet.lift]
end Tower
theorem periodicLocalBilinear_kernel (hCells : PeriodicLiftCells.CellsAndClassesHold)
    (hSums : DescendingKernelAlgebra)
    (hLocal : KernelsAndLinearMapMatrices) : Claim := by
  intro L hL k n hn I I' I'' R hR h4 H Hs f'' hH hper
  obtain ⟨hEvery, hMat⟩ := hLocal L hL k n hn
  have hSP := hSums L hL k n hn
  have hFin : ∀ J : WeightedIndexSet k, Finite (J.ImageCarrier L n) :=
    fun J => ((hCells L hL k n hn).2 J).1
  have : Finite (I.ImageCarrier L n) := hFin I
  have : Finite (I'.ImageCarrier L n) := hFin I'
  have : Finite (I''.ImageCarrier L n) := hFin I''
  have hCA := finite_near L hEvery I'' I hR
  have hBA := finite_near L hEvery I' I (R := 2 * R) (by positivity)
  have hAC := finite_near L hEvery I I'' hR
  have hBil := isFinSuppBilinear_wPairing_localBilinear hH hCA (I''.toPeriodicData L).weightOf
    (I''.lift L n f'')
  have hBilM : IsFinSuppBilinear fun (f : I.ImageCarrier L n → ℂ) (f' : I'.ImageCarrier L n → ℂ) =>
      quotBracket L n I'' f'' (Hs f f') := by
    have hs : ∀ u : I''.ImageCarrier L n → ℂ, Summable fun i =>
        ((I''.imageWeight L n i : ℝ) : ℂ) * (f'' i * u i) :=
      fun u => summable_weighted_right _ _ (Set.toFinite _)
    refine ⟨fun f g f' _ _ _ => ?_, fun c f f' _ _ => ?_, fun f f' g' _ _ _ => ?_,
      fun c f f' _ _ => ?_⟩
    · simp only [map_add, LinearMap.add_apply]
      exact wPairing_add_right _ (hs _) (hs _)
    · simp only [map_smul, LinearMap.smul_apply]
      exact wPairing_smul_right _ c _ _
    · simp only [map_add]
      exact wPairing_add_right _ (hs _) (hs _)
    · simp only [map_smul]
      exact wPairing_smul_right _ c _ _
  have hTex :=
    existsUnique_kernel_of_bilinear (w := (I.toPeriodicData L).weightOf) (weightOf_ofReal_ne_zero L I) hBil
  obtain ⟨M0, hM0, hM0u⟩ :=
    existsUnique_kernel_of_bilinear (w := I.imageWeight L n) (imageWeight_ofReal_ne_zero L n I) hBilM
  refine ⟨fun f f' hf hf' => hasFiniteSupport_localBilinear hH hCA hf (isBoundedFn_of_hasFiniteSupport hf'),
    hTex,
    ⟨M0, fun f f' => hM0 f f' (Set.toFinite _) (Set.toFinite _),
      fun M' hM' => hM0u M' fun f f' _ _ => hM' f f'⟩, ?_⟩
  intro T M hT hM
  have hT' : ∀ f f', HasFiniteSupport f → HasFiniteSupport f' →
      wPairing (I.toPeriodicData L).weightOf f (applyKernel T f') =
        wPairing (I''.toPeriodicData L).weightOf (I''.lift L n f'') (H f f') := hT
  have hTloc : IsRLocal L I' I (2 * R) T :=
    isLocalKernel_of_relation hH (weightOf_ofReal_ne_zero L I) hT'
  have hdesc : KernelDescends L n I' I T M := by
    refine ⟨⟨2 * R, by positivity, hTloc⟩, fun f' => ?_⟩
    have bg := lift_isBoundedFn L n f'
    obtain ⟨N, hN, -⟩ := hMat I I'' (Hs.flip f')
    have hSloc : IsRLocal L I I'' R (partialKernel H (I'.lift L n f')) :=
      partialKernel_isLocalKernel hH bg
    have hSdesc : KernelDescends L n I I'' (partialKernel H (I'.lift L n f')) N := by
      refine ⟨⟨R, hR, hSloc⟩, fun f => ?_⟩
      rw [applyKernel_partialKernel hH hAC bg (lift_isBoundedFn L n f), hper f f',
        ← hN f (Set.mem_univ _)]
      rfl
    have hadj := (hEvery I I'' R hR _ hSloc).2.2.2
    have hTr := (hSP I I'' I R hR _ _ 0 N N 0 hSloc hSloc (fun _ _ _ => rfl) hSdesc hSdesc
      (kernelDescends_zero L n I I)).2.2.2.2.2 (by linarith)
    have hNM : applyKernel (quotMatrixT L n I I'' N) f'' = applyKernel M f' := by
      funext κ
      have hw := imageWeight_ofReal_ne_zero L n I κ
      apply mul_left_cancel₀ hw
      have h1 : ((I.imageWeight L n κ : ℝ) : ℂ) * applyKernel M f' κ =
          quotBracket L n I'' f'' (Hs (pointIndicator κ) f') := by
        rw [← wPairing_pointIndicator]
        exact hM (pointIndicator κ) f'
      have h2 : Hs (pointIndicator κ) f' = applyKernel N (pointIndicator κ) := hN _ (Set.mem_univ _)
      rw [h1, h2]
      show _ * (∑' κ', quotMatrixT L n I I'' N κ κ' * f'' κ') =
        ∑' κ', ((I''.imageWeight L n κ' : ℝ) : ℂ) * (f'' κ' * applyKernel N (pointIndicator κ) κ')
      rw [← tsum_mul_left]
      refine tsum_congr fun κ' => ?_
      rw [applyKernel_pointIndicator]
      show _ * ((((I''.imageWeight L n κ' / I.imageWeight L n κ : ℝ)) : ℂ) * N κ' κ * f'' κ') = _
      push_cast
      field_simp
    funext ι
    have hw := weightOf_ofReal_ne_zero L I ι
    apply mul_left_cancel₀ hw
    have hs1 := weight_mul_applyKernel_of_bounded hH hBA hT' hTloc bg ι
    have hs2 : H (pointIndicator ι) (I'.lift L n f') =
        applyKernel (partialKernel H (I'.lift L n f')) (pointIndicator ι) :=
      (applyKernel_partialKernel hH hAC bg
        (isBoundedFn_of_hasFiniteSupport (pointIndicator_hasFiniteSupport ι))).symm
    have hs3 : wPairing (I.toPeriodicData L).weightOf
        (applyKernel (kernelT L I I'' (partialKernel H (I'.lift L n f')))
          (I''.lift L n f'')) (pointIndicator ι) =
        wPairing (I''.toPeriodicData L).weightOf (I''.lift L n f'')
          (applyKernel (partialKernel H (I'.lift L n f')) (pointIndicator ι)) :=
      hadj _ _ (pointIndicator_hasFiniteSupport ι)
    rw [hs1, hs2, ← hs3, hTr.2.2.2 f'', hNM, wPairing_comm, wPairing_pointIndicator]
  have htr := (hSP I' I I' (2 * R) (by positivity) T T 0 M M 0 hTloc hTloc (fun _ _ _ => rfl)
    hdesc hdesc (kernelDescends_zero L n I' I')).2.2.2.2.2 (by linarith)
  exact ⟨hTloc, hdesc, htr.2.2⟩
end YangMills.Construction.LocalKernels.LocalBilinearKernels
end
