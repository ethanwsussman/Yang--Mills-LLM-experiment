import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.MatricesOfALocalOperatorFunctionOnATorus
import YangMills.Construction.PeriodicOperators.MatricesOnATorusInCoordinates
import Mathlib
set_option autoImplicit false
open Filter Asymptotics Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates
open TorusMetric (euclidNormVec)
open Coordinates.ComplexCoordinates (IsHolomorphicIn stdBasisVector)
open Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn)
open Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
open LocalTorusMatrices (PeriodSumFiniteOnQuot supModulus)
section Entries
variable {J J' : Type}
theorem linearMapEntry_linearMapOfEntries [Finite J] (K : J' → J → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
theorem linearMap_ext_of_entry [Finite J] {M M' : (J → ℂ) →ₗ[ℂ] (J' → ℂ)}
    (h : ∀ c' c, linearMapEntry M c' c = linearMapEntry M' c' c) : M = M' := by
  classical
  refine LinearMap.pi_ext fun c x => ?_
  have hx : (Pi.single c x : J → ℂ) = x • Pi.single c 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  funext c'
  rw [hx, map_smul, map_smul]
  simp only [Pi.smul_apply]
  exact congrArg (x • ·) (h c' c)
theorem isLinearMap_of_linearMapEntry {V : Type} [AddCommMonoid V] [Module ℂ V] [Finite J]
    (G : V → (J → ℂ) →ₗ[ℂ] (J' → ℂ))
    (h : ∀ c' c, IsLinearMap ℂ fun v => linearMapEntry (G v) c' c) : IsLinearMap ℂ G :=
  ⟨fun x y => linearMap_ext_of_entry fun c' c => (h c' c).map_add x y,
    fun a x => linearMap_ext_of_entry fun c' c => (h c' c).map_smul a x⟩
end Entries
section Holomorphic
variable {N l : ℕ}
theorem isHolomorphicScalarIn_iff {O : Set (Coordinates.ComplexCoordinates N)}
    {g : Coordinates.ComplexCoordinates N → ℂ} :
    IsHolomorphicScalarIn O g ↔ IsOpen O ∧ ContinuousOn g O ∧
      ∀ a ∈ O, ∀ j : Fin N, ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ (fun ζ : ℂ => g (a + ζ • stdBasisVector j)) ζ := by
  constructor
  · rintro ⟨hO, hc, hd⟩
    refine ⟨hO, continuousOn_pi.1 hc 0, fun a ha j => ?_⟩
    filter_upwards [hd a ha j] with ζ h
    exact differentiableAt_pi.1 h 0
  · rintro ⟨hO, hc, hd⟩
    refine ⟨hO, continuousOn_pi.2 fun _ => hc, fun a ha j => ?_⟩
    filter_upwards [hd a ha j] with ζ h
    exact differentiableAt_pi.2 fun _ => h
theorem isHolomorphicScalarIn_sum {α : Type} (S : Finset α)
    {O : Set (Coordinates.ComplexCoordinates N)} (hO : IsOpen O)
    {g : α → Coordinates.ComplexCoordinates N → ℂ} (h : ∀ a, IsHolomorphicScalarIn O (g a)) :
    IsHolomorphicScalarIn O fun z => ∑ a ∈ S, g a z := by
  simp only [isHolomorphicScalarIn_iff] at h ⊢
  refine ⟨hO, continuousOn_finsetSum _ fun a _ => (h a).2.1, fun b hb j => ?_⟩
  have hall := (Filter.eventually_all_finset S).2 fun a _ => (h a).2.2 b hb j
  filter_upwards [hall] with ζ hζ
  exact DifferentiableAt.fun_sum hζ
theorem isHolomorphicScalarIn_congr {O : Set (Coordinates.ComplexCoordinates N)}
    {g g' : Coordinates.ComplexCoordinates N → ℂ}
    (h : IsHolomorphicScalarIn O g) (e : ∀ z ∈ O, g' z = g z) :
    IsHolomorphicScalarIn O g' := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.HolomorphicFnOn.congr_on <;> assumption
theorem isHolomorphicIn_coordSelect {O : Set (Coordinates.ComplexCoordinates N)} (hO : IsOpen O)
    (σ : Fin l → Fin N) :
    IsHolomorphicIn O (fun (z : Coordinates.ComplexCoordinates N) (j : Fin l) => z (σ j)) := by
  refine ⟨hO, Continuous.continuousOn (by fun_prop), fun a _ i => Eventually.of_forall fun ζ => ?_⟩
  refine differentiableAt_pi.2 fun j => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop
theorem isOpen_openPolydisk_zero (ρ : ℝ) :
    IsOpen (openPolydisk (0 : Coordinates.ComplexCoordinates N) ρ) := by
  have e : openPolydisk (0 : Coordinates.ComplexCoordinates N) ρ =
      ⋂ j, {z : Coordinates.ComplexCoordinates N |
        ‖z j - (0 : Coordinates.ComplexCoordinates N) j‖ < ρ} := by
    ext z
    simp [openPolydisk]
  rw [e]
  exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
end Holomorphic
section Shifts
variable {I : PeriodicData}
theorem translate_nsmul_injective (h : IsPeriodic I) (s : ℕ) (hs : 0 < s) (ι : I.Carrier) :
    Function.Injective fun n : Fin 4 → ℤ => I.translate (s • n) ι := by
  intro a b e
  have e' : I.translate (s • a) ι = I.translate (s • b) ι := e
  have h0 : I.translate (s • b - s • a) (I.translate (s • a) ι) = I.translate (s • a) ι := by
    rw [← h.translate_add, add_sub_cancel, e']
  have h1 : s • a = s • b := (sub_eq_zero.1 (h.free _ _ h0)).symm
  funext μ
  have h2 := congrFun h1 μ
  simp only [Pi.smul_apply, nsmul_eq_mul] at h2
  exact mul_left_cancel₀ (by exact_mod_cast hs.ne') h2
theorem linearMapEntry_descendMatrix_periodization {s : ℕ} [Finite (I.QuotMod s)]
    {Y : I.Carrier → I.Carrier → ℂ}
    (hY : PeriodSumFiniteOnQuot I I Y s) (ι' ι : I.Carrier) :
    linearMapEntry (linearMapOfEntries (descendMatrix I I s (periodization I I Y s)))
        (I.mkQuot s ι') (I.mkQuot s ι) = periodization I I Y s ι' ι := by
  rw [linearMapEntry_linearMapOfEntries]
  have hz : ∃ z, ∀ a b, I.mkQuot s a = I.mkQuot s ι' → I.mkQuot s b = I.mkQuot s ι →
      periodization I I Y s a b = z :=
    ⟨periodization I I Y s ι' ι, fun a b ha hb => hY.2 _ _ _ _ ha hb⟩
  exact ((Classical.epsilon_spec hz) ι' ι rfl rfl).symm
end Shifts
section Fields
variable {F I : PeriodicData} {N : ℕ} {s : ℕ} {ρ R : ℝ}
theorem isSupBelow_of_mem_openPolydisk (hρ : 0 < ρ) (e : Fin N ≃ F.QuotMod s)
    {z : Coordinates.ComplexCoordinates N}
    (hz : z ∈ openPolydisk (0 : Coordinates.ComplexCoordinates N) ρ) :
    IsSupBelow F (liftQuotField F s fun d => z (e.symm d)) ρ := by
  have hz' : ‖z‖ < ρ := (pi_norm_lt_iff hρ).2 fun j => by simpa using hz j
  exact ⟨‖z‖, hz', fun κ => norm_le_pi_norm z _⟩
theorem exists_holomorphic_entry
    (hPower : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} (hT : IsLocalWith F I I T ρ R)
    (e : Fin N ≃ F.QuotMod s) (ι' ι : I.Carrier) :
    ∃ g : Coordinates.ComplexCoordinates N → ℂ, IsHolomorphicScalarIn (openPolydisk 0 ρ) g ∧
      ∀ z ∈ openPolydisk (0 : Coordinates.ComplexCoordinates N) ρ,
        T (liftQuotField F s fun d => z (e.symm d)) ι' ι = g z := by
  obtain ⟨l, e', h, hh, hv⟩ := hT.holo_entry ι' ι
  let σ : Fin l → Fin N := fun j => e.symm (F.mkQuot s (e' j : F.Carrier))
  have hA := isHolomorphicIn_coordSelect (isOpen_openPolydisk_zero (N := N) ρ) σ
  have hmaps : MapsTo (fun (z : Coordinates.ComplexCoordinates N) (j : Fin l) => z (σ j))
      (openPolydisk 0 ρ) (openPolydisk 0 ρ) := fun z hz j => by simpa using hz (σ j)
  refine ⟨fun z => h fun j => z (σ j),
    (((hPower.1 l _ hh.1).1 1 (fun z _ => h z) hh).2.2.2.1 N _ _ hA hmaps), fun z hz => ?_⟩
  rw [hv _ (isSupBelow_of_mem_openPolydisk hT.radius_pos e hz)]
  congr 1
end Fields
theorem claim_holds (hFinite : CovariantFiniteRange.Claim)
    (hMatrices : LocalTorusMatrices.LocalTorusMatricesClaim)
    (hPower : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hQuotients : Quotients.QuotientTransposeNorm) : Claim := by
  intro F I hF hI T ρ R hT s hs hsR
  obtain ⟨hK, hTaylor⟩ := hMatrices F I I hF hI hI T ρ R hT s hs hsR
  have hclassI : Finite (I.QuotMod s) := (hQuotients I I hI hI s hs).1.2.1
  have rep : ∀ c : I.QuotMod s, ∃ ι, I.mkQuot s ι = c := fun c => Quot.exists_rep c
  have first_entry : ∀ (ζ : F.QuotMod s → ℂ) (ι' ι : I.Carrier),
      linearMapEntry (periodicCoeffOneMatrix F I T s ζ) (I.mkQuot s ι') (I.mkQuot s ι) =
        periodicCoeffOne F I I T s ζ ι' ι := fun ζ ι' ι =>
    linearMapEntry_descendMatrix_periodization (hK ζ ζ _ (Or.inr (Or.inr (Or.inl rfl)))).1 ι' ι
  have second_entry : ∀ (ζ ζ' : F.QuotMod s → ℂ) (ι' ι : I.Carrier),
      linearMapEntry (periodicCoeffTwoMatrix F I T s ζ ζ') (I.mkQuot s ι') (I.mkQuot s ι) =
        periodicCoeffTwo F I I T s ζ ζ' ι' ι := fun ζ ζ' ι' ι =>
    linearMapEntry_descendMatrix_periodization (hK ζ ζ' _ (Or.inr (Or.inr (Or.inr rfl)))).1 ι' ι
  have value_entry : ∀ ζ : F.QuotMod s → ℂ, IsSupBelow F (liftQuotField F s ζ) ρ →
      ∀ ι' ι : I.Carrier,
        linearMapEntry (linearMapOfEntries (descendMatrix I I s (periodicValue F I I T s ζ)))
          (I.mkQuot s ι') (I.mkQuot s ι) = periodicValue F I I T s ζ ι' ι := fun ζ hb ι' ι =>
    linearMapEntry_descendMatrix_periodization (hK ζ ζ _ (Or.inl ⟨hb, rfl⟩)).1 ι' ι
  have sum_form : ∀ ι' ι : I.Carrier, ∃ S : Finset (Fin 4 → ℤ), ∀ ζ : F.Carrier → ℂ,
      IsSupBelow F ζ ρ →
      periodization I I (T ζ) s ι' ι = ∑ n ∈ S, T ζ ι' (I.translate (s • n) ι) := by
    intro ι' ι
    have hfin : {n : Fin 4 → ℤ |
        euclidNormVec (I.pos (I.translate (s • n) ι) - I.pos ι') ≤ R}.Finite :=
      ((hFinite.1 I hI).1 (I.pos ι') R).preimage (f := fun n : Fin 4 → ℤ => I.translate (s • n) ι)
        (translate_nsmul_injective hI s hs ι).injOn
    refine ⟨hfin.toFinset, fun ζ hζ => ?_⟩
    unfold periodization
    exact tsum_eq_sum fun n hn => hT.vanish_far _ hζ _ _ (by simpa using hn)
  refine ⟨isLinearMap_of_linearMapEntry _ fun c' c => ?_,
    fun ζ' => isLinearMap_of_linearMapEntry _ fun c' c => ?_,
    fun ζ => isLinearMap_of_linearMapEntry _ fun c' c => ?_,
    fun ζ ζ' => linearMap_ext_of_entry fun c' c => ?_,
    fun N e => ⟨fun c' c => ?_, fun c' c => ?_, fun hreal v hv c' c => ?_⟩⟩
  · obtain ⟨ι', rfl⟩ := rep c'
    obtain ⟨ι, rfl⟩ := rep c
    simp only [first_entry]
    exact (hTaylor ι' ι).1
  · obtain ⟨ι', rfl⟩ := rep c'
    obtain ⟨ι, rfl⟩ := rep c
    simp only [second_entry]
    exact (hTaylor ι' ι).2.1 ζ'
  · obtain ⟨ι', rfl⟩ := rep c'
    obtain ⟨ι, rfl⟩ := rep c
    simp only [second_entry]
    exact (hTaylor ι' ι).2.2.1 ζ
  · obtain ⟨ι', rfl⟩ := rep c'
    obtain ⟨ι, rfl⟩ := rep c
    rw [second_entry, second_entry]
    exact (hTaylor ι' ι).2.2.2.1 ζ ζ'
  · obtain ⟨ι', rfl⟩ := rep c'
    obtain ⟨ι, rfl⟩ := rep c
    obtain ⟨S, hS⟩ := sum_form ι' ι
    choose g hg hgv using fun n : Fin 4 → ℤ =>
      exists_holomorphic_entry hPower hT e ι' (I.translate (s • n) ι)
    refine isHolomorphicScalarIn_congr
      (isHolomorphicScalarIn_sum S (isOpen_openPolydisk_zero ρ) hg) fun z hz => ?_
    have hb := isSupBelow_of_mem_openPolydisk hT.radius_pos e hz
    rw [value_entry _ hb]
    unfold periodicValue
    rw [hS _ hb]
    exact Finset.sum_congr rfl fun n _ => hgv n z hz
  · obtain ⟨ι', rfl⟩ := rep c'
    obtain ⟨ι, rfl⟩ := rep c
    let P : Coordinates.ComplexCoordinates N → F.QuotMod s → ℂ := fun z d => z (e.symm d)
    have hP : Continuous P := by fun_prop
    have hz0 : openPolydisk (0 : Coordinates.ComplexCoordinates N) ρ ∈
        𝓝 (0 : Coordinates.ComplexCoordinates N) :=
      (isOpen_openPolydisk_zero ρ).mem_nhds fun j => by simpa using hT.radius_pos
    have htend : Tendsto P (𝓝 0)
        (𝓝[{ζ : F.QuotMod s → ℂ | IsSupBelow F (liftQuotField F s ζ) ρ}] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hP.tendsto' 0 0 rfl, ?_⟩
      filter_upwards [hz0] with z hz using isSupBelow_of_mem_openPolydisk hT.radius_pos e hz
    have hmod : ∀ z : Coordinates.ComplexCoordinates N, supModulus F s (P z) ≤ ‖z‖ := fun z =>
      Real.iSup_le (fun _ => norm_le_pi_norm z _) (norm_nonneg z)
    have hmod0 : ∀ ζ : F.QuotMod s → ℂ, 0 ≤ supModulus F s ζ := fun ζ =>
      Real.iSup_nonneg fun _ => norm_nonneg _
    have hbound : (fun z : Coordinates.ComplexCoordinates N => supModulus F s (P z) ^ 3)
        =O[𝓝 0] fun z : Coordinates.ComplexCoordinates N => ‖z‖ ^ 3 := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
      simp only [one_mul, norm_pow, Real.norm_eq_abs, abs_norm, abs_of_nonneg (hmod0 (P z))]
      exact pow_le_pow_left₀ (hmod0 _) (hmod z) 3
    refine (((hTaylor ι' ι).2.2.2.2.comp_tendsto htend).trans hbound).congr' ?_ EventuallyEq.rfl
    filter_upwards [hz0] with z hz
    have hb0 : IsSupBelow F (liftQuotField F s 0) ρ :=
      ⟨0, hT.radius_pos, fun _ => by simp [liftQuotField]⟩
    rw [value_entry _ (isSupBelow_of_mem_openPolydisk hT.radius_pos e hz), value_entry _ hb0,
      first_entry, second_entry]
    rfl
  · obtain ⟨ι', rfl⟩ := rep c'
    obtain ⟨ι, rfl⟩ := rep c
    obtain ⟨S, hS⟩ := sum_form ι' ι
    have hz : (fun j => (v j : ℂ)) ∈ openPolydisk (0 : Coordinates.ComplexCoordinates N) ρ :=
      fun j => by simpa using hv j
    have hb := isSupBelow_of_mem_openPolydisk hT.radius_pos e hz
    rw [value_entry _ hb]
    unfold periodicValue
    rw [hS _ hb, Complex.im_sum]
    exact Finset.sum_eq_zero fun n _ =>
      hreal _ (fun κ => Complex.ofReal_im _) ⟨ρ, R, hT, hb⟩ _ _
end YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates
end
