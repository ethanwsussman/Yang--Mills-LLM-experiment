import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.PeriodicOperators.MatricesOfALocalOperatorFunctionOnATorusProof
import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open YangMills.Construction.Coordinates (ComplexCoordinates)
open YangMills.Construction.Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
open YangMills.Construction.Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
namespace ParameterIndependence
section Restriction
variable {F : PeriodicData}
theorem fieldExtend_apply {S : Set F.Carrier} {n : ℕ} (e : Fin n ≃ S) (z : ComplexCoordinates n)
    (j : Fin n) : fieldExtend e z ((e j : S) : F.Carrier) = z j :=
  Function.Injective.extend_apply (fun _ _ hab => e.injective (Subtype.ext hab)) z 0 j
theorem fieldValues_fieldExtend {S : Set F.Carrier} {n : ℕ} (e : Fin n ≃ S)
    (z : ComplexCoordinates n) : fieldValues e (fieldExtend e z) = z := by apply _root_.YangMills.Construction.PeriodicOperators.LocalTorusMatrices.fieldValues_fieldExtend <;> assumption
theorem norm_fieldExtend_le {S : Set F.Carrier} {n : ℕ} (e : Fin n ≃ S) (z : ComplexCoordinates n)
    (k : F.Carrier) : ‖fieldExtend e z k‖ ≤ ‖z‖ := by apply _root_.YangMills.Construction.PeriodicOperators.LocalTorusMatrices.norm_fieldExtend_le <;> assumption
theorem isSupBelow_fieldExtend {S : Set F.Carrier} {n : ℕ} (e : Fin n ≃ S)
    {z : ComplexCoordinates n} {r : ℝ} (hz : ‖z‖ < r) : IsSupBelow F (fieldExtend e z) r :=
  ⟨‖z‖, hz, norm_fieldExtend_le e z⟩
theorem isSupBelow_mono {w : F.Carrier → ℂ} {r s : ℝ} (h : IsSupBelow F w s) (hle : s ≤ r) :
    IsSupBelow F w r := by
  obtain ⟨t, ht, hb⟩ := h
  exact ⟨t, ht.trans_le hle, hb⟩
def restrictCoords {S S' : Set F.Carrier} {n n' : ℕ} (hS : S ⊆ S') (e : Fin n ≃ S)
    (e' : Fin n' ≃ S') : ComplexCoordinates n' →ₗ[ℂ] ComplexCoordinates n :=
  LinearMap.funLeft ℂ ℂ fun j => e'.symm ⟨e j, hS (e j).2⟩
variable {S S' : Set F.Carrier} {n n' : ℕ} (hS : S ⊆ S') (e : Fin n ≃ S) (e' : Fin n' ≃ S')
theorem restrictCoords_apply (z : ComplexCoordinates n') (j : Fin n) :
    restrictCoords hS e e' z j = z (e'.symm ⟨e j, hS (e j).2⟩) :=
  rfl
theorem restrictCoords_fieldValues (w : F.Carrier → ℂ) :
    restrictCoords hS e e' (fieldValues e' w) = fieldValues e w := by
  funext j
  rw [restrictCoords_apply]
  show w ((e' (e'.symm ⟨e j, hS (e j).2⟩) : S') : F.Carrier) = w (e j)
  rw [Equiv.apply_symm_apply]
theorem norm_restrictCoords_le (z : ComplexCoordinates n') : ‖restrictCoords hS e e' z‖ ≤ ‖z‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun _ => norm_le_pi_norm z _
theorem fieldExtend_restrictCoords (z : ComplexCoordinates n') {k : F.Carrier} (hk : k ∈ S) :
    fieldExtend e (restrictCoords hS e e' z) k = fieldExtend e' z k := by
  obtain ⟨j, hj⟩ := e.surjective ⟨k, hk⟩
  have hj' : ((e j : S) : F.Carrier) = k := congrArg Subtype.val hj
  subst hj'
  rw [fieldExtend_apply, restrictCoords_apply]
  have h := fieldExtend_apply e' z (e'.symm ⟨e j, hS (e j).2⟩)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm
end Restriction
section Expansions
variable {n m : ℕ} {f g : ComplexCoordinates n → ℂ} {φ : ComplexCoordinates n →ₗ[ℂ] ℂ}
  {β : ComplexCoordinates n →ₗ[ℂ] ComplexCoordinates n →ₗ[ℂ] ℂ}
theorem secondOrder_congr (hfg : f =ᶠ[𝓝 0] g) (hx : IsSecondOrderExpansion f φ β) :
    IsSecondOrderExpansion g φ β := by
  refine ⟨hx.1, hx.2.congr' ?_ EventuallyEq.rfl⟩
  have h0 : f 0 = g 0 := hfg.self_of_nhds
  filter_upwards [hfg] with z hz
  rw [hz, h0]
theorem secondOrder_comp (hx : IsSecondOrderExpansion f φ β)
    (L : ComplexCoordinates m →ₗ[ℂ] ComplexCoordinates n) (hL : ∀ z, ‖L z‖ ≤ ‖z‖) :
    IsSecondOrderExpansion (fun z => f (L z)) (φ ∘ₗ L) (β.compl₁₂ L L) := by
  refine ⟨fun z z' => by simpa using hx.1 (L z) (L z'), ?_⟩
  have ht : Tendsto L (𝓝 0) (𝓝 0) := by
    have h := (LinearMap.continuous_of_finiteDimensional L).tendsto 0
    simpa using h
  have h1 : (fun z : ComplexCoordinates m =>
      f (L z) - (f 0 + φ (L z) + (1 / 2 : ℂ) * β (L z) (L z)))
      =O[𝓝 0] fun z => ‖L z‖ ^ 3 := hx.2.comp_tendsto ht
  have h2 : (fun z : ComplexCoordinates m => ‖L z‖ ^ 3) =O[𝓝 0] fun z => ‖z‖ ^ 3 := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
    simp only [norm_pow, norm_norm, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (hL z) 3
  refine (h1.trans h2).congr' ?_ EventuallyEq.rfl
  filter_upwards with z
  simp
end Expansions
section Entries
variable {F I I' : PeriodicData} {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
theorem entry_eq_of_eqOn (hT : IsLocalWith F I I' T ρ R) (a' : I'.Carrier) (a : I.Carrier)
    {w₁ w₂ : F.Carrier → ℂ} (h₁ : IsSupBelow F w₁ ρ) (h₂ : IsSupBelow F w₂ ρ)
    (hag : ∀ k ∈ nearIndices F (I'.pos a') R, w₁ k = w₂ k) :
    T w₁ a' a = T w₂ a' a := by
  obtain ⟨n, e, h, -, hh⟩ := hT.holo_entry a' a
  rw [hh w₁ h₁, hh w₂ h₂]
  congr 1
  funext j
  exact hag _ (e j).2
theorem nearIndices_mono (y : InfiniteLattice.AmbientSpace) {R₀ : ℝ} (hR : R ≤ R₀) :
    nearIndices F y R ⊆ nearIndices F y R₀ :=
  fun _ hk => le_trans (show _ ≤ R from hk) hR
theorem secondOrder_enlarge (hT : IsLocalWith F I I' T ρ R) {R₀ : ℝ} (hR : R ≤ R₀)
    {a' : I'.Carrier} {a : I.Carrier} {n n₀ : ℕ} (e : Fin n ≃ nearIndices F (I'.pos a') R)
    (e₀ : Fin n₀ ≃ nearIndices F (I'.pos a') R₀)
    {φ : ComplexCoordinates n →ₗ[ℂ] ℂ}
    {β : ComplexCoordinates n →ₗ[ℂ] ComplexCoordinates n →ₗ[ℂ] ℂ}
    (hx : IsSecondOrderExpansion (entryFun T a' a e) φ β) :
    IsSecondOrderExpansion (entryFun T a' a e₀)
      (φ ∘ₗ restrictCoords (nearIndices_mono _ hR) e e₀)
      (β.compl₁₂ (restrictCoords (nearIndices_mono _ hR) e e₀)
        (restrictCoords (nearIndices_mono _ hR) e e₀)) := by
  refine secondOrder_congr ?_ (secondOrder_comp hx _ (norm_restrictCoords_le _ e e₀))
  filter_upwards [Metric.ball_mem_nhds (0 : ComplexCoordinates n₀) hT.radius_pos] with z hz
  have hz' : ‖z‖ < ρ := by simpa using hz
  exact entry_eq_of_eqOn hT a' a
    (isSupBelow_fieldExtend e ((norm_restrictCoords_le _ e e₀ z).trans_lt hz'))
    (isSupBelow_fieldExtend e₀ hz') fun k hk => fieldExtend_restrictCoords _ e e₀ z hk
theorem entryFun_eventuallyEq (hρ : 0 < ρ) {a' : I'.Carrier} {a : I.Carrier} {S : Set F.Carrier}
    {n : ℕ} (e : Fin n ≃ S) {h : ComplexCoordinates n → ℂ}
    (hh : ∀ w, IsSupBelow F w ρ → T w a' a = h (fieldValues e w)) :
    entryFun T a' a e =ᶠ[𝓝 0] h := by
  filter_upwards [Metric.ball_mem_nhds (0 : ComplexCoordinates n) hρ] with z hz
  have hz' : ‖z‖ < ρ := by simpa using hz
  show T (fieldExtend e z) a' a = h z
  rw [hh _ (isSupBelow_fieldExtend e hz'), fieldValues_fieldExtend]
theorem exists_secondOrder (hTaylor : Coordinates.QuadraticTaylor.UniqueExpansion)
    (hT : IsLocalWith F I I' T ρ R) (a' : I'.Carrier) (a : I.Carrier) :
    ∃ (n : ℕ) (e : Fin n ≃ nearIndices F (I'.pos a') R)
      (φ : ComplexCoordinates n →ₗ[ℂ] ℂ)
      (β : ComplexCoordinates n →ₗ[ℂ] ComplexCoordinates n →ₗ[ℂ] ℂ),
      IsSecondOrderExpansion (entryFun T a' a e) φ β := by
  obtain ⟨n, e, h, hol, hh⟩ := hT.holo_entry a' a
  obtain ⟨p, hp, -⟩ := hTaylor n ρ hT.radius_pos h hol
  exact ⟨n, e, p.1, p.2,
    secondOrder_congr (entryFun_eventuallyEq hT.radius_pos e hh).symm hp⟩
theorem secondOrder_coeffs_eq (hTaylor : Coordinates.QuadraticTaylor.UniqueExpansion)
    {ρ₂ R₂ ρ₀ R₀ : ℝ} (h₁ : IsLocalWith F I I' T ρ R)
    (h₂ : IsLocalWith F I I' T ρ₂ R₂) (h₀ : IsLocalWith F I I' T ρ₀ R₀)
    (hR₁ : R ≤ R₀) (hR₂ : R₂ ≤ R₀) {a' : I'.Carrier} {a : I.Carrier} {n₁ n₂ : ℕ}
    (e₁ : Fin n₁ ≃ nearIndices F (I'.pos a') R)
    (e₂ : Fin n₂ ≃ nearIndices F (I'.pos a') R₂)
    {φ₁ : ComplexCoordinates n₁ →ₗ[ℂ] ℂ}
    {β₁ : ComplexCoordinates n₁ →ₗ[ℂ] ComplexCoordinates n₁ →ₗ[ℂ] ℂ}
    {φ₂ : ComplexCoordinates n₂ →ₗ[ℂ] ℂ}
    {β₂ : ComplexCoordinates n₂ →ₗ[ℂ] ComplexCoordinates n₂ →ₗ[ℂ] ℂ}
    (x₁ : IsSecondOrderExpansion (entryFun T a' a e₁) φ₁ β₁)
    (x₂ : IsSecondOrderExpansion (entryFun T a' a e₂) φ₂ β₂) (w w' : F.Carrier → ℂ) :
    φ₁ (fieldValues e₁ w) = φ₂ (fieldValues e₂ w) ∧
      β₁ (fieldValues e₁ w) (fieldValues e₁ w') = β₂ (fieldValues e₂ w) (fieldValues e₂ w') := by
  obtain ⟨n, e, h, hol, hh⟩ := h₀.holo_entry a' a
  have heq := entryFun_eventuallyEq h₀.radius_pos e hh
  have y₁ := secondOrder_congr heq (secondOrder_enlarge h₁ hR₁ e₁ e x₁)
  have y₂ := secondOrder_congr heq (secondOrder_enlarge h₂ hR₂ e₂ e x₂)
  have hp := (hTaylor n ρ₀ h₀.radius_pos h hol).unique
    (y₁ := (_, _)) (y₂ := (_, _)) y₁ y₂
  have hφ := congrArg Prod.fst hp
  have hβ := congrArg Prod.snd hp
  constructor
  · have h3 : φ₁ (restrictCoords (nearIndices_mono _ hR₁) e₁ e (fieldValues e w)) =
        φ₂ (restrictCoords (nearIndices_mono _ hR₂) e₂ e (fieldValues e w)) :=
      LinearMap.congr_fun hφ (fieldValues e w)
    rwa [restrictCoords_fieldValues, restrictCoords_fieldValues] at h3
  · have h3 : β₁ (restrictCoords (nearIndices_mono _ hR₁) e₁ e (fieldValues e w))
          (restrictCoords (nearIndices_mono _ hR₁) e₁ e (fieldValues e w')) =
        β₂ (restrictCoords (nearIndices_mono _ hR₂) e₂ e (fieldValues e w))
          (restrictCoords (nearIndices_mono _ hR₂) e₂ e (fieldValues e w')) :=
      LinearMap.congr_fun (LinearMap.congr_fun hβ (fieldValues e w)) (fieldValues e w')
    rwa [restrictCoords_fieldValues, restrictCoords_fieldValues, restrictCoords_fieldValues,
      restrictCoords_fieldValues] at h3
theorem isOpen_openPolydisk (n : ℕ) (r : ℝ) :
    IsOpen (openPolydisk (0 : ComplexCoordinates n) r) := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isOpen_openPolydisk_zero <;> assumption
theorem isLocalWith_of_le
    (hAffine : Matrices.GroupLieProduct.ExpChartHolomorphy.AffineHolomorphy)
    (hHolo : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hFinite : ∀ (y : InfiniteLattice.AmbientSpace) (s : ℝ), (nearIndices F y s).Finite)
    (hT : IsLocalWith F I I' T ρ R) {ρ₀ R₀ : ℝ} (hρ₀ : 0 < ρ₀) (hρ : ρ₀ ≤ ρ)
    (hR : R ≤ R₀) : IsLocalWith F I I' T ρ₀ R₀ where
  radius_pos := hρ₀
  vanish_far := fun w hw a' a hn =>
    hT.vanish_far w (isSupBelow_mono hw hρ) a' a fun h => hn (h.trans hR)
  shift_covariant := fun w hw => hT.shift_covariant w (isSupBelow_mono hw hρ)
  holo_entry := by
    intro a' a
    obtain ⟨n, e, h, hol, hh⟩ := hT.holo_entry a' a
    have := (hFinite (I'.pos a') R₀).to_subtype
    obtain ⟨n₀, ⟨e₀⟩⟩ := Finite.exists_equiv_fin (nearIndices F (I'.pos a') R₀)
    have hS := nearIndices_mono (F := F) (I'.pos a') hR
    have hRes : ComplexCoordinates.IsHolomorphicIn (openPolydisk (0 : ComplexCoordinates n₀) ρ₀)
        (restrictCoords hS e e₀.symm) := by
      have haff := hAffine n₀ n (fun j => MvPolynomial.X (e₀ ⟨e j, hS (e j).2⟩))
        fun j => (MvPolynomial.totalDegree_X _).le
      have hfun : (fun (z : ComplexCoordinates n₀) (j : Fin n) =>
          MvPolynomial.eval z (MvPolynomial.X (e₀ ⟨e j, hS (e j).2⟩))) =
          restrictCoords hS e e₀.symm := by
        funext z j
        simp only [MvPolynomial.eval_X]
        rfl
      rw [hfun] at haff
      exact ⟨isOpen_openPolydisk _ _, haff.2.1.mono (subset_univ _),
        fun b _ j => haff.2.2 b (mem_univ b) j⟩
    have hmaps : MapsTo (restrictCoords hS e e₀.symm) (openPolydisk (0 : ComplexCoordinates n₀) ρ₀)
        (openPolydisk (0 : ComplexCoordinates n) ρ) := by
      intro z hz j
      have h1 : ‖z (e₀ ⟨e j, hS (e j).2⟩) - (0 : ComplexCoordinates n₀) _‖ < ρ₀ := hz _
      show ‖z (e₀ ⟨e j, hS (e j).2⟩) - (0 : ComplexCoordinates n) j‖ < ρ
      simp only [Pi.zero_apply, sub_zero] at h1 ⊢
      exact h1.trans_le hρ
    refine ⟨n₀, e₀.symm, fun z => h (restrictCoords hS e e₀.symm z), ?_, ?_⟩
    · exact ((hHolo.1 n _ hol.1).1 1 _ hol).2.2.2.1 n₀ _ _ hRes hmaps
    · intro w hw
      rw [hh w (isSupBelow_mono hw hρ)]
      exact congrArg h (restrictCoords_fieldValues hS e e₀.symm w).symm
end Entries
section Formed
variable {F I I' : PeriodicData} {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
theorem coeffOneWith_iff (hTaylor : Coordinates.QuadraticTaylor.UniqueExpansion) {ρ R : ℝ}
    (hT : IsLocalWith F I I' T ρ R) {w : F.Carrier → ℂ} {a' : I'.Carrier} {a : I.Carrier}
    {c : ℂ} (hc : IsLinearCoeff F I I' T w a' a c) (t : ℂ) :
    IsCoeffOneWith F I I' T ρ R w a' a t ↔ t = c := by
  constructor
  · rintro ⟨-, n, e, φ, β, x, rfl⟩
    exact hc ρ R hT n e φ β x
  · rintro rfl
    obtain ⟨n, e, φ, β, x⟩ := exists_secondOrder hTaylor hT a' a
    exact ⟨hT, n, e, φ, β, x, hc ρ R hT n e φ β x⟩
theorem coeffTwoWith_iff (hTaylor : Coordinates.QuadraticTaylor.UniqueExpansion) {ρ R : ℝ}
    (hT : IsLocalWith F I I' T ρ R) {w w' : F.Carrier → ℂ} {a' : I'.Carrier} {a : I.Carrier}
    {c : ℂ} (hc : IsBilinearCoeff F I I' T w w' a' a c) (t : ℂ) :
    IsCoeffTwoWith F I I' T ρ R w w' a' a t ↔ t = c := by
  constructor
  · rintro ⟨-, n, e, φ, β, x, rfl⟩
    exact hc ρ R hT n e φ β x
  · rintro rfl
    obtain ⟨n, e, φ, β, x⟩ := exists_secondOrder hTaylor hT a' a
    exact ⟨hT, n, e, φ, β, x, hc ρ R hT n e φ β x⟩
end Formed
theorem claim_holds
    (hCharts : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hKernels : CovariantFiniteRange.Claim)
    (hTaylor : Coordinates.QuadraticTaylor.UniqueExpansion)
    (hHolo : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    ParameterIndependence.Claim := by
  intro F I I' hF _ _ T ρ R ρ' R' hT hT'
  have hFinite := (hKernels.1 F hF).1
  have hmeet : ∀ {ρ₁ R₁ ρ₂ R₂ : ℝ}, IsLocalWith F I I' T ρ₁ R₁ →
      IsLocalWith F I I' T ρ₂ R₂ →
      IsLocalWith F I I' T (min ρ₁ ρ₂) (max R₁ R₂) := fun h₁ h₂ =>
    isLocalWith_of_le hCharts.1 hHolo hFinite h₁ (lt_min h₁.radius_pos h₂.radius_pos)
      (min_le_left _ _) (le_max_left _ _)
  have hfirst : ∀ (w : F.Carrier → ℂ) (a' : I'.Carrier) (a : I.Carrier),
      IsLinearCoeff F I I' T w a' a (coeffOne F I I' T w a' a) := by
    intro w a' a
    obtain ⟨n, e, φ, β, x⟩ := exists_secondOrder hTaylor hT a' a
    refine Classical.epsilon_spec (p := IsLinearCoeff F I I' T w a' a)
      ⟨φ (fieldValues e w), ?_⟩
    intro ρ₂ R₂ h₂ n₂ e₂ φ₂ β₂ x₂
    exact (secondOrder_coeffs_eq hTaylor hT h₂ (hmeet hT h₂) (le_max_left _ _) (le_max_right _ _)
      e e₂ x x₂ w w).1.symm
  have hsecond : ∀ (w w' : F.Carrier → ℂ) (a' : I'.Carrier) (a : I.Carrier),
      IsBilinearCoeff F I I' T w w' a' a (coeffTwo F I I' T w w' a' a) := by
    intro w w' a' a
    obtain ⟨n, e, φ, β, x⟩ := exists_secondOrder hTaylor hT a' a
    refine Classical.epsilon_spec (p := IsBilinearCoeff F I I' T w w' a' a)
      ⟨β (fieldValues e w) (fieldValues e w'), ?_⟩
    intro ρ₂ R₂ h₂ n₂ e₂ φ₂ β₂ x₂
    exact (secondOrder_coeffs_eq hTaylor hT h₂ (hmeet hT h₂) (le_max_left _ _) (le_max_right _ _)
      e e₂ x x₂ w w').2.symm
  refine ⟨⟨fun ρ₀ R₀ h0 h1 h2 => isLocalWith_of_le hCharts.1 hHolo hFinite hT h0 h1 h2,
    hmeet hT hT'⟩, ⟨fun w w' a' a => ⟨⟨coeffOneWith_iff hTaylor hT (hfirst w a' a),
      coeffOneWith_iff hTaylor hT' (hfirst w a' a), hfirst w a' a⟩,
      ⟨coeffTwoWith_iff hTaylor hT (hsecond w w' a' a),
        coeffTwoWith_iff hTaylor hT' (hsecond w w' a' a), hsecond w w' a' a⟩⟩, rfl⟩, ?_⟩
  intro s _ w h1 h2 h3 h4 a' a t
  exact ⟨fun h => ⟨hT', h3, h4, h.2.2.2⟩, fun h => ⟨hT, h1, h2, h.2.2.2⟩⟩
end ParameterIndependence
end YangMills.Construction.PeriodicOperators
end
