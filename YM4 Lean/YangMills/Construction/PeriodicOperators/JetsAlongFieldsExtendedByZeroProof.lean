import YangMills.Construction.Analysis.QuadraticTaylorUniqueness
import YangMills.Construction.Coordinates.HolomorphicIffDifferentiable
import YangMills.Construction.PeriodicOperators.JetsAlongFieldsExtendedByZero
import YangMills.Construction.PeriodicOperators.NumbersOfALocalOperatorFunctionProof
import YangMills.Construction.PeriodicOperators.TaylorCoefficientsReadOnALargerSetOfIndices
import Mathlib
set_option autoImplicit false
open Filter Topology Asymptotics Set
noncomputable section
namespace YangMills.Construction
open Coordinates
namespace PeriodicOperators
open Coordinates.QuadraticTaylor (IsSecondOrderExpansion)
open Coordinates.ComplexCoordinates.PowerSeriesHolomorphy (openPolydisk)
open LogDetSecondDerivs (descendField)
namespace ExtendByZeroJets
section Extension
variable {G F : PeriodicData} {e : G.Carrier → F.Carrier}
theorem extendByZero_apply (he : IsIndexEmbedding e) (f : G.Carrier → ℂ) (i : G.Carrier) :
    _root_.YangMills.Construction.PeriodicOperators.extendByZero e f (e i) = f i :=
  he.injective.extend_apply f 0 i
theorem extendByZero_of_not_mem_range (f : G.Carrier → ℂ) {k : F.Carrier} (hk : ¬ ∃ i, e i = k) :
    _root_.YangMills.Construction.PeriodicOperators.extendByZero e f k = 0 :=
  Function.extend_apply' f (0 : F.Carrier → ℂ) k hk
theorem extendByZero_zero (he : IsIndexEmbedding e) :
    _root_.YangMills.Construction.PeriodicOperators.extendByZero e (0 : G.Carrier → ℂ) = 0 := by
  funext k
  by_cases h : ∃ i, e i = k
  · obtain ⟨i, rfl⟩ := h
    rw [extendByZero_apply he]
    rfl
  · rw [extendByZero_of_not_mem_range _ h]
    rfl
theorem isSupBelow_extendByZero (he : IsIndexEmbedding e) {f : G.Carrier → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : IsSupBelow G f ρ) : IsSupBelow F (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f) ρ := by
  obtain ⟨r, hr, hb⟩ := hf
  refine ⟨max r 0, max_lt hr hρ, fun k => ?_⟩
  by_cases h : ∃ i, e i = k
  · obtain ⟨i, rfl⟩ := h
    rw [extendByZero_apply he]
    exact (hb i).trans (le_max_left _ _)
  · rw [extendByZero_of_not_mem_range _ h, norm_zero]
    exact le_max_right _ _
theorem extendByZero_shiftField (hF : IsPeriodic F) (he : IsIndexEmbedding e)
    (n : Fin 4 → ℤ) (f : G.Carrier → ℂ) :
    _root_.YangMills.Construction.PeriodicOperators.extendByZero e (shiftField G n f) =
      shiftField F n (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f) := by
  funext k
  show _ = _root_.YangMills.Construction.PeriodicOperators.extendByZero e f (F.translate (-n) k)
  by_cases h : ∃ i, e i = k
  · obtain ⟨i, rfl⟩ := h
    rw [← he.map_translate, extendByZero_apply he, extendByZero_apply he]
    rfl
  · have h' : ¬ ∃ i, e i = F.translate (-n) k := by
      rintro ⟨i, hi⟩
      refine h ⟨G.translate n i, ?_⟩
      rw [he.map_translate, hi, ← hF.translate_add, neg_add_cancel, hF.translate_zero]
    rw [extendByZero_of_not_mem_range _ h, extendByZero_of_not_mem_range _ h']
theorem map_mem_nearIndices (he : IsIndexEmbedding e) {y : InfiniteLattice.AmbientSpace} {R : ℝ}
    {i : G.Carrier} (hi : i ∈ nearIndices G y R) : e i ∈ nearIndices F y R := by
  show TorusMetric.euclidNormVec (F.pos (e i) - y) ≤ R
  rw [he.pos_map]
  exact hi
end Extension
section Values
variable {G F : PeriodicData} {e : G.Carrier → F.Carrier} {y : InfiniteLattice.AmbientSpace} {R : ℝ}
  {l m : ℕ}
open Classical in
def padValues (e : G.Carrier → F.Carrier) (eG : Fin l ≃ nearIndices G y R)
    (eF : Fin m ≃ nearIndices F y R) : ComplexCoordinates l →ₗ[ℂ] ComplexCoordinates m :=
  LinearMap.pi fun j =>
    if h : ∃ i, e (eG i : G.Carrier) = (eF j : F.Carrier) then LinearMap.proj (Classical.choose h) else 0
theorem padValues_apply_cases (eG : Fin l ≃ nearIndices G y R) (eF : Fin m ≃ nearIndices F y R)
    (z : ComplexCoordinates l) (j : Fin m) :
    padValues e eG eF z j = 0 ∨ ∃ i, padValues e eG eF z j = z i := by
  by_cases h : ∃ i, e (eG i : G.Carrier) = (eF j : F.Carrier)
  · right
    refine ⟨Classical.choose h, ?_⟩
    simp [padValues, h]
  · left
    simp [padValues, h]
theorem norm_padValues_le (eG : Fin l ≃ nearIndices G y R)
    (eF : Fin m ≃ nearIndices F y R) (z : ComplexCoordinates l) :
    ‖padValues e eG eF z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun j => ?_
  rcases padValues_apply_cases eG eF z j with h | ⟨i, h⟩
  · rw [h, norm_zero]
    exact norm_nonneg z
  · rw [h]
    exact norm_le_pi_norm z i
theorem padValues_fieldValues (he : IsIndexEmbedding e) (eG : Fin l ≃ nearIndices G y R)
    (eF : Fin m ≃ nearIndices F y R) (f : G.Carrier → ℂ) :
    padValues e eG eF (fieldValues eG f) = fieldValues eF (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f) := by
  funext j
  show _ = _root_.YangMills.Construction.PeriodicOperators.extendByZero e f (eF j : F.Carrier)
  by_cases h : ∃ i, e (eG i : G.Carrier) = (eF j : F.Carrier)
  · have hs := Classical.choose_spec h
    have h1 : padValues e eG eF (fieldValues eG f) j = f (eG (Classical.choose h) : G.Carrier) := by
      simp [padValues, h, fieldValues]
    have h2 := extendByZero_apply he f (eG (Classical.choose h) : G.Carrier)
    rw [hs] at h2
    rw [h1, h2]
  · have h0 : ¬ ∃ i, e i = (eF j : F.Carrier) := by
      rintro ⟨i, hi⟩
      have hw : i ∈ nearIndices G y R := by
        have hj := (eF j).2
        rw [← hi] at hj
        have hj' : TorusMetric.euclidNormVec (F.pos (e i) - y) ≤ R := hj
        rw [he.pos_map] at hj'
        exact hj'
      obtain ⟨i', hi'⟩ := eG.surjective ⟨i, hw⟩
      refine h ⟨i', ?_⟩
      rw [hi']
      exact hi
    rw [extendByZero_of_not_mem_range _ h0]
    simp [padValues, h]
theorem isOpen_openPolydisk_zero (ρ : ℝ) : IsOpen (openPolydisk (0 : ComplexCoordinates l) ρ) := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isOpen_openPolydisk_zero <;> assumption
theorem isHolomorphicIn_comp_padValues
    (hDiff : ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    (eG : Fin l ≃ nearIndices G y R) (eF : Fin m ≃ nearIndices F y R) {ρ : ℝ} (hρ : 0 < ρ)
    {h : ComplexCoordinates m → ℂ}
    (hol : ComplexCoordinates.IsHolomorphicIn (N' := 1) (openPolydisk (0 : ComplexCoordinates m) ρ)
      (fun z _ => h z)) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) (openPolydisk (0 : ComplexCoordinates l) ρ)
      (fun z _ => h (padValues e eG eF z)) := by
  have hd := (hDiff m 1 _ _ (isOpen_openPolydisk_zero ρ)).1 hol
  refine (hDiff l 1 _ _ (isOpen_openPolydisk_zero ρ)).2 ?_
  have hmaps : MapsTo (padValues e eG eF) (openPolydisk (0 : ComplexCoordinates l) ρ)
      (openPolydisk (0 : ComplexCoordinates m) ρ) := by
    intro z hz j
    show ‖padValues e eG eF z j - (0 : ComplexCoordinates m) j‖ < ρ
    rcases padValues_apply_cases eG eF z j with h0 | ⟨i, h0⟩
    · rw [h0]
      simpa using hρ
    · rw [h0]
      exact hz i
  have hL : DifferentiableOn ℂ (padValues e eG eF)
      (openPolydisk (0 : ComplexCoordinates l) ρ) :=
    (LinearMap.toContinuousLinearMap (padValues e eG eF)).differentiable.differentiableOn
  exact hd.comp hL hmaps
end Values
section Numbered
variable {F : PeriodicData}
theorem fieldValues_fieldExtend {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) (z : ComplexCoordinates l) :
    fieldValues e (fieldExtend e z) = z := by apply _root_.YangMills.Construction.PeriodicOperators.LocalTorusMatrices.fieldValues_fieldExtend <;> assumption
theorem isSupBelow_fieldExtend {S : Set F.Carrier} {l : ℕ} (e : Fin l ≃ S) {z : ComplexCoordinates l}
    {ρ : ℝ} (hz : ‖z‖ < ρ) : IsSupBelow F (fieldExtend e z) ρ := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.isSupBelow_fieldExtend <;> assumption
end Numbered
section Local
variable {G F I I' : PeriodicData} {e : G.Carrier → F.Carrier}
  {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
theorem isLocalWith_comp_extendByZero
    (hDiff : ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement)
    (hF : IsPeriodic F) (he : IsIndexEmbedding e)
    (hT : IsLocalWith F I I' T ρ R) :
    IsLocalWith G I I' (fun f => T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f)) ρ R where
  radius_pos := hT.radius_pos
  vanish_far := fun ζ hζ i' i hn =>
    hT.vanish_far _ (isSupBelow_extendByZero he hT.radius_pos hζ) i' i hn
  holo_entry := by
    intro i' i
    obtain ⟨m, eF, h, hol, hh⟩ := hT.holo_entry i' i
    have hfinF : Finite (nearIndices F (I'.pos i') R) := Finite.of_equiv _ eF
    have hfinG : Finite (nearIndices G (I'.pos i') R) :=
      Finite.of_injective
        (fun x : nearIndices G (I'.pos i') R =>
          (⟨e x, map_mem_nearIndices he x.2⟩ : nearIndices F (I'.pos i') R))
        (fun a b hab => Subtype.ext (he.injective (congrArg Subtype.val hab)))
    obtain ⟨l, ⟨eG⟩⟩ := Finite.exists_equiv_fin (nearIndices G (I'.pos i') R)
    refine ⟨l, eG.symm, fun z => h (padValues e eG.symm eF z),
      isHolomorphicIn_comp_padValues hDiff eG.symm eF hT.radius_pos hol, fun ζ hζ => ?_⟩
    show T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e ζ) i' i = h (padValues e eG.symm eF (fieldValues eG.symm ζ))
    rw [hh _ (isSupBelow_extendByZero he hT.radius_pos hζ), padValues_fieldValues he]
  shift_covariant := by
    intro ζ hζ n i' i
    show T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e (shiftField G n ζ)) _ _ = T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e ζ) _ _
    rw [extendByZero_shiftField hF he]
    exact hT.shift_covariant _ (isSupBelow_extendByZero he hT.radius_pos hζ) n i' i
end Local
section Expansions
variable {l m : ℕ} {f g : ComplexCoordinates l → ℂ} {φ φ' : ComplexCoordinates l →ₗ[ℂ] ℂ}
  {β β' : ComplexCoordinates l →ₗ[ℂ] ComplexCoordinates l →ₗ[ℂ] ℂ}
theorem secondOrder_congr (hfg : f =ᶠ[𝓝 0] g) (hx : IsSecondOrderExpansion f φ β) :
    IsSecondOrderExpansion g φ β := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.secondOrder_congr <;> assumption
theorem secondOrder_comp (hx : IsSecondOrderExpansion f φ β)
    (L : ComplexCoordinates m →ₗ[ℂ] ComplexCoordinates l) (hL : ∀ z, ‖L z‖ ≤ ‖z‖) :
    IsSecondOrderExpansion (fun z => f (L z)) (φ ∘ₗ L) (β.compl₁₂ L L) := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.secondOrder_comp <;> assumption
theorem secondOrder_unique (hU : Taylor.QuadraticTaylorUniqueness)
    (hx : IsSecondOrderExpansion f φ β) (hx' : IsSecondOrderExpansion f φ' β') :
    φ = φ' ∧ β = β' := by
  have hdiff : (fun A : ComplexCoordinates l => (φ' - φ) A + (((1 / 2 : ℂ) • (β' - β)) A A))
      =O[𝓝 0] fun A : ComplexCoordinates l => ‖A‖ ^ 3 := by
    refine (hx.2.sub hx'.2).congr' ?_ EventuallyEq.rfl
    filter_upwards with z
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  obtain ⟨h1, h2⟩ := hU (ComplexCoordinates l) (φ' - φ) ((1 / 2 : ℂ) • (β' - β)) hdiff
  have hdiag : ∀ A, β A A = β' A A := fun A => by
    have h := h2 A
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul] at h
    have h' : β' A A - β A A = 0 := by
      rcases mul_eq_zero.1 h with h0 | h0
      · norm_num at h0
      · exact h0
    exact (sub_eq_zero.1 h').symm
  refine ⟨(sub_eq_zero.1 h1).symm, ?_⟩
  refine LinearMap.ext₂ fun z z' => ?_
  have hs := hdiag (z + z')
  simp only [map_add, LinearMap.add_apply] at hs
  rw [hdiag z, hdiag z', hx.1 z' z, hx'.1 z' z] at hs
  have h2' : (2 : ℂ) * β z z' = 2 * β' z z' := by linear_combination hs
  exact mul_left_cancel₀ two_ne_zero h2'
end Expansions
section Coefficients
variable {G F I I' : PeriodicData} {e : G.Carrier → F.Carrier}
  {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ R : ℝ}
theorem coeff_comp_extendByZero (hRead : CoeffsOnSuperset.Claim)
    (hU : Taylor.QuadraticTaylorUniqueness)
    (hG : IsPeriodic G) (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') (he : IsIndexEmbedding e)
    (hT : IsLocalWith F I I' T ρ R)
    (hT' : IsLocalWith G I I' (fun f => T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f)) ρ R)
    (i' : I'.Carrier) (i : I.Carrier) :
    (∀ f, coeffOne G I I' (fun f => T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f)) f i' i =
      coeffOne F I I' T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f) i' i) ∧
    ∀ f f', coeffTwo G I I' (fun f => T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f)) f f' i' i =
      coeffTwo F I I' T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f) (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f') i' i := by
  obtain ⟨m, eF, hF₀, -, hhF⟩ := hT.holo_entry i' i
  obtain ⟨l, eG, -, -, -⟩ := hT'.holo_entry i' i
  obtain ⟨φF, βF, xF, hφF, hβF⟩ := hRead F I I' hF hI hI' T ρ R hT i' i _ m eF subset_rfl
  obtain ⟨φG, βG, xG, hφG, hβG⟩ :=
    hRead G I I' hG hI hI' (fun f => T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f)) ρ R hT' i' i _ l eG subset_rfl
  have hnear : (fun z => entryFun T i' i eF (padValues e eG eF z)) =ᶠ[𝓝 0]
      entryFun (fun f => T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f)) i' i eG := by
    filter_upwards [Metric.ball_mem_nhds (0 : ComplexCoordinates l) hT.radius_pos] with z hz
    have hz' : ‖z‖ < ρ := by simpa using hz
    have hbL : IsSupBelow F (fieldExtend eF (padValues e eG eF z)) ρ :=
      isSupBelow_fieldExtend eF ((norm_padValues_le eG eF z).trans_lt hz')
    have hbG : IsSupBelow F (_root_.YangMills.Construction.PeriodicOperators.extendByZero e (fieldExtend eG z)) ρ :=
      isSupBelow_extendByZero he hT.radius_pos (isSupBelow_fieldExtend eG hz')
    show T (fieldExtend eF (padValues e eG eF z)) i' i =
      T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e (fieldExtend eG z)) i' i
    rw [hhF _ hbL, hhF _ hbG, fieldValues_fieldExtend, ← padValues_fieldValues he eG eF,
      fieldValues_fieldExtend]
  have xL := secondOrder_congr hnear (secondOrder_comp xF (padValues e eG eF)
    (norm_padValues_le eG eF))
  obtain ⟨h1, h2⟩ := secondOrder_unique hU xG xL
  refine ⟨fun f => ?_, fun f f' => ?_⟩
  · rw [← hφG, ← hφF, h1, LinearMap.comp_apply, padValues_fieldValues he]
  · rw [← hβG, ← hβF, h2, LinearMap.compl₁₂_apply, padValues_fieldValues he,
      padValues_fieldValues he]
end Coefficients
section BlochWaves
variable {G F : PeriodicData} {e : G.Carrier → F.Carrier}
theorem descendField_mkQuot {u : F.Carrier → ℂ} (hu : ∀ n k, u (F.translate n k) = u k)
    (k : F.Carrier) : descendField F 1 u (F.mkQuot 1 k) = u k := by
  let v : F.UnitQuot → ℂ := Quot.lift u (by
    rintro a b ⟨n, rfl⟩
    rw [one_nsmul, hu])
  have hv : ∀ k', v (F.mkQuot 1 k') = u k' := fun _ => rfl
  have hex : ∃ z, ∀ k', F.mkQuot 1 k' = F.mkQuot 1 k → u k' = z :=
    ⟨u k, fun k' h => by rw [← hv k', h, hv]⟩
  exact (Classical.epsilon_spec hex k rfl).symm
theorem extendByZero_translate_invariant (hF : IsPeriodic F) (he : IsIndexEmbedding e)
    (ε : G.UnitQuot → ℂ) (n : Fin 4 → ℤ) (k : F.Carrier) :
    _root_.YangMills.Construction.PeriodicOperators.extendByZero e (fun i => ε (G.mkQuot 1 i)) (F.translate n k) =
      _root_.YangMills.Construction.PeriodicOperators.extendByZero e (fun i => ε (G.mkQuot 1 i)) k := by
  have hinv : shiftField G (-n) (fun i => ε (G.mkQuot 1 i)) =
      fun i => ε (G.mkQuot 1 i) := by
    funext i
    show ε (G.mkQuot 1 (G.translate (- -n) i)) = ε (G.mkQuot 1 i)
    rw [neg_neg]
    exact congrArg ε (Quot.sound ⟨n, by rw [one_nsmul]⟩).symm
  have h := congrFun (extendByZero_shiftField hF he (-n) fun i => ε (G.mkQuot 1 i)) k
  rw [hinv] at h
  rw [h]
  show _ = _root_.YangMills.Construction.PeriodicOperators.extendByZero e _ (F.translate (- -n) k)
  rw [neg_neg]
theorem blochWave_extendQuotByZero (hF : IsPeriodic F) (he : IsIndexEmbedding e)
    (p : Fin 4 → ℂ) (ε : G.UnitQuot → ℂ) :
    blochWave F p (extendQuotByZero e ε) =
      _root_.YangMills.Construction.PeriodicOperators.extendByZero e (blochWave G p ε) := by
  funext k
  have hc : extendQuotByZero e ε (F.mkQuot 1 k) =
      _root_.YangMills.Construction.PeriodicOperators.extendByZero e (fun i => ε (G.mkQuot 1 i)) k :=
    descendField_mkQuot (extendByZero_translate_invariant hF he ε) k
  unfold blochWave
  rw [hc]
  by_cases h : ∃ i, e i = k
  · obtain ⟨i, rfl⟩ := h
    rw [extendByZero_apply he, extendByZero_apply he, he.pos_map]
  · rw [extendByZero_of_not_mem_range _ h, extendByZero_of_not_mem_range _ h, mul_zero]
end BlochWaves
theorem claim_holds (hRead : CoeffsOnSuperset.Claim)
    (hU : Taylor.QuadraticTaylorUniqueness)
    (hDiff : ComplexCoordinates.HolomorphicDifferentiable.HolomorphicIffDifferentiableStatement) :
    Claim := by
  rintro G F I I' hG hF hI hI' e he T ⟨ρ, R, hT⟩
  have hT' := isLocalWith_comp_extendByZero hDiff hF he hT
  refine ⟨⟨ρ, R, hT'⟩, fun p εPlus εMinus => ?_⟩
  have hc := coeff_comp_extendByZero hRead hU hG hF hI hI' he hT hT'
  have h0 : coeffZero G I I' (fun f => T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f)) =
      coeffZero F I I' T := by
    show T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e 0) = T 0
    rw [extendByZero_zero he]
  have h1 : ∀ (q : Fin 4 → ℂ) (ε : G.UnitQuot → ℂ),
      coeffOne G I I' (fun f => T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f)) (blochWave G q ε) =
        coeffOne F I I' T (blochWave F q (extendQuotByZero e ε)) := by
    intro q ε
    funext i' i
    rw [blochWave_extendQuotByZero hF he]
    exact (hc i' i).1 _
  have h2 : coeffTwo G I I' (fun f => T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f))
        (blochWave G p εPlus) (blochWave G (-p) εMinus) =
      coeffTwo F I I' T (blochWave F p (extendQuotByZero e εPlus))
        (blochWave F (-p) (extendQuotByZero e εMinus)) := by
    funext i' i
    rw [blochWave_extendQuotByZero hF he, blochWave_extendQuotByZero hF he]
    exact (hc i' i).2 _ _
  have hpred : IsActionTriple G I I' (fun f => T (_root_.YangMills.Construction.PeriodicOperators.extendByZero e f)) p εPlus εMinus =
      IsActionTriple F I I' T p (extendQuotByZero e εPlus)
        (extendQuotByZero e εMinus) := by
    funext A
    unfold IsActionTriple
    rw [h1, h1, h2]
  unfold jetAlong
  rw [hpred, h0]
end ExtendByZeroJets
end PeriodicOperators
end YangMills.Construction
end
