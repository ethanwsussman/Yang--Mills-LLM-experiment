import YangMills.Construction.Towers.TheMassiveKernelsUnderTheDilation
import YangMills.Construction.Towers.TheSecondDifferentialsOfTheMassiveFunctionsAtTheBackgroundsProof
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.ScaledSecondDerivs
open PeriodicOperators
open PeriodicOperators.LogDetSecondDerivs
open Scaling
open Coordinates.ComplexCoordinates.LogDetSecondDeriv (asLine scalarSecondDeriv)
section Carried
def CarriesShift (J J' : PeriodicData) (d : J.Carrier ≃ J'.Carrier) (m : ℕ) : Prop :=
  ∀ (n : Fin 4 → ℤ) (ι : J.Carrier), d (J.translate n ι) = J'.translate (m • n) (d ι)
variable {J J' : PeriodicData} {d : J.Carrier ≃ J'.Carrier} {m s s' : ℕ}
theorem smul_smul_of_eq (hs : s' = m * s) (n : Fin 4 → ℤ) : m • s • n = s' • n := by
  rw [hs, mul_smul]
def quotEquiv (h : CarriesShift J J' d m) (hs : s' = m * s) : J.QuotMod s ≃ J'.QuotMod s' where
  toFun := Quot.map d (by
    rintro a _ ⟨n, rfl⟩
    exact ⟨n, by rw [h, smul_smul_of_eq hs]⟩)
  invFun := Quot.map d.symm (by
    rintro a _ ⟨n, rfl⟩
    refine ⟨n, d.injective ?_⟩
    rw [h, Equiv.apply_symm_apply, Equiv.apply_symm_apply, smul_smul_of_eq hs])
  left_inv q := by
    induction q using Quot.ind with
    | mk ι => exact congrArg (Quot.mk _) (d.symm_apply_apply ι)
  right_inv q := by
    induction q using Quot.ind with
    | mk ι => exact congrArg (Quot.mk _) (d.apply_symm_apply ι)
theorem descendField_liftQuotField (F : PeriodicData) (s : ℕ) (ζ : F.QuotMod s → ℂ) :
    descendField F s (liftQuotField F s ζ) = ζ := by
  funext q
  induction q using Quot.ind with
  | mk ι =>
    have spec := Classical.epsilon_spec
      (p := fun z => ∀ κ, F.mkQuot s κ = Quot.mk _ ι → liftQuotField F s ζ κ = z)
      ⟨ζ (Quot.mk _ ι), fun κ hκ => by simp only [liftQuotField, hκ]⟩
    exact (spec ι rfl).symm
theorem descendMatrix_mkQuot {K : PeriodicData} {t : ℕ} {G : K.Carrier → K.Carrier → ℂ}
    (h₁ : ∀ (n : Fin 4 → ℤ) x y, G (K.translate (t • n) x) y = G x y)
    (h₂ : ∀ (n : Fin 4 → ℤ) x y, G x (K.translate (t • n) y) = G x y) (a b : K.Carrier) :
    descendMatrix K K t G (K.mkQuot t a) (K.mkQuot t b) = G a b := by
  have spec := Classical.epsilon_spec
    (p := fun z => ∀ ι' ι, K.mkQuot t ι' = K.mkQuot t a → K.mkQuot t ι = K.mkQuot t b →
      G ι' ι = z)
    ⟨G a b, fun ι' ι e' e => by
      have l₁ : G ι' ι = G a ι :=
        congrArg (Quot.lift (fun x => G x ι) (by rintro x _ ⟨n, rfl⟩; exact (h₁ n x ι).symm)) e'
      have l₂ : G a ι = G a b :=
        congrArg (Quot.lift (fun y => G a y) (by rintro y _ ⟨n, rfl⟩; exact (h₂ n a y).symm)) e
      exact l₁.trans l₂⟩
  exact (spec a b rfl rfl).symm
end Carried
section Matrices
variable {F F' I I' : PeriodicData} {dF : F.Carrier ≃ F'.Carrier} {dI : I.Carrier ≃ I'.Carrier}
  {m s s' : ℕ} {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
  {T' : (F'.Carrier → ℂ) → I'.Carrier → I'.Carrier → ℂ} {c : ℂ}
theorem liftQuotField_comp_symm (hF : CarriesShift F F' dF m) (hs : s' = m * s)
    (ζ : F.QuotMod s → ℂ) :
    liftQuotField F s ζ ∘ dF.symm = liftQuotField F' s' (ζ ∘ (quotEquiv hF hs).symm) := rfl
theorem periodicValue_carried (hF : CarriesShift F F' dF m) (hI : CarriesShift I I' dI m)
    (hs : s' = m * s) (hT : ∀ f ι' ι, T f ι' ι = c * T' (f ∘ dF.symm) (dI ι') (dI ι))
    (ζ : F.QuotMod s → ℂ) (ι' ι : I.Carrier) :
    periodicValue F I I T s ζ ι' ι =
      c * periodicValue F' I' I' T' s' (ζ ∘ (quotEquiv hF hs).symm) (dI ι') (dI ι) := by
  simp only [periodicValue, periodization]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [hT, liftQuotField_comp_symm hF hs, hI, smul_smul_of_eq hs]
theorem shiftField_liftQuotField (F : PeriodicData) (t : ℕ) (ζ : F.QuotMod t → ℂ)
    (a : Fin 4 → ℤ) :
    shiftField F (t • a) (liftQuotField F t ζ) = liftQuotField F t ζ := by
  funext κ
  have e : F.mkQuot t κ = F.mkQuot t (F.translate (-(t • a)) κ) :=
    Quot.sound ⟨-a, by rw [smul_neg]⟩
  simp only [shiftField, liftQuotField, e]
theorem periodicValue_translate_right (hP : IsPeriodic I') (t : ℕ)
    (ζ : F'.QuotMod t → ℂ) (a : Fin 4 → ℤ) (x y : I'.Carrier) :
    periodicValue F' I' I' T' t ζ x (I'.translate (t • a) y) = periodicValue F' I' I' T' t ζ x y := by
  simp only [periodicValue, periodization]
  rw [← (Equiv.addLeft a).tsum_eq fun n : Fin 4 → ℤ =>
    T' (liftQuotField F' t ζ) x (I'.translate (t • n) y)]
  refine tsum_congr fun n => ?_
  rw [Equiv.coe_addLeft, smul_add, hP.translate_add]
theorem periodicValue_translate_left (hP : IsPeriodic I') {ρ R : ℝ}
    (hloc : IsLocalWith F' I' I' T' ρ R) (t : ℕ) (ζ : F'.QuotMod t → ℂ)
    (hb : IsSupBelow F' (liftQuotField F' t ζ) ρ) (a : Fin 4 → ℤ) (x y : I'.Carrier) :
    periodicValue F' I' I' T' t ζ (I'.translate (t • a) x) y = periodicValue F' I' I' T' t ζ x y := by
  simp only [periodicValue, periodization]
  rw [← (Equiv.subRight a).tsum_eq fun n : Fin 4 → ℤ =>
    T' (liftQuotField F' t ζ) x (I'.translate (t • n) y)]
  refine tsum_congr fun n => ?_
  have e : I'.translate (t • n) y = I'.translate (t • a) (I'.translate (t • (n - a)) y) := by
    rw [← hP.translate_add, ← smul_add, sub_add_cancel]
  have cov := hloc.shift_covariant _ hb (t • a) x (I'.translate (t • (n - a)) y)
  rw [shiftField_liftQuotField] at cov
  rw [e, cov, Equiv.subRight_apply]
theorem descendMatrix_carried (hF : CarriesShift F F' dF m) (hI : CarriesShift I I' dI m)
    (hs : s' = m * s) (hT : ∀ f ι' ι, T f ι' ι = c * T' (f ∘ dF.symm) (dI ι') (dI ι))
    (hP : IsPeriodic I') {ρ R : ℝ} (hloc : IsLocalWith F' I' I' T' ρ R)
    (ζ : F.QuotMod s → ℂ)
    (hb : IsSupBelow F' (liftQuotField F' s' (ζ ∘ (quotEquiv hF hs).symm)) ρ)
    (q₁ q₂ : I.QuotMod s) :
    descendMatrix I I s (periodicValue F I I T s ζ) q₁ q₂ =
      c * descendMatrix I' I' s' (periodicValue F' I' I' T' s' (ζ ∘ (quotEquiv hF hs).symm))
        (quotEquiv hI hs q₁) (quotEquiv hI hs q₂) := by
  induction q₁ using Quot.ind with
  | mk a =>
    induction q₂ using Quot.ind with
    | mk b =>
      have l := fun n x y => periodicValue_translate_left (T' := T') hP hloc s' _ hb n x y
      have r := fun n x y =>
        periodicValue_translate_right (T' := T') hP s' (ζ ∘ (quotEquiv hF hs).symm) n x y
      have e₁ : ∀ (n : Fin 4 → ℤ) x y, periodicValue F I I T s ζ (I.translate (s • n) x) y =
          periodicValue F I I T s ζ x y := fun n x y => by
        rw [periodicValue_carried hF hI hs hT, periodicValue_carried hF hI hs hT, hI,
          smul_smul_of_eq hs, l]
      have e₂ : ∀ (n : Fin 4 → ℤ) x y, periodicValue F I I T s ζ x (I.translate (s • n) y) =
          periodicValue F I I T s ζ x y := fun n x y => by
        rw [periodicValue_carried hF hI hs hT, periodicValue_carried hF hI hs hT, hI,
          smul_smul_of_eq hs, r]
      change descendMatrix I I s _ (I.mkQuot s a) (I.mkQuot s b) =
        c * descendMatrix I' I' s' _ (I'.mkQuot s' (dI a)) (I'.mkQuot s' (dI b))
      rw [descendMatrix_mkQuot l r, descendMatrix_mkQuot e₁ e₂,
        periodicValue_carried hF hI hs hT]
def quotFunEquiv (hI : CarriesShift I I' dI m) (hs : s' = m * s) :
    (I.QuotMod s → ℂ) ≃ₗ[ℂ] (I'.QuotMod s' → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (quotEquiv hI hs).symm
theorem quotOperator_carried (hF : CarriesShift F F' dF m) (hI : CarriesShift I I' dI m)
    (hs : s' = m * s) (hT : ∀ f ι' ι, T f ι' ι = c * T' (f ∘ dF.symm) (dI ι') (dI ι))
    (hP : IsPeriodic I') {ρ R : ℝ} (hloc : IsLocalWith F' I' I' T' ρ R)
    (hfin : Finite (I'.QuotMod s')) (ζ : F.QuotMod s → ℂ)
    (hb : IsSupBelow F' (liftQuotField F' s' (ζ ∘ (quotEquiv hF hs).symm)) ρ) :
    quotOperator F I T s ζ = (quotFunEquiv hI hs).symm.conj
      (c • quotOperator F' I' T' s' (ζ ∘ (quotEquiv hF hs).symm)) := by
  have hfin' : Finite (I.QuotMod s) := Finite.of_equiv _ (quotEquiv hI hs).symm
  refine LinearMap.ext fun f => funext fun q₁ => ?_
  change linearMapOfEntries _ f q₁ = c * linearMapOfEntries _ (f ∘ (quotEquiv hI hs).symm)
    (quotEquiv hI hs q₁)
  rw [linearMapOfEntries_eq_applyKernel, linearMapOfEntries_eq_applyKernel]
  simp only [applyKernel]
  rw [← (quotEquiv hI hs).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun q₂ => ?_
  rw [descendMatrix_carried hF hI hs hT hP hloc ζ hb]
  simp [mul_assoc]
theorem det_inverse_mul_conj_smul {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (Φ : V ≃ₗ[ℂ] W) (hc : c ≠ 0) (A B : Module.End ℂ V) :
    LinearMap.det (Ring.inverse (Φ.conj (c • A)) * Φ.conj (c • B)) =
      LinearMap.det (Ring.inverse A * B) := by
  have hconj : ∀ X : Module.End ℂ V, Φ.conj X = Φ.conjRingEquiv X := fun _ => rfl
  have step₁ : ∀ X : Module.End ℂ V, Ring.inverse (Φ.conjRingEquiv X) =
      Φ.conjRingEquiv (Ring.inverse X) := fun X => by
    by_cases h : IsUnit X
    · obtain ⟨u, rfl⟩ := h
      have := Ring.inverse_unit (Units.map (Φ.conjRingEquiv : Module.End ℂ V →* Module.End ℂ W) u)
      rw [Ring.inverse_unit]
      simpa using this
    · rw [Ring.inverse_non_unit _ h, map_zero]
      exact Ring.inverse_non_unit _ (fun h' => h ((isUnit_map_iff Φ.conjRingEquiv X).1 h'))
  have hw : IsUnit (algebraMap ℂ (Module.End ℂ V) c) := (IsUnit.mk0 c hc).map _
  obtain ⟨w, hw⟩ := hw
  have step₂ : Ring.inverse (c • A) * (c • B) = Ring.inverse A * B := by
    have hA : ∀ X : Module.End ℂ V, c • X = (w : Module.End ℂ V) * X := fun X => by
      rw [hw, Algebra.smul_def]
    by_cases h : IsUnit A
    · obtain ⟨u, rfl⟩ := h
      rw [hA, hA, ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, mul_inv_rev,
        Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
    · rw [Ring.inverse_non_unit _ h, hA, Ring.inverse_non_unit _ (fun h' => h
        ((Units.isUnit_units_mul w A).1 h')), zero_mul, zero_mul]
  rw [hconj, hconj, step₁, ← map_mul, step₂]
  exact LinearMap.det_conj (Ring.inverse A * B) Φ
theorem normalizedDet_carried (hF : CarriesShift F F' dF m) (hI : CarriesShift I I' dI m)
    (hs : s' = m * s) (hT : ∀ f ι' ι, T f ι' ι = c * T' (f ∘ dF.symm) (dI ι') (dI ι))
    (hc : c ≠ 0) (hP : IsPeriodic I') {ρ R : ℝ}
    (hloc : IsLocalWith F' I' I' T' ρ R) (hfin : Finite (I'.QuotMod s'))
    (ζ : F.QuotMod s → ℂ)
    (hb : IsSupBelow F' (liftQuotField F' s' (ζ ∘ (quotEquiv hF hs).symm)) ρ) :
    normalizedDet F I T s ζ =
      normalizedDet F' I' T' s' (ζ ∘ (quotEquiv hF hs).symm) := by
  have hb₀ : IsSupBelow F' (liftQuotField F' s'
      ((0 : F.QuotMod s → ℂ) ∘ (quotEquiv hF hs).symm)) ρ :=
    ⟨0, hloc.radius_pos, fun κ => by simp [liftQuotField]⟩
  have h₀ := quotOperator_carried hF hI hs hT hP hloc hfin 0 hb₀
  have h₁ := quotOperator_carried hF hI hs hT hP hloc hfin ζ hb
  have hz : (0 : F.QuotMod s → ℂ) ∘ (quotEquiv hF hs).symm = 0 := rfl
  rw [hz] at h₀
  simp only [normalizedDet]
  rw [h₀, h₁]
  exact det_inverse_mul_conj_smul _ hc _ _
end Matrices
section Differentials
theorem scalarSecondDeriv_congr {N : ℕ} {g g' : Coordinates.ComplexCoordinates N → ℂ}
    (h : g =ᶠ[𝓝 0] g') (k l : Coordinates.ComplexCoordinates N) :
    scalarSecondDeriv g 0 k l = scalarSecondDeriv g' 0 k l := by
  have h₁ : asLine g =ᶠ[𝓝 0] asLine g' :=
    h.mono fun z hz => funext fun _ => by simp only [asLine, hz]
  have h₂ := h₁.fderiv (𝕜 := ℝ)
  have hc : Tendsto (fun t : ℝ => (0 : Coordinates.ComplexCoordinates N) + t • k) (𝓝 0) (𝓝 0) := by
    have : Continuous fun t : ℝ => (0 : Coordinates.ComplexCoordinates N) + t • k := by fun_prop
    simpa using this.tendsto 0
  have h₃ : Coordinates.ComplexCoordinates.derivAlongLine (asLine g) 0 k l =ᶠ[𝓝 0]
      Coordinates.ComplexCoordinates.derivAlongLine (asLine g') 0 k l :=
    (hc.eventually h₂).mono fun t ht => by
      simp only [Coordinates.ComplexCoordinates.derivAlongLine, ht]
  simp only [scalarSecondDeriv, Coordinates.ComplexCoordinates.secondDeriv]
  rw [h₃.deriv_eq]
variable {F F' I I' : PeriodicData} {dF : F.Carrier ≃ F'.Carrier} {dI : I.Carrier ≃ I'.Carrier}
  {m s s' : ℕ} {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
  {T' : (F'.Carrier → ℂ) → I'.Carrier → I'.Carrier → ℂ} {c : ℂ}
theorem logDetSecondDeriv_carried (hF : CarriesShift F F' dF m) (hI : CarriesShift I I' dI m)
    (hs : s' = m * s) (hT : ∀ f ι' ι, T f ι' ι = c * T' (f ∘ dF.symm) (dI ι') (dI ι))
    (hc : c ≠ 0) (hP : IsPeriodic I') {ρ R : ℝ}
    (hloc : IsLocalWith F' I' I' T' ρ R) (hfin : Finite (I'.QuotMod s'))
    {N : ℕ} (e : Fin N ≃ F.QuotMod s) (ζ ζ₂ : F.QuotMod s → ℂ) :
    logDetSecondDeriv F I T e ζ ζ₂ =
      logDetSecondDeriv F' I' T' (e.trans (quotEquiv hF hs))
        (ζ ∘ (quotEquiv hF hs).symm) (ζ₂ ∘ (quotEquiv hF hs).symm) := by
  have hev : logDetInCoords F I T e =ᶠ[𝓝 0]
      logDetInCoords F' I' T' (e.trans (quotEquiv hF hs)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Coordinates.ComplexCoordinates N) hloc.radius_pos]
      with w hw
    have hw' : ‖w‖ < ρ := by simpa using hw
    have e₁ : ofCoords (e.trans (quotEquiv hF hs)) w =
        ofCoords e w ∘ (quotEquiv hF hs).symm := rfl
    have hb : IsSupBelow F' (liftQuotField F' s'
        (ofCoords e w ∘ (quotEquiv hF hs).symm)) ρ :=
      ⟨‖w‖, hw', fun κ => norm_le_pi_norm w _⟩
    simp only [logDetInCoords, logNormalizedDet]
    rw [e₁, normalizedDet_carried hF hI hs hT hc hP hloc hfin _ hb]
  have hco : ∀ ξ : F.QuotMod s → ℂ, toCoords (e.trans (quotEquiv hF hs))
      (ξ ∘ (quotEquiv hF hs).symm) = toCoords e ξ := fun ξ => by
    funext j
    simp [toCoords]
  simp only [logDetSecondDeriv]
  rw [hco, hco]
  exact scalarSecondDeriv_congr hev _ _
end Differentials
section Lattice
variable {a : ℝ} {N : ℕ}
def intVertex (h : a * N = 1) (n : Fin 4 → ℤ) : InfiniteLattice.LatticePoint a :=
  ⟨castVec n, fun μ => n μ * N, fun μ => by
    have e : ((n μ * (N : ℤ) : ℤ) : ℝ) * a = (n μ : ℝ) * (a * N) := by
      push_cast
      ring
    rw [e, h, mul_one]
    rfl⟩
theorem vertexImage_intShift (h : a * N = 1) (n : Fin 4 → ℤ) (x : InfiniteLattice.LatticePoint a) :
    FullSpace.vertexImage (intShift n) x = x + intVertex h n :=
  Subtype.ext (Classical.epsilon_spec
    (p := fun x' : InfiniteLattice.LatticePoint a =>
      (x' : InfiniteLattice.AmbientSpace) = intShift n x)
    ⟨x + intVertex h n, rfl⟩ |>.trans rfl)
theorem edgeImage_intShift_ends (h : a * N = 1) (n : Fin 4 → ℤ) (b : InfiniteLattice.Link a) :
    (FullSpace.edgeImage (intShift n) b).initial = b.initial + intVertex h n ∧
      (FullSpace.edgeImage (intShift n) b).terminal = b.terminal + intVertex h n := by
  have spec := Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link a =>
      b'.initial = FullSpace.vertexImage (intShift n) b.initial ∧
        b'.terminal = FullSpace.vertexImage (intShift n) b.terminal)
    ⟨⟨FullSpace.vertexImage (intShift n) b.initial, FullSpace.vertexImage (intShift n) b.terminal, by
      obtain ⟨μ, hμ⟩ := b.isAdjacent
      refine ⟨μ, ?_⟩
      rw [vertexImage_intShift h, vertexImage_intShift h, add_sub_add_right_eq_sub]
      exact hμ⟩, rfl, rfl⟩
  have spec' : (FullSpace.edgeImage (intShift n) b).initial =
        FullSpace.vertexImage (intShift n) b.initial ∧
      (FullSpace.edgeImage (intShift n) b).terminal =
        FullSpace.vertexImage (intShift n) b.terminal := spec
  rw [vertexImage_intShift h, vertexImage_intShift h] at spec'
  exact spec'
variable {L k j : ℕ}
theorem shiftEdge_ends (h : meshAt L k j * N = 1) (n : Fin 4 → ℤ)
    (b : PeriodicOperators.PosEdge L k j) :
    (shiftEdge n b).1.initial = b.1.initial + intVertex h n ∧
      (shiftEdge n b).1.terminal = b.1.terminal + intVertex h n := by
  have spec := Classical.epsilon_spec
    (p := fun b' : PeriodicOperators.PosEdge L k j => b'.1 = FullSpace.edgeImage (intShift n) b.1)
    ⟨⟨FullSpace.edgeImage (intShift n) b.1, by
      obtain ⟨μ, hμ⟩ := b.2
      refine ⟨μ, ?_⟩
      rw [(edgeImage_intShift_ends h n b.1).1, (edgeImage_intShift_ends h n b.1).2,
        add_sub_add_right_eq_sub]
      exact hμ⟩, rfl⟩
  have spec' : (shiftEdge n b).1 = FullSpace.edgeImage (intShift n) b.1 := spec
  rw [spec']
  exact edgeImage_intShift_ends h n b.1
theorem meshAt_mul_pow (hL : 0 < L) (k : ℕ) : meshAt L k 0 * ((L ^ k : ℕ) : ℝ) = 1 := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.BackgroundHessians.meshAt_mul_pow <;> assumption
theorem meshAt_zero_mul_one : meshAt L 0 0 * ((1 : ℕ) : ℝ) = 1 := by simp [meshAt]
theorem scaleVertex_intVertex (hL : 0 < L) (n : Fin 4 → ℤ) :
    FullSpace.scaleVertex hL (Nat.zero_le k) 0 (intVertex (meshAt_mul_pow hL k) n) =
      intVertex (meshAt_zero_mul_one (L := L)) (L ^ k • n) :=
  Subtype.ext (by
    rw [FullSpace.coe_scaleVertex, FullSpace.scaling_apply]
    funext μ
    simp [intVertex, castVec])
theorem carriesShift_vertices (hL : 0 < L) (k : ℕ) :
    CarriesShift (colourVertices L k 0) (colourVertices L 0 0) (scaleVertexIndex hL k) (L ^ k) := by
  intro n ι
  change (ι.1, FullSpace.scaleVertex hL (Nat.zero_le k) 0 (FullSpace.vertexImage (intShift n) ι.2)) =
    (ι.1, FullSpace.vertexImage (intShift (L ^ k • n))
      (FullSpace.scaleVertex hL (Nat.zero_le k) 0 ι.2))
  rw [vertexImage_intShift (meshAt_mul_pow hL k), vertexImage_intShift (meshAt_zero_mul_one (L := L)),
    map_add, scaleVertex_intVertex]
theorem carriesShift_edges (hL : 0 < L) (k : ℕ) :
    CarriesShift (colourEdges L k 0) (colourEdges L 0 0) (scaleEdgeIndex hL k) (L ^ k) := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.BackgroundHessians.scaleEdgeIndex_translate <;> assumption
end Lattice
theorem scalingInvariance_holds (hK : ScalingKernels.MassiveKernelsScale)
    (hLoc : Locality.OpFunsLocal) (hIdx : TowerIndexSets.Claim)
    (hQ : Quotients.QuotientTransposeNorm) :
    ScalingInvariance := by
  intro L hL hB k hk z hz
  have hη : 0 < finestMesh L k := by
    simp only [finestMesh, meshAt]
    exact zpow_pos (by exact_mod_cast hL) _
  have hw : 0 < finestMesh L k ^ 2 * z := by positivity
  have hc : ((((finestMesh L k : ℝ) : ℂ)) ^ 2)⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hη.ne'))
  obtain ⟨hP_s, hP_b, -⟩ := hIdx L hB 0 0 le_rfl
  obtain ⟨hzero, -⟩ := hLoc L hB _ hw
  obtain ⟨hlocal_s, hlocal_b, -⟩ := hzero
  obtain ⟨ρ₁, R₁, hm₁⟩ := hlocal_s
  obtain ⟨ρ₂, R₂, hm₂⟩ := hlocal_b
  have hF := carriesShift_edges hL k
  have hI := carriesShift_vertices hL k
  refine ⟨PeriodicLattice.torusSide L 1, ⟨1, one_pos, rfl⟩, fun s _ _ n _ _ N e => ?_⟩
  have hs : 2 * L ^ (n + k) = L ^ k * (2 * L ^ n) := by ring
  have hpos : 0 < 2 * L ^ (n + k) := by positivity
  have hfin_s : Finite ((colourVertices L 0 0).QuotMod (2 * L ^ (n + k))) :=
    (hQ _ _ hP_s hP_s _ hpos).1.2.1
  have hfin_b : Finite ((colourEdges L 0 0).QuotMod (2 * L ^ (n + k))) :=
    (hQ _ _ hP_b hP_b _ hpos).1.2.1
  have hd : ∀ ζ : (colourEdges L k 0).QuotMod (2 * L ^ n) → ℂ,
      scaledQuotField hL k n ζ = ζ ∘ (quotEquiv hF hs).symm := fun ζ => by
    have e₁ : scaledField hL k (liftQuotField (colourEdges L k 0) (2 * L ^ n) ζ) =
        liftQuotField (colourEdges L 0 0) (2 * L ^ (n + k))
          (ζ ∘ (quotEquiv hF hs).symm) := liftQuotField_comp_symm hF hs ζ
    simp only [scaledQuotField]
    rw [e₁, descendField_liftQuotField]
  refine ⟨e.trans (quotEquiv hF hs), fun ζ ζ' => ⟨?_, ?_⟩⟩
  · rw [hd, hd]
    exact logDetSecondDeriv_carried hF hI hs
      (fun f ι' ι => (hK L hL hB k hk z f).1 ι' ι) hc hP_s hm₁ hfin_s e ζ ζ'
  · rw [hd, hd]
    exact logDetSecondDeriv_carried hF (carriesShift_edges hL k) hs
      (fun f ι' ι => (hK L hL hB k hk z f).2 ι' ι) hc hP_b hm₂ hfin_b e ζ ζ'
end YangMills.Construction.Tower.MassiveOpFunctions.ScaledSecondDerivs
end
