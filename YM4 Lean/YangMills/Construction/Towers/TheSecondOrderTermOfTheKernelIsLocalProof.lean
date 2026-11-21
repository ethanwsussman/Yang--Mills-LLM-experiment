import YangMills.Construction.Towers.ScaledQOnTheWholeProof
import YangMills.Construction.PeriodicOperators.OperatorFunctionsThatAgreeOnSmallFieldsProof
import YangMills.Construction.Towers.EntriesOfTheIteratedMapsProof
import YangMills.Construction.Towers.TheActionAndCurrentTermsOfTheKernelAreLocalProof
import YangMills.Construction.Towers.TheBackgroundKernelAndTheCovariantLaplacianAreFormedProof
import YangMills.Construction.Towers.TheSecondOrderTermOfTheKernelIsLocal
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.QuadraticTermLocality
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.FieldValueFunctions
open YangMills.Construction.Tower.FullSpace.UnsymmetrisedKernelTerms
open YangMills.Construction.PeriodicOperators.HolomorphicCoordinateClosure
open YangMills.Construction.Tower.FullSpace.IteratedKernelEntries (edgesNear)
open YangMills.Construction.Tower.FullSpace.ReadsCubes (LocalAt IsFinitelySupportedForm)
open YangMills.Construction.Tower.FullSpace.AsDifferentials
  (complexQuadraticTerm topLogRatio topDeriv)
open YangMills.Construction.Tower.AsDifferentials
  (boundedSubmodule quadraticTermAt HasUniqueQuadraticTerm)
open YangMills.Construction.Tower.SupportOfMeans.Unbounded (supportEdges)
open YangMills.Construction.Tower.FullSpace.ElementaryEntries (QuadraticEntries)
open YangMills.Construction.TorusMetric (euclidNormVec)
section PauliCoordinates
theorem sum_pauliCoeff_smul {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • Matrices.ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
end PauliCoordinates
section HolomorphicMatrices
variable {F : PeriodicData} {ρ ρ' : ℝ} {S T : Set F.Carrier}
theorem holomorphicInValues_of_subset (hC : PeriodicOperators.HolomorphicCoordinateClosure.ClosureHolds)
    (hρ : 0 < ρ) (hle : ρ ≤ ρ') (hT : T.Finite) (hS : S ⊆ T) {g : (F.Carrier → ℂ) → ℂ}
    (h : HolomorphicInValuesBelow F ρ' S g) : HolomorphicInValuesBelow F ρ T g :=
  (hC F ρ T hρ hT).of_subset S g hS
    ((hC F ρ' S (hρ.trans_le hle) (hT.subset hS)).of_radius_le ρ g hρ hle h)
def PauliHolomorphicOn (F : PeriodicData) (ρ : ℝ) (T : Set F.Carrier)
    (Φ : (F.Carrier → ℂ) → Matrices.ComplexMatrix2) : Prop :=
  ∃ h : Fin 3 → (F.Carrier → ℂ) → ℂ, (∀ a, HolomorphicInValuesBelow F ρ T (h a)) ∧
    ∀ ζ, IsSupBelow F ζ ρ → Φ ζ = ∑ a, h a ζ • Matrices.ComplexMatrix2.pauliFamily a
theorem PauliHolomorphicOn.congr_below {Φ Ψ : (F.Carrier → ℂ) → Matrices.ComplexMatrix2}
    (e : ∀ ζ, IsSupBelow F ζ ρ → Φ ζ = Ψ ζ) (h : PauliHolomorphicOn F ρ T Φ) :
    PauliHolomorphicOn F ρ T Ψ := by
  obtain ⟨w, hw, he⟩ := h
  exact ⟨w, hw, fun ζ hζ => by rw [← e ζ hζ, he ζ hζ]⟩
theorem PauliHolomorphicOn.smul (hT : ClosureProperties F ρ T) {s : (F.Carrier → ℂ) → ℂ}
    {Φ : (F.Carrier → ℂ) → Matrices.ComplexMatrix2} (hs : HolomorphicInValuesBelow F ρ T s)
    (h : PauliHolomorphicOn F ρ T Φ) : PauliHolomorphicOn F ρ T fun ζ => s ζ • Φ ζ := by
  obtain ⟨w, hw, he⟩ := h
  refine ⟨fun a ζ => s ζ * w a ζ, fun a => hT.mul _ _ hs (hw a), fun ζ hζ => ?_⟩
  show s ζ • Φ ζ = _
  rw [he ζ hζ, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
theorem PauliHolomorphicOn.sum (hT : ClosureProperties F ρ T) {ι : Type} (s : Finset ι)
    (Φ : ι → (F.Carrier → ℂ) → Matrices.ComplexMatrix2)
    (h : ∀ i ∈ s, PauliHolomorphicOn F ρ T (Φ i)) :
    PauliHolomorphicOn F ρ T fun ζ => ∑ i ∈ s, Φ i ζ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ _ => 0, fun _ => hT.const 0, fun ζ _ => by simp⟩
  | insert i s hi ih =>
    obtain ⟨w, hw, he⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨w', hw', he'⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    refine ⟨fun a ζ => w a ζ + w' a ζ, fun a => hT.add _ _ (hw a) (hw' a), fun ζ hζ => ?_⟩
    show ∑ j ∈ insert i s, Φ j ζ = _
    rw [Finset.sum_insert hi, he ζ hζ, show ∑ j ∈ s, Φ j ζ = _ from he' ζ hζ,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => (add_smul _ _ _).symm
theorem PauliHolomorphicOn.halfTrace_mul (hT : ClosureProperties F ρ T)
    {Φ Ψ : (F.Carrier → ℂ) → Matrices.ComplexMatrix2}
    (hΦ : PauliHolomorphicOn F ρ T Φ) (hΨ : PauliHolomorphicOn F ρ T Ψ) :
    HolomorphicInValuesBelow F ρ T fun ζ => Matrices.ComplexMatrix2.halfTrace (Φ ζ * Ψ ζ) := by
  obtain ⟨w, hw, he⟩ := hΦ
  obtain ⟨w', hw', he'⟩ := hΨ
  refine hT.congr_below _ _ (fun ζ hζ => ?_) (hT.sum Finset.univ
    (fun p : Fin 3 × Fin 3 => fun ζ => (w p.1 ζ * w' p.2 ζ) *
      Matrices.ComplexMatrix2.halfTrace
        (Matrices.ComplexMatrix2.pauliFamily p.1 * Matrices.ComplexMatrix2.pauliFamily p.2))
    fun p _ => hT.mul _ _ (hT.mul _ _ (hw p.1) (hw' p.2)) (hT.const _))
  show _ = Matrices.ComplexMatrix2.halfTrace (Φ ζ * Ψ ζ)
  rw [he ζ hζ, he' ζ hζ, Fintype.sum_prod_type]
  simp only [Matrices.ComplexMatrix2.halfTrace, Matrices.ComplexMatrix2.fullTrace,
    Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  ring
end HolomorphicMatrices
section Positions
variable {a : ℝ}
theorem isSupBelow_mono {F : PeriodicData} {ζ : F.Carrier → ℂ} {ρ ρ' : ℝ}
    (h : IsSupBelow F ζ ρ) (hle : ρ ≤ ρ') : IsSupBelow F ζ ρ' := by apply _root_.YangMills.Construction.PeriodicOperators.LocalAgreement.isSupBelow_mono <;> assumption
theorem abs_terminal_sub_initial_le (ha : 0 < a) (b : InfiniteLattice.Link a) (i : Fin 4) :
    |(b.terminal : InfiniteLattice.AmbientSpace) i -
      (b.initial : InfiniteLattice.AmbientSpace) i| ≤ a := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.abs_terminal_sub_initial_le <;> assumption
theorem abs_sub_lt_of_mem_cubeOfOrder {a' : ℝ} (ha' : 0 < a') {L n : ℕ}
    {y : InfiniteLattice.LatticePoint a} {x : InfiniteLattice.AmbientSpace}
    (hx : x ∈ cubeOfOrder L a' n y) (i : Fin 4) :
    |x i - (y : InfiniteLattice.AmbientSpace) i| < (L : ℝ) ^ n * a' / 2 := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.abs_sub_centre_lt_of_mem_cubeOfOrder <;> assumption
variable {L k j : ℕ}
theorem meshAt_pos (hL : 0 < L) : 0 < meshAt L k j :=
  zpow_pos (by exact_mod_cast hL) _
theorem meshAt_eq_pow_mul (hL : 0 < L) : meshAt L k j = (L : ℝ) ^ j * meshAt L k 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.meshAt_eq_pow_mul <;> assumption
theorem meshAt_self : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
theorem abs_initial_sub_lt_of_mem_supportEdges (hL : 0 < L) {c : Edge L k k} {d : Edge L k 0}
    (hd : d ∈ supportEdges c) (i : Fin 4) :
    |(d.initial : InfiniteLattice.AmbientSpace) i -
      (c.initial : InfiniteLattice.AmbientSpace) i| < 3 / 2 := by
  have e : (L : ℝ) ^ k * meshAt L k 0 = 1 := by
    rw [← meshAt_eq_pow_mul hL, meshAt_self]
  have h1 : 0 < meshAt L k k := meshAt_pos hL
  rcases hd.2.1 with hp | hp
  · have h := abs_sub_lt_of_mem_cubeOfOrder (meshAt_pos hL) hp i
    rw [e] at h
    linarith
  · have h := abs_sub_lt_of_mem_cubeOfOrder (meshAt_pos hL) hp i
    rw [e] at h
    have h₂ := abs_terminal_sub_initial_le h1 c i
    have h₃ : meshAt L k k = 1 := meshAt_self
    linarith [abs_sub_le ((d.initial : InfiniteLattice.AmbientSpace) i)
      ((c.terminal : InfiniteLattice.AmbientSpace) i)
      ((c.initial : InfiniteLattice.AmbientSpace) i)]
end Positions
section FinitelySupportedForms
variable {L k : ℕ}
theorem extendOddly_of_isPositivelyOriented {a : ℝ}
    (f : InfiniteLattice.Link a → Matrices.ComplexMatrix2) {b : InfiniteLattice.Link a}
    (hb : b.IsPositivelyOriented) : extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_of_pos <;> assumption
theorem edgeForm_ext {a : ℝ} {B B' : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (h : B ∈ complexEdgeForms a) (h' : B' ∈ complexEdgeForms a)
    (e : ∀ d, d.IsPositivelyOriented → B d = B' d) : B = B' := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.complexEdgeForms_ext <;> assumption
theorem basisForm_apply_of_positive (a : Fin 3) (b : PositiveEdge (meshAt L k 0))
    {c : Edge L k 0} (hc : c.IsPositivelyOriented) :
    (basisForm a b : Edge L k 0 → Matrices.ComplexMatrix2) c =
      open Classical in if c = b.1 then Matrices.ComplexMatrix2.pauliFamily a else 0 := by apply _root_.YangMills.Construction.Tower.RescaledQFullSpace.basisForm_of_positive <;> assumption
theorem basisForm_mem (hL : 0 < L) (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    (basisForm a b : Edge L k 0 → Matrices.ComplexMatrix2) ∈ complexEdgeForms (meshAt L k 0) := by apply _root_.YangMills.Construction.Tower.FullSpace.FieldValueFunctions.LocalComponents.basisForm_mem <;> assumption
theorem basisForm_finitelySupported (hL : 0 < L) (a : Fin 3) (b : PositiveEdge (meshAt L k 0)) :
    IsFinitelySupportedForm (basisForm a b : Edge L k 0 → Matrices.ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.FullSpace.IteratedKernelEntries.basisForm_finitelySupported <;> assumption
theorem zero_finitelySupported :
    IsFinitelySupportedForm (0 : Edge L k 0 → Matrices.ComplexMatrix2) := by apply _root_.YangMills.Construction.Tower.FullSpace.ReadsCubes.isFinitelySupportedForm_zero <;> assumption
theorem smul_add_finitelySupported (z : ℂ) {E E' : Edge L k 0 → Matrices.ComplexMatrix2}
    (h : IsFinitelySupportedForm E) (h' : IsFinitelySupportedForm E') :
    IsFinitelySupportedForm (z • E + E') := by
  refine ⟨Submodule.add_mem _ (Submodule.smul_mem _ _ h.1) h'.1,
    (Set.Finite.union h.2 h'.2).subset fun d hd => ?_⟩
  by_contra hn
  apply hd
  have h₁ : E d.1 = 0 := by
    by_contra h0
    exact hn (Or.inl h0)
  have h₂ : E' d.1 = 0 := by
    by_contra h0
    exact hn (Or.inr h0)
  show (z • E + E') d.1 = 0
  simp [h₁, h₂]
theorem sum_finitelySupported {ι : Type} (s : Finset ι) (z : ι → ℂ)
    (E : ι → Edge L k 0 → Matrices.ComplexMatrix2) (h : ∀ i, IsFinitelySupportedForm (E i)) :
    IsFinitelySupportedForm (∑ i ∈ s, z i • E i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_finitelySupported
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact smul_add_finitelySupported _ (h i) ih
theorem eq_sum_pauliCoeff_basisForm (hL : 0 < L) {B : Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : B ∈ complexEdgeForms (meshAt L k 0)) (S : Finset (PositiveEdge (meshAt L k 0)))
    (h0 : ∀ d, d ∉ S → B d.1 = 0) :
    B = ∑ p ∈ (Finset.univ : Finset (Fin 3)) ×ˢ S,
      pauliCoeff p.1 (B p.2.1) • basisForm p.1 p.2 := by
  classical
  refine edgeForm_ext hB (Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (basisForm_mem hL p.1 p.2)) fun c hc => ?_
  have hmem : ∀ X : Edge L k 0 → Matrices.ComplexMatrix2, X ∈ complexEdgeForms (meshAt L k 0) →
      X c ∈ Matrices.ComplexMatrix2.traceless := fun X hX => hX.1 c hc
  rw [Finset.sum_apply, Finset.sum_product_right]
  simp only [Pi.smul_apply, basisForm_apply_of_positive _ _ hc]
  by_cases hs : (⟨c, hc⟩ : PositiveEdge (meshAt L k 0)) ∈ S
  · rw [Finset.sum_eq_single (⟨c, hc⟩ : PositiveEdge (meshAt L k 0))]
    · simp only [if_true]
      exact (sum_pauliCoeff_smul (hmem B hB)).symm
    · intro d _ hd
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [if_neg fun e => hd (Subtype.ext e.symm), smul_zero]
    · exact fun h => absurd hs h
  · rw [h0 _ hs]
    refine (Finset.sum_eq_zero fun d hd => Finset.sum_eq_zero fun a _ => ?_).symm
    rw [if_neg fun e => hs (by
      have : (⟨c, hc⟩ : PositiveEdge (meshAt L k 0)) = d := Subtype.ext e
      rwa [this]), smul_zero]
end FinitelySupportedForms
section QuadraticTerm
variable {L k : ℕ}
theorem mem_boundedSubmodule_of_finitelySupported {B : Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : IsFinitelySupportedForm B) :
    B ∈ boundedSubmodule (complexEdgeForms (meshAt L k 0)) := by apply _root_.YangMills.Construction.Tower.FullSpace.ReadsCubes.IsFinitelySupportedForm.mem_boundedSubmodule <;> assumption
theorem quadratic_smul_add_left (U : Edge L k 0 → Matrices.ComplexMatrix2) (z : ℂ)
    {E₁ E₂ E₃ : Edge L k 0 → Matrices.ComplexMatrix2}
    (h₁ : IsFinitelySupportedForm E₁) (h₂ : IsFinitelySupportedForm E₂)
    (h₃ : IsFinitelySupportedForm E₃) :
    complexQuadraticTerm L k U (z • E₁ + E₂) E₃ =
      z • complexQuadraticTerm L k U E₁ E₃ + complexQuadraticTerm L k U E₂ E₃ := by apply _root_.YangMills.Construction.Tower.FullSpace.HessianLaplacian.complexQuadraticTerm_add_smul_left <;> assumption
theorem quadratic_smul_add_right (U : Edge L k 0 → Matrices.ComplexMatrix2) (z : ℂ)
    {E₁ E₂ E₃ : Edge L k 0 → Matrices.ComplexMatrix2}
    (h₁ : IsFinitelySupportedForm E₁) (h₂ : IsFinitelySupportedForm E₂)
    (h₃ : IsFinitelySupportedForm E₃) :
    complexQuadraticTerm L k U E₃ (z • E₁ + E₂) =
      z • complexQuadraticTerm L k U E₃ E₁ + complexQuadraticTerm L k U E₃ E₂ := by apply _root_.YangMills.Construction.Tower.FullSpace.HessianLaplacian.complexQuadraticTerm_add_smul_right <;> assumption
theorem quadratic_zero_left (U : Edge L k 0 → Matrices.ComplexMatrix2)
    {G : Edge L k 0 → Matrices.ComplexMatrix2} (hG : IsFinitelySupportedForm G) :
    complexQuadraticTerm L k U 0 G = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.ReadsCubes.complexQuadraticTerm_zero_left <;> assumption
theorem quadratic_zero_right (U : Edge L k 0 → Matrices.ComplexMatrix2)
    {G : Edge L k 0 → Matrices.ComplexMatrix2} (hG : IsFinitelySupportedForm G) :
    complexQuadraticTerm L k U G 0 = 0 := by
  have e := quadratic_smul_add_right U 1 (zero_finitelySupported (L := L) (k := k))
    zero_finitelySupported hG
  simpa using e
theorem quadratic_sum_left (U : Edge L k 0 → Matrices.ComplexMatrix2) {ι : Type}
    (s : Finset ι) (z : ι → ℂ) (E : ι → Edge L k 0 → Matrices.ComplexMatrix2)
    (hE : ∀ i, IsFinitelySupportedForm (E i)) {G : Edge L k 0 → Matrices.ComplexMatrix2}
    (hG : IsFinitelySupportedForm G) :
    complexQuadraticTerm L k U (∑ i ∈ s, z i • E i) G =
      ∑ i ∈ s, z i • complexQuadraticTerm L k U (E i) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using quadratic_zero_left U hG
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      quadratic_smul_add_left U _ (hE i) (sum_finitelySupported s z E hE) hG, ih]
theorem quadratic_sum_right (U : Edge L k 0 → Matrices.ComplexMatrix2) {ι : Type}
    (s : Finset ι) (z : ι → ℂ) (E : ι → Edge L k 0 → Matrices.ComplexMatrix2)
    (hE : ∀ i, IsFinitelySupportedForm (E i)) {G : Edge L k 0 → Matrices.ComplexMatrix2}
    (hG : IsFinitelySupportedForm G) :
    complexQuadraticTerm L k U G (∑ i ∈ s, z i • E i) =
      ∑ i ∈ s, z i • complexQuadraticTerm L k U G (E i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using quadratic_zero_right U hG
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      quadratic_smul_add_right U _ (hE i) (sum_finitelySupported s z E hE) hG, ih]
theorem quadratic_sum_sum (U : Edge L k 0 → Matrices.ComplexMatrix2) {ι κ : Type}
    (s : Finset ι) (t : Finset κ) (x : ι → ℂ) (y : κ → ℂ)
    (E : ι → Edge L k 0 → Matrices.ComplexMatrix2) (G : κ → Edge L k 0 → Matrices.ComplexMatrix2)
    (hE : ∀ i, IsFinitelySupportedForm (E i)) (hG : ∀ j, IsFinitelySupportedForm (G j)) :
    complexQuadraticTerm L k U (∑ i ∈ s, x i • E i) (∑ j ∈ t, y j • G j) =
      ∑ i ∈ s, ∑ j ∈ t, x i • y j • complexQuadraticTerm L k U (E i) (G j) := by
  rw [quadratic_sum_left U s x E hE (sum_finitelySupported t y G hG)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [quadratic_sum_right U t y G hG (hE i), Finset.smul_sum]
theorem quadratic_mem_traceless {U : Edge L k 0 → Matrices.ComplexMatrix2}
    (hH : HasUniqueQuadraticTerm (complexEdgeForms (meshAt L k 0)) (topLogRatio L k U)
      (topDeriv L k U)) {B B' : Edge L k 0 → Matrices.ComplexMatrix2}
    (hB : IsFinitelySupportedForm B) (hB' : IsFinitelySupportedForm B')
    (c : PositiveEdge (meshAt L k k)) :
    complexQuadraticTerm L k U B B' c ∈ Matrices.ComplexMatrix2.traceless := by
  have b₁ := mem_boundedSubmodule_of_finitelySupported hB
  have b₂ := mem_boundedSubmodule_of_finitelySupported hB'
  simp only [complexQuadraticTerm, quadraticTermAt, dif_pos (And.intro b₁ b₂)]
  exact (hH.2.2 ⟨B, b₁⟩ ⟨B', b₂⟩ c).2
theorem quadratic_eq_zero_of_vanish {U : Edge L k 0 → Matrices.ComplexMatrix2} (hR : LocalAt U)
    {B B' : Edge L k 0 → Matrices.ComplexMatrix2} (hB : IsFinitelySupportedForm B)
    (hB' : IsFinitelySupportedForm B') (c : PositiveEdge (meshAt L k k))
    (h : (∀ d ∈ supportEdges c.1, B d = 0) ∨ ∀ d ∈ supportEdges c.1, B' d = 0) :
    complexQuadraticTerm L k U B B' c = 0 := by
  rcases h with h | h
  · rw [hR.quadraticTerm_local c B 0 B' B' hB zero_finitelySupported hB' hB'
      fun d hd => ⟨h d hd, rfl⟩, quadratic_zero_left U hB']
    rfl
  · rw [hR.quadraticTerm_local c B B B' 0 hB hB hB' zero_finitelySupported
      fun d hd => ⟨rfl, h d hd⟩, quadratic_zero_right U hB]
    rfl
end QuadraticTerm
section ShiftedBasis
variable {L k : ℕ} {hL : 0 < L}
abbrev shiftedBasis (hL : 0 < L) (a : Fin 3) (b : PositiveEdge (meshAt L k 0))
    (f : (fieldPeriodicData L k hL).Carrier → ℂ) : Edge L k 0 → Matrices.ComplexMatrix2 :=
  shiftedForm (gaugeFieldOfCoeffs hL f) (basisForm a b)
structure ShiftedBasisControl (hL : 0 < L) (ρ : ℝ) (a : Fin 3)
    (b : PositiveEdge (meshAt L k 0)) : Prop where
  coeffs : CoeffsHolomorphicOn (fieldPeriodicData L k hL) ρ
    (backgroundCoords L k hL (edgesNear L k b.1.initial (7 / 2)))
    (positiveEdgesWithin L k b.1.initial (3 / 2))
    (fun f => restrictToPositiveEdges (shiftedBasis hL a b f))
  mem_forms : ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ →
    shiftedBasis hL a b f ∈ complexEdgeForms (meshAt L k 0)
def IsWithinThree (c : PositiveEdge (meshAt L k k)) (b : PositiveEdge (meshAt L k 0)) : Prop :=
  ∀ i, |(c.1.initial : InfiniteLattice.AmbientSpace) i -
    (b.1.initial : InfiniteLattice.AmbientSpace) i| < 3
section Single
variable {ρ : ℝ} {a : Fin 3} {b : PositiveEdge (meshAt L k 0)}
theorem ShiftedBasisControl.eq_zero_of_far (h : ShiftedBasisControl hL ρ a b)
    {ζ : (fieldPeriodicData L k hL).Carrier → ℂ} (hζ : IsSupBelow (fieldPeriodicData L k hL) ζ ρ)
    {d : PositiveEdge (meshAt L k 0)} (hd : d ∉ positiveEdgesWithin L k b.1.initial (3 / 2)) :
    shiftedBasis hL a b ζ d.1 = 0 :=
  h.coeffs.eq_zero_of_not_mem ζ hζ d hd
theorem ShiftedBasisControl.finitelySupported (h : ShiftedBasisControl hL ρ a b)
    {ζ : (fieldPeriodicData L k hL).Carrier → ℂ} (hζ : IsSupBelow (fieldPeriodicData L k hL) ζ ρ) :
    IsFinitelySupportedForm (shiftedBasis hL a b ζ) :=
  ⟨h.mem_forms ζ hζ, h.coeffs.finite.subset fun d hd => by
    by_contra hn
    exact hd (h.eq_zero_of_far hζ hn)⟩
theorem ShiftedBasisControl.eq_zero_on_supportEdges (h : ShiftedBasisControl hL ρ a b)
    {ζ : (fieldPeriodicData L k hL).Carrier → ℂ} (hζ : IsSupBelow (fieldPeriodicData L k hL) ζ ρ)
    {c : PositiveEdge (meshAt L k k)} (hc : ¬IsWithinThree c b) :
    ∀ d ∈ supportEdges c.1, shiftedBasis hL a b ζ d = 0 := by
  intro d hd
  by_contra hne
  apply hc
  have hd' : (⟨d, hd.1⟩ : PositiveEdge (meshAt L k 0)) ∈
      positiveEdgesWithin L k b.1.initial (3 / 2) := by
    by_contra hn
    exact hne (h.eq_zero_of_far hζ hn)
  intro i
  have h₁ : |(d.initial : InfiniteLattice.AmbientSpace) i -
      (b.1.initial : InfiniteLattice.AmbientSpace) i| < 3 / 2 := (hd' i).1
  have h₂ := abs_initial_sub_lt_of_mem_supportEdges hL hd i
  have h₃ := abs_sub_le ((c.1.initial : InfiniteLattice.AmbientSpace) i)
    ((d.initial : InfiniteLattice.AmbientSpace) i) ((b.1.initial : InfiniteLattice.AmbientSpace) i)
  have h₄ := abs_sub_comm ((c.1.initial : InfiniteLattice.AmbientSpace) i)
    ((d.initial : InfiniteLattice.AmbientSpace) i)
  linarith
theorem ShiftedBasisControl.eq_sum (h : ShiftedBasisControl hL ρ a b)
    {ζ : (fieldPeriodicData L k hL).Carrier → ℂ} (hζ : IsSupBelow (fieldPeriodicData L k hL) ζ ρ) :
    shiftedBasis hL a b ζ = ∑ p ∈ (Finset.univ : Finset (Fin 3)) ×ˢ h.coeffs.finite.toFinset,
      pauliCoeff p.1 (shiftedBasis hL a b ζ p.2.1) • basisForm p.1 p.2 :=
  eq_sum_pauliCoeff_basisForm hL (h.mem_forms ζ hζ) _ fun _ hd =>
    h.eq_zero_of_far hζ fun hn => hd (h.coeffs.finite.mem_toFinset.2 hn)
end Single
theorem indicesWithin_finite
    (hfin : ∀ y ς, (nearIndices (fieldPeriodicData L k hL) y ς).Finite)
    (x : InfiniteLattice.AmbientSpace) (r : ℝ) : (indicesWithin L k hL x r).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelTermsLocality.indicesWithin_finite <;> assumption
theorem coarseOfCoeffs_positive (f : (fieldPeriodicData L k hL).Carrier → ℂ)
    (c : PositiveEdge (meshAt L k k)) :
    coarseOfCoeffs hL f c.1 =
      ∑ a : Fin 3, f ⟨.coarse, (a, c)⟩ • Matrices.ComplexMatrix2.pauliFamily a := by
  unfold coarseOfCoeffs edgePauliCoordinates
  dsimp only
  rw [extendOddly_of_isPositivelyOriented _ c.2, dif_pos c.2]
  rfl
end ShiftedBasis
section Locality
variable {L k : ℕ} {hL : 0 < L}
theorem quadratic_apply_sum_sum (hL : 0 < L) (U : Edge L k 0 → Matrices.ComplexMatrix2)
    (c : PositiveEdge (meshAt L k k)) {B B' : Edge L k 0 → Matrices.ComplexMatrix2}
    {s t : Finset (Fin 3 × PositiveEdge (meshAt L k 0))}
    {x y : Fin 3 × PositiveEdge (meshAt L k 0) → ℂ}
    (hB : B = ∑ p ∈ s, x p • basisForm p.1 p.2)
    (hB' : B' = ∑ r ∈ t, y r • basisForm r.1 r.2) :
    complexQuadraticTerm L k U B B' c = ∑ p ∈ s, ∑ r ∈ t, x p • y r •
      complexQuadraticTerm L k U (basisForm p.1 p.2) (basisForm r.1 r.2) c := by
  subst hB hB'
  rw [quadratic_sum_sum U s t x y (fun p => basisForm p.1 p.2)
    (fun r => basisForm r.1 r.2) (fun p => basisForm_finitelySupported hL p.1 p.2)
    fun r => basisForm_finitelySupported hL r.1 r.2]
  simp only [Finset.sum_apply, Pi.smul_apply]
theorem isLocalTerm_of_control {ρ ρ₁ ρ₂ : ℝ}
    (hC : PeriodicOperators.HolomorphicCoordinateClosure.ClosureHolds)
    (hfin : ∀ y ς, (nearIndices (fieldPeriodicData L k hL) y ς).Finite) (hρ : 0 < ρ)
    (l₁ : ρ ≤ ρ₁) (l₂ : ρ ≤ ρ₂)
    (hsmall : ∀ ζ, IsSupBelow (fieldPeriodicData L k hL) ζ ρ →
      gaugeFieldOfCoeffs hL ζ ∈ smallIterateFields L k)
    (hH : ∀ U ∈ smallIterateFields L k, HasUniqueQuadraticTerm
      (complexEdgeForms (meshAt L k 0)) (topLogRatio L k U) (topDeriv L k U))
    (hR : ∀ U ∈ smallIterateFields L k, LocalAt U)
    (hE : ∀ c, QuadraticEntries L k hL ρ₂ c)
    {a' a : Fin 3} {b' b : PositiveEdge (meshAt L k 0)}
    (hτ' : ShiftedBasisControl hL ρ₁ a' b') (hτ : ShiftedBasisControl hL ρ₁ a b) :
    IsLocalTerm L k hL ρ b' b (quadraticCoarseTerm L k hL a' b' a b) := by
  classical
  have off : ∀ ζ, IsSupBelow (fieldPeriodicData L k hL) ζ ρ → ∀ c : PositiveEdge (meshAt L k k),
      ¬(IsWithinThree c b' ∧ IsWithinThree c b) →
      complexQuadraticTerm L k (gaugeFieldOfCoeffs hL ζ)
        (shiftedBasis hL a' b' ζ) (shiftedBasis hL a b ζ) c = 0 := by
    intro ζ hζ c hc
    have hζ₁ := isSupBelow_mono hζ l₁
    refine quadratic_eq_zero_of_vanish (hR _ (hsmall ζ hζ)) (hτ'.finitelySupported hζ₁)
      (hτ.finitelySupported hζ₁) c ?_
    by_cases h₁ : IsWithinThree c b'
    · exact Or.inr (hτ.eq_zero_on_supportEdges hζ₁ fun h => hc ⟨h₁, h⟩)
    · exact Or.inl (hτ'.eq_zero_on_supportEdges hζ₁ h₁)
  refine ⟨fun ⟨i, hi⟩ ζ hζ => ?_, fun _ => ?_⟩
  · have z : complexQuadraticTerm L k (gaugeFieldOfCoeffs hL ζ)
        (shiftedBasis hL a' b' ζ) (shiftedBasis hL a b ζ) = 0 :=
      funext fun c => off ζ hζ c fun ⟨h₁, h₂⟩ => by
        have e₁ := h₁ i
        have e₂ := h₂ i
        have e₃ := abs_sub_le ((b.1.initial : InfiniteLattice.AmbientSpace) i)
          ((c.1.initial : InfiniteLattice.AmbientSpace) i)
          ((b'.1.initial : InfiniteLattice.AmbientSpace) i)
        have e₄ := abs_sub_comm ((b.1.initial : InfiniteLattice.AmbientSpace) i)
          ((c.1.initial : InfiniteLattice.AmbientSpace) i)
        linarith
    show traceFinsumPairing _ (complexQuadraticTerm L k (gaugeFieldOfCoeffs hL ζ)
      (shiftedBasis hL a' b' ζ) (shiftedBasis hL a b ζ)) = 0
    rw [z]
    simp [traceFinsumPairing, Matrices.ComplexMatrix2.halfTrace,
      Matrices.ComplexMatrix2.fullTrace]
  · set T := indicesWithin L k hL b'.1.initial (9 / 2) ∪ indicesWithin L k hL b.1.initial (7 / 2)
      with hTdef
    have hTf : T.Finite := (indicesWithin_finite hfin _ _).union (indicesWithin_finite hfin _ _)
    have hT := hC (fieldPeriodicData L k hL) ρ T hρ hTf
    have sub' : backgroundCoords L k hL (edgesNear L k b'.1.initial (7 / 2)) ⊆ T := by
      rintro _ ⟨e, d, hd, rfl⟩
      refine Or.inl fun i => ?_
      have h₁ := (hd i).1
      show |(d.1.initial : InfiniteLattice.AmbientSpace) i -
        (b'.1.initial : InfiniteLattice.AmbientSpace) i| < 9 / 2
      linarith
    have sub : backgroundCoords L k hL (edgesNear L k b.1.initial (7 / 2)) ⊆ T := by
      rintro _ ⟨e, d, hd, rfl⟩
      exact Or.inr fun i => (hd i).1
    have subB : ∀ c : PositiveEdge (meshAt L k k), IsWithinThree c b' →
        backgroundCoords L k hL (supportEdges c.1) ⊆ T := by
      rintro c hc _ ⟨e, d, hd, rfl⟩
      refine Or.inl fun i => ?_
      have h₁ := abs_initial_sub_lt_of_mem_supportEdges hL hd i
      have h₂ := hc i
      have h₃ := abs_sub_le ((d.1.initial : InfiniteLattice.AmbientSpace) i)
        ((c.1.initial : InfiniteLattice.AmbientSpace) i)
        ((b'.1.initial : InfiniteLattice.AmbientSpace) i)
      show |(d.1.initial : InfiniteLattice.AmbientSpace) i -
        (b'.1.initial : InfiniteLattice.AmbientSpace) i| < 9 / 2
      linarith
    have subC : ∀ c : PositiveEdge (meshAt L k k), IsWithinThree c b' → ∀ e : Fin 3,
        (⟨.coarse, (e, c)⟩ : LocalKernels.FieldIdx L k hL) ∈ T := fun c hc e =>
      Or.inl fun i => by
        have h₁ := hc i
        show |(c.1.initial : InfiniteLattice.AmbientSpace) i -
          (b'.1.initial : InfiniteLattice.AmbientSpace) i| < 9 / 2
        linarith
    have hCf : {c : PositiveEdge (meshAt L k k) | IsWithinThree c b' ∧ IsWithinThree c b}.Finite := by
      refine (hTf.preimage (f := fun c : PositiveEdge (meshAt L k k) =>
        (⟨.coarse, (0, c)⟩ : LocalKernels.FieldIdx L k hL)) ?_).subset
          fun c hc => subC c hc.1 0
      intro c _ c' _ e
      exact (Prod.ext_iff.1 (eq_of_heq (Sigma.mk.inj_iff.1 e).2)).2
    have hX : ∀ c : PositiveEdge (meshAt L k k), IsWithinThree c b' →
        PauliHolomorphicOn (fieldPeriodicData L k hL) ρ T fun ζ =>
          complexQuadraticTerm L k (gaugeFieldOfCoeffs hL ζ)
            (shiftedBasis hL a' b' ζ) (shiftedBasis hL a b ζ) c := by
      intro c hc
      have main : PauliHolomorphicOn (fieldPeriodicData L k hL) ρ T fun ζ =>
          ∑ p ∈ (Finset.univ : Finset (Fin 3)) ×ˢ hτ'.coeffs.finite.toFinset,
            ∑ r ∈ (Finset.univ : Finset (Fin 3)) ×ˢ hτ.coeffs.finite.toFinset,
              pauliCoeff p.1 (shiftedBasis hL a' b' ζ p.2.1) •
                pauliCoeff r.1 (shiftedBasis hL a b ζ r.2.1) •
                  complexQuadraticTerm L k (gaugeFieldOfCoeffs hL ζ)
                    (basisForm p.1 p.2) (basisForm r.1 r.2) c := by
        refine PauliHolomorphicOn.sum hT _ _ fun p hp =>
          PauliHolomorphicOn.sum hT _ _ fun r hr => ?_
        have hp' := hτ'.coeffs.finite.mem_toFinset.1 (Finset.mem_product.1 hp).2
        have hr' := hτ.coeffs.finite.mem_toFinset.1 (Finset.mem_product.1 hr).2
        refine PauliHolomorphicOn.smul hT
          (holomorphicInValues_of_subset hC hρ l₁ hTf sub' (hτ'.coeffs.holomorphic_coeff _ hp' _))
          (PauliHolomorphicOn.smul hT
            (holomorphicInValues_of_subset hC hρ l₁ hTf sub
              (hτ.coeffs.holomorphic_coeff _ hr' _)) ?_)
        refine ⟨fun e ζ => pauliCoeff e
          (complexQuadraticTerm L k (gaugeFieldOfCoeffs hL ζ)
            (basisForm p.1 p.2) (basisForm r.1 r.2) c),
          fun e => holomorphicInValues_of_subset hC hρ l₂ hTf (subB c hc)
            (hE c e p.1 r.1 p.2 r.2), fun ζ hζ => ?_⟩
        exact (sum_pauliCoeff_smul (quadratic_mem_traceless (hH _ (hsmall ζ hζ))
          (basisForm_finitelySupported hL _ _) (basisForm_finitelySupported hL _ _) c)).symm
      refine main.congr_below fun ζ hζ => ?_
      have hζ₁ := isSupBelow_mono hζ l₁
      exact (quadratic_apply_sum_sum hL _ c (hτ'.eq_sum hζ₁) (hτ.eq_sum hζ₁)).symm
    refine hT.congr_below _ _ (fun ζ hζ => ?_) (hT.sum hCf.toFinset
      (fun c ζ => Matrices.ComplexMatrix2.halfTrace
        (coarseOfCoeffs hL ζ c.1 *
          complexQuadraticTerm L k (gaugeFieldOfCoeffs hL ζ)
            (shiftedBasis hL a' b' ζ) (shiftedBasis hL a b ζ) c)) fun c hc => ?_)
    · show _ = traceFinsumPairing (restrictToPositiveEdges (coarseOfCoeffs hL ζ))
        (complexQuadraticTerm L k (gaugeFieldOfCoeffs hL ζ)
          (shiftedBasis hL a' b' ζ) (shiftedBasis hL a b ζ))
      unfold traceFinsumPairing
      refine (finsum_eq_sum_of_support_subset _ fun c hc => ?_).symm
      rw [Finset.mem_coe, hCf.mem_toFinset]
      by_contra hn
      apply hc
      show Matrices.ComplexMatrix2.halfTrace (coarseOfCoeffs hL ζ c.1 *
        complexQuadraticTerm L k (gaugeFieldOfCoeffs hL ζ)
          (shiftedBasis hL a' b' ζ) (shiftedBasis hL a b ζ) c) = 0
      rw [off ζ hζ c hn]
      simp [Matrices.ComplexMatrix2.halfTrace, Matrices.ComplexMatrix2.fullTrace]
    · have hc' := hCf.mem_toFinset.1 hc
      refine PauliHolomorphicOn.halfTrace_mul hT ?_ (hX c hc'.1)
      exact ⟨fun e ζ => ζ ⟨.coarse, (e, c)⟩, fun e => hT.coord _ (subC c hc'.1 e),
        fun ζ _ => coarseOfCoeffs_positive ζ c⟩
end Locality
theorem quadraticTermIsLocal_holds
    (hC : PeriodicOperators.HolomorphicCoordinateClosure.ClosureHolds)
    (hFin : PeriodicOperators.CovariantFiniteRange.Claim)
    (hTower : LocalKernels.IndexSetPeriodicity.Statement)
    (hSmall : FullSpace.SmallIterates.SmallIteratesNearOne)
    (hD : Tower.AsDifferentials.CovariantMeansAreDerivatives)
    (hR : FullSpace.ReadsCubes.Statement)
    (hE : FullSpace.ElementaryEntries.EntriesHolomorphic)
    (hS : FullSpace.BasisFormLocality.ElementaryFormLocality) : QuadraticTermIsLocal := by
  intro L hL hStd k hk
  obtain ⟨ρ₁, h₁, hS⟩ := hS L hL hStd k hk
  obtain ⟨ρ₂, h₂, -, hE⟩ := hE L hL hStd k hk
  obtain ⟨ρ₃, h₃, hU⟩ := (hSmall L hL hStd k hk).2
  have hfin : ∀ y ς, (nearIndices (fieldPeriodicData L k hL) y ς).Finite :=
    (hFin.1 _ ((hTower L hStd k).2 _).1).1
  obtain ⟨ρ, hρ, l₁, l₂, l₃⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₁ ∧ ρ ≤ ρ₂ ∧ ρ ≤ ρ₃ :=
    ⟨min ρ₁ (min ρ₂ ρ₃), lt_min h₁ (lt_min h₂ h₃), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hread : ∀ (a : Fin 3) (b : PositiveEdge (meshAt L k 0)), ShiftedBasisControl hL ρ₁ a b :=
    fun a b => ⟨(hS a b).2.1, (hS a b).2.2⟩
  exact ⟨ρ, hρ, fun a' b' a b => isLocalTerm_of_control hC hfin hρ l₁ l₂
    (fun ζ hζ => hU ζ (isSupBelow_mono hζ l₃)) (hD L hStd k hk).2.2 (hR L hStd k hk).1 hE
    (hread a' b') (hread a b)⟩
end YangMills.Construction.Tower.FullSpace.QuadraticTermLocality
end
