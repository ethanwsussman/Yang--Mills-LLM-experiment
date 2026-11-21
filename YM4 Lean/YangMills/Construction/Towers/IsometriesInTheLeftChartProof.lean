import YangMills.Construction.Towers.GaugeAndIsometricImagesAreConfigurationsProof
import YangMills.Construction.Towers.IsometriesInTheLeftChart
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices
open QuotientLattices
namespace Tower.LeftChartIsometries
theorem isUnit_of_det_eq_one {V : ComplexMatrix2} (hV : V.det = 1) : IsUnit V := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.isUnit_of_det_eq_one <;> assumption
theorem inv_inv_of_det_eq_one {V : ComplexMatrix2} (hV : V.det = 1) : V⁻¹⁻¹ = V :=
  Matrix.nonsing_inv_nonsing_inv V (by rw [hV]; exact isUnit_one)
theorem det_inv_eq_one {V : ComplexMatrix2} (hV : V.det = 1) : (V⁻¹).det = 1 := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.det_inv_of_det_eq_one <;> assumption
theorem matExp_conj_inv_mul_inv {V X : ComplexMatrix2} (hV : V.det = 1) :
    ComplexMatrix2.matExp (Complex.I • -ComplexMatrix2.conjugateBy V⁻¹ X) * V⁻¹ =
      (ComplexMatrix2.matExp (Complex.I • X) * V)⁻¹ := by
  have hunit := isUnit_of_det_eq_one hV
  have hconj : Complex.I • -ComplexMatrix2.conjugateBy V⁻¹ X = V⁻¹ * (-(Complex.I • X)) * V := by
    simp only [ComplexMatrix2.conjugateBy, inv_inv_of_det_eq_one hV, smul_neg, mul_neg, neg_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  have hVVinv : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V (by rw [hV]; exact isUnit_one)
  simp only [ComplexMatrix2.matExp]
  rw [hconj, Matrix.exp_conj' _ _ hunit, Matrix.exp_neg, Matrix.mul_inv_rev, mul_assoc, hVVinv,
    mul_one]
theorem halfTrace_neg_conj_mul_neg_conj {g : ComplexMatrix2} (hg : g.det = 1)
    (X Y : ComplexMatrix2) :
    ComplexMatrix2.halfTrace (-ComplexMatrix2.conjugateBy g X * -ComplexMatrix2.conjugateBy g Y) =
      ComplexMatrix2.halfTrace (X * Y) := by
  have hginv : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g (by rw [hg]; exact isUnit_one)
  have hprod : -ComplexMatrix2.conjugateBy g X * -ComplexMatrix2.conjugateBy g Y =
      g * (X * Y * g⁻¹) := by
    simp only [ComplexMatrix2.conjugateBy, neg_mul_neg]
    calc g * X * g⁻¹ * (g * Y * g⁻¹) = g * X * (g⁻¹ * g) * Y * g⁻¹ := by
          simp only [mul_assoc]
      _ = g * (X * Y * g⁻¹) := by rw [hginv]; simp only [mul_one, mul_assoc]
  rw [hprod]
  simp only [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace]
  rw [Matrix.trace_mul_comm, mul_assoc, hginv, mul_one]
theorem conjugateBy_inv_mem_hermitianTraceless {g X : ComplexMatrix2}
    (hg : g ∈ PeriodicLattice.compactGaugeGroup) (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy g⁻¹ X ∈ ComplexMatrix2.hermitianTraceless := by
  obtain ⟨hunitary, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hg
  have hstar : g * star g = 1 := Matrix.mem_unitaryGroup_iff.mp hunitary
  have hinv : g⁻¹ = star g := Matrix.inv_eq_right_inv hstar
  have hform : ComplexMatrix2.conjugateBy g⁻¹ X = g.conjTranspose * X * g := by
    rw [ComplexMatrix2.conjugateBy, inv_inv_of_det_eq_one hdet, hinv]
    rfl
  obtain ⟨hherm, htr⟩ := hX
  rw [hform]
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← hherm, mul_assoc]
  · simp only [ComplexMatrix2.fullTrace] at htr ⊢
    have hstar' : g * g.conjTranspose = 1 := hstar
    rw [Matrix.trace_mul_comm, ← mul_assoc, hstar', one_mul, htr]
theorem eq_zero_of_conjugateBy_inv_eq_zero {V X : ComplexMatrix2} (hV : V.det = 1)
    (h : ComplexMatrix2.conjugateBy V⁻¹ X = 0) : X = 0 := by
  have hVVinv : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V (by rw [hV]; exact isUnit_one)
  have hX : X = V * ComplexMatrix2.conjugateBy V⁻¹ X * V⁻¹ := by
    simp only [ComplexMatrix2.conjugateBy, inv_inv_of_det_eq_one hV]
    calc X = (V * V⁻¹) * X * (V * V⁻¹) := by rw [hVVinv, one_mul, mul_one]
      _ = V * (V⁻¹ * X * V) * V⁻¹ := by simp only [mul_assoc]
  rw [hX, h, mul_zero, zero_mul]
section Oriented
variable {β : Type} (P : β → Prop) (rev : β → β)
open Classical in
def twistedConfig (A U : β → ComplexMatrix2) : β → ComplexMatrix2 :=
  fun b => if P b then ComplexMatrix2.matExp (Complex.I • A b) * U b
    else (ComplexMatrix2.matExp (Complex.I • A (rev b)) * U (rev b))⁻¹
open Classical in
def oddExtension (f : β → ComplexMatrix2) : β → ComplexMatrix2 :=
  fun b => if P b then f b else -f (rev b)
open Classical in
def tangentValue (U B : β → ComplexMatrix2) (b : β) : ComplexMatrix2 :=
  if P b then B b else -ComplexMatrix2.conjugateBy (U (rev b))⁻¹ (B (rev b))
def pushForm (s : β → β) (U B : β → ComplexMatrix2) : β → ComplexMatrix2 :=
  oddExtension P rev fun b => tangentValue P rev U B (s b)
structure OrientationData (s : β → β) : Prop where
  rev_rev : ∀ b, rev (rev b) = b
  pos_rev : ∀ b, P (rev b) ↔ ¬P b
  map_rev : ∀ b, s (rev b) = rev (s b)
variable {P rev} {s : β → β} {U B : β → ComplexMatrix2}
theorem twistedConfig_of_pos {A V : β → ComplexMatrix2} {b : β} (hb : P b) :
    twistedConfig P rev A V b = ComplexMatrix2.matExp (Complex.I • A b) * V b := if_pos hb
theorem twistedConfig_of_not_pos {A V : β → ComplexMatrix2} {b : β} (hb : ¬P b) :
    twistedConfig P rev A V b =
      (ComplexMatrix2.matExp (Complex.I • A (rev b)) * V (rev b))⁻¹ := if_neg hb
theorem oddExtension_of_pos {f : β → ComplexMatrix2} {b : β} (hb : P b) :
    oddExtension P rev f b = f b := if_pos hb
theorem oddExtension_of_not_pos {f : β → ComplexMatrix2} {b : β} (hb : ¬P b) :
    oddExtension P rev f b = -f (rev b) :=
  if_neg hb
theorem tangentValue_of_pos {b : β} (hb : P b) : tangentValue P rev U B b = B b := if_pos hb
theorem tangentValue_of_not_pos {b : β} (hb : ¬P b) :
    tangentValue P rev U B b = -ComplexMatrix2.conjugateBy (U (rev b))⁻¹ (B (rev b)) := if_neg hb
theorem twistedConfig_rev_inv (h : OrientationData P rev s) (hdet : ∀ b, (U b).det = 1) (c : β) :
    (twistedConfig P rev B U (rev c))⁻¹ = twistedConfig P rev B U c := by
  by_cases hc : P c
  · have hc' : ¬P (rev c) := fun hr => (h.pos_rev c).mp hr hc
    rw [twistedConfig_of_not_pos hc', h.rev_rev, twistedConfig_of_pos hc]
    refine Matrix.nonsing_inv_nonsing_inv _ ?_
    rw [Matrix.det_mul, hdet, mul_one]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  · have hc' : P (rev c) := (h.pos_rev c).mpr hc
    rw [twistedConfig_of_pos hc', twistedConfig_of_not_pos hc]
theorem matExp_tangentValue_mul (h : OrientationData P rev s) (hU : ∀ b, U (rev b) = (U b)⁻¹)
    (hdet : ∀ b, (U b).det = 1) (c : β) :
    ComplexMatrix2.matExp (Complex.I • tangentValue P rev U B c) * U c =
      twistedConfig P rev B U c := by
  by_cases hc : P c
  · rw [tangentValue_of_pos hc, twistedConfig_of_pos hc]
  · have hUc : U c = (U (rev c))⁻¹ := by rw [← hU, h.rev_rev]
    rw [tangentValue_of_not_pos hc, twistedConfig_of_not_pos hc, hUc]
    exact matExp_conj_inv_mul_inv (hdet _)
theorem twistedConfig_pushForm (h : OrientationData P rev s) (hU : ∀ b, U (rev b) = (U b)⁻¹)
    (hdet : ∀ b, (U b).det = 1) :
    twistedConfig P rev (pushForm P rev s U B) (fun b => U (s b)) =
      fun b => twistedConfig P rev B U (s b) := by
  funext b
  by_cases hb : P b
  · rw [twistedConfig_of_pos hb, pushForm, oddExtension_of_pos hb]
    exact matExp_tangentValue_mul h hU hdet (s b)
  · have hb' : P (rev b) := (h.pos_rev b).mpr hb
    rw [twistedConfig_of_not_pos hb, pushForm, oddExtension_of_pos hb']
    show (ComplexMatrix2.matExp (Complex.I • tangentValue P rev U B (s (rev b))) *
      U (s (rev b)))⁻¹ = _
    rw [matExp_tangentValue_mul h hU hdet, h.map_rev]
    exact twistedConfig_rev_inv h hdet (s b)
theorem tangentValue_add (B' : β → ComplexMatrix2) (c : β) :
    tangentValue P rev U (B + B') c = tangentValue P rev U B c + tangentValue P rev U B' c := by
  by_cases hc : P c
  · simp only [tangentValue_of_pos hc, Pi.add_apply]
  · simp only [tangentValue_of_not_pos hc, Pi.add_apply, ComplexMatrix2.conjugateBy, mul_add,
      add_mul, neg_add]
theorem tangentValue_smul (r : ℝ) (c : β) :
    tangentValue P rev U (r • B) c = r • tangentValue P rev U B c := by
  by_cases hc : P c
  · simp only [tangentValue_of_pos hc, Pi.smul_apply]
  · simp only [tangentValue_of_not_pos hc, Pi.smul_apply, ComplexMatrix2.conjugateBy,
      mul_smul_comm, smul_mul_assoc, smul_neg]
theorem pushForm_add (B' : β → ComplexMatrix2) :
    pushForm P rev s U (B + B') = pushForm P rev s U B + pushForm P rev s U B' := by
  funext b
  by_cases hb : P b
  · simp only [pushForm, Pi.add_apply, oddExtension_of_pos hb, tangentValue_add]
  · simp only [pushForm, Pi.add_apply, oddExtension_of_not_pos hb, tangentValue_add, neg_add]
theorem pushForm_smul (r : ℝ) :
    pushForm P rev s U (r • B) = r • pushForm P rev s U B := by
  funext b
  by_cases hb : P b
  · simp only [pushForm, Pi.smul_apply, oddExtension_of_pos hb, tangentValue_smul]
  · simp only [pushForm, Pi.smul_apply, oddExtension_of_not_pos hb, tangentValue_smul, smul_neg]
theorem pushForm_mem (h : OrientationData P rev s)
    (hG : ∀ b, U b ∈ PeriodicLattice.compactGaugeGroup)
    (hB : ∀ b, P b → B b ∈ ComplexMatrix2.hermitianTraceless) :
    (∀ b, P b → pushForm P rev s U B b ∈ ComplexMatrix2.hermitianTraceless) ∧
      ∀ b, pushForm P rev s U B (rev b) = -pushForm P rev s U B b := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [pushForm, oddExtension_of_pos hb]
    by_cases hc : P (s b)
    · rw [tangentValue_of_pos hc]
      exact hB _ hc
    · rw [tangentValue_of_not_pos hc]
      exact ComplexMatrix2.hermitianTraceless.neg_mem
        (conjugateBy_inv_mem_hermitianTraceless (hG _) (hB _ ((h.pos_rev _).mpr hc)))
  · by_cases hb : P b
    · have hb' : ¬P (rev b) := fun hr => (h.pos_rev b).mp hr hb
      simp only [pushForm, oddExtension_of_not_pos hb', oddExtension_of_pos hb, h.rev_rev]
    · have hb' : P (rev b) := (h.pos_rev b).mpr hb
      simp only [pushForm, oddExtension_of_not_pos hb, oddExtension_of_pos hb', neg_neg]
theorem eq_zero_of_pushForm_eq_zero (h : OrientationData P rev s) (hs : Function.Surjective s)
    (hdet : ∀ b, (U b).det = 1) (hB : ∀ b, B (rev b) = -B b)
    (h0 : pushForm P rev s U B = 0) : B = 0 := by
  have hpos : ∀ c, P c → B c = 0 := by
    intro c hc
    obtain ⟨b, rfl⟩ := hs c
    by_cases hb : P b
    · have hval := congrFun h0 b
      rwa [pushForm, oddExtension_of_pos hb, tangentValue_of_pos hc] at hval
    · have hb' : P (rev b) := (h.pos_rev b).mpr hb
      have hc' : ¬P (rev (s b)) := fun hr => (h.pos_rev _).mp hr hc
      have hval := congrFun h0 (rev b)
      rw [pushForm, oddExtension_of_pos hb', h.map_rev, tangentValue_of_not_pos hc',
        h.rev_rev] at hval
      exact eq_zero_of_conjugateBy_inv_eq_zero (hdet _) (neg_eq_zero.mp hval)
  funext c
  by_cases hc : P c
  · exact hpos c hc
  · have hodd := hB (rev c)
    rw [h.rev_rev, hpos _ ((h.pos_rev c).mpr hc), neg_zero] at hodd
    exact hodd
def positivePerm (h : OrientationData P rev s) (b : {b // P b}) : {b // P b} :=
  open Classical in
  if hb : P (s b) then ⟨s b, hb⟩ else ⟨rev (s b), (h.pos_rev _).mpr hb⟩
theorem positivePerm_injective (h : OrientationData P rev s) (hs : Function.Injective s) :
    Function.Injective (positivePerm h) := by
  rintro ⟨b, hb⟩ ⟨b', hb'⟩ e
  have rev_inj : ∀ {x y : β}, rev x = rev y → x = y := fun {x y} e => by
    rw [← h.rev_rev x, e, h.rev_rev]
  have key : ∀ {x y : β}, P x → P y → s x = rev (s y) → False := by
    intro x y hx hy e
    have hxy : x = rev y := hs (e.trans (h.map_rev y).symm)
    exact (h.pos_rev y).mp (hxy ▸ hx) hy
  simp only [positivePerm] at e
  split_ifs at e with h₁ h₂ h₂
  · exact Subtype.ext (hs (congrArg Subtype.val e))
  · exact (key hb hb' (congrArg Subtype.val e)).elim
  · exact (key hb' hb (congrArg Subtype.val e).symm).elim
  · exact Subtype.ext (hs (rev_inj (congrArg Subtype.val e)))
theorem halfTrace_pushForm (h : OrientationData P rev s) (hdet : ∀ b, (U b).det = 1)
    (B' : β → ComplexMatrix2) (b : {b // P b}) :
    ComplexMatrix2.halfTrace (pushForm P rev s U B b * pushForm P rev s U B' b) =
      ComplexMatrix2.halfTrace (B (positivePerm h b) * B' (positivePerm h b)) := by
  simp only [pushForm, oddExtension_of_pos b.2]
  by_cases hc : P (s b)
  · simp only [positivePerm, dif_pos hc, tangentValue_of_pos hc]
  · simp only [positivePerm, dif_neg hc, tangentValue_of_not_pos hc]
    exact halfTrace_neg_conj_mul_neg_conj (det_inv_eq_one (hdet _)) _ _
theorem traceFinsumPairing_pushForm [Finite β] (h : OrientationData P rev s)
    (hs : Function.Injective s) (hdet : ∀ b, (U b).det = 1) (B' : β → ComplexMatrix2) :
    traceFinsumPairing (fun b : {b // P b} => pushForm P rev s U B b)
        (fun b : {b // P b} => pushForm P rev s U B' b) =
      traceFinsumPairing (fun b : {b // P b} => B b) (fun b : {b // P b} => B' b) := by
  have hbij : Function.Bijective (positivePerm h) :=
    Finite.injective_iff_bijective.mp (positivePerm_injective h hs)
  let e : {b // P b} ≃ {b // P b} := Equiv.ofBijective _ hbij
  let g : {b // P b} → ℂ := fun c => ComplexMatrix2.halfTrace (B c * B' c)
  have hterm : ∀ b : {b // P b}, ComplexMatrix2.halfTrace
      (pushForm P rev s U B b * pushForm P rev s U B' b) = g (e b) :=
    fun b => halfTrace_pushForm h hdet B' b
  exact (finsum_congr hterm).trans (finsum_comp_equiv e)
theorem pushForm_isOrthogonalOn [Finite β] (h : OrientationData P rev s)
    (hs : Function.Injective s) (S : Submodule ℝ (β → ComplexMatrix2))
    (hS : ∀ B, B ∈ S ↔ (∀ b, P b → B b ∈ ComplexMatrix2.hermitianTraceless) ∧
      ∀ b, B (rev b) = -B b)
    (hG : ∀ b, U b ∈ PeriodicLattice.compactGaugeGroup) (hdet : ∀ b, (U b).det = 1) :
    LeftChartFacts.IsOrthogonalOn S
      (fun B B' => traceFinsumPairing (fun b : {b // P b} => B b) (fun b : {b // P b} => B' b))
      (pushForm P rev s U) := by
  have hsurj : Function.Surjective s := Finite.injective_iff_surjective.mp hs
  let T : S →ₗ[ℝ] S :=
    { toFun := fun B => ⟨pushForm P rev s U B,
        (hS _).mpr (pushForm_mem h hG ((hS _).mp B.2).1)⟩
      map_add' := fun B B' => Subtype.ext (pushForm_add _)
      map_smul' := fun r B => Subtype.ext (pushForm_smul r) }
  have hT : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).mpr fun B hB => ?_
    exact Subtype.ext (eq_zero_of_pushForm_eq_zero h hsurj hdet ((hS _).mp B.2).2
      (congrArg Subtype.val hB))
  refine ⟨LinearEquiv.ofInjectiveEndo T hT, fun x => ?_, fun x y => ?_⟩
  · rw [LinearEquiv.coe_ofInjectiveEndo]
    rfl
  · exact traceFinsumPairing_pushForm h hs hdet _
end Oriented
section Lattices
variable {X : Type} [AddCommGroup X]
theorem areNeighbours_iff {e : Fin 4 → X} {x x' : X} :
    AreNeighbours e x x' ↔ ∃ μ, x' - x = e μ ∨ x' - x = -e μ := by apply _root_.YangMills.Construction.Tower.GaugeAndSymmetryImages.areNeighbours_iff_exists_axis <;> assumption
theorem positive_swap_iff {Λ : AddSubgroup X} {e : Fin 4 → Λ}
    (hN : StepsDistinctAndSigned Λ fun μ => (e μ : X)) {x y : Λ}
    (hxy : ∃ μ, y - x = e μ ∨ y - x = -e μ) :
    (∃ μ, x - y = e μ) ↔ ¬∃ μ, y - x = e μ := by
  have positive : ∀ {z w : Λ}, (∃ μ, w - z = e μ) ↔
      IsPositiveStep (fun μ => (e μ : X)) (z : X) (w : X) := by
    intro z w
    constructor
    · rintro ⟨μ, h⟩
      exact ⟨μ, by simpa [IsSignedAxisStep] using congrArg Subtype.val h⟩
    · rintro ⟨μ, h⟩
      exact ⟨μ, Subtype.ext (by simpa [IsSignedAxisStep] using h)⟩
  have hn : AreNeighbours (fun μ => (e μ : X)) (x : X) (y : X) := by
    refine areNeighbours_iff.mpr ?_
    obtain ⟨μ, h | h⟩ := hxy
    · exact ⟨μ, Or.inl (congrArg Subtype.val h)⟩
    · exact ⟨μ, Or.inr (congrArg Subtype.val h)⟩
  obtain ⟨ε, μ, hstep⟩ := hn
  have hx := ((hN.2.2 x x.2 y y.2).2 ε μ hstep).2
  rw [← positive, ← positive] at hx
  rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨fun h => (h₂ h).elim, fun h => (h h₁).elim⟩
  · exact ⟨fun _ => h₂, fun _ => h₁⟩
end Lattices
section PeriodicSide
variable {L n k j : ℕ} {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
theorem apply_vertexPreimage (hm : MapsSublatticeOnto k j f) (x : Vertex L n k j) :
    f (vertexPreimage (k := k) (j := j) f x) = x := by apply _root_.YangMills.Construction.Tower.ScalingInvariance.vertexPreimage_spec <;> assumption
theorem edgePreimage_endpoints
    (hP : NeighboursAtSpacing (torusDist L n)
      (PeriodicLattice.sublattice L n (refinementIndex k j))
      (PeriodicLattice.meshSize L (refinementIndex k j)) (torusAxisSteps L n k j))
    (hf : IsDistancePreserving f) (hm : MapsSublatticeOnto k j f) (b : Edge L n k j) :
    (edgePreimage (k := k) (j := j) f b).source = vertexPreimage (k := k) (j := j) f b.source ∧
      (edgePreimage (k := k) (j := j) f b).target =
        vertexPreimage (k := k) (j := j) f b.target := by apply _root_.YangMills.Construction.Tower.GaugeAndSymmetryImages.edgePreimage_endpoints <;> assumption
theorem edgePreimage_injective
    (hP : NeighboursAtSpacing (torusDist L n)
      (PeriodicLattice.sublattice L n (refinementIndex k j))
      (PeriodicLattice.meshSize L (refinementIndex k j)) (torusAxisSteps L n k j))
    (hf : IsDistancePreserving f) (hm : MapsSublatticeOnto k j f) :
    Function.Injective (edgePreimage (k := k) (j := j) f) := by
  have vertex : ∀ {x x' : Vertex L n k j},
      vertexPreimage (k := k) (j := j) f x = vertexPreimage (k := k) (j := j) f x' → x = x' := by
    intro x x' e
    apply Subtype.ext
    rw [← apply_vertexPreimage hm x, ← apply_vertexPreimage hm x', e]
  intro b b' e
  apply PeriodicLattice.Bond.ext
  · exact vertex (((edgePreimage_endpoints hP hf hm b).1.symm.trans (congrArg _ e)).trans
      (edgePreimage_endpoints hP hf hm b').1)
  · exact vertex (((edgePreimage_endpoints hP hf hm b).2.symm.trans (congrArg _ e)).trans
      (edgePreimage_endpoints hP hf hm b').2)
theorem orientationData_periodic
    (hN : StepsDistinctAndSigned (PeriodicLattice.sublattice L n (refinementIndex k j))
      (torusAxisSteps L n k j))
    (hP : NeighboursAtSpacing (torusDist L n)
      (PeriodicLattice.sublattice L n (refinementIndex k j))
      (PeriodicLattice.meshSize L (refinementIndex k j)) (torusAxisSteps L n k j))
    (hf : IsDistancePreserving f) (hm : MapsSublatticeOnto k j f) :
    OrientationData
      (PeriodicLattice.Bond.IsPositivelyOriented (L := L) (m := n)
        (j := PeriodicLattice.levelDepth k j))
      PeriodicLattice.Bond.opposite (edgePreimage (k := k) (j := j) f) where
  rev_rev b := rfl
  pos_rev b := positive_swap_iff (e := PeriodicLattice.unitStep L n (refinementIndex k j)) hN
    b.isNeighbour
  map_rev b := by
    apply PeriodicLattice.Bond.ext
    · exact (edgePreimage_endpoints hP hf hm b.opposite).1.trans
        (edgePreimage_endpoints hP hf hm b).2.symm
    · exact (edgePreimage_endpoints hP hf hm b.opposite).2.trans
        (edgePreimage_endpoints hP hf hm b).1.symm
end PeriodicSide
section FullSide
open InfiniteLattice (AmbientSpace)
variable {a : ℝ} {f : AmbientSpace → AmbientSpace}
theorem fullSpace_edgePreimage_endpoints
    (hP : NeighboursAtSpacing spaceDist (InfiniteLattice.latticeSubgroup a) a
      (spaceAxisSteps a))
    (hf : FullSpace.IsDistancePreserving f) (hm : FullSpace.MapsSublatticeOnto a f)
    (b : InfiniteLattice.Link a) :
    (FullSpace.edgePreimage f b).initial = FullSpace.vertexPreimage f b.initial ∧
      (FullSpace.edgePreimage f b).terminal = FullSpace.vertexPreimage f b.terminal := by apply _root_.YangMills.Construction.Tower.GaugeAndSymmetryImages.fullSpace_edgePreimage_endpoints <;> assumption
theorem orientationData_fullSpace
    (hN : StepsDistinctAndSigned (InfiniteLattice.latticeSubgroup a) (spaceAxisSteps a))
    (hP : NeighboursAtSpacing spaceDist (InfiniteLattice.latticeSubgroup a) a
      (spaceAxisSteps a))
    (hf : FullSpace.IsDistancePreserving f) (hm : FullSpace.MapsSublatticeOnto a f) :
    OrientationData (InfiniteLattice.Link.IsPositivelyOriented (a := a))
      InfiniteLattice.Link.opposite (FullSpace.edgePreimage f) where
  rev_rev b := rfl
  pos_rev b := positive_swap_iff (e := InfiniteLattice.axisStep a) hN b.isAdjacent
  map_rev b := by
    apply InfiniteLattice.Link.ext
    · exact (fullSpace_edgePreimage_endpoints hP hf hm b.opposite).1.trans
        (fullSpace_edgePreimage_endpoints hP hf hm b).2.symm
    · exact (fullSpace_edgePreimage_endpoints hP hf hm b.opposite).2.trans
        (fullSpace_edgePreimage_endpoints hP hf hm b).1.symm
end FullSide
theorem leftChartIsometryEquivariance_holds
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties) :
    LeftChartIsometryEquivariance := by
  intro L k j hL hj
  refine ⟨fun n hn => ?_, ?_⟩
  · intro f hf hm U hU
    have hS := hA L hL n j k hn hj
    have hN := hS.2.2.2.2.2.1
    have hP := hS.2.2.2.2.2.2.2.1
    have hO := orientationData_periodic hN hP hf hm
    have hrev : ∀ b, U b.opposite = (U b)⁻¹ := fun b => hU.2 b (mem_univ b)
    refine ⟨fun B _ => ?_, fun hr => ?_⟩
    · exact twistedConfig_pushForm hO hrev fun b => hU.1 b (mem_univ b)
    · have hfin : Finite (Edge L n k j) := hS.2.1.2.2.2.2.2.2.2.2.2.2.2.1
      have hG : ∀ b, U b ∈ PeriodicLattice.compactGaugeGroup := fun b => hr.1 b (mem_univ b)
      exact pushForm_isOrthogonalOn hO (edgePreimage_injective hP hf hm) _ (fun B => Iff.rfl) hG
        fun b => (Matrix.mem_specialUnitaryGroup_iff.mp (hG b)).2
  · intro f hf hm U hU B _
    have hS := hA L hL 1 j k le_rfl hj
    have e : PeriodicLattice.meshSize L (refinementIndex k j) = meshAt L k j :=
      meshSize_levelDepth L k j
    have hN := hS.2.2.2.2.2.2.1
    have hP := hS.2.2.2.2.2.2.2.2
    rw [e] at hN hP
    exact twistedConfig_pushForm (orientationData_fullSpace hN hP hf hm) hU.2 hU.1
end Tower.LeftChartIsometries
end YangMills.Construction
end
