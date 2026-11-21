import YangMills.Construction.Lattice.ElementarySquareCorners
import YangMills.Construction.Lattice.TransposesOfTheCovariantDerivativesOnALatticeProof
import YangMills.Construction.OneLoop.PauliMatrixRelations
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.PlaquettesAndSumsOfATower
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FaceSums
open Matrices
section Corners
variable {G : Type} [AddCommGroup G]
theorem cornerSet_eq_image (Λ : AddSubgroup G) (x a b : Λ) :
    {c : G | c ∈ [(x : G), x + a, x + a + b, x + b]} =
      Subtype.val '' ({x, x + a, x + a + b, x + b} : Set Λ) := by
  ext c
  simp [Set.image_insert_eq]
theorem squareFacts_in_subgroup {Λ : AddSubgroup G} {axis : Fin 4 → ℝ → G} {a : ℝ}
    (H : ElementarySquare.SquareFacts Λ axis a) (e : Fin 4 → Λ)
    (he : ∀ μ, (e μ : G) = axis μ a) (x y : Λ) (μ ν μ' ν' : Fin 4) (hμν : μ < ν)
    (hμν' : μ' < ν') :
    [x, x + e μ, x + e μ + e ν, x + e ν].Nodup ∧
      (({x, x + e μ, x + e μ + e ν, x + e ν} : Set Λ) =
          {y, y + e μ', y + e μ' + e ν', y + e ν'} →
        (x, μ, ν) = (y, μ', ν')) := by
  obtain ⟨⟨-, hnd⟩, hset, -⟩ := H x x.2 y y.2 μ ν μ' ν' hμν hμν'
  have hlist : ∀ (z : Λ) (α β : Fin 4), ElementarySquare.vertexList axis a (z : G) α β =
      [(z : G), z + e α, z + e α + e β, z + e β] := by
    intro z α β
    simp [ElementarySquare.vertexList, he]
  refine ⟨List.Nodup.of_map Subtype.val ?_, fun hc => ?_⟩
  · rw [hlist] at hnd
    simpa using hnd
  · rw [hlist, hlist] at hset
    obtain ⟨h₁, rfl, rfl⟩ := hset ((cornerSet_eq_image Λ x (e μ) (e ν)).trans
      ((congrArg (fun T => Subtype.val '' T) hc).trans
        (cornerSet_eq_image Λ y (e μ') (e ν')).symm))
    rw [Subtype.ext h₁]
end Corners
section Sums
variable {ι : Type*}
theorem halfTrace_mul_im {A B : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.hermitianTraceless)
    (hB : B ∈ ComplexMatrix2.hermitianTraceless) :
    (ComplexMatrix2.halfTrace (A * B)).im = 0 := by
  have h : star (ComplexMatrix2.fullTrace (A * B)) = ComplexMatrix2.fullTrace (A * B) :=
    ComplexMatrix2.LieElement.star_fullTrace_mul (⟨A, hA⟩ : ComplexMatrix2.hermitianTraceless)
      (⟨B, hB⟩ : ComplexMatrix2.hermitianTraceless)
  have h' : (ComplexMatrix2.fullTrace (A * B)).im = 0 := Complex.conj_eq_iff_im.mp h
  simp [ComplexMatrix2.halfTrace, Complex.mul_im, h']
theorem halfTrace_mul_self_re_nonneg {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    0 ≤ (ComplexMatrix2.halfTrace (A * A)).re := by apply _root_.YangMills.SharedProofs.p2980 <;> assumption
theorem eq_zero_of_halfTrace_mul_self_re {A : ComplexMatrix2}
    (hA : A ∈ ComplexMatrix2.hermitianTraceless)
    (h : (ComplexMatrix2.halfTrace (A * A)).re = 0) : A = 0 :=
  congrArg Subtype.val (ComplexMatrix2.LieElement.innerProductCore.definite
    (⟨A, hA⟩ : ComplexMatrix2.hermitianTraceless) h)
theorem support_halfTrace_mul_finite {f g : ι → ComplexMatrix2}
    (h : HasFiniteSupp f ∨ HasFiniteSupp g) :
    (Function.support fun σ => ComplexMatrix2.halfTrace (f σ * g σ)).Finite := by
  rcases h with h | h
  · refine Set.Finite.subset h fun σ hσ hf => hσ ?_
    simp [hf]
  · refine Set.Finite.subset h fun σ hσ hg => hσ ?_
    simp [hg]
theorem traceFinsumPairing_re {f g : ι → ComplexMatrix2}
    (h : HasFiniteSupp f ∨ HasFiniteSupp g) :
    (traceFinsumPairing f g).re = ∑ᶠ σ, (ComplexMatrix2.halfTrace (f σ * g σ)).re :=
  Complex.reAddGroupHom.map_finsum (support_halfTrace_mul_finite h)
theorem traceFinsumPairing_im {f g : ι → ComplexMatrix2}
    (hf : ∀ σ, f σ ∈ ComplexMatrix2.hermitianTraceless)
    (hg : ∀ σ, g σ ∈ ComplexMatrix2.hermitianTraceless)
    (h : HasFiniteSupp f ∨ HasFiniteSupp g) : (traceFinsumPairing f g).im = 0 := by
  have e : (traceFinsumPairing f g).im = ∑ᶠ σ, (ComplexMatrix2.halfTrace (f σ * g σ)).im :=
    Complex.imAddGroupHom.map_finsum (support_halfTrace_mul_finite h)
  rw [e]
  simp [halfTrace_mul_im (hf _) (hg _)]
theorem traceFinsumPairing_comm (f g : ι → ComplexMatrix2) :
    traceFinsumPairing f g = traceFinsumPairing g f := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.traceFinsumPairing_comm <;> assumption
theorem traceFinsumPairing_add_left {f f' g : ι → ComplexMatrix2} (hf : HasFiniteSupp f)
    (hf' : HasFiniteSupp f') :
    traceFinsumPairing (f + f') g = traceFinsumPairing f g + traceFinsumPairing f' g := by
  unfold traceFinsumPairing
  rw [← finsum_add_distrib (support_halfTrace_mul_finite (Or.inl hf))
    (support_halfTrace_mul_finite (Or.inl hf'))]
  refine finsum_congr fun σ => ?_
  simp only [Pi.add_apply, add_mul, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_add, mul_add]
theorem traceFinsumPairing_smul_left (f g : ι → ComplexMatrix2) (c : ℝ) :
    traceFinsumPairing (c • f) g = (c : ℂ) * traceFinsumPairing f g := by
  unfold traceFinsumPairing
  rw [mul_finsum]
  refine finsum_congr fun σ => ?_
  simp only [Pi.smul_apply, Matrix.smul_mul, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
    Matrix.trace_smul, Complex.real_smul]
  ring
@[instance_reducible]
def finSuppInnerCore (ι : Type*) : InnerProductSpace.Core ℝ (finSuppLieFields ι) where
  inner f g := (traceFinsumPairing (f : ι → ComplexMatrix2) (g : ι → ComplexMatrix2)).re
  conj_inner_symm f g := by
    simp only [conj_trivial]
    rw [traceFinsumPairing_comm]
  re_inner_nonneg f := by
    simp only [RCLike.re_to_real]
    rw [traceFinsumPairing_re (Or.inl f.2.2)]
    exact finsum_nonneg fun σ => halfTrace_mul_self_re_nonneg (f.2.1 σ)
  add_left f f' g := by
    have e : ((f + f' : finSuppLieFields ι) : ι → ComplexMatrix2) =
        (f : ι → ComplexMatrix2) + f' := rfl
    rw [e, traceFinsumPairing_add_left f.2.2 f'.2.2, Complex.add_re]
  smul_left f g c := by
    have e : ((c • f : finSuppLieFields ι) : ι → ComplexMatrix2) =
        c • (f : ι → ComplexMatrix2) := rfl
    rw [e, traceFinsumPairing_smul_left]
    have hi := traceFinsumPairing_im f.2.1 g.2.1 (Or.inl f.2.2)
    simp [Complex.mul_re, hi]
  definite f h := by
    have hs : (Function.support (f : ι → ComplexMatrix2)).Finite := f.2.2
    rw [traceFinsumPairing_re (Or.inl hs),
      finsum_eq_sum_of_support_subset (s := hs.toFinset) _ (fun σ hσ => by
        simp only [Set.Finite.coe_toFinset, Function.mem_support]
        intro h0
        exact hσ (by simp [h0]))] at h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun σ _ => halfTrace_mul_self_re_nonneg (f.2.1 σ))).mp h
    refine Subtype.ext (funext fun σ => ?_)
    by_cases hσ : σ ∈ hs.toFinset
    · exact eq_zero_of_halfTrace_mul_self_re (f.2.1 σ) (hz σ hσ)
    · by_contra h0
      exact hσ (hs.mem_toFinset.mpr h0)
theorem pairingIsInner_holds (ι : Type*) : PairingIsInner ι := by
  refine ⟨fun f g hf hg h => ⟨support_halfTrace_mul_finite h, traceFinsumPairing_im hf hg h⟩,
    finSuppInnerCore ι, fun f g => ?_⟩
  exact Complex.ext rfl
    ((Complex.ofReal_im _).trans (traceFinsumPairing_im f.2.1 g.2.1 (Or.inl f.2.2)).symm)
def finSuppEquivPi (ι : Type*) [Finite ι] :
    finSuppLieFields ι ≃ₗ[ℝ] (ι → ComplexMatrix2.hermitianTraceless) where
  toFun f σ := ⟨(f : ι → ComplexMatrix2) σ, f.2.1 σ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun u := ⟨fun σ => (u σ : ComplexMatrix2), fun σ => (u σ).2, Set.toFinite _⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem hasLieFieldDim_of_finite {ι : Type*} [Finite ι] (hP : OneLoop.PauliMatrixRelations)
    (S : Set ι) : HasLieFieldDim S := by
  obtain ⟨e, -⟩ := hP.2.2.1
  have : Module.Finite ℝ ComplexMatrix2.hermitianTraceless := Module.Finite.of_basis e.toBasis
  have h3 : Module.finrank ℝ ComplexMatrix2.LieElement = 3 := by
    simpa using Module.finrank_eq_card_basis e.toBasis
  have h3' : Module.finrank ℝ ComplexMatrix2.hermitianTraceless = 3 := h3
  have : Fintype S := Fintype.ofFinite S
  refine ⟨Set.toFinite S, fun f => Set.toFinite _, Module.Finite.equiv (finSuppEquivPi S).symm, ?_⟩
  rw [(finSuppEquivPi S).finrank_eq, Module.finrank_pi_fintype]
  simp only [h3', Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_coe_set_eq S, Nat.card_eq_fintype_card, mul_comm]
end Sums
theorem facesAndPairings_holds (hC : ElementarySquare.ElementarySquareStatement)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hP : OneLoop.PauliMatrixRelations) : FacesAndPairings := by
  intro L hL k j hj
  refine ⟨fun n hn => ?_, ?_, fun S => pairingIsInner_holds S, fun S => pairingIsInner_holds S,
    fun S => pairingIsInner_holds S⟩
  · obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, hS, hB, hPl⟩, -⟩ := hA L hL n j k hn hj
    have : Finite (Vertex L n k j) := hS
    have : Finite (Edge L n k j) := hB
    have : Finite (Face L n k j) := hPl
    refine ⟨fun x y μ ν μ' ν' h h' => ?_,
      fun S => ⟨pairingIsInner_holds S, hasLieFieldDim_of_finite hP S⟩,
      fun S => ⟨pairingIsInner_holds S, hasLieFieldDim_of_finite hP S⟩,
      fun S => ⟨pairingIsInner_holds S, hasLieFieldDim_of_finite hP S⟩⟩
    obtain ⟨h₁, h₂⟩ := squareFacts_in_subgroup (hC L hL n j k hn hj).1
      (PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j)) (fun _ => rfl)
      x y μ ν μ' ν' h h'
    exact ⟨h₁, h₂⟩
  · intro x y μ ν μ' ν' h h'
    have H := (hC L hL 1 j k le_rfl hj).2
    rw [meshSize_levelDepth] at H
    obtain ⟨h₁, h₂⟩ := squareFacts_in_subgroup H (InfiniteLattice.axisStep (meshAt L k j))
      (fun _ => rfl) x y μ ν μ' ν' h h'
    exact ⟨h₁, h₂⟩
end YangMills.Construction.Tower.FaceSums
end
