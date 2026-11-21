import YangMills.Construction.PeriodicOperators.AlgebraOfQuadruples
import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.BoundsOfTheNumbersOfAJet
import YangMills.Construction.PeriodicOperators.CalculusOfJets
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.Towers.BoundOfAnInterpolationRemainderBetweenTwoRoots
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.RootInterpolation
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
structure JetToolkit (δ : ℝ) (p : Fin 4 → ℂ) : Prop where
  jets : ∀ I I' I'' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    IsPeriodic I'' → JetDomains.JetAlgebra I I' I'' δ p
  mulAssoc : JetCalculus.MulAssocNormLe δ p
  transposeMul : JetCalculus.TransposeMulNorm δ p
  inv : JetCalculus.InvJetSpec δ p
  traceComm : JetCalculus.TraceNumberCommTranspose δ p
  mulUnital : ∀ I I' I'' : PeriodicData, QuadAlgebra.MulBilinearUnital p I I' I''
  normTrace : ∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    QuadAlgebra.JetNormTrace δ p I I'
  eqJets : JetArgumentsAndEqualJets
  numberBounds : JetNumberBounds.Claim
def JetEquiv (δ : ℝ) (p : Fin 4 → ℂ) {I I' : PeriodicData} (T S : JetQuad I I') : Prop :=
  IsJet δ p T ∧ IsJet δ p S ∧ EqAsJet δ p T S
section Calculus
variable {δ : ℝ} {p : Fin 4 → ℂ} {I I' I'' I''' : PeriodicData}
theorem JetEquiv.rfl' {T : JetQuad I I'} (h : IsJet δ p T) : JetEquiv δ p T T :=
  ⟨h, h, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
theorem JetEquiv.symm' {T S : JetQuad I I'} (h : JetEquiv δ p T S) : JetEquiv δ p S T :=
  ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm⟩
theorem JetEquiv.trans' {T S R : JetQuad I I'} (h : JetEquiv δ p T S) (k : JetEquiv δ p S R) :
    JetEquiv δ p T R :=
  ⟨h.1, k.2.1, h.2.2.1.trans k.2.2.1, h.2.2.2.1.trans k.2.2.2.1,
    h.2.2.2.2.1.trans k.2.2.2.2.1, h.2.2.2.2.2.trans k.2.2.2.2.2⟩
variable [Fact (IsPeriodic I)] [Fact (IsPeriodic I')]
  [Fact (IsPeriodic I'')] [Fact (IsPeriodic I''')]
namespace JetToolkit
variable (H : JetToolkit δ p)
include H
theorem isJet_mul {T : JetQuad I I'} {S : JetQuad I'' I} (hT : IsJet δ p T)
    (hS : IsJet δ p S) : IsJet δ p (mul p T S) :=
  (H.jets I I' I'' Fact.out Fact.out Fact.out).mul_isJet T S hT hS
theorem isJet_transposeAt {T : JetQuad I I'} (hT : IsJet δ p T) :
    IsJet δ p (transposeAt p T) :=
  (H.jets I I' I Fact.out Fact.out Fact.out).transpose_isJet T hT
theorem isJet_add {T S : JetQuad I I'} (hT : IsJet δ p T) (hS : IsJet δ p S) :
    IsJet δ p (add T S) :=
  (H.jets I I' I Fact.out Fact.out Fact.out).add_isJet T S hT hS
theorem isJet_smul (z : ℂ) {T : JetQuad I I'} (hT : IsJet δ p T) : IsJet δ p (smul z T) :=
  (H.jets I I' I Fact.out Fact.out Fact.out).smul_isJet z T hT
theorem isJet_one : IsJet δ p (one I) :=
  (H.jets I I I Fact.out Fact.out Fact.out).one_isJet
theorem equiv_mul {T T' : JetQuad I I'} {S S' : JetQuad I'' I} (h : JetEquiv δ p T T')
    (k : JetEquiv δ p S S') : JetEquiv δ p (mul p T S) (mul p T' S') :=
  ⟨H.isJet_mul h.1 k.1, H.isJet_mul h.2.1 k.2.1,
    (H.eqJets.2.1 δ p I I' Fact.out Fact.out T T' h.1 h.2.1 h.2.2).2.2.2.2 I'' Fact.out S S'
      k.1 k.2.1 k.2.2⟩
theorem mul_assoc' {T : JetQuad I' I} {S : JetQuad I'' I'} {R : JetQuad I''' I''}
    (hT : IsJet δ p T) (hS : IsJet δ p S) (hR : IsJet δ p R) :
    JetEquiv δ p (mul p (mul p T S) R) (mul p T (mul p S R)) :=
  ⟨H.isJet_mul (H.isJet_mul hT hS) hR, H.isJet_mul hT (H.isJet_mul hS hR),
    (H.mulAssoc I I' I'' I''' Fact.out Fact.out Fact.out Fact.out T S R hT hS hR).1⟩
theorem jetNorm_mul_le {T : JetQuad I I'} {S : JetQuad I'' I} (hT : IsJet δ p T)
    (hS : IsJet δ p S) : jetNorm δ p (mul p T S) ≤ jetNorm δ p T * jetNorm δ p S :=
  (H.mulAssoc I' I I'' I'' Fact.out Fact.out Fact.out Fact.out T S (one I'') hT hS
    H.isJet_one).2
theorem jetNorm_transposeAt {T : JetQuad I I'} (hT : IsJet δ p T) :
    jetNorm δ p (transposeAt p T) = jetNorm δ p T :=
  (H.transposeMul I' I I Fact.out Fact.out Fact.out T (one I) hT H.isJet_one).2
theorem transposeAt_mul {T : JetQuad I I'} {S : JetQuad I'' I} (hT : IsJet δ p T)
    (hS : IsJet δ p S) :
    JetEquiv δ p (transposeAt p (mul p T S)) (mul p (transposeAt p S) (transposeAt p T)) :=
  ⟨H.isJet_transposeAt (H.isJet_mul hT hS),
    H.isJet_mul (H.isJet_transposeAt hS) (H.isJet_transposeAt hT),
    (H.transposeMul I' I I'' Fact.out Fact.out Fact.out T S hT hS).1⟩
omit [Fact (IsPeriodic I)] [Fact (IsPeriodic I')] in
theorem one_mul' (T : JetQuad I I') : mul p (one I') T = T :=
  ((H.mulUnital I I' I).2.2.2.2 T).1
omit [Fact (IsPeriodic I)] [Fact (IsPeriodic I')] in
theorem mul_one' (T : JetQuad I I') : mul p T (one I) = T :=
  ((H.mulUnital I I' I).2.2.2.2 T).2
theorem traceNumber_eq_of_equiv {T S : JetQuad I I} (h : JetEquiv δ p T S) :
    traceNumber T = traceNumber S :=
  (H.eqJets.2.2 δ p I Fact.out T S h.1 h.2.1 h.2.2).1
theorem jetNorm_eq_of_equiv {T S : JetQuad I I'} (h : JetEquiv δ p T S) :
    jetNorm δ p T = jetNorm δ p S :=
  (H.eqJets.2.1 δ p I I' Fact.out Fact.out T S h.1 h.2.1 h.2.2).1
theorem traceNumber_mul_comm {T : JetQuad I I'} {S : JetQuad I' I} (hT : IsJet δ p T)
    (hS : IsJet δ p S) : traceNumber (mul p T S) = traceNumber (mul p S T) :=
  (H.traceComm I I' Fact.out Fact.out).1 T S hT hS
end JetToolkit
end Calculus
section Roots
variable {δ : ℝ} {p : Fin 4 → ℂ} {I K J J' : PeriodicData}
variable [Fact (IsPeriodic I)] [Fact (IsPeriodic K)]
  [Fact (IsPeriodic J)] [Fact (IsPeriodic J')]
theorem invJet_equiv_conj_root (H : JetToolkit δ p) {N M T B : JetQuad I I}
    (hN : IsJet δ p N) (hM : IsJet δ p M) (hMN : EqAsJet δ p (mul p M N) (one I))
    (hT : IsInvertibleJet δ p T) (hB : IsJet δ p B)
    (hSB : JetEquiv δ p (mul p (conjugateBy p N T) B) (one I)) :
    JetEquiv δ p (invJet p T) (mul p (mul p N B) N) := by
  have hO : IsJet δ p (one I) := H.isJet_one
  have hTj := hT.isJet
  have hinv := H.inv I Fact.out T hT
  have hS : IsJet δ p (conjugateBy p N T) := H.isJet_mul (H.isJet_mul hN hTj) hN
  have hTN : IsJet δ p (mul p T N) := H.isJet_mul hTj hN
  have hBN : IsJet δ p (mul p B N) := H.isJet_mul hB hN
  have hK : IsJet δ p (mul p (mul p N B) N) := H.isJet_mul (H.isJet_mul hN hB) hN
  have hMN' : JetEquiv δ p (mul p M N) (one I) := ⟨H.isJet_mul hM hN, hO, hMN⟩
  have e1 : JetEquiv δ p (mul p M (conjugateBy p N T)) (mul p T N) := by
    have a : JetEquiv δ p (mul p M (conjugateBy p N T)) (mul p M (mul p N (mul p T N))) :=
      H.equiv_mul (JetEquiv.rfl' hM) (H.mul_assoc' hN hTj hN)
    have b := (H.mul_assoc' hM hN hTN).symm'
    have c : JetEquiv δ p (mul p (mul p M N) (mul p T N)) (mul p T N) := by
      have := H.equiv_mul hMN' (JetEquiv.rfl' hTN)
      rwa [H.one_mul'] at this
    exact (a.trans' b).trans' c
  have e2 : JetEquiv δ p (mul p T (mul p (mul p N B) N)) (one I) := by
    have a := H.equiv_mul (JetEquiv.rfl' hTj) (H.mul_assoc' hN hB hN)
    have b := (H.mul_assoc' hTj hN hBN).symm'
    have c := H.equiv_mul e1.symm' (JetEquiv.rfl' hBN)
    have d := H.mul_assoc' hM hS hBN
    have f := H.equiv_mul (JetEquiv.rfl' hM) (H.mul_assoc' hS hB hN).symm'
    have g : JetEquiv δ p (mul p M (mul p (mul p (conjugateBy p N T) B) N)) (mul p M N) := by
      have := H.equiv_mul (JetEquiv.rfl' hM) (H.equiv_mul hSB (JetEquiv.rfl' hN))
      rwa [H.one_mul'] at this
    exact (((((a.trans' b).trans' c).trans' d).trans' f).trans' g).trans' hMN'
  have hI := hinv.1
  have hIT : JetEquiv δ p (mul p (invJet p T) T) (one I) :=
    ⟨H.isJet_mul hI hTj, hO, hinv.2.1⟩
  have a : JetEquiv δ p (invJet p T) (mul p (invJet p T) (mul p T (mul p (mul p N B) N))) := by
    have := H.equiv_mul (JetEquiv.rfl' hI) e2.symm'
    rwa [H.mul_one'] at this
  have b := (H.mul_assoc' hI hTj hK).symm'
  have c : JetEquiv δ p (mul p (mul p (invJet p T) T) (mul p (mul p N B) N))
      (mul p (mul p N B) N) := by
    have := H.equiv_mul hIT (JetEquiv.rfl' hK)
    rwa [H.one_mul'] at this
  exact (a.trans' b).trans' c
theorem mul_conj_root_equiv (H : JetToolkit δ p) {N R F₁ F₂ E₁ E₂ : JetQuad I I}
    (hN : IsJet δ p N) (hNN : JetEquiv δ p (mul p N N) R) (hF₁ : IsJet δ p F₁)
    (hF₂ : IsJet δ p F₂) (h₁ : JetEquiv δ p E₁ (mul p (mul p N F₁) N))
    (h₂ : JetEquiv δ p E₂ (mul p (mul p N F₂) N)) :
    JetEquiv δ p (mul p E₁ E₂) (mul p (mul p N (mul p (mul p F₁ R) F₂)) N) := by
  have hR := hNN.2.1
  have ha : IsJet δ p (mul p N F₁) := H.isJet_mul hN hF₁
  have hc : IsJet δ p (mul p N F₂) := H.isJet_mul hN hF₂
  have hcN : IsJet δ p (mul p (mul p N F₂) N) := H.isJet_mul hc hN
  have hRF : IsJet δ p (mul p R F₂) := H.isJet_mul hR hF₂
  have s1 := H.equiv_mul h₁ h₂
  have s2 := H.mul_assoc' ha hN hcN
  have s3 := (H.mul_assoc' hN hc hN).symm'
  have s6 : JetEquiv δ p (mul p N (mul p N F₂)) (mul p R F₂) :=
    (H.mul_assoc' hN hN hF₂).symm'.trans' (H.equiv_mul hNN (JetEquiv.rfl' hF₂))
  have s7 := s3.trans' (H.equiv_mul s6 (JetEquiv.rfl' hN))
  have s8 := H.equiv_mul (JetEquiv.rfl' ha) s7
  have s9 := (H.mul_assoc' ha hRF hN).symm'
  have s10 : JetEquiv δ p (mul p (mul p N F₁) (mul p R F₂))
      (mul p N (mul p (mul p F₁ R) F₂)) :=
    (H.mul_assoc' hN hF₁ hRF).trans'
      (H.equiv_mul (JetEquiv.rfl' hN) (H.mul_assoc' hF₁ hR hF₂).symm')
  have s11 := H.equiv_mul s10 (JetEquiv.rfl' hN)
  exact (((s1.trans' s2).trans' s8).trans' s9).trans' s11
theorem traceNumber_conj_root (H : JetToolkit δ p) {N F E W : JetQuad I I}
    (hN : IsJet δ p N) (hF : IsJet δ p F) (hW : IsJet δ p W)
    (h : JetEquiv δ p E (mul p (mul p N F) N)) :
    traceNumber (mul p E W) = traceNumber (mul p F (conjugateBy p N W)) := by
  have hNW : IsJet δ p (mul p N W) := H.isJet_mul hN hW
  have hNF : IsJet δ p (mul p N F) := H.isJet_mul hN hF
  have hFNW : IsJet δ p (mul p F (mul p N W)) := H.isJet_mul hF hNW
  have s1 := H.equiv_mul h (JetEquiv.rfl' hW)
  have s2 := H.mul_assoc' hNF hN hW
  have s3 := H.mul_assoc' hN hF hNW
  have s4 : JetEquiv δ p (mul p (mul p F (mul p N W)) N) (mul p F (conjugateBy p N W)) :=
    H.mul_assoc' hF hNW hN
  rw [H.traceNumber_eq_of_equiv ((s1.trans' s2).trans' s3), H.traceNumber_mul_comm hN hFNW,
    H.traceNumber_eq_of_equiv s4]
theorem norm_traceNumber_mul_form_le (H : JetToolkit δ p) {F : JetQuad I I}
    {Y : JetQuad K I} {X : JetQuad I K} {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hF : IsJet δ p F) (hY : IsJet δ p Y) (hX : IsJet δ p X)
    (nF : jetNorm δ p F ≤ ENNReal.ofReal c) (nY : jetNorm δ p Y ≤ ENNReal.ofReal a)
    (nX : jetNorm δ p X ≤ ENNReal.ofReal a) :
    ‖traceNumber (mul p F (mul p Y X))‖ ≤ fiberDim K * (a ^ 2 * c) := by
  have hFY : IsJet δ p (mul p F Y) := H.isJet_mul hF hY
  have hXFY : IsJet δ p (mul p X (mul p F Y)) := H.isJet_mul hX hFY
  have e : traceNumber (mul p F (mul p Y X)) = traceNumber (mul p X (mul p F Y)) := by
    rw [H.traceNumber_eq_of_equiv (H.mul_assoc' hF hY hX).symm', H.traceNumber_mul_comm hFY hX]
  have b := (H.numberBounds δ p hF.pos_width hF.mem_imStrip K Fact.out
    (mul p X (mul p F Y))).1 hXFY
  have n1 : jetNorm δ p (mul p X (mul p F Y)) ≤
      ENNReal.ofReal a * (ENNReal.ofReal c * ENNReal.ofReal a) :=
    (H.jetNorm_mul_le hX hFY).trans
      (mul_le_mul' nX ((H.jetNorm_mul_le hF hY).trans (mul_le_mul' nF nY)))
  have hn : (0 : ℝ) ≤ fiberDim K := by
    unfold fiberDim
    positivity
  have hr : ENNReal.ofReal (fiberDim K * (a ^ 2 * c)) =
      (Module.finrank ℂ (K.UnitQuot → ℂ) : ℝ≥0∞) *
        (ENNReal.ofReal a * (ENNReal.ofReal c * ENNReal.ofReal a)) := by
    rw [ENNReal.ofReal_mul hn, ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul ha]
    unfold fiberDim
    rw [ENNReal.ofReal_natCast]
    congr 2
    ring
  rw [e]
  refine (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 ?_
  rw [hr]
  exact b.trans (mul_le_mul' le_rfl n1)
theorem norm_traceNumber_mul_correction_le (H : JetToolkit δ p) {F S : JetQuad I I}
    {x : JetQuad I J} {y : JetQuad J' I} {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hF : IsJet δ p F) (hS : IsJet δ p S) (hx : IsJet δ p x) (hy : IsJet δ p y)
    (nF : jetNorm δ p F ≤ ENNReal.ofReal c) (nx : jetNorm δ p x ≤ ENNReal.ofReal a)
    (ny : jetNorm δ p y ≤ ENNReal.ofReal a)
    (hcorr : EqAsJet δ p S
      ((mul p (transposeAt p x) x).add (smul (-1) (mul p y (transposeAt p y))))) :
    ‖traceNumber (mul p F S)‖ ≤ (fiberDim J + fiberDim J') * a ^ 2 * c := by
  have hxT : IsJet δ p (transposeAt p x) := H.isJet_transposeAt hx
  have hyT : IsJet δ p (transposeAt p y) := H.isJet_transposeAt hy
  have hxx : IsJet δ p (mul p (transposeAt p x) x) := H.isJet_mul hxT hx
  have hyy : IsJet δ p (mul p y (transposeAt p y)) := H.isJet_mul hy hyT
  have hR := H.isJet_add hxx (H.isJet_smul (-1) hyy)
  have s : JetEquiv δ p S _ := ⟨hS, hR, hcorr⟩
  have e := H.traceNumber_eq_of_equiv (H.equiv_mul (JetEquiv.rfl' hF) s)
  have hb := H.mulUnital I I I
  have hn := H.normTrace I I Fact.out Fact.out
  have hFx : IsJet δ p (mul p F (mul p (transposeAt p x) x)) := H.isJet_mul hF hxx
  have hFy : IsJet δ p (mul p F (mul p y (transposeAt p y))) := H.isJet_mul hF hyy
  rw [e, hb.2.1, hb.2.2.2.1, hn.2.2.2.1 _ _ hFx (H.isJet_smul (-1) hFy), hn.2.2.2.2 _ _ hFy]
  have b1 := norm_traceNumber_mul_form_le H ha hc hF hxT hx nF
    ((H.jetNorm_transposeAt hx).le.trans nx) nx
  have b2 := norm_traceNumber_mul_form_le H ha hc hF hy hyT nF ny
    ((H.jetNorm_transposeAt hy).le.trans ny)
  calc _ ≤ ‖traceNumber (mul p F (mul p (transposeAt p x) x))‖ +
        ‖(-1 : ℂ) * traceNumber (mul p F (mul p y (transposeAt p y)))‖ := norm_add_le _ _
    _ ≤ fiberDim J * (a ^ 2 * c) + fiberDim J' * (a ^ 2 * c) := by
        rw [norm_mul, norm_neg, norm_one, one_mul]
        exact add_le_add b1 b2
    _ = _ := by ring
end Roots
theorem remainderBoundClaim_holds (hJ : JetCalculus.Claim) (hA : QuadAlgebra.Claim)
    (hE : JetArgumentsAndEqualJets) (hN : JetNumberBounds.Claim)
    (hL : JetDomains.OpFunJetTheory) : RemainderBoundClaim := by
  intro I J J' hI hJ₁ hJ₂ γ P hγ hB p A W N M Q y a b g ha hb hg D
  have : Fact (IsPeriodic I) := ⟨hI⟩
  have : Fact (IsPeriodic J) := ⟨hJ₁⟩
  have : Fact (IsPeriodic J') := ⟨hJ₂⟩
  have hδ := D.isJet_A.pos_width
  have hp := D.isJet_A.mem_imStrip
  have c := hJ stripHalfWidth p hδ hp
  have H : JetToolkit stripHalfWidth p :=
    ⟨fun I I' I'' a b c => hL.2.2 I I' I'' a b c stripHalfWidth p hδ hp, c.1, c.2.1, c.2.2.2.2.1,
      c.2.2.2.2.2.1, hA.1 p, fun I I' a b => hA.2 stripHalfWidth p hδ hp I I' a b, hE, hN⟩
  have hNj := D.isJet_N
  have hW := D.isJet_W
  have hQ := D.isJet_Q
  have hR : IsJet stripHalfWidth p (ofKernel I I P) := hB.isJet p hp
  have hNN : JetEquiv stripHalfWidth p (mul p N N) (ofKernel I I P) :=
    ⟨H.isJet_mul hNj hNj, hR, D.mul_self⟩
  have hx : IsJet stripHalfWidth p (mul p Q N) := H.isJet_mul hQ hNj
  have hS : IsJet stripHalfWidth p (conjugateBy p N W) := H.isJet_mul (H.isJet_mul hNj hW) hNj
  have root : ∀ T, InvertibleWithConjugate p N T b → ∃ F, IsJet stripHalfWidth p F ∧
      jetNorm stripHalfWidth p F ≤ ENNReal.ofReal b ∧
      JetEquiv stripHalfWidth p (invJet p T) (mul p (mul p N F) N) := by
    intro T hT
    have hi := H.inv I hI _ hT.conj_invertible
    exact ⟨_, hi.1, hT.conj_inv_norm_le, invJet_equiv_conj_root H hNj D.isJet_M D.left_inv
      hT.invertible hi.1 ⟨H.isJet_mul hT.conj_invertible.isJet hi.1, H.isJet_one, hi.2.2.1⟩⟩
  have corner : ∀ {E F : JetQuad I I} {c : ℝ}, 0 ≤ c → IsJet stripHalfWidth p F →
      jetNorm stripHalfWidth p F ≤ ENNReal.ofReal c →
      JetEquiv stripHalfWidth p E (mul p (mul p N F) N) →
      ‖traceNumber (mul p E W)‖ ≤ (fiberDim J + fiberDim J') * a ^ 2 * c := by
    intro E F c hc hF nF h
    rw [traceNumber_conj_root H hNj hF hW h]
    exact norm_traceNumber_mul_correction_le H ha hc hF hS hx D.isJet_y nF D.x_norm_le
      D.y_norm_le D.conj_decomp
  have triple : ∀ {F₁ F₂ : JetQuad I I} {c₁ c₂ : ℝ}, 0 ≤ c₁ → IsJet stripHalfWidth p F₁ →
      IsJet stripHalfWidth p F₂ → jetNorm stripHalfWidth p F₁ ≤ ENNReal.ofReal c₁ →
      jetNorm stripHalfWidth p F₂ ≤ ENNReal.ofReal c₂ →
      IsJet stripHalfWidth p (mul p (mul p F₁ (ofKernel I I P)) F₂) ∧
        jetNorm stripHalfWidth p (mul p (mul p F₁ (ofKernel I I P)) F₂) ≤
          ENNReal.ofReal (c₁ * g * c₂) := by
    intro F₁ F₂ c₁ c₂ hc₁ hF₁ hF₂ n₁ n₂
    have hFR := H.isJet_mul hF₁ hR
    refine ⟨H.isJet_mul hFR hF₂, ?_⟩
    rw [ENNReal.ofReal_mul (mul_nonneg hc₁ hg), ENNReal.ofReal_mul hc₁]
    exact (H.jetNorm_mul_le hFR hF₂).trans (mul_le_mul'
      ((H.jetNorm_mul_le hF₁ hR).trans (mul_le_mul' n₁ D.kernel_norm_le)) n₂)
  have addz : ∀ T S : JetQuad I I, add T (smul ((0 : ℝ) : ℂ) S) = T := by
    intro T S
    cases T
    simp [add, smul]
  have h0 : unitShiftedPath A W 0 = addScalarJet A 1 := addz _ _
  have hz : addScalarJet (A.add W) 0 = A.add W := addz _ _
  have i1 : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖traceNumber (mul p (invJet p (unitShiftedPath A W t)) W)‖ ≤
        (fiberDim J + fiberDim J') * a ^ 2 * b := by
    intro t ht
    obtain ⟨F, hF, nF, e⟩ := root _ (D.path t ht)
    exact corner hb hF nF e
  obtain ⟨F₀, hF₀, nF₀, eG⟩ := root (addScalarJet A 1)
    (h0 ▸ D.path 0 ⟨le_rfl, zero_le_one⟩)
  have i2 : ∀ τ ∈ Icc (0 : ℝ) 1, ‖correctionIntegrand p A W τ‖ ≤
      (fiberDim J + fiberDim J') * a ^ 2 * (b * g * b) +
        (fiberDim J + fiberDim J') * a ^ 2 * (b * g * (b * g * b)) + γ * b ^ 3 := by
    intro τ hτ
    obtain ⟨F', hF', nF', eP⟩ := root _ (D.shifted τ hτ)
    have eG' : JetEquiv stripHalfWidth p (unitShiftedInverse p A) (mul p (mul p N F₀) N) := eG
    have eP' : JetEquiv stripHalfWidth p (perturbedInverse p A W τ) (mul p (mul p N F') N) :=
      eP
    have hGj := eG'.1
    have hPj := eP'.1
    have eGG := mul_conj_root_equiv H hNj hNN hF₀ hF₀ eG' eG'
    have hGG := eGG.1
    obtain ⟨hF₂, nF₂⟩ := triple hb hF₀ hF₀ nF₀ nF₀
    obtain ⟨hF₃, nF₃⟩ := triple (by positivity) hF₂ hF' nF₂ nF'
    obtain ⟨hF₄, nF₄⟩ := triple hb hF' hF₀ nF' nF₀
    obtain ⟨hF₅, nF₅⟩ := triple hb hF' hF₂ nF' nF₂
    have b2 : ‖traceNumber (mul p (mul p (unitShiftedInverse p A) W)
        (perturbedInverse p A W τ))‖ ≤ (fiberDim J + fiberDim J') * a ^ 2 * (b * g * b) := by
      rw [H.traceNumber_mul_comm (H.isJet_mul hGj hW) hPj,
        H.traceNumber_eq_of_equiv (H.mul_assoc' hPj hGj hW).symm']
      exact corner (by positivity) hF₄ nF₄ (mul_conj_root_equiv H hNj hNN hF' hF₀ eP' eG')
    have b3 : ‖traceNumber (mul p (mul p (mul p (unitShiftedInverse p A)
        (unitShiftedInverse p A)) W) (perturbedInverse p A W τ))‖ ≤
        (fiberDim J + fiberDim J') * a ^ 2 * (b * g * (b * g * b)) := by
      rw [H.traceNumber_mul_comm (H.isJet_mul hGG hW) hPj,
        H.traceNumber_eq_of_equiv (H.mul_assoc' hPj hGG hW).symm']
      exact corner (by positivity) hF₅ nF₅ (mul_conj_root_equiv H hNj hNN hF' hF₂ eP' eGG)
    have b1 : ‖traceNumber (mul p (mul p (unitShiftedInverse p A) (unitShiftedInverse p A))
        (perturbedInverse p A W τ))‖ ≤ γ * b ^ 3 := by
      have eGGP := mul_conj_root_equiv H hNj hNN hF₂ hF' eGG eP'
      rw [H.traceNumber_eq_of_equiv eGGP, H.traceNumber_mul_comm (H.isJet_mul hNj hF₃) hNj,
        H.traceNumber_eq_of_equiv ((H.mul_assoc' hNj hNj hF₃).symm'.trans'
          (H.equiv_mul hNN (JetEquiv.rfl' hF₃)))]
      have hbr := ResolventTrace.IsBracketedProductOf.node
        (ResolventTrace.IsBracketedProductOf.leaf (p := p) (ofKernel I I P))
        (ResolventTrace.IsBracketedProductOf.node
          (ResolventTrace.IsBracketedProductOf.node
            (ResolventTrace.IsBracketedProductOf.node
              (ResolventTrace.IsBracketedProductOf.node
                (ResolventTrace.IsBracketedProductOf.leaf (p := p) F₀)
                (ResolventTrace.IsBracketedProductOf.leaf (p := p) (ofKernel I I P)))
              (ResolventTrace.IsBracketedProductOf.leaf (p := p) F₀))
            (ResolventTrace.IsBracketedProductOf.leaf (p := p) (ofKernel I I P)))
          (ResolventTrace.IsBracketedProductOf.leaf (p := p) F'))
      have hsix := hB.bracketing_eq p hp F₀ F₀ F' hF₀ hF₀ hF' _ hbr
      have s6 : JetEquiv stripHalfWidth p _ (ResolventTrace.sixfoldProduct p P F₀ F₀ F') :=
        ⟨hsix.1, hB.mul_isJet p hp _ _ _ hF₀ hF₀ hF', hsix.2⟩
      rw [H.traceNumber_eq_of_equiv s6]
      have hb3 := hB.trace_le p hp F₀ F₀ F' hF₀ hF₀ hF'
      refine (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (hb3.trans ?_)
      have e3 : ENNReal.ofReal (γ * b ^ 3) = ENNReal.ofReal γ * ENNReal.ofReal b *
          ENNReal.ofReal b * ENNReal.ofReal b := by
        rw [← ENNReal.ofReal_mul hγ, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      rw [e3]
      exact mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl nF₀) nF₀) nF'
    have hu0 : 0 ≤ 1 - τ := sub_nonneg.2 hτ.2
    have hu1 : 1 - τ ≤ 1 := by linarith [hτ.1]
    have hu2 : (1 - τ) ^ 2 ≤ 1 := by nlinarith
    have n1 : ‖((1 - τ : ℝ) : ℂ) ^ 2 * traceNumber (mul p (mul p (unitShiftedInverse p A)
        (unitShiftedInverse p A)) (perturbedInverse p A W τ))‖ ≤ γ * b ^ 3 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0]
      exact (mul_le_of_le_one_left (norm_nonneg _) hu2).trans b1
    have n3 : ‖((1 - τ : ℝ) : ℂ) * traceNumber (mul p (mul p (mul p (unitShiftedInverse p A)
        (unitShiftedInverse p A)) W) (perturbedInverse p A W τ))‖ ≤
        (fiberDim J + fiberDim J') * a ^ 2 * (b * g * (b * g * b)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
      exact (mul_le_of_le_one_left (norm_nonneg _) hu1).trans b3
    unfold correctionIntegrand
    refine (norm_sub_le _ _).trans ?_
    have := norm_sub_le (((1 - τ : ℝ) : ℂ) ^ 2 * traceNumber (mul p
        (mul p (unitShiftedInverse p A) (unitShiftedInverse p A)) (perturbedInverse p A W τ)))
      (traceNumber (mul p (mul p (unitShiftedInverse p A) W) (perturbedInverse p A W τ)))
    linarith
  constructor
  · unfold pathRemainder
    have a1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun t => traceNumber (mul p (invJet p (unitShiftedPath A W t)) W))
      (C := (fiberDim J + fiberDim J') * a ^ 2 * b)
      (fun t ht => i1 t (by
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact ⟨ht.1.le, ht.2⟩))
    have a2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun τ => correctionIntegrand p A W τ)
      (C := (fiberDim J + fiberDim J') * a ^ 2 * (b * g * b) +
        (fiberDim J + fiberDim J') * a ^ 2 * (b * g * (b * g * b)) + γ * b ^ 3)
      (fun t ht => i2 t (by
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact ⟨ht.1.le, ht.2⟩))
    have e1 : |(1 : ℝ) - 0| = 1 := by norm_num
    rw [e1, mul_one] at a1 a2
    refine (norm_sub_le _ _).trans ((add_le_add a1 a2).trans (le_of_eq ?_))
    ring
  · obtain ⟨F, hF, nF, e⟩ := root (A.add W) (hz ▸ D.shifted 0 ⟨le_rfl, zero_le_one⟩)
    have hQT := H.isJet_transposeAt hQ
    have hFN := H.isJet_mul hF hNj
    have hxF := H.isJet_mul hx hF
    have hxT := H.isJet_transposeAt hx
    have s1 : JetEquiv stripHalfWidth p (mul p Q (invJet p (A.add W)))
        (mul p (mul p (mul p Q N) F) N) :=
      (((H.equiv_mul (JetEquiv.rfl' hQ) e).trans' (H.equiv_mul (JetEquiv.rfl' hQ)
        (H.mul_assoc' hNj hF hNj))).trans' (H.mul_assoc' hQ hNj hFN).symm').trans'
          (H.mul_assoc' hx hF hNj).symm'
    have s2 := H.mul_assoc' hxF hNj hQT
    have s3 : JetEquiv stripHalfWidth p (mul p N (transposeAt p Q)) (transposeAt p (mul p Q N)) :=
      ((H.transposeAt_mul hQ hNj).trans' (H.equiv_mul
        ⟨H.isJet_transposeAt hNj, hNj, D.transpose_self⟩ (JetEquiv.rfl' hQT))).symm'
    have s4 := ((H.equiv_mul s1 (JetEquiv.rfl' hQT)).trans' s2).trans'
      (H.equiv_mul (JetEquiv.rfl' hxF) s3)
    rw [H.jetNorm_eq_of_equiv s4]
    have e2 : ENNReal.ofReal (a ^ 2 * b) =
        ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal a := by
      rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [e2]
    exact (H.jetNorm_mul_le hxF hxT).trans (mul_le_mul'
      ((H.jetNorm_mul_le hx hF).trans (mul_le_mul' D.x_norm_le nF))
      ((H.jetNorm_transposeAt hx).le.trans D.x_norm_le))
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.RootInterpolation
end
