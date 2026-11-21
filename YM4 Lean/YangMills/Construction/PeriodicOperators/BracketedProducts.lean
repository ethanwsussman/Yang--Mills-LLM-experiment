import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
inductive IsBracketing {b : ℕ} (X : Fin (b + 1) → PeriodicData)
    (K : (i : Fin b) → (X i.castSucc).Carrier → (X i.succ).Carrier → ℂ) :
    (lo hi : Fin (b + 1)) → ((X lo).Carrier → (X hi).Carrier → ℂ) → Prop
  | leaf (i : Fin b) : IsBracketing X K i.castSucc i.succ (K i)
  | node {lo mid hi : Fin (b + 1)} (P : (X lo).Carrier → (X mid).Carrier → ℂ)
      (Q : (X mid).Carrier → (X hi).Carrier → ℂ)
      (hP : IsBracketing X K lo mid P) (hQ : IsBracketing X K mid hi Q)
      (hPper : IsPeriodicKernel (X mid) (X lo) P)
      (hQper : IsPeriodicKernel (X hi) (X mid) Q) :
      IsBracketing X K lo hi (compKernel P Q)
end YangMills.Construction.PeriodicOperators
end
