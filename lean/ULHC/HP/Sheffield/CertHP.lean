/-
SPDX-License-Identifier: CC0-1.0
Dedicated to the public domain under CC0 1.0 Universal; see LICENSE.
-/
import ULHC.HP.Sheffield.Cert
import ULHC.HP.NotchPF

/-!
# A certified "no": no Hamiltonian s–t path

For `t` in a notch with phantom neighbour `p ∉ V` (edge `e0 = t–p`) and `s` dangling (a corner of
no cell of `V`), a state `G` on `V ∪ {p}` with a certificate `Cert V G FP t0 u0` and more than
`|FP| + 1` pieces rules out every Hamiltonian `s–t` path: such a path, with `e0`, is a factor of
the same degrees that agrees with `G` off `V` and has one piece (`cert_count`).
-/

namespace ULHC

namespace HP

open Finset Classical

theorem cert_no_hp {V : Finset Pt} {s t p : Pt} {e0 : Edge} (hs : Solid V) (hst : s ≠ t)
    (htV : t ∈ V) (hpV : p ∉ V) (he0 : Ends e0 t p) (hsD : ∀ c, IsCell V c → ¬ IsCorner s c)
    {G : Finset Edge} (hG : NotchF V s p e0 G) {FP : List FixedPr} {t0 u0 : Pt}
    (hc : Cert V G FP t0 u0) (hbig : FP.length + 1 < ncomp V G) :
    ¬ ∃ H, IsFactor V (dST s t) H ∧ ncomp V H = 1 := by
  rintro ⟨H, hH, hHam⟩
  have hHN := notch_up hst htV hpV he0 hH
  have hHam' : ncomp V (insert e0 H) = 1 := ncomp_one_of_conn htV (fun x hx y hy =>
    (conn_of_ncomp_one hHam hx hy).mono (Finset.subset_insert _ _))
  have hdc : ∀ q, IsCell V q → ∀ z, IsCorner z q → dST s p z = 2 := by
    intro q hq z hz
    have hzV : z ∈ V := by
      obtain ⟨x, y⟩ := q
      rcases hz with rfl | rfl | rfl | rfl
      · exact hq.1
      · exact hq.2.1
      · exact hq.2.2.1
      · exact hq.2.2.2
    have hzs : z ≠ s := fun h => hsD q hq (h ▸ hz)
    have hzp : z ≠ p := fun h => hpV (h ▸ hzV)
    unfold dST; simp [hzs, hzp]
  have hcount := cert_count hG.fac hHN.fac hs (Finset.subset_insert p V) hdc
    (symmDiff_inside_of_PAt (Inside.of_factor hG.fac) (Inside.of_factor hHN.fac) hG.pat hHN.pat) hc
  rw [hG.ncomp htV he0, hHN.ncomp htV he0, hHam'] at hcount
  omega

end HP

end ULHC
