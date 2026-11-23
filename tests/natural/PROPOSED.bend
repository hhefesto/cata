# Naturality, proposed for the human to move into a LAWS.bend (or reword or
# drop); PROOF.bend proves them.
#
# cata's specialiser (bend/Spec.bend) writes a copy of a polymorphic def at
# each type it is used at (telomare's bBasicEE, at Fix StuckExprF, Fix
# UnsizedExprF, ... : bBasicEE__Fix_StuckExprF_StuckExprF ...), with the
# class methods it calls resolved to their copies at that type.  With its
# types erased (bend2hs, tests/natural/Copies.hs) every copy of bBasicEE is
# one program up to the copies it calls: the copies are the components of
# one natural transformation, the methods its dictionary.  So the def is
# written here once, polymorphic, its dictionary its arguments (ee: the
# type's embed, Fix's or Cofree's; fw: the instance's embedding of a
# BasicExprF layer), a law about it is proved once, and each copy is an
# instance:
#
#   basicEE(T, L, copy's embed, copy's fw, x) == copy(x)    for every x,
#
# so the law holds at every copy (nat.unFix.at: by the instance and the law
# proved once, never by unfolding the copy again).
#
# Y is telomare's Telomare.Size.IR as a law run wrote it (./l: every module
# of a run on telomare, HsPrelude.bend among them; tests/natural/run.zsh).

import Base
import ./l/HsPrelude.bend as H
import ./l/Telomare_IR_Base.bend as B
import ./l/Telomare_Size_IR.bend as Y

# bBasicEE, once: T the fixed point, L its layer, ee its embed, fw the
# instance's embedding of a BasicExprF layer
def basicEE(-T: Data, -L: Data, ee: L -> T, fw: B.BasicExprF<T> -> L, x: B.BasicExprF<T>) -> T:
  ee(fw(x))

# the law, once: at Fix f, with Fix's embed, unFix undoes it
law nat.unFix:
  for -F: Data -> Data
  for fw: B.BasicExprF<H.Fix<F>> -> F(H.Fix<F>)
  for x: B.BasicExprF<H.Fix<F>>
  {H.Fix.unFix(F, basicEE(H.Fix<F>, F(H.Fix<F>), y => H.Fix.Fix{y}, fw, x)) == fw(x) : F(H.Fix<F>)}

# a copy, an instance (Telomare.Size.IR's; Telomare.Size has two more, at
# InputSizingExprF and UnsizedExprF, but BendTT's kernel cannot take that
# module: its translation of Telomare.PrettyPrint.Indent overflows bend's
# machine stack)
law nat.Deferred:
  for x: B.BasicExprF<H.Fix<(r_ => Y.DeferredExprF<r_>)>>
  {basicEE(H.Fix<(r_ => Y.DeferredExprF<r_>)>, Y.DeferredExprF<H.Fix<(r_ => Y.DeferredExprF<r_>)>>, y => Y.bGFix__Fix_DeferredExprF_DeferredExprF(y), y => Y.bBasicFW__DeferredExprF_Fix_DeferredExprF(y), x) == Y.bBasicEE__Fix_DeferredExprF_DeferredExprF(x) : H.Fix<(r_ => Y.DeferredExprF<r_>)>}

# the law at a copy, from the instance and the law proved once
law nat.unFix.at:
  for +x: B.BasicExprF<H.Fix<(r_ => Y.DeferredExprF<r_>)>>
  {H.Fix.unFix((r_ => Y.DeferredExprF<r_>), Y.bBasicEE__Fix_DeferredExprF_DeferredExprF(x)) == Y.bBasicFW__DeferredExprF_Fix_DeferredExprF(x) : Y.DeferredExprF<H.Fix<(r_ => Y.DeferredExprF<r_>)>>}
