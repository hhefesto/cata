# The proofs of PROPOSED.bend's naturality laws.  Nothing here is trusted:
# `bend PROOF.bend --verdict` rechecks them with BendTT's kernel.

import Base
import ./l/HsPrelude.bend as H
import ./l/Telomare_IR_Base.bend as B
import ./l/Telomare_Size_IR.bend as Y
import ./PROPOSED.bend as Proposed

def Proposed.nat.unFix(F, fw, x):
  {==}

def Proposed.nat.Deferred(x):
  {==}

# not by unfolding the copy: the instance rewrites it to the polymorphic
# def, where the law proved once applies
def Proposed.nat.unFix.at(x):
  %Proposed.nat.Deferred(x) : {H.Fix.unFix((r_ => Y.DeferredExprF<r_>), _) == Y.bBasicFW__DeferredExprF_Fix_DeferredExprF(x) : Y.DeferredExprF<H.Fix<(r_ => Y.DeferredExprF<r_>)>>}
  Proposed.nat.unFix((r_ => Y.DeferredExprF<r_>), y => Y.bBasicFW__DeferredExprF_Fix_DeferredExprF(y), x)
