# GHC's recursion and functions as values, against Core.bend's (section 14):
# written by RecGhc.hs (adj/int.zsh), not by hand

import Base
import ./Core.bend as C

def even() -> C.HPg:
  C.HPg{C.HdCons{C.HrIf{C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{1n}}}}, C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrTm{C.HLit{0n}}, C.HrTm{C.HLit{1n}}}}, C.HrComp{C.HrCall{1n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{1n}}}}}}}, C.HvNat{0n}, C.HdCons{C.HrIf{C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{1n}}}}, C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrTm{C.HLit{1n}}, C.HrTm{C.HLit{0n}}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{1n}}}}}}}, C.HvNat{0n}, C.HdNil{}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrTm{C.HSnd{}}}}}

def ghc.even.i1() -> {C.eval.hp(40n, even(), C.HvPair{C.HvUnit{}, C.HvNat{0n}}) == C.RDone{Some{C.HvBool{True{}}}} : C.Run}:
  {==}

def ghc.even.i1.F() -> {C.eval.bp(C.F.pn(40n, even()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{0n}})) == C.encM(Some{C.HvBool{True{}}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.even.i2() -> {C.eval.hp(40n, even(), C.HvPair{C.HvUnit{}, C.HvNat{1n}}) == C.RDone{Some{C.HvBool{False{}}}} : C.Run}:
  {==}

def ghc.even.i2.F() -> {C.eval.bp(C.F.pn(40n, even()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{1n}})) == C.encM(Some{C.HvBool{False{}}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.even.i3() -> {C.eval.hp(40n, even(), C.HvPair{C.HvUnit{}, C.HvNat{2n}}) == C.RDone{Some{C.HvBool{True{}}}} : C.Run}:
  {==}

def ghc.even.i3.F() -> {C.eval.bp(C.F.pn(40n, even()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{2n}})) == C.encM(Some{C.HvBool{True{}}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.even.i4() -> {C.eval.hp(40n, even(), C.HvPair{C.HvUnit{}, C.HvNat{7n}}) == C.RDone{Some{C.HvBool{False{}}}} : C.Run}:
  {==}

def ghc.even.i4.F() -> {C.eval.bp(C.F.pn(40n, even()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{7n}})) == C.encM(Some{C.HvBool{False{}}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.even.i5() -> {C.eval.hp(40n, even(), C.HvPair{C.HvUnit{}, C.HvNat{10n}}) == C.RDone{Some{C.HvBool{True{}}}} : C.Run}:
  {==}

def ghc.even.i5.F() -> {C.eval.bp(C.F.pn(40n, even()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{10n}})) == C.encM(Some{C.HvBool{True{}}}) : Maybe<&2, C.BV>}:
  {==}

def hofG() -> C.HPg:
  C.HPg{C.HdCons{C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrComp{C.HrCall{1n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrTm{C.HSnd{}}}}, C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrComp{C.HrCall{2n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrTm{C.HSnd{}}}}, C.HrTm{C.HLit{1n}}}}}}, C.HvNat{0n}, C.HdCons{C.HrIf{C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{1n}}}}, C.HrTm{C.HLit{1n}}, C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrComp{C.HrCall{2n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrCall{1n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{1n}}}}}}}}}}}, C.HvNat{0n}, C.HdCons{C.HrIf{C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{1n}}}}, C.HrTm{C.HLit{0n}}, C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrComp{C.HrCall{1n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrCall{2n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{1n}}}}}}}}}}}, C.HvNat{0n}, C.HdNil{}}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrTm{C.HSnd{}}}}}

def ghc.hofG.i1() -> {C.eval.hp(60n, hofG(), C.HvPair{C.HvUnit{}, C.HvNat{0n}}) == C.RDone{None{}} : C.Run}:
  {==}

def ghc.hofG.i1.F() -> {C.eval.bp(C.F.pn(60n, hofG()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{0n}})) == C.encM(None{}) : Maybe<&2, C.BV>}:
  {==}

def ghc.hofG.i2() -> {C.eval.hp(60n, hofG(), C.HvPair{C.HvUnit{}, C.HvNat{1n}}) == C.RDone{None{}} : C.Run}:
  {==}

def ghc.hofG.i2.F() -> {C.eval.bp(C.F.pn(60n, hofG()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{1n}})) == C.encM(None{}) : Maybe<&2, C.BV>}:
  {==}

def ghc.hofG.i3() -> {C.eval.hp(60n, hofG(), C.HvPair{C.HvUnit{}, C.HvNat{3n}}) == C.RDone{Some{C.HvNat{3n}}} : C.Run}:
  {==}

def ghc.hofG.i3.F() -> {C.eval.bp(C.F.pn(60n, hofG()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{3n}})) == C.encM(Some{C.HvNat{3n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.hofG.i4() -> {C.eval.hp(60n, hofG(), C.HvPair{C.HvUnit{}, C.HvNat{5n}}) == C.RDone{Some{C.HvNat{5n}}} : C.Run}:
  {==}

def ghc.hofG.i4.F() -> {C.eval.bp(C.F.pn(60n, hofG()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{5n}})) == C.encM(Some{C.HvNat{5n}}) : Maybe<&2, C.BV>}:
  {==}

def hofF() -> C.HPg:
  C.HPg{C.HdCons{C.HrIf{C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{1n}}}}, C.HrTm{C.HLit{1n}}, C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrComp{C.HrCall{1n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{1n}}}}}}}}}}}, C.HvNat{0n}, C.HdCons{C.HrIf{C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{1n}}}}, C.HrTm{C.HLit{0n}}, C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrCall{1n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{1n}}}}}}}}}}}, C.HvNat{0n}, C.HdNil{}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrTm{C.HSnd{}}}}}

def ghc.hofF.i1() -> {C.eval.hp(60n, hofF(), C.HvPair{C.HvUnit{}, C.HvNat{0n}}) == C.RDone{Some{C.HvNat{1n}}} : C.Run}:
  {==}

def ghc.hofF.i1.F() -> {C.eval.bp(C.F.pn(60n, hofF()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{0n}})) == C.encM(Some{C.HvNat{1n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.hofF.i2() -> {C.eval.hp(60n, hofF(), C.HvPair{C.HvUnit{}, C.HvNat{1n}}) == C.RDone{Some{C.HvNat{1n}}} : C.Run}:
  {==}

def ghc.hofF.i2.F() -> {C.eval.bp(C.F.pn(60n, hofF()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{1n}})) == C.encM(Some{C.HvNat{1n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.hofF.i3() -> {C.eval.hp(60n, hofF(), C.HvPair{C.HvUnit{}, C.HvNat{4n}}) == C.RDone{Some{C.HvNat{3n}}} : C.Run}:
  {==}

def ghc.hofF.i3.F() -> {C.eval.bp(C.F.pn(60n, hofF()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{4n}})) == C.encM(Some{C.HvNat{3n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.hofF.i4() -> {C.eval.hp(60n, hofF(), C.HvPair{C.HvUnit{}, C.HvNat{6n}}) == C.RDone{Some{C.HvNat{4n}}} : C.Run}:
  {==}

def ghc.hofF.i4.F() -> {C.eval.bp(C.F.pn(60n, hofF()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{6n}})) == C.encM(Some{C.HvNat{4n}}) : Maybe<&2, C.BV>}:
  {==}

def ack() -> C.HPg:
  C.HPg{C.HdCons{C.HrIf{C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrTm{C.HLit{1n}}}}, C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}, C.HrTm{C.HLit{1n}}}}, C.HrIf{C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}, C.HrTm{C.HLit{1n}}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrTm{C.HLit{1n}}}}, C.HrTm{C.HLit{1n}}}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrTm{C.HLit{1n}}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}, C.HrTm{C.HLit{1n}}}}}}}}}}}}, C.HvNat{0n}, C.HdNil{}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrTm{C.HSnd{}}}}}

def ghc.ack.i1() -> {C.eval.hp(60n, ack(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{0n}, C.HvNat{3n}}}) == C.RDone{Some{C.HvNat{4n}}} : C.Run}:
  {==}

def ghc.ack.i1.F() -> {C.eval.bp(C.F.pn(60n, ack()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{0n}, C.HvNat{3n}}})) == C.encM(Some{C.HvNat{4n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.ack.i2() -> {C.eval.hp(60n, ack(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{1n}, C.HvNat{2n}}}) == C.RDone{Some{C.HvNat{4n}}} : C.Run}:
  {==}

def ghc.ack.i2.F() -> {C.eval.bp(C.F.pn(60n, ack()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{1n}, C.HvNat{2n}}})) == C.encM(Some{C.HvNat{4n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.ack.i3() -> {C.eval.hp(60n, ack(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{2n}, C.HvNat{2n}}}) == C.RDone{Some{C.HvNat{7n}}} : C.Run}:
  {==}

def ghc.ack.i3.F() -> {C.eval.bp(C.F.pn(60n, ack()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{2n}, C.HvNat{2n}}})) == C.encM(Some{C.HvNat{7n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.ack.i4() -> {C.eval.hp(60n, ack(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{2n}, C.HvNat{3n}}}) == C.RDone{Some{C.HvNat{9n}}} : C.Run}:
  {==}

def ghc.ack.i4.F() -> {C.eval.bp(C.F.pn(60n, ack()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{2n}, C.HvNat{3n}}})) == C.encM(Some{C.HvNat{9n}}) : Maybe<&2, C.BV>}:
  {==}

def collatz() -> C.HPg:
  C.HPg{C.HdCons{C.HrIf{C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{2n}}}}, C.HrTm{C.HLit{0n}}, C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrTm{C.HLit{1n}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrIf{C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrComp{C.HrTm{C.HPrim{C.PMod{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{2n}}}}, C.HrTm{C.HLit{1n}}}}, C.HrComp{C.HrTm{C.HPrim{C.PDiv{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{2n}}}}, C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrTm{C.HLit{1n}}, C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}}}}}}}}, C.HvNat{0n}, C.HdNil{}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrTm{C.HSnd{}}}}}

def ghc.collatz.i1() -> {C.eval.hp(60n, collatz(), C.HvPair{C.HvUnit{}, C.HvNat{1n}}) == C.RDone{Some{C.HvNat{0n}}} : C.Run}:
  {==}

def ghc.collatz.i1.F() -> {C.eval.bp(C.F.pn(60n, collatz()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{1n}})) == C.encM(Some{C.HvNat{0n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.collatz.i2() -> {C.eval.hp(60n, collatz(), C.HvPair{C.HvUnit{}, C.HvNat{3n}}) == C.RDone{Some{C.HvNat{7n}}} : C.Run}:
  {==}

def ghc.collatz.i2.F() -> {C.eval.bp(C.F.pn(60n, collatz()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{3n}})) == C.encM(Some{C.HvNat{7n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.collatz.i3() -> {C.eval.hp(60n, collatz(), C.HvPair{C.HvUnit{}, C.HvNat{6n}}) == C.RDone{Some{C.HvNat{8n}}} : C.Run}:
  {==}

def ghc.collatz.i3.F() -> {C.eval.bp(C.F.pn(60n, collatz()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{6n}})) == C.encM(Some{C.HvNat{8n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.collatz.i4() -> {C.eval.hp(60n, collatz(), C.HvPair{C.HvUnit{}, C.HvNat{7n}}) == C.RDone{Some{C.HvNat{16n}}} : C.Run}:
  {==}

def ghc.collatz.i4.F() -> {C.eval.bp(C.F.pn(60n, collatz()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{7n}})) == C.encM(Some{C.HvNat{16n}}) : Maybe<&2, C.BV>}:
  {==}

def addAll() -> C.HPg:
  C.HPg{C.HdCons{C.HrComp{C.HrCase{C.HrTm{C.HNil{}}, C.HrCons{C.HrComp{C.HrApp{}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}}, C.HrComp{C.HrTm{C.HDist{}}, C.HrPr{C.HrTm{C.HId{}}, C.HrComp{C.HrTm{C.HFold{C.HComp{C.HInl{}, C.HUnit{}}, C.HComp{C.HInr{}, C.HPr{C.HFst{}, C.HComp{C.HCase{C.HNil{}, C.HCons{C.HFst{}, C.HSnd{}}}, C.HSnd{}}}}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}}}, C.HvNat{0n}, C.HdNil{}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrTm{C.clo(1n)}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}

def ghc.addAll.i1() -> {C.eval.hp(30n, addAll(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{5n}, C.HvNil{}}}) == C.RDone{Some{C.HvNil{}}} : C.Run}:
  {==}

def ghc.addAll.i1.F() -> {C.eval.bp(C.F.pn(30n, addAll()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{5n}, C.HvNil{}}})) == C.encM(Some{C.HvNil{}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.addAll.i2() -> {C.eval.hp(30n, addAll(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{5n}, C.HvCons{C.HvNat{1n}, C.HvCons{C.HvNat{2n}, C.HvCons{C.HvNat{3n}, C.HvNil{}}}}}}) == C.RDone{Some{C.HvCons{C.HvNat{6n}, C.HvCons{C.HvNat{7n}, C.HvCons{C.HvNat{8n}, C.HvNil{}}}}}} : C.Run}:
  {==}

def ghc.addAll.i2.F() -> {C.eval.bp(C.F.pn(30n, addAll()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{5n}, C.HvCons{C.HvNat{1n}, C.HvCons{C.HvNat{2n}, C.HvCons{C.HvNat{3n}, C.HvNil{}}}}}})) == C.encM(Some{C.HvCons{C.HvNat{6n}, C.HvCons{C.HvNat{7n}, C.HvCons{C.HvNat{8n}, C.HvNil{}}}}}) : Maybe<&2, C.BV>}:
  {==}

def applyAll() -> C.HPg:
  C.HPg{C.HdCons{C.HrComp{C.HrCase{C.HrTm{C.HNil{}}, C.HrCons{C.HrComp{C.HrApp{}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}}, C.HrComp{C.HrTm{C.HDist{}}, C.HrPr{C.HrTm{C.HId{}}, C.HrComp{C.HrTm{C.HFold{C.HComp{C.HInl{}, C.HUnit{}}, C.HComp{C.HInr{}, C.HPr{C.HFst{}, C.HComp{C.HCase{C.HNil{}, C.HCons{C.HFst{}, C.HSnd{}}}, C.HSnd{}}}}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrApp{}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HLit{1n}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrTm{C.HPrim{C.PDiv{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}}, C.HvNat{0n}, C.HdNil{}}}}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrTm{C.clo(1n)}, C.HrCons{C.HrTm{C.clo(2n)}, C.HrCons{C.HrTm{C.HPr{C.HLit{3n}, C.HUnit{}}}, C.HrCons{C.HrTm{C.clo(4n)}, C.HrTm{C.HNil{}}}}}}}}}

def ghc.applyAll.i1() -> {C.eval.hp(30n, applyAll(), C.HvPair{C.HvUnit{}, C.HvNat{0n}}) == C.RDone{None{}} : C.Run}:
  {==}

def ghc.applyAll.i1.F() -> {C.eval.bp(C.F.pn(30n, applyAll()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{0n}})) == C.encM(None{}) : Maybe<&2, C.BV>}:
  {==}

def ghc.applyAll.i2() -> {C.eval.hp(30n, applyAll(), C.HvPair{C.HvUnit{}, C.HvNat{1n}}) == C.RDone{Some{C.HvCons{C.HvNat{2n}, C.HvCons{C.HvNat{2n}, C.HvCons{C.HvNat{1n}, C.HvNil{}}}}}} : C.Run}:
  {==}

def ghc.applyAll.i2.F() -> {C.eval.bp(C.F.pn(30n, applyAll()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{1n}})) == C.encM(Some{C.HvCons{C.HvNat{2n}, C.HvCons{C.HvNat{2n}, C.HvCons{C.HvNat{1n}, C.HvNil{}}}}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.applyAll.i3() -> {C.eval.hp(30n, applyAll(), C.HvPair{C.HvUnit{}, C.HvNat{4n}}) == C.RDone{Some{C.HvCons{C.HvNat{8n}, C.HvCons{C.HvNat{5n}, C.HvCons{C.HvNat{1n}, C.HvNil{}}}}}} : C.Run}:
  {==}

def ghc.applyAll.i3.F() -> {C.eval.bp(C.F.pn(30n, applyAll()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{4n}})) == C.encM(Some{C.HvCons{C.HvNat{8n}, C.HvCons{C.HvNat{5n}, C.HvCons{C.HvNat{1n}, C.HvNil{}}}}}) : Maybe<&2, C.BV>}:
  {==}

def twiceTwice() -> C.HPg:
  C.HPg{C.HdCons{C.HrTm{C.clo(1n)}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrApp{}, C.HrPr{C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}, C.HrComp{C.HrApp{}, C.HrPr{C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}, C.HrTm{C.HSnd{}}}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}}, C.HvNat{0n}, C.HdNil{}}}}, C.HrComp{C.HrApp{}, C.HrPr{C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrTm{C.clo(2n)}}}}}, C.HrTm{C.HSnd{}}}}}

def ghc.twiceTwice.i1() -> {C.eval.hp(30n, twiceTwice(), C.HvPair{C.HvUnit{}, C.HvNat{0n}}) == C.RDone{Some{C.HvNat{0n}}} : C.Run}:
  {==}

def ghc.twiceTwice.i1.F() -> {C.eval.bp(C.F.pn(30n, twiceTwice()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{0n}})) == C.encM(Some{C.HvNat{0n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.twiceTwice.i2() -> {C.eval.hp(30n, twiceTwice(), C.HvPair{C.HvUnit{}, C.HvNat{3n}}) == C.RDone{Some{C.HvNat{15n}}} : C.Run}:
  {==}

def ghc.twiceTwice.i2.F() -> {C.eval.bp(C.F.pn(30n, twiceTwice()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{3n}})) == C.encM(Some{C.HvNat{15n}}) : Maybe<&2, C.BV>}:
  {==}

def minusAll() -> C.HPg:
  C.HPg{C.HdCons{C.HrComp{C.HrCase{C.HrComp{C.HrTm{C.HFst{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}}, C.HrComp{C.HrApp{}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}}}}}, C.HrComp{C.HrTm{C.HDist{}}, C.HrPr{C.HrTm{C.HId{}}, C.HrComp{C.HrTm{C.HFold{C.HComp{C.HInl{}, C.HUnit{}}, C.HComp{C.HInr{}, C.HPr{C.HFst{}, C.HComp{C.HCase{C.HNil{}, C.HCons{C.HFst{}, C.HSnd{}}}, C.HSnd{}}}}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}}, C.HvNat{0n}, C.HdCons{C.HrTm{C.clo(2n)}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrApp{}, C.HrPr{C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrComp{C.HrApp{}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrPr{C.HrTm{C.clo(3n)}, C.HrTm{C.HComp{C.HComp{C.HSnd{}, C.HFst{}}, C.HFst{}}}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}}}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}, C.HvNat{0n}, C.HdCons{C.HrTm{C.HSnd{}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}, C.HvNat{0n}, C.HdNil{}}}}}}}}, C.HrComp{C.HrApp{}, C.HrPr{C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrTm{C.clo(1n)}, C.HrPr{C.HrTm{C.clo(4n)}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrPr{C.HrTm{C.clo(5n)}, C.HrTm{C.HSnd{}}}}}}}}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrPr{C.HrTm{C.clo(6n)}, C.HrTm{C.HSnd{}}}}}}}}

def ghc.minusAll.i1() -> {C.eval.hp(30n, minusAll(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{10n}, C.HvCons{C.HvNat{1n}, C.HvCons{C.HvNat{2n}, C.HvCons{C.HvNat{3n}, C.HvNil{}}}}}}) == C.RDone{Some{C.HvNat{4n}}} : C.Run}:
  {==}

def ghc.minusAll.i1.F() -> {C.eval.bp(C.F.pn(30n, minusAll()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{10n}, C.HvCons{C.HvNat{1n}, C.HvCons{C.HvNat{2n}, C.HvCons{C.HvNat{3n}, C.HvNil{}}}}}})) == C.encM(Some{C.HvNat{4n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.minusAll.i2() -> {C.eval.hp(30n, minusAll(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{3n}, C.HvCons{C.HvNat{2n}, C.HvCons{C.HvNat{2n}, C.HvNil{}}}}}) == C.RDone{None{}} : C.Run}:
  {==}

def ghc.minusAll.i2.F() -> {C.eval.bp(C.F.pn(30n, minusAll()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{3n}, C.HvCons{C.HvNat{2n}, C.HvCons{C.HvNat{2n}, C.HvNil{}}}}})) == C.encM(None{}) : Maybe<&2, C.BV>}:
  {==}

def ghc.minusAll.i3() -> {C.eval.hp(30n, minusAll(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{4n}, C.HvNil{}}}) == C.RDone{Some{C.HvNat{4n}}} : C.Run}:
  {==}

def ghc.minusAll.i3.F() -> {C.eval.bp(C.F.pn(30n, minusAll()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{4n}, C.HvNil{}}})) == C.encM(Some{C.HvNat{4n}}) : Maybe<&2, C.BV>}:
  {==}

def fact() -> C.HPg:
  C.HPg{C.HdCons{C.HrIf{C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrTm{C.HLit{1n}}}}, C.HrComp{C.HrApp{}, C.HrPr{C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}, C.HrTm{C.HLit{1n}}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrTm{C.HLit{1n}}}}, C.HrTm{C.clo(1n)}}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrApp{}, C.HrPr{C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrComp{C.HrCall{2n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrTm{C.HSnd{}}}}}}}, C.HvNat{0n}, C.HdCons{C.HrIf{C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrTm{C.HLit{1n}}}}, C.HrTm{C.HLit{0n}}, C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrCall{2n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrTm{C.HLit{1n}}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}}}, C.HvNat{0n}, C.HdCons{C.HrTm{C.HSnd{}}, C.HvNat{0n}, C.HdNil{}}}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.clo(3n)}}}}}

def ghc.fact.i1() -> {C.eval.hp(60n, fact(), C.HvPair{C.HvUnit{}, C.HvNat{0n}}) == C.RDone{Some{C.HvNat{1n}}} : C.Run}:
  {==}

def ghc.fact.i1.F() -> {C.eval.bp(C.F.pn(60n, fact()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{0n}})) == C.encM(Some{C.HvNat{1n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.fact.i2() -> {C.eval.hp(60n, fact(), C.HvPair{C.HvUnit{}, C.HvNat{1n}}) == C.RDone{Some{C.HvNat{1n}}} : C.Run}:
  {==}

def ghc.fact.i2.F() -> {C.eval.bp(C.F.pn(60n, fact()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{1n}})) == C.encM(Some{C.HvNat{1n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.fact.i3() -> {C.eval.hp(60n, fact(), C.HvPair{C.HvUnit{}, C.HvNat{4n}}) == C.RDone{Some{C.HvNat{24n}}} : C.Run}:
  {==}

def ghc.fact.i3.F() -> {C.eval.bp(C.F.pn(60n, fact()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{4n}})) == C.encM(Some{C.HvNat{24n}}) : Maybe<&2, C.BV>}:
  {==}

def sumConcat() -> C.HPg:
  C.HPg{C.HdCons{C.HrComp{C.HrCase{C.HrComp{C.HrTm{C.HFst{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}}, C.HrComp{C.HrApp{}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}}}}}, C.HrComp{C.HrTm{C.HDist{}}, C.HrPr{C.HrTm{C.HId{}}, C.HrComp{C.HrTm{C.HFold{C.HComp{C.HInl{}, C.HUnit{}}, C.HComp{C.HInr{}, C.HPr{C.HFst{}, C.HComp{C.HCase{C.HNil{}, C.HCons{C.HFst{}, C.HSnd{}}}, C.HSnd{}}}}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrTm{C.clo(2n)}, C.HrPr{C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}}}}}, C.HvNat{0n}, C.HdCons{C.HrCons{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrTm{C.clo(4n)}, C.HrPr{C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}}}}}, C.HvNat{0n}, C.HdCons{C.HrCons{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrTm{C.clo(6n)}, C.HrPr{C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}}}}}, C.HvNat{0n}, C.HdCons{C.HrCons{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}, C.HvNat{0n}, C.HdNil{}}}}}}}}}}}, C.HrComp{C.HrPr{C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HSnd{}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrPr{C.HrPr{C.HrTm{C.HLit{0n}}, C.HrTm{C.clo(7n)}}, C.HrTm{C.HSnd{}}}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrPr{C.HrPr{C.HrTm{C.HLit{0n}}, C.HrTm{C.clo(8n)}}, C.HrTm{C.HSnd{}}}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrPr{C.HrPr{C.HrTm{C.HLit{0n}}, C.HrTm{C.clo(9n)}}, C.HrTm{C.HSnd{}}}}}}}}, C.HrTm{C.HSnd{}}}, C.HrPr{C.HrTm{C.HId{}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HSnd{}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrPr{C.HrPr{C.HrTm{C.HNil{}}, C.HrTm{C.clo(1n)}}, C.HrTm{C.HSnd{}}}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrPr{C.HrPr{C.HrTm{C.HNil{}}, C.HrTm{C.clo(3n)}}, C.HrTm{C.HSnd{}}}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrPr{C.HrPr{C.HrTm{C.HNil{}}, C.HrTm{C.clo(5n)}}, C.HrTm{C.HSnd{}}}}}}}}}}}

def ghc.sumConcat.i1() -> {C.eval.hp(40n, sumConcat(), C.HvPair{C.HvUnit{}, C.HvNil{}}) == C.RDone{Some{C.HvPair{C.HvNat{0n}, C.HvNil{}}}} : C.Run}:
  {==}

def ghc.sumConcat.i1.F() -> {C.eval.bp(C.F.pn(40n, sumConcat()), C.enc(C.HvPair{C.HvUnit{}, C.HvNil{}})) == C.encM(Some{C.HvPair{C.HvNat{0n}, C.HvNil{}}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.sumConcat.i2() -> {C.eval.hp(40n, sumConcat(), C.HvPair{C.HvUnit{}, C.HvCons{C.HvCons{C.HvNat{1n}, C.HvCons{C.HvNat{2n}, C.HvNil{}}}, C.HvCons{C.HvNil{}, C.HvCons{C.HvCons{C.HvNat{3n}, C.HvNil{}}, C.HvNil{}}}}}) == C.RDone{Some{C.HvPair{C.HvNat{6n}, C.HvCons{C.HvNat{1n}, C.HvCons{C.HvNat{2n}, C.HvCons{C.HvNat{3n}, C.HvNil{}}}}}}} : C.Run}:
  {==}

def ghc.sumConcat.i2.F() -> {C.eval.bp(C.F.pn(40n, sumConcat()), C.enc(C.HvPair{C.HvUnit{}, C.HvCons{C.HvCons{C.HvNat{1n}, C.HvCons{C.HvNat{2n}, C.HvNil{}}}, C.HvCons{C.HvNil{}, C.HvCons{C.HvCons{C.HvNat{3n}, C.HvNil{}}, C.HvNil{}}}}})) == C.encM(Some{C.HvPair{C.HvNat{6n}, C.HvCons{C.HvNat{1n}, C.HvCons{C.HvNat{2n}, C.HvCons{C.HvNat{3n}, C.HvNil{}}}}}}) : Maybe<&2, C.BV>}:
  {==}

def roseSum() -> C.HPg:
  C.HPg{C.HdCons{C.HrComp{C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrCall{1n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}, C.HrPr{C.HrTm{C.HId{}}, C.HrTm{C.HSnd{}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrCase{C.HrTm{C.HLit{0n}}, C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}}}, C.HrComp{C.HrCall{1n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}}, C.HrComp{C.HrTm{C.HDist{}}, C.HrPr{C.HrTm{C.HId{}}, C.HrTm{C.HSnd{}}}}}, C.HvNat{0n}, C.HdNil{}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrTm{C.HSnd{}}}}}

def ghc.roseSum.i1() -> {C.eval.hp(40n, roseSum(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{4n}, C.HvInl{C.HvUnit{}}}}) == C.RDone{Some{C.HvNat{4n}}} : C.Run}:
  {==}

def ghc.roseSum.i1.F() -> {C.eval.bp(C.F.pn(40n, roseSum()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{4n}, C.HvInl{C.HvUnit{}}}})) == C.encM(Some{C.HvNat{4n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.roseSum.i2() -> {C.eval.hp(40n, roseSum(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{1n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{2n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{5n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{3n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}}}}) == C.RDone{Some{C.HvNat{11n}}} : C.Run}:
  {==}

def ghc.roseSum.i2.F() -> {C.eval.bp(C.F.pn(40n, roseSum()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{1n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{2n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{5n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{3n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}}}})) == C.encM(Some{C.HvNat{11n}}) : Maybe<&2, C.BV>}:
  {==}

def roseDepth() -> C.HPg:
  C.HPg{C.HdCons{C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrTm{C.HLit{1n}}, C.HrComp{C.HrCall{1n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrCase{C.HrTm{C.HLit{0n}}, C.HrComp{C.HrIf{C.HrComp{C.HrTm{C.HPrim{C.PLt{}}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}}, C.HrPr{C.HrTm{C.HId{}}, C.HrPr{C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}}}, C.HrComp{C.HrCall{1n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}}}, C.HrComp{C.HrTm{C.HDist{}}, C.HrPr{C.HrTm{C.HId{}}, C.HrTm{C.HSnd{}}}}}, C.HvNat{0n}, C.HdNil{}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrTm{C.HSnd{}}}}}

def ghc.roseDepth.i1() -> {C.eval.hp(40n, roseDepth(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{4n}, C.HvInl{C.HvUnit{}}}}) == C.RDone{Some{C.HvNat{1n}}} : C.Run}:
  {==}

def ghc.roseDepth.i1.F() -> {C.eval.bp(C.F.pn(40n, roseDepth()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{4n}, C.HvInl{C.HvUnit{}}}})) == C.encM(Some{C.HvNat{1n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.roseDepth.i2() -> {C.eval.hp(40n, roseDepth(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{1n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{2n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{5n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{3n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}}}}) == C.RDone{Some{C.HvNat{3n}}} : C.Run}:
  {==}

def ghc.roseDepth.i2.F() -> {C.eval.bp(C.F.pn(40n, roseDepth()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{1n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{2n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{5n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{3n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}}}})) == C.encM(Some{C.HvNat{3n}}) : Maybe<&2, C.BV>}:
  {==}

def roseDouble() -> C.HPg:
  C.HPg{C.HdCons{C.HrComp{C.HrPr{C.HrComp{C.HrApp{}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}}}, C.HrComp{C.HrCall{1n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}, C.HrPr{C.HrTm{C.HId{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrCase{C.HrComp{C.HrTm{C.HInl{}}, C.HrTm{C.HUnit{}}}, C.HrComp{C.HrTm{C.HInr{}}, C.HrPr{C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}}}}, C.HrComp{C.HrCall{1n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}}}, C.HrComp{C.HrTm{C.HDist{}}, C.HrPr{C.HrTm{C.HId{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}, C.HvNat{0n}, C.HdNil{}}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrPr{C.HrTm{C.clo(2n)}, C.HrTm{C.HSnd{}}}}}}

def ghc.roseDouble.i1() -> {C.eval.hp(40n, roseDouble(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{4n}, C.HvInl{C.HvUnit{}}}}) == C.RDone{Some{C.HvPair{C.HvNat{8n}, C.HvInl{C.HvUnit{}}}}} : C.Run}:
  {==}

def ghc.roseDouble.i1.F() -> {C.eval.bp(C.F.pn(40n, roseDouble()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{4n}, C.HvInl{C.HvUnit{}}}})) == C.encM(Some{C.HvPair{C.HvNat{8n}, C.HvInl{C.HvUnit{}}}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.roseDouble.i2() -> {C.eval.hp(40n, roseDouble(), C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{1n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{2n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{5n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{3n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}}}}) == C.RDone{Some{C.HvPair{C.HvNat{2n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{4n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{10n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{6n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}}}}} : C.Run}:
  {==}

def ghc.roseDouble.i2.F() -> {C.eval.bp(C.F.pn(40n, roseDouble()), C.enc(C.HvPair{C.HvUnit{}, C.HvPair{C.HvNat{1n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{2n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{5n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{3n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}}}})) == C.encM(Some{C.HvPair{C.HvNat{2n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{4n}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{10n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}, C.HvInr{C.HvPair{C.HvPair{C.HvNat{6n}, C.HvInl{C.HvUnit{}}}, C.HvInl{C.HvUnit{}}}}}}}}) : Maybe<&2, C.BV>}:
  {==}

def evalEx() -> C.HPg:
  C.HPg{C.HdCons{C.HrComp{C.HrCase{C.HrTm{C.HSnd{}}, C.HrComp{C.HrCase{C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}, C.HrComp{C.HrCase{C.HrComp{C.HrTm{C.HPrim{C.PDiv{}}}, C.HrPr{C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}, C.HrComp{C.HrCall{1n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrTm{C.HSnd{}}}}}, C.HrComp{C.HrTm{C.HDist{}}, C.HrPr{C.HrTm{C.HId{}}, C.HrTm{C.HSnd{}}}}}}, C.HrComp{C.HrTm{C.HDist{}}, C.HrPr{C.HrTm{C.HId{}}, C.HrTm{C.HSnd{}}}}}}, C.HrComp{C.HrTm{C.HDist{}}, C.HrPr{C.HrTm{C.HId{}}, C.HrTm{C.HSnd{}}}}}, C.HvNat{0n}, C.HdCons{C.HrComp{C.HrCase{C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrTm{C.HSnd{}}}}, C.HrComp{C.HrTm{C.HPrim{C.PAdd{}}}, C.HrPr{C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HFst{}}, C.HrTm{C.HSnd{}}}}}, C.HrComp{C.HrCall{1n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrComp{C.HrTm{C.HSnd{}}, C.HrTm{C.HSnd{}}}}}}}}, C.HrComp{C.HrTm{C.HDist{}}, C.HrPr{C.HrTm{C.HId{}}, C.HrTm{C.HSnd{}}}}}, C.HvNat{0n}, C.HdNil{}}}, C.HrComp{C.HrCall{0n}, C.HrPr{C.HrTm{C.HUnit{}}, C.HrTm{C.HSnd{}}}}}

def ghc.evalEx.i1() -> {C.eval.hp(40n, evalEx(), C.HvPair{C.HvUnit{}, C.HvInl{C.HvNat{3n}}}) == C.RDone{Some{C.HvNat{3n}}} : C.Run}:
  {==}

def ghc.evalEx.i1.F() -> {C.eval.bp(C.F.pn(40n, evalEx()), C.enc(C.HvPair{C.HvUnit{}, C.HvInl{C.HvNat{3n}}})) == C.encM(Some{C.HvNat{3n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.evalEx.i2() -> {C.eval.hp(40n, evalEx(), C.HvPair{C.HvUnit{}, C.HvInr{C.HvInl{C.HvPair{C.HvInl{C.HvNat{7n}}, C.HvInl{C.HvNat{2n}}}}}}) == C.RDone{Some{C.HvNat{5n}}} : C.Run}:
  {==}

def ghc.evalEx.i2.F() -> {C.eval.bp(C.F.pn(40n, evalEx()), C.enc(C.HvPair{C.HvUnit{}, C.HvInr{C.HvInl{C.HvPair{C.HvInl{C.HvNat{7n}}, C.HvInl{C.HvNat{2n}}}}}})) == C.encM(Some{C.HvNat{5n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.evalEx.i3() -> {C.eval.hp(40n, evalEx(), C.HvPair{C.HvUnit{}, C.HvInr{C.HvInl{C.HvPair{C.HvInl{C.HvNat{2n}}, C.HvInl{C.HvNat{7n}}}}}}) == C.RDone{None{}} : C.Run}:
  {==}

def ghc.evalEx.i3.F() -> {C.eval.bp(C.F.pn(40n, evalEx()), C.enc(C.HvPair{C.HvUnit{}, C.HvInr{C.HvInl{C.HvPair{C.HvInl{C.HvNat{2n}}, C.HvInl{C.HvNat{7n}}}}}})) == C.encM(None{}) : Maybe<&2, C.BV>}:
  {==}

def ghc.evalEx.i4() -> {C.eval.hp(40n, evalEx(), C.HvPair{C.HvUnit{}, C.HvInr{C.HvInr{C.HvInl{C.HvPair{C.HvInl{C.HvNat{9n}}, C.HvInl{C.HvNat{2n}}}}}}}) == C.RDone{Some{C.HvNat{4n}}} : C.Run}:
  {==}

def ghc.evalEx.i4.F() -> {C.eval.bp(C.F.pn(40n, evalEx()), C.enc(C.HvPair{C.HvUnit{}, C.HvInr{C.HvInr{C.HvInl{C.HvPair{C.HvInl{C.HvNat{9n}}, C.HvInl{C.HvNat{2n}}}}}}})) == C.encM(Some{C.HvNat{4n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.evalEx.i5() -> {C.eval.hp(40n, evalEx(), C.HvPair{C.HvUnit{}, C.HvInr{C.HvInr{C.HvInl{C.HvPair{C.HvInl{C.HvNat{9n}}, C.HvInl{C.HvNat{0n}}}}}}}) == C.RDone{None{}} : C.Run}:
  {==}

def ghc.evalEx.i5.F() -> {C.eval.bp(C.F.pn(40n, evalEx()), C.enc(C.HvPair{C.HvUnit{}, C.HvInr{C.HvInr{C.HvInl{C.HvPair{C.HvInl{C.HvNat{9n}}, C.HvInl{C.HvNat{0n}}}}}}})) == C.encM(None{}) : Maybe<&2, C.BV>}:
  {==}

def ghc.evalEx.i6() -> {C.eval.hp(40n, evalEx(), C.HvPair{C.HvUnit{}, C.HvInr{C.HvInr{C.HvInr{C.HvInr{C.HvPair{C.HvInl{C.HvNat{1n}}, C.HvInr{C.HvPair{C.HvInr{C.HvInl{C.HvPair{C.HvInl{C.HvNat{9n}}, C.HvInl{C.HvNat{4n}}}}}, C.HvInl{C.HvInr{C.HvInr{C.HvInr{C.HvInl{C.HvInl{C.HvNat{2n}}}}}}}}}}}}}}}) == C.RDone{Some{C.HvNat{8n}}} : C.Run}:
  {==}

def ghc.evalEx.i6.F() -> {C.eval.bp(C.F.pn(40n, evalEx()), C.enc(C.HvPair{C.HvUnit{}, C.HvInr{C.HvInr{C.HvInr{C.HvInr{C.HvPair{C.HvInl{C.HvNat{1n}}, C.HvInr{C.HvPair{C.HvInr{C.HvInl{C.HvPair{C.HvInl{C.HvNat{9n}}, C.HvInl{C.HvNat{4n}}}}}, C.HvInl{C.HvInr{C.HvInr{C.HvInr{C.HvInl{C.HvInl{C.HvNat{2n}}}}}}}}}}}}}}})) == C.encM(Some{C.HvNat{8n}}) : Maybe<&2, C.BV>}:
  {==}

def ghc.evalEx.i7() -> {C.eval.hp(40n, evalEx(), C.HvPair{C.HvUnit{}, C.HvInr{C.HvInr{C.HvInr{C.HvInr{C.HvPair{C.HvInr{C.HvInr{C.HvInl{C.HvPair{C.HvInl{C.HvNat{1n}}, C.HvInl{C.HvNat{0n}}}}}}, C.HvInl{C.HvInl{C.HvNat{2n}}}}}}}}}) == C.RDone{None{}} : C.Run}:
  {==}

def ghc.evalEx.i7.F() -> {C.eval.bp(C.F.pn(40n, evalEx()), C.enc(C.HvPair{C.HvUnit{}, C.HvInr{C.HvInr{C.HvInr{C.HvInr{C.HvPair{C.HvInr{C.HvInr{C.HvInl{C.HvPair{C.HvInl{C.HvNat{1n}}, C.HvInl{C.HvNat{0n}}}}}}, C.HvInl{C.HvInl{C.HvNat{2n}}}}}}}}})) == C.encM(None{}) : Maybe<&2, C.BV>}:
  {==}

def constErr() -> C.HPg:
  C.HPg{C.HdCons{C.HrTm{C.clo(1n)}, C.HvNat{0n}, C.HdCons{C.HrTm{C.HComp{C.HSnd{}, C.HFst{}}}, C.HvNat{0n}, C.HdNil{}}}, C.HrComp{C.HrApp{}, C.HrPr{C.HrComp{C.HrApp{}, C.HrPr{C.HrTm{C.clo(0n)}, C.HrTm{C.HSnd{}}}}, C.HrComp{C.HrTm{C.HPrim{C.PSub{}}}, C.HrPr{C.HrTm{C.HLit{0n}}, C.HrTm{C.HLit{1n}}}}}}}

# GHC answers C.HvNat{4n} (an argument that errs, never forced)
def ghc.constErr.i1() -> {C.eval.hp(30n, constErr(), C.HvPair{C.HvUnit{}, C.HvNat{4n}}) == C.RDone{None{}} : C.Run}:
  {==}

def ghc.constErr.i1.F() -> {C.eval.bp(C.F.pn(30n, constErr()), C.enc(C.HvPair{C.HvUnit{}, C.HvNat{4n}})) == C.encM(None{}) : Maybe<&2, C.BV>}:
  {==}
