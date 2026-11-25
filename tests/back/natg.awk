# a module's laws' script for G(F(h)): in a module alone F takes h's Int,
# Integer and Natural to Nat, and G takes Nat to Natural, so G(F(h)) is
# called at Natural where h is at any of them (a call's type only: the
# script's classes and instances are as they are).  A package's script is
# as it is: there Int and Integer are HsInt, G's Integer, and BendRt's B'Up
# takes Int to it.
/^lawRun "/ { gsub(/LawP\.Integer/, "LawN.Natural"); gsub(/LawP\.Int/, "LawN.Natural") }
{ print }
