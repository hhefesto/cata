# a laws' script for G(F(h)): h's Map Int and IntMap (Set Int and IntSet) are
# wildcards in h's script (Law.bend's lw.map.ty); G's are Data.Map's and Set's
s/(_ /(LawM.Map LawP.Int /g
s/(_)/(LawS.Set LawP.Int)/g
