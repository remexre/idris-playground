module RBT.Proofs.Sorted

import RBT.Induction
import RBT.Tree

%access public export
%default total

AllLT : RBT -> Nat -> Type
AllLT E _ = () -- trivial
AllLT (T _ l x r) y = (AllLT l y, LT x y, AllLT r y)

AllGT : RBT -> Nat -> Type
AllGT E _ = () -- trivial
AllGT (T _ l x r) y = (AllGT l y, GT x y, AllGT r y)

Sorted : RBT -> Type
Sorted E = () -- trivial
Sorted (T _ l x r) = (AllLT l x, AllGT r x)

-- Almost trivial, since makeBlack doesn't alter anything Sorted cares about.
-- We need to do a case-split on the tree to force Idris to check that, though.
prfMakeBlackPreservesSorted : (tree : RBT) -> All Sorted tree -> All Sorted (makeBlack tree)
prfMakeBlackPreservesSorted E () = ()
prfMakeBlackPreservesSorted (T _ _ _ _) prf = prf

{-
prfBalancePreservesSorted : (tree : RBT) -> All Sorted tree -> All Sorted (balance tree)
prfBalancePreservesSorted E () = ()
prfBalancePreservesSorted (T B (T R (T R a x b) y c) z d)
  (((allLTay, ltxy, allLTby),
    allGTcy),
   (((allLTaz, ltxz, allLTbz), ltyz, allLTcz), allGTdz),
   sortedD) =
     ((allLTax, ?allGTbx),
      ((allLTay, ltxy, allLTby), allGTcy, ltyz, ?allGTdy),
      allLTcz, allGTdz) where
        allLTax : AllLT a x
        allLTax = ?allLTax1 (prfBalancePreservesSorted (T R (T R a x b) y c))
prfBalancePreservesSorted (T B (T R a x (T R b y c)) z d) prf = ?jajdsa
prfBalancePreservesSorted (T B a x (T R (T R b y c) z d)) prf = ?jajjsnd
prfBalancePreservesSorted (T B a x (T R b y (T R c z d))) prf = ?jajfwonk
prfBalancePreservesSorted (T c l x r) (sortedL, (allLTlx, allGTrx), sortedR) = ?aljsdn_3
-}

{-
prfInsPreservesSorted : (tree : RBT) -> (y : Nat) -> All Sorted tree -> All Sorted (ins y tree)
prfInsPreservesSorted E y () = ((), ((), ()), ()) -- trivial, in so many words
prfInsPreservesSorted (T c l x r) y prf with (cmp x y)
  prfInsPreservesSorted (T c l x r) (x + (S k)) prf | (CmpLT k) = ?prfInsPreservesSorted_rhs_1
  prfInsPreservesSorted (T c l y r) y prf | CmpEQ = ?odsna
  prfInsPreservesSorted (T c l (y + (S k)) r) y prf | (CmpGT k) = ?prfInsPreservesSorted_rhs_3
-}
