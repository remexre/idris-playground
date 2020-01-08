module RBT.Induction

import RBT.Tree

%access public export
%default total

-- Distributes a property to all children of a tree.
All : (RBT -> Type) -> RBT -> Type
All P E = P E
All P (T c l x r) = (P l, P (T c l x r), P r)

weaken : {tree : RBT} -> {P : RBT -> Type} -> All P tree -> P tree
weaken {tree=E} {P} prf = prf
weaken {tree=T c l x r} {P} (_, prf, _) = prf

-- Defines strong induction for proving local properties on a tree.
rbtInduction : (P : RBT -> Type) -- property
            -> P E -- empty case
            -> ((color: Color) -> (l: RBT) -> (x: Nat) -> (r: RBT) ->
                All P l -> All P r -> P (T color l x r))
            -> (tree: RBT) -> All P tree -- property holds for all trees
rbtInduction P empty branch E = empty
rbtInduction P empty branch (T c l x r) = (weaken l', x', weaken r') where
  l' : All P l
  l' = rbtInduction P empty branch l
  r' : All P r
  r' = rbtInduction P empty branch r
  x' : P (T c l x r)
  x' = branch c l x r l' r'
