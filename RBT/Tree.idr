module RBT.Tree

%access public export
%default total

data Color = R | B

-- Invariant that red node has black children enforced in type.
data RBT : Type where
  E : RBT
  T : Color -> RBT -> Nat -> RBT -> RBT

--------------------------------------------------------------------------------

compareBranch : Nat -> Nat -> b -> b -> b -> b
compareBranch m n l e g with (cmp m n)
  compareBranch m (m + (S y)) l e g | (CmpLT y) = l
  compareBranch n n l e g | CmpEQ = e
  compareBranch (n + (S x)) n l e g | (CmpGT x) = g

prf : (x : Nat) -> compareBranch x x l e g = e
prf x with (cmp x x)
  | CmpEQ = ?asdf

--------------------------------------------------------------------------------

balance : RBT -> RBT
balance E = E
balance (T B (T R (T R a x b) y c) z d) = T R (T B a x b) y (T B c z d)
balance (T B (T R a x (T R b y c)) z d) = T R (T B a x b) y (T B c z d)
balance (T B a x (T R (T R b y c) z d)) = T R (T B a x b) y (T B c z d)
balance (T B a x (T R b y (T R c z d))) = T R (T B a x b) y (T B c z d)
balance (T c l x r) = T c l x r

makeBlack : RBT -> RBT
makeBlack E = E
makeBlack (T _ l y r) = T B l y r

ins : Nat -> RBT -> RBT
ins x E = T R E x E
ins x (T c l y r) =
  compareBranch x y
    (balance (T c (ins x l) y r))
    (T c l y r)
    (balance (T c l y (ins x r)))

insert : Nat -> RBT -> RBT
insert x s = makeBlack (ins x s)

member : Nat -> RBT -> Bool
member _ E = False
member x (T _ l y r) =
  compareBranch x y
    (member x l)
    True
    (member x r)

--------------------------------------------------------------------------------

listFromRBT : RBT -> List Nat
listFromRBT E = []
listFromRBT (T _ l x r) = listFromRBT l ++ [x] ++ listFromRBT r

listToRBT : List Nat -> RBT
listToRBT [] = E
listToRBT (h::t) = insert h (listToRBT t)
