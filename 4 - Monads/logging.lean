/- ------- -/
/- Logging -/
/- ------- -/

def isEven (i : Int) : Bool :=
  i % 2 == 0

#eval isEven 0
#eval isEven 1
#eval isEven 2
#eval isEven 3

-- This function is a simplified example of a common pattern.
-- Many programs need to traverse a data structure once, while both
-- computing a main result and accumulating some kind of tertiary extra result.

-- computes the sum of a list while remembering the even numbers
def sumAndFindEvens1 : List Int → List Int × Int
  | []      => ([], 0)
  | x :: xs => let (evens, sum) := sumAndFindEvens1 xs
               (if isEven x then x :: evens else evens, sum + x)

#eval sumAndFindEvens1 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ]

inductive BinTree (α : Type) where
  | leaf   : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

-- computes the sum of all the nodes in a tree with an inorder traversal,
-- while simultaneously recording each nodes visited
def inorderSum1 : BinTree Int → List Int × Int
  | BinTree.leaf         => ([], 0)
  | BinTree.branch l x r => let (leftVisited,  leftSum)  := inorderSum1 l
                            let (rightVisited, rightSum) := inorderSum1 r
                            (leftVisited ++ [x] ++ rightVisited, leftSum + x + rightSum)

open BinTree
#eval inorderSum1 (branch                             
                    (branch leaf 13 leaf) 
                    5 
                    (branch leaf 10 leaf))

def sumAndFindEvens2 : List Int → List Int × Int
  | []      => ([], 0)
  | x :: xs => let (evens, sum) := sumAndFindEvens2 xs
               let evenHere     := if isEven x then [x] else []
               (evenHere ++ evens, sum + x)

#eval sumAndFindEvens2 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

structure WithLog (logged : Type) (α : Type) where
  log : List logged -- accumulated result
  val : α           -- value

-- the process of saving a list of accumulated results while passing a value on to the next step
-- of a computation can be factored out into a helper
def andThen (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}

def ok (x : β)    : WithLog α β    := {log := [],     val := x}
def save (data : α) : WithLog α Unit := {log := [data], val := ()}

def sumAndFindEvens3 : List Int → WithLog Int Int
  | []      => ok 0
  | x :: xs => andThen (if isEven x then save x else ok ()) fun ()  =>
               andThen (sumAndFindEvens3 xs)                fun sum =>
               ok (x + sum)

#eval sumAndFindEvens3 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def inorderSum3 : BinTree Int → WithLog Int Int
  | BinTree.leaf         => ok 0
  | BinTree.branch l x r => andThen (inorderSum3 l) fun leftSum  =>
                            andThen (save x)        fun ()       =>
                            andThen (inorderSum3 r) fun rightSum =>
                            ok (leftSum + x + rightSum)

#eval inorderSum3 (branch                             
                    (branch leaf 13 leaf) 
                    5 
                    (branch leaf 10 leaf))

infixl:55 " ~~> " => andThen

def sumAndFindEvens : List Int → WithLog Int Int
  | []      => ok 0
  | x :: xs => (if isEven x then save x else ok ()) ~~> fun ()  =>
               sumAndFindEvens xs                   ~~> fun sum =>
               ok (x + sum)

def inorderSum : BinTree Int → WithLog Int Int
  | BinTree.leaf         => ok 0
  | BinTree.branch l x r => inorderSum l ~~> fun leftSum  =>
                            save x       ~~> fun ()       =>
                            inorderSum r ~~> fun rightSum =>
                            ok (leftSum + x + rightSum)

def intTree : BinTree Int :=
  branch
    (branch
       (branch leaf 1 (branch leaf 2 leaf))
       3 
       leaf)
    4 
    (branch leaf 5 leaf)

#eval inorderSum intTree                             

#eval inorderSum (branch                             
                   (branch leaf 13 leaf) 
                   5 
                   (branch leaf 10 leaf))
